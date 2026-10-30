import ShorECDLP.Submission.Entrant.Compiler
import ShorECDLP.Framework.Quantum.AdaptiveDisjoint
section
set_option Elab.async false
namespace ShorECDLP.Entrant.Catalyst
open Quantum Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket
set_option linter.unusedSimpArgs false

def prepare (q : Wire) : Circuit := [.H q, .P .forward 2 q]
def kick (t q : Wire) : Circuit := [.CX t q] ++ controlledZ t q
private theorem phase_two : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring
private theorem upd_twice (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]

theorem kick_ket (t q : Wire) (ht : t ≠ q) (s : BasisState) (hq : s q = false) :
    Quantum.run (kick t q) (Quantum.run (prepare q) (ket s)) =
      Quantum.run (prepare q) (applyGate (.P .forward 2 t) (ket s)) := by
  simp only [kick, prepare, Quantum.run_append, Quantum.run_cons, Quantum.run_nil,
    LinearMap.id_coe, id_eq, applyGate_H_ket, applyGate_P_ket, map_add, map_smul,
    applyGate_CX_ket, run_controlledZ_ket t q _ ht, upd_same, upd_other _ _ _ ht,
    upd_twice, phase_two, hq, Bool.false_eq_true, if_false, if_true, mul_one]
  cases hs : s t <;> simp [hs, smul_add, smul_smul, Complex.I_mul_I]
  all_goals match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

theorem linear_on_supported (A B : State →ₗ[ℂ] State) (V : BasisState → Prop)
    (h : ∀ s, V s → A (ket s) = B (ket s)) (psi : State) (hp : SupportedOn V psi) :
    A psi = B psi := by
  have hb : BranchCoherentOn B V ⟨[],A⟩ 1 := by
    intro s hs
    simpa only [one_smul] using h s hs
  simpa only [one_smul] using hb.on_supported hp

theorem linear_comp_supported (A B C D : State →ₗ[ℂ] State) (V : BasisState → Prop)
    (h : ∀ s, V s → A (B (ket s)) = C (D (ket s))) (psi : State) (hp : SupportedOn V psi) :
    A (B psi) = C (D psi) := linear_on_supported (A.comp B) (C.comp D) V h psi hp

theorem kick_supported (t q : Wire) (ht : t ≠ q) (psi : State)
    (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (kick t q) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (applyGate (.P .forward 2 t) psi) :=
  linear_comp_supported (Quantum.run (kick t q)) (Quantum.run (prepare q))
    (Quantum.run (prepare q)) (applyGate (.P .forward 2 t)) _
    (kick_ket t q ht) psi hp

theorem prepare_gate (q : Wire) (g : Gate) (hq : q ∉ gateWires g) (psi : State) :
    applyGate g (Quantum.run (prepare q) psi) = Quantum.run (prepare q) (applyGate g psi) := by
  simp only [prepare, Quantum.run_cons, Quantum.run_nil, LinearMap.id_coe, id_eq]
  rw [applyGate_P_commute g q .forward 2 hq, applyGate_H_commute g q hq]

theorem prepare_reset (q w : Wire) (hq : q ≠ w) (b : Bool) (psi : State) :
    xResetKraus w b (Quantum.run (prepare q) psi) = Quantum.run (prepare q) (xResetKraus w b psi) := by
  simp only [prepare, Quantum.run_cons, Quantum.run_nil, LinearMap.id_coe, id_eq]
  rw [xReset_P_commute w q b .forward 2 hq,
    ← applyGate_reset_commute (.H q) w b (by simpa [gateWires, ne_comm] using hq)]
open Challenge AndGadget

def replacement (q : Wire) : Gate → Circuit
  | .P .forward 2 t => kick t q
  | g => [g]

def savedGate : Gate → Nat
  | .P .forward 2 _ => 1
  | _ => 0

def compile {n s e} (q : Wire) : Straight n s e → Straight n s e
  | .done => .done
  | .gate (.literal g) next => literals (replacement q g) (compile q next)
  | .gate (.whenBit r v g) next => .gate (.whenBit r v g) (compile q next)
  | .recordGate i v g next => .recordGate i v g (compile q next)
  | .measure w next => .measure w (compile q next)

def saved {n s e} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) next => savedGate g + saved next
  | .gate _ next => saved next
  | .recordGate _ _ _ next => saved next
  | .measure _ next => saved next

theorem replacement_correct (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (psi : State) (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (replacement q g) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (applyGate g psi) := by
  unfold replacement
  split
  · rename_i t
    exact kick_supported t q (by simpa [gateWires, ne_comm] using hq) psi hp
  · simpa only [Quantum.run_singleton] using prepare_gate q g hq psi

private theorem gate_frame (q : Wire) (gs : Circuit) (hq : q ∉ circuitWires gs)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (Quantum.run gs psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary gs .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[], Quantum.run gs⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hpsi
  exact h

private theorem reset_frame (q w : Wire) (hq : q ≠ w) (outcome : Bool)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (xResetKraus w outcome psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[outcome], xResetKraus w outcome⟩ ?_ psi hpsi
  cases outcome <;>
    simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_append, List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem compile_expectation {n s e} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hf : Fresh q p)
    (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (compile q p) history (Quantum.run (prepare q) psi) accept =
      expectation read p history psi accept := by
  induction p generalizing psi with
  | done =>
    simp only [compile, expectation, normSq_run (prepare q) (by simp [prepare, CircuitWellFormed, Gate.WellFormed])]
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [compile, expectation_literals, replacement_correct q g hf.1 psi hp,
        expectation, TemplateGate.instantiate, Quantum.run_singleton]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    | whenBit r v g =>
      simp only [compile, expectation, TemplateGate.instantiate]
      split
      · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
      · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | recordGate i v g p ih =>
    simp only [compile, expectation]
    split
    · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | measure w p ih =>
    simp only [compile, expectation, prepare_reset q w hf.1]
    rw [ih _ _ accept hf.2 (reset_frame q w hf.1 false psi hp), ih _ _ accept hf.2 (reset_frame q w hf.1 true psi hp)]

theorem replacement_t (q : Wire) (g : Gate) :
    ShorECDLP.tCount (replacement q g) + savedGate g = tCost g := by
  unfold replacement savedGate
  split
  · rfl
  · rename_i g h
    cases g <;> simp_all [tCount, tCost]

theorem literals_t {n s e} (gs : Circuit) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((literals gs p).instantiate read history).tCount =
      ShorECDLP.tCount gs + (p.instantiate read history).tCount := AndGadget.literals_t read gs p history

theorem compile_t {n s e} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((compile q p).instantiate read history).tCount + saved p =
      (p.instantiate read history).tCount := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [compile, literals_t, saved, Straight.instantiate, TemplateGate.instantiate,
        AdaptiveCircuit.tCount, tCount, List.sum_cons, List.map_cons, List.map_nil, List.sum_nil]
      have h := replacement_t q g
      simp only [ShorECDLP.tCount] at h
      have hi := ih history
      omega
    | whenBit r v g =>
      simp only [compile, saved, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount]
      have hi := ih history
      omega
  | recordGate i v g p ih =>
    simp only [compile, saved, Straight.instantiate, AdaptiveCircuit.tCount]
    have hi := ih history
    omega
  | measure w p ih =>
    simp only [compile, saved, Straight.instantiate, AdaptiveCircuit.tCount]
    have h0 := ih (Fin.lastCases false history)
    have h1 := ih (Fin.lastCases true history)
    omega

theorem replacement_wellFormed (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (hg : Gate.WellFormed g) : CircuitWellFormed (replacement q g) := by
  unfold replacement
  split
  · rename_i t
    have ht : t ≠ q := by simpa [gateWires, ne_comm] using hq
    simp [kick, controlledZ, CircuitWellFormed, Gate.WellFormed, ht]
  · simpa [CircuitWellFormed] using hg

theorem literals_wellFormed {n s e} (gs : Circuit) (p : Straight n s e)
    (hg : CircuitWellFormed gs) (hp : p.WellFormed) : (literals gs p).WellFormed := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
    exact ⟨hg g (by simp), ih (by intro a ha; exact hg a (by simp [ha]))⟩

theorem compile_wellFormed {n s e} (q : Wire) (p : Straight n s e)
    (hf : Fresh q p) (hp : p.WellFormed) : (compile q p).WellFormed := by
  induction p with
  | done => trivial
  | gate g p ih =>
    cases g with
    | literal g => exact literals_wellFormed _ _ (replacement_wellFormed q g hf.1 hp.1) (ih hf.2 hp.2)
    | whenBit => exact ⟨hp.1, ih hf.2 hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hf.2; exact hp.2⟩
  | measure w p ih => exact ih hf.2 hp

theorem replacement_wires (q : Wire) (g : Gate) :
    circuitWires (replacement q g) ⊆ q :: gateWires g := by
  unfold replacement
  split
  · simp [kick, controlledZ, circuitWires, gateWires, List.subset_def]
  · simp [circuitWires]

theorem literals_within {n s e} (ws : List Wire) (gs : Circuit) (p : Straight n s e)
    (hg : circuitWires gs ⊆ ws) (hp : Within ws p) : Within ws (literals gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
    have h : gateWires g ⊆ ws ∧ circuitWires gs ⊆ ws := by simpa [circuitWires] using hg
    exact ⟨h.1, ih h.2⟩

theorem compile_within {n s e} (q : Wire) (p : Straight n s e) (ws : List Wire)
    (hp : Within ws p) : Within (q::ws) (compile q p) := by
  induction p with
  | done => trivial
  | gate g p ih =>
    cases g with
    | literal g =>
      apply literals_within
      · exact (replacement_wires q g).trans (List.cons_subset_cons q hp.1)
      · exact ih hp.2
    | whenBit => exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), ih hp.2⟩
  | recordGate => exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), by apply_assumption; exact hp.2⟩
  | measure => exact ⟨List.mem_cons_of_mem q hp.1, by apply_assumption; exact hp.2⟩

theorem replacement_length (q : Wire) (g : Gate) :
    (replacement q g).length = 1 + 3 * savedGate g := by
  unfold replacement savedGate
  split <;> rfl

theorem compile_slots {n s e} (q : Wire) (p : Straight n s e) :
    (compile q p).gateSlots = p.gateSlots + 3 * saved p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp [compile, saved, literals_slots, replacement_length, Straight.gateSlots, ih] <;> omega
  | recordGate => simp_all [compile, saved, Straight.gateSlots]; omega
  | measure => exact (by apply_assumption)

theorem saved_le_slots {n s e} (p : Straight n s e) : saved p ≤ p.gateSlots := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      have hg : savedGate g ≤ 1 := by unfold savedGate; split <;> omega
      simp only [saved, Straight.gateSlots]
      omega
    | whenBit => simp only [saved, Straight.gateSlots]; omega
  | recordGate => simp only [saved, Straight.gateSlots]; omega
  | measure => exact (by apply_assumption)

theorem saved_literals {n s e} (gs : Circuit) (p : Straight n s e) :
    saved (literals gs p) = (gs.map savedGate).sum + saved p := by
  induction gs with
  | nil => simp [literals]
  | cons g gs ih =>
    change savedGate g + saved (literals gs p) = _
    rw [ih]
    simp [Nat.add_assoc]

theorem saved_toffoliPrefix {n s e} (a b t q : Wire) (p : Straight n (s+1) e) :
    saved (toffoliPrefix a b t q p) = 1 + saved p := by
  simp [toffoliPrefix, saved_literals, andCompute, parityPhase, xorPhase, saved, savedGate]

theorem saved_lower {n s e} (q : Wire) (p : Straight n s e) (start : Nat)
    (records : Fin s → Fin start) :
    saved (lower q p start records).program = added p + saved p := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp [lower, added, saved, saved_toffoliPrefix, ih, savedGate] <;> omega
    | whenBit => exact ih _ _
  | recordGate => exact (by apply_assumption)
  | measure => exact (by apply_assumption)

def compileEntry (q : Wire) (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := entry.finalCursor
  program := literals (prepare q) (compile q entry.program)

theorem compile_verified {n e} (q : Wire) (p : Straight n 0 e)
    (read : ConstantBit n → Bool) (layout : DecodeLayout) (Q : Secp256k1.Point)
    (psi : State) (hf : Fresh q p) (hp : SupportedOn (fun s => s q = false) psi) :
    Instrument.bornMass (((literals (prepare q) (compile q p)).instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi =
    Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [← expectation_verified, ← expectation_verified, expectation_literals]
  exact compile_expectation q p read Fin.elim0 psi _ hf hp

theorem compileEntry_within (q : Wire) (entry : StraightEntry) (ws : List Wire)
    (hp : Within ws entry.program) : Within (q::ws) (compileEntry q entry).program := by
  apply literals_within
  · simp [prepare, circuitWires, gateWires, List.subset_def]
  · exact compile_within q entry.program ws hp

theorem compile_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds newBounds : Bounds) (q : Wire) (ws : List Wire)
    (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hq : q ∉ ws)
    (hslots : entry.program.gateSlots + 3 * saved entry.program + 2 ≤ limits.gateSlots)
    (hqubits : ws.length + 1 ≤ newBounds.qubits)
    (ht : bounds.tModel + 1 ≤ newBounds.tModel + saved entry.program)
    (hm : entry.finalCursor ≤ newBounds.measurements) :
    Certificate limits layout (compileEntry q entry) newBounds where
  gateBudget := by simpa [compileEntry, literals_slots, compile_slots, prepare, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hslots
  recordBudget := cert.recordBudget
  tableBudget := cert.tableBudget
  candidateBudget := cert.candidateBudget
  wellFormed := literals_wellFormed _ _ (by simp [prepare, CircuitWellFormed, Gate.WellFormed])
    (compile_wellFormed q entry.program (hs.fresh q hq) cert.wellFormed)
  resources := by
    intro Q
    have hsup := (compileEntry_within q entry ws hs).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((compileEntry q entry).instantiate Q).wires.dedup.toFinset).card ≤ (q :: ws).length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (q :: ws))
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((compileEntry q entry).instantiate Q).qubitCount ≤ newBounds.qubits := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc.trans hqubits
    have htc := compile_t q entry.program (readConstant entry.coefficients.get Q) Fin.elim0
    have hto := (cert.resources Q).2.1
    have hmc := (compileEntry q entry).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    refine ⟨hqc, ?_, ?_⟩
    · change ((literals (prepare q) (compile q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      rw [literals_t]
      change 1 + ((compile q entry.program).instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      change (entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel at hto
      omega
    · change ((compileEntry q entry).program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ newBounds.measurements
      have he : ((compileEntry q entry).program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount = entry.finalCursor := by
        simpa only [Nat.add_zero] using hmc
      exact he.le.trans hm
  success := by
    intro Q d hn hd
    change 99 / 100 ≤ Instrument.bornMass
      (((literals (prepare q) (compile q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState)
    rw [compile_verified q entry.program _ layout Q _ (hs.fresh q hq)
      (supportedOn_ket _ _ rfl)]
    exact cert.success Q d hn hd

end
end ShorECDLP.Entrant.Catalyst
end
