import ShorECDLP.Submission.Entrant.MainA


set_option linter.unusedSectionVars false

section
set_option Elab.async false
namespace ShorECDLP.Entrant.CatalystS
open Quantum Paper2607_13816 ShorECDLP.Challenge ShorECDLP.Entrant.AndGadget
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket
set_option linter.unusedSimpArgs false

def unkick (t q : Wire) : Circuit := controlledZ t q ++ [.CX t q]

def inverseReplacement (q : Wire) : Gate → Circuit
  | .P .inverse 2 t => unkick t q
  | g => [g]

def inverseSavedGate : Gate → Nat
  | .P .inverse 2 _ => 1
  | _ => 0

def records {n s e : Nat} (i : Fin s) (v : Bool) (gs : Circuit) (next : Straight n s e) :
    Straight n s e :=
  gs.foldr (fun g tail => .recordGate i v g tail) next

def compile {n s e} (q : Wire) : Straight n s e → Straight n s e
  | .done => .done
  | .gate (.literal g) next => literals (Catalyst.replacement q g) (compile q next)
  | .gate (.whenBit r v g) next => .gate (.whenBit r v g) (compile q next)
  | .recordGate i v g next => records i v (inverseReplacement q g) (compile q next)
  | .measure w next => .measure w (compile q next)

def drop {n s e} : Straight n s e → Straight n s e
  | .done => .done
  | .gate g next => .gate g (drop next)
  | .recordGate i v g next =>
      if inverseSavedGate g = 1 then drop next else .recordGate i v g (drop next)
  | .measure w next => .measure w (drop next)

private theorem phase_two : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

private theorem phase_inverse_two : phaseCoeff .inverse 2 = -Complex.I := by
  have h : Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) = -Complex.I := by
    rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  simp only [phaseCoeff, phaseAngle]
  convert h using 2
  push_cast
  ring

private theorem upd_twice (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]

theorem unkick_ket (t q : Wire) (ht : t ≠ q) (s : BasisState) (hq : s q = false) :
    Quantum.run (unkick t q) (Quantum.run (Catalyst.prepare q) (ket s)) =
      Quantum.run (Catalyst.prepare q) (applyGate (.P .inverse 2 t) (ket s)) := by
  simp only [unkick, Catalyst.prepare, Quantum.run_append, Quantum.run_cons, Quantum.run_nil,
    LinearMap.id_coe, id_eq, applyGate_H_ket, applyGate_P_ket, map_add, map_smul,
    applyGate_CX_ket, run_controlledZ_ket t q _ ht, upd_same, upd_other _ _ _ ht,
    upd_twice, phase_two, phase_inverse_two, hq, Bool.false_eq_true, if_false, if_true, mul_one]
  cases hs : s t <;> simp [hs, onKet, upd_same, upd_other _ _ _ ht, upd_twice, smul_add, smul_smul, Complex.I_mul_I]
  all_goals match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

theorem unkick_supported (t q : Wire) (ht : t ≠ q) (psi : State)
    (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (unkick t q) (Quantum.run (Catalyst.prepare q) psi) =
      Quantum.run (Catalyst.prepare q) (applyGate (.P .inverse 2 t) psi) :=
  Catalyst.linear_comp_supported (Quantum.run (unkick t q)) (Quantum.run (Catalyst.prepare q))
    (Quantum.run (Catalyst.prepare q)) (applyGate (.P .inverse 2 t)) _
    (unkick_ket t q ht) psi hp

theorem inverseReplacement_correct (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (psi : State) (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (inverseReplacement q g) (Quantum.run (Catalyst.prepare q) psi) =
      Quantum.run (Catalyst.prepare q) (applyGate g psi) := by
  unfold inverseReplacement
  split
  · rename_i t
    exact unkick_supported t q (by simpa [gateWires, ne_comm] using hq) psi hp
  · simpa only [Quantum.run_singleton] using Catalyst.prepare_gate q g hq psi

private theorem frame_gate (q : Wire) (gs : Circuit) (hq : q ∉ circuitWires gs)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (Quantum.run gs psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary gs .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[], Quantum.run gs⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hpsi
  exact h

private theorem frame_reset (q w : Wire) (hq : q ≠ w) (outcome : Bool)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (xResetKraus w outcome psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[outcome], xResetKraus w outcome⟩ ?_ psi hpsi
  cases outcome <;>
    simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_append, List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem expectation_records {n s e : Nat} (read : ConstantBit n → Bool) (i : Fin s) (v : Bool)
    (gs : Circuit) (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read (records i v gs p) history psi accept =
      expectation read p history (Quantum.run (if history i = v then gs else []) psi) accept := by
  induction gs generalizing psi with
  | nil => by_cases h : history i = v <;> simp [records, h, Quantum.run_nil]
  | cons g gs ih =>
    simp only [records] at ih ⊢
    simp only [List.foldr_cons, expectation]
    rw [ih]
    by_cases h : history i = v
    · simp only [if_pos h, Quantum.run_cons, Quantum.run_nil]
    · simp only [if_neg h, Quantum.run_nil]

theorem compile_expectation {n s e} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hf : Fresh q p)
    (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (compile q p) history (Quantum.run (Catalyst.prepare q) psi) accept =
      expectation read p history psi accept := by
  induction p generalizing psi with
  | done =>
    simp only [compile, expectation, normSq_run (Catalyst.prepare q)
      (by simp [Catalyst.prepare, CircuitWellFormed, Gate.WellFormed])]
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [compile, expectation_literals, Catalyst.replacement_correct q g hf.1 psi hp,
        expectation, TemplateGate.instantiate, Quantum.run_singleton]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using frame_gate q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    | whenBit r v g =>
      simp only [compile, expectation, TemplateGate.instantiate]
      split
      · simp only [Quantum.run_singleton, Catalyst.prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using frame_gate q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
      · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | recordGate i v g p ih =>
    simp only [compile, expectation_records, expectation]
    by_cases h : history i = v
    · simp only [if_pos h, Quantum.run_singleton]
      rw [inverseReplacement_correct q g hf.1 psi hp]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using frame_gate q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    · simp only [if_neg h, Quantum.run_nil]
      exact ih history psi accept hf.2 hp
  | measure w p ih =>
    simp only [compile, expectation, Catalyst.prepare_reset q w hf.1]
    rw [ih _ _ accept hf.2 (frame_reset q w hf.1 false psi hp),
      ih _ _ accept hf.2 (frame_reset q w hf.1 true psi hp)]

theorem inverseReplacement_t (q : Wire) (g : Gate) :
    ShorECDLP.tCount (inverseReplacement q g) + inverseSavedGate g = tCost g := by
  unfold inverseReplacement inverseSavedGate
  split
  · rfl
  · rename_i g h
    cases g <;> simp_all [tCount, tCost]

theorem inverseSavedGate_le (g : Gate) : inverseSavedGate g ≤ 1 := by
  unfold inverseSavedGate
  split <;> simp

theorem inverseSavedGate_cost (g : Gate) (h : inverseSavedGate g = 1) : tCost g = 1 := by
  revert h
  unfold inverseSavedGate
  split <;> simp [tCost]

theorem savedGate_le (g : Gate) : Catalyst.savedGate g ≤ 1 := by
  unfold Catalyst.savedGate
  split <;> simp

theorem records_t {n s e} (i : Fin s) (v : Bool) (gs : Circuit) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((records i v gs p).instantiate read history).tCount =
      (if history i = v then ShorECDLP.tCount gs else 0) + (p.instantiate read history).tCount := by
  induction gs with
  | nil => by_cases h : history i = v <;> simp [records, h, ShorECDLP.tCount]
  | cons g gs ih =>
    simp only [records] at ih ⊢
    simp only [List.foldr_cons, Straight.instantiate, AdaptiveCircuit.tCount, ih]
    by_cases h : history i = v
    · simp only [if_pos h, ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
    · simp [if_neg h, ShorECDLP.tCount]

theorem compile_t {n s e} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((compile q p).instantiate read history).tCount + Catalyst.saved p =
      ((drop p).instantiate read history).tCount := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [compile, drop, Catalyst.literals_t, Catalyst.saved, Straight.instantiate,
        TemplateGate.instantiate, AdaptiveCircuit.tCount, tCount, List.sum_cons, List.map_cons,
        List.map_nil, List.sum_nil]
      have h := Catalyst.replacement_t q g
      simp only [ShorECDLP.tCount] at h
      have hi := ih history
      omega
    | whenBit r v g =>
      simp only [compile, drop, Catalyst.saved, Straight.instantiate, TemplateGate.instantiate,
        AdaptiveCircuit.tCount]
      have hi := ih history
      omega
  | recordGate i v g p ih =>
    have hi := ih history
    have hr := inverseReplacement_t q g
    simp only [compile, records_t, Catalyst.saved]
    by_cases hg : inverseSavedGate g = 1
    · have hc := inverseSavedGate_cost g hg
      simp only [drop, if_pos hg]
      have h0 : ShorECDLP.tCount (inverseReplacement q g) = 0 := by omega
      rw [h0]
      split <;> omega
    · have h0 : inverseSavedGate g = 0 := by have := inverseSavedGate_le g; omega
      simp only [drop, if_neg hg, Straight.instantiate, AdaptiveCircuit.tCount]
      rw [h0] at hr
      by_cases h : history i = v
      · simp only [if_pos h, ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil] at hr ⊢
        omega
      · simp only [if_neg h, ShorECDLP.tCount, List.map_nil, List.sum_nil]
        omega
  | measure w p ih =>
    simp only [compile, drop, Catalyst.saved, Straight.instantiate, AdaptiveCircuit.tCount]
    have h0 := ih (Fin.lastCases false history)
    have h1 := ih (Fin.lastCases true history)
    omega

theorem inverseReplacement_wellFormed (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (hg : Gate.WellFormed g) : CircuitWellFormed (inverseReplacement q g) := by
  unfold inverseReplacement
  split
  · rename_i t
    have ht : t ≠ q := by simpa [gateWires, ne_comm] using hq
    simp [unkick, controlledZ, CircuitWellFormed, Gate.WellFormed, ht]
  · simpa [CircuitWellFormed] using hg

theorem records_wellFormed {n s e : Nat} (i : Fin s) (v : Bool) (gs : Circuit)
    (p : Straight n s e) (hg : CircuitWellFormed gs) (hp : p.WellFormed) :
    (records i v gs p).WellFormed := by
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
    | literal g =>
      exact Catalyst.literals_wellFormed _ _ (Catalyst.replacement_wellFormed q g hf.1 hp.1)
        (ih hf.2 hp.2)
    | whenBit => exact ⟨hp.1, ih hf.2 hp.2⟩
  | recordGate i v g p ih =>
    exact records_wellFormed _ _ _ _ (inverseReplacement_wellFormed q g hf.1 hp.1) (ih hf.2 hp.2)
  | measure w p ih => exact ih hf.2 hp

theorem inverseReplacement_wires (q : Wire) (g : Gate) :
    circuitWires (inverseReplacement q g) ⊆ q :: gateWires g := by
  unfold inverseReplacement
  split
  · simp [unkick, controlledZ, circuitWires, gateWires, List.subset_def]
  · simp [circuitWires]

theorem records_within {n s e} (ws : List Wire) (i : Fin s) (v : Bool) (gs : Circuit)
    (p : Straight n s e) (hg : circuitWires gs ⊆ ws) (hp : Within ws p) :
    Within ws (records i v gs p) := by
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
      apply Catalyst.literals_within
      · exact (Catalyst.replacement_wires q g).trans (List.cons_subset_cons q hp.1)
      · exact ih hp.2
    | whenBit => exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), ih hp.2⟩
  | recordGate i v g p ih =>
    apply records_within
    · exact (inverseReplacement_wires q g).trans (List.cons_subset_cons q hp.1)
    · exact ih hp.2
  | measure => exact ⟨List.mem_cons_of_mem q hp.1, by apply_assumption; exact hp.2⟩

theorem inverseReplacement_length (q : Wire) (g : Gate) :
    (inverseReplacement q g).length = 1 + 3 * inverseSavedGate g := by
  unfold inverseReplacement inverseSavedGate
  split <;> rfl

theorem records_slots {n s e} (i : Fin s) (v : Bool) (gs : Circuit) (p : Straight n s e) :
    (records i v gs p).gateSlots = gs.length + p.gateSlots := by
  induction gs with
  | nil => simp [records]
  | cons g gs ih =>
    simp only [records] at ih ⊢
    simp only [List.foldr_cons, Straight.gateSlots, ih, List.length_cons]
    omega

theorem compile_slots_le {n s e} (q : Wire) (p : Straight n s e) :
    (compile q p).gateSlots ≤ 4 * p.gateSlots := by
  induction p with
  | done => simp [compile, Straight.gateSlots]
  | gate g p ih =>
    cases g with
    | literal g =>
      have h := savedGate_le g
      simp only [compile, literals_slots, Catalyst.replacement_length, Straight.gateSlots]
      omega
    | whenBit r v g =>
      simp only [compile, Straight.gateSlots]
      omega
  | recordGate i v g p ih =>
    have h := inverseSavedGate_le g
    simp only [compile, records_slots, inverseReplacement_length, Straight.gateSlots]
    omega
  | measure w p ih => simpa only [compile, Straight.gateSlots] using ih

def compileEntry (q : Wire) (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := entry.finalCursor
  program := literals (Catalyst.prepare q) (compile q entry.program)

theorem compile_verified {n e} (q : Wire) (p : Straight n 0 e)
    (read : ConstantBit n → Bool) (layout : DecodeLayout) (Q : Secp256k1.Point)
    (psi : State) (hf : Fresh q p) (hp : SupportedOn (fun s => s q = false) psi) :
    Instrument.bornMass (((literals (Catalyst.prepare q) (compile q p)).instantiate read
      Fin.elim0).run.filter (fun b => (verifiedCandidate layout Q b.history).isSome)) psi =
    Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [← expectation_verified, ← expectation_verified, expectation_literals]
  exact compile_expectation q p read Fin.elim0 psi _ hf hp

theorem compileEntry_within (q : Wire) (entry : StraightEntry) (ws : List Wire)
    (hp : Within ws entry.program) : Within (q::ws) (compileEntry q entry).program := by
  apply Catalyst.literals_within
  · simp [Catalyst.prepare, circuitWires, gateWires, List.subset_def]
  · exact compile_within q entry.program ws hp

theorem compile_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds newBounds : Bounds) (q : Wire) (ws : List Wire)
    (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hq : q ∉ ws)
    (hslots : 4 * entry.program.gateSlots + 2 ≤ limits.gateSlots)
    (hqubits : ws.length + 1 ≤ newBounds.qubits)
    (ht : ∀ Q, ((drop entry.program).instantiate (readConstant entry.coefficients.get Q)
      Fin.elim0).tCount + 1 ≤ newBounds.tModel + Catalyst.saved entry.program)
    (hm : entry.finalCursor ≤ newBounds.measurements) :
    Certificate limits layout (compileEntry q entry) newBounds where
  gateBudget := by
    have h := compile_slots_le q entry.program
    change (literals (Catalyst.prepare q) (compile q entry.program)).gateSlots ≤ limits.gateSlots
    rw [literals_slots]
    simp only [Catalyst.prepare, List.length_cons, List.length_nil]
    omega
  recordBudget := cert.recordBudget
  tableBudget := cert.tableBudget
  candidateBudget := cert.candidateBudget
  wellFormed := Catalyst.literals_wellFormed _ _
    (by simp [Catalyst.prepare, CircuitWellFormed, Gate.WellFormed])
    (compile_wellFormed q entry.program (hs.fresh q hq) cert.wellFormed)
  resources := by
    intro Q
    have hsup := (compileEntry_within q entry ws hs).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((compileEntry q entry).instantiate Q).wires.dedup.toFinset).card ≤
        (q :: ws).length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (q :: ws))
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((compileEntry q entry).instantiate Q).qubitCount ≤ newBounds.qubits := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc.trans hqubits
    have htc := compile_t q entry.program (readConstant entry.coefficients.get Q) Fin.elim0
    have hto := ht Q
    have hmc := (compileEntry q entry).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    refine ⟨hqc, ?_, ?_⟩
    · change ((literals (Catalyst.prepare q) (compile q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      rw [Catalyst.literals_t]
      change 1 + ((compile q entry.program).instantiate (readConstant entry.coefficients.get Q)
        Fin.elim0).tCount ≤ newBounds.tModel
      omega
    · change ((compileEntry q entry).program.instantiate (readConstant entry.coefficients.get Q)
        Fin.elim0).measurementCount ≤ newBounds.measurements
      have he : ((compileEntry q entry).program.instantiate (readConstant entry.coefficients.get Q)
          Fin.elim0).measurementCount = entry.finalCursor := by
        simpa only [Nat.add_zero] using hmc
      exact he.le.trans hm
  success := by
    intro Q d hn hd
    change 99 / 100 ≤ Instrument.bornMass
      (((literals (Catalyst.prepare q) (compile q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState)
    rw [compile_verified q entry.program _ layout Q _ (hs.fresh q hq)
      (supportedOn_ket _ _ rfl)]
    exact cert.success Q d hn hd


theorem drop_t_le {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    ((drop p).instantiate read history).tCount ≤ (p.instantiate read history).tCount := by
  induction p with
  | done => exact Nat.le_refl 0
  | gate g p ih =>
    simp only [drop, Straight.instantiate, AdaptiveCircuit.tCount]
    have := ih history
    omega
  | recordGate i v g p ih =>
    have := ih history
    by_cases hg : inverseSavedGate g = 1
    · simp only [drop, if_pos hg, Straight.instantiate, AdaptiveCircuit.tCount]
      omega
    · simp only [drop, if_neg hg, Straight.instantiate, AdaptiveCircuit.tCount]
      omega
  | measure w p ih =>
    simp only [drop, Straight.instantiate, AdaptiveCircuit.tCount]
    have h0 := ih (Fin.lastCases false history)
    have h1 := ih (Fin.lastCases true history)
    omega

theorem drop_append {n a b c} (p : Straight n a b) (q : Straight n b c) :
    drop (p.append q) = (drop p).append (drop q) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [Straight.append, drop, ih]
  | recordGate i v g p ih =>
    by_cases hg : inverseSavedGate g = 1
    · simp only [Straight.append, drop, if_pos hg, ih]
    · simp only [Straight.append, drop, if_neg hg, ih]
  | measure w p ih => simp only [Straight.append, drop, ih]

theorem drop_castFinish {n s e f} (h : e = f) (p : Straight n s e) :
    drop (ChallengeMigration.castFinish h p) = ChallengeMigration.castFinish h (drop p) := by
  subst f
  rfl

theorem drop_reindex {n m s e} (f : Fin n → Fin m) (p : Straight n s e) :
    drop (ChallengeMigration.reindexStraight f p) = ChallengeMigration.reindexStraight f (drop p) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [ChallengeMigration.reindexStraight, drop, ih]
  | recordGate i v g p ih =>
    by_cases hg : inverseSavedGate g = 1
    · simp only [ChallengeMigration.reindexStraight, drop, if_pos hg, ih]
    · simp only [ChallengeMigration.reindexStraight, drop, if_neg hg, ih]
  | measure w p ih => simp only [ChallengeMigration.reindexStraight, drop, ih]

theorem drop_literals {n s e} (gs : Circuit) (p : Straight n s e) :
    drop (literals gs p) = literals gs (drop p) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [literals] at ih ⊢
    simp only [List.foldr_cons, drop, ih]

theorem drop_prepareOuterBank {n s e} (ws : List Wire) (p : Straight n s e) :
    drop (ChallengeMigration.prepareOuterBank ws p) = ChallengeMigration.prepareOuterBank ws (drop p) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [ChallengeMigration.prepareOuterBank] at ih ⊢
    simp only [List.foldr_cons, drop, ih]

theorem drop_toffoliPrefix {n s e} (a b t q : Wire) (p : Straight n (s+1) e) :
    drop (toffoliPrefix a b t q p) = toffoliPrefix a b t q (drop p) := by
  simp [toffoliPrefix, drop_literals, drop, inverseSavedGate]

theorem drop_lower_t {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (newHistory : Fin start → Bool)
    (hmap : newHistory ∘ records = history) :
    ((drop (lower q p start records).program).instantiate read newHistory).tCount + 2 * added p =
      ((drop p).instantiate read history).tCount := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hm (outcome : Bool) :
                  (Fin.lastCases outcome newHistory) ∘ (fun i => (records i).castSucc) = history := by
                simpa only [Function.comp_def, Fin.lastCases_castSucc] using hmap
              have h0 := ih (start+1) (fun i => (records i).castSucc) history
                (Fin.lastCases false newHistory) (hm false)
              have h1 := ih (start+1) (fun i => (records i).castSucc) history
                (Fin.lastCases true newHistory) (hm true)
              simp only [lower, drop_toffoliPrefix, drop, toffoliPrefix_t, added, Straight.instantiate,
                TemplateGate.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tCost] at *
              omega
          | X t | H t | CX a t | P dir k t =>
              have h := ih start records history newHistory hmap
              simp only [lower, drop, added, Straight.instantiate, TemplateGate.instantiate,
                AdaptiveCircuit.tCount] at *
              omega
      | whenBit r v g =>
          have h := ih start records history newHistory hmap
          simp only [lower, drop, added, Straight.instantiate, AdaptiveCircuit.tCount] at *
          omega
  | recordGate i v g p ih =>
      have h := ih start records history newHistory hmap
      have hm : newHistory (records i) = history i := congrFun hmap i
      by_cases hg : inverseSavedGate g = 1
      · simp only [lower, drop, if_pos hg, added] at *
        omega
      · simp only [lower, drop, if_neg hg, added, Straight.instantiate, AdaptiveCircuit.tCount,
          hm] at *
        omega
  | measure w p ih =>
      have hm (outcome : Bool) : (Fin.lastCases outcome newHistory) ∘
          (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) =
          Fin.lastCases outcome history := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        all_goals simp [Function.comp_def, ← hmap]
      have h0 := ih (start+1) _ (Fin.lastCases false history) (Fin.lastCases false newHistory) (hm false)
      have h1 := ih (start+1) _ (Fin.lastCases true history) (Fin.lastCases true newHistory) (hm true)
      simp only [lower, drop, added, Straight.instantiate, AdaptiveCircuit.tCount] at *
      omega


def dropSlots : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, prior => (prior - 1) + dropSlots k (prior+1)

theorem drop_feedback_t_le {n s e : Nat} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((drop (ChallengeMigration.feedbackProgram dir w indices k p)).instantiate read history).tCount ≤
      indices.length + ((drop p).instantiate read history).tCount := by
  induction indices generalizing k with
  | nil => simp [ChallengeMigration.feedbackProgram]
  | cons i is ih =>
    have h := ih (k+1)
    by_cases hg : inverseSavedGate (.P dir k w) = 1
    · simp only [ChallengeMigration.feedbackProgram, drop, if_pos hg, List.length_cons]
      omega
    · simp only [ChallengeMigration.feedbackProgram, drop, if_neg hg, Straight.instantiate,
        AdaptiveCircuit.tCount, List.length_cons]
      have hcost : ShorECDLP.tCount (if history i = true then [.P dir k w] else []) ≤ 1 := by
        split <;> simp [ShorECDLP.tCount, tCost]
      omega

theorem drop_feedback_two {n s e : Nat} (w : Wire) (indices : List (Fin s))
    (p : Straight n s e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((drop (ChallengeMigration.feedbackProgram .inverse w indices 2 p)).instantiate read
      history).tCount ≤ (indices.length - 1) + ((drop p).instantiate read history).tCount := by
  cases indices with
  | nil => simp [ChallengeMigration.feedbackProgram]
  | cons i is =>
    have h := drop_feedback_t_le .inverse w is 3 p read history
    have hg : inverseSavedGate (.P .inverse 2 w) = 1 := rfl
    have he : drop (ChallengeMigration.feedbackProgram .inverse w (i :: is) 2 p) =
        drop (ChallengeMigration.feedbackProgram .inverse w is 3 p) := by
      simp only [ChallengeMigration.feedbackProgram, drop, if_pos hg]
    rw [he]
    simp only [List.length_cons]
    omega

theorem drop_fourier_t_le (n : Nat) (ws : List Wire) (start : Nat)
    (prior : List (Fin start)) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((drop (ChallengeMigration.fourierProgram n .inverse ws start prior)).instantiate read
      history).tCount ≤ dropSlots ws.length prior.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [ChallengeMigration.fourierProgram, drop_castFinish,
      ChallengeMigration.castFinish_instantiate]
    apply (drop_feedback_two _ _ _ _ _).trans
    have hf := ih (start+1) (Fin.last start :: prior.map Fin.castSucc) (Fin.lastCases false history)
    have ht := ih (start+1) (Fin.last start :: prior.map Fin.castSucc) (Fin.lastCases true history)
    simp only [drop, Straight.instantiate, AdaptiveCircuit.tCount, List.length_cons,
      List.length_map] at *
    simp only [dropSlots]
    omega

end
end ShorECDLP.Entrant.CatalystS
end


section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.CatalystS
noncomputable section
set_option linter.unusedSimpArgs false

def metadataDT : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (cost, width) :: ws, prior =>
      cost + dropSlots width prior + metadataDT ws (prior + width)

theorem axis_dt {n : Nat} (ws : List (Window n)) (read : ConstantBit n → Bool)
    (costs : List (Nat × Nat))
    (hw : List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ c.1) ws costs)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((drop (axis ws start prior)).instantiate read history).tCount ≤
      metadataDT costs prior.length := by
  induction ws generalizing costs start with
  | nil => cases hw; simp [axis, drop, metadataDT, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons w ws ih =>
    cases hw with
    | cons head tail =>
      rename_i c costs
      simp only [axis, drop_castFinish, castFinish_instantiate, drop_append, drop_prepareOuterBank]
      apply (outer_append_t_le _ _ read history
        (dropSlots w.wires.length prior.length +
          metadataDT costs (prior.length+w.wires.length)) ?_).trans
      · simp only [prepareOuterBank_t, metadataDT]
        have h := (drop_t_le _ read history).trans (head.2 start history)
        rw [head.1]
        omega
      · intro h
        apply (outer_append_t_le _ _ read h
          (metadataDT costs (prior.length+w.wires.length)) ?_).trans
        · have hf := drop_fourier_t_le n w.wires (start+w.count)
            (bankPrior w.count prior) read h
          simp only [bankPrior_length] at hf
          simp only [drop_castFinish, castFinish_instantiate]
          omega
        · intro h₂
          simpa [nextPrior, Nat.add_comm] using ih costs tail _
            (nextPrior w.count w.wires.length prior) h₂

theorem drop_framed {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    drop (framed p q r h) = framed (drop p) (drop q) (drop r) h := by
  unfold framed
  simp only [drop, drop_castFinish, drop_append]

theorem drop_fixedEntry_instantiate {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (Q : Secp256k1.Point) :
    (drop (fixedEntry f p).program).instantiate (readConstant (fixedEntry f p).coefficients.get Q)
      Fin.elim0 = (drop p).instantiate (readConstant f Q) Fin.elim0 := by
  have h : (fixedEntry f (drop p)).instantiate Q = (drop p).instantiate (readConstant f Q) Fin.elim0 := by
    dsimp only [fixedEntry, StraightEntry.instantiate]
    rw [reindexStraight_instantiate]
    simp only [Function.comp_def, reindexBit]
    congr 1
    funext r
    simp only [readConstant, List.get_eq_getElem, List.getElem_ofFn, Fin.val_cast, Fin.eta]
  dsimp only [fixedEntry, StraightEntry.instantiate] at h ⊢
  rw [drop_reindex]
  exact h

end
end ShorECDLP.Entrant.Single
end
