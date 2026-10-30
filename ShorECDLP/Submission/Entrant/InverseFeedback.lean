import ShorECDLP.Submission.Entrant.Base
namespace ShorECDLP.Entrant.InverseKick
open Quantum Paper2607_13816 Catalyst
noncomputable section
set_option maxHeartbeats 30000
set_option maxRecDepth 10000
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

def kickInv (t q : Wire) : Circuit := kick t q ++ pauliZ t
private theorem phase_forward : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring
private theorem phase_inverse : phaseCoeff .inverse 2 = -Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_neg_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring
private theorem upd_twice (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]
theorem z_prepare (t q : Wire) (ht : t ≠ q) (psi : State) :
    Quantum.run (pauliZ t) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (Quantum.run (pauliZ t) psi) := by
  simp only [pauliZ, Quantum.run_cons, Quantum.run_nil]
  rw [prepare_gate q (.H t) (by simpa [gateWires, ne_comm] using ht)]
  rw [prepare_gate q (.X t) (by simpa [gateWires, ne_comm] using ht)]
  rw [prepare_gate q (.H t) (by simpa [gateWires, ne_comm] using ht)]

theorem kick_ket (t q : Wire) (ht : t ≠ q) (s : BasisState) (hq : s q = false) :
    Quantum.run (kickInv t q) (Quantum.run (prepare q) (ket s)) =
      Quantum.run (prepare q) (applyGate (.P .inverse 2 t) (ket s)) := by
  rw [kickInv, Quantum.run_append, Catalyst.kick_ket t q ht s hq, z_prepare t q ht]
  simp only [applyGate_P_ket, phase_forward, phase_inverse, map_smul, run_pauliZ_ket]
  cases s t <;> simp
theorem kick_supported (t q : Wire) (ht : t ≠ q) (psi : State)
    (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (kickInv t q) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (applyGate (.P .inverse 2 t) psi) :=
  linear_comp_supported (Quantum.run (kickInv t q)) (Quantum.run (prepare q))
    (Quantum.run (prepare q)) (applyGate (.P .inverse 2 t)) _
    (kick_ket t q ht) psi hp
open Challenge AndGadget Paper2607_13816.ChallengeMigration

theorem expectation_recordGates {n s e : Nat} (read : ConstantBit n → Bool)
    (i : Fin s) (gs : Circuit) (p : Straight n s e) (history : Fin s → Bool)
    (psi : State) (accept : (Fin e → Bool) → Bool) :
    expectation read (recordGates i gs p) history psi accept =
      expectation read p history (Quantum.run (if history i then gs else []) psi) accept := by
  induction gs generalizing psi with
  | nil => simp [recordGates]
  | cons g gs ih =>
    cases h : history i <;>
      simp [recordGates, expectation, h, Quantum.run_cons, ih]

theorem conditional_kick {n s e : Nat} (read : ConstantBit n → Bool)
    (i : Fin s) (t q : Wire) (ht : t ≠ q) (p : Straight n s e)
    (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool)
    (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (recordGates i (kickInv t q) p) history (Quantum.run (prepare q) psi) accept =
      expectation read p history (Quantum.run (prepare q)
        (Quantum.run (if history i then [.P .inverse 2 t] else []) psi)) accept := by
  rw [expectation_recordGates]
  cases history i <;> simp [kick_supported t q ht psi hp]

def recordReplacement (q : Wire) : Gate → Circuit
  | .P .inverse 2 t => kickInv t q
  | g => [g]

theorem recordReplacement_correct (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (psi : State) (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (recordReplacement q g) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (applyGate g psi) := by
  unfold recordReplacement
  split
  · rename_i t
    exact kick_supported t q (by simpa [gateWires, ne_comm] using hq) psi hp
  · simpa only [Quantum.run_singleton] using prepare_gate q g hq psi

def compileRecord (q : Wire) : {n s e : Nat} → Straight n s e → Straight n s e
  | _, _, _, .done => .done
  | _, _, _, .gate g p => .gate g (compileRecord q p)
  | _, _, _, .recordGate i true g p => recordGates i (recordReplacement q g) (compileRecord q p)
  | _, _, _, .recordGate i false g p => .recordGate i false g (compileRecord q p)
  | _, _, _, .measure w p => .measure w (compileRecord q p)

private theorem gate_frame (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (psi : State) (hp : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (applyGate g psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary [g] .done) q false
    (by simpa [AdaptiveCircuit.wires, circuitWires] using hq)
    ⟨[], Quantum.run [g]⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hp
  simpa only [Quantum.run_singleton] using h

private theorem reset_frame (q w : Wire) (hq : q ≠ w) (outcome : Bool)
    (psi : State) (hp : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (xResetKraus w outcome psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[outcome], xResetKraus w outcome⟩ ?_ psi hp
  cases outcome <;>
    simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_append, List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem recordTrue {n s e : Nat} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (i : Fin s) (g : Gate)
    (ih : ∀ (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool),
      Fresh q p → SupportedOn (fun s => s q = false) psi →
      expectation read (compileRecord q p) history (Quantum.run (prepare q) psi) accept =
      expectation read p history psi accept)
    (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool)
    (hf : Fresh q (.recordGate i true g p))
    (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (compileRecord q (.recordGate i true g p)) history (Quantum.run (prepare q) psi) accept =
      expectation read (.recordGate i true g p) history psi accept := by
  rw [compileRecord, expectation_recordGates]
  simp only [expectation]
  cases h : history i
  · simpa only [h, Bool.false_eq_true, if_false, Quantum.run_nil] using ih history psi accept hf.2 hp
  · simp only [if_true, Quantum.run_singleton, recordReplacement_correct q g hf.1 psi hp]
    exact ih history _ accept hf.2 (gate_frame q g hf.1 psi hp)

theorem compileRecord_expectation {n s e : Nat} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hf : Fresh q p)
    (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (compileRecord q p) history (Quantum.run (prepare q) psi) accept =
      expectation read p history psi accept := by
  induction p generalizing psi with
  | done =>
    simp only [compileRecord, expectation, normSq_run (prepare q) (by simp [prepare, CircuitWellFormed, Gate.WellFormed])]
  | gate g p ih =>
    cases g with
    | literal g =>
      rw [compileRecord, expectation, expectation]
      simp only [TemplateGate.instantiate, Quantum.run_singleton]
      rw [prepare_gate q g hf.1]
      exact ih history _ accept hf.2 (gate_frame q g hf.1 psi hp)
    | whenBit r v g =>
      simp only [compileRecord, expectation, TemplateGate.instantiate]
      split
      · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (gate_frame q g hf.1 psi hp)
      · simpa only [Quantum.run_nil] using ih history psi accept hf.2 hp
  | recordGate i v g p ih =>
    cases v with
    | false =>
      simp only [compileRecord, expectation]
      split
      · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (gate_frame q g hf.1 psi hp)
      · simpa only [Quantum.run_nil] using ih history psi accept hf.2 hp
    | true => exact recordTrue q p read i g ih history psi accept hf hp
  | measure w p ih =>
    simp only [compileRecord, expectation, prepare_reset q w hf.1]
    rw [ih _ _ accept hf.2 (reset_frame q w hf.1 false psi hp), ih _ _ accept hf.2 (reset_frame q w hf.1 true psi hp)]
/-- Combine literal-S lowering with the record-controlled inverse-S lowering. -/
def compileAll (q : Wire) : {n s e : Nat} → Straight n s e → Straight n s e
  | _, _, _, .done => .done
  | _, _, _, .gate (.literal g) p => literals (replacement q g) (compileAll q p)
  | _, _, _, .gate (.whenBit r v g) p => .gate (.whenBit r v g) (compileAll q p)
  | _, _, _, .recordGate i true g p => recordGates i (recordReplacement q g) (compileAll q p)
  | _, _, _, .recordGate i false g p => .recordGate i false g (compileAll q p)
  | _, _, _, .measure w p => .measure w (compileAll q p)

theorem recordTrueAll {n s e : Nat} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (i : Fin s) (g : Gate)
    (ih : ∀ (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool),
      Fresh q p → SupportedOn (fun s => s q = false) psi →
      expectation read (compileAll q p) history (Quantum.run (prepare q) psi) accept =
      expectation read p history psi accept)
    (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool)
    (hf : Fresh q (.recordGate i true g p)) (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (compileAll q (.recordGate i true g p)) history (Quantum.run (prepare q) psi) accept =
      expectation read (.recordGate i true g p) history psi accept := by
  rw [compileAll, expectation_recordGates]
  simp only [expectation]
  cases h : history i
  · simpa only [h, Bool.false_eq_true, if_false, Quantum.run_nil] using ih history psi accept hf.2 hp
  · simp only [if_true, Quantum.run_singleton, recordReplacement_correct q g hf.1 psi hp]
    exact ih history _ accept hf.2 (gate_frame q g hf.1 psi hp)

theorem compileAll_expectation {n s e : Nat} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hf : Fresh q p)
    (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (compileAll q p) history (Quantum.run (prepare q) psi) accept =
      expectation read p history psi accept := by
  induction p generalizing psi with
  | done =>
    simp only [compileAll, expectation, normSq_run (prepare q) (by simp [prepare, CircuitWellFormed, Gate.WellFormed])]
  | gate g p ih =>
    cases g with
    | literal g =>
      rw [compileAll, expectation_literals, replacement_correct q g hf.1 psi hp, expectation]
      simp only [TemplateGate.instantiate, Quantum.run_singleton]
      exact ih history _ accept hf.2 (gate_frame q g hf.1 psi hp)
    | whenBit r v g =>
      simp only [compileAll, expectation, TemplateGate.instantiate]
      split
      · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (gate_frame q g hf.1 psi hp)
      · simpa only [Quantum.run_nil] using ih history psi accept hf.2 hp
  | recordGate i v g p ih =>
    cases v with
    | false =>
      simp only [compileAll, expectation]
      split
      · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (gate_frame q g hf.1 psi hp)
      · simpa only [Quantum.run_nil] using ih history psi accept hf.2 hp
    | true => exact recordTrueAll q p read i g ih history psi accept hf hp
  | measure w p ih =>
    simp only [compileAll, expectation, prepare_reset q w hf.1]
    rw [ih _ _ accept hf.2 (reset_frame q w hf.1 false psi hp), ih _ _ accept hf.2 (reset_frame q w hf.1 true psi hp)]

theorem recordReplacement_wellFormed (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (hg : Gate.WellFormed g) : CircuitWellFormed (recordReplacement q g) := by
  unfold recordReplacement
  split
  · rename_i t
    have ht : t ≠ q := by simpa [gateWires, ne_comm] using hq
    simp [kickInv, kick, pauliZ, controlledZ, CircuitWellFormed, Gate.WellFormed, ht]
  · simpa [CircuitWellFormed] using hg

theorem compileAll_wellFormed {n s e} (q : Wire) (p : Straight n s e)
    (hf : Fresh q p) (hp : p.WellFormed) : (compileAll q p).WellFormed := by
  induction p with
  | done => simp [compileAll, Straight.WellFormed]
  | gate g p ih =>
    cases g with
    | literal g => rw [compileAll]; exact Catalyst.literals_wellFormed _ _ (replacement_wellFormed q g hf.1 hp.1) (ih hf.2 hp.2)
    | whenBit => rw [compileAll]; exact ⟨hp.1, ih hf.2 hp.2⟩
  | recordGate i v g p ih =>
    cases v with
    | false => rw [compileAll]; exact ⟨hp.1, ih hf.2 hp.2⟩
    | true => rw [compileAll]; exact recordGates_wellFormed i _ _ (recordReplacement_wellFormed q g hf.1 hp.1) (ih hf.2 hp.2)
  | measure w p ih => rw [compileAll]; exact ih hf.2 hp

theorem recordReplacement_wires (q : Wire) (g : Gate) :
    circuitWires (recordReplacement q g) ⊆ q :: gateWires g := by
  unfold recordReplacement
  split
  · simp [kickInv, kick, pauliZ, controlledZ, circuitWires, gateWires, List.subset_def]
  · simp [circuitWires]

theorem recordGates_within {n s e} (i : Fin s) (ws : List Wire) (gs : Circuit) (p : Straight n s e)
    (hg : circuitWires gs ⊆ ws) (hp : Within ws p) : Within ws (recordGates i gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
    have h : gateWires g ⊆ ws ∧ circuitWires gs ⊆ ws := by simpa [circuitWires] using hg
    exact ⟨h.1, ih h.2⟩

theorem compileAll_within {n s e} (q : Wire) (p : Straight n s e) (ws : List Wire)
    (hp : Within ws p) : Within (q::ws) (compileAll q p) := by
  induction p with
  | done => simp [compileAll, Within]
  | gate g p ih =>
    cases g with
    | literal g => rw [compileAll]; exact literals_within _ _ _ ((replacement_wires q g).trans (List.cons_subset_cons q hp.1)) (ih hp.2)
    | whenBit => rw [compileAll]; exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), ih hp.2⟩
  | recordGate i v g p ih =>
    cases v with
    | false => rw [compileAll]; exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), ih hp.2⟩
    | true => rw [compileAll]; exact recordGates_within i _ _ _ ((recordReplacement_wires q g).trans (List.cons_subset_cons q hp.1)) (ih hp.2)
  | measure w p ih => rw [compileAll]; exact ⟨List.mem_cons_of_mem q hp.1, ih hp.2⟩

/-- Count each optional gate as if enabled, giving a history-independent upper bound. -/
def staticCost {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p => tCost g + staticCost p
  | .gate (.whenBit _ _ g) p => tCost g + staticCost p
  | .recordGate _ _ g p => tCost g + staticCost p
  | .measure _ p => staticCost p

def recordSavingGate : Gate → Nat
  | .P .inverse 2 _ => 1
  | _ => 0

def recordSaving {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate _ p => recordSaving p
  | .recordGate _ true g p => recordSavingGate g + recordSaving p
  | .recordGate _ false _ p => recordSaving p
  | .measure _ p => recordSaving p

theorem staticCost_eq {n s e} (p : Straight n s e) :
    staticCost p = 7 * added p + residue p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp [staticCost, added, residue, tCost, primitivePhaseCost, ih] <;> omega
    | whenBit => simp [staticCost, added, residue, ih]; omega
  | recordGate => simp [staticCost, added, residue, *]; omega
  | measure => simp [staticCost, added, residue, *]

theorem staticCost_literals {n s e} (gs : Circuit) (p : Straight n s e) :
    staticCost (literals gs p) = ShorECDLP.tCount gs + staticCost p := by
  induction gs with
  | nil => simp [literals, ShorECDLP.tCount]
  | cons g gs ih =>
    rw [show literals (g :: gs) p = .gate (.literal g) (literals gs p) by rfl]
    simp [staticCost, ShorECDLP.tCount, ih, Nat.add_assoc]

theorem staticCost_recordGates {n s e} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    staticCost (recordGates i gs p) = ShorECDLP.tCount gs + staticCost p := by
  induction gs with
  | nil => simp [recordGates, ShorECDLP.tCount]
  | cons g gs ih => simp [recordGates, staticCost, ShorECDLP.tCount, ih, Nat.add_assoc]

theorem recordReplacement_t (q : Wire) (g : Gate) :
    ShorECDLP.tCount (recordReplacement q g) + recordSavingGate g = tCost g := by
  unfold recordReplacement recordSavingGate
  split
  · simp [kickInv, kick, pauliZ, controlledZ, ShorECDLP.tCount, tCost]
  · rename_i g h
    cases g <;> simp_all [ShorECDLP.tCount, tCost]

theorem compileAll_static {n s e} (q : Wire) (p : Straight n s e) :
    staticCost (compileAll q p) + Catalyst.saved p + recordSaving p = staticCost p := by
  induction p with
  | done => simp [compileAll, staticCost, Catalyst.saved, recordSaving]
  | gate g p ih =>
    cases g with
    | literal g =>
      rw [compileAll, staticCost_literals]
      have hg := replacement_t q g
      simp only [Catalyst.saved, recordSaving, staticCost]
      omega
    | whenBit =>
      rw [compileAll]
      simp only [staticCost, Catalyst.saved, recordSaving]
      omega
  | recordGate i v g p ih =>
    cases v with
    | false =>
      rw [compileAll]
      simp only [staticCost, Catalyst.saved, recordSaving]
      omega
    | true =>
      rw [compileAll, staticCost_recordGates]
      have hg := recordReplacement_t q g
      simp only [staticCost, Catalyst.saved, recordSaving]
      omega
  | measure w p ih =>
    rw [compileAll]
    simp only [staticCost, Catalyst.saved, recordSaving]
    exact ih

theorem recordSaving_literals {n s e} (gs : Circuit) (p : Straight n s e) :
    recordSaving (literals gs p) = recordSaving p := by
  induction gs with
  | nil => simp [literals]
  | cons g gs ih =>
    rw [show literals (g :: gs) p = .gate (.literal g) (literals gs p) by rfl]
    simpa [recordSaving] using ih

theorem staticCost_toffoliPrefix {n s e} (a b t q : Wire) (p : Straight n (s+1) e) :
    staticCost (toffoliPrefix a b t q p) = 5 + staticCost p := by
  simp [toffoliPrefix, staticCost_literals, staticCost, andCompute, parityPhase, xorPhase,
    ShorECDLP.tCount, tCost]

theorem recordSaving_toffoliPrefix {n s e} (a b t q : Wire) (p : Straight n (s+1) e) :
    recordSaving (toffoliPrefix a b t q p) = recordSaving p := by
  simp [toffoliPrefix, recordSaving_literals, recordSaving, recordSavingGate]

theorem staticCost_lower {n s e} (q : Wire) (p : Straight n s e) (start : Nat)
    (records : Fin s → Fin start) :
    staticCost (lower q p start records).program + 2 * added p = staticCost p := by
  induction p generalizing start with
  | done => simp [lower, staticCost, added]
  | gate g p ih =>
    cases g with
    | literal g =>
      cases g with
      | CCX a b t =>
        have h := ih (start+1) (fun i => (records i).castSucc)
        simp only [lower, staticCost, added, staticCost_toffoliPrefix, tCost] at *
        omega
      | X t | H t | CX a t | P dir k t =>
        have h := ih start records
        simp only [lower, staticCost, added] at *
        omega
    | whenBit r v g =>
      have h := ih start records
      simp only [lower, staticCost, added] at *
      omega
  | recordGate i v g p ih =>
    have h := ih start records
    simp only [lower, staticCost, added] at *
    omega
  | measure w p ih =>
    have h := ih (start+1) (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc))
    simpa only [lower, staticCost, added] using h

theorem recordSaving_lower {n s e} (q : Wire) (p : Straight n s e) (start : Nat)
    (records : Fin s → Fin start) :
    recordSaving (lower q p start records).program = recordSaving p := by
  induction p generalizing start with
  | done => simp [lower, recordSaving]
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp [lower, recordSaving, recordSaving_toffoliPrefix, ih]
    | whenBit => simp [lower, recordSaving, ih]
  | recordGate i v g p ih => cases v <;> simp [lower, recordSaving, ih]
  | measure => simp [lower, recordSaving, *]

theorem added_t_lower {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) : 7 * added p ≤ (p.instantiate read history).tCount := by
  induction p with
  | done => simp [added, Straight.instantiate, AdaptiveCircuit.tCount]
  | gate g p ih =>
    have h := ih history
    cases g with
    | literal g => cases g <;>
      simp only [added, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
        ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tCost] at * <;> omega
    | whenBit r v g =>
      simp only [added, Straight.instantiate, AdaptiveCircuit.tCount] at *
      omega
  | recordGate i v g p ih =>
    have h := ih history
    simp only [added, Straight.instantiate, AdaptiveCircuit.tCount] at *
    omega
  | measure w p ih =>
    have h0 := ih (Fin.lastCases false history)
    have h1 := ih (Fin.lastCases true history)
    simp only [added, Straight.instantiate, AdaptiveCircuit.tCount] at *
    omega

theorem staticCost_zeroResidue {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (h : residue p = 0) :
    staticCost p = (p.instantiate read history).tCount := by
  have hl := added_t_lower p read history
  have hu := residue_t p read history
  rw [h, Nat.add_zero] at hu
  rw [staticCost_eq, h, Nat.add_zero]
  omega

theorem staticCost_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    staticCost (p.append q) = staticCost p + staticCost q := by
  simp only [staticCost_eq, added_append, residue_append]
  omega

theorem staticCost_cast {n s e f} (p : Straight n s e) (h : e = f) :
    staticCost (castFinish h p) = staticCost p := by subst f; rfl

theorem recordSaving_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    recordSaving (p.append q) = recordSaving p + recordSaving q := by
  induction p with
  | done => simp [Straight.append, recordSaving]
  | gate g p ih => simp [Straight.append, recordSaving, ih]
  | recordGate i v g p ih => cases v <;> simp [Straight.append, recordSaving, ih, Nat.add_assoc]
  | measure w p ih => simp [Straight.append, recordSaving, ih]

theorem recordSaving_cast {n s e f} (p : Straight n s e) (h : e = f) :
    recordSaving (castFinish h p) = recordSaving p := by subst f; rfl

theorem staticCost_feedback {n s e} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    staticCost (feedbackProgram dir w indices k p) = indices.length + staticCost p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih => simp [feedbackProgram, staticCost, tCost, ih, Nat.add_assoc, Nat.add_left_comm]

theorem staticCost_fourier (n : Nat) (dir : PhaseDir) (ws : List Wire) (start : Nat)
    (prior : List (Fin start)) :
    staticCost (fourierProgram n dir ws start prior) = fourierSlots ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [fourierProgram, staticCost, fourierSlots]
  | cons w ws ih =>
    simp only [fourierProgram, staticCost_cast, staticCost_feedback, staticCost, ih,
      List.length_cons, List.length_map, fourierSlots]

theorem staticCost_prepare {n s e} (ws : List Wire) (p : Straight n s e) :
    staticCost (prepareOuterBank ws p) = staticCost p := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [show prepareOuterBank (w :: ws) p = .gate (.literal (.H w)) (prepareOuterBank ws p) by rfl]
    simpa [staticCost, tCost] using ih

theorem staticCost_axis {n} (ws : List (Single.Window n)) (start : Nat) (prior : List (Fin start))
    (hw : ∀ w ∈ ws, ∀ start, staticCost (w.program start) ≤ Single.bodyT w.count) :
    staticCost (Single.axis ws start prior) ≤
      Single.metadataT (ws.map (fun w => (w.count, w.wires.length))) prior.length := by
  induction ws generalizing start with
  | nil => simp [Single.axis, Single.metadataT, staticCost]
  | cons w ws ih =>
    simp only [Single.axis, staticCost_cast, staticCost_append, staticCost_prepare,
      staticCost_fourier, bankPrior_length, List.map_cons, Single.metadataT]
    have h := hw w (by simp) start
    have ht := ih _ (Single.nextPrior w.count w.wires.length prior)
      (fun v hv => hw v (List.mem_cons_of_mem w hv))
    simp only [Single.nextPrior_length] at ht
    omega

theorem staticCost_window (w : Single.Window 851968)
    (hw : w ∈ Single.leftWindows ++ Single.rightWindows) (start : Nat) :
    staticCost (w.program start) ≤ Single.bodyT w.count := by
  have hz : residue (w.program start) = 0 := by
    rcases Single.windows_cases w hw with rfl | ⟨a, rfl⟩
    · exact FullCredit.residue_firstWindow start
    · exact FullCredit.residue_signedWindow a start
  rw [staticCost_zeroResidue (w.program start) (readConstant Single.mixedCoefficientAt 0)
    (fun _ => false) hz]
  exact Single.windows_t 0 w hw start _

theorem staticCost_reset (n start : Nat) (ws : List Wire) :
    staticCost (resetProgram n start ws) = 0 := by
  induction ws generalizing start with
  | nil => simp [resetProgram, staticCost]
  | cons w ws ih => simp [resetProgram, staticCost_cast, staticCost, ih]

theorem staticCost_framed {n s m k e f} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    staticCost (Single.framed p q r h) = staticCost p + staticCost q + staticCost r := by
  unfold Single.framed
  simp [staticCost, staticCost_cast, staticCost_append, tCost, Nat.add_assoc]

theorem staticCost_trial (start : Nat) : staticCost (Single.trial start) ≤ 14640353215 := by
  have hl := staticCost_axis Single.leftWindows start List.nil
    (fun w hw => staticCost_window w (List.mem_append_left _ hw))
  have hr := staticCost_axis Single.rightWindows (start + Single.axisCount Single.leftWindows) List.nil
    (fun w hw => staticCost_window w (List.mem_append_right _ hw))
  simp only [List.length_nil] at hl hr
  rw [Single.left_metadata, Single.left_t_budget] at hl
  rw [Single.right_metadata, Single.right_t_budget] at hr
  unfold Single.trial Single.resetBody
  rw [staticCost_framed, staticCost_cast, staticCost_reset]
  omega

theorem staticCost_program : staticCost Single.program ≤ 14640353215 := by
  unfold Single.program
  rw [staticCost_cast]
  exact staticCost_trial 0

open RoundedReadout NeighborReadout

theorem staticCost_addWord {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start)),
    staticCost (addWord (n := n) start carry bits) = 0
  | _, _, [] => by simp [addWord, staticCost]
  | start, carry, bit :: bits => by
    rw [addWord, staticCost_cast, staticCost_append]
    rw [staticCost_addWord (start+2) ⟨start, by omega⟩ (bits.map liftTwo)]
    simp [addStep, staticCost, tCost]
termination_by _ _ bits => bits.length

theorem staticCost_complementWord {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start)),
    staticCost (complementWord (n := n) start carry bits) = 0
  | _, _, [] => by simp [complementWord, staticCost]
  | start, carry, bit :: bits => by
    rw [complementWord, staticCost_cast, staticCost_append]
    rw [staticCost_complementWord (start+2) (liftTwo carry) (bits.map liftTwo)]
    simp [addStep, staticCost, tCost]
termination_by _ _ bits => bits.length

theorem staticCost_increment (n : Nat) {start width : Nat} (c : WordCursor start width) :
    staticCost (incrementStep n c) = 0 := by
  rw [incrementStep, staticCost_cast, staticCost_addWord]

theorem staticCost_complement (n : Nat) {start width : Nat} (c : WordCursor start width) :
    staticCost (complementStep n c) = 0 := by
  rw [complementStep, staticCost_cast, staticCost_complementWord]

theorem staticCost_positive (n : Nat) : ∀ (steps start width : Nat) (c : WordCursor start width),
    staticCost (positiveWords n steps start width c) = 0
  | 0, _, _, _ => by simp [positiveWords, staticCost_cast, staticCost]
  | steps+1, start, width, c => by
    rw [positiveWords, staticCost_cast, staticCost_append, staticCost_increment,
      staticCost_positive n steps]

theorem staticCost_negativeStep (n : Nat) {start width : Nat} (c : WordCursor start width) :
    staticCost (negativeStep n c) = 0 := by
  rw [negativeStep, staticCost_cast, staticCost_append, staticCost_increment, staticCost_complement]

theorem staticCost_negative (n : Nat) : ∀ (steps start width : Nat) (c : WordCursor start width),
    staticCost (negativeWords n steps start width c) = 0
  | 0, _, _, _ => by simp [negativeWords, staticCost_cast, staticCost]
  | steps+1, start, width, c => by
    rw [negativeWords, staticCost_cast, staticCost_append, staticCost_negativeStep,
      staticCost_negative n steps]

theorem staticCost_readout : staticCost Rounded.readout = 0 := by
  unfold Rounded.readout neighborSuffix
  rw [staticCost_cast, staticCost_append, staticCost_append, staticCost_append,
    staticCost_positive, staticCost_complement, staticCost_negative]
  simp [constantStep, staticCost, tCost]

theorem staticCost_rounded : staticCost Rounded.program ≤ 14640353215 := by
  unfold Rounded.program
  rw [staticCost_append, staticCost_readout, Nat.add_zero]
  exact staticCost_program

theorem staticCost_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    staticCost (reindexStraight f p) = staticCost p := by
  simp only [staticCost_eq, added_reindex, FullCredit.residue_reindex]

theorem recordSaving_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    recordSaving (reindexStraight f p) = recordSaving p := by
  induction p with
  | done => simp [reindexStraight, recordSaving]
  | gate g p ih => cases g <;> simp [reindexStraight, recordSaving, ih]
  | recordGate i v g p ih => cases v <;> simp [reindexStraight, recordSaving, ih]
  | measure => simp [reindexStraight, recordSaving, *]

theorem staticCost_fixedEntry {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e) :
    staticCost (Single.fixedEntry f p).program = staticCost p := by
  unfold Single.fixedEntry
  exact staticCost_reindex p _

theorem recordSaving_fixedEntry {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e) :
    recordSaving (Single.fixedEntry f p).program = recordSaving p := by
  unfold Single.fixedEntry
  exact recordSaving_reindex p _

theorem prefix_eq_literals {n s e} (xs : Circuit) (p : Straight n s e) :
    Optimization.literalPrefix xs p = literals xs p := by
  induction xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [Optimization.literalPrefix, literalProgram, literals, List.foldr_cons] at *
    exact congrArg (Straight.gate (.literal g)) ih

theorem staticCost_drops {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d) :
    staticCost q + d = staticCost p := by
  induction h with
  | refl => simp
  | skip g h ih => simp only [staticCost]; omega
  | skipRecord i v g hz h ih => simp only [staticCost]; omega
  | gate g h ih => cases g <;> simp only [staticCost] <;> omega
  | record i v g h ih => simp only [staticCost]; omega
  | measure w h ih => simp only [staticCost]; exact ih
  | replaceLiteral xs ys k hb h ih =>
    rw [prefix_eq_literals, prefix_eq_literals, staticCost_literals, staticCost_literals]
    have hc := hb.cost
    omega

theorem recordSaving_drops {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d) :
    recordSaving q = recordSaving p := by
  induction h with
  | refl => rfl
  | skip g h ih => simpa [recordSaving] using ih
  | skipRecord i v g hz h ih =>
    cases v <;> cases g <;> simp_all [recordSaving, recordSavingGate, tCost]
  | gate g h ih => cases g <;> simpa [recordSaving] using ih
  | record i v g h ih => cases v <;> simp [recordSaving, ih]
  | measure w h ih => simpa [recordSaving] using ih
  | replaceLiteral xs ys k hb h ih =>
    rw [prefix_eq_literals, prefix_eq_literals, recordSaving_literals, recordSaving_literals]
    exact ih

attribute [local irreducible] added residue staticCost Optimization.entryPatch

theorem staticCost_replaceEntry (e : StraightEntry) (p : Straight e.coefficients.length 0 e.finalCursor) :
    staticCost (Optimization.replaceEntry e p).program = staticCost p := rfl

private theorem parentStaticArithmetic (a b : Nat) (h : a + 460990684 = b)
    (hs : b ≤ 14640353215) : a ≤ 14179362531 := by omega

theorem staticCost_parent : staticCost Parent.entry.program ≤ 14179362531 := by
  have hs : staticCost Rounded.entry.program ≤ 14640353215 := by
    rw [Rounded.entry, staticCost_fixedEntry]
    exact staticCost_rounded
  rw [Parent.entry, staticCost_replaceEntry]
  exact parentStaticArithmetic _ _ (staticCost_drops Optimization.entryPatch.drops) hs

theorem staticCost_lowerEntry (q : Wire) (e : StraightEntry) :
    staticCost (lowerEntry q e).program + 2 * added e.program = staticCost e.program := by
  unfold lowerEntry
  exact staticCost_lower q e.program 0 Fin.elim0

private theorem fiveStaticArithmetic (a b c : Nat) (h : a + 2*b = c)
    (hb : 2025615251 ≤ b) (hc : c ≤ 14179362531) : a ≤ 10128132029 := by omega

theorem staticCost_five : staticCost Five.entry.program ≤ 10128132029 := by
  rw [Five.entry]
  exact fiveStaticArithmetic _ _ _ (staticCost_lowerEntry 1024 Parent.entry)
    AndGadget.parent_added_lower staticCost_parent

theorem recordSaving_feedback_ge {n s e} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    recordSaving p ≤ recordSaving (feedbackProgram dir w indices k p) := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih =>
    simp only [feedbackProgram, recordSaving]
    have h := ih (k+1)
    omega

theorem recordSaving_fourier_two (n start : Nat) (a b : Wire) (ws : List Wire)
    (prior : List (Fin start)) :
    1 ≤ recordSaving (fourierProgram n .inverse (a :: b :: ws) start prior) := by
  rw [fourierProgram, recordSaving_cast]
  have h := recordSaving_feedback_ge .inverse a prior 2
    (.measure a (fourierProgram n .inverse (b :: ws) (start+1) (Fin.last start :: prior.map Fin.castSucc)))
  simp only [recordSaving, fourierProgram, recordSaving_cast, feedbackProgram, recordSavingGate] at h
  simp only [fourierProgram, feedbackProgram]
  omega

theorem recordSaving_fourier_length (n start : Nat) (ws : List Wire)
    (prior : List (Fin start)) (h : 2 ≤ ws.length) :
    1 ≤ recordSaving (fourierProgram n .inverse ws start prior) := by
  cases ws with
  | nil => simp at h
  | cons a ws =>
    cases ws with
    | nil => simp at h
    | cons b ws => exact recordSaving_fourier_two n start a b ws prior

theorem recordSaving_prepare {n s e} (ws : List Wire) (p : Straight n s e) :
    recordSaving (prepareOuterBank ws p) = recordSaving p := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [show prepareOuterBank (w :: ws) p = .gate (.literal (.H w)) (prepareOuterBank ws p) by rfl]
    simpa [recordSaving] using ih

theorem recordSaving_axis_first {n} (w : Single.Window n) (ws : List (Single.Window n))
    (start : Nat) (prior : List (Fin start)) (hw : 2 ≤ w.wires.length) :
    1 ≤ recordSaving (Single.axis (w :: ws) start prior) := by
  rw [Single.axis, recordSaving_cast, recordSaving_append, recordSaving_prepare,
    recordSaving_append, recordSaving_cast]
  have h := recordSaving_fourier_length n (start+w.count) w.wires (bankPrior w.count prior) hw
  omega

theorem recordSaving_left (start : Nat) : 1 ≤ recordSaving (Single.axis Single.leftWindows start List.nil) := by
  unfold Single.leftWindows
  apply recordSaving_axis_first
  simp [Single.firstWindow, Single.bank]

theorem recordSaving_framed {n s m k e f} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    recordSaving (Single.framed p q r h) = recordSaving p + recordSaving q + recordSaving r := by
  unfold Single.framed
  simp [recordSaving, recordSaving_cast, recordSaving_append, Nat.add_assoc]

theorem recordSaving_program : 1 ≤ recordSaving Single.program := by
  unfold Single.program Single.trial
  rw [recordSaving_cast, recordSaving_framed]
  have h := recordSaving_left 0
  omega

theorem feedback_late {n s e} (w : Wire) (indices : List (Fin s)) (k : Nat)
    (p : Straight n s e) (hk : 3 ≤ k) :
    recordSaving (feedbackProgram .inverse w indices k p) = recordSaving p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih =>
    have hs : recordSavingGate (.P .inverse k w) = 0 := by
      cases k with
      | zero => omega
      | succ k => cases k with
        | zero => omega
        | succ k => cases k with
          | zero => omega
          | succ k => rfl
    simp only [feedbackProgram, recordSaving, hs, Nat.zero_add]
    exact ih (k+1) (by omega)

theorem feedback_two {n s e} (w : Wire) (indices : List (Fin s)) (p : Straight n s e) :
    recordSaving (feedbackProgram .inverse w indices 2 p) =
      (if indices.isEmpty then 0 else 1) + recordSaving p := by
  cases indices with
  | nil => simp [feedbackProgram]
  | cons i is =>
    simp only [feedbackProgram, recordSaving, recordSavingGate, List.isEmpty_cons, Bool.false_eq_true, if_false]
    rw [feedback_late w is 3 p (by omega)]

theorem fourier_savings (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    recordSaving (fourierProgram n .inverse ws start prior) =
      ws.length - (if prior.isEmpty then 1 else 0) := by
  induction ws generalizing start with
  | nil => simp [fourierProgram, recordSaving]
  | cons w ws ih =>
    rw [fourierProgram, recordSaving_cast, feedback_two]
    simp only [recordSaving]
    rw [ih]
    cases prior <;> cases ws <;> simp
    all_goals omega
theorem fourier_savings_nonempty (n start : Nat) (ws : List Wire) (prior : List (Fin start))
    (hp : 0 < prior.length) :
    recordSaving (fourierProgram n .inverse ws start prior) = ws.length := by
  rw [fourier_savings]
  cases prior with
  | nil => simp at hp
  | cons a xs => simp

theorem axis_savings_nonempty {n} (ws : List (Single.Window n)) (start : Nat)
    (prior : List (Fin start)) (hp : 0 < prior.length) :
    (ws.map (fun w => w.wires.length)).sum ≤ recordSaving (Single.axis ws start prior) := by
  induction ws generalizing start with
  | nil => simp [Single.axis, recordSaving]
  | cons w ws ih =>
    rw [Single.axis, recordSaving_cast, recordSaving_append, recordSaving_prepare,
      recordSaving_append, recordSaving_cast]
    have hb : 0 < (bankPrior w.count prior).length := by simpa [bankPrior_length] using hp
    rw [fourier_savings_nonempty n _ w.wires (bankPrior w.count prior) hb]
    have hp' : 0 < (Single.nextPrior w.count w.wires.length prior).length := by
      rw [Single.nextPrior_length]
      omega
    have h := ih _ (Single.nextPrior w.count w.wires.length prior) hp'
    simp only [List.map_cons, List.sum_cons]
    omega

theorem axis_savings_first {n} (w : Single.Window n) (ws : List (Single.Window n))
    (start : Nat) (hw : 0 < w.wires.length) :
    (w.wires.length + (ws.map (fun w => w.wires.length)).sum) - 1 ≤
      recordSaving (Single.axis (w :: ws) start List.nil) := by
  rw [Single.axis, recordSaving_cast, recordSaving_append, recordSaving_prepare,
    recordSaving_append, recordSaving_cast, fourier_savings]
  have hb : (bankPrior w.count (List.nil : List (Fin start))).isEmpty = true := by
    have h := bankPrior_length w.count (List.nil : List (Fin start))
    cases hs : bankPrior w.count (List.nil : List (Fin start)) with
    | nil => rfl
    | cons a as => simp [hs] at h
  rw [hb]
  simp only [if_true]
  have hp : 0 < (Single.nextPrior w.count w.wires.length (List.nil : List (Fin start))).length := by
    rw [Single.nextPrior_length]
    simp only [List.length_nil, Nat.zero_add]
    exact hw
  have h := axis_savings_nonempty ws _ _ hp
  omega

theorem left_width_sum : (Single.leftWindows.map (fun w => w.wires.length)).sum = 263 := by
  have h := congrArg (fun xs : List (Nat × Nat) => (xs.map Prod.snd).sum) Single.left_metadata
  simpa [List.map_map, Function.comp_def, Single.leftMetadata] using h

theorem right_width_sum : (Single.rightWindows.map (fun w => w.wires.length)).sum = 207 := by
  have h := congrArg (fun xs : List (Nat × Nat) => (xs.map Prod.snd).sum) Single.right_metadata
  simpa [List.map_map, Function.comp_def, Single.rightMetadata] using h

theorem axis_savings_left (start : Nat) : 262 ≤ recordSaving (Single.axis Single.leftWindows start List.nil) := by
  have hs := axis_savings_first Single.firstWindow (Single.leftSigned.map Single.signedWindow) start (by simp [Single.firstWindow, Single.bank])
  have hl := left_width_sum
  rw [Single.leftWindows] at hl ⊢
  simp only [List.map_cons, List.sum_cons] at hl
  omega

theorem axis_savings_right (start : Nat) : 206 ≤ recordSaving (Single.axis Single.rightWindows start List.nil) := by
  have hl := right_width_sum
  have hm := Single.right_metadata
  cases hw : Single.rightWindows with
  | nil => simp [hw] at hl
  | cons w ws =>
    have hpos : 0 < w.wires.length := by
      rw [hw] at hm
      simp only [List.map_cons, Single.rightMetadata, List.replicate_succ, List.cons.injEq, Prod.mk.injEq] at hm
      omega
    have hs := axis_savings_first w ws start hpos
    rw [hw] at hl
    simp only [List.map_cons, List.sum_cons] at hl
    omega

theorem recordSaving_program_468 : 468 ≤ recordSaving Single.program := by
  unfold Single.program Single.trial
  rw [recordSaving_cast, recordSaving_framed]
  have hl := axis_savings_left 0
  have hr := axis_savings_right (0 + Single.axisCount Single.leftWindows)
  omega


theorem recordSaving_replaceEntry (e : StraightEntry) (p : Straight e.coefficients.length 0 e.finalCursor) :
    recordSaving (Optimization.replaceEntry e p).program = recordSaving p := rfl

theorem recordSaving_lowerEntry (q : Wire) (e : StraightEntry) :
    recordSaving (lowerEntry q e).program = recordSaving e.program := by
  unfold lowerEntry
  exact recordSaving_lower q e.program 0 Fin.elim0

theorem recordSaving_five : 468 ≤ recordSaving Five.entry.program := by
  have hr := recordSaving_program_468
  have h : 468 ≤ recordSaving Rounded.entry.program := by
    rw [Rounded.entry, recordSaving_fixedEntry, Rounded.program, recordSaving_append]
    omega
  have hp : 468 ≤ recordSaving Parent.entry.program := by
    rw [Parent.entry, recordSaving_replaceEntry, recordSaving_drops Optimization.entryPatch.drops]
    exact h
  rw [Five.entry, recordSaving_lowerEntry]
  exact hp

theorem staticCost_t {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) : (p.instantiate read history).tCount ≤ staticCost p := by
  rw [staticCost_eq]
  exact residue_t p read history

theorem recordGates_slots {n s e} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    (recordGates i gs p).gateSlots = gs.length + p.gateSlots := by
  induction gs with
  | nil => simp [recordGates]
  | cons g gs ih => simp [recordGates, Straight.gateSlots, ih, Nat.add_assoc, Nat.add_left_comm]

theorem recordReplacement_length (q : Wire) (g : Gate) : (recordReplacement q g).length ≤ 7 := by
  unfold recordReplacement
  split
  · simp [kickInv, kick, controlledZ, pauliZ]
  · simp

theorem literalReplacement_length (q : Wire) (g : Gate) : (replacement q g).length ≤ 7 := by
  rw [replacement_length]
  have h : savedGate g ≤ 1 := by unfold savedGate; split <;> omega
  omega

theorem compileAll_slots {n s e} (q : Wire) (p : Straight n s e) :
    (compileAll q p).gateSlots ≤ 7 * p.gateSlots := by
  induction p with
  | done => simp [compileAll, Straight.gateSlots]
  | gate g p ih =>
    cases g with
    | literal g =>
      rw [compileAll, literals_slots]
      have h := literalReplacement_length q g
      simp only [Straight.gateSlots]
      omega
    | whenBit => rw [compileAll]; simp only [Straight.gateSlots]; omega
  | recordGate i v g p ih =>
    cases v with
    | false => rw [compileAll]; simp only [Straight.gateSlots]; omega
    | true =>
      rw [compileAll, recordGates_slots]
      have h := recordReplacement_length q g
      simp only [Straight.gateSlots]
      omega
  | measure w p ih => rw [compileAll]; simpa only [Straight.gateSlots] using ih

theorem saved_lowerEntry (q : Wire) (e : StraightEntry) :
    Catalyst.saved (lowerEntry q e).program = added e.program + Catalyst.saved e.program := by
  unfold lowerEntry
  exact Catalyst.saved_lower q e.program 0 Fin.elim0

theorem five_saved : 2025615251 ≤ Catalyst.saved Five.entry.program := by
  rw [Five.entry, saved_lowerEntry]
  have h := AndGadget.parent_added_lower
  omega

theorem compileAll_verified {n e} (q : Wire) (p : Straight n 0 e)
    (read : ConstantBit n → Bool) (layout : DecodeLayout) (Q : Secp256k1.Point)
    (psi : State) (hf : Fresh q p) (hp : SupportedOn (fun s => s q = false) psi) :
    Instrument.bornMass (((literals (prepare q) (compileAll q p)).instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi =
    Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [← expectation_verified, ← expectation_verified, expectation_literals]
  exact compileAll_expectation q p read Fin.elim0 psi _ hf hp

def compileAllEntry (q : Wire) (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := entry.finalCursor
  program := literals (prepare q) (compileAll q entry.program)

theorem compileAllEntry_within (q : Wire) (entry : StraightEntry) (ws : List Wire)
    (hp : Within ws entry.program) : Within (q::ws) (compileAllEntry q entry).program := by
  apply literals_within
  · simp [prepare, circuitWires, gateWires, List.subset_def]
  · exact compileAll_within q entry.program ws hp

theorem compileAll_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds newBounds : Bounds) (q : Wire) (ws : List Wire)
    (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hq : q ∉ ws)
    (hslots : 7 * entry.program.gateSlots + 2 ≤ limits.gateSlots)
    (hqubits : ws.length + 1 ≤ newBounds.qubits)
    (ht : staticCost entry.program + 1 ≤ newBounds.tModel + Catalyst.saved entry.program + recordSaving entry.program)
    (hm : entry.finalCursor ≤ newBounds.measurements) :
    Certificate limits layout (compileAllEntry q entry) newBounds where
  gateBudget := by
    have h := compileAll_slots q entry.program
    simp only [compileAllEntry, literals_slots, prepare, List.length_cons, List.length_nil] at *
    omega
  recordBudget := cert.recordBudget
  tableBudget := cert.tableBudget
  candidateBudget := cert.candidateBudget
  wellFormed := Catalyst.literals_wellFormed _ _ (by simp [prepare, CircuitWellFormed, Gate.WellFormed])
    (compileAll_wellFormed q entry.program (hs.fresh q hq) cert.wellFormed)
  resources := by
    intro Q
    have hsup := (compileAllEntry_within q entry ws hs).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((compileAllEntry q entry).instantiate Q).wires.dedup.toFinset).card ≤ (q :: ws).length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (q :: ws))
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((compileAllEntry q entry).instantiate Q).qubitCount ≤ newBounds.qubits := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc.trans hqubits
    have htc := staticCost_t (compileAll q entry.program) (readConstant entry.coefficients.get Q) Fin.elim0
    have hstatic := compileAll_static q entry.program
    have hmc := (compileAllEntry q entry).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    refine ⟨hqc, ?_, ?_⟩
    · change ((literals (prepare q) (compileAll q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      rw [Catalyst.literals_t]
      change 1 + ((compileAll q entry.program).instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      omega
    · change ((compileAllEntry q entry).program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ newBounds.measurements
      have he : ((compileAllEntry q entry).program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount = entry.finalCursor := by
        simpa only [Nat.add_zero] using hmc
      exact he.le.trans hm
  success := by
    intro Q d hn hd
    change 99 / 100 ≤ Instrument.bornMass
      (((literals (prepare q) (compileAll q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState)
    rw [compileAll_verified q entry.program _ layout Q _ (hs.fresh q hq)
      (supportedOn_ket _ _ rfl)]
    exact cert.success Q d hn hd

attribute [local irreducible] Within lower lowerEntry compileAllEntry Catalyst.saved recordSaving

private theorem cursor_bound (limits : Limits) (layout : DecodeLayout) (e : StraightEntry)
    (b : Bounds) (h : Certificate limits layout e b) : e.finalCursor ≤ b.measurements := by
  have hm := (h.resources 0).2.2
  have he := e.program.measurementCount (readConstant e.coefficients.get 0) Fin.elim0
  change (e.program.instantiate (readConstant e.coefficients.get 0) Fin.elim0).measurementCount ≤ b.measurements at hm
  omega

private theorem lowerEntry_within (q : Wire) (e : StraightEntry) (ws : List Wire)
    (hs : Within ws e.program) : Within (q::ws) (lowerEntry q e).program := by
  unfold lowerEntry
  exact lower_within q e.program ws hs 0 Fin.elim0

private theorem five_within : Within (1024 :: resetWires) Five.entry.program :=
  lowerEntry_within 1024 Parent.entry resetWires AndGadget.parent_within

private theorem lowerEntry_slots (q : Wire) (e : StraightEntry) :
    (lowerEntry q e).program.gateSlots = e.program.gateSlots + 18 * added e.program := by
  unfold lowerEntry
  exact lower_slots q e.program 0 Fin.elim0

private theorem slotArithmetic (old new a : Nat) (he : new = old + 18*a)
    (hs : old ≤ 90000176648) (ha : a ≤ 7361490608) : new ≤ 230350301035 := by omega

private theorem five_slots : Five.entry.program.gateSlots ≤ 230350301035 := by
  rw [Five.entry]
  exact slotArithmetic _ _ _ (lowerEntry_slots 1024 Parent.entry) AndGadget.parent_slots AndGadget.parent_added_upper

noncomputable def entry : StraightEntry := compileAllEntry 1025 Five.entry
noncomputable def layout : DecodeLayout := Five.layout
def bounds : Bounds := ⟨856, 8102516311, 8266128294⟩

private theorem costArithmetic (a b c : Nat) (ha : a ≤ 10128132029)
    (hb : 2025615251 ≤ b) (hc : 468 ≤ c) :
    a + 1 ≤ 8102516311 + b + c := by omega

attribute [local irreducible] Five.entry Parent.entry

private theorem candidateCost :
    staticCost Five.entry.program + 1 ≤ 8102516311 + Catalyst.saved Five.entry.program + recordSaving Five.entry.program :=
  costArithmetic _ _ _ staticCost_five five_saved recordSaving_five

private theorem slotBudget (a limit : Nat) (ha : a ≤ 230350301035)
    (hl : 4000000000000000 ≤ limit) : 7*a+2 ≤ limit := by omega

private theorem qCost : staticCost Five.entry.program + 1 ≤
    bounds.tModel + Catalyst.saved Five.entry.program + recordSaving Five.entry.program := by
  rw [show bounds.tModel = 8102516311 by rfl]
  exact candidateCost

private theorem qFresh : 1025 ∉ (1024 :: resetWires) := by simp [resetWires]
private theorem qBudget : 7 * Five.entry.program.gateSlots + 2 ≤ officialLimits.gateSlots :=
  slotBudget _ _ five_slots (by decide)
private theorem qCount : (1024 :: resetWires).length + 1 ≤ bounds.qubits := by
  change (1024 :: resetWires).length + 1 ≤ 856
  simp [resetWires_length]
private theorem qMeasure : Five.entry.finalCursor ≤ bounds.measurements :=
  cursor_bound officialLimits Five.layout Five.entry Five.bounds Five.certificate

theorem certificate : Certificate officialLimits layout entry bounds :=
  compileAll_certificate officialLimits Five.layout Five.entry Five.bounds bounds
    1025 (1024 :: resetWires) Five.certificate five_within qFresh qBudget qCount qCost qMeasure

end
end ShorECDLP.Entrant.InverseKick
