import ShorECDLP.Submission.Entrant.Compiler

/-! EDITABLE. Zero residue for the arithmetic outside the EEA cores.

The Toffoli lowering saves two T-model units for every unconditional literal CCX.  Its credited
count used only the measured EEA cores.  Here the same residue argument (`residue = 0`, i.e. no
phase gates and no constant- or record-controlled non-Clifford gates) is proved for the Gidney
adders and comparators, the modular arithmetic built from them and the Horner multipliers, so
their Toffoli gates are credited as well. -/

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! ## Generic residue facts -/

/-- A circuit with no phase instruction. -/
def PhaseFree (gs : Circuit) : Prop := (gs.map primitivePhaseCost).sum = 0

theorem phaseFree_of_HPFree {gs : Circuit} (h : Classical.HPFree gs) : PhaseFree gs :=
  primitivePhaseCost_of_HPFree gs h

theorem phaseFree_nil : PhaseFree [] := rfl

theorem phaseFree_append {a b : Circuit} (ha : PhaseFree a) (hb : PhaseFree b) :
    PhaseFree (a ++ b) := by
  unfold PhaseFree at *; simp [List.map_append, List.sum_append, ha, hb]

theorem phaseFree_cons {g : Gate} {gs : Circuit} (hg : primitivePhaseCost g = 0)
    (hs : PhaseFree gs) : PhaseFree (g :: gs) := by
  unfold PhaseFree at *; simp [hg, hs]

theorem phaseFree_adjoint {gs : Circuit} (h : PhaseFree gs) : PhaseFree gs.adjoint := by
  unfold PhaseFree at *
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons] at h
    have hg : primitivePhaseCost g = 0 := by omega
    have hs : (gs.map primitivePhaseCost).sum = 0 := by omega
    simp only [Circuit.adjoint, List.map_reverse, List.map_cons, List.reverse_cons,
      List.map_append, List.sum_append] at ih ⊢
    have := ih hs
    cases g <;> simp_all [Gate.adjoint, primitivePhaseCost]

theorem residue_literal_pf {n s} {gs : Circuit} (h : PhaseFree gs) :
    residue (literalProgram gs : Straight n s s) = 0 := by
  rw [residue_literal]; exact h

def templateResidue {n : Nat} : TemplateGate n → Nat
  | .literal g => primitivePhaseCost g
  | .whenBit _ _ g => tCost g

theorem residue_gateProgram {n s} (gs : List (TemplateGate n)) :
    residue (gateProgram gs : Straight n s s) = (gs.map templateResidue).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [gateProgram, residue, templateResidue, ih]

theorem residue_relabel {n s e} (p : Straight n s e) (f : Wire ≃ Wire) :
    residue (relabelStraight f p) = residue p := by
  have hp (g : Gate) : primitivePhaseCost (g.relabel f) = primitivePhaseCost g := by
    cases g <;> rfl
  have ht (g : Gate) : tCost (g.relabel f) = tCost g := by cases g <;> rfl
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g <;> simp [relabelStraight, relabelTemplateGate, residue, ih, hp, ht]
  | recordGate i v g p ih => simp [relabelStraight, residue, ih, ht]
  | measure w p ih => simp [relabelStraight, residue, ih]

theorem residue_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    residue (reindexStraight f p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp [reindexStraight, reindexGate, residue, ih]
  | recordGate i v g p ih => simp [reindexStraight, residue, ih]
  | measure w p ih => simp [reindexStraight, residue, ih]

theorem residue_shift {n s e} (p : Straight n s e) (offset : Nat) :
    residue (shiftStraight offset p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp [shiftStraight, residue, ih]
  | recordGate i v g p ih => simp [shiftStraight, residue, ih]
  | measure w p ih => simp [shiftStraight, residue, ih]

theorem residue_constantStraight {n s e} (q : Wire) (p : Straight n s e) :
    residue (constantStraight q p) ≤ residue p := by
  have hp (g : Gate) : primitivePhaseCost (constantControlGate q g) = primitivePhaseCost g := by
    cases g <;> simp [constantControlGate] <;> split <;> rfl
  have ht (g : Gate) : tCost (constantControlGate q g) ≤ tCost g := by
    cases g <;> simp [constantControlGate] <;> split <;> simp [tCost]
  induction p with
  | done => exact Nat.le_refl _
  | gate g p ih =>
    cases g with
    | literal g => simp only [constantStraight, constantTemplateGate, residue, hp]; omega
    | whenBit i v g =>
      simp only [constantStraight, constantTemplateGate, residue]; have := ht g; omega
  | recordGate i v g p ih =>
    simp only [constantStraight, residue]; have := ht g; omega
  | measure w p ih => simpa [constantStraight, residue] using ih

theorem residue_registerCorrection {n s e} (ws : List Wire) (is : List (Fin s))
    (next : Straight n s e) :
    residue (registerCorrectionProgram ws is next) = residue next := by
  induction ws generalizing is with
  | nil => cases is <;> rfl
  | cons w ws ih =>
    cases is with
    | nil => rfl
    | cons i is =>
      simp [registerCorrectionProgram, residue_recordGates, pauliZ, tCount, tCost, ih]

theorem residue_deferred (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (hc : PhaseFree cleanup) :
    ∀ (cells : List (Circuit × Wire)), (∀ c ∈ cells, PhaseFree c.1) →
      ∀ (start : Nat) (prior : List (Fin start)),
        residue (deferredCorrectionProgram n targets cleanup cells start prior) = 0 := by
  intro cells
  induction cells with
  | nil =>
    intro _ start prior
    simp only [deferredCorrectionProgram, residue_registerCorrection, residue_append,
      residue_literal_pf hc, residue_done]
  | cons c cells ih =>
    intro hcells start prior
    obtain ⟨gs, w⟩ := c
    simp only [deferredCorrectionProgram, residue_cast, residue_append,
      residue_literal_pf (hcells _ (List.mem_cons_self ..))]
    simp only [residue, Nat.zero_add]
    exact ih (fun c hc => hcells c (List.mem_cons_of_mem _ hc)) _ _

def lookupOpResidue {n : Nat} : LookupOp n → Nat
  | .gates gs => (gs.map templateResidue).sum
  | .erase _ _ _ => 0

theorem residue_lookup (n : Nat) :
    ∀ (ops : List (LookupOp n)) (start : Nat),
      residue (lookupProgram n ops start) = (ops.map lookupOpResidue).sum := by
  intro ops
  induction ops with
  | nil => intro _; rfl
  | cons op ops ih =>
    intro start
    cases op with
    | gates gs => simp [lookupProgram, residue_append, residue_gateProgram, ih, lookupOpResidue]
    | erase a b t => simp [lookupProgram, residue_cast, residue_append, ih, lookupOpResidue]

theorem residue_collect {n : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hn : ∀ cursor prior, residue (next cursor prior).2 = 0) :
    ∀ (ws : List Wire) (start : Nat) (prior : List (Fin start)),
      residue (collectProgram n next ws start prior).2 = 0 := by
  intro ws
  induction ws with
  | nil => intro start prior; exact hn start prior
  | cons w ws ih =>
    intro start prior
    simp only [collectProgram, residue_cast, residue]
    exact ih _ _

/-! ## Phase-free literal leaves -/

@[simp] theorem sum_controlledAddCarry (bs as : List Wire) (q c f : Wire) :
    ((controlledAddCarry bs as q c f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (controlledAddCarry_HPFree bs as q c f)

@[simp] theorem sum_controlledSubCarry (bs as : List Wire) (q c f : Wire) :
    ((controlledSubCarry bs as q c f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (controlledSubCarry_HPFree bs as q c f)

@[simp] theorem sum_controlledCompareLT (l r : List Wire) (q c f : Wire) :
    ((controlledCompareLT l r q c f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (controlledCompareLT_HPFree l r q c f)

@[simp] theorem sum_doublingShift (acc : List Wire) (f : Wire) :
    ((doublingShift acc f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (doublingShift_HPFree acc f)

@[simp] theorem sum_doublingShift_adjoint (acc : List Wire) (f : Wire) :
    (((doublingShift acc f).adjoint).map primitivePhaseCost).sum = 0 :=
  phaseFree_adjoint (sum_doublingShift acc f)

@[simp] theorem sum_controlledComplement (input : List Wire) (q : Wire) :
    ((controlledComplement input q).map primitivePhaseCost).sum = 0 := by
  unfold controlledComplement
  induction input with
  | nil => rfl
  | cons w ws ih => simpa [primitivePhaseCost] using ih

@[simp] theorem sum_workRegistersPrepare : (workRegistersPrepare.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ workRegistersPrepare_resources.2.1

@[simp] theorem sum_workRegistersRestore : (workRegistersRestore.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ workRegistersRestore_resources.2.1

@[simp] theorem sum_eeaLengthSetup : (eeaLengthSetup.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp only [eeaLengthSetup, Classical.hpFree_append]
  exact ⟨⟨xorConstant_HPFree _ _, xorConstant_HPFree _ _⟩, lengthInitialize_HPFree _ _ _ _ _⟩

@[simp] theorem sum_eeaLengthUndo : (eeaLengthUndo.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp only [eeaLengthUndo, Classical.hpFree_append]
  exact ⟨⟨lengthInitialize_HPFree _ _ _ _ _, xorConstant_HPFree _ _⟩, xorConstant_HPFree _ _⟩

@[simp] theorem sum_terminalEpochCompression :
    (terminalEpochCompression.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp [terminalEpochCompression, mcxVChain_HPFree]

@[simp] theorem sum_terminalWork1Clear : (terminalWork1Clear.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (xorConstant_HPFree _ _)

@[simp] theorem sum_canonicalWork2Rotation :
    (canonicalWork2Rotation.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ canonicalWork2Rotation_HPFree

@[simp] theorem sum_canonicalWork2InverseRotation :
    (canonicalWork2InverseRotation.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ canonicalWork2InverseRotation_HPFree

@[simp] theorem sum_fig15SwapOutput : (fig15SwapOutput.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  intro g hg
  simp only [fig15SwapOutput, List.mem_flatMap] at hg
  obtain ⟨i, hi, hg⟩ := hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> trivial

@[simp] theorem sum_fig15ZeroPrepare : (fig15ZeroPrepare.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  rw [fig15ZeroPrepare, nonzeroInputPrepare, Classical.hpFree_append]
  exact ⟨computeEqConst_HPFree _ _ _ _, by simp [Classical.HPFree]⟩

@[simp] theorem sum_fig15ZeroRestore : (fig15ZeroRestore.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  rw [fig15ZeroRestore, nonzeroInputRestore, Classical.hpFree_append]
  exact ⟨by simp [Classical.HPFree], computeEqConst_HPFree _ _ _ _⟩

@[simp] theorem sum_signedAddressCircuit (q sign : Wire) (bits : List Wire) :
    ((signedAddressCircuit q sign bits).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (signedAddressCircuit_HPFree q sign bits)

@[simp] theorem sum_zeroMask (register : List Wire) (value : Nat) :
    ((zeroMask register value).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (zeroMask_HPFree register value)

/-! ## Gidney adders and comparators -/

theorem pf_flipWord (ws : List Wire) : PhaseFree (gidneyFlipWord ws) := by
  unfold PhaseFree gidneyFlipWord
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [primitivePhaseCost] using ih

theorem pf_constCarryXor (input dirty : List Wire) (constant : List Bool) (q c : Wire) :
    PhaseFree (controlledConstCarryXor input dirty constant q c) :=
  controlledConstCarryXor_cost_zero primitivePhaseCost (fun _ _ => rfl) (fun _ _ _ => rfl)
    input dirty constant q c

theorem pf_addCleanup (input dirty : List Wire) (constant : List Bool) (q c : Wire) :
    PhaseFree (gidneyAddCleanup input dirty constant q c) := by
  unfold gidneyAddCleanup
  exact phaseFree_append (phaseFree_append (pf_flipWord _) (pf_constCarryXor _ _ _ _ _))
    (pf_flipWord _)

theorem pf_addCarryCell (q c s a i d : Wire) (k : Bool) :
    PhaseFree (gidneyAddCarryCell q c s a i d k) := by
  unfold PhaseFree gidneyAddCarryCell; cases k <;> simp [primitivePhaseCost]

theorem pf_compareCarryCell (q c s a i d f : Wire) (k last : Bool) :
    PhaseFree (gidneyCompareCarryCell q c s a i d f k last) := by
  unfold PhaseFree gidneyCompareCarryCell; cases k <;> cases last <;> simp [primitivePhaseCost]

theorem pf_gidneyCells (q : Wire) :
    ∀ (as ds : List Wire) (ks : List Bool) (cur sp anc : Wire),
      ∀ c ∈ gidneyCarryCells q cur sp anc as ds ks, PhaseFree c.1 := by
  intro as
  induction as with
  | nil => intro ds ks cur sp anc c hc; simp [gidneyCarryCells] at hc
  | cons a as ih =>
    intro ds ks cur sp anc c hc
    cases ds with
    | nil =>
      cases as with
      | nil =>
        cases ks with
        | nil => simp [gidneyCarryCells] at hc
        | cons k ks =>
          cases ks with
          | nil =>
            simp only [gidneyCarryCells, List.mem_singleton] at hc; subst hc
            unfold PhaseFree; cases k <;> simp [primitivePhaseCost]
          | cons k' ks => simp [gidneyCarryCells] at hc
      | cons b bs => cases ks <;> simp [gidneyCarryCells] at hc
    | cons d ds =>
      cases ks with
      | nil => cases as <;> simp [gidneyCarryCells] at hc
      | cons k ks =>
        have hc' : c = (gidneyAddCarryCell q cur sp anc a d k, cur) ∨
            c ∈ gidneyCarryCells q sp cur anc as ds ks := by
          cases as <;> simpa [gidneyCarryCells] using hc
        rcases hc' with rfl | hc'
        · exact pf_addCarryCell _ _ _ _ _ _ _
        · exact ih ds ks sp cur anc c hc'

theorem pf_compareCells (q f : Wire) :
    ∀ (as ds : List Wire) (ks : List Bool) (cur sp anc : Wire),
      ∀ c ∈ compareCarryCells q cur sp anc f as ds ks, PhaseFree c.1 := by
  intro as
  induction as with
  | nil =>
    intro ds ks cur sp anc c hc
    cases ds <;> cases ks <;> simp [compareCarryCells] at hc
    subst hc; exact phaseFree_nil
  | cons a as ih =>
    intro ds ks cur sp anc c hc
    cases ds with
    | nil => cases ks <;> simp [compareCarryCells] at hc
    | cons d ds =>
      cases ks with
      | nil => simp [compareCarryCells] at hc
      | cons k ks =>
        simp only [compareCarryCells, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact pf_compareCarryCell _ _ _ _ _ _ _ _ _
        · exact ih ds ks sp cur anc c hc

@[simp] theorem residue_gidney (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) :
    residue (gidneyProgram n start input dirty constant q carry spare ancilla).2 = 0 := by
  change compiledResidue (gidneyProgram n start input dirty constant q carry spare ancilla) = 0
  unfold gidneyProgram
  split
  · rfl
  · split
    · exact residue_literal_pf (by unfold PhaseFree; split <;> simp [primitivePhaseCost])
    · show residue (gidneyNontrivialProgram _ _ _ _ _ _ _ _ _ _ _ _) = 0
      unfold gidneyNontrivialProgram
      rw [residue_append, residue_literal_pf (pf_addCarryCell _ _ _ _ _ _ _), Nat.zero_add]
      exact residue_deferred n _ _ (pf_addCleanup _ _ _ _ _) _ (pf_gidneyCells q _ _ _ _ _ _) _ _
    · rfl

@[simp] theorem residue_compareCore (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) :
    residue (compareCoreProgram n start input dirty constant q carry spare ancilla flag).2 = 0 := by
  change compiledResidue (compareCoreProgram n start input dirty constant q carry spare ancilla flag) = 0
  unfold compareCoreProgram
  split
  · show residue (compareCarryProgram _ _ _ _ _ _ _ _ _ _ _ _ _) = 0
    unfold compareCarryProgram
    rw [residue_append, residue_literal_pf (pf_compareCarryCell _ _ _ _ _ _ _ _ _), Nat.zero_add]
    exact residue_deferred n _ _ (pf_constCarryXor _ _ _ _ _) _ (pf_compareCells q flag _ _ _ _ _ _) _ _
  · rfl

@[simp] theorem residue_compareGE (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) :
    residue (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2 = 0 := by
  change compiledResidue (compareGEProgram n start input dirty threshold q carry spare ancilla flag) = 0
  unfold compareGEProgram
  split
  · exact residue_literal_pf (by unfold PhaseFree; simp [primitivePhaseCost])
  · split
    · rfl
    · exact residue_compareCore n start input dirty _ q carry spare ancilla flag

@[simp] theorem residue_uncontrolledCompare (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (carry spare ancilla flag : Wire) :
    residue (uncontrolledCompareProgram n start input dirty threshold carry spare ancilla flag).2 = 0 := by
  unfold uncontrolledCompareProgram
  have h := residue_constantStraight (gidneyCompareVirtualControl input dirty carry spare ancilla flag)
    (compareGEProgram n start input dirty threshold
      (gidneyCompareVirtualControl input dirty carry spare ancilla flag) carry spare ancilla flag).2
  rw [residue_compareGE] at h
  exact Nat.le_zero.mp h

/-! ## Modular arithmetic -/

@[simp] theorem residue_modularAdd (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q carry spare ancilla flag : Wire) :
    residue (modularAddProgram n start input acc correction modulus q carry spare ancilla flag).2 = 0 := by
  simp [modularAddProgram, residue_append, residue_literal]

@[simp] theorem residue_modularNegate (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) :
    residue (modularNegateProgram n start target dirty modulus q c r t f).2 = 0 := by
  simp [modularNegateProgram]

@[simp] theorem residue_negativeNegate (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) :
    residue (negativeNegateProgram n start target dirty modulus q c r t f).2 = 0 := by
  simp [negativeNegateProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_modularSub (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) :
    residue (modularSubProgram n start input acc modulus p q c r t f).2 = 0 := by
  simp [modularSubProgram, residue_literal]

@[simp] theorem residue_modularDouble (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (modularDoubleProgram n start acc dirty bits p c r t f).2 = 0 := by
  cases acc with
  | nil => rfl
  | cons a rest => simp [modularDoubleProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_modularHalve (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (modularHalveProgram n start acc dirty bits p c r t f).2 = 0 := by
  cases acc with
  | nil => rfl
  | cons a rest => simp [modularHalveProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_horner (n : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (start : Nat) :
    residue (hornerProgram n start controls input acc bits p c r t f).2 = 0 := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih => simp [hornerProgram, ih]

@[simp] theorem residue_hornerInverse (n : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (start : Nat) :
    residue (hornerInverseProgram n start controls input acc bits p c r t f).2 = 0 := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih => simp [hornerInverseProgram, ih]

@[simp] theorem residue_squareAdd (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) :
    residue (squareAddProgram n start input acc bits p q copied c r t f).2 = 0 := by
  simp [squareAddProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_squareSub (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) :
    residue (squareSubProgram n start input acc bits p q copied c r t f).2 = 0 := by
  simp [squareSubProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_square (n : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (start : Nat) :
    residue (squareProgram n start controls input acc bits p copied c r t f).2 = 0 := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih => simp [squareProgram, ih]

@[simp] theorem residue_squareInverse (n : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (start : Nat) :
    residue (squareInverseProgram n start controls input acc bits p copied c r t f).2 = 0 := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih => simp [squareInverseProgram, ih]

@[simp] theorem residue_squareSubtract (n start : Nat) (x y acc : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire) :
    residue (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2 = 0 := by
  simp [squareSubtractProgram]

/-! ## EEA wrappers -/

@[simp] theorem residue_constMinus (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) :
    residue (constMinusProgram n start input dirty bits q c r t).2 = 0 := by
  simp [constMinusProgram]

@[simp] theorem residue_eeaCenter (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) :
    residue (eeaCenterProgram n start input dirty bits p c r t iter).2 = 0 := by
  simp [eeaCenterProgram]

@[simp] theorem residue_eeaUncenter (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) :
    residue (eeaUncenterProgram n start input dirty bits p c r t iter).2 = 0 := by
  simp [eeaUncenterProgram]

@[simp] theorem residue_eeaParity (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) :
    residue (eeaParityProgram n start input dirty bits c r t iter).2 = 0 := by
  simp [eeaParityProgram, residue_literal, primitivePhaseCost]

theorem residue_preprocess (n start : Nat) : residue (preprocessProgram n start).2 = 0 := by
  unfold preprocessProgram
  rw [residue_surround, residue_eeaCenter, sum_workRegistersPrepare, sum_eeaLengthSetup]

theorem residue_unpreprocess (n start : Nat) : residue (unpreprocessProgram n start).2 = 0 := by
  unfold unpreprocessProgram
  rw [residue_surround, residue_eeaUncenter, sum_eeaLengthUndo, sum_workRegistersRestore]

theorem residue_productionParity (n start : Nat) :
    residue (productionParityProgram n start).2 = 0 := by
  unfold productionParityProgram
  exact residue_eeaParity _ _ _ _ _ _ _ _ _

attribute [local irreducible] terminalWork1Clear

theorem residue_measuredForwardWrapper (n start : Nat) :
    residue (measuredForwardWrapperProgram n start).2 = 0 := by
  unfold measuredForwardWrapperProgram
  apply residue_sequence
  intro p hp s
  simp only [measuredForwardWrapperSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h <;> subst p
  · exact residue_preprocess n s
  · exact residue_measuredSchedule _ _ _ _ _ _
  · show residue (literalProgram _) = 0
    rw [residue_literal, List.map_append, List.sum_append, sum_canonicalWork2Rotation,
      sum_terminalEpochCompression]
  · exact residue_productionParity n s
  · exact (residue_literal _).trans sum_terminalWork1Clear

theorem residue_measuredReverseWrapper (n start : Nat) :
    residue (measuredReverseWrapperProgram n start).2 = 0 := by
  unfold measuredReverseWrapperProgram
  apply residue_sequence
  intro p hp s
  simp only [measuredReverseWrapperSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h <;> subst p
  · exact (residue_literal _).trans sum_terminalWork1Clear
  · exact residue_productionParity n s
  · show residue (literalProgram _) = 0
    rw [residue_literal, List.map_append, List.sum_append, sum_terminalEpochCompression,
      sum_canonicalWork2InverseRotation]
  · exact residue_measuredInverseSchedule _ _ _ _ _
  · exact residue_unpreprocess n s

theorem residue_measuredForwardDataBank (n start : Nat) :
    residue (measuredForwardDataBankProgram n start).2 = 0 := by
  unfold measuredForwardDataBankProgram relabelCompiled
  rw [residue_relabel]
  exact residue_measuredForwardWrapper n start

theorem residue_measuredReverseDataBank (n start : Nat) :
    residue (measuredReverseDataBankProgram n start).2 = 0 := by
  unfold measuredReverseDataBankProgram relabelCompiled
  rw [residue_relabel]
  exact residue_measuredReverseWrapper n start

/-! ## In-place division and multiplication -/

theorem residue_multiplyWork (n start : Nat) : residue (multiplyWorkProgram n start).2 = 0 := by
  unfold multiplyWorkProgram; apply residue_horner

theorem residue_multiplyData (n start : Nat) : residue (multiplyDataProgram n start).2 = 0 := by
  unfold multiplyDataProgram; apply residue_horner

theorem residue_unmultiplyData (n start : Nat) :
    residue (unmultiplyDataProgram n start).2 = 0 := by
  unfold unmultiplyDataProgram; apply residue_hornerInverse

attribute [local irreducible] measuredForwardWrapperProgram measuredReverseWrapperProgram
  measuredForwardDataBankProgram measuredReverseDataBankProgram multiplyDataProgram
  multiplyWorkProgram unmultiplyDataProgram

theorem residue_correctionCompiled (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    residue (correctionCompiled n start ws prior).2 = 0 := by
  unfold correctionCompiled
  exact (residue_registerCorrection ws prior _).trans rfl

theorem residue_app {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : residue p.2 = 0) (hq : residue q.2 = 0) : residue (appendCompiled p q).2 = 0 := by
  rw [residue_compiled, hp, hq]

theorem residue_divisionCleanup (n start : Nat) :
    residue (divisionCleanupProgram n start).2 = 0 := by
  unfold divisionCleanupProgram appendLiteral
  exact residue_app _ _ (residue_unmultiplyData _ _) (residue_literal_pf sum_fig15SwapOutput)

theorem residue_divisionCorrection (n start : Nat) (prior : List (Fin start)) :
    residue (divisionCorrectionProgram n start prior).2 = 0 := by
  unfold divisionCorrectionProgram
  exact residue_app _ _ (residue_correctionCompiled _ _ _ _) (residue_divisionCleanup _ _)

theorem residue_divisionAfterReset (n start : Nat) (prior : List (Fin start)) :
    residue (divisionAfterResetProgram n start prior).2 = 0 := by
  unfold divisionAfterResetProgram appendRetaining
  exact residue_app _ _
    (residue_app _ _ (residue_measuredReverseDataBank _ _) (residue_multiplyData _ _))
    (residue_divisionCorrection _ _ _)

attribute [local irreducible] divisionAfterResetProgram

theorem residue_division (n start : Nat) : residue (divisionProgram n start).2 = 0 := by
  unfold divisionProgram
  exact residue_app _ _
    (residue_app _ _ (residue_measuredForwardWrapper _ _) (residue_multiplyWork _ _))
    (residue_collect _ (residue_divisionAfterReset n) _ _ _)

theorem residue_multiplicationCleanup (n start : Nat) :
    residue (multiplicationCleanupProgram n start).2 = 0 := by
  unfold multiplicationCleanupProgram appendLiteral
  exact residue_app _ _ (residue_unmultiplyData _ _)
    (residue_app _ _ (residue_measuredReverseDataBank _ _) (residue_literal_pf sum_fig15SwapOutput))

theorem residue_multiplicationCorrection (n start : Nat) (prior : List (Fin start)) :
    residue (multiplicationCorrectionProgram n start prior).2 = 0 := by
  unfold multiplicationCorrectionProgram
  exact residue_app _ _ (residue_correctionCompiled _ _ _ _) (residue_multiplicationCleanup _ _)

theorem residue_multiplicationAfterReset (n start : Nat) (prior : List (Fin start)) :
    residue (multiplicationAfterResetProgram n start prior).2 = 0 := by
  unfold multiplicationAfterResetProgram appendRetaining
  exact residue_app _ _
    (residue_app _ _ (residue_measuredForwardDataBank _ _) (residue_multiplyData _ _))
    (residue_multiplicationCorrection _ _ _)

attribute [local irreducible] multiplicationAfterResetProgram

theorem residue_multiplication (n start : Nat) :
    residue (multiplicationProgram n start).2 = 0 := by
  unfold multiplicationProgram
  exact residue_app _ _ (residue_multiplyWork _ _)
    (residue_collect _ (residue_multiplicationAfterReset n) _ _ _)

/-! ## Lookups -/

@[simp] theorem lookupOpResidue_gates {n : Nat} (gs : List (TemplateGate n)) :
    lookupOpResidue (.gates gs) = (gs.map templateResidue).sum := rfl

@[simp] theorem lookupOpResidue_erase {n : Nat} (a b t : Wire) :
    lookupOpResidue (n := n) (.erase a b t) = 0 := rfl

@[simp] theorem lookupOpResidue_ordinary {n : Nat} (gs : Circuit) :
    lookupOpResidue (ordinaryOp (n := n) gs) = (gs.map primitivePhaseCost).sum := by
  unfold ordinaryOp lookupOpResidue
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, templateResidue] at ih ⊢; rw [ih]

theorem tres_lookupLeaf {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire)) :
    ((lookupLeafGates q ports).map templateResidue).sum = 0 := by
  unfold lookupLeafGates
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [templateResidue, tCost] using ih

theorem opsResidue_unary {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (hl : ∀ l q, ((leaf l q).map templateResidue).sum = 0) :
    ∀ (tree : UnaryActionTree) (q : Wire) (path : List Wire),
      ((unaryLookupOps leaf tree q path).map lookupOpResidue).sum = 0 := by
  intro tree
  induction tree with
  | leaf l => intro q path; simp [unaryLookupOps, hl]
  | node bit zero one ihz iho =>
    intro q path
    cases path with
    | nil => simp [unaryLookupOps]
    | cons p ps =>
      simp [unaryLookupOps, ihz, iho, computeZeroAnd, primitivePhaseCost]

theorem residue_fieldLoad (field : PointField) (start : Nat) :
    residue (fieldLoadProgram field start) = 0 := by
  rw [fieldLoadProgram, residue_cast, residue_lookup, fieldLoadOps]
  exact opsResidue_unary _ (fun l q => tres_lookupLeaf _ _) _ _ _

theorem residue_fieldLookupAdd (field : PointField) (acc : List Wire) (start : Nat) :
    residue (fieldLookupAddProgram field acc start).2 = 0 := by
  unfold fieldLookupAddProgram
  simp only [residue_compiled, residue_fieldLoad, residue_modularAdd]

theorem residue_firstLookup (start : Nat) : residue (firstLookupProgram start) = 0 := by
  rw [firstLookupProgram, residue_cast, residue_lookup, firstLookupOps]
  exact opsResidue_unary _ (fun l q => tres_lookupLeaf _ _) _ _ _

/-! ## Window coordinates -/

theorem residue_yNegate (start : Nat) : residue (yNegateProgram start).2 = 0 := by
  unfold yNegateProgram; apply residue_negativeNegate

theorem residue_signedField (field : PointField) (start : Nat) :
    residue (signedFieldProgram field start).2 = 0 := by
  unfold signedFieldProgram
  simp only [residue_compiled, residue_yNegate, residue_fieldLookupAdd]

theorem residue_xNegate (n start : Nat) : residue (xNegateProgram n start).2 = 0 := by
  unfold xNegateProgram; apply residue_modularNegate

theorem residue_pointSquare (n start : Nat) : residue (pointSquareProgram n start).2 = 0 := by
  unfold pointSquareProgram; apply residue_squareSubtract

end
end ShorECDLP.Entrant.AndGadget
end
