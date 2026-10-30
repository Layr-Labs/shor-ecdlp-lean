import ShorECDLP.Submission.Entrant.Credit
import ShorECDLP.Submission.Entrant.Single.Physical

/-! EDITABLE. Zero residue for complete signed windows.

Adapted from public submission 03bad799-6ecf-43f0-9764-ee07b27961a1.
The measured exceptional tests and borrowed-flag guards below extend that proof
to the 29-window neighbor-decoding producer of 1747672a.


The window bodies add lookups, the zero-allowed field guards and the endpoint correction block
around the arithmetic of `Credit`.  With every block free of phase instructions and of
constant- or record-controlled non-Clifford gates, each window's exact T-count is carried by
its literal Toffoli gates alone, which credits all of them to the lowering. -/

section
namespace ShorECDLP.Entrant.FullCredit
open ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Secp256k1
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! ## Endpoint correction lookups -/

theorem tres_endpointSelectGate {n : Nat} (q : Wire) (port : Wire × EndpointBit n) :
    ((endpointSelectGate q port).map templateResidue).sum = 0 := by
  obtain ⟨w, b⟩ := port
  rcases b with b | r
  · cases b <;> rfl
  · rfl

theorem tres_endpointSelectGates {n : Nat} (q : Wire) (ports : List (Wire × EndpointBit n)) :
    ((endpointSelectGates q ports).map templateResidue).sum = 0 := by
  unfold endpointSelectGates
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, tres_endpointSelectGate, ih]

@[simp] theorem sum_ipxTest (k : Fin 4) : ((ipxTest k).map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  rw [ipxTest, Classical.hpFree_append, Classical.hpFree_append]
  exact ⟨⟨computeEqConst_HPFree _ _ _ _, computeEqConst_HPFree _ _ _ _⟩,
    computeEqConst_HPFree _ _ _ _⟩

theorem opsResidue_tail {n} (a : Wire) (cs : List Wire) (t : Wire) (ws : List Wire) :
    ((@measuredTailOps n a cs t ws).map lookupOpResidue).sum = 0 := by
  induction cs generalizing a ws with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => simp [measuredTailOps, primitivePhaseCost]
    | cons d ds => cases ws <;> simp [measuredTailOps, ih, primitivePhaseCost]

theorem opsResidue_equality {n} (r : List Wire) (v : Nat) (t : Wire) (ws : List Wire) :
    ((@measuredEqualityOps n r v t ws).map lookupOpResidue).sum = 0 := by
  have hz := sum_zeroMask r v
  simp only [measuredEqualityOps, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, lookupOpResidue_ordinary, hz, Nat.zero_add,
    Nat.add_zero]
  unfold measuredChainOps
  split <;> simp [opsResidue_tail, primitivePhaseCost]

theorem opsResidue_measuredTest {n} (k : Fin 4) :
    ((@ipxMeasuredTestOps n k).map lookupOpResidue).sum = 0 := by
  simp [ipxMeasuredTestOps, List.map_append, List.sum_append, opsResidue_equality]

theorem opsResidue_ipx {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire) :
    ∀ ops : List IpxOp, ((ipxOps rows tree paths ops).map lookupOpResidue).sum = 0
  | [] => rfl
  | .query c u v :: ops => by
    rw [ipxOps, List.map_append, List.sum_append, opsResidue_ipx rows tree paths ops,
      opsResidue_unary _ (fun l q => by
        rw [ipxLeaf, List.map_append, List.sum_append, tres_endpointSelectGates,
          tres_endpointSelectGates])]
  | .test k :: ops => by
    rw [ipxOps, List.map_append, List.sum_append, opsResidue_ipx rows tree paths ops,
      opsResidue_measuredTest, Nat.add_zero]

/-! ## Window bodies -/

theorem residue_zeroDivision (n start : Nat) : residue (zeroDivisionProgram n start).2 = 0 := by
  unfold zeroDivisionProgram
  rw [residue_surround, residue_division, sum_fig15ZeroPrepare, sum_fig15ZeroRestore]

theorem residue_zeroMultiplication (n start : Nat) :
    residue (zeroMultiplicationProgram n start).2 = 0 := by
  unfold zeroMultiplicationProgram
  rw [residue_surround, residue_multiplication, sum_fig15ZeroPrepare, sum_fig15ZeroRestore]

theorem residue_eq (n start : Nat) (r : List Wire) (v : Nat) (t : Wire) (ws : List Wire) :
    residue (equalityProgram n start r v t ws).2 = 0 := by
  exact residue_equality n start r v t ws

theorem residue_borrowedField (n start : Nat) (arithmetic : FixedSegment n)
    (ha : ∀ s, residue (arithmetic s).2 = 0) :
    residue (BorrowFlag.fieldProgram n start arithmetic).2 = 0 := by
  unfold BorrowFlag.fieldProgram
  rw [residue_surround]
  have hf : (BorrowFlag.flip.map primitivePhaseCost).sum = 0 := by rfl
  rw [hf, Nat.zero_add, Nat.add_zero]
  apply residue_sequence
  intro p hp s
  simp only [BorrowFlag.coreSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h <;> subst p
  · simp [relabelCompiled, residue_relabel, BorrowFlag.prepareProgram, residue_eq,
      residue_literal, ZeroAdaptive.cx, primitivePhaseCost]
  · exact ha s
  · simp [relabelCompiled, residue_relabel, BorrowFlag.restoreProgram, residue_eq,
      residue_literal, ZeroAdaptive.cx, primitivePhaseCost]

theorem residue_coordinate (start : Nat) : residue (BorrowFlag.adaptiveCoordinateProgram start).2 = 0 := by
  unfold BorrowFlag.adaptiveCoordinateProgram
  apply residue_sequence
  intro p hp s
  simp only [BorrowFlag.adaptiveCoordinateSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h <;> subst p
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s
  · exact residue_borrowedField _ s _ (residue_division _)
  · exact residue_pointSquare _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_borrowedField _ s _ (residue_multiplication _)
  · exact residue_xNegate _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s

theorem residue_placed (start : Nat) : residue (Single.Physical.placedProgram start).2 = 0 := by
  unfold Single.Physical.placedProgram ipxProgramOf
  exact (residue_lookup _ _ _).trans (opsResidue_ipx _ _ _ _)

theorem residue_core (start : Nat) : residue (Single.Physical.core start).2 = 0 := by
  unfold Single.Physical.core
  apply residue_sequence
  intro p hp s
  simp only [Single.Physical.segments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h <;> subst p
  · exact residue_coordinate s
  · exact residue_yNegate s
  · exact residue_placed s
  · exact residue_yNegate s

theorem residue_prepared (start : Nat) : residue (Single.Physical.prepared start).2 = 0 := by
  unfold Single.Physical.prepared
  rw [residue_surround, residue_core, sum_signedAddressCircuit]

theorem residue_actual (start : Nat) : residue (Single.Physical.actual.program start) = 0 := by
  unfold Single.Physical.actual closedWindow
  exact ((residue_shift _ _).trans (residue_cast _ _)).trans
    ((residue_relabel _ _).trans (residue_prepared 0))

theorem residue_signedWindow (w : Single.SignedWindow) (start : Nat) :
    residue ((Single.signedWindow w).program start) = 0 := by
  unfold Single.signedWindow
  exact (residue_reindex _ _).trans (residue_actual start)

theorem residue_firstWindow (start : Nat) : residue (Single.firstWindow.program start) = 0 := by
  unfold Single.firstWindow
  dsimp only
  rw [residue_reindex]
  unfold First15.program
  rw [residue_cast, residue_lookup]
  unfold First15.ops
  apply opsResidue_unary
  intro l q
  unfold pointLeaf
  exact tres_lookupLeaf _ _

/-! ## Window credits -/

/-- Every T gate of a signed window comes from an unconditional literal Toffoli. -/
theorem signedFullCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) 73323441 := by
  have ht := Single.signedWindow_t 0 w start (fun _ => false)
  have hr := residue_t ((Single.signedWindow w).program start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  rw [ht, residue_signedWindow] at hr
  unfold AtLeast
  omega

/-- The first window is a bare lookup, credited the same way. -/
theorem firstFullCount (start : Nat) : AtLeast (Single.firstWindow.program start) 32767 := by
  have ht := Single.firstWindow_t_uniform 0 start (fun _ => false)
  have hr := residue_t (Single.firstWindow.program start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  rw [ht, residue_firstWindow] at hr
  unfold AtLeast
  omega

end
end ShorECDLP.Entrant.FullCredit
end
