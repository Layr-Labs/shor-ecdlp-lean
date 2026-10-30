import ShorECDLP.Submission.Entrant.Credit
import ShorECDLP.Submission.Entrant.Single.Physical

/-! EDITABLE. Zero residue for complete signed windows.

The window bodies add lookups, the zero-allowed field guards and the endpoint correction block
around the arithmetic of `Credit`.  With every block free of phase instructions and of
constant- or record-controlled non-Clifford gates, each window's exact T-count is carried by
its literal Toffoli gates alone, which credits all of them to the lowering. -/

section
namespace ShorECDLP.Entrant.AndGadget
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

theorem opsResidue_ipx {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire) :
    ∀ ops : List IpxOp, ((ipxOps rows tree paths ops).map lookupOpResidue).sum = 0
  | [] => rfl
  | .query c u v :: ops => by
    rw [ipxOps, List.map_append, List.sum_append, opsResidue_ipx rows tree paths ops,
      opsResidue_unary _ (fun l q => by
        rw [ipxLeaf, List.map_append, List.sum_append, tres_endpointSelectGates,
          tres_endpointSelectGates])]
  | .test k :: ops => by
    rw [ipxOps, List.map_cons, List.sum_cons, opsResidue_ipx rows tree paths ops,
      lookupOpResidue_ordinary, sum_ipxTest]

/-! ## Window bodies -/

theorem residue_zeroDivision (n start : Nat) : residue (zeroDivisionProgram n start).2 = 0 := by
  unfold zeroDivisionProgram
  rw [residue_surround, residue_division, sum_fig15ZeroPrepare, sum_fig15ZeroRestore]

theorem residue_zeroMultiplication (n start : Nat) :
    residue (zeroMultiplicationProgram n start).2 = 0 := by
  unfold zeroMultiplicationProgram
  rw [residue_surround, residue_multiplication, sum_fig15ZeroPrepare, sum_fig15ZeroRestore]

theorem residue_coordinate (start : Nat) : residue (coordinateProgram start).2 = 0 := by
  unfold coordinateProgram
  apply residue_sequence
  intro p hp s
  simp only [coordinateSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h <;> subst p
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s
  · exact residue_zeroDivision _ s
  · exact residue_pointSquare _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_zeroMultiplication _ s
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
  exact residue_firstLookup start

/-! ## Window credits -/

/-- Every T gate of a signed window comes from an unconditional literal Toffoli. -/
theorem signedFullCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) 73330577 := by
  have ht := Single.signedWindow_t 0 w start (fun _ => false)
  have hr := residue_t ((Single.signedWindow w).program start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  rw [ht, residue_signedWindow] at hr
  unfold AtLeast
  omega

/-- The first window is a bare lookup, credited the same way. -/
theorem firstFullCount (start : Nat) : AtLeast (Single.firstWindow.program start) 65535 := by
  have ht := Single.firstWindow_t_uniform 0 start (fun _ => false)
  have hr := residue_t (Single.firstWindow.program start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  rw [ht, residue_firstWindow] at hr
  unfold AtLeast
  omega

end
end ShorECDLP.Entrant.AndGadget
end
