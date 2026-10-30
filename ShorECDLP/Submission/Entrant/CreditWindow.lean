import ShorECDLP.Submission.Entrant.Credit
import ShorECDLP.Submission.Entrant.Single.Physical

/-! EDITABLE. Zero residue for complete signed windows.

The window bodies add lookups, the borrowed-flag field guards and the endpoint correction block
around the arithmetic of `Credit`.  With every block free of phase instructions and of
constant- or record-controlled non-Clifford gates, each window's exact T-count is carried by
its literal Toffoli gates alone, which credits all of them to the lowering. -/

section
namespace ShorECDLP.Entrant.WindowCredit
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Secp256k1
open ShorECDLP.Entrant.AndGadget
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

theorem opsResidue_measuredTail {n : Nat} : (a : Wire) → (cs : List Wire) → (t : Wire) →
    (ws : List Wire) → ((measuredTailOps (n := n) a cs t ws).map lookupOpResidue).sum = 0
  | _, [], _, _ => by simp [measuredTailOps]
  | a, [c], t, _ => by simp [measuredTailOps, primitivePhaseCost]
  | a, c :: d :: cs, t, w :: ws => by
      simp [measuredTailOps, primitivePhaseCost, opsResidue_measuredTail w (d :: cs) t ws]
  | _, _ :: _ :: _, _, [] => by simp [measuredTailOps]

theorem opsResidue_measuredChain {n : Nat} : (cs : List Wire) → (t : Wire) → (ws : List Wire) →
    ((measuredChainOps (n := n) cs t ws).map lookupOpResidue).sum = 0
  | [], _, _ => by simp [measuredChainOps, primitivePhaseCost]
  | [_], _, _ => by simp [measuredChainOps, primitivePhaseCost]
  | _ :: _ :: _, _, _ => by simp only [measuredChainOps]; exact opsResidue_measuredTail _ _ _ _

theorem opsResidue_measuredEquality {n : Nat} (r : List Wire) (v : Nat) (t : Wire)
    (ws : List Wire) : ((measuredEqualityOps (n := n) r v t ws).map lookupOpResidue).sum = 0 := by
  rw [measuredEqualityOps, List.map_append, List.map_append, List.sum_append, List.sum_append,
    opsResidue_measuredChain]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, lookupOpResidue_ordinary,
    sum_zeroMask]
  rfl

theorem opsResidue_ipxTest {n : Nat} (k : Fin 4) :
    ((ipxMeasuredTestOps (n := n) k).map lookupOpResidue).sum = 0 := by
  rw [ipxMeasuredTestOps, List.map_append, List.map_append, List.sum_append, List.sum_append,
    opsResidue_measuredEquality, opsResidue_measuredEquality]

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
      opsResidue_ipxTest]

/-! ## Borrowed-flag field blocks -/

theorem residue_borrowField (n start : Nat) (arithmetic : FixedSegment n)
    (ha : ∀ s, residue (arithmetic s).2 = 0) :
    residue (ShorECDLP.Entrant.BorrowFlag.fieldProgram n start arithmetic).2 = 0 := by
  unfold ShorECDLP.Entrant.BorrowFlag.fieldProgram
  rw [residue_surround, residue_sequence n _ ?_ start]
  · rfl
  · intro p hp s
    simp only [ShorECDLP.Entrant.BorrowFlag.coreSegments, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with h | h | h <;> subst p
    · show residue (relabelStraight _ _) = 0
      rw [residue_relabel]
      unfold ShorECDLP.Entrant.BorrowFlag.prepareProgram
      exact residue_app _ _ (residue_equality _ _ _ _ _ _) (residue_literal_pf rfl)
    · exact ha s
    · show residue (relabelStraight _ _) = 0
      rw [residue_relabel]
      unfold ShorECDLP.Entrant.BorrowFlag.restoreProgram
      rw [residue_prepend, residue_equality]
      rfl

theorem residue_borrowDivision (n start : Nat) :
    residue (ShorECDLP.Entrant.BorrowFlag.divisionProgram n start).2 = 0 := by
  unfold ShorECDLP.Entrant.BorrowFlag.divisionProgram
  exact residue_borrowField n start _ (residue_division n)

theorem residue_borrowMultiplication (n start : Nat) :
    residue (ShorECDLP.Entrant.BorrowFlag.multiplicationProgram n start).2 = 0 := by
  unfold ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  exact residue_borrowField n start _ (residue_multiplication n)

/-! ## Window bodies -/

theorem residue_adaptiveCoordinate (start : Nat) :
    residue (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2 = 0 := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram
  apply residue_sequence
  intro p hp s
  simp only [ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h <;> subst p
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s
  · exact residue_borrowDivision _ s
  · exact residue_pointSquare _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_borrowMultiplication _ s
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
  · exact residue_adaptiveCoordinate s
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
  rw [residue_reindex, ShorECDLP.Entrant.First15.program, residue_cast, residue_lookup,
    ShorECDLP.Entrant.First15.ops]
  exact opsResidue_unary _ (fun l q => tres_lookupLeaf _ _) _ _ _

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
end ShorECDLP.Entrant.WindowCredit
end
