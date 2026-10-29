import ShorECDLP.Submission.Entrant.Streaming.Semantics
import ShorECDLP.Submission.Entrant.Streaming.Resources
import ShorECDLP.Submission.Entrant.Streaming.Correction
import ShorECDLP.Submission.«2607_13816».Window.SignedAddress
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
import ShorECDLP.Submission.«2607_13816».Challenge.Reindex
import ShorECDLP.Challenge.Decoder
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Challenge.Resources

open ShorECDLP.Entrant.ZeroAdaptive

/-! EDITABLE. Single-trial entrant: mixed-width circuit and resource proofs.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Coordinate ====

section
/-! Table-parametric instantiations of the Apache-2.0 licensed Streaming
compilation lemmas. Arithmetic circuits and their coherent proofs are reused.
Only the public coefficient read function is generalized here. -/

namespace ShorECDLP.Entrant.Single.Physical
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] fieldLoadProgram modularAddProgram divisionProgram multiplicationProgram
  squareSubtractProgram modularNegateProgram secp256k1InPlaceDivision secp256k1InPlaceMultiplication

noncomputable def tablePoint (coeffs : Fin 32768 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a % 32768, Nat.mod_lt _ (by decide)⟩)

theorem fieldLoadOps_circuit (coeffs : Fin 32768 → PointCoeff) (field : PointField) (Q : Point) :
    lookupCircuit (readConstant coeffs Q) (fieldLoadOps field) =
    tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (tablePoint coeffs Q l) field))
      pointLookupAddress 836 pointLookupPath := by
  rw [fieldLoadOps, unaryLookupOps_circuit]
  unfold tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  obtain ⟨i, hi, he⟩ := tableAddressTree_label _ 0 1 l hl
  have hlt : l < 32768 := by simpa [he, pointLookupAddress] using hi
  rw [fieldLeaf_instantiate]
  simp only [tablePoint, Nat.mod_eq_of_lt hlt]

theorem fieldLoadProgram_run (coeffs : Fin 32768 → PointCoeff) (field : PointField) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    ((fieldLoadProgram field start).instantiate (readConstant coeffs Q) history).run =
      (tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (tablePoint coeffs Q l) field))
        pointLookupAddress 836 pointLookupPath).run := by
  rw [fieldLoadProgram, castFinish_instantiate, lookupProgram_run, fieldLoadOps_circuit coeffs field Q]

theorem fieldLoadProgram_tCount (coeffs : Fin 32768 → PointCoeff) (field : PointField)
    (start : Nat) (Q : Point) (history : Fin start → Bool) :
    ((ShorECDLP.Paper2607_13816.ChallengeMigration.fieldLoadProgram field start).instantiate
      (readConstant coeffs Q) history).tCount = 229369 := by
  rw [ShorECDLP.Paper2607_13816.ChallengeMigration.fieldLoadProgram, castFinish_instantiate,
    lookupProgram_tCount, fieldLoadOps_circuit coeffs field Q,
    tableLookupProgram_tCount _ _ _ _ (by decide) (by decide)]
  rfl

theorem fieldLookupAddProgram_run (coeffs : Fin 32768 → PointCoeff) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledRun (fieldLookupAddProgram field acc start) (readConstant coeffs Q) history =
      (lookupModularAddProgram (fun l => fieldValue (tablePoint coeffs Q l) field)
        pointLookupAddress pointLookupPath (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).run := by
  let read := readConstant coeffs Q
  let lookup := tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (tablePoint coeffs Q l) field))
    pointLookupAddress 836 pointLookupPath
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  let target := controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558
  have addRun : ∀ h, (add.2.instantiate read h).run = target.run := by
    intro h
    exact modularAddProgram_run 32768 _ _ acc _ _ _ _ _ _ _
      (by simp [hl]) (by simp [secp256k1ReductionConstantBits, hl]) (by omega) read h
  have suffixRun : ∀ h, compiledRun
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩) read h =
      (target.seq lookup).run := by
    intro h
    rw [appendCompiled_run add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩ read h lookup
      (fun h => fieldLoadProgram_run coeffs field _ Q h),
      AdaptiveCircuit.run_seq, addRun h, ← AdaptiveCircuit.run_seq]
  change compiledRun
    (appendCompiled ⟨32767, fieldLoadProgram field start⟩
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)) read history = _
  rw [appendCompiled_run _ _ _ _ (target.seq lookup) suffixRun,
    AdaptiveCircuit.run_seq, fieldLoadProgram_run coeffs field start Q history,
    ← AdaptiveCircuit.run_seq]
  rw [← adaptive_seq_assoc]
  rfl

theorem fieldLookupAddProgram_tCount (coeffs : Fin 32768 → PointCoeff) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) (readConstant coeffs Q) history =
      229369 + (controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount + 229369 := by
  let read := readConstant coeffs Q
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  let target := controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558
  have addT : ∀ h, (add.2.instantiate read h).tCount = target.tCount := by
    intro h
    exact modularAddProgram_tCount 32768 _ _ acc _ _ _ _ _ _ _
      (by simp [hl]) (by simp [secp256k1ReductionConstantBits, hl]) (by omega) read h
  have suffixT : ∀ h, compiledTCount
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩) read h =
      target.tCount + 229369 := by
    intro h
    rw [appendCompiled_tCount add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩ read h 229369
      (fun h => fieldLoadProgram_tCount coeffs field _ Q h), addT h]
  change compiledTCount
    (appendCompiled ⟨32767, fieldLoadProgram field start⟩
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)) read history = _
  rw [appendCompiled_tCount _ _ _ _ (target.tCount+229369) suffixT,
    fieldLoadProgram_tCount coeffs field start Q history]
  exact (Nat.add_assoc _ _ _).symm

theorem fig14LookupX_compiled (coeffs : Fin 32768 → PointCoeff) (field : PointField) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    compiledRun (fieldLookupAddProgram field (List.range' 263 256) start)
      (readConstant coeffs Q) history =
      (fig14LookupX (fun l => fieldValue (tablePoint coeffs Q l) field)).run := by
  exact fieldLookupAddProgram_run coeffs field _ start Q (by simp) history

theorem signedFieldProgram_run (coeffs : Fin 32768 → PointCoeff) (field : PointField) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    compiledRun (signedFieldProgram field start) (readConstant coeffs Q) history =
      (signedPointLookupY (fun l => fieldValue (tablePoint coeffs Q l) field)).run := by
  unfold signedFieldProgram
  dsimp only
  unfold signedPointLookupY signedLookupModularAddProgram
  simp only [List.length_range']
  rw [adaptive_seq_assoc]
  apply appendCompiled_run_eq
  · exact yNegateProgram_run start _ history
  · intro h
    apply appendCompiled_run_eq
    · exact fieldLookupAddProgram_run coeffs field _ _ Q (by simp) h
    · intro h
      exact yNegateProgram_run _ _ h

theorem fieldLookupAddProgram_tCount_source (coeffs : Fin 32768 → PointCoeff) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) (readConstant coeffs Q) history =
      (lookupModularAddProgram (fun l => fieldValue (tablePoint coeffs Q l) field)
        pointLookupAddress pointLookupPath (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount := by
  rw [fieldLookupAddProgram_tCount coeffs field acc start Q hl history]
  simp only [lookupModularAddProgram, adaptive_tCount_seq]
  rw [tableLookupProgram_tCount _ _ _ _ (by decide) (by decide)]
  rfl

theorem yNegateProgram_tCount (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    compiledTCount (yNegateProgram start) read history =
      (negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
        (constantBits 256 ShorECDLP.p) 854 559 560 561 558).tCount := by
  exact negativeNegateProgram_tCount 32768 start _ _ _ _ _ _ _ _
    (by simp) (by rw [constantBits_length, List.length_range']) (by simp) read history

theorem signedFieldProgram_tCount (coeffs : Fin 32768 → PointCoeff) (field : PointField) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    compiledTCount (signedFieldProgram field start) (readConstant coeffs Q) history =
      (signedPointLookupY (fun l => fieldValue (tablePoint coeffs Q l) field)).tCount := by
  unfold signedFieldProgram
  dsimp only
  unfold signedPointLookupY signedLookupModularAddProgram
  simp only [List.length_range']
  rw [adaptive_seq_assoc]
  apply appendCompiled_tCount_eq
  · exact yNegateProgram_tCount start _ history
  · intro h
    apply appendCompiled_tCount_eq
    · exact fieldLookupAddProgram_tCount_source coeffs field _ _ Q (by simp) h
    · intro h
      exact yNegateProgram_tCount _ _ h

noncomputable def adaptiveCoordinateSources (Q : Point) (coeffs : Fin 32768 → PointCoeff) : List AdaptiveCircuit :=
  [fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .negX),
   signedPointLookupY (fun l => baseFieldValue (tablePoint coeffs Q l) .negY),
   ShorECDLP.Entrant.ZeroAdaptive.division, fig14SquareSubtract,
   fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .tripleX),
   ShorECDLP.Entrant.ZeroAdaptive.multiplication, fig14Negate,
   fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .x),
   signedPointLookupY (fun l => baseFieldValue (tablePoint coeffs Q l) .negY)]

theorem adaptiveCoordinateSources_eq (Q : Point) (coeffs : Fin 32768 → PointCoeff) :
    sequenceCircuit (adaptiveCoordinateSources Q coeffs) =
      ShorECDLP.Entrant.ZeroAdaptive.coordinateSource (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y) := by
  have hx (P : Point) : baseFieldValue P .x = fieldValue P .x := rfl
  have hn (P : Point) : baseFieldValue P .negX = fieldValue P .negX := rfl
  have hy (P : Point) : baseFieldValue P .negY = fieldValue P .negY := rfl
  have ht (P : Point) : baseFieldValue P .tripleX = fieldValue P .tripleX := rfl
  simp only [adaptiveCoordinateSources, hx, hn, hy, ht, sequenceCircuit, ShorECDLP.Entrant.ZeroAdaptive.coordinateSource,
    adaptive_seq_assoc, adaptive_seq_done, field_negX, field_negY, field_tripleX, field_x_mod]

theorem adaptiveCoordinateProgram_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (adaptiveCoordinateProgram start) (readConstant coeffs Q) history =
      (ShorECDLP.Entrant.ZeroAdaptive.coordinateSource (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y)).run := by
  unfold adaptiveCoordinateProgram
  rw [← adaptiveCoordinateSources_eq]
  apply sequenceProgram_run
  unfold adaptiveCoordinateSegments adaptiveCoordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fig14LookupX_compiled coeffs .negX cursor Q h
  · intro cursor h
    exact signedFieldProgram_run coeffs .negY cursor Q h
  · intro cursor h
    exact zDivisionProgram_run 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled coeffs .tripleX cursor Q h
  · intro cursor h
    exact zMultiplicationProgram_run 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled coeffs .x cursor Q h
  · intro cursor h
    exact signedFieldProgram_run coeffs .negY cursor Q h

theorem adaptiveCoordinateProgram_tCount (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (adaptiveCoordinateProgram start) (readConstant coeffs Q) history =
      (ShorECDLP.Entrant.ZeroAdaptive.coordinateSource (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y)).tCount := by
  unfold adaptiveCoordinateProgram
  rw [← adaptiveCoordinateSources_eq]
  apply sequenceProgram_tCount
  unfold adaptiveCoordinateSegments adaptiveCoordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .negX _ cursor Q (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount coeffs .negY cursor Q h
  · intro cursor h
    exact zDivisionProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .tripleX _ cursor Q (by simp) h
  · intro cursor h
    exact zMultiplicationProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .x _ cursor Q (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount coeffs .negY cursor Q h

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Batch ====

section
/-! Table-parametric in-place exceptional correction. The correction and
its semantic proof adapt the Streaming construction (VerifiedQC PR #551,
Apache-2.0) to the mixed-width coefficient table. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

def tableRows (label : Nat) : Fin 32768 := ⟨label % 32768, Nat.mod_lt _ (by decide)⟩

noncomputable def placedBatchSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  ipxSourceOps (readConstant coeffs Q) tableRows batchWindowTree pointLookupPath ipxSchedule

noncomputable def placedBatchState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (st : BasisState) : BasisState :=
  Classical.run (ipxUnitaryOps (readConstant coeffs Q) tableRows batchWindowTree pointLookupPath ipxSchedule) st

attribute [local irreducible] ipxUnitaryOps ipxSourceOps

theorem placedBatchSource_state (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (placedBatchSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (placedBatchState coeffs Q))
      (IpxInv pointLookupPath) := by
  have h := ipxSourceOps_coherent coeffs Q tableRows batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule
  apply h.congrIdeal
  intro st _
  rw [run_ket_agrees_classical _ st (ipxUnitaryOps_HPFree _ _ _ _ _)]
  simp only [placedBatchState,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem placedBatchState_frame (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : IpxInv pointLookupPath s) (w : Wire) (hw : w ∉ pointLogicalWires)
    (hf : ∀ k, w ≠ ipxFlag k) : placedBatchState coeffs Q s w = s w :=
  (ipxUnitary_model coeffs Q tableRows batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule s hs).2.2 w hw hf

theorem placedBatchState_pointWrite (coeffs : Fin 32768 → PointCoeff) (Q : Point) (st : BasisState)
    (hv : Secp256k1ZeroAllowedInputValid st) (hq : st 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (tableRows (batchWindowTree.routeLabel st))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point) (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P)) :
    placedBatchState coeffs Q st = pointWrite (P + .some hC) st := by
  have hinv := ipxInv_of_valid st hv hq
  have hm := ipxUnitary_model coeffs Q tableRows batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule st hinv
  have hA : st ∘ accumulatorPort = coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P)) :=
    (accumulatorPort_coordinates st hv).trans (congrArg coordinateWordBits hdata)
  have hF : (fun k => st (ipxFlag k)) = fun _ => false := funext (ipxFlags_clean st hv)
  have hres := hm.1
  rw [hA,hF] at hres
  change _ = ipxModel _ _ at hres
  rw [ipxModel_point coeffs Q _ hC hr hord P] at hres
  have hacc := congrArg Prod.fst hres
  have hfl := congrArg Prod.snd hres
  dsimp only at hacc hfl
  apply ShorECDLP.Paper2607_13816.ChallengeMigration.accumulator_word_frame_ext
  · exact (accumulatorPort_encoding_iff _ _).mp hacc
  · intro v hv'
    by_cases hk : ∃ k, v = ipxFlag k
    · obtain ⟨k,rfl⟩ := hk
      exact (congrFun hfl k).trans (ipxFlags_clean st hv k).symm
    · push_neg at hk
      exact hm.2.2 v hv' hk

theorem tablePoint_order (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0) (a : Nat) :
    order • tablePoint coeffs Q a = 0 := by
  unfold tablePoint constantPoint
  rw [nsmul_add, smul_comm order, smul_comm order, generator_nsmul_eq_zero, hQ, nsmul_zero, nsmul_zero, add_zero]

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/State ====

section
/-! Table-parametric boundary composition adapted from the Apache-2.0
licensed Streaming `BatchedWindowState` module. Point arithmetic and its
exceptional cases are supplied by the existing coordinate and batch results. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

noncomputable def signedBatchState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  windowYNegateState (placedBatchState coeffs Q (windowYNegateState s))

theorem pointWrite_frame_eq (P : Point) (s t : BasisState)
    (h : ∀ w, w ∉ pointLogicalWires → s w=t w) : pointWrite P s=pointWrite P t := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hw]
  · simp only [pointWrite,if_neg hw,h w hw]

theorem signedBatchState_pointWrite (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    signedBatchState coeffs Q s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have htq : windowYNegateState s 836 = true :=
    ((windowYNegateState_correct s hs).2 836 (by decide)).trans hq
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  have he := placedBatchState_pointWrite coeffs Q _ ht htq hC hr hord P' hd
  have hsign : placedBatchState coeffs Q (windowYNegateState s) 854 = s 854 :=
    (placedBatchState_frame coeffs Q _ (ipxInv_of_valid _ ht htq) 854 (by decide +kernel)
      (ipxFlag_ne_of_ge 854 (by decide))).trans
      ((windowYNegateState_correct s hs).2 854 (by decide +kernel))
  have hv : Secp256k1ZeroAllowedInputValid (placedBatchState coeffs Q (windowYNegateState s)) := by
    rw [he]; exact pointWrite_valid _ _ ht
  have hc : pointStateCoordinates (placedBatchState coeffs Q (windowYNegateState s)) =
      fig14PointEncoding (P' + .some hC) := by
    rw [he]; exact pointWrite_coordinates _ _
  unfold signedBatchState
  rw [windowYNegateState_pointWrite (P' + .some hC) _ hv hc,hsign,he,pointWrite_overwrite]
  have hpoint : (if s 854 then P' + .some hC else -(P' + .some hC)) =
      P + if s 854 then .some hC else -(.some hC) := by
    cases hsg : s 854 <;> simp [P',hsg,add_comm]
  rw [hpoint]
  apply pointWrite_frame_eq
  intro v hv
  apply (windowYNegateState_correct s hs).2 v
  intro hy
  exact hv (List.mem_append_right _ (List.mem_append_left _ hy))
noncomputable def batchedWindowState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  signedBatchState coeffs Q (signedLookupCoordinateState
    (fun a => fieldValue (tablePoint coeffs Q a) .x) (fun a => fieldValue (tablePoint coeffs Q a) .y) s)

theorem batchedWindowState_finite (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : tablePoint coeffs Q (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState coeffs Q s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let xs := fun a => fieldValue (tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (tablePoint coeffs Q a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have ha : tableAddressValue pointLookupAddress t=tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854=s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hr' : constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState t)))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    exact hr
  have hx : xs (tableAddressValue pointLookupAddress s)=x.val := by simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s)=y.val := by simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s=(if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases s 854 <;> simp [ZMod.neg_val']
  have hd : pointStateCoordinates t=fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  have he := signedBatchState_pointWrite coeffs Q t ht.1.1 ht.1.2 hC hr'
    (hr ▸ tablePoint_order coeffs Q hQ _) P hd
  change signedBatchState coeffs Q t= _
  rw [he,hz]
  apply pointWrite_frame_eq
  intro v hv
  exact signedLookupCoordinateState_frame xs ys s hs.1 v
    (fun hx => hv (List.mem_append_left _ hx))
    (fun hy => hv (List.mem_append_right _ (List.mem_append_left _ hy)))
theorem batchedWindowState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState coeffs Q s = pointWrite
      (P + if s 854 then tablePoint coeffs Q (tableAddressValue pointLookupAddress s)
        else -tablePoint coeffs Q (tableAddressValue pointLookupAddress s)) s := by
  cases he : tablePoint coeffs Q (tableAddressValue pointLookupAddress s) with
  | zero => exact False.elim (hn _ he)
  | some hC => exact batchedWindowState_finite coeffs Q hQ s hs hC he P hP

theorem signedBatchState_middle_ready (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    Secp256k1ZeroAllowedInputValid (placedBatchState coeffs Q (windowYNegateState s)) := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have htq : windowYNegateState s 836 = true :=
    ((windowYNegateState_correct s hs).2 836 (by decide)).trans hq
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  rw [placedBatchState_pointWrite coeffs Q _ ht htq hC hr hord P' hd]
  exact pointWrite_valid _ _ ht

def SignedBatchReady (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y),
    constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC ∧
    order • (.some hC : Point) = 0 ∧
    ∃ P : Point, pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Body ====

section
/-! The existing full-size corrected physical body, with table rows supplied
by the caller. Adapted from the Apache-2.0 licensed Streaming WindowBody. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] batchWindowTree
attribute [local irreducible] adaptiveCoordinateProgram yNegateProgram
  ipxProgramOf sequenceProgram surroundCompiled relabelCompiled

theorem correction_count (start : Nat) :
    (ipxProgramOf tableRows batchWindowTree pointLookupPath start).1 = 432091 := by
  simp only [ipxProgramOf]
  rw [ipxOps_measurements _ _ _ ipxTree_layout, ipxSchedule_queries, batchWindowTree_nodes]
  norm_num [ipxSchedule_tests]

@[irreducible] def placedProgram (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  ipxProgramOf tableRows batchWindowTree pointLookupPath start

theorem placedProgram_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (placedProgram start) (readConstant coeffs Q) history =
      (placedBatchSource coeffs Q).run := by
  unfold placedProgram compiledRun
  simp only [ipxProgramOf, lookupProgram_run, ipxOps_source, placedBatchSource]

def segments : List (FixedSegment 32768) :=
  [adaptiveCoordinateProgram, yNegateProgram, placedProgram, yNegateProgram]

@[irreducible] noncomputable def sources (coeffs : Fin 32768 → PointCoeff) (Q : Point) : List AdaptiveCircuit :=
  [ShorECDLP.Entrant.ZeroAdaptive.coordinateSource (fun l => fieldValue (tablePoint coeffs Q l) .x)
    (fun l => fieldValue (tablePoint coeffs Q l) .y), windowYNegate,
    placedBatchSource coeffs Q, windowYNegate]

@[irreducible] def core (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  sequenceProgram 32768 segments start

theorem core_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (core start) (readConstant coeffs Q) history =
      (sequenceCircuit (sources coeffs Q)).run := by
  unfold core
  apply sequenceProgram_run
  unfold segments sources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact adaptiveCoordinateProgram_run coeffs cursor Q h
  · intro cursor h; exact yNegateProgram_run cursor _ h
  · intro cursor h; exact placedProgram_run coeffs cursor Q h
  · intro cursor h; exact yNegateProgram_run cursor _ h

@[irreducible] def prepared (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  surroundCompiled (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (core start)

@[irreducible] noncomputable def preparedSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
    ((sequenceCircuit (sources coeffs Q)).seq
      (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))

theorem prepared_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (prepared start) (readConstant coeffs Q) history =
      (preparedSource coeffs Q).run := by
  unfold prepared preparedSource
  exact surroundCompiled_run _ _ _ _ _ _ (core_run coeffs start Q history)

theorem coordinate_count (start : Nat) : (adaptiveCoordinateProgram start).1 = 30273718 := by
  have h := sharedAdaptiveCoordinateProgram_count (.right ⟨0, by decide⟩) start
  simpa only [sharedAdaptiveCoordinateProgram, reindexCompiled] using h

theorem negate_count (start : Nat) : (yNegateProgram start).1 = 1022 := by
  have h := sharedYNegateProgram_count (.right ⟨0, by decide⟩) start
  simpa only [sharedYNegateProgram, reindexCompiled] using h

theorem placed_count (start : Nat) : (placedProgram start).1 = 432091 := by
  unfold placedProgram
  exact correction_count start

private theorem sequence_count (n : Nat) (ps : List (FixedSegment n)) (counts : List Nat)
    (h : List.Forall₂ (fun p count => ∀ start, (p start).1 = count) ps counts) (start : Nat) :
    (sequenceProgram n ps start).1 = counts.sum := by
  induction h generalizing start with
  | nil => simp only [sequenceProgram, List.sum_nil]
  | cons hp _ ih =>
    simp only [sequenceProgram, appendCompiled, List.sum_cons]
    rw [hp, ih]

theorem core_count (start : Nat) : (core start).1 = 30707853 := by
  have h := sequence_count 32768 segments ([30273718, 1022, 432091, 1022] : List Nat) (by
    unfold segments
    exact List.Forall₂.cons coordinate_count (List.Forall₂.cons negate_count
      (List.Forall₂.cons placed_count (List.Forall₂.cons negate_count .nil)))) start
  unfold core
  exact h

theorem prepared_count (start : Nat) : (prepared start).1 = 30707853 := by
  unfold prepared
  rw [surroundCompiled_count, core_count]

@[irreducible] def actual : OuterWindow 32768 :=
  closedWindow (castFinish (by rw [prepared_count])
    (relabelStraight (windowAddressPerm 855 (by decide)) (prepared 0).2))

theorem actual_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actual.program start).instantiate (readConstant coeffs Q) history).run =
      ((preparedSource coeffs Q).relabel (windowAddressPerm 855 (by decide))).run := by
  unfold actual
  simp only [closedWindow_run, castFinish_instantiate, relabelStraight_instantiate, AdaptiveCircuit.run_relabel]
  have h := prepared_run coeffs 0 Q Fin.elim0
  unfold compiledRun at h
  exact congrArg (List.map (InstrumentBranch.relabel (windowAddressPerm 855 (by decide)))) h

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Coherent ====

section
/-! Coherent composition of the full-size physical windows for arbitrary
public row values. Adapted from the Apache-2.0 licensed Streaming boundary
and address-placement proofs. The library supplies all arithmetic coherence. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

private theorem restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

noncomputable def signedBatchSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (windowYNegate.seq (placedBatchSource coeffs Q)).seq windowYNegate

theorem signedBatchSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (signedBatchSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (signedBatchState coeffs Q)) (SignedBatchReady coeffs Q) := by
  have hneg : CoherentlyImplementsOn windowYNegate (Finsupp.lmapDomain ℂ ℂ windowYNegateState)
      (SignedBatchReady coeffs Q) := restrictCoherent windowYNegate_coherent (fun s hs => hs.1.1.1)
  have hfirst := composeCoherent hneg (placedBatchSource_state coeffs Q) (fun s hs => by
    have hn := windowYNegateState_batchedReady s hs.1
    exact ipxInv_of_valid _ hn.1.1 hn.1.2)
  have hlast := composeCoherent hfirst windowYNegate_coherent (by
    intro s hs
    obtain ⟨hr,x,y,hC,hrow,hord,P,hdata⟩ := hs
    exact signedBatchState_middle_ready coeffs Q s hr.1.1 hr.1.2 hC hrow hord P hdata)
  exact hlast
theorem batchedWindow_coordinate_ready (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : tablePoint coeffs Q (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    SignedBatchReady coeffs Q (signedLookupCoordinateState
      (fun a => fieldValue (tablePoint coeffs Q a) .x) (fun a => fieldValue (tablePoint coeffs Q a) .y) s) := by
  let xs := fun a => fieldValue (tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (tablePoint coeffs Q a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have ha : tableAddressValue pointLookupAddress t=tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854=s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hr' : constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState t)))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    exact hr
  have hx : xs (tableAddressValue pointLookupAddress s)=x.val := by simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s)=y.val := by simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s=(if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases s 854 <;> simp [ZMod.neg_val']
  have hd : pointStateCoordinates t=fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  exact ⟨ht,x,y,hC,hr',hr ▸ tablePoint_order coeffs Q hQ _,P,hd⟩

theorem batchedWindowSources_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0) :
    CoherentlyImplementsOn (sequenceCircuit (sources coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState coeffs Q)) BatchedWindowValid := by
  let xs := fun a => fieldValue (tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (tablePoint coeffs Q a) .y
  have hfirst : CoherentlyImplementsOn (ShorECDLP.Entrant.ZeroAdaptive.coordinateSource xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    restrictCoherent (ShorECDLP.Entrant.ZeroAdaptive.coordinateSource_coherent xs ys) (fun s hs => hs.1.1)
  have h := composeCoherent hfirst (signedBatchSource_coherent coeffs Q) (by
    intro s hs
    obtain ⟨hs,P,hP⟩ := hs
    cases he : tablePoint coeffs Q (tableAddressValue pointLookupAddress s) with
    | zero => exact False.elim (hn _ he)
    | some hC => exact batchedWindow_coordinate_ready coeffs Q hQ s hs hC he P hP)
  simpa only [sources,sequenceCircuit,signedBatchSource,adaptive_seq_assoc,adaptive_seq_done,
    batchedWindowState,xs,ys] using h
theorem batchedWindowState_valid (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (batchedWindowState coeffs Q s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [batchedWindowState_correct coeffs Q hQ hn s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

noncomputable def preparedBatchState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  batchPrepareState (batchedWindowState coeffs Q (batchPrepareState s))

theorem preparedBatchState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    preparedBatchState coeffs Q s = pointWrite
      (P + if s 854 then tablePoint coeffs Q (tableAddressValue pointLookupAddress (batchPrepareState s))
        else -tablePoint coeffs Q (tableAddressValue pointLookupAddress (batchPrepareState s))) s := by
  unfold preparedBatchState
  rw [batchedWindowState_correct coeffs Q hQ hn _ (batchPrepareState_ready s hs) P
    ((batchPrepareState_coordinates s).trans hP),batchPrepareState_pointWrite,
    batchPrepareState_involution,batchPrepareState_frame s 854 (by decide)]

theorem batchPrepare_coherent : CoherentlyImplementsOn
    (.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done)
    (Finsupp.lmapDomain ℂ ℂ batchPrepareState) BatchedWindowValid := by
  have h := CoherentlyImplementsOn.unitary (signedAddressCircuit 836 854 pointLookupAddress) BatchedWindowValid
  apply h.congrIdeal
  intro s hs
  simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,batchPrepareState] using
    signedAddressCircuit_ket 836 854 pointLookupAddress (by decide) (by decide) (by decide) s

attribute [local irreducible] batchPrepareState batchedWindowState

theorem preparedSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0) :
    CoherentlyImplementsOn (preparedSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState coeffs Q)) BatchedWindowValid := by
  have hc := composeCoherent (batchedWindowSources_coherent coeffs Q hQ hn) batchPrepare_coherent
    (batchedWindowState_valid coeffs Q hQ hn)
  have h := composeCoherent (f := batchPrepareState)
    (g := fun s => batchPrepareState (batchedWindowState coeffs Q s))
    batchPrepare_coherent hc batchPrepareState_valid
  unfold preparedSource
  exact h

private theorem parkedWindow_valid (start : Nat) (hs : 855≤start) (s : BasisState)
    (hv : PointLookupValid s) : PointLookupValid (relabelBasis (windowAddressPerm start hs).symm s) := by
  have he (w : Wire) (hw : w<839) : relabelBasis (windowAddressPerm start hs).symm s w=s w := by
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w hw]
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro w hw
    have hb : w<839 := by simp only [List.mem_append,List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    rw [he w hb]
    exact hv.1.1 w hw
  · rw [he 837 (by decide)]; exact hv.1.2.1
  · have hh : wireValues (List.range' 263 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 263 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.1
  · have hh : wireValues (List.range' 580 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 580 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.2
  · rw [he 836 (by decide)]; exact hv.2

private theorem point_bank_bound (w : Wire) (hw : w∈pointLogicalWires) : w<839 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega
private theorem relabel_pointWrite (start : Nat) (hs : 855≤start)
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis (windowAddressPerm start hs)
      (pointWrite P (relabelBasis (windowAddressPerm start hs).symm s))=pointWrite P s := by
  have hsym : (windowAddressPerm start hs).symm=windowAddressPerm start hs := rfl
  funext w
  by_cases hw : w∈pointLogicalWires
  · have he := windowAddressPerm_core start hs w (point_bank_bound w hw)
    simp [relabelBasis,hsym,he,pointWrite,hw]
  · have hn : (windowAddressPerm start hs).symm w∉pointLogicalWires := by
      intro h
      have he := windowAddressPerm_core start hs _ (point_bank_bound _ h)
      rw [Equiv.apply_symm_apply] at he
      exact hw (he ▸ h)
    simp [relabelBasis,pointWrite,hw,hn]

private theorem relabel_coordinates (start : Nat) (hs : 855≤start) (s : BasisState) :
    pointStateCoordinates (relabelBasis (windowAddressPerm start hs).symm s)=pointStateCoordinates s := by
  have he (bits : List Wire) (hb : ∀ w∈bits,w<839) :
      wireValues bits (relabelBasis (windowAddressPerm start hs).symm s)=wireValues bits s := by
    apply List.map_congr_left
    intro w hw
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w (hb w hw)]
  have hx := he (List.range' 263 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hy := he (List.range' 580 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs 838 (by decide)]


theorem windowAddressPerm_workspace (w : Wire) (hw : w ∈ batchWorkspace) :
    windowAddressPerm 855 (by decide) w=w := by
  simp [batchWorkspace] at hw

theorem actualWindow_pullback_ready (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (relabelBasis (windowAddressPerm 855 (by decide)).symm s) := by
  refine ⟨parkedWindow_valid 855 (by decide) s hs.1,?_⟩
  intro w hw
  change s (windowAddressPerm 855 (by decide) w)=false
  rw [windowAddressPerm_workspace w hw]
  exact hs.2 w hw

theorem actualWindow_pullback_valid (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (relabelBasis (windowAddressPerm 855 (by decide)).symm s) := by
  obtain ⟨hs,P,hP⟩ := hs
  exact ⟨actualWindow_pullback_ready s hs,P,(relabel_coordinates 855 (by decide) s).trans hP⟩

noncomputable def actualBatchedWindowState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm 855 (by decide))
    (preparedBatchState coeffs Q (relabelBasis (windowAddressPerm 855 (by decide)).symm s))

theorem actualBatchedWindow_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actual.program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState coeffs Q)) BatchedWindowValid := by
  have h := (preparedSource_coherent coeffs Q hQ hn).relabel (windowAddressPerm 855 (by decide))
  have hr : CoherentlyImplementsOn ((preparedSource coeffs Q).relabel (windowAddressPerm 855 (by decide)))
      ((relabelState (windowAddressPerm 855 (by decide))).comp
        ((Finsupp.lmapDomain ℂ ℂ (preparedBatchState coeffs Q)).comp
          (relabelState (windowAddressPerm 855 (by decide)).symm))) BatchedWindowValid := by
    obtain ⟨cs,hc,hm⟩ := h
    exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (actualWindow_pullback_valid s hs)),hm⟩
  have he : CoherentlyImplementsOn ((preparedSource coeffs Q).relabel (windowAddressPerm 855 (by decide)))
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState coeffs Q)) BatchedWindowValid := by
    apply hr.congrIdeal
    intro s hs
    simp [actualBatchedWindowState,LinearMap.comp_apply,relabelState,ket]
  unfold CoherentlyImplementsOn at he ⊢
  rw [actual_run coeffs start Q history]
  exact he

theorem actualBatchedWindowState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState coeffs Q s = pointWrite
      (P + if s 870 then tablePoint coeffs Q (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))
        else -tablePoint coeffs Q (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))) s := by
  unfold actualBatchedWindowState
  rw [preparedBatchState_correct coeffs Q hQ hn _ (actualWindow_pullback_ready s hs) P
    ((relabel_coordinates 855 (by decide) s).trans hP),relabel_pointWrite]
  have he : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854=s 870 := by
    simp only [relabelBasis,Equiv.symm_symm]
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [he]

private theorem address_word_eq (bits : List Wire) (s : BasisState) :
    tableAddressValue bits s=boolWordToNat (wireValues bits s) := by
  induction bits with
  | nil => rfl
  | cons w ws ih => simpa only [tableAddressValue,wireValues,List.map_cons,boolWordToNat] using congrArg (fun n => (s w).toNat+2*n) ih

theorem actualWindow_selected_address (s : BasisState) (hs : BatchedPointReady s) :
    tableAddressValue pointLookupAddress
      (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s))=
      signedTableAddress 32768 (windowRawDigit 0 s) := by
  have hq : relabelBasis (windowAddressPerm 855 (by decide)).symm s 836=true :=
    (actualWindow_pullback_ready s hs).1.2
  rw [address_word_eq,batchPrepareState,signedAddressState_value _ _ _ _ hq]
  have ha := parkedWindow_address 855 (by decide) s
  rw [address_word_eq,address_word_eq] at ha
  have hz : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854=s 870 := by
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [ha,hz]
  rfl


theorem actualBatchedWindowState_selected (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState coeffs Q s = pointWrite
      (P + if s 870 then tablePoint coeffs Q (signedTableAddress 32768 (windowRawDigit 0 s))
        else -tablePoint coeffs Q (signedTableAddress 32768 (windowRawDigit 0 s))) s := by
  rw [actualBatchedWindowState_correct coeffs Q hQ hn s hs P hP,actualWindow_selected_address s hs]

theorem actualBatchedWindowState_valid (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (actualBatchedWindowState coeffs Q s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected coeffs Q hQ hn s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

theorem actualBatchedWindowState_frame (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) (v : Wire) (hv : v∉pointLogicalWires) :
    actualBatchedWindowState coeffs Q s v=s v := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected coeffs Q hQ hn s hs P hP]
  simp [pointWrite,hv]

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Schedule ====

section
/-! A 263-bit axis uses eight 16-bit windows followed by nine 15-bit windows.
The address definition below reuses the signed-address convention of the
Apache-2.0 licensed 2607_13816 submission. -/

namespace ShorECDLP.Entrant.Single

open ShorECDLP.Paper2607_13816

@[irreducible] def widths : List Nat :=
  [16, 16, 16, 16, 16, 16, 16, 16, 15, 15, 15, 15, 15, 15, 15, 15, 15]

@[irreducible] def exponents : List Nat :=
  [247, 231, 215, 199, 183, 167, 151, 135, 120, 105, 90, 75, 60, 45, 30, 15, 0]

theorem widths_length : widths.length = 17 := by
  simp [widths]

theorem widths_sum : widths.sum = 263 := by
  simp [widths]

theorem exponents_length : exponents.length = 17 := by
  simp [exponents]

/-- The zero padding bit is between the low magnitude bits and the sign. -/
def paddedValue (low : Nat) (sign : Bool) : Nat := low + 32768 * sign.toNat

def logicalValue (low : Nat) (sign : Bool) : Nat := low + 16384 * sign.toNat

/-- Aliasing the two physical address halves preserves the logical address. -/
theorem padded_address (low : Nat) (sign : Bool) (hlow : low < 16384) :
    signedTableAddress 32768 (paddedValue low sign) % 16384 =
      signedTableAddress 16384 (logicalValue low sign) := by
  cases sign with
  | false =>
    have hbig : low < 32768 := by omega
    have hsub : 32767 - low = 16384 + (16383 - low) := by omega
    have hrem : 16383 - low < 16384 := by omega
    simp only [paddedValue, logicalValue, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      signedTableAddress, if_pos hbig, if_pos hlow]
    rw [hsub, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hrem]
  | true =>
    have hbig : ¬ low + 32768 < 32768 := by omega
    have hsmall : ¬ low + 16384 < 16384 := by omega
    simp only [paddedValue, logicalValue, Bool.toNat_true, Nat.mul_one,
      signedTableAddress, if_neg hbig, if_neg hsmall]
    have h1 : low + 32768 - 32768 = low := by omega
    have h2 : low + 16384 - 16384 = low := by omega
    rw [h1, h2, Nat.mod_eq_of_lt hlow]

/-- Static positions for variable-width windows with fixed body record counts. -/
def positions : List (Nat × Nat) → Nat → List Nat
  | [], _ => []
  | (count, width) :: ws, start =>
      List.range' (start + count) width ++ positions ws (start + count + width)

def recordCount : List (Nat × Nat) → Nat
  | [] => 0
  | (count, width) :: ws => count + width + recordCount ws

theorem positions_length (ws : List (Nat × Nat)) (start : Nat) :
    (positions ws start).length = (ws.map Prod.snd).sum := by
  induction ws generalizing start with
  | nil => simp [positions]
  | cons w ws ih =>
    rcases w with ⟨count, width⟩
    simp [positions, ih]

theorem positions_bounds (ws : List (Nat × Nat)) (start i : Nat)
    (hi : i ∈ positions ws start) : start ≤ i ∧ i < start + recordCount ws := by
  induction ws generalizing start with
  | nil => simp [positions] at hi
  | cons w ws ih =>
    rcases w with ⟨count, width⟩
    simp only [positions, List.mem_append] at hi
    rcases hi with hi | hi
    · have h := List.mem_range'.mp hi
      simp only [recordCount]
      omega
    · have h := ih _ hi
      simp only [recordCount]
      omega

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Outer ====

section
/-! Variable-width outer-axis skeleton adapted from the Apache-2.0 licensed
2607_13816 challenge migration. The caller must establish each window's
coherent semantics and bank cleanliness. -/

namespace ShorECDLP.Entrant.Single

open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

structure Window (n : Nat) where
  wires : List Wire
  count : Nat
  program : (start : Nat) → Straight n start (start + count)

def axisCount {n : Nat} : List (Window n) → Nat
  | [] => 0
  | w :: ws => w.count + w.wires.length + axisCount ws

def nextPrior {start : Nat} (count width : Nat) (prior : List (Fin start)) :
    List (Fin (start + count + width)) :=
  (List.ofFn (fun i : Fin width =>
    (⟨start + count + i.val, by omega⟩ : Fin (start + count + width)))).reverse ++
    prior.map (fun i => ⟨i.val, by omega⟩)

/-- Within an axis, feedback tracks only preceding Fourier outputs. -/
def axis {n : Nat} :
    (ws : List (Window n)) → (start : Nat) → List (Fin start) →
      Straight n start (start + axisCount ws)
  | [], _, _ => .done
  | w :: ws, start, prior =>
    let fourier : Straight n (start+w.count) (start+w.count+w.wires.length) :=
      castFinish (by simp) (fourierProgram n .inverse w.wires (start+w.count) (bankPrior w.count prior))
    castFinish (by simp only [axisCount]; omega)
      ((prepareOuterBank w.wires.reverse (w.program start)).append (fourier.append
        (axis ws (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior))))

def axisPositions {n : Nat} (ws : List (Window n)) (start : Nat) : List Nat :=
  positions (ws.map (fun w => (w.count, w.wires.length))) start

theorem axisPositions_length {n : Nat} (ws : List (Window n)) (start : Nat) :
    (axisPositions ws start).length = (ws.map (fun w => w.wires.length)).sum := by
  simp only [axisPositions, positions_length, List.map_map, Function.comp_def]

theorem recordCount_eq_axisCount {n : Nat} (ws : List (Window n)) :
    recordCount (ws.map (fun w => (w.count, w.wires.length))) = axisCount ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [recordCount, axisCount, ih]

theorem axisPositions_bounds {n : Nat} (ws : List (Window n)) (start i : Nat)
    (hi : i ∈ axisPositions ws start) : start ≤ i ∧ i < start + axisCount ws := by
  have h := positions_bounds (ws.map (fun w => (w.count, w.wires.length))) start i
    (show i ∈ positions (ws.map (fun w => (w.count, w.wires.length))) start from hi)
  simpa only [recordCount_eq_axisCount] using h

/-- Evidence that a selected position was produced by a Fourier bank. -/
def FourierRecord {n : Nat} (read : ConstantBit n → Bool)
    (whole : List Bool) (i : Nat) : Prop :=
  ∃ (wires : List Wire) (bankStart : Nat) (prior : List (Fin bankStart))
      (h : Fin bankStart → Bool) (f : InstrumentBranch) (bit : Fin wires.length),
      f ∈ ((fourierProgram n .inverse wires bankStart prior).instantiate read h).run ∧
      i = bankStart + bit.val ∧ whole[i]? = f.history[bit.val]? ∧
      List.ofFn h = whole.take bankStart

theorem axis_records {n : Nat} (ws : List (Window n))
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((axis ws start prior).instantiate read history).run) :
    ∀ i ∈ axisPositions ws start, FourierRecord read (List.ofFn history ++ b.history) i := by
  induction ws generalizing start b with
  | nil => intro i hi; simp [axisPositions, positions] at hi
  | cons w ws ih =>
    simp only [axis, castFinish_instantiate] at hb
    obtain ⟨h₁, a, rest, ha, hr, he₁, rfl⟩ := straight_append_branch _ _ read history b hb
    obtain ⟨h₂, f, c, hf, hc, he₂, rfl⟩ := straight_append_branch _ _ read h₁ rest hr
    simp only [castFinish_instantiate] at hf
    have hfull : List.ofFn history ++ (a.seq (f.seq c)).history =
        List.ofFn h₁ ++ f.history ++ c.history := by
      simp only [InstrumentBranch.seq, he₁, List.append_assoc]
    have htail : List.ofFn h₂ ++ c.history =
        List.ofFn history ++ (a.seq (f.seq c)).history := by
      rw [he₂, ← hfull]
    intro i hi
    change i ∈ List.range' (start+w.count) w.wires.length ++
      axisPositions ws (start+w.count+w.wires.length) at hi
    rcases List.mem_append.mp hi with hi | hi
    · have hi' := List.mem_range'.mp hi
      let bit : Fin w.wires.length := ⟨i - (start+w.count), by omega⟩
      have hbit : i = start+w.count+bit.val := by dsimp [bit]; omega
      refine ⟨w.wires, start+w.count, bankPrior w.count prior, h₁, f, bit, hf, hbit, ?_, ?_⟩
      · rw [hfull, hbit]
        exact fourierProgram_record_at n .inverse w.wires _ _ read h₁ f hf
          (List.ofFn h₁) c.history (by simp) bit
      · rw [hfull, List.append_assoc]
        have hlen : (List.ofFn h₁).length = start+w.count := by simp
        simpa only [hlen] using (show (List.ofFn h₁ ++ (f.history ++ c.history)).take
          (List.ofFn h₁).length = List.ofFn h₁ from List.take_left).symm
    · have ht := ih _ _ h₂ c hc i hi
      simpa only [htail] using ht

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Plan ====

section
namespace ShorECDLP.Entrant.Single

/-- Exponents of successive most-significant-first mixed-radix digits. -/
def suffixExponents : List Nat → List Nat
  | [] => []
  | _ :: rest => rest.sum :: suffixExponents rest

theorem exponents_match_widths : suffixExponents widths = exponents := by
  simp [widths, exponents, suffixExponents]

@[irreducible] def leftMetadata : List (Nat × Nat) :=
  (65535, 16) :: List.replicate 7 (30707853, 16) ++ List.replicate 9 (30707853, 15)

@[irreducible] def rightMetadata : List (Nat × Nat) :=
  List.replicate 8 (30707853, 16) ++ List.replicate 9 (30707853, 15)

theorem left_widths : leftMetadata.map Prod.snd = widths := by
  simp [leftMetadata, widths]

theorem right_widths : rightMetadata.map Prod.snd = widths := by
  simp [rightMetadata, widths]

theorem left_record_count : recordCount leftMetadata = 491391446 := by
  norm_num [leftMetadata, recordCount, List.replicate]

theorem right_record_count : recordCount rightMetadata = 522033764 := by
  norm_num [rightMetadata, recordCount, List.replicate]

theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 263 := by
  rw [positions_length, left_widths, widths_sum]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 263 := by
  rw [positions_length, right_widths, widths_sum]

theorem projected_rows : 65536 + 15 * 32768 + 18 * 16384 = 851968 := by norm_num

theorem projected_records : 491391446 + 522033764 + 854 = 1013426064 := by norm_num

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Rows ====

section
namespace ShorECDLP.Entrant.Single

open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Chronological signed windows after the direct first load. -/
inductive SignedWindow where
  | left16 (index : Fin 7)
  | left15 (index : Fin 9)
  | right16 (index : Fin 8)
  | right15 (index : Fin 9)

def firstRow (a : Fin 65536) : Fin 851968 := ⟨a.val, by omega⟩

/-- Each width-15 window aliases the two physical address halves. -/
def signedRow : SignedWindow → Fin 32768 → Fin 851968
  | .left16 j, a => ⟨65536 + j.val * 32768 + a.val, by omega⟩
  | .left15 j, a => ⟨294912 + j.val * 16384 + a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩
  | .right16 j, a => ⟨442368 + j.val * 32768 + a.val, by omega⟩
  | .right15 j, a => ⟨704512 + j.val * 16384 + a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩

theorem left15_alias (j : Fin 9) (a : Fin 32768) :
    signedRow (.left15 j) a = signedRow (.left15 j) ⟨a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩ := by
  apply Fin.ext
  simp [signedRow]

theorem right15_alias (j : Fin 9) (a : Fin 32768) :
    signedRow (.right15 j) a = signedRow (.right15 j) ⟨a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩ := by
  apply Fin.ext
  simp [signedRow]

/-- The reindexing preserves the behavior under the corresponding table read. -/
theorem signed_reindex_instantiate {s e : Nat} (w : SignedWindow)
    (p : Straight 32768 s e) (read : ConstantBit 851968 → Bool) (history : Fin s → Bool) :
    (reindexStraight (signedRow w) p).instantiate read history =
      p.instantiate (read ∘ reindexBit (signedRow w)) history :=
  reindexStraight_instantiate (signedRow w) p read history

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Interface ====

section
/-! The mixed-width window contract. Distribution proofs may take `WindowLaw`
as a hypothesis; the concrete implementation supplies this same contract.
The physical arithmetic and its exceptional cases are inherited from the
Apache-2.0 licensed Streaming construction. -/

namespace ShorECDLP.Entrant.Single

open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def leftSigned : List SignedWindow :=
  List.ofFn (fun j : Fin 7 => SignedWindow.left16 j) ++
    List.ofFn (fun j : Fin 9 => SignedWindow.left15 j)

@[irreducible] def rightSigned : List SignedWindow :=
  List.ofFn (fun j : Fin 8 => SignedWindow.right16 j) ++
    List.ofFn (fun j : Fin 9 => SignedWindow.right15 j)

def SignedWindow.width : SignedWindow → Nat
  | .left16 _ | .right16 _ => 16
  | .left15 _ | .right15 _ => 15

def SignedWindow.exponent : SignedWindow → Nat
  | .left16 j => 231 - 16 * j.val
  | .right16 j => 247 - 16 * j.val
  | .left15 j | .right15 j => 120 - 15 * j.val

def SignedWindow.base (Q : Point) : SignedWindow → Point
  | .left16 _ | .left15 _ => G
  | .right16 _ | .right15 _ => Q

def bank (width : Nat) : List Wire :=
  if width = 15 then List.range' 855 14 ++ [870] else List.range' 855 16

def digit (width : Nat) (s : BasisState) : Nat := tableAddressValue (bank width) s

def halfOrder : Nat := (order + 1) / 2

def offsetScalar (width exponent : Nat) : Nat :=
  (2^(width-1) + order - halfOrder) * 2^exponent

@[irreducible] def leftOffset : Nat := ((widths.zip exponents).drop 1).foldr
  (fun p acc => offsetScalar p.1 p.2 + acc) 0

@[irreducible] def rightOffset : Nat := (widths.zip exponents).foldr
  (fun p acc => offsetScalar p.1 p.2 + acc) 0

@[irreducible] noncomputable def initialPoint (Q : Point) (v : Nat) : Point :=
  (v * 2^247 + leftOffset) • G + rightOffset • Q

noncomputable def increment (Q : Point) (w : SignedWindow) (v : Nat) : Point :=
  ((2 * (v : Int) - (2 : Int)^w.width + 1) : Int) •
    ((halfOrder * 2^w.exponent) • w.base Q)

noncomputable def firstUpdate (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (initialPoint Q (digit 16 s)) s

/-- A graph form avoids choosing a point from arbitrary invalid coordinates. -/
def WindowLaw {n : Nat} (coeffs : Fin n → PointCoeff)
    (physical : Window n) (update : Point → BasisState → BasisState)
    (valid : BasisState → Prop) : Prop :=
  ∀ (Q : Point), order • Q = 0 → Q ≠ 0 → ∀ start history,
    CoherentlyImplementsOn ((physical.program start).instantiate
      (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (update Q)) valid

def WindowValid (w : SignedWindow) (s : BasisState) : Prop :=
  BatchedWindowValid s ∧ (w.width = 15 → s 869 = false)

/-- The signed law names its ideal state map and fixes that map on every valid
point encoding. Its branch coefficients are uniform across input basis states. -/
structure SignedWindowLaw {n : Nat} (coeffs : Fin n → PointCoeff)
    (physical : SignedWindow → Window n) where
  update : Point → SignedWindow → BasisState → BasisState
  correct : ∀ Q w s, order • Q = 0 → Q ≠ 0 → WindowValid w s → ∀ P,
    pointStateCoordinates s = fig14PointEncoding P →
    update Q w s = pointWrite (P + increment Q w (digit w.width s)) s
  coherent : ∀ w, WindowLaw coeffs (physical w) (fun Q => update Q w) (WindowValid w)

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Coefficients ====

section
/-! Mixed-width public coefficients. The coefficient encoding and torsion
identities reuse the Apache-2.0 licensed Streaming construction. -/

namespace ShorECDLP.Entrant.Single

open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

/-- The first lookup directly loads the accumulator, including infinity. -/
@[irreducible] def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients (v * 2^247 + leftOffset) rightOffset

@[irreducible] def oddScalar (exponent address : Nat) : Nat :=
  (2 * address + 1) * 2^exponent * halfOrder

@[irreducible] def signedCoefficients (w : SignedWindow) (address : Nat) : PointCoeff :=
  match w with
  | .left16 _ | .left15 _ => coefficients (oddScalar w.exponent address) 0
  | .right16 _ | .right15 _ => coefficients 0 (oddScalar w.exponent address)

@[irreducible] def mixedCoefficientAt (i : Fin 851968) : PointCoeff :=
  if i.val < 65536 then initialCoefficients i.val
  else if i.val < 294912 then
    coefficients (oddScalar (231 - 16 * ((i.val - 65536) / 32768)) ((i.val - 65536) % 32768)) 0
  else if i.val < 442368 then
    coefficients (oddScalar (120 - 15 * ((i.val - 294912) / 16384)) ((i.val - 294912) % 16384)) 0
  else if i.val < 704512 then
    coefficients 0 (oddScalar (247 - 16 * ((i.val - 442368) / 32768)) ((i.val - 442368) % 32768))
  else coefficients 0 (oddScalar (120 - 15 * ((i.val - 704512) / 16384)) ((i.val - 704512) % 16384))

@[irreducible] def mixedCoefficientTable : List PointCoeff := List.ofFn mixedCoefficientAt

theorem mixedCoefficientTable_length : mixedCoefficientTable.length = 851968 := by
  unfold mixedCoefficientTable
  exact List.length_ofFn

theorem mixedCoefficientAt_first (a : Fin 65536) :
    mixedCoefficientAt (firstRow a) = initialCoefficients a.val := by
  simp [mixedCoefficientAt, firstRow, a.isLt]

theorem mixedCoefficientAt_signed (w : SignedWindow) (a : Fin 32768) :
    mixedCoefficientAt (signedRow w a) =
      signedCoefficients w (a.val % 2^(w.width-1)) := by
  cases w with
  | left16 j =>
    have h1 : ¬ (signedRow (.left16 j) a).val < 65536 := by simp [signedRow]; omega
    have h2 : (signedRow (.left16 j) a).val < 294912 := by simp [signedRow]; omega
    have hj : ((signedRow (.left16 j) a).val - 65536) / 32768 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.left16 j) a).val - 65536) % 32768 = a.val := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, hj, ha, signedCoefficients, SignedWindow.width,
      SignedWindow.exponent, Nat.mod_eq_of_lt a.isLt]
  | left15 j =>
    have hb : a.val % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have h1 : ¬ (signedRow (.left15 j) a).val < 65536 := by simp [signedRow]; omega
    have h2 : ¬ (signedRow (.left15 j) a).val < 294912 := by simp [signedRow]; omega
    have h3 : (signedRow (.left15 j) a).val < 442368 := by simp [signedRow]; omega
    have hj : ((signedRow (.left15 j) a).val - 294912) / 16384 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.left15 j) a).val - 294912) % 16384 = a.val % 16384 := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, h3, hj, ha, signedCoefficients,
      SignedWindow.width, SignedWindow.exponent]
  | right16 j =>
    have h1 : ¬ (signedRow (.right16 j) a).val < 65536 := by simp [signedRow]; omega
    have h2 : ¬ (signedRow (.right16 j) a).val < 294912 := by simp [signedRow]; omega
    have h3 : ¬ (signedRow (.right16 j) a).val < 442368 := by simp [signedRow]; omega
    have h4 : (signedRow (.right16 j) a).val < 704512 := by simp [signedRow]; omega
    have hj : ((signedRow (.right16 j) a).val - 442368) / 32768 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.right16 j) a).val - 442368) % 32768 = a.val := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, h3, h4, hj, ha, signedCoefficients,
      SignedWindow.width, SignedWindow.exponent, Nat.mod_eq_of_lt a.isLt]
  | right15 j =>
    have hb : a.val % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have h1 : ¬ (signedRow (.right15 j) a).val < 65536 := by simp [signedRow]; omega
    have h2 : ¬ (signedRow (.right15 j) a).val < 294912 := by simp [signedRow]; omega
    have h3 : ¬ (signedRow (.right15 j) a).val < 442368 := by simp [signedRow]; omega
    have h4 : ¬ (signedRow (.right15 j) a).val < 704512 := by simp [signedRow]; omega
    have hj : ((signedRow (.right15 j) a).val - 704512) / 16384 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.right15 j) a).val - 704512) % 16384 = a.val % 16384 := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, h3, h4, hj, ha, signedCoefficients,
      SignedWindow.width, SignedWindow.exponent]

theorem initialCoefficients_point (Q : Point) (hQ : order • Q = 0) (v : Nat) :
    constantPoint Q (initialCoefficients v) = initialPoint Q v :=
by
  unfold initialCoefficients initialPoint
  exact coefficients_point _ _ Q hQ

noncomputable def positivePoint (Q : Point) (w : SignedWindow) (address : Nat) : Point :=
  oddScalar w.exponent (address % 2^(w.width-1)) • w.base Q

theorem signedCoefficients_point (Q : Point) (hQ : order • Q = 0)
    (w : SignedWindow) (address : Nat) :
    constantPoint Q (signedCoefficients w (address % 2^(w.width-1))) =
      positivePoint Q w address := by
  cases w <;> simp [signedCoefficients, coefficients_point _ _ Q hQ,
    positivePoint, SignedWindow.base]

theorem positivePoint_ne_zero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (address : Nat) : positivePoint Q w address ≠ 0 := by
  let P := w.base Q
  have hp : P ≠ 0 := by
    cases w with
    | left16 _ | left15 _ => exact G_ne_zero
    | right16 _ | right15 _ => exact hn
  have hr : order • P = 0 := by
    cases w with
    | left16 _ | left15 _ => exact generator_nsmul_eq_zero
    | right16 _ | right15 _ => exact hQ
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf P = order := addOrderOf_eq_prime hr hp
  have hw : 2^(w.width-1) ≤ 32768 := by cases w <;> norm_num [SignedWindow.width]
  have hm : 0 < 2^(w.width-1) := pow_pos (by decide) _
  have hb := Nat.mod_lt address hm
  have hl : 65535 < order := by norm_num [order]
  have hs : 0 < 2*(address % 2^(w.width-1))+1 ∧
      2*(address % 2^(w.width-1))+1 < order := by omega
  have hh : 0 < halfOrder ∧ halfOrder < order := by dsimp [halfOrder]; omega
  have hodd : ¬ order ∣ 2*(address % 2^(w.width-1))+1 :=
    fun h => (Nat.le_of_dvd hs.1 h).not_gt hs.2
  have hhalf : ¬ order ∣ halfOrder := fun h => (Nat.le_of_dvd hh.1 h).not_gt hh.2
  have htwo : ¬ order ∣ 2 := fun h => (Nat.le_of_dvd (by decide : 0 < 2) h).not_gt (by omega)
  intro hz
  have he : ((2*(address % 2^(w.width-1))+1)*2^w.exponent*halfOrder) • P = 0 := by simpa only [positivePoint, oddScalar] using hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  rw [ho] at hd
  rcases order_prime.dvd_mul.mp hd with hd | hd
  · rcases order_prime.dvd_mul.mp hd with hd | hd
    · exact hodd hd
    · exact htwo (order_prime.dvd_of_dvd_pow hd)
  · exact hhalf hd

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Padding ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem address_append (xs ys : List Wire) (s : BasisState) :
    tableAddressValue (xs ++ ys) s =
      tableAddressValue xs s + 2^xs.length * tableAddressValue ys s := by
  induction xs with
  | nil => simp [tableAddressValue]
  | cons x xs ih =>
    simp only [List.cons_append, tableAddressValue, List.length_cons, ih, pow_succ]
    ring

theorem bank_length (width : Nat) (hw : width = 15 ∨ width = 16) :
    (bank width).length = width := by
  rcases hw with rfl | rfl <;> simp [bank]

theorem window_width (w : SignedWindow) : w.width = 15 ∨ w.width = 16 := by
  cases w <;> simp [SignedWindow.width]

theorem digit15_low (s : BasisState) :
    digit 15 s = logicalValue (tableAddressValue (List.range' 855 14) s) (s 870) := by
  simp [digit, bank, address_append, tableAddressValue, logicalValue]

theorem digit16_physical (s : BasisState) : digit 16 s = windowRawDigit 0 s := by
  simp [digit, bank, windowRawDigit, windowAddressBits, windowBankStart,
    tableAddressValue, List.range', wireValues, boolWordToNat]
  omega

theorem physical_padding (s : BasisState) (hs : s 869 = false) :
    windowRawDigit 0 s = paddedValue (tableAddressValue (List.range' 855 14) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat, hs]

theorem digit_bound (w : SignedWindow) (s : BasisState) : digit w.width s < 2^w.width := by
  have h := tableAddressValue_lt (bank w.width) s
  rw [bank_length _ (window_width w)] at h
  exact h

theorem digit_low_sign (w : SignedWindow) (s : BasisState) :
    digit w.width s < 2^(w.width-1) ↔ s 870 = false := by
  rcases window_width w with hw | hw
  · rw [hw, digit15_low]
    have hb := tableAddressValue_lt (List.range' 855 14) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue]
  · rw [hw, digit16_physical]
    exact reused_window_digit_low s

/-- Both physical address halves select the same logical signed row. -/
theorem selected_address_alias (w : SignedWindow) (s : BasisState)
    (hz : w.width = 15 → s 869 = false) :
    signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1) =
      signedTableAddress (2^(w.width-1)) (digit w.width s) := by
  rcases window_width w with hw | hw
  · rw [hw, physical_padding s (hz hw), digit15_low]
    exact padded_address _ _ (by simpa using tableAddressValue_lt (List.range' 855 14) s)
  · rw [hw, digit16_physical]
    exact Nat.mod_eq_of_lt (signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s))

/-- Table signs implement the intended centered odd logical digit. -/
theorem selected_increment (Q : Point) (w : SignedWindow) (s : BasisState)
    (hz : w.width = 15 → s 869 = false) :
    (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) =
      increment Q w (digit w.width s) := by
  have hpow : (2 : Int)^w.width = 2 * (2^(w.width-1) : Nat) := by
    rcases window_width w with hw | hw <;> rw [hw] <;> norm_num
  have hs : (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) =
      signedTableOdd (2^(w.width-1)) (digit w.width s) •
        ((halfOrder * 2^w.exponent) • w.base Q) := by
    simp only [positivePoint, selected_address_alias w s hz, oddScalar, mul_smul]
    rw [smul_comm halfOrder (2^w.exponent)]
    cases h : s 870
    · rw [if_neg (by decide), signedTableOdd, if_pos ((digit_low_sign w s).mpr h)]
      simp only [neg_zsmul, natCast_zsmul]
    · rw [if_pos rfl, signedTableOdd, if_neg (by
        intro hh
        have he := (digit_low_sign w s).mp hh
        simp [h] at he)]
      simp only [natCast_zsmul]
  rw [hs, signedTableOdd_value]
  unfold increment
  rw [hpow]

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/First ====

section
/-! Direct loading with the mixed-width offsets. Adapted from the Apache-2.0
licensed Streaming PointTable; the physical theorem permits infinity. -/

namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def firstWindow : Window 851968 :=
  ⟨(bank 16).reverse, 65535, fun start => reindexStraight firstRow (firstLookupProgram start)⟩

theorem initialLookup_circuit (Q : Point) (hQ : order • Q = 0) :
    lookupCircuit (readConstant (fun i : Fin 65536 => initialCoefficients i.val) Q) firstLookupOps =
      physicalPointLookup (initialPoint Q) := by
  rw [firstLookupOps, unaryLookupOps_circuit]
  unfold physicalPointLookup directPointLookup tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  obtain ⟨i, hi, he⟩ := tableAddressTree_label _ 0 1 l hl
  have hlt : l < 65536 := by simpa [he] using hi
  rw [pointLeaf_instantiate]
  simp only [Nat.mod_eq_of_lt hlt, initialCoefficients_point Q hQ, pointTableMask]

theorem firstWindow_run (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).run =
      (physicalPointLookup (initialPoint Q)).run := by
  unfold firstWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex firstRow _ _ Q mixedCoefficientAt_first]
  rw [firstLookupProgram, castFinish_instantiate, lookupProgram_run, initialLookup_circuit Q hQ]

theorem firstWindow_coherent (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    CoherentlyImplementsOn ((firstWindow.program start).instantiate
      (readConstant mixedCoefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (firstUpdate Q))
      (DirectPointLookupValid (List.range' 519 16) 836) := by
  unfold CoherentlyImplementsOn
  rw [firstWindow_run Q hQ start history]
  exact physicalPointLookup_coherent (initialPoint Q)

theorem firstWindow_t (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 458745 := by
  unfold firstWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex firstRow _ _ Q mixedCoefficientAt_first]
  rw [firstLookupProgram, castFinish_instantiate, lookupProgram_tCount, initialLookup_circuit Q hQ]
  exact (physicalPointLookup_resources _).1

theorem firstUpdate_valid (Q : Point) (s : BasisState) (hs : FirstWindowInput s) :
    BatchedWindowValid (firstUpdate Q s) := firstWindowInput_pointWrite s hs _

theorem firstUpdate_frame (Q : Point) (s : BasisState) (v : Wire)
    (hv : v ∉ pointLogicalWires) : firstUpdate Q s v = s v := pointWrite_frame _ _ v hv

/- The following uniform cost argument is adapted from the Apache-2.0
licensed Streaming UniformT module. -/
private theorem leaf_t_zero {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire))
    (read : ConstantBit n → Bool) :
    ShorECDLP.tCount ((lookupLeafGates q ports).flatMap (TemplateGate.instantiate read)) = 0 := by
  rw [lookupLeafGates_instantiate]
  induction ports.filter (fun p => read p.1) with
  | nil => rfl
  | cons p ps ih => simpa [ShorECDLP.tCount, tCost] using ih
private theorem unary_t_congr (tree : UnaryActionTree) (f g : Nat → Wire → Circuit)
    (h : ∀ l w, ShorECDLP.tCount (f l w) = ShorECDLP.tCount (g l w))
    (q : Wire) (anc : List Wire) :
    (unaryAction .inc f tree q anc).tCount = (unaryAction .inc g tree q anc).tCount := by
  induction tree generalizing q anc with
  | leaf l => simp [unaryAction,AdaptiveCircuit.tCount,h]
  | node b z o ihz iho => cases anc <;>
      simp only [unaryAction,AdaptiveCircuit.tCount,adaptive_tCount_seq,ihz,iho]
private theorem first_load_uniform (start : Nat)
    (read : ConstantBit 65536 → Bool) (history : Fin start → Bool) :
    ((firstLookupProgram start).instantiate read history).tCount = 458745 := by
  have he : ((firstLookupProgram start).instantiate read history).tCount =
      ((firstLookupProgram start).instantiate (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) 0) history).tCount := by
    simp only [firstLookupProgram,castFinish_instantiate,lookupProgram_tCount,firstLookupOps,unaryLookupOps_circuit]
    apply unary_t_congr
    intro l w
    simp only [pointLeaf,leaf_t_zero]
  exact he.trans (firstLookupProgram_tCount start 0 (by simp) history)
theorem firstWindow_t_uniform (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 458745 := by
  unfold firstWindow
  rw [reindexStraight_instantiate]
  exact first_load_uniform start _ history

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Windows ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def signedWindow (w : SignedWindow) : Window 851968 :=
  ⟨(bank w.width).reverse, Physical.actual.count,
    fun start => reindexStraight (signedRow w) (Physical.actual.program start)⟩

def windowCoefficients (w : SignedWindow) : Fin 32768 → PointCoeff :=
  fun a => mixedCoefficientAt (signedRow w a)

theorem window_table_point (Q : Point) (hQ : order • Q = 0) (w : SignedWindow) (a : Nat) :
    Physical.tablePoint (windowCoefficients w) Q a = positivePoint Q w a := by
  unfold Physical.tablePoint windowCoefficients
  rw [mixedCoefficientAt_signed, signedCoefficients_point Q hQ]
  have ha : a % 32768 % 2^(w.width-1) = a % 2^(w.width-1) := by
    cases w <;> norm_num [SignedWindow.width]
  simp only [positivePoint, ha]

noncomputable def windowUpdate (Q : Point) (w : SignedWindow) : BasisState → BasisState :=
  Physical.actualBatchedWindowState (windowCoefficients w) Q

theorem windowUpdate_correct (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    windowUpdate Q w s = pointWrite (P + increment Q w (digit w.width s)) s := by
  unfold windowUpdate
  rw [Physical.actualBatchedWindowState_selected _ Q hQ
    (fun a => (window_table_point Q hQ w a).symm ▸ positivePoint_ne_zero Q hQ hn w a)
    s hs.1.1 P hP, window_table_point Q hQ, selected_increment Q w s hs.2]

private theorem reindex_coherent {n m s e : Nat} (f : Fin n → Fin m)
    (p : Straight n s e) (read : ConstantBit m → Bool) (read' : ConstantBit n → Bool)
    (history : Fin s → Bool) (hread : read ∘ reindexBit f = read')
    (ideal : State →ₗ[ℂ] State) (valid : BasisState → Prop)
    (h : CoherentlyImplementsOn (p.instantiate read' history) ideal valid) :
    CoherentlyImplementsOn ((reindexStraight f p).instantiate read history) ideal valid := by
  rw [reindexStraight_instantiate, hread]
  exact h

private theorem restrict_coherent {a : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a ideal P)
    (hr : ∀ s, R s → P s) : CoherentlyImplementsOn a ideal R := by
  obtain ⟨cs, hc, hm⟩ := h
  exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (hr s hs)), hm⟩

theorem signedWindow_coherent (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((signedWindow w).program start |>.instantiate
      (readConstant mixedCoefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w) := by
  have h := Physical.actualBatchedWindow_coherent (windowCoefficients w) Q hQ
    (fun a => (window_table_point Q hQ w a).symm ▸ positivePoint_ne_zero Q hQ hn w a)
    start history
  have ht := reindex_coherent (signedRow w) (Physical.actual.program start)
    (readConstant mixedCoefficientAt Q) (readConstant (windowCoefficients w) Q) history
    (readConstant_reindex (signedRow w) (windowCoefficients w) mixedCoefficientAt Q (fun _ => rfl))
    _ _ h
  unfold signedWindow windowUpdate
  exact restrict_coherent ht (fun _ hs => hs.1)

noncomputable def concreteSignedWindowLaw : SignedWindowLaw mixedCoefficientAt signedWindow where
  update := windowUpdate
  correct := fun Q w s hQ hn hs P hP => windowUpdate_correct Q hQ hn w s hs P hP
  coherent := fun w Q hQ hn start history => signedWindow_coherent Q hQ hn w start history

theorem windowUpdate_frame (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) (v : Wire)
    (hv : v ∉ pointLogicalWires) : windowUpdate Q w s v = s v := by
  obtain ⟨P, hP⟩ := hs.1.2
  rw [windowUpdate_correct Q hQ hn w s hs P hP]
  exact pointWrite_frame _ _ v hv

/-- The unused magnitude wire is restored, for both signs and all transcripts
through the coherent implementation. -/
theorem windowUpdate_padding (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) :
    w.width = 15 → windowUpdate Q w s 869 = false := by
  intro hw
  rw [windowUpdate_frame Q hQ hn w s hs 869 (by decide +kernel)]
  exact hs.2 hw

theorem windowUpdate_valid (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) :
    WindowValid w (windowUpdate Q w s) := by
  obtain ⟨P, hP⟩ := hs.1.2
  rw [windowUpdate_correct Q hQ hn w s hs P hP]
  exact ⟨⟨pointWrite_batchedReady _ s hs.1.1, _, pointWrite_coordinates _ s⟩,
    fun hw => (pointWrite_frame _ s 869 (by decide +kernel)).trans (hs.2 hw)⟩

theorem signedWindow_wires (w : SignedWindow) : (signedWindow w).wires = (bank w.width).reverse := by
  unfold signedWindow
  rfl

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/BodyCounts ====

section
namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] batchWindowTree
attribute [local irreducible] adaptiveCoordinateProgram yNegateProgram
  ShorECDLP.Entrant.ZeroAdaptive.coordinateSource placedBatchSource windowYNegate ipxProgramOf
  sequenceProgram surroundCompiled relabelCompiled

theorem actual_count : actual.count = 30707853 := by
  unfold actual closedWindow
  rfl

theorem placed_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (placedProgram start) (readConstant coeffs Q) history =
      (placedBatchSource coeffs Q).tCount := by
  unfold placedProgram compiledTCount
  simp only [ipxProgramOf, lookupProgram_tCount, ipxOps_source, placedBatchSource]

theorem batch_t (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    (placedBatchSource coeffs Q).tCount = 3024805 := by
  rw [placedBatchSource, ipxSourceOps_tCount _ _ _ _ ipxTree_layout, ipxSchedule_cost, batchWindowTree_nodes]

theorem sources_t (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    (sequenceCircuit (sources coeffs Q)).tCount = 513264087 := by
  unfold sources
  rw [sequenceCircuit_four_tCount, (coordinate_numeric_counts _ _).1,
    windowYNegate_numeric_counts.1, batch_t]

theorem core_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (core start) (readConstant coeffs Q) history =
      (sequenceCircuit (sources coeffs Q)).tCount := by
  unfold core
  apply sequenceProgram_tCount
  unfold segments sources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact adaptiveCoordinateProgram_tCount coeffs cursor Q h
  · intro cursor h; unfold windowYNegate; exact yNegateProgram_tCount cursor _ h
  · intro cursor h; exact placed_t coeffs cursor Q h
  · intro cursor h; unfold windowYNegate; exact yNegateProgram_tCount cursor _ h

theorem actual_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actual.program start).instantiate (readConstant coeffs Q) history).tCount = 513264087 := by
  have h := surroundCompiled_tCount (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (core 0)
    (sequenceCircuit (sources coeffs Q)) (readConstant coeffs Q) Fin.elim0
    (core_t coeffs 0 Q Fin.elim0)
  simp only [AdaptiveCircuit.tCount, adaptive_tCount_seq, signedAddressCircuit_tCount,
    Nat.zero_add, Nat.add_zero, sources_t] at h
  unfold actual
  simp only [closedWindow_run, castFinish_instantiate, relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
  change compiledTCount (prepared 0) (readConstant coeffs Q) Fin.elim0 = _
  unfold prepared
  exact h

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/WindowCounts ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem signedWindow_count (w : SignedWindow) : (signedWindow w).count = 30707853 := by
  unfold signedWindow
  exact Physical.actual_count

theorem signedWindow_t (Q : Point) (w : SignedWindow) (start : Nat)
    (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 513264087 := by
  unfold signedWindow
  rw [reindexStraight_instantiate, readConstant_reindex (signedRow w)
    (windowCoefficients w) mixedCoefficientAt Q (fun _ => rfl)]
  exact Physical.actual_t (windowCoefficients w) start Q history

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Layout ====

section
namespace ShorECDLP.Entrant.Single

open ShorECDLP.Challenge

def params : DecoderParams := ⟨263, 263, by omega, by omega, by omega, by omega⟩

/-- The first right bank follows the complete left-axis transcript. -/
def trialPositions : TrialPositions params where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, params] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata 491391446).toArray, by
    simpa only [List.size_toArray, params] using right_positions_length 491391446⟩

def layout : DecodeLayout := ⟨.nearestPair, params, [trialPositions], by simp⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 491391446 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    491391446 ≤ i ∧ i < 1013425210 := by
  have h := positions_bounds rightMetadata 491391446 i
    (show i ∈ positions rightMetadata 491391446 from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/OuterProperties ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

def bodyT (count : Nat) : Nat := if count = 65535 then 458745 else 513264087

def metadataT : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (count, width) :: ws, prior =>
      bodyT count + fourierSlots width prior + metadataT ws (prior + width)

def metadataSlots (slots : Nat) : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (_, width) :: ws, prior =>
      slots + width + fourierSlots width prior + metadataSlots slots ws (prior + width)

theorem nextPrior_length {start : Nat} (count width : Nat) (prior : List (Fin start)) :
    (nextPrior count width prior).length = prior.length + width := by
  simp [nextPrior, Nat.add_comm]

theorem axis_wellFormed {n : Nat} (ws : List (Window n))
    (hw : ∀ w ∈ ws, ∀ start, (w.program start).WellFormed) (start : Nat)
    (prior : List (Fin start)) : (axis ws start prior).WellFormed := by
  induction ws generalizing start with
  | nil => trivial
  | cons w ws ih =>
    simp only [axis, castFinish_wellFormed]
    apply straight_append_wellFormed _ _ (prepareOuterBank_wellFormed _ _ (hw w (by simp) start))
    apply straight_append_wellFormed
    · simpa only [castFinish_wellFormed] using fourierProgram_wellFormed n .inverse w.wires _ _
    · exact ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _ _

theorem axis_slots {n : Nat} (ws : List (Window n)) (slots : Nat)
    (hw : ∀ w ∈ ws, ∀ start, (w.program start).gateSlots ≤ slots)
    (start : Nat) (prior : List (Fin start)) :
    (axis ws start prior).gateSlots ≤
      metadataSlots slots (ws.map (fun w => (w.count, w.wires.length))) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis, metadataSlots, Straight.gateSlots]
  | cons w ws ih =>
    simp only [axis, castFinish_gateSlots, Straight.gateSlots_append,
      prepareOuterBank_slots, List.length_reverse, fourierProgram_slots, bankPrior_length]
    have h := ih (fun v hv => hw v (List.mem_cons_of_mem w hv))
      (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior)
    have hg := hw w (by simp) start
    simp only [nextPrior_length] at h
    simp only [List.map_cons, metadataSlots]
    omega

theorem axis_t {n : Nat} (ws : List (Window n)) (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ ws, ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ bodyT w.count)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((axis ws start prior).instantiate read history).tCount ≤
      metadataT (ws.map (fun w => (w.count, w.wires.length))) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis, metadataT, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons w ws ih =>
    simp only [axis, castFinish_instantiate]
    apply (outer_append_t_le _ _ read history
      (fourierSlots w.wires.length prior.length +
        metadataT (ws.map (fun w => (w.count, w.wires.length))) (prior.length+w.wires.length)) ?_).trans
    · simp only [prepareOuterBank_t, List.map_cons, metadataT]
      have h := hw w (by simp) start history
      omega
    · intro h
      apply (outer_append_t_le _ _ read h
        (metadataT (ws.map (fun w => (w.count, w.wires.length))) (prior.length+w.wires.length)) ?_).trans
      · have hf := fourierProgram_t_le n .inverse w.wires (start+w.count)
          (bankPrior w.count prior) read h
        simp only [bankPrior_length] at hf
        simp only [castFinish_instantiate]
        omega
      · intro h₂
        simpa only [nextPrior_length] using
          ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _
            (nextPrior w.count w.wires.length prior) h₂

theorem axis_support {n : Nat} (ws : List (Window n)) (support : List Wire)
    (hb : ∀ w ∈ ws, w.wires ⊆ support)
    (hp : ∀ w ∈ ws, ∀ start read history,
      ((w.program start).instantiate read history).wires ⊆ support)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    ((axis ws start prior).instantiate read history).wires ⊆ support := by
  induction ws generalizing start with
  | nil => exact List.nil_subset _
  | cons w ws ih =>
    simp only [axis, castFinish_instantiate]
    apply outer_append_support
    · apply prepareOuterBank_support
      · intro v hv; exact hb w (by simp) (List.mem_reverse.mp hv)
      · exact hp w (by simp) start read history
    · intro h
      apply outer_append_support
      · simp only [castFinish_instantiate]
        exact fourierProgram_support n .inverse w.wires _ _ read h support (hb w (by simp))
      · intro h₂
        exact ih (fun v hv => hb v (List.mem_cons_of_mem w hv))
          (fun v hv => hp v (List.mem_cons_of_mem w hv)) _ _ h₂

/-- Newest-first feedback contains exactly the earlier selected axis outputs. -/
theorem nextPrior_values {start : Nat} (count width : Nat) (prior : List (Fin start)) :
    (nextPrior count width prior).map Fin.val =
      (List.range' (start + count) width).reverse ++ prior.map Fin.val := by
  simp only [nextPrior, List.map_append, List.map_reverse, List.map_ofFn, List.map_map,
    Function.comp_def]
  congr 1
  apply congrArg List.reverse
  apply List.ext_getElem
  · simp
  · intro i hi hj; simp

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Framing ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- A fixed query flag surrounds two axes and a reset. -/
@[irreducible] def framed {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) : Straight n s f :=
  .gate (.literal (.X 836)) (castFinish h (p.append (q.append (.gate (.literal (.X 836)) r))))

theorem framed_wellFormed {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (hp : p.WellFormed) (hq : q.WellFormed) (hr : r.WellFormed) :
    (framed p q r h).WellFormed := by
  unfold framed
  refine ⟨trivial, ?_⟩
  rw [castFinish_wellFormed]
  exact straight_append_wellFormed _ _ hp (straight_append_wellFormed _ _ hq ⟨trivial, hr⟩)

theorem framed_slots {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    (framed p q r h).gateSlots = p.gateSlots + q.gateSlots + r.gateSlots + 2 := by
  unfold framed
  simp only [Straight.gateSlots, castFinish_gateSlots, Straight.gateSlots_append]
  omega

theorem framed_t_le {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (a b : Nat) (hp : (p.instantiate read history).tCount ≤ a)
    (hq : ∀ history, (q.instantiate read history).tCount ≤ b)
    (hr : ∀ history, (r.instantiate read history).tCount = 0) :
    ((framed p q r h).instantiate read history).tCount ≤ a + b := by
  unfold framed
  simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
    ShorECDLP.tCount, tCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.zero_add, castFinish_instantiate]
  apply (outer_append_t_le _ _ read history b ?_).trans (Nat.add_le_add_right hp b)
  intro hq'
  apply (outer_append_t_le _ _ read hq' 0 ?_).trans
  · simpa only [Nat.add_zero] using hq hq'
  · intro hr'
    simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, tCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.zero_add, hr hr']
    exact Nat.le_refl 0

theorem framed_support {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (support : List Wire) (hx : (836 : Wire) ∈ support)
    (hp : (p.instantiate read history).wires ⊆ support)
    (hq : ∀ history, (q.instantiate read history).wires ⊆ support)
    (hr : ∀ history, (r.instantiate read history).wires ⊆ support) :
    ((framed p q r h).instantiate read history).wires ⊆ support := by
  have x_support {a b : Nat} (p : Straight n a b) (history : Fin a → Bool)
      (hp : (p.instantiate read history).wires ⊆ support) :
      ((Straight.gate (.literal (.X 836)) p).instantiate read history).wires ⊆ support := by
    intro v hv
    change v ∈ circuitWires [.X 836] ++ _ at hv
    rcases List.mem_append.mp hv with hv | hv
    · have he : v = 836 := by simpa [circuitWires, gateWires] using hv
      exact he ▸ hx
    · exact hp hv
  unfold framed
  apply x_support
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history support hp
  intro hq'
  exact outer_append_support _ _ read hq' support (hq hq') (fun hr' => x_support r hr' (hr hr'))

theorem framed_run {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((framed p q r h).instantiate read history).run =
      (AdaptiveCircuit.unitary [.X 836]
        ((p.append (q.append (.gate (.literal (.X 836)) r))).instantiate read history)).run := by
  unfold framed
  simp only [Straight.instantiate, TemplateGate.instantiate, castFinish_instantiate]

theorem framed_branch {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (b : InstrumentBranch) (hb : b ∈ ((framed p q r h).instantiate read history).run) :
    ∃ c ∈ ((p.append (q.append (.gate (.literal (.X 836)) r))).instantiate read history).run,
      b = ⟨c.history, c.kraus.comp (Quantum.run [.X 836])⟩ := by
  simp only [framed, castFinish_instantiate, Straight.instantiate, TemplateGate.instantiate,
    AdaptiveCircuit.run] at hb
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hb
  exact ⟨c, hc, he.symm⟩

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Program ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] resetProgram

@[irreducible] def leftWindows : List (Window 851968) :=
  firstWindow :: leftSigned.map signedWindow

@[irreducible] def rightWindows : List (Window 851968) := rightSigned.map signedWindow

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftSigned, signedWindow_count, signedWindow_wires,
    SignedWindow.width, bank, firstWindow, leftMetadata]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightSigned, signedWindow_count, signedWindow_wires,
    SignedWindow.width, bank, rightMetadata]

theorem left_count : axisCount leftWindows = 491391446 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 522033764 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

theorem left_positions (start : Nat) : axisPositions leftWindows start = positions leftMetadata start := by
  rw [axisPositions, left_metadata]

theorem right_positions (start : Nat) : axisPositions rightWindows start = positions rightMetadata start := by
  rw [axisPositions, right_metadata]

@[irreducible] def resetBody (start : Nat) : Straight 851968 start (start + 854) :=
  castFinish (by rw [resetWires_length]) (resetProgram 851968 start resetWires)

theorem resetBody_run (start : Nat) (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).run =
      (measureResetWithCorrection resetWires (fun _ => [])).run := by
  unfold resetBody
  rw [castFinish_instantiate, resetProgram_run]

theorem resetBody_t (start : Nat) (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).tCount = 0 := by
  unfold resetBody
  rw [castFinish_instantiate, resetProgram_t]

theorem resetBody_slots (start : Nat) : (resetBody start).gateSlots = 0 := by
  unfold resetBody
  rw [castFinish_gateSlots, resetProgram_gateSlots]

theorem resetBody_wellFormed (start : Nat) : (resetBody start).WellFormed := by
  unfold resetBody
  rw [castFinish_wellFormed]
  exact resetProgram_wellFormed _ _ _

theorem resetBody_support (start : Nat) (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).wires ⊆ 837 :: resetWires := by
  unfold resetBody
  rw [castFinish_instantiate]
  exact resetProgram_support _ _ _ _ read history (List.subset_cons_of_subset 837 (List.Subset.refl _))

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + 854

theorem trialCount_eq : trialCount = 1013426064 := by
  rw [trialCount, left_count, right_count]

/-- One trial, with independent same-axis feedback histories and a final reset. -/
@[irreducible] def trial (start : Nat) : Straight 851968 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

@[irreducible] def program : Straight 851968 0 1013426064 :=
  castFinish (by rw [trialCount_eq]) (trial 0)

theorem left_output_records (start : Nat) (prior : List (Fin start))
    (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((axis leftWindows start prior).instantiate read history).run) :
    ∀ i ∈ positions leftMetadata start, FourierRecord read (List.ofFn history ++ b.history) i := by
  rw [← left_positions]
  exact axis_records leftWindows start prior read history b hb

theorem right_output_records (start : Nat) (prior : List (Fin start))
    (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((axis rightWindows start prior).instantiate read history).run) :
    ∀ i ∈ positions rightMetadata start, FourierRecord read (List.ofFn history ++ b.history) i := by
  rw [← right_positions]
  exact axis_records rightWindows start prior read history b hb

theorem layout_left_positions : trialPositions.left.toList = axisPositions leftWindows 0 := by
  rw [left_positions]
  simp only [trialPositions, Vector.toList, List.toList_toArray]

theorem layout_right_positions : trialPositions.right.toList =
    axisPositions rightWindows (axisCount leftWindows) := by
  rw [right_positions, left_count]
  simp only [trialPositions, Vector.toList, List.toList_toArray]

/-- The protected decoder reads the actual Fourier position vectors in their
stored little-endian order. -/
theorem layout_read_left (history : List Bool) :
    readWord history trialPositions.left.toList = readWord history (axisPositions leftWindows 0) := by
  rw [layout_left_positions]

theorem layout_read_right (history : List Bool) :
    readWord history trialPositions.right.toList =
      readWord history (axisPositions rightWindows (axisCount leftWindows)) := by
  rw [layout_right_positions]

theorem program_history_length (read : ConstantBit 851968 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (program.instantiate read Fin.elim0).run) : b.history.length = 1013426064 := by
  exact straight_history_length program read Fin.elim0 b hb

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/BodyPhysical ====

section
namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] batchWindowTree
attribute [local irreducible] adaptiveCoordinateProgram yNegateProgram ipxProgramOf

private theorem old_in_complete : resetWires ⊆ completeBatchedSupport :=
  List.subset_cons_of_subset 837 (List.Subset.refl _)

theorem placed_wellFormed (start : Nat) : (placedProgram start).2.WellFormed := by
  unfold placedProgram
  exact ipxProgramOf_wellFormed _ _ _ ipxTree_layout ipxPaths_outside start

theorem core_wellFormed (start : Nat) : (core start).2.WellFormed := by
  unfold core
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [segments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact adaptiveCoordinateProgram_wellFormed cursor
  · exact yNegateProgram_wellFormed cursor
  · exact placed_wellFormed cursor
  · exact yNegateProgram_wellFormed cursor

theorem prepared_wellFormed (start : Nat) : (prepared start).2.WellFormed := by
  unfold prepared
  exact surroundCompiled_wellFormed _ _ _
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide)) (core_wellFormed start)

theorem actual_wellFormed (start : Nat) : (actual.program start).WellFormed := by
  unfold actual closedWindow
  apply shiftStraight_wellFormed
  rw [castFinish_wellFormed]
  exact (relabelStraight_wellFormed _ _).mpr (prepared_wellFormed 0)

private theorem closed_relabel_support {n e f : Nat} (h : e = f) (perm : Wire ≃ Wire)
    (p : Straight n 0 e) (start : Nat) :
    straightWires ((closedWindow (castFinish h (relabelStraight perm p))).program start) =
      (straightWires p).map perm := by
  simp only [closedWindow, straightWires_shift, straightWires_castFinish, straightWires_relabel]

theorem placed_slots (start : Nat) : (placedProgram start).2.gateSlots ≤ 1183842436 := by
  unfold placedProgram
  simp only [ipxProgramOf, lookupProgram_slots]
  have h := ipxOps_slots_le tableRows batchWindowTree pointLookupPath ipxSchedule
  rw [ipxSlotBound_schedule, batchWindowTree_nodes] at h
  omega

theorem core_slots (start : Nat) : (core start).2.gateSlots ≤ 2683895180 := by
  have h := sequenceProgram_slots_le 32768 segments
    ([1500000000, 26372, 1183842436, 26372] : List Nat) (by
      unfold segments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
      · intro s; exact adaptiveCoordinateProgram_slots s
      · intro s; exact yNegateProgram_slots_le s
      · intro s; exact placed_slots s
      · intro s; exact yNegateProgram_slots_le s) start
  unfold core
  simpa only [List.sum_cons, List.sum_nil] using h

theorem prepared_slots (start : Nat) : (prepared start).2.gateSlots ≤ 3000000000 := by
  have h := core_slots start
  unfold prepared
  simp only [surroundCompiled_slots, signedAddressCircuit_length,
    pointLookupAddress, List.length_range']
  omega

theorem actual_slots (start : Nat) : (actual.program start).gateSlots ≤ 3000000000 := by
  unfold actual closedWindow
  simp only [shiftStraight_gateSlots, castFinish_gateSlots, relabelStraight_slots]
  exact prepared_slots 0

theorem coordinate_support (start : Nat) :
    (straightWires (adaptiveCoordinateProgram start).2).map (windowAddressPerm 855 (by decide)) ⊆
      completeBatchedSupport := by
  have h := sharedAdaptiveCoordinateProgram_support_static (.right ⟨0, by decide⟩) start
  simpa only [sharedAdaptiveCoordinateProgram, reindexCompiled_support] using h

theorem negate_support (start : Nat) :
    (straightWires (yNegateProgram start).2).map (windowAddressPerm 855 (by decide)) ⊆
      completeBatchedSupport := by
  have h := (sharedYNegateProgram_support_static (.right ⟨0, by decide⟩) start).trans old_in_complete
  simpa only [sharedYNegateProgram, reindexCompiled_support] using h

theorem placed_support (start : Nat) :
    (straightWires (placedProgram start).2).map (windowAddressPerm 855 (by decide)) ⊆
      completeBatchedSupport := by
  have hraw : straightWires (ipxProgramOf tableRows batchWindowTree pointLookupPath start).2 ⊆ ipxRawSupport := by
    apply ipxProgramOf_support
    · intro c
      have hc := ipxControl_lt c
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
    · intro z hz
      simp only [pointLookupPath,List.mem_range'_1] at hz
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
    · intro z hz
      unfold batchWindowTree at hz
      have h := (tableAddressTree_mem_index pointLookupAddress 0 1 z).mp hz
      simp only [pointLookupAddress,List.mem_range'_1] at h
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
  unfold placedProgram
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact old_in_complete (ipxRawSupport_placed v (hraw hv))

theorem core_support (cursor : Nat) : (straightWires (core cursor).2).map
    (windowAddressPerm 855 (by decide)) ⊆ completeBatchedSupport := by
  unfold core
  apply sequenceProgram_mapped_support
  simp only [segments, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
  exact ⟨coordinate_support, negate_support, placed_support, negate_support⟩

theorem prepared_support (start : Nat) : (straightWires (prepared start).2).map
    (windowAddressPerm 855 (by decide)) ⊆ completeBatchedSupport := by
  unfold prepared
  simp only [surroundCompiled_support, List.map_append, List.append_subset]
  exact ⟨⟨signedAddressCircuit_support_static.trans old_in_complete, core_support start⟩,
    signedAddressCircuit_support_static.trans old_in_complete⟩

theorem actual_support (start : Nat) :
    straightWires (actual.program start) ⊆ completeBatchedSupport := by
  unfold actual
  rw [closed_relabel_support]
  exact prepared_support 0

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/WindowProperties ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] firstLookupProgram

private theorem reset_in_complete : resetWires ⊆ completeBatchedSupport := by
  intro w hw
  exact List.mem_cons_of_mem 837 hw

theorem firstWindow_wellFormed (start : Nat) : (firstWindow.program start).WellFormed := by
  unfold firstWindow
  exact (reindexStraight_wellFormed firstRow (firstLookupProgram start)).mpr (firstLookupProgram_wellFormed start)

theorem firstWindow_slots (start : Nat) : (firstWindow.program start).gateSlots ≤ 3000000000 := by
  have h := actualFirstWindow_slots start
  simp only [actualFirstWindow, reindexStraight_gateSlots] at h
  unfold firstWindow
  rw [reindexStraight_gateSlots]
  exact h.trans (by norm_num)

theorem firstWindow_support (start : Nat) :
    straightWires (firstWindow.program start) ⊆ completeBatchedSupport := by
  have h := (actualFirstWindow_support_static start).trans reset_in_complete
  simp only [actualFirstWindow, straightWires_reindex] at h
  unfold firstWindow
  rw [straightWires_reindex]
  exact h

theorem signedWindow_wellFormed (w : SignedWindow) (start : Nat) :
    ((signedWindow w).program start).WellFormed := by
  unfold signedWindow
  exact (reindexStraight_wellFormed (signedRow w) (Physical.actual.program start)).mpr (Physical.actual_wellFormed start)

theorem signedWindow_slots (w : SignedWindow) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ 3000000000 := by
  unfold signedWindow
  rw [reindexStraight_gateSlots]
  exact Physical.actual_slots start

theorem signedWindow_support (w : SignedWindow) (start : Nat) :
    straightWires ((signedWindow w).program start) ⊆ completeBatchedSupport := by
  unfold signedWindow
  rw [straightWires_reindex]
  exact Physical.actual_support start

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Validity ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem windowBank_subset (w : SignedWindow) : bank w.width ⊆ streamAddress := by
  intro v hv
  rcases window_width w with hw | hw
  · rw [hw] at hv
    simp only [bank, if_true, List.mem_append, List.mem_range'_1, List.mem_singleton] at hv
    simp only [streamAddress, List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · rw [hw] at hv
    simpa only [bank, show (16 : Nat) ≠ 15 by decide, if_false, streamAddress] using hv

theorem bank_padding_excluded (w : SignedWindow) (hw : w.width = 15) : 869 ∉ bank w.width := by
  rw [hw]
  simp [bank, List.mem_range'_1]

theorem bank_outside_point (w : SignedWindow) (v : Wire) (hv : v ∈ bank w.width) :
    v ∉ pointLogicalWires := by
  have hb := windowBank_subset w hv
  simp only [streamAddress, List.mem_range'_1] at hb
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem windowValid_update (w : SignedWindow) (s : BasisState) (hs : WindowValid w s)
    (v : Wire) (hv : v ∈ bank w.width) (b : Bool) : WindowValid w (s[v ↦ b]) := by
  refine ⟨batchedWindowValid_address_update s hs.1 v (windowBank_subset w hv) b, ?_⟩
  intro hw
  have hne : (869 : Wire) ≠ v := by intro he; subst v; exact bank_padding_excluded w hw hv
  simpa only [upd, if_neg hne] using hs.2 hw

private theorem supported_smul {V : BasisState → Prop} {ψ : State} (c : ℂ)
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])

private theorem supported_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ + φ) := by
  intro s hs
  by_cases h : ψ s = 0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h

theorem supported_transform (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn W (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn W (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s = 0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz, hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u = s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [map_add, he, map_smul]
    exact supported_add (supported_smul c (hL s hvs)) (ih hvψ)

theorem supported_linear (V : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn V (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn V (L ψ) :=
  supported_transform V V L hL ψ hψ

theorem windowValid_prepare (w : SignedWindow) (ws : List Wire)
    (hws : ws ⊆ bank w.width) (ψ : State) (hψ : SupportedOn (WindowValid w) ψ) :
    SupportedOn (WindowValid w) (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons v vs ih =>
    apply ih (fun z hz => hws (List.mem_cons_of_mem v hz))
    apply supported_linear (WindowValid w) (applyGate (.H v)) ?_ ψ hψ
    intro s hs
    rw [applyGate_ket]
    exact supported_add
      (supported_smul _ (supportedOn_ket _ _ (windowValid_update w s hs v (hws (by simp)) false)))
      (supported_smul _ (supportedOn_ket _ _ (windowValid_update w s hs v (hws (by simp)) true)))

theorem windowValid_clear (w : SignedWindow) (ws : List Wire)
    (hws : ws ⊆ bank w.width) (s : BasisState) (hs : WindowValid w s) :
    WindowValid w (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => exact hs
  | cons v vs ih =>
    exact ih (fun z hz => hws (List.mem_cons_of_mem v hz)) _
      (windowValid_update w s hs v (hws (by simp)) false)

theorem windowValid_fourier (w : SignedWindow) (dir : PhaseDir) (ws : List Wire)
    (hws : ws ⊆ bank w.width) (prior bs : List Bool) (ψ : State)
    (hψ : SupportedOn (WindowValid w) ψ) :
    SupportedOn (WindowValid w) (fourierBranch dir ws prior bs ψ) := by
  apply supported_linear _ _ ?_ ψ hψ
  intro s hs
  rw [fourierBranch_ket]
  exact supported_smul _ (supportedOn_ket _ _ (windowValid_clear w ws hws s hs))

/-- Clearing the Fourier bank commutes with writing the point accumulator. -/
theorem clear_pointWrite (w : SignedWindow) (P : Point) (s : BasisState) :
    fourierClear (bank w.width) (pointWrite P s) =
      pointWrite P (fourierClear (bank w.width) s) := by
  funext v
  rw [fourierClear_apply]
  by_cases hv : v ∈ bank w.width
  · simp only [hv, if_true, pointWrite_frame P _ v (bank_outside_point w v hv), fourierClear_apply]
  · rw [if_neg hv]
    unfold pointWrite
    split_ifs <;> simp [fourierClear_apply, hv]

theorem windowUpdate_cleared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    fourierClear (bank w.width) (windowUpdate Q w s) =
      pointWrite (P + increment Q w (digit w.width s)) (fourierClear (bank w.width) s) := by
  rw [windowUpdate_correct Q hQ hn w s hs P hP, clear_pointWrite]

def TrialReady (s : BasisState) : Prop := BatchedWindowValid s ∧ Clean streamAddress s

def Prepared (w : SignedWindow) (s : BasisState) : Prop :=
  BatchedWindowValid s ∧ ∀ v ∈ streamAddress, v ∉ bank w.width → s v = false

theorem prepared_valid (w : SignedWindow) (s : BasisState) (hs : Prepared w s) : WindowValid w s := by
  refine ⟨hs.1, ?_⟩
  intro hw
  exact hs.2 869 (by simp [streamAddress]) (bank_padding_excluded w hw)

theorem ready_prepared (w : SignedWindow) (s : BasisState) (hs : TrialReady s) : Prepared w s :=
  ⟨hs.1, fun v hv _ => hs.2 v hv⟩

theorem prepared_update (w : SignedWindow) (s : BasisState) (hs : Prepared w s)
    (v : Wire) (hv : v ∈ bank w.width) (b : Bool) : Prepared w (s[v ↦ b]) := by
  refine ⟨batchedWindowValid_address_update s hs.1 v (windowBank_subset w hv) b, ?_⟩
  intro z hz hn
  have hne : z ≠ v := by intro h; subst z; exact hn hv
  simpa only [upd, if_neg hne] using hs.2 z hz hn

theorem prepared_prepare (w : SignedWindow) (ws : List Wire) (hws : ws ⊆ bank w.width)
    (ψ : State) (hψ : SupportedOn (Prepared w) ψ) :
    SupportedOn (Prepared w) (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons v vs ih =>
    apply ih (fun z hz => hws (List.mem_cons_of_mem v hz))
    apply supported_linear (Prepared w) (applyGate (.H v)) ?_ ψ hψ
    intro s hs
    rw [applyGate_ket]
    exact supported_add
      (supported_smul _ (supportedOn_ket _ _ (prepared_update w s hs v (hws (by simp)) false)))
      (supported_smul _ (supportedOn_ket _ _ (prepared_update w s hs v (hws (by simp)) true)))

theorem stream_outside_point (v : Wire) (hv : v ∈ streamAddress) : v ∉ pointLogicalWires := by
  simp only [streamAddress, List.mem_range'_1] at hv
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem prepared_windowUpdate (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : Prepared w s) : Prepared w (windowUpdate Q w s) := by
  refine ⟨(windowUpdate_valid Q hQ hn w s (prepared_valid w s hs)).1, ?_⟩
  intro v hv ha
  rw [windowUpdate_frame Q hQ hn w s (prepared_valid w s hs) v (stream_outside_point v hv)]
  exact hs.2 v hv ha

theorem prepared_clear_ready (w : SignedWindow) (s : BasisState) (hs : Prepared w s) :
    TrialReady (fourierClear (bank w.width).reverse s) := by
  refine ⟨batchedWindowValid_fourierClear _ (fun _ h => windowBank_subset w (List.mem_reverse.mp h)) s hs.1, ?_⟩
  intro v hv
  rw [fourierClear_apply]
  split_ifs with h
  · rfl
  · exact hs.2 v hv (fun hmem => h (List.mem_reverse.mpr hmem))

theorem ready_prepare (w : SignedWindow) (ψ : State) (hψ : SupportedOn TrialReady ψ) :
    SupportedOn (Prepared w) (Quantum.run ((bank w.width).map Gate.H) ψ) :=
  prepared_prepare w _ (List.Subset.refl _) ψ (fun s hs => ready_prepared w s (hψ s hs))

theorem signed_branch_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ (((signedWindow w).program start).instantiate (readConstant mixedCoefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn (Prepared w) ψ) : SupportedOn (Prepared w) (b.kraus ψ) := by
  obtain ⟨c, hc⟩ := (signedWindow_coherent Q hQ hn w start history).branch_coefficient b hb
  rw [hc.on_supported (fun s hs => prepared_valid w s (hψ s hs))]
  apply supported_smul
  apply supported_linear (Prepared w) _ ?_ ψ hψ
  intro s hs
  simpa only [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using
    supportedOn_ket (Prepared w) _ (prepared_windowUpdate Q hQ hn w s hs)

theorem prepared_fourier_ready (w : SignedWindow) (prior bs : List Bool)
    (ψ : State) (hψ : SupportedOn (Prepared w) ψ) :
    SupportedOn TrialReady (fourierBranch .inverse (bank w.width).reverse prior bs ψ) := by
  apply supported_transform (Prepared w) TrialReady _ ?_ ψ hψ
  intro s hs
  rw [fourierBranch_ket]
  exact supported_smul _ (supportedOn_ket _ _ (prepared_clear_ready w s hs))

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/ResourceArithmetic ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem windows_cases (w : Window 851968) (hw : w ∈ leftWindows ++ rightWindows) :
    w = firstWindow ∨ ∃ s, w = signedWindow s := by
  simp only [leftWindows, rightWindows, List.mem_append, List.mem_cons, List.mem_map] at hw
  rcases hw with (h | ⟨s, _, h⟩) | ⟨s, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h.symm⟩
  · exact Or.inr ⟨s, h.symm⟩

theorem windows_wellFormed (w : Window 851968) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).WellFormed := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_wellFormed start
  · exact signedWindow_wellFormed s start

theorem windows_slots (w : Window 851968) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).gateSlots ≤ 3000000000 := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_slots start
  · exact signedWindow_slots s start

theorem windows_t (Q : Point) (w : Window 851968)
    (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) (history : Fin start → Bool) :
    ((w.program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ bodyT w.count := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · rw [firstWindow_t_uniform Q start history]
    simp [firstWindow, bodyT]
  · rw [signedWindow_t Q s start history, signedWindow_count]
    simp [bodyT]

theorem left_t_budget : metadataT leftMetadata 0 = 8212718590 := by
  norm_num [leftMetadata, metadataT, bodyT, List.replicate, fourierSlots]

theorem right_t_budget : metadataT rightMetadata 0 = 8725523932 := by
  norm_num [rightMetadata, metadataT, bodyT, List.replicate, fourierSlots]

theorem slots_budget : metadataSlots 3000000000 leftMetadata 0 +
    metadataSlots 3000000000 rightMetadata 0 + 2 = 102000069434 := by
  norm_num [leftMetadata, rightMetadata, metadataSlots, List.replicate, fourierSlots]

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/TrialValidity ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem trial_wellFormed (start : Nat) : (trial start).WellFormed := by
  unfold trial
  apply framed_wellFormed
  · exact axis_wellFormed leftWindows (fun w hw => windows_wellFormed w (List.mem_append_left _ hw)) _ _
  · exact axis_wellFormed rightWindows (fun w hw => windows_wellFormed w (List.mem_append_right _ hw)) _ _
  · exact resetBody_wellFormed _

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/ProgramShape ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem trial_slots (start : Nat) : (trial start).gateSlots ≤ 102000069434 := by
  have hl := axis_slots leftWindows 3000000000
    (fun w hw => windows_slots w (List.mem_append_left _ hw)) start List.nil
  have hr := axis_slots rightWindows 3000000000
    (fun w hw => windows_slots w (List.mem_append_right _ hw)) (start + axisCount leftWindows) List.nil
  rw [left_metadata] at hl
  rw [right_metadata] at hr
  simp only [List.length_nil] at hl hr
  unfold trial
  rw [framed_slots, resetBody_slots]
  have h := slots_budget
  omega

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Resources ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem left_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 8212718590 := by
  have h := axis_t leftWindows (readConstant mixedCoefficientAt Q)
    (fun w hw => windows_t Q w (List.mem_append_left _ hw)) start List.nil history
  rwa [left_metadata, List.length_nil, left_t_budget] at h

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 8725523932 := by
  have h := axis_t rightWindows (readConstant mixedCoefficientAt Q)
    (fun w hw => windows_t Q w (List.mem_append_right _ hw)) start List.nil history
  rwa [right_metadata, List.length_nil, right_t_budget] at h

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 16938242522 := by
  unfold trial
  exact framed_t_le _ _ _ _ _ history 8212718590 8725523932
    (left_axis_t Q start history) (fun h => right_axis_t Q _ h) (fun h => resetBody_t _ _ h)

theorem program_wellFormed : program.WellFormed := by
  unfold program
  rw [castFinish_wellFormed]
  exact trial_wellFormed 0

theorem program_slots : program.gateSlots ≤ 102000069434 := by
  unfold program
  rw [castFinish_gateSlots]
  exact trial_slots 0

theorem program_t (Q : Point) :
    (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).tCount ≤ 16938242522 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0

theorem program_measurements (read : ConstantBit 851968 → Bool) :
    (program.instantiate read Fin.elim0).measurementCount = 1013426064 := by
  exact program.measurementCount read Fin.elim0

theorem stream_support : streamAddress ⊆ completeBatchedSupport := by
  intro v hv
  exact List.mem_cons_of_mem 837 (List.mem_append_right _ hv)

theorem windows_bank_support (w : Window 851968) (hw : w ∈ leftWindows ++ rightWindows) :
    w.wires ⊆ completeBatchedSupport := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · unfold firstWindow
    intro v hv
    apply stream_support
    simpa only [List.mem_reverse, bank, show (16 : Nat) ≠ 15 by decide, if_false, streamAddress] using hv
  · rw [signedWindow_wires]
    intro v hv
    exact stream_support (windowBank_subset s (List.mem_reverse.mp hv))

theorem windows_support (w : Window 851968) (hw : w ∈ leftWindows ++ rightWindows)
    (start : Nat) (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ completeBatchedSupport := by
  apply (straight_instantiate_support _ read history).trans
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_support start
  · exact signedWindow_support s start

private theorem flag_support : (836 : Wire) ∈ completeBatchedSupport := by
  simp [completeBatchedSupport, resetWires]

theorem left_axis_support (start : Nat) (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate read history).wires ⊆ completeBatchedSupport :=
  axis_support leftWindows completeBatchedSupport
    (fun w hw => windows_bank_support w (List.mem_append_left _ hw))
    (fun w hw => windows_support w (List.mem_append_left _ hw)) start List.nil read history

theorem right_axis_support (start : Nat) (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate read history).wires ⊆ completeBatchedSupport :=
  axis_support rightWindows completeBatchedSupport
    (fun w hw => windows_bank_support w (List.mem_append_right _ hw))
    (fun w hw => windows_support w (List.mem_append_right _ hw)) start List.nil read history

theorem trial_support (start : Nat) (read : ConstantBit 851968 → Bool) (history : Fin start → Bool) :
    ((trial start).instantiate read history).wires ⊆ completeBatchedSupport := by
  unfold trial
  exact framed_support _ _ _ _ read history completeBatchedSupport flag_support
    (left_axis_support start read history) (fun h => right_axis_support _ read h)
    (fun h => resetBody_support _ read h)

theorem program_support (read : ConstantBit 851968 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ completeBatchedSupport := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_support 0 read Fin.elim0

theorem program_qubits (read : ConstantBit 851968 → Bool) :
    (program.instantiate read Fin.elim0).qubitCount ≤ 855 := by
  have hs : (program.instantiate read Fin.elim0).wires.dedup.toFinset ⊆
      completeBatchedSupport.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (program_support read (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount, completeBatchedSupport_length] using hc

theorem program_resource_facts (Q : Point) :
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).qubits ≤ 855 ∧
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).tModel ≤ 16938242522 ∧
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).measurements = 1013426064 :=
  ⟨program_qubits _, program_t Q, program_measurements _⟩

theorem table_rows_limit : mixedCoefficientTable.length ≤ 983040 := by
  rw [mixedCoefficientTable_length]
  norm_num

theorem one_candidate_check : layout.trials.length * decoderCandidateLimit layout.kind layout.params = 1 := by
  simp [layout, decoderCandidateLimit]

theorem resource_product : 855 * 16938242522 = 14482197356310 := by norm_num

end ShorECDLP.Entrant.Single

end
