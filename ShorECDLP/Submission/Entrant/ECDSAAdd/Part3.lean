-- Vendored from ECDSAAdd (ecdsa.fail Lean challenge), Apache-2.0, Copyright 2026 Runzhou Tao, Anirudh and ECDSAAdd contributors; 156 source modules at c3f340a (listed in MODULES.txt), concatenated. Changes: module paths, expanded notation, private-name renames; declarations unreachable from the ShorECDLP judge roots (no kernel or elaborator reference) removed in the 2026-11-11 dead-code compaction, `-- source:` markers kept.
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part1
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part2
import Mathlib.Tactic

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedResult.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedSquareProof.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measured_input_out_disjoint (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    (L.core.y++[L.core.sumCarry]).Disjoint L.core.out := by
  apply List.disjoint_left.mpr
  intro q hi ho
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hi
  have b := List.count_pos_iff.mpr ho
  simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h a
  omega

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroGateSupport.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Framework/UnitaryControl.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Framework/ExactControl.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/ControlledNormalizedMod.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroCnotResources.lean
noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledNormalizedResources.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareB.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCFull.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareOpaque.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedA.lean
noncomputable section

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedBPrefix.lean
noncomputable section

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedFirst.lean
noncomputable section

set_option maxRecDepth 20000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

attribute [local irreducible] addRotateProductValue

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedBSuffix.lean
noncomputable section

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedC.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedSecond.lean
noncomputable section

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareFull.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

attribute [local irreducible] addRotateProductValue
  subTimesProductValue branchCMiddleValue

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareSpec.lean
noncomputable section

set_option maxRecDepth 5000000
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareSupport.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def Certified (L : CuccaroStreamedSquareWideLayout) (p : Program) : Prop :=
  ProperProgram p ∧ ECDSAAdd.wires p⊆L.wires.toFinset

theorem Certified.reverse {L : CuccaroStreamedSquareWideLayout} {a : Program}
    (ha : L.Certified a) : L.Certified a.reverse := by
  exact ⟨properProgram_reverse a ha.1,by simpa only [wires_reverse] using ha.2⟩

theorem sum_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    L.Certified L.core.prepareSum ∧ L.Certified L.core.clearSum := by
  have bitMem : L.core.pad.getD 0 0∈L.core.pad := by
    have h : 0<L.core.pad.length := by rw [hw.core.pad]; omega
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  have hiEq : L.core.high=L.core.y.drop 128 := by
    simp [CuccaroStreamedSquareLayout.high,hw.core.y]
  have bounds (q : Wire) :
      (L.core.cin::(L.core.low++[L.core.pad.getD 0 0])++L.core.sum).count q≤
        L.wires.count q := by
    have sp := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
    have pb := (List.singleton_sublist.mpr bitMem).count_le q
    simp only [List.count_append] at sp
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.low,CuccaroStreamedSquareLayout.sum,hiEq,
      List.count_append,List.count_cons,List.count_nil] at pb ⊢
    omega
  have nd : (L.core.cin::(L.core.low++[L.core.pad.getD 0 0])++L.core.sum).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    exact (bounds q).trans (List.nodup_iff_count.mp hn q)
  have producer : L.Certified L.core.prepareSum := by
    refine ⟨cuccaroAdd_proper _ _ _ nd,?_⟩
    intro q hq
    have mem := List.mem_toFinset.mp (cuccaroAdd_wires_subset
      (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin hq)
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp
      (lt_of_lt_of_le (List.count_pos_iff.mpr mem) (bounds q)))
  exact ⟨producer,producer.reverse⟩

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareControlled.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c scratch : Wire) (hc : c∉L.wires) (ht : scratch∉L.wires) (hct : c≠scratch)
include hw hn hc ht hct

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedControlledResources.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c scratch : Wire)
include hw

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/PointStreamedSquare.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem ControlledPointLayout.streamedSquare_wires_eq (L : ControlledPointLayout)
    (hw : L.Widths) :
    L.dialogStreamedSquareWide.wires=L.point.y++L.point.x++L.dialogPool.take 775 := by
  calc
    L.dialogStreamedSquareWide.wires =
      L.dialogStreamedSquareWide.core.y++L.dialogStreamedSquareWide.core.out++
        (L.dialogStreamedSquareWide.core.product++L.dialogStreamedSquareWide.core.pad++
         L.dialogStreamedSquareWide.core.work++
         [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
          L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
          L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
          L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad) := by
            simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
              List.append_assoc]
    _ = _ := by
      rw [L.dialogStreamedSquareWide_pool hw]
      rfl

theorem ControlledPointLayout.streamedSquare_control_nodup
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.core.generic::L.core.poolWire 775::L.dialogStreamedSquareWide.wires).Nodup := by
  rw [L.streamedSquare_wires_eq hw]
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 776 L.dialogPool).count_le q
  have he := congrArg (List.count q) (L.dialogBit_prefix hw 775 (by omega))
  norm_num only at he
  simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.count_cons,
    List.count_append,List.count_nil] at h he ⊢
  omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedSupport.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

private def Contains (S : Finset Wire) (xs : List Wire) : Prop := ∀q∈xs,q∈S
private theorem Contains.take {S : Finset Wire} {xs : List Wire} (h : Contains S xs) (n : Nat) :
    Contains S (xs.take n) := fun q hq => h q (List.mem_of_mem_take hq)
private theorem Contains.drop {S : Finset Wire} {xs : List Wire} (h : Contains S xs) (n : Nat) :
    Contains S (xs.drop n) := fun q hq => h q (List.mem_of_mem_drop hq)
private theorem Contains.append {S : Finset Wire} {xs ys : List Wire}
    (hx : Contains S xs) (hy : Contains S ys) : Contains S (xs++ys) := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact hx q h
  · exact hy q h

private theorem contains_finset {S : Finset Wire} {xs : List Wire} (h : Contains S xs) :
    xs.toFinset⊆S := fun q hq => h q (List.mem_toFinset.mp hq)

private def Ambient (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Finset Wire :=
  (control::L.wires).toFinset

private theorem measured_banks_contained (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    Contains (L.Ambient control) L.inputBank ∧
    Contains (L.Ambient control) L.leafCarry ∧
    Contains (L.Ambient control) L.leafPad ∧
    Contains (L.Ambient control) L.foldCarry ∧
    Contains (L.Ambient control) L.shortCarry := by
  have work : Contains (L.Ambient control) L.core.work := by
    intro q hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,hq]
  have pad : Contains (L.Ambient control) L.foldPad := by
    intro q hq
    simp only [foldPad,List.mem_append] at hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires]
    tauto
  have carries : Contains (L.Ambient control) L.foldCarry := by
    intro q hq
    simp only [foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact pad q hq
    all_goals simp [Ambient,wires,CuccaroStreamedSquareLayout.wires]
  exact ⟨work.take 129,(work.drop 129).append ((pad.drop 1).take 130),
    pad.take 1,carries,carries.take 255⟩

theorem measured_small_support (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    ECDSAAdd.wires L.normalizeSource⊆L.Ambient control ∧
    ECDSAAdd.wires L.restoreSource⊆L.Ambient control ∧
    ECDSAAdd.wires L.reflectOutput⊆L.Ambient control ∧
    ECDSAAdd.wires (L.measuredCore.program SquareReduction.c SquareReduction.p)⊆L.Ambient control := by
  have banks := L.measured_banks_contained control
  have w : Contains (L.Ambient control) L.core.work := by
    intro q hq; simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,hq]
  have o : Contains (L.Ambient control) L.core.out := by
    intro q hq; simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,hq]
  have bits : Contains (L.Ambient control)
      [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag] := by
    intro q hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires] at hq ⊢
    tauto
  have embedWork : (L.core.work++L.shortCarry++[L.core.cin,L.core.normFlag]).toFinset⊆L.Ambient control := by
    apply contains_finset
    exact (w.append banks.2.2.2.2).append (by
      intro q hq; apply bits q; simp at hq ⊢; tauto)
  have ge := (compareConstantGe_wires_subset L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p).trans embedWork
  have addEmbed : ((some L.core.normFlag).toList++L.core.work++L.shortCarry++[L.core.cin]).toFinset⊆L.Ambient control := by
    intro q hq
    apply embedWork
    simp at hq ⊢
    tauto
  have add := (mappedConstAdd_wires_subset (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.c).trans addEmbed
  have undo := (mappedConstAdd_wires_subset (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.p).trans addEmbed
  have reflected := mappedConstAdd_wires_subset none L.core.out L.shortCarry L.core.cin SquareReduction.p
  have refEmbed : (Option.toList (none : Option Wire)++L.core.out++L.shortCarry++[L.core.cin]).toFinset⊆L.Ambient control := by
    apply contains_finset
    simpa using (o.append banks.2.2.2.2).append (show Contains (L.Ambient control) [L.core.cin] from by
      intro q hq; apply bits q; simp at hq ⊢; tauto)
  have rr := reflected.trans refEmbed
  have core := L.measuredCore.program_wires_subset SquareReduction.c SquareReduction.p
  have coreEmbed : L.measuredCore.wires.toFinset⊆L.Ambient control := by
    apply contains_finset
    change Contains (L.Ambient control) (L.core.work++L.core.out++L.foldCarry++
      [L.core.outHigh,L.core.cin,L.core.modFlag])
    exact ((w.append o).append banks.2.2.2.1).append (by
      intro q hq; apply bits q; simp at hq ⊢; tauto)
  refine ⟨?_,?_,?_,core.trans coreEmbed⟩
  · simpa only [normalizeSource,wires_append,Finset.union_subset_iff] using And.intro ge add
  · simpa only [restoreSource,wires_append,Finset.union_subset_iff] using And.intro undo ge
  · simpa only [reflectOutput,wires_append,Finset.union_subset_iff,notRegister_wires] using
      And.intro (contains_finset o) rr

theorem measuredFold_support (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (f : MeasuredSquareFold) (hs : ∀q∈f.src,q∈L.core.product) :
    ECDSAAdd.wires (L.measuredFold f)⊆L.Ambient control := by
  have ops := L.measured_small_support control
  have cp := copyRegister_wires_subset none f.src (L.foldDestination f)
  have embed : (Option.toList (none : Option Wire)++f.src++L.foldDestination f).toFinset⊆L.Ambient control := by
    intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hq|hq
    · have h := hs q hq
      simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,h]
    · have h := List.mem_of_mem_drop (List.mem_of_mem_take hq)
      simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,h]
  have copy := cp.trans embed
  cases h : f.canonical <;>
    simp only [measuredFold,h,if_false,if_true,wires_append,wires,Finset.union_subset_iff,Finset.empty_subset] <;>
    tauto

theorem measuredFolds_support (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (orientation : Bool) (items : List MeasuredSquareFold)
    (hs : ∀f∈items,∀q∈f.src,q∈L.core.product) :
    ECDSAAdd.wires (L.measuredFolds orientation items)⊆L.Ambient control := by
  induction items generalizing orientation with
  | nil => simp [measuredFolds,ECDSAAdd.wires]
  | cons f fs ih =>
    have fold := L.measuredFold_support control f (hs f (by simp))
    have tail := ih f.negative (by intro f hf; exact hs f (by simp [hf]))
    have reflect := (L.measured_small_support control).2.2.1
    by_cases same : orientation=f.negative <;>
      simp only [measuredFolds,same,if_false,if_true,wires_append,wires,Finset.union_subset_iff,Finset.empty_subset] <;>
      tauto

theorem withMeasuredSquare_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (src dst : List Wire) (body : Program)
    (hs : 2≤src.length) (hsmax : src.length≤129) (hd : dst.length=2*src.length)
    (srcMem : ∀q∈src,q∈L.core.y++[L.core.sumCarry])
    (dstMem : ∀q∈dst,q∈L.core.product)
    (hb : ECDSAAdd.wires body⊆L.Ambient control) :
    ECDSAAdd.wires (L.withMeasuredSquare control src dst body)⊆L.Ambient control := by
  have bank := L.measured_banks_contained control
  have sizes := L.measured_bank_widths hw
  let input := L.inputBank.take src.length
  have inLen : input.length=src.length := by simp [input,sizes.1,hsmax]
  have source : Contains (L.Ambient control) src := by
    intro q hq
    have h := srcMem q hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires] at h ⊢
    tauto
  have dest : Contains (L.Ambient control) dst := by
    intro q hq
    have h := dstMem q hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,h]
  have inputSupport := bank.1.take src.length
  have leaf := mappedSignedSquare_wires_subset input dst L.leafPad L.leafCarry L.core.cin
    (by rw [inLen];exact hd) (by rw [sizes.2.2.1]) (by rw [sizes.2.1,hd];omega)
  have leafEmbed : (input++dst++L.leafPad++L.leafCarry++[L.core.cin]).toFinset⊆L.Ambient control := by
    apply contains_finset
    exact (((inputSupport.append dest).append bank.2.2.1).append bank.2.1).append (by
      intro q hq; simp at hq; subst q
      simp [Ambient,wires,CuccaroStreamedSquareLayout.wires])
  have make := leaf.1.trans leafEmbed
  have clear := leaf.2.trans leafEmbed
  have copyEmbed : ((some control).toList++src++input).toFinset⊆L.Ambient control := by
    apply contains_finset
    exact ((show Contains (L.Ambient control) (some control).toList from by
      intro q hq; simp at hq; subst q; simp [Ambient]).append source).append inputSupport
  have copy := (copyRegister_wires_subset (some control) src input).trans copyEmbed
  have eraseEmbed : (control::src++input).toFinset⊆L.Ambient control := by simpa using copyEmbed
  have erase := (eraseMask_wires_subset control src input).trans eraseEmbed
  simpa only [withMeasuredSquare,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro copy make) erase) hb) copy) clear) erase

private theorem nafItems_inside (src product : List Wire) (negative : Bool)
    (hs : ∀q∈src,q∈product) :
    ∀f∈nafMinusOneItems negative src,∀q∈f.src,q∈product := by
  intro f hf q hq
  simp only [nafMinusOneItems,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> exact hs q hq

private theorem shiftedItems_inside (src product : List Wire) (negative : Bool) (j : Nat)
    (hs : ∀q∈src,q∈product) :
    ∀f∈shiftedProductItems negative src j,∀q∈f.src,q∈product := by
  intro f hf q hq
  by_cases zero : j=0
  · simp [shiftedProductItems,zero] at hf
    subst f
    exact hs q hq
  · simp only [shiftedProductItems,zero,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|hf
    · simp only [rotateFull,List.mem_append] at hq
      rcases hq with hq|hq
      · exact hs q (List.mem_of_mem_drop hq)
      · exact hs q (List.mem_of_mem_take hq)
    · exact nafItems_inside (src.drop (256-j)) product negative
        (fun q hq => hs q (List.mem_of_mem_drop hq)) f hf q hq

theorem measured_items_support (L : CuccaroStreamedSquareWideLayout) :
    (∀f∈L.measuredAItems,∀q∈f.src,q∈L.core.product) ∧
    (∀f∈L.measuredBItems,∀q∈f.src,q∈L.core.product) ∧
    (∀f∈L.measuredCItems,∀q∈f.src,q∈L.core.product) := by
  have take : ∀q∈L.core.product.take 256,q∈L.core.product := fun _ h => List.mem_of_mem_take h
  have drop : ∀q∈L.core.product.drop 128,q∈L.core.product := fun _ h => List.mem_of_mem_drop h
  have rotate : ∀q∈L.rotated128,q∈L.core.product := by
    intro q hq
    simp only [rotated128,List.mem_append] at hq
    rcases hq with hq|hq
    · exact List.mem_of_mem_drop (List.mem_of_mem_take hq)
    · exact List.mem_of_mem_take hq
  have naf0 := nafItems_inside (L.core.product.drop 128) L.core.product false drop
  have naf1 := nafItems_inside (L.core.product.drop 128) L.core.product true drop
  have sh0 := shiftedItems_inside (L.core.product.take 256) L.core.product true 0 take
  have sh4 := shiftedItems_inside (L.core.product.take 256) L.core.product true 4 take
  have sh6 := shiftedItems_inside (L.core.product.take 256) L.core.product false 6 take
  have sh10 := shiftedItems_inside (L.core.product.take 256) L.core.product true 10 take
  have sh32 := shiftedItems_inside (L.core.product.take 256) L.core.product true 32 take
  refine ⟨?_,?_,?_⟩
  · intro f hf q hq
    simp only [measuredAItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with (rfl|rfl)|hf
    · exact take q hq
    · exact rotate q hq
    · exact naf0 f hf q hq
  · intro f hf q hq
    simp only [measuredBItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with (((((rfl|hf)|hf)|hf)|hf)|hf)|hf
    · exact rotate q hq
    · exact naf0 f hf q hq
    · exact sh0 f hf q hq
    · exact sh4 f hf q hq
    · exact sh6 f hf q hq
    · exact sh10 f hf q hq
    · exact sh32 f hf q hq
  · intro f hf q hq
    simp only [measuredCItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with (rfl|hf)|rfl
    · exact rotate q hq
    · exact naf1 f hf q hq
    · exact List.mem_of_mem_drop hq

theorem measuredProgram_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (L.measuredProgram control)⊆(control::L.wires).toFinset := by
  have items := L.measured_items_support
  have a := L.measuredFolds_support control false L.measuredAItems items.1
  have b := L.measuredFolds_support control false L.measuredBItems items.2.1
  have c := L.measuredFolds_support control true L.measuredCItems items.2.2
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sa := L.withMeasuredSquare_support hw control L.core.low (L.core.product.take 256)
    (L.measuredFolds false L.measuredAItems) (by omega) (by omega) (by omega)
    (by intro q hq; simp [CuccaroStreamedSquareLayout.low] at hq; exact List.mem_append_left _ (List.mem_of_mem_take hq))
    (fun _ hq => List.mem_of_mem_take hq) a
  have sb := L.withMeasuredSquare_support hw control L.core.high (L.core.product.take 256)
    (L.measuredFolds false L.measuredBItems) (by omega) (by omega) (by omega)
    (by intro q hq; exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
    (fun _ hq => List.mem_of_mem_take hq) b
  have sc := L.withMeasuredSquare_support hw control L.core.sum L.core.product
    (L.measuredFolds true L.measuredCItems) (by omega) (by omega) (by rw [hw.core.product,sum])
    (by
      intro q hq
      simp only [CuccaroStreamedSquareLayout.sum,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl
      · exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq))
      · simp)
    (fun _ hq => hq) c
  have sumCert := L.sum_certified hw hn
  have embed : L.wires.toFinset⊆L.Ambient control := by intro q hq; simp [Ambient,hq]
  have prep := sumCert.1.2.trans embed
  have unprep := sumCert.2.2.trans embed
  have reflection := (L.measured_small_support control).2.2.1
  change ECDSAAdd.wires (L.measuredProgram control)⊆L.Ambient control
  simpa only [measuredProgram,measuredBranchA,measuredBranchB,measuredBranchC,
    wires_append,Finset.union_subset_iff] using And.intro (And.intro (And.intro sa sb)
      (And.intro (And.intro prep sc) unprep)) reflection

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/PointMeasuredSquareCandidate.lean
noncomputable section

set_option maxHeartbeats 3000000

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Exact measured Step 4 binding in the existing point-layout pool. -/
def pointMeasuredSquareCandidate (L : ControlledPointLayout) : Program :=
  L.dialogStreamedSquareWide.measuredProgram L.core.generic

theorem pointMeasuredSquareCandidate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (pointMeasuredSquareCandidate L)=99902 ∧
    measurementCount (pointMeasuredSquareCandidate L)=99382 :=
  L.dialogStreamedSquareWide.measuredProgram_counts (L.dialogStreamedSquareWide_widths hw) L.core.generic

theorem pointMeasuredSquareCandidate_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (pointMeasuredSquareCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
  have support := L.dialogStreamedSquareWide.measuredProgram_support
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn) L.core.generic
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro q hq
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hq
      exact List.mem_of_mem_take hq
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp : q∈L.dialogPool.take 775 → q∈L.dialogPool.take 776 := fun h => small h
    tauto
  exact support.trans embed

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Framework/WireRenameComposition.lean
noncomputable section

namespace ECDSAAdd

theorem renameCorrection_comp (f g : Wire → Wire) (c : Correction) :
    renameCorrection f (renameCorrection g c)=renameCorrection (f ∘ g) c := by
  cases c <;> rfl

theorem renameInstr_comp (f g : Wire → Wire) (i : Instr) :
    renameInstr f (renameInstr g i)=renameInstr (f ∘ g) i := by
  cases i <;> simp [renameInstr,List.map_map,Function.comp_def,renameCorrection_comp]

theorem renameProgram_comp (f g : Wire → Wire) (p : Program) :
    renameProgram f (renameProgram g p)=renameProgram (f ∘ g) p := by
  simp only [renameProgram,List.map_map]
  apply List.map_congr_left
  intro i _
  exact renameInstr_comp f g i

theorem renameCorrections_congr (f g : Wire → Wire) (cs : List Correction)
    (h : ∀ q∈correctionWires cs, f q=g q) :
    cs.map (renameCorrection f)=cs.map (renameCorrection g) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z q =>
      have qeq := h q (by simp [correctionWires])
      have tail := ih (fun q hq => h q (Finset.mem_union_right _ hq))
      simp only [List.map_cons,renameCorrection,qeq,tail]
    | CZ a b =>
      have ae := h a (by simp [correctionWires])
      have be := h b (by simp [correctionWires])
      have tail := ih (fun q hq => h q (Finset.mem_union_right _ hq))
      simp only [List.map_cons,renameCorrection,ae,be,tail]

theorem renameInstr_congr (f g : Wire → Wire) (i : Instr)
    (h : ∀ q∈i.wires, f q=g q) : renameInstr f i=renameInstr g i := by
  cases i with
  | X q => simp only [renameInstr,h q (by simp [Instr.wires])]
  | CX a q => simp only [renameInstr,h a (by simp [Instr.wires]),h q (by simp [Instr.wires])]
  | CCX a b q =>
    simp only [renameInstr,h a (by simp [Instr.wires]),h b (by simp [Instr.wires]),
      h q (by simp [Instr.wires])]
  | measureX q c0 c1 =>
    have qeq := h q (by simp [Instr.wires])
    have e0 := renameCorrections_congr f g c0
      (fun q hq => h q (Finset.mem_union_left _ (Finset.mem_union_right _ hq)))
    have e1 := renameCorrections_congr f g c1
      (fun q hq => h q (Finset.mem_union_right _ hq))
    simp only [renameInstr,qeq,e0,e1]

/-- Equality of placements on actual gate and correction support suffices;
unaccessed descriptor names never affect the emitted program. -/
theorem renameProgram_congr_support (f g : Wire → Wire) (p : Program)
    (h : ∀ q∈wires p, f q=g q) : renameProgram f p=renameProgram g p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    have head := renameInstr_congr f g i (fun q hq => h q (Finset.mem_union_left _ hq))
    have tail := ih (fun q hq => h q (Finset.mem_union_right _ hq))
    change renameInstr f i :: renameProgram f p = renameInstr g i :: renameProgram g p
    rw [head,tail]

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/CompressedPointSquarePool.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.CompressedPointSquare
open ControlledPointLayout
attribute [local irreducible] run wires pointMeasuredSquareCandidate

def indexFn (i : Nat) : Nat :=
  if 515 ≤ i ∧ i < 684 then i+261 else if 776 ≤ i ∧ i < 945 then i-261 else i

private theorem index_twice : Function.Involutive indexFn := by
  intro i
  unfold indexFn
  split_ifs <;> omega

def indexPermutation : Equiv.Perm Nat :=
  {toFun:=indexFn,invFun:=indexFn,left_inv:=index_twice,right_inv:=index_twice}

theorem index_bounded (i : Nat) (hi : i < 945) : indexPermutation i < 945 := by
  change indexFn i < 945
  unfold indexFn
  split_ifs <;> omega

theorem prefix_allowed (i : Nat) (hi : i < 776) :
    indexPermutation i < 515 ∨ (684 ≤ indexPermutation i ∧ indexPermutation i < 945) := by
  change indexFn i < 515 ∨ (684 ≤ indexFn i ∧ indexFn i < 945)
  unfold indexFn
  split_ifs <;> omega

def BoundedInjective (w : Nat → Wire) : Prop :=
  ∀i j,i < 945 → j < 945 → w i=w j → i=j

def LeftSite (w : Nat → Wire) (q : Wire) : Prop := ∃i,515 ≤ i ∧ i < 684 ∧ q=w i
def RightSite (w : Nat → Wire) (q : Wire) : Prop := ∃i,776 ≤ i ∧ i < 945 ∧ q=w i

/-- Only the338 declared pool sites are moved; fallback labels outside
that allocation are never assumed injective. -/
noncomputable def wireFn (w : Nat → Wire) (q : Wire) : Wire := by
  classical
  exact if h : LeftSite w q then w (Classical.choose h+261)
    else if h : RightSite w q then w (Classical.choose h-261) else q

theorem wire_apply (w : Nat → Wire) (hn : BoundedInjective w)
    (i : Nat) (hi : i < 945) : wireFn w (w i)=w (indexPermutation i) := by
  classical
  change wireFn w (w i)=w (indexFn i)
  by_cases a : 515 ≤ i ∧ i < 684
  · have yes : LeftSite w (w i) := ⟨i,a.1,a.2,rfl⟩
    have spec := Classical.choose_spec yes
    have pick : Classical.choose yes=i := hn _ i (by omega) hi spec.2.2.symm
    simp only [wireFn,dif_pos yes,pick,indexFn,if_pos a]
  · have no : ¬LeftSite w (w i) := by
      rintro ⟨j,hj,hk,e⟩
      have eq := hn i j hi (by omega) e
      exact a (by omega)
    by_cases b : 776 ≤ i ∧ i < 945
    · have yes : RightSite w (w i) := ⟨i,b.1,b.2,rfl⟩
      have spec := Classical.choose_spec yes
      have pick : Classical.choose yes=i := hn _ i spec.2.1 hi spec.2.2.symm
      simp only [wireFn,dif_neg no,dif_pos yes,pick,indexFn,if_neg a,if_pos b]
    · have no' : ¬RightSite w (w i) := by
        rintro ⟨j,hj,hk,e⟩
        have eq := hn i j hi hk e
        exact b (by omega)
      simp only [wireFn,dif_neg no,dif_neg no',indexFn,if_neg a,if_neg b]

private theorem wire_twice (w : Nat → Wire) (hn : BoundedInjective w) :
    Function.Involutive (wireFn w) := by
  classical
  intro q
  by_cases a : LeftSite w q
  · obtain ⟨i,lo,hi,rfl⟩ := a
    rw [wire_apply w hn i (by omega),wire_apply w hn _ (index_bounded i (by omega))]
    exact congrArg w (indexPermutation.symm_apply_apply i)
  · by_cases b : RightSite w q
    · obtain ⟨i,lo,hi,rfl⟩ := b
      rw [wire_apply w hn i hi,wire_apply w hn _ (index_bounded i hi)]
      exact congrArg w (indexPermutation.symm_apply_apply i)
    · simp only [wireFn,dif_neg a,dif_neg b]

noncomputable def poolPermutation (w : Nat → Wire) (hn : BoundedInjective w) : Equiv.Perm Wire :=
  {toFun:=wireFn w,invFun:=wireFn w,left_inv:=wire_twice w hn,right_inv:=wire_twice w hn}

theorem outside_fixed (w : Nat → Wire) (hn : BoundedInjective w) (q : Wire)
    (ha : ¬LeftSite w q) (hb : ¬RightSite w q) : poolPermutation w hn q=q := by
  classical
  change wireFn w q=q
  simp only [wireFn,dif_neg ha,dif_neg hb]

private theorem getD_member {α : Type} (xs : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    xs.getD i d∈xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => exact List.mem_cons_of_mem a (ih i (by simpa using hi))

private theorem getD_injective (xs : List Wire) (nd : xs.Nodup) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) (eq : xs.getD i 0=xs.getD j 0) : i=j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons a xs ih =>
    have tail := (List.nodup_cons.mp nd)
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getD_cons_zero,List.getD_cons_succ] at eq
        exact (tail.1 (eq.symm ▸ getD_member xs j 0 (by simpa using hj))).elim
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getD_cons_zero,List.getD_cons_succ] at eq
        exact (tail.1 (eq ▸ getD_member xs i 0 (by simpa using hi))).elim
      | succ j =>
        exact congrArg Nat.succ (ih tail.2 i j (by simpa using hi) (by simpa using hj) eq)

theorem layout_bounded_injective (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    BoundedInjective L.core.poolWire := by
  have nd : L.core.pool.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have full := List.nodup_iff_count.mp (L.core_nodup hn) q
    simp only [PointAddLayout.wires,PointAddLayout.work,List.count_append] at full
    omega
  intro i j hi hj eq
  exact getD_injective L.core.pool nd i j (by rw [hw.pool]; omega) (by rw [hw.pool]; omega) eq

def residents (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags

theorem resident_fixed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈residents L) : poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) q=q := by
  have dis := (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  have away : q∉L.dialogPool := List.disjoint_left.mp dis hq
  have bit (i : Nat) (hi : i < 945) : L.core.poolWire i∈L.dialogPool := by
    have small : L.core.poolWire i∈L.core.pool.take 2613 := by
      rw [←L.core.pool_prefix hw 2613 (by omega)]
      exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1]; omega,rfl⟩
    exact small
  apply outside_fixed
  · rintro ⟨i,lo,hi,e⟩
    exact away (e ▸ bit i (by omega))
  · rintro ⟨i,lo,hi,e⟩
    exact away (e ▸ bit i hi)

/-- Explicit common work inventory; square image uses its existing first
and second intervals, and does not reintroduce515..683. -/
def sharedPool (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515++wireBlock L.core.poolWire 684 858++wireBlock L.core.poolWire 1800 5

noncomputable def program (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (pointMeasuredSquareCandidate L)

theorem measured_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L hw hn)⊆(residents L++sharedPool L).toFinset := by
  intro q hq
  rw [program,renameProgram_support] at hq
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  have supp := pointMeasuredSquareCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at supp
  have res : old∈residents L ∨ old∈L.dialogPool.take 776 := by
    simp only [residents,PointAddLayout.pointWires,inPlaceFlags,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false]
    tauto
  rcases res with res|mem
  · rw [resident_fixed L hw hn old res]
    exact List.mem_toFinset.mpr (List.mem_append_left _ res)
  · have prefixView : L.dialogPool.take 776=wireBlock L.core.poolWire 0 776 := by
      simp only [dialogPool,List.take_take,Nat.min_eq_left (show 776 ≤ 2613 by omega)]
      exact (L.core.pool_prefix hw 776 (by omega)).symm
    rw [prefixView] at mem
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) (L.core.poolWire i)=
      L.core.poolWire (indexPermutation i) from
        wire_apply L.core.poolWire (layout_bounded_injective L hw hn) i (by omega)]
    apply List.mem_toFinset.mpr
    apply List.mem_append_right
    rcases prefix_allowed i bound with lo|hi
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr
        ⟨indexPermutation i,by simp [List.mem_range'_1]; omega,rfl⟩))
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨indexPermutation i,by simp [List.mem_range'_1]; omega,rfl⟩))

/-- Computable finite lookup, with length as the not-found sentinel. -/
def searchIndex (q : Wire) : List Wire → Nat
  | [] => 0
  | a::as => if q=a then 0 else searchIndex q as+1

private theorem search_spec (xs : List Wire) (q : Wire) (h : searchIndex q xs < xs.length) :
    xs.getD (searchIndex q xs) 0=q := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases e : q=a
    · simp [searchIndex,e]
    · have bound : searchIndex q xs < xs.length := by simpa [searchIndex,e] using h
      simpa only [searchIndex,if_neg e,List.getD_cons_succ] using ih bound

private theorem search_hits (xs : List Wire) (nd : xs.Nodup) (i : Nat) (hi : i < xs.length) :
    searchIndex (xs.getD i 0) xs=i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    have tail := List.nodup_cons.mp nd
    cases i with
    | zero => simp [searchIndex]
    | succ i =>
      have bound : i < xs.length := by simpa using hi
      have away : xs.getD i 0≠a := fun e => tail.1 (e ▸ getD_member xs i 0 bound)
      simp only [List.getD_cons_succ,searchIndex,if_neg away]
      exact congrArg Nat.succ (ih tail.2 i bound)

private theorem prefix_getD (w : Nat → Wire) (i : Nat) (hi : i < 945) :
    (wireBlock w 0 945).getD i 0=w i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [wireBlock_length] using hi)]
  simp [wireBlock]

private theorem found_index (w : Nat → Wire) (hn : BoundedInjective w) (i : Nat) (hi : i < 945) :
    searchIndex (w i) (wireBlock w 0 945)=i := by
  have nd : (wireBlock w 0 945).Nodup := by
    apply List.Nodup.map_on
    · intro a ha b hb eq
      simp only [List.mem_range'_1] at ha hb
      exact hn a b (by omega) (by omega) eq
    · exact List.nodup_range'
  have hit := search_hits (wireBlock w 0 945) nd i (by simpa only [wireBlock_length] using hi)
  rw [prefix_getD w i hi] at hit
  exact hit

/-- Production relabeling reads only945 declared pool labels and is fully
computable; no Classical.choose value occurs in the emitted program. -/
def labelFn (w : Nat → Wire) (q : Wire) : Wire :=
  let i := searchIndex q (wireBlock w 0 945)
  if i < 945 then w (indexPermutation i) else q

theorem label_matches (w : Nat → Wire) (hn : BoundedInjective w) (q : Wire) :
    labelFn w q=poolPermutation w hn q := by
  let i := searchIndex q (wireBlock w 0 945)
  by_cases found : i < 945
  · have qeq : q=w i := (search_spec (wireBlock w 0 945) q
        (by simpa only [wireBlock_length] using found)).symm.trans (prefix_getD w i found)
    change (if i < 945 then w (indexPermutation i) else q)=wireFn w q
    rw [if_pos found,qeq,wire_apply w hn i found]
  · have noA : ¬LeftSite w q := by
      rintro ⟨j,lo,hi,e⟩
      have hit : i=j := by change searchIndex q (wireBlock w 0 945)=j; rw [e]; exact found_index w hn j (by omega)
      omega
    have noB : ¬RightSite w q := by
      rintro ⟨j,lo,hi,e⟩
      have hit : i=j := by change searchIndex q (wireBlock w 0 945)=j; rw [e]; exact found_index w hn j hi
      omega
    change (if i < 945 then w (indexPermutation i) else q)=poolPermutation w hn q
    rw [if_neg found,outside_fixed w hn q noA noB]

def computableProgram (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (pointMeasuredSquareCandidate L)

theorem computableProgram_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    computableProgram L=program L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

theorem computable_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (computableProgram L)⊆(residents L++sharedPool L).toFinset := by
  rw [computableProgram_eq L hw hn]
  exact measured_support L hw hn

end ECDSAAdd.Arithmetic.CompressedPointSquare
end

-- source: ECDSAAdd/Arithmetic/SignedSquarePhysical.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem xorWhenFalse_physical (c : Wire) (ys : List Wire) (hc : c ∉ ys) :
    GatePhysical (xorWhenFalse c ys) := by
  induction ys with
  | nil => simp [xorWhenFalse,GatePhysical]
  | cons y ys ih =>
    simp only [List.mem_cons,not_or] at hc
    simp only [xorWhenFalse,gatePhysical_append]
    exact ⟨by simpa [GatePhysical,PhysicalInstr,ProperGate] using hc.1,ih hc.2⟩

theorem signedSquareRow_physical (c : Wire) (xs dst pad carry : List Wire)
    (hn : (c :: xs ++ dst ++ pad ++ carry).Nodup) :
    GatePhysical (signedSquareRow c xs dst pad carry) ∧
    GatePhysical (signedSquareRowClear c xs dst pad carry) := by
  have hc : c ∉ dst := by
    intro hh; exact (List.nodup_cons.mp hn).1 (by simp [hh])
  have ht : c ∉ dst.take xs.length := fun hh => hc (List.mem_of_mem_take hh)
  have nd : (c :: (xs ++ pad.take 1) ++ dst ++ carry.take xs.length).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have hp := (List.take_sublist 1 pad).count_le q
    have hk := (List.take_sublist xs.length carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  simp only [signedSquareRow,signedSquareRowClear,gatePhysical_append]
  exact ⟨⟨⟨xorWhenFalse_physical _ _ ht,addInPlace_physical _ _ _ _ nd⟩,
    xorWhenFalse_physical _ _ hc⟩,
    xorWhenFalse_physical _ _ hc,notRegister_physical _,addInPlace_physical _ _ _ _ nd,
    notRegister_physical _,xorWhenFalse_physical _ _ ht⟩

theorem signedSquareRows_physical (xs dst pad carry : List Wire)
    (hn : (xs ++ dst ++ pad ++ carry).Nodup) :
    GatePhysical (signedSquareRows xs dst pad carry) ∧
    GatePhysical (signedSquareRowsClear xs dst pad carry) := by
  induction xs generalizing dst with
  | nil => simp [signedSquareRows,signedSquareRowsClear,GatePhysical]
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedSquareRows,signedSquareRowsClear,GatePhysical]
    | cons d xs =>
      have nr : (c :: (d::xs) ++ (dst.drop 1).take ((d::xs).length+1) ++ pad ++ carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hn q
        have hd := (List.drop_sublist 1 dst).count_le q
        have ht := (List.take_sublist ((d::xs).length+1) (dst.drop 1)).count_le q
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      have nt : ((d::xs) ++ dst.drop 2 ++ pad ++ carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hn q
        have hd := (List.drop_sublist 2 dst).count_le q
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      have row := signedSquareRow_physical _ _ _ _ _ nr
      have tail := ih _ nt
      simp only [signedSquareRows,signedSquareRowsClear,gatePhysical_append]
      exact ⟨⟨row.1,tail.1⟩,tail.2,row.2⟩

theorem signedSquareTop_physical (xs dst : List Wire) (hn : (xs ++ dst).Nodup) :
    GatePhysical (signedSquareTop xs dst) := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,GatePhysical]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,GatePhysical]
      | cons d dst =>
        cases dst with
        | nil => simp [signedSquareTop,GatePhysical]
        | cons z dst =>
          have hx : x ≠ z := by
            intro he; subst x
            have h := List.nodup_iff_count.mp hn z
            simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,ite_true] at h
            omega
          simpa [signedSquareTop,GatePhysical,PhysicalInstr,ProperGate] using hx
    | cons x' xs =>
      cases dst with
      | nil => simp [signedSquareTop,GatePhysical]
      | cons d dst =>
        cases dst with
        | nil => simp [signedSquareTop,GatePhysical]
        | cons z dst =>
          apply ih
          apply List.nodup_iff_count.mpr; intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append] at h ⊢; omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedSquarePhysical.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem mappedDiag_physical (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin :: xs ++ dst ++ carry).Nodup) :
    GatePhysical (mappedDiagAdd xs dst carry cin) ∧
    GatePhysical (mappedDiagSub xs dst carry cin) := by
  have nd : (cin :: dst ++ carry.take (dst.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist (dst.length-1) carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have ha : ∀ b ∈ mappedDiagonal xs, ∀ q ∈ b.wire,
      q ∉ cin :: dst ++ carry.take (dst.length-1) := by
    intro b hb q hq hm
    have hs : q ∈ mappedWires (mappedDiagonal xs) :=
      List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    rw [mappedDiagonal_wires] at hs
    have hx : q ∈ xs := by
      rcases List.mem_append.mp hs with h|h
      · exact h
      · exact List.mem_of_mem_take h
    have h := List.nodup_iff_count.mp hn q
    have hc := List.count_pos_iff.mpr hx
    have hh := List.count_pos_iff.mpr hm
    have ht := (List.take_sublist (dst.length-1) carry).count_le q
    simp only [List.count_cons,List.count_append] at h hh; omega
  have hadd := mappedAdd_physical (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin nd ha
  refine ⟨hadd,?_⟩
  simp only [mappedDiagSub,mappedSub,gatePhysical_append]
  exact ⟨⟨notRegister_physical _,hadd⟩,notRegister_physical _⟩

theorem mappedSignedSquare_physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin :: xs ++ dst ++ pad ++ carry).Nodup) :
    GatePhysical (mappedSignedSquare xs dst pad carry cin) ∧
    GatePhysical (mappedSignedSquareClear xs dst pad carry cin) := by
  have nr : (xs ++ dst ++ pad ++ carry).Nodup := (List.nodup_cons.mp hn).2
  have nt : (xs ++ dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have nd : (cin :: xs ++ dst ++ carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have rows := signedSquareRows_physical xs dst pad carry nr
  have top := signedSquareTop_physical xs dst nt
  have diag := mappedDiag_physical xs dst carry cin nd
  simp only [mappedSignedSquare,mappedSignedSquareClear,gatePhysical_append]
  exact ⟨⟨⟨rows.1,top⟩,diag.2⟩,⟨diag.1,top⟩,rows.2⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredFoldPhysical.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem MeasuredSourceNormalizeLayout.physical (L : MeasuredSourceNormalizeLayout)
    (p c : Nat) (hn : L.wires.Nodup) :
    GatePhysical (L.normalize p c) ∧ GatePhysical (L.restore p) ∧ GatePhysical (L.reflect p) := by
  have nd : (L.cin :: L.word ++ L.carry).Nodup := (List.nodup_cons.mp hn).2
  have hc : ∀ q ∈ some L.flag, q ∉ L.cin :: L.word ++ L.carry := by
    intro q hq; have he : L.flag = q := by simpa using hq
    subst q; exact (List.nodup_cons.mp hn).1
  have nc : ([L.cin,L.flag] ++ L.word ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simpa [wires,List.count_append,List.count_cons,List.count_nil,Nat.add_comm,
      Nat.add_left_comm,Nat.add_assoc] using h
  simp only [normalize,restore,reflect,gatePhysical_append]
  exact ⟨⟨compareConstantGe_physical _ _ _ _ _ nc,mappedConstAdd_physical _ _ _ _ _ nd hc⟩,
    ⟨mappedConstAdd_physical _ _ _ _ _ nd hc,compareConstantGe_physical _ _ _ _ _ nc⟩,
    notRegister_physical _,mappedConstAdd_physical _ _ _ _ _ nd (by simp)⟩

theorem measuredFoldKernel_physical (K : MeasuredCanonicalModLayout) (flag : Wire)
    (canonical : Bool) (c p : Nat) (hn : (flag :: K.wires).Nodup) :
    GatePhysical (measuredFoldKernel K flag canonical c p) := by
  have nd : (measuredFoldNormalize K flag).wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist (K.src.length-1) K.carry).count_le q
    simp only [measuredFoldNormalize,MeasuredSourceNormalizeLayout.wires,
      MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have hN := (measuredFoldNormalize K flag).physical p c nd
  have hK := K.physical c p (List.nodup_cons.mp hn).2
  cases canonical with
  | false =>
    simpa only [measuredFoldKernel,Bool.false_eq_true,ite_false,gatePhysical_append]
      using (show (GatePhysical ((measuredFoldNormalize K flag).normalize p c) ∧
        GatePhysical (K.program c p)) ∧ GatePhysical ((measuredFoldNormalize K flag).restore p)
        from ⟨⟨hN.1,hK⟩,hN.2.1⟩)
  | true => simpa [measuredFoldKernel] using hK

theorem copySlice_physical (src dst : List Wire) (shift : Nat) (hn : (src ++ dst).Nodup) :
    GatePhysical (copySlice src dst shift) := by
  apply copyRegister_physical none _ _ _ (by simp)
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hn q
  have hdrop := (List.drop_sublist shift dst).count_le q
  have htake := (List.take_sublist src.length (dst.drop shift)).count_le q
  simp only [List.count_append] at h ⊢; omega

theorem measuredCopiedFold_physical (K : MeasuredCanonicalModLayout) (flag : Wire)
    (src : List Wire) (shift : Nat) (canonical : Bool) (c p : Nat)
    (hn : (src ++ flag :: K.wires).Nodup) :
    GatePhysical (measuredCopiedFold K flag src shift canonical c p) := by
  have nk : (flag :: K.wires).Nodup := (List.nodup_append.mp hn).2.1
  have nc : (src ++ K.src).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [measuredCopiedFold,gatePhysical_append]
  exact ⟨⟨copySlice_physical _ _ _ nc,measuredFoldKernel_physical _ _ _ _ _ nk⟩,
    copySlice_physical _ _ _ nc⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedPhysical.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
open RecordedQuantum

theorem measuredFold_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (f : MeasuredSquareFold)
    (hs : ∀ q, f.src.count q ≤ L.core.product.count q) : GatePhysical (L.measuredFold f) := by
  rw [L.measuredFold_eq_copied hw]
  exact measuredCopiedFold_physical _ _ _ _ _ _ _ (L.measuredFold_interfaces hn f.src hs)

theorem reflectOutput_physical (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    GatePhysical L.reflectOutput := by
  let N : MeasuredSourceNormalizeLayout :=
    {word:=L.core.out,carry:=L.shortCarry,cin:=L.core.cin,flag:=L.core.normFlag}
  have nd : N.wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist 255 L.foldCarry).count_le q
    simp only [N,MeasuredSourceNormalizeLayout.wires,shortCarry,foldCarry,foldPad,
      wires,CuccaroStreamedSquareLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ht ⊢
    omega
  exact (N.physical SquareReduction.p SquareReduction.c nd).2.2

theorem measuredFolds_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (orientation : Bool) (items : List MeasuredSquareFold)
    (hs : ∀ f ∈ items, ∀ q, f.src.count q ≤ L.core.product.count q) :
    GatePhysical (L.measuredFolds orientation items) := by
  induction items generalizing orientation with
  | nil => simp [measuredFolds,GatePhysical]
  | cons f fs ih =>
    have ht := ih f.negative (fun z hz => hs z (by simp [hz]))
    have hf := L.measuredFold_physical hw hn f (hs f (by simp))
    have hr := L.reflectOutput_physical hn
    simp only [measuredFolds,gatePhysical_append]
    refine ⟨⟨?_,hf⟩,ht⟩
    split
    · simp [GatePhysical]
    · exact hr

theorem withMeasuredSquare_physical (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control :: L.wires).Nodup) (src dst : List Wire)
    (hs : ∀ q, src.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q)
    (hd : ∀ q, dst.count q ≤ L.core.product.count q) (body : Program)
    (hb : GatePhysical body) : GatePhysical (L.withMeasuredSquare control src dst body) := by
  have nd := L.measured_leaf_nodup control hn src dst hs hd
  have nc : (src ++ L.inputBank.take src.length).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have hc : ∀ q ∈ some control, q ∉ L.inputBank.take src.length := by
    intro q hq hm
    have he : control = q := by simpa using hq
    subst q
    have h := List.nodup_iff_count.mp nd control
    have hh := List.count_pos_iff.mpr hm
    simp only [List.count_cons,List.count_append,beq_self_eq_true,ite_true] at h; omega
  have ns : (L.core.cin :: L.inputBank.take src.length ++ dst ++ L.leafPad ++ L.leafCarry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have cp := copyRegister_physical (some control) src (L.inputBank.take src.length) nc hc
  have sq := mappedSignedSquare_physical _ _ _ _ _ ns
  have er := eraseMask_physical control src (L.inputBank.take src.length)
  simp only [withMeasuredSquare,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨cp,sq.1⟩,er⟩,hb⟩,cp⟩,sq.2⟩,er⟩

/-- Layout bounds for all static fold lists; extracting counts on a zero
basis introduces no assumption about the circuit's actual input state. -/
theorem measuredItems_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀ f ∈ L.measuredAItems, ∀ q, f.src.count q ≤ L.core.product.count q) ∧
    (∀ f ∈ L.measuredBItems, ∀ q, f.src.count q ≤ L.core.product.count q) ∧
    (∀ f ∈ L.measuredCItems, ∀ q, f.src.count q ≤ L.core.product.count q) := by
  let z : BasisState := fun _ => false
  have hz : regValue L.core.product z = 0^2 := by
    simpa using (regValue_zero L.core.product z).mpr (fun _ _ => rfl)
  exact ⟨fun f hf => (L.measuredA_views hw z 0 (by decide) hz f hf).count,
    (fun f hf => (L.measuredB_views hw z 0 (by decide) hz f hf).count),
    (fun f hf => (L.measuredC_views hw z 0 hz f hf).count)⟩

theorem measuredProgram_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (L.measuredProgram control) := by
  have nd := (List.nodup_cons.mp hn).2
  have hc := L.measuredItems_counts hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have a := L.withMeasuredSquare_physical control hn _ _ hl hp _
    (L.measuredFolds_physical hw nd false _ hc.1)
  have b := L.withMeasuredSquare_physical control hn _ _ hb hp _
    (L.measuredFolds_physical hw nd false _ hc.2.1)
  have c := L.withMeasuredSquare_physical control hn _ _ hs (fun _ => le_rfl) _
    (L.measuredFolds_physical hw nd true _ hc.2.2)
  have prep := (physical_embed _).mp (physical_of_proper _ (L.sum_certified hw nd).1.1)
  have clear := (physical_embed _).mp (physical_of_proper _ (L.sum_certified hw nd).2.1)
  simp only [measuredProgram,measuredBranchA,measuredBranchB,measuredBranchC,gatePhysical_append]
  exact ⟨⟨⟨a,b⟩,⟨prep,c⟩,clear⟩,L.reflectOutput_physical nd⟩

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/PointSquarePhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem gatePhysical_rename (f : Wire → Wire) (hf : Function.Injective f)
    (p : Program) (hp : GatePhysical p) : GatePhysical (renameProgram f p) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have h := hp j hj
  cases j <;> simp_all [renameInstr,PhysicalInstr,ProperGate, hf.eq_iff]

theorem pointMeasuredSquareCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (pointMeasuredSquareCandidate L) := by
  apply L.dialogStreamedSquareWide.measuredProgram_physical (L.dialogStreamedSquareWide_widths hw)
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢; omega

theorem CompressedPointSquare.computableProgram_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (computableProgram L) := by
  rw [computableProgram_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact pointMeasuredSquareCandidate_physical L hw hn

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactWalkPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem signComplement_physical (q : Wire) (xs : List Wire) (hq : q ∉ xs) :
    GatePhysical (signComplement q xs) := by
  intro i hi
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
  exact fun he => hq (he ▸ hx)

theorem signedWords_physical (q : Wire) (x y carry : List Wire)
    (hn : (q::x++y++carry).Nodup) :
    GatePhysical (signedAdd q x y carry) ∧ GatePhysical (signedSub q x y carry) := by
  have away : q ∉ x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x away
  have add := addInPlace_physical x y carry q hn
  have nots := notRegister_physical y
  have h : GatePhysical (signedAdd q x y carry) := by
    simpa only [signedAdd,gatePhysical_append] using And.intro (And.intro fan add) fan
  exact ⟨h,by simpa only [signedSub,gatePhysical_append] using And.intro (And.intro nots h) nots⟩

theorem narrowRecords_physical (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) :
    GatePhysical (narrowSignedRecord L n) ∧ GatePhysical (narrowSignedUnrecord L n) := by
  have view := L.views n hw
  have nd := L.short_nodup hn
  have sx : L.sx≠L.q := by
    intro eq
    exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←eq])
  have sy : L.sy≠L.q := by
    intro eq
    exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←eq])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,sx,sy]
  have a := signedWords_physical L.q L.xp L.yp L.carryLow nd
  have f := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowSignedRecord,narrowSignedUnrecord,signedRecord,signedUnrecord,
    view.1,view.2.1,view.2.2.1,view.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨⟨toggle,a.1⟩,toggle⟩,f⟩,⟨f,⟨toggle,a.2⟩,toggle⟩⟩

theorem narrowTicks_physical (L : SkywalkIntegerLayout) (n : Nat) (hv : L.Valid)
    (hn : 0<n) (hle : n≤L.half.length) :
    GatePhysical (narrowSkywalkTick L n) ∧ GatePhysical (narrowSkywalkUntick L n) := by
  have route := L.route_nodup hv
  have swnd : (L.a0::L.ah++L.bh).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp route q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have ab : L.a0≠L.b0 := by
    intro eq; exact (List.nodup_cons.mp route).1 (by simp [eq])
  have se : L.aSign≠L.ext := by
    intro eq
    have h := List.nodup_iff_count.mp hv.nodup L.ext
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,eq,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have pa : L.previous≠L.a0 := by
    intro eq
    exact (List.nodup_cons.mp hv.nodup).1 (by simp [eq])
  have sw := swapRegisters_physical L.a0 L.ah L.bh swnd
  have cx : GatePhysical [.CX L.a0 L.b0] := by simp [GatePhysical,PhysicalInstr,ProperGate,ab]
  have half : GatePhysical (skywalkSignedHalf L.aSign L.ext) := by
    simp [skywalkSignedHalf,GatePhysical,PhysicalInstr,ProperGate,se]
  have prev : GatePhysical [.CX L.previous L.a0] := by simp [GatePhysical,PhysicalInstr,ProperGate,pa]
  have recs := narrowRecords_physical (narrowSkywalkRecordLayout L n) n
    (narrowSkywalkRecord_widths L hv n hn hle) (narrowSkywalkRecord_nodup L hv n hn hle)
  simp only [narrowSkywalkTick,narrowSkywalkUntick,skywalkRoute,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨sw,cx⟩,half⟩,recs.1⟩,prev⟩,⟨⟨⟨⟨prev,recs.2⟩,half⟩,cx⟩,sw⟩⟩

theorem compactSigns_physical (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid) :
    GatePhysical (compactSkywalkSignRelease L) ∧ GatePhysical (compactSkywalkSignExpand L) :=
  ⟨signComplement_physical L.sign L.released (L.signAway hv),
   signComplement_physical L.sign L.released (L.signAway hv)⟩

theorem compactTicks_physical (w : Nat → Wire) (i : Nat) (hi : i<512)
    (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (compactSkywalkTick w i) ∧ GatePhysical (compactSkywalkReverseTick w i) := by
  have bounds := compactSkywalkTick_width_bounds i hi
  have n := narrowTicks_physical (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)
    (compactSkywalkTick_valid w i hi hn) (by omega)
    (by rw [compactSkywalkTick_half w i hi,wireBlock_length]; omega)
  have val := compactSkywalkTick_release_valid w i hi hn
  have a := compactSigns_physical (compactSkywalkTickARelease w i) val.1
  have b := compactSigns_physical (compactSkywalkTickBRelease w i) val.2
  simp only [compactSkywalkTick,compactSkywalkTickCleanup,compactSkywalkReverseTick,
    compactSkywalkReverseExpand,gatePhysical_append]
  exact ⟨⟨n.1,a.1,b.1⟩,⟨⟨b.2,a.2⟩,n.2⟩⟩

theorem codecPack_physical : GatePhysical TranscriptCodec3.pack := by
  apply physicalGateCheck_correct
  decide

theorem codecUnpack_physical : GatePhysical TranscriptCodec3.unpack := by
  apply physicalGateCheck_correct
  decide

theorem transcriptCodec_physical (w : Fin 6 → Wire) :
    GatePhysical (TranscriptCodec3.encode w) ∧ GatePhysical (TranscriptCodec3.decode w) := by
  exact ⟨gatePhysical_rename _ (TranscriptCodec3.placement w).injective _ codecPack_physical,
    gatePhysical_rename _ (TranscriptCodec3.placement w).injective _ codecUnpack_physical⟩

theorem compressedLoops_physical (w : Nat → Wire) (i n : Nat) (hi : i+n≤512)
    (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (compressedCompactForward w i n) ∧ GatePhysical (compressedCompactReverse w i n) := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,compressedCompactReverse,GatePhysical]
  | succ n ih =>
    have tick := compactTicks_physical w i (by omega) hn
    have tail := ih (i+1) (by omega)
    have codec := transcriptCodec_physical (compressedHistoryMap w (i-3))
    have pack : GatePhysical (compressedPackAfter w i) := by
      unfold compressedPackAfter
      split
      · exact codec.1
      · simp [GatePhysical]
    have unpack : GatePhysical (compressedDecodeBefore w i) := by
      unfold compressedDecodeBefore
      split
      · exact codec.2
      · simp [GatePhysical]
    simp only [compressedCompactForward,compressedCompactReverse,gatePhysical_append]
    exact ⟨⟨⟨tick.1,pack⟩,tail.1⟩,⟨⟨tail.2,unpack⟩,tick.2⟩⟩
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedAllocationPermutation.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedAllocation

def W (j : Nat) : Nat := 515+j
def H (j : Nat) : Nat := 1028+3*j+1
def spare : Nat := 684
def workRegion (q : Nat) : Prop := 515 ≤ q ∧ q ≤ 684
def holeRegion (q : Nat) : Prop := 1029 ≤ q ∧ q ≤ 1536 ∧ q%3=0
def zeroRegion (q : Nat) : Prop := workRegion q ∨ holeRegion q
def omitted (q : Nat) : Prop := 515 ≤ q ∧ q < 684

instance workRegion_decidable (q : Nat) : Decidable (workRegion q) := by
  unfold workRegion
  infer_instance

instance holeRegion_decidable (q : Nat) : Decidable (holeRegion q) := by
  unfold holeRegion
  infer_instance

private def baseFn (q : Nat) : Nat :=
  if workRegion q then H (q-515)
  else if holeRegion q then W ((q-1029)/3) else q

private theorem base_W (j : Nat) (hj : j < 170) : baseFn (W j)=H j := by
  have h : workRegion (W j) := by unfold workRegion W; omega
  simp only [baseFn,if_pos h]
  unfold W H
  omega

private theorem base_H (j : Nat) (hj : j < 170) : baseFn (H j)=W j := by
  have nw : ¬workRegion (H j) := by unfold workRegion H; omega
  have hh : holeRegion (H j) := by unfold holeRegion H; omega
  simp only [baseFn,if_neg nw,if_pos hh]
  unfold W H
  omega

private theorem base_involutive : Function.Involutive baseFn := by
  intro q
  by_cases hw : workRegion q
  · have hj : q-515 < 170 := by unfold workRegion at hw; omega
    have eq : q=W (q-515) := by unfold workRegion at hw; unfold W; omega
    rw [eq,base_W _ hj,base_H _ hj]
  · by_cases hh : holeRegion q
    · have hj : (q-1029)/3 < 170 := by unfold holeRegion at hh; omega
      have eq : q=H ((q-1029)/3) := by unfold holeRegion at hh; unfold H; omega
      rw [eq,base_H _ hj,base_W _ hj]
    · simp only [baseFn,if_neg hw,if_neg hh]

/-- Swap all170 disjoint work/codec-zero pairs. This is a total public
permutation, rather than a noninjective alias of old logical wires. -/
def pi0 : Equiv.Perm Nat :=
  { toFun:=baseFn,invFun:=baseFn,left_inv:=base_involutive,right_inv:=base_involutive }

theorem pi0_W (j : Nat) (hj : j < 170) : pi0 (W j)=H j := base_W j hj
theorem pi0_H (j : Nat) (hj : j < 170) : pi0 (H j)=W j := base_H j hj

theorem pi0_outside (q : Nat) (hq : ¬zeroRegion q) : pi0 q=q := by
  have hw : ¬workRegion q := fun h => hq (Or.inl h)
  have hh : ¬holeRegion q := fun h => hq (Or.inr h)
  change baseFn q=q
  simp only [baseFn,if_neg hw,if_neg hh]

private theorem swap_left (a b : Nat) : Equiv.swap a b a=b := by
  simp

private theorem swap_right (a b : Nat) : Equiv.swap a b b=a := by
  simp

private theorem swap_outside (a b q : Nat) (ha : q ≠ a) (hb : q ≠ b) :
    Equiv.swap a b q=q := by simp [Equiv.swap_apply_def,ha,hb]

/-- Restore the active raw codec slot while assigning its work role to
the common spare. The remaining role exchange is an injective3-cycle. -/
def pi (j : Nat) : Equiv.Perm Nat :=
  (Equiv.swap (W j) (H j)).trans ((Equiv.swap (H j) (H 169)).trans pi0)

theorem pi_apply (j q : Nat) :
    pi j q=pi0 (Equiv.swap (H j) (H 169) (Equiv.swap (W j) (H j) q)) := rfl

theorem pi_selected (j : Nat) (_hj : j < 170) : pi j (W j)=spare := by
  rw [pi_apply,swap_left,swap_left,pi0_H 169 (by omega)]
  rfl

theorem pi_current (j : Nat) (hj : j < 170) : pi j (H j)=H j := by
  have a : W j ≠ H j := by unfold W H; omega
  have b : W j ≠ H 169 := by unfold W H; omega
  rw [pi_apply,swap_right,swap_outside _ _ _ a b,pi0_W j hj]

theorem pi_other (j k : Nat) (hj : j < 170) (hk : k < 170) (hne : k ≠ j) :
    pi j (W k)=H k := by
  have a : W k ≠ W j := by unfold W; omega
  have b : W k ≠ H j := by unfold W H; omega
  have c : W k ≠ H 169 := by unfold W H; omega
  rw [pi_apply,swap_outside _ _ _ a b,swap_outside _ _ _ b c,pi0_W k hk]

theorem pi_outside (j q : Nat) (hj : j < 170) (hq : ¬zeroRegion q) : pi j q=q := by
  have nw : q ≠ W j := by intro e; subst q; apply hq; left; unfold workRegion W; omega
  have nh : q ≠ H j := by intro e; subst q; apply hq; right; unfold holeRegion H; omega
  have ns : q ≠ H 169 := by intro e; subst q; apply hq; right; unfold holeRegion H; omega
  rw [pi_apply,swap_outside _ _ _ nw nh,swap_outside _ _ _ nh ns,pi0_outside q hq]

theorem pi_selected_not_omitted (j : Nat) (hj : j < 170) : ¬omitted (pi j (W j)) := by
  rw [pi_selected j hj]
  unfold omitted spare
  omega

theorem pi_other_not_omitted (j k : Nat) (hj : j < 170) (hk : k < 170) (hne : k ≠ j) :
    ¬omitted (pi j (W k)) := by
  rw [pi_other j k hj hk hne]
  unfold omitted H
  omega

end ECDSAAdd.Arithmetic.CompressedAllocation
end

-- source: ECDSAAdd/Arithmetic/CompressedCompactZeroSlots.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run compressedEncodePrefix compressedHistoryEncode

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedAllocationBoundary.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedAllocation

end ECDSAAdd.Arithmetic.CompressedAllocation
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldActiveSupport.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open BalancedCircuit BalancedField
attribute [local irreducible] BalancedCircuit.coreProgram BalancedCircuit.program
  BalancedInverse.program OffsetBorrowedField.program OffsetBorrowedInverse.program
  OffsetBorrowedInverse.tail BalancedCleanupOffset.program BalancedCleanupOffset.chain
  BalancedCleanupOffsetSlim.program BalancedCleanupOffsetSlim.chain
  BalancedCleanupOffsetZero.program BalancedCleanupOffsetZero.core
  BalancedCleanupOffset.view BalancedCleanup.prepareSign BalancedCleanup.program
  wires

/-- Descriptor-only Minus/Plus roles are excluded from actual cleanup support.
In the shared caller they name history0/1; no cleanup instruction touches them. -/
def activeOffsetSites (L : BalancedCleanupOffset.Layout) : List Wire :=
  [L.sourceGuard,L.cout] ++ L.toCircuit.toLayout.wires ++ L.offsetCarry

theorem offset_support (L : BalancedCleanupOffset.Layout) (hw : L.Widths) :
    wires (BalancedCleanupOffset.program L) ⊆ (activeOffsetSites L).toFinset := by
  let W := (activeOffsetSites L).toFinset
  have member (q : Wire) : q∈W ↔
      q∈[L.sourceGuard,L.cout,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry ∨ q∈L.offsetCarry := by
    simp [W,activeOffsetSites,BalancedCleanup.Layout.wires,or_assoc]
  have data (q : Wire) (h : q∈L.y++L.r++L.carry++L.offsetCarry) : q∈W := by
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rw [member]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have own : L.toCircuit.toLayout.wires.toFinset⊆W := by
    intro q hq
    simp only [W,activeOffsetSites,List.mem_toFinset,List.mem_append] at ⊢
    exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
  have sgSub : wires (BalancedCleanup.prepareSign L.toCircuit.toLayout)⊆
      wires (BalancedCleanup.program L.toCircuit.toLayout) := by
    rw [BalancedCleanup.program,wires_append]
    exact Finset.subset_union_left
  have sg := sgSub.trans ((BalancedCleanup.support L.toCircuit.toLayout hw.1).trans own)
  have vw : wires (BalancedCleanupOffset.view L)⊆W := by
    intro q hq
    have h := BalancedCleanupOffset.view_support L hw hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
    rcases h with rfl|rfl|h|h
    · simp [member]
    · simp [member]
    · exact data q (by simp [h])
    · exact data q (by simp [h])
  have ch := OffsetBorrowedSupport.chainSupport (BalancedCleanupOffset.offsetBits L)
    L.y L.r L.offsetCarry L.carry L.one L.cout L.parity W
    (fun q hq => by rw [BalancedCleanupOffset.offsetSources L q hq]; simp [member])
    (fun q hq => data q (by simp [hq])) (fun q hq => data q (by simp [hq]))
    (fun q hq => data q (by simp [hq])) (fun q hq => data q (by simp [hq]))
    (by simp [member]) (by simp [member]) (by simp [member])
  have c : wires [.X L.cout]⊆W := by
    simp [wires,Instr.wires,Finset.subset_iff,member]
  simp only [BalancedCleanupOffset.program,wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨sg,vw⟩,c⟩,ch⟩,c⟩,vw⟩,sg⟩

private theorem head_member (r : List Wire) (h : 0 < r.length) : r.headD 0∈r := by
  cases r <;> simp_all

private theorem tail_member (r : List Wire) (q : Wire) (h : q∈r.tail) : q∈r := by
  cases r with
  | nil => simp at h
  | cons a r => exact List.mem_cons_of_mem a h

private theorem mapped_tail_subset (bits : List MappedBit) : mappedWires bits.tail⊆mappedWires bits := by
  cases bits with
  | nil => simp [mappedWires]
  | cons b bits =>
    intro q hq
    exact BalancedCleanupOffset.mapped_tail_member b bits q hq

/-- Zero-head cleanup uses only the same active roles as the old emitted
cleanup. Neither descriptor-only Minus nor Plus is admitted to the pool. -/
theorem zero_offset_support (L : BalancedCleanupOffset.Layout) (hw : L.Widths) :
    wires (BalancedCleanupOffsetZero.program L)⊆(activeOffsetSites L).toFinset := by
  let W := (activeOffsetSites L).toFinset
  have member (q : Wire) : q∈W ↔
      q∈[L.sourceGuard,L.cout,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry ∨ q∈L.offsetCarry := by
    simp [W,activeOffsetSites,BalancedCleanup.Layout.wires,or_assoc]
  have data (q : Wire) (h : q∈L.y++L.r++L.carry++L.offsetCarry) : q∈W := by
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rw [member]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have carry : L.carry.length=256 := hw.1.2.2
  have offset : L.offsetCarry.length=256 := hw.2
  have bitTail : (BalancedCleanupOffset.offsetBits L).tail.length=255 := by
    rw [List.length_tail,BalancedCleanupOffset.offsetBits_length]
  have rTail : L.r.tail.length=255 := by rw [List.length_tail,width.2.1]
  have yTail : L.y.tail.length=255 := by rw [List.length_tail,width.2.2.1]
  have cTail : L.carry.tail.length=255 := by rw [List.length_tail,carry]
  have oTail : L.offsetCarry.tail.length=255 := by rw [List.length_tail,offset]
  have aW : L.y.headD 0∈W := data _ (by
    have h := head_member L.y (by omega)
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
  have yW : L.r.headD 0∈W := data _ (by
    have h := head_member L.r (by omega)
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
  have dW : L.carry.headD 0∈W := data _ (by
    have h := head_member L.carry (by omega)
    exact List.mem_append_left _ (List.mem_append_right _ h))
  have oneW : L.one∈W := by simp [member]
  have coutW : L.cout∈W := by simp [member]
  have parityW : L.parity∈W := by simp [member]
  have pool := BalancedCleanupOffset.chain_pool_support (BalancedCleanupOffset.offsetBits L).tail
    L.y.tail L.r.tail L.offsetCarry.tail L.carry.tail L.one (L.carry.headD 0) L.parity W
    (fun q hq => by
      rw [BalancedCleanupOffset.offsetSources L q (mapped_tail_subset _ hq)]
      simp [member])
    (fun q hq => data q (by simp [tail_member L.y q hq]))
    (fun q hq => data q (by simp [tail_member L.r q hq]))
    (fun q hq => data q (by simp [tail_member L.offsetCarry q hq]))
    (fun q hq => data q (by simp [tail_member L.carry q hq])) oneW dW parityW
  have tail := (BalancedCleanupOffsetSlim.chain_support (BalancedCleanupOffset.offsetBits L).tail
    L.y.tail L.r.tail L.offsetCarry.tail L.carry.tail L.one (L.carry.headD 0) L.parity
    (by omega) (by omega) (by omega) (by omega)).trans pool
  have small : wires [.X (L.r.headD 0)]⊆W ∧
      wires (majority (L.y.headD 0) (L.r.headD 0) L.cout (L.carry.headD 0))⊆W ∧
      wires (eraseCarry (L.y.headD 0) (L.r.headD 0) L.cout (L.carry.headD 0))⊆W := by
    simp [majority,eraseCarry,wires,Instr.wires,correctionWires,Finset.subset_iff,coutW]
    have head_eq (xs : List Wire) : xs.head?.getD 0=xs.headD 0 := by
      cases xs <;> rfl
    simpa only [head_eq] using
      (show L.r.headD 0∈W ∧ (L.carry.headD 0∈W ∧ L.y.headD 0∈W ∧ L.r.headD 0∈W) ∧
        L.y.headD 0∈W ∧ L.r.headD 0∈W ∧ L.carry.headD 0∈W from
          ⟨yW,⟨dW,aW,yW⟩,aW,yW,dW⟩)
  have co : wires (BalancedCleanupOffsetZero.core L)⊆W := by
    simp only [BalancedCleanupOffsetZero.core,BalancedCleanupOffsetZeroHead.program,
      wires_append,Finset.union_subset_iff,and_assoc]
    exact ⟨small.1,small.2.1,tail,small.2.2,small.1⟩
  have old := offset_support L hw
  rw [BalancedCleanupOffset.program_sandwich] at old
  simp only [BalancedCleanupOffsetZero.program,wires_append,Finset.union_subset_iff] at old ⊢
  exact ⟨⟨old.1.1,co⟩,old.2⟩

def sharedSites (w : Nat → Wire) (sign : Wire) : List Wire :=
  [sign,w 765,w 1026] ++ (balancedSharedPorts w sign).wires ++
    OffsetCleanupBorrowedCaller.carry w

/-- Actual forward and inverse kernels avoid the raw history, despite the
unused descriptor roles in their auxiliary cleanup layout. -/
theorem kernels_support (w : Nat → Wire) (sign : Wire) :
    wires (OffsetBorrowedField.program w sign)⊆(sharedSites w sign).toFinset ∧
    wires (OffsetBorrowedInverse.program w sign)⊆(sharedSites w sign).toFinset := by
  let L := balancedSharedPorts w sign
  let W := (sharedSites w sign).toFinset
  have native : L.wires.toFinset⊆W := by
    intro q hq
    simp only [W,sharedSites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
  have coreSub : wires (BalancedCircuit.coreProgram L)⊆wires (BalancedCircuit.program L) := by
    intro q hq
    simp only [BalancedCircuit.program_eq_core,wires_append,Finset.mem_union]
    exact Or.inl (Or.inl hq)
  have tailSub : wires (OffsetBorrowedInverse.tail L)⊆wires (BalancedInverse.program L) := by
    have eq : BalancedInverse.program L=[.CX L.ymsb L.sourceGuard]++
        BalancedInverse.recoverParity L++OffsetBorrowedInverse.tail L := by
      simp only [BalancedInverse.program,OffsetBorrowedInverse.tail,List.append_assoc]
    intro q hq
    simp only [eq,wires_append,Finset.mem_union]
    exact Or.inr hq
  have active : (activeOffsetSites (OffsetCleanupBorrowedCaller.layout w sign)).toFinset⊆W := by
    intro q hq
    simp only [activeOffsetSites,OffsetCleanupBorrowedCaller.layout,
      List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with rfl|rfl|h|h
    · change w 765∈W
      simp [W,sharedSites]
    · simp [W,sharedSites]
    · apply native
      simp only [L,BalancedCircuit.Layout.wires,List.mem_toFinset,List.mem_append]
      exact Or.inr h
    · simp [W,sharedSites,h]
  have core := coreSub.trans ((balancedSharedPorts_support w sign).trans native)
  have tail := tailSub.trans ((BalancedInverse.support L (balancedSharedPorts_widths w sign)).trans native)
  have off := (zero_offset_support _ (OffsetCleanupBorrowedCaller.widths w sign)).trans active
  have forwardOff := (TerminalParityOffset.support_old _ (OffsetCleanupBorrowedCaller.widths w sign)).trans off
  have cx : wires [.CX L.ymsb L.sourceGuard]⊆W := by
    apply Finset.Subset.trans (s₂:=L.wires.toFinset) _ native
    simp [wires,Instr.wires,Finset.subset_iff,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires]
  simp only [OffsetBorrowedField.program,OffsetBorrowedInverse.program,
    OffsetBorrowedInverse.recoverParity,wires_append,Finset.union_subset_iff]
  exact ⟨⟨core,⟨forwardOff,cx⟩⟩,⟨⟨cx,off⟩,tail⟩⟩

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldGroupProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Decode only the current three raw letters, execute their actual field
cells, and encode the same group again before advancing. Final one/two
letters stay raw, matching the full512 delayed integer pack schedule. -/
def codecGroupForward {α : Type} (w : Nat → Wire) (cell : α → Program)
    (start : Nat) : List α → Program
  | a::b::c::tail => compressedHistoryDecode w start ++ cell a ++ cell b ++ cell c ++
      compressedHistoryEncode w start ++ codecGroupForward w cell (start+3) tail
  | [a,b] => cell a ++ cell b
  | [a] => cell a
  | [] => []

/-- Reverse field replay visits groups and cells in reverse, while retaining
the same independent decoder and measured encoder at each group boundary. -/
def codecGroupBackward {α : Type} (w : Nat → Wire) (cell : α → Program)
    (start : Nat) : List α → Program
  | a::b::c::tail => codecGroupBackward w cell (start+3) tail ++
      compressedHistoryDecode w start ++ cell c ++ cell b ++ cell a ++
      compressedHistoryEncode w start
  | [a,b] => cell b ++ cell a
  | [a] => cell a
  | [] => []

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldCellSupport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open BalancedCircuit DirectSkywalk
attribute [local irreducible] wires OffsetBorrowedCanonical.body OffsetBorrowedInverseCanonical.body

theorem bodies_active (w : Nat → Wire) (sign eff : Wire) (W : Finset Wire)
    (hk : (sharedSites w sign).toFinset ⊆ W) (he : eff ∈ W) :
    wires (OffsetBorrowedCanonical.body w sign eff) ⊆ W ∧
    wires (OffsetBorrowedInverseCanonical.body w sign eff) ⊆ W := by
  let L := balancedSharedPorts w sign
  have native : L.wires.toFinset ⊆ W := by
    intro q hq
    apply hk
    simp only [sharedSites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
  have signIn : sign ∈ W := hk (by simp [sharedSites])
  have xx : wires [.X sign] ⊆ W := by simp [wires,Instr.wires,Finset.subset_iff,signIn]
  have field := kernels_support w sign
  have fw := field.1.trans hk
  have rv := field.2.trans hk
  have width := BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)
  have sw0 := swapRegisters_wires eff L.r L.y (width.2.1.trans width.2.2.1.symm)
  have sw : wires (swapRegisters eff L.r L.y) ⊆ W := by
    intro q hq
    have h := sw0 hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    rcases h with rfl|h|h
    · exact he
    all_goals
      apply native
      simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
        BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
        List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  simp only [OffsetBorrowedCanonical.body,OffsetBorrowedInverseCanonical.body,
    OffsetBorrowedInverseCanonical.double,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨xx,fw,xx,sw,sw,xx,rv,xx⟩

/-- Only the two current raw controls are added to the nonhistory kernel
support. Descriptor-only history0/1 never enters this actual support. -/
theorem cells_active (w : Nat → Wire) (b g swap sign eff : Wire) (ig is : Bool)
    (W : Finset Wire) (hk : (sharedSites w sign).toFinset ⊆ W)
    (hb : b ∈ W) (hg : g ∈ W) (hs : swap ∈ W) (he : eff ∈ W) :
    wires (OffsetBorrowedCanonical.cell w b g swap sign eff ig is) ⊆ W ∧
    wires (OffsetBorrowedInverseCanonical.cell w b g swap sign eff ig is) ⊆ W := by
  have body := bodies_active w sign eff W hk he
  have sg : sign ∈ W := hk (by simp [sharedSites])
  constructor
  · exact DirectSupport.selectWindow b g sign ig _ W hb hg sg
      (DirectSupport.selectWindow b swap eff is _ W hb hs he body.1)
  · exact DirectSupport.selectWindow b g sign ig _ W hb hg sg
      (DirectSupport.selectWindow b swap eff is _ W hb hs he body.2)

/-- Every history wire is excluded by the actual shared kernel support,
using only descriptor expansion and injectivity of the declared shared map. -/
theorem history_active_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign ∉ skywalkPoolWires w)
    (start : Nat) (hs : start+3 ≤ 512) (j : Fin 6) :
    w (compressedHistoryId start j) ∉ sharedSites w sign := by
  let idx := compressedHistoryId start j
  have bound : idx < 1798 := compressedHistoryId_bound start hs j
  have region := compressedHistoryId_region start hs j
  have signNe : w idx ≠ sign := by
    intro e
    apply ho
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨idx,by omega,e⟩
  have noBlock (a n : Nat) (hbn : a+n ≤ 2314)
      (away : idx < a ∨ a+n ≤ idx) : w idx ∉ wireBlock w a n :=
    arith_block_away w hn idx a n (by omega) hbn away
  have nr := noBlock 2057 254 (by omega) (by dsimp [idx] at *; omega)
  have ny := noBlock 770 255 (by omega) (by dsimp [idx] at *; omega)
  have nc := noBlock 1540 256 (by omega) (by dsimp [idx] at *; omega)
  have nb := noBlock 512 253 (by omega) (by dsimp [idx] at *; omega)
  have flags : w idx ∉ ([765,1026,768,767,766,1796,1797,1027,2311,1025,2056].map w) := by
    intro h
    obtain ⟨k,hk,he⟩ := List.mem_map.mp h
    have kb : k < 2314 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
    have eq := skywalkShared_index_inj w hn k idx kb (by omega) he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    dsimp [idx] at *
    omega
  simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,not_or,
    not_false_eq_true,and_true] at flags
  simp only [sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  tauto

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedAllocationSupport.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedAllocation

def fieldSite (q : Nat) : Prop :=
  (512 ≤ q ∧ q ≤ 769) ∨ (770 ≤ q ∧ q ≤ 1027) ∨
  (1540 ≤ q ∧ q ≤ 1797) ∨ (2056 ≤ q ∧ q ≤ 2312) ∨
  q=0 ∨ q=1 ∨ q=2400 ∨ q=2409 ∨ q=2410

def packetSites (j : Nat) : List Nat :=
  [3*j,1028+3*j,3*j+1,H j,3*j+2,1030+3*j]

def groupInventory (j : Nat) : List Nat :=
  CompressedFieldSupport.sharedSites id 2409 ++ [2400,2410] ++ packetSites j

theorem nonhole_pi_safe (j q : Nat) (hj : j < 170) (hq : ¬holeRegion q) :
    ¬omitted (pi j q) := by
  by_cases hw : workRegion q
  · have hk : q-515 < 170 := by unfold workRegion at hw; omega
    have eq : q=W (q-515) := by unfold workRegion at hw; unfold W; omega
    by_cases same : q-515=j
    · rw [eq,same]
      exact pi_selected_not_omitted j hj
    · rw [eq]
      exact pi_other_not_omitted j _ hj hk same
  · have hz : ¬zeroRegion q := fun h => h.elim hw hq
    rw [pi_outside j q hj hz]
    unfold omitted workRegion at *
    omega

theorem nonhole_pi0_safe (q : Nat) (hq : ¬holeRegion q) : ¬omitted (pi0 q) := by
  by_cases hw : workRegion q
  · have hk : q-515 < 170 := by unfold workRegion at hw; omega
    have eq : q=W (q-515) := by unfold workRegion at hw; unfold W; omega
    rw [eq,pi0_W _ hk]
    unfold omitted H
    omega
  · have hz : ¬zeroRegion q := fun h => h.elim hw hq
    rw [pi0_outside q hz]
    unfold omitted workRegion at *
    omega

theorem field_not_hole (q : Nat) (h : fieldSite q) : ¬holeRegion q := by
  unfold fieldSite holeRegion at *
  omega

theorem field_safe (j q : Nat) (hj : j < 170) (h : fieldSite q) : ¬omitted (pi j q) :=
  nonhole_pi_safe j q hj (field_not_hole q h)

theorem field_pi0_safe (q : Nat) (h : fieldSite q) : ¬omitted (pi0 q) :=
  nonhole_pi0_safe q (field_not_hole q h)

theorem packet_fixed (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : pi j q=q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega
  · exact pi_current j hj
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega
  · apply pi_outside j _ hj; unfold zeroRegion workRegion holeRegion; omega

theorem packet_safe (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : ¬omitted (pi j q) := by
  rw [packet_fixed j q hj h]
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold omitted
  unfold H at h
  omega

private theorem shared_field_site (q : Nat)
    (h : q∈CompressedFieldSupport.sharedSites id 2409) : fieldSite q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,
    BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,List.mem_append,
    List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold fieldSite
  omega

theorem inventory_safe (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) :
    ¬omitted (pi j q) := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact field_safe j q hj (shared_field_site q h)
  · have hs : q=2400 ∨ q=2410 := by simpa using h
    apply field_safe j q hj
    unfold fieldSite
    omega
  · exact packet_safe j q hj h

end ECDSAAdd.Arithmetic.CompressedAllocation
end

-- source: ECDSAAdd/Arithmetic/CompressedAllocationSwitch.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.CompressedAllocation

end ECDSAAdd.Arithmetic.CompressedAllocation
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkForward.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] run compressedEncodePrefix
attribute [local irreducible] narrowSkywalkScheduledTick compressedHistoryEncode

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkRestore.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] run compressedDecodePrefix compressedEncodePrefix
attribute [local irreducible] narrowSkywalkRoutedUnloop

theorem run_no_measurement_phase (p : Program) (hm : measurementCount p=0)
    (s : State) (m : List Bool) : (run p m s).phase=s.phase := by
  induction p generalizing s m with
  | nil => simp only [run]
  | cons i p ih =>
    cases i with
    | X q =>
      simp only [run]
      exact ih hm ⟨s.phase,writeBit s.basis q (!s.basis q)⟩ m
    | CX a q =>
      simp only [run]
      exact ih hm ⟨s.phase,writeBit s.basis q (s.basis q ^^ s.basis a)⟩ m
    | CCX a b q =>
      simp only [run]
      exact ih hm ⟨s.phase,writeBit s.basis q (s.basis q ^^ (s.basis a && s.basis b))⟩ m
    | measureX q c0 c1 =>
      simp only [measurementCount] at hm
      omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedCompactDecode.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run compressedDecodePrefix compressedEncodePrefix
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

/-- Every compressed priorEncoded has a separately emitted coherent inverse.
The input domain comes from the actual exact integer-history assertion. -/
theorem compressedCompactDecodePrefix_inverse (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p n i : Nat) (hp0 : 0 < p) (hpo : p%2 = 1) (hni : n ≤ i) (hi : i ≤ 512)
    (s : State) (mE mD : List Bool)
    (h : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (compressedDecodePrefix w n) mD (run (compressedEncodePrefix w n) mE s)=s := by
  induction n generalizing mE mD with
  | zero => simp [compressedEncodePrefix,compressedDecodePrefix,run]
  | succ n ih =>
    have hbound : n < 512 := by omega
    let priorEncoded := run (compressedEncodePrefix w n)
      (mE.take (measurementCount (compressedEncodePrefix w n))) s
    have clean : run (compressedDecodeBefore w n) []
        (run (compressedPackAfter w n) (mE.drop (measurementCount (compressedEncodePrefix w n))) priorEncoded)=priorEncoded := by
      cases he : compressedPackDue n
      · simp only [compressedDecodeBefore,compressedPackAfter,he,Bool.false_eq_true,if_false,run]
      · have hn3 := compressedPackDue_true n he
        have same (j : Fin 6) : priorEncoded.basis (compressedHistoryMap w (n-3) j)=
            s.basis (compressedHistoryMap w (n-3) j) := by
          exact compressedPrefix_raw_next w hn hlo n hbound he s _ j
        have rawLegal := compressedCompactHistory_legal w hn x p i (n-3) hp0 hpo (by omega) hi s.basis h
        have legal :
            (priorEncoded.basis (compressedHistoryMap w (n-3) 0) && priorEncoded.basis (compressedHistoryMap w (n-3) 1))=false ∧
            (priorEncoded.basis (compressedHistoryMap w (n-3) 2) && priorEncoded.basis (compressedHistoryMap w (n-3) 3))=false ∧
            (priorEncoded.basis (compressedHistoryMap w (n-3) 4) && priorEncoded.basis (compressedHistoryMap w (n-3) 5))=false := by
          rw [same 0,same 1,same 2,same 3,same 4,same 5]
          exact rawLegal
        have hc := TranscriptCodec3.decode_encode (compressedHistoryMap w (n-3))
          (compressedHistoryMap_injective w hn (n-3) (by omega))
          (compressedHistoryMap_above w (n-3) (by omega) hlo) priorEncoded
          (mE.drop (measurementCount (compressedEncodePrefix w n))) [] legal
        simpa only [compressedDecodeBefore,compressedPackAfter,he,if_true,
          compressedHistoryEncode,compressedHistoryDecode] using hc
    rw [compressedEncodePrefix,compressedDecodePrefix,run_append,run_append]
    have hd0 := (compressedPackAfter_counts w n).2.2.2
    rw [hd0]
    simp only [List.take_zero,List.drop_zero]
    rw [clean]
    exact ih (by omega) _ _

/-- The actual coherent decoder recovers the compact raw state, including
caller outsiders, and preserves the current input phase independently of records. -/
theorem compressedCompactStage_decoded (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p n : Nat) (hp0 : 0 < p) (hpo : p%2 = 1) (hn512 : n ≤ 512)
    (s : State) (h : CompressedCompactStage w x p n s.basis) :
    (run (compressedDecodePrefix w n) [] s).phase = s.phase ∧
    CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) n
      (run (compressedDecodePrefix w n) [] s).basis := by
  obtain ⟨raw,hraw,hbasis⟩ := h
  have inverse := compressedCompactDecodePrefix_inverse w hn hlo x p n n hp0 hpo
    (Nat.le_refl n) hn512 raw [] [] hraw
  have records := run_basis_records (compressedDecodePrefix w n) s
    (run (compressedEncodePrefix w n) [] raw) [] [] hbasis
  have bits : (run (compressedDecodePrefix w n) [] s).basis = raw.basis :=
    records.trans (congrArg State.basis inverse)
  refine ⟨run_no_measurement_phase _ (compressedDecodePrefix_measurements w n) s [],?_⟩
  rw [bits]
  exact hraw

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedCompactMaskZeros.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] compressedHistoryEncode compressedEncodePrefix run

private theorem block_mem (w : Nat → Wire) (a n i : Nat)
    (ha : a ≤ i) (hi : i < a+n) : w i∈wireBlock w a n := by
  simp only [wireBlock,List.mem_map,List.mem_range'_1]
  exact ⟨i,⟨ha,hi⟩,rfl⟩

theorem compressedPrefix_history_support (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n : Nat) (hn512 : n ≤ 512) :
    wires (compressedEncodePrefix w n)⊆
      (wireBlock w 0 512++wireBlock w 1028 512).toFinset := by
  induction n with
  | zero => simp [compressedEncodePrefix,wires]
  | succ n ih =>
    have old := ih (by omega)
    have now : wires (compressedPackAfter w n)⊆
        (wireBlock w 0 512++wireBlock w 1028 512).toFinset := by
      intro q hq
      cases due : compressedPackDue n
      · simp [compressedPackAfter,due,wires] at hq
      · have hd := compressedPackDue_true n due
        have qenc : q∈wires (compressedHistoryEncode w (n-3)) := by
          simpa only [compressedPackAfter,due,if_true] using hq
        obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo (n-3) (by omega)
          _ (Or.inl rfl) q qenc
        have region := compressedHistoryId_region (n-3) (by omega) j
        apply List.mem_toFinset.mpr
        rcases region with h|h
        · apply List.mem_append_left
          exact block_mem w 0 512 _ (by omega) h
        · apply List.mem_append_right
          exact block_mem w 1028 512 _ h.1 h.2
    simpa only [compressedEncodePrefix,wires_append,Finset.union_subset_iff] using
      And.intro old now

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedCompactRestore.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run compactSkywalkForward compactSkywalkReverse compressedCompactReverse

private theorem decode_support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (i : Nat) (hi : i < 512) :
    wires (compressedDecodeBefore w i) ⊆ (skywalkPoolWires w).toFinset := by
  intro q hq
  cases due : compressedPackDue i
  · simp [compressedDecodeBefore,due,wires] at hq
  · have h3 := compressedPackDue_true i due
    have hq' : q ∈ wires (compressedHistoryDecode w (i-3)) := by
      simpa only [compressedDecodeBefore,due,if_true] using hq
    obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo (i-3) (by omega) _ (Or.inr rfl) q hq'
    have bound := compressedHistoryId_bound (i-3) (by omega) j
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨compressedHistoryId (i-3) j,by omega,rfl⟩

theorem compressedCompactReverse_support (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    wires (compressedCompactReverse w i n) ⊆ (skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [compressedCompactReverse,wires]
  | succ n ih =>
    have tick : wires (compactSkywalkReverseTick w i) ⊆ (skywalkPoolWires w).toFinset := by
      intro q hq
      exact List.mem_toFinset.mpr (compactSkywalkTick_local_support w i (by omega)
        (List.mem_toFinset.mp (compactSkywalkReverseTick_support w i (by omega) hn hq)))
    simp only [compressedCompactReverse,wires_append,Finset.union_subset_iff]
    exact ⟨⟨ih (i+1) (by omega),decode_support w hn hlo i (by omega)⟩,tick⟩

theorem compressedCompactReverse_frame (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hsteps : i+n ≤ 512) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ skywalkPoolWires w) :
    (run (compressedCompactReverse w i n) m s).basis q = s.basis q := by
  apply run_preserves_outside
  intro h
  exact hq (List.mem_toFinset.mp (compressedCompactReverse_support w hn hlo i n hsteps h))

/-- Actual reverse component prices; no whole-point allocation claim. -/
theorem compressedCompactReverse_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    toffoliCount (compressedCompactReverse w i n) = compactSkywalkForwardT i n+4*compressedPackCount i n ∧
    measurementCount (compressedCompactReverse w i n) = compactSkywalkForwardM i n := by
  have relative := compressedCompactReverse_counts_relative w i n
  have compact := compactSkywalkReverse_counts w hn i n hsteps
  rw [compact.1,compact.2] at relative
  exact relative

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldWindowTransport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
attribute [local irreducible] run wires compressedHistoryEncode compressedHistoryDecode

/-- A current three-cell group reads only its own six raw controls, plus
nonhistory data/work and external activation/selection controls. -/
def groupReadSites (w : Nat → Wire) (b sign eff : Wire) (start : Nat) : Finset Wire :=
  (sharedSites w sign).toFinset ∪ {b,eff} ∪ wires (compressedHistoryEncode w start)

theorem current_cells_support (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (g swap : Wire) (ig is : Bool)
    (hg : g ∈ wires (compressedHistoryEncode w start))
    (hs : swap ∈ wires (compressedHistoryEncode w start)) :
    wires (OffsetBorrowedCanonical.cell w b g swap sign eff ig is) ⊆ groupReadSites w b sign eff start ∧
    wires (OffsetBorrowedInverseCanonical.cell w b g swap sign eff ig is) ⊆ groupReadSites w b sign eff start := by
  apply cells_active
  · intro q hq
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hq)
  · simp [groupReadSites]
  · exact Finset.mem_union_right _ hg
  · exact Finset.mem_union_right _ hs
  · simp [groupReadSites]

/-- Every other history encoder is disjoint from a current field group.
The actual strong support excludes descriptor-only history0/1. -/
theorem other_encoder_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hb : b ∉ skywalkPoolWires w) (hsign : sign ∉ skywalkPoolWires w)
    (heff : eff ∉ skywalkPoolWires w) (a start : Nat)
    (ha : a+3 ≤ 512) (hst : start+3 ≤ 512) (sep : a+3 ≤ start ∨ start+3 ≤ a)
    (body : Program) (support : wires body ⊆ groupReadSites w b sign eff start) :
    Disjoint (wires (compressedHistoryEncode w a)) (wires body) := by
  have pool := skywalkShared_integer_nodup w hn
  have groups : Disjoint (wires (compressedHistoryEncode w a)) (wires (compressedHistoryEncode w start)) := by
    rcases sep with h|h
    · exact compressedHistory_windows_disjoint w pool hlo a start ha hst h
    · exact (compressedHistory_windows_disjoint w pool hlo start a hst ha h).symm
  apply Finset.disjoint_left.mpr
  intro q hq ht
  obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w pool hlo a ha _ (Or.inl rfl) q hq
  have bound := compressedHistoryId_bound a ha j
  have own : w (compressedHistoryId a j) ∈ skywalkPoolWires w := by
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨compressedHistoryId a j,by omega,rfl⟩
  have away := history_active_away w sign hn hsign a ha j
  have read := support ht
  simp only [groupReadSites,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at read
  rcases read with (read|read)|read
  · exact away (List.mem_toFinset.mp read)
  · rcases read with eq|eq
    · exact hb (eq ▸ own)
    · exact heff (eq ▸ own)
  · exact Finset.disjoint_left.mp groups hq read

/-- Exact current-window transport with independently supplied records.
Other groups may already be encoded: their actual program is commuted,
never interpreted using a false raw-history PairFrame premise. -/
theorem window_transport_other (w : Nat → Wire) (start : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hs : start+3 ≤ 512) (other body : Program)
    (he : Disjoint (wires other) (wires (compressedHistoryEncode w start)))
    (hb : Disjoint (wires other) (wires body))
    (s : State) (mOther m0 m1 m2 m3 : List Bool)
    (legal : (s.basis (compressedHistoryMap w start 0) && s.basis (compressedHistoryMap w start 1)) = false ∧
      (s.basis (compressedHistoryMap w start 2) && s.basis (compressedHistoryMap w start 3)) = false ∧
      (s.basis (compressedHistoryMap w start 4) && s.basis (compressedHistoryMap w start 5)) = false) :
    run (compressedHistoryEncode w start) m3
      (run body m2 (run (compressedHistoryDecode w start) m1
        (run other mOther (run (compressedHistoryEncode w start) m0 s)))) =
      run other mOther (run (compressedHistoryEncode w start) m3 (run body m2 s)) := by
  have same (j : Fin 6) : (run other mOther s).basis (compressedHistoryMap w start j) =
      s.basis (compressedHistoryMap w start j) := by
    apply run_preserves_outside
    intro h
    exact Finset.disjoint_left.mp he h (compressedHistory_site_mem w hn hlo start hs j)
  have legalOther :
      ((run other mOther s).basis (compressedHistoryMap w start 0) &&
        (run other mOther s).basis (compressedHistoryMap w start 1)) = false ∧
      ((run other mOther s).basis (compressedHistoryMap w start 2) &&
        (run other mOther s).basis (compressedHistoryMap w start 3)) = false ∧
      ((run other mOther s).basis (compressedHistoryMap w start 4) &&
        (run other mOther s).basis (compressedHistoryMap w start 5)) = false := by
    rw [same 0,same 1,same 2,same 3,same 4,same 5]
    exact legal
  rw [run_disjoint_commute other (compressedHistoryEncode w start) he mOther m0 s]
  have window := TranscriptCodec3.window_states (compressedHistoryMap w start)
    (compressedHistoryMap_injective w hn start hs) (compressedHistoryMap_above w start hs hlo)
    body (run other mOther s) m0 m1 m2 m3 legalOther
  have window' : run (compressedHistoryEncode w start) m3
      (run body m2 (run (compressedHistoryDecode w start) m1
        (run (compressedHistoryEncode w start) m0 (run other mOther s)))) =
      run (compressedHistoryEncode w start) m3 (run body m2 (run other mOther s)) := by
    simpa only [compressedHistoryEncode,compressedHistoryDecode] using window
  rw [window']
  rw [←run_disjoint_commute other body hb mOther m2 s]
  exact (run_disjoint_commute other (compressedHistoryEncode w start) he mOther m3 (run body m2 s)).symm

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldGroupPacket.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell

def rawForwardPacket (w : Nat → Wire) (b sign eff : Wire) (a c d : MixedTranscriptLetter) : Program :=
  OffsetBorrowedCanonical.replay w b sign eff [a,c,d]
def rawBackwardPacket (w : Nat → Wire) (b sign eff : Wire) (a c d : MixedTranscriptLetter) : Program :=
  OffsetBorrowedInverseCanonical.replay w b sign eff [a,c,d]

private theorem forward_layout (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (a c d : MixedTranscriptLetter) :
    codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) start [a,c,d] =
    compressedHistoryDecode w start++rawForwardPacket w b sign eff a c d++compressedHistoryEncode w start := by
  simp only [codecGroupForward,rawForwardPacket,OffsetBorrowedCanonical.replay,List.append_nil,List.append_assoc]

private theorem backward_layout (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (a c d : MixedTranscriptLetter) :
    codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) start [a,c,d] =
    compressedHistoryDecode w start++rawBackwardPacket w b sign eff a c d++compressedHistoryEncode w start := by
  simp only [codecGroupBackward,rawBackwardPacket,OffsetBorrowedInverseCanonical.replay,
    List.nil_append,List.append_assoc]

/-- Exact emitted decode/body/re-encode evaluation. Decoder consumes no
record, and each actual body and encoder receives its own record suffix. -/
private theorem window_run (w : Nat → Wire) (start : Nat) (body : Program) (s : State) (m : List Bool) :
    run (compressedHistoryDecode w start++body++compressedHistoryEncode w start) m s =
      run (compressedHistoryEncode w start) (m.drop (measurementCount body))
        (run body m (run (compressedHistoryDecode w start) [] s)) := by
  have zero := (compressedHistory_counts w start).2.2.2
  simp only [List.append_assoc]
  rw [run_append,zero,List.take_zero,List.drop_zero,run_append,run_take]

/-- Actual forward three-cell semantic packet under other encoded history.
The result carries complete State encoding and the old full field frame;
no raw PairFrame is assumed for the physical other-encoded input. -/
theorem forward_packet (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (a c d : MixedTranscriptLetter) (hn : (skywalkSharedWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (hs : start+3 ≤ 512)
    (hf : MixedTranscriptReplayLayout w b sign eff [a,c,d])
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (X Y : Fp) (s : State)
    (input : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis)
    (legal : (s.basis (compressedHistoryMap w start 0) && s.basis (compressedHistoryMap w start 1)) = false ∧
      (s.basis (compressedHistoryMap w start 2) && s.basis (compressedHistoryMap w start 3)) = false ∧
      (s.basis (compressedHistoryMap w start 4) && s.basis (compressedHistoryMap w start 5)) = false)
    (other : Program)
    (hE : Disjoint (wires other) (wires (compressedHistoryEncode w start)))
    (hB : Disjoint (wires other) (wires (rawForwardPacket w b sign eff a c d)))
    (mOther mInit m : List Bool) :
    ∃ rawOut : State,
      run (codecGroupForward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) start [a,c,d]) m
        (run other mOther (run (compressedHistoryEncode w start) mInit s)) =
      run other mOther (run (compressedHistoryEncode w start)
        (m.drop (measurementCount (rawForwardPacket w b sign eff a c d))) rawOut) ∧
      rawOut.phase = s.phase ∧
      PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)).1)
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)).2) rawOut.basis := by
  let body := rawForwardPacket w b sign eff a c d
  let rawOut := run body m s
  have raw := OffsetBorrowedCanonical.replay_frame w b sign eff hn [a,c,d] hf ho base hg0 he0 env X Y s m input
  have transport := window_transport_other w start (skywalkShared_integer_nodup w hn) hlo hs
    other body hE hB s mOther mInit [] m (m.drop (measurementCount body)) legal
  refine ⟨rawOut,?_,raw.1,raw.2⟩
  rw [forward_layout,window_run]
  exact transport

/-- Independently measured inverse packet executes the three inverse cells
in reverse order, retaining the same complete encoded State relation. -/
theorem backward_packet (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (a c d : MixedTranscriptLetter) (hn : (skywalkSharedWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (hs : start+3 ≤ 512)
    (hf : MixedTranscriptReplayLayout w b sign eff [a,c,d])
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (X Y : Fp) (s : State)
    (input : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis)
    (legal : (s.basis (compressedHistoryMap w start 0) && s.basis (compressedHistoryMap w start 1)) = false ∧
      (s.basis (compressedHistoryMap w start 2) && s.basis (compressedHistoryMap w start 3)) = false ∧
      (s.basis (compressedHistoryMap w start 4) && s.basis (compressedHistoryMap w start 5)) = false)
    (other : Program)
    (hE : Disjoint (wires other) (wires (compressedHistoryEncode w start)))
    (hB : Disjoint (wires other) (wires (rawBackwardPacket w b sign eff a c d)))
    (mOther mInit m : List Bool) :
    ∃ rawOut : State,
      run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) start [a,c,d]) m
        (run other mOther (run (compressedHistoryEncode w start) mInit s)) =
      run other mOther (run (compressedHistoryEncode w start)
        (m.drop (measurementCount (rawBackwardPacket w b sign eff a c d))) rawOut) ∧
      rawOut.phase = s.phase ∧
      PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadReplayInverse (mixedTranscriptControls base b [a,c,d]) (X,Y)).1)
        (centerWord (skywalkPayloadReplayInverse (mixedTranscriptControls base b [a,c,d]) (X,Y)).2) rawOut.basis := by
  let body := rawBackwardPacket w b sign eff a c d
  let rawOut := run body m s
  have raw := OffsetBorrowedInverseCanonical.replay_frame w b sign eff hn [a,c,d] hf ho base hg0 he0 env X Y s m input
  have transport := window_transport_other w start (skywalkShared_integer_nodup w hn) hlo hs
    other body hE hB s mOther mInit [] m (m.drop (measurementCount body)) legal
  refine ⟨rawOut,?_,raw.1,raw.2⟩
  rw [backward_layout,window_run]
  exact transport

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldFullEncoding.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run compressedHistoryEncode

def allGroupEncode (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => allGroupEncode w n++compressedHistoryEncode w (3*n)

/-- All legal raw groups, without any sampled or approximate tape domain. -/
def RawGroupLegal (w : Nat → Wire) (n : Nat) (s : BasisState) : Prop :=
  ∀ j,j < n →
    (s (compressedHistoryMap w (3*j) 0) && s (compressedHistoryMap w (3*j) 1)) = false ∧
    (s (compressedHistoryMap w (3*j) 2) && s (compressedHistoryMap w (3*j) 3)) = false ∧
    (s (compressedHistoryMap w (3*j) 4) && s (compressedHistoryMap w (3*j) 5)) = false

/-- This is the physical invariant: raw field frame under the fixed full
170-group encoding. It never asserts a raw frame on an encoded history. -/
def EncodedFieldFrame (w : Nat → Wire) (sign : Wire) (base : BasisState)
    (X Y : Fp) (s : State) : Prop :=
  ∃ raw : State,
    raw.phase = s.phase ∧
    PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) raw.basis ∧
    s = run (allGroupEncode w 170) [] raw

private theorem due1 (n : Nat) : compressedPackDue (3*n+1) = false := by
  simp [compressedPackDue,Nat.add_mod]
private theorem due2 (n : Nat) : compressedPackDue (3*n+2) = false := by
  simp [compressedPackDue,Nat.add_mod]
private theorem due3 (n : Nat) : compressedPackDue (3*n+3) = true := by
  simp [compressedPackDue]

/-- The fixed full encoding is exactly the existing delayed integer prefix. -/
theorem encode_prefix_index (w : Nat → Wire) (n : Nat) :
    compressedEncodePrefix w (3*n+1) = allGroupEncode w n := by
  induction n with
  | zero => simp [compressedEncodePrefix,compressedPackAfter,compressedPackDue,allGroupEncode]
  | succ n ih =>
    have index : 3*(n+1)+1 = ((3*n+1)+1)+1+1 := by omega
    rw [index,compressedEncodePrefix,compressedEncodePrefix,compressedEncodePrefix,ih]
    have d1 := due1 n
    have d2 := due2 n
    have d3 := due3 n
    have h2 : 3*n+1+1 = 3*n+2 := by omega
    have h3 : 3*n+1+1+1 = 3*n+3 := by omega
    rw [h2,h3]
    simp only [compressedPackAfter,d1,d2,d3,Bool.false_eq_true,if_false,if_true,List.append_nil]
    rw [show 3*n+3-3 = 3*n by omega]
    rfl

theorem encode_prefix_512 (w : Nat → Wire) :
    compressedEncodePrefix w 512 = allGroupEncode w 170 := by
  rw [show (512:Nat) = 511+1 from rfl,compressedEncodePrefix]
  rw [show (511:Nat) = 3*170+1 from rfl,encode_prefix_index]
  simp [compressedPackAfter,compressedPackDue]

theorem allGroupEncode_disjoint (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n j : Nat) (bound : 3*n ≤ 512) (outside : n ≤ j) (jb : 3*j+3 ≤ 512) :
    Disjoint (wires (allGroupEncode w n)) (wires (compressedHistoryEncode w (3*j))) := by
  induction n with
  | zero => simp [allGroupEncode,wires]
  | succ n ih =>
    have old := ih (by omega) (by omega)
    have now := compressedHistory_windows_disjoint w hn hlo (3*n) (3*j) (by omega) jb (by omega)
    simp only [allGroupEncode,wires_append,Finset.disjoint_union_left]
    exact ⟨old,now⟩

/-- Every encoder keeps its record-independent complete State on this
legal domain, including phase; all other groups are disjoint actual programs. -/
theorem allGroupEncode_phase (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n : Nat) (bound : 3*n ≤ 512) (s : State) (m : List Bool)
    (legal : RawGroupLegal w n s.basis) :
    (run (allGroupEncode w n) m s).phase = s.phase := by
  induction n generalizing m with
  | zero => simp only [allGroupEncode,run]
  | succ n ih =>
    let before := run (allGroupEncode w n) (m.take (measurementCount (allGroupEncode w n))) s
    have first := ih (by omega)
      (m.take (measurementCount (allGroupEncode w n))) (fun j hj => legal j (by omega))
    have dis := allGroupEncode_disjoint w hn hlo n n (by omega) (Nat.le_refl _) (by omega)
    have same (j : Fin 6) : before.basis (compressedHistoryMap w (3*n) j) =
        s.basis (compressedHistoryMap w (3*n) j) := by
      apply run_preserves_outside
      intro h
      exact Finset.disjoint_left.mp dis h (compressedHistory_site_mem w hn hlo (3*n) (by omega) j)
    have dom := legal n (by omega)
    have domBefore :
        (before.basis (compressedHistoryMap w (3*n) 0) && before.basis (compressedHistoryMap w (3*n) 1)) = false ∧
        (before.basis (compressedHistoryMap w (3*n) 2) && before.basis (compressedHistoryMap w (3*n) 3)) = false ∧
        (before.basis (compressedHistoryMap w (3*n) 4) && before.basis (compressedHistoryMap w (3*n) 5)) = false := by
      rw [same 0,same 1,same 2,same 3,same 4,same 5]
      exact dom
    have codec := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*n))
      (compressedHistoryMap_injective w hn (3*n) (by omega))
      (compressedHistoryMap_above w (3*n) (by omega) hlo) before
      (m.drop (measurementCount (allGroupEncode w n))) domBefore
    rw [allGroupEncode,run_append]
    simpa only [compressedHistoryEncode,before] using codec.1.trans first

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldEncodingFactor.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
attribute [local irreducible] run compressedHistoryEncode

def otherGroupEncode (w : Nat → Wire) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if n=j then otherGroupEncode w j n else
      otherGroupEncode w j n++compressedHistoryEncode w (3*n)

theorem otherGroupEncode_outside (w : Nat → Wire) (n j : Nat) (h : n ≤ j) :
    otherGroupEncode w j n = allGroupEncode w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [otherGroupEncode,if_neg (by omega),ih (by omega),allGroupEncode]

theorem otherGroupEncode_member (w : Nat → Wire) (n j : Nat) (q : Wire)
    (h : q ∈ wires (otherGroupEncode w j n)) :
    ∃ k,k < n ∧ k ≠ j ∧ q ∈ wires (compressedHistoryEncode w (3*k)) := by
  induction n with
  | zero => simp [otherGroupEncode,wires] at h
  | succ n ih =>
    by_cases same : n=j
    · simp only [otherGroupEncode,if_pos same] at h
      obtain ⟨k,hk,hj,member⟩ := ih h
      exact ⟨k,by omega,hj,member⟩
    · simp only [otherGroupEncode,if_neg same,wires_append,Finset.mem_union] at h
      rcases h with h|h
      · obtain ⟨k,hk,hj,member⟩ := ih h
        exact ⟨k,by omega,hj,member⟩
      · exact ⟨n,by omega,same,h⟩

theorem otherGroupEncode_disjoint (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n j : Nat) (bound : 3*n ≤ 512) (hj : j < n) :
    Disjoint (wires (otherGroupEncode w j n)) (wires (compressedHistoryEncode w (3*j))) := by
  apply Finset.disjoint_left.mpr
  intro q hq hc
  obtain ⟨k,hk,ne,member⟩ := otherGroupEncode_member w n j q hq
  have sep : 3*k+3 ≤ 3*j ∨ 3*j+3 ≤ 3*k := by omega
  have dis : Disjoint (wires (compressedHistoryEncode w (3*k)))
      (wires (compressedHistoryEncode w (3*j))) := by
    rcases sep with h|h
    · exact compressedHistory_windows_disjoint w hn hlo _ _ (by omega) (by omega) h
    · exact (compressedHistory_windows_disjoint w hn hlo _ _ (by omega) (by omega) h).symm
  exact Finset.disjoint_left.mp dis member hc

/-- Extract the current encoder from the actual full170-group circuit;
all remaining groups stay encoded in their original order. -/
theorem allGroupEncode_factor (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n j : Nat) (bound : 3*n ≤ 512) (hj : j < n) (s : State) :
    run (allGroupEncode w n) [] s =
      run (otherGroupEncode w j n) [] (run (compressedHistoryEncode w (3*j)) [] s) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    by_cases same : j=n
    · subst j
      have dis := allGroupEncode_disjoint w hn hlo n n (by omega) (Nat.le_refl _) (by omega)
      rw [allGroupEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [otherGroupEncode,if_pos rfl,otherGroupEncode_outside w n n (Nat.le_refl _)]
      exact (run_disjoint_commute (allGroupEncode w n) (compressedHistoryEncode w (3*n)) dis [] [] s).symm
    · have small : j < n := by omega
      have prior := ih j (by omega) small
      have right : run (otherGroupEncode w j (n+1)) []
          (run (compressedHistoryEncode w (3*j)) [] s) =
          run (compressedHistoryEncode w (3*n)) []
            (run (otherGroupEncode w j n) [] (run (compressedHistoryEncode w (3*j)) [] s)) := by
        rw [otherGroupEncode,if_neg (Ne.symm same),run_append]
        simp only [List.take_nil,List.drop_nil]
      rw [allGroupEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [prior,right]

/-- The complete foreign encoder is disjoint from an actual current
three-cell packet; this supplies the packet theorem's concrete premise. -/
theorem otherGroupEncode_body_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hb : b ∉ skywalkPoolWires w) (hs : sign ∉ skywalkPoolWires w) (he : eff ∉ skywalkPoolWires w)
    (n j : Nat) (bound : 3*n ≤ 512) (hj : j < n) (body : Program)
    (support : wires body ⊆ groupReadSites w b sign eff (3*j)) :
    Disjoint (wires (otherGroupEncode w j n)) (wires body) := by
  apply Finset.disjoint_left.mpr
  intro q hq hbody
  obtain ⟨k,hk,ne,member⟩ := otherGroupEncode_member w n j q hq
  have dis := other_encoder_disjoint w b sign eff hn hlo hb hs he (3*k) (3*j)
    (by omega) (by omega) (by omega) body support
  exact Finset.disjoint_left.mp dis member hbody

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldInvariantStep.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run

private theorem history_words_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign ∉ skywalkPoolWires w)
    (start : Nat) (hs : start+3 ≤ 512) (j : Fin 6) :
    compressedHistoryMap w start j ∉ (balancedSharedPorts w sign).r ∧
    compressedHistoryMap w start j ∉ (balancedSharedPorts w sign).y := by
  have away := history_active_away w sign hn ho start hs j
  constructor <;> intro h <;> apply away
  all_goals
    simp only [compressedHistoryMap,sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      BalancedCleanup.Layout.y,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto

/-- Field frames preserve the raw legal history on the entire fixed tape. -/
theorem frame_history_legal (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign ∉ skywalkPoolWires w)
    (base s : BasisState) (X Y : Nat) (legal : RawGroupLegal w 170 base)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base X Y s) :
    RawGroupLegal w 170 s := by
  intro k hk
  have same (j : Fin 6) : s (compressedHistoryMap w (3*k) j) = base (compressedHistoryMap w (3*k) j) :=
    h.2.2 _ (history_words_away w sign hn ho (3*k) (by omega) j).1
      (history_words_away w sign hn ho (3*k) (by omega) j).2
  rw [same 0,same 1,same 2,same 3,same 4,same 5]
  exact legal k hk

private theorem current_records (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (j : Nat) (hj : j < 170) (s : State) (m : List Bool)
    (legal : RawGroupLegal w 170 s.basis) :
    run (compressedHistoryEncode w (3*j)) m s = run (compressedHistoryEncode w (3*j)) [] s := by
  have a := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s m (legal j hj)
  have z := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s [] (legal j hj)
  apply State.extensionality
  · simpa only [compressedHistoryEncode] using a.1.trans z.1.symm
  · exact run_basis_records _ s s m [] rfl

/-- A real three-cell forward packet advances the fixed full170-prefix
encoding invariant, including the physical caller phase and all raw outsiders.
Only structural packet support is assumed; its semantic frame is instantiated
from the accepted actual field cells, not supplied as a circuit oracle. -/
theorem encoded_forward_packet_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (j : Nat) (hj : j < 170) (a c d : MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign eff [a,c,d])
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base) (X Y : Fp)
    (support : wires (rawForwardPacket w b sign eff a c d) ⊆ groupReadSites w b sign eff (3*j))
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign base X Y s) :
    let out := run (codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]) m s
    out.phase = s.phase ∧ EncodedFieldFrame w sign base
      (skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)).1
      (skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)).2 out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs base raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj _ support
  obtain ⟨rawOut,state,outPhase,outFrame⟩ := forward_packet w b sign eff (3*j) a c d hn hlo
    (by omega) hf ho base hg0 he0 env X Y raw frame (leg j hj)
    (otherGroupEncode w j 170) hE hB [] [] m
  have outLegal := frame_history_legal w sign hn hs base rawOut.basis _ _ legal outFrame
  have records := current_records w pool hlo j hj rawOut
    (m.drop (measurementCount (rawForwardPacket w b sign eff a c d))) outLegal
  rw [records] at state
  have back := allGroupEncode_factor w pool hlo 170 j (by decide) hj rawOut
  rw [←back] at state
  have actual : run (codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]) m s =
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,factor]
    exact state
  dsimp only
  rw [actual]
  have encodedPhase := allGroupEncode_phase w pool hlo 170 (by decide) rawOut [] outLegal
  refine ⟨encodedPhase.trans (outPhase.trans phase),?_⟩
  refine ⟨rawOut,encodedPhase.symm,outFrame,rfl⟩

/-- Reverse packet counterpart under the same fixed full encoding. -/
theorem encoded_backward_packet_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (j : Nat) (hj : j < 170) (a c d : MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign eff [a,c,d])
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base) (X Y : Fp)
    (support : wires (rawBackwardPacket w b sign eff a c d) ⊆ groupReadSites w b sign eff (3*j))
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign base X Y s) :
    let out := run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]) m s
    out.phase = s.phase ∧ EncodedFieldFrame w sign base
      (skywalkPayloadReplayInverse (mixedTranscriptControls base b [a,c,d]) (X,Y)).1
      (skywalkPayloadReplayInverse (mixedTranscriptControls base b [a,c,d]) (X,Y)).2 out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs base raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj _ support
  obtain ⟨rawOut,state,outPhase,outFrame⟩ := backward_packet w b sign eff (3*j) a c d hn hlo
    (by omega) hf ho base hg0 he0 env X Y raw frame (leg j hj)
    (otherGroupEncode w j 170) hE hB [] [] m
  have outLegal := frame_history_legal w sign hn hs base rawOut.basis _ _ legal outFrame
  have records := current_records w pool hlo j hj rawOut
    (m.drop (measurementCount (rawBackwardPacket w b sign eff a c d))) outLegal
  rw [records] at state
  have back := allGroupEncode_factor w pool hlo 170 j (by decide) hj rawOut
  rw [←back] at state
  have actual : run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]) m s =
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,factor]
    exact state
  dsimp only
  rw [actual]
  have encodedPhase := allGroupEncode_phase w pool hlo 170 (by decide) rawOut [] outLegal
  refine ⟨encodedPhase.trans (outPhase.trans phase),?_⟩
  refine ⟨rawOut,encodedPhase.symm,outFrame,rfl⟩

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldTapeAlignment.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport

def IndexedLetters (w : Nat → Wire) : Nat → List MixedTranscriptLetter → Prop
  | _,[] => True
  | i,l::ls => l.1=(w i,w (1028+i)) ∧ IndexedLetters w (i+1) ls

theorem packet_active_support (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (ls : List MixedTranscriptLetter)
    (h : ∀ l ∈ ls,l.1.1 ∈ wires (compressedHistoryEncode w start) ∧
      l.1.2 ∈ wires (compressedHistoryEncode w start)) :
    wires (OffsetBorrowedCanonical.replay w b sign eff ls) ⊆ groupReadSites w b sign eff start ∧
    wires (OffsetBorrowedInverseCanonical.replay w b sign eff ls) ⊆ groupReadSites w b sign eff start := by
  induction ls with
  | nil => simp [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,wires]
  | cons l ls ih =>
    have own := h l (by simp)
    have first := current_cells_support w b sign eff start l.1.1 l.1.2 l.2.1 l.2.2 own.1 own.2
    have rest := ih (fun q hq => h q (by simp [hq]))
    simp only [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,
      wires_append,Finset.union_subset_iff]
    exact ⟨⟨first.1,rest.1⟩,⟨rest.2,first.2⟩⟩

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldRawTail.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires allGroupEncode otherGroupEncode compressedHistoryEncode
attribute [local irreducible] OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] OffsetBorrowedCanonical.replay OffsetBorrowedInverseCanonical.replay

def directionalReplay (reverse : Bool) (w : Nat → Wire) (b sign eff : Wire)
    (ls : List MixedTranscriptLetter) : Program :=
  if reverse then OffsetBorrowedInverseCanonical.replay w b sign eff ls
  else OffsetBorrowedCanonical.replay w b sign eff ls

attribute [local irreducible] directionalReplay

def directionalPayload (reverse : Bool) (controls : List (Bool×Bool)) (xy : Fp×Fp) : Fp×Fp :=
  if reverse then skywalkPayloadReplayInverse controls xy else skywalkPayloadReplay controls xy

private theorem encoder_member (w : Nat → Wire) (q : Wire)
    (h : q ∈ wires (allGroupEncode w 170)) :
    ∃ k,k < 170 ∧ q ∈ wires (compressedHistoryEncode w (3*k)) := by
  rw [←otherGroupEncode_outside w 170 170 (Nat.le_refl _)] at h
  obtain ⟨k,hk,_,hm⟩ := otherGroupEncode_member w 170 170 q h
  exact ⟨k,hk,hm⟩

private theorem tail_cell_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (i : Nat) (hloi : 510 ≤ i) (hii : i < 512) (ig is : Bool) :
    Disjoint (wires (allGroupEncode w 170))
      (wires (OffsetBorrowedCanonical.cell w b (w i) (w (1028+i)) sign eff ig is)) ∧
    Disjoint (wires (allGroupEncode w 170))
      (wires (OffsetBorrowedInverseCanonical.cell w b (w i) (w (1028+i)) sign eff ig is)) := by
  let W := (sharedSites w sign).toFinset ∪ {b,eff,w i,w (1028+i)}
  have support := cells_active w b (w i) (w (1028+i)) sign eff ig is W
    (fun _ h => Finset.mem_union_left _ h) (by simp [W]) (by simp [W]) (by simp [W]) (by simp [W])
  have dis : Disjoint (wires (allGroupEncode w 170)) W := by
    apply Finset.disjoint_left.mpr
    intro q hq hW
    obtain ⟨k,hk,hm⟩ := encoder_member w q hq
    obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w (skywalkShared_integer_nodup w hn) hlo
      (3*k) (by omega) _ (Or.inl rfl) q hm
    let idx := compressedHistoryId (3*k) j
    have bound : idx < 1798 := compressedHistoryId_bound (3*k) (by omega) j
    have own : w idx ∈ skywalkPoolWires w := by
      simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
      exact ⟨idx,by omega,rfl⟩
    have active := history_active_away w sign hn (hp sign (by simp)) (3*k) (by omega) j
    have ng : w idx ≠ w i := by
      intro e
      have eq := skywalkShared_index_inj w hn idx i (by omega) (by omega) e
      have hj := j.isLt
      unfold idx compressedHistoryId at eq
      split_ifs at eq <;> omega
    have ns : w idx ≠ w (1028+i) := by
      intro e
      have eq := skywalkShared_index_inj w hn idx (1028+i) (by omega) (by omega) e
      have hj := j.isLt
      unfold idx compressedHistoryId at eq
      split_ifs at eq <;> omega
    simp only [W,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hW
    rcases hW with h|h|h|h|h
    · exact active (List.mem_toFinset.mp h)
    · exact hp b (by simp) (h ▸ own)
    · exact hp eff (by simp) (h ▸ own)
    · exact ng h
    · exact ns h
  exact ⟨dis.mono_right support.1,dis.mono_right support.2⟩

theorem tail_replay_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (i : Nat) (ls : List MixedTranscriptLetter) (start : 510 ≤ i)
    (bound : i+ls.length ≤ 512) (aligned : IndexedLetters w i ls) :
    Disjoint (wires (allGroupEncode w 170)) (wires (OffsetBorrowedCanonical.replay w b sign eff ls)) ∧
    Disjoint (wires (allGroupEncode w 170)) (wires (OffsetBorrowedInverseCanonical.replay w b sign eff ls)) := by
  induction ls generalizing i with
  | nil => simp [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,wires]
  | cons l ls ih =>
    have first := tail_cell_disjoint w b sign eff hn hlo hp i start (by simp at bound; omega) l.2.1 l.2.2
    have rest := ih (i+1) (by omega) (by simp at bound; omega) aligned.2
    have control := aligned.1
    simp only [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,
      wires_append,Finset.disjoint_union_right]
    rw [control]
    exact ⟨⟨first.1,rest.1⟩,⟨rest.2,first.2⟩⟩

/-- The final two original letters stay raw while the complete170 earlier
groups stay encoded. Both directions preserve the full encoding invariant. -/
theorem encoded_tail_replay (reverse : Bool) (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (i : Nat) (ls : List MixedTranscriptLetter) (start : 510 ≤ i)
    (bound : i+ls.length ≤ 512) (aligned : IndexedLetters w i ls)
    (hf : MixedTranscriptReplayLayout w b sign eff ls)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign base X Y s) :
    let out := run (directionalReplay reverse w b sign eff ls) m s
    out.phase = s.phase ∧ EncodedFieldFrame w sign base
      (directionalPayload reverse (mixedTranscriptControls base b ls) (X,Y)).1
      (directionalPayload reverse (mixedTranscriptControls base b ls) (X,Y)).2 out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have ds := tail_replay_disjoint w b sign eff hn hlo hp i ls start bound aligned
  have dis : Disjoint (wires (allGroupEncode w 170)) (wires (directionalReplay reverse w b sign eff ls)) := by
    cases reverse <;> simp only [directionalReplay,Bool.false_eq_true,if_false,if_true]
    · exact ds.1
    · exact ds.2
  have rr : (run (directionalReplay reverse w b sign eff ls) m raw).phase = raw.phase ∧
      PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (directionalPayload reverse (mixedTranscriptControls base b ls) (X,Y)).1)
        (centerWord (directionalPayload reverse (mixedTranscriptControls base b ls) (X,Y)).2)
        (run (directionalReplay reverse w b sign eff ls) m raw).basis := by
    cases reverse <;> simp only [directionalReplay,directionalPayload,Bool.false_eq_true,if_false,if_true]
    · exact OffsetBorrowedCanonical.replay_frame w b sign eff hn ls hf ho base hg0 he0 env X Y raw m frame
    · exact OffsetBorrowedInverseCanonical.replay_frame w b sign eff hn ls hf ho base hg0 he0 env X Y raw m frame
  let rawOut := run (directionalReplay reverse w b sign eff ls) m raw
  have leg := frame_history_legal w sign hn (hp sign (by simp)) base rawOut.basis _ _ legal rr.2
  have commute := (run_disjoint_commute (allGroupEncode w 170)
    (directionalReplay reverse w b sign eff ls) dis [] m raw).symm
  have actual : run (directionalReplay reverse w b sign eff ls) m s =
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,commute]
  dsimp only
  rw [actual]
  have p := allGroupEncode_phase w (skywalkShared_integer_nodup w hn) hlo 170 (by decide) rawOut [] leg
  exact ⟨p.trans (rr.1.trans phase),⟨rawOut,p.symm,rr.2,rfl⟩⟩

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldGroupedReplay.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedFieldEncodedZeros.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedAllocation
attribute [local irreducible] run wires allGroupEncode compressedHistoryEncode

/-- The actual final MX instruction clears codec site3 for every input.
Legality is needed for phase/invertibility, but not for this zero output. -/
private theorem pack_hole_zero (s : State) (m : List Bool) :
    (run TranscriptCodec3.pack m s).basis 3 = false := by
  have layout : TranscriptCodec3.pack = TranscriptCodec3.pack.dropLast++
      [.measureX 3 [] [.CZ 1 0]] := by rfl
  rw [layout,run_append,run_take]
  simp only [run,measureAndCorrect,correct_basis,writeBit,Function.update_self]

private theorem placed_hole_zero (f : Fin 6 → Wire) (hn : Function.Injective f)
    (hl : ∀ j,6 ≤ f j) (s : State) (m : List Bool) :
    (run (TranscriptCodec3.encode f) m s).basis (f 3) = false := by
  let e := TranscriptCodec3.placement f
  have eq := run_rename e e.injective TranscriptCodec3.pack m s
  have atThree := congrArg (fun t : State => t.basis 3) eq
  have site : e 3 = f 3 := TranscriptCodec3.placement_apply f hn hl 3
  change (run (TranscriptCodec3.encode f) m s).basis (e 3) =
    (run TranscriptCodec3.pack m (pullState e s)).basis 3 at atThree
  rw [site] at atThree
  exact atThree.trans (pack_hole_zero (pullState e s) m)

/-- Every hole is cleared by its own actual encoder and kept by every
other encoder. This statement is universal, even before assuming legal tape. -/
theorem allGroupEncode_holes_zero (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n : Nat) (bound : 3*n ≤ 512) (s : State) (m : List Bool)
    (j : Nat) (hj : j < n) :
    (run (allGroupEncode w n) m s).basis (w (H j)) = false := by
  induction n generalizing m j with
  | zero => omega
  | succ n ih =>
    let before := run (allGroupEncode w n) (m.take (measurementCount (allGroupEncode w n))) s
    rw [allGroupEncode,run_append]
    by_cases current : j=n
    · subst j
      have zero := placed_hole_zero (compressedHistoryMap w (3*n))
        (compressedHistoryMap_injective w hn (3*n) (by omega))
        (compressedHistoryMap_above w (3*n) (by omega) hlo) before
        (m.drop (measurementCount (allGroupEncode w n)))
      simpa only [compressedHistoryEncode,compressedHistoryMap,compressedHistoryId,H,
        Nat.reduceMod,Nat.reduceDiv,Nat.reduceEqDiff,if_false] using zero
    · have older : j < n := by omega
      have old := ih (by omega) (m.take (measurementCount (allGroupEncode w n))) j older
      have dis := compressedHistory_windows_disjoint w hn hlo (3*j) (3*n) (by omega) (by omega) (by omega)
      have site : w (H j) ∈ wires (compressedHistoryEncode w (3*j)) := by
        simpa only [compressedHistoryMap,compressedHistoryId,H,Nat.reduceMod,Nat.reduceDiv,
          Nat.reduceEqDiff,if_false] using compressedHistory_site_mem w hn hlo (3*j) (by omega) 3
      have keep := run_preserves_outside (compressedHistoryEncode w (3*n))
        (m.drop (measurementCount (allGroupEncode w n))) before (w (H j))
        (fun h => Finset.disjoint_left.mp dis site h)
      exact keep.trans old

/-- Existing raw field work cleanliness is transported by the field frame;
encoding never touches the170 work positions. -/
theorem encoded_work_zero (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (base : BasisState) (env : Env w base) (X Y : Fp) (s : State)
    (frame : EncodedFieldFrame w sign base X Y s)
    (j : Nat) (hj : j < 170) : s.basis (w (W j)) = false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have rawEnv := pair_env w sign hn base raw.basis _ _ env rawFrame
  have zero := OffsetCleanupBorrowedCaller.maskBit_zero w raw.basis rawEnv.1 (W j)
    (by unfold W; omega) (by unfold W; omega)
  have pool := skywalkShared_integer_nodup w hn
  have support := compressedPrefix_history_support w pool hlo 512 (by decide)
  have away : w (W j) ∉ wires (allGroupEncode w 170) := by
    rw [←encode_prefix_512]
    intro hq
    have member := List.mem_toFinset.mp (support hq)
    rcases List.mem_append.mp member with member|member
    all_goals
      obtain ⟨k,hk,eq⟩ := List.mem_map.mp member
      simp only [List.mem_range'_1] at hk
      have same := skywalkPool_index_inj w pool k (W j) (by omega) (by unfold W; omega) eq
      unfold W at same
      omega
  rw [encoded]
  exact (run_preserves_outside (allGroupEncode w 170) [] raw (w (W j)) away).trans zero

/-- Derived universal allocation boundary for every encoded field frame.
No extra all-zero bank hypothesis is added to the replay/caller contract. -/
theorem encoded_zero_region (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (base : BasisState) (env : Env w base) (X Y : Fp) (s : State)
    (frame : EncodedFieldFrame w sign base X Y s) :
    ∀ q,zeroRegion q → (pullState w s).basis q = false := by
  intro q hq
  rcases hq with work|hole
  · have j : q = W (q-515) := by unfold workRegion W at *; omega
    have bound : q-515 < 170 := by unfold workRegion at work; omega
    rw [j]
    exact encoded_work_zero w sign hn hlo base env X Y s frame _ bound
  · have j : q = H ((q-1029)/3) := by unfold holeRegion H at *; omega
    have bound : (q-1029)/3 < 170 := by unfold holeRegion at hole; omega
    obtain ⟨raw,_,_,encoded⟩ := frame
    rw [encoded,j]
    exact allGroupEncode_holes_zero w (skywalkShared_integer_nodup w hn) hlo 170 (by decide) raw [] _ bound

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedTerminalEncodingBridge.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode otherGroupEncode
  compressedHistoryEncode compressedEncodePrefix skywalkArithmeticClear

/-- The actual physical compact terminal tape satisfies every codec's
three ternary predicates, without a sampled or shortened trace. -/
theorem compact_terminal_raw_legal (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (s : BasisState)
    (stage : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s) :
    RawGroupLegal w 170 s := by
  intro j hj
  exact compressedCompactHistory_legal w hn x p 512 (3*j) hp0 hpo
    (by omega) (by decide) s stage

/-- Recover a complete-State raw witness from the actual encoded integer
postcondition. Its phase is chosen to match the caller, then justified by
record-independent encoder correctness on the derived legal tape. -/
theorem compressed_terminal_encoded_state (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1) (s : State)
    (stage : CompressedCompactStage w x p 512 s.basis) :
    ∃ raw : State,
      CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 raw.basis ∧
      RawGroupLegal w 170 raw.basis ∧ raw.phase=s.phase ∧
      s=run (allGroupEncode w 170) [] raw := by
  obtain ⟨ghost,compact,bits⟩ := stage
  let raw : State := {basis:=ghost.basis,phase:=s.phase}
  have legal := compact_terminal_raw_legal w hn x p hp0 hpo raw.basis compact
  have phase := allGroupEncode_phase w hn hlo 170 (by decide) raw [] legal
  have basis : s.basis=(run (allGroupEncode w 170) [] raw).basis := by
    rw [encode_prefix_512] at bits
    exact bits.trans (run_basis_records (allGroupEncode w 170) ghost raw [] [] rfl)
  refine ⟨raw,compact,legal,rfl,?_⟩
  apply State.extensionality
  · exact phase.symm
  · exact basis

private theorem full_encoder_member (w : Nat → Wire) (q : Wire)
    (h : q∈wires (allGroupEncode w 170)) :
    ∃j,j < 170 ∧ q∈wires (compressedHistoryEncode w (3*j)) := by
  rw [←otherGroupEncode_outside w 170 170 (Nat.le_refl _)] at h
  obtain ⟨j,hj,_,member⟩ := otherGroupEncode_member w 170 170 q h
  exact ⟨j,hj,member⟩

/-- The actual last orientation511 remains raw. The full encoder uses
only records0..509 and1028..1537; clear targets512 and770 are nonhistory. -/
theorem full_encoder_clear_disjoint (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w) :
    Disjoint (wires (allGroupEncode w 170)) (wires (skywalkArithmeticClear w)) := by
  apply Finset.disjoint_left.mpr
  intro q encoded clear
  obtain ⟨j,hj,member⟩ := full_encoder_member w q encoded
  obtain ⟨u,rfl⟩ := compressedHistory_gate_mem w hn hlo (3*j) (by omega)
    _ (Or.inl rfl) q member
  let idx := compressedHistoryId (3*j) u
  have range : idx < 510 ∨ (1028 ≤ idx ∧ idx < 1538) := by
    have hu := u.isLt
    unfold idx compressedHistoryId
    split_ifs <;> omega
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at clear
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at clear
  rcases clear with eq|eq|eq
  · have same := skywalkPool_index_inj w hn idx 511 (by omega) (by omega) eq
    omega
  · have same := skywalkPool_index_inj w hn idx 512 (by omega) (by omega) eq
    omega
  · have same := skywalkPool_index_inj w hn idx 770 (by omega) (by omega) eq
    omega

/-- Exact complete-State commutation includes every measurement correction
and arbitrary independent encoder/clear record streams and incoming phase. -/
theorem full_encoder_clear_commute (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (s : State) (m n : List Bool) :
    run (allGroupEncode w 170) m (run (skywalkArithmeticClear w) n s)=
      run (skywalkArithmeticClear w) n (run (allGroupEncode w 170) m s) :=
  run_disjoint_commute _ _ (full_encoder_clear_disjoint w hn hlo) m n s

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/CompressedForwardCallerEquality.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open CompressedFieldSupport
attribute [local irreducible] run wires compactSkywalkForward compressedCompactForward allGroupEncode
attribute [local irreducible] SkywalkTrace.next Nat.iterate SkywalkIntegerStage

/-- Support of the actual full encoder stays inside the original integer
pool, including every measurement-correction site. -/
theorem allGroupEncode_pool_support (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w) :
    wires (allGroupEncode w 170)⊆(skywalkPoolWires w).toFinset := by
  have history := compressedPrefix_history_support w hn hlo 512 (by decide)
  rw [encode_prefix_512] at history
  intro q hq
  have member := List.mem_toFinset.mp (history hq)
  simp only [List.mem_append,wireBlock] at member
  rcases member with member|member
  all_goals
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1] at hi ⊢
    exact ⟨i,by omega,rfl⟩

/-- The actual compressed forward emitter is exactly full encoding of the
actual compact terminal State. The original seed domain, full512 rounds,
incoming phase, and arbitrary independent record lists are retained. -/
theorem compressedCompactForward_caller_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (s : State) (mNew mRaw : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    run (compressedCompactForward w 0 512) mNew s=
      run (allGroupEncode w 170) [] (run (compactSkywalkForward w 0 512) mRaw s) := by
  have pool := skywalkShared_integer_nodup w hn
  have compressed := compressedCompactForward_512_spec w pool hlo x p hp0 hx0 hpo hp hx hc s mNew hin
  have compact := compactSkywalkForward_512 w pool x p hp0 hx0 hpo hp hx hc s mRaw hin
  generalize eCompressed : run (compressedCompactForward w 0 512) mNew s=compressedState at compressed ⊢
  generalize eCompact : run (compactSkywalkForward w 0 512) mRaw s=compactState at compact ⊢
  obtain ⟨ghost,ghostStage,legal,ghostPhase,encoded⟩ :=
    compressed_terminal_encoded_state w pool hlo x p hp0 hpo compressedState compressed.2
  have ghostTerminal := (compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc
    ghost.basis ghostStage).2
  have compactTerminal := (compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc
    compactState.basis compact.2).2
  have phase : ghost.phase=compactState.phase :=
    ghostPhase.trans (compressed.1.trans compact.1.symm)
  have bits : ∀q∈(skywalkPoolWires w).toFinset,ghost.basis q=compactState.basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w (SkywalkRails.encode false false (x:Int) (p:Int))
      512 (by decide) ghost.basis compactState.basis ghostTerminal compactTerminal q
      (List.mem_toFinset.mp hq)
  have support := allGroupEncode_pool_support w pool hlo
  have agreement := pool_run_agrees (allGroupEncode w 170) (skywalkPoolWires w).toFinset
    support [] ghost compactState phase bits
  generalize eEncoded : run (allGroupEncode w 170) [] compactState=encodedState at agreement ⊢
  apply State.extensionality compressedState encodedState
  · rw [encoded]
    exact agreement.1
  · funext q
    by_cases hq : q∈skywalkPoolWires w
    · rw [encoded]
      exact agreement.2 q (List.mem_toFinset.mpr hq)
    · have forwardFrame := compressedCompactForward_frame w pool hlo 0 512 (by decide) s mNew q hq
      have compactFrame := compactSkywalkForward_frame w pool 0 512 (by decide) s mRaw q hq
      have encoderFrame := run_preserves_outside (allGroupEncode w 170) [] compactState q
        (fun h => hq (List.mem_toFinset.mp (support h)))
      rw [eCompressed] at forwardFrame
      rw [eCompact] at compactFrame
      rw [eEncoded] at encoderFrame
      exact forwardFrame.trans (encoderFrame.trans compactFrame).symm

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedAllocationSites.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation

def indices : List Nat := List.range' 0 515++List.range' 684 1114++
  List.range' 2056 258++List.range' 2400 12
def slots : List Wire := indices.map (fun q => q+16)
def live (q : Nat) : Prop := q < 1798 ∨ (2056 ≤ q ∧ q < 2314) ∨ (2400 ≤ q ∧ q < 2412)
def base (q : Nat) : Wire := q+16
def placed (j q : Nat) : Wire := pi j q+16
def allPlaced (q : Nat) : Wire := pi0 q+16

theorem base_injective : Function.Injective base := by
  intro a b h
  change a+16=b+16 at h
  exact Nat.add_right_cancel h
theorem base_pool_nodup : (skywalkPoolWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ h; exact base_injective h
  · exact List.nodup_range'

theorem base_above : CompressedHistoryAbove base := by
  intro q _
  change 6 ≤ q+16
  omega

theorem placed_injective (j : Nat) : Function.Injective (placed j) := by
  intro a b h
  apply (pi j).injective
  change pi j a+16=pi j b+16 at h
  exact Nat.add_right_cancel h
theorem allPlaced_injective : Function.Injective allPlaced := by
  intro a b h
  apply pi0.injective
  change pi0 a+16=pi0 b+16 at h
  exact Nat.add_right_cancel h

private theorem appendRange (xs : List Nat) (hd : xs.Nodup) (a n : Nat)
    (sep : ∀q∈xs,q < a ∨ a+n ≤ q) : (xs++List.range' a n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨hd,List.nodup_range',List.disjoint_left.mpr ?_⟩
  intro q hq hr
  have hs := sep q hq
  simp only [List.mem_range'_1] at hr
  omega

theorem indices_nodup : indices.Nodup := by
  have a := appendRange (List.range' 0 515) List.nodup_range' 684 1114
    (by intro q h; simp only [List.mem_range'_1] at h; omega)
  have b := appendRange _ a 2056 258
    (by intro q h; simp only [List.mem_append,List.mem_range'_1] at h; omega)
  have c := appendRange _ b 2400 12
    (by intro q h; simp only [List.mem_append,List.mem_range'_1] at h; omega)
  exact c

theorem mem_indices (q : Nat) : q∈indices ↔ live q ∧ ¬omitted q := by
  simp only [indices,List.mem_append,List.mem_range'_1]
  unfold live omitted
  omega

theorem slot_mem (q : Nat) (hl : live q) (ho : ¬omitted q) : base q∈slots.toFinset := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨q,(mem_indices q).mpr ⟨hl,ho⟩,rfl⟩

private theorem outside_live_outside_zero (q : Nat) (h : ¬live q) : ¬zeroRegion q := by
  unfold live zeroRegion workRegion holeRegion at *
  omega

theorem pi_live (j q : Nat) (hj : j < 170) (hq : live q) : live (pi j q) := by
  by_contra bad
  have eq := (pi j).injective (pi_outside j (pi j q) hj (outside_live_outside_zero _ bad))
  exact bad (eq.symm ▸ hq)

theorem pi0_live (q : Nat) (hq : live q) : live (pi0 q) := by
  by_contra bad
  have eq := pi0.injective (pi0_outside (pi0 q) (outside_live_outside_zero _ bad))
  exact bad (eq.symm ▸ hq)

theorem field_live (q : Nat) (h : fieldSite q) : live q := by unfold fieldSite live at *; omega

theorem packet_live (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : live q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold live
  unfold H at h
  omega

theorem allPlaced_field_mem (q : Nat) (h : fieldSite q) : allPlaced q∈slots.toFinset :=
  slot_mem _ (pi0_live q (field_live q h)) (field_pi0_safe q h)

theorem placed_packet_mem (j q : Nat) (hj : j < 170) (h : q∈packetSites j) :
    placed j q∈slots.toFinset :=
  slot_mem _ (pi_live j q hj (packet_live j q hj h)) (packet_safe j q hj h)

theorem history_packet (j : Nat) (u : Fin 6) : compressedHistoryId (3*j) u∈packetSites j := by
  fin_cases u
  · change 3*j∈packetSites j
    simp [packetSites]
  · change 1028+3*j∈packetSites j
    simp [packetSites]
  · change 3*j+1∈packetSites j
    simp [packetSites]
  · change 1028+3*j+1∈packetSites j
    simp [packetSites,H]
  · change 3*j+2∈packetSites j
    simp [packetSites]
  · change 1028+3*j+2∈packetSites j
    have e : 1028+3*j+2=1030+3*j := by omega
    rw [e]
    simp [packetSites]

theorem placed_pool_nodup (j : Nat) : (skywalkPoolWires (placed j)).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ h; exact placed_injective j h
  · exact List.nodup_range'

theorem placed_above (j : Nat) : CompressedHistoryAbove (placed j) := by
  intro q _
  change 6 ≤ pi j q+16
  omega

/-- Codec placement is constructed above6, not by renaming a codec whose
logical template labels collided with raw group0. -/
theorem codec_support (j : Nat) (hj : j < 170) :
    wires (compressedHistoryEncode (placed j) (3*j))⊆slots.toFinset ∧
    wires (compressedHistoryDecode (placed j) (3*j))⊆slots.toFinset := by
  constructor
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inl rfl) q hq
    exact placed_packet_mem j _ hj (history_packet j u)
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inr rfl) q hq
    exact placed_packet_mem j _ hj (history_packet j u)

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/CompressedPlacementTransport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic.MappedCompressed

/-- Extend a logical permutation above the sixteen reserved labels. -/
def shiftedFn (e : Equiv.Perm Nat) (q : Nat) : Nat :=
  if q < 16 then q else e (q-16)+16

theorem shiftedFn_base (e : Equiv.Perm Nat) (q : Nat) :
    shiftedFn e (base q)=base (e q) := by
  simp [shiftedFn,base]

private theorem shifted_inverse (e : Equiv.Perm Nat) (q : Nat) :
    shiftedFn e.symm (shiftedFn e q)=q := by
  by_cases h : q < 16
  · simp [shiftedFn,h]
  · have bound : ¬e (q-16)+16 < 16 := by omega
    simp only [shiftedFn,if_neg h,if_neg bound,Nat.add_sub_cancel,
      e.symm_apply_apply]
    omega

def shifted (e : Equiv.Perm Nat) : Equiv.Perm Nat :=
  { toFun := shiftedFn e, invFun := shiftedFn e.symm,
    left_inv := shifted_inverse e, right_inv := shifted_inverse e.symm }

theorem shifted_base (e : Equiv.Perm Nat) (q : Nat) :
    shifted e (base q)=base (e q) := shiftedFn_base e q

/-- Natural relabeling includes every measurement correction in the codec. -/
theorem codec_rename (f : Wire → Wire) (w : Fin 6 → Wire)
    (hn : Function.Injective w) (hw : ∀i,6 ≤ w i)
    (hf : Function.Injective (f ∘ w)) (hfw : ∀i,6 ≤ f (w i)) :
    renameProgram f (TranscriptCodec3.encode w)=TranscriptCodec3.encode (f ∘ w) ∧
    renameProgram f (TranscriptCodec3.decode w)=TranscriptCodec3.decode (f ∘ w) := by
  have onSupport (q : Nat) (hq : q∈Finset.range 6) :
      (f ∘ TranscriptCodec3.placement w) q=TranscriptCodec3.placement (f ∘ w) q := by
    have lt := Finset.mem_range.mp hq
    have a := TranscriptCodec3.placement_apply w hn hw ⟨q,lt⟩
    have b := TranscriptCodec3.placement_apply (f ∘ w) hf hfw ⟨q,lt⟩
    exact (congrArg f a).trans b.symm
  constructor
  · unfold TranscriptCodec3.encode
    rw [renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    exact onSupport q (TranscriptCodec3.support.1 ▸ hq)
  · unfold TranscriptCodec3.decode
    rw [renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    exact onSupport q (TranscriptCodec3.support.2 ▸ hq)

theorem shifted_current_codec (j : Nat) (hj : j < 170) :
    renameProgram (shifted (CompressedAllocation.pi j))
        (compressedHistoryEncode base (3*j))=compressedHistoryEncode (placed j) (3*j) ∧
    renameProgram (shifted (CompressedAllocation.pi j))
        (compressedHistoryDecode base (3*j))=compressedHistoryDecode (placed j) (3*j) := by
  have maps : shifted (CompressedAllocation.pi j) ∘ compressedHistoryMap base (3*j)=
      compressedHistoryMap (placed j) (3*j) := by
    funext u
    exact shifted_base _ _
  have hn := compressedHistoryMap_injective base
    (List.Nodup.map base_injective List.nodup_range') (3*j) (by omega)
  have highBase : CompressedHistoryAbove base := by
    intro q _
    change 6 ≤ q+16
    omega
  have hw := compressedHistoryMap_above base (3*j) (by omega) highBase
  have hf : Function.Injective
      (shifted (CompressedAllocation.pi j) ∘ compressedHistoryMap base (3*j)) :=
    (shifted _).injective.comp hn
  have high : ∀u,6 ≤ shifted (CompressedAllocation.pi j) (compressedHistoryMap base (3*j) u) := by
    intro u
    rw [show shifted (CompressedAllocation.pi j) (compressedHistoryMap base (3*j) u)=
      compressedHistoryMap (placed j) (3*j) u from congrFun maps u]
    exact compressedHistoryMap_above (placed j) (3*j) (by omega) (placed_above j) u
  have result := codec_rename (shifted (CompressedAllocation.pi j))
    (compressedHistoryMap base (3*j)) hn hw hf high
  simpa only [compressedHistoryEncode,compressedHistoryDecode,maps] using result

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/CompressedPointSquareCorrect.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.CompressedPointSquare
open ControlledPointLayout Secp256k1
attribute [local irreducible] run wires computableProgram program pointMeasuredSquareCandidate

private theorem pool_bit (L : ControlledPointLayout) (hw : L.Widths)
    (i : Nat) (hi : i < 945) : L.core.poolWire i∈L.dialogPool := by
  change L.core.poolWire i∈L.core.pool.take 2613
  rw [←L.core.pool_prefix hw 2613 (by omega)]
  exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1]; omega,rfl⟩

/-- Only declared pool wires move. Their zero basis bits make the complete
State invariant under the public permutation, including incoming phase. -/
theorem zero_pool_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (clean : ∀q∈L.dialogPool,s.basis q=false) :
    pullState (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) s=s := by
  classical
  let inj := layout_bounded_injective L hw hn
  let e := poolPermutation L.core.poolWire inj
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (e q)=s.basis q
    by_cases left : LeftSite L.core.poolWire q
    · obtain ⟨i,lo,hi,rfl⟩ := left
      have eq : e (L.core.poolWire i)=L.core.poolWire (indexPermutation i) :=
        wire_apply L.core.poolWire inj i (by omega)
      rw [eq]
      exact (clean _ (pool_bit L hw _ (index_bounded i (by omega)))).trans
        (clean _ (pool_bit L hw i (by omega))).symm
    · by_cases right : RightSite L.core.poolWire q
      · obtain ⟨i,lo,hi,rfl⟩ := right
        have eq : e (L.core.poolWire i)=L.core.poolWire (indexPermutation i) :=
          wire_apply L.core.poolWire inj i hi
        rw [eq]
        exact (clean _ (pool_bit L hw _ (index_bounded i hi))).trans
          (clean _ (pool_bit L hw i hi)).symm
      · rw [outside_fixed L.core.poolWire inj q left right]

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (computableProgram L)=99902 ∧ measurementCount (computableProgram L)=99382 := by
  rw [computableProgram]
  have renamed := renameProgram_counts (labelFn L.core.poolWire) (pointMeasuredSquareCandidate L)
  have old := pointMeasuredSquareCandidate_counts L hw
  exact ⟨renamed.1.trans old.1,renamed.2.trans old.2⟩

end ECDSAAdd.Arithmetic.CompressedPointSquare
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedPointPlacement.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open ControlledPointLayout

def pointMeta (L : ControlledPointLayout) : List Wire :=
  [L.core.generic,L.point.finite,L.control,L.infinitySelect,L.doubleSelect,L.genericSelect,
    L.core.equalX,L.core.equalNegY,L.core.double,L.skywalkDirectSelectorG,
    L.skywalkDirectSelectorS,L.skywalkDirectZero]

/-- Only the shared labels and twelve declared metadata sites are placed.
Fallback labels outside that domain carry no injectivity claim. -/
def pointIndexWire (L : ControlledPointLayout) (i : Nat) : Wire :=
  if i < 2314 then L.skywalkDirectMap i else (pointMeta L).getD (i-2400) L.control

def pointWireFn (L : ControlledPointLayout) (q : Wire) : Wire := pointIndexWire L (q-16)
def pointIndexSites : List Nat := List.range' 0 2314++List.range' 2400 12

theorem pointWireFn_base (L : ControlledPointLayout) (i : Nat) :
    pointWireFn L (base i) = pointIndexWire L i := by
  simp only [pointWireFn,base,Nat.add_sub_cancel]

theorem pointIndexWire_shared (L : ControlledPointLayout) (i : Nat) (hi : i < 2314) :
    pointIndexWire L i = L.skywalkDirectMap i := by
  simp only [pointIndexWire,if_pos hi]

private theorem inventory_map (L : ControlledPointLayout) :
    pointIndexSites.map (pointIndexWire L)=skywalkSharedWires L.skywalkDirectMap++pointMeta L := by
  have shared : (List.range' 0 2314).map (pointIndexWire L)=skywalkSharedWires L.skywalkDirectMap := by
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range'_1] at hi
    exact pointIndexWire_shared L i hi.2
  have metadataMap : (List.range' 2400 12).map (pointIndexWire L)=pointMeta L := by
    simp [List.range',pointIndexWire,pointMeta]
  simp only [pointIndexSites,List.map_append,shared,metadataMap]

/-- All2314 shared labels and twelve metadata labels permute exactly the
existing declared point inventory, including its three arithmetic scalars. -/
theorem pointIndexSites_perm (L : ControlledPointLayout) (hw : L.Widths) :
    (pointIndexSites.map (pointIndexWire L)).Perm L.skywalkDirectDeclaredSites := by
  have shared := skywalkPointWire_shared L.core.poolWire L.point.x L.point.y hw.inputX hw.inputY
  have poolPrefix : L.dialogPool.take 1805=wireBlock L.core.poolWire 0 1805 := by
    rw [L.core.pool_prefix hw 1805 (by omega)]
    simp only [dialogPool,List.take_take,Nat.min_eq_left (show 1805≤2613 by omega)]
  have split : wireBlock L.core.poolWire 0 1805=
      wireBlock L.core.poolWire 0 770++wireBlock L.core.poolWire 770 1030++
      wireBlock L.core.poolWire 1800 2++
      [L.skywalkDirectSelectorG,L.skywalkDirectSelectorS,L.skywalkDirectZero] := by
    have scalars : wireBlock L.core.poolWire 1802 3=
        [L.skywalkDirectSelectorG,L.skywalkDirectSelectorS,L.skywalkDirectZero] := by
      simp [wireBlock,List.range',skywalkDirectSelectorG,skywalkDirectSelectorS,skywalkDirectZero]
    rw [←wireBlock_append L.core.poolWire 0 1802 3,scalars]
    have first : wireBlock L.core.poolWire 0 1802=
        wireBlock L.core.poolWire 0 770++wireBlock L.core.poolWire 770 1030++
        wireBlock L.core.poolWire 1800 2 := by
      symm; rw [wireBlock_append,wireBlock_append]
    rw [first]
  rw [inventory_map]
  apply List.perm_iff_count.mpr
  intro q
  simp only [skywalkDirectDeclaredSites,poolPrefix,split,skywalkDirectMap,shared,
    pointMeta,PointAddLayout.pointWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil]
  omega

private theorem nodup_map_inj (f : Nat → Wire) (xs : List Nat)
    (nd : (xs.map f).Nodup) (a b : Nat) (ha : a∈xs) (hb : b∈xs) (eq : f a=f b) : a=b := by
  induction xs generalizing a b with
  | nil => simp at ha
  | cons c cs ih =>
    have head := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with atHead|inTailA
    · rcases List.mem_cons.mp hb with btHead|inTailB
      · exact atHead.trans btHead.symm
      · have inMap : f b ∈ cs.map f := List.mem_map.mpr ⟨b,inTailB,rfl⟩
        have headEq : f c = f b := (congrArg f atHead).symm.trans eq
        exact (head.1 (headEq.symm ▸ inMap)).elim
    · rcases List.mem_cons.mp hb with btHead|inTailB
      · have inMap : f a ∈ cs.map f := List.mem_map.mpr ⟨a,inTailA,rfl⟩
        have headEq : f a = f c := eq.trans (congrArg f btHead)
        exact (head.1 (headEq ▸ inMap)).elim
      · exact ih head.2 a b inTailA inTailB eq

theorem indices_subset_pointIndexSites : indices ⊆ pointIndexSites := by
  intro i hi
  simp only [indices,pointIndexSites,List.mem_append,List.mem_range'_1] at hi ⊢
  omega

/-- Finite placement injectivity on S only, derived from the declared
point-site permutation. No global Wire→Wire injectivity is asserted. -/
theorem pointWireFn_injective_slots (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ∀ a∈slots.toFinset,∀ b∈slots.toFinset,pointWireFn L a=pointWireFn L b → a=b := by
  have nd := (pointIndexSites_perm L hw).nodup_iff.mpr (L.skywalkDirectDeclaredSites_nodup hn)
  intro a ha b hb eq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  have same : pointIndexWire L i=pointIndexWire L j := by
    simpa only [pointWireFn,Nat.add_sub_cancel] using eq
  have ij := nodup_map_inj (pointIndexWire L) pointIndexSites nd i j
    (indices_subset_pointIndexSites hi) (indices_subset_pointIndexSites hj) same
  exact congrArg (fun k => k+16) ij

theorem pointWireFn_block (L : ControlledPointLayout) (start len : Nat) :
    (wireBlock base start len).map (pointWireFn L)=wireBlock (pointIndexWire L) start len := by
  simp only [wireBlock,List.map_map]
  apply List.map_congr_left
  intro i _
  exact pointWireFn_base L i

theorem pointWireFn_shared_block (L : ControlledPointLayout) (start len : Nat) (bound : start+len≤2314) :
    (wireBlock base start len).map (pointWireFn L)=wireBlock L.skywalkDirectMap start len := by
  rw [pointWireFn_block]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range'_1] at hi
  exact pointIndexWire_shared L i (by omega)

theorem pointWireFn_coordinates (L : ControlledPointLayout) (hw : L.Widths) :
    (wireBlock base 770 256).map (pointWireFn L)=L.point.x ∧
    (wireBlock base 2056 256).map (pointWireFn L)=L.point.y := by
  rw [pointWireFn_shared_block L 770 256 (by omega),
    pointWireFn_shared_block L 2056 256 (by omega)]
  exact L.skywalkDirectMap_coordinates hw

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedPointImages.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open ControlledPointLayout DirectSkywalk

theorem point_pool_mem_dialog (L : ControlledPointLayout) (hw : L.Widths)
    (i : Nat) (hi : i < 2613) : L.core.poolWire i ∈ L.dialogPool := by
  change L.core.poolWire i ∈ L.core.pool.take 2613
  rw [←L.core.pool_prefix hw 2613 (by omega)]
  exact arith_mem L.core.poolWire 0 2613 i (by omega) hi

/-- Every original shared noncoordinate label is bound to existing clean
dialog work, independently of the contents of either public coordinate. -/
theorem pointIndexWire_work_mem (L : ControlledPointLayout) (hw : L.Widths)
    (i : Nat) (hi : i < 2314) (hx : i < 770 ∨ 1026 ≤ i)
    (hy : i < 2056 ∨ 2312 ≤ i) : pointIndexWire L i ∈ L.dialogPool := by
  rw [pointIndexWire_shared L i hi]
  unfold skywalkDirectMap skywalkPointWire
  have nx : ¬(770 ≤ i ∧ i < 1026) := by omega
  have ny : ¬(2056 ≤ i ∧ i < 2312) := by omega
  simp only [if_neg nx,if_neg ny]
  apply point_pool_mem_dialog L hw
  split_ifs <;> omega

theorem pointWireFn_sharedWork (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈skywalkSharedWires base,q∈slots.toFinset →
      q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 →
      pointWireFn L q∈L.dialogPool := by
  intro q hq _ hx hy
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have outsideX : i < 770 ∨ 1026 ≤ i := by
    by_contra bad
    exact hx (arith_mem base 770 256 i (by omega) (by omega))
  have outsideY : i < 2056 ∨ 2312 ≤ i := by
    by_contra bad
    exact hy (arith_mem base 2056 256 i (by omega) (by omega))
  rw [pointWireFn_base]
  exact pointIndexWire_work_mem L hw i hi.2 outsideX outsideY

theorem pointWireFn_control (L : ControlledPointLayout) : pointWireFn L (base 2400)=L.core.generic := by
  simp [pointWireFn_base,pointIndexWire,pointMeta]

theorem pointWireFn_scalar_dialog (L : ControlledPointLayout) (hw : L.Widths) :
    pointWireFn L (base 2409)∈L.dialogPool ∧ pointWireFn L (base 2410)∈L.dialogPool ∧
      pointWireFn L (base 2411)∈L.dialogPool := by
  have a := point_pool_mem_dialog L hw 1802 (by omega)
  have b := point_pool_mem_dialog L hw 1803 (by omega)
  have c := point_pool_mem_dialog L hw 1804 (by omega)
  simpa [pointWireFn_base,pointIndexWire,pointMeta,skywalkDirectSelectorG,
    skywalkDirectSelectorS,skywalkDirectZero] using And.intro a (And.intro b c)

private theorem getD_member (xs : List Wire) (i : Nat) (d : Wire) (hi : i < xs.length) :
    xs.getD i d∈xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => exact List.mem_cons_of_mem a (ih i (by simpa using hi))

private theorem pool_mem_shared (L : ControlledPointLayout) (i : Nat)
    (hi : i < 515 ∨ (684 ≤ i ∧ i < 1542) ∨ (1800 ≤ i ∧ i < 1805)) :
    L.core.poolWire i∈CompressedPointSquare.sharedPool L := by
  rcases hi with low|middle|high
  · exact List.mem_append_left _ (List.mem_append_left _
      (arith_mem L.core.poolWire 0 515 i (by omega) low))
  · exact List.mem_append_left _ (List.mem_append_right _
      (arith_mem L.core.poolWire 684 858 i middle.1 middle.2))
  · exact List.mem_append_right _ (arith_mem L.core.poolWire 1800 5 i high.1 high.2)

theorem pointIndexWire_inventory (L : ControlledPointLayout) (hw : L.Widths)
    (i : Nat) (hi : i∈indices) :
    pointIndexWire L i∈CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L := by
  have range : i < 515 ∨ (684 ≤ i ∧ i < 1798) ∨ (2056 ≤ i ∧ i < 2314) ∨
      (2400 ≤ i ∧ i < 2412) := by
    simp only [indices,List.mem_append,List.mem_range'_1] at hi
    omega
  by_cases shared : i < 2314
  · rw [pointIndexWire_shared L i shared]
    unfold skywalkDirectMap skywalkPointWire
    split_ifs with x y a b
    · apply List.mem_append_left
      have member := getD_member L.point.x (i-770) 0 (by change i-770 < L.core.input.x.length; rw [hw.inputX]; omega)
      simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
      tauto
    · apply List.mem_append_left
      have member := getD_member L.point.y (i-2056) 0 (by change i-2056 < L.core.input.y.length; rw [hw.inputY]; omega)
      simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
      tauto
    all_goals
      apply List.mem_append_right
      apply pool_mem_shared L
      omega
  · have metadata : 2400 ≤ i ∧ i < 2412 := by omega
    by_cases resident : i < 2409
    · interval_cases i <;>
        simp [pointIndexWire,pointMeta,CompressedPointSquare.residents,PointAddLayout.pointWires,inPlaceFlags]
    · have last : i=2409 ∨ i=2410 ∨ i=2411 := by omega
      rcases last with rfl|rfl|rfl
      · apply List.mem_append_right
        simpa [pointIndexWire,pointMeta,skywalkDirectSelectorG] using
          pool_mem_shared L 1802 (Or.inr (Or.inr ⟨by omega,by omega⟩))
      · apply List.mem_append_right
        simpa [pointIndexWire,pointMeta,skywalkDirectSelectorS] using
          pool_mem_shared L 1803 (Or.inr (Or.inr ⟨by omega,by omega⟩))
      · apply List.mem_append_right
        simpa [pointIndexWire,pointMeta,skywalkDirectZero] using
          pool_mem_shared L 1804 (Or.inr (Or.inr ⟨by omega,by omega⟩))

/-- Arithmetic image shares exactly the existing compressed square's
physical work inventory;515..683 never return to this support certificate. -/
theorem pointWireFn_slots_image (L : ControlledPointLayout) (hw : L.Widths) :
    slots.toFinset.image (pointWireFn L)⊆
      (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).toFinset := by
  intro q hq
  obtain ⟨old,member,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  apply List.mem_toFinset.mpr
  have same : pointWireFn L (i+16)=pointIndexWire L i := by
    simp only [pointWireFn,Nat.add_sub_cancel]
  rw [same]
  exact pointIndexWire_inventory L hw i hi

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/FieldRenameLayouts.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename

def mapBit (f : Wire → Wire) (b : MappedBit) : MappedBit :=
  {wire:=b.wire.map f,flip:=b.flip}
def mapCleanup (f : Wire → Wire) (L : BalancedCleanup.Layout) : BalancedCleanup.Layout :=
  {r0:=f L.r0,rtail:=L.rtail.map f,rmsb:=f L.rmsb,
   ylow:=L.ylow.map f,ymsb:=f L.ymsb,carry:=L.carry.map f,
   sign:=f L.sign,parity:=f L.parity,lower:=f L.lower,one:=f L.one}
def mapCircuit (f : Wire → Wire) (L : BalancedCircuit.Layout) : BalancedCircuit.Layout :=
  {toLayout:=mapCleanup f L.toLayout,sourceGuard:=f L.sourceGuard,
   cout:=f L.cout,minus:=f L.minus,plus:=f L.plus}
def mapOffset (f : Wire → Wire) (L : BalancedCleanupOffset.Layout) : BalancedCleanupOffset.Layout :=
  {toCircuit:=mapCircuit f L.toCircuit,offsetCarry:=L.offsetCarry.map f}

theorem r_map (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    (mapCleanup f L).r=L.r.map f := by
  simp [mapCleanup,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
theorem y_map (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    (mapCleanup f L).y=L.y.map f := by
  simp [mapCleanup,BalancedCleanup.Layout.y]
theorem rawSource_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    BalancedCircuit.rawSource (mapCircuit f L)=(BalancedCircuit.rawSource L).map f := by
  simp [BalancedCircuit.rawSource,mapCircuit,y_map]
theorem rawTarget_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    BalancedCircuit.rawTarget (mapCircuit f L)=(BalancedCircuit.rawTarget L).map f := by
  simp [BalancedCircuit.rawTarget,mapCircuit,mapCleanup,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
theorem foldTarget_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    BalancedCircuit.foldTarget (mapCircuit f L)=(BalancedCircuit.foldTarget L).map f := by
  simp [BalancedCircuit.foldTarget,mapCircuit,mapCleanup]

theorem foldBits_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (BalancedCircuit.foldBits L).map (mapBit f)=BalancedCircuit.foldBits (mapCircuit f L) := by
  simp only [BalancedCircuit.foldBits,List.map_append,List.map_map,List.map_cons,List.map_nil]
  congr 1

theorem offsetBits_map (f : Wire → Wire) (L : BalancedCleanupOffset.Layout) :
    (BalancedCleanupOffset.offsetBits L).map (mapBit f)=BalancedCleanupOffset.offsetBits (mapOffset f L) := by
  simp only [BalancedCleanupOffset.offsetBits,List.map_map]
  apply List.map_congr_left
  intro i _
  by_cases h : i=1 <;> simp [mapBit,mapOffset,mapCircuit,mapCleanup,h]

theorem wireBlock_map (f w : Wire → Wire) (start len : Nat) :
    (wireBlock w start len).map f=wireBlock (f ∘ w) start len := by
  simp only [wireBlock,List.map_map,Function.comp_def]

theorem sharedPorts_map (f w : Wire → Wire) (sign : Wire) :
    mapCircuit f (balancedSharedPorts w sign)=balancedSharedPorts (f ∘ w) (f sign) := by
  simp only [mapCircuit,mapCleanup,balancedSharedPorts,wireBlock_map,Function.comp_def]

theorem callerCarry_map (f w : Wire → Wire) :
    (OffsetCleanupBorrowedCaller.carry w).map f=OffsetCleanupBorrowedCaller.carry (f ∘ w) := by
  simp [OffsetCleanupBorrowedCaller.carry,wireBlock_map,Function.comp_def]

theorem callerLayout_map (f w : Wire → Wire) (sign : Wire) :
    mapOffset f (OffsetCleanupBorrowedCaller.layout w sign)=
      OffsetCleanupBorrowedCaller.layout (f ∘ w) (f sign) := by
  simp only [mapOffset,mapCircuit,mapCleanup,OffsetCleanupBorrowedCaller.layout,
    balancedSharedPorts,callerCarry_map,wireBlock_map,Function.comp_def]

/-- The source-first seed bit is natural whenever the source is nonempty;
there is no invalid assumption that f maps the default wire0 to wire0. -/
theorem first_source_map (f : Wire → Wire) (xs : List Wire) (h : xs ≠ []) :
    (xs.map f).getD 0 0=f (xs.getD 0 0) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/FieldRenamePrimitives.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename

theorem rename_append (f : Wire → Wire) (p q : Program) :
    renameProgram f (p++q)=renameProgram f p++renameProgram f q := by
  simp only [renameProgram,List.map_append]

theorem rename_reverse (f : Wire → Wire) (p : Program) :
    renameProgram f p.reverse=(renameProgram f p).reverse := by
  simp only [renameProgram,List.map_reverse]

theorem majority_natural (f : Wire → Wire) (a b c d : Wire) :
    renameProgram f (majority a b c d)=majority (f a) (f b) (f c) (f d) := rfl
theorem eraseCarry_natural (f : Wire → Wire) (a b c d : Wire) :
    renameProgram f (eraseCarry a b c d)=eraseCarry (f a) (f b) (f c) (f d) := rfl

theorem mappedMajority_natural (f : Wire → Wire) (b : MappedBit) (y c d : Wire) :
    renameProgram f (mappedMajority b y c d)=mappedMajority (mapBit f b) (f y) (f c) (f d) := by
  cases b with
  | mk a flip =>
    cases a <;> cases flip <;>
      simp [mappedMajority,mapBit,borrowMajority,majority,
        renameProgram,renameInstr]

theorem mappedEraseCarry_natural (f : Wire → Wire) (b : MappedBit) (y c d : Wire) :
    renameProgram f (mappedEraseCarry b y c d)=mappedEraseCarry (mapBit f b) (f y) (f c) (f d) := by
  cases b with
  | mk a flip =>
    cases a <;> cases flip <;>
      simp [mappedEraseCarry,mapBit,eraseBorrow,eraseCarry,
        renameProgram,renameInstr,renameCorrection]

theorem mappedSum_natural (f : Wire → Wire) (b : MappedBit) (y c : Wire) :
    renameProgram f (mappedSum b y c)=mappedSum (mapBit f b) (f y) (f c) := by
  cases b with
  | mk a flip =>
    cases a <;> cases flip <;> simp [mappedSum,mapBit,renameProgram,renameInstr]

theorem flipBelow_natural (f : Wire → Wire) (c : Option Wire) (top t : Wire) :
    renameProgram f (flipBelow c top t)=flipBelow (c.map f) (f top) (f t) := by
  cases c <;> rfl

theorem notRegister_natural (f : Wire → Wire) (r : List Wire) :
    renameProgram f (notRegister r)=notRegister (r.map f) := by
  simp only [notRegister,renameProgram,List.map_map,Function.comp_def,renameInstr]

theorem signComplement_natural (f : Wire → Wire) (q : Wire) (r : List Wire) :
    renameProgram f (signComplement q r)=signComplement (f q) (r.map f) := by
  simp only [signComplement,renameProgram,List.map_map,Function.comp_def,renameInstr]

theorem swapBits_natural (f : Wire → Wire) (a b : Wire) :
    renameProgram f (swapBits a b)=swapBits (f a) (f b) := rfl

theorem selectWindow_natural (f : Wire → Wire) (b src flag : Wire)
    (constant : Bool) (body : Program) :
    renameProgram f (transcriptSelectWindow b src flag constant body)=
      transcriptSelectWindow (f b) (f src) (f flag) constant (renameProgram f body) := by
  cases constant <;>
    simp [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,renameProgram,renameInstr,renameCorrection]

end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/FieldRenameRegisters.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename

theorem copyRegister_natural (f : Wire → Wire) (c : Option Wire) (a b : List Wire) :
    renameProgram f (copyRegister c a b)=copyRegister (c.map f) (a.map f) (b.map f) := by
  induction a generalizing b with
  | nil => simp [copyRegister,renameProgram]
  | cons a as ih =>
    cases b with
    | nil => simp [copyRegister,renameProgram]
    | cons b bs =>
      simp only [copyRegister,List.map_cons,rename_append,ih]
      cases c <;> rfl

theorem swapRegisters_natural (f : Wire → Wire) (c : Wire) (a b : List Wire) :
    renameProgram f (swapRegisters c a b)=swapRegisters (f c) (a.map f) (b.map f) := by
  simp only [swapRegisters,rename_append,copyRegister_natural,Option.map_none,Option.map_some]

theorem addInPlace_natural (f : Wire → Wire) (a b carry : List Wire) (cin : Wire) :
    renameProgram f (addInPlace a b carry cin)=addInPlace (a.map f) (b.map f) (carry.map f) (f cin) := by
  induction a generalizing b carry cin with
  | nil => simp [addInPlace,renameProgram]
  | cons a as ih =>
    cases as with
    | nil =>
      cases b with
      | nil => simp [addInPlace,renameProgram]
      | cons b bs => cases bs <;> simp [addInPlace,renameProgram,renameInstr]
    | cons a' as =>
      cases b with
      | nil => simp [addInPlace,renameProgram]
      | cons b bs =>
        cases bs with
        | nil => simp [addInPlace,renameProgram]
        | cons b' bs =>
          cases carry with
          | nil => simp [addInPlace,renameProgram]
          | cons c cs =>
            simp only [addInPlace,List.map_cons,rename_append,majority_natural,
              eraseCarry_natural,ih]
            rfl

theorem subInPlace_natural (f : Wire → Wire) (a b carry : List Wire) (cin : Wire) :
    renameProgram f (subInPlace a b carry cin)=subInPlace (a.map f) (b.map f) (carry.map f) (f cin) := by
  simp only [subInPlace,rename_append,notRegister_natural,addInPlace_natural]

theorem mappedAdd_natural (f : Wire → Wire) (a : List MappedBit) (b carry : List Wire) (cin : Wire) :
    renameProgram f (mappedAdd a b carry cin)=
      mappedAdd (a.map (mapBit f)) (b.map f) (carry.map f) (f cin) := by
  induction a generalizing b carry cin with
  | nil => simp [mappedAdd,renameProgram]
  | cons a as ih =>
    cases as with
    | nil =>
      cases b with
      | nil => simp [mappedAdd,renameProgram]
      | cons b bs =>
        cases bs with
        | nil => simpa only [mappedAdd,List.map_cons,List.map_nil] using mappedSum_natural f a b cin
        | cons b' bs => simp [mappedAdd,renameProgram]
    | cons a' as =>
      cases b with
      | nil => simp [mappedAdd,renameProgram]
      | cons b bs =>
        cases bs with
        | nil => simp [mappedAdd,renameProgram]
        | cons b' bs =>
          cases carry with
          | nil => simp [mappedAdd,renameProgram]
          | cons c cs =>
            simp only [mappedAdd,List.map_cons,rename_append,mappedMajority_natural,
              mappedEraseCarry_natural,mappedSum_natural,ih]

theorem mappedSub_natural (f : Wire → Wire) (a : List MappedBit) (b carry : List Wire) (cin : Wire) :
    renameProgram f (mappedSub a b carry cin)=
      mappedSub (a.map (mapBit f)) (b.map f) (carry.map f) (f cin) := by
  simp only [mappedSub,rename_append,notRegister_natural,mappedAdd_natural]

theorem rotate_natural (f : Wire → Wire) (r : List Wire) :
    renameProgram f (rotateRight r)=rotateRight (r.map f) ∧
    renameProgram f (rotateLeft r)=rotateLeft (r.map f) := by
  induction r with
  | nil => simp [rotateRight,rotateLeft,renameProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,renameProgram]
    | cons b bs =>
      simp only [rotateRight,rotateLeft,List.map_cons,rename_append,swapBits_natural,ih.1,ih.2]
      constructor <;> trivial

theorem rotateRight_natural (f : Wire → Wire) (r : List Wire) :
    renameProgram f (rotateRight r)=rotateRight (r.map f) := (rotate_natural f r).1
theorem rotateLeft_natural (f : Wire → Wire) (r : List Wire) :
    renameProgram f (rotateLeft r)=rotateLeft (r.map f) := (rotate_natural f r).2

end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/FieldRenameOffset.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry majority eraseCarry

theorem prepareSign_natural (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    renameProgram f (BalancedCleanup.prepareSign L)=BalancedCleanup.prepareSign (mapCleanup f L) := by
  simp only [BalancedCleanup.prepareSign,rename_append,signComplement_natural]
  simp only [mapCleanup,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.map_cons,List.map_append]
  rfl

theorem offset_view_natural (f : Wire → Wire) (L : BalancedCleanupOffset.Layout) :
    renameProgram f (BalancedCleanupOffset.view L)=BalancedCleanupOffset.view (mapOffset f L) := by
  simp only [BalancedCleanupOffset.view,rename_append,rotateLeft_natural,signComplement_natural]
  simp only [mapOffset,mapCircuit,mapCleanup,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.map_cons,List.map_append]
  rfl

end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/FieldRenameMeasuredChain.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
open BalancedCleanupOffset

attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry majority eraseCarry

private theorem measured_prepareHead_natural (f : Wire → Wire) (b : MappedBit)
    (a y cinC cinB c d : Wire) :
    renameProgram f (prepareHead b a y cinC cinB c d) =
      prepareHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) := by
  simp only [prepareHead,rename_append,mappedMajority_natural,mappedSum_natural,
    majority_natural]
  rfl

private theorem measured_releaseHead_natural (f : Wire → Wire) (b : MappedBit)
    (a y cinC cinB c d : Wire) :
    renameProgram f (releaseHead b a y cinC cinB c d) =
      releaseHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) := by
  simp only [releaseHead,rename_append,eraseCarry_natural,mappedSum_natural,
    mappedEraseCarry_natural]
  rfl

private theorem measured_terminal_natural (f : Wire → Wire) (a y cin target : Wire) :
    renameProgram f (TerminalParityMeasure.program a y cin target)=
      TerminalParityMeasure.program (f a) (f y) (f cin) (f target) := by
  simp only [TerminalParityMeasure.program,rename_append,eraseCarry_natural]
  rfl

/-- Relabel the actual shortened final branch as well as all ordinary heads.
Aligned lengths are sufficient for every production-width call. -/
theorem measured_offset_chain_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    renameProgram f (TerminalParityMeasure.chain bits xs ys cs ds cinC cinB target) =
      TerminalParityMeasure.chain (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f cinC) (f cinB) (f target) := by
  induction ys generalizing bits xs cs ds cinC cinB with
  | nil =>
    have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    simpa only [TerminalParityMeasure.chain,List.map_nil,Option.map_none] using
      (flipBelow_natural f none cinB target)
  | cons y ys ih =>
    cases bits with
    | nil => simp at hb
    | cons b bits =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          cases ds with
          | nil => simp at hd
          | cons d ds =>
            cases ys with
            | nil =>
              have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
              have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
              have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
              have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
              subst bits xs cs ds
              simp only [TerminalParityMeasure.chain,TerminalParityMeasure.leaf,List.map_cons,List.map_nil,
                rename_append,mappedSum_natural,measured_terminal_natural]
              rfl
            | cons y' ys =>
              cases bits with
              | nil => simp at hb
              | cons b' bits =>
                have tail := ih (b'::bits) xs cs ds c d
                  (by simpa using hb) (by simpa using hx)
                  (by simpa using hc) (by simpa using hd)
                change renameProgram f
                    (prepareHead b a y cinC cinB c d ++
                      TerminalParityMeasure.chain (b'::bits) xs (y'::ys) cs ds c d target ++
                      releaseHead b a y cinC cinB c d) =
                  prepareHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) ++
                    TerminalParityMeasure.chain ((b'::bits).map (mapBit f))
                      (xs.map f) ((y'::ys).map f) (cs.map f) (ds.map f)
                      (f c) (f d) (f target) ++
                    releaseHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d)
                simp only [rename_append,measured_prepareHead_natural,measured_releaseHead_natural,tail]

end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/FieldRenameMeasuredOffset.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
open BalancedCleanupOffset
attribute [local irreducible] TerminalParityMeasure.chain majority eraseCarry

private theorem mapped_tail {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).tail=xs.tail.map f := by cases xs <;> rfl

/-- A default wire is never read on the proven production-width input. -/
private theorem mapped_head (f : Wire → Wire) (xs : List Wire) (h : xs≠[]) :
    (xs.map f).headD 0=f (xs.headD 0) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

/-- Rename the actual first-bit omission and the unchanged slim tail. -/
theorem measured_zero_head_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (a y cinC cinB d target : Wire)
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    renameProgram f (TerminalParityZeroHead.program bits xs ys cs ds a y cinC cinB d target)=
      TerminalParityZeroHead.program (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f a) (f y) (f cinC) (f cinB) (f d) (f target) := by
  have tail := measured_offset_chain_natural f bits xs ys cs ds cinC d target hb hx hc hd
  simp only [TerminalParityZeroHead.program,rename_append,majority_natural,
    eraseCarry_natural,tail]
  rfl

/-- The actual mapped lists have256 entries, so headD defaults cannot cause
an invalid assumption that the relabeling fixes physical wire0. -/
theorem measured_zero_offset_core_natural (f : Wire → Wire) (L : Layout) (hw : L.Widths) :
    renameProgram f (TerminalParityOffset.core L)=
      TerminalParityOffset.core (mapOffset f L) := by
  have widths := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  have co : L.offsetCarry.length=256 := hw.2
  have hy : L.y≠[] := by intro h; simp [h] at widths
  have hr : L.r≠[] := by intro h; simp [h] at widths
  have hc : L.carry≠[] := by intro h; simp [h] at cy
  have bitlen : (offsetBits L).tail.length=255 := by rw [List.length_tail,offsetBits_length]
  have ylen : L.y.tail.length=255 := by rw [List.length_tail,widths.2.2.1]
  have rlen : L.r.tail.length=255 := by rw [List.length_tail,widths.2.1]
  have clen : L.offsetCarry.tail.length=255 := by rw [List.length_tail,co]
  have dlen : L.carry.tail.length=255 := by rw [List.length_tail,cy]
  have ym : (mapOffset f L).y=L.y.map f := y_map f L.toCircuit.toLayout
  have rm : (mapOffset f L).r=L.r.map f := r_map f L.toCircuit.toLayout
  have cm : (mapOffset f L).offsetCarry=L.offsetCarry.map f := rfl
  have dm : (mapOffset f L).carry=L.carry.map f := rfl
  have natural := measured_zero_head_natural f (offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail (L.y.headD 0) (L.r.headD 0) L.one L.cout
    (L.carry.headD 0) L.parity (by omega) (by omega) (by omega) (by omega)
  simp only [TerminalParityOffset.core,natural,ym,rm,cm,dm,←offsetBits_map,
    mapped_tail,mapped_head f L.y hy,mapped_head f L.r hr,mapped_head f L.carry hc]
  rfl

private theorem measured_zero_front_natural (f : Wire → Wire) (L : Layout) :
    renameProgram f (front L)=front (mapOffset f L) := by
  simp only [front,rename_append,prepareSign_natural,offset_view_natural]
  rfl

/-- Exact instruction-list equality for the actual510-T/M cleanup.
No injectivity or phase premise is needed for structural relabeling. -/
theorem measured_zero_offset_program_natural (f : Wire → Wire) (L : Layout) (hw : L.Widths) :
    renameProgram f (TerminalParityOffset.program L)=
      TerminalParityOffset.program (mapOffset f L) := by
  simp only [TerminalParityOffset.program,rename_append,rename_reverse,
    measured_zero_front_natural,measured_zero_offset_core_natural f L hw]
end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/FieldRenameOffsetSlim.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
open BalancedCleanupOffset

attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry majority eraseCarry

private theorem slim_prepareHead_natural (f : Wire → Wire) (b : MappedBit)
    (a y cinC cinB c d : Wire) :
    renameProgram f (prepareHead b a y cinC cinB c d) =
      prepareHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) := by
  simp only [prepareHead,rename_append,mappedMajority_natural,mappedSum_natural,
    majority_natural]
  rfl

private theorem slim_releaseHead_natural (f : Wire → Wire) (b : MappedBit)
    (a y cinC cinB c d : Wire) :
    renameProgram f (releaseHead b a y cinC cinB c d) =
      releaseHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) := by
  simp only [releaseHead,rename_append,eraseCarry_natural,mappedSum_natural,
    mappedEraseCarry_natural]
  rfl

private theorem slim_compare_singleton_natural (f : Wire → Wire)
    (a y d cin target : Wire) :
    renameProgram f (compareChain none [a] [y] [d] cin target) =
      compareChain none [f a] [f y] [f d] (f cin) (f target) := by
  simp only [compareChain,rename_append,majority_natural,eraseCarry_natural,
    flipBelow_natural,Option.map_none]

/-- Relabel the actual shortened final branch as well as all ordinary heads.
Aligned lengths are sufficient for every production-width call. -/
theorem slim_offset_chain_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    renameProgram f (BalancedCleanupOffsetSlim.chain bits xs ys cs ds cinC cinB target) =
      BalancedCleanupOffsetSlim.chain (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f cinC) (f cinB) (f target) := by
  induction ys generalizing bits xs cs ds cinC cinB with
  | nil =>
    have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    simpa only [BalancedCleanupOffsetSlim.chain,List.map_nil,Option.map_none] using
      (flipBelow_natural f none cinB target)
  | cons y ys ih =>
    cases bits with
    | nil => simp at hb
    | cons b bits =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          cases ds with
          | nil => simp at hd
          | cons d ds =>
            cases ys with
            | nil =>
              have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
              have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
              have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
              have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
              subst bits xs cs ds
              simp only [BalancedCleanupOffsetSlim.chain,List.map_cons,List.map_nil,
                rename_append,mappedSum_natural,slim_compare_singleton_natural]
              rfl
            | cons y' ys =>
              cases bits with
              | nil => simp at hb
              | cons b' bits =>
                have tail := ih (b'::bits) xs cs ds c d
                  (by simpa using hb) (by simpa using hx)
                  (by simpa using hc) (by simpa using hd)
                change renameProgram f
                    (prepareHead b a y cinC cinB c d ++
                      BalancedCleanupOffsetSlim.chain (b'::bits) xs (y'::ys) cs ds c d target ++
                      releaseHead b a y cinC cinB c d) =
                  prepareHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) ++
                    BalancedCleanupOffsetSlim.chain ((b'::bits).map (mapBit f))
                      (xs.map f) ((y'::ys).map f) (cs.map f) (ds.map f)
                      (f c) (f d) (f target) ++
                    releaseHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d)
                simp only [rename_append,slim_prepareHead_natural,slim_releaseHead_natural,tail]

private theorem slim_front_natural (f : Wire → Wire) (L : Layout) :
    renameProgram f (front L)=front (mapOffset f L) := by
  simp only [front,rename_append,prepareSign_natural,offset_view_natural]
  rfl

attribute [local irreducible] BalancedCleanupOffsetSlim.chain

end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/FieldRenameOffsetZero.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
open BalancedCleanupOffset
attribute [local irreducible] BalancedCleanupOffsetSlim.chain majority eraseCarry

private theorem mapped_tail_FieldRenameOffsetZero {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).tail=xs.tail.map f := by cases xs <;> rfl

/-- A default wire is never read on the proven production-width input. -/
private theorem mapped_head_FieldRenameOffsetZero (f : Wire → Wire) (xs : List Wire) (h : xs≠[]) :
    (xs.map f).headD 0=f (xs.headD 0) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

/-- Rename the actual first-bit omission and the unchanged slim tail. -/
theorem zero_head_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (a y cinC cinB d target : Wire)
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    renameProgram f (BalancedCleanupOffsetZeroHead.program bits xs ys cs ds a y cinC cinB d target)=
      BalancedCleanupOffsetZeroHead.program (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f a) (f y) (f cinC) (f cinB) (f d) (f target) := by
  have tail := slim_offset_chain_natural f bits xs ys cs ds cinC d target hb hx hc hd
  simp only [BalancedCleanupOffsetZeroHead.program,rename_append,majority_natural,
    eraseCarry_natural,tail]
  rfl

/-- The actual mapped lists have256 entries, so headD defaults cannot cause
an invalid assumption that the relabeling fixes physical wire0. -/
theorem zero_offset_core_natural (f : Wire → Wire) (L : Layout) (hw : L.Widths) :
    renameProgram f (BalancedCleanupOffsetZero.core L)=
      BalancedCleanupOffsetZero.core (mapOffset f L) := by
  have widths := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  have co : L.offsetCarry.length=256 := hw.2
  have hy : L.y≠[] := by intro h; simp [h] at widths
  have hr : L.r≠[] := by intro h; simp [h] at widths
  have hc : L.carry≠[] := by intro h; simp [h] at cy
  have bitlen : (offsetBits L).tail.length=255 := by rw [List.length_tail,offsetBits_length]
  have ylen : L.y.tail.length=255 := by rw [List.length_tail,widths.2.2.1]
  have rlen : L.r.tail.length=255 := by rw [List.length_tail,widths.2.1]
  have clen : L.offsetCarry.tail.length=255 := by rw [List.length_tail,co]
  have dlen : L.carry.tail.length=255 := by rw [List.length_tail,cy]
  have ym : (mapOffset f L).y=L.y.map f := y_map f L.toCircuit.toLayout
  have rm : (mapOffset f L).r=L.r.map f := r_map f L.toCircuit.toLayout
  have cm : (mapOffset f L).offsetCarry=L.offsetCarry.map f := rfl
  have dm : (mapOffset f L).carry=L.carry.map f := rfl
  have natural := zero_head_natural f (offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail (L.y.headD 0) (L.r.headD 0) L.one L.cout
    (L.carry.headD 0) L.parity (by omega) (by omega) (by omega) (by omega)
  simp only [BalancedCleanupOffsetZero.core,natural,ym,rm,cm,dm,←offsetBits_map,
    mapped_tail_FieldRenameOffsetZero,mapped_head_FieldRenameOffsetZero f L.y hy,mapped_head_FieldRenameOffsetZero f L.r hr,mapped_head_FieldRenameOffsetZero f L.carry hc]
  rfl

private theorem zero_front_natural (f : Wire → Wire) (L : Layout) :
    renameProgram f (front L)=front (mapOffset f L) := by
  simp only [front,rename_append,prepareSign_natural,offset_view_natural]
  rfl

/-- Exact instruction-list equality for the actual510-T/M cleanup.
No injectivity or phase premise is needed for structural relabeling. -/
theorem zero_offset_program_natural (f : Wire → Wire) (L : Layout) (hw : L.Widths) :
    renameProgram f (BalancedCleanupOffsetZero.program L)=
      BalancedCleanupOffsetZero.program (mapOffset f L) := by
  simp only [BalancedCleanupOffsetZero.program,rename_append,rename_reverse,
    zero_front_natural,zero_offset_core_natural f L hw]
end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/FieldRenameKernels.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] addInPlace subInPlace mappedAdd mappedSub
  rotateRight rotateLeft signComplement BalancedCircuit.foldBits
  BalancedCircuit.rawSource BalancedCircuit.rawTarget BalancedCircuit.foldTarget

theorem seedViews_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow ≠ []) :
    renameProgram f (BalancedCircuit.seedViews L)=BalancedCircuit.seedViews (mapCircuit f L) := by
  simp only [BalancedCircuit.seedViews,mapCircuit,mapCleanup,first_source_map f L.ylow hy,
    renameProgram,List.map_cons,List.map_nil,renameInstr]

theorem rawAdd_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedCircuit.rawAdd L)=BalancedCircuit.rawAdd (mapCircuit f L) := by
  simp only [BalancedCircuit.rawAdd,rename_append,signComplement_natural,addInPlace_natural,
    rawSource_map,rawTarget_map]
  rfl

theorem prepareFold_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedCircuit.prepareFold L)=BalancedCircuit.prepareFold (mapCircuit f L) := by
  simp only [BalancedCircuit.prepareFold,mapCircuit,mapCleanup,renameProgram,
    List.map_cons,List.map_nil,renameInstr]

theorem fold_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedCircuit.fold L)=BalancedCircuit.fold (mapCircuit f L) := by
  simp only [BalancedCircuit.fold,rename_append,mappedAdd_natural,foldBits_map,foldTarget_map,
    List.map_append,List.map_cons,List.map_nil]
  rfl

theorem releaseSelectors_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedCircuit.releaseSelectors L)=
      BalancedCircuit.releaseSelectors (mapCircuit f L) := by
  simp only [BalancedCircuit.releaseSelectors,mapCircuit,mapCleanup,renameProgram,
    List.map_cons,List.map_nil,renameInstr,renameCorrection]

theorem coreProgram_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow ≠ []) :
    renameProgram f (BalancedCircuit.coreProgram L)=BalancedCircuit.coreProgram (mapCircuit f L) := by
  simp only [BalancedCircuit.coreProgram,rename_append,seedViews_natural f L hy,
    rawAdd_natural,prepareFold_natural,fold_natural,rotateRight_natural,rawTarget_map,
    releaseSelectors_natural]

theorem recoverSelectors_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedInverse.recoverSelectors L)=
      BalancedInverse.recoverSelectors (mapCircuit f L) := by
  simp only [BalancedInverse.recoverSelectors,mapCircuit,mapCleanup,renameProgram,
    List.map_cons,List.map_nil,renameInstr]

theorem undoFold_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedInverse.undoFold L)=BalancedInverse.undoFold (mapCircuit f L) := by
  simp only [BalancedInverse.undoFold,rename_append,mappedSub_natural,foldBits_map,foldTarget_map,
    List.map_append,List.map_cons,List.map_nil]
  rfl

theorem undoPreparation_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedInverse.undoPreparation L)=
      BalancedInverse.undoPreparation (mapCircuit f L) := by
  simp only [BalancedInverse.undoPreparation,mapCircuit,mapCleanup,renameProgram,
    List.map_cons,List.map_nil,renameInstr,renameCorrection]

theorem rawSubtract_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedInverse.rawSubtract L)=BalancedInverse.rawSubtract (mapCircuit f L) := by
  simp only [BalancedInverse.rawSubtract,rename_append,signComplement_natural,subInPlace_natural,
    rawSource_map,rawTarget_map]
  rfl

theorem inverse_tail_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow ≠ []) :
    renameProgram f (OffsetBorrowedInverse.tail L)=OffsetBorrowedInverse.tail (mapCircuit f L) := by
  simp only [OffsetBorrowedInverse.tail,rename_append,rename_reverse,recoverSelectors_natural,
    rotateLeft_natural,rawTarget_map,undoFold_natural,undoPreparation_natural,rawSubtract_natural,
    seedViews_natural f L hy]

private theorem shared_ylow_nonempty (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).ylow ≠ [] := by
  intro h
  have len := (balancedSharedPorts_widths w sign).2.1
  rw [h] at len
  contradiction

theorem forward_program_natural (f w : Wire → Wire) (sign : Wire) :
    renameProgram f (OffsetBorrowedField.program w sign)=
      OffsetBorrowedField.program (f ∘ w) (f sign) := by
  simp only [OffsetBorrowedField.program,rename_append,
    coreProgram_natural f _ (shared_ylow_nonempty w sign),sharedPorts_map,
    measured_zero_offset_program_natural f _ (OffsetCleanupBorrowedCaller.widths w sign),callerLayout_map]
  rfl

theorem inverse_program_natural (f w : Wire → Wire) (sign : Wire) :
    renameProgram f (OffsetBorrowedInverse.program w sign)=
      OffsetBorrowedInverse.program (f ∘ w) (f sign) := by
  simp only [OffsetBorrowedInverse.program,OffsetBorrowedInverse.recoverParity,rename_append,
    zero_offset_program_natural f _ (OffsetCleanupBorrowedCaller.widths w sign),callerLayout_map,
    inverse_tail_natural f _ (shared_ylow_nonempty w sign),sharedPorts_map]
  rfl

end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedFieldReplay.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation Secp256k1
attribute [local irreducible] wires OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] dblInPlace halfInPlace copyRegister
attribute [local irreducible] addInPlace subInPlace compareLt

def logicalCell (divide : Bool) (i : Nat) : Program :=
  let unit := mixedTranscriptUnitTrace.getD i (false,false)
  if divide then OffsetBorrowedCanonical.cell id 2400 i (1028+i) 2409 2410 unit.1 unit.2
  else OffsetBorrowedInverseCanonical.cell id 2400 i (1028+i) 2409 2410 unit.1 unit.2

private theorem shared_live (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : live q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold live
  omega

private theorem shared_site (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : fieldSite q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold fieldSite
  omega

private theorem inventory_live (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) : live q := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact shared_live q h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    unfold live
    omega
  · exact packet_live j q hj h

theorem mappedCell_support (divide : Bool) (j i : Nat) (hj : j < 170)
    (hi0 : 3*j ≤ i) (hi : i < 3*j+3) :
    wires (renameProgram (placed j) (logicalCell divide i))⊆slots.toFinset := by
  have g : i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have s : 1028+i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    unfold H
    omega
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 (groupInventory j).toFinset
    (by intro q hq; simp only [groupInventory,List.mem_toFinset,List.mem_append];
        exact Or.inl (Or.inl (List.mem_toFinset.mp hq)))
    (by simp [groupInventory]) (by simp [groupInventory,g])
    (by simp [groupInventory,s]) (by simp [groupInventory])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈groupInventory j := by
    cases divide
    · exact List.mem_toFinset.mp (body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw))
    · exact List.mem_toFinset.mp (body.1 (by simpa only [logicalCell,if_true] using hraw))
  exact slot_mem _ (pi_live j old hj (inventory_live j old hj belongs)) (inventory_safe j old hj belongs)

def mappedGroup (divide : Bool) (j : Nat) : Program :=
  compressedHistoryDecode (placed j) (3*j) ++
  (if divide then renameProgram (placed j) (logicalCell divide (3*j)) ++
      renameProgram (placed j) (logicalCell divide (3*j+1)) ++
      renameProgram (placed j) (logicalCell divide (3*j+2))
   else renameProgram (placed j) (logicalCell divide (3*j+2)) ++
      renameProgram (placed j) (logicalCell divide (3*j+1)) ++
      renameProgram (placed j) (logicalCell divide (3*j))) ++
  compressedHistoryEncode (placed j) (3*j)

theorem mappedGroup_support (divide : Bool) (j : Nat) (hj : j < 170) :
    wires (mappedGroup divide j)⊆slots.toFinset := by
  have codec := codec_support j hj
  have a := mappedCell_support divide j (3*j) hj (by omega) (by omega)
  have b := mappedCell_support divide j (3*j+1) hj (by omega) (by omega)
  have c := mappedCell_support divide j (3*j+2) hj (by omega) (by omega)
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff,and_assoc]
  · exact ⟨codec.2,c,b,a,codec.1⟩
  · exact ⟨codec.2,a,b,c,codec.1⟩

def mappedGroups (divide : Bool) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if divide then mappedGroup divide j++mappedGroups divide (j+1) n
    else mappedGroups divide (j+1) n++mappedGroup divide j

theorem mappedGroups_support (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    wires (mappedGroups divide j n)⊆slots.toFinset := by
  induction n generalizing j with
  | zero => simp [mappedGroups,wires]
  | succ n ih =>
    have current := mappedGroup_support divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.union_subset_iff]
    · exact ⟨rest,current⟩
    · exact ⟨current,rest⟩

private theorem tail_support (divide : Bool) (i : Nat) (hi : i=510 ∨ i=511) :
    wires (renameProgram allPlaced (logicalCell divide i))⊆slots.toFinset := by
  let W := (CompressedFieldSupport.sharedSites id 2409++[2400,2410,i,1028+i]).toFinset
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 W
    (by intro q hq; simp only [W,List.mem_toFinset,List.mem_append]; exact Or.inl (List.mem_toFinset.mp hq))
    (by simp [W]) (by simp [W]) (by simp [W]) (by simp [W])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈W := by
    cases divide
    · exact body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw)
    · exact body.1 (by simpa only [logicalCell,if_true] using hraw)
  have bounds : 510 ≤ i ∧ i ≤ 511 := by omega
  simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,or_assoc] at belongs
  have hl : live old := by
    rcases belongs with h|rfl|rfl|rfl|rfl
    · exact shared_live old h
    all_goals unfold live; omega
  have nh : ¬holeRegion old := by
    rcases belongs with h|rfl|rfl|rfl|rfl
    · exact field_not_hole old (shared_site old h)
    all_goals unfold holeRegion; omega
  exact slot_mem _ (pi0_live old hl) (nonhole_pi0_safe old nh)

def mappedReplay (divide : Bool) : Program :=
  if divide then mappedGroups divide 0 170++renameProgram allPlaced (logicalCell divide 510)++
      renameProgram allPlaced (logicalCell divide 511)
  else renameProgram allPlaced (logicalCell divide 511)++
      renameProgram allPlaced (logicalCell divide 510)++mappedGroups divide 0 170

theorem mappedReplay_support (divide : Bool) : wires (mappedReplay divide)⊆slots.toFinset := by
  have groups := mappedGroups_support divide 0 170 (by omega)
  have a := tail_support divide 510 (by omega)
  have b := tail_support divide 511 (by omega)
  cases divide <;> simp only [mappedReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff,and_assoc]
  · exact ⟨b,a,groups⟩
  · exact ⟨groups,a,b⟩

private theorem convert_site (target : Bool) (q : Nat)
    (h : q∈(if target then balancedSharedTargetConvert id else balancedSharedSourceConvert id).wires) :
    fieldSite q := by
  cases target <;> simp only [Bool.false_eq_true,if_false,if_true,
    balancedSharedTargetConvert,balancedSharedSourceConvert,BalancedConvert.Layout.wires,
    wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  all_goals dsimp only [id] at h; unfold fieldSite; omega

def converterPair (canonical : Bool) : Program :=
  if canonical then BalancedConvert.canonical (balancedSharedTargetConvert id)++
    BalancedConvert.canonical (balancedSharedSourceConvert id)
  else BalancedConvert.center (balancedSharedTargetConvert id)++
    BalancedConvert.center (balancedSharedSourceConvert id)

theorem converters_support (canonical : Bool) :
    wires (renameProgram allPlaced (converterPair canonical))⊆slots.toFinset := by
  have target := BalancedConvert.support (balancedSharedTargetConvert id)
  have source := BalancedConvert.support (balancedSharedSourceConvert id)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have site : fieldSite old := by
    cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at hraw
    · rcases hraw with h|h
      · exact convert_site true old (List.mem_toFinset.mp (target.1 h))
      · exact convert_site false old (List.mem_toFinset.mp (source.1 h))
    · rcases hraw with h|h
      · exact convert_site true old (List.mem_toFinset.mp (target.2 h))
      · exact convert_site false old (List.mem_toFinset.mp (source.2 h))
  exact allPlaced_field_mem old site

theorem copy_support : wires (renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))⊆slots.toFinset := by
  have zword : (skywalkSharedField id).z=wireBlock id 2056 257 := skywalkShared_field_z id
  have aword : (skywalkSharedField id).a=wireBlock id 770 257 := rfl
  have cp := copyRegister_wires_subset none (skywalkSharedField id).z (skywalkSharedField id).a
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member := cp hraw
  rw [zword,aword] at member
  have site : fieldSite old := by
    simp only [List.mem_toFinset,Option.toList_none,List.nil_append,wireBlock,List.map_id,
      List.mem_append,List.mem_range'_1] at member
    unfold fieldSite
    omega
  exact allPlaced_field_mem old site

def fieldSegment (divide : Bool) : Program :=
  (if divide then renameProgram allPlaced (dblInPlace (borrowedSkywalkUnary id) p)
   else renameProgram allPlaced (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))++
  renameProgram allPlaced (converterPair false)++mappedReplay divide++
  renameProgram allPlaced (converterPair true)++
  (if divide then renameProgram allPlaced (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)
   else renameProgram allPlaced (halfInPlace (borrowedSkywalkUnary id) p))

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/FieldRenameCells.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] OffsetBorrowedField.program OffsetBorrowedInverse.program
  swapRegisters transcriptSelectWindow

theorem shared_r_map (f w : Wire → Wire) (sign : Wire) :
    (balancedSharedPorts (f ∘ w) (f sign)).r=(balancedSharedPorts w sign).r.map f := by
  have h := congrArg (fun L : BalancedCircuit.Layout => L.r) (sharedPorts_map f w sign)
  simpa only [mapCircuit,r_map] using h.symm

theorem shared_y_map (f w : Wire → Wire) (sign : Wire) :
    (balancedSharedPorts (f ∘ w) (f sign)).y=(balancedSharedPorts w sign).y.map f := by
  have h := congrArg (fun L : BalancedCircuit.Layout => L.y) (sharedPorts_map f w sign)
  simpa only [mapCircuit,y_map] using h.symm

theorem forward_body_natural (f w : Wire → Wire) (sign effS : Wire) :
    renameProgram f (OffsetBorrowedCanonical.body w sign effS)=
      OffsetBorrowedCanonical.body (f ∘ w) (f sign) (f effS) := by
  simp only [OffsetBorrowedCanonical.body,rename_append,forward_program_natural,
    swapRegisters_natural,shared_r_map,shared_y_map]
  rfl

theorem inverse_double_natural (f w : Wire → Wire) (sign : Wire) :
    renameProgram f (OffsetBorrowedInverseCanonical.double w sign)=
      OffsetBorrowedInverseCanonical.double (f ∘ w) (f sign) := by
  simp only [OffsetBorrowedInverseCanonical.double,rename_append,inverse_program_natural]
  rfl

theorem inverse_body_natural (f w : Wire → Wire) (sign effS : Wire) :
    renameProgram f (OffsetBorrowedInverseCanonical.body w sign effS)=
      OffsetBorrowedInverseCanonical.body (f ∘ w) (f sign) (f effS) := by
  simp only [OffsetBorrowedInverseCanonical.body,rename_append,swapRegisters_natural,
    shared_r_map,shared_y_map,inverse_double_natural]

theorem forward_cell_natural (f w : Wire → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    renameProgram f (OffsetBorrowedCanonical.cell w b g swap sign effS ig is)=
      OffsetBorrowedCanonical.cell (f ∘ w) (f b) (f g) (f swap) (f sign) (f effS) ig is := by
  simp only [OffsetBorrowedCanonical.cell,selectWindow_natural,forward_body_natural]

theorem inverse_cell_natural (f w : Wire → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    renameProgram f (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is)=
      OffsetBorrowedInverseCanonical.cell (f ∘ w) (f b) (f g) (f swap) (f sign) (f effS) ig is := by
  simp only [OffsetBorrowedInverseCanonical.cell,selectWindow_natural,inverse_body_natural]

/-- Structural relabeling of the actual512-round unit-trace emission.
No primitive or measured arithmetic circuit is expanded at this layer. -/
theorem logical_cell_natural (f : Wire → Wire) (divide : Bool) (i : Nat) :
    renameProgram f (MappedCompressed.logicalCell divide i)=
      (if divide then OffsetBorrowedCanonical.cell f (f 2400) (f i) (f (1028+i))
          (f 2409) (f 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2
       else OffsetBorrowedInverseCanonical.cell f (f 2400) (f i) (f (1028+i))
          (f 2409) (f 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2) := by
  cases divide <;> simp only [MappedCompressed.logicalCell,Bool.false_eq_true,if_false,if_true,
    forward_cell_natural,inverse_cell_natural,Function.comp_id]

end ECDSAAdd.Arithmetic.FieldRename
end

-- source: ECDSAAdd/Arithmetic/EndpointSwapTrimProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.EndpointSwapTrim

/-- Final forward cell: keep the actual G-selected kernel; retire no data
or transcript and omit only the S window proved identity at the endpoint. -/
def forward (w : Nat → Wire) (b g flag : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])

/-- First inverse cell: its input words are equal, so the original preceding
S window is unnecessary. The inverse kernel has independent measurements. -/
def inverse (w : Nat → Wire) (b g flag : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])

theorem counts (w : Nat → Wire) (b g flag : Wire) (ig : Bool) :
    toffoliCount (forward w b g flag ig)=1023 ∧
    measurementCount (forward w b g flag ig)=1024 ∧
    toffoliCount (inverse w b g flag ig)=1024 ∧
    measurementCount (inverse w b g flag ig)=1024 := by
  have f := OffsetBorrowedField.counts w flag
  have i := OffsetBorrowedInverse.counts w flag
  have fw := transcriptSelectWindow_counts b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])
  have iv := transcriptSelectWindow_counts b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])
  simp only [forward,inverse,fw.1,fw.2,iv.1,iv.2,
    toffoliCount_append,measurementCount_append,f.1,f.2,i.1,i.2]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.EndpointSwapTrim
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedSerializedCellProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.OffsetBorrowedSerialized

attribute [local irreducible] OffsetBorrowedField.program OffsetBorrowedInverse.program
  swapRegisters wires

/-- Each window restores flag=false before the next selection. The real field
kernel is surrounded by its existing control-polarity correction. -/
def forward (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag]) ++
  transcriptSelectWindow b swap flag is
    (swapRegisters flag (balancedSharedPorts w flag).r (balancedSharedPorts w flag).y)

end ECDSAAdd.Arithmetic.OffsetBorrowedSerialized
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedSerializedCellProof.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedSerialized
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run BalancedCircuit.program BalancedInverse.program
  OffsetBorrowedField.program OffsetBorrowedInverse.program
theorem half_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run ([.X sign]++OffsetBorrowedField.program w sign++[.X sign]) m s=
      run ([.X sign]++BalancedCircuit.program (balancedSharedPorts w sign)++[.X sign]) m s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway L nd sign (by simp [L,balancedSharedPorts])
  have sa : sign∉L.r ∧ sign∉L.y := ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have se := pair_env w sign hn base s.basis _ _ he h
  generalize eu : run [.X sign] m s=u
  have us := BalancedCleanupOffset.x_run sign s m
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ue : Env w u.basis := by
    rw [us]
    exact env_write w sign ho s.basis (!s.basis sign) se
  have ug : u.basis sign= !base sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.2.1,centerWord_decode]
  have eq := OffsetBorrowedCanonical.kernel_eq w sign hn ho (!base sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m m ug ur uy ue
  simp only [List.append_assoc]
  rw [run_append,run_take]
  change run (OffsetBorrowedField.program w sign++[.X sign]) m
    (run [.X sign] m s)=_
  rw [eu,run_append,run_take,eq]
  rw [run_append,run_take]
  change _=run (BalancedCircuit.program L++[.X sign]) m (run [.X sign] m s)
  rw [eu,run_append,run_take]
  exact zero_records [.X sign] (by simp only [measurementCount]) _ _ _

end ECDSAAdd.Arithmetic.OffsetBorrowedSerialized
end

-- source: ECDSAAdd/Arithmetic/PairFrameUnique.lean
noncomputable section

set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic

/-- Equal exact register words determine every bit occurring in the register.
No disjointness or clean-work hypothesis is needed for this finite fact. -/
theorem regValue_equal_bits (r : List Wire) (s t : BasisState)
    (h : regValue r s=regValue r t) : ∀q∈r,s q=t q := by
  induction r with
  | nil => simp
  | cons a as ih =>
    change (if s a then 1 else 0)+2*regValue as s=
      (if t a then 1 else 0)+2*regValue as t at h
    have head : s a=t a := by
      cases hs : s a <;> cases ht : t a <;>
        simp only [hs,ht,Bool.false_eq_true,if_true,if_false] at h ⊢ <;> omega
    have tail : regValue as s=regValue as t := by
      rw [head] at h
      omega
    intro q hq
    rcases List.mem_cons.mp hq with eq|member
    · simpa only [eq] using head
    · exact ih tail q member

/-- The complete two-register frame has a unique output basis state. -/
theorem PairFrame.unique (r y : List Wire) (base : BasisState) (X Y : Nat)
    (s t : BasisState) (hs : PairFrame r y base X Y s)
    (ht : PairFrame r y base X Y t) : s=t := by
  funext q
  by_cases hr : q∈r
  · exact regValue_equal_bits r s t (hs.1.trans ht.1.symm) q hr
  · by_cases hy : q∈y
    · exact regValue_equal_bits y s t (hs.2.1.trans ht.2.1.symm) q hy
    · exact (hs.2.2 q hr hy).trans (ht.2.2 q hr hy).symm

/-- Independent record streams can be compared through complete frames, rather
than expanding either instruction list. Both programs must prove phase repair. -/
theorem PairFrame.program_eq (r y : List Wire) (base : BasisState) (I J X Y : Nat)
    (p q : Program)
    (hp : Triple (PairFrame r y base I J) p (PairFrame r y base X Y))
    (hq : Triple (PairFrame r y base I J) q (PairFrame r y base X Y))
    (s : State) (mp mq : List Bool) (h : PairFrame r y base I J s.basis) :
    run p mp s=run q mq s := by
  have a := hp s mp h
  have b := hq s mq h
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · exact PairFrame.unique r y base X Y _ _ a.2 b.2

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/EndpointSwapTrimProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EndpointSwapTrim
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run OffsetBorrowedField.program OffsetBorrowedInverse.program
  BalancedCircuit.program BalancedInverse.program

private theorem kernel_frame (divide : Bool) (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkSharedWires w)
    (base : BasisState) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      ([.X sign]++(if divide then OffsetBorrowedField.program w sign
        else OffsetBorrowedInverse.program w sign)++[.X sign])
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then (X+(if base sign then Y else -Y))/2
          else 2*X+(if base sign then -Y else Y))) (centerWord Y)) := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have clean := balancedSharedPorts_clean w sign base he.1 he.2.1
  cases divide
  · have old := balancedTranscriptDouble_frame (balancedSharedPorts w sign)
      (balancedSharedPorts_widths w sign) nd base clean X Y
    intro s m h
    simp only [Bool.false_eq_true,if_false]
    rw [← OffsetBorrowedInverseCanonical.double,
      OffsetBorrowedInverseCanonical.double_eq w sign hn ho base he X Y s m h]
    exact old s m h
  · have old := balancedTranscriptHalf_frame (balancedSharedPorts w sign)
      (balancedSharedPorts_widths w sign) nd base clean X Y
    intro s m h
    simp only [if_true]
    rw [OffsetBorrowedSerialized.half_eq w sign hn ho base he X Y s m h]
    exact old s m h

theorem partial_frame (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkSharedWires w)
    (nd : [b,g,sign].Nodup)
    (hb : b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y)
    (hg : g∉(balancedSharedPorts w sign).r ∧ g∉(balancedSharedPorts w sign).y)
    (hs : sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y)
    (base : BasisState) (hz : base sign=false) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      (if divide then forward w b g sign ig else inverse w b g sign ig)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then (X+(if mixedTranscriptBit base b g ig then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit base b g ig then -Y else Y))) (centerWord Y)) := by
  have body := kernel_frame divide w sign hn ho
    (mixedTranscriptBase base b g sign ig) (env_write w sign ho base _ he) X Y
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at body
  have window := transcriptSelectWindow_pairFrame b g sign ig _ _ nd hb hg hs
    base hz _ _ _ _ _ body
  cases divide <;> simpa only [forward,inverse,Bool.false_eq_true,if_false,if_true] using window

private theorem flags (w : Nat → Wire) (b g swap sign effS : Wire)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS) :
    [b,g,sign].Nodup ∧
    (b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y) ∧
    (g∉(balancedSharedPorts w sign).r ∧ g∉(balancedSharedPorts w sign).y) ∧
    (sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y) := by
  have ctrl := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ctrl
  refine ⟨?_,hl.outside b (by simp),hl.outside g (by simp),
    hl.outside sign (by simp [balancedSharedPorts])⟩
  simp [List.nodup_cons]
  tauto

/-- Equal output coordinates reflect equality at the original final swap
boundary. This algebraic fact does not constrain the selected G or S. -/
theorem forward_dup_of_payload_equal (G S : Bool) (X Y : Fp)
    (h : (skywalkPayloadCell G S (X,Y)).1=(skywalkPayloadCell G S (X,Y)).2) :
    (X+(if G then Y else -Y))/2=Y := by
  cases S with
  | false => simpa only [skywalkPayloadCell,Bool.false_eq_true,if_false] using h
  | true =>
    have eq : Y=(X+(if G then Y else -Y))/2 := by
      simpa only [skywalkPayloadCell,if_true] using h
    exact eq.symm

/-- Forward duplication is required at the swap boundary, not at the input.
The accepted final replay postcondition supplies this equality. G may be either
value: there is no unsupported assumption that the penultimate state is done. -/
theorem forward_oldcell_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hz : base sign=false) (hS : base effS=false) (he : Env w base)
    (X Y : Fp)
    (dup : (X+(if mixedTranscriptBit base b g ig then Y else -Y))/2=Y)
    (s : State) (mNew mOld : List Bool)
    (input : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (forward w b g sign ig) mNew s=
      run (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) mOld s := by
  have f := flags w b g swap sign effS hl
  have fresh := partial_frame true w b g sign ig hn ho f.1 f.2.1 f.2.2.1 f.2.2.2
    base hz he X Y
  simp only [if_true,dup] at fresh
  have old := OffsetBorrowedCanonical.cell_frame w b g swap sign effS ig is
    hn hl ho hoS base hz hS he X Y
  have old' : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (OffsetBorrowedCanonical.cell w b g swap sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord Y) (centerWord Y)) := by
    cases hswap : mixedTranscriptBit base b swap is <;>
      simpa only [skywalkPayloadCell,dup,hswap,if_true,if_false,Bool.false_eq_true] using old
  exact PairFrame.program_eq _ _ base _ _ _ _ _ _ fresh old' s mNew mOld input

/-- Inverse input duplication makes its initial swap identity for arbitrary
selected S; complete frames compare independent measurement streams. -/
theorem inverse_oldcell_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hz : base sign=false) (hS : base effS=false) (he : Env w base)
    (Y : Fp) (s : State) (mNew mOld : List Bool)
    (input : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord Y) (centerWord Y) s.basis) :
    run (inverse w b g sign ig) mNew s=
      run (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) mOld s := by
  have f := flags w b g swap sign effS hl
  have fresh := partial_frame false w b g sign ig hn ho f.1 f.2.1 f.2.2.1 f.2.2.2
    base hz he Y Y
  simp only [Bool.false_eq_true,if_false] at fresh
  have old := OffsetBorrowedInverseCanonical.cell_frame w b g swap sign effS ig is
    hn hl ho hoS base hz hS he Y Y
  have old' : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord Y) (centerWord Y)) (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (2*Y+(if mixedTranscriptBit base b g ig then -Y else Y))) (centerWord Y)) := by
    cases hswap : mixedTranscriptBit base b swap is <;>
      simpa only [skywalkPayloadUncell,hswap,if_true,if_false,Bool.false_eq_true] using old
  exact PairFrame.program_eq _ _ base _ _ _ _ _ _ fresh old' s mNew mOld input

end ECDSAAdd.Arithmetic.EndpointSwapTrim
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedReplayCounts.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1
attribute [local irreducible] logicalCell dblInPlace halfInPlace copyRegister
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] toffoliCount measurementCount

private theorem renameT (f : Wire → Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem renameM (f : Wire → Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

private theorem swap_nd :
    (2410::(balancedSharedPorts id 2409).r++(balancedSharedPorts id 2409).y).Nodup := by
  rw [balancedSharedPorts_r,balancedSharedPorts_y]
  simp only [wireBlock,List.map_id]
  apply List.nodup_cons.mpr
  constructor
  · intro h
    rcases List.mem_append.mp h with h|h
    all_goals have bound := List.mem_range'_1.mp h; omega
  · apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hr hy
    simp only [List.mem_range'_1] at hr hy
    omega

theorem logicalCell_counts (divide : Bool) (i : Nat) :
    toffoliCount (logicalCell divide i)=(if divide then 1280 else 1281) ∧ measurementCount (logicalCell divide i)=1025 := by
  cases divide <;> simp only [logicalCell,Bool.false_eq_true,if_false,if_true]
  · exact OffsetBorrowedInverseCanonical.cell_counts id 2400 i (1028+i) 2409 2410
      (mixedTranscriptUnitTrace.getD i (false,false)).1
      (mixedTranscriptUnitTrace.getD i (false,false)).2 swap_nd
  · exact OffsetBorrowedCanonical.cell_counts id 2400 i (1028+i) 2409 2410
      (mixedTranscriptUnitTrace.getD i (false,false)).1
      (mixedTranscriptUnitTrace.getD i (false,false)).2 swap_nd

theorem mappedGroup_counts (divide : Bool) (j : Nat) :
    toffoliCount (mappedGroup divide j)=(if divide then 3847 else 3850) ∧ measurementCount (mappedGroup divide j)=3076 := by
  have codec := compressedHistory_counts (placed j) (3*j)
  have a := logicalCell_counts divide (3*j)
  have b := logicalCell_counts divide (3*j+1)
  have c := logicalCell_counts divide (3*j+2)
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,renameT,renameM,
    a.1,a.2,b.1,b.2,c.1,c.2,codec.1,codec.2.1,codec.2.2.1,codec.2.2.2]
  all_goals norm_num

theorem mappedGroups_counts (divide : Bool) (j n : Nat) :
    toffoliCount (mappedGroups divide j n)=(if divide then 3847 else 3850)*n ∧
    measurementCount (mappedGroups divide j n)=3076*n := by
  induction n generalizing j with
  | zero => simp [mappedGroups,toffoliCount,measurementCount]
  | succ n ih =>
    have head := mappedGroup_counts divide j
    have rest := ih (j+1)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append,head.1,head.2,rest.1,rest.2]
    all_goals constructor <;> omega

theorem converterPair_counts (canonical : Bool) :
    toffoliCount (converterPair canonical)=1530 ∧ measurementCount (converterPair canonical)=1530 := by
  have target := BalancedConvert.counts (balancedSharedTargetConvert id) (balancedSharedTargetConvert_widths id)
  have source := BalancedConvert.counts (balancedSharedSourceConvert id) (balancedSharedSourceConvert_widths id)
  cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,target.1,target.2.1,target.2.2.1,target.2.2.2,
    source.1,source.2.1,source.2.2.1,source.2.2.2]
  all_goals norm_num

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedPacketTransport.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
attribute [local irreducible] logicalCell compressedHistoryEncode compressedHistoryDecode run

/-- The reference packet retains full-sized clean logical workspace. -/
def baseGroup (divide : Bool) (j : Nat) : Program :=
  compressedHistoryDecode base (3*j) ++
  (if divide then renameProgram base (logicalCell divide (3*j)) ++
      renameProgram base (logicalCell divide (3*j+1)) ++
      renameProgram base (logicalCell divide (3*j+2))
   else renameProgram base (logicalCell divide (3*j+2)) ++
      renameProgram base (logicalCell divide (3*j+1)) ++
      renameProgram base (logicalCell divide (3*j))) ++
  compressedHistoryEncode base (3*j)

theorem shifted_cell (j : Nat) (p : Program) :
    renameProgram (shifted (CompressedAllocation.pi j)) (renameProgram base p)=
      renameProgram (placed j) p := by
  rw [renameProgram_comp]
  have eq : shifted (CompressedAllocation.pi j) ∘ base=placed j := by
    funext q
    exact shifted_base _ _
  rw [eq]

/-- Exact emitted-program equality, including every correction operand. -/
theorem mappedGroup_eq_rename (divide : Bool) (j : Nat) (hj : j < 170) :
    mappedGroup divide j=renameProgram (shifted (CompressedAllocation.pi j)) (baseGroup divide j) := by
  have codec := shifted_current_codec j hj
  have append (f : Wire → Wire) (p q : Program) :
      renameProgram f (p++q)=renameProgram f p++renameProgram f q := by
    simp only [renameProgram,List.map_append]
  cases divide <;>
    simp only [mappedGroup,baseGroup,Bool.false_eq_true,if_false,if_true,
      append,codec.1,codec.2,shifted_cell]

/-- Every measurement record yields the same complete logical State under
the injective placement. This is a packet theorem, not a whole-caller claim. -/
theorem mappedGroup_run (divide : Bool) (j : Nat) (hj : j < 170)
    (s : State) (m : List Bool) :
    pullState (shifted (CompressedAllocation.pi j)) (run (mappedGroup divide j) m s)=
      run (baseGroup divide j) m (pullState (shifted (CompressedAllocation.pi j)) s) := by
  rw [mappedGroup_eq_rename divide j hj]
  exact run_rename _ (shifted _).injective _ m s

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedBaseReplay.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
attribute [local irreducible] toffoliCount measurementCount logicalCell
private theorem baseRenameT (P : Program) :
    toffoliCount (renameProgram base P)=toffoliCount P := (renameProgram_counts base P).1
private theorem baseRenameM (P : Program) :
    measurementCount (renameProgram base P)=measurementCount P := (renameProgram_counts base P).2

def baseGroups (divide : Bool) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if divide then baseGroup divide j++baseGroups divide (j+1) n
    else baseGroups divide (j+1) n++baseGroup divide j

theorem baseGroup_counts (divide : Bool) (j : Nat) :
    toffoliCount (baseGroup divide j)=(if divide then 3847 else 3850) ∧ measurementCount (baseGroup divide j)=3076 := by
  have codec := compressedHistory_counts base (3*j)
  have a := logicalCell_counts divide (3*j)
  have b := logicalCell_counts divide (3*j+1)
  have c := logicalCell_counts divide (3*j+2)
  cases divide <;> simp only [baseGroup,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,baseRenameT,baseRenameM,
    a.1,a.2,b.1,b.2,c.1,c.2,codec.1,codec.2.1,codec.2.2.1,codec.2.2.2]
  all_goals norm_num

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedPacketCorrect.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run

private theorem zip_range_getD (w : Nat → Wire) (n start i : Nat) (hi : i < n)
    (cs : List (Bool×Bool)) (hc : cs.length=n) (fallback : MixedTranscriptLetter) :
    (((List.range n).map (fun k => (w (start+k),w (1028+start+k)))).zip cs).getD i fallback =
      ((w (start+i),w (1028+start+i)),cs.getD i (false,false)) := by
  induction n generalizing start i cs with
  | zero => omega
  | succ n ih =>
    cases cs with
    | nil => simp at hc
    | cons c cs =>
      have len : cs.length=n := by simpa using hc
      rw [List.range_succ_eq_map,List.map_cons,List.zip_cons_cons]
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getD_cons_succ]
        simpa only [List.map_map,Function.comp_def,Nat.succ_eq_add_one,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (start+1) i (by omega) cs len

/-- Both coordinates and inactive unit-trace bits are those of the actual
original512 mixed tape, including every valid last packet index. -/
theorem mixedTape_base_getD (i : Nat) (hi : i < 512) :
    (mixedTranscriptTape base).getD i ((0,0),(false,false)) =
      ((base i,base (1028+i)),mixedTranscriptUnitTrace.getD i (false,false)) := by
  simpa only [mixedTranscriptTape,skywalkSharedTape,Nat.zero_add] using
    zip_range_getD base 512 0 i hi mixedTranscriptUnitTrace mixedTranscriptUnitTrace_length ((0,0),(false,false))

def packetLetters (j : Nat) : List MixedTranscriptLetter :=
  [(mixedTranscriptTape base).getD (3*j) ((0,0),(false,false)),
   (mixedTranscriptTape base).getD (3*j+1) ((0,0),(false,false)),
   (mixedTranscriptTape base).getD (3*j+2) ((0,0),(false,false))]

/-- Exact emitted instructions, including every measurement correction:
the base relabeling is a natural relabeling of this finite field cell. -/
theorem base_cell_eq (divide : Bool) (i : Nat) :
    renameProgram base (logicalCell divide i) =
      (if divide then OffsetBorrowedCanonical.cell base (base 2400) (base i) (base (1028+i))
          (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2
       else OffsetBorrowedInverseCanonical.cell base (base 2400) (base i) (base (1028+i))
          (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2) := by
  exact FieldRename.logical_cell_natural base divide i

/-- This is the actual base packet used by mappedGroup, not a postulated
body oracle. The raw control letters and unit constants match the mixed tape. -/
theorem baseGroup_eq_packet (divide : Bool) (j : Nat) (hj : j < 170) :
    baseGroup divide j =
      (if divide then codecGroupForward base (fun l : MixedTranscriptLetter =>
          OffsetBorrowedCanonical.cell base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) l.2.1 l.2.2)
          (3*j) (packetLetters j)
       else codecGroupBackward base (fun l : MixedTranscriptLetter =>
          OffsetBorrowedInverseCanonical.cell base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) l.2.1 l.2.2)
          (3*j) (packetLetters j)) := by
  have a := mixedTape_base_getD (3*j) (by omega)
  have c := mixedTape_base_getD (3*j+1) (by omega)
  have d := mixedTape_base_getD (3*j+2) (by omega)
  cases divide <;> simp only [baseGroup,packetLetters,a,c,d,codecGroupForward,codecGroupBackward,
    base_cell_eq,Bool.false_eq_true,if_false,if_true,List.append_nil,List.nil_append,List.append_assoc]

/-- Complete semantic bridge for the actual baseGroup, over the fixed170
encoding. The only body premise is actual static support, which follows from
its current-index cell support; no circuit-correctness assumption is added. -/
theorem baseGroup_encoded_step (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (support : wires (if divide then rawForwardPacket base (base 2400) (base 2409) (base 2410)
        ((packetLetters j).getD 0 ((0,0),(false,false))) ((packetLetters j).getD 1 ((0,0),(false,false)))
        ((packetLetters j).getD 2 ((0,0),(false,false)))
      else rawBackwardPacket base (base 2400) (base 2409) (base 2410)
        ((packetLetters j).getD 0 ((0,0),(false,false))) ((packetLetters j).getD 1 ((0,0),(false,false)))
        ((packetLetters j).getD 2 ((0,0),(false,false)))) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) (3*j))
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (baseGroup divide j) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).2 out := by
  let a := (mixedTranscriptTape base).getD (3*j) ((0,0),(false,false))
  let c := (mixedTranscriptTape base).getD (3*j+1) ((0,0),(false,false))
  let d := (mixedTranscriptTape base).getD (3*j+2) ((0,0),(false,false))
  cases divide
  · have step := encoded_backward_packet_step base (base 2400) (base 2409) (base 2410) hn hlo j hj a c d
      hf ho hp origin hg0 hs0 env legal X Y (by simpa [packetLetters] using support) s m input
    rw [baseGroup_eq_packet false j hj]
    simpa only [packetLetters,directionalPayload,Bool.not_false,if_true,a,c,d] using step
  · have step := encoded_forward_packet_step base (base 2400) (base 2409) (base 2410) hn hlo j hj a c d
      hf ho hp origin hg0 hs0 env legal X Y (by simpa [packetLetters] using support) s m input
    rw [baseGroup_eq_packet true j hj]
    simpa only [packetLetters,directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,a,c,d] using step

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedReplayIdentity.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
attribute [local irreducible] logicalCell OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

def tapeLetter (i : Nat) : MixedTranscriptLetter :=
  (mixedTranscriptTape base).getD i ((0,0),(false,false))

def indexedLetters (start n : Nat) : List MixedTranscriptLetter :=
  (List.range n).map (fun k => tapeLetter (start+k))

private theorem enumerate_getD {α : Type} (ls : List α) (fallback : α) :
    (List.range ls.length).map (fun i => ls.getD i fallback)=ls := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    rw [List.length_cons,List.range_succ_eq_map]
    simpa only [List.map_cons,List.map_map,Function.comp_def,List.getD_cons_zero,
      List.getD_cons_succ] using congrArg (List.cons a) ih

theorem indexedLetters_full : indexedLetters 0 512=mixedTranscriptTape base := by
  have h := enumerate_getD (mixedTranscriptTape base) ((0,0),(false,false))
  simpa only [mixedTranscriptTape_length,indexedLetters,tapeLetter,Nat.zero_add] using h

def referenceCell (divide : Bool) (l : MixedTranscriptLetter) : Program :=
  if divide then OffsetBorrowedCanonical.cell base (base 2400) l.1.1 l.1.2
    (base 2409) (base 2410) l.2.1 l.2.2
  else OffsetBorrowedInverseCanonical.cell base (base 2400) l.1.1 l.1.2
    (base 2409) (base 2410) l.2.1 l.2.2

theorem referenceCell_letter (divide : Bool) (i : Nat) (hi : i < 512) :
    referenceCell divide (tapeLetter i)=renameProgram base (logicalCell divide i) := by
  rw [tapeLetter,mixedTape_base_getD i hi,base_cell_eq]
  cases divide <;> rfl

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Math/SkywalkTerminationBudget.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.SkywalkNat

/-- A terminal logical state is padded by genuine identity transitions. -/
theorem iter_fixed_of_u_zero (z : State) (i : Nat) (hz : z.u=0) :
    step^[i] z=z := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [step,hz,if_true]

/-- Strict value widths lose one unit of total exponent at a nonterminal step.
The small-source odd branch exchanges the two exponent witnesses. No sampled
width, bitLength estimate, or product-only rounding is used. -/
theorem step_exponent_budget (z : State) (a b : Nat)
    (hu0 : 0<z.u) (hv0 : 0<z.v) (hu : z.u<2^a) (hv : z.v<2^b) :
    ∃ a' b', a'+b'+1=a+b ∧ (step z).u<2^a' ∧ (step z).v<2^b' := by
  cases a with
  | zero => simp only [pow_zero] at hu; omega
  | succ a =>
    cases b with
    | zero => simp only [pow_zero] at hv; omega
    | succ b =>
      have ua : z.u<2^a*2 := by simpa only [pow_succ] using hu
      have vb : z.v<2^b*2 := by simpa only [pow_succ] using hv
      have uh : z.u/2<2^a := by omega
      have ud : (z.u-z.v)/2<2^a := by omega
      have vd : (z.v-z.u)/2<2^b := by omega
      have hz : z.u≠0 := by omega
      by_cases he : z.u%2=0
      · refine ⟨a,b+1,by omega,?_,?_⟩
        · simpa only [step,if_neg hz,if_pos he] using uh
        · simpa only [step,if_neg hz,if_pos he] using hv
      · by_cases hle : z.v≤z.u
        · refine ⟨a,b+1,by omega,?_,?_⟩
          · simpa only [step,if_neg hz,if_neg he,if_pos hle] using ud
          · simpa only [step,if_neg hz,if_neg he,if_pos hle] using hv
        · refine ⟨b,a+1,by omega,?_,?_⟩
          · simpa only [step,if_neg hz,if_neg he,if_neg hle] using vd
          · simpa only [step,if_neg hz,if_neg he,if_neg hle] using hu

private theorem budget_aux : ∀ k a b (z : State), a+b=k →
    0<z.v → z.v%2=1 → z.u<2^a → z.v<2^b →
      (step^[k-1] z).u=0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a b z hab hv0 hvodd hu hv
    by_cases hz : z.u=0
    · rw [iter_fixed_of_u_zero z (k-1) hz]
      exact hz
    · have hu0 : 0<z.u := Nat.pos_of_ne_zero hz
      obtain ⟨a',b',hnext,hu',hv'⟩ := step_exponent_budget z a b hu0 hv0 hu hv
      have lower : a'+b'<k := by omega
      have valid := step_v_odd_pos z hv0 hvodd
      have tail := ih (a'+b') lower a' b' (step z) rfl
        valid.1 valid.2 hu' hv'
      have huExp : 0<a := by
        by_contra h
        have ha : a=0 := by omega
        rw [ha,pow_zero] at hu
        omega
      have hvExp : 0<b := by
        by_contra h
        have hb : b=0 := by omega
        rw [hb,pow_zero] at hv
        omega
      have rounds : k-1=(a'+b'-1)+1 := by omega
      rw [rounds,Function.iterate_succ_apply]
      exact tail

/-- Positive odd v and two strict width witnesses give a+b−1 rounds,
including initially terminal states and every terminal padding suffix. -/
theorem iter_u_zero_budget (z : State) (a b : Nat) (hv0 : 0<z.v)
    (hvodd : z.v%2=1) (hu : z.u<2^a) (hv : z.v<2^b) :
    (step^[a+b-1] z).u=0 :=
  budget_aux (a+b) a b z rfl hv0 hvodd hu hv

attribute [local irreducible] Nat.iterate

/-- Exact all-input termination, one round stronger than the product bound.
The unchanged coprimality/odd-positive hypotheses identify terminal v=1. -/
theorem terminates_2n_sub_one (p x n : Nat) (hp0 : 0<p) (_hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<2^n) (hc : x.Coprime p) :
    (step^[2*n-1] (init x p)).u=0 ∧ (step^[2*n-1] (init x p)).v=1 := by
  have hu := iter_u_zero_budget (init x p) n n hp0 hpodd hx hp
  have index : n+n-1=2*n-1 := by omega
  rw [index] at hu
  have valid := iter_valid (2*n-1) (init x p) hp0 hpodd
  have hg : (step^[2*n-1] (init x p)).u.gcd (step^[2*n-1] (init x p)).v=1 :=
    valid.2.2.trans hc
  rw [hu,Nat.gcd_zero_left] at hg
  exact ⟨hu,hg⟩

/-- Complete256-bit canonical range: the state before round512 is terminal. -/
theorem terminates_511 (p x : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) :
    (step^[511] (init x p)).u=0 ∧ (step^[511] (init x p)).v=1 := by
  simpa only [Nat.reduceMul,Nat.reduceSub] using
    (terminates_2n_sub_one p x 256 hp0 hx0 hpodd hp (hx.trans hp) hc)

end ECDSAAdd.SkywalkNat
end

-- source: ECDSAAdd/Math/SkywalkTerminalLastControls.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.SkywalkTrace
open SkywalkRails Secp256k1

/-- Index an actual record without unfolding a fixed512-element trace. The
default is arbitrary because every index in the statement is in range. -/
theorem trace_getD_code (n : Nat) (r : SkywalkRails.State) (i : Nat)
    (hi : i<n) (default : Bool×Bool) :
    (trace n r).getD i default=code (next^[i] r) := by
  induction n generalizing r i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h := ih (next r) i (by omega)
      simpa only [trace,Function.iterate_succ_apply] using h

attribute [local irreducible] Nat.iterate trace next

theorem code_terminal (g s : Bool) : code (encode g s 0 1)=(true,false) := by
  have h := SkywalkRails.terminal_step g s (1 : Int) (by norm_num) (by norm_num)
  simp only [code,h]

/-- The old orientation and smaller sign are existential and unconstrained.
Only the proven terminal logical values feed the terminal-step theorem. -/
theorem code_after_budget (p x n : Nat) (g s : Bool) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<2^n) (hc : x.Coprime p) :
    code (next^[2*n-1] (encode g s (x : Int) (p : Int)))=(true,false) := by
  have terminal := SkywalkNat.terminates_2n_sub_one p x n hp0 hx0 hpodd hp hx hc
  obtain ⟨G,S,encoded⟩ := iter_encoded (2*n-1) g s (SkywalkNat.init x p) hp0 hpodd
  change next^[2*n-1] (encode g s (x : Int) (p : Int))=
    encode G S ((SkywalkNat.step^[2*n-1] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[2*n-1] (SkywalkNat.init x p)).v : Int) at encoded
  rw [terminal.1,terminal.2] at encoded
  rw [encoded]
  exact code_terminal G S

private theorem canonical_coprime (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p) :
    x.Coprime ECDSAAdd.p := by
  apply Nat.Coprime.symm
  apply Secp256k1.p_prime.coprime_iff_not_dvd.mpr
  intro hd
  exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)

theorem code511 (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p) :
    code (next^[511] (encode false false (x : Int) (ECDSAAdd.p : Int)))=(true,false) := by
  have h := code_after_budget ECDSAAdd.p x 256 false false
    (by norm_num [ECDSAAdd.p]) hx0 (by norm_num [ECDSAAdd.p])
    (by norm_num [ECDSAAdd.p]) (hx.trans (by norm_num [ECDSAAdd.p]))
    (canonical_coprime x hx0 hx)
  simpa only [Nat.reduceMul,Nat.reduceSub] using h

/-- Actual last record of the unchanged512-round trace, for the entire
canonical nonzero domain. No sampled convergence or tie convention is used. -/
theorem trace512_last (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (default : Bool×Bool) :
    (trace 512 (encode false false (x : Int) (ECDSAAdd.p : Int))).getD 511 default=
      (true,false) := by
  rw [trace_getD_code 512 _ 511 (by decide) default]
  exact code511 x hx0 hx

theorem unit_trace512_last (default : Bool×Bool) :
    (trace 512 (encode false false (1 : Int) (ECDSAAdd.p : Int))).getD 511 default=
      (true,false) :=
  trace512_last 1 (by omega) (by norm_num [ECDSAAdd.p]) default

end ECDSAAdd.SkywalkTrace
end

-- source: ECDSAAdd/Math/SkywalkTerminalMixedControls.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.SkywalkTrace
open SkywalkRails Secp256k1
attribute [local irreducible] Nat.iterate trace next

private theorem map_getD_read {α β : Type} (read : α → β) (rs : List α)
    (i : Nat) (default : α) :
    (rs.map read).getD i (read default)=read (rs.getD i default) := by
  induction rs generalizing i with
  | nil => rfl
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem selected_zip_map {α : Type} (rs : List α) (cs : List (Bool×Bool))
    (read : α → Bool×Bool) (enabled : Bool) (hlen : rs.length=cs.length) :
    (rs.zip cs).map (fun l => if enabled then read l.1 else l.2)=
      if enabled then rs.map read else cs := by
  induction rs generalizing cs with
  | nil =>
    cases cs with
    | nil => cases enabled <;> rfl
    | cons c cs => simp at hlen
  | cons r rs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have ht : rs.length=cs.length := by simpa using hlen
      have tail := ih cs ht
      have lifted := congrArg (List.cons (if enabled then read r else c)) tail
      cases enabled <;> simpa only [List.zip_cons_cons,List.map_cons,
        Bool.false_eq_true,if_false,if_true] using lifted

/-- The exact effective-control list used by the mixed transcript selects
the actual trace or the divisor-one trace. Both have the same final letter. -/
theorem mixed_controls_index511 {α : Type} (rs : List α) (read : α → Bool×Bool)
    (enabled : Bool) (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hr : rs.map read=trace 512 (encode false false (x : Int) (ECDSAAdd.p : Int)))
    (default : Bool×Bool) :
    ((rs.zip (trace 512 (encode false false (1 : Int) (ECDSAAdd.p : Int)))).map
      (fun l => if enabled then read l.1 else l.2)).getD 511 default=(true,false) := by
  have len : rs.length=512 := by
    have h := congrArg List.length hr
    simpa only [List.length_map,trace_length] using h
  rw [selected_zip_map rs _ read enabled (by simpa only [trace_length] using len)]
  cases enabled
  · exact unit_trace512_last default
  · rw [hr]
    exact trace512_last x hx0 hx default

/-- Pointwise form for the actual mixed letter at index511. In arithmetic,
the pair read is componentwise mixedTranscriptBit; Bool cases identify it
with this pair selector. The index/default do not change record dependencies. -/
theorem mixed_letter_index511 {α : Type} (rs : List α) (read : α → Bool×Bool)
    (enabled : Bool) (default : α) (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hr : rs.map read=trace 512 (encode false false (x : Int) (ECDSAAdd.p : Int))) :
    let letter := (rs.zip (trace 512 (encode false false (1 : Int) (ECDSAAdd.p : Int)))).getD
      511 (default,(false,false))
    (if enabled then read letter.1 else letter.2)=(true,false) := by
  dsimp only
  have h := mixed_controls_index511 rs read enabled x hx0 hx hr
    (if enabled then read default else (false,false))
  have selected := map_getD_read
    (fun l : α×(Bool×Bool) => if enabled then read l.1 else l.2)
    (rs.zip (trace 512 (encode false false (1 : Int) (ECDSAAdd.p : Int))))
    511 (default,(false,false))
  rw [selected] at h
  exact h

end ECDSAAdd.SkywalkTrace
end

-- source: ECDSAAdd/Arithmetic/TerminalMixedTapeControls.lean
noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
open Secp256k1
attribute [local irreducible] SkywalkTrace.trace skywalkSharedTape

def terminalMixedLetter (w : Nat → Wire) : MixedTranscriptLetter :=
  (mixedTranscriptTape w).getD 511 ((w 0,w 1028),(false,false))

/-- Actual recorded controls and the inactive unit trace give the same final
letter. This derives terminal controls from the original caller trace premise. -/
theorem terminalMixedLetter_controls (w : Nat → Wire) (base : BasisState) (b : Wire)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    (mixedTranscriptBit base b (terminalMixedLetter w).1.1 (terminalMixedLetter w).2.1,
      mixedTranscriptBit base b (terminalMixedLetter w).1.2 (terminalMixedLetter w).2.2)=
      (true,false) := by
  let read : (Wire×Wire) → Bool×Bool := fun r => (base r.1,base r.2)
  have record : (skywalkSharedTape w).map read=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) := hr
  have selected := SkywalkTrace.mixed_letter_index511 (skywalkSharedTape w) read
    (base b) (w 0,w 1028) x hx0 hx record
  cases hb : base b <;>
    simpa only [terminalMixedLetter,mixedTranscriptTape,mixedTranscriptUnitTrace,
      mixedTranscriptBit,read,hb,if_true,if_false,Bool.false_eq_true] using selected

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayPayload.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedFieldSupport
attribute [local irreducible] SkywalkTrace.trace mixedTranscriptTape mixedTranscriptUnitTrace

def trimLetters : List MixedTranscriptLetter := indexedLetters 0 511

private theorem indexed_step (start n : Nat) :
    indexedLetters start (n+1)=tapeLetter start::indexedLetters (start+1) n := by
  simp only [indexedLetters,List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def]
  simp only [Nat.add_zero,Nat.succ_eq_add_one,Nat.add_comm,Nat.add_left_comm]

theorem indexedLetters_append (start n k : Nat) :
    indexedLetters start (n+k)=indexedLetters start n++indexedLetters (start+n) k := by
  induction n generalizing start with
  | zero => simp only [Nat.zero_add,Nat.add_zero,indexedLetters,List.range_zero,List.map_nil,List.nil_append]
  | succ n ih =>
    rw [show n+1+k=(n+k)+1 by omega,indexed_step,indexed_step,ih]
    simp only [List.cons_append]
    rw [show start+1+n=start+(n+1) by omega]

theorem trimLetters_last : trimLetters++[tapeLetter 511]=mixedTranscriptTape base := by
  have split := indexedLetters_append 0 511 1
  have last : indexedLetters 511 1=[tapeLetter 511] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  rw [last] at split
  simpa only [Nat.zero_add,Nat.reduceAdd,trimLetters,indexedLetters_full] using split.symm

private theorem getD_defaults {α : Type} (ls : List α) (i : Nat) (hi : i<ls.length) (a b : α) :
    ls.getD i a=ls.getD i b := by
  induction ls generalizing i with
  | nil => simp at hi
  | cons h t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

theorem lastLetter_controls (origin : BasisState) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    (mixedTranscriptBit origin (base 2400) (tapeLetter 511).1.1 (tapeLetter 511).2.1,
      mixedTranscriptBit origin (base 2400) (tapeLetter 511).1.2 (tapeLetter 511).2.2)=(true,false) := by
  have same : terminalMixedLetter base=tapeLetter 511 :=
    getD_defaults _ 511 (by rw [mixedTranscriptTape_length]; decide) _ _
  rw [←same]
  exact terminalMixedLetter_controls base origin (base 2400) x hx0 hx hr

attribute [local irreducible] indexedLetters trimLetters

private theorem replay_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)

private theorem inverse_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplayInverse (a++b) Q=
      skywalkPayloadReplayInverse a (skywalkPayloadReplayInverse b Q) := by
  induction a with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.cons_append,skywalkPayloadReplayInverse,ih]

private theorem terminal_uncell (Y : Fp) : skywalkPayloadUncell true false (Y,Y)=(Y,Y) := by
  apply Prod.ext <;> simp only [skywalkPayloadUncell,Bool.false_eq_true,if_false,if_true]
  · ring

/-- The actual511-letter field prefix already reaches duplicated quotient
words. This is derived from the original512-trace contract and terminal control,
without adding a new point-input or record assumption. -/
theorem trimLetters_quotient (origin : BasisState) (x : Nat) (Y : Fp)
    (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) trimLetters) (2*Y,0)=
      (if origin (base 2400) then Y/(x : Fp) else Y,
       if origin (base 2400) then Y/(x : Fp) else Y) := by
  have full := mixedTranscriptTape_quotient base origin (base 2400) x Y hx0 hx hr
  rw [←trimLetters_last] at full
  simp only [mixedTranscriptControls,List.map_append,List.map_cons,List.map_nil,
    lastLetter_controls origin x hx0 hx hr,replay_append,skywalkPayloadReplay] at full
  have inv := congrArg (skywalkPayloadUncell true false) full
  rw [skywalkPayloadUncell_cell,terminal_uncell] at inv
  exact inv

theorem trimLetters_product (origin : BasisState) (x : Nat) (Y : Fp)
    (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) trimLetters) (Y,Y)=
      (2*(if origin (base 2400) then Y*(x : Fp) else Y),0) := by
  have full := mixedTranscriptTape_product base origin (base 2400) x Y hx0 hx hr
  rw [←trimLetters_last] at full
  simpa only [mixedTranscriptControls,List.map_append,List.map_cons,List.map_nil,
    lastLetter_controls origin x hx0 hx hr,inverse_append,skywalkPayloadReplayInverse,
    terminal_uncell] using full

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/PenultimateSwapIdentity.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.PenultimateSwapIdentity
open Secp256k1 MappedCompressed
attribute [local irreducible] run mixedTranscriptUnitTrace indexedLetters trimLetters

/-- Proposed raw510 replacement: only the S-selected swap/window disappears.
The incumbent arithmetic, G selection and all original field ports remain. -/
def cell (divide : Bool) : Program :=
  let unit := mixedTranscriptUnitTrace.getD 510 (false,false)
  if divide then EndpointSwapTrim.forward id 2400 510 2409 unit.1
  else EndpointSwapTrim.inverse id 2400 510 2409 unit.1

theorem cell_counts (divide : Bool) :
    toffoliCount (cell divide)=(if divide then 1023 else 1024) ∧ measurementCount (cell divide)=1024 := by
  have h := EndpointSwapTrim.counts id 2400 510 2409
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  cases divide <;> simp only [cell,Bool.false_eq_true,if_false,if_true]
  · exact h.2.2
  · exact ⟨h.1,h.2.1⟩

def penultimatePayload (origin : BasisState) (Y : Fp) : Fp×Fp :=
  skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (indexedLetters 0 510)) (2*Y,0)

private theorem trimLetters_penultimate :
    trimLetters=indexedLetters 0 510++[tapeLetter 510] := by
  have last : indexedLetters 510 1=[tapeLetter 510] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  have split := indexedLetters_append 0 510 1
  rw [last] at split
  simpa only [Nat.zero_add,Nat.reduceAdd,trimLetters] using split

private theorem replay_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)

/-- Derived from the original512-trace contract, not a new terminal/input
assumption. The final forward swap acts on equal words for either S polarity. -/
theorem penultimate_half_dup (origin : BasisState) (x : Nat) (Y : Fp)
    (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    ((penultimatePayload origin Y).1+
      (if mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.1 (tapeLetter 510).2.1
        then (penultimatePayload origin Y).2 else -(penultimatePayload origin Y).2))/2=
      (penultimatePayload origin Y).2 := by
  have whole := trimLetters_quotient origin x Y hx0 hx trace
  rw [trimLetters_penultimate] at whole
  simp only [mixedTranscriptControls,List.map_append,List.map_cons,List.map_nil,
    replay_append,skywalkPayloadReplay] at whole
  apply EndpointSwapTrim.forward_dup_of_payload_equal
    (mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.1 (tapeLetter 510).2.1)
    (mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.2 (tapeLetter 510).2.2)
    (penultimatePayload origin Y).1 (penultimatePayload origin Y).2
  simpa only [penultimatePayload,mixedTranscriptControls] using
    (congrArg Prod.fst whole).trans (congrArg Prod.snd whole).symm

/- Caller bridge still required; this file does not claim whole-segment equivalence.
1. Forward: obtain the actual raw510 input EncodedFieldFrame from the modified
   firstGroup + remaining169 packet frames, with payload penultimatePayload.
   Rewrite tapeLetter510 to its concrete base510/base1538/unit controls.
   Apply accepted EndpointSwapTrim.forward_oldcell_eq using penultimate_half_dup.
2. Inverse: inverseEntryPrefix already gives EncodedFieldFrame Y Y; apply
   accepted EndpointSwapTrim.inverse_oldcell_eq before mappedGroups/firstGroup.
3. Both: extract the complete raw PairFrame/Env witness from EncodedFieldFrame,
   then transport the new program from base to allPlaced using the same zero-
   region allocation argument as trimCell_step. Prove its wire support is a
   subset of logicalCell510 and retain slots/whole1899 bound.
4. Rewrite terminalReplay's single raw510 cell only, compose independent record
   lists through converter suffixes, and inherit the existing full field spec.
   The raw511 omission and entry cancellation are unchanged; no double credit.
   New field segment target:657560T/525980MX, saving257T/1MX in each direction.
-/
end ECDSAAdd.Arithmetic.PenultimateSwapIdentity
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedCleanTransport.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run

private theorem inverse_zero (e : Equiv.Perm Nat)
    (fix : ∀q,¬zeroRegion q → e q=q) (q : Nat) (hq : zeroRegion q) :
    zeroRegion (e q) := by
  by_contra bad
  have eq := e.injective (fix (e q) bad)
  exact bad (eq.symm ▸ hq)

theorem shifted_zero_boundary (e : Equiv.Perm Nat)
    (fix : ∀q,¬zeroRegion q → e q=q) (s : State)
    (hz : ∀q,zeroRegion q → s.basis (base q)=false) :
    pullState (shifted e) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (shifted e q)=s.basis q
    by_cases small : q < 16
    · change s.basis (shiftedFn e q)=s.basis q
      simp only [shiftedFn,if_pos small]
    · have eq : q=base (q-16) := by
        change q=(q-16)+16
        exact (Nat.sub_add_cancel (Nat.le_of_not_gt small)).symm
      rw [eq,shifted_base]
      by_cases clean : zeroRegion (q-16)
      · exact (hz _ (inverse_zero e fix _ clean)).trans (hz _ clean).symm
      · rw [fix _ clean]

theorem pullState_perm_injective (e : Equiv.Perm Nat) : Function.Injective (pullState e) := by
  intro s t h
  apply State.extensionality
  · have ph := congrArg (fun x : State => x.phase) h
    exact ph
  · funext q
    have bit := congrArg (fun x : State => x.basis (e.symm q)) h
    simpa only [pullState,e.apply_symm_apply] using bit

/-- A packet whose reference input and output have clean allocation roles
executes identically as a complete State, not only on the retained payload. -/
theorem mappedGroup_state_eq (divide : Bool) (j : Nat) (hj : j < 170)
    (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀q,zeroRegion q → (run (baseGroup divide j) m s).basis (base q)=false) :
    run (mappedGroup divide j) m s=run (baseGroup divide j) m s := by
  have fix := fun q hq => pi_outside j q hj hq
  have input := shifted_zero_boundary (pi j) fix s hin
  have output := shifted_zero_boundary (pi j) fix (run (baseGroup divide j) m s) hout
  apply pullState_perm_injective (shifted (pi j))
  rw [mappedGroup_run divide j hj,input,output]

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedTailFrame.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run directionalReplay OffsetBorrowedCanonical.cell
  OffsetBorrowedInverseCanonical.cell logicalCell

def tailLetters : List MixedTranscriptLetter :=
  [(mixedTranscriptTape base).getD 510 ((0,0),(false,false)),
   (mixedTranscriptTape base).getD 511 ((0,0),(false,false))]

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedEncodedFrameLayout.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run

private theorem getD_member_MappedCompressedEncodedFrameLayout {α : Type} (ls : List α) (i : Nat) (fallback : α)
    (hi : i < ls.length) : ls.getD i fallback ∈ ls := by
  induction ls generalizing i with
  | nil => simp at hi
  | cons a ls ih =>
    cases i with
    | zero => simp
    | succ i =>
      have bound : i < ls.length := by simpa using hi
      exact List.mem_cons_of_mem a (ih i bound)

theorem layout_of_subset (w : Nat → Wire) (b sign eff : Wire)
    (ls full : List MixedTranscriptLetter) (subset : ∀l∈ls,l∈full)
    (hf : MixedTranscriptReplayLayout w b sign eff full) :
    MixedTranscriptReplayLayout w b sign eff ls :=
  fun l hl => hf l (subset l hl)

/-- Full-tape layout supplies the actual stored unit constants and control
coordinates at every valid original round. -/
theorem mixedTape_getD_layout (w : Nat → Wire) (b sign eff : Wire)
    (hf : MixedTranscriptReplayLayout w b sign eff (mixedTranscriptTape w))
    (i : Nat) (hi : i < 512) :
    MixedTranscriptFieldLayout w b
      ((mixedTranscriptTape w).getD i ((0,0),(false,false))).1.1
      ((mixedTranscriptTape w).getD i ((0,0),(false,false))).1.2 sign eff := by
  apply hf
  apply getD_member_MappedCompressedEncodedFrameLayout
  simpa only [mixedTranscriptTape_length] using hi

theorem packetLetters_subset (j : Nat) (hj : j < 170) :
    ∀l∈packetLetters j,l∈mixedTranscriptTape base := by
  intro l hl
  simp only [packetLetters,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl|rfl
  all_goals
    apply getD_member_MappedCompressedEncodedFrameLayout
    rw [mixedTranscriptTape_length]
    omega

/-- All170 packet contracts are consequences of one original full layout. -/
theorem packet_layouts (b sign eff : Wire)
    (hf : MixedTranscriptReplayLayout base b sign eff (mixedTranscriptTape base)) :
    ∀j,j < 170 → MixedTranscriptReplayLayout base b sign eff (packetLetters j) := by
  intro j hj
  exact layout_of_subset base b sign eff _ _ (packetLetters_subset j hj) hf

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedPacketSupport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedFieldSupport
attribute [local irreducible] mixedTranscriptTape mixedTranscriptUnitTrace

theorem packet_controls (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base) :
    ∀ l ∈ packetLetters j,
      l.1.1 ∈ wires (compressedHistoryEncode base (3*j)) ∧
      l.1.2 ∈ wires (compressedHistoryEncode base (3*j)) := by
  have pool := skywalkShared_integer_nodup base hn
  have site (k : Fin 6) := compressedHistory_site_mem base pool hlo (3*j) (by omega) k
  have a := mixedTape_base_getD (3*j) (by omega)
  have c := mixedTape_base_getD (3*j+1) (by omega)
  have d := mixedTape_base_getD (3*j+2) (by omega)
  intro l hl
  simp only [packetLetters,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl|rfl
  · rw [a]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId] using site 0
    · simpa [compressedHistoryMap,compressedHistoryId] using site 1
  · rw [c]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId] using site 2
    · simpa [compressedHistoryMap,compressedHistoryId] using site 3
  · rw [d]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using site 4
    · simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using site 5

/-- The actual three cells meet the structural support premise of their
correctness proof; no support oracle is required from the arithmetic caller. -/
theorem packet_structural_support (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base) :
    wires (if divide then rawForwardPacket base (base 2400) (base 2409) (base 2410)
      ((packetLetters j).getD 0 ((0,0),(false,false))) ((packetLetters j).getD 1 ((0,0),(false,false)))
      ((packetLetters j).getD 2 ((0,0),(false,false)))
    else rawBackwardPacket base (base 2400) (base 2409) (base 2410)
      ((packetLetters j).getD 0 ((0,0),(false,false))) ((packetLetters j).getD 1 ((0,0),(false,false)))
      ((packetLetters j).getD 2 ((0,0),(false,false)))) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) (3*j) := by
  have both := packet_active_support base (base 2400) (base 2409) (base 2410)
    (3*j) (packetLetters j) (packet_controls j hj hn hlo)
  cases divide
  · simpa [packetLetters,rawBackwardPacket,OffsetBorrowedInverseCanonical.replay,List.append_assoc] using both.2
  · simpa [packetLetters,rawForwardPacket,OffsetBorrowedCanonical.replay,List.append_assoc] using both.1

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedPacketFrame.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run

/-- The actual low-width packet implements the original exact field update.
Both clean placement boundaries follow from the encoded frame itself. -/
theorem mappedGroup_encoded_step (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (mappedGroup divide j) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).2 out := by
  have reference := baseGroup_encoded_step divide j hj hn hlo ho hp hf origin hg0 hs0 env legal X Y
    (packet_structural_support divide j hj hn hlo) s m input
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env _ _
    (run (baseGroup divide j) m s) reference.2
  have same := mappedGroup_state_eq divide j hj s m cleanIn cleanOut
  change (run (mappedGroup divide j) m s).phase=s.phase ∧ _
  rw [same]
  exact reference

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Framework/PacketSequenceFrame.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.PacketSequence
attribute [local irreducible] run measurementCount

def program (forward : Bool) (p : Nat → Program) : Nat → Nat → Program
  | _,0 => []
  | j,n+1 => if forward then p j++program forward p (j+1) n
      else program forward p (j+1) n++p j

def payload {α : Type} (forward : Bool) (step : Nat → α → α) : Nat → Nat → α → α
  | _,0,Q => Q
  | j,n+1,Q => if forward then payload forward step (j+1) n (step j Q)
      else step j (payload forward step (j+1) n Q)

theorem counts_equal (forward : Bool) (p r : Nat → Program)
    (same : ∀j,measurementCount (p j)=measurementCount (r j)) (j n : Nat) :
    measurementCount (program forward p j n)=measurementCount (program forward r j n) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases forward <;> simp only [program,Bool.false_eq_true,if_false,if_true,
      measurementCount_append,same,ih]

/-- Generic composition is instantiated only with proved actual packet
contracts. Every record is partitioned by the emitted measurement count. -/
theorem frame {α : Type} (forward : Bool) (p r : Nat → Program)
    (step : Nat → α → α) (F : α → State → Prop) (N : Nat)
    (counts : ∀j,measurementCount (p j)=measurementCount (r j))
    (packet : ∀j,j < N → ∀Q s m,F Q s →
      run (p j) m s=run (r j) m s ∧ (run (p j) m s).phase=s.phase ∧
      F (step j Q) (run (p j) m s)) (j n : Nat) (bound : j+n ≤ N)
    (Q : α) (s : State) (m : List Bool) (input : F Q s) :
    let out := run (program forward p j n) m s
    out=run (program forward r j n) m s ∧ out.phase=s.phase ∧
      F (payload forward step j n Q) out := by
  induction n generalizing j Q s m with
  | zero => simpa only [program,run,payload] using
      (show s=s ∧ s.phase=s.phase ∧ F Q s from ⟨rfl,rfl,input⟩)
  | succ n ih =>
    have hj : j < N := by omega
    cases forward
    · let later := program false p (j+1) n
      let t := run later (m.take (measurementCount later)) s
      let V := payload false step (j+1) n Q
      have rest := ih (j+1) (by omega) Q s (m.take (measurementCount later)) input
      have first := packet j hj V t (m.drop (measurementCount later)) rest.2.2
      have mc : measurementCount (program false r (j+1) n)=measurementCount later :=
        (counts_equal false p r counts (j+1) n).symm
      have eq : run (program false p j (n+1)) m s=run (program false r j (n+1)) m s := by
        simp only [program,Bool.false_eq_true,if_false,run_append]
        rw [mc,←rest.1]
        exact first.1
      refine ⟨eq,?_,?_⟩
      · simpa only [program,Bool.false_eq_true,if_false,run_append,later,t] using first.2.1.trans rest.2.1
      · simpa only [program,Bool.false_eq_true,if_false,run_append,payload,V,later,t] using first.2.2
    · let head := p j
      let t := run head (m.take (measurementCount head)) s
      have first := packet j hj Q s (m.take (measurementCount head)) input
      have rest := ih (j+1) (by omega) (step j Q) t (m.drop (measurementCount head)) first.2.2
      have eq : run (program true p j (n+1)) m s=run (program true r j (n+1)) m s := by
        simp only [program,if_true,run_append]
        rw [←counts j,←first.1]
        exact rest.1
      refine ⟨eq,?_,?_⟩
      · simpa only [program,if_true,run_append,head,t] using rest.2.1.trans first.2.1
      · simpa only [program,if_true,run_append,payload,head,t] using rest.2.2

end ECDSAAdd.PacketSequence
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedGroupsFrame.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run mappedGroup baseGroup
attribute [local irreducible] mappedGroups baseGroups measurementCount packetLetters
  mixedTranscriptTape mixedTranscriptUnitTrace

def groupsPayload (divide : Bool) (origin : BasisState) : Nat → Nat → Fp×Fp → Fp×Fp
  | _,0,Q => Q
  | j,n+1,Q =>
      if divide then groupsPayload divide origin (j+1) n
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) Q)
      else directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j))
        (groupsPayload divide origin (j+1) n Q)

private theorem packet_complete (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (mappedGroup divide j) m s=run (baseGroup divide j) m s ∧
    (run (mappedGroup divide j) m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).2
      (run (mappedGroup divide j) m s) := by
  have ref := baseGroup_encoded_step divide j hj hn hlo ho hp hf origin hg0 hs0 env legal X Y
    (packet_structural_support divide j hj hn hlo) s m input
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env _ _
    (run (baseGroup divide j) m s) ref.2
  exact ⟨mappedGroup_state_eq divide j hj s m cleanIn cleanOut,
    mappedGroup_encoded_step divide j hj hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input⟩

private theorem mapped_sequence_eq (divide : Bool) (j n : Nat) :
    PacketSequence.program divide (mappedGroup divide) j n=mappedGroups divide j n := by
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,mappedGroups]
  | succ n ih => cases divide <;> simp only [PacketSequence.program,mappedGroups,
      Bool.false_eq_true,if_false,if_true,ih]

private theorem base_sequence_eq (divide : Bool) (j n : Nat) :
    PacketSequence.program divide (baseGroup divide) j n=baseGroups divide j n := by
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,baseGroups]
  | succ n ih => cases divide <;> simp only [PacketSequence.program,baseGroups,
      Bool.false_eq_true,if_false,if_true,ih]

private theorem groups_payload_eq (divide : Bool) (origin : BasisState) (j n : Nat) (Q : Fp×Fp) :
    PacketSequence.payload divide
      (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters k)) V)
      j n Q=groupsPayload divide origin j n Q := by
  induction n generalizing j Q with
  | zero => rfl
  | succ n ih => cases divide <;> simp only [PacketSequence.payload,groupsPayload,
      Bool.false_eq_true,if_false,if_true,ih]

/-- Actual mapped packet contracts instantiate the generic sequence proof.
The complete State and phase agree with the emitted reference replay. -/
theorem mappedGroups_frame (divide : Bool) (j n : Nat) (bound : j+n ≤ 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : ∀k,k < 170 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters k))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (mappedGroups divide j n) m s
    out=run (baseGroups divide j n) m s ∧ out.phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin (groupsPayload divide origin j n (X,Y)).1
        (groupsPayload divide origin j n (X,Y)).2 out := by
  have countEq (k : Nat) : measurementCount (mappedGroup divide k)=measurementCount (baseGroup divide k) :=
    (mappedGroup_counts divide k).2.trans (baseGroup_counts divide k).2.symm
  have all := PacketSequence.frame divide (mappedGroup divide) (baseGroup divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters k)) V)
    (fun V t => EncodedFieldFrame base (base 2409) origin V.1 V.2 t) 170 countEq
    (fun k hk V t records h => packet_complete divide k hk hn hlo ho hp (hf k hk)
      origin hg0 hs0 env legal V.1 V.2 t records h) j n bound (X,Y) s m input
  simpa only [mapped_sequence_eq,base_sequence_eq,groups_payload_eq] using all

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Framework/RunAppendAgreement.lean
noncomputable section
namespace ECDSAAdd
attribute [local irreducible] run measurementCount

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedReplayFrame.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run mappedGroups baseGroups measurementCount
  mixedTranscriptTape mixedTranscriptUnitTrace packetLetters tailLetters

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayCore.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayTrim.lean
noncomputable section

set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation
attribute [local irreducible] wires toffoliCount measurementCount logicalCell mappedGroups

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayReference.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run logicalCell mappedGroups baseGroups measurementCount
  mixedTranscriptTape mixedTranscriptUnitTrace packetLetters tapeLetter

/-- Raw residual510 has its original scalar and complete encoded frame under
all independent records. The allocation switch follows derived zero regions. -/
theorem trimCell_step (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (renameProgram allPlaced (logicalCell divide 510)) m s=
      run (renameProgram base (logicalCell divide 510)) m s ∧
    (run (renameProgram allPlaced (logicalCell divide 510)) m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (X,Y)).2
      (run (renameProgram allPlaced (logicalCell divide 510)) m s) := by
  have aligned : IndexedLetters base 510 [tapeLetter 510] := by
    simp only [tapeLetter,mixedTape_base_getD 510 (by decide),IndexedLetters]
    exact ⟨trivial,trivial⟩
  have layout : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) [tapeLetter 510] := by
    intro l hl
    have eq : l=tapeLetter 510 := by simpa using hl
    subst l
    simpa only [tapeLetter] using mixedTape_getD_layout base _ _ _ hf 510 (by decide)
  have ref := encoded_tail_replay (!divide) base _ _ _ hn hlo ho hp 510 [tapeLetter 510]
    (by omega) (by simp) aligned layout origin hg0 hs0 env legal X Y s m input
  have selectedProgram : directionalReplay (!divide) base (base 2400) (base 2409) (base 2410) [tapeLetter 510]=
      renameProgram base (logicalCell divide 510) := by
    rw [←referenceCell_letter divide 510 (by decide)]
    cases divide <;> simp only [directionalReplay,referenceCell,OffsetBorrowedCanonical.replay,
      OffsetBorrowedInverseCanonical.replay,Bool.not_true,Bool.not_false,Bool.false_eq_true,
      if_false,if_true,List.append_nil,List.nil_append]
  rw [selectedProgram] at ref
  have hin := encoded_zero_region base _ hn hlo origin env X Y s input
  have hout := encoded_zero_region base _ hn hlo origin env _ _ _ ref.2
  have pin := shifted_zero_boundary pi0 pi0_outside s hin
  have pout := shifted_zero_boundary pi0 pi0_outside _ hout
  have rename : renameProgram allPlaced (logicalCell divide 510)=
      renameProgram (shifted pi0) (renameProgram base (logicalCell divide 510)) := by
    rw [renameProgram_comp]
    congr 1
  have eq : run (renameProgram allPlaced (logicalCell divide 510)) m s=
      run (renameProgram base (logicalCell divide 510)) m s := by
    apply pullState_perm_injective (shifted pi0)
    rw [rename,run_rename _ (shifted pi0).injective,pin,pout]
  exact ⟨eq,by rw [eq]; exact ref⟩

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/PenultimateMappedCellProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.PenultimateMappedCellProof
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
open OffsetBorrowedCanonical
attribute [local irreducible] run wires mixedTranscriptUnitTrace mixedTranscriptTape

private theorem forward_natural (f w : Wire → Wire) (b g flag : Wire) (ig : Bool) :
    renameProgram f (EndpointSwapTrim.forward w b g flag ig)=
      EndpointSwapTrim.forward (f ∘ w) (f b) (f g) (f flag) ig := by
  simp only [EndpointSwapTrim.forward,FieldRename.selectWindow_natural,
    FieldRename.rename_append,FieldRename.forward_program_natural]
  rfl

private theorem inverse_natural (f w : Wire → Wire) (b g flag : Wire) (ig : Bool) :
    renameProgram f (EndpointSwapTrim.inverse w b g flag ig)=
      EndpointSwapTrim.inverse (f ∘ w) (f b) (f g) (f flag) ig := by
  simp only [EndpointSwapTrim.inverse,FieldRename.selectWindow_natural,
    FieldRename.rename_append,FieldRename.inverse_program_natural]
  rfl

/-- Naturality of the actual new raw cell; no input-state premise. -/
theorem cell_natural (f : Wire → Wire) (divide : Bool) :
    renameProgram f (PenultimateSwapIdentity.cell divide)=
      if divide then EndpointSwapTrim.forward f (f 2400) (f 510) (f 2409)
        (mixedTranscriptUnitTrace.getD 510 (false,false)).1
      else EndpointSwapTrim.inverse f (f 2400) (f 510) (f 2409)
        (mixedTranscriptUnitTrace.getD 510 (false,false)).1 := by
  cases divide <;> simp only [PenultimateSwapIdentity.cell,Bool.false_eq_true,
    if_false,if_true,forward_natural,inverse_natural,Function.comp_id]

private theorem window_mono (b src flag : Wire) (constant : Bool) (P Q : Program)
    (h : wires P⊆wires Q) :
    wires (transcriptSelectWindow b src flag constant P)⊆
      wires (transcriptSelectWindow b src flag constant Q) := by
  intro q hq
  have body : q∈wires P → q∈wires Q := fun hp => h hp
  simp only [transcriptSelectWindow,wires_append,Finset.mem_union] at hq ⊢
  tauto

private theorem body_window (b src flag : Wire) (constant : Bool) (P : Program) :
    wires P⊆wires (transcriptSelectWindow b src flag constant P) := by
  intro q hq
  simp only [transcriptSelectWindow,wires_append,Finset.mem_union]
  tauto

/-- The omitted S window/swap introduce no replacement sites or corrections. -/
theorem logical_support_subset (divide : Bool) :
    wires (PenultimateSwapIdentity.cell divide)⊆wires (logicalCell divide 510) := by
  cases divide
  · simp only [PenultimateSwapIdentity.cell,logicalCell,Bool.false_eq_true,if_false,
      EndpointSwapTrim.inverse,OffsetBorrowedInverseCanonical.cell]
    apply window_mono
    have inner : wires ([.X 2409]++OffsetBorrowedInverse.program id 2409++[.X 2409])⊆
        wires (OffsetBorrowedInverseCanonical.body id 2409 2410) := by
      intro q hq
      simp only [OffsetBorrowedInverseCanonical.body,OffsetBorrowedInverseCanonical.double,
        wires_append,Finset.mem_union] at hq ⊢
      tauto
    exact inner.trans (body_window _ _ _ _ _)
  · simp only [PenultimateSwapIdentity.cell,logicalCell,if_true,
      EndpointSwapTrim.forward,OffsetBorrowedCanonical.cell]
    apply window_mono
    have inner : wires ([.X 2409]++OffsetBorrowedField.program id 2409++[.X 2409])⊆
        wires (OffsetBorrowedCanonical.body id 2409 2410) := by
      intro q hq
      simp only [OffsetBorrowedCanonical.body,wires_append,Finset.mem_union] at hq ⊢
      tauto
    exact inner.trans (body_window _ _ _ _ _)

theorem support_subset (divide : Bool) :
    wires (renameProgram allPlaced (PenultimateSwapIdentity.cell divide))⊆
      wires (renameProgram allPlaced (logicalCell divide 510)) := by
  rw [renameProgram_support,renameProgram_support]
  exact Finset.image_mono allPlaced (logical_support_subset divide)

/-- Forward duplication is the actual half output; inverse duplication is its input. -/
def Condition (divide : Bool) (origin : BasisState) (X Y : Fp) : Prop :=
  if divide then
    (X+(if mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.1
      (tapeLetter 510).2.1 then Y else -Y))/2=Y
  else X=Y

private theorem base_cell_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (X Y : Fp) (s : State) (mNew mOld : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (cond : Condition divide origin X Y) :
    run (renameProgram base (PenultimateSwapIdentity.cell divide)) mNew s=
      run (renameProgram base (logicalCell divide 510)) mOld s := by
  let unit := mixedTranscriptUnitTrace.getD 510 (false,false)
  have letter : tapeLetter 510=((base 510,base 1538),unit) := by
    simp only [tapeLetter,mixedTape_base_getD 510 (by decide),Nat.reduceAdd,unit]
  have layout : MixedTranscriptFieldLayout base (base 2400) (base 510) (base 1538)
      (base 2409) (base 2410) := by
    simpa only [mixedTape_base_getD 510 (by decide),Nat.reduceAdd] using
      mixedTape_getD_layout base (base 2400) (base 2409) (base 2410) hf 510 (by decide)
  have hl := balancedSharedTranscriptLayout_direct base (base 2400) (base 510)
    (base 1538) (base 2409) (base 2410) layout ho
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have rawEq : run (renameProgram base (PenultimateSwapIdentity.cell divide)) mNew raw=
      run (renameProgram base (logicalCell divide 510)) mOld raw := by
    rw [cell_natural,FieldRename.logical_cell_natural]
    simp only [Nat.reduceAdd]
    cases divide
    · simp only [Condition,Bool.false_eq_true,if_false] at cond
      subst X
      simp only [Bool.false_eq_true,if_false]
      exact EndpointSwapTrim.inverse_oldcell_eq base _ _ _ _ _ unit.1 unit.2
        hn hl (ho _ (by simp)) (ho _ (by simp)) origin hg0 hs0 env Y raw mNew mOld frame
    · simp only [Condition,if_true,letter] at cond
      simp only [if_true]
      exact EndpointSwapTrim.forward_oldcell_eq base _ _ _ _ _ unit.1 unit.2
        hn hl (ho _ (by simp)) (ho _ (by simp)) origin hg0 hs0 env X Y cond raw mNew mOld frame
  have aligned : IndexedLetters base 510 [tapeLetter 510] := by
    simp only [letter,IndexedLetters]
    exact ⟨trivial,trivial⟩
  have dis := tail_replay_disjoint base (base 2400) (base 2409) (base 2410)
    hn hlo hp 510 [tapeLetter 510] (by omega) (by simp) aligned
  have oldDis : Disjoint (wires (allGroupEncode base 170))
      (wires (renameProgram base (logicalCell divide 510))) := by
    rw [FieldRename.logical_cell_natural]
    cases divide
    · simpa only [OffsetBorrowedInverseCanonical.replay,letter,List.append_nil,List.nil_append,
        Bool.false_eq_true,if_false,Nat.reduceAdd] using dis.2
    · simpa only [OffsetBorrowedCanonical.replay,letter,List.append_nil,List.nil_append,
        if_true,Nat.reduceAdd] using dis.1
  have sub : wires (renameProgram base (PenultimateSwapIdentity.cell divide))⊆
      wires (renameProgram base (logicalCell divide 510)) := by
    rw [renameProgram_support,renameProgram_support]
    exact Finset.image_mono base (logical_support_subset divide)
  have newDis := oldDis.mono_right sub
  have newCommute := (run_disjoint_commute (allGroupEncode base 170)
    (renameProgram base (PenultimateSwapIdentity.cell divide)) newDis [] mNew raw).symm
  have oldCommute := (run_disjoint_commute (allGroupEncode base 170)
    (renameProgram base (logicalCell divide 510)) oldDis [] mOld raw).symm
  rw [encoded,newCommute,oldCommute,rawEq]

/-- Complete mapped State equality, including spectators and every independent tape. -/
theorem cell_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (mNew mOld : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (cond : Condition divide origin X Y) :
    run (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) mNew s=
      run (renameProgram allPlaced (logicalCell divide 510)) mOld s := by
  have eq := base_cell_eq divide hn hlo ho hp hf origin hg0 hs0 env X Y s mNew mOld input cond
  have old := trimCell_step divide hn hlo ho hp hf origin hg0 hs0 env legal X Y s mOld input
  have hin := encoded_zero_region base _ hn hlo origin env X Y s input
  have hout := encoded_zero_region base _ hn hlo origin env _ _ _ old.2.2
  have newOutZero : ∀q,zeroRegion q →
      (run (renameProgram base (PenultimateSwapIdentity.cell divide)) mNew s).basis (base q)=false := by
    rw [eq,←old.1]
    exact hout
  have pin := shifted_zero_boundary pi0 pi0_outside s hin
  have pout := shifted_zero_boundary pi0 pi0_outside _ newOutZero
  have rename : renameProgram allPlaced (PenultimateSwapIdentity.cell divide)=
      renameProgram (shifted pi0) (renameProgram base (PenultimateSwapIdentity.cell divide)) := by
    rw [renameProgram_comp]
    congr 1
  have placed : run (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) mNew s=
      run (renameProgram base (PenultimateSwapIdentity.cell divide)) mNew s := by
    apply pullState_perm_injective (shifted pi0)
    rw [rename,run_rename _ (shifted pi0).injective,pin,pout]
  exact placed.trans (eq.trans old.1.symm)

theorem forward_cell_eq
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (mNew mOld : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (dup : (X+(if mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.1
      (tapeLetter 510).2.1 then Y else -Y))/2=Y) :
    run (renameProgram allPlaced (PenultimateSwapIdentity.cell true)) mNew s=
      run (renameProgram allPlaced (logicalCell true 510)) mOld s :=
  cell_eq true hn hlo ho hp hf origin hg0 hs0 env legal X Y s mNew mOld input dup

theorem inverse_cell_eq
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (Y : Fp)
    (s : State) (mNew mOld : List Bool) (input : EncodedFieldFrame base (base 2409) origin Y Y s) :
    run (renameProgram allPlaced (PenultimateSwapIdentity.cell false)) mNew s=
      run (renameProgram allPlaced (logicalCell false 510)) mOld s :=
  cell_eq false hn hlo ho hp hf origin hg0 hs0 env legal Y Y s mNew mOld input rfl

end ECDSAAdd.Arithmetic.PenultimateMappedCellProof
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedConversionNaturality.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] majority eraseCarry mappedAdd mappedSub

def mapConvert (f : Wire → Wire) (L : BalancedConvert.Layout) : BalancedConvert.Layout :=
  {low:=L.low.map f,msb:=f L.msb,carry:=L.carry.map f,
   cin:=f L.cin,one:=f L.one,flag:=f L.flag}

end ECDSAAdd.Arithmetic.FieldRename

namespace ECDSAAdd.Arithmetic.MappedCompressed
open FieldRename

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/EntryFieldSeedCancellation.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryFieldSeedCancellation
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run dblInPlace halfInPlace OffsetBorrowedCanonical.cell
attribute [local irreducible] transcriptSelectWindow swapRegisters

def selectedSwap (w : Nat → Wire) (b swap sign effS : Wire) (is : Bool) : Program :=
  transcriptSelectWindow b swap effS is
    (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)

end ECDSAAdd.Arithmetic.EntryFieldSeedCancellation
end

-- source: ECDSAAdd/Arithmetic/EntryMappedFieldSegmentTrim.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 MappedCompressed CompressedAllocation
attribute [local irreducible] wires logicalCell compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] dblInPlace halfInPlace copyRegister
attribute [local irreducible] toffoliCount measurementCount
private theorem emptyT : toffoliCount ([] : Program)=0 := by simp [toffoliCount]
private theorem emptyM : measurementCount ([] : Program)=0 := by simp [measurementCount]

/-- Cell zero retains its original recorded S selection and quantum control. -/
def logicalZero : Program :=
  EntryFieldSeedCancellation.selectedSwap id 2400 1028 2409 2410
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2

def firstGroup (divide : Bool) : Program :=
  compressedHistoryDecode (placed 0) 0 ++
  (if divide then renameProgram (placed 0) logicalZero ++
      renameProgram (placed 0) (logicalCell divide 1) ++
      renameProgram (placed 0) (logicalCell divide 2)
   else renameProgram (placed 0) (logicalCell divide 2) ++
      renameProgram (placed 0) (logicalCell divide 1) ++
      renameProgram (placed 0) logicalZero) ++
  compressedHistoryEncode (placed 0) 0

/-- The remaining 169 packets and both raw tail cells are unchanged. -/
def replay (divide : Bool) : Program :=
  if divide then firstGroup divide ++ mappedGroups divide 1 169 ++
      renameProgram allPlaced (logicalCell divide 510) ++
      renameProgram allPlaced (logicalCell divide 511)
  else renameProgram allPlaced (logicalCell divide 511) ++
      renameProgram allPlaced (logicalCell divide 510) ++
      mappedGroups divide 1 169 ++ firstGroup divide

def fieldSegment (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (converterPair false) ++ replay divide ++
  renameProgram allPlaced (converterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

private theorem window_mono (b source flag : Wire) (v : Bool) (P Q : Program)
    (h : wires P ⊆ wires Q) :
    wires (transcriptSelectWindow b source flag v P) ⊆
      wires (transcriptSelectWindow b source flag v Q) := by
  simp only [transcriptSelectWindow,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _))
    (Finset.Subset.refl _)

private theorem body_in_window (b source flag : Wire) (v : Bool) (P : Program) :
    wires P ⊆ wires (transcriptSelectWindow b source flag v P) := by
  intro q hq
  simp only [transcriptSelectWindow,wires_append,Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hq))

private theorem rename_mono (f : Wire → Wire) (P Q : Program)
    (h : wires P ⊆ wires Q) : wires (renameProgram f P) ⊆ wires (renameProgram f Q) := by
  rw [renameProgram_support,renameProgram_support]
  exact Finset.image_mono _ h

theorem logicalZero_support_sub (divide : Bool) : wires logicalZero ⊆ wires (logicalCell divide 0) := by
  let sw := swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y
  have leaf : wires sw ⊆ wires (if divide then OffsetBorrowedCanonical.body id 2409 2410
      else OffsetBorrowedInverseCanonical.body id 2409 2410) := by
    cases divide
    · simp only [Bool.false_eq_true,if_false,OffsetBorrowedInverseCanonical.body,wires_append]
      exact Finset.subset_union_left
    · simp only [if_true,OffsetBorrowedCanonical.body,wires_append]
      exact Finset.subset_union_right
  cases divide <;>
    simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,logicalCell,
      Bool.false_eq_true,if_false,if_true,OffsetBorrowedCanonical.cell,
      OffsetBorrowedInverseCanonical.cell] at ⊢
  all_goals exact (window_mono _ _ _ _ _ _ leaf).trans (body_in_window _ _ _ _ _)

theorem firstGroup_support_sub (divide : Bool) :
    wires (firstGroup divide) ⊆ wires (mappedGroup divide 0) := by
  have sub := rename_mono (placed 0) _ _ (logicalZero_support_sub divide)
  cases divide <;> simp only [firstGroup,mappedGroup,Bool.false_eq_true,if_false,if_true,
    Nat.mul_zero,Nat.zero_add,wires_append,Finset.union_assoc]
  · exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union (Finset.Subset.refl _)
          (Finset.union_subset_union sub (Finset.Subset.refl _))))
  · exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union sub (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union (Finset.Subset.refl _) (Finset.Subset.refl _))))

theorem replay_support_sub (divide : Bool) : wires (replay divide) ⊆ wires (mappedReplay divide) := by
  have sub := firstGroup_support_sub divide
  have unfoldGroups : mappedGroups divide 0 170 =
      if divide then mappedGroup divide 0 ++ mappedGroups divide 1 169
      else mappedGroups divide 1 169 ++ mappedGroup divide 0 := by rfl
  cases divide <;> simp only [replay,mappedReplay,unfoldGroups,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_assoc]
  · exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union (Finset.Subset.refl _) sub))
  · exact Finset.union_subset_union sub (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _) (Finset.Subset.refl _)))

private theorem swap_nd :
    (2410::(balancedSharedPorts id 2409).r++(balancedSharedPorts id 2409).y).Nodup := by
  rw [balancedSharedPorts_r,balancedSharedPorts_y]
  simp only [wireBlock,List.map_id]
  apply List.nodup_cons.mpr
  constructor
  · intro h
    rcases List.mem_append.mp h with h|h
    all_goals have bound := List.mem_range'_1.mp h; omega
  · apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hr hy
    simp only [List.mem_range'_1] at hr hy
    omega

theorem logicalZero_counts : toffoliCount logicalZero=257 ∧ measurementCount logicalZero=1 := by
  have width := BalancedCleanup.widths (balancedSharedPorts id 2409).toLayout (balancedSharedPorts_widths id 2409)
  have sw := swapRegisters_resources 2410 _ _ (width.2.1.trans width.2.2.1.symm) swap_nd
  have sel := transcriptSelectWindow_counts 2400 1028 2410
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)
  simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,sel.1,sel.2,sw.1,sw.2.1,width.2.1]
  norm_num

private theorem renameT (f : Wire → Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem renameM (f : Wire → Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem firstGroup_counts (divide : Bool) :
    toffoliCount (firstGroup divide)=(if divide then 2824 else 2826) ∧ measurementCount (firstGroup divide)=2052 := by
  have codec := compressedHistory_counts (placed 0) 0
  have a := logicalCell_counts divide 1
  have b := logicalCell_counts divide 2
  cases divide <;> simp only [firstGroup,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,renameT,renameM,logicalZero_counts.1,
    logicalZero_counts.2,a.1,a.2,b.1,b.2,codec.1,codec.2.1,codec.2.2.1,codec.2.2.2]
  all_goals norm_num

theorem replay_counts (divide : Bool) :
    toffoliCount (replay divide)=(if divide then 655527 else 656038) ∧ measurementCount (replay divide)=523946 := by
  have groups := mappedGroups_counts divide 1 169
  have first := firstGroup_counts divide
  have a := logicalCell_counts divide 510
  have b := logicalCell_counts divide 511
  cases divide <;> simp only [replay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,renameT,renameM,groups.1,groups.2,
    first.1,first.2,a.1,a.2,b.1,b.2]
  all_goals norm_num

private theorem copy_counts :
    toffoliCount (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)=0 ∧
    measurementCount (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)=0 := by
  have len : (skywalkSharedField id).z.length=(skywalkSharedField id).a.length := by
    rw [skywalkShared_field_z]
    change (wireBlock id 2056 257).length=(wireBlock id 770 257).length
    simp [wireBlock]
  have copy := copyRegister_counts none (skywalkSharedField id).z (skywalkSharedField id).a len
  simpa only [Option.isSome_none,Bool.false_eq_true,if_false] using copy

theorem fieldSegment_counts (divide : Bool) :
    toffoliCount (fieldSegment divide)=(if divide then 658587 else 659098) ∧ measurementCount (fieldSegment divide)=527006 := by
  have center := converterPair_counts false
  have canonical := converterPair_counts true
  have rp := replay_counts divide
  cases divide <;> simp only [fieldSegment,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,emptyT,emptyM,
    renameT,renameM,copy_counts.1,copy_counts.2,center.1,center.2,canonical.1,canonical.2,rp.1,rp.2]
  all_goals norm_num

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedConversionPlacement.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation FieldRename

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedConversionEncoding.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedCanonicalFrame.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run wires allGroupEncode compressedHistoryEncode
  BalancedConvert.center BalancedConvert.canonical

/-- Actual257-bit public field ports under the fixed full history encoding. -/
def EncodedCanonicalFrame (origin : BasisState) (X Y : Fp) (s : State) : Prop :=
  ∃ raw : State,raw.phase=s.phase ∧
    PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val Y.val raw.basis ∧
    s=run (allGroupEncode base 170) [] raw

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedCopyEndpoint.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedAllocation CompressedFieldSupport FieldRename
attribute [local irreducible] run wires copyRegister allGroupEncode

def copyPairAt (w : Nat → Wire) : Program :=
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedUnaryNaturality.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] addInPlace subInPlace compareLt compareLtConst
attribute [local irreducible] maskedConstant xorConstant maskedAddConst

end ECDSAAdd.Arithmetic.FieldRename

namespace ECDSAAdd.Arithmetic.MappedCompressed
open FieldRename Secp256k1

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedEndpointEncodingSupport.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode dblInPlace halfInPlace copyRegister

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedEncodedEndpoints.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode dblInPlace halfInPlace copyRegister

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/EntryMappedFieldSegmentTrimProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run logicalCell compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] allGroupEncode

/-- Full logical reference of the actual first packet. Its remaining two
cells and both codecs are exactly the old emitted instructions. -/
def baseFirstGroup (divide : Bool) : Program :=
  compressedHistoryDecode base 0 ++
  (if divide then renameProgram base logicalZero ++
      renameProgram base (logicalCell divide 1) ++ renameProgram base (logicalCell divide 2)
   else renameProgram base (logicalCell divide 2) ++
      renameProgram base (logicalCell divide 1) ++ renameProgram base logicalZero) ++
  compressedHistoryEncode base 0

theorem firstGroup_eq_rename (divide : Bool) :
    firstGroup divide=renameProgram (shifted (pi 0)) (baseFirstGroup divide) := by
  have codec := shifted_current_codec 0 (by decide)
  have append (f : Wire → Wire) (p q : Program) :
      renameProgram f (p++q)=renameProgram f p++renameProgram f q := by
    simp only [renameProgram,List.map_append]
  cases divide <;> simp only [firstGroup,baseFirstGroup,Bool.false_eq_true,if_false,if_true,
    append,Nat.mul_zero,codec.1,codec.2,shifted_cell]

theorem firstGroup_run (divide : Bool) (s : State) (m : List Bool) :
    pullState (shifted (pi 0)) (run (firstGroup divide) m s)=
      run (baseFirstGroup divide) m (pullState (shifted (pi 0)) s) := by
  rw [firstGroup_eq_rename]
  exact run_rename _ (shifted _).injective _ m s

/-- Structural allocation transport only. The caller must derive both
boundaries from its encoded frames before using this helper. -/
theorem firstGroup_state_eq (divide : Bool) (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀q,zeroRegion q → (run (baseFirstGroup divide) m s).basis (base q)=false) :
    run (firstGroup divide) m s=run (baseFirstGroup divide) m s := by
  have fix := fun q hq => pi_outside 0 q (by decide) hq
  have input := shifted_zero_boundary (pi 0) fix s hin
  have output := shifted_zero_boundary (pi 0) fix (run (baseFirstGroup divide) m s) hout
  apply pullState_perm_injective (shifted (pi 0))
  rw [firstGroup_run,input,output]

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
end

-- source: ECDSAAdd/Arithmetic/EntryBodySupport.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.EntryBodySupport
open MappedCompressed CompressedFieldSupport
attribute [local irreducible] wires logicalCell renameProgram
  OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell

/-- Support composition is checked over abstract programs. Neither the
renamed cell programs nor their concrete256-bit gate lists are normalized. -/
theorem renamed_three_support (f : Wire → Wire) (P Q R S : Program) (W : Finset Wire)
    (sub : wires P ⊆ wires Q)
    (hq : wires (renameProgram f Q) ⊆ W)
    (hr : wires (renameProgram f R) ⊆ W)
    (hs : wires (renameProgram f S) ⊆ W) :
    wires (renameProgram f P ++ renameProgram f R ++ renameProgram f S) ⊆ W := by
  have renamed : wires (renameProgram f P) ⊆ wires (renameProgram f Q) := by
    rw [renameProgram_support,renameProgram_support]
    exact Finset.image_mono f sub
  rw [wires_append,wires_append]
  exact Finset.union_subset (Finset.union_subset (renamed.trans hq) hr) hs

/-- The naturality conversion is checked with an abstract placement and
cell index, before any caller instantiates its recorded constants or wires. -/
theorem renamed_logical_support (f : Nat → Wire) (divide : Bool) (i start : Nat)
    (hg : f i ∈ wires (compressedHistoryEncode f start))
    (hs : f (1028+i) ∈ wires (compressedHistoryEncode f start)) :
    wires (renameProgram f (logicalCell divide i)) ⊆
      groupReadSites f (f 2400) (f 2409) (f 2410) start := by
  have leaf := current_cells_support f (f 2400) (f 2409) (f 2410) start
    (f i) (f (1028+i)) (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 hg hs
  rw [FieldRename.logical_cell_natural]
  cases divide
  · simpa only [Bool.false_eq_true,if_false] using leaf.2
  · simpa only [if_true] using leaf.1

end ECDSAAdd.Arithmetic.EntryBodySupport
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedReplaySpec.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run mappedReplay
  mixedTranscriptTape mixedTranscriptUnitTrace directionalPayload

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayTrimProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run mappedReplay mixedTranscriptTape
  mixedTranscriptUnitTrace directionalPayload indexedLetters trimLetters

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/EntryInversePayload.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.EntryInversePayload
open Secp256k1 MappedCompressed CompressedFieldSupport
attribute [local irreducible] groupsPayload indexedLetters trimLetters packetLetters
  mixedTranscriptTape mixedTranscriptUnitTrace

private theorem inverse_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplayInverse (a++b) Q=
      skywalkPayloadReplayInverse a (skywalkPayloadReplayInverse b Q) := by
  induction a with
  | nil => rfl
  | cons l ls ih => simp only [List.cons_append,skywalkPayloadReplayInverse,ih]

private theorem packet_indexed (j : Nat) : packetLetters j=indexedLetters (3*j) 3 := by
  simp [packetLetters,indexedLetters,tapeLetter,List.range_succ]

/-- Packet payload recursion is exactly the original ordered field tape. -/
theorem inverse_groups_payload (j n : Nat) (origin : BasisState) (Q : Fp×Fp) :
    groupsPayload false origin j n Q=
      skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400)
        (indexedLetters (3*j) (3*n))) Q := by
  induction n generalizing j Q with
  | zero => simp only [groupsPayload,indexedLetters,Nat.mul_zero,List.range_zero,List.map_nil,
      mixedTranscriptControls,skywalkPayloadReplayInverse]
  | succ n ih =>
    have len : 3*(n+1)=3+3*n := by omega
    have start : 3*(j+1)=3*j+3 := by omega
    rw [len,indexedLetters_append]
    simp only [groupsPayload,Bool.false_eq_true,if_false,Bool.not_false,directionalPayload,if_true,
      mixedTranscriptControls,List.map_append,inverse_append,ih,start,←packet_indexed]

/-- All170 packets followed by the retained raw510 inverse cell give the
accepted terminal-trim multiplication result, with no new input premise. -/
theorem inverse_boundary (origin : BasisState) (x : Nat) (Y : Fp)
    (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    groupsPayload false origin 0 170
      (skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (Y,Y))=
      (2*(if origin (base 2400) then Y*(x:Fp) else Y),0) := by
  have split := indexedLetters_append 0 510 1
  have one : indexedLetters 510 1=[tapeLetter 510] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  rw [Nat.zero_add,one] at split
  have shape : trimLetters=indexedLetters 0 510++[tapeLetter 510] := by
    simpa only [trimLetters] using split
  rw [inverse_groups_payload]
  have result := trimLetters_product origin x Y hx0 hx trace
  rw [shape] at result
  simp only [mixedTranscriptControls,List.map_append,inverse_append] at result
  exact result

/-- Removing the final inverse half-add is forced by the existing zero
source result. This algebra is valid for every recorded G/S pair. -/
theorem remove_final_double (g sw : Bool) (Q : Fp×Fp) (Z : Fp)
    (old : skywalkPayloadUncell g sw Q=(2*Z,0)) :
    (if sw then (Q.2,Q.1) else Q)=(Z,0) := by
  let V := if sw then (Q.2,Q.1) else Q
  have value : (2*V.1+(if g then -V.2 else V.2),V.2)=(2*Z,0) := old
  have source : V.2=0 := congrArg Prod.snd value
  have target : 2*V.1=2*Z := by
    have t := congrArg Prod.fst value
    simpa only [source,neg_zero,ite_self,add_zero] using t
  have two : (2:Fp)≠0 := by decide
  have same : V.1=Z := mul_left_cancel₀ two target
  exact Prod.ext same source

end ECDSAAdd.Arithmetic.EntryInversePayload
end

-- source: ECDSAAdd/Arithmetic/EntrySelectedSwapFrame.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Arithmetic.EntrySelectedSwapFrame
open Secp256k1 BalancedField CompressedFieldSupport
attribute [local irreducible] run transcriptSelectWindow swapRegisters

private theorem swap_pair (r y : List Wire) (flag : Wire) (len : r.length=y.length)
    (nd : (flag::r++y).Nodup) (origin : BasisState) (X Y : Nat) :
    Triple (PairFrame r y origin X Y) (swapRegisters flag r y)
      (PairFrame r y origin (if origin flag then Y else X) (if origin flag then X else Y)) := by
  intro s m input
  have out := swapRegisters_correct flag r y len nd s m
  have away := (List.nodup_cons.mp nd).1
  have same := input.2.2 flag (fun h => away (List.mem_append_left _ h))
    (fun h => away (List.mem_append_right _ h))
  refine ⟨out.1,?_,?_,fun q qr qy => (out.2.1 q qr qy).trans (input.2.2 q qr qy)⟩
  · rw [out.2.2.1,same,input.1,input.2.1]
  · rw [out.2.2.2,same,input.1,input.2.1]

/-- Retains the quantum activation control and the actual recorded S bit. -/
theorem selectedSwap_frame (w : Nat → Wire) (b g swap sign effS : Wire) (is : Bool)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (origin : BasisState) (hs0 : origin effS=false) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y))
      (EntryFieldSeedCancellation.selectedSwap w b swap sign effS is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
        (centerWord (if mixedTranscriptBit origin b swap is then Y else X))
        (centerWord (if mixedTranscriptBit origin b swap is then X else Y))) := by
  have controls := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at controls
  have nd : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have body := swap_pair _ _ effS (width.2.1.trans width.2.2.1.symm) hl.swapND
    (mixedTranscriptBase origin b swap effS is) (centerWord X) (centerWord Y)
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at body
  have body' : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      (mixedTranscriptBase origin b swap effS is) (centerWord X) (centerWord Y))
      (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        (mixedTranscriptBase origin b swap effS is)
        (centerWord (if mixedTranscriptBit origin b swap is then Y else X))
        (centerWord (if mixedTranscriptBit origin b swap is then X else Y))) := by
    cases bit : mixedTranscriptBit origin b swap is <;>
      simpa only [mixedTranscriptBase,writeBit,bit,if_true,if_false,Bool.false_eq_true] using body
  exact transcriptSelectWindow_pairFrame b swap effS is _ _ nd (hl.outside b (by simp))
    (hl.outside swap (by simp)) (hl.outside effS (by simp)) origin hs0 _ _ _ _ _ body'

private theorem current_records (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (j : Nat) (hj : j < 170) (s : State) (m : List Bool)
    (legal : RawGroupLegal w 170 s.basis) :
    run (compressedHistoryEncode w (3*j)) m s = run (compressedHistoryEncode w (3*j)) [] s := by
  have a := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s m (legal j hj)
  have z := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s [] (legal j hj)
  apply State.extensionality
  · simpa only [compressedHistoryEncode] using a.1.trans z.1.symm
  · exact run_basis_records _ s s m [] rfl

/-- Generic codec conjugacy. The body frame is a reusable Hoare theorem;
all history legality and allocation boundaries still follow from the frame. -/
theorem encoded_window_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (j : Nat) (hj : j < 170) (origin : BasisState) (legal : RawGroupLegal w 170 origin)
    (X Y A B : Fp) (body : Program)
    (support : wires body ⊆ groupReadSites w b sign eff (3*j))
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign origin X Y s) :
    let out := run (compressedHistoryDecode w (3*j)++body++compressedHistoryEncode w (3*j)) m s
    out.phase=s.phase ∧ EncodedFieldFrame w sign origin A B out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs origin raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB := otherGroupEncode_body_disjoint w b sign eff hn hlo
    (hp b (by simp)) hs (hp eff (by simp)) 170 j (by decide) hj body support
  let rawOut := run body m raw
  have result := correct raw m frame
  have outLegal := frame_history_legal w sign hn hs origin rawOut.basis _ _ legal result.2
  have transport := window_transport_other w (3*j) pool hlo (by omega)
    (otherGroupEncode w j 170) body hE hB raw [] [] [] m
    (m.drop (measurementCount body)) (leg j hj)
  rw [current_records w pool hlo j hj rawOut _ outLegal] at transport
  have back := allGroupEncode_factor w pool hlo 170 j (by decide) hj rawOut
  rw [←back] at transport
  have actual : run (compressedHistoryDecode w (3*j)++body++compressedHistoryEncode w (3*j)) m s =
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,factor]
    have zero := (compressedHistory_counts w (3*j)).2.2.2
    simp only [List.append_assoc]
    rw [run_append,zero,List.take_zero,List.drop_zero,run_append,run_take]
    exact transport
  dsimp only
  rw [actual]
  have encPhase := allGroupEncode_phase w pool hlo 170 (by decide) rawOut [] outLegal
  exact ⟨encPhase.trans (result.1.trans phase),rawOut,encPhase.symm,result.2,rfl⟩

end ECDSAAdd.Arithmetic.EntrySelectedSwapFrame
end

-- source: ECDSAAdd/Arithmetic/EntryInverseFirstGroupFrame.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires logicalCell renameProgram
  OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
  compressedHistoryEncode compressedHistoryDecode

private theorem selected_natural (f : Nat → Wire) : renameProgram f logicalZero =
    EntryFieldSeedCancellation.selectedSwap f (f 2400) (f 1028) (f 2409) (f 2410)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 := by
  have rmap : (balancedSharedPorts f (f 2409)).r=(balancedSharedPorts id 2409).r.map f := by
    simpa only [Function.comp_id] using FieldRename.shared_r_map f id 2409
  have ymap : (balancedSharedPorts f (f 2409)).y=(balancedSharedPorts id 2409).y.map f := by
    simpa only [Function.comp_id] using FieldRename.shared_y_map f id 2409
  simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,FieldRename.selectWindow_natural,
    FieldRename.swapRegisters_natural,rmap,ymap]

def inverseBody : Program := renameProgram base (logicalCell false 2) ++
  renameProgram base (logicalCell false 1) ++ renameProgram base logicalZero

def inverseZeroPayload (origin : BasisState) (X Y : Fp) : Fp×Fp :=
  let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400)
    [(mixedTranscriptTape base).getD 1 ((0,0),(false,false)),
     (mixedTranscriptTape base).getD 2 ((0,0),(false,false))]) (X,Y)
  if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then (Q.2,Q.1) else Q

private theorem reversed_three_support (f : Wire → Wire) (P Q R S : Program) (W : Finset Wire)
    (sub : wires P ⊆ wires Q) (hq : wires (renameProgram f Q) ⊆ W)
    (hr : wires (renameProgram f R) ⊆ W) (hs : wires (renameProgram f S) ⊆ W) :
    wires (renameProgram f S++renameProgram f R++renameProgram f P) ⊆ W := by
  have renamed : wires (renameProgram f P) ⊆ wires (renameProgram f Q) := by
    rw [renameProgram_support,renameProgram_support]
    exact Finset.image_mono f sub
  rw [wires_append,wires_append]
  exact Finset.union_subset (Finset.union_subset hs hr) (renamed.trans hq)

theorem inverseBody_support (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base) :
    wires inverseBody ⊆ groupReadSites base (base 2400) (base 2409) (base 2410) 0 := by
  have pool := skywalkShared_integer_nodup base hn
  have site (k : Fin 6) := compressedHistory_site_mem base pool hlo 0 (by decide) k
  unfold inverseBody
  exact reversed_three_support base logicalZero (logicalCell false 0) (logicalCell false 1)
    (logicalCell false 2) (groupReadSites base (base 2400) (base 2409) (base 2410) 0)
    (logicalZero_support_sub false)
    (EntryBodySupport.renamed_logical_support base false 0 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 0)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 1))
    (EntryBodySupport.renamed_logical_support base false 1 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 2)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 3))
    (EntryBodySupport.renamed_logical_support base false 2 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 4)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 5))

/-- Both remaining inverse cells and the recorded S window are retained. -/
theorem inverseBody_frame
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord X) (centerWord Y)) inverseBody
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (inverseZeroPayload origin X Y).1) (centerWord (inverseZeroPayload origin X Y).2)) := by
  let a := (mixedTranscriptTape base).getD 0 ((0,0),(false,false))
  let c := (mixedTranscriptTape base).getD 1 ((0,0),(false,false))
  let d := (mixedTranscriptTape base).getD 2 ((0,0),(false,false))
  let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) [c,d]) (X,Y)
  have aEq := mixedTape_base_getD 0 (by decide)
  have cEq := mixedTape_base_getD 1 (by decide)
  have dEq := mixedTape_base_getD 2 (by decide)
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) a.1.1 a.1.2
    (base 2409) (base 2410) (hf a (by simp [a,packetLetters])) ho
  rw [show a=((base 0,base 1028),mixedTranscriptUnitTrace.getD 0 (false,false)) from aEq] at layout
  have rest := OffsetBorrowedInverseCanonical.replay_frame base (base 2400) (base 2409) (base 2410)
    hn [c,d] (by
      intro l hl
      apply hf l
      simp only [packetLetters,Nat.mul_zero,Nat.zero_add,List.mem_cons,List.not_mem_nil,or_false]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      exact Or.inr (by simpa only [c,d] using hl)) ho origin hg0 hs0 env X Y
  have sw := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 layout origin hs0 Q.1 Q.2
  have result := rest.seq sw
  have bodyEq : inverseBody=OffsetBorrowedInverseCanonical.replay base (base 2400) (base 2409)
      (base 2410) [c,d]++EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028)
        (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 := by
    simp only [inverseBody,selected_natural,OffsetBorrowedInverseCanonical.replay,base_cell_eq,
      Bool.false_eq_true,if_false,List.append_nil,List.nil_append,c,d,cEq,dEq,List.append_assoc]
  rw [bodyEq]
  cases bit : mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 <;>
    simpa only [inverseZeroPayload,bit,if_true,if_false,Bool.false_eq_true,Q,c,d] using result

/-- The existing complete inverse result forces the retained window's
output. Neither source-zero nor fixed measurement results are assumed. -/
theorem inverseZeroPayload_of_old (origin : BasisState) (X Y Z : Fp)
    (old : skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (X,Y)=(2*Z,0)) :
    inverseZeroPayload origin X Y=(Z,0) := by
  have aEq := mixedTape_base_getD 0 (by decide)
  have value : skywalkPayloadUncell
      (mixedTranscriptBit origin (base 2400) (base 0) (mixedTranscriptUnitTrace.getD 0 (false,false)).1)
      (mixedTranscriptBit origin (base 2400) (base 1028) (mixedTranscriptUnitTrace.getD 0 (false,false)).2)
      (skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400)
        [(mixedTranscriptTape base).getD 1 ((0,0),(false,false)),
         (mixedTranscriptTape base).getD 2 ((0,0),(false,false))]) (X,Y))=(2*Z,0) := by
    simpa only [packetLetters,Nat.mul_zero,Nat.zero_add,mixedTranscriptControls,List.map_cons,
      List.map_nil,skywalkPayloadReplayInverse,aEq] using old
  exact EntryInversePayload.remove_final_double _ _ _ Z value

-- Check the transport once on arbitrary programs, before specializing to the packet.
private theorem transport_encoded (P Q : Program)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (X Y A B : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (ref : (run P m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A B (run P m s))
    (same : (∀q,zeroRegion q → s.basis (base q)=false) →
      (∀q,zeroRegion q → (run P m s).basis (base q)=false) →
      run Q m s=run P m s) :
    (run Q m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A B (run Q m s) := by
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env A B (run P m s) ref.2
  rw [same cleanIn cleanOut]
  exact ref

/-- Actual mapped packet-zero inverse, with clean placement boundaries
derived from its complete encoded field frames. -/
theorem firstGroup_inverse_step
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (X Y : Fp) (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    (run (firstGroup false) m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (inverseZeroPayload origin X Y).1 (inverseZeroPayload origin X Y).2 (run (firstGroup false) m s) := by
  have ref := EntrySelectedSwapFrame.encoded_window_step base (base 2400) (base 2409) (base 2410)
    hn hlo hp 0 (by decide) origin legal X Y _ _ inverseBody (inverseBody_support hn hlo)
    (inverseBody_frame hn ho hf origin hg0 hs0 env X Y) s m input
  simp only [Nat.mul_zero] at ref
  have shape : baseFirstGroup false=compressedHistoryDecode base 0++inverseBody++compressedHistoryEncode base 0 := by
    simp only [baseFirstGroup,inverseBody,Bool.false_eq_true,if_false]
  rw [←shape] at ref
  exact transport_encoded (baseFirstGroup false) (firstGroup false) hn hlo origin env X Y _ _
    s m input ref (firstGroup_state_eq false s m)

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
end

-- source: ECDSAAdd/Arithmetic/EntryBodySupportConcrete.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.EntryBodySupport
open MappedCompressed CompressedFieldSupport EntryMappedFieldSegmentTrim
attribute [local irreducible] wires logicalCell renameProgram logicalZero
  compressedHistoryEncode OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell

/-- Isolated concrete instantiation of the abstract support contracts.
There is no raw-packet or naturality conversion at this specialization. -/
theorem first_body_support (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) :
    wires (renameProgram base logicalZero ++ renameProgram base (logicalCell true 1) ++
      renameProgram base (logicalCell true 2)) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) 0 := by
  have pool := skywalkShared_integer_nodup base hn
  have site (k : Fin 6) := compressedHistory_site_mem base pool hlo 0 (by decide) k
  exact renamed_three_support base logicalZero (logicalCell true 0) (logicalCell true 1)
    (logicalCell true 2) (groupReadSites base (base 2400) (base 2409) (base 2410) 0)
    (logicalZero_support_sub true)
    (renamed_logical_support base true 0 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 0)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 1))
    (renamed_logical_support base true 1 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 2)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 3))
    (renamed_logical_support base true 2 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 4)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 5))

end ECDSAAdd.Arithmetic.EntryBodySupport
end

-- source: ECDSAAdd/Framework/RunThreeStates.lean
noncomputable section
namespace ECDSAAdd
attribute [local irreducible] run

/-- Measured composition uses independent records for each real stage.
The supplied relation is proved from the three executed stage equations. -/
theorem run_three_states (p q r : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 : State) (m1 m2 m3 : List Bool),
      run p m1 s=s1 → run q m2 s1=s2 → run r m3 s2=s3 → P s s3)
    (s : State) (m : List Bool) : P s (run (p++(q++r)) m s) := by
  simp only [run_append]
  apply h s _ _ _ _ _ _ <;> rfl
end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedCanonicalReplay.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run mappedReplay directionalPayload
  mixedTranscriptTape mixedTranscriptUnitTrace

/-- The actual middle three blocks of fieldSegment, with both boundary
conversions retained and all history groups encoded at each outer boundary. -/
def canonicalMappedReplay (divide : Bool) : Program :=
  renameProgram allPlaced (converterPair false)++
    (mappedReplay divide++renameProgram allPlaced (converterPair true))

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedFieldSegmentSpec.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run fieldSegment canonicalMappedReplay mappedReplay
  dblInPlace halfInPlace copyRegister converterPair

def fieldPrefix (divide : Bool) : Program := if divide then
  renameProgram allPlaced (dblInPlace (borrowedSkywalkUnary id) p)
  else renameProgram allPlaced (copyPairAt id)

def fieldResult (divide : Bool) (origin : BasisState) (x : Nat) (Y : Fp) : Fp :=
  if origin (base 2400) then (if divide then Y/(x : Fp) else Y*(x : Fp)) else Y

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/EntryMappedFieldSegmentTrimForward.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires logicalCell compressedHistoryEncode compressedHistoryDecode
  OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
  OffsetBorrowedField.program TerminalParityOffset.program TerminalParityOffset.core
  TerminalParityMeasure.chain TerminalParityMeasure.leaf

private theorem zero_natural : renameProgram base logicalZero =
    EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028) (base 2409) (base 2410)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 := by
  have rmap : (balancedSharedPorts base (base 2409)).r=
      (balancedSharedPorts id 2409).r.map base := by
    simpa only [Function.comp_id] using FieldRename.shared_r_map base id 2409
  have ymap : (balancedSharedPorts base (base 2409)).y=
      (balancedSharedPorts id 2409).y.map base := by
    simpa only [Function.comp_id] using FieldRename.shared_y_map base id 2409
  simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,FieldRename.selectWindow_natural,
    FieldRename.swapRegisters_natural,rmap,ymap]

private def firstBody : Program := renameProgram base logicalZero ++
    renameProgram base (logicalCell true 1) ++ renameProgram base (logicalCell true 2)

private theorem payload_zero (g sw : Bool) (Y : Fp) :
    skywalkPayloadCell g sw (2*Y,0)=(if sw then 0 else Y,if sw then Y else 0) := by
  have two : (2:Fp)≠0 := by decide
  have half : (2*Y)/2=Y := mul_div_cancel_left₀ Y two
  simp only [skywalkPayloadCell,neg_zero,ite_self,add_zero,half]
  cases sw <;> rfl

/-- The retained S window followed by the two unchanged cells realizes
exactly the original three-cell update on the seeded payload. -/
theorem firstBody_frame
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord Y) (centerWord 0)) firstBody
      (PairFrame (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y origin
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)).1)
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)).2)) := by
  let a := (mixedTranscriptTape base).getD 0 ((0,0),(false,false))
  let c := (mixedTranscriptTape base).getD 1 ((0,0),(false,false))
  let d := (mixedTranscriptTape base).getD 2 ((0,0),(false,false))
  have aEq := mixedTape_base_getD 0 (by decide)
  have cEq := mixedTape_base_getD 1 (by decide)
  have dEq := mixedTape_base_getD 2 (by decide)
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) a.1.1 a.1.2
    (base 2409) (base 2410) (hf a (by simp [a,packetLetters])) ho
  rw [show a=((base 0,base 1028),mixedTranscriptUnitTrace.getD 0 (false,false)) from aEq] at layout
  have sw := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 layout origin hs0 Y 0
  let A := if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then 0 else Y
  let B := if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then Y else 0
  have rest := OffsetBorrowedCanonical.replay_frame base (base 2400) (base 2409) (base 2410)
    hn [c,d] (by
      intro l hl
      apply hf l
      simp only [packetLetters,Nat.mul_zero,Nat.zero_add,List.mem_cons,List.not_mem_nil,or_false]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      exact Or.inr (by simpa only [c,d] using hl))
    ho origin hg0 hs0 env A B
  have result := sw.seq rest
  have bodyEq : firstBody=EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028)
      (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 ++
      OffsetBorrowedCanonical.replay base (base 2400) (base 2409) (base 2410) [c,d] := by
    simp only [firstBody,zero_natural,OffsetBorrowedCanonical.replay,base_cell_eq,
      if_true,List.append_nil,c,d,cEq,dEq,List.append_assoc]
  rw [bodyEq]
  simpa only [packetLetters,Nat.mul_zero,Nat.zero_add,mixedTranscriptControls,List.map_cons,
    List.map_nil,skywalkPayloadReplay,aEq,payload_zero,A,B,a,c,d] using result

private theorem firstBody_support (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) : wires firstBody ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) 0 := by
  unfold firstBody
  exact EntryBodySupport.first_body_support hn hlo

-- Check the transport once on arbitrary programs, before specializing to the packet.
private theorem transport_encoded_EntryMappedFieldSegmentTrimForward (P Q : Program)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (X Y A B : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (ref : (run P m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A B (run P m s))
    (same : (∀q,zeroRegion q → s.basis (base q)=false) →
      (∀q,zeroRegion q → (run P m s).basis (base q)=false) →
      run Q m s=run P m s) :
    (run Q m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A B (run Q m s) := by
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env A B (run P m s) ref.2
  rw [same cleanIn cleanOut]
  exact ref

/-- Exact native first packet, with both clean placement boundaries derived
from the encoded frame and the accepted selected-swap frame. -/
theorem firstGroup_forward_step
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin Y 0 s) :
    let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
    (run (firstGroup true) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Q.1 Q.2 (run (firstGroup true) m s) := by
  have ref := EntrySelectedSwapFrame.encoded_window_step base (base 2400) (base 2409) (base 2410)
    hn hlo hp 0 (by decide) origin legal Y 0 _ _ firstBody (firstBody_support hn hlo)
    (firstBody_frame hn ho hf origin hg0 hs0 env Y) s m input
  simp only [Nat.mul_zero] at ref
  have shape : baseFirstGroup true=compressedHistoryDecode base 0++firstBody++compressedHistoryEncode base 0 := by
    simp only [baseFirstGroup,firstBody,if_true]
  rw [←shape] at ref
  exact transport_encoded_EntryMappedFieldSegmentTrimForward (baseFirstGroup true) (firstGroup true) hn hlo origin env Y 0 _ _
    s m input ref (firstGroup_state_eq true s m)

-- Keep programs symbolic so kernel conversion does not evaluate concrete gate lists.

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedFieldSegment.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run directionalPayload
  mixedTranscriptTape mixedTranscriptUnitTrace

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/EntryMappedFieldSegmentTrimTerminal.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires logicalCell mappedGroups toffoliCount measurementCount

/-- Entry cancellation and the previously proved terminal omission are
separate transformations: all170 native codecs and raw510 are retained. -/
def terminalReplay (divide : Bool) : Program :=
  if divide then firstGroup divide ++ mappedGroups divide 1 169 ++
      renameProgram allPlaced (logicalCell divide 510)
  else renameProgram allPlaced (logicalCell divide 510) ++
      mappedGroups divide 1 169 ++ firstGroup divide

def terminalFieldSegment (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (converterPair false) ++ terminalReplay divide ++
  renameProgram allPlaced (converterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

theorem terminalReplay_support_sub (divide : Bool) : wires (terminalReplay divide) ⊆ wires (replay divide) := by
  cases divide <;> simp only [terminalReplay,replay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.subset_iff]
  all_goals intro q h; simp only [Finset.mem_union] at h ⊢; tauto

private theorem terminal_empty_wires : wires ([] : Program)=∅ := by simp [wires]

theorem terminalFieldSegment_support (divide : Bool) : wires (terminalFieldSegment divide) ⊆ slots.toFinset := by
  have rp := (terminalReplay_support_sub divide).trans ((replay_support_sub divide).trans (mappedReplay_support divide))
  have a := converters_support false
  have b := converters_support true
  cases divide <;> simp only [terminalFieldSegment,Bool.false_eq_true,if_false,if_true,
    wires_append,terminal_empty_wires,Finset.empty_union,Finset.union_empty,
    Finset.union_subset_iff,and_assoc]
  · exact ⟨copy_support,a,rp,b⟩
  · exact ⟨a,rp,b,copy_support⟩

theorem terminalReplay_counts (divide : Bool) :
    toffoliCount (terminalReplay divide)=(if divide then 654247 else 654757) ∧ measurementCount (terminalReplay divide)=522921 := by
  have groups := mappedGroups_counts divide 1 169
  have first := firstGroup_counts divide
  have cell := logicalCell_counts divide 510
  have renamed := renameProgram_counts allPlaced (logicalCell divide 510)
  cases divide <;> simp only [terminalReplay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,groups.1,groups.2,first.1,first.2,
    renamed.1,renamed.2,cell.1,cell.2]
  all_goals norm_num

/-- Savings here include only the separately established terminal cell.
The1535 entry saving is relative to the current terminal-trim wrapper. -/
theorem terminalFieldSegment_counts (divide : Bool) :
    toffoliCount (terminalFieldSegment divide)=(if divide then 657307 else 657817) ∧ measurementCount (terminalFieldSegment divide)=525981 := by
  have old := fieldSegment_counts divide
  have full := replay_counts divide
  have trim := terminalReplay_counts divide
  simp only [fieldSegment,toffoliCount_append,measurementCount_append] at old
  simp only [terminalFieldSegment,toffoliCount_append,measurementCount_append]
  rw [full.1,full.2] at old
  rw [trim.1,trim.2]
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at old ⊢
  all_goals constructor <;> omega

private def oldTerminalPrefix : Program := fieldPrefix true ++
  renameProgram allPlaced (converterPair false) ++ mappedGroup true 0

-- Keep programs symbolic so kernel conversion does not evaluate concrete gate lists.

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayResources.lean
noncomputable section

set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation
attribute [local irreducible] wires toffoliCount measurementCount mappedReplay

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/EntryMappedFieldSegmentTrimInverse.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run logicalCell terminalReplay terminalFieldSegment groupsPayload

private theorem inverse_groups_succ (origin : BasisState) (j n : Nat) (Q : Fp×Fp) :
    groupsPayload false origin j (n+1) Q=
      skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) (packetLetters j))
        (groupsPayload false origin (j+1) n Q) := by
  simp only [groupsPayload,Bool.false_eq_true,if_false,Bool.not_false,directionalPayload,if_true]

/-- The actual inverse emission retains raw510, all169 later native packets,
and the cell-zero S window. Its final zero source follows from the accepted
whole inverse payload identity under the original512 recorded trace. -/
theorem terminalReplay_inverse_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (terminalReplay false) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Z 0 (run (terminalReplay false) m s) := by
  let A := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (Y,Y)
  let B := groupsPayload false origin 1 169 A
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have old : skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) (packetLetters 0)) B=(2*Z,0) := by
    have result := EntryInversePayload.inverse_boundary origin x Y hx0 hx trace
    rw [inverse_groups_succ origin 0 169 A] at result
    exact result
  have removed := inverseZeroPayload_of_old origin B.1 B.2 Z old
  let P : State → State → Prop := fun initial out => EncodedFieldFrame base (base 2409) origin Y Y initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin Z 0 out
  have all := run_three_states (renameProgram allPlaced (logicalCell false 510))
    (mappedGroups false 1 169) (firstGroup false) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have first := trimCell_step false hn hlo ho hp hf origin hg0 hs0 env legal Y Y initial m1 hin
      rw [h1] at first
      have frame1 : EncodedFieldFrame base (base 2409) origin A.1 A.2 s1 := by
        simpa only [directionalPayload,Bool.not_false,if_true,A] using first.2.2
      have later := mappedGroups_frame false 1 169 (by decide) hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf) origin hg0 hs0 env legal
        A.1 A.2 s1 m2 frame1
      rw [h2] at later
      have last := firstGroup_inverse_step hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal B.1 B.2 s2 m3 later.2.2
      rw [h3,removed] at last
      exact ⟨last.1.trans (later.2.1.trans first.2.1),last.2⟩) s m input
  have shape : terminalReplay false=renameProgram allPlaced (logicalCell false 510)++
      (mappedGroups false 1 169++firstGroup false) := by
    simp only [terminalReplay,Bool.false_eq_true,if_false,List.append_assoc]
  rw [←shape] at all
  exact all

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
end

-- source: ECDSAAdd/Arithmetic/PenultimateMappedProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.PenultimateMapped
open Secp256k1 MappedCompressed CompressedAllocation
attribute [local irreducible] run wires toffoliCount measurementCount logicalCell

/-- Keep all packets and the entry cancellation; replace only raw cell510. -/
def replay (divide : Bool) : Program :=
  if divide then EntryMappedFieldSegmentTrim.firstGroup divide ++ mappedGroups divide 1 169 ++
      renameProgram allPlaced (PenultimateSwapIdentity.cell divide)
  else renameProgram allPlaced (PenultimateSwapIdentity.cell divide) ++
      mappedGroups divide 1 169 ++ EntryMappedFieldSegmentTrim.firstGroup divide

def fieldSegment (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (converterPair false) ++ replay divide ++
  renameProgram allPlaced (converterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

theorem replay_counts (divide : Bool) :
    toffoliCount (replay divide)=(if divide then 653990 else 654500) ∧ measurementCount (replay divide)=522920 := by
  have groups := mappedGroups_counts divide 1 169
  have first := EntryMappedFieldSegmentTrim.firstGroup_counts divide
  have cell := PenultimateSwapIdentity.cell_counts divide
  have renamed := renameProgram_counts allPlaced (PenultimateSwapIdentity.cell divide)
  cases divide <;> simp only [replay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,groups.1,groups.2,first.1,first.2,
    renamed.1,renamed.2,cell.1,cell.2]
  all_goals norm_num

theorem fieldSegment_counts (divide : Bool) :
    toffoliCount (fieldSegment divide)=(if divide then 657050 else 657560) ∧ measurementCount (fieldSegment divide)=525980 := by
  have old := EntryMappedFieldSegmentTrim.terminalFieldSegment_counts divide
  have oldReplay := EntryMappedFieldSegmentTrim.terminalReplay_counts divide
  have fresh := replay_counts divide
  simp only [EntryMappedFieldSegmentTrim.terminalFieldSegment,toffoliCount_append,
    measurementCount_append,oldReplay.1,oldReplay.2] at old
  simp only [fieldSegment,toffoliCount_append,measurementCount_append,fresh.1,fresh.2]
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at old oldReplay fresh ⊢
  all_goals constructor <;> omega

end ECDSAAdd.Arithmetic.PenultimateMapped
end

-- source: ECDSAAdd/Framework/CertifiedProgram.lean
noncomputable section

namespace ECDSAAdd

/-- Kernel-sealed executable packaging, with its original code certified in
the result type. No proof proposition or evaluator result is assumed. -/
noncomputable def certifiedProgram (P : Program) : {Q : Program // Q=P} :=
  Classical.choice ⟨⟨P,rfl⟩⟩

noncomputable def sealedProgram (P : Program) : Program := (certifiedProgram P).val

theorem sealedProgram_eq (P : Program) : sealedProgram P=P :=
  (certifiedProgram P).property

theorem sealedProgram_run (P : Program) (m : List Bool) (s : State) :
    run (sealedProgram P) m s=run P m s :=
  congrArg (fun Q : Program => run Q m s) (sealedProgram_eq P)

theorem sealedProgram_cost (P : Program) :
    toffoliCount (sealedProgram P)=toffoliCount P ∧
    measurementCount (sealedProgram P)=measurementCount P ∧
    wires (sealedProgram P)=wires P := by
  rw [sealedProgram_eq]
  exact ⟨rfl,rfl,rfl⟩

end ECDSAAdd
end

-- source: ECDSAAdd/Framework/ProgramContextEq.lean
noncomputable section

namespace ECDSAAdd
attribute [local irreducible] run measurementCount

end ECDSAAdd
end

-- source: ECDSAAdd/Framework/RecordPadding.lean
noncomputable section

namespace ECDSAAdd

/-- Missing records are already interpreted as false by run. -/
theorem run_replicate_false (P : Program) (n : Nat) (s : State) :
    run P (List.replicate n false) s=run P [] s := by
  induction P generalizing n s with
  | nil => rfl
  | cons i P ih =>
    cases i with
    | X t => exact ih n _
    | CX c t => exact ih n _
    | CCX a b t => exact ih n _
    | measureX t c0 c1 =>
      cases n with
      | zero => rfl
      | succ n => simpa only [List.replicate_succ,run,List.headD_cons,List.tail_cons,
          List.headD_nil,List.tail_nil] using ih n (measureAndCorrect t c0 c1 false s)

/-- Padding a finite measurement tape by false preserves every State. -/
theorem run_pad_false (P : Program) (m : List Bool) (n : Nat) (s : State) :
    run P (m++List.replicate n false) s=run P m s := by
  induction P generalizing m s with
  | nil => rfl
  | cons i P ih =>
    cases i with
    | X t => exact ih m _
    | CX c t => exact ih m _
    | CCX a b t => exact ih m _
    | measureX t c0 c1 =>
      cases m with
      | nil => simpa only [List.nil_append] using
          run_replicate_false (.measureX t c0 c1::P) n s
      | cons b m =>
          simpa only [List.cons_append,run,List.headD_cons,List.tail_cons] using
            (ih m (measureAndCorrect t c0 c1 b s))

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/PenultimateMappedForward.lean
noncomputable section

set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.PenultimateMapped
open Secp256k1 MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run groupsPayload indexedLetters packetLetters
  mixedTranscriptTape mixedTranscriptUnitTrace mappedGroups logicalCell
  EntryMappedFieldSegmentTrim.firstGroup measurementCount
  PenultimateSwapIdentity.cell PenultimateSwapIdentity.penultimatePayload fieldSegment replay
  baseGroups converterPair copyPairAt

private theorem replay_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)

private theorem packet_indexed (j : Nat) : packetLetters j=indexedLetters (3*j) 3 := by
  simp [packetLetters,indexedLetters,tapeLetter,List.range_succ]

private theorem groups_succ (origin : BasisState) (j n : Nat) (Q : Fp×Fp) :
    groupsPayload true origin j (n+1) Q=groupsPayload true origin (j+1) n
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters j)) Q) := by
  simp only [groupsPayload,if_true,Bool.not_true,directionalPayload,Bool.false_eq_true,if_false]

/-- Abstract packet recursion avoids expanding the concrete170-packet list. -/
theorem forward_groups_payload (j n : Nat) (origin : BasisState) (Q : Fp×Fp) :
    groupsPayload true origin j n Q=
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
        (indexedLetters (3*j) (3*n))) Q := by
  induction n generalizing j Q with
  | zero => simp only [groupsPayload,indexedLetters,Nat.mul_zero,List.range_zero,List.map_nil,
      mixedTranscriptControls,skywalkPayloadReplay]
  | succ n ih =>
    have len : 3*(n+1)=3+3*n := by omega
    have start : 3*(j+1)=3*j+3 := by omega
    rw [groups_succ,len,indexedLetters_append]
    simp only [mixedTranscriptControls,List.map_append,replay_append,ih,start,←packet_indexed]

private def rawPrefix : Program := renameProgram allPlaced (converterPair false) ++
  (EntryMappedFieldSegmentTrim.firstGroup true ++ mappedGroups true 1 169)
attribute [local irreducible] rawPrefix

/- Head States agree when their internal prefix records coincide; local cell
records remain independent. This record condition is proved by construction in
the public wrapper and adds no public input or outcome restriction. -/

end ECDSAAdd.Arithmetic.PenultimateMapped
end

-- source: ECDSAAdd/Arithmetic/PenultimateMappedInverse.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.PenultimateMapped
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run measurementCount logicalCell mappedGroups

private def oldHead_PenultimateMappedInverse : Program := renameProgram allPlaced (logicalCell false 510)
private def newHead_PenultimateMappedInverse : Program := renameProgram allPlaced (PenultimateSwapIdentity.cell false)
private def commonSuffix : Program := mappedGroups false 1 169 ++
  EntryMappedFieldSegmentTrim.firstGroup false

private theorem replay_inverse_join : replay false=newHead_PenultimateMappedInverse++commonSuffix := by
  simp only [replay,newHead_PenultimateMappedInverse,commonSuffix,Bool.false_eq_true,if_false,List.append_assoc]

private theorem old_replay_inverse_join :
    EntryMappedFieldSegmentTrim.terminalReplay false=oldHead_PenultimateMappedInverse++commonSuffix := by
  simp only [EntryMappedFieldSegmentTrim.terminalReplay,oldHead_PenultimateMappedInverse,commonSuffix,
    Bool.false_eq_true,if_false,List.append_assoc]

-- Keep programs symbolic so kernel conversion does not evaluate concrete gate lists.
private theorem replace_prefix (P Q R : Program) (s : State) (m : List Bool)
    (same : ∀ a b, run P a s = run Q b s) :
    run (P ++ R) (List.replicate (measurementCount P) false ++
      m.drop (measurementCount Q)) s = run (Q ++ R) m s := by
  rw [run_append,run_append,same _ (m.take (measurementCount Q))]
  simp only [List.drop_append,List.length_replicate,Nat.sub_self,List.drop_zero,
    List.drop_replicate,List.replicate_zero,List.nil_append]

/-- Complete encoded inverse replay under the existing caller domain.
Only cell510 changes; the common packet/entry suffix keeps its actual record
stream, and the legacy head uses an independent padded record prefix. -/
theorem replay_inverse_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Z 0 (run (replay false) m s) := by
  let records := List.replicate (measurementCount oldHead_PenultimateMappedInverse) false ++
    m.drop (measurementCount newHead_PenultimateMappedInverse)
  have old := EntryMappedFieldSegmentTrim.terminalReplay_inverse_spec hn hlo ho hp hf
    origin hg0 hs0 env legal x Y hx0 hx trace s records input
  have stateEq : run (replay false) m s=
      run (EntryMappedFieldSegmentTrim.terminalReplay false) records s := by
    rw [replay_inverse_join,old_replay_inverse_join]
    exact (replace_prefix oldHead_PenultimateMappedInverse newHead_PenultimateMappedInverse commonSuffix s m (fun a b =>
      (PenultimateMappedCellProof.inverse_cell_eq hn hlo ho hp hf
        origin hg0 hs0 env legal Y s b a input).symm)).symm
  rw [←stateEq] at old
  exact old

end ECDSAAdd.Arithmetic.PenultimateMapped
end

-- source: ECDSAAdd/Arithmetic/PenultimateMappedResources.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.PenultimateMapped
open Secp256k1 MappedCompressed CompressedAllocation
attribute [local irreducible] wires logicalCell PenultimateSwapIdentity.cell
  EntryMappedFieldSegmentTrim.firstGroup mappedGroups mixedTranscriptUnitTrace

private theorem append_mono (A B C D : Program)
    (ha : wires A⊆wires C) (hb : wires B⊆wires D) :
    wires (A++B)⊆wires (C++D) := by
  rw [wires_append,wires_append]
  exact Finset.union_subset_union ha hb

theorem replay_support_sub (divide : Bool) :
    wires (replay divide)⊆wires (EntryMappedFieldSegmentTrim.terminalReplay divide) := by
  have small := PenultimateMappedCellProof.support_subset divide
  cases divide
  · simpa only [replay,EntryMappedFieldSegmentTrim.terminalReplay,Bool.false_eq_true,if_false]
      using append_mono _ _ _ _
        (append_mono _ _ _ _ small (Finset.Subset.refl _)) (Finset.Subset.refl _)
  · simpa only [replay,EntryMappedFieldSegmentTrim.terminalReplay,if_true]
      using append_mono _ _ _ _ (Finset.Subset.refl _) small

theorem fieldSegment_support_sub (divide : Bool) :
    wires (fieldSegment divide)⊆wires (EntryMappedFieldSegmentTrim.terminalFieldSegment divide) := by
  let P : Program := if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)
  let C : Program := renameProgram allPlaced (converterPair false)
  let D : Program := renameProgram allPlaced (converterPair true)
  let S : Program := if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else []
  have middle := append_mono (P++C) (replay divide) (P++C)
    (EntryMappedFieldSegmentTrim.terminalReplay divide) (Finset.Subset.refl _)
    (replay_support_sub divide)
  have tail := append_mono _ D _ D middle (Finset.Subset.refl _)
  have whole := append_mono _ S _ S tail (Finset.Subset.refl _)
  simpa only [fieldSegment,EntryMappedFieldSegmentTrim.terminalFieldSegment,P,C,D,S]
    using whole

theorem fieldSegment_support (divide : Bool) :
    wires (fieldSegment divide)⊆slots.toFinset :=
  (fieldSegment_support_sub divide).trans
    (EntryMappedFieldSegmentTrim.terminalFieldSegment_support divide)

end ECDSAAdd.Arithmetic.PenultimateMapped
end

-- source: ECDSAAdd/Arithmetic/EntryForwardSelectedFieldSegment.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run wires toffoliCount measurementCount

/-- Both exact entry cancellations retain the terminal omission and remove the
penultimate equal-word swap. The original field contract and all 512 native
integer recording rounds remain unchanged. -/
def selectedFieldSegment (divide : Bool) : Program :=
  PenultimateMapped.fieldSegment divide

theorem selectedFieldSegment_support (divide : Bool) :
    wires (selectedFieldSegment divide) ⊆ slots.toFinset :=
  PenultimateMapped.fieldSegment_support divide

theorem selectedFieldSegment_counts (divide : Bool) :
    toffoliCount (selectedFieldSegment divide)=(if divide then 657050 else 657560) ∧
    measurementCount (selectedFieldSegment divide)=525980 :=
  PenultimateMapped.fieldSegment_counts divide

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectProgram.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open Secp256k1

def hConstant : Nat := (p+1)/2
def kConstant (inverse odd : Bool) : Nat :=
  if inverse then if odd then (p-1)/2 else 2^258-p
  else if odd then 2^258-(p-1)/2 else p

def hBits (w : Nat → Wire) (inverse : Bool) : List MappedBit :=
  (List.range 253).map (fun j =>
    if (if inverse then 2^256-hConstant else hConstant).testBit (j+3)
    then {wire:=some (w 1028),flip:=false} else {wire:=none,flip:=false})

def kBits (w : Nat → Wire) (inverse : Bool) : List MappedBit :=
  (List.range 257).map (fun j =>
    let a := (kConstant inverse false).testBit (j+1)
    let b := (kConstant inverse true).testBit (j+1)
    if a=b then {wire:=none,flip:=a}
    else {wire:=some (w 1028),flip:=a})

def hAdd (w : Nat → Wire) (inverse : Bool) : Program :=
  mappedAdd (hBits w inverse) (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)

def kAdd (w : Nat → Wire) (inverse : Bool) : Program :=
  mappedAdd (kBits w inverse) (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)++
    [.X (w 770)]

def lowCopy (w : Nat → Wire) : Program :=
  copyRegister none (wireBlock w 771 255) (wireBlock w 1 255)

def forward (w : Nat → Wire) : Program :=
  [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]++
  lowCopy w++hAdd w false++[.CX (w 1028) (w 770)]++
  rotateRight (wireBlock w 770 258)++kAdd w false

def inverse (w : Nat → Wire) : Program :=
  kAdd w true++rotateLeft (wireBlock w 770 258)++
  [.CX (w 1028) (w 770)]++hAdd w true++lowCopy w++
  [.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)]

theorem hBits_length (w : Nat → Wire) (inverse : Bool) :
    (hBits w inverse).length=253 := by simp [hBits]
theorem kBits_length (w : Nat → Wire) (inverse : Bool) :
    (kBits w inverse).length=257 := by simp [kBits]

theorem hAdd_counts (w : Nat → Wire) (inverse : Bool) :
    toffoliCount (hAdd w inverse)=252 ∧ measurementCount (hAdd w inverse)=252 := by
  have h := mappedAdd_counts (hBits w inverse) (wireBlock w 4 253)
    (wireBlock w 1540 252) (w 1797)
    (by simp [hBits_length,wireBlock_length]) (by simp [wireBlock_length])
  simpa [hAdd,wireBlock_length] using h

theorem kAdd_counts (w : Nat → Wire) (inverse : Bool) :
    toffoliCount (kAdd w inverse)=256 ∧ measurementCount (kAdd w inverse)=256 := by
  have h := mappedAdd_counts (kBits w inverse) (wireBlock w 771 257)
    (wireBlock w 1540 256) (w 770)
    (by simp [kBits_length,wireBlock_length]) (by simp [wireBlock_length])
  simp only [wireBlock_length] at h
  simp [kAdd,toffoliCount_append,measurementCount_append,h.1,h.2,toffoliCount,measurementCount]

theorem lowCopy_counts (w : Nat → Wire) :
    toffoliCount (lowCopy w)=0 ∧ measurementCount (lowCopy w)=0 := by
  have h := copyRegister_counts none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length])
  simpa [lowCopy] using h

theorem forward_counts (w : Nat → Wire) :
    toffoliCount (forward w)=508 ∧ measurementCount (forward w)=508 := by
  have h := hAdd_counts w false
  have k := kAdd_counts w false
  have c := lowCopy_counts w
  have r := rotate_counts (wireBlock w 770 258)
  simp [forward,toffoliCount_append,measurementCount_append,h.1,h.2,k.1,k.2,
    c.1,c.2,r.1,r.2.1,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectLayout.lean
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect

theorem index_ne (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<1798) (hj : j<1798) (hne : i≠j) : w i≠w j := by
  intro h
  exact hne (skywalkPool_index_inj w hn i j hi hj h)

theorem block_not_mem (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i a n : Nat) (hi : i<1798) (ha : a+n≤1798)
    (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n := by
  intro h
  obtain ⟨j,hj,he⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  have eq := skywalkPool_index_inj w hn i j hi (by omega) he.symm
  omega

theorem block_nodup (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj he
    simp only [List.mem_range'_1] at hi hj
    exact skywalkPool_index_inj w hn i j (by omega) (by omega) he
  · exact List.nodup_range'

theorem block_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798)
    (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := by
  apply List.disjoint_left.mpr
  intro q hq hk
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
  obtain ⟨j,hj,hf⟩ := List.mem_map.mp hk
  simp only [List.mem_range'_1] at hi hj
  have eq := skywalkPool_index_inj w hn i j (by omega) (by omega) (he.trans hf.symm)
  omega

theorem block_subset (w : Nat → Wire) (a n m : Nat) (h : n≤m) :
    ∀q∈wireBlock w a n,q∈wireBlock w a m := by
  intro q hq
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
  apply List.mem_map.mpr
  refine ⟨i,?_,he⟩
  simp only [List.mem_range'_1] at hi ⊢
  omega

private theorem two_ranges_nd (a n b m : Nat) (sep : a+n≤b) :
    (List.range' a n++List.range' b m).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_range',List.nodup_range',?_⟩
  apply List.disjoint_left.mpr
  intro q hq hk
  simp only [List.mem_range'_1] at hq hk
  omega

private theorem map_pool_nd (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ids : List Nat) (hi : ∀i∈ids,i<1798) (hd : ids.Nodup) : (ids.map w).Nodup := by
  apply List.Nodup.map_on
  · intro i him j hjm he
    exact skywalkPool_index_inj w hn i j (hi i him) (hi j hjm) he
  · exact hd

theorem h_inputs_nd (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup := by
  have hd : (1797::(List.range' 4 253++List.range' 1540 252)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,two_ranges_nd 4 253 1540 252 (by omega)⟩
    intro h
    simp only [List.mem_append,List.mem_range'_1] at h
    omega
  have a := map_pool_nd w hn _ (by
    intro i hi
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hi
    omega) hd
  simpa only [List.map_cons,List.map_append,wireBlock] using a

theorem k_inputs_nd (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup := by
  have hd : (770::(List.range' 771 257++List.range' 1540 256)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,two_ranges_nd 771 257 1540 256 (by omega)⟩
    intro h
    simp only [List.mem_append,List.mem_range'_1] at h
    omega
  have a := map_pool_nd w hn _ (by
    intro i hi
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hi
    omega) hd
  simpa only [List.map_cons,List.map_append,wireBlock] using a

private theorem flag_choice_wire (flag q : Wire) (bit : Bool)
    (hq : q∈(if bit then ({wire:=some flag,flip:=false} : MappedBit)
      else {wire:=none,flip:=false}).wire.toList) : q=flag := by
  cases bit <;> simp_all

theorem hBits_wire (w : Nat → Wire) (inverse : Bool) (q : Wire)
    (hq : q∈mappedWires (hBits w inverse)) : q=w 1028 := by
  obtain ⟨bit,hbit,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hbit
  exact flag_choice_wire (w 1028) q
    ((if inverse then 2^256-hConstant else hConstant).testBit (j+3)) hq

theorem kBits_wire (w : Nat → Wire) (inverse : Bool) (q : Wire)
    (hq : q∈mappedWires (kBits w inverse)) : q=w 1028 := by
  obtain ⟨bit,hbit,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hbit
  dsimp only at hq
  split at hq <;> simp_all

theorem h_sources_fresh (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (inverse : Bool) : ∀q∈mappedWires (hBits w inverse),
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252) := by
  intro q hq
  rw [hBits_wire w inverse q hq]
  simp only [List.mem_cons,List.mem_append,not_or]
  exact ⟨index_ne w hn 1028 1797 (by omega) (by omega) (by omega),
    block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega),
    block_not_mem w hn 1028 1540 252 (by omega) (by omega) (by omega)⟩

theorem k_sources_fresh (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (inverse : Bool) : ∀q∈mappedWires (kBits w inverse),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256) := by
  intro q hq
  rw [kBits_wire w inverse q hq]
  simp only [List.mem_cons,List.mem_append,not_or]
  exact ⟨index_ne w hn 1028 770 (by omega) (by omega) (by omega),
    block_not_mem w hn 1028 771 257 (by omega) (by omega) (by omega),
    block_not_mem w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩

theorem copy_inputs_nd (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    (wireBlock w 771 255++wireBlock w 1 255).Nodup := by
  exact List.nodup_append'.mpr ⟨block_nodup w hn _ _ (by omega),
    block_nodup w hn _ _ (by omega),block_disjoint w hn _ _ _ _ (by omega) (by omega) (by omega)⟩

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectSupport.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] mappedAdd hAdd kAdd lowCopy forward inverse wires

/-- All actual quantum sites, including retained sign and carry-in. -/
def prefixSites (w : Nat → Wire) : List Wire :=
  wireBlock w 0 257 ++ wireBlock w 770 258 ++ wireBlock w 1540 256 ++
    [w 1028,w 1797]

private theorem block_inside (w : Nat → Wire) (a n : Nat)
    (ha : a+n≤257 ∨ (770≤a ∧ a+n≤1028) ∨ (1540≤a ∧ a+n≤1796)) :
    ∀q∈wireBlock w a n,q∈prefixSites w := by
  intro q hq
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have mem (b m : Nat) (hb : b ≤ i ∧ i < b+m) : q∈wireBlock w b m := by
    apply List.mem_map.mpr
    exact ⟨i,by simpa only [List.mem_range'_1] using hb,he⟩
  simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases ha with h|h|h
  · exact Or.inl (Or.inl (Or.inl (mem 0 257 (by omega))))
  · exact Or.inl (Or.inl (Or.inr (mem 770 258 (by omega))))
  · exact Or.inl (Or.inr (mem 1540 256 (by omega)))

private theorem scalar_inside (w : Nat → Wire) (i : Nat)
    (hi : i=0 ∨ i=770 ∨ i=1028 ∨ i=1797) : w i∈prefixSites w := by
  rcases hi with rfl|rfl|rfl|rfl
  · exact block_inside w 0 257 (by omega) _ (by simp [wireBlock,List.range'])
  · exact block_inside w 770 258 (by omega) _ (by simp [wireBlock,List.range'])
  · simp [prefixSites]
  · simp [prefixSites]

private theorem h_support (w : Nat → Wire) (inv : Bool) :
    wires (hAdd w inv) ⊆ (prefixSites w).toFinset := by
  rw [hAdd]
  apply Finset.Subset.trans (mappedAdd_wires_subset (hBits w inv)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797))
  intro q hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  rcases hq with ((hq|hq)|hq)|hq
  · rw [hBits_wire w inv q hq]
    exact scalar_inside w 1028 (by omega)
  · exact block_inside w 4 253 (by omega) q hq
  · exact block_inside w 1540 252 (by omega) q hq
  · subst q; exact scalar_inside w 1797 (by omega)

private theorem k_support (w : Nat → Wire) (inv : Bool) :
    wires (kAdd w inv) ⊆ (prefixSites w).toFinset := by
  intro q hq
  simp only [kAdd,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have h := mappedAdd_wires_subset (kBits w inv) (wireBlock w 771 257)
      (wireBlock w 1540 256) (w 770) hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    apply List.mem_toFinset.mpr
    rcases h with ((h|h)|h)|h
    · rw [kBits_wire w inv q h]; exact scalar_inside w 1028 (by omega)
    · exact block_inside w 771 257 (by omega) q h
    · exact block_inside w 1540 256 (by omega) q h
    · subst q; exact scalar_inside w 770 (by omega)
  · have eq : q=w 770 := by simpa [wires,Instr.wires] using hq
    subst q; exact List.mem_toFinset.mpr (scalar_inside w 770 (by omega))

private theorem copy_support (w : Nat → Wire) :
    wires (lowCopy w) ⊆ (prefixSites w).toFinset := by
  have hn : wireBlock w 771 255 ≠ [] := by
    intro h
    have hl := wireBlock_length w 771 255
    rw [h] at hl
    simp at hl
  rw [lowCopy,copyRegister_wires none _ _ (by simp [wireBlock_length])]
  simp only [List.isEmpty_iff,hn,if_false,Option.toList_none,List.nil_append]
  intro q hq
  simp only [List.mem_toFinset,List.mem_append] at hq
  apply List.mem_toFinset.mpr
  rcases hq with hq|hq
  · exact block_inside w 771 255 (by omega) q hq
  · exact block_inside w 1 255 (by omega) q hq

theorem prefix_support (w : Nat → Wire) :
    wires (forward w) ⊆ (prefixSites w).toFinset ∧
    wires (inverse w) ⊆ (prefixSites w).toFinset := by
  have hr := rotate_wires (wireBlock w 770 258)
  simp only [wireBlock_length,show ¬(258<2) by omega,if_false] at hr
  have rR : wires (rotateRight (wireBlock w 770 258)) ⊆ (prefixSites w).toFinset := by
    intro q hq
    rw [hr.1] at hq
    exact List.mem_toFinset.mpr (block_inside w 770 258 (by omega) q (List.mem_toFinset.mp hq))
  have rL : wires (rotateLeft (wireBlock w 770 258)) ⊆ (prefixSites w).toFinset := by
    intro q hq
    rw [hr.2] at hq
    exact List.mem_toFinset.mpr (block_inside w 770 258 (by omega) q (List.mem_toFinset.mp hq))
  have h0 := List.mem_toFinset.mpr (scalar_inside w 0 (by omega))
  have hB := List.mem_toFinset.mpr (scalar_inside w 770 (by omega))
  have hS := List.mem_toFinset.mpr (scalar_inside w 1028 (by omega))
  constructor <;> intro q hq
  · simp only [forward,wires_append,Finset.mem_union] at hq
    rcases hq with ((((hq|hq)|hq)|hq)|hq)|hq
    · simp [wires,Instr.wires] at hq
      rcases hq with rfl|rfl|rfl <;> assumption
    · exact copy_support w hq
    · exact h_support w false hq
    · simp [wires,Instr.wires] at hq
      rcases hq with rfl|rfl <;> assumption
    · exact rR hq
    · exact k_support w false hq
  · simp only [inverse,wires_append,Finset.mem_union] at hq
    rcases hq with ((((hq|hq)|hq)|hq)|hq)|hq
    · exact k_support w true hq
    · exact rL hq
    · simp [wires,Instr.wires] at hq
      rcases hq with rfl|rfl <;> assumption
    · exact h_support w true hq
    · exact copy_support w hq
    · simp [wires,Instr.wires] at hq
      rcases hq with rfl|rfl|rfl <;> assumption

theorem prefix_pool_subset (w : Nat → Wire) :
    prefixSites w ⊆ skywalkPoolWires w := by
  intro q hq
  simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
  rcases hq with ((hq|hq)|hq)|(hq|hq)
  all_goals first
    | obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact ⟨i,by omega,he⟩
    | subst q; exact ⟨1028,by omega,rfl⟩
    | subst q; exact ⟨1797,by omega,rfl⟩

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/KnownOutputAdder.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.KnownOutputAdder

def boolValue : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*boolValue bs

def sumBits : List MappedBit → List Wire → Bool → BasisState → List Bool
  | b::bs,y::ys,c,s =>
      sumBit (b.value s) (s y) c :: sumBits bs ys (carryBit (b.value s) (s y) c) s
  | _,_,_,_ => []

theorem sumBits_length (bits : List MappedBit) (ys : List Wire) (c : Bool)
    (s : BasisState) (hl : bits.length=ys.length) :
    (sumBits bits ys c s).length=ys.length := by
  induction ys generalizing bits c with
  | nil => simp [sumBits]
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs => simp [sumBits,ih bs _ (by simpa using hl)]

theorem sumBits_value (bits : List MappedBit) (ys : List Wire) (c : Bool)
    (s : BasisState) (hl : bits.length=ys.length) :
    boolValue (sumBits bits ys c s)=
      (mappedValue bits s+regValue ys s+c.toNat)%2^ys.length := by
  induction ys generalizing bits c with
  | nil =>
    have h : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [h,sumBits,boolValue,mappedValue,regValue,Nat.mod_one]
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      rw [sumBits,boolValue,ih bs _ (by simpa using hl)]
      simpa only [mappedValue,regValue,List.length_cons,List.foldr_cons,
        Bool.toNat,Bool.cond_eq_ite] using
        sum_value_step (b.value s) (s y) c (mappedValue bs s) (regValue ys s) ys.length

theorem boolValue_injective (xs ys : List Bool) (hl : xs.length=ys.length)
    (hv : boolValue xs=boolValue ys) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    have h : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    simp [h]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [boolValue] at hv
      have bits : x=y := by
        cases x <;> cases y <;> simp only [Bool.toNat_false,Bool.toNat_true] at hv ⊢
        all_goals first | rfl | omega
      subst y
      have tails : boolValue xs=boolValue ys := by omega
      exact congrArg (List.cons x) (ih ys (by simpa using hl) tails)

theorem mapped_boolValue (bits : List MappedBit) (s : BasisState) :
    boolValue (bits.map (fun b => b.value s))=mappedValue bits s := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [boolValue,mappedValue,ih]

def Ready (bits sums : List MappedBit) (ys : List Wire) (c : Bool) (s : BasisState) : Prop :=
  sums.map (fun b => b.value s)=sumBits bits ys c s

theorem ready_of_value (bits sums : List MappedBit) (ys : List Wire) (c : Bool)
    (s : BasisState) (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hv : mappedValue sums s=(mappedValue bits s+regValue ys s+c.toNat)%2^ys.length) :
    Ready bits sums ys c s := by
  apply boolValue_injective
  · simp [hs,sumBits_length bits ys c s hl]
  · rw [mapped_boolValue,hv,sumBits_value bits ys c s hl]

def xorBit (b : MappedBit) (target : Wire) : Program :=
  (match b.wire with | none => [] | some a => [.CX a target])++
    (if b.flip then [.X target] else [])

def prepare (b desired : MappedBit) (nextTarget carry : Wire) : Program :=
  [.CX nextTarget carry]++xorBit b carry++xorBit desired carry

/-- Same full bank as the ordinary adder. Its carry producers are replaced
by affine reads of a disjoint, immutable complete sum witness. -/
def program : List MappedBit → List Wire → List MappedBit → List Wire → Wire → Program
  | b::b'::bs,y::y'::ys,d::d'::ds,c::cs,cin =>
      prepare b' d' y' c++program (b'::bs) (y'::ys) (d'::ds) cs c++
        mappedEraseCarry b y cin c++mappedSum b y cin
  | [b],[y],[_],_,cin => mappedSum b y cin
  | _,_,_,_,_ => []

theorem xorBit_counts (b : MappedBit) (target : Wire) :
    toffoliCount (xorBit b target)=0 ∧ measurementCount (xorBit b target)=0 := by
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp [xorBit,hw,hf,toffoliCount,measurementCount]

theorem prepare_counts (b d : MappedBit) (y c : Wire) :
    toffoliCount (prepare b d y c)=0 ∧ measurementCount (prepare b d y c)=0 := by
  have h := xorBit_counts b c
  have k := xorBit_counts d c
  simp [prepare,toffoliCount_append,measurementCount_append,h.1,h.2,k.1,k.2,
    toffoliCount,measurementCount]

theorem program_counts (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) :
    toffoliCount (program bits ys sums carry cin)=0 ∧
    measurementCount (program bits ys sums carry cin)=ys.length-1 := by
  induction ys generalizing bits sums carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp at hs
      | cons d ds =>
        cases ys with
        | nil =>
          have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have hd : ds=[] := List.eq_nil_of_length_eq_zero (by simpa using hs)
          subst bs; subst ds
          have h := mappedBit_counts b y cin cin
          simpa [program] using And.intro h.2.2.2.2.1 h.2.2.2.2.2
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simp at hs
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have h := prepare_counts b' d' y' c
                have t := ih (b'::bs) (d'::ds) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                have k := mappedBit_counts b y cin c
                simp only [program,toffoliCount_append,measurementCount_append,h.1,h.2,
                  t.1,t.2,k.2.2.1,k.2.2.2.1,k.2.2.2.2.1,k.2.2.2.2.2]
                simp

theorem xorBit_correct (b : MappedBit) (target : Wire)
    (ha : ∀q∈b.wire,q≠target) (s : State) (m : List Bool) :
    run (xorBit b target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^ b.value s.basis)⟩ := by
  cases hw : b.wire with
  | none =>
    cases hf : b.flip <;> simp only [xorBit,hw,hf,if_false,if_true,
      Bool.false_eq_true,List.nil_append,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=target <;>
        simp [writeBit,MappedBit.value,hw,hf,hq]
  | some a =>
    have ne : a≠target := ha a (by simp [hw])
    cases hf : b.flip <;> simp only [xorBit,hw,hf,if_false,if_true,
      Bool.false_eq_true,List.cons_append,List.nil_append,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=target
      · subst q
        cases hb : s.basis target <;> cases hx : s.basis a <;>
          simp [writeBit,MappedBit.value,hw,hf,ne,hb,hx]
      · simp [writeBit,hq]

theorem prepare_correct (b d : MappedBit) (y c : Wire)
    (hy : y≠c) (hb : ∀q∈b.wire,q≠c) (hd : ∀q∈d.wire,q≠c)
    (s : State) (m : List Bool) :
    run (prepare b d y c) m s=
      ⟨s.phase,writeBit s.basis c
        (((s.basis c ^^ s.basis y) ^^ b.value s.basis) ^^ d.value s.basis)⟩ := by
  let u : State := ⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis y)⟩
  let v : State := ⟨s.phase,writeBit u.basis c (u.basis c ^^ b.value u.basis)⟩
  have bu : b.value u.basis=b.value s.basis := by
    apply mappedBit_value_congr
    intro q hq
    simp [u,writeBit,hb q hq]
  have dv : d.value v.basis=d.value s.basis := by
    apply mappedBit_value_congr
    intro q hq
    simp [v,u,writeBit,hd q hq]
  have bc := xorBit_counts b c
  have dc := xorBit_counts d c
  rw [prepare]
  simp only [List.append_assoc,run_append,measurementCount,bc.2,
    dc.2,List.take_zero,List.drop_zero,run]
  change run (xorBit d c) m (run (xorBit b c) [] u)=_
  rw [xorBit_correct b c hb u []]
  change run (xorBit d c) m v=_
  rw [xorBit_correct d c hd v m,dv]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=c
  · subst q
    simp only [v,State.basis,writeBit,Function.update_self]
    rw [bu]
    simp [u,writeBit]
  · simp [v,u,writeBit,hq]

private theorem head_source_mem (b : MappedBit) (bs : List MappedBit)
    (q : Wire) (hq : q∈b.wire) : q∈mappedWires (b::bs) := by
  cases hw : b.wire with
  | none => simp [hw] at hq
  | some a =>
    have eq : a=q := by simpa [hw] using hq
    subst a
    simp [mappedWires,hw]

private theorem tail_source_mem (b : MappedBit) (bs : List MappedBit)
    (q : Wire) (hq : q∈mappedWires bs) : q∈mappedWires (b::bs) := by
  exact List.mem_append_right _ hq

theorem sumBits_congr (bits : List MappedBit) (ys : List Wire) (c : Bool)
    (s t : BasisState) (hs : ∀q∈mappedWires bits,s q=t q)
    (hy : ∀q∈ys,s q=t q) : sumBits bits ys c s=sumBits bits ys c t := by
  induction bits generalizing ys c with
  | nil => rfl
  | cons b bs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have bit : b.value s=b.value t := mappedBit_value_congr b s t
        (fun q hq => hs q (head_source_mem b bs q hq))
      simp only [sumBits,bit,hy y (by simp)]
      exact congrArg (List.cons _) (ih ys _
        (fun q hq => hs q (tail_source_mem b bs q hq))
        (fun q hq => hy q (by simp [hq])))

theorem ready_congr (bits sums : List MappedBit) (ys : List Wire) (c : Bool)
    (s t : BasisState) (hs : ∀q∈mappedWires bits,s q=t q)
    (hw : ∀q∈mappedWires sums,s q=t q) (hy : ∀q∈ys,s q=t q)
    (h : Ready bits sums ys c s) : Ready bits sums ys c t := by
  have vals : sums.map (fun b => b.value s)=sums.map (fun b => b.value t) := by
    apply List.map_congr_left
    intro b hb
    apply mappedBit_value_congr
    intro q hq
    apply hw q
    change q∈sums.flatMap (fun b => b.wire.toList)
    apply List.mem_flatMap.mpr
    exact ⟨b,hb,by simpa using hq⟩
  unfold Ready at h ⊢
  rw [←vals,←sumBits_congr bits ys c s t hs hy]
  exact h

/-- Exact program transport on the known-sum subspace. The ordinary mapped
adder remains unrestricted; only this receiver carries the additional premise. -/
theorem program_eq_mappedAdd (bits sums : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hw : ∀q∈mappedWires sums,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (ready : Ready bits sums ys (s.basis cin) s.basis) :
    run (program bits ys sums carry cin) m s=run (mappedAdd bits ys carry cin) m s := by
  induction ys generalizing bits sums carry cin s m with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp at hs
      | cons d ds =>
        cases ys with
        | nil =>
          have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have hd : ds=[] := List.eq_nil_of_length_eq_zero (by simpa using hs)
          subst bs; subst ds
          rfl
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simp at hs
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have cnt := List.nodup_iff_count.mp hn
                have yc : y≠c := by
                  intro bad; have h := cnt c; subst y
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have yc' : y'≠c := by
                  intro bad; have h := cnt c; subst y'
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have cc : cin≠c := by
                  intro bad; have h := cnt c; subst cin
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have ctail : c∉y'::ys := by
                  intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
                  omega
                have ccs : c∉cs := by
                  intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
                  omega
                have three : [y,cin,c].Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro q; have h := cnt q
                  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
                  omega
                have nd : (c::((y'::ys)++cs)).Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro q; have h := cnt q
                  simp only [List.count_cons,List.count_append] at h ⊢
                  omega
                have source : ∀q∈mappedWires (b'::bs),q∉c::((y'::ys)++cs) := by
                  intro q hq bad
                  exact ha q (tail_source_mem b _ q hq)
                    (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have witness : ∀q∈mappedWires (d'::ds),q∉c::((y'::ys)++cs) := by
                  intro q hq bad
                  exact hw q (tail_source_mem d _ q hq)
                    (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have sourceC (q : Wire) (hq : q∈mappedWires (b::b'::bs)) : q≠c := by
                  intro bad; exact ha q hq (by simp [bad])
                have witnessC (q : Wire) (hq : q∈mappedWires (d::d'::ds)) : q≠c := by
                  intro bad; exact hw q hq (by simp [bad])
                let K := carryBit (b.value s.basis) (s.basis y) (s.basis cin)
                let u : State := ⟨s.phase,writeBit s.basis c K⟩
                have clean0 : s.basis c=false := hclean c (by simp)
                have rt : Ready (b'::bs) (d'::ds) (y'::ys) K s.basis := by
                  exact (List.cons.inj ready).2
                have next : d'.value s.basis=sumBit (b'.value s.basis) (s.basis y') K := by
                  exact (List.cons.inj rt).1
                have affine : ((s.basis y' ^^ b'.value s.basis) ^^ d'.value s.basis)=K := by
                  rw [next]
                  cases b'.value s.basis <;> cases s.basis y' <;> cases K <;> decide
                have pre (mm : List Bool) : run (prepare b' d' y' c) mm s=u := by
                  rw [prepare_correct b' d' y' c yc'
                    (fun q hq => sourceC q (tail_source_mem b _ q (head_source_mem b' bs q hq)))
                    (fun q hq => witnessC q (tail_source_mem d _ q (head_source_mem d' ds q hq))) s mm]
                  simp [u,clean0,affine]
                have old (mm : List Bool) : run (mappedMajority b y cin c) mm s=u := by
                  rw [mappedMajority_correct b y cin c three]
                  · simp [u,K,clean0]
                  · intro q hq bad
                    exact ha q (head_source_mem b _ q hq)
                      (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have keep (q : Wire) (hne : q≠c) : u.basis q=s.basis q := by
                  simp [u,writeBit,hne]
                have uc : u.basis c=K := by simp [u,writeBit]
                have tailReady : Ready (b'::bs) (d'::ds) (y'::ys) (u.basis c) u.basis := by
                  rw [uc]
                  apply ready_congr _ _ _ _ s.basis u.basis _ _ _ rt
                  · intro q hq
                    exact (keep q (sourceC q (tail_source_mem b _ q hq))).symm
                  · intro q hq
                    exact (keep q (witnessC q (tail_source_mem d _ q hq))).symm
                  · intro q hq
                    exact (keep q (fun bad => ctail (bad ▸ hq))).symm
                have clean : ∀q∈cs,u.basis q=false := by
                  intro q hq
                  rw [keep q (fun bad => ccs (bad ▸ hq))]
                  exact hclean q (by simp [hq])
                have tail (mm : List Bool) := ih (b'::bs) (d'::ds) cs c nd source witness
                  (by simpa using hl) (by simpa using hs) (by simpa using hc) u mm clean tailReady
                have pc := prepare_counts b' d' y' c
                have oc := mappedBit_counts b y cin c
                have nc := program_counts (b'::bs) (d'::ds) (y'::ys) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                have mc := mappedAdd_counts (b'::bs) (y'::ys) cs c
                  (by simpa using hl) (by simpa using hc)
                rw [program,mappedAdd]
                simp only [List.append_assoc,run_append,run_take,pc.2,oc.2.1,
                  nc.2,mc.2,List.take_zero,List.drop_zero]
                rw [pre,old,tail]

theorem xorBit_support (b : MappedBit) (target : Wire) :
    wires (xorBit b target)⊆(b.wire.toList++[target]).toFinset := by
  intro q hq
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp [xorBit,hw,hf,wires,Instr.wires] at hq ⊢
  all_goals tauto

theorem prepare_support (b d : MappedBit) (y c : Wire) :
    wires (prepare b d y c)⊆(b.wire.toList++d.wire.toList++[y,c]).toFinset := by
  intro q hq
  simp only [prepare,wires_append,Finset.mem_union] at hq
  rcases hq with (hq|hq)|hq
  · have h : q=y ∨ q=c := by simpa [wires,Instr.wires] using hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · have h := xorBit_support b c hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  · have h := xorBit_support d c hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto

theorem program_support (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (program bits ys sums carry cin)⊆
      (mappedWires bits++mappedWires sums++ys++carry++[cin]).toFinset := by
  induction ys generalizing bits sums carry cin with
  | nil => cases bits <;> cases sums <;> simp [program,wires]
  | cons y ys ih =>
    cases bits with
    | nil => simp [program,wires]
    | cons b bs =>
      cases sums with
      | nil => simp [program,wires]
      | cons d ds =>
        cases ys with
        | nil =>
          cases bs with
          | nil =>
            cases ds with
            | nil =>
              apply Finset.Subset.trans (mappedBit_wires b y cin cin).2.2
              intro q hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                or_false,mappedWires,List.flatMap_cons,List.flatMap_nil] at hq ⊢
              tauto
            | cons d' ds => simp [program,wires]
          | cons b' bs => simp [program,wires]
        | cons y' ys =>
          cases bs with
          | nil => simp [program,wires]
          | cons b' bs =>
            cases ds with
            | nil => simp [program,wires]
            | cons d' ds =>
              cases carry with
              | nil => simp [program,wires]
              | cons c cs =>
                intro q hq
                simp only [program,wires_append,Finset.mem_union] at hq
                have p := prepare_support b' d' y' c
                have r := ih (b'::bs) (d'::ds) cs c
                have e := (mappedBit_wires b y cin c).2.1
                have z := (mappedBit_wires b y cin c).2.2
                rcases hq with ((hq|hq)|hq)|hq
                · have h := p hq
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                    or_false,mappedWires,List.flatMap_cons] at h ⊢
                  tauto
                · have h := r hq
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                    or_false,mappedWires,List.flatMap_cons] at h ⊢
                  tauto
                · have h := e hq
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                    or_false,mappedWires,List.flatMap_cons] at h ⊢
                  tauto
                · have h := z hq
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                    or_false,mappedWires,List.flatMap_cons] at h ⊢
                  tauto

end ECDSAAdd.Arithmetic.KnownOutputAdder
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectValues.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect

def hScalar (inverse odd : Bool) : Nat :=
  (List.range 253).foldr (fun j acc =>
    (if (if inverse then 2^256-hConstant else hConstant).testBit (j+3)
      then odd else false).toNat+2*acc) 0

def kScalar (inverse odd : Bool) : Nat :=
  (List.range 257).foldr (fun j acc =>
    (if odd then (kConstant inverse true).testBit (j+1)
      else (kConstant inverse false).testBit (j+1)).toNat+2*acc) 0

/-- Fixed modulus bit constants are reduced by the Lean kernel, without external evaluation. -/
theorem hScalar_value (inverse odd : Bool) :
    hScalar inverse odd=if odd then
      (if inverse then 2^256-hConstant else hConstant)/8 else 0 := by
  cases inverse <;> cases odd <;> decide

theorem kScalar_value (inverse odd : Bool) :
    kScalar inverse odd=kConstant inverse odd/2 := by
  cases inverse <;> cases odd <;> decide

private theorem h_list_value (is : List Nat) (flag : Wire) (inverse : Bool)
    (s : BasisState) :
    mappedValue (is.map (fun j =>
      if (if inverse then 2^256-hConstant else hConstant).testBit (j+3)
      then ({wire:=some flag,flip:=false} : MappedBit)
      else {wire:=none,flip:=false})) s=
      is.foldr (fun j acc =>
        (if (if inverse then 2^256-hConstant else hConstant).testBit (j+3)
          then s flag else false).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih]
    cases h : (if inverse then 2^256-hConstant else hConstant).testBit (j+3) <;>
      simp [h,MappedBit.value]

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem k_list_value (is : List Nat) (flag : Wire) (inverse : Bool)
    (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (kConstant inverse false).testBit (j+1)
      let b := (kConstant inverse true).testBit (j+1)
      if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc =>
        (if s flag then (kConstant inverse true).testBit (j+1)
          else (kConstant inverse false).testBit (j+1)).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem hBits_value (w : Nat → Wire) (inverse : Bool) (s : BasisState) :
    mappedValue (hBits w inverse) s=if s (w 1028) then
      (if inverse then 2^256-hConstant else hConstant)/8 else 0 := by
  rw [hBits,h_list_value]
  exact hScalar_value inverse (s (w 1028))

theorem kBits_value (w : Nat → Wire) (inverse : Bool) (s : BasisState) :
    mappedValue (kBits w inverse) s=kConstant inverse (s (w 1028))/2 := by
  rw [kBits,k_list_value]
  exact kScalar_value inverse (s (w 1028))

theorem hConstant_low_zero : hConstant%8=0 := by decide
theorem kConstant_low_one (inverse odd : Bool) : kConstant inverse odd%2=1 := by
  cases inverse <;> cases odd <;> decide

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectAddProof.lean
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] mappedAdd run

/-- Actual H emission, all records and incoming phases; carry cleaning follows
from the complete outside-target frame. -/
theorem hAdd_spec (w : Nat → Wire) (inverse : Bool) (s : State) (m : List Bool)
    (hn : (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup)
    (hs : ∀q∈mappedWires (hBits w inverse),
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252))
    (hc : ∀q∈wireBlock w 1540 252,s.basis q=false) :
    (run (hAdd w inverse) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 4 253 → (run (hAdd w inverse) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 4 253) (run (hAdd w inverse) m s).basis=
      ((if s.basis (w 1028) then (if inverse then 2^256-hConstant else hConstant)/8 else 0)+
        regValue (wireBlock w 4 253) s.basis+(s.basis (w 1797)).toNat)%2^253 := by
  have a := mappedAdd_correct (hBits w inverse) (wireBlock w 4 253)
    (wireBlock w 1540 252) (w 1797) hn hs
    (by simp [hBits_length,wireBlock_length]) (by simp [wireBlock_length]) s m hc
  simpa only [hAdd,hBits_value,wireBlock_length] using a

def kTail (w : Nat → Wire) (inverse : Bool) : Program :=
  mappedAdd (kBits w inverse) (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)

/-- The head is an immutable carry-in for the actual emitted K tail. -/
theorem kTail_spec (w : Nat → Wire) (inverse : Bool) (s : State) (m : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀q∈mappedWires (kBits w inverse),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    (run (kTail w inverse) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 771 257 → (run (kTail w inverse) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 771 257) (run (kTail w inverse) m s).basis=
      (kConstant inverse (s.basis (w 1028))/2+
        regValue (wireBlock w 771 257) s.basis+(s.basis (w 770)).toNat)%2^257 := by
  have a := mappedAdd_correct (kBits w inverse) (wireBlock w 771 257)
    (wireBlock w 1540 256) (w 770) hn hs
    (by simp [kBits_length,wireBlock_length]) (by simp [wireBlock_length]) s m hc
  simpa only [kTail,kBits_value,wireBlock_length] using a

theorem kAdd_run (w : Nat → Wire) (inverse : Bool) (s : State) (m : List Bool) :
    run (kAdd w inverse) m s=
      let u := run (kTail w inverse) (m.take (measurementCount (kTail w inverse))) s
      ⟨u.phase,writeBit u.basis (w 770) (!(u.basis (w 770)))⟩ := by
  rw [kAdd,run_append]
  simp only [run,kTail]

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectInverseProof.lean
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] mappedAdd run hAdd kAdd kTail

private theorem state_of_value_frame (r : List Wire) (s t : State)
    (hp : t.phase=s.phase) (hv : regValue r t.basis=regValue r s.basis)
    (he : ∀q,q∉r → t.basis q=s.basis q) : t=s := by
  apply congrArg₂ State.mk hp
  funext q
  by_cases hq : q∈r
  · exact (regValue_eq_iff r _ _).mp hv q hq
  · exact he q hq

private theorem mod_add_cancel (a b x M : Nat) (_hM : 0<M)
    (hab : (a+b)%M=0) (hx : x<M) : (b+(a+x)%M)%M=x := by
  have normalize : (b+(a+x)%M)%M=(b+(a+x))%M := by
    simp only [Nat.add_mod,Nat.mod_mod]
  rw [normalize]
  have rearrange : b+(a+x)=a+b+x := by omega
  rw [rearrange,Nat.add_mod,hab,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt hx]

private theorem cons_value (h : Wire) (r : List Wire) (s : BasisState) :
    regValue (h::r) s=(s h).toNat+2*regValue r s := by
  cases hb : s h <;> simp [regValue,hb]
private theorem low_one_mod (C T : Nat) (b : Bool) (hc : C%2=1) :
    (!b).toNat+2*((C/2+T+b.toNat)%2^257)=(b.toNat+2*T+C)%2^258 := by
  have split := Nat.mod_add_div C 2
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true,Bool.not_false,
    Bool.not_true,Nat.add_zero] <;> omega
private theorem toggle_head_value (h : Wire) (r : List Wire) (s : BasisState)
    (ha : h∉r) :
    regValue (h::r) (writeBit s h (!(s h)))=(!s h).toNat+2*regValue r s := by
  have head : (writeBit s h (!(s h))) h=!(s h) := by simp [writeBit]
  have tail : regValue r (writeBit s h (!(s h)))=regValue r s := by
    apply regValue_congr
    intro q hq
    have ne : q≠h := by intro e; subst q; exact ha hq
    simp [writeBit,ne]
  rw [cons_value,head,tail]

theorem hAdd_cancel (w : Nat → Wire) (s : State) (mF mI : List Bool)
    (hn : (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup)
    (hs : ∀i q,q∈mappedWires (hBits w i) →
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252))
    (flag : w 1028∉wireBlock w 4 253)
    (hc : ∀q∈wireBlock w 1540 252,s.basis q=false)
    (cin : s.basis (w 1797)=false) :
    run (hAdd w true) mI (run (hAdd w false) mF s)=s := by
  let t := run (hAdd w false) mF s
  have f := hAdd_spec w false s mF hn (hs false) hc
  have away (q : Wire) (hq : q∈wireBlock w 1540 252) : q∉wireBlock w 4 253 := by
    exact List.disjoint_right.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2 hq
  have caway := (List.nodup_cons.mp hn).1
  have tclean : ∀q∈wireBlock w 1540 252,t.basis q=false := by
    intro q hq; exact (f.2.1 q (away q hq)).trans (hc q hq)
  have i := hAdd_spec w true t mI hn (hs true) tclean
  have tf : t.basis (w 1028)=s.basis (w 1028) := f.2.1 _ flag
  have tc : t.basis (w 1797)=false :=
    (f.2.1 _ (fun h => caway (List.mem_append_left _ h))).trans cin
  have sum : ((if s.basis (w 1028) then (2^256-hConstant)/8 else 0)+
      (if s.basis (w 1028) then hConstant/8 else 0))%2^253=0 := by
    cases s.basis (w 1028) <;> decide
  apply state_of_value_frame (wireBlock w 4 253) s _ (i.1.trans f.1)
  · rw [i.2.2,tf,tc,f.2.2,cin]
    simp only [Bool.toNat_false,Nat.add_zero,if_false]
    apply mod_add_cancel _ _ _ _ (by positivity)
      (by simpa [Nat.add_comm] using sum)
    simpa only [wireBlock_length] using regValue_lt (wireBlock w 4 253) s.basis
  · intro q hq; exact (i.2.1 q hq).trans (f.2.1 q hq)

/-- Full K word, including the delayed low-bit flip. -/
theorem kAdd_spec (w : Nat → Wire) (inv : Bool) (s : State) (m : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀q∈mappedWires (kBits w inv),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    (run (kAdd w inv) m s).phase=s.phase ∧
    (∀q,q∉w 770::wireBlock w 771 257 →
      (run (kAdd w inv) m s).basis q=s.basis q) ∧
    regValue (w 770::wireBlock w 771 257) (run (kAdd w inv) m s).basis=
      (kConstant inv (s.basis (w 1028))+
        regValue (w 770::wireBlock w 771 257) s.basis)%2^258 := by
  have a := kTail_spec w inv s (m.take (measurementCount (kTail w inv))) hn hs hc
  generalize ht : run (kTail w inv) (m.take (measurementCount (kTail w inv))) s=t at a
  have hRun : run (kAdd w inv) m s=
      (⟨t.phase,writeBit t.basis (w 770) (!(t.basis (w 770)))⟩ : State) := by
    rw [kAdd_run,ht]
  have headAway : w 770∉wireBlock w 771 257 := by
    intro h; exact (List.nodup_cons.mp hn).1 (List.mem_append_left _ h)
  have head : t.basis (w 770)=s.basis (w 770) := a.2.1 _ headAway
  rw [hRun]
  dsimp only
  refine ⟨a.1,?_,?_⟩
  · intro q hq
    have parts : q≠w 770 ∧ q∉wireBlock w 771 257 := by
      simpa only [List.mem_cons,not_or] using hq
    have ne := parts.1
    have nt := parts.2
    simpa [writeBit,ne] using a.2.1 q nt
  · rw [toggle_head_value (w 770) (wireBlock w 771 257) t.basis headAway,head,
      a.2.2,cons_value]
    have parity := kConstant_low_one inv (s.basis (w 1028))
    exact (low_one_mod (kConstant inv (s.basis (w 1028)))
      (regValue (wireBlock w 771 257) s.basis) (s.basis (w 770)) parity).trans
        (congrArg (fun z : Nat => z%2^258) (Nat.add_comm _ _))

theorem kAdd_cancel (w : Nat → Wire) (s : State) (mF mI : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀i q,q∈mappedWires (kBits w i) →
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (flag : w 1028∉w 770::wireBlock w 771 257)
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    run (kAdd w true) mI (run (kAdd w false) mF s)=s := by
  let t := run (kAdd w false) mF s
  have f := kAdd_spec w false s mF hn (hs false) hc
  have away (q : Wire) (hq : q∈wireBlock w 1540 256) :
      q∉w 770::wireBlock w 771 257 := by
    have ne : q≠w 770 := by
      intro h; exact (List.nodup_cons.mp hn).1 (List.mem_append_right _ (h ▸ hq))
    have nt := List.disjoint_right.mp
      (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2 hq
    simp [ne,nt]
  have tclean : ∀q∈wireBlock w 1540 256,t.basis q=false := by
    intro q hq; exact (f.2.1 q (away q hq)).trans (hc q hq)
  have i := kAdd_spec w true t mI hn (hs true) tclean
  have tf : t.basis (w 1028)=s.basis (w 1028) := f.2.1 _ flag
  have sum : (kConstant false (s.basis (w 1028))+
      kConstant true (s.basis (w 1028)))%2^258=0 := by
    cases s.basis (w 1028) <;> decide
  apply state_of_value_frame (w 770::wireBlock w 771 257) s _ (i.1.trans f.1)
  · rw [i.2.2,tf,f.2.2]
    apply mod_add_cancel _ _ _ _ (by positivity) sum
    have bound := regValue_lt (w 770::wireBlock w 771 257) s.basis
    simpa only [List.length_cons,wireBlock_length] using bound
  · intro q hq; exact (i.2.1 q hq).trans (f.2.1 q hq)

def inverseFront (w : Nat → Wire) : Program :=
  [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]++lowCopy w
def inverseBack (w : Nat → Wire) : Program :=
  lowCopy w++[.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)]
def inverseMiddle (w : Nat → Wire) : Program :=
  [.CX (w 1028) (w 770)]++rotateRight (wireBlock w 770 258)
def inverseUnmiddle (w : Nat → Wire) : Program :=
  rotateLeft (wireBlock w 770 258)++[.CX (w 1028) (w 770)]

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectInverseWrapper.lean
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run mappedAdd hAdd kAdd kTail forward inverse

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstKnownProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.NativeFirstKnown
open NativeFirstDirect
attribute [local irreducible] KnownOutputAdder.program mappedAdd wires run
  NativeFirstDirect.inverse NativeFirstDirect.forward inverseUnmiddle inverseBack

def desired (w : Nat → Wire) : List MappedBit :=
  mappedRead (wireBlock w 774 252) false++[{wire:=none,flip:=false}]

def hReceiver (w : Nat → Wire) : Program :=
  sealedProgram (KnownOutputAdder.program (hBits w true) (wireBlock w 4 253) (desired w)
    (wireBlock w 1540 252) (w 1797))

/-- Specialized clean-caller inverse; the unrestricted inverse is unchanged. -/
def inverse (w : Nat → Wire) : Program :=
  kAdd w true++inverseUnmiddle w++hReceiver w++inverseBack w

attribute [local irreducible] inverse

theorem desired_length (w : Nat → Wire) : (desired w).length=253 := by
  simp [desired,mappedRead,wireBlock_length]

theorem desired_value (w : Nat → Wire) (s : BasisState) :
    mappedValue (desired w) s=regValue (wireBlock w 774 252) s := by
  simp [desired,mappedValue_append,mappedRead_value,mappedValue,MappedBit.value]

theorem desired_wires (w : Nat → Wire) :
    mappedWires (desired w)=wireBlock w 774 252 := by
  simp only [desired,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    Option.toList_none,List.nil_append,List.append_nil]
  exact mappedRead_wires _ false

theorem desired_fresh (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    ∀q∈mappedWires (desired w),q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252) := by
  intro q hq
  rw [desired_wires] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [List.mem_cons,List.mem_append,not_or]
  exact ⟨index_ne w hn i 1797 (by omega) (by omega) (by omega),
    block_not_mem w hn i 4 253 (by omega) (by omega) (by omega),
    block_not_mem w hn i 1540 252 (by omega) (by omega) (by omega)⟩

theorem hReceiver_counts (w : Nat → Wire) :
    toffoliCount (hReceiver w)=0 ∧ measurementCount (hReceiver w)=252 := by
  have h := KnownOutputAdder.program_counts (hBits w true) (desired w)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
    (by simp [hBits_length,wireBlock_length])
    (by simp [desired_length,wireBlock_length]) (by simp [wireBlock_length])
  simpa only [hReceiver,sealedProgram_eq,wireBlock_length] using h

theorem inverse_counts (w : Nat → Wire) :
    toffoliCount (inverse w)=256 ∧ measurementCount (inverse w)=508 := by
  have k := kAdd_counts w true
  have h := hReceiver_counts w
  have c := lowCopy_counts w
  have r := rotate_counts (wireBlock w 770 258)
  simp [inverse,inverseUnmiddle,inverseBack,toffoliCount_append,measurementCount_append,
    k.1,k.2,h.1,h.2,c.1,c.2,r.2.2.1,r.2.2.2,toffoliCount,measurementCount]

theorem hReceiver_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (hc : ∀q∈wireBlock w 1540 252,s.basis q=false)
    (known : mappedValue (desired w) s.basis=
      (mappedValue (hBits w true) s.basis+regValue (wireBlock w 4 253) s.basis+
        (s.basis (w 1797)).toNat)%2^253) :
    run (hReceiver w) m s=run (hAdd w true) m s := by
  rw [hReceiver,sealedProgram_run]
  apply KnownOutputAdder.program_eq_mappedAdd _ _ _ _ _ (h_inputs_nd w hn)
    (h_sources_fresh w hn true) (desired_fresh w hn)
    (by simp [hBits_length,wireBlock_length])
    (by simp [desired_length,wireBlock_length]) (by simp [wireBlock_length]) s m hc
  exact KnownOutputAdder.ready_of_value _ _ _ _ _
    (by simp [hBits_length,wireBlock_length])
    (by simp [desired_length,wireBlock_length]) (by simpa [wireBlock_length] using known)

attribute [local irreducible] hAdd kAdd lowCopy rotateLeft rotateRight hReceiver

private theorem block_inside (w : Nat → Wire) (a n : Nat)
    (ha : a+n≤257 ∨ (770≤a ∧ a+n≤1028) ∨ (1540≤a ∧ a+n≤1796)) :
    ∀q∈wireBlock w a n,q∈prefixSites w := by
  intro q hq
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have mem (b m : Nat) (hb : b ≤ i ∧ i < b+m) : q∈wireBlock w b m := by
    exact List.mem_map.mpr ⟨i,by simpa only [List.mem_range'_1] using hb,he⟩
  simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases ha with h|h|h
  · exact Or.inl (Or.inl (Or.inl (mem 0 257 (by omega))))
  · exact Or.inl (Or.inl (Or.inr (mem 770 258 (by omega))))
  · exact Or.inl (Or.inr (mem 1540 256 (by omega)))

theorem hReceiver_support (w : Nat → Wire) :
    wires (hReceiver w)⊆(prefixSites w).toFinset := by
  intro q hq
  rw [hReceiver,(sealedProgram_cost _).2.2] at hq
  have h := KnownOutputAdder.program_support (hBits w true) (desired w)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797) hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with (((h|h)|h)|h)|h
  · rw [hBits_wire w true q h]
    simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inl True.intro)
  · rw [desired_wires] at h
    exact block_inside w 774 252 (by omega) q h
  · exact block_inside w 4 253 (by omega) q h
  · exact block_inside w 1540 252 (by omega) q h
  · subst q
    simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr True.intro)

theorem inverse_support (w : Nat → Wire) :
    wires (inverse w)⊆(prefixSites w).toFinset := by
  have old := (prefix_support w).2
  have hK : wires (kAdd w true)⊆wires (NativeFirstDirect.inverse w) := by
    intro q hq
    simp only [NativeFirstDirect.inverse,wires_append,Finset.mem_union]
    tauto
  have hU : wires (inverseUnmiddle w)⊆wires (NativeFirstDirect.inverse w) := by
    intro q hq
    simp only [inverseUnmiddle,wires_append,Finset.mem_union] at hq
    simp only [NativeFirstDirect.inverse,wires_append,Finset.mem_union]
    tauto
  have hB : wires (inverseBack w)⊆wires (NativeFirstDirect.inverse w) := by
    intro q hq
    simp only [inverseBack,wires_append,Finset.mem_union] at hq
    simp only [NativeFirstDirect.inverse,wires_append,Finset.mem_union]
    tauto
  intro q hq
  simp only [inverse,wires_append,Finset.mem_union] at hq
  rcases hq with ((hq|hq)|hq)|hq
  · exact old (hK hq)
  · exact old (hU hq)
  · exact hReceiver_support w hq
  · exact old (hB hq)

end ECDSAAdd.Arithmetic.NativeFirstKnown
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedStageSupport.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation Secp256k1
attribute [local irreducible] wires compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
  NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse

private theorem base_integer_mem (q : Nat) (h : q < 515 ∨ (770 ≤ q ∧ q < 1798)) :
    base q∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold omitted; omega

private theorem tick_layout_support (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout base i).wires.toFinset⊆slots.toFinset := by
  have width := compactSkywalkTick_width_bounds i hi
  have view : (compactSkywalkTickLayout base i).wires =
      ([skywalkPoolPreviousId i,1028+i,i+compactSkywalkTickPreWidth i,i,770]++
      List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
      List.range' 771 (compactSkywalkTickPreWidth i-1)++
      List.range' 1540 (compactSkywalkTickPreWidth i-1)).map base := by
    change base (skywalkPoolPreviousId i)::base (1028+i)::
      base (i+compactSkywalkTickPreWidth i)::base i::base 770::
      ((compactSkywalkTickLayout base i).ah++(compactSkywalkTickLayout base i).bh++
      wireBlock base 1540 (compactSkywalkTickPreWidth i-1)) = _
    rw [compactSkywalkTick_ah base i hi,compactSkywalkTick_bh base i hi]
    simp [wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [List.mem_toFinset,view] at hq
  obtain ⟨old,h,rfl⟩ := List.mem_map.mp hq
  apply base_integer_mem
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  by_cases hz : i=0
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; omega

theorem ticks_support (i : Nat) (hi : i < 512) :
    wires (compactSkywalkTick base i)⊆slots.toFinset ∧
    wires (compactSkywalkReverseTick base i)⊆slots.toFinset :=
  ⟨(compactSkywalkTick_support base i hi base_pool_nodup).trans (tick_layout_support i hi),
   (compactSkywalkReverseTick_support base i hi base_pool_nodup).trans (tick_layout_support i hi)⟩

private theorem base_codec_support (start : Nat) (hs : start+3 ≤ 512) :
    wires (compressedHistoryEncode base start)⊆slots.toFinset ∧
    wires (compressedHistoryDecode base start)⊆slots.toFinset := by
  have lift (P : Program) (he : P=compressedHistoryEncode base start ∨
      P=compressedHistoryDecode base start) : wires P⊆slots.toFinset := by
    intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above start hs P he q hq
    have region := compressedHistoryId_region start hs u
    apply base_integer_mem
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

private theorem delayed_codec_support (i : Nat) (hi : i < 512) :
    wires (compressedPackAfter base i)⊆slots.toFinset ∧
    wires (compressedDecodeBefore base i)⊆slots.toFinset := by
  cases h : compressedPackDue i
  · simp [compressedPackAfter,compressedDecodeBefore,h,wires]
  · have due := compressedPackDue_true i h
    have support := base_codec_support (i-3) (by omega)
    simpa only [compressedPackAfter,compressedDecodeBefore,h,if_true] using support

theorem integer_support (i n : Nat) (h : i+n ≤ 512) :
    wires (compressedCompactForward base i n)⊆slots.toFinset ∧
    wires (compressedCompactReverse base i n)⊆slots.toFinset := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,compressedCompactReverse,wires]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := ticks_support i (by omega)
    have codec := delayed_codec_support i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,wires_append,
      Finset.union_subset_iff,and_assoc]
    exact ⟨tick.1,codec.1,rest.1,rest.2,codec.2,tick.2⟩

theorem clear_support : wires (skywalkArithmeticClear base)⊆slots.toFinset := by
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals apply base_integer_mem; omega

private theorem native_prefix_slots :
    (NativeFirstDirect.prefixSites base).toFinset⊆slots.toFinset := by
  intro q hq
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      apply slot_mem
      · unfold live; omega
      · unfold omitted; omega
    | apply slot_mem
      · unfold live; omega
      · unfold omitted; omega

/-- Exact first native prefix and independent inverse; the remaining ticks,
codec schedule, and selected field program retain their existing allocation. -/
def kernel (divide : Bool) : Program :=
  NativeFirstDirect.forward base++compressedCompactForward base 1 511++
  skywalkArithmeticClear base++selectedFieldSegment divide++skywalkArithmeticClear base++
  compressedCompactReverse base 1 511++NativeFirstKnown.inverse base

theorem kernel_support (divide : Bool) : wires (kernel divide)⊆slots.toFinset := by
  have native := NativeFirstDirect.prefix_support base
  have integer := integer_support 1 511 (by omega)
  simp only [kernel,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨native.1.trans native_prefix_slots,integer.1,clear_support,
    selectedFieldSegment_support divide,clear_support,integer.2,(NativeFirstKnown.inverse_support base).trans native_prefix_slots⟩

def controlled (divide : Bool) : Program :=
  directZeroControlled (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (kernel divide)

private theorem zero_sites :
    (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255)).toFinset⊆slots.toFinset := by
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,wireBlock,
    List.mem_map,List.mem_range'_1] at hq
  rcases hq with rfl|rfl|(h|h)
  · exact slot_mem 2411 (by unfold live; omega) (by unfold omitted; omega)
  · exact slot_mem 2313 (by unfold live; omega) (by unfold omitted; omega)
  all_goals obtain ⟨old,ho,rfl⟩ := h; apply base_integer_mem; omega

theorem controlled_support (divide : Bool) : wires (controlled divide)⊆slots.toFinset := by
  have z := (directZeroDivisor_wires (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411)).trans zero_sites
  rw [wires_append,Finset.union_subset_iff] at z
  simp only [controlled,directZeroControlled,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨z.1,kernel_support divide,z.2⟩

/-- All resident field data and nine caller selectors are counted, even when
an instruction does not touch one of the selector sites. -/
def resident : List Wire := wireBlock base 770 256++wireBlock base 2056 256++wireBlock base 2400 9

theorem resident_support : resident.toFinset⊆slots.toFinset := by
  intro q hq
  simp only [resident,List.mem_toFinset,List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with (h|h)|h
  all_goals
    obtain ⟨old,ho,rfl⟩ := h
    apply slot_mem
    · unfold live; omega
    · unfold omitted; omega

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/RunPoolBasisAgreement.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run wires

/-- Basis locality on a certified pool is independent of incoming phase.
Every correction operand is included in the actual program support. -/
theorem run_pool_basis_agreement (p : Program) (W : Finset Wire)
    (support : wires p⊆W) (s t : State) (m : List Bool)
    (bits : ∀q∈W,s.basis q=t.basis q) :
    ∀q∈W,(run p m s).basis q=(run p m t).basis q := by
  have read : ∀q∈wires p,s.basis q=t.basis q := fun q hq => bits q (support hq)
  have increment := run_local_increment p s t m read
  intro q hq
  by_cases used : q∈wires p
  · exact increment.2 q used
  · exact (run_preserves_outside p m s q used).trans
      ((bits q hq).trans (run_preserves_outside p m t q used).symm)
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/EncodedFieldPoolBasis.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open DirectSkywalk
attribute [local irreducible] run wires

/-- Generic field-frame locality keeps concrete encoder and register
definitions out of kernel checking of the composed caller comparison. -/
theorem encoded_field_pool_basis (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (encoder : Program) (support : wires encoder⊆(skywalkPoolWires w).toFinset)
    (origin : BasisState) (ha : regValue (skywalkSharedField w).a origin=0)
    (X : Nat) (raw s : State)
    (frame : PairFrame (skywalkSharedField w).z (skywalkSharedField w).a origin X 0 raw.basis)
    (encoded : s=run encoder [] raw) :
    ∀q∈skywalkPoolWires w,s.basis q=
      (run encoder [] ({phase:=false,basis:=origin} : State)).basis q := by
  have keeps := arith_field_frame (skywalkSharedField w) origin raw.basis X ha frame
  have rawPool : ∀q∈skywalkPoolWires w,raw.basis q=origin q := by
    intro q hq
    exact keeps q (arith_pool_away_z w hn q hq)
  let ref : State := {phase:=false,basis:=origin}
  rw [encoded]
  intro q hq
  exact run_pool_basis_agreement encoder (skywalkPoolWires w).toFinset support raw ref []
    (fun k hk => rawPool k (List.mem_toFinset.mp hk)) q (List.mem_toFinset.mpr hq)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedFieldPoolRestore.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode compressedEncodePrefix
  compressedCompactForward compressedCompactReverse fieldSegment skywalkArithmeticClear

private theorem encoder_pool_support (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) :
    wires (allGroupEncode base 170)⊆(skywalkPoolWires base).toFinset := by
  have history := compressedPrefix_history_support base (skywalkShared_integer_nodup base hn)
    hlo 512 (by decide)
  rw [encode_prefix_512] at history
  intro q hq
  have member := List.mem_toFinset.mp (history hq)
  simp only [List.mem_append,wireBlock] at member
  rcases member with member|member
  all_goals
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1] at hi ⊢
    exact ⟨i,by omega,rfl⟩

/-- Source zero and the full257-bit frame determine every integer-pool
bit even though the numerator, outside that pool, has already changed. -/
theorem encodedCanonical_pool_basis (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame origin X 0 s) :
    ∀q∈skywalkPoolWires base,s.basis q=
      (run (allGroupEncode base 170) [] ({phase:=false,basis:=origin} : State)).basis q := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have narrow : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using rawFrame
  have support := encoder_pool_support hn hlo
  exact encoded_field_pool_basis base hn (allGroupEncode base 170) support origin ha
    X.val raw s narrow encoded

private theorem clear_pool_support :
    wires (skywalkArithmeticClear base)⊆(skywalkPoolWires base).toFinset := by
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact List.mem_toFinset.mpr (arith_mem base 0 1798 _ (by omega) (by omega))

/-- The second independently recorded clear restores the encoded terminal
pool after a proven pool-preserving field update. -/
theorem clear_after_pool_update (hn : (skywalkSharedWires base).Nodup)
    (recorded field : State) (mFirst mLast : List Bool)
    (phase : field.phase=(run (skywalkArithmeticClear base) mFirst recorded).phase)
    (pool : ∀q∈skywalkPoolWires base,
      field.basis q=(run (skywalkArithmeticClear base) mFirst recorded).basis q) :
    (run (skywalkArithmeticClear base) mLast field).phase=recorded.phase ∧
      ∀q∈skywalkPoolWires base,(run (skywalkArithmeticClear base) mLast field).basis q=recorded.basis q := by
  have agrees := pool_run_agrees (skywalkArithmeticClear base) (skywalkPoolWires base).toFinset
    clear_pool_support mLast field (run (skywalkArithmeticClear base) mFirst recorded)
    phase (fun q hq => pool q (List.mem_toFinset.mp hq))
  have twice : run (skywalkArithmeticClear base) mLast
      (run (skywalkArithmeticClear base) mFirst recorded)=recorded := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) recorded mFirst mLast
  rw [twice] at agrees
  exact ⟨agrees.1,fun q hq => agrees.2 q (List.mem_toFinset.mpr hq)⟩

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/EntryForwardSelectedPoolRestore.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run selectedFieldSegment skywalkArithmeticClear
  compressedCompactForward compressedCompactReverse

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedCallerFrame.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode

theorem caller_encoder_pool_support (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) :
    wires (allGroupEncode base 170) ⊆ (skywalkPoolWires base).toFinset := by
  have history := compressedPrefix_history_support base (skywalkShared_integer_nodup base hn)
    hlo 512 (by decide)
  rw [encode_prefix_512] at history
  intro q hq
  have member := List.mem_toFinset.mp (history hq)
  simp only [List.mem_append,wireBlock] at member
  rcases member with member|member
  all_goals
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1] at hi ⊢
    exact ⟨i,by omega,rfl⟩

/-- The physical encoded frame retains the full target port and every
nonpool outsider. Codec gates remain confined to the integer pool. -/
theorem encodedCanonical_caller_frame (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (ha : regValue (skywalkSharedField base).a origin = 0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame origin X 0 s) :
    regValue (skywalkSharedField base).z s.basis = X.val ∧
    ∀ q,q ∉ (skywalkSharedField base).z → q ∉ skywalkPoolWires base → s.basis q = origin q := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have narrow : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using rawFrame
  have keeps := arith_field_frame (skywalkSharedField base) origin raw.basis X.val ha narrow
  have support := caller_encoder_pool_support hn hlo
  have encoderAway (q : Wire) (hq : q ∉ skywalkPoolWires base) :
      (run (allGroupEncode base 170) [] raw).basis q = raw.basis q :=
    run_preserves_outside _ [] raw q (fun h => hq (List.mem_toFinset.mp (support h)))
  constructor
  · apply Eq.trans (regValue_congr _ _ _ ?_) narrow.1
    intro q hq
    rw [encoded]
    exact encoderAway q (fun hp => arith_pool_away_z base hn q hp hq)
  · intro q hz hp
    rw [encoded]
    exact (encoderAway q hp).trans (keeps q hz)

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedRawPreparation.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] skywalkSeed literalSkywalkSeed narrowSkywalkRoutedLoop
attribute [local irreducible] compactSkywalkForward run measurementCount
attribute [local irreducible] SkywalkTrace.next Nat.iterate

/-- Facts at the actual cleared raw caller boundary, before any history codec.
Every field and tape fact is derived from the original public input contract. -/
structure PreparationFacts (x : Nat) (Y : Fp) (entry origin : State) : Prop where
  sourceZero : regValue (skywalkSharedField base).a origin.basis = 0
  workZero : regValue (skywalkSharedField base).work origin.basis = 0
  unusedZero : regValue (skywalkSharedUnused base) origin.basis = 0
  targetValue : regValue (skywalkSharedField base).z origin.basis = Y.val
  env : Env base origin.basis
  targetHigh : origin.basis (base 2312) = false
  sourceHigh : origin.basis (base 1026) = false
  trace : skywalkTapeControls origin.basis (skywalkSharedTape base) =
    SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))
  legal : RawGroupLegal base 170 origin.basis
  controls : ∀ q ∈ [base 2400,base 2409,base 2410],origin.basis q = entry.basis q
  phase : origin.phase = entry.phase

/-- Clear uses only511,512,770. Every six-site group ends before510 or1538,
so its actual raw legality survives the caller's physical terminal clear. -/
private theorem clear_raw_legal (before after : State) (m : List Bool)
    (clear : run (skywalkArithmeticClear base) m before = after)
    (legal : RawGroupLegal base 170 before.basis) :
    RawGroupLegal base 170 after.basis := by
  have keep (j : Nat) (hj : j < 170) (u : Fin 6) :
      after.basis (compressedHistoryMap base (3*j) u) =
        before.basis (compressedHistoryMap base (3*j) u) := by
    have range : compressedHistoryId (3*j) u < 510 ∨
        (1028 ≤ compressedHistoryId (3*j) u ∧ compressedHistoryId (3*j) u < 1538) := by
      have hu := u.isLt
      unfold compressedHistoryId
      split <;> omega
    have away : base (compressedHistoryId (3*j) u) ∉ wires (skywalkArithmeticClear base) := by
      intro used
      rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at used
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at used
      rcases used with eq|eq|eq
      all_goals
        have same := base_injective eq
        omega
    have frame := run_preserves_outside (skywalkArithmeticClear base) m before
      (base (compressedHistoryId (3*j) u)) away
    rw [clear] at frame
    exact frame
  intro j hj
  rw [keep j hj 0,keep j hj 1,keep j hj 2,keep j hj 3,keep j hj 4,keep j hj 5]
  exact legal j hj

/-- The real literal seed, full raw compact loop, and actual terminal clear
prepare the unchanged field caller. No encoded-state Env is assumed. -/
theorem rawPreparation_facts
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m1 m2 m3 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (s1 s2 origin : State)
    (hs1 : run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) m1 s = s1)
    (hs2 : run (compactSkywalkForward base 0 512) m2 s1 = s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2 = origin) :
    PreparationFacts x Y s origin := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hp : p < 2^256 := by norm_num [p]
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2 = 1 := by norm_num [p]
  have pool := skywalkShared_integer_nodup base hn
  have oldhs1 := (directSkywalkLiteralSeed_seed_eq base hn x Y.val hx s m1 hin).symm.trans hs1
  have h1 := skywalkSeed_spec (skywalkSharedSeed base) 258 p x
    (skywalkShared_seed_widths base) (skywalkShared_seed_nodup base hn)
    (by omega) hp (hx.trans hp) s m1 (arith_seed_input base hn x Y.val s.basis hin)
  rw [oldhs1] at h1
  have stage0 := arith_seed_stage0 base hn x Y.val hx s m1 hin
  rw [oldhs1] at stage0
  have oldhs2 := (compactSkywalkCaller_forward_eq base hn x p hp0 hx0 hpo hp hx
    (arith_coprime x hx0 hx) s1 m2 m2 stage0).symm.trans hs2
  have h2 := narrowSkywalkRouted512_spec base pool x p hp0 hx0 hpo hp hx
    (arith_coprime x hx0 hx) s1 m2 stage0
  rw [oldhs2] at h2
  have raw := compactSkywalkForward_512 base pool x p hp0 hx0 hpo hp hx
    (arith_coprime x hx0 hx) s1 m2 stage0
  rw [hs2] at raw
  have legalBefore := compact_terminal_raw_legal base pool x p hp0 hpo s2.basis raw.2
  have legal := clear_raw_legal s2 origin m3 hs3 legalBefore
  have h3 := skywalkTerminalClear_correct _ _ _ (arith_clear_gates base hn) s2 m3
  change (run (skywalkArithmeticClear base) m3 s2).phase = s2.phase ∧ _ at h3
  rw [hs3] at h3
  have clean := arith_clean_preparation base hn x Y.val hx0 hx s m1 m2 m3 hin
  rw [oldhs1,oldhs2,hs3] at clean
  have work := skywalkShared_clean_to_field base origin.basis clean
  have value : regValue (skywalkSharedField base).z origin.basis = Y.val := by
    have frame := arith_preparation_frame base hn s m1 m2 m3
    rw [oldhs1,oldhs2,hs3] at frame
    exact (regValue_congr _ _ _ frame).trans (arith_z_input base hn x Y.val s.basis hin)
  have tape : skywalkTapeControls origin.basis (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) := by
    have frame := arith_tape_clear base hn s2 m3
    rw [hs3] at frame
    exact frame.trans (arith_tape base x s2.basis h2.2)
  have controls (q : Wire) (hq : q ∈ [base 2400,base 2409,base 2410]) :
      origin.basis q = s.basis q := by
    have outside := ho q hq
    have poolAway : q ∉ skywalkPoolWires base :=
      fun bad => outside (arith_block_subset_shared base 0 1798 (by omega) bad)
    have seedAway : q ∉ (skywalkSharedSeed base).usedWires :=
      fun bad => outside (arith_seed_subset_shared base bad)
    have k1 := (skywalkSeed_frame (skywalkSharedSeed base) 258 p
      (skywalkShared_seed_widths base) s m1 q seedAway).1
    have k2 := arith_record_outside base hn s1 m2 q poolAway
    have k3 := arith_clear_outside base hn s2 m3 q poolAway
    rw [oldhs1] at k1
    rw [oldhs2] at k2
    rw [hs3] at k3
    exact k3.trans (k2.trans k1)
  have environment : Env base origin.basis := env_of_canonical_source base hn
    origin.basis (0 : Fp) (by simpa using work.1) work.2.1 work.2.2
  have high := skywalkShared_numerator_high_zero base origin.basis Y.val value
    ((ZMod.val_lt Y).trans hp)
  exact ⟨work.1,work.2.1,work.2.2,value,environment,high,environment.2.2,
    tape,legal,controls,h3.1.trans (h2.1.trans h1.1)⟩

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedCallerPreparation.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run compactSkywalkForward compressedCompactForward
  literalSkywalkSeed skywalkSeed skywalkArithmeticClear allGroupEncode

/-- The actual compressed caller prefix supplies the verified field
contract by an exact raw witness, not an assumed decoded-history state. -/
theorem compressedPreparation_facts (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (m1 m2 m3 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (s1 s2 s3 : State)
    (hs1 : run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) m1 s=s1)
    (hs2 : run (compressedCompactForward base 0 512) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2=s3) :
    ∃ origin : State,PreparationFacts x Y s origin ∧
      origin.phase=s3.phase ∧ s3=run (allGroupEncode base 170) [] origin ∧
      EncodedCanonicalFrame origin.basis Y 0 s3 := by
  have pool := skywalkShared_integer_nodup base hn
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have oldSeed := (directSkywalkLiteralSeed_seed_eq base hn x Y.val hx s m1 hin).symm.trans hs1
  have stage0 := arith_seed_stage0 base hn x Y.val hx s m1 hin
  rw [oldSeed] at stage0
  let recorded := run (compactSkywalkForward base 0 512) [] s1
  let origin := run (skywalkArithmeticClear base) m3 recorded
  have facts := rawPreparation_facts hn ho x Y hx0 hx s m1 [] m3 hin s1 recorded origin hs1 rfl rfl
  have forward := compressedCompactForward_caller_eq base hn hlo x p hp0 hx0 hpo hp hx
    (arith_coprime x hx0 hx) s1 m2 [] stage0
  rw [hs2] at forward
  have encoded : s3=run (allGroupEncode base 170) [] origin := by
    rw [←hs3,forward]
    exact (full_encoder_clear_commute base pool hlo recorded [] m3).symm
  have encoderPhase := allGroupEncode_phase base pool hlo 170 (by decide) origin [] facts.legal
  have phase : origin.phase=s3.phase := by
    rw [encoded]
    exact encoderPhase.symm
  refine ⟨origin,facts,phase,encoded,origin,phase,?_,encoded⟩
  exact ⟨facts.targetValue,by simpa only [ZMod.val_zero] using facts.sourceZero,fun _ _ _ => rfl⟩

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectSeedInput.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run literalSkywalkSeed

private theorem positive_read (r : List Wire) (s : BasisState) (x : Nat)
    (hv : regValue r s=x) (fit : x<2^(r.length-1)) : signedRegValue r s=(x : Int) := by
  unfold signedRegValue signedDecode
  rw [hv,if_pos fit]

/-- The old emitted seed meets the unchanged first native tick contract.
The extension zero comes from the existing caller workspace invariant. -/
theorem seed_first_input (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false) :
    SkywalkIntegerInput (compactSkywalkTickLayout w 0)
      ((x : Int)+(p : Int)) (x : Int) false
      (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s).basis := by
  have hp : p<2^256 := by norm_num [p]
  have post := literalSkywalkSeed_spec (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by omega) hp (hx.trans hp) s m hin
  generalize ht : run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s=t at post ⊢
  have p2 : 2^257=2*2^256 := by rw [show 257=256+1 from rfl,pow_succ]; omega
  have sumfit : p+x<2^257 := by rw [p2]; omega
  have xfit : x<2^257 := by rw [p2]; omega
  have ar : (compactSkywalkTickLayout w 0).a=wireBlock w 0 258 := by
    simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_a w 0 (by omega)
  have br : (compactSkywalkTickLayout w 0).b=wireBlock w 770 258 := by
    simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_b w 0 (by omega)
  have av : signedRegValue (wireBlock w 0 258) t.basis=((x : Int)+(p : Int)) := by
    have h := positive_read (wireBlock w 0 258) t.basis (p+x) post.2.a
      (by simpa only [wireBlock_length,Nat.reduceSub] using sumfit)
    simpa only [Nat.cast_add,add_comm] using h
  have bv := positive_read (wireBlock w 770 258) t.basis x post.2.b
    (by simpa only [wireBlock_length,Nat.reduceSub] using xfit)
  have keep := literalSkywalkSeed_preserves_outsideA (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by omega) hp (hx.trans hp) s m hin (w 258)
    (block_not_mem w hn 258 0 258 (by omega) (by omega) (by omega))
  rw [ht] at keep
  unfold SkywalkIntegerInput
  rw [ar,br]
  refine ⟨av,bv,?_,?_,?_,?_⟩
  · exact post.2.cin
  · exact keep.trans ext
  · exact post.2.one
  · exact post.2.carry

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectCallerInput.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect

private theorem block_away_shared (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i a n : Nat) (hi : i<2314) (ha : a+n ≤ 2314)
    (sep : i<a ∨ a+n ≤ i) : w i ∉ wireBlock w a n := by
  intro h
  obtain ⟨j,hj,he⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  have eq := skywalkShared_index_inj w hn j i (by omega) hi he
  omega

private theorem clean_bit (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y i : Nat) (bits : BasisState) (hin : SkywalkArithmeticInput w x y bits)
    (hi : i<2314) (hx : i<770 ∨ 1026 ≤ i) (hy : i<2056 ∨ 2312 ≤ i) : bits (w i)=false := by
  apply hin.2.2 (w i)
  · exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  · exact block_away_shared w hn i 770 256 hi (by omega) hx
  · exact block_away_shared w hn i 2056 256 hi (by omega) hy

private theorem clean_word (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y a n : Nat) (bits : BasisState) (hin : SkywalkArithmeticInput w x y bits)
    (ha : a+n ≤ 2314) (hx : a+n ≤ 770 ∨ 1026 ≤ a) (hy : a+n ≤ 2056 ∨ 2312 ≤ a) :
    regValue (wireBlock w a n) bits=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact clean_bit w hn x y i bits hin (by omega) (by omega) (by omega)

/-- Readiness is derived from the full caller's existing workspace contract.
No new restriction is imposed on the divisor, numerator, or control. -/
theorem caller_ready (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (bits : BasisState) (hin : SkywalkArithmeticInput w x y bits) :
    LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x bits ∧ bits (w 258)=false := by
  have bz := clean_word w hn x y 1026 2 bits hin (by omega) (by omega) (by omega)
  have bv : regValue (wireBlock w 770 258) bits=x := by
    rw [←wireBlock_append w 770 256 2,regValue_append,bz,Nat.mul_zero,Nat.add_zero]
    exact hin.1
  refine ⟨?_,clean_bit w hn x y 258 bits hin (by omega) (by omega) (by omega)⟩
  refine ⟨clean_word w hn x y 0 258 bits hin (by omega) (by omega) (by omega),bv,
    clean_word w hn x y 1540 257 bits hin (by omega) (by omega) (by omega),?_,?_,?_⟩
  · exact clean_bit w hn x y 1797 bits hin (by omega) (by omega) (by omega)
  · exact clean_bit w hn x y 1028 bits hin (by omega) (by omega) (by omega)
  · exact clean_bit w hn x y 1797 bits hin (by omega) (by omega) (by omega)

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectWordProof.lean
noncomputable section

set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] mappedAdd run hAdd kTail kAdd

private theorem block_one (w : Nat → Wire) (a : Nat) :
    wireBlock w a 1=[w a] := by simp [wireBlock,List.range']

private theorem cons_value_NativeFirstDirectWordProof (h : Wire) (r : List Wire) (s : BasisState) :
    regValue (h::r) s=(s h).toNat+2*regValue r s := by
  cases hb : s h <;> simp [regValue,hb]

private theorem low_one_mod_NativeFirstDirectWordProof (C T : Nat) (b : Bool) (hc : C%2=1) :
    (!b).toNat+2*((C/2+T+b.toNat)%2^257)=(b.toNat+2*T+C)%2^258 := by
  have split := Nat.mod_add_div C 2
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true,Bool.not_false,
    Bool.not_true,Nat.add_zero] <;> omega

/-- Abstract basis-state proof: no embedded gate program is normalized. -/
private theorem toggle_head_value_NativeFirstDirectWordProof (h : Wire) (r : List Wire) (s : BasisState)
    (ha : h∉r) :
    regValue (h::r) (writeBit s h (!(s h)))=(!s h).toNat+2*regValue r s := by
  have head : (writeBit s h (!(s h))) h=!(s h) := by simp [writeBit]
  have tail : regValue r (writeBit s h (!(s h)))=regValue r s := by
    apply regValue_congr
    intro q hq
    have ne : q≠h := by intro e; subst q; exact ha hq
    simp [writeBit,ne]
  rw [cons_value_NativeFirstDirectWordProof,head,tail]

/-- A high-slice addition, including preservation of the untouched low slice. -/
private theorem high_value (lo hi : List Wire) (s t : BasisState) (C : Nat)
    (low : regValue lo t=regValue lo s)
    (high : regValue hi t=(C+regValue hi s)%2^hi.length)
    (fit : regValue (lo++hi) s+2^lo.length*C<2^(lo.length+hi.length)) :
    regValue (lo++hi) t=regValue (lo++hi) s+2^lo.length*C := by
  have pos : 0<2^lo.length := Nat.two_pow_pos _
  have bound : C+regValue hi s<2^hi.length := by
    rw [regValue_append,Nat.pow_add] at fit
    nlinarith
  rw [regValue_append,low,high,Nat.mod_eq_of_lt bound,regValue_append]
  ring

/-- Actual H word arithmetic, phase, and full frame for every independent tape.
The three untouched low H bits cannot carry when the fixed increment is /8. -/
theorem hAdd_word (w : Nat → Wire) (s : State) (m : List Bool)
    (hn : (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup)
    (hs : ∀q∈mappedWires (hBits w false),
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252))
    (hc : ∀q∈wireBlock w 1540 252,s.basis q=false)
    (hcin : s.basis (w 1797)=false)
    (hl : ∀q∈wireBlock w 1 3,q∉wireBlock w 4 253)
    (fit : regValue (wireBlock w 1 256) s.basis+
      (if s.basis (w 1028) then hConstant else 0)<2^256) :
    (run (hAdd w false) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 4 253 → (run (hAdd w false) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 1 256) (run (hAdd w false) m s).basis=
      regValue (wireBlock w 1 256) s.basis+
        (if s.basis (w 1028) then hConstant else 0) := by
  have a := hAdd_spec w false s m hn hs hc
  refine ⟨a.1,a.2.1,?_⟩
  have low := regValue_congr (wireBlock w 1 3) _ s.basis
    (fun q hq => a.2.1 q (hl q hq))
  have high : regValue (wireBlock w 4 253) (run (hAdd w false) m s).basis=
      ((if s.basis (w 1028) then hConstant/8 else 0)+
        regValue (wireBlock w 4 253) s.basis)%2^253 := by
    simpa [hcin] using a.2.2
  have mult : 8*(if s.basis (w 1028) then hConstant/8 else 0)=
      (if s.basis (w 1028) then hConstant else 0) := by
    cases s.basis (w 1028) <;> simp
    have z := hConstant_low_zero
    omega
  have split := wireBlock_append w 1 3 253
  have f : regValue (wireBlock w 1 3++wireBlock w 4 253) s.basis+
      2^(wireBlock w 1 3).length*(if s.basis (w 1028) then hConstant/8 else 0)<
      2^((wireBlock w 1 3).length+(wireBlock w 4 253).length) := by
    simpa [wireBlock_length,split,mult] using fit
  have out := high_value (wireBlock w 1 3) (wireBlock w 4 253) s.basis
    (run (hAdd w false) m s).basis _ low
    (by simpa [wireBlock_length] using high) f
  simpa [wireBlock_length,split,mult] using out

/-- Full K word: the retained head is the tail carry-in, then the final X
implements the low-one constant. All other wires and incoming phase return. -/
theorem kAdd_word (w : Nat → Wire) (s : State) (m : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀q∈mappedWires (kBits w false),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    (run (kAdd w false) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 770 258 → (run (kAdd w false) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 770 258) (run (kAdd w false) m s).basis=
      (regValue (wireBlock w 770 258) s.basis+
        kConstant false (s.basis (w 1028)))%2^258 := by
  let u := run (kTail w false) (m.take (measurementCount (kTail w false))) s
  have a := kTail_spec w false s (m.take (measurementCount (kTail w false))) hn hs hc
  have hb : w 770∉wireBlock w 771 257 := by
    intro h
    exact (List.nodup_cons.mp hn).1 (List.mem_append_left _ h)
  have head : u.basis (w 770)=s.basis (w 770) := a.2.1 _ hb
  have split : w 770::wireBlock w 771 257=wireBlock w 770 258 := by
    simpa [block_one] using wireBlock_append w 770 1 257
  rw [kAdd_run]
  refine ⟨a.1,?_,?_⟩
  · intro q hq
    have hq0 : q≠w 770 := by intro e; subst q; exact hq (by rw [←split]; simp)
    have hqt : q∉wireBlock w 771 257 := by intro h; exact hq (by rw [←split]; simp [h])
    simpa [u,writeBit,hq0] using a.2.1 q hqt
  · rw [←split,toggle_head_value_NativeFirstDirectWordProof (w 770) (wireBlock w 771 257) u.basis hb,head]
    have value := a.2.2
    change regValue (wireBlock w 771 257) u.basis=_ at value
    rw [value,cons_value_NativeFirstDirectWordProof]
    have parity := kConstant_low_one false (s.basis (w 1028))
    exact low_one_mod_NativeFirstDirectWordProof _ _ _ parity

/-- The actual three Clifford gates set both coherent transcript bits. -/
theorem front_spec (w : Nat → Wire) (s : State) (m : List Bool)
    (hne : w 0≠w 1028) (ha : s.basis (w 0)=false)
    (hs : s.basis (w 1028)=false) :
    run [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] m s=
      ⟨s.phase,writeBit (writeBit s.basis (w 1028) (s.basis (w 770)))
        (w 0) (!(s.basis (w 770)))⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=w 0
  · subst q
    simp [run,writeBit,ha,hs,hne,Ne.symm hne]
  by_cases ht : q=w 1028
  · subst q
    simp [run,writeBit,ha,hs,hne,Ne.symm hne]
  simp [run,writeBit,ha,hs,hne,Ne.symm hne,hq,ht]

/-- The low-bit clear is coherent and preserves every other bit and phase. -/
theorem clear_spec (w : Nat → Wire) (s : State) (m : List Bool)
    (h : s.basis (w 770)=s.basis (w 1028)) :
    run [.CX (w 1028) (w 770)] m s=
      ⟨s.phase,writeBit s.basis (w 770) false⟩ := by
  simp only [run,h,Bool.xor_self]

end ECDSAAdd.Arithmetic.NativeFirstDirect
end
