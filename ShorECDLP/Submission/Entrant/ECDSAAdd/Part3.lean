-- Vendored from ECDSAAdd (ecdsa.fail Lean challenge), Apache-2.0, Copyright 2026 Runzhou Tao, Anirudh and ECDSAAdd contributors; 156 source modules at c3f340a (listed in MODULES.txt), concatenated. Changes: module paths, expanded notation, private-name renames.
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part1
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part2
import Mathlib.Tactic

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedResult.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def measuredCompleteResult (enabled : Bool) (A B O : Nat) : Nat :=
  SquareReduction.p-1-measuredCMiddleResult ((if enabled then A+B else 0)^2)
    (measuredBResult ((if enabled then B else 0)^2) (measuredAResult ((if enabled then A else 0)^2) O))

theorem measuredCompleteResult_lt (enabled : Bool) (A B O : Nat) :
    measuredCompleteResult enabled A B O<SquareReduction.p := by
  have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  dsimp [measuredCompleteResult]
  omega

theorem measuredCompleteResult_exact (enabled : Bool) (A B O : Nat) :
    measuredCompleteResult enabled A B O=
      subModValue (if enabled then (A+2^128*B)^2 else 0) O := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := measuredAResult PA O
  let OB := measuredBResult PB OA
  let OC := measuredCMiddleResult PC OB
  have ea := measuredAResult_cast PA O
  have eb := measuredBResult_cast PB OA
  have ec := measuredCMiddleResult_cast PC OB
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have ocBound : OC<SquareReduction.p := (measured_results_lt PC OB).2.2
  have cast : (measuredCompleteResult enabled A B O : ZMod SquareReduction.p)=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    change ((SquareReduction.p-1-OC : Nat) : ZMod SquareReduction.p)=_
    rw [measuredReflection_zmod OC ocBound,subModValue_cast]
    linear_combination ea+eb+ec+identity
  have targetBound : subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt (measuredCompleteResult_lt enabled A B O),ZMod.val_natCast_of_lt targetBound] using value

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

/-- The complete emitted controlled square subtraction, for every 256-bit
source, canonical output and every measurement record. Every non-output
wire, including control and all shared scratch, and the phase are restored. -/
theorem measuredProgram_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (L.measuredProgram control) records s).phase=s.phase ∧
    regValue L.core.out (run (L.measuredProgram control) records s).basis=
      (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (L.measuredProgram control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := measuredAResult PA O
  let OB := measuredBResult PB OA
  let OC := measuredCMiddleResult PC OB
  let restA := records.drop (measurementCount (L.measuredBranchA control))
  let restB := restA.drop (measurementCount (L.measuredBranchB control))
  let restC := restB.drop (measurementCount (L.measuredBranchC control))
  let u := run (L.measuredBranchA control) (records.take (measurementCount (L.measuredBranchA control))) s
  let v := run (L.measuredBranchB control) (restA.take (measurementCount (L.measuredBranchB control))) u
  let w := run (L.measuredBranchC control) (restB.take (measurementCount (L.measuredBranchC control))) v
  let out := run L.reflectOutput restC w
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ea := L.measuredBranchA_correct hw control hn A O hO s
    (records.take (measurementCount (L.measuredBranchA control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := L.measuredBranchB_correct hw control hn B OA (measured_results_lt PA O).1 u
    (restA.take (measurementCount (L.measuredBranchB control))) highU ea.2.1 productU cleanU
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ea.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A := regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have sumV : regValue L.core.sum v.basis=B :=
    (regValue_congr _ _ _ (fun q hq => sameV q (sumAway q hq))).trans sumB
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ec := L.measuredBranchC_correct hw control hn A B OB (measured_results_lt PB OA).2.1 v
    (restB.take (measurementCount (L.measuredBranchC control))) lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have cleanW : L.PairClean w.basis :=
    L.squareFrame_clean nd s.basis w.basis OC ⟨ec.2.1,sameW⟩ hc
  have er := L.reflectOutput_correct hw nd OC (measured_results_lt PC OB).2.2 w restC ec.2.1 cleanW
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out out.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := measuredCompleteResult_exact enabled A B O
    rw [split] at exactResult
    exact er.2.1.trans exactResult
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨er.1.trans (ec.1.trans (eb.1.trans ea.1)),fullValue,?_⟩
    intro q hq
    exact (er.2.2 q hq).trans (sameW q hq)
  simpa [measuredProgram,u,v,w,out,restA,restB,restC,enabled,run_append,Nat.add_assoc] using final

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroGateSupport.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic

theorem xorConstant_unitary (r : List Wire) (k : Nat) :
    ProperProgram (xorConstant r k) := by
  induction r generalizing k with
  | nil => simp [xorConstant,ProperProgram]
  | cons q r ih =>
    by_cases h : k%2=1
    · simp only [xorConstant,h,if_true,properProgram_append]
      exact ⟨by simp [ProperProgram,ProperGate],ih (k/2)⟩
    · simpa [xorConstant,h] using ih (k/2)

theorem maskedConstant_unitary (c : Wire) (r : List Wire) (k : Nat)
    (hc : c∉r) : ProperProgram (maskedConstant c r k) := by
  induction r generalizing k with
  | nil => simp [maskedConstant,ProperProgram]
  | cons q r ih =>
    have cq : c≠q := fun e => hc (by simp [e])
    have cr : c∉r := fun h => hc (by simp [h])
    by_cases h : k%2=1
    · simp only [maskedConstant,h,if_true,properProgram_append]
      exact ⟨by simpa [ProperProgram,ProperGate] using cq,ih (k/2) cr⟩
    · simpa [maskedConstant,h] using ih (k/2) cr

private theorem mod_nd (L : CuccaroModLayout) (hn : L.wires.Nodup)
    (r : List Wire) (hr : ∀q,r.count q≤L.wires.count q) : r.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  exact (hr q).trans (List.nodup_iff_count.mp hn q)

theorem cuccaroMod_unitary (L : CuccaroModLayout) (p : Nat) (hn : L.wires.Nodup) :
    ProperProgram (cuccaroModAdd L p) ∧ ProperProgram (cuccaroModSub L p) := by
  have az : (L.cin::L.a++L.z).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have wz : (L.cin::L.scratch++L.z).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have wl : (L.cin::L.work++L.low).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.z,CuccaroModLayout.scratch,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have aw : (L.cin::L.a++L.scratch).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have lw : (L.low++L.work).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.z,CuccaroModLayout.scratch,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have mask : (L.high::L.work).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.z,CuccaroModLayout.scratch,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have flags : [L.workHigh,L.high,L.flag].Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.z,CuccaroModLayout.scratch,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have hfh : L.flag≠L.high := by
    have h := List.nodup_cons.mp (List.nodup_cons.mp flags).2
    simpa [ne_comm] using h.1
  have hwh : L.workHigh≠L.high := by
    have h := List.nodup_cons.mp flags
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact h.1.1
  constructor
  · simp only [cuccaroModAdd,properProgram_append]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cuccaroAdd_proper _ _ _ az,
      xorConstant_unitary _ _⟩,cuccaroSub_proper _ _ _ wz⟩,
      xorConstant_unitary _ _⟩,maskedConstant_unitary _ _ _
        (List.nodup_cons.mp mask).1⟩,cuccaroAdd_proper _ _ _ wl⟩,
      maskedConstant_unitary _ _ _ (List.nodup_cons.mp mask).1⟩,
      copyRegister_none_proper _ _ lw⟩,cuccaroSub_proper _ _ _ aw⟩,
      by simpa [ProperProgram,ProperGate] using hwh⟩,
      cuccaroAdd_proper _ _ _ aw⟩,copyRegister_none_proper _ _ lw⟩
  · simp only [cuccaroModSub,properProgram_append]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cuccaroSub_proper _ _ _ az,
      maskedConstant_unitary _ _ _ (List.nodup_cons.mp mask).1⟩,
      cuccaroAdd_proper _ _ _ wl⟩,
      maskedConstant_unitary _ _ _ (List.nodup_cons.mp mask).1⟩,
      by simpa [ProperProgram,ProperGate] using And.intro hfh.symm hfh⟩,
      cuccaroAdd_proper _ _ _ az⟩,xorConstant_unitary _ _⟩,
      cuccaroSub_proper _ _ _ wz⟩,
      by simpa [ProperProgram,ProperGate] using hfh.symm⟩,
      cuccaroAdd_proper _ _ _ wz⟩,xorConstant_unitary _ _⟩,
      cuccaroSub_proper _ _ _ az⟩

theorem cuccaroNormalizedMod_unitary (L : CuccaroNormalizedModLayout)
    (c p : Nat) (hn : L.wires.Nodup) :
    ProperProgram (cuccaroNormalizedModAdd L c p) ∧
    ProperProgram (cuccaroNormalizedModSub L c p) := by
  have nd : L.normalize.wires.Nodup ∧ L.modular.wires.Nodup := by
    constructor <;> apply List.nodup_iff_count.mpr <;> intro q
    all_goals
      have h := List.nodup_iff_count.mp hn q
      simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
        CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
        CuccaroNormalizedModLayout.modular,CuccaroModLayout.wires,CuccaroModLayout.z,
        CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.count_cons,
        List.count_append,List.count_nil] at h ⊢
      omega
  have norm := cuccaroNormalize_proper L.normalize c nd.1
  have clear := properProgram_reverse _ norm
  have mods := cuccaroMod_unitary L.modular p nd.2
  simp only [cuccaroNormalizedModAdd,cuccaroNormalizedModSub,
    cuccaroNormalizeClear,properProgram_append]
  exact ⟨⟨⟨norm,mods.1⟩,clear⟩,⟨⟨norm,mods.2⟩,clear⟩⟩

theorem cuccaroMod_wires_subset (L : CuccaroModLayout) (n p : Nat)
    (hw : L.Widths n) :
    wires (cuccaroModAdd L p)⊆L.wires.toFinset ∧
    wires (cuccaroModSub L p)⊆L.wires.toFinset := by
  have add (a b : List Wire) (h : ∀q,q∈L.cin::a++b → q∈L.wires) :
      wires (cuccaroAdd a b L.cin)⊆L.wires.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp
      (cuccaroAdd_wires_subset a b L.cin hq)))
  have sub (a b : List Wire) (h : ∀q,q∈L.cin::a++b → q∈L.wires) :
      wires (cuccaroSub a b L.cin)⊆L.wires.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp
      (cuccaroSub_wires_subset a b L.cin hq)))
  have xor (r : List Wire) (h : ∀q,q∈r → q∈L.wires) :
      wires (xorConstant r p)⊆L.wires.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp
      (xorConstant_wires_subset r p hq)))
  have mask : wires (maskedConstant L.high L.work p)⊆L.wires.toFinset := by
    intro q hq
    have h := maskedConstant_wires_subset L.high L.work p hq
    simpa only [List.mem_toFinset,CuccaroModLayout.wires,CuccaroModLayout.z,
      CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
      List.mem_append,List.not_mem_nil,or_false] using
      (show q∈L.wires from by
        simp only [List.mem_toFinset,List.mem_cons] at h
        simp only [CuccaroModLayout.wires,CuccaroModLayout.z,
          CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
          List.mem_append,List.not_mem_nil,or_false]
        tauto)
  have copy : wires (copyRegister none L.low L.work)⊆L.wires.toFinset := by
    rw [copyRegister_wires _ _ _ (hw.low.trans hw.work.symm)]
    split
    · exact Finset.empty_subset _
    · intro q hq
      simp only [List.mem_toFinset,Option.toList_none,List.nil_append,
        List.mem_append] at hq
      simp only [List.mem_toFinset,CuccaroModLayout.wires,CuccaroModLayout.z,
        CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
        List.mem_append,List.not_mem_nil,or_false]
      tauto
  constructor
  all_goals
    simp only [cuccaroModAdd,cuccaroModSub,wires_append,Finset.union_subset_iff]
    repeat' constructor
    all_goals first | exact mask | exact copy | apply add | apply sub | apply xor | skip
    all_goals
      intro q hq
      simp only [List.mem_toFinset,CuccaroModLayout.wires,CuccaroModLayout.z,
        CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
        List.mem_append,List.not_mem_nil,or_false,wires,Instr.wires,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.notMem_empty,or_false] at hq ⊢
      tauto

theorem cuccaroNormalizedMod_wires_subset (L : CuccaroNormalizedModLayout)
    (n c p : Nat) (hw : L.Widths n) :
    wires (cuccaroNormalizedModAdd L c p)⊆L.wires.toFinset ∧
    wires (cuccaroNormalizedModSub L c p)⊆L.wires.toFinset := by
  have norm : wires (cuccaroNormalize L.normalize c)⊆L.wires.toFinset := by
    intro q hq
    have h := cuccaroNormalize_wires_subset L.normalize c hq
    simp only [List.mem_toFinset,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
    simp only [List.mem_toFinset,CuccaroNormalizedModLayout.wires,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    tauto
  have clear : wires (cuccaroNormalizeClear L.normalize c)⊆L.wires.toFinset := by
    simpa only [cuccaroNormalizeClear,wires_reverse] using norm
  have mods := cuccaroMod_wires_subset L.modular n p (L.modular_widths n hw)
  have embed : L.modular.wires.toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,CuccaroNormalizedModLayout.modular,
      CuccaroModLayout.wires,CuccaroModLayout.z,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false] at hq
    simp only [List.mem_toFinset,CuccaroNormalizedModLayout.wires,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    tauto
  simp only [cuccaroNormalizedModAdd,cuccaroNormalizedModSub,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨norm,mods.1.trans embed⟩,clear⟩,⟨⟨norm,mods.2.trans embed⟩,clear⟩⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Framework/UnitaryControl.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd

/-- Exact gate control with one reusable clean conjunction bit. -/
def controlInstr (c scratch : Wire) : Instr → Program
  | .X t => [.CX c t]
  | .CX a t => [.CCX c a t]
  | .CCX a b t => [.CCX c a scratch,.CCX scratch b t,.CCX c a scratch]
  | .measureX _ _ _ => []

def controlUnitary (c scratch : Wire) (p : Program) : Program :=
  p.flatMap (controlInstr c scratch)

theorem controlInstr_measurementCount (c scratch : Wire) (i : Instr) :
    measurementCount (controlInstr c scratch i)=0 := by
  cases i <;> rfl

theorem controlInstr_run (c scratch : Wire) (i : Instr) (hi : ProperGate i)
    (hc : c∉i.wires) (ht : scratch∉i.wires) (hct : c≠scratch)
    (s : State) (m : List Bool) (hz : s.basis scratch=false) :
    run (controlInstr c scratch i) m s=
      if s.basis c then run [i] m s else s := by
  cases s with
  | mk phase bits =>
    change bits scratch=false at hz
    cases i with
    | X t =>
      cases sc : bits c <;> simp only [controlInstr,run,sc,if_false,if_true]
      all_goals
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t <;> simp [writeBit,hq]
    | CX a t =>
      cases sc : bits c <;>
        simp only [controlInstr,run,sc,if_false,if_true,Bool.false_and,Bool.true_and]
      all_goals
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t <;> simp [writeBit,hq]
    | CCX a b t =>
      simp only [ProperGate] at hi
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton,not_or] at hc ht
      cases sc : bits c <;> simp only [controlInstr,run,sc,if_false,if_true]
      all_goals
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t
        · subst q
          simp [writeBit,ht.1,ht.2.1,ht.2.2,Ne.symm ht.1,Ne.symm ht.2.1,
            Ne.symm ht.2.2,hct,hi.1,hi.2,hc.2.2,hz,sc]
        · by_cases hqs : q=scratch
          · subst q
            simp [writeBit,ht.1,ht.2.1,ht.2.2,Ne.symm ht.1,Ne.symm ht.2.1,
              hct,hi.1,hc.2.2,hz,sc]
          · simp [writeBit,hq,hqs,ht.1,ht.2.1,Ne.symm ht.1,Ne.symm ht.2.1,
              hct,hi.1,hc.2.2,hz,sc]
    | measureX t z o => contradiction

theorem controlUnitary_measurementCount (c scratch : Wire) (p : Program) :
    measurementCount (controlUnitary c scratch p)=0 := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [controlUnitary,List.flatMap_cons,measurementCount_append]
    rw [controlInstr_measurementCount]
    simpa only [controlUnitary,Nat.zero_add] using ih

theorem controlUnitary_run (c scratch : Wire) (p : Program)
    (hp : ProperProgram p) (hc : c∉wires p) (ht : scratch∉wires p)
    (hct : c≠scratch) (s : State) (m : List Bool) (hz : s.basis scratch=false) :
    run (controlUnitary c scratch p) m s=
      if s.basis c then run p m s else s := by
  induction p generalizing s m with
  | nil => cases s.basis c <;> rfl
  | cons i p ih =>
    have hi := hp i (by simp)
    have hpt : ProperProgram p := by intro j hj; exact hp j (by simp [hj])
    simp only [wires,Finset.mem_union,not_or] at hc ht
    have hci : c∉i.wires := hc.1
    have hcp : c∉wires p := hc.2
    have hti : scratch∉i.wires := ht.1
    have htp : scratch∉wires p := ht.2
    let u := if s.basis c then run [i] m s else s
    have uControl : u.basis c=s.basis c := by
      cases sc : s.basis c
      · simp [u,sc]
      · simp only [u,sc,if_true]
        exact (run_preserves_outside [i] m s c (by simpa [wires] using hci)).trans sc
    have uScratch : u.basis scratch=false := by
      cases sc : s.basis c
      · simpa [u,sc] using hz
      · simp only [u,sc,if_true]
        exact (run_preserves_outside [i] m s scratch
          (by simpa [wires] using hti)).trans hz
    have first := controlInstr_run c scratch i hi hci hti hct s m hz
    change run (controlInstr c scratch i++controlUnitary c scratch p) m s=_
    rw [run_append,run_take,controlInstr_measurementCount,List.drop_zero,first]
    change run (controlUnitary c scratch p) m u=_
    rw [ih hpt hcp htp u m uScratch,uControl]
    cases sc : s.basis c
    · simp [sc,u]
    · simp only [sc,if_true,u]
      have im := properGate_measurementCount i hi
      have exec : run (i::p) m s=run p m (run [i] m s) := by
        change run ([i]++p) m s=_
        rw [run_append,run_take,im,List.drop_zero]
      exact exec.symm

def cnotCount : Program → Nat
  | [] => 0
  | .CX _ _::p => 1+cnotCount p
  | _::p => cnotCount p

@[simp] theorem cnotCount_append (p q : Program) :
    cnotCount (p++q)=cnotCount p+cnotCount q := by
  induction p with
  | nil => simp [cnotCount]
  | cons i p ih => cases i <;> simp [cnotCount,ih,Nat.add_assoc]

theorem cnotCount_reverse (p : Program) : cnotCount p.reverse=cnotCount p := by
  induction p with
  | nil => rfl
  | cons i p ih => cases i <;> simp [cnotCount,ih,Nat.add_comm]

theorem controlUnitary_toffoliCount (c scratch : Wire) (p : Program) :
    toffoliCount (controlUnitary c scratch p)=3*toffoliCount p+cnotCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [controlUnitary] at ih
    cases i <;> simp [controlUnitary,controlInstr,toffoliCount_append,
      toffoliCount,cnotCount,ih] <;> omega

theorem controlInstr_wires_subset (c scratch : Wire) (i : Instr) :
    wires (controlInstr c scratch i)⊆{c,scratch}∪i.wires := by
  cases i <;> intro q hq <;>
    simp only [controlInstr,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false] at hq ⊢ <;> tauto

theorem controlUnitary_wires_subset (c scratch : Wire) (p : Program) :
    wires (controlUnitary c scratch p)⊆{c,scratch}∪wires p := by
  induction p with
  | nil => simp [controlUnitary,wires]
  | cons i p ih =>
    intro q hq
    simp only [controlUnitary,List.flatMap_cons,wires_append,
      Finset.mem_union] at hq
    change q∈{c,scratch}∪(i.wires∪wires p)
    rcases hq with hq|hq
    · have h := controlInstr_wires_subset c scratch i hq
      simp only [Finset.mem_union] at h ⊢
      tauto
    · have h := ih hq
      simp only [Finset.mem_union] at h ⊢
      tauto

end ECDSAAdd
end

-- source: ECDSAAdd/Framework/ExactControl.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd

/-- An exact controlled replacement with one shared, restored scratch bit.
The contract is equality of the complete state, including phase. -/
structure ExactControl (c scratch : Wire) (original replacement : Program) : Prop where
  proper : ProperProgram original
  controlAway : c∉wires original
  scratchAway : scratch∉wires original
  measurement : measurementCount replacement=0
  support : wires replacement⊆{c,scratch}∪wires original
  execute : ∀ (s : State) (m : List Bool), s.basis scratch=false →
    run replacement m s=if s.basis c then run original m s else s

theorem ExactControl.direct (c scratch : Wire) (p : Program)
    (hp : ProperProgram p) (hc : c∉wires p) (hs : scratch∉wires p)
    (hcs : c≠scratch) : ExactControl c scratch p (controlUnitary c scratch p) :=
  ⟨hp,hc,hs,controlUnitary_measurementCount _ _ _,
    controlUnitary_wires_subset _ _ _,controlUnitary_run c scratch p hp hc hs hcs⟩

theorem ExactControl.nil (c scratch : Wire) : ExactControl c scratch [] [] := by
  refine ⟨by simp [ProperProgram],by simp [wires],by simp [wires],rfl,
    by simp [wires],?_⟩
  intro s m hz
  cases s.basis c <;> rfl

theorem ExactControl.append {c scratch : Wire} {p q p' q' : Program}
    (hp : ExactControl c scratch p p') (hq : ExactControl c scratch q q') :
    ExactControl c scratch (p++q) (p'++q') := by
  refine ⟨(properProgram_append p q).mpr ⟨hp.proper,hq.proper⟩,
    ?_,?_,?_,?_,?_⟩
  · simpa only [wires_append,Finset.mem_union,not_or] using
      And.intro hp.controlAway hq.controlAway
  · simpa only [wires_append,Finset.mem_union,not_or] using
      And.intro hp.scratchAway hq.scratchAway
  · simp only [measurementCount_append,hp.measurement,hq.measurement]
  · intro w hw
    simp only [wires_append,Finset.mem_union] at hw ⊢
    rcases hw with hw|hw
    · have h := hp.support hw
      simp only [Finset.mem_union] at h
      tauto
    · have h := hq.support hw
      simp only [Finset.mem_union] at h
      tauto
  · intro s m hz
    let u := if s.basis c then run p m s else s
    have uc : u.basis c=s.basis c := by
      cases hc : s.basis c
      · simp [u,hc]
      · simp only [u,hc,if_true]
        exact (run_preserves_outside p m s c hp.controlAway).trans hc
    have uz : u.basis scratch=false := by
      cases hc : s.basis c
      · simpa [u,hc] using hz
      · simp only [u,hc,if_true]
        exact (run_preserves_outside p m s scratch hp.scratchAway).trans hz
    rw [run_append,run_take,hp.measurement,List.drop_zero,hp.execute s m hz]
    change run q' m u=_
    rw [hq.execute u m uz,uc]
    have pm := properProgram_measurementCount p hp.proper
    cases hc : s.basis c
    · simp [hc,u]
    · simp only [hc,if_true,u]
      rw [run_append,run_take,pm,List.drop_zero]

/-- Leave reversible preparation and cleanup uncontrolled.  Only the middle
update needs control; the disabled branch is the exact preparation roundtrip. -/
theorem ExactControl.sandwich {c scratch : Wire} {p q q' : Program}
    (hp : ProperProgram p) (hc : c∉wires p) (hs : scratch∉wires p)
    (hq : ExactControl c scratch q q') :
    ExactControl c scratch (p++q++p.reverse) (p++q'++p.reverse) := by
  have pr := properProgram_reverse p hp
  have pm := properProgram_measurementCount p hp
  have prm : measurementCount p.reverse=0 := by rw [measurementCount_reverse,pm]
  refine ⟨(properProgram_append _ _).mpr
    ⟨(properProgram_append _ _).mpr ⟨hp,hq.proper⟩,pr⟩,?_,?_,?_,?_,?_⟩
  · simpa only [wires_append,wires_reverse,Finset.mem_union,not_or] using
      And.intro (And.intro hc hq.controlAway) hc
  · simpa only [wires_append,wires_reverse,Finset.mem_union,not_or] using
      And.intro (And.intro hs hq.scratchAway) hs
  · simp [measurementCount_append,pm,prm,hq.measurement]
  · intro w hw
    simp only [wires_append,wires_reverse,Finset.mem_union] at hw ⊢
    rcases hw with (hw|hw)|hw
    · tauto
    · have h := hq.support hw
      simp only [Finset.mem_union] at h
      tauto
    · tauto
  · intro s m hz
    let u := run p m s
    have uc : u.basis c=s.basis c := run_preserves_outside p m s c hc
    have uz : u.basis scratch=false := (run_preserves_outside p m s scratch hs).trans hz
    have qm := properProgram_measurementCount q hq.proper
    have pEmpty (st : State) : run p [] st=run p m st := by
      have h := run_take p m st
      simpa only [pm,List.take_zero] using h
    have qEmpty (st : State) : run q [] st=run q m st := by
      have h := run_take q m st
      simpa only [qm,List.take_zero] using h
    have q'Empty (st : State) : run q' [] st=run q' m st := by
      have h := run_take q' m st
      simpa only [hq.measurement,List.take_zero] using h
    simp only [List.append_assoc,run_append,pm,hq.measurement,qm,
      List.drop_zero,List.take_zero,pEmpty,qEmpty,q'Empty]
    change run p.reverse m (run q' m u)=_
    rw [hq.execute u m uz,uc]
    cases h : s.basis c
    · exact run_reverse_proper p hp s m m
    · rfl

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/ControlledNormalizedMod.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic

def controlledNormalizedModAdd (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (c p : Nat) : Program :=
  cuccaroNormalize L.normalize c++
    controlUnitary control scratch (cuccaroModAdd L.modular p)++
    cuccaroNormalizeClear L.normalize c

def controlledNormalizedModSub (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (c p : Nat) : Program :=
  cuccaroNormalize L.normalize c++
    controlUnitary control scratch (cuccaroModSub L.modular p)++
    cuccaroNormalizeClear L.normalize c

private theorem normalized_views_nodup (L : CuccaroNormalizedModLayout)
    (hn : L.wires.Nodup) : L.normalize.wires.Nodup ∧ L.modular.wires.Nodup := by
  constructor <;> apply List.nodup_iff_count.mpr <;> intro q
  all_goals
    have h := List.nodup_iff_count.mp hn q
    simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizedModLayout.modular,CuccaroModLayout.wires,CuccaroModLayout.z,
      CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.count_cons,
      List.count_append,List.count_nil] at h ⊢
    omega

private theorem normalized_views_away (L : CuccaroNormalizedModLayout)
    (q : Wire) (hq : q∉L.wires) : q∉L.normalize.wires ∧ q∉L.modular.wires := by
  constructor <;> intro h <;> apply hq
  all_goals
    simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizedModLayout.modular,CuccaroModLayout.wires,CuccaroModLayout.z,
      CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
      List.mem_append,List.not_mem_nil,or_false] at h ⊢
    tauto

theorem controlledNormalizedMod_exact (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (n c p : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (hc : control∉L.wires) (ht : scratch∉L.wires)
    (hct : control≠scratch) :
    ExactControl control scratch (cuccaroNormalizedModAdd L c p)
      (controlledNormalizedModAdd control scratch L c p) ∧
    ExactControl control scratch (cuccaroNormalizedModSub L c p)
      (controlledNormalizedModSub control scratch L c p) := by
  have nd := normalized_views_nodup L hn
  have ca := normalized_views_away L control hc
  have ta := normalized_views_away L scratch ht
  have normProper := cuccaroNormalize_proper L.normalize c nd.1
  have normSupport := cuccaroNormalize_wires_subset L.normalize c
  have normC : control∉wires (cuccaroNormalize L.normalize c) := by
    intro h
    exact ca.1 (List.mem_toFinset.mp (normSupport h))
  have normT : scratch∉wires (cuccaroNormalize L.normalize c) := by
    intro h
    exact ta.1 (List.mem_toFinset.mp (normSupport h))
  have modProper := cuccaroMod_unitary L.modular p nd.2
  have modSupport := cuccaroMod_wires_subset L.modular n p (L.modular_widths n hw)
  have addC : control∉wires (cuccaroModAdd L.modular p) := by
    intro h
    exact ca.2 (List.mem_toFinset.mp (modSupport.1 h))
  have addT : scratch∉wires (cuccaroModAdd L.modular p) := by
    intro h
    exact ta.2 (List.mem_toFinset.mp (modSupport.1 h))
  have subC : control∉wires (cuccaroModSub L.modular p) := by
    intro h
    exact ca.2 (List.mem_toFinset.mp (modSupport.2 h))
  have subT : scratch∉wires (cuccaroModSub L.modular p) := by
    intro h
    exact ta.2 (List.mem_toFinset.mp (modSupport.2 h))
  have add := ExactControl.direct control scratch (cuccaroModAdd L.modular p)
    modProper.1 addC addT hct
  have sub := ExactControl.direct control scratch (cuccaroModSub L.modular p)
    modProper.2 subC subT hct
  exact ⟨ExactControl.sandwich normProper normC normT add,
    ExactControl.sandwich normProper normC normT sub⟩

theorem controlledNormalizedMod_counts (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (n c p : Nat) (hw : L.Widths n) :
    (toffoliCount (controlledNormalizedModAdd control scratch L c p)=
      2*(4*n-2)+3*(10*n-2)+cnotCount (cuccaroModAdd L.modular p) ∧
      measurementCount (controlledNormalizedModAdd control scratch L c p)=0) ∧
    (toffoliCount (controlledNormalizedModSub control scratch L c p)=
      2*(4*n-2)+3*(12*n-2)+cnotCount (cuccaroModSub L.modular p) ∧
      measurementCount (controlledNormalizedModSub control scratch L c p)=0) := by
  have norm := cuccaroNormalize_counts L.normalize n c (L.normalize_widths n hw)
  have add := cuccaroModAdd_counts L.modular n p (L.modular_widths n hw)
  have sub := cuccaroModSub_counts L.modular n p (L.modular_widths n hw)
  simp only [controlledNormalizedModAdd,controlledNormalizedModSub,
    toffoliCount_append,measurementCount_append,controlUnitary_toffoliCount,
    controlUnitary_measurementCount,norm.1.1,norm.1.2,norm.2.1,norm.2.2,
    add.1,sub.1]
  constructor
  · constructor
    · omega
    · trivial
  · constructor
    · omega
    · trivial

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroCnotResources.lean
noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def constantWeight : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,k => (if k%2=1 then 1 else 0)+constantWeight n (k/2)

theorem xorConstant_cnotCount (r : List Wire) (k : Nat) :
    cnotCount (xorConstant r k)=0 := by
  induction r generalizing k with
  | nil => rfl
  | cons q r ih =>
    by_cases h : k%2=1 <;> simp [xorConstant,h,cnotCount,ih]

theorem maskedConstant_cnotCount (c : Wire) (r : List Wire) (k : Nat) :
    cnotCount (maskedConstant c r k)=constantWeight r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons q r ih =>
    by_cases h : k%2=1 <;> simp [maskedConstant,constantWeight,h,cnotCount,ih]

theorem notRegister_cnotCount (r : List Wire) : cnotCount (notRegister r)=0 := by
  induction r with
  | nil => rfl
  | cons q r ih =>
    change cnotCount (Instr.X q::notRegister r)=0
    exact ih

theorem copyRegister_none_cnotCount (a b : List Wire) (hl : a.length=b.length) :
    cnotCount (copyRegister none a b)=a.length := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [copyRegister,cnotCount]
  | cons x a ih =>
    cases b with
    | nil => simp at hl
    | cons y b =>
      have h := ih b (by simpa using hl)
      simp [copyRegister,copyGate,cnotCount,h,Nat.add_comm]

theorem cuccaroAdd_cnotCount (a b : List Wire) (cin : Wire)
    (hl : a.length=b.length) :
    cnotCount (cuccaroAdd a b cin)=if a.length=0 then 0 else 4*a.length-2 := by
  induction a generalizing b cin with
  | nil => cases b <;> simp_all [cuccaroAdd,cnotCount]
  | cons x a ih =>
    cases a with
    | nil =>
      cases b with
      | nil => simp at hl
      | cons y b =>
        have hb : b=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        subst b
        rfl
    | cons x' a =>
      cases b with
      | nil => simp at hl
      | cons y b =>
        cases b with
        | nil => simp at hl
        | cons y' b =>
          have h := ih (y'::b) x (by simpa using hl)
          simp only [cuccaroAdd,cnotCount_append,cuccaroMaj,cuccaroUma,
            cnotCount,List.length_cons,h]
          simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
          omega

theorem cuccaroSub_cnotCount (a b : List Wire) (cin : Wire)
    (hl : a.length=b.length) :
    cnotCount (cuccaroSub a b cin)=if a.length=0 then 0 else 4*a.length-2 := by
  simp only [cuccaroSub,cnotCount_append,notRegister_cnotCount,
    cuccaroAdd_cnotCount a b cin hl,Nat.zero_add,Nat.add_zero]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledNormalizedResources.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

theorem cuccaroMod_cnotCounts (L : CuccaroModLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    cnotCount (cuccaroModAdd L p)=22*n+7+2*constantWeight n p ∧
    cnotCount (cuccaroModSub L p)=24*n+11+2*constantWeight n p := by
  have zl := L.z_length n hw
  have sl := L.scratch_length n hw
  have a1 := cuccaroAdd_cnotCount L.a L.z L.cin (hw.a.trans zl.symm)
  have s1 := cuccaroSub_cnotCount L.scratch L.z L.cin (sl.trans zl.symm)
  have a2 := cuccaroAdd_cnotCount L.work L.low L.cin (hw.work.trans hw.low.symm)
  have s2 := cuccaroSub_cnotCount L.a L.scratch L.cin (hw.a.trans sl.symm)
  have a3 := cuccaroAdd_cnotCount L.a L.scratch L.cin (hw.a.trans sl.symm)
  have s3 := cuccaroSub_cnotCount L.a L.z L.cin (hw.a.trans zl.symm)
  have a4 := cuccaroAdd_cnotCount L.scratch L.z L.cin (sl.trans zl.symm)
  have cp := copyRegister_none_cnotCount L.low L.work (hw.low.trans hw.work.symm)
  have nz : n≠0 := by omega
  simp only [hw.a,hw.work,sl,nz,Nat.add_eq_zero_iff,Nat.one_ne_zero,
    and_false,if_false] at a1 s1 a2 s2 a3 s3 a4
  simp only [cuccaroModAdd,cuccaroModSub,cnotCount_append,
    a1,s1,a2,s2,a3,s3,a4,cp,xorConstant_cnotCount,maskedConstant_cnotCount,
    hw.work,hw.low,cnotCount]
  constructor <;> omega

/-- Kernel-computed full 256-bit constant weight; no external evaluation or sampled
carry/borrow window is used. -/
theorem secp256k1_prime_weight : constantWeight 256 SquareReduction.p=250 := by
  decide

theorem controlledNormalizedMod_secp256k1_counts (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (hw : L.Widths 256) :
    (toffoliCount (controlledNormalizedModAdd control scratch L
        SquareReduction.c SquareReduction.p)=15857 ∧
      measurementCount (controlledNormalizedModAdd control scratch L
        SquareReduction.c SquareReduction.p)=0) ∧
    (toffoliCount (controlledNormalizedModSub control scratch L
        SquareReduction.c SquareReduction.p)=17909 ∧
      measurementCount (controlledNormalizedModSub control scratch L
        SquareReduction.c SquareReduction.p)=0) := by
  have h := controlledNormalizedMod_counts control scratch L 256
    SquareReduction.c SquareReduction.p hw
  have cx := cuccaroMod_cnotCounts L.modular 256 SquareReduction.p
    (L.modular_widths 256 hw) (by omega)
  simpa only [cx.1,cx.2,secp256k1_prime_weight] using h

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareB.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

theorem branchB_suffix_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (B O : Nat)
    (hB : regValue L.core.high base=B) (hBb : B<2^128)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base (B^2) O)
      (L.subTimesC (L.core.product.take 256)++L.core.square128Clear L.core.high)
      (PairFrame L base 0 (subTimesProductValue (B^2) O)) := by
  have highLen := L.core.high_length hw.core
  have highCount (q : Wire) : L.core.high.count q≤L.core.y.count q := by
    have h1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have h2 := (List.drop_sublist 128 L.core.y).count_le q
    simpa [CuccaroStreamedSquareLayout.high] using h1.trans h2
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let O2 := subTimesProductValue (B^2) O
  have timesT := L.subTimesC_pair hw hnd base (B^2) O hO hc
  have clrT := L.square128Clear_pair hw hnd L.core.high highLen highCount base B O2
    hB hBb hprod (PairClean.corePad L base hc) hc.work hc.cin
  intro s records hs
  let s1 := run (L.subTimesC (L.core.product.take 256)) [] s
  let s2 := run (L.core.square128Clear L.core.high) records s1
  have e1 := timesT s [] hs
  have e2 := clrT s1 records e1.2
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have timesm := L.subTimesC_counts hw (L.core.product.take 256) p256
  have exec : run
      (L.subTimesC (L.core.product.take 256)++L.core.square128Clear L.core.high)
      records s=s2 := by
    simp [s1,s2,run_append,timesm.2]
  rw [exec]
  exact ⟨e2.1.trans e1.1,e2.2⟩

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

theorem branchC_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B O : Nat)
    (hA : regValue L.core.low base=A) (hB : regValue L.core.sum base=B)
    (hbound : A+B<2^129) (hprod : regValue L.core.product base=0)
    (hout : regValue L.core.out base=O) (hO : O<SquareReduction.p)
    (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.branchC
      (PairFrame L base 0 (branchCMiddleValue (A+B) O)) := by
  have disPO := L.product_out_disjoint hnd
  have disSP : L.core.sum.Disjoint L.core.product := by
    apply List.disjoint_left.mpr
    intro q hs hp
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hs
    have h2 := List.count_pos_iff.mpr hp
    have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hh2 := (List.drop_sublist 128 L.core.y).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  have disSO : L.core.sum.Disjoint L.core.out := by
    apply List.disjoint_left.mpr
    intro q hs ho
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hs
    have h2 := List.count_pos_iff.mpr ho
    have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hh2 := (List.drop_sublist 128 L.core.y).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  have auxAwaySum (q : Wire)
      (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
      q∉L.core.sum := by
    intro hs
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hs
    have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hh2 := (List.drop_sublist 128 L.core.y).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h h1 h2
    omega
  have prepT := L.prepareSum_frame hw hnd base A B hA hB hbound
    (PairClean.corePad L base hc) hc.cin
  intro s records hs
  have sameBasis : s.basis=base := by
    funext q
    by_cases hp : q∈L.core.product
    · exact (regValue_eq_iff L.core.product _ _).mp
        (hs.product.trans hprod.symm) q hp
    by_cases ho : q∈L.core.out
    · exact (regValue_eq_iff L.core.out _ _).mp (hs.out.trans hout.symm) q ho
    · exact hs.frame q hp ho
  have prepPre : SquareFrame L.core.sum base B s.basis := by
    rw [sameBasis]
    exact ⟨hB,fun _ _ => rfl⟩
  let s1 := run L.core.prepareSum [] s
  have e1 := prepT s [] prepPre
  have prod1 : regValue L.core.product s1.basis=0 := by
    rw [←hprod]
    apply regValue_congr
    intro q hq
    exact e1.2.2 q (fun hs => List.disjoint_left.mp disSP hs hq)
  have out1 : regValue L.core.out s1.basis=O := by
    rw [←hout]
    apply regValue_congr
    intro q hq
    exact e1.2.2 q (fun hs => List.disjoint_left.mp disSO hs hq)
  have clean1 : PairClean L s1.basis := by
    have keep (q : Wire)
        (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
          L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
        s1.basis q=base q :=
      e1.2.2 q (auxAwaySum q hq)
    constructor
    · rw [←hc.pad]
      apply regValue_congr
      intro q hq
      exact keep q (by simp [hq])
    · rw [←hc.work]
      apply regValue_congr
      intro q hq
      exact keep q (by simp [hq])
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have middleT := L.branchC_middle_pair hw hnd s1.basis (A+B) O e1.2.1
    prod1 hO clean1
  have middlePre : PairFrame L s1.basis 0 O s1.basis :=
    ⟨prod1,out1,fun _ _ _ => rfl⟩
  let s2 := run (L.core.square129++L.subRotate128 true++L.core.square129Clear) [] s1
  have e2 := middleT s1 [] middlePre
  let restoreBase : BasisState := fun q => if q∈L.core.out then s2.basis q else s.basis q
  have lowRestore : regValue L.core.low restoreBase=A := by
    rw [←hA]
    apply regValue_congr
    intro q hq
    have away : q∉L.core.out := by
      intro ho
      have h := List.nodup_iff_count.mp hnd q
      have h1 := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
      have h3 := List.count_pos_iff.mpr ho
      simp only [wires,CuccaroStreamedSquareLayout.wires,
        CuccaroStreamedSquareLayout.low,List.count_append,List.count_cons,
        List.count_nil] at h
      omega
    simp [restoreBase,away,sameBasis]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    rw [←hB]
    apply regValue_congr
    intro q hq
    simp [restoreBase,List.disjoint_left.mp disSO hq,sameBasis]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    rw [←PairClean.corePad L base hc]
    apply regValue_congr
    intro q hq
    have away := (L.pairAuxAway hnd q (by simp [foldPad,hq])).2
    simp [restoreBase,away,sameBasis]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway hnd L.core.cin (by simp)).2
    simp [restoreBase,away,sameBasis,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) s2.basis := by
    constructor
    · calc
        regValue L.core.sum s2.basis = regValue L.core.sum s1.basis :=
          regValue_congr _ _ _ (fun q hq => e2.2.frame q
            (List.disjoint_left.mp disSP hq) (List.disjoint_left.mp disSO hq))
        _ = A+B := e1.2.1
    · intro q hq
      simp only [restoreBase]
      by_cases ho : q∈L.core.out
      · simp [ho]
      rw [if_neg ho]
      by_cases hp : q∈L.core.product
      · have z2 := (regValue_zero _ _).mp e2.2.product q hp
        have z0 := (regValue_zero _ _).mp hs.product q hp
        exact z2.trans z0.symm
      · exact (e2.2.frame q hp ho).trans ((e1.2.2 q hq).trans
          (congrFun sameBasis q).symm)
  have clearT := L.clearSum_frame hw hnd restoreBase A B lowRestore sumRestore
    hbound padRestore cinRestore
  let s3 := run L.core.clearSum records s2
  have e3 := clearT s2 records clearPre
  have finalProd : regValue L.core.product s3.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have es := e3.2.2 q (fun hs => List.disjoint_left.mp disSP hs hq)
    have qo : q∉L.core.out := List.disjoint_left.mp disPO hq
    simp only [restoreBase,if_neg qo] at es
    exact es.trans ((regValue_zero _ _).mp hs.product q hq)
  have finalOut : regValue L.core.out s3.basis=branchCMiddleValue (A+B) O := by
    rw [←e2.2.out]
    apply regValue_congr
    intro q hq
    have es := e3.2.2 q (fun hs => List.disjoint_left.mp disSO hs hq)
    simp only [restoreBase,if_pos hq] at es
    exact es
  have prepM := L.core.sum_counts hw.core
  have squareM := L.core.square129_counts hw.core
  have rotM := L.rotate128_counts hw
  have middleM : measurementCount
      (L.core.square129++L.subRotate128 true++L.core.square129Clear)=0 := by
    simp [measurementCount_append,squareM.1.2,squareM.2.2,rotM.2.2.2]
  have exec : run L.branchC records s=s3 := by
    simp [branchC,s1,s2,s3,run_append,prepM.1.2,squareM.1.2,
      squareM.2.2,rotM.2.2.2]
  rw [exec]
  refine ⟨e3.1.trans (e2.1.trans e1.1),finalProd,finalOut,?_⟩
  intro q hp ho
  by_cases hsq : q∈L.core.sum
  · have eqsum := (regValue_eq_iff L.core.sum s3.basis restoreBase).mp
        (e3.2.1.trans sumRestore.symm) q hsq
    simpa [restoreBase,ho,sameBasis] using eqsum
  · have ec := e3.2.2 q hsq
    simp only [restoreBase,if_neg ho] at ec
    exact ec.trans (congrFun sameBasis q)

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareOpaque.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

/-- An executable list append hidden behind an irreducible boundary.  This
prevents Lean's kernel from recursively expanding a million-instruction left
operand when independently checked circuit specifications are sequenced. -/
def checkedSeq (a b : Program) : Program := a++b

theorem checkedSeq_eq (a b : Program) : checkedSeq a b=a++b := by rfl

attribute [irreducible] checkedSeq

theorem checkedSeq_correct {P Q R : BasisState → Prop} {a b : Program}
    (ha : Triple P a Q) (hb : Triple Q b R) :
    Triple P (checkedSeq a b) R := by
  rw [checkedSeq_eq]
  exact ha.seq hb

/-- Kernel-sealed aliases keep the verified branch boundaries intact when the
full streamed circuit is composed.  Their executable values remain the exact
gate programs below. -/
def checkedBranchA (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.branchA

def checkedBranchBPrefix (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.core.square128 L.core.high++L.addRotate128 false

def checkedBranchBSuffix (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.subTimesC (L.core.product.take 256)++L.core.square128Clear L.core.high

def checkedBranchC (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.branchC

theorem checkedBranchA_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedBranchA=L.branchA := by rfl

theorem checkedBranchBPrefix_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedBranchBPrefix=
      L.core.square128 L.core.high++L.addRotate128 false := by rfl

theorem checkedBranchBSuffix_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedBranchBSuffix=
      L.subTimesC (L.core.product.take 256)++
        L.core.square128Clear L.core.high := by rfl

theorem checkedBranchC_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedBranchC=L.branchC := by rfl

attribute [irreducible] checkedBranchA checkedBranchBPrefix checkedBranchBSuffix checkedBranchC

def checkedFirstHalf (L : CuccaroStreamedSquareWideLayout) : Program :=
  checkedSeq L.checkedBranchA L.checkedBranchBPrefix

def checkedSecondHalf (L : CuccaroStreamedSquareWideLayout) : Program :=
  checkedSeq L.checkedBranchBSuffix L.checkedBranchC

theorem checkedFirstHalf_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedFirstHalf=checkedSeq L.checkedBranchA L.checkedBranchBPrefix := by rfl

theorem checkedSecondHalf_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedSecondHalf=checkedSeq L.checkedBranchBSuffix L.checkedBranchC := by rfl

attribute [irreducible] checkedFirstHalf checkedSecondHalf

def checkedProgram (L : CuccaroStreamedSquareWideLayout) : Program :=
  checkedSeq L.checkedFirstHalf L.checkedSecondHalf

theorem checkedProgram_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedProgram=checkedSeq L.checkedFirstHalf L.checkedSecondHalf := by rfl

attribute [irreducible] checkedProgram

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedA.lean
noncomputable section

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedBranchA_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A O : Nat)
    (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedBranchA
      (PairFrame L base 0 (branchAValue A O)) := by
  rw [L.checkedBranchA_eq]
  exact L.branchA_pair hw hnd base A O hA hAb hprod hO hc

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedBPrefix.lean
noncomputable section

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedBranchB_prefix_pair (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState) (B O : Nat)
    (hB : regValue L.core.high base=B)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedBranchBPrefix
      (PairFrame L base (B^2) (addRotateProductValue (B^2) O false)) := by
  rw [L.checkedBranchBPrefix_eq]
  exact L.branchB_prefix_pair hw hnd base B O hB hO hc

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedFirst.lean
noncomputable section

set_option maxRecDepth 20000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

private theorem branchAValue_lt (A O : Nat) :
    branchAValue A O<SquareReduction.p := by
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  unfold branchAValue addRotateProductValue addRotate128Value
  simp only [Bool.false_eq_true,if_false]
  unfold addCMinusOneValue addModValue subModValue
  exact Nat.mod_lt _ hp

attribute [local irreducible] branchAValue addRotateProductValue

theorem checkedFirstHalf_pair (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState)
    (A B O : Nat) (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hB : regValue L.core.high base=B)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedFirstHalf
      (PairFrame L base (B^2)
        (addRotateProductValue (B^2) (branchAValue A O) false)) := by
  have ha := L.checkedBranchA_pair hw hnd base A O hA hAb hprod hO hc
  have hb := L.checkedBranchB_prefix_pair hw hnd base B (branchAValue A O) hB
    (branchAValue_lt A O) hc
  rw [L.checkedFirstHalf_eq]
  exact checkedSeq_correct ha hb

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedBSuffix.lean
noncomputable section

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedBranchB_suffix_pair (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState) (B O : Nat)
    (hB : regValue L.core.high base=B) (hBb : B<2^128)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base (B^2) O) L.checkedBranchBSuffix
      (PairFrame L base 0 (subTimesProductValue (B^2) O)) := by
  rw [L.checkedBranchBSuffix_eq]
  exact L.branchB_suffix_pair hw hnd base B O hB hBb hprod hO hc

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedC.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

/-- Rebase the cross-term branch on the state produced by the two leaf
branches, then transport its frame back to the original stage entry state. -/
theorem checkedBranchC_pair_rebased (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState) (A B O : Nat)
    (hA : regValue L.core.low base=A) (hB : regValue L.core.sum base=B)
    (hbound : A+B<2^129) (hO : O<SquareReduction.p)
    (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedBranchC
      (PairFrame L base 0 (branchCMiddleValue (A+B) O)) := by
  rw [L.checkedBranchC_eq]
  have lowAway (q : Wire) (hq : q∈L.core.low) :
      q∉L.core.product ∧ q∉L.core.out := by
    constructor <;> intro hm
    all_goals
      have h := List.nodup_iff_count.mp hnd q
      have h1 := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
      have h2 := List.count_pos_iff.mpr hm
      simp only [wires,CuccaroStreamedSquareLayout.wires,
        List.count_append,List.count_cons,List.count_nil] at h
      omega
  have sumAway (q : Wire) (hq : q∈L.core.sum) :
      q∉L.core.product ∧ q∉L.core.out := by
    constructor <;> intro hm
    all_goals
      have h := List.nodup_iff_count.mp hnd q
      have h1 := List.count_pos_iff.mpr hq
      have h2 := List.count_pos_iff.mpr hm
      have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
      have hh2 := (List.drop_sublist 128 L.core.y).count_le q
      simp only [wires,CuccaroStreamedSquareLayout.wires,
        CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
        List.count_append,List.count_cons,List.count_nil] at h h1
      omega
  intro s records hs
  have hAs : regValue L.core.low s.basis=A := by
    rw [←hA]
    apply regValue_congr
    intro q hq
    exact hs.frame q (lowAway q hq).1 (lowAway q hq).2
  have hBs : regValue L.core.sum s.basis=B := by
    rw [←hB]
    apply regValue_congr
    intro q hq
    exact hs.frame q (sumAway q hq).1 (sumAway q hq).2
  have cleanS := PairFrame.clean L hnd base 0 O s.basis hs hc
  have ct := L.branchC_pair hw hnd s.basis A B O hAs hBs hbound
    hs.product hs.out hO cleanS
  have preS : PairFrame L s.basis 0 O s.basis :=
    ⟨hs.product,hs.out,fun _ _ _ => rfl⟩
  obtain ⟨phase,out⟩ := ct s records preS
  refine ⟨phase,out.product,out.out,?_⟩
  intro q hp ho
  exact (out.frame q hp ho).trans (hs.frame q hp ho)

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareCheckedSecond.lean
noncomputable section

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedSecondHalf_pair (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState)
    (A B O : Nat) (hA : regValue L.core.low base=A)
    (hHigh : regValue L.core.high base=B)
    (hSum : regValue L.core.sum base=B) (hBb : B<2^128)
    (hprod : regValue L.core.product base=0) (hsum : A+B<2^129)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base (B^2) O) L.checkedSecondHalf
      (PairFrame L base 0
        (branchCMiddleValue (A+B) (subTimesProductValue (B^2) O))) := by
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb := L.checkedBranchB_suffix_pair hw hnd base B O hHigh hBb hprod hO hc
  have hc' := L.checkedBranchC_pair_rebased hw hnd base A B
    (subTimesProductValue (B^2) O) hA hSum hsum (Nat.mod_lt _ hp) hc
  rw [L.checkedSecondHalf_eq]
  exact checkedSeq_correct hb hc'

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareFull.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

private theorem addRotateProductValue_lt (P O : Nat) :
    addRotateProductValue P O false<SquareReduction.p := by
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  unfold addRotateProductValue addRotate128Value
  simp only [Bool.false_eq_true,if_false]
  unfold addCMinusOneValue addModValue subModValue
  exact Nat.mod_lt _ hp

attribute [local irreducible] branchAValue addRotateProductValue
  subTimesProductValue branchCMiddleValue

/-- The three independently verified streamed branches compose without
expanding their gate streams.  Keeping the value expression abstract here is
intentional: the following arithmetic lemma identifies it with subtraction of
the full 256-bit square modulo `p`. -/
theorem program_pair_raw (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B O : Nat)
    (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hB : regValue L.core.high base=B) (hBb : B<2^128)
    (hsumCarry : base L.core.sumCarry=false)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p)
    (hsum : A+B<2^129) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedProgram
      (PairFrame L base 0
        (branchCMiddleValue (A+B)
          (subTimesProductValue (B^2)
            (addRotateProductValue (B^2) (branchAValue A O) false)))) := by
  have first := L.checkedFirstHalf_pair hw hnd base A B O hA hAb hB hprod hO hc
  have hsumValue : regValue L.core.sum base=B := by
    rw [CuccaroStreamedSquareLayout.sum,regValue_append,hB]
    change B+2^L.core.high.length*(if base L.core.sumCarry then 1 else 0)=B
    simp [hsumCarry]
  have second := L.checkedSecondHalf_pair hw hnd base A B
    (addRotateProductValue (B^2) (branchAValue A O) false) hA hB hsumValue hBb
    hprod hsum (addRotateProductValue_lt (B^2) (branchAValue A O)) hc
  rw [L.checkedProgram_eq]
  exact checkedSeq_correct first second

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareSpec.lean
noncomputable section

set_option maxRecDepth 5000000
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedProgram_original (L : CuccaroStreamedSquareWideLayout) :
    L.checkedProgram=L.program := by
  rw [L.checkedProgram_eq,L.checkedFirstHalf_eq,L.checkedSecondHalf_eq,
    checkedSeq_eq,checkedSeq_eq,checkedSeq_eq,L.checkedBranchA_eq,
    L.checkedBranchBPrefix_eq,L.checkedBranchBSuffix_eq,L.checkedBranchC_eq]
  simp only [program,branchB,List.append_assoc]

theorem program_square_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B O : Nat)
    (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hB : regValue L.core.high base=B) (hBb : B<2^128)
    (hsumCarry : base L.core.sumCarry=false)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.program
      (PairFrame L base 0
        ((O+SquareReduction.p-((A+2^128*B)^2)%SquareReduction.p)%SquareReduction.p)) := by
  have hsum : A+B<2^129 := by
    norm_num [Nat.pow_succ] at hAb hBb ⊢
    omega
  have raw := L.program_pair_raw hw hnd base A B O hA hAb hB hBb hsumCarry
    hprod hO hsum hc
  have result := streamedSquareValue_exact A B O hAb hBb
  change branchCMiddleValue (A+B)
      (subTimesProductValue (B^2)
        (addRotateProductValue (B^2) (branchAValue A O) false))=_ at result
  rw [result,L.checkedProgram_original] at raw
  exact raw

/-- Exact square subtraction on every 256-bit source and canonical output.
The source, all workspace bits, every outside wire and the phase are restored. -/
theorem program_square_correct (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hprod : regValue L.core.product s.basis=0)
    (hsumCarry : s.basis L.core.sumCarry=false) (hc : PairClean L s.basis) :
    (run L.program records s).phase=s.phase ∧
    regValue L.core.out (run L.program records s).basis=
      (O+SquareReduction.p-(Y^2)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run L.program records s).basis q=s.basis q := by
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  have hab : A<2^128 := by
    simpa only [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have hbb : B<2^128 := by
    simpa only [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have split : A+2^128*B=Y := by
    have hb : L.core.high=L.core.y.drop 128 := by
      simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have h := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at h
    simpa only [A,B,CuccaroStreamedSquareLayout.low,hb,
      show min 128 256=128 by decide] using h.symm
  have pre : PairFrame L s.basis 0 O s.basis :=
    ⟨hprod,ho,fun _ _ _ => rfl⟩
  have h := L.program_square_pair hw hnd s.basis A B O rfl hab rfl hbb
    hsumCarry hprod hO hc s records pre
  rw [split] at h
  refine ⟨h.1,h.2.out,?_⟩
  intro q hqo
  by_cases hqp : q∈L.core.product
  · exact ((regValue_zero _ _).mp h.2.product q hqp).trans
      ((regValue_zero _ _).mp hprod q hqp).symm
  · exact h.2.frame q hqp hqo

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

theorem Certified.append {L : CuccaroStreamedSquareWideLayout} {a b : Program}
    (ha : L.Certified a) (hb : L.Certified b) : L.Certified (a++b) := by
  exact ⟨properProgram_append a b |>.mpr ⟨ha.1,hb.1⟩,
    by simpa only [wires_append,Finset.union_subset_iff] using And.intro ha.2 hb.2⟩

theorem Certified.reverse {L : CuccaroStreamedSquareWideLayout} {a : Program}
    (ha : L.Certified a) : L.Certified a.reverse := by
  exact ⟨properProgram_reverse a ha.1,by simpa only [wires_reverse] using ha.2⟩

theorem source_certified (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (src : List Wire) (hv : L.SourceView src) :
    L.Certified (L.addSource src) ∧ L.Certified (L.subSource src) := by
  have nd := L.source_nodup hn src hv
  have proper := cuccaroNormalizedMod_unitary (L.source src)
    SquareReduction.c SquareReduction.p nd
  have support := cuccaroNormalizedMod_wires_subset (L.source src) 256
    SquareReduction.c SquareReduction.p (L.source_widths hw src hv.length)
  have srcMem (q : Wire) (hq : q∈src) : q∈L.core.product ∨ q∈L.foldPad := by
    by_contra h
    simp only [not_or] at h
    have hs := hv.count_le q
    have hc := List.count_pos_iff.mpr hq
    rw [List.count_eq_zero.mpr h.1,List.count_eq_zero.mpr h.2] at hs
    omega
  have embed : (L.source src).wires.toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [source,CuccaroNormalizedModLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    have hs : q∈src → q∈L.core.product ∨ q∈L.core.pad ∨ q∈L.overflowPad := by
      intro h
      have m := srcMem q h
      simpa only [foldPad,List.mem_append,or_assoc] using m
    tauto
  exact ⟨⟨proper.1,support.1.trans embed⟩,⟨proper.2,support.2.trans embed⟩⟩

theorem producer_certified (L : CuccaroStreamedSquareWideLayout)
    (hn : L.wires.Nodup) (src dst mask : List Wire) (n : Nat)
    (hsrc : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hdst : ∀q,dst.count q≤L.core.product.count q)
    (hmask : ∀q,mask.count q≤L.core.work.count q)
    (hs : src.length=n) (hd : dst.length=2*n)
    (hm : n≤mask.length) (hp : 1≤L.core.pad.length) (hn2 : 2≤n) :
    L.Certified (cuccaroSignedTriangularSquare src dst L.core.pad mask [] L.core.cin) ∧
    L.Certified (cuccaroSignedTriangularSquareClear src dst L.core.pad mask [] L.core.cin) := by
  have nd : (L.core.cin::src++dst++L.core.pad++mask++[]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have h1 := hsrc q
    have h2 := hdst q
    have h3 := hmask q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at h h1 ⊢
    omega
  have proper := cuccaroSignedTriangularSquare_proper L.core.cin
    src dst L.core.pad mask [] nd
  have supp := cuccaroSignedTriangularSquare_wires_subset L.core.cin
    src dst L.core.pad mask [] (by omega) (by omega) hp (by omega)
  have embed : (L.core.cin::src++dst++L.core.pad++mask++[]).toFinset⊆L.wires.toFinset := by
    intro q hq
    have pos := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
    have h1 := hsrc q
    have h2 := hdst q
    have h3 := hmask q
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at pos h1 ⊢
    omega
  exact ⟨⟨proper,supp.1.trans embed⟩,
    ⟨properProgram_reverse _ proper,supp.2.trans embed⟩⟩

theorem square128_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (src : List Wire)
    (hs : src.length=128) (hsrc : ∀q,src.count q≤L.core.y.count q) :
    L.Certified (L.core.square128 src) ∧ L.Certified (L.core.square128Clear src) := by
  apply L.producer_certified hn src (L.core.product.take 256) (L.core.work.take 128) 128
    (by intro q; have h:=hsrc q; simp only [List.count_append]; omega)
    (by intro q; exact (List.take_sublist 256 L.core.product).count_le q)
    (by intro q; exact (List.take_sublist 128 L.core.work).count_le q) hs
    (by simp [hw.core.product]) (by simp [hw.core.work])
    (by rw [hw.core.pad]; omega) (by omega)

theorem square129_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    L.Certified L.core.square129 ∧ L.Certified L.core.square129Clear := by
  apply L.producer_certified hn L.core.sum L.core.product (L.core.work.take 129) 129
    (by
      intro q
      have h1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
      have h2 := (List.drop_sublist 128 L.core.y).count_le q
      simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
        List.count_append] at h1 ⊢
      omega)
    (by intro q; exact le_rfl)
    (by intro q; exact (List.take_sublist 129 L.core.work).count_le q)
    (L.core.sum_length hw.core) (by rw [hw.core.product])
    (by simp [hw.core.work]) (by rw [hw.core.pad]; omega) (by omega)

theorem cMinusOne_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (src : List Wire)
    (hsrc : ∀q,src.count q≤L.core.product.count q)
    (hs2 : 2≤src.length) (hs : src.length+32≤256) :
    L.Certified (L.addCMinusOne src) ∧ L.Certified (L.subCMinusOne src) := by
  have s4 := L.source_certified hw hn (L.shifted src 4)
    (L.shifted_view hw src hsrc 4 hs2 (by omega))
  have s6 := L.source_certified hw hn (L.shifted src 6)
    (L.shifted_view hw src hsrc 6 hs2 (by omega))
  have s10 := L.source_certified hw hn (L.shifted src 10)
    (L.shifted_view hw src hsrc 10 hs2 (by omega))
  have s32 := L.source_certified hw hn (L.shifted src 32)
    (L.shifted_view hw src hsrc 32 hs2 hs)
  exact ⟨((s4.1.append s6.2).append s10.1).append s32.1,
    ((s4.2.append s6.1).append s10.2).append s32.2⟩

theorem rotate128_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (overhang : Bool) :
    L.Certified (L.addRotate128 overhang) ∧ L.Certified (L.subRotate128 overhang) := by
  have rot := L.source_certified hw hn L.rotated128 (L.rotated128_view hw)
  have terms := L.cMinusOne_certified hw hn (L.core.product.drop 128)
    (L.productDrop_count 128) (by simp [hw.core.product]) (by simp [hw.core.product])
  have tail := L.source_certified hw hn (L.shifted (L.core.product.drop 256) 128)
    (L.shiftedProductDrop_view hw 256 128 (by simp [hw.core.product])
      (by simp [hw.core.product]))
  have nil : L.Certified [] := by simp [Certified,ProperProgram,ECDSAAdd.wires]
  cases overhang
  · exact ⟨(rot.1.append terms.1).append nil,(rot.2.append terms.2).append nil⟩
  · exact ⟨(rot.1.append terms.1).append tail.1,(rot.2.append terms.2).append tail.2⟩

theorem shiftFull_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (j : Nat)
    (hj2 : 2≤j) (hj : j≤224) :
    L.Certified (L.addShiftFull (L.core.product.take 256) j) ∧
    L.Certified (L.subShiftFull (L.core.product.take 256) j) := by
  have rot := L.source_certified hw hn (rotateFull (L.core.product.take 256) j)
    (L.rotateFull_view hw j (by omega))
  have len : ((L.core.product.take 256).drop (256-j)).length=j := by
    simp [hw.core.product]
    omega
  have terms := L.cMinusOne_certified hw hn
    ((L.core.product.take 256).drop (256-j)) (L.productTakeDrop_count (256-j))
    (by rw [len]; exact hj2) (by rw [len]; omega)
  have jnz : j≠0 := by omega
  simpa only [addShiftFull,subShiftFull,jnz,if_false] using
    And.intro (rot.1.append terms.1) (rot.2.append terms.2)

theorem timesC_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    L.Certified (L.subTimesC (L.core.product.take 256)) := by
  have base := L.source_certified hw hn (L.core.product.take 256)
    (L.productTake256_view hw)
  have s4 := L.shiftFull_certified hw hn 4 (by omega) (by omega)
  have s6 := L.shiftFull_certified hw hn 6 (by omega) (by omega)
  have s10 := L.shiftFull_certified hw hn 10 (by omega) (by omega)
  have s32 := L.shiftFull_certified hw hn 32 (by omega) (by omega)
  simpa only [subTimesC,subShiftFull,if_true] using
    (((base.2.append s4.2).append s6.1).append s10.2).append s32.2

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

theorem program_certified (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : L.Certified L.program := by
  have low := L.square128_certified hw hn L.core.low (L.core.low_length hw.core)
    (by intro q; exact (List.take_sublist 128 L.core.y).count_le q)
  have high := L.square128_certified hw hn L.core.high (L.core.high_length hw.core)
    (by
      intro q
      exact ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
        ((List.drop_sublist 128 L.core.y).count_le q))
  have sum := L.square129_certified hw hn
  have prepare := L.sum_certified hw hn
  have rotate0 := L.rotate128_certified hw hn false
  have rotate1 := L.rotate128_certified hw hn true
  have sub := L.source_certified hw hn (L.core.product.take 256)
    (L.productTake256_view hw)
  have times := L.timesC_certified hw hn
  have a : L.Certified L.branchA :=
    (((low.1.append sub.2).append rotate0.1).append low.2)
  have b : L.Certified L.branchB :=
    (high.1.append rotate0.1).append (times.append high.2)
  have c : L.Certified L.branchC :=
    (prepare.1.append ((sum.1.append rotate1.2).append sum.2)).append prepare.2
  exact (a.append b).append c

theorem program_static_support (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : qubitCount L.program≤1287 := by
  have h := L.program_certified hw hn
  rw [qubitCount]
  calc
    _ ≤ L.wires.toFinset.card := Finset.card_le_card h.2
    _ = 1287 := by rw [List.toFinset_card_of_nodup hn,L.wires_length hw]

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

def controlledAddSource (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (src : List Wire) : Program :=
  controlledNormalizedModAdd c scratch (L.source src) SquareReduction.c SquareReduction.p

def controlledSubSource (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (src : List Wire) : Program :=
  controlledNormalizedModSub c scratch (L.source src) SquareReduction.c SquareReduction.p

def controlledAddCMinusOne (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (src : List Wire) : Program :=
  L.controlledAddSource c scratch (L.shifted src 4)++
  L.controlledSubSource c scratch (L.shifted src 6)++
  L.controlledAddSource c scratch (L.shifted src 10)++
  L.controlledAddSource c scratch (L.shifted src 32)

def controlledSubCMinusOne (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (src : List Wire) : Program :=
  L.controlledSubSource c scratch (L.shifted src 4)++
  L.controlledAddSource c scratch (L.shifted src 6)++
  L.controlledSubSource c scratch (L.shifted src 10)++
  L.controlledSubSource c scratch (L.shifted src 32)

def controlledAddRotate128 (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (overhang : Bool) : Program :=
  L.controlledAddSource c scratch L.rotated128++
  L.controlledAddCMinusOne c scratch (L.core.product.drop 128)++
  if overhang then L.controlledAddSource c scratch
    (L.shifted (L.core.product.drop 256) 128) else []

def controlledSubRotate128 (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (overhang : Bool) : Program :=
  L.controlledSubSource c scratch L.rotated128++
  L.controlledSubCMinusOne c scratch (L.core.product.drop 128)++
  if overhang then L.controlledSubSource c scratch
    (L.shifted (L.core.product.drop 256) 128) else []

def controlledAddShiftFull (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (j : Nat) : Program :=
  if j=0 then L.controlledAddSource c scratch (L.core.product.take 256)
  else L.controlledAddSource c scratch (rotateFull (L.core.product.take 256) j)++
    L.controlledAddCMinusOne c scratch ((L.core.product.take 256).drop (256-j))

def controlledSubShiftFull (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (j : Nat) : Program :=
  if j=0 then L.controlledSubSource c scratch (L.core.product.take 256)
  else L.controlledSubSource c scratch (rotateFull (L.core.product.take 256) j)++
    L.controlledSubCMinusOne c scratch ((L.core.product.take 256).drop (256-j))

def controlledTimesC (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  L.controlledSubShiftFull c scratch 0++L.controlledSubShiftFull c scratch 4++
  L.controlledAddShiftFull c scratch 6++L.controlledSubShiftFull c scratch 10++
  L.controlledSubShiftFull c scratch 32

def controlledBranchA (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  L.core.square128 L.core.low++
    (L.controlledSubSource c scratch (L.core.product.take 256)++
      L.controlledAddRotate128 c scratch false)++L.core.square128Clear L.core.low

def controlledBranchB (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  L.core.square128 L.core.high++
    (L.controlledAddRotate128 c scratch false++L.controlledTimesC c scratch)++
    L.core.square128Clear L.core.high

def controlledBranchC (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  (L.core.prepareSum++L.core.square129)++L.controlledSubRotate128 c scratch true++
    (L.core.square129Clear++L.core.clearSum)

/-- Compute and uncompute each square unconditionally.  Normalize each source
unconditionally too; only its canonical modular output update is controlled. -/
def controlledProgram (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  L.controlledBranchA c scratch++L.controlledBranchB c scratch++L.controlledBranchC c scratch

theorem source_layout_subset (L : CuccaroStreamedSquareWideLayout)
    (src : List Wire) (hv : L.SourceView src) : (L.source src).wires⊆L.wires := by
  intro q hq
  have srcMem (hq : q∈src) : q∈L.core.product ∨ q∈L.foldPad := by
    by_contra h
    simp only [not_or] at h
    have hs := hv.count_le q
    have hc := List.count_pos_iff.mpr hq
    rw [List.count_eq_zero.mpr h.1,List.count_eq_zero.mpr h.2] at hs
    omega
  simp only [source,CuccaroNormalizedModLayout.wires,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [wires,CuccaroStreamedSquareLayout.wires,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  have hs : q∈src → q∈L.core.product ∨ q∈L.core.pad ∨ q∈L.overflowPad := by
    intro h
    simpa only [foldPad,List.mem_append,or_assoc] using srcMem h
  tauto

variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c scratch : Wire) (hc : c∉L.wires) (ht : scratch∉L.wires) (hct : c≠scratch)
include hw hn hc ht hct

theorem controlledSource_exact (src : List Wire) (hv : L.SourceView src) :
    ExactControl c scratch (L.addSource src) (L.controlledAddSource c scratch src) ∧
    ExactControl c scratch (L.subSource src) (L.controlledSubSource c scratch src) := by
  have embed := L.source_layout_subset src hv
  exact controlledNormalizedMod_exact c scratch (L.source src) 256
    SquareReduction.c SquareReduction.p (L.source_widths hw src hv.length)
    (L.source_nodup hn src hv) (fun h => hc (embed h)) (fun h => ht (embed h)) hct

theorem controlledCMinusOne_exact (src : List Wire)
    (hsrc : ∀q,src.count q≤L.core.product.count q)
    (hs2 : 2≤src.length) (hs : src.length+32≤256) :
    ExactControl c scratch (L.addCMinusOne src) (L.controlledAddCMinusOne c scratch src) ∧
    ExactControl c scratch (L.subCMinusOne src) (L.controlledSubCMinusOne c scratch src) := by
  have s4 := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shifted_view hw src hsrc 4 hs2 (by omega))
  have s6 := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shifted_view hw src hsrc 6 hs2 (by omega))
  have s10 := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shifted_view hw src hsrc 10 hs2 (by omega))
  have s32 := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shifted_view hw src hsrc 32 hs2 hs)
  exact ⟨((s4.1.append s6.2).append s10.1).append s32.1,
    ((s4.2.append s6.1).append s10.2).append s32.2⟩

theorem controlledRotate128_exact (overhang : Bool) :
    ExactControl c scratch (L.addRotate128 overhang) (L.controlledAddRotate128 c scratch overhang) ∧
    ExactControl c scratch (L.subRotate128 overhang) (L.controlledSubRotate128 c scratch overhang) := by
  have rot := L.controlledSource_exact hw hn c scratch hc ht hct _ (L.rotated128_view hw)
  have terms := L.controlledCMinusOne_exact hw hn c scratch hc ht hct
    (L.core.product.drop 128) (L.productDrop_count 128)
    (by simp [hw.core.product]) (by simp [hw.core.product])
  have tail := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shiftedProductDrop_view hw 256 128 (by simp [hw.core.product])
      (by simp [hw.core.product]))
  cases overhang
  · exact ⟨(rot.1.append terms.1).append (ExactControl.nil c scratch),
      (rot.2.append terms.2).append (ExactControl.nil c scratch)⟩
  · exact ⟨(rot.1.append terms.1).append tail.1,
      (rot.2.append terms.2).append tail.2⟩

theorem controlledShiftFull_exact (j : Nat) (hj2 : 2≤j) (hj : j≤224) :
    ExactControl c scratch (L.addShiftFull (L.core.product.take 256) j)
      (L.controlledAddShiftFull c scratch j) ∧
    ExactControl c scratch (L.subShiftFull (L.core.product.take 256) j)
      (L.controlledSubShiftFull c scratch j) := by
  have rot := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.rotateFull_view hw j (by omega))
  have len : ((L.core.product.take 256).drop (256-j)).length=j := by
    simp [hw.core.product]
    omega
  have terms := L.controlledCMinusOne_exact hw hn c scratch hc ht hct
    ((L.core.product.take 256).drop (256-j)) (L.productTakeDrop_count (256-j))
    (by rw [len]; exact hj2) (by rw [len]; omega)
  have jnz : j≠0 := by omega
  simpa only [addShiftFull,subShiftFull,controlledAddShiftFull,controlledSubShiftFull,
    jnz,if_false] using And.intro (rot.1.append terms.1) (rot.2.append terms.2)

theorem controlledTimesC_exact :
    ExactControl c scratch (L.subTimesC (L.core.product.take 256))
      (L.controlledTimesC c scratch) := by
  have base := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.productTake256_view hw)
  have s4 := L.controlledShiftFull_exact hw hn c scratch hc ht hct 4 (by omega) (by omega)
  have s6 := L.controlledShiftFull_exact hw hn c scratch hc ht hct 6 (by omega) (by omega)
  have s10 := L.controlledShiftFull_exact hw hn c scratch hc ht hct 10 (by omega) (by omega)
  have s32 := L.controlledShiftFull_exact hw hn c scratch hc ht hct 32 (by omega) (by omega)
  simpa only [subTimesC,controlledTimesC,subShiftFull,controlledSubShiftFull,if_true] using
    (((base.2.append s4.2).append s6.1).append s10.2).append s32.2

private theorem certified_away (p : Program) (hp : L.Certified p) :
    c∉ECDSAAdd.wires p ∧ scratch∉ECDSAAdd.wires p := by
  exact ⟨fun h => hc (List.mem_toFinset.mp (hp.2 h)),
    fun h => ht (List.mem_toFinset.mp (hp.2 h))⟩

theorem controlledBranchA_exact :
    ExactControl c scratch L.branchA (L.controlledBranchA c scratch) := by
  have prod := L.square128_certified hw hn L.core.low (L.core.low_length hw.core)
    (by intro q; exact (List.take_sublist 128 L.core.y).count_le q)
  have away := L.certified_away hw hn c scratch hc ht hct _ prod.1
  have sub := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.productTake256_view hw)
  have rot := L.controlledRotate128_exact hw hn c scratch hc ht hct false
  have inner := sub.2.append rot.1
  have result := ExactControl.sandwich prod.1.1 away.1 away.2 inner
  have clearEq : L.core.square128Clear L.core.low=
      (L.core.square128 L.core.low).reverse := rfl
  simpa only [branchA,controlledBranchA,clearEq,List.append_assoc] using result

theorem controlledBranchB_exact :
    ExactControl c scratch L.branchB (L.controlledBranchB c scratch) := by
  have prod := L.square128_certified hw hn L.core.high (L.core.high_length hw.core)
    (by
      intro q
      exact ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
        ((List.drop_sublist 128 L.core.y).count_le q))
  have away := L.certified_away hw hn c scratch hc ht hct _ prod.1
  have rot := L.controlledRotate128_exact hw hn c scratch hc ht hct false
  have times := L.controlledTimesC_exact hw hn c scratch hc ht hct
  have result := ExactControl.sandwich prod.1.1 away.1 away.2 (rot.1.append times)
  have clearEq : L.core.square128Clear L.core.high=
      (L.core.square128 L.core.high).reverse := rfl
  simpa only [branchB,controlledBranchB,clearEq,List.append_assoc] using result

theorem controlledBranchC_exact :
    ExactControl c scratch L.branchC (L.controlledBranchC c scratch) := by
  have prep := L.sum_certified hw hn
  have sq := L.square129_certified hw hn
  have producer := prep.1.append sq.1
  have away := L.certified_away hw hn c scratch hc ht hct _ producer
  have rot := L.controlledRotate128_exact hw hn c scratch hc ht hct true
  have result := ExactControl.sandwich producer.1 away.1 away.2 rot.2
  have clearEq : L.core.square129Clear=(L.core.square129).reverse := rfl
  simpa only [branchC,controlledBranchC,clearEq,CuccaroStreamedSquareLayout.clearSum,
    List.reverse_append,List.append_assoc] using result

/-- Whole-state equality with the previous all-gates-controlled square, using
the same reusable scratch wire and no additional qubit sites. -/
theorem controlledProgram_exact :
    ExactControl c scratch L.program (L.controlledProgram c scratch) := by
  have a := L.controlledBranchA_exact hw hn c scratch hc ht hct
  have b := L.controlledBranchB_exact hw hn c scratch hc ht hct
  have z := L.controlledBranchC_exact hw hn c scratch hc ht hct
  exact (a.append b).append z

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

theorem controlledSource_counts (src : List Wire) (hs : src.length=256) :
    (toffoliCount (L.controlledAddSource c scratch src)=15857 ∧
      measurementCount (L.controlledAddSource c scratch src)=0) ∧
    (toffoliCount (L.controlledSubSource c scratch src)=17909 ∧
      measurementCount (L.controlledSubSource c scratch src)=0) :=
  controlledNormalizedMod_secp256k1_counts c scratch (L.source src)
    (L.source_widths hw src hs)

theorem controlledCMinusOne_counts (src : List Wire)
    (hs2 : 2≤src.length) (hs : src.length+32≤256) :
    (toffoliCount (L.controlledAddCMinusOne c scratch src)=65480 ∧
      measurementCount (L.controlledAddCMinusOne c scratch src)=0) ∧
    (toffoliCount (L.controlledSubCMinusOne c scratch src)=69584 ∧
      measurementCount (L.controlledSubCMinusOne c scratch src)=0) := by
  have s4 := L.controlledSource_counts hw c scratch _
    (L.shifted_length hw src 4 hs2 (by omega))
  have s6 := L.controlledSource_counts hw c scratch _
    (L.shifted_length hw src 6 hs2 (by omega))
  have s10 := L.controlledSource_counts hw c scratch _
    (L.shifted_length hw src 10 hs2 (by omega))
  have s32 := L.controlledSource_counts hw c scratch _ (L.shifted_length hw src 32 hs2 hs)
  simp [controlledAddCMinusOne,controlledSubCMinusOne,toffoliCount_append,
    measurementCount_append,s4,s6,s10,s32]

theorem controlledRotate128_counts :
    (toffoliCount (L.controlledAddRotate128 c scratch false)=81337 ∧
      measurementCount (L.controlledAddRotate128 c scratch false)=0) ∧
    (toffoliCount (L.controlledSubRotate128 c scratch false)=87493 ∧
      measurementCount (L.controlledSubRotate128 c scratch false)=0) ∧
    (toffoliCount (L.controlledSubRotate128 c scratch true)=105402 ∧
      measurementCount (L.controlledSubRotate128 c scratch true)=0) := by
  have rot := L.controlledSource_counts hw c scratch _ (L.rotated128_view hw).length
  have terms := L.controlledCMinusOne_counts hw c scratch (L.core.product.drop 128)
    (by simp [hw.core.product]) (by simp [hw.core.product])
  have tail := L.controlledSource_counts hw c scratch _
    (L.shifted_length hw (L.core.product.drop 256) 128 (by simp [hw.core.product])
      (by simp [hw.core.product]))
  simp [controlledAddRotate128,controlledSubRotate128,toffoliCount_append,
    measurementCount_append,rot,terms,tail,toffoliCount,measurementCount]

theorem controlledShiftFull_counts (j : Nat) (hj2 : 2≤j) (hj : j≤224) :
    (toffoliCount (L.controlledAddShiftFull c scratch j)=81337 ∧
      measurementCount (L.controlledAddShiftFull c scratch j)=0) ∧
    (toffoliCount (L.controlledSubShiftFull c scratch j)=87493 ∧
      measurementCount (L.controlledSubShiftFull c scratch j)=0) := by
  have rot := L.controlledSource_counts hw c scratch _ (L.rotateFull_view hw j (by omega)).length
  have len : ((L.core.product.take 256).drop (256-j)).length=j := by
    simp [hw.core.product]
    omega
  have terms := L.controlledCMinusOne_counts hw c scratch
    ((L.core.product.take 256).drop (256-j))
    (by rw [len]; exact hj2) (by rw [len]; omega)
  have jnz : j≠0 := by omega
  simp [controlledAddShiftFull,controlledSubShiftFull,jnz,toffoliCount_append,
    measurementCount_append,rot,terms]

theorem controlledTimesC_counts :
    toffoliCount (L.controlledTimesC c scratch)=361725 ∧
    measurementCount (L.controlledTimesC c scratch)=0 := by
  have base := L.controlledSource_counts hw c scratch _ (L.productTake256_view hw).length
  have s4 := L.controlledShiftFull_counts hw c scratch 4 (by omega) (by omega)
  have s6 := L.controlledShiftFull_counts hw c scratch 6 (by omega) (by omega)
  have s10 := L.controlledShiftFull_counts hw c scratch 10 (by omega) (by omega)
  have s32 := L.controlledShiftFull_counts hw c scratch 32 (by omega) (by omega)
  have zeroEq : L.controlledSubShiftFull c scratch 0=
      L.controlledSubSource c scratch (L.core.product.take 256) := rfl
  simp [controlledTimesC,zeroEq,toffoliCount_append,
    measurementCount_append,base,s4,s6,s10,s32]

theorem controlledProgram_counts :
    toffoliCount (L.controlledProgram c scratch)=749338 ∧
      measurementCount (L.controlledProgram c scratch)=0 := by
  have lo := L.core.square128_counts hw.core L.core.low (L.core.low_length hw.core)
  have hi := L.core.square128_counts hw.core L.core.high (L.core.high_length hw.core)
  have sq := L.core.square129_counts hw.core
  have prep := L.core.sum_counts hw.core
  have base := L.controlledSource_counts hw c scratch _ (L.productTake256_view hw).length
  have rot := L.controlledRotate128_counts hw c scratch
  have times := L.controlledTimesC_counts hw c scratch
  simp [controlledProgram,controlledBranchA,controlledBranchB,controlledBranchC,
    toffoliCount_append,measurementCount_append,lo,hi,sq,prep,base,rot,times]

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

def pointStreamedSquare (L : ControlledPointLayout) : Program :=
  L.dialogStreamedSquareWide.controlledProgram L.core.generic (L.core.poolWire 775)

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

theorem pointStreamedSquare_exact_control (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    ExactControl L.core.generic (L.core.poolWire 775) L.dialogStreamedSquareWide.program
      (pointStreamedSquare L) := by
  have nd := L.streamedSquare_control_nodup hw hn
  have n0 := List.nodup_cons.mp nd
  have n1 := List.nodup_cons.mp n0.2
  exact L.dialogStreamedSquareWide.controlledProgram_exact
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn)
    L.core.generic (L.core.poolWire 775)
    (fun h => n0.1 (List.mem_cons_of_mem _ h)) n1.1
    (fun h => n0.1 (by simp [h]))

theorem pointStreamedSquare_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointStreamedSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointStreamedSquare L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (pointStreamedSquare L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have support := K.program_certified hwK ndK
  have nd := L.streamedSquare_control_nodup hw hn
  have n0 := List.nodup_cons.mp nd
  have n1 := List.nodup_cons.mp n0.2
  have controlAway : L.core.generic∉wires K.program := by
    intro h
    exact n0.1 (List.mem_cons_of_mem _ (List.mem_toFinset.mp (support.2 h)))
  have scratchAway : L.core.poolWire 775∉wires K.program := by
    intro h
    exact n1.1 (List.mem_toFinset.mp (support.2 h))
  have scratchIn : L.core.poolWire 775∈L.dialogPool := by
    have h : L.core.poolWire 775∈L.dialogPool.take 775++[L.core.poolWire 775] := by simp
    rw [L.dialogBit_prefix hw 775 (by omega)] at h
    exact List.mem_of_mem_take h
  have scratchZero : s.basis (L.core.poolWire 775)=false :=
    (regValue_zero _ _).mp hc _ scratchIn
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have kernel := K.program_square_correct hwK ndK Y X (by simpa only [hp] using hX)
    s m hy hx prod0 sum0 clean
  have guard := (pointStreamedSquare_exact_control L hw hn).execute s m scratchZero
  change run (pointStreamedSquare L) m s=_ at guard
  rw [guard,hb]
  cases B
  · simp [hx,Nat.mod_eq_of_lt hX]
  · simpa only [if_true,hp,pow_two] using kernel

def pointStreamedSquareCost (_L : ControlledPointLayout) : Nat := 749338

theorem pointStreamedSquare_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (pointStreamedSquare L)=pointStreamedSquareCost L ∧
    measurementCount (pointStreamedSquare L)=0 :=
  L.dialogStreamedSquareWide.controlledProgram_counts
    (L.dialogStreamedSquareWide_widths hw) L.core.generic (L.core.poolWire 775)

theorem pointStreamedSquare_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (pointStreamedSquare L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
  have supp := (L.dialogStreamedSquareWide.program_certified
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn)).2
  have embed : L.dialogStreamedSquareWide.wires.toFinset⊆
      (L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    intro q hq
    simp only [List.mem_toFinset,List.mem_append] at hq ⊢
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro v hv
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hv
      exact List.mem_of_mem_take hv
    tauto
  have scratch : L.core.poolWire 775∈L.dialogPool.take 776 := by
    have h : L.core.poolWire 775∈L.dialogPool.take 775++[L.core.poolWire 775] := by simp
    simpa only [L.dialogBit_prefix hw 775 (by omega)] using h
  intro q hq
  have h := (pointStreamedSquare_exact_control L hw hn).support hq
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with (rfl|rfl)|h
  · simp
  · simp [scratch]
  · have h' := embed (supp h)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h' ⊢
    tauto

def ControlledPointLayout.streamedSquareStageSites (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags++L.dialogPool.take 776

theorem pointStreamedSquare_stage_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (pointStreamedSquare L)⊆L.streamedSquareStageSites.toFinset := by
  intro q hq
  have h := pointStreamedSquare_support L hw hn hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
  simp only [List.mem_toFinset,streamedSquareStageSites,PointAddLayout.pointWires,
    inPlaceFlags,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
  tauto

theorem pointStreamedSquare_stage_sites (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    L.streamedSquareStageSites.Nodup ∧ L.streamedSquareStageSites.length=1297 ∧
      qubitCount (pointStreamedSquare L)≤1297 := by
  have nd : L.streamedSquareStageSites.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have ht := (List.take_sublist 776 L.dialogPool).count_le q
    simp only [streamedSquareStageSites,dialogUsedWires,List.count_append] at h ⊢
    omega
  have len : L.streamedSquareStageSites.length=1297 := by
    simp only [streamedSquareStageSites,PointAddLayout.pointWires,inPlaceFlags,
      List.length_cons,List.length_append,List.length_nil,List.length_take,
      show L.point.x.length=256 from hw.inputX,
      show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw]
    norm_num
  refine ⟨nd,len,?_⟩
  rw [qubitCount]
  calc
    _ ≤ L.streamedSquareStageSites.toFinset.card :=
      Finset.card_le_card (pointStreamedSquare_stage_support L hw hn)
    _ = 1297 := by rw [List.toFinset_card_of_nodup nd,len]

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

/-- The resident point/control/classification registers and all workspace
fit in 1,297 distinct allocated sites, giving a safe peak-live ceiling. -/
theorem pointMeasuredSquareCandidate_stage_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (pointMeasuredSquareCandidate L)⊆L.streamedSquareStageSites.toFinset := by
  intro q hq
  have h := pointMeasuredSquareCandidate_support L hw hn hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  simp only [ControlledPointLayout.streamedSquareStageSites,PointAddLayout.pointWires,
    ControlledPointLayout.inPlaceFlags,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false]
  tauto

theorem pointMeasuredSquareCandidate_stage_sites (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    L.streamedSquareStageSites.Nodup ∧ L.streamedSquareStageSites.length=1297 ∧
      qubitCount (pointMeasuredSquareCandidate L)≤1297 := by
  have sites := pointStreamedSquare_stage_sites L hw hn
  refine ⟨sites.1,sites.2.1,?_⟩
  rw [qubitCount]
  calc
    _ ≤ L.streamedSquareStageSites.toFinset.card :=
      Finset.card_le_card (pointMeasuredSquareCandidate_stage_support L hw hn)
    _ = 1297 := by rw [List.toFinset_card_of_nodup sites.1,sites.2.1]

theorem pointMeasuredSquareCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointMeasuredSquareCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointMeasuredSquareCandidate L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (pointMeasuredSquareCandidate L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have kernel := K.measuredProgram_correct hwK L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean
  simpa only [pointMeasuredSquareCandidate,hb,hp,pow_two] using kernel

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

theorem sharedPool_length (L : ControlledPointLayout) : (sharedPool L).length=1378 := by
  simp only [sharedPool,List.length_append,wireBlock_length]

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

theorem pi0_injective : Function.Injective pi0 := pi0.injective
theorem pi_injective (j : Nat) : Function.Injective (pi j) := (pi j).injective

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

/-- Every group actually packed in a prefix has a proved-zero fourth site.
The proof uses codec legality and instruction disjointness, never sampled bits. -/
theorem compressedPrefix_zero_slots (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (s : State) (legal : ∀ j, j+3 ≤ 512 →
      (s.basis (compressedHistoryMap w j 0) && s.basis (compressedHistoryMap w j 1))=false ∧
      (s.basis (compressedHistoryMap w j 2) && s.basis (compressedHistoryMap w j 3))=false ∧
      (s.basis (compressedHistoryMap w j 4) && s.basis (compressedHistoryMap w j 5))=false)
    (n : Nat) (hn512 : n ≤ 512) (m : List Bool)
    (start : Nat) (hmod : start%3=0) (hbound : start+4 ≤ n) :
    (run (compressedEncodePrefix w n) m s).basis (w (1028+start+1))=false := by
  induction n generalizing m start with
  | zero => omega
  | succ n ih =>
    have hi : n < 512 := by omega
    cases due : compressedPackDue n
    · have before : start+4 ≤ n := by
        by_contra h
        have e : n=start+3 := by omega
        have yes : compressedPackDue n=true := by
          simp [compressedPackDue,e,hmod]
        rw [yes] at due
        contradiction
      have old := ih (by omega) (m.take (measurementCount (compressedEncodePrefix w n)))
        start hmod before
      simp only [compressedEncodePrefix,run_append,compressedPackAfter,due,
        Bool.false_eq_true,if_false]
      simpa only [run] using old
    · have ndue := compressedPackDue_true n due
      let before := run (compressedEncodePrefix w n)
        (m.take (measurementCount (compressedEncodePrefix w n))) s
      rw [compressedEncodePrefix,run_append]
      simp only [compressedPackAfter,due,if_true]
      change (run (compressedHistoryEncode w (n-3))
        (m.drop (measurementCount (compressedEncodePrefix w n))) before).basis _=false
      by_cases same : start=n-3
      · have reads (j : Fin 6) : before.basis (compressedHistoryMap w (n-3) j)=
            s.basis (compressedHistoryMap w (n-3) j) :=
          compressedPrefix_raw_next w hn hlo n hi due s _ j
        have domain := legal (n-3) (by omega)
        have actualLegal :
            (before.basis (compressedHistoryMap w (n-3) 0) && before.basis (compressedHistoryMap w (n-3) 1))=false ∧
            (before.basis (compressedHistoryMap w (n-3) 2) && before.basis (compressedHistoryMap w (n-3) 3))=false ∧
            (before.basis (compressedHistoryMap w (n-3) 4) && before.basis (compressedHistoryMap w (n-3) 5))=false := by
          rw [reads 0,reads 1,reads 2,reads 3,reads 4,reads 5]
          exact domain
        have codec := TranscriptCodec3.placement_correct (compressedHistoryMap w (n-3))
          (compressedHistoryMap_injective w hn (n-3) (by omega))
          (compressedHistoryMap_above w (n-3) (by omega) hlo) before
          (m.drop (measurementCount (compressedEncodePrefix w n))) actualLegal
        simpa only [same,compressedHistoryEncode,compressedHistoryMap,compressedHistoryId,
          Nat.reduceMod,Nat.reduceDiv,Nat.reduceEqDiff,if_false] using codec.2.1
      · have sep : start+3 ≤ n-3 := by omega
        have old := ih (by omega) (m.take (measurementCount (compressedEncodePrefix w n)))
          start hmod (by omega)
        have disjoint := compressedHistory_windows_disjoint w hn hlo start (n-3)
          (by omega) (by omega) sep
        have site : w (1028+start+1)∈wires (compressedHistoryEncode w start) := by
          simpa only [compressedHistoryMap,compressedHistoryId,Nat.reduceMod,Nat.reduceDiv,
            Nat.reduceEqDiff,if_false] using compressedHistory_site_mem w hn hlo start (by omega) 3
        have keep := run_preserves_outside (compressedHistoryEncode w (n-3))
          (m.drop (measurementCount (compressedEncodePrefix w n))) before (w (1028+start+1))
          (fun h => Finset.disjoint_left.mp disjoint site h)
        exact keep.trans old

/-- The complete compact integer caller supplies legality for all170 groups. -/
theorem compressedCompactStage_512_zero_slots (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1) (s : State)
    (h : CompressedCompactStage w x p 512 s.basis)
    (j : Nat) (hj : j < 170) : s.basis (w (1029+3*j))=false := by
  obtain ⟨raw,hraw,bits⟩ := h
  have legal (start : Nat) (hs : start+3 ≤ 512) :=
    compressedCompactHistory_legal w hn x p 512 start hp0 hpo hs (by decide) raw.basis hraw
  have zero := compressedPrefix_zero_slots w hn hlo raw legal 512 (by decide) []
    (3*j) (by omega) (by omega)
  rw [bits]
  have index : 1028+3*j+1=1029+3*j := by omega
  simpa only [index] using zero

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedAllocationBoundary.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedAllocation

private theorem region_W (q : Nat) (h : workRegion q) :
    ∃j, j < 170 ∧ q=W j := by
  refine ⟨q-515,?_,?_⟩
  · unfold workRegion at h; omega
  · unfold workRegion at h; unfold W; omega

private theorem region_H (q : Nat) (h : holeRegion q) :
    ∃j, j < 170 ∧ q=H j := by
  refine ⟨(q-1029)/3,?_,?_⟩
  · unfold holeRegion at h; omega
  · unfold holeRegion at h; unfold H; omega

/-- The accepted compressed integer assertion supplies every hole zero;
the actual existing caller field-work invariant supplies every work zero.
There is no additional assumed all-zero allocation-bank oracle. -/
theorem caller_zero_boundary (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (s : State) (hstage : CompressedCompactStage w x p 512 s.basis)
    (hw : regValue (skywalkSharedField w).work s.basis=0) :
    ∀q,zeroRegion q → (pullState w s).basis q=false := by
  intro q hq
  rcases hq with hq|hq
  · obtain ⟨j,hj,rfl⟩ := region_W q hq
    exact OffsetCleanupBorrowedCaller.maskBit_zero w s.basis hw (W j)
      (by unfold W; omega) (by unfold W; omega)
  · obtain ⟨j,hj,rfl⟩ := region_H q hq
    have zero := compressedCompactStage_512_zero_slots w hn hlo x p hp0 hpo s hstage j hj
    change s.basis (w (H j))=false
    have index : H j=1029+3*j := by unfold H; omega
    rw [index]
    exact zero

private theorem perm_preserves_region (e : Equiv.Perm Nat)
    (fix : ∀q,¬zeroRegion q → e q=q) (q : Nat) (hq : zeroRegion q) : zeroRegion (e q) := by
  by_contra bad
  have eq : e q=q := e.injective (fix (e q) bad)
  exact bad (eq.symm ▸ hq)

/-- Arbitrary phase and all live data are preserved: the entire placement
permutation acts only on sites supplied zero by the boundary certificate. -/
theorem pull_zero_permutation (e : Equiv.Perm Nat) (s : State)
    (fix : ∀q,¬zeroRegion q → e q=q)
    (hz : ∀q,zeroRegion q → s.basis q=false) : pullState e s=s := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq : zeroRegion q
    · exact (hz (e q) (perm_preserves_region e fix q hq)).trans (hz q hq).symm
    · change s.basis (e q)=s.basis q
      rw [fix q hq]

theorem pi0_boundary (s : State) (hz : ∀q,zeroRegion q → s.basis q=false) :
    pullState pi0 s=s := pull_zero_permutation pi0 s pi0_outside hz

theorem pi_boundary (j : Nat) (hj : j < 170) (s : State)
    (hz : ∀q,zeroRegion q → s.basis q=false) : pullState (pi j) s=s :=
  pull_zero_permutation (pi j) s (pi_outside j · hj ·) hz

private theorem encode_other_zero_role (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (j : Nat) (hj : j < 170) (q : Nat)
    (hq : zeroRegion q) (hne : q ≠ H j) (s : State) (m : List Bool) :
    (run (compressedHistoryEncode w (3*j)) m s).basis (w q)=s.basis (w q) := by
  apply run_preserves_outside
  intro touch
  obtain ⟨index,eq⟩ := compressedHistory_gate_mem w hn hlo (3*j) (by omega)
    _ (Or.inl rfl) (w q) touch
  have qb : q < 1798 := by unfold zeroRegion workRegion holeRegion at hq; omega
  have same := skywalkPool_index_inj w hn q (compressedHistoryId (3*j) index)
    qb (compressedHistoryId_bound _ (by omega) index) eq
  have ix := index.isLt
  unfold zeroRegion workRegion holeRegion at hq
  unfold H at hne
  unfold compressedHistoryId at same
  split_ifs at same <;> omega

/-- The measured current encoder re-establishes all zero allocation roles.
Other packed holes and clean field work are transported by actual support;
only the current hole zero is supplied anew by the codec correctness proof. -/
theorem reencode_zero_boundary (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (j : Nat) (hj : j < 170) (s : State) (m : List Bool)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (other : ∀k, k < 170 → k ≠ j → s.basis (w (H k))=false)
    (legal : (s.basis (compressedHistoryMap w (3*j) 0) && s.basis (compressedHistoryMap w (3*j) 1))=false ∧
      (s.basis (compressedHistoryMap w (3*j) 2) && s.basis (compressedHistoryMap w (3*j) 3))=false ∧
      (s.basis (compressedHistoryMap w (3*j) 4) && s.basis (compressedHistoryMap w (3*j) 5))=false) :
    ∀q,zeroRegion q →
      (run (compressedHistoryEncode w (3*j)) m s).basis (w q)=false := by
  have codec := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s m legal
  intro q hq
  by_cases current : q=H j
  · subst q
    have hz := codec.2.1
    change (run (compressedHistoryEncode w (3*j)) m s).basis (w (1028+3*j+1))=false at hz
    have index : H j=1028+3*j+1 := rfl
    rw [index]
    exact hz
  · have keep := encode_other_zero_role w hn hlo j hj q hq current s m
    rw [keep]
    rcases hq with hq|hq
    · obtain ⟨k,hk,rfl⟩ := region_W q hq
      exact OffsetCleanupBorrowedCaller.maskBit_zero w s.basis hw (W k)
        (by unfold W; omega) (by unfold W; omega)
    · obtain ⟨k,hk,rfl⟩ := region_H q hq
      exact other k hk (by intro same; subst k; exact current rfl)

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

private theorem slim_support_sub (L : BalancedCleanupOffset.Layout) (hw : L.Widths) :
    wires (BalancedCleanupOffsetSlim.program L)⊆wires (BalancedCleanupOffset.program L) := by
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have carry : L.carry.length=256 := hw.1.2.2
  have offset : L.offsetCarry.length=256 := hw.2
  have subset := BalancedCleanupOffsetSlim.chain_support (BalancedCleanupOffset.offsetBits L)
    L.y L.r L.offsetCarry L.carry L.one L.cout L.parity
    (by simp [BalancedCleanupOffset.offsetBits,width.2.1])
    (by omega) (by omega) (by omega)
  rw [BalancedCleanupOffset.program_sandwich]
  simp only [BalancedCleanupOffsetSlim.program,wires_append,wires_reverse]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _) subset) (Finset.Subset.refl _)

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

/-- Counts belong to these emitted packet programs. They do not assert a
complete compressed arithmetic caller or any reduced physical allocation. -/
theorem codecGroups_counts {α : Type} {cost : Nat} (w : Nat → Wire) (cell : α → Program)
    (hc : ∀ a, toffoliCount (cell a)=cost ∧ measurementCount (cell a)=1025)
    (start : Nat) (ls : List α) :
    toffoliCount (codecGroupForward w cell start ls)=cost*ls.length+7*(ls.length/3) ∧
    measurementCount (codecGroupForward w cell start ls)=1025*ls.length+ls.length/3 ∧
    toffoliCount (codecGroupBackward w cell start ls)=cost*ls.length+7*(ls.length/3) ∧
    measurementCount (codecGroupBackward w cell start ls)=1025*ls.length+ls.length/3 := by
  suffices aux : ∀ n start (ls : List α), ls.length=n →
      toffoliCount (codecGroupForward w cell start ls)=cost*ls.length+7*(ls.length/3) ∧
      measurementCount (codecGroupForward w cell start ls)=1025*ls.length+ls.length/3 ∧
      toffoliCount (codecGroupBackward w cell start ls)=cost*ls.length+7*(ls.length/3) ∧
      measurementCount (codecGroupBackward w cell start ls)=1025*ls.length+ls.length/3 by
    exact aux ls.length start ls rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro start ls hlen
    cases ls with
    | nil => simp [codecGroupForward,codecGroupBackward,toffoliCount,measurementCount]
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [codecGroupForward,codecGroupBackward,(hc a).1,(hc a).2,List.length_cons,
          List.length_nil]
        norm_num
      | cons b rest =>
        cases rest with
        | nil =>
          simp only [codecGroupForward,codecGroupBackward,toffoliCount_append,
            measurementCount_append,(hc a).1,(hc a).2,(hc b).1,(hc b).2,
            List.length_cons,List.length_nil]
          norm_num
          omega
        | cons c tail =>
          have ht : tail.length < n := by simp only [List.length_cons] at hlen; omega
          have next := ih tail.length ht (start+3) tail rfl
          have codec := compressedHistory_counts w start
          simp only [codecGroupForward,codecGroupBackward,toffoliCount_append,
            measurementCount_append,codec.1,codec.2.1,codec.2.2.1,codec.2.2.2,
            (hc a).1,(hc a).2,(hc b).1,(hc b).2,(hc c).1,(hc c).2,
            next.1,next.2.1,next.2.2.1,next.2.2.2,List.length_cons]
          simp only [Nat.mul_succ]
          and_intros <;> omega

theorem codecGroups_512_counts {α : Type} {cost : Nat} (w : Nat → Wire) (cell : α → Program)
    (hc : ∀ a, toffoliCount (cell a)=cost ∧ measurementCount (cell a)=1025)
    (ls : List α) (hl : ls.length=512) :
    toffoliCount (codecGroupForward w cell 0 ls)=cost*512+1190 ∧
    measurementCount (codecGroupForward w cell 0 ls)=524970 ∧
    toffoliCount (codecGroupBackward w cell 0 ls)=cost*512+1190 ∧
    measurementCount (codecGroupBackward w cell 0 ls)=524970 := by
  have h := codecGroups_counts w cell hc 0 ls
  simpa only [hl,Nat.reduceMul,Nat.reduceDiv,Nat.reduceAdd] using h

/-- Actual mixed-control forward field cells wrapped in three-letter codecs.
Boundary conversions and integer/control wrappers remain separate. -/
def compressedFieldForwardGroups (w : Nat → Wire) (b sign effS : Wire) : Program :=
  codecGroupForward w (fun l : MixedTranscriptLetter =>
    OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2) 0
    (mixedTranscriptTape w)

/-- Actual independently measured inverse field cells, not reversed MX gates. -/
def compressedFieldBackwardGroups (w : Nat → Wire) (b sign effS : Wire) : Program :=
  codecGroupBackward w (fun l : MixedTranscriptLetter =>
    OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2) 0
    (mixedTranscriptTape w)

theorem compressedFieldGroups_counts (w : Nat → Wire) (b sign effS : Wire)
    (hsw : (effS::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup) :
    toffoliCount (compressedFieldForwardGroups w b sign effS)=656550 ∧
    measurementCount (compressedFieldForwardGroups w b sign effS)=524970 ∧
    toffoliCount (compressedFieldBackwardGroups w b sign effS)=657062 ∧
    measurementCount (compressedFieldBackwardGroups w b sign effS)=524970 := by
  have fw := codecGroups_512_counts w
    (fun l : MixedTranscriptLetter => OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2)
    (fun l => OffsetBorrowedCanonical.cell_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hsw)
    (mixedTranscriptTape w) (mixedTranscriptTape_length w)
  have rv := codecGroups_512_counts w
    (fun l : MixedTranscriptLetter => OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2)
    (fun l => OffsetBorrowedInverseCanonical.cell_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hsw)
    (mixedTranscriptTape w) (mixedTranscriptTape_length w)
  exact ⟨fw.1,fw.2.1,rv.2.2.1,rv.2.2.2⟩

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

/-- The certificate uses the accepted actual instruction-derived cell
support, rather than an assumed semantic frame or declared-list oracle. -/
theorem current_cells_avoid_omitted (j : Nat) (hj : j < 170)
    (g swap : Nat) (hg : g∈packetSites j) (hs : swap∈packetSites j) (ig is : Bool) :
    (∀q∈wires (renameProgram (pi j)
      (OffsetBorrowedCanonical.cell id 2400 g swap 2409 2410 ig is)),¬omitted q) ∧
    (∀q∈wires (renameProgram (pi j)
      (OffsetBorrowedInverseCanonical.cell id 2400 g swap 2409 2410 ig is)),¬omitted q) := by
  have actual := CompressedFieldSupport.cells_active id 2400 g swap 2409 2410 ig is
    (groupInventory j).toFinset
    (by intro q hq; simp only [groupInventory,List.mem_toFinset,List.mem_append];
        exact Or.inl (Or.inl (List.mem_toFinset.mp hq)))
    (by simp [groupInventory]) (by simp [groupInventory,hg])
    (by simp [groupInventory,hs]) (by simp [groupInventory])
  constructor
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp hq
    exact inventory_safe j old hj (List.mem_toFinset.mp (actual.1 hold))
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp hq
    exact inventory_safe j old hj (List.mem_toFinset.mp (actual.2 hold))

theorem current_work_record_disjoint (j k : Nat) (hj : j < 170) (hk : k < 170)
    (q : Nat) (h : q∈packetSites j) : pi j (W k) ≠ pi j q := by
  apply (pi j).injective.ne
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold W H at *
  omega

end ECDSAAdd.Arithmetic.CompressedAllocation
end

-- source: ECDSAAdd/Arithmetic/CompressedAllocationSwitch.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.CompressedAllocation

private theorem inverse_outside (e : Equiv.Perm Nat)
    (fix : ∀ q, ¬zeroRegion q → e q=q) (q : Nat) (hq : ¬zeroRegion q) :
    e.symm q=q := by
  calc
    e.symm q = e.symm (e q) := by rw [fix q hq]
    _ = q := e.symm_apply_apply q

/-- Switch two public placements only at a proved-zero allocation boundary.
The logical State, including phase and every live coordinate, is identical.
No swap instruction or measurement is inserted into the actual circuit. -/
theorem switch_zero_placements (old next : Equiv.Perm Nat) (actual logical : State)
    (oldFix : ∀ q, ¬zeroRegion q → old q=q)
    (nextFix : ∀ q, ¬zeroRegion q → next q=q)
    (hmap : pullState old actual=logical)
    (hz : ∀ q, zeroRegion q → logical.basis q=false) :
    pullState next actual=logical := by
  have original : pullState old.symm logical=actual := by
    rw [←hmap]
    apply State.extensionality
    · rfl
    · funext q
      simp only [pullState,old.apply_symm_apply]
  let delta := next.trans old.symm
  have fix : ∀ q, ¬zeroRegion q → delta q=q := by
    intro q hq
    change old.symm (next q)=q
    rw [nextFix q hq,inverse_outside old oldFix q hq]
  have same := pull_zero_permutation delta logical fix hz
  rw [←original]
  change pullState delta logical=logical
  exact same

/-- The next renamed block executes the same logical instructions and every
measurement correction under its new injective placement. -/
theorem run_switch_zero_placements (old next : Equiv.Perm Nat)
    (actual logical : State) (program : Program) (m : List Bool)
    (oldFix : ∀ q, ¬zeroRegion q → old q=q)
    (nextFix : ∀ q, ¬zeroRegion q → next q=q)
    (hmap : pullState old actual=logical)
    (hz : ∀ q, zeroRegion q → logical.basis q=false) :
    pullState next (run (renameProgram next program) m actual)=run program m logical := by
  rw [run_rename next next.injective,
    switch_zero_placements old next actual logical oldFix nextFix hmap hz]

theorem run_switch_packet_placements (a j : Nat) (ha : a < 170) (hj : j < 170)
    (actual logical : State) (program : Program) (m : List Bool)
    (hmap : pullState (pi a) actual=logical)
    (hz : ∀ q, zeroRegion q → logical.basis q=false) :
    pullState (pi j) (run (renameProgram (pi j) program) m actual)=run program m logical :=
  run_switch_zero_placements (pi a) (pi j) actual logical program m
    (fun q hq => pi_outside a q ha hq) (fun q hq => pi_outside j q hj hq) hmap hz

end ECDSAAdd.Arithmetic.CompressedAllocation
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkForward.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- A ghost raw state supplies the old exact integer invariant. Encoding is
an actual circuit program; the assertion equates the complete caller basis.
Incoming phase is unrestricted and is preserved separately by the Triple. -/
def CompressedIntegerStage (w : Nat → Wire) (x p i : Nat) (bits : BasisState) : Prop :=
  ∃ raw : State,
    SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis ∧
    bits=(run (compressedEncodePrefix w i) [] raw).basis

attribute [local irreducible] run compressedEncodePrefix compressedSkywalkLoop
attribute [local irreducible] narrowSkywalkScheduledTick compressedHistoryEncode

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem compressedIntegerStage_zero (w : Nat → Wire) (x p : Nat) (s : State)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    CompressedIntegerStage w x p 0 s.basis := by
  refine ⟨s,h,?_⟩
  simp only [compressedEncodePrefix,run]

theorem compressedIntegerStage_step (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hi : i < 512) :
    Triple (CompressedIntegerStage w x p i)
      (narrowSkywalkScheduledTick w i ++ compressedPackAfter w i)
      (CompressedIntegerStage w x p (i+1)) := by
  intro s m hs
  obtain ⟨raw,hraw,hbits⟩ := hs
  let tick := narrowSkywalkScheduledTick w i
  let mt := m.take (measurementCount tick)
  let me := m.drop (measurementCount tick)
  let actual := run tick mt s
  let next := run tick [] raw
  have step := narrowSkywalkRoutedStage_step w hn x p i hp0 hx0 hpo hp hx hc hi
  have hnxt := step raw [] hraw
  have hmt := step raw mt hraw
  have hd := (compressedPrefix_disjoint_tick w hn hlo i i (Nat.le_refl i) hi).1
  have read : ∀ q∈wires tick,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    apply run_preserves_outside
    exact fun he => Finset.disjoint_left.mp hd he hq
  have hl := run_local_increment tick s raw mt read
  have hphase : actual.phase=s.phase := by
    apply xor_neutral
    have hh := hl.1
    rw [hmt.1] at hh
    simpa only [Bool.xor_self] using hh
  have hcomm := run_disjoint_commute (compressedEncodePrefix w i) tick hd [] [] raw
  have hb0 := run_basis_records tick s (run (compressedEncodePrefix w i) [] raw) mt [] hbits
  have hb : actual.basis=(run (compressedEncodePrefix w i) [] next).basis :=
    hb0.trans (congrArg State.basis hcomm.symm)
  have hpackphase : (run (compressedPackAfter w i) me actual).phase=actual.phase := by
    cases he : compressedPackDue i
    · simp only [compressedPackAfter,he,Bool.false_eq_true,if_false,run]
    · have h3 := compressedPackDue_true i he
      have same (j : Fin 6) : actual.basis (compressedHistoryMap w (i-3) j)=
          next.basis (compressedHistoryMap w (i-3) j) := by
        rw [hb]
        exact compressedPrefix_raw_next w hn hlo i hi he next [] j
      have legal := compressedHistoryStage_legal w x p (i+1) (i-3) hp0 hpo (by omega) next.basis hnxt.2
      have actualLegal :
          (actual.basis (compressedHistoryMap w (i-3) 0) && actual.basis (compressedHistoryMap w (i-3) 1))=false ∧
          (actual.basis (compressedHistoryMap w (i-3) 2) && actual.basis (compressedHistoryMap w (i-3) 3))=false ∧
          (actual.basis (compressedHistoryMap w (i-3) 4) && actual.basis (compressedHistoryMap w (i-3) 5))=false := by
        rw [same 0,same 1,same 2,same 3,same 4,same 5]
        exact legal
      have cp := TranscriptCodec3.placement_correct (compressedHistoryMap w (i-3))
        (compressedHistoryMap_injective w hn (i-3) (by omega))
        (compressedHistoryMap_above w (i-3) (by omega) hlo) actual me actualLegal
      simpa only [compressedPackAfter,he,if_true,compressedHistoryEncode] using cp.1
  have hpackbits := run_basis_records (compressedPackAfter w i) actual
    (run (compressedEncodePrefix w i) [] next) me [] hb
  have hbnext : (run (compressedPackAfter w i) me actual).basis=
      (run (compressedEncodePrefix w (i+1)) [] next).basis := by
    rw [compressedEncodePrefix,run_append]
    simp only [List.take_nil,List.drop_nil]
    exact hpackbits
  rw [run_append]
  exact ⟨hpackphase.trans hphase,⟨next,hnxt.2,hbnext⟩⟩

/-- Complete forward composition for arbitrary records, including phase.
This theorem retains the exact original divisor and all 512 integer steps. -/
theorem compressedSkywalkLoop_spec (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p i n : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hi : i+n ≤ 512) :
    Triple (CompressedIntegerStage w x p i) (compressedSkywalkLoop w i n)
      (CompressedIntegerStage w x p (i+n)) := by
  induction n generalizing i with
  | zero =>
    rw [compressedSkywalkLoop,Nat.add_zero]
    intro s m h
    simpa only [run] using And.intro (rfl : s.phase=s.phase) h
  | succ n ih =>
    have hstep := compressedIntegerStage_step w hn hlo x p i hp0 hx0 hpo hp hx hc (by omega)
    have htail := ih (i+1) (by omega)
    have hall := hstep.seq htail
    have hindex : i+(n+1)=(i+1)+n := by omega
    rw [compressedSkywalkLoop,hindex]
    simpa only [List.append_assoc] using hall

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkRestore.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] run compressedDecodePrefix compressedEncodePrefix
attribute [local irreducible] compressedSkywalkUnloop narrowSkywalkRoutedUnloop

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

/-- Decoding the model recovers the full raw caller basis, including any
outside coordinate update. The decoder itself preserves incoming phase. -/
theorem compressedIntegerStage_decoded (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p n : Nat) (hp0 : 0 < p) (hpo : p%2=1) (hn512 : n ≤ 512)
    (s : State) (h : CompressedIntegerStage w x p n s.basis) :
    (run (compressedDecodePrefix w n) [] s).phase=s.phase ∧
    SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) n
      (run (compressedDecodePrefix w n) [] s).basis := by
  obtain ⟨raw,hraw,hbasis⟩ := h
  have hi := compressedDecodePrefix_inverse w hn hlo x p n n hp0 hpo
    (Nat.le_refl n) hn512 raw [] [] hraw
  have hb := run_basis_records (compressedDecodePrefix w n) s
    (run (compressedEncodePrefix w n) [] raw) [] [] hbasis
  have he : (run (compressedDecodePrefix w n) [] s).basis=raw.basis :=
    hb.trans (congrArg State.basis hi)
  refine ⟨run_no_measurement_phase _ (compressedDecodePrefix_measurements w n) s [],?_⟩
  rw [he]
  exact hraw

/-- Full 512-step reverse restoration after an external numerator update.
All integer-pool sites return to the initial seed; the current phase is kept. -/
theorem compressedSkywalkUnloop_restore_pool (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (hfinal : CompressedIntegerStage w x p 512 s.basis) :
    (run (compressedSkywalkUnloop w 0 512) m s).phase=s.phase ∧
    ∀ q∈skywalkPoolWires w,(run (compressedSkywalkUnloop w 0 512) m s).basis q=initial.basis q := by
  have hd := compressedIntegerStage_decoded w hn hlo x p 512 hp0 hpo (Nat.le_refl _) s hfinal
  have hr := narrowSkywalkRoutedUnloop_restore_pool w hn x p hp0 hx0 hpo hp hx hc
    initial (run (compressedDecodePrefix w 512) [] s) m hinit hd.2
  rw [compressedSkywalkUnloop_normalize w hn hlo 0 512 (by omega),compressedDecodeRange_zero,run_append,
    compressedDecodePrefix_measurements]
  simp only [List.take_zero,List.drop_zero]
  exact ⟨hr.1.trans hd.1,hr.2⟩

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

/-- The170 reusable mask positions are actual compact terminal tail zeros. -/
theorem compactTerminal_mask_zero (w : Nat → Wire) (r : SkywalkRails.State)
    (s : BasisState) (h : CompactSkywalkStage w r 512 s) (j : Nat) (hj : j < 170) :
    s (w (515+j))=false := by
  have clean := h.2.1
  have released : (compactSkywalkSignPoolA w 512).released=wireBlock w 514 256 := by
    change (wireBlock w 512 258).drop 2=wireBlock w 514 256
    rw [←wireBlock_append w 512 2 256]
    simp [wireBlock_length]
  apply clean
  rw [released]
  exact block_mem w 514 256 (515+j) (by omega) (by omega)

/-- History packing preserves every terminal mask zero, for all records. -/
theorem compressedCompactStage_512_mask_zero (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (s : State) (h : CompressedCompactStage w x p 512 s.basis)
    (j : Nat) (hj : j < 170) : s.basis (w (515+j))=false := by
  obtain ⟨raw,hraw,bits⟩ := h
  have zero := compactTerminal_mask_zero w _ raw.basis hraw j hj
  have support := compressedPrefix_history_support w hn hlo 512 (by decide)
  have away : w (515+j)∉wires (compressedEncodePrefix w 512) := by
    intro hq
    have hhist := List.mem_toFinset.mp (support hq)
    rcases List.mem_append.mp hhist with hq|hq
    all_goals
      obtain ⟨k,hk,he⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hk
      have eq := skywalkPool_index_inj w hn k (515+j) (by omega) (by omega) he
      omega
  rw [bits]
  exact (run_preserves_outside _ [] raw _ away).trans zero

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

/-- The terminal compact predicate determines the physical integer pool.
The reference emitter and its inverse here are both genuinely compact. -/
private theorem terminal_restore (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (hfinal : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s.basis) :
    (run (compactSkywalkReverse w 0 512) m s).phase = s.phase ∧
    ∀ q ∈ skywalkPoolWires w,(run (compactSkywalkReverse w 0 512) m s).basis q = initial.basis q := by
  let start : State := ⟨s.phase,initial.basis⟩
  have forward := compactSkywalkForward_512 w hn x p hp0 hx0 hpo hp hx hc start [] hinit
  have own := (compactSkywalkStage_terminal w hn x p hp0 hx0 hpo hp hx hc s.basis hfinal).2
  have reference := (compactSkywalkStage_terminal w hn x p hp0 hx0 hpo hp hx hc _ forward.2).2
  have inverse := compactSkywalkReverse_512_roundtrip w hn x p hp0 hx0 hpo hp hx hc start [] m hinit
  have bits : ∀ q ∈ (skywalkPoolWires w).toFinset,
      s.basis q = (run (compactSkywalkForward w 0 512) [] start).basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w _ 512 (by decide) _ _ own reference q (List.mem_toFinset.mp hq)
  have agrees := pool_run_agrees (compactSkywalkReverse w 0 512) (skywalkPoolWires w).toFinset
    (compactSkywalkReverse_support w hn 0 512 (by decide)) m s
    (run (compactSkywalkForward w 0 512) [] start) forward.1.symm bits
  rw [inverse] at agrees
  refine ⟨agrees.1,?_⟩
  intro q hq
  exact agrees.2 q (List.mem_toFinset.mpr hq)

/-- Complete512 compact-plus-codec restoration from the encoded terminal
pool. Outsiders may already contain arbitrary coexisting field updates. -/
theorem compressedCompactReverse_restore_pool (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (hfinal : CompressedCompactStage w x p 512 s.basis) :
    (run (compressedCompactReverse w 0 512) m s).phase = s.phase ∧
    ∀ q ∈ skywalkPoolWires w,(run (compressedCompactReverse w 0 512) m s).basis q = initial.basis q := by
  have decoded := compressedCompactStage_decoded w hn hlo x p 512 hp0 hpo (by decide) s hfinal
  have restored := terminal_restore w hn x p hp0 hx0 hpo hp hx hc
    initial (run (compressedDecodePrefix w 512) [] s) m hinit decoded.2
  rw [compressedCompactReverse_normalize w hn hlo 0 512 (by decide),compressedDecodeRange_zero,
    run_append,compressedDecodePrefix_measurements]
  simp only [List.take_zero,List.drop_zero]
  exact ⟨restored.1.trans decoded.1,restored.2⟩

/-- Forward and inverse records are independent, and the full physical
caller State returns, including arbitrary incoming phase and every outsider. -/
theorem compressedCompactReverse_512_roundtrip (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (s : State) (mForward mReverse : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    run (compressedCompactReverse w 0 512) mReverse
      (run (compressedCompactForward w 0 512) mForward s) = s := by
  have forward := compressedCompactForward_512_spec w hn hlo x p hp0 hx0 hpo hp hx hc s mForward hin
  have reverse := compressedCompactReverse_restore_pool w hn hlo x p hp0 hx0 hpo hp hx hc
    s (run (compressedCompactForward w 0 512) mForward s) mReverse hin forward.2
  apply State.extensionality
  · exact reverse.1.trans forward.1
  · funext q
    by_cases hq : q ∈ skywalkPoolWires w
    · exact reverse.2 q hq
    · exact (compressedCompactReverse_frame w hn hlo 0 512 (by decide) _ mReverse q hq).trans
        (compressedCompactForward_frame w hn hlo 0 512 (by decide) s mForward q hq)

/-- A field operation need only retain the actual encoded integer pool and
phase. The emitted compact reverse restores it and keeps all field outsiders. -/
theorem compressedCompactReverse_restore_after_outside (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (s field : State) (mForward mReverse : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis)
    (hphase : field.phase = (run (compressedCompactForward w 0 512) mForward s).phase)
    (hpool : ∀ q ∈ skywalkPoolWires w,
      field.basis q = (run (compressedCompactForward w 0 512) mForward s).basis q) :
    (run (compressedCompactReverse w 0 512) mReverse field).phase = s.phase ∧
    (∀ q ∈ skywalkPoolWires w,(run (compressedCompactReverse w 0 512) mReverse field).basis q = s.basis q) ∧
    (∀ q,q ∉ skywalkPoolWires w → (run (compressedCompactReverse w 0 512) mReverse field).basis q = field.basis q) := by
  have inverse := compressedCompactReverse_512_roundtrip w hn hlo x p hp0 hx0 hpo hp hx hc s mForward mReverse hin
  have agrees := pool_run_agrees (compressedCompactReverse w 0 512) (skywalkPoolWires w).toFinset
    (compressedCompactReverse_support w hn hlo 0 512 (by decide)) mReverse field
    (run (compressedCompactForward w 0 512) mForward s) hphase
    (fun q hq => hpool q (List.mem_toFinset.mp hq))
  rw [inverse] at agrees
  refine ⟨agrees.1,?_,?_⟩
  · intro q hq; exact agrees.2 q (List.mem_toFinset.mpr hq)
  · intro q hq; exact compressedCompactReverse_frame w hn hlo 0 512 (by decide) field mReverse q hq

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

theorem allGroupEncode_records (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n : Nat) (bound : 3*n ≤ 512) (s : State) (m k : List Bool)
    (legal : RawGroupLegal w n s.basis) :
    run (allGroupEncode w n) m s = run (allGroupEncode w n) k s := by
  apply State.extensionality
  · exact (allGroupEncode_phase w hn hlo n bound s m legal).trans
      (allGroupEncode_phase w hn hlo n bound s k legal).symm
  · exact run_basis_records _ s s m k rfl

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

theorem indexed_zip (w : Nat → Wire) (n i : Nat) (cs : List (Bool×Bool)) :
    IndexedLetters w i (((List.range n).map (fun k => (w (i+k),w (1028+i+k)))).zip cs) := by
  induction n generalizing i cs with
  | zero => simp [IndexedLetters]
  | succ n ih =>
    cases cs with
    | nil => simp [IndexedLetters]
    | cons c cs =>
      rw [List.range_succ_eq_map,List.map_cons,List.zip_cons_cons]
      change (w (i+0),w (1028+i+0))=(w i,w (1028+i)) ∧ _
      refine ⟨by simp,?_⟩
      simpa only [List.map_map,Function.comp_def,Nat.succ_eq_add_one,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1) cs

theorem mixedTape_indexed (w : Nat → Wire) : IndexedLetters w 0 (mixedTranscriptTape w) := by
  simpa only [mixedTranscriptTape,skywalkSharedTape,Nat.zero_add] using
    indexed_zip w 512 0 mixedTranscriptUnitTrace

theorem indexed_three_tail (w : Nat → Wire) (i : Nat) (a c d : MixedTranscriptLetter)
    (tail : List MixedTranscriptLetter) (h : IndexedLetters w i (a::c::d::tail)) :
    IndexedLetters w (i+3) tail := by
  have next := h.2.2.2
  simpa only [Nat.add_assoc] using next

theorem indexed_packet_controls (w : Nat → Wire) (j : Nat) (hj : j < 170)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (a c d : MixedTranscriptLetter) (tail : List MixedTranscriptLetter)
    (h : IndexedLetters w (3*j) (a::c::d::tail)) :
    ∀ l ∈ [a,c,d],l.1.1 ∈ wires (compressedHistoryEncode w (3*j)) ∧
      l.1.2 ∈ wires (compressedHistoryEncode w (3*j)) := by
  have site (k : Fin 6) := compressedHistory_site_mem w hn hlo (3*j) (by omega) k
  have ha := h.1
  have hc := h.2.1
  have hd := h.2.2.1
  intro l hl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl|rfl
  · rw [ha]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId] using site 0
    · simpa [compressedHistoryMap,compressedHistoryId] using site 1
  · rw [hc]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId] using site 2
    · simpa [compressedHistoryMap,compressedHistoryId] using site 3
  · rw [hd]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using site 4
    · simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using site 5

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

private theorem short_programs (w : Nat → Wire) (b sign eff : Wire) (i : Nat)
    (ls : List MixedTranscriptLetter) (h : ls.length ≤ 2) :
    codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) i ls =
      directionalReplay false w b sign eff ls ∧
    codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) i ls =
      directionalReplay true w b sign eff ls := by
  cases ls with
  | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
      OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
  | cons a ls =>
    cases ls with
    | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
        OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
    | cons c ls =>
      cases ls with
      | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
          OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
      | cons d tail =>
        simp at h
        omega

private theorem split_programs {α : Type} (w : Nat → Wire) (cell : α → Program)
    (i : Nat) (a c d : α) (tail : List α) :
    codecGroupForward w cell i (a::c::d::tail) =
      codecGroupForward w cell i [a,c,d]++codecGroupForward w cell (i+3) tail ∧
    codecGroupBackward w cell i (a::c::d::tail) =
      codecGroupBackward w cell (i+3) tail++codecGroupBackward w cell i [a,c,d] := by
  simp only [codecGroupForward,codecGroupBackward,List.append_nil,List.nil_append,List.append_assoc]
  constructor <;> trivial

/-- Full emitted packet recursion. The two raw final letters are retained;
all170 integer codec groups remain represented by the same fixed encoding. -/
theorem grouped_encoded_replays (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base)
    (n j : Nat) (remaining : j+n=170) (ls : List MixedTranscriptLetter)
    (length : ls.length=3*n+2) (aligned : IndexedLetters w (3*j) ls)
    (hf : MixedTranscriptReplayLayout w b sign eff ls) :
    (∀ (X Y : Fp) (s : State) (m : List Bool), EncodedFieldFrame w sign base X Y s →
      let out := run (codecGroupForward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) ls) m s
      out.phase=s.phase ∧ EncodedFieldFrame w sign base
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2 out) ∧
    (∀ (X Y : Fp) (s : State) (m : List Bool), EncodedFieldFrame w sign base X Y s →
      let out := run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) ls) m s
      out.phase=s.phase ∧ EncodedFieldFrame w sign base
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).1
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).2 out) := by
  induction n generalizing j ls with
  | zero =>
    have ji : j=170 := by omega
    have len : ls.length=2 := by simpa using length
    have programs := short_programs w b sign eff (3*j) ls (by omega)
    constructor
    · intro X Y s m input
      rw [programs.1]
      simpa only [directionalPayload,Bool.false_eq_true,if_false] using
        encoded_tail_replay false w b sign eff hn hlo ho hp (3*j) ls (by omega)
          (by omega) aligned hf base hg0 he0 env legal X Y s m input
    · intro X Y s m input
      rw [programs.2]
      simpa only [directionalPayload,if_true] using
        encoded_tail_replay true w b sign eff hn hlo ho hp (3*j) ls (by omega)
          (by omega) aligned hf base hg0 he0 env legal X Y s m input
  | succ n ih =>
    cases ls with
    | nil => simp at length
    | cons a rest =>
      cases rest with
      | nil => simp at length
      | cons c rest =>
        cases rest with
        | nil => simp at length
        | cons d tail =>
          have jj : j < 170 := by omega
          have next : IndexedLetters w (3*(j+1)) tail := by
            simpa only [Nat.mul_add,Nat.mul_one] using indexed_three_tail w (3*j) a c d tail aligned
          have lenTail : tail.length=3*n+2 := by simp only [List.length_cons] at length; omega
          have hfTail : MixedTranscriptReplayLayout w b sign eff tail := fun q hq => hf q (by simp [hq])
          have hfPacket : MixedTranscriptReplayLayout w b sign eff [a,c,d] := by
            intro q hq
            exact hf q (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using
              (show q=a ∨ q=c ∨ q=d ∨ q∈tail from by simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto))
          have controls := indexed_packet_controls w j jj (skywalkShared_integer_nodup w hn) hlo a c d tail aligned
          have support := packet_active_support w b sign eff (3*j) [a,c,d] controls
          have tailSpec := ih (j+1) (by omega) tail lenTail next hfTail
          have fwSplit := (split_programs w (fun l : MixedTranscriptLetter =>
            OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) a c d tail).1
          have rvSplit := (split_programs w (fun l : MixedTranscriptLetter =>
            OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) a c d tail).2
          constructor
          · intro X Y s m input
            let packet := codecGroupForward w (fun l : MixedTranscriptLetter =>
              OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]
            let t := run packet (m.take (measurementCount packet)) s
            let Q := skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)
            have first := encoded_forward_packet_step w b sign eff hn hlo j jj a c d hfPacket ho hp
              base hg0 he0 env legal X Y (by simpa only [rawForwardPacket] using support.1)
              s (m.take (measurementCount packet)) input
            have rest := tailSpec.1 Q.1 Q.2 t (m.drop (measurementCount packet)) first.2
            rw [fwSplit,run_append]
            change (run _ _ t).phase=s.phase ∧ _
            refine ⟨rest.1.trans first.1,?_⟩
            simpa only [mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,Q] using rest.2
          · intro X Y s m input
            let later := codecGroupBackward w (fun l : MixedTranscriptLetter =>
              OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j+3) tail
            let t := run later (m.take (measurementCount later)) s
            let Q := skywalkPayloadReplayInverse (mixedTranscriptControls base b tail) (X,Y)
            have rest := tailSpec.2 X Y s (m.take (measurementCount later)) input
            have first := encoded_backward_packet_step w b sign eff hn hlo j jj a c d hfPacket ho hp
              base hg0 he0 env legal Q.1 Q.2 (by simpa only [rawBackwardPacket] using support.2)
              t (m.drop (measurementCount later)) rest.2
            rw [rvSplit,run_append]
            change (run _ _ t).phase=s.phase ∧ _
            refine ⟨first.1.trans rest.1,?_⟩
            simpa only [mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q] using first.2

/-- Explicit actual512 forward and inverse field emissions, for all records.
No physical qubit allocation or whole-point resource claim is made here. -/
theorem compressedFieldGroups_512_frame (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (hf : MixedTranscriptReplayLayout w b sign eff (mixedTranscriptTape w))
    (base : BasisState) (hg0 : base sign=false) (he0 : base eff=false)
    (env : Env w base) (legal : RawGroupLegal w 170 base)
    (X Y : Fp) (s : State) (m : List Bool) (input : EncodedFieldFrame w sign base X Y s) :
    ((run (compressedFieldForwardGroups w b sign eff) m s).phase=s.phase ∧
      EncodedFieldFrame w sign base
        (skywalkPayloadReplay (mixedTranscriptControls base b (mixedTranscriptTape w)) (X,Y)).1
        (skywalkPayloadReplay (mixedTranscriptControls base b (mixedTranscriptTape w)) (X,Y)).2
        (run (compressedFieldForwardGroups w b sign eff) m s)) ∧
    ((run (compressedFieldBackwardGroups w b sign eff) m s).phase=s.phase ∧
      EncodedFieldFrame w sign base
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b (mixedTranscriptTape w)) (X,Y)).1
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b (mixedTranscriptTape w)) (X,Y)).2
        (run (compressedFieldBackwardGroups w b sign eff) m s)) := by
  have all := grouped_encoded_replays w b sign eff hn hlo ho hp base hg0 he0 env legal 170 0
    (by decide) (mixedTranscriptTape w) (by rw [mixedTranscriptTape_length]) (mixedTape_indexed w) hf
  exact ⟨all.1 X Y s m input,all.2 X Y s m input⟩

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

/-- Switching placements at an encoded packet boundary is justified by
that invariant itself; phase and every live field coordinate are preserved. -/
theorem run_switch_encoded_boundary (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (base : BasisState) (env : Env w base) (X Y : Fp) (s actual : State)
    (frame : EncodedFieldFrame w sign base X Y s)
    (a j : Nat) (ha : a < 170) (hj : j < 170) (program : Program) (m : List Bool)
    (map : pullState (pi a) actual = pullState w s) :
    pullState (pi j) (run (renameProgram (pi j) program) m actual) =
      run program m (pullState w s) :=
  run_switch_packet_placements a j ha hj actual (pullState w s) program m map
    (encoded_zero_region w sign hn hlo base env X Y s frame)

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

/-- The actual clear therefore retains a legal ghost encoding relation.
This bridge asserts no field Env before caller work and ports are prepared. -/
theorem compressed_terminal_clear_encoding (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1) (s : State)
    (stage : CompressedCompactStage w x p 512 s.basis) (m : List Bool) :
    ∃ raw : State,
      CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 raw.basis ∧
      RawGroupLegal w 170 raw.basis ∧ raw.phase=s.phase ∧
      run (skywalkArithmeticClear w) m s=
        run (allGroupEncode w 170) [] (run (skywalkArithmeticClear w) m raw) := by
  obtain ⟨raw,compact,legal,phase,encoded⟩ :=
    compressed_terminal_encoded_state w hn hlo x p hp0 hpo s stage
  refine ⟨raw,compact,legal,phase,?_⟩
  rw [encoded]
  exact (full_encoder_clear_commute w hn hlo raw [] m).symm

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

theorem slots_nodup : slots.Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ h
    change a+16=b+16 at h
    exact Nat.add_right_cancel h
  · exact indices_nodup

theorem slots_length : slots.length=1899 := by simp [slots,indices]

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

theorem placed_field_mem (j q : Nat) (hj : j < 170) (h : fieldSite q) :
    placed j q∈slots.toFinset := slot_mem _ (pi_live j q hj (field_live q h)) (field_safe j q hj h)

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

private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

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

private theorem pull_injective (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

/-- Exact complete-State equivalence for the actual computable emission.
All original square inputs, independent records, and the full pool contract
are retained; the permutation is confined to clean declared sites. -/
theorem state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (computableProgram L) m s=run (pointMeasuredSquareCandidate L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := pointMeasuredSquareCandidate_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (pointMeasuredSquareCandidate L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (pool_away_x L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (pointMeasuredSquareCandidate L) m s) cleanOut
  rw [computableProgram_eq L hw hn,program]
  apply pull_injective e
  have semantic := run_rename e e.injective (pointMeasuredSquareCandidate L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

/-- Existing phase, numeric, clean-work, and every outsider guarantees are
inherited as properties of the actual computable renamed square. -/
theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (computableProgram L) m s).phase=s.phase ∧
    regValue L.point.x (run (computableProgram L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (computableProgram L) m s).basis q=s.basis q := by
  rw [state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact pointMeasuredSquareCandidate_correct L hw hn X Y B hX s m hb hx hy hc

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (computableProgram L)=99902 ∧ measurementCount (computableProgram L)=99382 := by
  rw [computableProgram]
  have renamed := renameProgram_counts (labelFn L.core.poolWire) (pointMeasuredSquareCandidate L)
  have old := pointMeasuredSquareCandidate_counts L hw
  exact ⟨renamed.1.trans old.1,renamed.2.trans old.2⟩

theorem residents_length (L : ControlledPointLayout) (hw : L.Widths) : (residents L).length=521 := by
  simp only [residents,PointAddLayout.pointWires,inPlaceFlags,List.length_append,List.length_cons,
    List.length_nil,show L.point.x.length=256 from hw.inputX,
    show L.point.y.length=256 from hw.inputY]

/-- The actual square fits the shared candidate inventory. Cardinality is
bounded by the1899 explicit sites; no whole-point allocation claim is made. -/
theorem shared_support_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (residents L++sharedPool L).length=1899 ∧
    wires (computableProgram L)⊆(residents L++sharedPool L).toFinset ∧
    qubitCount (computableProgram L) ≤ 1899 := by
  have length : (residents L++sharedPool L).length=1899 := by
    rw [List.length_append,residents_length L hw,sharedPool_length]
  have support := computable_support L hw hn
  refine ⟨length,support,?_⟩
  change (wires (computableProgram L)).card ≤ 1899
  calc
    _ ≤ (residents L++sharedPool L).toFinset.card := Finset.card_le_card support
    _ ≤ (residents L++sharedPool L).length := List.toFinset_card_le _
    _ = 1899 := length

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

theorem pointIndexWire_metadata (L : ControlledPointLayout) :
    pointIndexWire L 2400=L.core.generic ∧ pointIndexWire L 2401=L.point.finite ∧
    pointIndexWire L 2402=L.control ∧ pointIndexWire L 2403=L.infinitySelect ∧
    pointIndexWire L 2404=L.doubleSelect ∧ pointIndexWire L 2405=L.genericSelect ∧
    pointIndexWire L 2406=L.core.equalX ∧ pointIndexWire L 2407=L.core.equalNegY ∧
    pointIndexWire L 2408=L.core.double ∧ pointIndexWire L 2409=L.skywalkDirectSelectorG ∧
    pointIndexWire L 2410=L.skywalkDirectSelectorS ∧ pointIndexWire L 2411=L.skywalkDirectZero := by
  simp [pointIndexWire,pointMeta]

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

theorem pointInventory_length (L : ControlledPointLayout) (hw : L.Widths) :
    (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).length=1899 := by
  simp [CompressedPointSquare.residents,CompressedPointSquare.sharedPool_length,
    PointAddLayout.pointWires,inPlaceFlags,point,hw.inputX,hw.inputY]

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

theorem low_map (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    (mapCleanup f L).low=L.low.map f := by
  simp [mapCleanup,BalancedCleanup.Layout.low]
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

theorem offset_chain_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (cinC cinB target : Wire) :
    renameProgram f (BalancedCleanupOffset.chain bits xs ys cs ds cinC cinB target) =
      BalancedCleanupOffset.chain (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f cinC) (f cinB) (f target) := by
  induction bits generalizing xs ys cs ds cinC cinB with
  | nil =>
    cases xs <;> cases ys <;> cases cs <;> cases ds <;>
      simp only [BalancedCleanupOffset.chain,List.map_nil,List.map_cons,renameProgram,List.map_nil]
    exact flipBelow_natural f none cinB target
  | cons b bits ih =>
    cases xs with
    | nil => simp [BalancedCleanupOffset.chain,renameProgram]
    | cons a xs =>
      cases ys with
      | nil => simp [BalancedCleanupOffset.chain,renameProgram]
      | cons y ys =>
        cases cs with
        | nil => simp [BalancedCleanupOffset.chain,renameProgram]
        | cons c cs =>
          cases ds with
          | nil => simp [BalancedCleanupOffset.chain,renameProgram]
          | cons d ds =>
            simp only [BalancedCleanupOffset.chain,List.map_cons,rename_append,
              mappedMajority_natural,mappedSum_natural,majority_natural,eraseCarry_natural,
              mappedEraseCarry_natural,ih]
            rfl

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

theorem offset_program_natural (f : Wire → Wire) (L : BalancedCleanupOffset.Layout) :
    renameProgram f (BalancedCleanupOffset.program L)=BalancedCleanupOffset.program (mapOffset f L) := by
  simp only [BalancedCleanupOffset.program,rename_append,rename_reverse,prepareSign_natural,
    offset_view_natural,offset_chain_natural,offsetBits_map]
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

/-- Naturality of the actual 511-T/M cleanup, including the singleton leaf.
No injectivity premise is needed for this syntactic relabeling identity. -/
theorem slim_offset_program_natural (f : Wire → Wire) (L : Layout) (hw : L.Widths) :
    renameProgram f (BalancedCleanupOffsetSlim.program L) =
      BalancedCleanupOffsetSlim.program (mapOffset f L) := by
  have widths := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  have co : L.offsetCarry.length=256 := hw.2
  have cn := slim_offset_chain_natural f (offsetBits L) L.y L.r L.offsetCarry L.carry
    L.one L.cout L.parity (by simp [offsetBits,widths.2.1]) (by omega)
    (by omega) (by omega)
  simp only [BalancedCleanupOffsetSlim.program,rename_append,rename_reverse,
    slim_front_natural,cn,offsetBits_map]
  simp only [mapOffset,mapCircuit,mapCleanup,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.map_cons,List.map_append]
  rfl

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

theorem unary_support (divide : Bool) :
    wires (renameProgram allPlaced (if divide then dblInPlace (borrowedSkywalkUnary id) p
      else halfInPlace (borrowedSkywalkUnary id) p))⊆slots.toFinset := by
  have u := modUnary_wires (borrowedSkywalkUnary id) 256 p (borrowedSkywalkUnary_widths id) (by omega)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member : old∈((borrowedSkywalkUnary id).z++(borrowedSkywalkUnary id).core.work++
      [(borrowedSkywalkUnary id).flag]).toFinset := by
    cases divide
    · simp only [Bool.false_eq_true,if_false] at hraw
      rw [u.2] at hraw
      exact hraw
    · simp only [if_true] at hraw
      rw [u.1] at hraw
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hraw))
  have site : fieldSite old := by
    change old∈((wireBlock id 2056 256++[id 2312])++
      (wireBlock id 512 257++wireBlock id 1540 256++[id 1797])++[id 769]).toFinset at member
    simp only [List.mem_toFinset,wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false] at member
    dsimp only [id] at member
    simp only [or_assoc] at member
    rcases member with h|rfl|h|h|rfl|rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · norm_num [fieldSite]
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · norm_num [fieldSite]
    · norm_num [fieldSite]
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

theorem fieldSegment_support (divide : Bool) : wires (fieldSegment divide)⊆slots.toFinset := by
  have unary := unary_support divide
  have a := converters_support false
  have b := converters_support true
  have r := mappedReplay_support divide
  cases divide <;> simp only [fieldSegment,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff,and_assoc]
  · exact ⟨copy_support,a,r,b,unary⟩
  · exact ⟨unary,a,r,b,copy_support⟩

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

/-- Swap selection is retired before selecting the inverse field control.
This uses the independently measured inverse kernel, never reversed MX. -/
def inverse (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b swap flag is
    (swapRegisters flag (balancedSharedPorts w flag).r (balancedSharedPorts w flag).y) ++
  transcriptSelectWindow b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])

def sites (w : Nat → Wire) (b g swap flag : Wire) : List Wire :=
  [b,g,swap]++CompressedFieldSupport.sharedSites w flag

theorem counts (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool)
    (hn : (flag::(balancedSharedPorts w flag).r++
      (balancedSharedPorts w flag).y).Nodup) :
    toffoliCount (forward w b g swap flag ig is)=1280 ∧
    measurementCount (forward w b g swap flag ig is)=1025 ∧
    toffoliCount (inverse w b g swap flag ig is)=1281 ∧
    measurementCount (inverse w b g swap flag ig is)=1025 := by
  have width := BalancedCleanup.widths (balancedSharedPorts w flag).toLayout
    (balancedSharedPorts_widths w flag)
  have sw := swapRegisters_resources flag _ _ (width.2.1.trans width.2.2.1.symm) hn
  have fw := OffsetBorrowedField.counts w flag
  have iv := OffsetBorrowedInverse.counts w flag
  have fsel := transcriptSelectWindow_counts b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])
  have isel := transcriptSelectWindow_counts b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])
  have ssel := transcriptSelectWindow_counts b swap flag is
    (swapRegisters flag (balancedSharedPorts w flag).r (balancedSharedPorts w flag).y)
  simp only [forward,inverse,toffoliCount_append,measurementCount_append,
    fsel.1,fsel.2,isel.1,isel.2,ssel.1,ssel.2,
    fw.1,fw.2,iv.1,iv.2,sw.1,sw.2.1,width.2.1]
  norm_num [toffoliCount,measurementCount]

theorem forward_counts (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool)
    (hn : (flag::(balancedSharedPorts w flag).r++(balancedSharedPorts w flag).y).Nodup) :
    toffoliCount (forward w b g swap flag ig is)=1280 ∧
    measurementCount (forward w b g swap flag ig is)=1025 := by
  have h := counts w b g swap flag ig is hn
  exact ⟨h.1,h.2.1⟩

theorem inverse_counts (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool)
    (hn : (flag::(balancedSharedPorts w flag).r++(balancedSharedPorts w flag).y).Nodup) :
    toffoliCount (inverse w b g swap flag ig is)=1281 ∧
    measurementCount (inverse w b g swap flag ig is)=1025 := by
  have h := counts w b g swap flag ig is hn
  exact ⟨h.2.2.1,h.2.2.2⟩

private theorem window_support (b src flag : Wire) (constant : Bool)
    (body : Program) (W : Finset Wire) (hb : b∈W) (hs : src∈W)
    (hf : flag∈W) (hbody : wires body⊆W) :
    wires (transcriptSelectWindow b src flag constant body)⊆W := by
  have select : wires (transcriptSelectCompute b src flag constant)⊆W ∧
      wires (transcriptSelectExpose flag constant)⊆W ∧
      wires (transcriptSelectErase b src flag constant)⊆W := by
    cases constant <;>
      simp [transcriptSelectCompute,transcriptSelectExpose,transcriptSelectErase,
        wires,Instr.wires,correctionWires,Finset.subset_iff,hb,hs,hf]
  simp only [transcriptSelectWindow,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨select.1,select.2.1,hbody,select.2.1,select.2.2⟩

private theorem swap_layout_support (L : BalancedCircuit.Layout)
    (hw : L.r.length=L.y.length) :
    wires (swapRegisters L.sign L.r L.y)⊆L.wires.toFinset := by
  intro q hq
  have member := (swapRegisters_wires L.sign L.r L.y hw) hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member ⊢
  tauto

/-- Only one effective-control site occurs in either actual instruction list.
All measured Z/CZ correction support is included. -/
theorem support (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool) :
    wires (forward w b g swap flag ig is)⊆(sites w b g swap flag).toFinset ∧
    wires (inverse w b g swap flag ig is)⊆(sites w b g swap flag).toFinset := by
  let L := balancedSharedPorts w flag
  let W := (sites w b g swap flag).toFinset
  have own : L.wires.toFinset⊆W := by
    intro q hq
    simp only [W,sites,CompressedFieldSupport.sharedSites,List.mem_toFinset,
      List.mem_append] at ⊢
    exact Or.inr (Or.inl (Or.inr (List.mem_toFinset.mp hq)))
  have kernelOwn : (CompressedFieldSupport.sharedSites w flag).toFinset⊆W := by
    intro q hq
    simp only [W,sites,List.mem_toFinset,List.mem_append]
    exact Or.inr (List.mem_toFinset.mp hq)
  have controls : b∈W ∧ g∈W ∧ swap∈W ∧ flag∈W := by
    simp [W,sites,CompressedFieldSupport.sharedSites]
  have kernels := CompressedFieldSupport.kernels_support w flag
  have flagSupport : wires [.X flag]⊆W := by
    simp [wires,Instr.wires,Finset.subset_iff,controls.2.2.2]
  have fw : wires ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])⊆W := by
    simp only [wires_append,Finset.union_subset_iff]
    exact ⟨⟨flagSupport,kernels.1.trans kernelOwn⟩,flagSupport⟩
  have iv : wires ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])⊆W := by
    simp only [wires_append,Finset.union_subset_iff]
    exact ⟨⟨flagSupport,kernels.2.trans kernelOwn⟩,flagSupport⟩
  have width := BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w flag)
  have sw : wires (swapRegisters flag L.r L.y)⊆W :=
    (swap_layout_support L (width.2.1.trans width.2.2.1.symm)).trans own
  have fwin := window_support b g flag ig _ W controls.1 controls.2.1 controls.2.2.2 fw
  have iwin := window_support b g flag ig _ W controls.1 controls.2.1 controls.2.2.2 iv
  have swin := window_support b swap flag is _ W controls.1 controls.2.2.1 controls.2.2.2 sw
  simp only [forward,inverse,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fwin,swin⟩,⟨swin,iwin⟩⟩

theorem omitted_effS_away (w : Nat → Wire) (b g swap flag oldEffS : Wire)
    (ig is : Bool) (ha : oldEffS∉sites w b g swap flag) :
    oldEffS∉wires (forward w b g swap flag ig is) ∧
    oldEffS∉wires (inverse w b g swap flag ig is) := by
  have h := support w b g swap flag ig is
  exact ⟨fun hm => ha (List.mem_toFinset.mp (h.1 hm)),
    fun hm => ha (List.mem_toFinset.mp (h.2 hm))⟩

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

private theorem swap_pair (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have ca : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c ca.1 ca.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]


private theorem field_frame (divide : Bool) (w : Nat → Wire) (sign : Wire)
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
    rw [half_eq w sign hn ho base he X Y s m h]
    exact old s m h

private theorem field_window (divide : Bool) (w : Nat → Wire) (b src sign : Wire)
    (constant : Bool) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (nd : [b,src,sign].Nodup)
    (hb : b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y)
    (hs : src∉(balancedSharedPorts w sign).r ∧ src∉(balancedSharedPorts w sign).y)
    (hf : sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y)
    (base : BasisState) (hz : base sign=false) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      (transcriptSelectWindow b src sign constant ([.X sign]++
        (if divide then OffsetBorrowedField.program w sign else OffsetBorrowedInverse.program w sign)++[.X sign]))
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then (X+(if mixedTranscriptBit base b src constant then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit base b src constant then -Y else Y))) (centerWord Y)) := by
  have f := field_frame divide w sign hn ho (mixedTranscriptBase base b src sign constant)
    (env_write w sign ho base _ he) X Y
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at f
  exact transcriptSelectWindow_pairFrame b src sign constant _ _ nd hb hs hf base hz _ _ _ _ _ f

private theorem swap_window (w : Nat → Wire) (b src sign : Wire) (constant : Bool)
    (nd : [b,src,sign].Nodup)
    (hb : b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y)
    (hs : src∉(balancedSharedPorts w sign).r ∧ src∉(balancedSharedPorts w sign).y)
    (hf : sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y)
    (sw : (sign::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup)
    (base : BasisState) (hz : base sign=false) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      (transcriptSelectWindow b src sign constant
        (swapRegisters sign (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y))
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if mixedTranscriptBit base b src constant then Y else X))
        (centerWord (if mixedTranscriptBit base b src constant then X else Y))) := by
  have len := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have f := swap_pair _ _ sign (len.2.1.trans len.2.2.1.symm) sw
    (mixedTranscriptBase base b src sign constant) (centerWord X) (centerWord Y)
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at f
  have f' : Triple
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        (mixedTranscriptBase base b src sign constant) (centerWord X) (centerWord Y))
      (swapRegisters sign (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      (mixedTranscriptBase base b src sign constant)
      (centerWord (if mixedTranscriptBit base b src constant then Y else X))
      (centerWord (if mixedTranscriptBit base b src constant then X else Y))) := by
    cases hbit : mixedTranscriptBit base b src constant <;>
      simpa only [mixedTranscriptBase,writeBit,hbit,if_true,if_false,Bool.false_eq_true] using f
  exact transcriptSelectWindow_pairFrame b src sign constant _ _ nd hb hs hf base hz _ _ _ _ _ f'

theorem cell_frame (divide : Bool) (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (hz : base sign=false)
    (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      (if divide then forward w b g swap sign ig is else inverse w b g swap sign ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then skywalkPayloadCell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y) else skywalkPayloadUncell
          (mixedTranscriptBit base b g ig) (mixedTranscriptBit base b swap is) (X,Y)).1)
        (centerWord (if divide then skywalkPayloadCell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y) else skywalkPayloadUncell
          (mixedTranscriptBit base b g ig) (mixedTranscriptBit base b swap is) (X,Y)).2)) := by
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ss : [b,swap,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ba := hl.outside b (by simp)
  have ga := hl.outside g (by simp)
  have sa := hl.outside swap (by simp)
  have fa := hl.outside sign (by simp [balancedSharedPorts])
  have sw : (sign::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup :=
    List.nodup_cons.mpr ⟨by
      intro h
      rcases List.mem_append.mp h with h|h
      · exact fa.1 h
      · exact fa.2 h,
      balancedSharedLayout_pairND w sign hn⟩
  cases divide
  · let A := if mixedTranscriptBit base b swap is then Y else X
    let B := if mixedTranscriptBit base b swap is then X else Y
    have first := swap_window w b swap sign is ss ba sa fa sw base hz X Y
    have last := field_window false w b g sign ig hn ho sg ba ga fa base hz he A B
    have result := first.seq last
    cases hswap : mixedTranscriptBit base b swap is <;>
      simpa only [inverse,skywalkPayloadUncell,A,B,hswap,if_true,if_false,Bool.false_eq_true] using result
  · let H := (X+(if mixedTranscriptBit base b g ig then Y else -Y))/2
    have first := field_window true w b g sign ig hn ho sg ba ga fa base hz he X Y
    have last := swap_window w b swap sign is ss ba sa fa sw base hz H Y
    have result := first.seq last
    cases hswap : mixedTranscriptBit base b swap is <;>
      simpa only [forward,skywalkPayloadCell,H,hswap,if_true,if_false,Bool.false_eq_true] using result
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

private theorem swap_equal_pair (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (base : BasisState) (X : Nat) :
    Triple (PairFrame r y base X X) (swapRegisters c r y) (PairFrame r y base X X) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · simpa only [h.1,h.2.1,ite_self] using v.2.2.1
  · simpa only [h.1,h.2.1,ite_self] using v.2.2.2

/-- The complete actual measured S window is identity on equal words,
including both control polarities and every outcome. Its flag must start0. -/
theorem swap_window_state (r y : List Wire) (b src flag : Wire) (constant : Bool)
    (hlen : r.length=y.length) (hn : (flag::r++y).Nodup)
    (nd : [b,src,flag].Nodup) (hb : b∉r ∧ b∉y) (hs : src∉r ∧ src∉y)
    (s : State) (m : List Bool) (hz : s.basis flag=false)
    (heq : regValue r s.basis=regValue y s.basis) :
    run (transcriptSelectWindow b src flag constant (swapRegisters flag r y)) m s=s := by
  have hf : flag∉r ∧ flag∉y := by
    have away := (List.nodup_cons.mp hn).1
    exact ⟨fun h => away (List.mem_append_left _ h),
      fun h => away (List.mem_append_right _ h)⟩
  let X := regValue r s.basis
  have input : PairFrame r y s.basis X X s.basis := ⟨rfl,heq.symm,fun _ _ _ => rfl⟩
  have body := swap_equal_pair r y flag hlen hn
    (mixedTranscriptBase s.basis b src flag constant) X
  have window := transcriptSelectWindow_pairFrame b src flag constant r y
    nd hb hs hf s.basis hz X X X X (swapRegisters flag r y) body
  have out := window s m input
  apply State.extensionality
  · exact out.1
  · exact PairFrame.unique r y s.basis X X _ _ out.2 input

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

theorem forward_support_subset (w : Nat → Wire) (b g swap sign : Wire) (ig is : Bool) :
    wires (forward w b g sign ig)⊆
      wires (OffsetBorrowedSerialized.forward w b g swap sign ig is) := by
  change wires (forward w b g sign ig)⊆
    wires (forward w b g sign ig ++ transcriptSelectWindow b swap sign is
      (swapRegisters sign (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y))
  rw [wires_append]
  exact Finset.subset_union_left

theorem inverse_support_subset (w : Nat → Wire) (b g swap sign : Wire) (ig is : Bool) :
    wires (inverse w b g sign ig)⊆
      wires (OffsetBorrowedSerialized.inverse w b g swap sign ig is) := by
  change wires (inverse w b g sign ig)⊆
    wires (transcriptSelectWindow b swap sign is
      (swapRegisters sign (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y) ++
        inverse w b g sign ig)
  rw [wires_append]
  exact Finset.subset_union_right

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

theorem mappedReplay_counts (divide : Bool) :
    toffoliCount (mappedReplay divide)=(if divide then 656550 else 657062) ∧ measurementCount (mappedReplay divide)=524970 := by
  have groups := mappedGroups_counts divide 0 170
  have a := logicalCell_counts divide 510
  have b := logicalCell_counts divide 511
  cases divide <;> simp only [mappedReplay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,renameT,renameM,groups.1,groups.2,a.1,a.2,b.1,b.2]
  all_goals norm_num

theorem converterPair_counts (canonical : Bool) :
    toffoliCount (converterPair canonical)=1530 ∧ measurementCount (converterPair canonical)=1530 := by
  have target := BalancedConvert.counts (balancedSharedTargetConvert id) (balancedSharedTargetConvert_widths id)
  have source := BalancedConvert.counts (balancedSharedSourceConvert id) (balancedSharedSourceConvert_widths id)
  cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,target.1,target.2.1,target.2.2.1,target.2.2.2,
    source.1,source.2.1,source.2.2.1,source.2.2.2]
  all_goals norm_num

private theorem endpointCopy_counts :
    toffoliCount (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)=0 ∧
    measurementCount (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)=0 := by
  have len : (skywalkSharedField id).z.length=(skywalkSharedField id).a.length := by
    rw [skywalkShared_field_z]
    change (wireBlock id 2056 257).length=(wireBlock id 770 257).length
    simp [wireBlock]
  have copy := copyRegister_counts none (skywalkSharedField id).z (skywalkSharedField id).a len
  simpa only [Option.isSome_none,Bool.false_eq_true,if_false] using copy

theorem fieldSegment_counts (divide : Bool) :
    toffoliCount (fieldSegment divide)=(if divide then 660121 else 660634) ∧
    measurementCount (fieldSegment divide)=(if divide then 528541 else 528542) := by
  have unary := modUnary_counts (borrowedSkywalkUnary id) 256 p (borrowedSkywalkUnary_widths id) (by omega)
  have center := converterPair_counts false
  have canonical := converterPair_counts true
  have replay := mappedReplay_counts divide
  cases divide <;> simp only [fieldSegment,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,renameT,renameM,endpointCopy_counts.1,
    endpointCopy_counts.2,unary.1,unary.2.1,unary.2.2.1,unary.2.2.2,
    center.1,center.2,canonical.1,canonical.2,replay.1,replay.2]
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

def baseTail (divide : Bool) : Program :=
  if divide then renameProgram base (logicalCell divide 510)++renameProgram base (logicalCell divide 511)
  else renameProgram base (logicalCell divide 511)++renameProgram base (logicalCell divide 510)

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

theorem baseGroups_counts (divide : Bool) (j n : Nat) :
    toffoliCount (baseGroups divide j n)=(if divide then 3847 else 3850)*n ∧
    measurementCount (baseGroups divide j n)=3076*n := by
  induction n generalizing j with
  | zero => simp [baseGroups,toffoliCount,measurementCount]
  | succ n ih =>
    have head := baseGroup_counts divide j
    have rest := ih (j+1)
    cases divide <;> simp only [baseGroups,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append,head.1,head.2,rest.1,rest.2]
    all_goals constructor <;> omega

theorem baseGroup_counts_eq (divide : Bool) (j : Nat) (hj : j < 170) :
    toffoliCount (baseGroup divide j)=toffoliCount (mappedGroup divide j) ∧
    measurementCount (baseGroup divide j)=measurementCount (mappedGroup divide j) := by
  rw [mappedGroup_eq_rename divide j hj]
  have counts := renameProgram_counts (shifted (CompressedAllocation.pi j)) (baseGroup divide j)
  exact ⟨counts.1.symm,counts.2.symm⟩

theorem baseGroups_counts_eq (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    toffoliCount (baseGroups divide j n)=toffoliCount (mappedGroups divide j n) ∧
    measurementCount (baseGroups divide j n)=measurementCount (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp only [baseGroups,mappedGroups]
            constructor <;> trivial
  | succ n ih =>
    have head := baseGroup_counts_eq divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [baseGroups,mappedGroups,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append,head.1,head.2,rest.1,rest.2]
    all_goals constructor <;> trivial

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

private theorem indexedLetters_zero (start : Nat) : indexedLetters start 0=[] := rfl

private theorem indexedLetters_step (start n : Nat) :
    indexedLetters start (n+1)=tapeLetter start::indexedLetters (start+1) n := by
  simp only [indexedLetters,List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def]
  simp only [Nat.add_zero,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem indexedLetters_three (start n : Nat) :
    indexedLetters start (n+3)=tapeLetter start::tapeLetter (start+1)::tapeLetter (start+2)::
      indexedLetters (start+3) n := by
  rw [show n+3=(n+2)+1 by omega,indexedLetters_step,
    show n+2=(n+1)+1 by omega,indexedLetters_step,indexedLetters_step]

def referenceCell (divide : Bool) (l : MixedTranscriptLetter) : Program :=
  if divide then OffsetBorrowedCanonical.cell base (base 2400) l.1.1 l.1.2
    (base 2409) (base 2410) l.2.1 l.2.2
  else OffsetBorrowedInverseCanonical.cell base (base 2400) l.1.1 l.1.2
    (base 2409) (base 2410) l.2.1 l.2.2

def referenceGroups (divide : Bool) (start : Nat) (ls : List MixedTranscriptLetter) : Program :=
  if divide then codecGroupForward base (referenceCell divide) start ls
  else codecGroupBackward base (referenceCell divide) start ls

theorem referenceCell_letter (divide : Bool) (i : Nat) (hi : i < 512) :
    referenceCell divide (tapeLetter i)=renameProgram base (logicalCell divide i) := by
  rw [tapeLetter,mixedTape_base_getD i hi,base_cell_eq]
  cases divide <;> rfl

private theorem reference_cons3 (divide : Bool) (start : Nat)
    (a c d : MixedTranscriptLetter) (tail : List MixedTranscriptLetter) :
    referenceGroups divide start (a::c::d::tail)=
      if divide then referenceGroups divide start [a,c,d]++referenceGroups divide (start+3) tail
      else referenceGroups divide (start+3) tail++referenceGroups divide start [a,c,d] := by
  cases divide <;> simp only [referenceGroups,Bool.false_eq_true,if_false,if_true,
    codecGroupForward,codecGroupBackward,List.append_nil,List.nil_append,List.append_assoc]

theorem baseGroup_eq_reference (divide : Bool) (j : Nat) (hj : j < 170) :
    baseGroup divide j=referenceGroups divide (3*j) (packetLetters j) := by
  have packet := baseGroup_eq_packet divide j hj
  cases divide <;> simpa only [referenceGroups,referenceCell,Bool.false_eq_true,if_false,if_true] using packet

private theorem reference_packet_append (divide : Bool) (j : Nat) (hj : j < 170)
    (tail : List MixedTranscriptLetter) :
    referenceGroups divide (3*j) (packetLetters j++tail)=
      if divide then baseGroup divide j++referenceGroups divide (3*j+3) tail
      else referenceGroups divide (3*j+3) tail++baseGroup divide j := by
  have h := reference_cons3 divide (3*j) (tapeLetter (3*j))
    (tapeLetter (3*j+1)) (tapeLetter (3*j+2)) tail
  change referenceGroups divide (3*j) (packetLetters j++tail)=
    (if divide then referenceGroups divide (3*j) (packetLetters j)++referenceGroups divide (3*j+3) tail
     else referenceGroups divide (3*j+3) tail++referenceGroups divide (3*j) (packetLetters j)) at h
  rw [←baseGroup_eq_reference divide j hj] at h
  exact h

theorem baseTail_eq_reference (divide : Bool) :
    baseTail divide=referenceGroups divide 510 (indexedLetters 510 2) := by
  have a := referenceCell_letter divide 510 (by omega)
  have b := referenceCell_letter divide 511 (by omega)
  have letters : indexedLetters 510 2=[tapeLetter 510,tapeLetter 511] := by
    rw [show 2=1+1 by rfl,indexedLetters_step,show 1=0+1 by rfl,indexedLetters_step,indexedLetters_zero]
  rw [letters]
  cases divide <;> simp only [baseTail,referenceGroups,Bool.false_eq_true,if_false,if_true,
    codecGroupForward,codecGroupBackward,a,b]

/-- Structural recursion over all170 packets and the two raw terminal letters.
The tape is reconstructed from its actual getD values, with no body oracle. -/
theorem baseGroups_tail_eq_reference (divide : Bool) (j n : Nat) (h : j+n=170) :
    (if divide then baseGroups divide j n++baseTail divide
     else baseTail divide++baseGroups divide j n)=
      referenceGroups divide (3*j) (indexedLetters (3*j) (3*n+2)) := by
  induction n generalizing j with
  | zero =>
    have hj : j=170 := by omega
    subst j
    simpa only [baseGroups,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,
      List.nil_append,List.append_nil,ite_self] using baseTail_eq_reference divide
  | succ n ih =>
    have rest := ih (j+1) (by omega)
    have split : indexedLetters (3*j) (3*(n+1)+2)=
        packetLetters j++indexedLetters (3*(j+1)) (3*n+2) := by
      rw [show 3*(n+1)+2=(3*n+2)+3 by omega,indexedLetters_three]
      simp only [packetLetters,tapeLetter,List.cons_append,List.nil_append]
      rw [show 3*j+3=3*(j+1) by omega]
    rw [split,reference_packet_append divide j (by omega),
      show 3*j+3=3*(j+1) by omega]
    cases divide <;> simp only [baseGroups,Bool.false_eq_true,if_false,if_true] at rest ⊢
    · rw [←rest]
      simp only [List.append_assoc]
    · rw [←rest]
      simp only [List.append_assoc]

theorem base_forward_replay_identity :
    baseGroups true 0 170++baseTail true=
      compressedFieldForwardGroups base (base 2400) (base 2409) (base 2410) := by
  have h := baseGroups_tail_eq_reference true 0 170 (by omega)
  simpa only [if_true,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,Nat.reduceAdd,indexedLetters_full,
    referenceGroups,referenceCell,compressedFieldForwardGroups] using h

theorem base_backward_replay_identity :
    baseTail false++baseGroups false 0 170=
      compressedFieldBackwardGroups base (base 2400) (base 2409) (base 2410) := by
  have h := baseGroups_tail_eq_reference false 0 170 (by omega)
  simpa only [Bool.false_eq_true,if_false,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,Nat.reduceAdd,
    indexedLetters_full,referenceGroups,referenceCell,compressedFieldBackwardGroups] using h

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

theorem terminates_canonical_sub_one (p x n : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<p) (hc : p.Coprime x) :
    (step^[2*n-1] (init x p)).u=0 ∧ (step^[2*n-1] (init x p)).v=1 :=
  terminates_2n_sub_one p x n hp0 hx0 hpodd hp (hx.trans hp) hc.symm

/-- Complete256-bit canonical range: the state before round512 is terminal. -/
theorem terminates_511 (p x : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) :
    (step^[511] (init x p)).u=0 ∧ (step^[511] (init x p)).v=1 := by
  simpa only [Nat.reduceMul,Nat.reduceSub] using
    (terminates_2n_sub_one p x 256 hp0 hx0 hpodd hp (hx.trans hp) hc)

/-- Padding beyond the improved horizon changes no logical state. -/
theorem terminal_padding (p x n j : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<2^n) (hc : x.Coprime p) :
    step^[j] (step^[2*n-1] (init x p))=step^[2*n-1] (init x p) :=
  iter_fixed_of_u_zero _ j (terminates_2n_sub_one p x n hp0 hx0 hpodd hp hx hc).1

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

/-- Generic physical-record bridge. Instantiate α=Wire×Wire and read with
the caller's two basis reads. This stays below arithmetic/kernel imports. -/
theorem record_index511_controls {α : Type} (rs : List α) (read : α → Bool×Bool)
    (default : α) (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hr : rs.map read=trace 512 (encode false false (x : Int) (ECDSAAdd.p : Int))) :
    read (rs.getD 511 default)=(true,false) := by
  have h : (rs.map read).getD 511 (read default)=(true,false) := by
    rw [hr]
    exact trace512_last x hx0 hx _
  rw [map_getD_read] at h
  exact h

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

theorem cell_saving (divide : Bool) :
    toffoliCount (logicalCell divide 510)=toffoliCount (cell divide)+257 ∧
    measurementCount (logicalCell divide 510)=measurementCount (cell divide)+1 := by
  have old := logicalCell_counts divide 510
  have fresh := cell_counts divide
  rw [old.1,old.2,fresh.1,fresh.2]
  cases divide <;> norm_num

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

/-- The actual two raw residual cells, in ascending forward order and
independently measured descending inverse order. -/
def tailProgram (divide : Bool) : Program :=
  if divide then renameProgram allPlaced (logicalCell divide 510)++
      renameProgram allPlaced (logicalCell divide 511)
  else renameProgram allPlaced (logicalCell divide 511)++
      renameProgram allPlaced (logicalCell divide 510)

theorem tailLetters_indexed : IndexedLetters base 510 tailLetters := by
  rw [tailLetters,mixedTape_base_getD 510 (by decide),mixedTape_base_getD 511 (by decide)]
  simp [IndexedLetters]

/-- Keep the tape indices symbolic while the kernel checks the replay identity. -/
private theorem two_cells_eq_replay (divide : Bool) (i j : Nat)
    (hi : i < 512) (hj : j < 512) :
    (if divide then renameProgram base (logicalCell divide i) ++
        renameProgram base (logicalCell divide j)
      else renameProgram base (logicalCell divide j) ++
        renameProgram base (logicalCell divide i)) =
    directionalReplay (!divide) base (base 2400) (base 2409) (base 2410)
      [(mixedTranscriptTape base).getD i ((0,0),(false,false)),
       (mixedTranscriptTape base).getD j ((0,0),(false,false))] := by
  have a := mixedTape_base_getD i hi
  have b := mixedTape_base_getD j hj
  cases divide <;> simp only [a,b,base_cell_eq,directionalReplay,
    OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
    List.append_nil,List.nil_append]

theorem baseTail_eq_replay (divide : Bool) :
    baseTail divide=directionalReplay (!divide) base (base 2400) (base 2409) (base 2410) tailLetters := by
  exact two_cells_eq_replay divide 510 511 (by decide) (by decide)

private theorem shifted_all_cell (divide : Bool) (i : Nat) :
    renameProgram (shifted pi0) (renameProgram base (logicalCell divide i))=
      renameProgram allPlaced (logicalCell divide i) := by
  rw [renameProgram_comp]
  have eq : shifted pi0 ∘ base=allPlaced := by
    funext q
    exact shifted_base pi0 q
  rw [eq]

theorem tailProgram_eq_rename (divide : Bool) :
    tailProgram divide=renameProgram (shifted pi0) (baseTail divide) := by
  cases divide <;> simp only [tailProgram,baseTail,Bool.false_eq_true,if_false,if_true,
    FieldRename.rename_append,shifted_all_cell]

theorem tailProgram_run (divide : Bool) (s : State) (m : List Bool) :
    pullState (shifted pi0) (run (tailProgram divide) m s)=
      run (baseTail divide) m (pullState (shifted pi0) s) := by
  rw [tailProgram_eq_rename]
  exact run_rename _ (shifted pi0).injective _ m s

/-- Complete-State transport follows from the same derived clean boundary
as the packet placement, while all170 earlier groups remain encoded. -/
theorem tailProgram_state_eq (divide : Bool) (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀q,zeroRegion q → (run (baseTail divide) m s).basis (base q)=false) :
    run (tailProgram divide) m s=run (baseTail divide) m s := by
  have input := shifted_zero_boundary pi0 pi0_outside s hin
  have output := shifted_zero_boundary pi0 pi0_outside (run (baseTail divide) m s) hout
  apply pullState_perm_injective (shifted pi0)
  rw [tailProgram_run,input,output]

/-- Both last raw letters implement their exact original field update for
every independent measurement record, retaining the complete encoded frame. -/
theorem tailProgram_encoded_step (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) tailLetters)
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (tailProgram divide) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)).2 out := by
  have reference := encoded_tail_replay (!divide) base (base 2400) (base 2409) (base 2410)
    hn hlo ho hp 510 tailLetters (by omega) (by simp [tailLetters]) tailLetters_indexed
    hf origin hg0 hs0 env legal X Y s m input
  rw [←baseTail_eq_replay divide] at reference
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env _ _
    (run (baseTail divide) m s) reference.2
  have same := tailProgram_state_eq divide s m cleanIn cleanOut
  change (run (tailProgram divide) m s).phase=s.phase ∧ _
  rw [same]
  exact reference

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

theorem tailLetters_subset : ∀l∈tailLetters,l∈mixedTranscriptTape base := by
  intro l hl
  simp only [tailLetters,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl
  all_goals
    apply getD_member_MappedCompressedEncodedFrameLayout
    rw [mixedTranscriptTape_length]
    decide

/-- The last two raw cells need no separately assumed field layout. -/
theorem tail_layout (b sign eff : Wire)
    (hf : MixedTranscriptReplayLayout base b sign eff (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base b sign eff tailLetters :=
  layout_of_subset base b sign eff _ _ tailLetters_subset hf

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

/-- Exact measured composition with prefixes partitioned by actual counts. -/
theorem run_append_agreement (p r q v : Program) (s : State) (m : List Bool)
    (counts : measurementCount r=measurementCount p)
    (first : run p (m.take (measurementCount p)) s=run r (m.take (measurementCount p)) s)
    (second : run q (m.drop (measurementCount p)) (run p (m.take (measurementCount p)) s)=
      run v (m.drop (measurementCount p)) (run p (m.take (measurementCount p)) s)) :
    run (p++q) m s=run (r++v) m s := by
  rw [run_append,run_append,counts,←first]
  exact second
end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedReplayFrame.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run mappedGroups baseGroups tailProgram baseTail measurementCount
  mixedTranscriptTape mixedTranscriptUnitTrace packetLetters tailLetters

theorem mappedReplay_join (divide : Bool) : mappedReplay divide=
    (if divide then mappedGroups divide 0 170++tailProgram divide
     else tailProgram divide++mappedGroups divide 0 170) := by
  cases divide <;> simp only [mappedReplay,tailProgram,Bool.false_eq_true,if_false,if_true,List.append_assoc]

private theorem tail_complete (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) tailLetters)
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (tailProgram divide) m s=run (baseTail divide) m s ∧
    (run (tailProgram divide) m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)).2
      (run (tailProgram divide) m s) := by
  have out := tailProgram_encoded_step divide hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input
  have zeroIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have zeroOut := encoded_zero_region base (base 2409) hn hlo origin env _ _
    (run (tailProgram divide) m s) out.2
  have pin := shifted_zero_boundary pi0 pi0_outside s zeroIn
  have pout := shifted_zero_boundary pi0 pi0_outside (run (tailProgram divide) m s) zeroOut
  have eq := tailProgram_run divide s m
  rw [pin,pout] at eq
  exact ⟨eq,out⟩

/-- Every actual mapped cell, including the residual raw pair, agrees as a
complete State with the original exact full encoded reference replay. -/
theorem mappedReplay_reference (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : ∀k,k < 170 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters k))
    (ht : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) tailLetters)
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (mappedReplay divide) m s=run
      (if divide then compressedFieldForwardGroups base (base 2400) (base 2409) (base 2410)
       else compressedFieldBackwardGroups base (base 2400) (base 2409) (base 2410)) m s := by
  cases divide
  · let first := tailProgram false
    let t := run first (m.take (measurementCount first)) s
    have tail := tail_complete false hn hlo ho hp ht origin hg0 hs0 env legal X Y
      s (m.take (measurementCount first)) input
    simp only [Bool.not_false] at tail
    generalize hQ : directionalPayload true (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)=Q at tail
    have groups := mappedGroups_frame false 0 170 (by decide) hn hlo ho hp hf origin hg0 hs0 env legal
      Q.1 Q.2 t (m.drop (measurementCount first)) tail.2.2
    have countEq : measurementCount (baseTail false)=measurementCount first := by
      change measurementCount (baseTail false)=measurementCount (tailProgram false)
      rw [tailProgram_eq_rename]
      exact (renameProgram_counts (shifted pi0) (baseTail false)).2.symm
    rw [mappedReplay_join]
    simp only [Bool.false_eq_true,if_false]
    rw [←base_backward_replay_identity]
    exact run_append_agreement first (baseTail false) (mappedGroups false 0 170)
      (baseGroups false 0 170) s m countEq tail.1 groups.1
  · let first := mappedGroups true 0 170
    let t := run first (m.take (measurementCount first)) s
    have groups := mappedGroups_frame true 0 170 (by decide) hn hlo ho hp hf origin hg0 hs0 env legal
      X Y s (m.take (measurementCount first)) input
    generalize hQ : groupsPayload true origin 0 170 (X,Y)=Q at groups
    have tail := tail_complete true hn hlo ho hp ht origin hg0 hs0 env legal Q.1 Q.2
      t (m.drop (measurementCount first)) groups.2.2
    have countEq : measurementCount (baseGroups true 0 170)=measurementCount first :=
      (baseGroups_counts true 0 170).2.trans (mappedGroups_counts true 0 170).2.symm
    rw [mappedReplay_join]
    simp only [if_true]
    rw [←base_forward_replay_identity]
    exact run_append_agreement first (baseGroups true 0 170) (tailProgram true)
      (baseTail true) s m countEq groups.1 tail.1

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayCore.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run
private theorem short_programs_TerminalMappedReplayCore (w : Nat → Wire) (b sign eff : Wire) (i : Nat)
    (ls : List MixedTranscriptLetter) (h : ls.length ≤ 2) :
    codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) i ls =
      directionalReplay false w b sign eff ls ∧
    codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) i ls =
      directionalReplay true w b sign eff ls := by
  cases ls with
  | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
      OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
  | cons a ls =>
    cases ls with
    | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
        OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
    | cons c ls =>
      cases ls with
      | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
          OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
      | cons d tail => simp at h; omega
private theorem split_programs_TerminalMappedReplayCore {α : Type} (w : Nat → Wire) (cell : α → Program)
    (i : Nat) (a c d : α) (tail : List α) :
    codecGroupForward w cell i (a::c::d::tail) =
      codecGroupForward w cell i [a,c,d]++codecGroupForward w cell (i+3) tail ∧
    codecGroupBackward w cell i (a::c::d::tail) =
      codecGroupBackward w cell (i+3) tail++codecGroupBackward w cell i [a,c,d] := by
  simp only [codecGroupForward,codecGroupBackward,List.append_nil,List.nil_append,List.append_assoc]
  constructor <;> trivial
/-- Existing packet proof, with its universally framed raw tail instantiated
at one residual letter instead of two. No arithmetic primitive is changed. -/
theorem trim_grouped_encoded_replays (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base)
    (n j : Nat) (remaining : j+n=170) (ls : List MixedTranscriptLetter)
    (length : ls.length=3*n+1) (aligned : IndexedLetters w (3*j) ls)
    (hf : MixedTranscriptReplayLayout w b sign eff ls) :
    (∀ (X Y : Fp) (s : State) (m : List Bool), EncodedFieldFrame w sign base X Y s →
      let out := run (codecGroupForward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) ls) m s
      out.phase=s.phase ∧ EncodedFieldFrame w sign base
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2 out) ∧
    (∀ (X Y : Fp) (s : State) (m : List Bool), EncodedFieldFrame w sign base X Y s →
      let out := run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) ls) m s
      out.phase=s.phase ∧ EncodedFieldFrame w sign base
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).1
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).2 out) := by
  induction n generalizing j ls with
  | zero =>
    have ji : j=170 := by omega
    have len : ls.length=1 := by simpa using length
    have programs := short_programs_TerminalMappedReplayCore w b sign eff (3*j) ls (by omega)
    constructor
    · intro X Y s m input
      rw [programs.1]
      simpa only [directionalPayload,Bool.false_eq_true,if_false] using
        encoded_tail_replay false w b sign eff hn hlo ho hp (3*j) ls (by omega)
          (by omega) aligned hf base hg0 he0 env legal X Y s m input
    · intro X Y s m input
      rw [programs.2]
      simpa only [directionalPayload,if_true] using
        encoded_tail_replay true w b sign eff hn hlo ho hp (3*j) ls (by omega)
          (by omega) aligned hf base hg0 he0 env legal X Y s m input
  | succ n ih =>
    cases ls with
    | nil => simp at length
    | cons a rest =>
      cases rest with
      | nil => simp at length
      | cons c rest =>
        cases rest with
        | nil => simp at length
        | cons d tail =>
          have jj : j < 170 := by omega
          have next : IndexedLetters w (3*(j+1)) tail := by
            simpa only [Nat.mul_add,Nat.mul_one] using indexed_three_tail w (3*j) a c d tail aligned
          have lenTail : tail.length=3*n+1 := by simp only [List.length_cons] at length; omega
          have hfTail : MixedTranscriptReplayLayout w b sign eff tail := fun q hq => hf q (by simp [hq])
          have hfPacket : MixedTranscriptReplayLayout w b sign eff [a,c,d] := by
            intro q hq
            exact hf q (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using
              (show q=a ∨ q=c ∨ q=d ∨ q∈tail from by simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto))
          have controls := indexed_packet_controls w j jj (skywalkShared_integer_nodup w hn) hlo a c d tail aligned
          have support := packet_active_support w b sign eff (3*j) [a,c,d] controls
          have tailSpec := ih (j+1) (by omega) tail lenTail next hfTail
          have fwSplit := (split_programs_TerminalMappedReplayCore w (fun l : MixedTranscriptLetter =>
            OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) a c d tail).1
          have rvSplit := (split_programs_TerminalMappedReplayCore w (fun l : MixedTranscriptLetter =>
            OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) a c d tail).2
          constructor
          · intro X Y s m input
            let packet := codecGroupForward w (fun l : MixedTranscriptLetter =>
              OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]
            let t := run packet (m.take (measurementCount packet)) s
            let Q := skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)
            have first := encoded_forward_packet_step w b sign eff hn hlo j jj a c d hfPacket ho hp
              base hg0 he0 env legal X Y (by simpa only [rawForwardPacket] using support.1)
              s (m.take (measurementCount packet)) input
            have rest := tailSpec.1 Q.1 Q.2 t (m.drop (measurementCount packet)) first.2
            rw [fwSplit,run_append]
            change (run _ _ t).phase=s.phase ∧ _
            refine ⟨rest.1.trans first.1,?_⟩
            simpa only [mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,Q] using rest.2
          · intro X Y s m input
            let later := codecGroupBackward w (fun l : MixedTranscriptLetter =>
              OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j+3) tail
            let t := run later (m.take (measurementCount later)) s
            let Q := skywalkPayloadReplayInverse (mixedTranscriptControls base b tail) (X,Y)
            have rest := tailSpec.2 X Y s (m.take (measurementCount later)) input
            have first := encoded_backward_packet_step w b sign eff hn hlo j jj a c d hfPacket ho hp
              base hg0 he0 env legal Q.1 Q.2 (by simpa only [rawBackwardPacket] using support.2)
              t (m.drop (measurementCount later)) rest.2
            rw [rvSplit,run_append]
            change (run _ _ t).phase=s.phase ∧ _
            refine ⟨first.1.trans rest.1,?_⟩
            simpa only [mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q] using first.2

end ECDSAAdd.Arithmetic.CompressedFieldSupport
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayTrim.lean
noncomputable section

set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation
attribute [local irreducible] wires toffoliCount measurementCount logicalCell mappedGroups

/-- Only the field replay is trimmed. Integer recording and its170 codecs
remain unchanged; the single raw residual field letter is logical510. -/
def trimReplay (divide : Bool) : Program :=
  if divide then mappedGroups divide 0 170 ++ renameProgram allPlaced (logicalCell divide 510)
  else renameProgram allPlaced (logicalCell divide 510) ++ mappedGroups divide 0 170

theorem trimReplay_join (divide : Bool) :
    mappedReplay divide = if divide then trimReplay divide ++ renameProgram allPlaced (logicalCell divide 511)
      else renameProgram allPlaced (logicalCell divide 511) ++ trimReplay divide := by
  cases divide <;> simp only [mappedReplay,trimReplay,Bool.false_eq_true,if_false,if_true,List.append_assoc]

theorem trimReplay_support (divide : Bool) : wires (trimReplay divide) ⊆ slots.toFinset := by
  have full := mappedReplay_support divide
  cases divide <;> simp only [mappedReplay,trimReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff,and_assoc] at full ⊢
  · exact ⟨full.2.1,full.2.2⟩
  · exact ⟨full.1,full.2.1⟩

theorem trimReplay_counts (divide : Bool) :
    toffoliCount (trimReplay divide)=(if divide then 655270 else 655781) ∧ measurementCount (trimReplay divide)=523945 := by
  have groups := mappedGroups_counts divide 0 170
  have cell := logicalCell_counts divide 510
  have counts := renameProgram_counts allPlaced (logicalCell divide 510)
  cases divide <;> simp only [trimReplay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,counts.1,counts.2,
    groups.1,groups.2,cell.1,cell.2]
  all_goals norm_num

theorem trimReplay_count_saving (divide : Bool) :
    toffoliCount (mappedReplay divide)=toffoliCount (trimReplay divide)+(if divide then 1280 else 1281) ∧
    measurementCount (mappedReplay divide)=measurementCount (trimReplay divide)+1025 := by
  rw [(mappedReplay_counts divide).1,(mappedReplay_counts divide).2,
    (trimReplay_counts divide).1,(trimReplay_counts divide).2]
  cases divide <;> norm_num

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

def baseTrimReplay (divide : Bool) : Program :=
  if divide then baseGroups divide 0 170++renameProgram base (logicalCell divide 510)
  else renameProgram base (logicalCell divide 510)++baseGroups divide 0 170

private theorem reference_packet (divide : Bool) (j : Nat) (hj : j<170)
    (tail : List MixedTranscriptLetter) :
    referenceGroups divide (3*j) (packetLetters j++tail)=
      if divide then baseGroup divide j++referenceGroups divide (3*j+3) tail
      else referenceGroups divide (3*j+3) tail++baseGroup divide j := by
  rw [baseGroup_eq_reference divide j hj]
  cases divide <;> simp only [packetLetters,referenceGroups,Bool.false_eq_true,if_false,if_true,
    List.cons_append,List.nil_append,codecGroupForward,codecGroupBackward,
    List.append_nil,List.append_assoc]

private theorem baseTrim_reference (divide : Bool) (j n : Nat) (h : j+n=170) :
    (if divide then baseGroups divide j n++renameProgram base (logicalCell divide 510)
     else renameProgram base (logicalCell divide 510)++baseGroups divide j n)=
      referenceGroups divide (3*j) (indexedLetters (3*j) (3*n+1)) := by
  induction n generalizing j with
  | zero =>
    have hj : j=170 := by omega
    subst j
    have cell := referenceCell_letter divide 510 (by decide)
    have letters : indexedLetters 510 1=[tapeLetter 510] := by rfl
    cases divide <;> simp only [baseGroups,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,
      List.nil_append,List.append_nil,Bool.false_eq_true,if_false,if_true,letters,
      referenceGroups,codecGroupForward,codecGroupBackward,cell]
  | succ n ih =>
    have rest := ih (j+1) (by omega)
    have packet : indexedLetters (3*j) 3=packetLetters j := by
      simp [indexedLetters,packetLetters,tapeLetter,List.range_succ_eq_map]
    have split : indexedLetters (3*j) (3*(n+1)+1)=
        packetLetters j++indexedLetters (3*(j+1)) (3*n+1) := by
      rw [show 3*(n+1)+1=3+(3*n+1) by omega,indexedLetters_append,packet]
      rw [show 3*j+3=3*(j+1) by omega]
    rw [split,reference_packet divide j (by omega),show 3*j+3=3*(j+1) by omega]
    cases divide <;> simp only [baseGroups,Bool.false_eq_true,if_false,if_true] at rest ⊢
    all_goals rw [←rest]; simp only [List.append_assoc]

theorem baseTrimReplay_reference (divide : Bool) :
    baseTrimReplay divide=referenceGroups divide 0 trimLetters := by
  simpa only [baseTrimReplay,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,Nat.reduceAdd,trimLetters]
    using baseTrim_reference divide 0 170 (by decide)

private theorem indexed_prefix (w : Nat → Wire) (ls tail : List MixedTranscriptLetter)
    (i : Nat) (h : IndexedLetters w i (ls++tail)) : IndexedLetters w i ls := by
  induction ls generalizing i with
  | nil => trivial
  | cons l ls ih => exact ⟨h.1,ih (i+1) h.2⟩

theorem trimLetters_indexed : IndexedLetters base 0 trimLetters := by
  have h := mixedTape_indexed base
  rw [←trimLetters_last] at h
  exact indexed_prefix base trimLetters [tapeLetter 511] 0 h

theorem trimLetters_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) trimLetters := by
  intro l hl
  apply hf
  rw [←trimLetters_last]
  exact List.mem_append_left _ hl

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

theorem trimReplay_reference (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (trimReplay divide) m s=run (baseTrimReplay divide) m s := by
  cases divide
  · let first := renameProgram allPlaced (logicalCell false 510)
    let t := run first (m.take (measurementCount first)) s
    have tail := trimCell_step false hn hlo ho hp hf origin hg0 hs0 env legal X Y
      s (m.take (measurementCount first)) input
    generalize hQ : directionalPayload (!false)
      (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (X,Y)=Q at tail
    have groups := mappedGroups_frame false 0 170 (by decide) hn hlo ho hp (packet_layouts _ _ _ hf)
      origin hg0 hs0 env legal Q.1 Q.2 t (m.drop (measurementCount first)) tail.2.2
    have counts : measurementCount (renameProgram base (logicalCell false 510))=measurementCount first :=
      (renameProgram_counts base _).2.trans (renameProgram_counts allPlaced _).2.symm
    simpa only [trimReplay,baseTrimReplay,Bool.false_eq_true,if_false] using
      run_append_agreement first _ (mappedGroups false 0 170) (baseGroups false 0 170)
        s m counts tail.1 groups.1
  · let first := mappedGroups true 0 170
    let t := run first (m.take (measurementCount first)) s
    have groups := mappedGroups_frame true 0 170 (by decide) hn hlo ho hp (packet_layouts _ _ _ hf)
      origin hg0 hs0 env legal X Y s (m.take (measurementCount first)) input
    generalize hQ : groupsPayload true origin 0 170 (X,Y)=Q at groups
    have tail := trimCell_step true hn hlo ho hp hf origin hg0 hs0 env legal Q.1 Q.2
      t (m.drop (measurementCount first)) groups.2.2
    have counts : measurementCount (baseGroups true 0 170)=measurementCount first :=
      (baseGroups_counts true 0 170).2.trans (mappedGroups_counts true 0 170).2.symm
    simpa only [trimReplay,baseTrimReplay,if_true] using
      run_append_agreement first (baseGroups true 0 170) _ _ s m counts groups.1 tail.1

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

theorem convert_word_map (f : Wire → Wire) (L : BalancedConvert.Layout) :
    (mapConvert f L).word=L.word.map f := by
  simp [mapConvert,BalancedConvert.Layout.word]

theorem convert_correction_map (f : Wire → Wire) (L : BalancedConvert.Layout) :
    (BalancedConvert.correction L).map (mapBit f)=BalancedConvert.correction (mapConvert f L) := by
  simp only [BalancedConvert.correction,List.map_map]
  apply List.map_congr_left
  intro i _
  by_cases h : BalancedCircuit.sparseF.testBit i <;> simp [mapBit,mapConvert,h]

theorem literalConstSum_natural (f : Wire → Wire) (bit : Bool) (x cin : Wire) :
    renameProgram f (literalConstSum bit x cin)=literalConstSum bit (f x) (f cin) := by
  cases bit <;> rfl

theorem literalConstStep_natural (f : Wire → Wire) (bit : Bool) (x cin cout : Wire) :
    renameProgram f (literalConstStep bit x cin cout)=literalConstStep bit (f x) (f cin) (f cout) := by
  cases bit <;> rfl

theorem literalConstErase_natural (f : Wire → Wire) (bit : Bool) (x cin cout one : Wire) :
    renameProgram f (literalConstErase bit x cin cout one)=
      literalConstErase bit (f x) (f cin) (f cout) (f one) := by
  cases bit <;> rfl

theorem literalConstAdd_natural (f : Wire → Wire) (xs cs : List Wire) (cin one : Wire) (k : Nat) :
    renameProgram f (literalConstAdd xs cs cin one k)=
      literalConstAdd (xs.map f) (cs.map f) (f cin) (f one) k := by
  induction xs generalizing cs cin k with
  | nil => simp [literalConstAdd,renameProgram]
  | cons x xs ih =>
    cases xs with
    | nil => simpa only [literalConstAdd,List.map_cons,List.map_nil] using
        literalConstSum_natural f (decide (k%2=1)) x cin
    | cons y ys =>
      cases cs with
      | nil => simp [literalConstAdd,renameProgram]
      | cons c cs =>
        simp only [literalConstAdd,List.map_cons,rename_append,literalConstStep_natural,
          literalConstErase_natural,ih]

theorem xorConstant_natural (f : Wire → Wire) (xs : List Wire) (k : Nat) :
    renameProgram f (xorConstant xs k)=xorConstant (xs.map f) k := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : k%2=1
    · simp only [xorConstant,if_pos h,List.map_cons,rename_append,ih]
      rfl
    · simp only [xorConstant,if_neg h,List.map_cons,rename_append,ih]
      rfl

theorem compareChain_natural (f : Wire → Wire) (control : Option Wire)
    (xs ys cs : List Wire) (cin target : Wire) :
    renameProgram f (compareChain control xs ys cs cin target)=
      compareChain (control.map f) (xs.map f) (ys.map f) (cs.map f) (f cin) (f target) := by
  induction xs generalizing ys cs cin with
  | nil =>
    cases ys <;> cases cs <;> simp only [compareChain,List.map_nil,List.map_cons,renameProgram,List.map_nil]
    exact flipBelow_natural f control cin target
  | cons x xs ih =>
    cases ys with
    | nil => simp [compareChain,renameProgram]
    | cons y ys =>
      cases cs with
      | nil => simp [compareChain,renameProgram]
      | cons c cs => simp only [compareChain,List.map_cons,rename_append,majority_natural,eraseCarry_natural,ih]

theorem compareLt_natural (f : Wire → Wire) (control : Option Wire)
    (xs ys cs : List Wire) (cin target : Wire) :
    renameProgram f (compareLt control xs ys cs cin target)=
      compareLt (control.map f) (xs.map f) (ys.map f) (cs.map f) (f cin) (f target) := by
  simp only [compareLt,rename_append,notRegister_natural,compareChain_natural,List.map_cons]

theorem compareLtConst_natural (f : Wire → Wire) (control : Option Wire)
    (xs constant cs : List Wire) (cin target : Wire) (k : Nat) :
    renameProgram f (compareLtConst control xs constant cs cin target k)=
      compareLtConst (control.map f) (xs.map f) (constant.map f) (cs.map f) (f cin) (f target) k := by
  simp only [compareLtConst,rename_append,xorConstant_natural,compareLt_natural]

theorem convert_predicate_natural (f : Wire → Wire) (L : BalancedConvert.Layout) :
    renameProgram f (BalancedConvert.predicate L)=BalancedConvert.predicate (mapConvert f L) := by
  simp only [BalancedConvert.predicate,rename_append,literalConstAdd_natural,convert_word_map]
  rfl

theorem convert_center_natural (f : Wire → Wire) (L : BalancedConvert.Layout) :
    renameProgram f (BalancedConvert.center L)=BalancedConvert.center (mapConvert f L) := by
  simp only [BalancedConvert.center,rename_append,convert_predicate_natural,mappedAdd_natural,
    convert_word_map,convert_correction_map]
  rfl

theorem convert_canonical_natural (f : Wire → Wire) (L : BalancedConvert.Layout) :
    renameProgram f (BalancedConvert.canonical L)=BalancedConvert.canonical (mapConvert f L) := by
  simp only [BalancedConvert.canonical,rename_append,convert_predicate_natural,mappedSub_natural,
    convert_word_map,convert_correction_map]
  rfl

theorem sharedTargetConvert_map (f w : Wire → Wire) :
    mapConvert f (balancedSharedTargetConvert w)=balancedSharedTargetConvert (f ∘ w) := by
  simp only [mapConvert,balancedSharedTargetConvert,wireBlock_map,Function.comp_def]

theorem sharedSourceConvert_map (f w : Wire → Wire) :
    mapConvert f (balancedSharedSourceConvert w)=balancedSharedSourceConvert (f ∘ w) := by
  simp only [mapConvert,balancedSharedSourceConvert,wireBlock_map,Function.comp_def]

end ECDSAAdd.Arithmetic.FieldRename

namespace ECDSAAdd.Arithmetic.MappedCompressed
open FieldRename

def converterPairAt (w : Nat → Wire) (canonical : Bool) : Program :=
  if canonical then BalancedConvert.canonical (balancedSharedTargetConvert w)++
    BalancedConvert.canonical (balancedSharedSourceConvert w)
  else BalancedConvert.center (balancedSharedTargetConvert w)++
    BalancedConvert.center (balancedSharedSourceConvert w)

theorem converterPair_natural (f : Wire → Wire) (canonical : Bool) :
    renameProgram f (converterPair canonical)=converterPairAt f canonical := by
  cases canonical <;> simp only [converterPair,converterPairAt,Bool.false_eq_true,if_false,if_true,
    rename_append,convert_center_natural,convert_canonical_natural,
    sharedTargetConvert_map,sharedSourceConvert_map,Function.comp_id]

theorem base_converterPair_natural (canonical : Bool) :
    renameProgram base (converterPair canonical)=converterPairAt base canonical :=
  converterPair_natural base canonical

/-- The all-packed converter uses the same injective public pi0 placement
as the rest of the field boundary. This is exact program structure, including
every measurement correction; a zero-boundary state bridge is separate. -/
theorem allPlaced_converterPair_natural (canonical : Bool) :
    renameProgram allPlaced (converterPair canonical)=
      renameProgram (shifted CompressedAllocation.pi0) (converterPairAt base canonical) := by
  rw [←base_converterPair_natural,renameProgram_comp]
  have placement : shifted CompressedAllocation.pi0 ∘ base=allPlaced := by
    funext q
    exact shifted_base _ _
  rw [placement]

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

private theorem fp_bound (X : Fp) : X.val<2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])
private theorem word_bound (X : Fp) : centerWord X<2^256 := encodeWord_bound _ _
private theorem halve_double (X : Fp) : (2*X)/2=X := by
  have h : (2 : Fp)≠0 := by decide
  exact mul_div_cancel_left₀ X h

def centers (w : Nat → Wire) : Program := MappedCompressed.converterPairAt w false
def canonicals (w : Nat → Wire) : Program := MappedCompressed.converterPairAt w true
def selectedSwap (w : Nat → Wire) (b swap sign effS : Wire) (is : Bool) : Program :=
  transcriptSelectWindow b swap effS is
    (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
def oldEntry (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  dblInPlace (borrowedSkywalkUnary w) p++centers w++
    OffsetBorrowedCanonical.cell w b g swap sign effS ig is
def newEntry (w : Nat → Wire) (b swap sign effS : Wire) (is : Bool) : Program :=
  centers w++selectedSwap w b swap sign effS is

private theorem wide_lift (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base : BasisState) (br : base (w 2312)=false) (by0 : base (w 1026)=false)
    (I J O P : Nat) (hi : I<2^256) (hj : J<2^256) (code : Program)
    (proof : Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base I J) code
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base O P)) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base I J) code
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base O P) := by
  intro s m input
  rw [balancedSharedDivision_z,balancedSharedDivision_a] at input
  have narrow := balancedPair_narrow _ _ _ _ base s.basis I J
    (by simpa only [wireBlock_length] using hi) (by simpa only [wireBlock_length] using hj) input br by0
  have output := proof s m narrow
  have away := balancedSharedDivision_high_outside w hn
  have wide := balancedPair_widen _ _ _ _ base _ O P output.2 away.1 away.2 br by0
  rw [←balancedSharedDivision_z,←balancedSharedDivision_a] at wide
  exact ⟨output.1,wide⟩

private theorem boundary_frame (canonical : Bool) (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0) (hu : regValue (skywalkSharedUnused w) base=0)
    (br : base (w 2312)=false) (by0 : base (w 1026)=false) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
      (if canonical then centerWord X else X.val) (if canonical then centerWord Y else Y.val))
      (MappedCompressed.converterPairAt w canonical)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (if canonical then X.val else centerWord X) (if canonical then Y.val else centerWord Y)) := by
  let L := balancedSharedPorts w sign
  let D := balancedSharedBoundary w sign hn
  have clean := balancedSharedBoundary_clean w sign base hw hu
  cases canonical
  · have frame := balancedTranscriptCenterPair_frame L D base clean.1 clean.2 X Y
    have low : Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base X.val Y.val)
        (MappedCompressed.converterPairAt w false)
        (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base (centerWord X) (centerWord Y)) := by
      simpa only [L,D,balancedSharedPorts_r,balancedSharedPorts_y,balancedTranscriptCenterPair,
        balancedSharedBoundary,MappedCompressed.converterPairAt,Bool.false_eq_true,if_false] using frame
    exact wide_lift w hn base br by0 _ _ _ _ (fp_bound X) (fp_bound Y) _ low
  · have frame := balancedTranscriptCanonicalPair_frame L D base clean.1 clean.2 X Y
    have low : Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base (centerWord X) (centerWord Y))
        (MappedCompressed.converterPairAt w true)
        (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base X.val Y.val) := by
      simpa only [L,D,balancedSharedPorts_r,balancedSharedPorts_y,balancedTranscriptCanonicalPair,
        balancedSharedBoundary,MappedCompressed.converterPairAt,if_true] using frame
    exact wide_lift w hn base br by0 _ _ _ _ (word_bound X) (word_bound Y) _ low

private theorem swap_pair (r y : List Wire) (flag : Wire) (len : r.length=y.length)
    (nd : (flag::r++y).Nodup) (base : BasisState) (X Y : Nat) :
    Triple (PairFrame r y base X Y) (swapRegisters flag r y)
      (PairFrame r y base (if base flag then Y else X) (if base flag then X else Y)) := by
  intro s m input
  have out := swapRegisters_correct flag r y len nd s m
  have away := (List.nodup_cons.mp nd).1
  have same := input.2.2 flag (fun h => away (List.mem_append_left _ h))
    (fun h => away (List.mem_append_right _ h))
  refine ⟨out.1,?_,?_,fun q qr qy => (out.2.1 q qr qy).trans (input.2.2 q qr qy)⟩
  · rw [out.2.2.1,same,input.1,input.2.1]
  · rw [out.2.2.2,same,input.1,input.2.1]

private theorem swap_window_frame (w : Nat → Wire) (b g swap sign effS : Wire) (is : Bool)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (base : BasisState) (hs0 : base effS=false) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base (centerWord X) (centerWord Y))
      (selectedSwap w b swap sign effS is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if mixedTranscriptBit base b swap is then Y else X))
        (centerWord (if mixedTranscriptBit base b swap is then X else Y))) := by
  have controls := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at controls
  have nd : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have body := swap_pair _ _ effS (width.2.1.trans width.2.2.1.symm) hl.swapND
    (mixedTranscriptBase base b swap effS is) (centerWord X) (centerWord Y)
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at body
  have body' : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      (mixedTranscriptBase base b swap effS is) (centerWord X) (centerWord Y))
      (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        (mixedTranscriptBase base b swap effS is)
        (centerWord (if mixedTranscriptBit base b swap is then Y else X))
        (centerWord (if mixedTranscriptBit base b swap is then X else Y))) := by
    cases bit : mixedTranscriptBit base b swap is <;>
      simpa only [mixedTranscriptBase,writeBit,bit,if_true,if_false,Bool.false_eq_true] using body
  exact transcriptSelectWindow_pairFrame b swap effS is _ _ nd (hl.outside b (by simp))
    (hl.outside swap (by simp)) (hl.outside effS (by simp)) base hs0 _ _ _ _ _ body'

theorem entry_frames (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (hw : regValue (skywalkSharedField w).work base=0) (hu : regValue (skywalkSharedUnused w) base=0)
    (he : Env w base) (br : base (w 2312)=false) (by0 : base (w 1026)=false) (Y : Fp) :
    let post := PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
      (centerWord (if mixedTranscriptBit base b swap is then 0 else Y))
      (centerWord (if mixedTranscriptBit base b swap is then Y else 0))
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val 0)
      (oldEntry w b g swap sign effS ig is) post ∧
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val 0)
      (newEntry w b swap sign effS is) post := by
  have doubled := borrowedSkywalkUnary_double_frame w hn base hw hu Y 0
  have oldCenter := boundary_frame false w sign hn base hw hu br by0 (2*Y) 0
  have newCenter := boundary_frame false w sign hn base hw hu br by0 Y 0
  have cell := OffsetBorrowedCanonical.cell_frame w b g swap sign effS ig is hn hl ho hoS base hg0 hs0 he (2*Y) 0
  have lowCell : Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base (centerWord (2*Y)) (centerWord 0))
      (OffsetBorrowedCanonical.cell w b g swap sign effS ig is)
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
        (centerWord (if mixedTranscriptBit base b swap is then 0 else Y))
        (centerWord (if mixedTranscriptBit base b swap is then Y else 0))) := by
    cases bit : mixedTranscriptBit base b swap is <;>
      simpa only [balancedSharedPorts_r,balancedSharedPorts_y,skywalkPayloadCell,neg_zero,ite_self,
        add_zero,halve_double,bit,if_false,if_true,Bool.false_eq_true] using cell
  have wideCell := wide_lift w hn base br by0 _ _ _ _ (word_bound (2*Y)) (word_bound 0) _ lowCell
  have sw := swap_window_frame w b g swap sign effS is hl base hs0 Y 0
  have lowSwap := sw
  rw [balancedSharedPorts_r,balancedSharedPorts_y] at lowSwap
  have wideSwap := wide_lift w hn base br by0 _ _ _ _ (word_bound Y) (word_bound 0) _ lowSwap
  constructor
  · simpa only [oldEntry,ZMod.val_zero] using (doubled.seq oldCenter).seq wideCell
  · simpa only [newEntry,centers,ZMod.val_zero] using newCenter.seq wideSwap

/-- The extension zeros are derived from the actual canonical words. No
even-Y premise or extra caller-base semantic condition is introduced. -/
theorem entry_state_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (Y : Fp) (s : State) (mOld mNew : List Bool)
    (hg0 : s.basis sign=false) (hs0 : s.basis effS=false)
    (hw : regValue (skywalkSharedField w).work s.basis=0) (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hR : regValue (skywalkSharedField w).z s.basis=Y.val)
    (hY : regValue (skywalkSharedField w).a s.basis=0) :
    run (oldEntry w b g swap sign effS ig is) mOld s=run (newEntry w b swap sign effS is) mNew s := by
  have r := hR
  have y := hY
  rw [balancedSharedDivision_z] at r
  rw [balancedSharedDivision_a] at y
  have br := (balancedCanonical_high_zero _ _ s.basis Y.val
    (by simpa only [wireBlock_length] using fp_bound Y) r).2
  have by0 := (balancedCanonical_high_zero _ _ s.basis 0 (by simp [wireBlock_length]) y).2
  have env := env_of_canonical_source w hn s.basis 0 (by simpa using hY) hw hu
  have frames := entry_frames w b g swap sign effS ig is hn hl ho hoS s.basis hg0 hs0 hw hu env br by0 Y
  exact PairFrame.program_eq _ _ s.basis _ _ _ _ _ _ frames.1 frames.2 s mOld mNew
    ⟨hR,hY,fun _ _ _ => rfl⟩

theorem counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (effS::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup) :
    toffoliCount (oldEntry w b g swap sign effS ig is)=3321 ∧
    measurementCount (oldEntry w b g swap sign effS ig is)=3066 ∧
    toffoliCount (newEntry w b swap sign effS is)=1787 ∧
    measurementCount (newEntry w b swap sign effS is)=1531 := by
  have unary := modUnary_counts (borrowedSkywalkUnary w) 256 p (borrowedSkywalkUnary_widths w) (by omega)
  have target := BalancedConvert.counts (balancedSharedTargetConvert w) (balancedSharedTargetConvert_widths w)
  have source := BalancedConvert.counts (balancedSharedSourceConvert w) (balancedSharedSourceConvert_widths w)
  have cell := OffsetBorrowedCanonical.cell_counts w b g swap sign effS ig is hn
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have sw := swapRegisters_resources effS _ _ (width.2.1.trans width.2.2.1.symm) hn
  have selection := transcriptSelectWindow_counts b swap effS is
    (swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
  simp only [oldEntry,newEntry,centers,MappedCompressed.converterPairAt,Bool.false_eq_true,if_false,
    selectedSwap,toffoliCount_append,measurementCount_append,unary.1,unary.2.1,
    target.1,target.2.1,source.1,source.2.1,cell.1,cell.2,selection.1,selection.2,
    sw.1,sw.2.1,width.2.1]
  norm_num

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
private theorem emptyW : wires ([] : Program)=∅ := by simp [wires]
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

theorem fieldSegment_support (divide : Bool) :
    wires (fieldSegment divide) ⊆ slots.toFinset := by
  have rp := (replay_support_sub divide).trans (mappedReplay_support divide)
  have a := converters_support false
  have b := converters_support true
  cases divide <;> simp only [fieldSegment,Bool.false_eq_true,if_false,if_true,
    wires_append,emptyW,Finset.empty_union,Finset.union_empty,Finset.union_subset_iff,and_assoc]
  · exact ⟨copy_support,a,rp,b⟩
  · exact ⟨a,rp,b,copy_support⟩

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

private def converterSite (q : Nat) : Prop :=
  (770 ≤ q ∧ q ≤ 1027) ∨ (1540 ≤ q ∧ q ≤ 1797) ∨ (2056 ≤ q ∧ q ≤ 2311)

private theorem site_fixed (q : Nat) (h : converterSite q) : allPlaced q=base q := by
  change pi0 q+16=q+16
  rw [pi0_outside q]
  unfold converterSite zeroRegion workRegion holeRegion at *
  omega

private theorem block_fixed (start len : Nat)
    (hs : ∀q,start ≤ q → q < start+len → converterSite q) :
    wireBlock allPlaced start len=wireBlock base start len := by
  unfold wireBlock
  apply List.map_congr_left
  intro q hq
  have bound := List.mem_range'_1.mp hq
  exact site_fixed q (hs q bound.1 bound.2)

theorem target_conversion_placement :
    balancedSharedTargetConvert allPlaced=balancedSharedTargetConvert base := by
  have low := block_fixed 2056 255 (by intro q lo hi; unfold converterSite; omega)
  have carry := block_fixed 1540 255 (by intro q lo hi; unfold converterSite; omega)
  simp only [balancedSharedTargetConvert,low,carry,
    site_fixed 2311 (by unfold converterSite; omega),
    site_fixed 1797 (by unfold converterSite; omega),
    site_fixed 1027 (by unfold converterSite; omega),
    site_fixed 1796 (by unfold converterSite; omega)]

theorem source_conversion_placement :
    balancedSharedSourceConvert allPlaced=balancedSharedSourceConvert base := by
  have low := block_fixed 770 255 (by intro q lo hi; unfold converterSite; omega)
  have carry := block_fixed 1540 255 (by intro q lo hi; unfold converterSite; omega)
  simp only [balancedSharedSourceConvert,low,carry,
    site_fixed 1025 (by unfold converterSite; omega),
    site_fixed 1797 (by unfold converterSite; omega),
    site_fixed 1027 (by unfold converterSite; omega),
    site_fixed 1796 (by unfold converterSite; omega)]

/-- Boundary converters never borrow the omitted work positions or encoded
holes. The actual placement is therefore identical as a complete program. -/
theorem converterPair_placement (canonical : Bool) :
    renameProgram allPlaced (converterPair canonical)=converterPairAt base canonical := by
  rw [converterPair_natural]
  cases canonical <;> simp only [converterPairAt,Bool.false_eq_true,if_false,if_true,
    target_conversion_placement,source_conversion_placement]

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedConversionEncoding.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedFieldSupport
attribute [local irreducible] run wires converterPairAt allGroupEncode

private def conversionIds : List Nat := [1797,1027,1796,2311,1025]++
  List.range' 2056 255++List.range' 770 255++List.range' 1540 255

private theorem declared_conversion_support (target : Bool) :
    (if target then balancedSharedTargetConvert base else balancedSharedSourceConvert base).wires.toFinset ⊆
      (conversionIds.map base).toFinset := by
  intro q hq
  cases target <;>
    simp only [Bool.false_eq_true,if_false,if_true,balancedSharedTargetConvert,balancedSharedSourceConvert,
      BalancedConvert.Layout.wires,conversionIds,wireBlock,List.map_append,List.map_cons,List.map_nil,
      List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢ <;> tauto

private theorem conversion_support (canonical : Bool) :
    wires (converterPairAt base canonical) ⊆ (conversionIds.map base).toFinset := by
  have t := BalancedConvert.support (balancedSharedTargetConvert base)
  have u := BalancedConvert.support (balancedSharedSourceConvert base)
  have dt := declared_conversion_support true
  have ds := declared_conversion_support false
  cases canonical <;> simp only [converterPairAt,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff]
  · exact ⟨t.1.trans dt,u.1.trans ds⟩
  · exact ⟨t.2.trans dt,u.2.trans ds⟩

/-- The full history encoder and actual converters have disjoint support,
including every outcome-dependent correction site. -/
theorem encoder_conversion_disjoint (canonical : Bool) :
    Disjoint (wires (allGroupEncode base 170)) (wires (converterPairAt base canonical)) := by
  have hist := compressedPrefix_history_support base base_pool_nodup base_above 512 (by decide)
  rw [encode_prefix_512] at hist
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have history := List.mem_toFinset.mp (hist hq)
  have converted := List.mem_toFinset.mp (conversion_support canonical hc)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp converted
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp history
    have same := base_injective eq
    subst i
    simp only [List.mem_range'_1] at hi
    simp only [conversionIds,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    omega

/-- Conversion transports the entire encoded caller State, with arbitrary
independent encoder and conversion records and arbitrary incoming phase. -/
theorem encoder_conversion_commute (canonical : Bool) (s : State) (m n : List Bool) :
    run (converterPairAt base canonical) n (run (allGroupEncode base 170) m s)=
      run (allGroupEncode base 170) m (run (converterPairAt base canonical) n s) :=
  (run_disjoint_commute _ _ (encoder_conversion_disjoint canonical) m n s).symm

theorem mapped_converter_encoding (canonical : Bool) (s : State) (m n : List Bool) :
    run (renameProgram allPlaced (converterPair canonical)) n (run (allGroupEncode base 170) m s)=
      run (allGroupEncode base 170) m (run (converterPairAt base canonical) n s) := by
  rw [converterPair_placement]
  exact encoder_conversion_commute canonical s m n

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

theorem canonical_pair_work_zero (hn : (skywalkSharedWires base).Nodup)
    (origin current : BasisState) (X Y : Nat)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (frame : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X Y current) :
    regValue (skywalkSharedField base).work current=0 := by
  have full := skywalkShared_field_nodup base hn
  change ((skywalkSharedField base).a++(skywalkSharedField base).z++
    (skywalkSharedField base).work).Nodup at full
  have dis := (List.nodup_append'.mp full).2.2
  apply (regValue_zero _ _).mpr
  intro q hq
  have az : q∉(skywalkSharedField base).a ∧ q∉(skywalkSharedField base).z := by
    constructor
    · intro h; exact List.disjoint_left.mp dis (List.mem_append_left _ h) hq
    · intro h; exact List.disjoint_left.mp dis (List.mem_append_right _ h) hq
  exact (frame.2.2 q az.2 az.1).trans ((regValue_zero _ _).mp hw q hq)

theorem encoded_canonical_work_zero (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (X Y : Fp) (s : State) (frame : EncodedCanonicalFrame origin X Y s)
    (j : Nat) (hj : j < 170) : s.basis (base (W j))=false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have rawWork := canonical_pair_work_zero hn origin raw.basis _ _ hw rawFrame
  have zero := OffsetCleanupBorrowedCaller.maskBit_zero base raw.basis rawWork (W j)
    (by unfold W; omega) (by unfold W; omega)
  have pool := skywalkShared_integer_nodup base hn
  have hist := compressedPrefix_history_support base pool hlo 512 (by decide)
  rw [encode_prefix_512] at hist
  have away : base (W j)∉wires (allGroupEncode base 170) := by
    intro used
    have mem := List.mem_toFinset.mp (hist used)
    rcases List.mem_append.mp mem with mem|mem
    all_goals
      obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
      simp only [List.mem_range'_1] at hk
      have same := skywalkPool_index_inj base pool k (W j) (by omega) (by unfold W; omega) eq
      unfold W at same
      omega
  rw [encoded]
  exact (run_preserves_outside (allGroupEncode base 170) [] raw _ away).trans zero

/-- Allocation work and codec holes are derived from the full canonical
frame and existing caller cleanliness, without an additional zero bank. -/
theorem encoded_canonical_zero_region (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (_hu : regValue (skywalkSharedUnused base) origin=0)
    (X Y : Fp) (s : State) (frame : EncodedCanonicalFrame origin X Y s) :
    ∀q,zeroRegion q → s.basis (base q)=false := by
  intro q hq
  rcases hq with work|hole
  · have index : q=W (q-515) := by unfold workRegion W at *; omega
    have bound : q-515 < 170 := by unfold workRegion at work; omega
    rw [index]
    exact encoded_canonical_work_zero hn hlo origin hw X Y s frame _ bound
  · have index : q=H ((q-1029)/3) := by unfold holeRegion H at *; omega
    have bound : (q-1029)/3 < 170 := by unfold holeRegion at hole; omega
    obtain ⟨raw,_,_,encoded⟩ := frame
    rw [encoded,index]
    exact allGroupEncode_holes_zero base (skywalkShared_integer_nodup base hn) hlo
      170 (by decide) raw [] _ bound

private theorem port_split (sign : Wire) :
    (skywalkSharedField base).z=(balancedSharedPorts base sign).r++[base 2312] ∧
    (skywalkSharedField base).a=(balancedSharedPorts base sign).y++[base 1026] := by
  rw [skywalkShared_field_z,balancedSharedPorts_r,balancedSharedPorts_y]
  constructor
  · have split := wireBlock_append base 2056 256 1
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using split.symm
  · have split := wireBlock_append base 770 256 1
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using split.symm

private theorem value_bound (X : Fp) : X.val < 2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

private theorem conversion_transport (canonical : Bool) (s raw : State) (m : List Bool)
    (encoded : s=run (allGroupEncode base 170) [] raw)
    (phase : (run (converterPairAt base canonical) m raw).phase=raw.phase) :
    (run (converterPairAt base canonical) m s).phase=s.phase ∧
    run (converterPairAt base canonical) m s=
      run (allGroupEncode base 170) [] (run (converterPairAt base canonical) m raw) := by
  have dis := encoder_conversion_disjoint canonical
  have read : ∀q∈wires (converterPairAt base canonical),s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment (converterPairAt base canonical) s raw m read).1
  rw [phase,Bool.xor_self] at increment
  refine ⟨xor_neutral _ _ increment,?_⟩
  rw [encoded]
  exact encoder_conversion_commute canonical raw [] m

/-- Actual converter entry, retaining the same caller origin. Its high-zero
facts come from canonical origin ports, not from a low-word assertion. -/
theorem encoded_center_pair (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    (run (converterPairAt base false) m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin X Y (run (converterPairAt base false) m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  let L := balancedSharedPorts base (base 2409)
  let D := balancedSharedBoundary base (base 2409) hn
  have split := port_split (base 2409)
  rw [split.1,split.2] at frame
  have narrow := balancedPair_narrow L.r L.y (base 2312) (base 1026) origin raw.basis
    X.val Y.val (by simpa only [L,balancedSharedPorts_r,wireBlock_length] using value_bound X)
    (by simpa only [L,balancedSharedPorts_y,wireBlock_length] using value_bound Y) frame hr hy
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have result := balancedTranscriptCenterPair_frame L D origin clean.1 clean.2 X Y raw m narrow
  change (run (converterPairAt base false) m raw).phase=raw.phase ∧ _ at result
  have actual := conversion_transport false s raw m encoded result.1
  refine ⟨actual.1,run (converterPairAt base false) m raw,
    result.1.trans (phase.trans actual.1.symm),result.2,actual.2⟩

/-- Actual converter exit widens back to both original257-bit ports. -/
theorem encoded_canonical_pair (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    (run (converterPairAt base true) m s).phase=s.phase ∧
    EncodedCanonicalFrame origin X Y (run (converterPairAt base true) m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  let L := balancedSharedPorts base (base 2409)
  let D := balancedSharedBoundary base (base 2409) hn
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have result := balancedTranscriptCanonicalPair_frame L D origin clean.1 clean.2 X Y raw m frame
  change (run (converterPairAt base true) m raw).phase=raw.phase ∧ _ at result
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen L.r L.y (base 2312) (base 1026) origin _ X.val Y.val
    result.2 (by simpa only [L,balancedSharedPorts_r,balancedSharedPorts_y] using outside.1)
    (by simpa only [L,balancedSharedPorts_r,balancedSharedPorts_y] using outside.2) hr hy
  have split := port_split (base 2409)
  rw [←split.1,←split.2] at wide
  have actual := conversion_transport true s raw m encoded result.1
  refine ⟨actual.1,run (converterPairAt base true) m raw,
    result.1.trans (phase.trans actual.1.symm),wide,actual.2⟩

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

theorem copyPair_natural (f : Nat → Wire) :
    renameProgram f (copyPairAt id)=copyPairAt f := by
  simp only [copyPairAt,copyRegister_natural,skywalkShared_field_z,wireBlock_map,
    Option.map_none,Function.comp_id]
  rfl

private theorem block_fixed_MappedCompressedCopyEndpoint (start len : Nat)
    (hs : ∀q,start ≤ q → q < start+len → ¬zeroRegion q) :
    wireBlock allPlaced start len=wireBlock base start len := by
  unfold wireBlock
  apply List.map_congr_left
  intro q hq
  have range := List.mem_range'_1.mp hq
  change pi0 q+16=q+16
  rw [pi0_outside q (hs q range.1 range.2)]

/-- Both full257-bit copy words lie outside every reassigned role. -/
theorem copyPair_placement : renameProgram allPlaced (copyPairAt id)=copyPairAt base := by
  rw [copyPair_natural]
  have z := block_fixed_MappedCompressedCopyEndpoint 2056 257
    (by intro q lo hi; unfold zeroRegion workRegion holeRegion; omega)
  have a := block_fixed_MappedCompressedCopyEndpoint 770 257
    (by intro q lo hi; unfold zeroRegion workRegion holeRegion; omega)
  simp only [copyPairAt,skywalkShared_field_z]
  change copyRegister none (wireBlock allPlaced 2056 257) (wireBlock allPlaced 770 257)=
    copyRegister none (wireBlock base 2056 257) (wireBlock base 770 257)
  rw [z,a]

theorem copyPair_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState) (X Y : Nat) :
    Triple (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X Y)
      (copyPairAt base)
      (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X (Y^^^X)) := by
  have widths := skywalkShared_field_widths base
  have length : (skywalkSharedField base).z.length=(skywalkSharedField base).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,widths.core.low,widths.core.a]
  have nd := skywalkShared_field_nodup base hn
  have pair : ((skywalkSharedField base).z++(skywalkSharedField base).a).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have full := List.nodup_iff_count.mp nd q
    simp only [ModInPlaceLayout.wires,List.count_append] at full ⊢
    omega
  have dis := (List.nodup_append'.mp pair).2.2
  intro s m input
  obtain ⟨phase,keep,value⟩ := copyRegister_correct none (skywalkSharedField base).z
    (skywalkSharedField base).a length pair (by simp) s m
  refine ⟨phase,PairFrame.update_dst _ _ origin s.basis _ X Y _ dis input keep ?_⟩
  simpa only [copyValue,input.1,input.2.1] using value

/-- Exact retained endpoint operations: populate a clean source, or erase
the equal source after division. Incoming phase and every outsider restore. -/
theorem copyPair_fill (hn : (skywalkSharedWires base).Nodup) (origin : BasisState) (X : Fp) :
    Triple (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val 0)
      (copyPairAt base)
      (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val X.val) := by
  simpa only [Nat.zero_xor] using copyPair_frame hn origin X.val 0

theorem copyPair_clear (hn : (skywalkSharedWires base).Nodup) (origin : BasisState) (X : Fp) :
    Triple (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val X.val)
      (copyPairAt base)
      (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val 0) := by
  simpa only [Nat.xor_self] using copyPair_frame hn origin X.val X.val

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedUnaryNaturality.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] addInPlace subInPlace compareLt compareLtConst
attribute [local irreducible] maskedConstant xorConstant maskedAddConst maskedSubConst

def mapModUnary (f : Wire → Wire) (U : ModUnaryLayout) : ModUnaryLayout :=
  {low:=U.low.map f,high:=f U.high,constant:=U.constant.map f,
   carry:=U.carry.map f,cin:=f U.cin,mask:=U.mask.map f,flag:=f U.flag}

theorem modUnary_z_map (f : Wire → Wire) (U : ModUnaryLayout) :
    (mapModUnary f U).z=U.z.map f := by
  simp [mapModUnary,ModUnaryLayout.z]

/-- Both the nonempty head and the fallback high wire are relabeled. -/
theorem modUnary_bit_map (f : Wire → Wire) (U : ModUnaryLayout) :
    (mapModUnary f U).bit=f U.bit := by
  cases h : U.low <;> simp [ModUnaryLayout.bit,mapModUnary,h]

theorem take_natural (f : Wire → Wire) (r : List Wire) (n : Nat) :
    (r.take n).map f=(r.map f).take n := by
  induction n generalizing r with
  | zero => simp
  | succ n ih => cases r <;> simp [ih]

theorem maskedConstant_natural (f : Wire → Wire) (control : Wire) (r : List Wire) (k : Nat) :
    renameProgram f (maskedConstant control r k)=maskedConstant (f control) (r.map f) k := by
  induction r generalizing k with
  | nil => simp [maskedConstant,renameProgram]
  | cons x xs ih =>
    by_cases h : k%2=1
    · simp only [maskedConstant,if_pos h,List.map_cons,rename_append,ih]
      rfl
    · simp only [maskedConstant,if_neg h,List.map_cons,rename_append,ih]
      rfl

theorem maskedAddConst_natural (f : Wire → Wire) (control : Wire)
    (constant target carry : List Wire) (cin : Wire) (k : Nat) :
    renameProgram f (maskedAddConst control constant target carry cin k)=
      maskedAddConst (f control) (constant.map f) (target.map f) (carry.map f) (f cin) k := by
  simp only [maskedAddConst,rename_append,maskedConstant_natural,addInPlace_natural]

theorem maskedSubConst_natural (f : Wire → Wire) (control : Wire)
    (constant target carry : List Wire) (cin : Wire) (k : Nat) :
    renameProgram f (maskedSubConst control constant target carry cin k)=
      maskedSubConst (f control) (constant.map f) (target.map f) (carry.map f) (f cin) k := by
  simp only [maskedSubConst,rename_append,maskedConstant_natural,subInPlace_natural]

theorem dblInPlace_natural (f : Wire → Wire) (U : ModUnaryLayout) (p : Nat) :
    renameProgram f (dblInPlace U p)=dblInPlace (mapModUnary f U) p := by
  simp only [dblInPlace,rename_append,rotateLeft_natural,xorConstant_natural,
    subInPlace_natural,maskedAddConst_natural,modUnary_z_map,modUnary_bit_map]
  simp only [mapModUnary,List.length_map,take_natural]
  rfl

theorem halfInPlace_natural (f : Wire → Wire) (U : ModUnaryLayout) (p : Nat) :
    renameProgram f (halfInPlace U p)=halfInPlace (mapModUnary f U) p := by
  simp only [halfInPlace,rename_append,maskedAddConst_natural,rotateRight_natural,
    compareLtConst_natural,modUnary_z_map,modUnary_bit_map,Option.map_none]
  simp only [mapModUnary,List.length_map,take_natural]
  rfl

theorem borrowedUnary_map (f w : Wire → Wire) :
    mapModUnary f (borrowedSkywalkUnary w)=borrowedSkywalkUnary (f ∘ w) := by
  simp only [mapModUnary,borrowedSkywalkUnary,wireBlock_map,Function.comp_def]

theorem borrowed_dbl_natural (f : Wire → Wire) (p : Nat) :
    renameProgram f (dblInPlace (borrowedSkywalkUnary id) p)=dblInPlace (borrowedSkywalkUnary f) p := by
  rw [dblInPlace_natural,borrowedUnary_map,Function.comp_id]

theorem borrowed_half_natural (f : Wire → Wire) (p : Nat) :
    renameProgram f (halfInPlace (borrowedSkywalkUnary id) p)=halfInPlace (borrowedSkywalkUnary f) p := by
  rw [halfInPlace_natural,borrowedUnary_map,Function.comp_id]

end ECDSAAdd.Arithmetic.FieldRename

namespace ECDSAAdd.Arithmetic.MappedCompressed
open FieldRename Secp256k1

/-- Public all-packed placement maps every gate and correction of each
endpoint, with the modulus and all classical constant bits preserved. -/
theorem allPlaced_dbl_natural :
    renameProgram allPlaced (dblInPlace (borrowedSkywalkUnary id) p)=
      renameProgram (shifted CompressedAllocation.pi0) (dblInPlace (borrowedSkywalkUnary base) p) := by
  rw [←borrowed_dbl_natural base,renameProgram_comp]
  have placement : shifted CompressedAllocation.pi0 ∘ base=allPlaced := by
    funext q
    exact shifted_base _ _
  rw [placement]

theorem allPlaced_half_natural :
    renameProgram allPlaced (halfInPlace (borrowedSkywalkUnary id) p)=
      renameProgram (shifted CompressedAllocation.pi0) (halfInPlace (borrowedSkywalkUnary base) p) := by
  rw [←borrowed_half_natural base,renameProgram_comp]
  have placement : shifted CompressedAllocation.pi0 ∘ base=allPlaced := by
    funext q
    exact shifted_base _ _
  rw [placement]

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

private def endpointRegion (q : Nat) : Prop :=
  (512 ≤ q ∧ q ≤ 1027) ∨ (1540 ≤ q ∧ q ≤ 1797) ∨ (2056 ≤ q ∧ q ≤ 2312)

private def unaryIds : List Nat := List.range' 2056 256++[2312]++
  List.range' 512 257++List.range' 1540 256++[1797,769]
private def copyIds : List Nat := List.range' 2056 257++List.range' 770 257

private theorem unary_region (q : Nat) (h : q∈unaryIds) : endpointRegion q := by
  simp only [unaryIds,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
    or_false,or_assoc] at h
  rcases h with h|rfl|h|h|rfl|rfl
  · exact Or.inr (Or.inr (by omega))
  · norm_num [endpointRegion]
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · norm_num [endpointRegion]
  · norm_num [endpointRegion]

private theorem copy_region (q : Nat) (h : q∈copyIds) : endpointRegion q := by
  simp only [copyIds,List.mem_append,List.mem_range'_1] at h
  rcases h with h|h
  · exact Or.inr (Or.inr (by omega))
  · exact Or.inl (by omega)

private theorem endpoint_unary_history_support (divide : Bool) :
    wires (if divide then dblInPlace (borrowedSkywalkUnary base) p
      else halfInPlace (borrowedSkywalkUnary base) p)⊆(unaryIds.map base).toFinset := by
  have counts := modUnary_wires (borrowedSkywalkUnary base) 256 p
    (borrowedSkywalkUnary_widths base) (by omega)
  have view : ((borrowedSkywalkUnary base).z++(borrowedSkywalkUnary base).core.work++
      [(borrowedSkywalkUnary base).flag])=unaryIds.map base := by
    change (wireBlock base 2056 256++[base 2312])++
      (wireBlock base 512 257++wireBlock base 1540 256++[base 1797])++[base 769]=_
    simp [unaryIds,wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [←view]
  cases divide
  · simp only [Bool.false_eq_true,if_false] at hq
    rw [counts.2] at hq
    exact hq
  · simp only [if_true] at hq
    rw [counts.1] at hq
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hq))

private theorem endpoint_copy_history_support : wires (copyPairAt base)⊆(copyIds.map base).toFinset := by
  have support := copyRegister_wires_subset none (skywalkSharedField base).z (skywalkSharedField base).a
  have view : (none : Option Wire).toList++(skywalkSharedField base).z++
      (skywalkSharedField base).a=copyIds.map base := by
    rw [skywalkShared_field_z]
    change []++wireBlock base 2056 257++wireBlock base 770 257=_
    simp [copyIds,wireBlock,List.map_append]
  intro q hq
  change q∈wires (copyRegister none (skywalkSharedField base).z (skywalkSharedField base).a) at hq
  have h := support hq
  rw [view] at h
  exact h

/-- Actual instruction support, including encoder and endpoint corrections.
Every endpoint site is outside both complete512-bit history rails. -/
private theorem encoder_away (P : Program) (ids : List Nat)
    (support : wires P⊆(ids.map base).toFinset)
    (outside : ∀q∈ids,endpointRegion q) :
    Disjoint (wires (allGroupEncode base 170)) (wires P) := by
  have hist := compressedPrefix_history_support base base_pool_nodup base_above 512 (by decide)
  rw [encode_prefix_512] at hist
  apply Finset.disjoint_left.mpr
  intro q he hp
  have history := List.mem_toFinset.mp (hist he)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (support hp))
  have region := outside j hj
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,equal⟩ := List.mem_map.mp history
    have same := base_injective equal
    subst i
    simp only [List.mem_range'_1] at hi
    rcases region with region|region|region <;> omega

theorem encoder_unary_disjoint (divide : Bool) :
    Disjoint (wires (allGroupEncode base 170))
      (wires (if divide then dblInPlace (borrowedSkywalkUnary base) p
        else halfInPlace (borrowedSkywalkUnary base) p)) :=
  encoder_away _ unaryIds (endpoint_unary_history_support divide) unary_region

theorem encoder_copy_disjoint :
    Disjoint (wires (allGroupEncode base 170)) (wires (copyPairAt base)) :=
  encoder_away _ copyIds endpoint_copy_history_support copy_region

/-- Complete State equality holds for arbitrary independent measurement
record lists and arbitrary incoming phase. -/
theorem encoder_unary_commute (divide : Bool) (s : State) (m n : List Bool) :
    run (if divide then dblInPlace (borrowedSkywalkUnary base) p
      else halfInPlace (borrowedSkywalkUnary base) p) n (run (allGroupEncode base 170) m s)=
    run (allGroupEncode base 170) m
      (run (if divide then dblInPlace (borrowedSkywalkUnary base) p
        else halfInPlace (borrowedSkywalkUnary base) p) n s) :=
  (run_disjoint_commute _ _ (encoder_unary_disjoint divide) m n s).symm

theorem encoder_copy_commute (s : State) (m n : List Bool) :
    run (copyPairAt base) n (run (allGroupEncode base 170) m s)=
      run (allGroupEncode base 170) m (run (copyPairAt base) n s) :=
  (run_disjoint_commute _ _ encoder_copy_disjoint m n s).symm

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedEncodedEndpoints.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode dblInPlace halfInPlace copyRegister

private theorem xor_neutral_MappedCompressedEncodedEndpoints (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

private theorem encoded_endpoint (P : Program)
    (dis : Disjoint (wires (allGroupEncode base 170)) (wires P))
    (origin : BasisState) (X Y A B : Fp)
    (correct : Triple (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
        origin X.val Y.val) P
      (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin A.val B.val))
    (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    (run P m s).phase=s.phase ∧ EncodedCanonicalFrame origin A B (run P m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have result := correct raw m frame
  have read : ∀q∈wires P,s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment P s raw m read).1
  rw [result.1,Bool.xor_self] at increment
  have actualPhase := xor_neutral_MappedCompressedEncodedEndpoints _ _ increment
  have actual : run P m s=run (allGroupEncode base 170) [] (run P m raw) := by
    rw [encoded]
    exact (run_disjoint_commute _ _ dis [] m raw).symm
  exact ⟨actualPhase,run P m raw,result.1.trans (phase.trans actualPhase.symm),result.2,actual⟩

/-- Actual base unary emission preserves the entire encoded canonical
frame for all field inputs and independent measurement records. -/
theorem encoded_unary_step (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    let P := if divide then dblInPlace (borrowedSkywalkUnary base) p
      else halfInPlace (borrowedSkywalkUnary base) p
    (run P m s).phase=s.phase ∧
      EncodedCanonicalFrame origin (if divide then 2*X else X/2) Y (run P m s) := by
  cases divide
  · exact encoded_endpoint _ (encoder_unary_disjoint false) origin X Y (X/2) Y
      (borrowedSkywalkUnary_half_frame base hn origin hw hu X Y) s m input
  · exact encoded_endpoint _ (encoder_unary_disjoint true) origin X Y (2*X) Y
      (borrowedSkywalkUnary_double_frame base hn origin hw hu X Y) s m input

private theorem placed_endpoint_state_eq (P : Program) (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀q,zeroRegion q → (run P m s).basis (base q)=false) :
    run (renameProgram (shifted pi0) P) m s=run P m s := by
  have input := shifted_zero_boundary pi0 pi0_outside s hin
  have output := shifted_zero_boundary pi0 pi0_outside (run P m s) hout
  have same := run_rename (shifted pi0) (shifted pi0).injective P m s
  rw [input] at same
  apply pullState_perm_injective (shifted pi0)
  exact same.trans output.symm

theorem mapped_unary_state_eq (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    run (renameProgram allPlaced (if divide then dblInPlace (borrowedSkywalkUnary id) p
        else halfInPlace (borrowedSkywalkUnary id) p)) m s=
      run (if divide then dblInPlace (borrowedSkywalkUnary base) p
        else halfInPlace (borrowedSkywalkUnary base) p) m s := by
  let P := if divide then dblInPlace (borrowedSkywalkUnary base) p
    else halfInPlace (borrowedSkywalkUnary base) p
  have reference := encoded_unary_step divide hn origin hw hu X Y s m input
  have cleanIn := encoded_canonical_zero_region hn hlo origin hw hu X Y s input
  have cleanOut := encoded_canonical_zero_region hn hlo origin hw hu _ Y (run P m s) reference.2
  have same := placed_endpoint_state_eq P s m cleanIn cleanOut
  cases divide
  · simp only [Bool.false_eq_true,if_false]
    rw [allPlaced_half_natural]
    exact same
  · simp only [if_true]
    rw [allPlaced_dbl_natural]
    exact same

/-- Physical low-width unary endpoint, with both placement boundaries
derived from the encoded frame instead of a new clean-bank premise. -/
theorem mapped_unary_step (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    let P := renameProgram allPlaced (if divide then dblInPlace (borrowedSkywalkUnary id) p
      else halfInPlace (borrowedSkywalkUnary id) p)
    (run P m s).phase=s.phase ∧
      EncodedCanonicalFrame origin (if divide then 2*X else X/2) Y (run P m s) := by
  have same := mapped_unary_state_eq divide hn hlo origin hw hu X Y s m input
  dsimp only
  rw [same]
  exact encoded_unary_step divide hn origin hw hu X Y s m input

/-- Populate the original full source port, preserving all encoded history. -/
theorem encoded_copy_fill (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (X : Fp) (s : State) (m : List Bool)
    (input : EncodedCanonicalFrame origin X 0 s) :
    (run (copyPairAt base) m s).phase=s.phase ∧
      EncodedCanonicalFrame origin X X (run (copyPairAt base) m s) := by
  apply encoded_endpoint _ encoder_copy_disjoint origin X 0 X X _ s m input
  simpa only [ZMod.val_zero] using copyPair_fill hn origin X

/-- The equal retained source port is cleared by the actual XOR copy. -/
theorem encoded_copy_clear (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (X : Fp) (s : State) (m : List Bool)
    (input : EncodedCanonicalFrame origin X X s) :
    (run (copyPairAt base) m s).phase=s.phase ∧
      EncodedCanonicalFrame origin X 0 (run (copyPairAt base) m s) := by
  apply encoded_endpoint _ encoder_copy_disjoint origin X X X 0 _ s m input
  simpa only [ZMod.val_zero] using copyPair_clear hn origin X

theorem mapped_copy_fill (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (X : Fp) (s : State) (m : List Bool)
    (input : EncodedCanonicalFrame origin X 0 s) :
    (run (renameProgram allPlaced (copyPairAt id)) m s).phase=s.phase ∧
      EncodedCanonicalFrame origin X X (run (renameProgram allPlaced (copyPairAt id)) m s) := by
  rw [copyPair_placement]
  exact encoded_copy_fill hn origin X s m input

theorem mapped_copy_clear (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (X : Fp) (s : State) (m : List Bool)
    (input : EncodedCanonicalFrame origin X X s) :
    (run (renameProgram allPlaced (copyPairAt id)) m s).phase=s.phase ∧
      EncodedCanonicalFrame origin X 0 (run (renameProgram allPlaced (copyPairAt id)) m s) := by
  rw [copyPair_placement]
  exact encoded_copy_clear hn origin X s m input

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

/-- Encoding does not weaken the complete outside-register frame. Equal
payloads and physical phases identify one complete encoded State. -/
theorem encoded_field_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : EncodedFieldFrame base (base 2409) origin X Y s)
    (ht : EncodedFieldFrame base (base 2409) origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩ := hs
  obtain ⟨b,hb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

theorem encoded_canonical_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : EncodedCanonicalFrame origin X Y s)
    (ht : EncodedCanonicalFrame origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩ := hs
  obtain ⟨b,hb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

/-- The accepted leaf cancellation can be followed by actual remaining
cell instructions and the full encoder with one common suffix stream.
This statement makes no claim that the seed commutes with a decoder. -/
theorem raw_entry_suffix_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (Y : Fp) (s : State) (mOld mNew mSuffix : List Bool) (suffix : Program)
    (hg0 : s.basis sign=false) (hs0 : s.basis effS=false)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hR : regValue (skywalkSharedField w).z s.basis=Y.val)
    (hY : regValue (skywalkSharedField w).a s.basis=0) :
    run (allGroupEncode w 170) []
      (run suffix mSuffix (run (EntryFieldSeedCancellation.oldEntry w b g swap sign effS ig is) mOld s))=
    run (allGroupEncode w 170) []
      (run suffix mSuffix (run (EntryFieldSeedCancellation.newEntry w b swap sign effS is) mNew s)) := by
  rw [EntryFieldSeedCancellation.entry_state_eq w b g swap sign effS ig is hn hl ho hoS
    Y s mOld mNew hg0 hs0 hw hu hR hY]

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
attribute [local irreducible] run mappedReplay compressedFieldForwardGroups compressedFieldBackwardGroups
  mixedTranscriptTape mixedTranscriptUnitTrace directionalPayload

/-- The entire actual512-cell mapped forward or inverse circuit realizes
the original field replay, with exact incoming phase and encoded workspace.
Packet and residual layouts are derived from the original full tape. -/
theorem mappedReplay_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (mappedReplay divide) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).2 out := by
  have eq := mappedReplay_reference divide hn hlo ho hp
    (packet_layouts _ _ _ hf) (tail_layout _ _ _ hf) origin hg0 hs0 env legal X Y s m input
  have spec := compressedFieldGroups_512_frame base (base 2400) (base 2409) (base 2410)
    hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input
  cases divide
  · rw [eq]
    simpa only [Bool.false_eq_true,if_false,Bool.not_false,directionalPayload,if_true] using spec.2
  · rw [eq]
    simpa only [if_true,Bool.not_true,directionalPayload,Bool.false_eq_true,if_false] using spec.1

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayTrimProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run trimReplay baseTrimReplay mappedReplay mixedTranscriptTape
  mixedTranscriptUnitTrace directionalPayload indexedLetters trimLetters

/-- The511 actual field cells retain the full fixed170-group encoding,
including phase and every work/control/source-frame bit. -/
theorem trimReplay_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (trimReplay divide) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) trimLetters) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) trimLetters) (X,Y)).2 out := by
  have eq := trimReplay_reference divide hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input
  have len : trimLetters.length=3*170+1 := by
    simp only [trimLetters,indexedLetters,List.length_map,List.length_range]
  have ref := trim_grouped_encoded_replays base (base 2400) (base 2409) (base 2410)
    hn hlo ho hp origin hg0 hs0 env legal 170 0 (by decide) trimLetters len trimLetters_indexed
    (trimLetters_layout hf)
  rw [eq,baseTrimReplay_reference]
  cases divide
  · simpa only [referenceGroups,referenceCell,Bool.false_eq_true,if_false,Bool.not_false,
      directionalPayload,if_true] using ref.2 X Y s m input
  · simpa only [referenceGroups,referenceCell,if_true,Bool.not_true,directionalPayload,
      Bool.false_eq_true,if_false] using ref.1 X Y s m input

private theorem encoded_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (phase : s.phase=t.phase)
    (hs : EncodedFieldFrame base (base 2409) origin X Y s)
    (ht : EncodedFieldFrame base (base 2409) origin X Y t) : s=t := by
  obtain ⟨a,pa,fa,ea⟩ := hs
  obtain ⟨b,pb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact pa.trans (phase.trans pb.symm)
    · exact PairFrame.unique _ _ origin _ _ a.basis b.basis fa fb
  rw [ea,eb,raw]

def trimInput (divide : Bool) (Y : Fp) : Fp×Fp := if divide then (2*Y,0) else (Y,Y)
def trimOutput (divide : Bool) (origin : BasisState) (x : Nat) (Y : Fp) : Fp×Fp :=
  if divide then
    (if origin (base 2400) then Y/(x : Fp) else Y,
     if origin (base 2400) then Y/(x : Fp) else Y)
  else (2*(if origin (base 2400) then Y*(x : Fp) else Y),0)

/-- The public specialization uses the original canonical nonzero divisor
and actual512 signed-trace premise. No new terminal-state input is required. -/
theorem trimReplay_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin (trimInput divide Y).1 (trimInput divide Y).2 s) :
    let out := run (trimReplay divide) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (trimOutput divide origin x Y).1 (trimOutput divide origin x Y).2 out := by
  have frame := trimReplay_frame divide hn hlo ho hp hf origin hg0 hs0 env legal
    (trimInput divide Y).1 (trimInput divide Y).2 s m input
  cases divide
  · simpa only [trimInput,trimOutput,Bool.false_eq_true,if_false,Bool.not_false,
      directionalPayload,if_true,trimLetters_product origin x Y hx0 hx hr] using frame
  · simpa only [trimInput,trimOutput,if_true,Bool.not_true,directionalPayload,
      Bool.false_eq_true,if_false,trimLetters_quotient origin x Y hx0 hx hr] using frame

/-- Independent records for the new511-cell and legacy512-cell programs
produce exactly the same complete State on the actual caller trajectory. -/
theorem trimReplay_old_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (s : State) (m k : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin (trimInput divide Y).1 (trimInput divide Y).2 s) :
    run (trimReplay divide) m s=run (mappedReplay divide) k s := by
  have a := trimReplay_spec divide hn hlo ho hp hf origin hg0 hs0 env legal x Y hx0 hx hr s m input
  have b := mappedReplay_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    (trimInput divide Y).1 (trimInput divide Y).2 s k input
  have old : (run (mappedReplay divide) k s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin
        (trimOutput divide origin x Y).1 (trimOutput divide origin x Y).2
        (run (mappedReplay divide) k s) := by
    cases divide
    · simpa only [trimInput,trimOutput,Bool.false_eq_true,if_false,Bool.not_false,
        directionalPayload,if_true,mixedTranscriptTape_product base origin (base 2400) x Y hx0 hx hr] using b
    · simpa only [trimInput,trimOutput,if_true,Bool.not_true,directionalPayload,
        Bool.false_eq_true,if_false,mixedTranscriptTape_quotient base origin (base 2400) x Y hx0 hx hr] using b
  exact encoded_unique origin _ _ _ _ (a.1.trans old.1.symm) a.2 old.2

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
attribute [local irreducible] run mappedReplay converterPairAt directionalPayload
  mixedTranscriptTape mixedTranscriptUnitTrace

/-- The actual middle three blocks of fieldSegment, with both boundary
conversions retained and all history groups encoded at each outer boundary. -/
def canonicalMappedReplay (divide : Bool) : Program :=
  renameProgram allPlaced (converterPair false)++
    (mappedReplay divide++renameProgram allPlaced (converterPair true))

theorem canonicalMappedReplay_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    let out := run (canonicalMappedReplay divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).2 out := by
  let P : State → State → Prop := fun initial out =>
    EncodedCanonicalFrame origin X Y initial → out.phase=initial.phase ∧
      EncodedCanonicalFrame origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).2 out
  have all := run_three_states
    (renameProgram allPlaced (converterPair false)) (mappedReplay divide)
    (renameProgram allPlaced (converterPair true)) P
    (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      rw [converterPair_placement] at h1 h3
      have first := encoded_center_pair hn origin hw hu hr hy X Y initial m1 hin
      rw [h1] at first
      have middle := mappedReplay_spec divide hn hlo ho hp hf origin hg0 hs0 env legal X Y s1 m2 first.2
      rw [h2] at middle
      change s3.phase=initial.phase ∧ _
      generalize hQ : directionalPayload (!divide)
        (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)=Q at middle ⊢
      have last := encoded_canonical_pair hn origin hw hu hr hy Q.1 Q.2 s2 m3 middle.2
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m
  exact all input

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
def fieldSuffix (divide : Bool) : Program := if divide then
  renameProgram allPlaced (copyPairAt id)
  else renameProgram allPlaced (halfInPlace (borrowedSkywalkUnary id) p)

theorem fieldSegment_join (divide : Bool) :
    fieldSegment divide=fieldPrefix divide++(canonicalMappedReplay divide++fieldSuffix divide) := by
  cases divide <;> simp only [fieldSegment,fieldPrefix,fieldSuffix,copyPairAt,canonicalMappedReplay,
    Bool.false_eq_true,if_false,if_true,List.append_assoc]

def fieldResult (divide : Bool) (origin : BasisState) (x : Nat) (Y : Fp) : Fp :=
  if origin (base 2400) then (if divide then Y/(x : Fp) else Y*(x : Fp)) else Y

/-- Complete actual mapped field segment: both retained endpoints and both
conversions surround the full512 field replay. All records preserve phase,
the encoded transcript, and the clean original source port. -/
theorem fieldSegment_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (fieldSegment divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out
  have all := run_three_states (fieldPrefix divide) (canonicalMappedReplay divide) (fieldSuffix divide) P
    (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      cases divide
      · simp only [fieldPrefix,fieldSuffix,Bool.false_eq_true,if_false] at h1 h3
        have first := mapped_copy_fill hn origin Y initial m1 hin
        rw [h1] at first
        have middle := canonicalMappedReplay_spec false hn hlo ho hp hf origin hg0 hs0 env legal
          hw hu hr hy Y Y s1 m2 first.2
        rw [h2] at middle
        simp only [Bool.not_false,directionalPayload,if_true] at middle
        rw [mixedTranscriptTape_product base origin (base 2400) x Y hx0 hx trace] at middle
        let Z := if origin (base 2400) then Y*(x:Fp) else Y
        have last := mapped_unary_step false hn hlo origin hw hu (2*Z) 0 s2 m3 middle.2
        simp only [Bool.false_eq_true,if_false] at last
        rw [h3] at last
        have two : (2:Fp)≠0 := by decide
        have halve : (2*Z)/2=Z := by rw [mul_comm 2 Z,mul_div_cancel_right₀ Z two]
        rw [halve] at last
        exact ⟨last.1.trans (middle.1.trans first.1),by simpa only [fieldResult,Bool.false_eq_true,if_false,Z] using last.2⟩
      · simp only [fieldPrefix,fieldSuffix,if_true] at h1 h3
        have first := mapped_unary_step true hn hlo origin hw hu Y 0 initial m1 hin
        simp only [if_true] at first
        rw [h1] at first
        have middle := canonicalMappedReplay_spec true hn hlo ho hp hf origin hg0 hs0 env legal
          hw hu hr hy (2*Y) 0 s1 m2 first.2
        rw [h2] at middle
        simp only [Bool.not_true,directionalPayload,Bool.false_eq_true,if_false] at middle
        rw [mixedTranscriptTape_quotient base origin (base 2400) x Y hx0 hx trace] at middle
        let Z := if origin (base 2400) then Y/(x:Fp) else Y
        have last := mapped_copy_clear hn origin Z s2 m3 middle.2
        rw [h3] at last
        exact ⟨last.1.trans (middle.1.trans first.1),by simpa only [fieldResult,if_true,Z] using last.2⟩) s m
  rw [fieldSegment_join]
  exact all input

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

private def oldPrefix : Program := fieldPrefix true ++
  renameProgram allPlaced (converterPair false) ++ mappedGroup true 0
private def newPrefix : Program := renameProgram allPlaced (converterPair false) ++ firstGroup true
private def commonSuffix : Program := mappedGroups true 1 169 ++ tailProgram true ++
  renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced (copyPairAt id)

/-- Independent record streams identify one full encoded packet output.
The unary endpoint is evaluated on its encoded input before any decoder. -/
theorem forward_prefix_state_eq
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (mOld mNew : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    run oldPrefix mOld s=run newPrefix mNew s := by
  let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin Q.1 Q.2 out
  have old := run_three_states (fieldPrefix true) (renameProgram allPlaced (converterPair false))
    (mappedGroup true 0) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have a := mapped_unary_step true hn hlo origin hw hu Y 0 initial m1 hin
      simp only [fieldPrefix,if_true] at h1
      simp only [if_true] at a
      rw [h1] at a
      have b := encoded_center_pair hn origin hw hu hr hy (2*Y) 0 s1 m2 a.2
      rw [converterPair_placement false] at h2
      rw [h2] at b
      have c := mappedGroup_encoded_step true 0 (by decide) hn hlo ho hp hf origin hg0 hs0
        env legal (2*Y) 0 s2 m3 b.2
      rw [h3] at c
      exact ⟨c.1.trans (b.1.trans a.1),by simpa only [directionalPayload,Bool.not_true,
        Bool.false_eq_true,if_false,Q] using c.2⟩) s mOld input
  have oldShape : oldPrefix=fieldPrefix true ++
      (renameProgram allPlaced (converterPair false)++mappedGroup true 0) := by
    simp only [oldPrefix,List.append_assoc]
  rw [←oldShape] at old
  let center := renameProgram allPlaced (converterPair false)
  let t := run center (mNew.take (measurementCount center)) s
  have first := encoded_center_pair hn origin hw hu hr hy Y 0 s
    (mNew.take (measurementCount center)) input
  have first' : t.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin Y 0 t := by
    simpa only [t,center,converterPair_placement] using first
  have last := firstGroup_forward_step hn hlo ho hp hf origin hg0 hs0 env legal Y t
    (mNew.drop (measurementCount center)) first'.2
  have current : (run newPrefix mNew s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Q.1 Q.2 (run newPrefix mNew s) := by
    simp only [newPrefix,run_append]
    exact ⟨last.1.trans first'.1,last.2⟩
  exact encoded_field_unique origin Q.1 Q.2 _ _ old.2 current.2 (old.1.trans current.1.symm)

private theorem forward_groups_succ (j n : Nat) :
    mappedGroups true j (n+1)=mappedGroup true j++mappedGroups true (j+1) n := by
  simp only [mappedGroups,if_true]

private theorem old_forward_join : MappedCompressed.fieldSegment true=oldPrefix++commonSuffix := by
  have groups : mappedGroups true 0 170=mappedGroup true 0++mappedGroups true 1 169 :=
    forward_groups_succ 0 169
  simp only [MappedCompressed.fieldSegment,oldPrefix,commonSuffix,fieldPrefix,copyPairAt,
    if_true,MappedCompressed.mappedReplay,groups,tailProgram,List.append_assoc]
private theorem new_forward_join : fieldSegment true=newPrefix++commonSuffix := by
  simp only [fieldSegment,newPrefix,commonSuffix,replay,copyPairAt,if_true,tailProgram,
    List.nil_append,List.append_assoc]

-- Keep programs symbolic so kernel conversion does not evaluate concrete gate lists.
private theorem replace_prefix (P Q R : Program) (s : State) (m : List Bool)
    (same : ∀ a b, run P a s = run Q b s) :
    run (P ++ R) (List.replicate (measurementCount P) false ++
      m.drop (measurementCount Q)) s = run (Q ++ R) m s := by
  rw [run_append,run_append,same _ (m.take (measurementCount Q))]
  simp only [List.drop_append,List.length_replicate,Nat.sub_self,List.drop_zero,
    List.drop_replicate,List.replicate_zero,List.nil_append]

/-- Full actual forward field wrapper. The fixed170 packet encoding, raw
510/511 tail and complete caller State are retained for all independent MX
records. The old endpoint is replaced only at the closed first-packet boundary. -/
theorem fieldTrimSegment_forward_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (fieldSegment true) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out := by
  let suffixRecords := m.drop (measurementCount newPrefix)
  let records := List.replicate (measurementCount oldPrefix) false ++ suffixRecords
  have old := MappedCompressed.fieldSegment_spec true hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s records input
  have actualStateEq : run (MappedCompressed.fieldSegment true) records s=run (fieldSegment true) m s := by
    rw [old_forward_join,new_forward_join]
    exact replace_prefix oldPrefix newPrefix commonSuffix s m (fun a b =>
      forward_prefix_state_eq hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal hw hu hr hy Y s a b input)
  rw [actualStateEq] at old
  exact old

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedFieldSegment.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run trimReplay converterPairAt directionalPayload
  mixedTranscriptTape mixedTranscriptUnitTrace
/-- The actual middle three blocks of fieldSegment, with both boundary
conversions retained and all history groups encoded at each outer boundary. -/
def canonicalTrimReplay (divide : Bool) : Program :=
  renameProgram allPlaced (converterPair false)++
    (trimReplay divide++renameProgram allPlaced (converterPair true))

theorem canonicalTrimReplay_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin (trimInput divide Y).1 (trimInput divide Y).2 s) :
    let out := run (canonicalTrimReplay divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin
      (trimOutput divide origin x Y).1
      (trimOutput divide origin x Y).2 out := by
  let P : State → State → Prop := fun initial out =>
    EncodedCanonicalFrame origin (trimInput divide Y).1 (trimInput divide Y).2 initial → out.phase=initial.phase ∧
      EncodedCanonicalFrame origin
        (trimOutput divide origin x Y).1
        (trimOutput divide origin x Y).2 out
  have all := run_three_states
    (renameProgram allPlaced (converterPair false)) (trimReplay divide)
    (renameProgram allPlaced (converterPair true)) P
    (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      rw [converterPair_placement] at h1 h3
      have first := encoded_center_pair hn origin hw hu hr hy (trimInput divide Y).1 (trimInput divide Y).2 initial m1 hin
      rw [h1] at first
      have middle := trimReplay_spec divide hn hlo ho hp hf origin hg0 hs0 env legal x Y hx0 hx trace s1 m2 first.2
      rw [h2] at middle
      change s3.phase=initial.phase ∧ _
      generalize hQ : trimOutput divide origin x Y=Q at middle ⊢
      have last := encoded_canonical_pair hn origin hw hu hr hy Q.1 Q.2 s2 m3 middle.2
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m
  exact all input


/-- Actual retained outer endpoints and conversions, with only the proven
terminal field cell omitted. Native integer recording still has512 rounds. -/
def fieldTrimSegment (divide : Bool) : Program :=
  fieldPrefix divide++(canonicalTrimReplay divide++fieldSuffix divide)

/-- Complete actual mapped field segment: both retained endpoints and both
conversions surround the511 field replay; native recording stays512. All records preserve phase,
the encoded transcript, and the clean original source port. -/
theorem fieldTrimSegment_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (fieldTrimSegment divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out
  have all := run_three_states (fieldPrefix divide) (canonicalTrimReplay divide) (fieldSuffix divide) P
    (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      cases divide
      · simp only [fieldPrefix,fieldSuffix,Bool.false_eq_true,if_false] at h1 h3
        have first := mapped_copy_fill hn origin Y initial m1 hin
        rw [h1] at first
        have middle := canonicalTrimReplay_spec false hn hlo ho hp hf origin hg0 hs0 env legal
          hw hu hr hy x Y hx0 hx trace s1 m2 first.2
        rw [h2] at middle
        simp only [trimOutput,Bool.false_eq_true,if_false] at middle
        let Z := if origin (base 2400) then Y*(x:Fp) else Y
        have last := mapped_unary_step false hn hlo origin hw hu (2*Z) 0 s2 m3 middle.2
        simp only [Bool.false_eq_true,if_false] at last
        rw [h3] at last
        have two : (2:Fp)≠0 := by decide
        have halve : (2*Z)/2=Z := by rw [mul_comm 2 Z,mul_div_cancel_right₀ Z two]
        rw [halve] at last
        exact ⟨last.1.trans (middle.1.trans first.1),by simpa only [fieldResult,Bool.false_eq_true,if_false,Z] using last.2⟩
      · simp only [fieldPrefix,fieldSuffix,if_true] at h1 h3
        have first := mapped_unary_step true hn hlo origin hw hu Y 0 initial m1 hin
        simp only [if_true] at first
        rw [h1] at first
        have middle := canonicalTrimReplay_spec true hn hlo ho hp hf origin hg0 hs0 env legal
          hw hu hr hy x Y hx0 hx trace s1 m2 first.2
        rw [h2] at middle
        simp only [trimOutput,if_true] at middle
        let Z := if origin (base 2400) then Y/(x:Fp) else Y
        have last := mapped_copy_clear hn origin Z s2 m3 middle.2
        rw [h3] at last
        exact ⟨last.1.trans (middle.1.trans first.1),by simpa only [fieldResult,if_true,Z] using last.2⟩) s m
  exact all input

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
private def newTerminalPrefix : Program := renameProgram allPlaced (converterPair false) ++ firstGroup true
private def terminalSuffix : Program := mappedGroups true 1 169 ++
  renameProgram allPlaced (logicalCell true 510) ++
  renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced (copyPairAt id)

private theorem forward_groups_succ_EntryMappedFieldSegmentTrimTerminal (j n : Nat) :
    mappedGroups true j (n+1)=mappedGroup true j++mappedGroups true (j+1) n := by
  simp only [mappedGroups,if_true]

private theorem oldTerminal_join : MappedCompressed.fieldTrimSegment true=oldTerminalPrefix++terminalSuffix := by
  have groups : mappedGroups true 0 170=mappedGroup true 0++mappedGroups true 1 169 :=
    forward_groups_succ_EntryMappedFieldSegmentTrimTerminal 0 169
  simp only [MappedCompressed.fieldTrimSegment,canonicalTrimReplay,trimReplay,oldTerminalPrefix,
    terminalSuffix,fieldPrefix,fieldSuffix,groups,if_true,List.append_assoc]
private theorem newTerminal_join : terminalFieldSegment true=newTerminalPrefix++terminalSuffix := by
  simp only [terminalFieldSegment,terminalReplay,newTerminalPrefix,terminalSuffix,copyPairAt,
    if_true,List.nil_append,List.append_assoc]

-- Keep programs symbolic so kernel conversion does not evaluate concrete gate lists.
private theorem replace_prefix_EntryMappedFieldSegmentTrimTerminal (P Q R : Program) (s : State) (m : List Bool)
    (same : ∀ a b, run P a s = run Q b s) :
    run (P ++ R) (List.replicate (measurementCount P) false ++
      m.drop (measurementCount Q)) s = run (Q ++ R) m s := by
  rw [run_append,run_append,same _ (m.take (measurementCount Q))]
  simp only [List.drop_append,List.length_replicate,Nat.sub_self,List.drop_zero,
    List.drop_replicate,List.replicate_zero,List.nil_append]

/-- Closed forward entry cancellation on the current511-cell wrapper.
Terminal omission is inherited from its accepted512-trace derivation,
without adding any terminal-source, activation or measurement premise. -/
theorem terminalFieldTrimSegment_forward_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (terminalFieldSegment true) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out := by
  let suffixRecords := m.drop (measurementCount newTerminalPrefix)
  let records := List.replicate (measurementCount oldTerminalPrefix) false ++ suffixRecords
  have old := MappedCompressed.fieldTrimSegment_spec true hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s records input
  have actualStateEq : run (MappedCompressed.fieldTrimSegment true) records s=run (terminalFieldSegment true) m s := by
    rw [oldTerminal_join,newTerminal_join]
    exact replace_prefix_EntryMappedFieldSegmentTrimTerminal oldTerminalPrefix newTerminalPrefix terminalSuffix s m (fun a b =>
      forward_prefix_state_eq hn hlo ho hp (packet_layouts _ _ _ hf 0 (by decide))
        origin hg0 hs0 env legal hw hu hr hy Y s a b input)
  rw [actualStateEq] at old
  exact old

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
end

-- source: ECDSAAdd/Arithmetic/TerminalMappedReplayResources.lean
noncomputable section

set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation
attribute [local irreducible] wires toffoliCount measurementCount mappedReplay trimReplay

theorem fieldTrimSegment_support (divide : Bool) :
    wires (fieldTrimSegment divide) ⊆ slots.toFinset := by
  have full := fieldSegment_support divide
  rw [fieldSegment_join] at full
  simp only [fieldTrimSegment,canonicalTrimReplay,canonicalMappedReplay,wires_append,
    Finset.union_subset_iff,and_assoc] at full ⊢
  exact ⟨full.1,full.2.1,trimReplay_support divide,full.2.2.2.1,full.2.2.2.2⟩

theorem fieldTrimSegment_saving (divide : Bool) :
    toffoliCount (fieldSegment divide)=toffoliCount (fieldTrimSegment divide)+(if divide then 1280 else 1281) ∧
    measurementCount (fieldSegment divide)=measurementCount (fieldTrimSegment divide)+1025 := by
  have saving := trimReplay_count_saving divide
  rw [fieldSegment_join]
  simp only [fieldTrimSegment,canonicalTrimReplay,canonicalMappedReplay,toffoliCount_append,
    measurementCount_append]
  constructor <;> omega

theorem fieldTrimSegment_counts (divide : Bool) :
    toffoliCount (fieldTrimSegment divide)=(if divide then 658841 else 659353) ∧
    measurementCount (fieldTrimSegment divide)=(if divide then 527516 else 527517) := by
  have old := fieldSegment_counts divide
  have saving := fieldTrimSegment_saving divide
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at old saving ⊢
  all_goals constructor <;> omega

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

private def inverseEntryPrefix : Program := renameProgram allPlaced (copyPairAt id)++
  renameProgram allPlaced (converterPair false)

private theorem inverseEntryPrefix_step
    (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run inverseEntryPrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Y Y (run inverseEntryPrefix m s) := by
  let copy := renameProgram allPlaced (copyPairAt id)
  let t := run copy (m.take (measurementCount copy)) s
  have first := mapped_copy_fill hn origin Y s (m.take (measurementCount copy)) input
  have second := encoded_center_pair hn origin hw hu hr hy Y Y t
    (m.drop (measurementCount copy)) first.2
  simp only [inverseEntryPrefix,run_append,converterPair_placement]
  exact ⟨second.1.trans first.1,second.2⟩

private theorem inverse_entry_join : terminalFieldSegment false=inverseEntryPrefix++
    (terminalReplay false++renameProgram allPlaced (converterPair true)) := by
  simp only [terminalFieldSegment,inverseEntryPrefix,copyPairAt,Bool.false_eq_true,if_false,
    List.append_nil,List.append_assoc]

/-- Full actual inverse field wrapper under the unchanged public contract.
Both original high bits, workspace, transcript, activation control and phase
are restored for every independent measurement stream. The terminal511 cell
remains omitted, and the final inverse arithmetic/unseed pair is cancelled. -/
theorem terminalFieldTrimSegment_inverse_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (terminalFieldSegment false) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin Z 0 out
  have all := run_three_states inverseEntryPrefix (terminalReplay false)
    (renameProgram allPlaced (converterPair true)) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have first := inverseEntryPrefix_step hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at first
      have middle := terminalReplay_inverse_spec hn hlo ho hp hf origin hg0 hs0 env legal
        x Y hx0 hx trace s1 m2 first.2
      rw [h2] at middle
      have last := encoded_canonical_pair hn origin hw hu hr hy Z 0 s2 m3 middle.2
      rw [converterPair_placement true] at h3
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m input
  rw [inverse_entry_join]
  simpa only [fieldResult,Bool.false_eq_true,if_false,Z] using all

theorem inverse_entry_resources : toffoliCount (terminalFieldSegment false)=657817 ∧
    measurementCount (terminalFieldSegment false)=525981 := terminalFieldSegment_counts false

theorem inverse_entry_support : wires (terminalFieldSegment false) ⊆ slots.toFinset :=
  terminalFieldSegment_support false

/-- Entry/unseed savings relative to the already terminal-trim production
wrapper; the previously integrated1281-T terminal saving is not recounted. -/
theorem inverse_entry_saving :
    toffoliCount (MappedCompressed.fieldTrimSegment false)=toffoliCount (terminalFieldSegment false)+1536 ∧
    measurementCount (MappedCompressed.fieldTrimSegment false)=measurementCount (terminalFieldSegment false)+1536 := by
  have old := MappedCompressed.fieldTrimSegment_counts false
  rw [old.1,old.2,inverse_entry_resources.1,inverse_entry_resources.2]
  norm_num

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

theorem saving (divide : Bool) :
    toffoliCount (EntryMappedFieldSegmentTrim.terminalFieldSegment divide)=
      toffoliCount (fieldSegment divide)+257 ∧
    measurementCount (EntryMappedFieldSegmentTrim.terminalFieldSegment divide)=
      measurementCount (fieldSegment divide)+1 := by
  rw [(EntryMappedFieldSegmentTrim.terminalFieldSegment_counts divide).1,
    (EntryMappedFieldSegmentTrim.terminalFieldSegment_counts divide).2,
    (fieldSegment_counts divide).1,(fieldSegment_counts divide).2]
  cases divide <;> norm_num

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

/-- Compose an already established local State equality without reducing the
programs. The record splits are the ordinary operational splits of run_append. -/
theorem append_context_eq (P Q R : Program) (s : State) (m n : List Bool)
    (localEq :
      run Q (m.drop (measurementCount P)) (run P (m.take (measurementCount P)) s)=
      run R (n.drop (measurementCount P)) (run P (n.take (measurementCount P)) s)) :
    run (P++Q) m s=run (P++R) n s :=
  (run_append P Q m s).trans (localEq.trans (run_append P R n s).symm)

/-- A shared suffix observes equal head States on independent record lists.
No field or input hypothesis is introduced by this generic context lemma. -/
theorem suffix_context_eq (P Q S : Program) (s : State) (m n : List Bool)
    (headEq : run P (m.take (measurementCount P)) s=
      run Q (n.take (measurementCount Q)) s)
    (tailEq : m.drop (measurementCount P)=n.drop (measurementCount Q)) :
    run (P++S) m s=run (Q++S) n s := by
  have stateEq := congrArg (fun t : State => run S (m.drop (measurementCount P)) t) headEq
  have recordsEq := congrArg (fun k : List Bool =>
    run S k (run Q (n.take (measurementCount Q)) s)) tailEq
  exact (run_append P S m s).trans
    (stateEq.trans (recordsEq.trans (run_append Q S n s).symm))

/-- Keep program-shape conversion inside a generic theorem rather than asking
the caller's elaborator to unfold two concrete measured gate lists. -/
theorem program_shape_context_eq (P Q P' Q' : Program) (s : State) (m n : List Bool)
    (hp : P=P') (hq : Q=Q') (states : run P' m s=run Q' n s) :
    run P m s=run Q n s :=
  (congrArg (fun p : Program => run p m s) hp).trans
    (states.trans (congrArg (fun q : Program => run q n s) hq).symm)

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

private theorem first_rest_payload (origin : BasisState) (Y : Fp) :
    groupsPayload true origin 1 169
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0))=
      PenultimateSwapIdentity.penultimatePayload origin Y := by
  have start : groupsPayload true origin 0 170 (2*Y,0)=
      groupsPayload true origin 1 169
        (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)) :=
    groups_succ origin 0 169 (2*Y,0)
  have generic : groupsPayload true origin 0 170 (2*Y,0)=
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
        (indexedLetters (3*0) (3*170))) (2*Y,0) :=
    forward_groups_payload 0 170 origin (2*Y,0)
  have zero : 3*0=0 := by decide
  have length : 3*170=510 := by decide
  have lettersEq : indexedLetters (3*0) (3*170)=indexedLetters 0 510 :=
    congrArg₂ indexedLetters zero length
  have lifted : skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
      (indexedLetters (3*0) (3*170))) (2*Y,0)=
        skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
          (indexedLetters 0 510)) (2*Y,0) :=
    congrArg (fun ls : List MixedTranscriptLetter =>
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) ls) (2*Y,0)) lettersEq
  have fold : skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
      (indexedLetters 0 510)) (2*Y,0)=PenultimateSwapIdentity.penultimatePayload origin Y := by
    unfold PenultimateSwapIdentity.penultimatePayload
    rfl
  exact start.symm.trans (generic.trans (lifted.trans fold))


private def rawPrefix : Program := renameProgram allPlaced (converterPair false) ++
  (EntryMappedFieldSegmentTrim.firstGroup true ++ mappedGroups true 1 169)
private def headPrefix : Program := sealedProgram rawPrefix
private def oldHead : Program := sealedProgram (headPrefix ++ renameProgram allPlaced (logicalCell true 510))
private def newHead : Program := sealedProgram (headPrefix ++ renameProgram allPlaced (PenultimateSwapIdentity.cell true))
private def commonTail : Program := renameProgram allPlaced (converterPair true) ++
  renameProgram allPlaced (copyPairAt id)
attribute [local irreducible] rawPrefix headPrefix oldHead newHead commonTail

private theorem headPrefix_eq : headPrefix=rawPrefix := by
  unfold headPrefix
  exact sealedProgram_eq _
private theorem oldHead_eq : oldHead=headPrefix++renameProgram allPlaced (logicalCell true 510) := by
  unfold oldHead
  exact sealedProgram_eq _
private theorem newHead_eq : newHead=headPrefix++renameProgram allPlaced (PenultimateSwapIdentity.cell true) := by
  unfold newHead
  exact sealedProgram_eq _

/-- The actual entry-cancelled first packet and169 native packets expose the
same penultimate payload as the original510-letter mathematical prefix. -/
private theorem headPrefix_step
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let A := PenultimateSwapIdentity.penultimatePayload origin Y
    (run headPrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A.1 A.2 (run headPrefix m s) := by
  let A := PenultimateSwapIdentity.penultimatePayload origin Y
  let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin A.1 A.2 out
  have all := run_three_states (renameProgram allPlaced (converterPair false))
    (EntryMappedFieldSegmentTrim.firstGroup true) (mappedGroups true 1 169) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have a := encoded_center_pair hn origin hw hu hr hy Y 0 initial m1 hin
      rw [converterPair_placement false] at h1
      rw [h1] at a
      have b := EntryMappedFieldSegmentTrim.firstGroup_forward_step hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal Y s1 m2 a.2
      rw [h2] at b
      have frame2 : EncodedFieldFrame base (base 2409) origin Q.1 Q.2 s2 := b.2
      have cAll := mappedGroups_frame true 1 169 (by decide) hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf)
        origin hg0 hs0 env legal Q.1 Q.2 s2 m3 frame2
      have cPhase : (run (mappedGroups true 1 169) m3 s2).phase=s2.phase := cAll.2.1
      have cFrame : EncodedFieldFrame base (base 2409) origin
          (groupsPayload true origin 1 169 (Q.1,Q.2)).1
          (groupsPayload true origin 1 169 (Q.1,Q.2)).2
          (run (mappedGroups true 1 169) m3 s2) := cAll.2.2
      rw [h3] at cPhase cFrame
      have payload : groupsPayload true origin 1 169 (Q.1,Q.2)=A := by
        change groupsPayload true origin 1 169 Q=A
        exact first_rest_payload origin Y
      rw [payload] at cFrame
      exact ⟨cPhase.trans (b.1.trans a.1),cFrame⟩) s m input
  have rawResult : (run rawPrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A.1 A.2 (run rawPrefix m s) := by
    simpa only [rawPrefix] using all
  have eval : run headPrefix m s=run rawPrefix m s := by
    unfold headPrefix
    exact sealedProgram_run rawPrefix m s
  exact Eq.mp (congrArg (fun out : State => out.phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin A.1 A.2 out) eval.symm) rawResult


/- Head States agree when their internal prefix records coincide; local cell
records remain independent. This record condition is proved by construction in
the public wrapper and adds no public input or outcome restriction. -/
private theorem head_state_eq
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (mOld mNew : List Bool)
    (hprefix : mOld.take (measurementCount headPrefix)=mNew.take (measurementCount headPrefix))
    (input : EncodedCanonicalFrame origin Y 0 s) :
    run oldHead mOld s=run newHead mNew s := by
  let A := PenultimateSwapIdentity.penultimatePayload origin Y
  let newState := run headPrefix (mNew.take (measurementCount headPrefix)) s
  have newFrame : newState.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin A.1 A.2 newState :=
    headPrefix_step hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy Y s _ input
  have last := PenultimateMappedCellProof.forward_cell_eq hn hlo ho hp hf
    origin hg0 hs0 env legal A.1 A.2 newState
    (mNew.drop (measurementCount headPrefix)) (mOld.drop (measurementCount headPrefix))
    newFrame.2 (PenultimateSwapIdentity.penultimate_half_dup origin x Y hx0 hx trace)
  have prefixStates := congrArg (fun rs : List Bool => run headPrefix rs s) hprefix
  have transport := congrArg (fun t : State =>
    run (renameProgram allPlaced (logicalCell true 510)) (mOld.drop (measurementCount headPrefix)) t) prefixStates
  have context := append_context_eq headPrefix
    (renameProgram allPlaced (logicalCell true 510))
    (renameProgram allPlaced (PenultimateSwapIdentity.cell true)) s mOld mNew (transport.trans last.symm)
  have oldShape : oldHead=headPrefix++renameProgram allPlaced (logicalCell true 510) := oldHead_eq
  have newShape : newHead=headPrefix++renameProgram allPlaced (PenultimateSwapIdentity.cell true) := newHead_eq
  exact program_shape_context_eq oldHead newHead
    (headPrefix++renameProgram allPlaced (logicalCell true 510))
    (headPrefix++renameProgram allPlaced (PenultimateSwapIdentity.cell true))
    s mOld mNew oldShape newShape context


private theorem old_join : EntryMappedFieldSegmentTrim.terminalFieldSegment true=oldHead++commonTail := by
  have raw : EntryMappedFieldSegmentTrim.terminalFieldSegment true=
      (rawPrefix++renameProgram allPlaced (logicalCell true 510))++commonTail := by
    simp only [EntryMappedFieldSegmentTrim.terminalFieldSegment,EntryMappedFieldSegmentTrim.terminalReplay,
      rawPrefix,commonTail,copyPairAt,if_true,List.nil_append,List.append_assoc]
  have shape := oldHead_eq.trans (congrArg (fun q : Program =>
    q++renameProgram allPlaced (logicalCell true 510)) headPrefix_eq)
  exact raw.trans (congrArg (fun q : Program => q++commonTail) shape).symm

private theorem new_join : fieldSegment true=newHead++commonTail := by
  have raw : fieldSegment true=
      (rawPrefix++renameProgram allPlaced (PenultimateSwapIdentity.cell true))++commonTail := by
    simp only [fieldSegment,replay,rawPrefix,commonTail,copyPairAt,if_true,List.nil_append,List.append_assoc]
  have shape := newHead_eq.trans (congrArg (fun q : Program =>
    q++renameProgram allPlaced (PenultimateSwapIdentity.cell true)) headPrefix_eq)
  exact raw.trans (congrArg (fun q : Program => q++commonTail) shape).symm


private theorem splice_records (n a b : Nat) (m : List Bool) :
    let padded := m++List.replicate (n+b) false
    let records := padded.take n++(List.replicate a false++padded.drop (n+b))
    records.take n=padded.take n ∧ records.drop (n+a)=padded.drop (n+b) := by
  let padded := m++List.replicate (n+b) false
  have bound : n≤padded.length := by simp only [padded,List.length_append,List.length_replicate]; omega
  have len : (padded.take n).length=n := List.length_take_of_le bound
  constructor
  · change ((padded.take n)++(List.replicate a false++padded.drop (n+b))).take n=padded.take n
    rw [List.take_append_of_le_length len.symm.le,List.take_take,Nat.min_self]
  · have gone : (padded.take n).drop (n+a)=[] := List.drop_eq_nil_of_le (by rw [len]; omega)
    have sub : n+a-n=a := by omega
    change ((padded.take n)++(List.replicate a false++padded.drop (n+b))).drop (n+a)=padded.drop (n+b)
    rw [List.drop_append,len,gone,sub,List.nil_append]
    rw [List.drop_append,List.length_replicate,List.drop_replicate,Nat.sub_self,
      List.replicate_zero,List.nil_append,List.drop_zero]

/-- Only raw510's S window is removed. The original complete point-input,
trace, activation, workspace and encoding contract is retained. Every fresh
MX outcome and arbitrary incoming phase are covered by State equality. -/
theorem fieldSegment_forward_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (fieldSegment true) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out := by
  let p := measurementCount headPrefix
  let a := measurementCount (renameProgram allPlaced (logicalCell true 510))
  let b := measurementCount (renameProgram allPlaced (PenultimateSwapIdentity.cell true))
  have oldCount : measurementCount oldHead=p+a :=
    (congrArg measurementCount oldHead_eq).trans (measurementCount_append _ _)
  have newCount : measurementCount newHead=p+b :=
    (congrArg measurementCount newHead_eq).trans (measurementCount_append _ _)
  let padded := m++List.replicate (p+b) false
  let records := padded.take p++(List.replicate a false++padded.drop (p+b))
  have splice := splice_records p a b m
  have prefixRecords : records.take p=padded.take p := splice.1
  have tailRecords : records.drop (measurementCount oldHead)=padded.drop (measurementCount newHead) := by
    simpa only [oldCount,newCount] using splice.2
  have oldBound : p≤measurementCount oldHead := by rw [oldCount]; omega
  have newBound : p≤measurementCount newHead := by rw [newCount]; omega
  have prefixTakes : (records.take (measurementCount oldHead)).take p=
      (padded.take (measurementCount newHead)).take p := by
    simpa only [List.take_take,Nat.min_eq_left oldBound,Nat.min_eq_left newBound] using prefixRecords
  have headEq := head_state_eq hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy
    x hx0 hx trace Y s (records.take (measurementCount oldHead))
    (padded.take (measurementCount newHead)) prefixTakes input
  have context := suffix_context_eq oldHead newHead commonTail s records padded headEq tailRecords
  have programEq : run (EntryMappedFieldSegmentTrim.terminalFieldSegment true) records s=
      run (fieldSegment true) padded s :=
    (congrArg (fun q : Program => run q records s) old_join).trans
      (context.trans (congrArg (fun q : Program => run q padded s) new_join).symm)
  have padEq : run (fieldSegment true) padded s=run (fieldSegment true) m s :=
    run_pad_false (fieldSegment true) m (p+b) s
  have actualStateEq := programEq.trans padEq
  have old := EntryMappedFieldSegmentTrim.terminalFieldTrimSegment_forward_spec
    hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy x hx0 hx trace Y s records input
  exact Eq.mp (congrArg (fun out : State =>
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out) actualStateEq) old

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

private def inversePrefix : Program := renameProgram allPlaced (copyPairAt id) ++
  renameProgram allPlaced (converterPair false)

private theorem inversePrefix_spec
    (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run inversePrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Y Y (run inversePrefix m s) := by
  let copy := renameProgram allPlaced (copyPairAt id)
  let t := run copy (m.take (measurementCount copy)) s
  have first := mapped_copy_fill hn origin Y s (m.take (measurementCount copy)) input
  have second := encoded_center_pair hn origin hw hu hr hy Y Y t
    (m.drop (measurementCount copy)) first.2
  simp only [inversePrefix,run_append,converterPair_placement]
  exact ⟨second.1.trans first.1,second.2⟩

private theorem fieldSegment_inverse_join : fieldSegment false=inversePrefix++
    (replay false++renameProgram allPlaced (converterPair true)) := by
  simp only [fieldSegment,inversePrefix,copyPairAt,Bool.false_eq_true,if_false,
    List.append_nil,List.append_assoc]

/-- Original full field contract, with no additional endpoint or measurement
assumption. The duplicate inverse head is derived from the emitted copy and
conversion prefix. All work, source, controls, transcript and phase retain
 the accepted encoded canonical frame. -/
theorem fieldSegment_inverse_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (fieldSegment false) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin Z 0 out
  have all := run_three_states inversePrefix (replay false)
    (renameProgram allPlaced (converterPair true)) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have first := inversePrefix_spec hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at first
      have middle := replay_inverse_spec hn hlo ho hp hf origin hg0 hs0 env legal
        x Y hx0 hx trace s1 m2 first.2
      rw [h2] at middle
      have last := encoded_canonical_pair hn origin hw hu hr hy Z 0 s2 m3 middle.2
      rw [converterPair_placement true] at h3
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m input
  rw [fieldSegment_inverse_join]
  simpa only [fieldResult,Bool.false_eq_true,if_false,Z] using all

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

/-- Same hypotheses and conclusion as the current complete field contract.
Every record stream and incoming phase remains quantified. -/
theorem selectedFieldSegment_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (selectedFieldSegment divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  cases divide
  · simpa only [selectedFieldSegment, Bool.false_eq_true, if_false] using
      PenultimateMapped.fieldSegment_inverse_spec hn hlo ho hp hf origin hg0 hs0 env legal
        hw hu hr hy x hx0 hx trace Y s m input
  · simpa only [selectedFieldSegment, if_true] using
      PenultimateMapped.fieldSegment_forward_spec
        hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy x hx0 hx trace Y s m input

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

theorem inverse_counts (w : Nat → Wire) :
    toffoliCount (inverse w)=508 ∧ measurementCount (inverse w)=508 := by
  have h := hAdd_counts w true
  have k := kAdd_counts w true
  have c := lowCopy_counts w
  have r := rotate_counts (wireBlock w 770 258)
  simp [inverse,toffoliCount_append,measurementCount_append,h.1,h.2,k.1,k.2,
    c.1,c.2,r.2.2.1,r.2.2.2,toffoliCount,measurementCount]

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

theorem prefix_qubitBound (w : Nat → Wire) :
    qubitCount (forward w)≤773 ∧ qubitCount (inverse w)≤773 := by
  have h := prefix_support w
  have hc := List.toFinset_card_le (prefixSites w)
  have hl : (prefixSites w).length=773 := by simp [prefixSites,wireBlock_length]
  rw [hl] at hc
  exact ⟨(Finset.card_le_card h.1).trans hc,(Finset.card_le_card h.2).trans hc⟩

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

private theorem write_twice (s : BasisState) (q : Wire) (a b : Bool) :
    writeBit (writeBit s q a) q b=writeBit s q b := by
  funext w
  by_cases h : w=q <;> simp [writeBit,h]

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

theorem program_correct (bits sums : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hw : ∀q∈mappedWires sums,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (sumKnown : mappedValue sums s.basis=
      (mappedValue bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length) :
    (run (program bits ys sums carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (program bits ys sums carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (program bits ys sums carry cin) m s).basis=mappedValue sums s.basis := by
  have ready := ready_of_value bits sums ys (s.basis cin) s.basis hl hs sumKnown
  rw [program_eq_mappedAdd bits sums ys carry cin hn ha hw hl hs hc s m hclean ready]
  have old := mappedAdd_correct bits ys carry cin hn ha hl hc s m hclean
  exact ⟨old.1,old.2.1,old.2.2.trans sumKnown.symm⟩

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

theorem kAdd_phase (w : Nat → Wire) (inverse : Bool) (s : State) (m : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀q∈mappedWires (kBits w inverse),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    (run (kAdd w inverse) m s).phase=s.phase := by
  rw [kAdd_run]
  exact (kTail_spec w inverse s _ hn hs hc).1

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
private theorem copy_cancel (src dst : List Wire) (hl : src.length=dst.length)
    (hn : (src++dst).Nodup) (s : State) (m n : List Bool) :
    run (copyRegister none src dst) n (run (copyRegister none src dst) m s)=s := by
  have f := copyRegister_correct none src dst hl hn (by simp) s m
  have i := copyRegister_correct none src dst hl hn (by simp)
    (run (copyRegister none src dst) m s) n
  have srcKeep := regValue_congr src (run (copyRegister none src dst) m s).basis s.basis
    (fun q hq => f.2.1 q (List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hq))
  apply state_of_value_frame dst s _ (i.1.trans f.1)
  · rw [i.2.2,f.2.2]
    simp only [copyValue]
    rw [srcKeep,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  · intro q hq; exact (i.2.1 q hq).trans (f.2.1 q hq)

private theorem rotate_reverse (r : List Wire) :
    (rotateRight r).reverse=rotateLeft r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      rw [rotateRight,rotateLeft,List.reverse_append,ih]
      rfl
private theorem rotate_proper (r : List Wire) (hn : r.Nodup) :
    ProperProgram (rotateRight r) := by
  induction r with
  | nil => simp [rotateRight,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,ProperProgram]
    | cons b r =>
      have nd := List.nodup_cons.mp hn
      have ne : a≠b := fun h => nd.1 (by simp [h])
      exact (properProgram_append _ _).mpr
        ⟨by simp [swapBits,ProperProgram,ProperGate,ne,Ne.symm ne],ih nd.2⟩
private theorem rotate_cancel (r : List Wire) (hn : r.Nodup) (s : State) (m n : List Bool) :
    run (rotateLeft r) n (run (rotateRight r) m s)=s := by
  rw [←rotate_reverse]
  exact run_reverse_proper _ (rotate_proper r hn) s m n

def inverseFront (w : Nat → Wire) : Program :=
  [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]++lowCopy w
def inverseBack (w : Nat → Wire) : Program :=
  lowCopy w++[.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)]
def inverseMiddle (w : Nat → Wire) : Program :=
  [.CX (w 1028) (w 770)]++rotateRight (wireBlock w 770 258)
def inverseUnmiddle (w : Nat → Wire) : Program :=
  rotateLeft (wireBlock w 770 258)++[.CX (w 1028) (w 770)]

private theorem front_cancel (w : Nat → Wire) (s : State) (m n : List Bool)
    (hn : (wireBlock w 771 255++wireBlock w 1 255).Nodup)
    (h0 : w 770≠w 1028) (h1 : w 1028≠w 0) :
    run (inverseBack w) n (run (inverseFront w) m s)=s := by
  let P : Program := [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]
  have hp : ProperProgram P := by simp [P,ProperProgram,ProperGate,h0,h1]
  have c := copy_cancel (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) hn (run P m s) m n
  have hm : measurementCount P=0 := properProgram_measurementCount P hp
  have cm := (lowCopy_counts w).2
  change run (lowCopy w++P.reverse) n (run (P++lowCopy w) m s)=s
  rw [run_append,run_take,run_append,run_take,hm,cm,List.drop_zero]
  simp only [List.drop_zero]
  rw [show run (lowCopy w) n (run (lowCopy w) m (run P m s))=run P m s from c]
  exact run_reverse_proper P hp s m n

private theorem middle_cancel (w : Nat → Wire) (s : State) (m n : List Bool)
    (hn : (wireBlock w 770 258).Nodup) (hne : w 1028≠w 770) :
    run (inverseUnmiddle w) n (run (inverseMiddle w) m s)=s := by
  rw [inverseUnmiddle,inverseMiddle,run_append,run_take,run_append,run_take,
    (rotate_counts (wireBlock w 770 258)).2.2.2,
    show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,List.drop_zero]
  rw [rotate_cancel _ hn]
  exact properGate_involution (.CX (w 1028) (w 770)) hne s m n

/-- The layout conditions concern only physical roles. No forward result or
measurement outcome is assumed in this inverse theorem. -/
theorem inverse_forward (w : Nat → Wire) (s : State) (mF mI : List Bool)
    (hnH : (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup)
    (hnK : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hsH : ∀i q,q∈mappedWires (hBits w i) →
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252))
    (hsK : ∀i q,q∈mappedWires (kBits w i) →
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hflag : w 1028∉wireBlock w 4 253)
    (kflag : w 1028∉w 770::wireBlock w 771 257)
    (copyND : (wireBlock w 771 255++wireBlock w 1 255).Nodup)
    (rotateND : (wireBlock w 770 258).Nodup)
    (ne0 : w 770≠w 1028) (ne1 : w 1028≠w 0)
    (carryAway : ∀q∈wireBlock w 1540 256,
      q∉wires (inverseFront w) ∧ q∉wireBlock w 4 253 ∧ q∉wires (inverseMiddle w))
    (carrySubset : ∀q∈wireBlock w 1540 252,q∈wireBlock w 1540 256)
    (cinAway : w 1797∉wires (inverseFront w))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false)
    (cin : s.basis (w 1797)=false) :
    run (inverse w) mI (run (forward w) mF s)=s := by
  let u := run (inverseFront w) mF s
  let v := run (hAdd w false) mF u
  let z := run (inverseMiddle w) (mF.drop 252) v
  have uc : ∀q∈wireBlock w 1540 256,u.basis q=false := by
    intro q hq; exact (run_preserves_outside _ mF s q (carryAway q hq).1).trans (hc q hq)
  have ui : u.basis (w 1797)=false :=
    (run_preserves_outside _ mF s _ cinAway).trans cin
  have ha := hAdd_spec w false u mF hnH (hsH false)
    (fun q hq => uc q (carrySubset q hq))
  have vc : ∀q∈wireBlock w 1540 256,v.basis q=false := by
    intro q hq; exact (ha.2.1 q (carryAway q hq).2.1).trans (uc q hq)
  have zc : ∀q∈wireBlock w 1540 256,z.basis q=false := by
    intro q hq; exact (run_preserves_outside _ _ v q (carryAway q hq).2.2).trans (vc q hq)
  have kc := kAdd_cancel w z (mF.drop 252) mI hnK hsK kflag zc
  have hh := hAdd_cancel w u mF (mI.drop 256) hnH hsH hflag
    (fun q hq => uc q (carrySubset q hq)) ui
  have fm : measurementCount (inverseFront w)=0 := by
    simp [inverseFront,measurementCount_append,measurementCount,(lowCopy_counts w).2]
  have mm : measurementCount (inverseMiddle w)=0 := by
    simp [inverseMiddle,measurementCount_append,measurementCount,(rotate_counts _).2.1]
  have um : measurementCount (inverseUnmiddle w)=0 := by
    simp [inverseUnmiddle,measurementCount_append,measurementCount,(rotate_counts _).2.2.2]
  have fr : forward w=inverseFront w++(hAdd w false++(inverseMiddle w++kAdd w false)) := by
    simp only [forward,inverseFront,inverseMiddle,List.append_assoc]
  have ir : inverse w=kAdd w true++(inverseUnmiddle w++(hAdd w true++inverseBack w)) := by
    simp only [inverse,inverseBack,inverseUnmiddle,List.append_assoc]
  have fRun : run (forward w) mF s=run (kAdd w false) (mF.drop 252) z := by
    rw [fr,run_append,run_take,fm,List.drop_zero]
    rw [run_append,run_take,(hAdd_counts w false).2]
    rw [run_append,run_take,mm,List.drop_zero]
  have iRun (t : State) : run (inverse w) mI t=
      run (inverseBack w) ((mI.drop 256).drop 252)
        (run (hAdd w true) (mI.drop 256)
          (run (inverseUnmiddle w) (mI.drop 256) (run (kAdd w true) mI t))) := by
    rw [ir,run_append,run_take,(kAdd_counts w true).2]
    rw [run_append,run_take,um,List.drop_zero]
    rw [run_append,run_take,(hAdd_counts w true).2]
  rw [iRun,fRun,kc,middle_cancel w v _ _ rotateND (Ne.symm ne0),hh]
  exact front_cancel w s _ _ copyND ne0 ne1
end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectInverseWrapper.lean
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run mappedAdd hAdd kAdd kTail forward inverse

private theorem copy_away (w : Nat → Wire) (q : Wire)
    (hs : q∉wireBlock w 771 255) (hd : q∉wireBlock w 1 255) :
    q∉wires (lowCopy w) := by
  rw [lowCopy,copyRegister_wires none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length])]
  split_ifs
  · simp
  · simpa only [Option.toList_none,List.nil_append,List.mem_toFinset,
      List.mem_append,not_or] using And.intro hs hd

private theorem front_away (w : Nat → Wire) (q : Wire)
    (h0 : q≠w 0) (hb : q≠w 770) (he : q≠w 1028)
    (hs : q∉wireBlock w 771 255) (hd : q∉wireBlock w 1 255) :
    q∉wires (inverseFront w) := by
  have flags : q∉wires [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] := by
    simp [wires,Instr.wires,h0,hb,he]
  rw [inverseFront,wires_append,Finset.mem_union,not_or]
  exact ⟨flags,copy_away w q hs hd⟩

private theorem middle_away (w : Nat → Wire) (q : Wire)
    (hb : q≠w 770) (he : q≠w 1028) (hr : q∉wireBlock w 770 258) :
    q∉wires (inverseMiddle w) := by
  have first : q∉wires [.CX (w 1028) (w 770)] := by
    simp [wires,Instr.wires,hb,he]
  have rot : q∉wires (rotateRight (wireBlock w 770 258)) := by
    rw [(rotate_wires (wireBlock w 770 258)).1]
    split_ifs
    · simp
    · simpa only [List.mem_toFinset] using hr
  rw [inverseMiddle,wires_append,Finset.mem_union,not_or]
  exact ⟨first,rot⟩

/-- Existing seed readiness suffices. The stronger primitive needs no bound
on x and no extension-zero assumption; all original data and spectators return. -/
theorem inverse_forward_ready (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (s : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    run (inverse w) mI (run (forward w) mF s)=s := by
  have bank : regValue (wireBlock w 1540 257) s.basis=0 := ready.carry
  have clean : ∀q∈wireBlock w 1540 256,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp bank q (block_subset w 1540 256 257 (by omega) q hq)
  have cin : s.basis (w 1797)=false := ready.cin
  refine inverse_forward w s mF mI (h_inputs_nd w hn) (k_inputs_nd w hn)
    (fun i => h_sources_fresh w hn i) (fun i => k_sources_fresh w hn i)
    (block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega))
    ?_ (copy_inputs_nd w hn) (block_nodup w hn 770 258 (by omega))
    (index_ne w hn 770 1028 (by omega) (by omega) (by omega))
    (index_ne w hn 1028 0 (by omega) (by omega) (by omega))
    ?_ (block_subset w 1540 252 256 (by omega)) ?_ clean cin
  · simp only [List.mem_cons,not_or]
    exact ⟨index_ne w hn 1028 770 (by omega) (by omega) (by omega),
      block_not_mem w hn 1028 771 257 (by omega) (by omega) (by omega)⟩
  · intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have h0 := index_ne w hn j 0 (by omega) (by omega) (by omega)
    have hb := index_ne w hn j 770 (by omega) (by omega) (by omega)
    have he := index_ne w hn j 1028 (by omega) (by omega) (by omega)
    exact ⟨front_away w (w j) h0 hb he
        (block_not_mem w hn j 771 255 (by omega) (by omega) (by omega))
        (block_not_mem w hn j 1 255 (by omega) (by omega) (by omega)),
      block_not_mem w hn j 4 253 (by omega) (by omega) (by omega),
      middle_away w (w j) hb he
        (block_not_mem w hn j 770 258 (by omega) (by omega) (by omega))⟩
  · exact front_away w (w 1797)
      (index_ne w hn 1797 0 (by omega) (by omega) (by omega))
      (index_ne w hn 1797 770 (by omega) (by omega) (by omega))
      (index_ne w hn 1797 1028 (by omega) (by omega) (by omega))
      (block_not_mem w hn 1797 771 255 (by omega) (by omega) (by omega))
      (block_not_mem w hn 1797 1 255 (by omega) (by omega) (by omega))

/-- Numerical post equality must also include phase and the outside frame.
The G bit is already included in the complete A word. -/
theorem prefix_post_unique (w : Nat → Wire) (s t : State)
    (phase : s.phase=t.phase)
    (a : regValue (wireBlock w 0 258) s.basis=regValue (wireBlock w 0 258) t.basis)
    (b : regValue (wireBlock w 770 258) s.basis=regValue (wireBlock w 770 258) t.basis)
    (e : s.basis (w 1028)=t.basis (w 1028))
    (outside : ∀q,q∉wireBlock w 0 258++wireBlock w 770 258++[w 1028] →
      s.basis q=t.basis q) : s=t := by
  apply congrArg₂ State.mk phase
  funext q
  by_cases ha : q∈wireBlock w 0 258
  · exact (regValue_eq_iff _ _ _).mp a q ha
  by_cases hb : q∈wireBlock w 770 258
  · exact (regValue_eq_iff _ _ _).mp b q hb
  by_cases he : q=w 1028
  · subst q; exact e
  exact outside q (by simp [ha,hb,he])

/-- The caller may replace the actual forward output by any complete State
proved equal to it, with independently chosen inverse outcomes. No extra
original-x register or an erasure oracle appears in this interface. -/
theorem inverse_forward_transport (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (s t : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (post : t=run (forward w) mF s) : run (inverse w) mI t=s := by
  rw [post]
  exact inverse_forward_ready w hn x s mF mI ready

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

theorem seed_support :
    wires (literalSkywalkSeed (literalSkywalkPoolSeed base) p)⊆slots.toFinset ∧
    wires (literalSkywalkUnseed (literalSkywalkPoolSeed base) p)⊆slots.toFinset := by
  have support := literalSkywalkSeed_support (literalSkywalkPoolSeed base) 258 p
    (literalSkywalkPoolSeed_widths base)
  have lift : (literalSkywalkPoolSeed base).usedWires.toFinset⊆slots.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,literalSkywalkPoolSeed,LiteralSkywalkSeedLayout.usedWires,
      List.mem_cons,List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at hq
    rcases hq with rfl|rfl|((h|h)|h)
    · exact base_integer_mem 1028 (by omega)
    · exact base_integer_mem 1797 (by omega)
    all_goals obtain ⟨old,ho,rfl⟩ := h; exact base_integer_mem old (by omega)
  exact ⟨support.1.trans lift,support.2.trans lift⟩

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

theorem resident_length : resident.length=521 := by simp [resident,wireBlock]

theorem resident_support : resident.toFinset⊆slots.toFinset := by
  intro q hq
  simp only [resident,List.mem_toFinset,List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with (h|h)|h
  all_goals
    obtain ⟨old,ho,rfl⟩ := h
    apply slot_mem
    · unfold live; omega
    · unfold omitted; omega

theorem total_site_bound (divide : Bool) :
    (wires (controlled divide)∪resident.toFinset).card ≤ 1899 := by
  have sub : wires (controlled divide)∪resident.toFinset⊆slots.toFinset :=
    Finset.union_subset (controlled_support divide) resident_support
  have card := Finset.card_le_card sub
  have exactCard : slots.toFinset.card=1899 := by
    rw [List.toFinset_card_of_nodup slots_nodup,slots_length]
  exact exactCard ▸ card

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

/-- The actual complete field segment keeps its incoming encoded pool and
phase; neither conclusion assumes a global tape-phase oracle. -/
theorem fieldSegment_pool_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run (fieldSegment divide) m s).phase=s.phase ∧
      ∀q∈skywalkPoolWires base,(run (fieldSegment divide) m s).basis q=s.basis q := by
  have result := fieldSegment_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s m input
  have before := encodedCanonical_pool_basis hn hlo origin ha Y s input
  have after := encodedCanonical_pool_basis hn hlo origin ha _ (run (fieldSegment divide) m s) result.2
  exact ⟨result.1,fun q hq => (after q hq).trans (before q hq).symm⟩

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

/-- Actual forward, clear, field, clear and compact reverse composition.
All original512 rounds and every independent record list are retained. -/
theorem fieldSegment_reverse_pool (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (initial : State) (mForward mFirst mField mLast mReverse : List Bool)
    (hin : SkywalkIntegerStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (input : EncodedCanonicalFrame origin Y 0
      (run (skywalkArithmeticClear base) mFirst (run (compressedCompactForward base 0 512) mForward initial))) :
    let recorded := run (compressedCompactForward base 0 512) mForward initial
    let prepared := run (skywalkArithmeticClear base) mFirst recorded
    let field := run (fieldSegment divide) mField prepared
    let restored := run (skywalkArithmeticClear base) mLast field
    (run (compressedCompactReverse base 0 512) mReverse restored).phase=initial.phase ∧
      (∀q∈skywalkPoolWires base,(run (compressedCompactReverse base 0 512) mReverse restored).basis q=initial.basis q) ∧
      (∀q,q∉skywalkPoolWires base →
        (run (compressedCompactReverse base 0 512) mReverse restored).basis q=restored.basis q) := by
  let recorded := run (compressedCompactForward base 0 512) mForward initial
  let prepared := run (skywalkArithmeticClear base) mFirst recorded
  let field := run (fieldSegment divide) mField prepared
  let restored := run (skywalkArithmeticClear base) mLast field
  have keeps := fieldSegment_pool_frame divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy ha x hx0 hx trace Y prepared mField input
  have recovered := clear_after_pool_update hn recorded field mFirst mLast keeps.1 keeps.2
  exact compressedCompactReverse_restore_after_outside base (skywalkShared_integer_nodup base hn)
    hlo x p (by norm_num [p]) hx0 (by norm_num [p]) (by norm_num [p]) hx
    (arith_coprime x hx0 hx) initial restored mForward mReverse hin recovered.1 recovered.2

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
theorem selectedFieldSegment_pool_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run (selectedFieldSegment divide) m s).phase=s.phase ∧
      ∀q∈skywalkPoolWires base,(run (selectedFieldSegment divide) m s).basis q=s.basis q := by
  have result := selectedFieldSegment_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s m input
  have before := encodedCanonical_pool_basis hn hlo origin ha Y s input
  have after := encodedCanonical_pool_basis hn hlo origin ha _ (run (selectedFieldSegment divide) m s) result.2
  exact ⟨result.1,fun q hq => (after q hq).trans (before q hq).symm⟩

theorem selectedFieldSegment_reverse_pool (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (initial : State) (mForward mFirst mField mLast mReverse : List Bool)
    (hin : SkywalkIntegerStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (input : EncodedCanonicalFrame origin Y 0
      (run (skywalkArithmeticClear base) mFirst (run (compressedCompactForward base 0 512) mForward initial))) :
    let recorded := run (compressedCompactForward base 0 512) mForward initial
    let prepared := run (skywalkArithmeticClear base) mFirst recorded
    let field := run (selectedFieldSegment divide) mField prepared
    let restored := run (skywalkArithmeticClear base) mLast field
    (run (compressedCompactReverse base 0 512) mReverse restored).phase=initial.phase ∧
      (∀q∈skywalkPoolWires base,(run (compressedCompactReverse base 0 512) mReverse restored).basis q=initial.basis q) ∧
      (∀q,q∉skywalkPoolWires base →
        (run (compressedCompactReverse base 0 512) mReverse restored).basis q=restored.basis q) := by
  let recorded := run (compressedCompactForward base 0 512) mForward initial
  let prepared := run (skywalkArithmeticClear base) mFirst recorded
  let field := run (selectedFieldSegment divide) mField prepared
  let restored := run (skywalkArithmeticClear base) mLast field
  have keeps := selectedFieldSegment_pool_frame divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy ha x hx0 hx trace Y prepared mField input
  have recovered := clear_after_pool_update hn recorded field mFirst mLast keeps.1 keeps.2
  exact compressedCompactReverse_restore_after_outside base (skywalkShared_integer_nodup base hn)
    hlo x p (by norm_num [p]) hx0 (by norm_num [p]) (by norm_num [p]) hx
    (arith_coprime x hx0 hx) initial restored mForward mReverse hin recovered.1 recovered.2

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
