import ShorECDLP.Submission.Entrant.V2.PointAdd
import Batteries.Tactic.OpenPrivate

/-! EDITABLE. Generic affine branch with a dirty inversion.

The V2 generic branch inverts `x₁ - x₂` with the Bennett-clean engine program (checkpoint
chain forward, result copied out, chain reversed).  The direct-output addition then runs the
whole branch and its reverse, so every inversion pays the chain four times.

Here the branch runs only the engine's forward sweep, on a copy of the engine placed ten
257-wire blocks above the add and multiply engines, and XOR-copies the result into `t2`.  The
checkpoints stay in the shifted engine until the caller's reverse uncomputes them, so every
inversion pays the chain twice.  The shifted engine lies inside the engine's reserved layout,
so the branch's wire support is unchanged.

Correctness is reduced to the V2 theorem: on every wire outside the shifted engine the new
branch agrees with the V2 branch. -/

namespace ShorECDLP
namespace Secp256k1
namespace V2

open Classical
open Arithmetic

open private shiftedView shiftedView_runShiftCircuit regValue_shiftWires clean_shiftWires_iff
  shiftCircuit_usesOnly shiftWires_lower shiftWires_nodup shiftCircuit_HPFree
  shiftCircuit_wellFormed shiftCircuit_tCount fieldSubConst_usesOnly fieldMul_usesOnly
  fieldSub_usesOnly genericPointCompute_correct genericPointCompute_tCount
  pointAddBranchActiveSupport IsPointAddFieldRegister pointAddFieldRegister_belowArithmetic
  pointAddFieldRegister_length pointAddFieldRegister_nodup pointAddFieldRegister_disjoint
  pointAddFieldAt_disjoint pointAddFieldAt_ne pointAddEngine_field_disjoint
  clean_of_preserved_outside regValue_of_preserved_outside fieldSubVal fieldInv_correct
  fieldSubConst_correct cleanAddEngine_of_branchWork cleanInvEngine_of_branchWork
  clean_fieldSubEngine_of_addEngine fieldSubConst_HPFree fieldMul_HPFree fieldSub_HPFree
  fieldSubConst_wellFormed fieldMul_wellFormed fieldSub_wellFormed fieldSubConst_tCount
  fieldMul_tCount fieldSub_tCount fieldInv_tCount fieldInv_HPFree genericPointCompute_usesOnly
  localWorkSize selectedOffset candidateOffset
  from ShorECDLP.Submission.Entrant.V2.PointAdd

/-! ## The shifted engine -/

def dirtyOffset (pw : Wire) : Wire := pointAddArithmeticOffset pw + 2570

def dirtyWork (pw : Wire) : List Wire := shiftWires (dirtyOffset pw) Engine.core.allWires

def dirtyBase (pw : Wire) : List Wire := shiftWires (dirtyOffset pw) Engine.core.lhs

def dirtyOut (pw : Wire) : List Wire := shiftWires (dirtyOffset pw) Engine.core.out

/-- `out ^= input ^ (p - 2)`, leaving the engine's checkpoints in `dirtyWork`. -/
def dirtyInv (pw : Wire) (input out : List Wire) : Circuit :=
  Arithmetic.copyReg input (dirtyBase pw) ++
    shiftCircuit (dirtyOffset pw) Engine.fwdProgram ++
    Arithmetic.copyReg (dirtyOut pw) out

/-! ## Wire facts -/

theorem mem_shift {o w : Wire} {ws : List Wire} (h : w ∈ shiftWires o ws) :
    ∃ v ∈ ws, w = o + v := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
  exact ⟨v, hv, rfl⟩

theorem shift_mem {o v : Wire} {ws : List Wire} (h : v ∈ ws) : o + v ∈ shiftWires o ws :=
  List.mem_map.mpr ⟨v, h, rfl⟩

theorem shift_sub {o : Wire} {ws vs : List Wire} (h : ∀ v ∈ ws, v ∈ vs) :
    ∀ w ∈ shiftWires o ws, w ∈ shiftWires o vs := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := mem_shift hw
  exact shift_mem (h v hv)

theorem dirty_ge (pw : Wire) :
    ∀ w ∈ dirtyWork pw, (pointAddArithmeticOffset pw : Nat) + 2570 ≤ w :=
  shiftWires_lower _ _

theorem dirty_in_engine (pw : Wire) :
    ∀ w ∈ dirtyWork pw, w ∈ shiftWires (pointAddArithmeticOffset pw) Engine.layout.allWires := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := mem_shift hw
  have hlt := Nat.add_lt_add_left (Engine.core_lt v hv) 2570
  have hcov := Engine.allWires_covers (2570 + v) (by simp only [Engine.wireBound]; omega)
  have h := shift_mem (o := pointAddArithmeticOffset pw) hcov
  simpa only [dirtyOffset, Nat.add_assoc] using h

theorem dirty_in_arith (pw : Wire) :
    ∀ w ∈ dirtyWork pw, w ∈ pointAddArithmeticWork pw := by
  intro w hw
  rw [pointAddArithmeticWork, List.mem_dedup]
  exact List.mem_append_right _ (dirty_in_engine pw w hw)

theorem dirty_in_branchWork (pw : Wire) :
    ∀ w ∈ dirtyWork pw, w ∈ pointAddBranchWork pw := by
  intro w hw
  rw [pointAddBranchWork]
  exact List.mem_append_right _ (dirty_in_arith pw w hw)

theorem field_not_dirty (pw : Wire) (r : List Wire) (hr : IsPointAddFieldRegister pw r) :
    ∀ w ∈ r, w ∉ dirtyWork pw := by
  intro w hw hd
  have h1 := pointAddFieldRegister_belowArithmetic pw r hr w hw
  have h2 := dirty_ge pw w hd
  exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le h1 (Nat.le_trans (Nat.le_add_right _ 2570) h2))

theorem addLayout_lt : ∀ v ∈ Secp256k1Instance.secpAddLayout.allWires, v < 2570 := by
  intro v hv
  show @LT.lt ℕ _ v 2570
  simp only [Secp256k1Instance.secpAddLayout, RegisterLayout.allWires,
    Secp256k1Instance.addWork, Secp256k1Instance.addScratchBlocks,
    Secp256k1Instance.blocksWires, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Secp256k1Instance.Block.wires, Secp256k1Instance.reg, Secp256k1Instance.regBlock,
    Secp256k1Instance.bitBlock, Secp256k1Instance.fieldWidth, Secp256k1Instance.baseId,
    Secp256k1Instance.exponentId, Secp256k1Instance.outId, Secp256k1Instance.initialAccId,
    List.mem_append, List.mem_range'_1] at hv
  omega

theorem mulLayout_lt : ∀ v ∈ Secp256k1Instance.secpMulLayout.allWires, v < 2570 := by
  intro v hv
  show @LT.lt ℕ _ v 2570
  simp only [Secp256k1Instance.secpMulLayout, RegisterLayout.allWires,
    Secp256k1Instance.mulWork, LowSpaceModMul.work, Secp256k1Instance.reg,
    Secp256k1Instance.regBlock, Secp256k1Instance.Block.wires, Secp256k1Instance.bitWire,
    Secp256k1Instance.mulCarry, Secp256k1Instance.mulBranch, Secp256k1Instance.mulOverflow,
    Secp256k1Instance.fieldWidth, Secp256k1Instance.baseId, Secp256k1Instance.exponentId,
    Secp256k1Instance.outId, Secp256k1Instance.initialAccId,
    Secp256k1Instance.historyStartId, List.mem_append, List.mem_cons, List.mem_range'_1,
    List.not_mem_nil, or_false] at hv
  rcases hv with (((h | h) | h) | ((h | h) | h) | h | h) <;> first | omega | (subst h; decide)

theorem addEngine_not_dirty (pw : Wire) :
    ∀ w ∈ shiftWires (pointAddArithmeticOffset pw) Secp256k1Instance.secpAddLayout.allWires,
      w ∉ dirtyWork pw := by
  intro w hw hd
  obtain ⟨v, hv, rfl⟩ := mem_shift hw
  have h1 := addLayout_lt v hv
  have h2 := dirty_ge pw _ hd
  exact Nat.lt_irrefl v (Nat.lt_of_lt_of_le h1 (Nat.le_of_add_le_add_left h2))

theorem mulEngine_not_dirty (pw : Wire) :
    ∀ w ∈ shiftWires (pointAddArithmeticOffset pw) Secp256k1Instance.secpMulLayout.allWires,
      w ∉ dirtyWork pw := by
  intro w hw hd
  obtain ⟨v, hv, rfl⟩ := mem_shift hw
  have h1 := mulLayout_lt v hv
  have h2 := dirty_ge pw _ hd
  exact Nat.lt_irrefl v (Nat.lt_of_lt_of_le h1 (Nat.le_of_add_le_add_left h2))

theorem core_lhs_sub : ∀ w ∈ Engine.core.lhs, w ∈ Engine.core.allWires := by
  intro w hw
  simp only [RegisterLayout.allWires, List.mem_append]
  tauto

theorem core_out_sub : ∀ w ∈ Engine.core.out, w ∈ Engine.core.allWires := by
  intro w hw
  simp only [RegisterLayout.allWires, List.mem_append]
  tauto

theorem core_outWork_sub : ∀ w ∈ Engine.core.out ++ Engine.core.work,
    w ∈ Engine.core.allWires := by
  intro w hw
  simp only [RegisterLayout.allWires, List.mem_append] at hw ⊢
  tauto

theorem core_lhs_not_outWork : ∀ v ∈ Engine.core.lhs, v ∉ Engine.core.out ++ Engine.core.work := by
  intro v hv hv'
  have hnd : (Engine.core.lhs ++ Engine.core.rhs ++ Engine.core.out ++ Engine.core.work).Nodup :=
    Engine.core_valid.2.2
  have h := List.nodup_append.mp hnd
  have h1 := List.nodup_append.mp h.1
  rcases List.mem_append.mp hv' with hv' | hv'
  · exact h1.2.2 v (List.mem_append_left _ hv) v hv' rfl
  · exact h.2.2 v (List.mem_append_left _ (List.mem_append_left _ hv)) v hv' rfl

theorem shift_inj {o a b : Wire} (h : o + a = o + b) : a = b := Nat.add_left_cancel h

theorem dirtyBase_not_outWork (pw : Wire) :
    ∀ w ∈ dirtyBase pw, w ∉ shiftWires (dirtyOffset pw) (Engine.core.out ++ Engine.core.work) := by
  intro w hw hw'
  obtain ⟨a, ha, rfl⟩ := mem_shift hw
  obtain ⟨b, hb, hab⟩ := mem_shift hw'
  rw [shift_inj hab] at ha
  exact core_lhs_not_outWork b ha hb

theorem shift_nodup {o : Wire} {ws : List Wire} (h : ws.Nodup) : (shiftWires o ws).Nodup :=
  shiftWires_nodup o ws h

theorem candidate_not_dirty (pw : Wire) : ∀ w ∈ pointAddCandidate pw, w ∉ dirtyWork pw := by
  intro w hw hd
  have h2 : (2570 : ℕ) + pointAddArithmeticOffset pw ≤ w := by
    have := dirty_ge pw w hd
    rwa [Nat.add_comm] at this
  simp only [pointAddCandidate, List.mem_range'_1] at hw
  simp only [pointAddArithmeticOffset, localWorkSize, selectedOffset, pointWidth] at h2
  have h3 := hw.2
  have h4 : pointWidth = 513 := rfl
  omega

/-! ## The dirty inversion -/

theorem dirtyInv_correct (pw : Wire) (input out : List Wire)
    (hinR : IsPointAddFieldRegister pw input) (houtR : IsPointAddFieldRegister pw out)
    (_hne : out ≠ input) (st : BasisState)
    (hcleanOut : Clean out st) (hcleanD : Clean (dirtyWork pw) st)
    (hbound : regValue input st < p) :
    let after := Classical.run (dirtyInv pw input out) st
    regValue out after = regValue input st ^ (p - 2) % p ∧
      ∀ w, w ∉ out → w ∉ dirtyWork pw → after w = st w := by
  intro after
  have hinD := field_not_dirty pw input hinR
  have houtD := field_not_dirty pw out houtR
  have hbaseD : ∀ w ∈ dirtyBase pw, w ∈ dirtyWork pw := shift_sub core_lhs_sub
  have hresD : ∀ w ∈ dirtyOut pw, w ∈ dirtyWork pw := shift_sub core_out_sub
  have hlenIn : input.length = 257 := pointAddFieldRegister_length pw input hinR
  have hlenOut : out.length = 257 := pointAddFieldRegister_length pw out houtR
  have hlenBase : (dirtyBase pw).length = 257 := by
    simp only [dirtyBase, shiftWires, List.length_map, Engine.core_lhs_length]
  have hlenRes : (dirtyOut pw).length = 257 := by
    simp only [dirtyOut, shiftWires, List.length_map, Engine.core_out_length]
  have hndIn := pointAddFieldRegister_nodup pw input hinR
  have hndOut := pointAddFieldRegister_nodup pw out houtR
  have hcoreNd : (Engine.core.lhs ++ Engine.core.rhs ++ Engine.core.out ++
      Engine.core.work).Nodup := Engine.core_valid.2.2
  have hlhsNd : Engine.core.lhs.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hcoreNd).1).1).1
  have houtNd : Engine.core.out.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp hcoreNd).1).2.1
  -- copy the input into the shifted base
  let s1 := Classical.run (Arithmetic.copyReg input (dirtyBase pw)) st
  have hs1v : regValue (dirtyBase pw) s1 = regValue input st := by
    apply Arithmetic.copyReg_correct input (dirtyBase pw) st (by rw [hlenBase, hlenIn])
    · rw [List.nodup_append]
      refine ⟨hndIn, shift_nodup hlhsNd, ?_⟩
      intro a ha b hb hab
      subst hab
      exact hinD a ha (hbaseD a hb)
    · intro w hw
      exact hcleanD w (hbaseD w hw)
  have hs1f : ∀ w, w ∉ dirtyBase pw → s1 w = st w := fun w hw =>
    Arithmetic.copyReg_other w input (dirtyBase pw) st hw
  -- the shifted forward sweep
  let s2 := Classical.run (shiftCircuit (dirtyOffset pw) Engine.fwdProgram) s1
  have hview := shiftedView_runShiftCircuit (dirtyOffset pw) Engine.fwdProgram s1
  have hlhs : regValue Engine.core.lhs (shiftedView (dirtyOffset pw) s1) < p := by
    rw [← regValue_shiftWires]
    change regValue (dirtyBase pw) s1 < p
    rw [hs1v]
    exact hbound
  have hcl : Clean (Engine.core.out ++ Engine.core.work) (shiftedView (dirtyOffset pw) s1) := by
    rw [← clean_shiftWires_iff]
    intro w hw
    have hwD : w ∈ dirtyWork pw := shift_sub core_outWork_sub w hw
    have hnb : w ∉ dirtyBase pw := fun hb => dirtyBase_not_outWork pw w hb hw
    rw [hs1f w hnb]
    exact hcleanD w hwD
  obtain ⟨hfv, _⟩ := Engine.fwd_correct _ hlhs hcl
  have hs2v : regValue (dirtyOut pw) s2 = regValue input st ^ (p - 2) % p := by
    have h := regValue_shiftWires (dirtyOffset pw) Engine.core.out s2
    change regValue (dirtyOut pw) s2 = _ at h
    rw [h, hview, hfv, ← regValue_shiftWires]
    change regValue (dirtyBase pw) s1 ^ (p - 2) % p = _
    rw [hs1v]
  have hs2f : ∀ w, w ∉ dirtyWork pw → s2 w = s1 w := by
    intro w hw
    exact (shiftCircuit_usesOnly (dirtyOffset pw) _ _ Engine.fwd_usesOnly).preservesOutside
      s1 w hw
  -- copy the result out
  have hcleanOut2 : Clean out s2 := by
    intro w hw
    rw [hs2f w (houtD w hw), hs1f w (fun hb => houtD w hw (hbaseD w hb))]
    exact hcleanOut w hw
  have hafter : after = Classical.run (Arithmetic.copyReg (dirtyOut pw) out) s2 := by
    simp only [after, dirtyInv, Classical.run_append]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hafter, Arithmetic.copyReg_correct (dirtyOut pw) out s2 (by rw [hlenOut, hlenRes])
      ?_ hcleanOut2, hs2v]
    rw [List.nodup_append]
    refine ⟨shift_nodup houtNd, hndOut, ?_⟩
    intro a ha b hb hab
    subst hab
    exact houtD a hb (hresD a ha)
  · intro w hw hwD
    rw [hafter, Arithmetic.copyReg_other w _ _ s2 hw, hs2f w hwD,
      hs1f w (fun hb => hwD (hbaseD w hb))]

theorem bits_eq_of_regValue_eq :
    ∀ (ws : List Wire) (s t : BasisState),
      regValue ws s = regValue ws t → ∀ w ∈ ws, s w = t w := by
  intro ws
  induction ws with
  | nil => intro s t _ w hw; simp at hw
  | cons v vs ih =>
    intro s t h w hw
    rw [regValue_cons, regValue_cons] at h
    have hv : s v = t v := by
      cases hs : s v <;> cases ht : t v <;> first | rfl | (simp [hs, ht] at h; omega)
    have hrest : regValue vs s = regValue vs t := by
      rw [hv] at h
      omega
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hv
    · exact ih s t hrest w hw

theorem run_agree_outside (c : Circuit) (U D : List Wire) (hc : CircuitUsesOnly U c)
    (hUD : ∀ w ∈ U, w ∉ D) (s t : BasisState) (hst : ∀ w, w ∉ D → s w = t w) :
    ∀ w, w ∉ D → Classical.run c s w = Classical.run c t w := by
  intro w hw
  by_cases hU : w ∈ U
  · exact CircuitUsesOnly.run_congr hc (fun v hv => hst v (hUD v hv)) w hU
  · rw [CircuitUsesOnly.preservesOutside hc s w hU, CircuitUsesOnly.preservesOutside hc t w hU]
    exact hst w hw

/-! ## The generic branch, split around its inversion -/

def genericPrefix (pw : Wire) (xC yC : Fp) : Circuit :=
  fieldSubConst (pointAddArithmeticOffset pw) (pointAddY pw) yC.val (pointAddT0 pw) ++
    fieldSubConst (pointAddArithmeticOffset pw) (pointAddX pw) xC.val (pointAddT1 pw)

def genericSuffix (pw : Wire) (xC yC : Fp) : Circuit :=
  let offset := pointAddArithmeticOffset pw
  let x := pointAddX pw
  let y := pointAddY pw
  let t0 := pointAddT0 pw
  let t1 := pointAddT1 pw
  let t2 := pointAddT2 pw
  let t3 := pointAddT3 pw
  let t4 := pointAddT4 pw
  let t5 := pointAddT5 pw
  let numerator := fieldSubConst offset y yC.val t0
  let denominator := fieldSubConst offset x xC.val t1
  let slope := fieldMul offset t0 t2 t3
  let slopeSq := fieldMul offset t3 t3 t0
  let minusX := fieldSub offset t0 x t1
  let xOut := fieldSubConst offset t1 xC.val t5
  let xDifference := fieldSub offset x t5 t0
  let yProduct := fieldMul offset t3 t0 t1
  let yOut := fieldSub offset t1 y t4
  slope ++ denominator.reverse ++ numerator.reverse ++ slopeSq ++ minusX ++ xOut ++
    minusX.reverse ++ slopeSq.reverse ++ xDifference ++ yProduct ++ yOut

theorem genericPointCompute_split (pw : Wire) (xC yC : Fp) :
    genericPointCompute pw xC yC =
      genericPrefix pw xC yC ++
        fieldInv (pointAddArithmeticOffset pw) (pointAddT1 pw) (pointAddT2 pw) ++
        genericSuffix pw xC yC := by
  simp only [genericPointCompute, genericPrefix, genericSuffix, List.append_assoc]

/-- The generic affine branch with the dirty inversion. -/
def genericPointComputeD (pw : Wire) (xC yC : Fp) : Circuit :=
  genericPrefix pw xC yC ++ dirtyInv pw (pointAddT1 pw) (pointAddT2 pw) ++
    genericSuffix pw xC yC

def suffixSupport (pw : Wire) : List Wire :=
  pointAddX pw ++ pointAddY pw ++ pointAddT0 pw ++ pointAddT1 pw ++ pointAddT2 pw ++
    pointAddT3 pw ++ pointAddT4 pw ++ pointAddT5 pw ++
    shiftWires (pointAddArithmeticOffset pw) Secp256k1Instance.secpAddLayout.allWires ++
    shiftWires (pointAddArithmeticOffset pw) Secp256k1Instance.secpMulLayout.allWires

theorem mul_in (pw : Wire) (a b c : List Wire) (ha : ∀ w ∈ a, w ∈ suffixSupport pw)
    (hb : ∀ w ∈ b, w ∈ suffixSupport pw) (hc : ∀ w ∈ c, w ∈ suffixSupport pw) :
    CircuitUsesOnly (suffixSupport pw) (fieldMul (pointAddArithmeticOffset pw) a b c) := by
  apply usesOnly_mono (fieldMul_usesOnly _ a b c)
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with ((h | h) | h) | h
  · exact ha w h
  · exact hb w h
  · exact hc w h
  · exact List.mem_append_right _ h

theorem sub_in (pw : Wire) (a b c : List Wire) (ha : ∀ w ∈ a, w ∈ suffixSupport pw)
    (hb : ∀ w ∈ b, w ∈ suffixSupport pw) (hc : ∀ w ∈ c, w ∈ suffixSupport pw) :
    CircuitUsesOnly (suffixSupport pw) (fieldSub (pointAddArithmeticOffset pw) a b c) := by
  apply usesOnly_mono (fieldSub_usesOnly _ a b c)
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with ((h | h) | h) | h
  · exact ha w h
  · exact hb w h
  · exact hc w h
  · exact List.mem_append_left _ (List.mem_append_right _ h)

theorem subc_in (pw : Wire) (a : List Wire) (k : Nat) (c : List Wire)
    (ha : ∀ w ∈ a, w ∈ suffixSupport pw) (hc : ∀ w ∈ c, w ∈ suffixSupport pw) :
    CircuitUsesOnly (suffixSupport pw) (fieldSubConst (pointAddArithmeticOffset pw) a k c) := by
  apply usesOnly_mono (fieldSubConst_usesOnly _ a k c)
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with (h | h) | h
  · exact ha w h
  · exact hc w h
  · exact List.mem_append_left _ (List.mem_append_right _ h)

theorem genericSuffix_usesOnly (pw : Wire) (xC yC : Fp) :
    CircuitUsesOnly (suffixSupport pw) (genericSuffix pw xC yC) := by
  have hx : ∀ w ∈ pointAddX pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have hy : ∀ w ∈ pointAddY pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h0 : ∀ w ∈ pointAddT0 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h1 : ∀ w ∈ pointAddT1 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h2 : ∀ w ∈ pointAddT2 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h3 : ∀ w ∈ pointAddT3 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h4 : ∀ w ∈ pointAddT4 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h5 : ∀ w ∈ pointAddT5 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  simp only [genericSuffix]
  refine usesOnly_append (usesOnly_append (usesOnly_append (usesOnly_append (usesOnly_append
    (usesOnly_append (usesOnly_append (usesOnly_append (usesOnly_append (usesOnly_append
      ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact mul_in pw _ _ _ h0 h2 h3
  · exact usesOnly_reverse (subc_in pw _ _ _ hx h1)
  · exact usesOnly_reverse (subc_in pw _ _ _ hy h0)
  · exact mul_in pw _ _ _ h3 h3 h0
  · exact sub_in pw _ _ _ h0 hx h1
  · exact subc_in pw _ _ _ h1 h5
  · exact usesOnly_reverse (sub_in pw _ _ _ h0 hx h1)
  · exact usesOnly_reverse (mul_in pw _ _ _ h3 h3 h0)
  · exact sub_in pw _ _ _ hx h5 h0
  · exact mul_in pw _ _ _ h3 h0 h1
  · exact sub_in pw _ _ _ h1 hy h4

theorem suffixSupport_not_dirty (pw : Wire) : ∀ w ∈ suffixSupport pw, w ∉ dirtyWork pw := by
  intro w hw
  simp only [suffixSupport, List.mem_append] at hw
  rcases hw with (((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · exact field_not_dirty pw _ (by simp [IsPointAddFieldRegister]) w h
  · exact field_not_dirty pw _ (by simp [IsPointAddFieldRegister]) w h
  · exact field_not_dirty pw _ (by simp [IsPointAddFieldRegister]) w h
  · exact field_not_dirty pw _ (by simp [IsPointAddFieldRegister]) w h
  · exact field_not_dirty pw _ (by simp [IsPointAddFieldRegister]) w h
  · exact field_not_dirty pw _ (by simp [IsPointAddFieldRegister]) w h
  · exact field_not_dirty pw _ (by simp [IsPointAddFieldRegister]) w h
  · exact field_not_dirty pw _ (by simp [IsPointAddFieldRegister]) w h
  · exact addEngine_not_dirty pw w h
  · exact mulEngine_not_dirty pw w h

/-! ## Correctness -/

theorem fermat_val [Fact (Nat.Prime p)] (a : Fp) (ha : a ≠ 0) :
    a.val ^ (p - 2) % p = (a⁻¹).val := by
  have h1 : (((a.val ^ (p - 2) : ℕ)) : Fp) = a⁻¹ := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val, fermat_inv a ha]
  have h2 := congrArg ZMod.val h1
  rwa [ZMod.val_natCast] at h2

theorem genericPointComputeD_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire) (xR yR xC yC : Fp)
    (hx : xR ≠ xC)
    (st : BasisState)
    (hxReg : regValue (pointAddX workStart) st = xR.val)
    (hyReg : regValue (pointAddY workStart) st = yR.val)
    (hclean : Clean (pointAddBranchWork workStart) st)
    (hcleanT5 : Clean (pointAddT5 workStart) st) :
    let after := Classical.run
      (genericPointComputeD workStart xC yC) st
    regValue (pointAddT5 workStart) after =
        (genericX xR yR xC yC).val ∧
      regValue (pointAddT4 workStart) after =
        (genericY xR yR xC yC).val ∧
      Clean (pointAddCandidate workStart) after := by
  intro after
  have horig := genericPointCompute_correct workStart xR yR xC yC hx st hxReg hyReg hclean
    hcleanT5
  have hX : IsPointAddFieldRegister workStart (pointAddX workStart) := by
    simp [IsPointAddFieldRegister]
  have hY : IsPointAddFieldRegister workStart (pointAddY workStart) := by
    simp [IsPointAddFieldRegister]
  have hT0 : IsPointAddFieldRegister workStart (pointAddT0 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT1 : IsPointAddFieldRegister workStart (pointAddT1 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT2 : IsPointAddFieldRegister workStart (pointAddT2 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT4 : IsPointAddFieldRegister workStart (pointAddT4 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT5 : IsPointAddFieldRegister workStart (pointAddT5 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT1T0 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT1, pointAddT0] using
      pointAddFieldAt_disjoint workStart 3 2 (by norm_num)
  have hT2T0 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT2, pointAddT0] using
      pointAddFieldAt_disjoint workStart 4 2 (by norm_num)
  have hT2T1 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT2, pointAddT1] using
      pointAddFieldAt_disjoint workStart 4 3 (by norm_num)
  have hXT0 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT0 workStart) := by
    simpa [pointAddX, pointAddT0] using
      pointAddFieldAt_disjoint workStart 0 2 (by norm_num)
  have hcleanT0 : Clean (pointAddT0 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT1 : Clean (pointAddT1 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT2 : Clean (pointAddT2 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanAdd := cleanAddEngine_of_branchWork workStart st hclean
  have hcleanInv := cleanInvEngine_of_branchWork workStart st hclean
  let numerator := fieldSubConst
    (pointAddArithmeticOffset workStart)
    (pointAddY workStart) yC.val (pointAddT0 workStart)
  let afterNumerator := Classical.run numerator st
  have hn := fieldSubConst_correct workStart
    (pointAddY workStart) (pointAddT0 workStart) yC.val
    hY hT0 (by
      simpa [pointAddY, pointAddT0] using
        pointAddFieldAt_ne workStart 2 1 (by norm_num))
    st hcleanT0
    (clean_fieldSubEngine_of_addEngine workStart st hcleanAdd)
    (by simpa [hyReg] using yR.val_lt) yC.val_lt
  dsimp only at hn
  change regValue (pointAddT0 workStart) afterNumerator =
      (regValue (pointAddY workStart) st + p - yC.val) % p ∧
    ∀ w, w ∉ pointAddT0 workStart →
      afterNumerator w = st w at hn
  let denominator := fieldSubConst
    (pointAddArithmeticOffset workStart)
    (pointAddX workStart) xC.val (pointAddT1 workStart)
  let afterDenominator := Classical.run denominator afterNumerator
  have hcleanT1N := clean_of_preserved_outside
    hT1T0 hcleanT1 hn.2
  have hcleanAddN := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanAdd hn.2
  have hxN := regValue_of_preserved_outside hXT0 hn.2
  have hd := fieldSubConst_correct workStart
    (pointAddX workStart) (pointAddT1 workStart) xC.val
    hX hT1 (by
      simpa [pointAddX, pointAddT1] using
        pointAddFieldAt_ne workStart 3 0 (by norm_num))
    afterNumerator hcleanT1N
    (clean_fieldSubEngine_of_addEngine workStart afterNumerator hcleanAddN)
    (by rw [hxN, hxReg]; exact xR.val_lt) xC.val_lt
  dsimp only at hd
  change regValue (pointAddT1 workStart) afterDenominator =
      (regValue (pointAddX workStart) afterNumerator + p - xC.val) % p ∧
    ∀ w, w ∉ pointAddT1 workStart →
      afterDenominator w = afterNumerator w at hd
  have hdVal : regValue (pointAddT1 workStart) afterDenominator =
      (xR - xC).val := by
    calc
      regValue (pointAddT1 workStart) afterDenominator =
          (xR.val + p - xC.val) % p := by
        simpa [hxN, hxReg] using hd.1
      _ = (xR - xC).val := fieldSubVal xR xC
  have hcleanT2N := clean_of_preserved_outside hT2T0 hcleanT2 hn.2
  have hcleanT2D := clean_of_preserved_outside hT2T1 hcleanT2N hd.2
  have hcleanInvN := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Engine.layout.allWires
      (pointAddT0 workStart) hT0)
    hcleanInv hn.2
  have hcleanInvD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Engine.layout.allWires
      (pointAddT1 workStart) hT1)
    hcleanInvN hd.2
  have hdenNonzero :
      ((regValue (pointAddT1 workStart) afterDenominator : Nat) : Fp) ≠ 0 := by
    rw [hdVal, ZMod.natCast_zmod_val]
    exact sub_ne_zero.mpr hx
  have hi := fieldInv_correct workStart
    (pointAddT1 workStart) (pointAddT2 workStart)
    hT1 hT2 (by
      simpa [pointAddT1, pointAddT2] using
        pointAddFieldAt_ne workStart 4 3 (by norm_num))
    afterDenominator hcleanT2D hcleanInvD
    (by rw [hdVal]; exact (xR - xC).val_lt) hdenNonzero
  dsimp only at hi
  have hcleanD : Clean (dirtyWork workStart) afterDenominator := by
    intro w hw
    have h1 : w ∉ pointAddT1 workStart := fun h => field_not_dirty _ _ hT1 w h hw
    have h0 : w ∉ pointAddT0 workStart := fun h => field_not_dirty _ _ hT0 w h hw
    rw [hd.2 w h1, hn.2 w h0]
    exact hclean w (dirty_in_branchWork workStart w hw)
  have hdi := dirtyInv_correct workStart (pointAddT1 workStart) (pointAddT2 workStart) hT1 hT2
    (by simpa [pointAddT1, pointAddT2] using pointAddFieldAt_ne workStart 4 3 (by norm_num))
    afterDenominator hcleanT2D hcleanD (by rw [hdVal]; exact (xR - xC).val_lt)
  dsimp only at hdi
  have hagree1 : ∀ w, w ∉ dirtyWork workStart →
      Classical.run (dirtyInv workStart (pointAddT1 workStart) (pointAddT2 workStart))
          afterDenominator w =
        Classical.run (fieldInv (pointAddArithmeticOffset workStart) (pointAddT1 workStart)
          (pointAddT2 workStart)) afterDenominator w := by
    intro w hw
    by_cases ht2 : w ∈ pointAddT2 workStart
    · apply bits_eq_of_regValue_eq (pointAddT2 workStart) _ _ _ w ht2
      rw [hdi.1, hi.1, hdVal, ZMod.natCast_zmod_val, fermat_val _ (sub_ne_zero.mpr hx)]
    · rw [hdi.2 w ht2 hw, hi.2 w ht2]
  have hprefix : Classical.run (genericPrefix workStart xC yC) st = afterDenominator := by
    simp only [genericPrefix, Classical.run_append]
    rfl
  have hagree : ∀ w, w ∉ dirtyWork workStart →
      after w = Classical.run (genericPointCompute workStart xC yC) st w := by
    intro w hw
    simp only [after, genericPointComputeD, genericPointCompute_split, Classical.run_append,
      hprefix]
    exact run_agree_outside _ _ _ (genericSuffix_usesOnly workStart xC yC)
      (suffixSupport_not_dirty workStart) _ _ hagree1 w hw
  obtain ⟨o1, o2, o3⟩ := horig
  refine ⟨?_, ?_, ?_⟩
  · rw [← o1]
    exact regValue_congr _ _ _ (fun w hw => hagree w (field_not_dirty _ _ hT5 w hw))
  · rw [← o2]
    exact regValue_congr _ _ _ (fun w hw => hagree w (field_not_dirty _ _ hT4 w hw))
  · intro w hw
    rw [hagree w (candidate_not_dirty workStart w hw)]
    exact o3 w hw

/-! ## Structure and cost -/

theorem dirtyInv_usesOnly (pw : Wire) (input out : List Wire) :
    CircuitUsesOnly (input ++ out ++ dirtyWork pw) (dirtyInv pw input out) := by
  have hbaseD : ∀ w ∈ dirtyBase pw, w ∈ dirtyWork pw := shift_sub core_lhs_sub
  have hresD : ∀ w ∈ dirtyOut pw, w ∈ dirtyWork pw := shift_sub core_out_sub
  refine usesOnly_append (usesOnly_append ?_ ?_) ?_
  · apply Arithmetic.copyReg_usesOnly
    · intro w h; exact List.mem_append_left _ (List.mem_append_left _ h)
    · intro w h; exact List.mem_append_right _ (hbaseD w h)
  · exact usesOnly_mono (shiftCircuit_usesOnly _ _ _ Engine.fwd_usesOnly)
      (fun w h => List.mem_append_right _ h)
  · apply Arithmetic.copyReg_usesOnly
    · intro w h; exact List.mem_append_right _ (hresD w h)
    · intro w h; exact List.mem_append_left _ (List.mem_append_right _ h)

theorem dirtyInv_HPFree (pw : Wire) (input out : List Wire) :
    Classical.HPFree (dirtyInv pw input out) := by
  simp only [dirtyInv, Classical.hpFree_append]
  exact ⟨⟨Arithmetic.copyReg_HPFree _ _, shiftCircuit_HPFree _ _ Engine.fwd_HPFree⟩,
    Arithmetic.copyReg_HPFree _ _⟩

theorem dirtyInv_wellFormed (pw : Wire) (input out : List Wire)
    (hinR : IsPointAddFieldRegister pw input) (houtR : IsPointAddFieldRegister pw out) :
    CircuitWellFormed (dirtyInv pw input out) := by
  have hinD := field_not_dirty pw input hinR
  have houtD := field_not_dirty pw out houtR
  have hbaseD : ∀ w ∈ dirtyBase pw, w ∈ dirtyWork pw := shift_sub core_lhs_sub
  have hresD : ∀ w ∈ dirtyOut pw, w ∈ dirtyWork pw := shift_sub core_out_sub
  have hcoreNd : (Engine.core.lhs ++ Engine.core.rhs ++ Engine.core.out ++
      Engine.core.work).Nodup := Engine.core_valid.2.2
  have hlhsNd : Engine.core.lhs.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hcoreNd).1).1).1
  have houtNd : Engine.core.out.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp hcoreNd).1).2.1
  simp only [dirtyInv, circuitWellFormed_append]
  refine ⟨⟨Arithmetic.copyReg_wellFormed _ _ ?_, shiftCircuit_wellFormed _ _ Engine.fwd_wellFormed⟩,
    Arithmetic.copyReg_wellFormed _ _ ?_⟩
  · rw [List.nodup_append]
    refine ⟨pointAddFieldRegister_nodup pw input hinR, shift_nodup hlhsNd, ?_⟩
    intro a ha b hb hab
    subst hab
    exact hinD a ha (hbaseD a hb)
  · rw [List.nodup_append]
    refine ⟨shift_nodup houtNd, pointAddFieldRegister_nodup pw out houtR, ?_⟩
    intro a ha b hb hab
    subst hab
    exact houtD a hb (hresD a ha)

theorem dirtyInv_tCount (pw : Wire) (input out : List Wire) :
    tCount (dirtyInv pw input out) = Engine.fwdCost := by
  simp [dirtyInv, tCount_append, Arithmetic.copyReg_tCount, shiftCircuit_tCount, Engine.fwd_tCount]

theorem suffix_sub_active (pw : Wire) :
    ∀ w ∈ suffixSupport pw, w ∈ pointAddBranchActiveSupport pw := by
  intro w hw
  simp only [suffixSupport, List.mem_append] at hw
  simp only [pointAddBranchActiveSupport, List.mem_append]
  rcases hw with (((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) <;>
    simp only [h, or_true, true_or]

theorem genericPointComputeD_usesOnly (pw : Wire) (xC yC : Fp) :
    CircuitUsesOnly (pointAddBranchActiveSupport pw) (genericPointComputeD pw xC yC) := by
  have hx : ∀ w ∈ pointAddX pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have hy : ∀ w ∈ pointAddY pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h0 : ∀ w ∈ pointAddT0 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h1 : ∀ w ∈ pointAddT1 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  have h2 : ∀ w ∈ pointAddT2 pw, w ∈ suffixSupport pw := by
    intro w h; simp only [suffixSupport, List.mem_append]; tauto
  refine usesOnly_append (usesOnly_append ?_ ?_) ?_
  · exact usesOnly_mono (usesOnly_append (subc_in pw _ _ _ hy h0) (subc_in pw _ _ _ hx h1))
      (suffix_sub_active pw)
  · apply usesOnly_mono (dirtyInv_usesOnly pw _ _)
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact suffix_sub_active pw w (h1 w hw)
      · exact suffix_sub_active pw w (h2 w hw)
    · have he := dirty_in_engine pw w hw
      simp only [pointAddBranchActiveSupport, List.mem_append]
      simp only [he, or_true]
  · exact usesOnly_mono (genericSuffix_usesOnly pw xC yC) (suffix_sub_active pw)

theorem genericSuffix_HPFree (pw : Wire) (xC yC : Fp) :
    Classical.HPFree (genericSuffix pw xC yC) := by
  simp [genericSuffix, fieldSubConst_HPFree, fieldMul_HPFree, fieldSub_HPFree,
    Arithmetic.hpFree_reverse]

theorem genericPrefix_HPFree (pw : Wire) (xC yC : Fp) :
    Classical.HPFree (genericPrefix pw xC yC) := by
  simp [genericPrefix, fieldSubConst_HPFree]

theorem genericPointComputeD_HPFree (pw : Wire) (xC yC : Fp) :
    Classical.HPFree (genericPointComputeD pw xC yC) := by
  rw [genericPointComputeD, Classical.hpFree_append, Classical.hpFree_append]
  exact ⟨⟨genericPrefix_HPFree pw xC yC, dirtyInv_HPFree _ _ _⟩, genericSuffix_HPFree pw xC yC⟩

theorem genericSuffix_wellFormed (pw : Wire) (xC yC : Fp) :
    CircuitWellFormed (genericSuffix pw xC yC) := by
  simp [genericSuffix, fieldSubConst_wellFormed, fieldMul_wellFormed, fieldSub_wellFormed,
    IsPointAddFieldRegister, Arithmetic.wellFormed_reverse]

theorem genericPrefix_wellFormed (pw : Wire) (xC yC : Fp) :
    CircuitWellFormed (genericPrefix pw xC yC) := by
  simp [genericPrefix, fieldSubConst_wellFormed, IsPointAddFieldRegister]

theorem genericPointComputeD_wellFormed (pw : Wire) (xC yC : Fp) :
    CircuitWellFormed (genericPointComputeD pw xC yC) := by
  have hd := dirtyInv_wellFormed pw (pointAddT1 pw) (pointAddT2 pw)
    (by simp [IsPointAddFieldRegister]) (by simp [IsPointAddFieldRegister])
  rw [genericPointComputeD, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨genericPrefix_wellFormed pw xC yC, hd⟩, genericSuffix_wellFormed pw xC yC⟩

theorem genericPointComputeD_tCount (pw : Wire) (xC yC : Fp) :
    tCount (genericPointComputeD pw xC yC) = 5309967978 := by
  have h := genericPointCompute_tCount pw xC yC
  rw [genericPointCompute_split, tCount_append, tCount_append, fieldInv_tCount] at h
  rw [genericPointComputeD, tCount_append, tCount_append, dirtyInv_tCount]
  simp only [Engine.fwdCost]
  omega

end V2
end Secp256k1
end ShorECDLP
