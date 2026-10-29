import ShorECDLP.Submission.Entrant.FastGates
import Batteries.Tactic.OpenPrivate

/-! EDITABLE. The wires actually touched by the single-pass controlled point addition.

The single-pass `fastOut` writes its result straight into the output register. It never
touches the V2 `selected` register (the last 513 wires of the local point-addition block),
and of the V2 `choice` register it only uses the first wire, as the branch ancilla. The
support below omits both, so the qubit envelope can be certified without them. No register
position changes. -/

namespace ShorECDLP
namespace Secp256k1
namespace V2

open Classical
open Arithmetic
open Challenge

open private pointAddBranchActiveSupport genericPointCompute_usesOnly
  packFinitePoint_usesOnly_pointAdd pointAddFlags_usesOnly controlledCopyReg_usesOnly
  from ShorECDLP.Submission.Entrant.V2.PointAdd

/-- Local point-addition wires below `selected`, followed by the arithmetic engines. -/
def tightPW (pw : Wire) : List Wire := List.range' pw 3599 ++ pointAddArithmeticWork pw

private theorem range_sub (pw a n : Nat) (h : a + n ≤ 3599) :
    ∀ w ∈ List.range' (pw + a) n, w ∈ tightPW pw := by
  intro w hw
  apply List.mem_append_left
  simp only [List.mem_range'_1] at hw ⊢
  omega

private theorem engine_sub (pw w : Wire)
    (hw : w ∈ shiftWires (pointAddArithmeticOffset pw) Secp256k1Instance.secpAddLayout.allWires ∨
      w ∈ shiftWires (pointAddArithmeticOffset pw) Secp256k1Instance.secpMulLayout.allWires ∨
        w ∈ shiftWires (pointAddArithmeticOffset pw) Engine.layout.allWires) :
    w ∈ tightPW pw := by
  apply List.mem_append_right
  unfold pointAddArithmeticWork
  rw [List.mem_dedup]
  rcases hw with h | h | h
  · exact List.mem_append_left _ (List.mem_append_left _ h)
  · exact List.mem_append_left _ (List.mem_append_right _ h)
  · exact List.mem_append_right _ h

theorem tight_x (pw : Wire) : ∀ w ∈ pointAddX pw, w ∈ tightPW pw := by
  have e : pointAddX pw = List.range' (pw + 0) 257 := rfl
  rw [e]; exact range_sub pw 0 257 (by norm_num)
theorem tight_y (pw : Wire) : ∀ w ∈ pointAddY pw, w ∈ tightPW pw := by
  have e : pointAddY pw = List.range' (pw + 257) 257 := rfl
  rw [e]; exact range_sub pw 257 257 (by norm_num)
theorem tight_t0 (pw : Wire) : ∀ w ∈ pointAddT0 pw, w ∈ tightPW pw := by
  have e : pointAddT0 pw = List.range' (pw + 514) 257 := rfl
  rw [e]; exact range_sub pw 514 257 (by norm_num)
theorem tight_t1 (pw : Wire) : ∀ w ∈ pointAddT1 pw, w ∈ tightPW pw := by
  have e : pointAddT1 pw = List.range' (pw + 771) 257 := rfl
  rw [e]; exact range_sub pw 771 257 (by norm_num)
theorem tight_t2 (pw : Wire) : ∀ w ∈ pointAddT2 pw, w ∈ tightPW pw := by
  have e : pointAddT2 pw = List.range' (pw + 1028) 257 := rfl
  rw [e]; exact range_sub pw 1028 257 (by norm_num)
theorem tight_t3 (pw : Wire) : ∀ w ∈ pointAddT3 pw, w ∈ tightPW pw := by
  have e : pointAddT3 pw = List.range' (pw + 1285) 257 := rfl
  rw [e]; exact range_sub pw 1285 257 (by norm_num)
theorem tight_t4 (pw : Wire) : ∀ w ∈ pointAddT4 pw, w ∈ tightPW pw := by
  have e : pointAddT4 pw = List.range' (pw + 1542) 257 := rfl
  rw [e]; exact range_sub pw 1542 257 (by norm_num)
theorem tight_t5 (pw : Wire) : ∀ w ∈ pointAddT5 pw, w ∈ tightPW pw := by
  have e : pointAddT5 pw = List.range' (pw + 1799) 257 := rfl
  rw [e]; exact range_sub pw 1799 257 (by norm_num)
theorem tight_cand (pw : Wire) : ∀ w ∈ pointAddCandidate pw, w ∈ tightPW pw := by
  have e : pointAddCandidate pw = List.range' (pw + 3086) 513 := rfl
  rw [e]; exact range_sub pw 3086 513 (by norm_num)

private theorem one_sub (pw a : Nat) (h : a < 3599) : pw + a ∈ tightPW pw :=
  range_sub pw a 1 (by omega) (pw + a) (by simp)

theorem tight_flagWork (pw : Wire) : ∀ w ∈ pointAddFlagWork pw, w ∈ tightPW pw := by
  have e1 : pointAddConst pw = List.range' (pw + 1799) 256 := rfl
  have e2 : pointAddZeroHistory pw = [pw + 2055] := rfl
  have e3 : pointAddXDifference pw = List.range' (pw + 2056) 256 := rfl
  have e4 : pointAddXHistory pw = List.range' (pw + 2312) 256 := rfl
  have e5 : pointAddYDifference pw = List.range' (pw + 2568) 256 := rfl
  have e6 : pointAddYHistory pw = List.range' (pw + 2824) 256 := rfl
  have f0 : pointAddInfinityFlag pw = pw + 3080 := rfl
  have f1 : pointAddXEqFlag pw = pw + 3081 := rfl
  have f2 : pointAddYNegFlag pw = pw + 3082 := rfl
  have f3 : pointAddGenericFlag pw = pw + 3083 := rfl
  have f4 : pointAddPairFlag pw = pw + 3084 := rfl
  have f5 : pointAddDoubleFlag pw = pw + 3085 := rfl
  intro w hw
  simp only [pointAddFlagWork, e1, e2, e3, e4, e5, e6, f0, f1, f2, f3, f4, f5, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (((((h | h) | h) | h) | h) | h) | h | h | h | h | h | h
  · exact range_sub pw 1799 256 (by norm_num) w h
  · subst h; exact one_sub pw 2055 (by norm_num)
  · exact range_sub pw 2056 256 (by norm_num) w h
  · exact range_sub pw 2312 256 (by norm_num) w h
  · exact range_sub pw 2568 256 (by norm_num) w h
  · exact range_sub pw 2824 256 (by norm_num) w h
  · subst h; exact one_sub pw 3080 (by norm_num)
  · subst h; exact one_sub pw 3081 (by norm_num)
  · subst h; exact one_sub pw 3082 (by norm_num)
  · subst h; exact one_sub pw 3083 (by norm_num)
  · subst h; exact one_sub pw 3084 (by norm_num)
  · subst h; exact one_sub pw 3085 (by norm_num)

theorem tight_activeSupport (pw : Wire) :
    ∀ w ∈ pointAddBranchActiveSupport pw, w ∈ tightPW pw := by
  intro w hw
  simp only [pointAddBranchActiveSupport, List.mem_append] at hw
  rcases hw with h | h | h | h | h | h | h | h | h | h
  · exact tight_x pw w h
  · exact tight_y pw w h
  · exact tight_t0 pw w h
  · exact tight_t1 pw w h
  · exact tight_t2 pw w h
  · exact tight_t3 pw w h
  · exact tight_t4 pw w h
  · exact tight_t5 pw w h
  · exact tight_cand pw w h
  · exact engine_sub pw w h

theorem setup_usesOnly_tight (pointReg : List Wire) (pw : Wire) (xC yC : Fp) :
    CircuitUsesOnly (pointReg ++ tightPW pw) (pointAddSetup pointReg pw xC yC) := by
  have hx : CircuitUsesOnly (pointReg ++ tightPW pw) (pointAddCopyX pointReg pw) := by
    rw [pointAddCopyX]
    apply Arithmetic.copyReg_usesOnly
    · intro w hw
      exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hw))
    · intro w hw
      exact List.mem_append_right _ (tight_x pw w (List.mem_of_mem_take hw))
  have hy : CircuitUsesOnly (pointReg ++ tightPW pw) (pointAddCopyY pointReg pw) := by
    rw [pointAddCopyY]
    apply Arithmetic.copyReg_usesOnly
    · intro w hw
      exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hw))
    · intro w hw
      exact List.mem_append_right _ (tight_y pw w (List.mem_of_mem_take hw))
  have hflags := usesOnly_mono (ys := pointReg ++ tightPW pw)
      (pointAddFlags_usesOnly pointReg pw xC yC) (by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (tight_flagWork pw w h))
  rw [pointAddSetup, pointAddCoordinateCopies]
  exact usesOnly_append (usesOnly_append hx hy) hflags

theorem genericK_usesOnly_tight (pw : Wire) (xC yC : Fp) :
    CircuitUsesOnly (tightPW pw) (fastGenericK pw xC yC) :=
  usesOnly_mono (usesOnly_append (genericPointComputeD_usesOnly pw xC yC)
    (packFinitePoint_usesOnly_pointAdd pw)) (tight_activeSupport pw)

theorem loadCand_usesOnly_tight (pw : Wire) (v : Nat) :
    CircuitUsesOnly (tightPW pw) (loadConst (pointAddCandidate pw) v) :=
  usesOnly_mono (loadConst_usesOnly _ _) (tight_cand pw)

/-- Tight support of one single-pass out-of-place controlled addition. -/
theorem fastOut_usesOnly_tight (control : Wire) (pointReg outReg : List Wire) (ws : Wire)
    (C : Point) :
    CircuitUsesOnly ([control] ++ pointReg ++ outReg ++ [ws] ++
        tightPW (controlledPointAddPointWorkStart ws))
      (fastOut control pointReg outReg ws C) := by
  let pw := controlledPointAddPointWorkStart ws
  let S := [control] ++ pointReg ++ outReg ++ [ws] ++ tightPW pw
  have hSc : control ∈ S := by simp [S]
  have hSa : ws ∈ S := by simp [S]
  have hSP : ∀ w ∈ pointReg, w ∈ S := fun w hw => by simp [S, hw]
  have hSO : ∀ w ∈ outReg, w ∈ S := fun w hw => by simp [S, hw]
  have hST : ∀ w ∈ tightPW pw, w ∈ S := fun w hw => by simp [S, hw]
  have hSPT : ∀ w ∈ pointReg ++ tightPW pw, w ∈ S := fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact hSP w h
    · exact hST w h
  have hflag (f : Wire) (hf : f ∈ pointAddFlagWork pw) : f ∈ S := hST f (tight_flagWork pw f hf)
  have hgen : pointAddGenericFlag pw ∈ S := hflag _ (by simp [pointAddFlagWork])
  have hdbl : pointAddDoubleFlag pw ∈ S := hflag _ (by simp [pointAddFlagWork])
  have hinf : pointAddInfinityFlag pw ∈ S := hflag _ (by simp [pointAddFlagWork])
  have hcS : ∀ w ∈ pointAddCandidate pw, w ∈ S := fun w hw => hST w (tight_cand pw w hw)
  have hsetupU := usesOnly_mono (setup_usesOnly_tight pointReg pw (pointCoordinates C).2.1
    (pointCoordinates C).2.2) hSPT
  have hpassU : CircuitUsesOnly S (fastPass control pointReg outReg) := by
    have hx : CircuitUsesOnly S ([Gate.X control] : Circuit) := by
      intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact hSc
    exact usesOnly_append (usesOnly_append hx (usesOnly_mono
      (controlledCopyReg_usesOnly control pointReg outReg) (by
        intro w hw
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hw
        rcases hw with rfl | hw | hw
        · exact hSc
        · exact hSP w hw
        · exact hSO w hw))) hx
  simp only [fastOut, fastBlocks]
  exact usesOnly_append (usesOnly_append (usesOnly_append hpassU hsetupU)
    (usesOnly_append (usesOnly_append
      (fastBlock_usesOnly _ _ _ _ _ _ S (usesOnly_mono (genericK_usesOnly_tight _ _ _) hST)
        hSc hgen hSa hcS hSO)
      (fastBlock_usesOnly _ _ _ _ _ _ S (usesOnly_mono (loadCand_usesOnly_tight _ _) hST)
        hSc hdbl hSa hcS hSO))
      (fastBlock_usesOnly _ _ _ _ _ _ S (usesOnly_mono (loadCand_usesOnly_tight _ _) hST)
        hSc hinf hSa hcS hSO))) (usesOnly_reverse hsetupU)

/-- Tight workspace of one in-place controlled addition placed at `workStart`. -/
def tightWork (workStart : Wire) : List Wire :=
  controlledPointAddTemp workStart ++ [controlledPointAddAuxStart workStart] ++
    tightPW (controlledPointAddPointWorkStart (controlledPointAddAuxStart workStart))

/-- Template-level tight support of the fast scalar multiplication. -/
theorem fastScalarGates_usesOnly_tight {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (pointReg : List Wire) (workStart : Wire) (cs : List Wire) (rs : List (Fin n × Fin n)) :
    CircuitUsesOnly (cs ++ (pointReg ++ tightWork workStart))
      ((fastScalarGates pointReg workStart cs rs).flatMap
        (TemplateGate.instantiate (readConstant coeffs Q))) := by
  induction cs generalizing rs with
  | nil => cases rs <;> exact fun g hg => by simp [fastScalarGates] at hg
  | cons c cs ih =>
    cases rs with
    | nil => exact fun g hg => by simp [fastScalarGates] at hg
    | cons r rs =>
      let temp := controlledPointAddTemp workStart
      let auxStart := controlledPointAddAuxStart workStart
      let T := [c] ++ pointReg ++ temp ++ [auxStart] ++
        tightPW (controlledPointAddPointWorkStart auxStart)
      have hf := fastOut_usesOnly_tight c pointReg temp auxStart (constantPoint Q (coeffs r.1))
      have hb := fastOut_usesOnly_tight c pointReg temp auxStart (constantPoint Q (coeffs r.2))
      have hswap : CircuitUsesOnly T (pointSwapReg pointReg temp) := by
        apply usesOnly_mono (pointSwapReg_usesOnly' pointReg temp)
        intro w hw
        simp only [T, List.mem_append] at hw ⊢
        tauto
      have hhead : CircuitUsesOnly T
          ((fastCPAGates r.1 r.2 c pointReg workStart).flatMap
            (TemplateGate.instantiate (readConstant coeffs Q))) := by
        rw [fastCPAGates_instantiate]
        exact usesOnly_append (usesOnly_append hf hswap) (usesOnly_reverse hb)
      have htail := ih rs
      simp only [fastScalarGates, List.flatMap_append]
      refine usesOnly_append (usesOnly_mono hhead ?_) (usesOnly_mono htail ?_)
      · intro w hw
        simp only [T, tightWork, temp, auxStart, List.mem_append, List.mem_cons] at hw ⊢
        tauto
      · intro w hw
        simp only [List.mem_append, List.mem_cons] at hw ⊢
        tauto

end V2
end Secp256k1
end ShorECDLP
