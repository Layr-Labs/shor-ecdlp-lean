import ShorECDLP.Submission.Entrant.V2.Controlled_PointAdd
import ShorECDLP.Challenge.Template
import Batteries.Tactic.OpenPrivate

/-! EDITABLE. Controlled point addition without nested uncomputation.

`fastOut` computes `out ^= encode (if control then R + C else R)` directly:

* the Naive setup stage computes the branch flags;
* a control-gated copy writes `R` when the control is off;
* the generic affine branch is computed once, XOR-copied into `out` under
  `control ∧ genericFlag`, and uncomputed;
* the doubling and infinity branches have classical results (`C + C` and `C`),
  so they are loaded as constants under `control ∧ flag`;
* the setup is uncomputed.

The V2 (Naive-derived) construction instead computes all branches into a private register,
copies that register out and runs the whole computation backwards; the doubling
branch is a quantum computation there.  -/

namespace ShorECDLP
namespace Secp256k1
namespace V2

open Classical
open Arithmetic
open scoped ArithmeticNotation
open Challenge (pointCoordinates)

variable [Fact (Nat.Prime p)]

open private pointAddBranchActiveSupport genericPointCompute_usesOnly
  packFinitePoint_usesOnly_pointAdd pointAddBranchActiveSupport_mem_work
  pointAddCandidate_mem_work genericPointCompute_HPFree packFinitePoint_HPFree
  genericPointCompute_wellFormed packFinitePoint_wellFormed controlledCopyReg_HPFree
  controlledCopyReg_wellFormed controlledCopyReg_usesOnly run_controlledCopyReg_true
  run_controlledCopyReg_false pointAddSetup_usesOnly pointAddCoordinateCopies_wellFormed
  pointAddFlags_wellFormed genericPointCompute_correct packFinitePoint_correct
  run_writeReg_commute writeReg_other controlledCopyReg_tCount packFinitePoint_tCount
  pointAddSetup_tCount genericPointCompute_tCount pointAddControl_mem_work
  from ShorECDLP.Submission.Entrant.V2.PointAdd
open private pointSwapReg_usesOnly pointSwapReg_tCount
  from ShorECDLP.Submission.Entrant.V2.Controlled_PointAdd

/-! ## Circuit -/

/-- `out ^= P` when `control = false`. -/
def fastPass (control : Wire) (pointReg outReg : List Wire) : Circuit :=
  [Gate.X control] ++ controlledCopyReg control pointReg outReg ++ [Gate.X control]

/-- `out ^= cand(K)` when `control ∧ flag`, with `anc` a clean ancilla. -/
def fastBlock (control flag anc : Wire) (K : Circuit) (cand outReg : List Wire) : Circuit :=
  [Gate.CCX control flag anc] ++ K ++ controlledCopyReg anc cand outReg ++ K.reverse ++
    [Gate.CCX control flag anc]

def fastGenericK (pw : Wire) (xC yC : Fp) : Circuit :=
  genericPointCompute pw xC yC ++
    packFinitePoint (pointAddT2 pw) (pointAddT4 pw) (pointAddCandidate pw)

def fastBlocks (control anc : Wire) (outReg : List Wire) (pw : Wire) (C : Point) :
    Circuit :=
  let xC := (pointCoordinates C).2.1
  let yC := (pointCoordinates C).2.2
  let cand := pointAddCandidate pw
  fastBlock control (pointAddGenericFlag pw) anc (fastGenericK pw xC yC) cand outReg ++
    fastBlock control (pointAddDoubleFlag pw) anc
      (loadConst cand (encode (C + C)).val) cand outReg ++
    fastBlock control (pointAddInfinityFlag pw) anc
      (loadConst cand (encode C).val) cand outReg

def fastOut (control : Wire) (pointReg outReg : List Wire) (workStart : Wire)
    (C : Point) : Circuit :=
  let pw := controlledPointAddPointWorkStart workStart
  let setup := pointAddSetup pointReg pw (pointCoordinates C).2.1 (pointCoordinates C).2.2
  fastPass control pointReg outReg ++ setup ++ fastBlocks control workStart outReg pw C ++
    setup.reverse

/-- In-place controlled addition of a classical point, same layout as the Naive one. -/
def fastCPA (control : Wire) (pointReg : List Wire) (workStart : Wire) (C : Point) :
    Circuit :=
  let temp := controlledPointAddTemp workStart
  let auxStart := controlledPointAddAuxStart workStart
  fastOut control pointReg temp auxStart C ++ pointSwapReg pointReg temp ++
    (fastOut control pointReg temp auxStart (-C)).reverse

/-! ## Generic block semantics -/

omit [Fact (Nat.Prime p)] in
theorem upd_self (s : BasisState) (w : Wire) : s[w ↦ s w] = s := by
  funext v
  by_cases h : v = w
  · subst h; simp [upd]
  · simp [upd, h]

omit [Fact (Nat.Prime p)] in
theorem ccx_false (a b t : Wire) (s : BasisState) (h : (s a && s b) = false) :
    Classical.applyGate (.CCX a b t) s = s := by
  simp only [Classical.applyGate, h, Bool.xor_false, upd_self]

omit [Fact (Nat.Prime p)] in
theorem writeReg_not_mem' (ws : List Wire) (n : Nat) (s : BasisState) (w : Wire)
    (hw : w ∉ ws) : writeReg ws n s w = s w := by
  induction ws generalizing n s with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.mem_cons, not_or] at hw
    simp only [writeReg]
    rw [ih _ _ hw.2, upd_other _ _ _ hw.1]

omit [Fact (Nat.Prime p)] in
theorem writeReg_upd_comm (ws : List Wire) (n : Nat) (s : BasisState) (w : Wire) (b : Bool)
    (hw : w ∉ ws) : writeReg ws n (s[w ↦ b]) = (writeReg ws n s)[w ↦ b] := by
  induction ws generalizing n s with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.mem_cons, not_or] at hw
    simp only [writeReg]
    rw [← ih _ _ hw.2]
    congr 1
    funext u
    by_cases hu : u = v
    · subst hu; simp [upd, Ne.symm hw.1]
    · by_cases hu' : u = w
      · subst hu'; simp [upd, hu]
      · simp [upd, hu, hu']

omit [Fact (Nat.Prime p)] in
/-- An inactive block is the identity. -/
theorem fastBlock_inactive (control flag anc : Wire) (K : Circuit) (cand outReg work : List Wire)
    (s : BasisState) (hfree : HPFree K) (hwf : CircuitWellFormed K)
    (huses : CircuitUsesOnly work K) (hanc : anc ∉ work)
    (hoff : (s control && s flag) = false) (hancClean : s anc = false) :
    Classical.run (fastBlock control flag anc K cand outReg) s = s := by
  have h1 : Classical.run [Gate.CCX control flag anc] s = s := by
    simp only [Classical.run_cons, Classical.run_nil, ccx_false _ _ _ _ hoff]
  have hK : Classical.run K s anc = false := by
    rw [huses.preservesOutside s anc hanc, hancClean]
  have h2 : Classical.run (controlledCopyReg anc cand outReg) (Classical.run K s) =
      Classical.run K s := run_controlledCopyReg_false anc cand outReg _ hK
  simp only [fastBlock, Classical.run_append, h1, h2, run_reverse_cancel K s hfree hwf]

omit [Fact (Nat.Prime p)] in
/-- An active block XORs the candidate produced by `K` into a clean output. -/
theorem fastBlock_active (control flag anc : Wire) (K : Circuit) (cand outReg work : List Wire)
    (s : BasisState) (hfree : HPFree K) (hwf : CircuitWellFormed K)
    (huses : CircuitUsesOnly work K) (hcand : ∀ w ∈ cand, w ∈ work)
    (hnodup : (outReg ++ work).Nodup) (hlen : outReg.length = cand.length)
    (hanc : anc ∉ work) (hancOut : anc ∉ outReg)
    (hcontrolOut : control ∉ outReg) (hflagOut : flag ∉ outReg)
    (hcontrolAnc : control ≠ anc) (hflagAnc : flag ≠ anc)
    (hcc : (anc :: cand ++ outReg).Nodup)
    (hc : s control = true) (hf : s flag = true) (hancClean : s anc = false)
    (hclean : Clean outReg s) :
    Classical.run (fastBlock control flag anc K cand outReg) s =
      writeReg outReg (regValue cand (Classical.run K s)) s := by
  let s1 := s[anc ↦ true]
  have h1 : Classical.run [Gate.CCX control flag anc] s = s1 := by
    simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate, hc, hf,
      hancClean, Bool.and_self, Bool.false_xor, s1]
  have hK1 : Classical.run K s1 anc = true := by
    rw [huses.preservesOutside s1 anc hanc]; simp [s1]
  have hcopy : Classical.run (controlledCopyReg anc cand outReg) (Classical.run K s1) =
      Classical.run (copyReg cand outReg) (Classical.run K s1) :=
    run_controlledCopyReg_true anc cand outReg _ hcc hK1
  have hagree : ∀ w ∈ work, s1 w = s w := by
    intro w hw
    have hne : w ≠ anc := fun e => hanc (e ▸ hw)
    simp [s1, upd, hne]
  have hval : regValue cand (Classical.run K s1) = regValue cand (Classical.run K s) := by
    apply regValue_congr
    intro w hw
    exact Arithmetic.CircuitUsesOnly.run_congr huses hagree w (hcand w hw)
  have hclean1 : Clean outReg s1 := by
    intro w hw
    have hne : w ≠ anc := fun e => hancOut (e ▸ hw)
    simp [s1, upd, hne, hclean w hw]
  have hbound : regValue cand (Classical.run K s1) < 2 ^ outReg.length := by
    rw [hlen]; exact regValue_lt_two_pow _ _
  have hben := bennett_copyReg_eq_writeReg K ([] : List Wire) cand outReg work s1 _ hfree hwf
    (by simpa using huses) hcand (by simpa using hnodup) hlen hclean1 rfl hbound
  have hmid : Classical.run (K ++ controlledCopyReg anc cand outReg ++ K.reverse) s1 =
      writeReg outReg (regValue cand (Classical.run K s)) s1 := by
    rw [Classical.run_append, Classical.run_append, hcopy, ← Classical.run_append,
      ← Classical.run_append, ← hval]
    simpa only [List.append_assoc] using hben
  have hfinal : Classical.run [Gate.CCX control flag anc]
      (writeReg outReg (regValue cand (Classical.run K s)) s1) =
      writeReg outReg (regValue cand (Classical.run K s)) s := by
    simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate,
      writeReg_not_mem' _ _ _ _ hcontrolOut, writeReg_not_mem' _ _ _ _ hflagOut,
      writeReg_not_mem' _ _ _ _ hancOut]
    simp only [s1, upd_other s anc true hcontrolAnc, upd_other s anc true hflagAnc, hc, hf,
      upd_same, Bool.and_self, Bool.true_xor, Bool.not_true]
    rw [← writeReg_upd_comm _ _ _ _ _ hancOut]
    congr 1
    funext v
    by_cases hv : v = anc
    · subst hv; simp [upd, hancClean]
    · simp [upd, hv]
  have hassoc : fastBlock control flag anc K cand outReg =
      [Gate.CCX control flag anc] ++ (K ++ controlledCopyReg anc cand outReg ++ K.reverse) ++
        [Gate.CCX control flag anc] := by
    simp [fastBlock, List.append_assoc]
  rw [hassoc, Classical.run_append, Classical.run_append, h1, hmid, hfinal]


/-! ## Pass block -/

omit [Fact (Nat.Prime p)] in
theorem fastPass_on (control : Wire) (pointReg outReg : List Wire) (s : BasisState)
    (hc : s control = true) :
    Classical.run (fastPass control pointReg outReg) s = s := by
  have h1 : Classical.run [Gate.X control] s = s[control ↦ false] := by
    simp [Classical.applyGate, hc]
  have h2 := run_controlledCopyReg_false control pointReg outReg (s[control ↦ false])
    (by simp)
  simp only [fastPass, Classical.run_append, h1, h2]
  simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate, upd_same,
    Bool.not_false]
  funext v
  by_cases hv : v = control
  · subst hv; simp [upd, hc]
  · simp [upd, hv]

omit [Fact (Nat.Prime p)] in
theorem fastPass_off (control : Wire) (pointReg outReg : List Wire) (s : BasisState)
    (hc : s control = false) (hlen : outReg.length = pointReg.length)
    (hnd : (control :: pointReg ++ outReg).Nodup) (hclean : Clean outReg s) :
    Classical.run (fastPass control pointReg outReg) s =
      writeReg outReg (regValue pointReg s) s := by
  have hcP : control ∉ pointReg := fun h => (List.nodup_cons.mp hnd).1 (List.mem_append_left _ h)
  have hcO : control ∉ outReg := fun h => (List.nodup_cons.mp hnd).1 (List.mem_append_right _ h)
  have h1 : Classical.run [Gate.X control] s = s[control ↦ true] := by
    simp [Classical.applyGate, hc]
  have h2 := run_controlledCopyReg_true control pointReg outReg (s[control ↦ true]) hnd
    (by simp)
  have hclean1 : Clean outReg (s[control ↦ true]) := by
    intro w hw
    have hne : w ≠ control := fun e => hcO (e ▸ hw)
    simp [upd, hne, hclean w hw]
  have hval : regValue pointReg (s[control ↦ true]) = regValue pointReg s :=
    regValue_upd_not_mem _ _ _ _ hcP
  have h3 := copyReg_eq_writeReg_of_value pointReg outReg ([] : List Wire) (s[control ↦ true])
    (regValue pointReg s) hlen (by simpa using (List.nodup_cons.mp hnd).2) hclean1 hval
    (by rw [hlen]; exact regValue_lt_two_pow _ _)
  simp only [fastPass, Classical.run_append, h1, h2, h3]
  simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate,
    writeReg_not_mem' _ _ _ _ hcO, upd_same, Bool.not_true]
  rw [← writeReg_upd_comm _ _ _ _ _ hcO]
  congr 1
  funext v
  by_cases hv : v = control
  · subst hv; simp [upd, hc]
  · simp [upd, hv]

/-! ## Structural facts -/

omit [Fact (Nat.Prime p)] in
theorem regValue_eq_zero_of_clean (ws : List Wire) (s : BasisState) (h : Clean ws s) :
    regValue ws s = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [regValue_cons, h w List.mem_cons_self, ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]
    simp

omit [Fact (Nat.Prime p)] in
theorem writeReg_zero_of_clean (ws : List Wire) (s : BasisState) (h : Clean ws s) :
    writeReg ws 0 s = s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [writeReg, Nat.zero_div, Nat.testBit_zero, Nat.zero_mod]
    have hs : s[w ↦ decide (0 = 1)] = s := by
      rw [show decide (0 = 1) = s w by rw [h w List.mem_cons_self]; rfl, upd_self]
    rw [hs, ih s (fun v hv => h v (List.mem_cons_of_mem _ hv))]

omit [Fact (Nat.Prime p)] in
theorem fastGenericK_HPFree (pw : Wire) (xC yC : Fp) : HPFree (fastGenericK pw xC yC) := by
  simp only [fastGenericK, hpFree_append]
  exact ⟨genericPointCompute_HPFree pw xC yC, packFinitePoint_HPFree _ _ _⟩

omit [Fact (Nat.Prime p)] in
theorem fastGenericK_wellFormed (pw : Wire) (xC yC : Fp) :
    CircuitWellFormed (fastGenericK pw xC yC) := by
  rw [fastGenericK, circuitWellFormed_append]
  exact ⟨genericPointCompute_wellFormed pw xC yC, packFinitePoint_wellFormed pw⟩

omit [Fact (Nat.Prime p)] in
theorem fastGenericK_usesOnly (pw : Wire) (xC yC : Fp) :
    CircuitUsesOnly (pointAddWork pw) (fastGenericK pw xC yC) :=
  usesOnly_mono (usesOnly_append (genericPointCompute_usesOnly pw xC yC)
    (packFinitePoint_usesOnly_pointAdd pw)) (pointAddBranchActiveSupport_mem_work pw)

omit [Fact (Nat.Prime p)] in
theorem loadCand_usesOnly (pw : Wire) (v : Nat) :
    CircuitUsesOnly (pointAddWork pw) (loadConst (pointAddCandidate pw) v) :=
  usesOnly_mono (loadConst_usesOnly _ _) (pointAddCandidate_mem_work pw)

omit [Fact (Nat.Prime p)] in
theorem fastSetup_wellFormed (pointReg outReg : List Wire) (pw : Wire) (xC yC : Fp)
    (hnodup : (pointReg ++ outReg ++ pointAddWork pw).Nodup) :
    CircuitWellFormed (pointAddSetup pointReg pw xC yC) := by
  rw [pointAddSetup, circuitWellFormed_append]
  exact ⟨pointAddCoordinateCopies_wellFormed pointReg outReg pw hnodup,
    pointAddFlags_wellFormed pointReg outReg pw xC yC hnodup⟩

/-! ## Forward correctness -/

theorem fastOut_correct (control : Wire) (pointReg outReg : List Wire) (workStart : Wire)
    (C R : Point) (hC0 : C ≠ 0) (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (houtLength : outReg.length = pointWidth)
    (hnodup : ([control] ++ pointReg ++ outReg ++ controlledPointAddOutWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean : Clean (outReg ++ controlledPointAddOutWork workStart) st) :
    Classical.run (fastOut control pointReg outReg workStart C) st =
      writeReg outReg (encode (controlledPointResult (st control) R C)).val st := by
  cases C with
  | zero => exact (hC0 rfl).elim
  | @some xC yC hC =>
  let pw := controlledPointAddPointWorkStart workStart
  let work := pointAddWork pw
  let choice := controlledPointAddChoice workStart
  let cand := pointAddCandidate pw
  let anc := workStart
  let setup := pointAddSetup pointReg pw xC yC
  have hwork : controlledPointAddOutWork workStart = choice ++ work := rfl
  -- disjointness bookkeeping
  have hN : (control :: (pointReg ++ (outReg ++ (choice ++ work)))).Nodup := by
    simpa [hwork, List.append_assoc] using hnodup
  obtain ⟨hcNot, hN1⟩ := List.nodup_cons.mp hN
  obtain ⟨hPnd, hN2, hPx⟩ := List.nodup_append.mp hN1
  obtain ⟨hOnd, hN3, hOx⟩ := List.nodup_append.mp hN2
  obtain ⟨hChnd, hWnd, hChx⟩ := List.nodup_append.mp hN3
  have hancChoice : anc ∈ choice := by
    simp [choice, anc, controlledPointAddChoice, pointWidth]
  have hancWork : anc ∉ work := fun h => hChx anc hancChoice anc h rfl
  have hancOut : anc ∉ outReg := fun h => hOx anc h anc (List.mem_append_left _ hancChoice) rfl
  have hancP : anc ∉ pointReg := fun h =>
    hPx anc h anc (List.mem_append_right _ (List.mem_append_left _ hancChoice)) rfl
  have hcontrolAnc : control ≠ anc := fun h => hcNot (by
    rw [h]; exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ hancChoice)))
  have hcontrolOut : control ∉ outReg := fun h =>
    hcNot (List.mem_append_right _ (List.mem_append_left _ h))
  have hcontrolWork : control ∉ work := fun h =>
    hcNot (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h)))
  have hcontrolP : control ∉ pointReg := fun h => hcNot (List.mem_append_left _ h)
  have hOW : ∀ w ∈ outReg, w ∉ work := fun w hw hw' =>
    hOx w hw w (List.mem_append_right _ hw') rfl
  have hPW : ∀ w ∈ pointReg, w ∉ work := fun w hw hw' =>
    hPx w hw w (List.mem_append_right _ (List.mem_append_right _ hw')) rfl
  have hPO : ∀ w ∈ pointReg, w ∉ outReg := fun w hw hw' =>
    hPx w hw w (List.mem_append_left _ hw') rfl
  have hOWnd : (outReg ++ work).Nodup :=
    List.nodup_append.mpr ⟨hOnd, hWnd, fun a ha b hb => hOx a ha b (List.mem_append_right _ hb)⟩
  have hPOWnd : (pointReg ++ outReg ++ work).Nodup := by
    rw [List.append_assoc]
    exact List.nodup_append.mpr ⟨hPnd, hOWnd, fun a ha b hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact hPx a ha b (List.mem_append_left _ hb)
      · exact hPx a ha b (List.mem_append_right _ (List.mem_append_right _ hb))⟩
  have hcandWork : ∀ w ∈ cand, w ∈ work := pointAddCandidate_mem_work pw
  have hcandLen : cand.length = pointWidth := by simp [cand, pointAddCandidate]
  have hcc : (anc :: cand ++ outReg).Nodup := by
    rw [List.cons_append]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact hancWork (hcandWork _ h)
      · exact hancOut h
    · refine List.nodup_append.mpr ⟨?_, hOnd, fun a ha b hb => ?_⟩
      · simp [cand, pointAddCandidate, List.nodup_range']
      · intro e; subst e; exact hOW a hb (hcandWork a ha)
  have hgenW : pointAddGenericFlag pw ∈ work := pointAddControl_mem_work pw 3 (by norm_num)
  have hdblW : pointAddDoubleFlag pw ∈ work := pointAddControl_mem_work pw 5 (by norm_num)
  have hinfW : pointAddInfinityFlag pw ∈ work := by
    simpa using pointAddControl_mem_work pw 0 (by norm_num)
  have hcleanOut : Clean outReg st := fun w hw => hclean w (List.mem_append_left _ hw)
  have hcleanWork : Clean work st := fun w hw =>
    hclean w (List.mem_append_right _ (by rw [hwork]; exact List.mem_append_right _ hw))
  have hancClean : st anc = false := hclean anc (List.mem_append_right _
    (by rw [hwork]; exact List.mem_append_left _ hancChoice))
  have hsetupHP : HPFree setup := pointAddSetup_HPFree pointReg pw xC yC
  have hsetupWF : CircuitWellFormed setup := fastSetup_wellFormed pointReg outReg pw xC yC hPOWnd
  have hsetupUses : CircuitUsesOnly (pointReg ++ work) setup := pointAddSetup_usesOnly pointReg pw xC yC
  have hsetupDisj : ModExp.Schedule.WireDisjoint (pointReg ++ work) outReg := by
    intro a ha b hb e
    subst e
    rcases List.mem_append.mp ha with ha | ha
    · exact hPO a ha hb
    · exact hOW a hb ha
  -- generic block facts
  have inactive : ∀ (flag : Wire) (K : Circuit) (s : BasisState), HPFree K →
      CircuitWellFormed K → CircuitUsesOnly work K → (s control && s flag) = false →
      s anc = false → Classical.run (fastBlock control flag anc K cand outReg) s = s :=
    fun flag K s hK hW hU hoff ha =>
      fastBlock_inactive control flag anc K cand outReg work s hK hW hU hancWork hoff ha
  have active : ∀ (flag : Wire) (K : Circuit) (s : BasisState), flag ∈ work → HPFree K →
      CircuitWellFormed K → CircuitUsesOnly work K → s control = true → s flag = true →
      s anc = false → Clean outReg s →
      Classical.run (fastBlock control flag anc K cand outReg) s =
        writeReg outReg (regValue cand (Classical.run K s)) s :=
    fun flag K s hfl hK hW hU hc hf ha hcl =>
      fastBlock_active control flag anc K cand outReg work s hK hW hU hcandWork hOWnd
        (by rw [houtLength, hcandLen]) hancWork hancOut hcontrolOut
        (fun h => hOW flag h hfl) hcontrolAnc (fun e => hancWork (e ▸ hfl)) hcc hc hf ha hcl
  have hGK := fastGenericK_HPFree pw xC yC
  have hGW := fastGenericK_wellFormed pw xC yC
  have hGU : CircuitUsesOnly work (fastGenericK pw xC yC) := fastGenericK_usesOnly pw xC yC
  have hLK (v : Nat) : HPFree (loadConst cand v) := loadConst_HPFree _ _
  have hLW (v : Nat) : CircuitWellFormed (loadConst cand v) := loadConst_wellFormed _ _
  have hLU (v : Nat) : CircuitUsesOnly work (loadConst cand v) := loadCand_usesOnly pw v
  let blocks := fastBlocks control anc outReg pw (.some hC)
  have hfast : fastOut control pointReg outReg workStart (.some hC) =
      fastPass control pointReg outReg ++ setup ++ blocks ++ setup.reverse := rfl
  have hblocksEq : blocks =
      fastBlock control (pointAddGenericFlag pw) anc (fastGenericK pw xC yC) cand outReg ++
      fastBlock control (pointAddDoubleFlag pw) anc
        (loadConst cand (encode ((.some hC : Point) + .some hC)).val) cand outReg ++
      fastBlock control (pointAddInfinityFlag pw) anc
        (loadConst cand (encode (.some hC : Point)).val) cand outReg := rfl
  -- after the setup, writes to `outReg` commute with its reverse
  have hfinish : ∀ (v : Nat) (s : BasisState),
      Classical.run setup.reverse (writeReg outReg v (Classical.run setup s)) =
        writeReg outReg v s := by
    intro v s
    rw [run_writeReg_commute setup.reverse (pointReg ++ work) outReg v _
      (usesOnly_reverse hsetupUses) hsetupDisj hOnd, run_reverse_cancel setup s hsetupHP hsetupWF]
  have hkeep : ∀ (s : BasisState) (w : Wire), w ∉ pointReg ++ work →
      Classical.run setup s w = s w := fun s w hw => hsetupUses.preservesOutside s w hw
  have hcNotPW : control ∉ pointReg ++ work := by
    intro h; rcases List.mem_append.mp h with h | h
    · exact hcontrolP h
    · exact hcontrolWork h
  have haNotPW : anc ∉ pointReg ++ work := by
    intro h; rcases List.mem_append.mp h with h | h
    · exact hancP h
    · exact hancWork h
  cases hctl : st control with
  | false =>
    let s1 := writeReg outReg (encodeNat R) st
    have h1 : Classical.run (fastPass control pointReg outReg) st = s1 := by
      rw [fastPass_off control pointReg outReg st hctl (by rw [houtLength, hpointLength])
        (by simpa [List.append_assoc] using
          (List.nodup_cons.mpr ⟨fun h => hcNot (by
            rcases List.mem_append.mp h with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_append_left _ h)), List.nodup_append.mpr
            ⟨hPnd, hOnd, fun a ha b hb => hPx a ha b (List.mem_append_left _ hb)⟩⟩ :
            (control :: (pointReg ++ outReg)).Nodup)) hcleanOut, hpoint]
    have hs1c : s1 control = false := by
      show writeReg outReg (encodeNat R) st control = false
      rw [writeReg_not_mem' _ _ _ _ hcontrolOut, hctl]
    have hs1a : s1 anc = false := by
      show writeReg outReg (encodeNat R) st anc = false
      rw [writeReg_not_mem' _ _ _ _ hancOut, hancClean]
    let s2 := Classical.run setup s1
    have hs2c : s2 control = false := by
      show Classical.run setup s1 control = false
      rw [hkeep _ _ hcNotPW, hs1c]
    have hs2a : s2 anc = false := by
      show Classical.run setup s1 anc = false
      rw [hkeep _ _ haNotPW, hs1a]
    have hblocks : Classical.run blocks s2 = s2 := by
      rw [hblocksEq, Classical.run_append, Classical.run_append]
      rw [inactive _ _ _ hGK hGW hGU (by simp [hs2c]) hs2a,
        inactive _ _ _ (hLK _) (hLW _) (hLU _) (by simp [hs2c]) hs2a,
        inactive _ _ _ (hLK _) (hLW _) (hLU _) (by simp [hs2c]) hs2a]
    rw [hfast, Classical.run_append, Classical.run_append, Classical.run_append, h1, hblocks,
      run_reverse_cancel setup s1 hsetupHP hsetupWF]
    simp only [controlledPointResult, Bool.false_eq_true, if_false, encode_val, s1]
  | true =>
    have h1 : Classical.run (fastPass control pointReg outReg) st = st :=
      fastPass_on control pointReg outReg st hctl
    let s2 := Classical.run setup st
    have hs2c : s2 control = true := by
      show Classical.run setup st control = true
      rw [hkeep _ _ hcNotPW, hctl]
    have hs2a : s2 anc = false := by
      show Classical.run setup st anc = false
      rw [hkeep _ _ haNotPW, hancClean]
    have hs2o : Clean outReg s2 := by
      intro w hw
      show Classical.run setup st w = false
      rw [hkeep _ _ (fun h => by
        rcases List.mem_append.mp h with h | h
        · exact hPO w h hw
        · exact hOW w hw h), hcleanOut w hw]
    have hblocks : Classical.run blocks s2 =
        writeReg outReg (encode (R + (.some hC : Point))).val s2 := by
      rw [hblocksEq, Classical.run_append, Classical.run_append]
      have hcandNd : cand.Nodup := by simp [cand, pointAddCandidate, List.nodup_range']
      have hcandClean (hbw : Clean (pointAddBranchWork pw) s2) : Clean cand s2 :=
        fun w hw => hbw w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))
      have hload (v : Nat) (hv : v < 2 ^ pointWidth) (hbw : Clean (pointAddBranchWork pw) s2) :
          regValue cand (Classical.run (loadConst cand v) s2) = v :=
        loadConst_correct cand v s2 hcandNd (hcandClean hbw) (by rw [hcandLen]; exact hv)
      cases R with
      | zero =>
        obtain ⟨hinf, hgen, hdbl, hbw⟩ := pointAddSetup_zero_correct pointReg outReg pw
          (xC := xC) (yC := yC) st hpointLength hPOWnd hpoint hcleanWork
        have hinf' : s2 (pointAddInfinityFlag pw) = true := hinf
        have hgen' : s2 (pointAddGenericFlag pw) = false := hgen
        have hdbl' : s2 (pointAddDoubleFlag pw) = false := hdbl
        rw [inactive _ _ _ hGK hGW hGU (by rw [hs2c, hgen']; rfl) hs2a,
          inactive _ _ _ (hLK _) (hLW _) (hLU _) (by rw [hs2c, hdbl']; rfl) hs2a,
          active _ _ _ hinfW (hLK _) (hLW _) (hLU _) hs2c hinf' hs2a hs2o,
          hload _ (encode _).isLt hbw]
        rfl
      | @some xR yR hR =>
        obtain ⟨hxReg, hyReg, hinf, hgen, hdbl, hbw⟩ := pointAddSetup_some_correct pointReg outReg
          pw (xC := xC) (yC := yC) hR st hpointLength hPOWnd hpoint hcleanWork
        have hinf' : s2 (pointAddInfinityFlag pw) = false := hinf
        by_cases hx : xR = xC
        · have hgen' : s2 (pointAddGenericFlag pw) = false := by
            change Classical.run setup st (pointAddGenericFlag pw) = false
            rw [hgen]; simp [hx]
          by_cases hinv : yR = -yC
          · have hdbl' : s2 (pointAddDoubleFlag pw) = false := by
              change Classical.run setup st (pointAddDoubleFlag pw) = false
              rw [hdbl]; simp [hinv]
            rw [inactive _ _ _ hGK hGW hGU (by rw [hs2c, hgen']; rfl) hs2a,
              inactive _ _ _ (hLK _) (hLW _) (hLU _) (by rw [hs2c, hdbl']; rfl) hs2a,
              inactive _ _ _ (hLK _) (hLW _) (hLU _) (by rw [hs2c, hinf']; rfl) hs2a,
              inverseAdd_correct hR hC hx hinv, encode_val, encodeNat_zero]
            exact (writeReg_zero_of_clean outReg s2 hs2o).symm
          · have hdbl' : s2 (pointAddDoubleFlag pw) = true := by
              change Classical.run setup st (pointAddDoubleFlag pw) = true
              rw [hdbl]; simp [hx, hinv]
            have hy := y_eq_of_x_eq_of_not_inverse hR hC hx hinv
            subst hx hy
            rw [inactive _ _ _ hGK hGW hGU (by rw [hs2c, hgen']; rfl) hs2a,
              active _ _ _ hdblW (hLK _) (hLW _) (hLU _) hs2c hdbl' hs2a hs2o,
              hload _ (encode _).isLt hbw]
            have hs3c : (writeReg outReg (encode ((.some hR : Point) + .some hR)).val s2)
                control = true := by rw [writeReg_not_mem' _ _ _ _ hcontrolOut, hs2c]
            have hs3a : (writeReg outReg (encode ((.some hR : Point) + .some hR)).val s2)
                anc = false := by rw [writeReg_not_mem' _ _ _ _ hancOut, hs2a]
            have hs3i : (writeReg outReg (encode ((.some hR : Point) + .some hR)).val s2)
                (pointAddInfinityFlag pw) = false := by
              rw [writeReg_not_mem' _ _ _ _ (fun h => hOW _ h hinfW), hinf']
            rw [inactive _ _ _ (hLK _) (hLW _) (hLU _) (by rw [hs3c, hs3i]; rfl) hs3a]
        · have hgen' : s2 (pointAddGenericFlag pw) = true := by
            change Classical.run setup st (pointAddGenericFlag pw) = true
            rw [hgen]; simp [hx]
          have hdbl' : s2 (pointAddDoubleFlag pw) = false := by
            change Classical.run setup st (pointAddDoubleFlag pw) = false
            rw [hdbl]; simp [hx]
          obtain ⟨ht2, ht4, hcc2⟩ := genericPointCompute_correct pw xR yR xC yC hx s2
            hxReg hyReg hbw
          have hpack := packFinitePoint_correct pw (generic_nonsingular hR hC hx)
            (Classical.run (genericPointCompute pw xC yC) s2) ht2 ht4 hcc2
          have hgv : regValue cand (Classical.run (fastGenericK pw xC yC) s2) =
              (encode ((.some hR : Point) + .some hC)).val := by
            rw [fastGenericK, Classical.run_append, hpack, encode_val, ← genericAdd_correct hR hC hx]
            rfl
          rw [active _ _ _ hgenW hGK hGW hGU hs2c hgen' hs2a hs2o, hgv]
          have hs3c : (writeReg outReg (encode ((.some hR : Point) + .some hC)).val s2)
              control = true := by rw [writeReg_not_mem' _ _ _ _ hcontrolOut, hs2c]
          have hs3a : (writeReg outReg (encode ((.some hR : Point) + .some hC)).val s2)
              anc = false := by rw [writeReg_not_mem' _ _ _ _ hancOut, hs2a]
          have hs3d : (writeReg outReg (encode ((.some hR : Point) + .some hC)).val s2)
              (pointAddDoubleFlag pw) = false := by
            rw [writeReg_not_mem' _ _ _ _ (fun h => hOW _ h hdblW), hdbl']
          have hs3i : (writeReg outReg (encode ((.some hR : Point) + .some hC)).val s2)
              (pointAddInfinityFlag pw) = false := by
            rw [writeReg_not_mem' _ _ _ _ (fun h => hOW _ h hinfW), hinf']
          rw [inactive _ _ _ (hLK _) (hLW _) (hLU _) (by rw [hs3c, hs3d]; rfl) hs3a,
            inactive _ _ _ (hLK _) (hLW _) (hLU _) (by rw [hs3c, hs3i]; rfl) hs3a]
    rw [hfast, Classical.run_append, Classical.run_append, Classical.run_append, h1, hblocks,
      hfinish]
    simp only [controlledPointResult, if_true]

/-! ## Structural facts for the forward circuit -/

omit [Fact (Nat.Prime p)] in
theorem fastBlock_HPFree (control flag anc : Wire) (K : Circuit) (cand outReg : List Wire)
    (hK : HPFree K) : HPFree (fastBlock control flag anc K cand outReg) := by
  simp only [fastBlock, hpFree_append]
  exact ⟨⟨⟨⟨by simp, hK⟩, controlledCopyReg_HPFree _ _ _⟩, Arithmetic.hpFree_reverse hK⟩, by simp⟩

omit [Fact (Nat.Prime p)] in
theorem fastOut_HPFree (control : Wire) (pointReg outReg : List Wire) (workStart : Wire)
    (C : Point) : HPFree (fastOut control pointReg outReg workStart C) := by
  simp only [fastOut, fastBlocks, fastPass, hpFree_append]
  refine ⟨⟨⟨⟨⟨by simp, controlledCopyReg_HPFree _ _ _⟩, by simp⟩, pointAddSetup_HPFree _ _ _ _⟩,
    ⟨⟨fastBlock_HPFree _ _ _ _ _ _ (fastGenericK_HPFree _ _ _),
      fastBlock_HPFree _ _ _ _ _ _ (loadConst_HPFree _ _)⟩,
      fastBlock_HPFree _ _ _ _ _ _ (loadConst_HPFree _ _)⟩⟩,
    Arithmetic.hpFree_reverse (pointAddSetup_HPFree _ _ _ _)⟩

omit [Fact (Nat.Prime p)] in
theorem fastBlock_wellFormed (control flag anc : Wire) (K : Circuit) (cand outReg : List Wire)
    (hK : CircuitWellFormed K) (h1 : control ≠ flag) (h2 : control ≠ anc) (h3 : flag ≠ anc)
    (hcc : (anc :: cand ++ outReg).Nodup) :
    CircuitWellFormed (fastBlock control flag anc K cand outReg) := by
  simp only [fastBlock, circuitWellFormed_append]
  have hg : CircuitWellFormed [Gate.CCX control flag anc] := by
    simp [CircuitWellFormed, Gate.WellFormed, h1, h2, h3]
  exact ⟨⟨⟨⟨hg, hK⟩, controlledCopyReg_wellFormed _ _ _ hcc⟩, Arithmetic.wellFormed_reverse hK⟩, hg⟩

omit [Fact (Nat.Prime p)] in
theorem fastBlock_usesOnly (control flag anc : Wire) (K : Circuit) (cand outReg ws : List Wire)
    (hK : CircuitUsesOnly ws K) (hc : control ∈ ws) (hf : flag ∈ ws) (ha : anc ∈ ws)
    (hcand : ∀ w ∈ cand, w ∈ ws) (hout : ∀ w ∈ outReg, w ∈ ws) :
    CircuitUsesOnly ws (fastBlock control flag anc K cand outReg) := by
  have hg : CircuitUsesOnly ws ([Gate.CCX control flag anc] : Circuit) := by
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact ⟨hc, hf, ha⟩
  have hcc : CircuitUsesOnly ws (controlledCopyReg anc cand outReg) :=
    usesOnly_mono (controlledCopyReg_usesOnly anc cand outReg) (by
      intro w hw
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hw | hw
      · exact ha
      · exact hcand w hw
      · exact hout w hw)
  simp only [fastBlock]
  exact usesOnly_append (usesOnly_append (usesOnly_append (usesOnly_append hg hK) hcc)
    (usesOnly_reverse hK)) hg

omit [Fact (Nat.Prime p)] in
theorem fastOut_structural (control : Wire) (pointReg outReg : List Wire) (workStart : Wire)
    (C : Point)
    (hnodup : ([control] ++ pointReg ++ outReg ++ controlledPointAddOutWork workStart).Nodup) :
    CircuitWellFormed (fastOut control pointReg outReg workStart C) ∧
      CircuitUsesOnly ([control] ++ pointReg ++ outReg ++ controlledPointAddOutWork workStart)
        (fastOut control pointReg outReg workStart C) := by
  let pw := controlledPointAddPointWorkStart workStart
  let work := pointAddWork pw
  let choice := controlledPointAddChoice workStart
  let cand := pointAddCandidate pw
  let anc := workStart
  have hwork : controlledPointAddOutWork workStart = choice ++ work := rfl
  have hN : (control :: (pointReg ++ (outReg ++ (choice ++ work)))).Nodup := by
    simpa [hwork, List.append_assoc] using hnodup
  obtain ⟨hcNot, hN1⟩ := List.nodup_cons.mp hN
  obtain ⟨hPnd, hN2, hPx⟩ := List.nodup_append.mp hN1
  obtain ⟨hOnd, hN3, hOx⟩ := List.nodup_append.mp hN2
  obtain ⟨hChnd, hWnd, hChx⟩ := List.nodup_append.mp hN3
  have hancChoice : anc ∈ choice := by
    simp [choice, anc, controlledPointAddChoice, pointWidth]
  have hancWork : anc ∉ work := fun h => hChx anc hancChoice anc h rfl
  have hancOut : anc ∉ outReg := fun h => hOx anc h anc (List.mem_append_left _ hancChoice) rfl
  have hcontrolAnc : control ≠ anc := fun h => hcNot (by
    rw [h]; exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ hancChoice)))
  have hcontrolWork : control ∉ work := fun h =>
    hcNot (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h)))
  have hOW : ∀ w ∈ outReg, w ∉ work := fun w hw hw' =>
    hOx w hw w (List.mem_append_right _ hw') rfl
  have hOWnd : (outReg ++ work).Nodup :=
    List.nodup_append.mpr ⟨hOnd, hWnd, fun a ha b hb => hOx a ha b (List.mem_append_right _ hb)⟩
  have hPOWnd : (pointReg ++ outReg ++ work).Nodup := by
    rw [List.append_assoc]
    exact List.nodup_append.mpr ⟨hPnd, hOWnd, fun a ha b hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact hPx a ha b (List.mem_append_left _ hb)
      · exact hPx a ha b (List.mem_append_right _ (List.mem_append_right _ hb))⟩
  have hcandWork : ∀ w ∈ cand, w ∈ work := pointAddCandidate_mem_work pw
  have hcc : (anc :: cand ++ outReg).Nodup := by
    rw [List.cons_append]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact hancWork (hcandWork _ h)
      · exact hancOut h
    · refine List.nodup_append.mpr ⟨?_, hOnd, fun a ha b hb => ?_⟩
      · simp [cand, pointAddCandidate, List.nodup_range']
      · intro e; subst e; exact hOW a hb (hcandWork a ha)
  have hpass : (control :: pointReg ++ outReg).Nodup := by
    rw [List.cons_append]
    exact List.nodup_cons.mpr ⟨fun h => hcNot (by
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)), List.nodup_append.mpr
      ⟨hPnd, hOnd, fun a ha b hb => hPx a ha b (List.mem_append_left _ hb)⟩⟩
  have hgenW : pointAddGenericFlag pw ∈ work := pointAddControl_mem_work pw 3 (by norm_num)
  have hdblW : pointAddDoubleFlag pw ∈ work := pointAddControl_mem_work pw 5 (by norm_num)
  have hinfW : pointAddInfinityFlag pw ∈ work := by
    simpa using pointAddControl_mem_work pw 0 (by norm_num)
  have hne (f : Wire) (hf : f ∈ work) : control ≠ f ∧ f ≠ anc :=
    ⟨fun e => hcontrolWork (e ▸ hf), fun e => hancWork (e ▸ hf)⟩
  constructor
  · simp only [fastOut, fastBlocks, fastPass, circuitWellFormed_append]
    have hsetup := fastSetup_wellFormed pointReg outReg pw (pointCoordinates C).2.1
      (pointCoordinates C).2.2 hPOWnd
    refine ⟨⟨⟨⟨⟨by simp [CircuitWellFormed, Gate.WellFormed],
      controlledCopyReg_wellFormed _ _ _ hpass⟩, by simp [CircuitWellFormed, Gate.WellFormed]⟩,
      hsetup⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩, Arithmetic.wellFormed_reverse hsetup⟩
    · exact fastBlock_wellFormed _ _ _ _ _ _ (fastGenericK_wellFormed _ _ _)
        (hne _ hgenW).1 hcontrolAnc (hne _ hgenW).2 hcc
    · exact fastBlock_wellFormed _ _ _ _ _ _ (loadConst_wellFormed _ _)
        (hne _ hdblW).1 hcontrolAnc (hne _ hdblW).2 hcc
    · exact fastBlock_wellFormed _ _ _ _ _ _ (loadConst_wellFormed _ _)
        (hne _ hinfW).1 hcontrolAnc (hne _ hinfW).2 hcc
  · let S := [control] ++ pointReg ++ outReg ++ controlledPointAddOutWork workStart
    have hSc : control ∈ S := List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_singleton_self _)))
    have hSP : ∀ w ∈ pointReg, w ∈ S := fun w hw =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))
    have hSO : ∀ w ∈ outReg, w ∈ S := fun w hw =>
      List.mem_append_left _ (List.mem_append_right _ hw)
    have hSW : ∀ w ∈ work, w ∈ S := fun w hw =>
      List.mem_append_right _ (by rw [hwork]; exact List.mem_append_right _ hw)
    have hSa : anc ∈ S :=
      List.mem_append_right _ (by rw [hwork]; exact List.mem_append_left _ hancChoice)
    have hSPW : ∀ w ∈ pointReg ++ work, w ∈ S := fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hSP w hw
      · exact hSW w hw
    have hsetupU := usesOnly_mono (pointAddSetup_usesOnly pointReg pw (pointCoordinates C).2.1
      (pointCoordinates C).2.2) hSPW
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
    have hcS : ∀ w ∈ cand, w ∈ S := fun w hw => hSW w (hcandWork w hw)
    simp only [fastOut, fastBlocks]
    exact usesOnly_append (usesOnly_append (usesOnly_append hpassU hsetupU)
      (usesOnly_append (usesOnly_append
        (fastBlock_usesOnly _ _ _ _ _ _ S (usesOnly_mono (fastGenericK_usesOnly _ _ _) hSW)
          hSc (hSW _ hgenW) hSa hcS hSO)
        (fastBlock_usesOnly _ _ _ _ _ _ S (usesOnly_mono (loadCand_usesOnly _ _) hSW)
          hSc (hSW _ hdblW) hSa hcS hSO))
        (fastBlock_usesOnly _ _ _ _ _ _ S (usesOnly_mono (loadCand_usesOnly _ _) hSW)
          hSc (hSW _ hinfW) hSa hcS hSO))) (usesOnly_reverse hsetupU)

/-! ## In-place controlled addition -/

theorem fastCPA_correct (control : Wire) (pointReg : List Wire) (workStart : Wire)
    (C R : Point) (hC0 : C ≠ 0) (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup : ([control] ++ pointReg ++ controlledPointAddWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean : Clean (controlledPointAddWork workStart) st) :
    Classical.run (fastCPA control pointReg workStart C) st =
      writeReg pointReg (encode (controlledPointResult (st control) R C)).val st := by
  let temp := controlledPointAddTemp workStart
  let auxStart := controlledPointAddAuxStart workStart
  let work := controlledPointAddOutWork auxStart
  let result := controlledPointResult (st control) R C
  have htempLength : temp.length = pointWidth := by
    simp [temp, controlledPointAddTemp]
  have houtNodup : ([control] ++ pointReg ++ temp ++ work).Nodup := by
    simpa [temp, auxStart, work, controlledPointAddWork, controlledPointAddTemp,
      controlledPointAddAuxStart, List.append_assoc] using hnodup
  have hcleanOut : Clean (temp ++ work) st := by
    simpa [temp, auxStart, work, controlledPointAddWork, controlledPointAddTemp,
      controlledPointAddAuxStart] using hclean
  have h0 : (control :: (pointReg ++ temp ++ work)).Nodup := by
    simpa [List.append_assoc] using houtNodup
  have hswapNodup : (pointReg ++ temp ++ work).Nodup := (List.nodup_cons.mp h0).2
  have hcP : control ∉ pointReg := fun h =>
    (List.nodup_cons.mp h0).1 (List.mem_append_left _ (List.mem_append_left _ h))
  have hPnd : pointReg.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp hswapNodup).1).1
  have hPx : ∀ a ∈ pointReg, ∀ b ∈ temp ++ work, a ≠ b := by
    have h := List.nodup_append.mp (by simpa [List.append_assoc] using hswapNodup :
      (pointReg ++ (temp ++ work)).Nodup)
    exact h.2.2
  have hforward : Classical.run (fastOut control pointReg temp auxStart C) st =
      writeReg temp (encode result).val st :=
    fastOut_correct control pointReg temp auxStart C R hC0 st hpointLength htempLength
      houtNodup hpoint hcleanOut
  have hswap : Classical.run (pointSwapReg pointReg temp) (writeReg temp (encode result).val st) =
      writeReg temp (encodeNat R) (writeReg pointReg (encode result).val st) := by
    have h := pointSwapReg_correct pointReg temp work st (encode result).val
      (by rw [hpointLength, htempLength]) hswapNodup
    rw [hpoint] at h
    exact h
  let s1 := writeReg pointReg (encode result).val st
  have hs1point : regValue pointReg s1 = encodeNat result :=
    PointRegister.regValue_write_encode pointReg result st hpointLength hPnd
  have hs1clean : Clean (temp ++ work) s1 := by
    intro w hw
    show writeReg pointReg (encode result).val st w = false
    rw [writeReg_not_mem' _ _ _ _ (fun h => hPx w h w hw rfl), hcleanOut w hw]
  have hs1c : s1 control = st control := writeReg_not_mem' _ _ _ _ hcP
  have hback := fastOut_correct control pointReg temp auxStart (-C) result (neg_ne_zero.mpr hC0)
    s1 hpointLength htempLength houtNodup hs1point hs1clean
  have hres : controlledPointResult (s1 control) result (-C) = R := by
    rw [hs1c]
    simp only [result, controlledPointResult]
    cases st control <;> simp
  rw [hres, encode_val] at hback
  have hrev := run_reverse_cancel (fastOut control pointReg temp auxStart (-C)) s1
    (fastOut_HPFree _ _ _ _ _)
    (fastOut_structural control pointReg temp auxStart (-C) houtNodup).1
  rw [hback] at hrev
  simp only [fastCPA, Classical.run_append]
  change Classical.run (fastOut control pointReg temp auxStart (-C)).reverse
      (Classical.run (pointSwapReg pointReg temp)
        (Classical.run (fastOut control pointReg temp auxStart C) st)) = s1
  rw [hforward, hswap]
  exact hrev

omit [Fact (Nat.Prime p)] in
theorem fastCPA_HPFree (control : Wire) (pointReg : List Wire) (workStart : Wire) (C : Point) :
    HPFree (fastCPA control pointReg workStart C) := by
  simp only [fastCPA, hpFree_append]
  exact ⟨⟨fastOut_HPFree _ _ _ _ _, pointSwapReg_HPFree _ _⟩,
    Arithmetic.hpFree_reverse (fastOut_HPFree _ _ _ _ _)⟩

omit [Fact (Nat.Prime p)] in
theorem fastCPA_structural (control : Wire) (pointReg : List Wire) (workStart : Wire)
    (C : Point) (hnodup : ([control] ++ pointReg ++ controlledPointAddWork workStart).Nodup) :
    CircuitWellFormed (fastCPA control pointReg workStart C) ∧
      CircuitUsesOnly ([control] ++ pointReg ++ controlledPointAddWork workStart)
        (fastCPA control pointReg workStart C) := by
  let temp := controlledPointAddTemp workStart
  let auxStart := controlledPointAddAuxStart workStart
  let work := controlledPointAddOutWork auxStart
  have houtNodup : ([control] ++ pointReg ++ temp ++ work).Nodup := by
    simpa [temp, auxStart, work, controlledPointAddWork, controlledPointAddTemp,
      controlledPointAddAuxStart, List.append_assoc] using hnodup
  have h0 : (control :: (pointReg ++ temp ++ work)).Nodup := by
    simpa [List.append_assoc] using houtNodup
  have hswapNodup : (pointReg ++ temp).Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp h0).2).1
  have hf := fastOut_structural control pointReg temp auxStart C houtNodup
  have hb := fastOut_structural control pointReg temp auxStart (-C) houtNodup
  have hsupport : [control] ++ pointReg ++ controlledPointAddWork workStart =
      [control] ++ pointReg ++ temp ++ work := by
    simp [temp, auxStart, work, controlledPointAddWork, List.append_assoc]
  constructor
  · simp only [fastCPA, circuitWellFormed_append]
    exact ⟨⟨hf.1, pointSwapReg_wellFormed _ _ hswapNodup⟩, Arithmetic.wellFormed_reverse hb.1⟩
  · rw [hsupport]
    simp only [fastCPA]
    refine usesOnly_append (usesOnly_append hf.2 ?_) (usesOnly_reverse hb.2)
    apply usesOnly_mono (pointSwapReg_usesOnly pointReg temp)
    intro w hw
    simp only [List.mem_append] at hw ⊢
    tauto

/-! ## Exact T-count -/

omit [Fact (Nat.Prime p)] in
theorem fastBlock_tCount (control flag anc : Wire) (K : Circuit) (cand outReg : List Wire)
    (hlen : cand.length = outReg.length) :
    tCount (fastBlock control flag anc K cand outReg) = 2 * tCount K + 7 * outReg.length + 14 := by
  simp only [fastBlock, tCount_append, tCount_reverse, controlledCopyReg_tCount anc cand outReg hlen]
  simp [tCount, tCost]
  omega

omit [Fact (Nat.Prime p)] in
theorem fastOut_tCount (control : Wire) (pointReg outReg : List Wire) (workStart : Wire)
    (C : Point) (hP : pointReg.length = pointWidth) (hO : outReg.length = pointWidth) :
    tCount (fastOut control pointReg outReg workStart C) = 41911338924 := by
  have hc : (pointAddCandidate (controlledPointAddPointWorkStart workStart)).length =
      outReg.length := by rw [hO]; simp [pointAddCandidate]
  simp only [fastOut, fastBlocks, fastPass, tCount_append, tCount_reverse,
    fastBlock_tCount _ _ _ _ _ _ hc, controlledCopyReg_tCount control pointReg outReg
      (by rw [hP, hO]), pointAddSetup_tCount, fastGenericK, genericPointCompute_tCount,
    packFinitePoint_tCount, loadConst_tCount, hO]
  simp [tCount, tCost, pointWidth]

omit [Fact (Nat.Prime p)] in
theorem fastCPA2_tCount (control : Wire) (pointReg : List Wire) (workStart : Wire)
    (C C' : Point) (hP : pointReg.length = pointWidth) :
    tCount (fastOut control pointReg (controlledPointAddTemp workStart)
        (controlledPointAddAuxStart workStart) C ++
      pointSwapReg pointReg (controlledPointAddTemp workStart) ++
      (fastOut control pointReg (controlledPointAddTemp workStart)
        (controlledPointAddAuxStart workStart) C').reverse) = 83822677848 := by
  have ht : (controlledPointAddTemp workStart).length = pointWidth := by
    simp [controlledPointAddTemp]
  simp only [tCount_append, tCount_reverse, fastOut_tCount _ _ _ _ _ hP ht, pointSwapReg_tCount]

omit [Fact (Nat.Prime p)] in
theorem pointSwapReg_usesOnly' (left right : List Wire) :
    CircuitUsesOnly (left ++ right) (pointSwapReg left right) :=
  pointSwapReg_usesOnly left right

end V2
end Secp256k1
end ShorECDLP
