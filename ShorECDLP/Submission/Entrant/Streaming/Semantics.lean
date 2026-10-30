import ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation
import ShorECDLP.Submission.Entrant.Streaming.Resources
import ShorECDLP.Submission.«2607_13816».Window.StreamKernel
import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Framework.Quantum.TerminalInterference
import ShorECDLP.Submission.«2607_13816».Window.Uniform

open ShorECDLP.Entrant.ZeroAdaptive

/-! EDITABLE. Single-trial entrant: inherited coherent physical and Fourier lemmas.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Streaming/BatchBoundary ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchBoundary.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. The in-place XOR
correction keeps no resident endpoint workspace, so `batchWorkspace` is empty and the
five-word placement lemmas are gone. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge

def batchWorkspace : List Wire := []
def BatchedPointReady (s : BasisState) : Prop := PointLookupValid s ∧ Clean batchWorkspace s

theorem batchWorkspace_outside (w : Wire) (hw : w ∈ batchWorkspace) : w ∉ pointLogicalWires := by
  simp [batchWorkspace] at hw

theorem windowYNegateState_batchedReady (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (windowYNegateState s) := by
  have hf := (windowYNegateState_correct s hs.1.1).2
  refine ⟨⟨windowYNegateState_ready s hs.1.1,?_⟩,?_⟩
  · rw [hf 836 (by decide)]
    exact hs.1.2
  · intro w hw
    rw [hf w (by
      intro hy
      exact batchWorkspace_outside w hw (List.mem_append_right _ (List.mem_append_left _ hy)))]
    exact hs.2 w hw
theorem signedLookupCoordinateState_batchedReady (x y : Nat → Nat) (s : BasisState)
    (hs : BatchedPointReady s) : BatchedPointReady (signedLookupCoordinateState x y s) := by
  refine ⟨signedLookupCoordinateState_ready x y s hs.1,?_⟩
  intro w hw
  have hout := batchWorkspace_outside w hw
  rw [signedLookupCoordinateState_frame x y s hs.1 w
    (fun hx => hout (List.mem_append_left _ hx))
    (fun hy => hout (List.mem_append_right _ (List.mem_append_left _ hy)))]
  exact hs.2 w hw

private theorem address_frame (bits : List Wire) (s t : BasisState)
    (h : ∀ w ∈ bits, s w=t w) : tableAddressValue bits s=tableAddressValue bits t := by
  induction bits with
  | nil => rfl
  | cons w ws ih =>
    simp only [tableAddressValue,h w (by simp),ih (fun w hw => h w (by simp [hw]))]

theorem batchWindowTree_route (s : BasisState) :
    batchWindowTree.routeLabel s = tableAddressValue pointLookupAddress s := by
  rw [batchWindowTree,tableAddressTree_route,zero_add,one_mul]

theorem windowYNegateState_address (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    tableAddressValue pointLookupAddress (windowYNegateState s)=tableAddressValue pointLookupAddress s := by
  apply address_frame
  intro w hw
  apply (windowYNegateState_correct s hs).2 w
  simp only [pointLookupAddress,List.mem_range'_1] at hw
  simp only [List.mem_range'_1]
  omega

theorem pointWrite_batchedReady (P : Point) (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (pointWrite P s) := by
  refine ⟨⟨pointWrite_valid P s hs.1.1,?_⟩,?_⟩
  · rw [pointWrite_frame P s 836 (by decide +kernel)]
    exact hs.1.2
  · intro w hw
    rw [pointWrite_frame P s w (batchWorkspace_outside w hw)]
    exact hs.2 w hw

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/BatchedWindowState ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchedWindowState.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
noncomputable def signedBatchState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  windowYNegateState (ipxState Q w (windowYNegateState s))

theorem pointWrite_frame_eq (P : Point) (s t : BasisState)
    (h : ∀ w, w ∉ pointLogicalWires → s w=t w) : pointWrite P s=pointWrite P t := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hw]
  · simp only [pointWrite,if_neg hw,h w hw]

theorem signedBatchState_pointWrite (Q : Point) (w : OddWindow) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    signedBatchState Q w s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
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
  have he := ipxState_pointWrite Q w _ ht htq hC hr hord P' hd
  have hsign : ipxState Q w (windowYNegateState s) 854 = s 854 :=
    (ipxState_frame Q w _ (ipxInv_of_valid _ ht htq) 854 (by decide +kernel)
      (ipxFlag_ne_of_ge 854 (by decide))).trans
      ((windowYNegateState_correct s hs).2 854 (by decide +kernel))
  have hv : Secp256k1ZeroAllowedInputValid (ipxState Q w (windowYNegateState s)) := by
    rw [he]; exact pointWrite_valid _ _ ht
  have hc : pointStateCoordinates (ipxState Q w (windowYNegateState s)) =
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
theorem windowPoint_order (Q : Point) (hQ : order • Q=0) (w : OddWindow) (a : Nat) :
    order • windowPoint Q w a = 0 := by
  have key : ∀ P : Point, order • P = 0 → ∀ j, order • oddWindowPoint P j a = 0 := by
    intro P hP j
    unfold oddWindowPoint
    rw [smul_comm order,smul_comm order,signedWindowHalfPoint,smul_comm order,hP,nsmul_zero,nsmul_zero,
      nsmul_zero]
  cases w with
  | left j => exact key G generator_nsmul_eq_zero j.val
  | right j => exact key Q hQ j.val

noncomputable def batchedWindowState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  signedBatchState Q w (signedLookupCoordinateState
    (fun a => fieldValue (windowPoint Q w a) .x) (fun a => fieldValue (windowPoint Q w a) .y) s)

theorem batchedWindowState_finite (Q : Point) (hQ : order • Q=0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : windowPoint Q w (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState Q w s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
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
  have hr' : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (windowYNegateState t)))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    unfold batchWindowRows
    rw [coefficientAt_window,oddWindowCoefficients_point w _ Q hQ]
    have hb : tableAddressValue pointLookupAddress s < 32768 := tableAddressValue_lt pointLookupAddress s
    simpa only [Nat.mod_eq_of_lt hb] using hr
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
  have hord : order • (.some hC : Point) = 0 := hr ▸ windowPoint_order Q hQ w _
  have he := signedBatchState_pointWrite Q w t ht.1.1 ht.1.2 hC hr' hord P hd
  change signedBatchState Q w t= _
  rw [he,hz]
  apply pointWrite_frame_eq
  intro v hv
  exact signedLookupCoordinateState_frame xs ys s hs.1 v
    (fun hx => hv (List.mem_append_left _ hx))
    (fun hy => hv (List.mem_append_right _ (List.mem_append_left _ hy)))
theorem windowPoint_ne_zero (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) (a : Nat) :
    windowPoint Q w a ≠ 0 := by
  cases w with
  | left j => exact oddWindowPoint_ne_zero G G_ne_zero generator_nsmul_eq_zero j.val a
  | right j => exact oddWindowPoint_ne_zero Q hn hQ j.val a

theorem batchedWindowState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress s)
        else -windowPoint Q w (tableAddressValue pointLookupAddress s)) s := by
  cases he : windowPoint Q w (tableAddressValue pointLookupAddress s) with
  | zero => exact False.elim (windowPoint_ne_zero Q hQ hn w _ he)
  | some hC => exact batchedWindowState_finite Q hQ w s hs hC he P hP

theorem signedBatchState_middle_ready (Q : Point) (w : OddWindow) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    Secp256k1ZeroAllowedInputValid (ipxState Q w (windowYNegateState s)) := by
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
  rw [ipxState_pointWrite Q w _ ht htq hC hr hord P' hd]
  exact pointWrite_valid _ _ ht

def SignedBatchReady (Q : Point) (w : OddWindow) (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y),
    constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC ∧
    order • (.some hC : Point) = 0 ∧
    ∃ P : Point, pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/BatchedWindowCoherent ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchedWindowCoherent.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
private theorem restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

theorem composeCoherent {a b : AdaptiveCircuit} {f g : BasisState → BasisState}
    {P R : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) P)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) R)
    (hf : ∀ s, P s → R (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) P := by
  have h := ha.seq hb (by
    intro s hs
    simpa [ket] using supportedOn_ket R (f s) (hf s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

noncomputable def signedBatchSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (windowYNegate.seq (ipxSource Q w)).seq windowYNegate

theorem signedBatchSource_coherent (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn (signedBatchSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (signedBatchState Q w)) (SignedBatchReady Q w) := by
  have hneg : CoherentlyImplementsOn windowYNegate (Finsupp.lmapDomain ℂ ℂ windowYNegateState)
      (SignedBatchReady Q w) := restrictCoherent windowYNegate_coherent (fun s hs => hs.1.1.1)
  have hfirst := composeCoherent hneg (ipxSource_state Q w) (fun s hs => by
    have hn := windowYNegateState_batchedReady s hs.1
    exact ipxInv_of_valid _ hn.1.1 hn.1.2)
  have hlast := composeCoherent hfirst windowYNegate_coherent (by
    intro s hs
    obtain ⟨hr,x,y,hC,hrow,hord,P,hdata⟩ := hs
    exact signedBatchState_middle_ready Q w s hr.1.1 hr.1.2 hC hrow hord P hdata)
  exact hlast
theorem batchedWindow_coordinate_ready (Q : Point) (hQ : order • Q=0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : windowPoint Q w (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    SignedBatchReady Q w (signedLookupCoordinateState
      (fun a => fieldValue (windowPoint Q w a) .x) (fun a => fieldValue (windowPoint Q w a) .y) s) := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
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
  have hr' : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (windowYNegateState t)))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    unfold batchWindowRows
    rw [coefficientAt_window,oddWindowCoefficients_point w _ Q hQ]
    have hb : tableAddressValue pointLookupAddress s < 32768 := tableAddressValue_lt pointLookupAddress s
    simpa only [Nat.mod_eq_of_lt hb] using hr
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
  exact ⟨ht,x,y,hC,hr',hr ▸ windowPoint_order Q hQ w _,P,hd⟩

def BatchedWindowValid (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ P : Point, pointStateCoordinates s=fig14PointEncoding P

theorem ipxWindowSources_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) :
    CoherentlyImplementsOn (sequenceCircuit (ipxWindowSources Q w))
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState Q w)) BatchedWindowValid := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
  have hfirst : CoherentlyImplementsOn (ShorECDLP.Entrant.ZeroAdaptive.coordinateSource xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    restrictCoherent (ShorECDLP.Entrant.ZeroAdaptive.coordinateSource_coherent xs ys) (fun s hs => hs.1.1)
  have h := composeCoherent hfirst (signedBatchSource_coherent Q w) (by
    intro s hs
    obtain ⟨hs,P,hP⟩ := hs
    cases he : windowPoint Q w (tableAddressValue pointLookupAddress s) with
    | zero => exact False.elim (windowPoint_ne_zero Q hQ hn w _ he)
    | some hC => exact batchedWindow_coordinate_ready Q hQ w s hs hC he P hP)
  simpa only [ipxWindowSources,sequenceCircuit,signedBatchSource,adaptive_seq_assoc,adaptive_seq_done,
    batchedWindowState,xs,ys] using h
theorem ipxWindowCore_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((ipxWindowCore w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState Q w)) BatchedWindowValid := by
  have h := ipxWindowSources_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := ipxWindowCore_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/PreparedBatch ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/PreparedBatch.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
def batchPrepareState : BasisState → BasisState := signedAddressState 836 854 pointLookupAddress

theorem batchPrepareState_frame (s : BasisState) (w : Wire) (hw : w ∉ pointLookupAddress) :
    batchPrepareState s w=s w := signedAddressState_frame 836 854 pointLookupAddress s w hw

private theorem address_outside_point (w : Wire) (hw : w ∈ pointLogicalWires) : w ∉ pointLookupAddress := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false] at hw
  simp only [pointLookupAddress,List.mem_range'_1]
  dsimp only [Wire] at *
  omega

private theorem prepare_word (s : BasisState) (bits : List Wire)
    (h : ∀ w ∈ bits, w ∉ pointLookupAddress) : wireValues bits (batchPrepareState s)=wireValues bits s := by
  apply List.map_congr_left
  intro w hw
  exact batchPrepareState_frame s w (h w hw)

theorem batchPrepareState_ready (s : BasisState) (hs : BatchedPointReady s) : BatchedPointReady (batchPrepareState s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩
  · intro w hw
    rw [batchPrepareState_frame s w (by
      simp only [List.mem_append,List.mem_range'_1] at hw
      simp only [pointLookupAddress,List.mem_range'_1]
      omega)]
    exact hs.1.1.1 w hw
  · rw [batchPrepareState_frame s 837 (by decide)]
    exact hs.1.1.2.1
  · rw [prepare_word s (List.range' 263 256) (fun w hw => address_outside_point w (List.mem_append_left _ hw))]
    exact hs.1.1.2.2.1
  · rw [prepare_word s (List.range' 580 256) (fun w hw => address_outside_point w (List.mem_append_right _ (List.mem_append_left _ hw)))]
    exact hs.1.1.2.2.2
  · rw [batchPrepareState_frame s 836 (by decide)]
    exact hs.1.2
  · intro w hw
    simp [batchWorkspace] at hw

theorem batchPrepareState_coordinates (s : BasisState) : pointStateCoordinates (batchPrepareState s)=pointStateCoordinates s := by
  unfold pointStateCoordinates
  rw [batchPrepareState_frame s 838 (by decide),
    prepare_word s (List.range' 263 256) (fun w hw => address_outside_point w (List.mem_append_left _ hw)),
    prepare_word s (List.range' 580 256) (fun w hw => address_outside_point w (List.mem_append_right _ (List.mem_append_left _ hw)))]

theorem batchPrepareState_pointWrite (P : Point) (s : BasisState) :
    batchPrepareState (pointWrite P s)=pointWrite P (batchPrepareState s) := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · rw [batchPrepareState_frame _ w (address_outside_point w hw)]
    simp only [pointWrite,if_pos hw]
  · rw [pointWrite_frame _ _ w hw]
    unfold batchPrepareState signedAddressState tableXorState
    rw [pointWrite_frame P s 854 (by decide +kernel),pointWrite_frame P s 836 (by decide +kernel),pointWrite_frame P s w hw]

theorem batchPrepareState_involution (s : BasisState) : batchPrepareState (batchPrepareState s)=s :=
  signedAddressState_involution 836 854 pointLookupAddress (by decide) (by decide) s
theorem batchPrepareState_valid (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (batchPrepareState s) := by
  obtain ⟨hs,P,hP⟩ := hs
  exact ⟨batchPrepareState_ready s hs,P,(batchPrepareState_coordinates s).trans hP⟩

theorem batchedWindowState_valid (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (batchedWindowState Q w s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [batchedWindowState_correct Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

noncomputable def preparedBatchState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  batchPrepareState (batchedWindowState Q w (batchPrepareState s))

theorem preparedBatchState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    preparedBatchState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress (batchPrepareState s))
        else -windowPoint Q w (tableAddressValue pointLookupAddress (batchPrepareState s))) s := by
  unfold preparedBatchState
  rw [batchedWindowState_correct Q hQ hn w _ (batchPrepareState_ready s hs) P
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

theorem ipxWindowPreparedSource_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) :
    CoherentlyImplementsOn (ipxWindowPreparedSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)) BatchedWindowValid := by
  have hc := composeCoherent (ipxWindowSources_coherent Q hQ hn w) batchPrepare_coherent
    (batchedWindowState_valid Q hQ hn w)
  have h := composeCoherent (f := batchPrepareState)
    (g := fun s => batchPrepareState (batchedWindowState Q w s))
    batchPrepare_coherent hc batchPrepareState_valid
  exact h

theorem ipxWindowPrepared_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((ipxWindowPrepared w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)) BatchedWindowValid := by
  have h := ipxWindowPreparedSource_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := ipxWindowPrepared_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ActualWindow ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ActualWindow.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
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

noncomputable def actualIpxWindowState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm 855 (by decide))
    (preparedBatchState Q w (relabelBasis (windowAddressPerm 855 (by decide)).symm s))

theorem actualIpxWindow_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn (((actualIpxWindow w).program start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)) BatchedWindowValid := by
  have h := (ipxWindowPreparedSource_coherent Q hQ hn w).relabel (windowAddressPerm 855 (by decide))
  have hr : CoherentlyImplementsOn ((ipxWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide)))
      ((relabelState (windowAddressPerm 855 (by decide))).comp
        ((Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)).comp
          (relabelState (windowAddressPerm 855 (by decide)).symm))) BatchedWindowValid := by
    obtain ⟨cs,hc,hm⟩ := h
    exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (actualWindow_pullback_valid s hs)),hm⟩
  have he : CoherentlyImplementsOn ((ipxWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide)))
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)) BatchedWindowValid := by
    apply hr.congrIdeal
    intro s hs
    simp [actualIpxWindowState,LinearMap.comp_apply,relabelState,ket]
  unfold CoherentlyImplementsOn at he ⊢
  rw [actualIpxWindow_run w start Q hQ history]
  exact he

theorem actualIpxWindowState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualIpxWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))
        else -windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))) s := by
  unfold actualIpxWindowState
  rw [preparedBatchState_correct Q hQ hn w _ (actualWindow_pullback_ready s hs) P
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


theorem actualIpxWindowState_selected (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualIpxWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
        else -windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) s := by
  rw [actualIpxWindowState_correct Q hQ hn w s hs P hP,actualWindow_selected_address s hs]

theorem actualIpxWindowState_valid (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (actualIpxWindowState Q w s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualIpxWindowState_selected Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

theorem actualIpxWindowState_frame (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) (v : Wire) (hv : v∉pointLogicalWires) :
    actualIpxWindowState Q w s v=s v := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualIpxWindowState_selected Q hQ hn w s hs P hP]
  simp [pointWrite,hv]

/-- The mixed first-window table may contain infinity; this direct-load theorem
has no nonzero-table-entry hypothesis. -/
theorem actualFirstWindow_coherent (Q : Point) (hQ : order • Q=0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actualFirstWindow.program start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite
        (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
          ((2^(16*15)) • G) (tableAddressValue (List.range' 855 16) s)) s))
      (DirectPointLookupValid (List.range' 519 16) 836) := by
  unfold CoherentlyImplementsOn
  rw [actualFirstWindow_run start Q hQ history]
  exact physicalPointLookup_coherent _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowValidity ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowValidity.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1

theorem batchedWindowValid_address_update (s : BasisState) (hs : BatchedWindowValid s)
    (w : Wire) (hw : w ∈ streamAddress) (b : Bool) : BatchedWindowValid (s[w ↦ b]) := by
  have hw' : 855 ≤ w ∧ w < 871 := by simpa [streamAddress,List.mem_range'_1] using hw
  have hcore (v : Wire) (hv : v < 839) : (s[w ↦ b]) v = s v := by
    simp only [upd]
    rw [if_neg (by dsimp only [Wire] at *; omega)]
  have hx : wireValues (List.range' 263 256) (s[w ↦ b]) = wireValues (List.range' 263 256) s := by
    apply List.map_congr_left
    intro v hv
    exact hcore v (by simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  have hy : wireValues (List.range' 580 256) (s[w ↦ b]) = wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro v hv
    exact hcore v (by simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  obtain ⟨⟨⟨hclean,hzero,hxbound,hybound⟩,hq⟩,-⟩ := hs.1
  refine ⟨⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro v hv
    rw [hcore v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)]
    exact hclean v hv
  · rw [hcore 837 (by decide)]; exact hzero
  · rw [hx]; exact hxbound
  · rw [hy]; exact hybound
  · rw [hcore 836 (by decide)]; exact hq
  · intro v hv
    simp [batchWorkspace] at hv
  · obtain ⟨P,hP⟩ := hs.2
    refine ⟨P,?_⟩
    simpa only [pointStateCoordinates,hcore 838 (by decide),hx,hy] using hP


private theorem support_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ+φ) := by
  intro s hs
  by_cases h : ψ s=0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h
private theorem support_smul {V : BasisState → Prop} {ψ : State} (c : ℂ)
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])
private theorem support_linear (V : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn V (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn V (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz,hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u=s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,he,map_smul]
    exact support_add (support_smul c (hL s hvs)) (ih hvψ)

theorem batchedWindowValid_fourierClear (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (s : BasisState)
    (hs : BatchedWindowValid s) : BatchedWindowValid (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => exact hs
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (batchedWindowValid_address_update s hs w (hws w (by simp)) false)

theorem batchedWindowValid_fourierBranch (dir : PhaseDir) (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (prior bs : List Bool)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (fourierBranch dir ws prior bs ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  rw [fourierBranch_ket]
  exact support_smul _ (supportedOn_ket _ _
    (batchedWindowValid_fourierClear ws hws s hs))

theorem batchedWindowValid_H (w : Wire) (hw : w ∈ streamAddress)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (applyGate (.H w) ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  rw [applyGate_ket]
  exact support_add
    (support_smul _ (supportedOn_ket _ _ (batchedWindowValid_address_update s hs w hw false)))
    (support_smul _ (supportedOn_ket _ _ (batchedWindowValid_address_update s hs w hw true)))

theorem batchedWindowValid_prepare (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (ψ : State)
    (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (batchedWindowValid_H w (hws w (by simp)) ψ hψ)


theorem actualIpxWindowState_supported (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (ψ : State)
    (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w) ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  simpa [ket] using supportedOn_ket BatchedWindowValid _
    (actualIpxWindowState_valid Q hQ hn w s hs)

theorem actualIpxWindow_branch_supported (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (start : Nat) (history : Fin start → Bool)
    (b : InstrumentBranch)
    (hb : b ∈ (((actualIpxWindow w).program start).instantiate
      (readConstant coefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (b.kraus ψ) := by
  obtain ⟨c,hc⟩ := (actualIpxWindow_coherent Q hQ hn w start history).branch_coefficient b hb
  rw [hc.on_supported hψ]
  exact support_smul c (actualIpxWindowState_supported Q hQ hn w ψ hψ)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/FirstValidity ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/FirstValidity.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1

private theorem zero_word (n : Nat) : boolWordToNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]
private theorem zero_read (ws : List Wire) (s : BasisState)
    (hs : ∀ w ∈ ws, s w = false) :
    wireValues ws s = List.replicate ws.length false := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wireValues,List.map_cons,List.length_cons,List.replicate_succ]
    rw [hs w (by simp)]
    exact congrArg (false :: ·) (ih (fun v hv => hs v (List.mem_cons_of_mem w hv)))

/-- Before direct loading, only the query flag and address register may be nonzero. -/
def FirstWindowInput (s : BasisState) : Prop :=
  s 836 = true ∧ ∀ v, v ≠ 836 → v ∉ streamAddress → s v = false

theorem firstWindowInput_start : FirstWindowInput (zeroBasisState[836 ↦ true]) := by
  constructor
  · simp [upd]
  · intro v hv _
    simp [upd,hv,zeroBasisState]

theorem firstWindowInput_update (s : BasisState) (hs : FirstWindowInput s)
    (w : Wire) (hw : w ∈ streamAddress) (b : Bool) : FirstWindowInput (s[w ↦ b]) := by
  have hw' : 855 ≤ w ∧ w < 871 := by simpa [streamAddress,List.mem_range'_1] using hw
  have hwb : 855 ≤ w := hw'.1
  constructor
  · simpa only [upd,if_neg (by dsimp only [Wire] at *; omega : (836:Wire) ≠ w)] using hs.1
  · intro v hv ha
    have hvw : v ≠ w := by intro he; subst v; exact ha hw
    simpa only [upd,if_neg hvw] using hs.2 v hv ha

theorem firstWindowInput_ready (s : BasisState) (hs : FirstWindowInput s) :
    BatchedPointReady s := by
  have hz (v : Wire) (hv : v < 836) : s v = false :=
    hs.2 v (by dsimp only [Wire] at *; omega) (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)
  have hx : wireValues (List.range' 263 256) s = List.replicate 256 false := by
    exact (zero_read _ s (fun v hv => hz v (by
      simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega))).trans
      (by simp only [List.length_range'])
  have hy : wireValues (List.range' 580 256) s = List.replicate 256 false := by
    exact (zero_read _ s (fun v hv => hz v (by
      simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega))).trans
      (by simp only [List.length_range'])
  refine ⟨⟨⟨?_,?_,?_,?_⟩,hs.1⟩,?_⟩
  · intro v hv
    exact hz v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  · exact hs.2 837 (by decide) (by simp [streamAddress])
  · rw [hx]; rw [zero_word]; norm_num [ShorECDLP.p]
  · rw [hy]; rw [zero_word]; norm_num [ShorECDLP.p]
  · intro v hv
    simp [batchWorkspace] at hv

theorem firstWindowInput_lookup (s : BasisState) (hs : FirstWindowInput s) :
    DirectPointLookupValid (List.range' 519 16) 836 s := by
  refine ⟨?_,?_,hs.1⟩
  · intro v hv
    apply hs.2
    · simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
    · simp only [List.mem_range'_1] at hv
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega
  · intro v hv
    have hb : v < 839 := by
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    have hn : v ≠ 836 := by
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    exact hs.2 v hn (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)

theorem firstWindowInput_pointWrite (s : BasisState) (hs : FirstWindowInput s) (P : Point) :
    BatchedWindowValid (pointWrite P s) :=
  ⟨pointWrite_batchedReady P s (firstWindowInput_ready s hs),P,pointWrite_coordinates P s⟩



private theorem support_linear_FirstValidity (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn W (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn W (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz,hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u=s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,he,map_smul]
    exact support_add (support_smul c (hL s hvs)) (ih hvψ)

theorem firstWindowInput_H (w : Wire) (hw : w ∈ streamAddress)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn FirstWindowInput (applyGate (.H w) ψ) := by
  apply support_linear_FirstValidity FirstWindowInput FirstWindowInput (applyGate (.H w)) ?_ ψ hψ
  intro s hs
  rw [applyGate_ket]
  exact support_add
    (support_smul _ (supportedOn_ket _ _ (firstWindowInput_update s hs w hw false)))
    (support_smul _ (supportedOn_ket _ _ (firstWindowInput_update s hs w hw true)))

theorem firstWindowInput_prepare (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (ψ : State)
    (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn FirstWindowInput (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (firstWindowInput_H w (hws w (by simp)) ψ hψ)

noncomputable def actualFirstWindowState (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
    ((2^(16*15)) • G) (tableAddressValue (List.range' 855 16) s)) s

theorem actualFirstWindowState_supported (Q : Point) (ψ : State)
    (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn BatchedWindowValid
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q) ψ) := by
  apply support_linear_FirstValidity FirstWindowInput BatchedWindowValid _ ?_ ψ hψ
  intro s hs
  rw [show Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q) (ket s) =
      ket (actualFirstWindowState Q s) from by simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]]
  exact supportedOn_ket _ _ (firstWindowInput_pointWrite s hs _)

theorem actualFirstWindow_coherent_input (Q : Point) (hQ : order • Q = 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actualFirstWindow.program start).instantiate
      (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput := by
  obtain ⟨cs,ha,hm⟩ := actualFirstWindow_coherent Q hQ start history
  exact ⟨cs,ha.imp (fun _ _ hb s hs => hb s (firstWindowInput_lookup s hs)),hm⟩

theorem actualFirstWindow_branch_supported (Q : Point) (hQ : order • Q = 0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((actualFirstWindow.program start).instantiate
      (readConstant coefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn BatchedWindowValid (b.kraus ψ) := by
  obtain ⟨c,hc⟩ := (actualFirstWindow_coherent_input Q hQ start history).branch_coefficient b hb
  rw [hc.on_supported hψ]
  exact support_smul c (actualFirstWindowState_supported Q ψ hψ)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CrossWindowWeights ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CrossWindowWeights.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Chronological outputs from later windows have the higher binary weights. -/
theorem fourierWordLSB_append (xs ys : List Bool) :
    fourierWordLSB (xs ++ ys) = fourierWordLSB xs + 2 ^ xs.length * fourierWordLSB ys := by
  induction xs with
  | nil => simp [fourierWordLSB]
  | cons b xs ih =>
    simp only [List.cons_append, fourierWordLSB, List.length_cons, ih, pow_succ]
    ring

/-- Reversing the newest-first feedback history restores chronological output. -/
theorem fourierWordLSB_updated_history (bits prior : List Bool) :
    fourierWordLSB (bits.reverse ++ prior).reverse =
      fourierWordLSB prior.reverse + 2 ^ prior.length * fourierWordLSB bits := by
  rw [List.reverse_append, List.reverse_reverse, fourierWordLSB_append, List.length_reverse]

/-- Input words use the opposite convention: the first window is most significant. -/
theorem fourierWordMSB_append (xs ys : List Bool) :
    fourierWordMSB (xs ++ ys) = fourierWordMSB xs * 2 ^ ys.length + fourierWordMSB ys := by
  induction xs with
  | nil => simp [fourierWordMSB]
  | cons b xs ih =>
    simp only [List.cons_append, fourierWordMSB, List.length_append, ih, pow_add]
    ring

-- Both sides of the signed-address boundary, including both extreme addresses.
example : [0, 32767, 32768, 65535].map (signedTableOdd 32768) =
    [-65535, -1, 1, 65535] := by decide +kernel

-- Two radix-65536 input windows. The fixed offset cancels both centered digits.
example : ([0, 32767, 32768, 65535] : List Nat).all (fun a =>
    [0, 32767, 32768, 65535].all (fun b =>
      65535 * (65536 + 1) + signedTableOdd 32768 a * 65536 +
        signedTableOdd 32768 b == 2 * ((a : Int) * 65536 + b))) = true := by
  decide +kernel

example : fourierWordLSB (List.replicate 16 false ++ true :: List.replicate 15 false) =
    65536 := by decide +kernel

/-- The offset cancellation holds for every pair of input digits, including the
sign boundary. Multiplication by a half-point turns the right side into the
ordinary unsigned two-window scalar. -/
theorem two_window_signed_offset (a b : Nat) :
    65535 * (65536 + 1) + signedTableOdd 32768 a * 65536 + signedTableOdd 32768 b =
      2 * ((a : Int) * 65536 + b) := by
  rw [signedTableOdd_value, signedTableOdd_value]
  ring

/-- Splitting a Fourier word at a window boundary retains all feedback phases. -/
theorem fourierBitAmplitude_append (dir : PhaseDir) (xs ys prior bs cs : List Bool)
    (hl : bs.length = xs.length) :
    fourierBitAmplitude dir (xs ++ ys) prior (bs ++ cs) =
      fourierBitAmplitude dir xs prior bs *
        fourierBitAmplitude dir ys (bs.reverse ++ prior) cs := by
  induction xs generalizing prior bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp hl
    subst bs
    simp [fourierBitAmplitude]
  | cons a xs ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.cons_append, fourierBitAmplitude]
      rw [ih (b :: prior) bs (by simpa using hl)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      ring

/-- Actual feedback order for any number of complete windows. -/
theorem window_history_fold (windows : List (List Bool)) (prior : List Bool) :
    windows.foldl (fun history bits => bits.reverse ++ history) prior =
      windows.flatten.reverse ++ prior := by
  induction windows generalizing prior with
  | nil => simp
  | cons bits windows ih =>
    simp only [List.foldl_cons, ih, List.flatten_cons, List.reverse_append, List.append_assoc]

/-- Product of the individual window amplitudes, with the actual newest-first
history carried from one window to the next. -/
noncomputable def windowFourierAmplitude (dir : PhaseDir) :
    List (List Bool × List Bool) → List Bool → ℂ
  | [], _ => 1
  | (input, output) :: windows, prior =>
      fourierBitAmplitude dir input prior output *
        windowFourierAmplitude dir windows (output.reverse ++ prior)

theorem windowFourierAmplitude_flatten (dir : PhaseDir)
    (windows : List (List Bool × List Bool)) (prior : List Bool)
    (hl : ∀ w ∈ windows, w.2.length = w.1.length) :
    windowFourierAmplitude dir windows prior =
      fourierBitAmplitude dir (windows.map Prod.fst).flatten prior
        (windows.map Prod.snd).flatten := by
  induction windows generalizing prior with
  | nil => simp [windowFourierAmplitude, fourierBitAmplitude]
  | cons w windows ih =>
    simp only [windowFourierAmplitude, List.map_cons, List.flatten_cons]
    rw [fourierBitAmplitude_append dir _ _ _ _ _ (hl w (by simp)),
      ih _ (fun v hv => hl v (List.mem_cons_of_mem w hv))]

/-- The entire axis has one Fourier kernel; window feedback introduces no
extra phase when the axis starts with empty history. -/
theorem windowFourierAmplitude_kernel (dir : PhaseDir)
    (windows : List (List Bool × List Bool))
    (hl : ∀ w ∈ windows, w.2.length = w.1.length) :
    windowFourierAmplitude dir windows List.nil =
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ (windows.map Prod.fst).flatten.length) *
        dyadicFourierKernel dir (windows.map Prod.fst).flatten.length
          (fourierWordMSB (windows.map Prod.fst).flatten)
          (fourierWordLSB (windows.map Prod.snd).flatten) := by
  have he : (windows.map Prod.snd).flatten.length =
      (windows.map Prod.fst).flatten.length := by
    induction windows with
    | nil => rfl
    | cons w windows ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rw [hl w (by simp), ih (fun v hv => hl v (List.mem_cons_of_mem w hv))]
  rw [windowFourierAmplitude_flatten dir windows List.nil hl,
    fourierBitAmplitude_eq dir _ List.nil _ he]
  simp [fourierHistoryPhase, fourierHistoryAngle]

/-- All centered odd digits, including the first mixed-table digit, reconstruct
an unsigned scalar after its fixed initial offset is added. -/
theorem signed_odd_digits_reconstruct (digits : List Nat) :
    signedWindowValue 65536 (digits.map (signedTableOdd 32768)) +
      (65535 * radixGeometric digits.length : Nat) =
      2 * (windowValue 65536 digits : Int) := by
  induction digits with
  | nil => simp [signedWindowValue, windowValue, radixGeometric]
  | cons d ds ih =>
    simp only [List.map_cons, List.length_cons, signedWindowValue,
      windowValue, radixGeometric, signedTableOdd_value]
    push_cast at ih ⊢
    linear_combination 65536 * ih

/-- Group-level reconstruction uses only the subgroup order, and imposes no
exceptional-point exclusion on the accumulator. -/
theorem signed_odd_digits_point {A : Type} [AddCommGroup A]
    (P : A) (r : Nat) (hr : Odd r) (hP : r • P = 0) (digits : List Nat) :
    signedWindowValue 65536 (digits.map (signedTableOdd 32768)) •
        signedWindowHalfPoint P r +
      (65535 * radixGeometric digits.length) • signedWindowHalfPoint P r =
        windowValue 65536 digits • P := by
  rw [← natCast_zsmul (signedWindowHalfPoint P r) (65535 * radixGeometric digits.length),
    ← add_zsmul, signed_odd_digits_reconstruct]
  rw [show 2 * (windowValue 65536 digits : Int) =
    (windowValue 65536 digits : Int) + (windowValue 65536 digits : Int) by ring,
    add_zsmul, natCast_zsmul, ← nsmul_add,
    signedWindowHalfPoint_double P r hr hP]

/-- A fixed-width list of windows retains leading zero windows. -/
theorem fixed_windows_flatten_length (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    windows.flatten.length = w * windows.length := by
  induction windows with
  | nil => simp
  | cons bits windows ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hw bits (by simp), ih (fun bs hb => hw bs (List.mem_cons_of_mem bits hb))]
    ring

/-- Chronological window outputs are the little-endian radix digits of the
integer accepted by the decoder. -/
theorem output_windows_value (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    fourierWordLSB windows.flatten = windowValue (2 ^ w) (windows.map fourierWordLSB) := by
  induction windows with
  | nil => rfl
  | cons bits windows ih =>
    simp only [List.flatten_cons, List.map_cons, windowValue, fourierWordLSB_append]
    rw [hw bits (by simp), ih (fun bs hb => hw bs (List.mem_cons_of_mem bits hb))]

private theorem windowValue_append (base : Nat) (xs ys : List Nat) :
    windowValue base (xs ++ ys) = windowValue base xs + base ^ xs.length * windowValue base ys := by
  induction xs with
  | nil => simp [windowValue]
  | cons x xs ih =>
    simp only [List.cons_append, windowValue, List.length_cons, ih, pow_succ]
    ring

/-- Input windows run in descending significance, opposite to emitted output
weights. This is the unsigned scalar reconstructed by the signed point tables. -/
theorem input_windows_value (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    fourierWordMSB windows.flatten =
      windowValue (2 ^ w) (windows.map fourierWordMSB).reverse := by
  induction windows with
  | nil => rfl
  | cons bits windows ih =>
    have ht := fun bs hb => hw bs (List.mem_cons_of_mem bits hb)
    simp only [List.flatten_cons, List.map_cons, List.reverse_cons,
      fourierWordMSB_append, windowValue_append, List.length_reverse, List.length_map,
      windowValue]
    rw [ih ht, fixed_windows_flatten_length w windows ht, pow_mul]
    ring

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CrossWindowPoint ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CrossWindowPoint.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1

/-- The sign bit and the unsigned value agree even at the two central digits. -/
theorem reused_window_digit_low (s : BasisState) :
    windowRawDigit 0 s < 32768 ↔ s 870 = false := by
  have hb := boolWordToNat_lt_pow_two (wireValues (windowAddressBits 0) s)
  simp only [wireValues, List.length_map, windowAddressBits, List.length_range'] at hb
  change boolWordToNat (wireValues (windowAddressBits 0) s) < 32768 at hb
  cases hh : s 870 <;> simp_all [windowRawDigit, windowBankStart]

/-- Actual signed table selection gives a centered odd scalar at its fixed
power-of-two weight. No accumulator point is excluded. -/
theorem reused_window_selected_odd (P : Point) (j : Nat) (s : BasisState) :
    (if s 870 then oddWindowPoint P j (signedTableAddress 32768 (windowRawDigit 0 s))
      else -oddWindowPoint P j (signedTableAddress 32768 (windowRawDigit 0 s))) =
    signedTableOdd 32768 (windowRawDigit 0 s) •
      ((2 ^ (16 * j)) • signedWindowHalfPoint P order) := by
  have ha := signedTableAddress_bound 32768 (windowRawDigit 0 s) (windowRawDigit_bound 0 s)
  simp only [oddWindowPoint, Nat.mod_eq_of_lt ha, signedTableOdd]
  cases hs : s 870
  · rw [if_neg (by decide), if_pos ((reused_window_digit_low s).mpr hs)]
    simp only [neg_zsmul, natCast_zsmul]
  · rw [if_pos rfl, if_neg (by intro h; have hh := (reused_window_digit_low s).mp h; simp [hs] at hh)]
    simp only [natCast_zsmul]

/-- The corrected actual left window has precisely its scalar digit action. -/
theorem actual_left_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (j : Fin 15) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualIpxWindowState Q (.left j) s =
      pointWrite (P + signedTableOdd 32768 (windowRawDigit 0 s) •
        ((2 ^ (16 * j.val)) • signedWindowHalfPoint G order)) s := by
  rw [actualIpxWindowState_selected Q hQ hn (.left j) s hs P hP]
  simp only [windowPoint, reused_window_selected_odd]

/-- The corrected actual right window has precisely its scalar digit action. -/
theorem actual_right_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (j : Fin 13) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualIpxWindowState Q (.right j) s =
      pointWrite (P + signedTableOdd 32768 (windowRawDigit 0 s) •
        ((2 ^ (16 * j.val)) • signedWindowHalfPoint Q order)) s := by
  rw [actualIpxWindowState_selected Q hQ hn (.right j) s hs P hP]
  simp only [windowPoint, reused_window_selected_odd]
/-- The mixed first table obeys the same centered odd-digit formula as the
later tables, including any row whose resulting point is infinity. -/
theorem actual_first_window_digit (Q : Point) (s : BasisState) :
    actualFirstWindowState Q s =
      pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
        signedTableOdd 32768 (windowRawDigit 0 s) •
          ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s := by
  have ha : tableAddressValue (List.range' 855 16) s = windowRawDigit 0 s := by
    simp [tableAddressValue, windowRawDigit, windowAddressBits, windowBankStart,
      List.range', wireValues, boolWordToNat]
    omega
  have hd : (2 ^ (16 * 15)) • signedWindowHalfPoint G order +
      (2 ^ (16 * 15)) • signedWindowHalfPoint G order = (2 ^ (16 * 15)) • G := by
    rw [← nsmul_add, signedWindowHalfPoint_double G order (by decide +kernel)
      generator_nsmul_eq_zero]
  have he := signedTable_point ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)
    32768 (windowRawDigit 0 s)
  rw [hd] at he
  have hh : signedWindowHalfPoint ((2 ^ (16 * 15)) • G) order =
      (2 ^ (16 * 15)) • signedWindowHalfPoint G order := by
    exact smul_comm ((order + 1) / 2) (2 ^ (16 * 15)) G
  simp only [actualFirstWindowState, firstWindowTable, ha, hh]
  rw [sub_eq_iff_eq_add.mp he]
  rfl

/-- Once the actual signed digits have been accumulated, the two initial
 offsets cancel exactly. This is an exact group identity, without a loss term. -/
theorem two_axis_signed_digits (Q : Point) (hQ : order • Q = 0)
    (left right : List Nat) (hl : left.length = 16) (hr : right.length = 13) :
    axisWindowOffset G 16 + axisWindowOffset Q 13 +
      signedWindowValue 65536 (left.map (signedTableOdd 32768)) •
        signedWindowHalfPoint G order +
      signedWindowValue 65536 (right.map (signedTableOdd 32768)) •
        signedWindowHalfPoint Q order =
      windowValue 65536 left • G + windowValue 65536 right • Q := by
  have hleft := signed_odd_digits_point G order (by decide +kernel)
    generator_nsmul_eq_zero left
  have hright := signed_odd_digits_point Q order (by decide +kernel) hQ right
  rw [hl] at hleft
  rw [hr] at hright
  change _ + axisWindowOffset G 16 = _ at hleft
  change _ + axisWindowOffset Q 13 = _ at hright
  rw [← hleft, ← hright]
  abel

/-- In bit-word form, the signed tables reconstruct exactly the two integers
used as input exponents by the 256/208 Fourier kernels. -/
theorem two_axis_input_words (Q : Point) (hQ : order • Q = 0)
    (left right : List (List Bool)) (hl : left.length = 16) (hr : right.length = 13)
    (hlw : ∀ bits ∈ left, bits.length = 16) (hrw : ∀ bits ∈ right, bits.length = 16) :
    axisWindowOffset G 16 + axisWindowOffset Q 13 +
      signedWindowValue 65536 ((left.map fourierWordMSB).reverse.map (signedTableOdd 32768)) •
        signedWindowHalfPoint G order +
      signedWindowValue 65536 ((right.map fourierWordMSB).reverse.map (signedTableOdd 32768)) •
        signedWindowHalfPoint Q order =
      fourierWordMSB left.flatten • G + fourierWordMSB right.flatten • Q := by
  rw [input_windows_value 16 left hlw, input_windows_value 16 right hrw]
  exact two_axis_signed_digits Q hQ _ _ (by simpa using hl) (by simpa using hr)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem literalProgram_wellFormed {n s : Nat} (gs : Circuit) (h : CircuitWellFormed gs) :
    (literalProgram (n:=n) (s:=s) gs).WellFormed := by
  apply gateProgram_wellFormed
  intro g hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  exact h v hv

theorem appendCompiled_wellFormed {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : p.2.WellFormed) (hq : q.2.WellFormed) : (appendCompiled p q).2.WellFormed := by
  simpa only [appendCompiled,castFinish_wellFormed] using straight_append_wellFormed p.2 q.2 hp hq

theorem prependCompiled_wellFormed {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hg : CircuitWellFormed gs) (hp : p.2.WellFormed) : (prependCompiled gs p).2.WellFormed :=
  straight_append_wellFormed _ _ (literalProgram_wellFormed gs hg) hp

theorem surroundCompiled_wellFormed {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hb : CircuitWellFormed before) (ha : CircuitWellFormed after) (hp : p.2.WellFormed) :
    (surroundCompiled before after p).2.WellFormed :=
  prependCompiled_wellFormed _ _ hb (appendCompiled_wellFormed _ _ hp (literalProgram_wellFormed after ha))

theorem sequenceProgram_wellFormed (n : Nat) (ps : List (FixedSegment n))
    (hp : ∀ p∈ps,∀ start,(p start).2.WellFormed) (start : Nat) :
    (sequenceProgram n ps start).2.WellFormed := by
  induction ps generalizing start with
  | nil => trivial
  | cons p ps ih =>
    exact appendCompiled_wellFormed _ _ (hp p (by simp) start)
      (ih (fun q hq => hp q (by simp [hq])) _)

theorem reindexStraight_wellFormed {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    (reindexStraight f p).WellFormed ↔ p.WellFormed := by
  have hg (g : TemplateGate n) : (reindexGate f g).WellFormed ↔ g.WellFormed := by
    cases g <;> rfl
  induction p with
  | done => rfl
  | gate g p ih => simp only [reindexStraight,Straight.WellFormed,hg,ih]
  | recordGate i v g p ih => simp only [reindexStraight,Straight.WellFormed,ih]
  | measure w p ih => exact ih

theorem reindexCompiled_wellFormed {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    (reindexCompiled f p).2.WellFormed ↔ p.2.WellFormed :=
  reindexStraight_wellFormed f p.2

theorem registerCorrectionProgram_wellFormed {n s e : Nat} (ws : List Wire)
    (indices : List (Fin s)) (next : Straight n s e) (hn : next.WellFormed) :
    (registerCorrectionProgram ws indices next).WellFormed := by
  induction ws generalizing indices with
  | nil => exact hn
  | cons w ws ih =>
    cases indices with
    | nil => exact hn
    | cons i is =>
      exact recordGates_wellFormed i (pauliZ w) _ (by simp [pauliZ,CircuitWellFormed,Gate.WellFormed]) (ih is)

theorem deferredCorrectionProgram_wellFormed (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (hc : CircuitWellFormed cleanup)
    (hcs : ∀ cell ∈ cells, CircuitWellFormed cell.1) (start : Nat) (prior : List (Fin start)) :
    (deferredCorrectionProgram n targets cleanup cells start prior).WellFormed := by
  induction cells generalizing start with
  | nil =>
    exact registerCorrectionProgram_wellFormed _ _ _
      (straight_append_wellFormed _ _ (literalProgram_wellFormed cleanup hc)
        (registerCorrectionProgram_wellFormed _ _ _ trivial))
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    simp only [deferredCorrectionProgram,castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalProgram_wellFormed gs (hcs (gs,w) (by simp)))
      (ih (fun c h => hcs c (by simp [h])) _ _)

theorem deferredCorrectionCircuit_physical (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (outcomes : List Bool)
    (h : (deferredCorrectionCircuit targets cleanup cells outcomes).WellFormed) :
    CircuitWellFormed cleanup ∧ ∀ cell∈cells,CircuitWellFormed cell.1 := by
  induction cells generalizing outcomes with
  | nil =>
    have hc := h.1
    simp only [CircuitWellFormed,List.forall_mem_append] at hc
    exact ⟨hc.1.2,by simp⟩
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    obtain ⟨hc,ht⟩ := ih (outcomes++[false]) h.2.1
    exact ⟨hc,by intro c hm; rcases List.mem_cons.mp hm with rfl|hm; exact h.1; exact ht c hm⟩

theorem deferredCorrectionProgram_wellFormed_of_source (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (outcomes : List Bool)
    (h : (deferredCorrectionCircuit targets cleanup cells outcomes).WellFormed)
    (start : Nat) (prior : List (Fin start)) :
    (deferredCorrectionProgram n targets cleanup cells start prior).WellFormed := by
  obtain ⟨hc,ht⟩ := deferredCorrectionCircuit_physical targets cleanup cells outcomes h
  exact deferredCorrectionProgram_wellFormed n targets cleanup cells hc ht start prior

theorem gidneyNontrivialProgram_wellFormed (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length = ds.length+1) (hk : ks.length=as.length)
    (hnz : (k::ks).all (fun b => !b)=false)
    (h : (controlledGidneyAddConst (a::as) (d::ds) (k::ks) q carry spare ancilla).WellFormed) :
    (gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).WellFormed := by
  have hh : CircuitWellFormed (gidneyAddCarryCell q carry spare ancilla a d k) ∧
      (deferredCorrectionCircuit (d::ds) (gidneyAddCleanup (a::as) (d::ds) (k::ks) q carry)
        (gidneyCarryCells q spare carry ancilla as ds ks) List.nil).WellFormed := by
    rw [← gidneyCarryCells_source q spare carry ancilla as ds ks _ _ List.nil hd hk]
    cases as with
    | nil => simp at hd
    | cons b bs => simpa only [controlledGidneyAddConst,hnz,Bool.false_eq_true,if_false,
        AdaptiveCircuit.WellFormed] using h
  exact straight_append_wellFormed _ _ (literalProgram_wellFormed _ hh.1)
    (deferredCorrectionProgram_wellFormed_of_source n _ _ _ List.nil hh.2 start List.nil)

theorem gidneyProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1) (hk : constant.length=input.length)
    (h : (controlledGidneyAddConst input dirty constant q carry spare ancilla).WellFormed) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.WellFormed := by
  let WF : ((count : Nat) × Straight n start (start+count)) → Prop := fun p => p.2.WellFormed
  change WF (gidneyProgram n start input dirty constant q carry spare ancilla)
  unfold gidneyProgram
  split
  · trivial
  · rename_i hz
    have hnz : constant.all (fun k => !k)=false := Bool.eq_false_iff.mpr hz
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have ha : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
          subst as
          have hks : ks=[] := List.eq_nil_of_length_eq_zero (by simpa using hk)
          subst ks
          dsimp only [WF]
          apply literalProgram_wellFormed
          have hh := h
          unfold controlledGidneyAddConst at hh
          simp only [hnz,Bool.false_eq_true,if_false,AdaptiveCircuit.WellFormed] at hh
          exact hh.1
        | cons d ds =>
          cases as with
          | nil => simp at hd
          | cons b bs =>
            dsimp only [WF]
            exact gidneyNontrivialProgram_wellFormed n start a d q carry spare ancilla (b::bs) ds k ks
              (by simpa using hd) (by simpa using hk) hnz h

theorem gidneyProgram_wellFormed (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1) (hk : constant.length=input.length)
    (hnd : ([q,carry,spare,ancilla]++input++dirty).Nodup) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.WellFormed :=
  gidneyProgram_wellFormed_of_source n start input dirty constant q carry spare ancilla hd hk
    (controlledGidneyAddConst_wellFormed input dirty constant q carry spare ancilla hk.symm hd hnd)

theorem compareCarryCells_wellFormed (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (targets : List Wire)
    (cleanup : Circuit) (outcomes : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (gidneyCompareTail q current spare ancilla flag
      (fun bs => registerZCorrection targets bs ++ cleanup ++ registerZCorrection targets bs)
      outcomes input dirty constant).WellFormed) :
    (deferredCorrectionCircuit targets cleanup
      (compareCarryCells q current spare ancilla flag input dirty constant) outcomes).WellFormed := by
  induction input generalizing current spare dirty constant outcomes with
  | nil =>
    have hd' : dirty=[] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant=[] := List.eq_nil_of_length_eq_zero hk
    subst dirty
    subst constant
    exact ⟨by simp [CircuitWellFormed],h⟩
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact ⟨h.1,ih spare current dirty constant (outcomes++[false]) (by simpa using hd)
          (by simpa using hk) h.2.1,
          ih spare current dirty constant (outcomes++[true]) (by simpa using hd)
          (by simpa using hk) h.2.2⟩

theorem compareCarryProgram_wellFormed_of_source (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (controlledGidneyCompareCarry (a::input) (d::dirty) (k::constant) q carry spare ancilla flag).WellFormed) :
    (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).WellFormed := by
  have hh := compareCarryCells_wellFormed q spare carry ancilla flag input dirty constant (d::dirty)
    (controlledConstCarryXor (a::input) (d::dirty) (k::constant) q carry) List.nil hd hk h.2
  exact straight_append_wellFormed _ _ (literalProgram_wellFormed _ h.1)
    (deferredCorrectionProgram_wellFormed_of_source n _ _ _ List.nil hh start List.nil)

theorem compareCoreProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (controlledGidneyCompareCarry input dirty constant q carry spare ancilla flag).WellFormed) :
    (compareCoreProgram n start input dirty constant q carry spare ancilla flag).2.WellFormed := by
  cases input with
  | nil => trivial
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact compareCarryProgram_wellFormed_of_source n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk) h

theorem compareGEProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (h : (controlledGidneyCompareGE input dirty threshold q carry spare ancilla flag).WellFormed) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.WellFormed := by
  let WF : ((count : Nat) × Straight n start (start+count)) → Prop := fun p => p.2.WellFormed
  change WF (compareGEProgram n start input dirty threshold q carry spare ancilla flag)
  unfold compareGEProgram
  split
  · rename_i hz
    exact literalProgram_wellFormed _ (by simpa only [controlledGidneyCompareGE,if_pos hz,
      AdaptiveCircuit.WellFormed,and_true] using h)
  · rename_i hz
    split
    · trivial
    · rename_i hh
      apply compareCoreProgram_wellFormed_of_source _ _ _ _ _ _ _ _ _ _ hd (by simp)
      simpa only [controlledGidneyCompareGE,if_neg hz,if_neg hh] using h

theorem compareGEProgram_wellFormed (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (hnd : ([q,carry,spare,ancilla,flag]++input++dirty).Nodup) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.WellFormed :=
  compareGEProgram_wellFormed_of_source n start input dirty threshold q carry spare ancilla flag hd
    (controlledGidneyCompareGE_wellFormed input dirty threshold q carry spare ancilla flag hd hnd)

theorem modularNegateProgram_wellFormed (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    (modularNegateProgram n start target dirty modulus q c r t f).2.WellFormed := by
  have hl := constantModular_layout target dirty q c r t f hnd
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  have hq : q∉target := by
    intro hh
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 q (by simp) q hh rfl
  unfold modularNegateProgram
  apply appendCompiled_wellFormed
  · exact compareGEProgram_wellFormed n start target dirty 1 q c r t f hd hnd
  · apply prependCompiled_wellFormed
    · intro gate hg
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
      exact fun he => hq (he ▸ hw)
    · apply appendCompiled_wellFormed
      · exact gidneyProgram_wellFormed _ _ _ _ _ q c r t htake (by simp) hl.1
      · apply appendCompiled_wellFormed
        · exact gidneyProgram_wellFormed _ _ _ _ _ f c r t htake hk.symm hl.2.1
        · exact compareGEProgram_wellFormed _ _ target dirty 1 q c r t f hd hnd

theorem negativeNegateProgram_wellFormed (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    (negativeNegateProgram n start target dirty modulus q c r t f).2.WellFormed :=
  prependCompiled_wellFormed _ _ (by simp [CircuitWellFormed,Gate.WellFormed])
    (appendCompiled_wellFormed _ _ (modularNegateProgram_wellFormed n start target dirty modulus q c r t f hk hd hn hnd)
      (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])))

theorem yNegateProgram_wellFormed (start : Nat) : (yNegateProgram start).2.WellFormed :=
  negativeNegateProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp [constantBits_length])
    (by simp) (by simp) (by decide +kernel)

theorem sharedYNegateProgram_wellFormed (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).2.WellFormed :=
  (reindexCompiled_wellFormed (windowIndex w) (yNegateProgram start)).mpr (yNegateProgram_wellFormed start)

attribute [local irreducible] modularNegateProgram

theorem xNegateProgram_wellFormed (n start : Nat) : (xNegateProgram n start).2.WellFormed := by
  unfold xNegateProgram
  apply modularNegateProgram_wellFormed n start (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558 (by simp [constantBits_length]) (by simp) (by simp)
  rw [List.nodup_append,List.nodup_append]
  refine ⟨⟨by decide,by exact List.nodup_range',?_⟩,by exact List.nodup_range',?_⟩
  · intro a ha b hb he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    simp only [List.mem_range'_1] at hb
    dsimp only [Wire] at *
    omega
  · intro a ha b hb he
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at ha
    simp only [List.mem_range'_1] at hb
    dsimp only [Wire] at *
    omega
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ModularPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ModularPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem constantStraight_wellFormed {n s e : Nat} (q : Wire) (p : Straight n s e)
    (h : p.WellFormed) : (constantStraight q p).WellFormed := by
  have ht (g : TemplateGate n) (hg : g.WellFormed) : (constantTemplateGate q g).WellFormed := by
    cases g <;> exact constantControlGate_wellFormed q _ hg
  induction p with
  | done => trivial
  | gate g p ih => exact ⟨ht g h.1,ih h.2⟩
  | recordGate i v g p ih => exact ⟨constantControlGate_wellFormed q g h.1,ih h.2⟩
  | measure w p ih => exact ih h

theorem uncontrolledCompareProgram_wellFormed (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (hd : input.length=dirty.length)
    (hnd : ([c,r,t,f]++input++dirty).Nodup) :
    (uncontrolledCompareProgram n start input dirty threshold c r t f).2.WellFormed := by
  apply constantStraight_wellFormed
  apply compareGEProgram_wellFormed _ _ _ _ _ _ _ _ _ _ hd
  change (gidneyCompareVirtualControl input dirty c r t f :: ([c,r,t,f]++input++dirty)).Nodup
  refine List.nodup_cons.mpr ⟨?_,hnd⟩
  intro hm
  have hh : ([c,r,t,f]++input++dirty).sum+1 ≤ ([c,r,t,f]++input++dirty).sum := List.le_sum_of_mem hm
  exact (Nat.not_succ_le_self _) hh

attribute [local irreducible] uncontrolledCompareProgram gidneyProgram

theorem modularAddProgram_wellFormed (n start : Nat) (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=correction.length) (hnd : ([q,c,r,t,f]++input++acc).Nodup) :
    (modularAddProgram n start input acc correction p q c r t f).2.WellFormed := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length=(input.take (acc.length-1)).length+1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold modularAddProgram
  apply straight_append_wellFormed
  · exact literalProgram_wellFormed _ (controlledAddCarry_wellFormed input acc q c f hlen hl.1)
  · apply appendCompiled_wellFormed
    · exact uncontrolledCompareProgram_wellFormed _ _ acc input p c r t f hlen.symm hl.2.1
    · apply straight_append_wellFormed
      · exact gidneyProgram_wellFormed _ _ acc _ correction f c r t hd hk.symm hl.2.2.1
      · exact literalProgram_wellFormed _ (controlledCompareLT_wellFormed acc input q c f hlen.symm hl.2.2.2)

theorem modularSubProgram_wellFormed (n start : Nat) (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=modulus.length) (hnd : ([q,c,r,t,f]++input++acc).Nodup) :
    (modularSubProgram n start input acc modulus p q c r t f).2.WellFormed := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length=(input.take (acc.length-1)).length+1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold modularSubProgram
  apply prependCompiled_wellFormed
  · exact controlledCompareLT_wellFormed acc input q c f hlen.symm hl.2.2.2
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ acc _ modulus f c r t hd hk.symm hl.2.2.1
    · apply appendCompiled_wellFormed
      · exact uncontrolledCompareProgram_wellFormed _ _ acc input p c r t f hlen.symm hl.2.1
      · apply literalProgram_wellFormed
        exact (circuitWellFormed_adjoint _).mpr (controlledAddCarry_wellFormed input acc q c f hlen hl.1)

theorem modularDoubleProgram_wellFormed (n start : Nat) (a : Wire) (rest dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a::rest).length=bits.length) (hd : (a::rest).length=dirty.length)
    (hnd : ([c,r,t,f]++(a::rest)++dirty).Nodup) :
    (modularDoubleProgram n start (a::rest) dirty bits p c r t f).2.WellFormed := by
  have hl := doubling_layout (a::rest) dirty c r t f hnd
  have htlen : (a::rest).length=(dirty.take rest.length).length+1 := by
    simp only [List.length_take,List.length_cons] at hd ⊢
    rw [Nat.min_eq_left (by omega)]
  have hshort : ([f,c,r,t]++(a::rest)++dirty.take rest.length).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t]++(a::rest))).append (List.take_sublist _ _)) hl.2
  unfold modularDoubleProgram
  apply prependCompiled_wellFormed
  · exact doublingShift_wellFormed a f rest hl.1
  · apply appendCompiled_wellFormed
    · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
    · apply appendCompiled_wellFormed
      · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ htlen hk.symm hshort
      · apply literalProgram_wellFormed
        have hfa : f≠a := fun he => (List.nodup_cons.mp hl.1).1 (by simp [he])
        simp [CircuitWellFormed,Gate.WellFormed,Ne.symm hfa]

theorem modularHalveProgram_wellFormed (n start : Nat) (a : Wire) (rest dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a::rest).length=bits.length) (hd : (a::rest).length=dirty.length)
    (hnd : ([c,r,t,f]++(a::rest)++dirty).Nodup) :
    (modularHalveProgram n start (a::rest) dirty bits p c r t f).2.WellFormed := by
  have hl := doubling_layout (a::rest) dirty c r t f hnd
  have htlen : (a::rest).length=(dirty.take rest.length).length+1 := by
    simp only [List.length_take,List.length_cons] at hd ⊢
    rw [Nat.min_eq_left (by omega)]
  have hshort : ([f,c,r,t]++(a::rest)++dirty.take rest.length).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t]++(a::rest))).append (List.take_sublist _ _)) hl.2
  unfold modularHalveProgram
  apply prependCompiled_wellFormed
  · have hfa : f≠a := fun he => (List.nodup_cons.mp hl.1).1 (by simp [he])
    simp [CircuitWellFormed,Gate.WellFormed,Ne.symm hfa]
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ htlen hk.symm hshort
    · apply appendCompiled_wellFormed
      · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
      · exact literalProgram_wellFormed _ ((circuitWellFormed_adjoint _).mpr (doublingShift_wellFormed a f rest hl.1))

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([c,r,t,f]++controls++input++(a::rest)).Nodup) :
    (hornerProgram n start controls input (a::rest) bits p c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [hornerProgram]
    apply appendCompiled_wellFormed
    · exact ih _ (horner_tail_layout q qs input (a::rest) c r t f hnd)
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(hornerProgram n start qs input (a::rest) bits p c r t f).1)
          (start+(hornerProgram n start qs input (a::rest) bits p c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · exact modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
          (horner_add_layout q qs input (a::rest) c r t f hnd)
      · apply appendCompiled_wellFormed
        · exact modularDoubleProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout (q::qs) input (a::rest) c r t f hnd)
        · exact modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
            (horner_add_layout q qs input (a::rest) c r t f hnd)

theorem hornerInverseProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([c,r,t,f]++controls++input++(a::rest)).Nodup) :
    (hornerInverseProgram n start controls input (a::rest) bits p c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [hornerInverseProgram]
    apply appendCompiled_wellFormed
    · exact modularSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
        (horner_add_layout q qs input (a::rest) c r t f hnd)
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(modularSubProgram n start input (a::rest) bits p q c r t f).1)
          (start+(modularSubProgram n start input (a::rest) bits p q c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · trivial
      · apply appendCompiled_wellFormed
        · exact modularHalveProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout (q::qs) input (a::rest) c r t f hnd)
        · exact ih _ (horner_tail_layout q qs input (a::rest) c r t f hnd)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEACenterPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEACenterPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] gidneyProgram uncontrolledCompareProgram

theorem constMinusProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hd : input.length=dirty.length+1) (hk : input.length=bits.length)
    (hnd : ([q,c,r,t]++input++dirty).Nodup) :
    (constMinusProgram n start input dirty bits q c r t).2.WellFormed := by
  unfold constMinusProgram
  apply prependCompiled_wellFormed
  · exact (controlledConstMinus_wellFormed input dirty bits q c r t hk hd hnd).1
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ hd (by simp) hnd
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hk.symm hnd

private theorem center_layout (input dirty : List Wire) (c r t iter : Wire)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup) :
    ([iter,c,r,t] ++ input ++ dirty.take (input.length - 1)).Nodup := by
  have hp : ([c,r,t,iter] ++ input ++ dirty).Perm ([iter,c,r,t] ++ input ++ dirty) :=
    ((show ([c,r,t] ++ [iter]).Perm ([iter] ++ [c,r,t]) from
      List.perm_append_comm).append_right input).append_right dirty
  exact (hp.nodup_iff.mp hnd).sublist
    ((List.Sublist.refl _).append (List.take_sublist _ _))

attribute [local irreducible] constMinusProgram

theorem eeaCenterProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length)
    (hk : input.length=bits.length) (hpos : 0 < input.length)
    (hnd : ([c,r,t,iter]++input++dirty).Nodup) :
    (eeaCenterProgram n start input dirty bits p c r t iter).2.WellFormed := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaCenterProgram
  apply appendCompiled_wellFormed
  · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
  · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ ht hk (center_layout input dirty c r t iter hnd)

theorem eeaUncenterProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length)
    (hk : input.length=bits.length) (hpos : 0 < input.length)
    (hnd : ([c,r,t,iter]++input++dirty).Nodup) :
    (eeaUncenterProgram n start input dirty bits p c r t iter).2.WellFormed := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaUncenterProgram
  apply appendCompiled_wellFormed
  · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ ht hk (center_layout input dirty c r t iter hnd)
  · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
theorem eeaParityProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (hd : input.length=dirty.length+1) (hk : input.length=bits.length)
    (hnd : ([iter,c,r,t]++input++dirty).Nodup) :
    (eeaParityProgram n start input dirty bits c r t iter).2.WellFormed := by
  unfold eeaParityProgram
  apply prependCompiled_wellFormed
  · simp [CircuitWellFormed,Gate.WellFormed]
  · apply appendCompiled_wellFormed
    · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hk hnd
    · exact literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])



theorem adaptive_seq_wellFormed_parts (first second : AdaptiveCircuit)
    (h : (first.seq second).WellFormed) : first.WellFormed ∧ second.WellFormed := by
  induction first with
  | done => exact ⟨trivial,h⟩
  | unitary gs next ih =>
    have hh := ih h.2
    exact ⟨⟨h.1,hh.1⟩,hh.2⟩
  | xMeasureReset w p q ihp ihq =>
    have hp := ihp h.1
    have hq := ihq h.2
    exact ⟨⟨hp.1,hq.1⟩,hp.2⟩

private theorem preprocessCenter_layout :
    ([560,561,562,2] ++ (List.range' 266 256).reverse ++ List.range' 4 256).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨by decide,
    by simpa using (List.nodup_range' (s := 266) (n := 256)), ?_⟩,
    List.nodup_range', ?_⟩
  · intro a ha b hb he
    simp at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  · intro a ha b hb he
    simp at ha hb
    rcases ha with ha | ha
    · rcases ha with rfl | rfl | rfl | rfl; omega
    · omega

private theorem parity_layout :
    ([2,560,561,562]++List.range' 263 256++List.range' 4 255).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

attribute [local irreducible] eeaCenterProgram eeaUncenterProgram eeaParityProgram
  eeaCenter eeaUncenter eeaLengthSetup eeaLengthUndo workRegistersPrepare workRegistersRestore

theorem preprocessProgram_wellFormed (n start : Nat) : (preprocessProgram n start).2.WellFormed := by
  unfold preprocessProgram
  apply surroundCompiled_wellFormed
  · exact workRegistersPrepare_resources.1
  · exact (adaptive_seq_wellFormed_parts (eeaCenter (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2) (.unitary eeaLengthSetup .done) eeaPreprocess_wellFormed.2).2.1
  · exact eeaCenterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) preprocessCenter_layout

theorem unpreprocessProgram_wellFormed (n start : Nat) : (unpreprocessProgram n start).2.WellFormed := by
  unfold unpreprocessProgram
  apply surroundCompiled_wellFormed
  · exact eeaUnpreprocess_wellFormed.1
  · exact workRegistersRestore_resources.1
  · exact eeaUncenterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) preprocessCenter_layout

theorem productionParityProgram_wellFormed (n start : Nat) : (productionParityProgram n start).2.WellFormed := by
  unfold productionParityProgram
  exact eeaParityProgram_wellFormed _ _ _ _ _ _ _ _ _ (by simp) (by simp [secp256k1ModulusBits]) parity_layout
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEAStructuralPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEAStructuralPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem vchainTailProgram_wellFormed (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat)
    (h : (mcxVChainTailAdaptive acc controls target scratch).WellFormed) :
    (vchainTailProgram n controls acc target scratch start).2.WellFormed := by
  induction controls generalizing acc scratch start with
  | nil => trivial
  | cons control controls ih =>
    cases controls with
    | nil => exact literalProgram_wellFormed _ h.1
    | cons next controls =>
      cases scratch with
      | nil => trivial
      | cons work scratch =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2
        apply prependCompiled_wellFormed
        · exact h.1
        · apply appendCompiled_wellFormed
          · exact ih work scratch start hs.1
          · apply andEraseProgram_wellFormed
            have hg := h.1 (.CCX control acc work) (by simp)
            exact hg.1

theorem vchainProgram_wellFormed (n start : Nat) (controls : List Wire) (target : Wire)
    (scratch : List Wire) (h : (mcxVChainAdaptive controls target scratch).WellFormed) :
    (vchainProgram n start controls target scratch).2.WellFormed := by
  cases controls with
  | nil => exact literalProgram_wellFormed _ h.1
  | cons first rest =>
    cases rest with
    | nil => exact literalProgram_wellFormed _ h.1
    | cons second rest => exact vchainTailProgram_wellFormed _ _ _ _ _ _ h

attribute [local irreducible] vchainProgram

theorem rippleMajProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledMajAdaptive control target addend carry scratch).WellFormed) :
    (rippleMajProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleMajProgram
  exact prependCompiled_wellFormed _ _ h.1 (vchainProgram_wellFormed _ _ _ _ _ h.2)

theorem rippleUmaInvProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledUmaInvAdaptive control target addend carry scratch).WellFormed) :
    (rippleUmaInvProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleUmaInvProgram
  exact prependCompiled_wellFormed _ _ h.1 (vchainProgram_wellFormed _ _ _ _ _ h.2)

theorem rippleUmaProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledUmaAdaptive control target addend carry scratch).WellFormed) :
    (rippleUmaProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleUmaProgram
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem rippleMajInvProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledMajInvAdaptive control target addend carry scratch).WellFormed) :
    (rippleMajInvProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleMajInvProgram
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem rippleFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (h : (rippleFirstCellAdaptive mode control target addend carry scratch).WellFormed) :
    (rippleFirstProgram n start mode control target addend carry scratch).2.WellFormed := by
  cases mode with
  | add => exact rippleMajProgram_wellFormed _ _ _ _ _ _ _ h
  | sub => exact rippleUmaInvProgram_wellFormed _ _ _ _ _ _ _ h

theorem rippleSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (h : (rippleSecondCellAdaptive mode control target addend carry scratch).WellFormed) :
    (rippleSecondProgram n start mode control target addend carry scratch).2.WellFormed := by
  cases mode with
  | add => exact rippleUmaProgram_wellFormed _ _ _ _ _ _ _ h
  | sub => exact rippleMajInvProgram_wellFormed _ _ _ _ _ _ _ h


theorem sequenceCircuit_wellFormed_members (sources : List AdaptiveCircuit)
    (h : (sequenceCircuit sources).WellFormed) : ∀ source ∈ sources, source.WellFormed := by
  induction sources with
  | nil => simp
  | cons source rest ih =>
    have hs := adaptive_seq_wellFormed_parts source (sequenceCircuit rest) h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hs.1
    · exact ih hs.2 c hc

theorem phaseSegments_wellFormed (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit)
    (h : (sequenceCircuit (phaseSources r shift core)).WellFormed) :
    ∀ seg ∈ phaseSegments n r shift core, ∀ start, (seg start).2.WellFormed := by
  have hs := sequenceCircuit_wellFormed_members _ h
  have ha := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthQ (r.withShiftEpoch shift).zeroQ (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hb := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthRPrime (r.withShiftEpoch shift).zeroRPrime (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hc := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthS (r.withShiftEpoch shift).zeroS (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hg := (hs (.unitary core .done) (by simp [phaseSources])).1
  intro seg hm start
  simp only [phaseSegments,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact vchainProgram_wellFormed _ _ _ _ _ ha
    | exact vchainProgram_wellFormed _ _ _ _ _ hb
    | exact vchainProgram_wellFormed _ _ _ _ _ hc
    | exact literalProgram_wellFormed _ hg
    | exact literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])

theorem phaseProgram_wellFormed (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (h : (phaseUpdateEpochAdaptive r shift).WellFormed) : (phaseProgram n start r shift).2.WellFormed := by
  apply sequenceProgram_wellFormed
  apply phaseSegments_wellFormed
  rwa [phaseSources_forward]

theorem phaseInverseProgram_wellFormed (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (h : (phaseUpdateEpochInverseAdaptive r shift).WellFormed) : (phaseInverseProgram n start r shift).2.WellFormed := by
  apply sequenceProgram_wellFormed
  apply phaseSegments_wellFormed
  rwa [phaseSources_inverse]


theorem zeroEraseProgram_wellFormed (n start : Nat) (a b w : Wire) (hab : a ≠ b) :
    (zeroEraseProgram n start a b w).2.WellFormed := by
  apply prependCompiled_wellFormed
  · simp [CircuitWellFormed,Gate.WellFormed]
  · exact appendCompiled_wellFormed _ _ (andEraseProgram_wellFormed _ _ _ _ _ hab)
      (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed]))

theorem unaryProgram_wellFormed (n : Nat) (order : UnaryOrder)
    (leaf : Nat → Wire → (start : Nat) → (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → AdaptiveCircuit)
    (hleaf : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (h : (unaryAdaptiveAction order source tree control paths).WellFormed) :
    (unaryProgram n order leaf tree control paths start).2.WellFormed := by
  let WF := fun (start : Nat) (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF start _
  induction tree generalizing control paths start with
  | leaf label =>
    simp only [unaryProgram]
    exact hleaf label control start h
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp only [unaryProgram]; trivial
    | cons path rest =>
      cases order with
      | inc =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2
        have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
        have hab := (h.1 (.CCX control bit path) (by simp [computeZeroAnd])).1
        simp only [unaryProgram]
        apply prependCompiled_wellFormed _ _ h.1
        apply appendCompiled_wellFormed _ _ (ihz _ _ _ hs.1)
        apply prependCompiled_wellFormed _ _ hs.2.1
        apply appendCompiled_wellFormed _ _ (iho _ _ _ ht.1)
        exact prependCompiled_wellFormed _ _ ht.2.1 (zeroEraseProgram_wellFormed _ _ _ _ _ hab)
      | dec =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2.2
        have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
        have hab := (h.1 (.CCX control bit path) (by simp [computeZeroAnd])).1
        simp only [unaryProgram]
        apply prependCompiled_wellFormed _ _ h.1
        apply prependCompiled_wellFormed _ _ h.2.1
        apply appendCompiled_wellFormed _ _ (iho _ _ _ hs.1)
        apply prependCompiled_wellFormed _ _ hs.2.1
        exact appendCompiled_wellFormed _ _ (ihz _ _ _ ht.1) (zeroEraseProgram_wellFormed _ _ _ _ _ hab)


attribute [local irreducible] rippleFirstProgram rippleSecondProgram

theorem coefficientFirstProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (h : (coefficientPrefixFirstLeafAdaptive r k K mode target label control).WellFormed) :
    (coefficientFirstProgram n start r k K mode target label control).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem coefficientSecondProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (h : (coefficientPrefixSecondLeafAdaptive r k K mode target label control).WellFormed) :
    (coefficientSecondProgram n start r k K mode target label control).2.WellFormed :=
  prependCompiled_wellFormed _ _ h.1 (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ h.2)

attribute [local irreducible] coefficientFirstProgram coefficientSecondProgram

theorem coefficientProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (h : (coefficientPrefixAdaptive r k K mode signUpdate target).WellFormed) :
    (coefficientProgram n start r k K mode signUpdate target).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
  unfold coefficientProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact unaryProgram_wellFormed _ _ _ _
      (fun label control cursor h => coefficientFirstProgram_wellFormed n cursor r k K mode target label control h) _ _ _ _ hs.1
  · apply prependCompiled_wellFormed _ _ hs.2.1
    apply appendCompiled_wellFormed
    · exact unaryProgram_wellFormed _ _ _ _
        (fun label control cursor h => coefficientSecondProgram_wellFormed n cursor r k K mode target label control h) _ _ _ _ ht.1
    · exact literalProgram_wellFormed _ ht.2.1

theorem coefficientInverseProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (h : (coefficientPrefixInverseAdaptive r k K mode signUpdate target).WellFormed) :
    (coefficientInverseProgram n start r k K mode signUpdate target).2.WellFormed :=
  coefficientProgram_wellFormed _ _ _ _ _ _ _ _ h
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEAIntervalPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEAIntervalPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

/-! Structural preservation of gate validity. Generic lemmas assume validity of the source gates;
production wrapper lemmas discharge that premise using the fixed source layouts. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] terminalWork1Clear

theorem dualEraseProgram_wellFormed (n start : Nat) (a i x b j y : Wire) (ha : a ≠ i) (hb : b ≠ j) :
    (dualEraseProgram n start a i x b j y).2.WellFormed :=
  appendCompiled_wellFormed _ _ (zeroEraseProgram_wellFormed _ _ _ _ _ hb)
    (zeroEraseProgram_wellFormed _ _ _ _ _ ha)

theorem dualProgram_wellFormed (n : Nat) (order : UnaryOrder)
    (leaf : Nat → Wire → Wire → (start : Nat) → (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → Wire → AdaptiveCircuit)
    (hleaf : ∀ label a b start, (source label a b).WellFormed → (leaf label a b start).2.WellFormed)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat)
    (h : (dualUnaryAdaptiveAction order source tree a b xs ys).WellFormed) :
    (dualProgram n order leaf tree a b xs ys start).2.WellFormed := by
  let WF := fun (start : Nat) (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF start _
  induction tree generalizing a b xs ys start with
  | leaf label => simp only [dualProgram]; exact hleaf label a b start h
  | node i j zero one ihz iho =>
    cases xs with
    | nil => simp only [dualProgram]; trivial
    | cons x xs =>
      cases ys with
      | nil => simp only [dualProgram]; trivial
      | cons y ys =>
        cases order with
        | inc =>
          have hs := adaptive_seq_wellFormed_parts _ _ h.2.2
          have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
          have ha := (h.1 (.CCX a i x) (by simp [computeZeroAnd])).1
          have hb := (h.2.1 (.CCX b j y) (by simp [computeZeroAnd])).1
          simp only [dualProgram]
          apply prependCompiled_wellFormed _ _ h.1
          apply prependCompiled_wellFormed _ _ h.2.1
          apply appendCompiled_wellFormed _ _ (ihz _ _ _ _ _ hs.1)
          apply prependCompiled_wellFormed _ _ hs.2.1
          apply appendCompiled_wellFormed _ _ (iho _ _ _ _ _ ht.1)
          exact prependCompiled_wellFormed _ _ ht.2.1 (dualEraseProgram_wellFormed _ _ _ _ _ _ _ _ ha hb)
        | dec =>
          have hs := adaptive_seq_wellFormed_parts _ _ h.2.2.2
          have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
          have ha := (h.1 (.CCX a i x) (by simp [computeZeroAnd])).1
          have hb := (h.2.1 (.CCX b j y) (by simp [computeZeroAnd])).1
          simp only [dualProgram]
          apply prependCompiled_wellFormed _ _ h.1
          apply prependCompiled_wellFormed _ _ h.2.1
          apply prependCompiled_wellFormed _ _ h.2.2.1
          apply appendCompiled_wellFormed _ _ (iho _ _ _ _ _ hs.1)
          apply prependCompiled_wellFormed _ _ hs.2.1
          exact appendCompiled_wellFormed _ _ (ihz _ _ _ _ _ ht.1) (dualEraseProgram_wellFormed _ _ _ _ _ _ _ _ ha hb)


theorem equalityProgram_wellFormed (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire)
    (h : (computeEqConstAdaptive register value flag scratch).WellFormed) :
    (equalityProgram n start register value flag scratch).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem toggleEqualityProgram_wellFormed (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire)
    (h : (toggleEqConstUnderControlAdaptive root register value acc flag scratch).WellFormed) :
    (toggleEqualityProgram n start root register value acc flag scratch).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (equalityProgram_wellFormed _ _ _ _ _ _ hs.1)
    (prependCompiled_wellFormed _ _ hs.2.1 (equalityProgram_wellFormed _ _ _ _ _ _ hs.2.2))

theorem intervalFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire)
    (h : (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).WellFormed) :
    (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem intervalSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire)
    (h : (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).WellFormed) :
    (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem topFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (h : (topSpecialFirstLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).WellFormed) :
    (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  exact appendCompiled_wellFormed _ _ (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ ht.1)
      (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ ht.2))

theorem topSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (h : (topSpecialSecondLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).WellFormed) :
    (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  exact appendCompiled_wellFormed _ _ (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ ht.1)
      (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ ht.2))


theorem traversalFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (h : (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).WellFormed) :
    (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.WellFormed := by
  unfold traversalFirstProgram
  apply dualProgram_wellFormed _ _ _ _ ?_ _ _ _ _ _ _ h
  intro label right left cursor hh
  exact intervalFirstProgram_wellFormed n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left hh

theorem traversalSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (h : (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).WellFormed) :
    (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.WellFormed := by
  unfold traversalSecondProgram
  apply dualProgram_wellFormed _ _ _ _ ?_ _ _ _ _ _ _ h
  intro label right left cursor hh
  exact intervalSecondProgram_wellFormed n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left hh


theorem intervalTopFirstProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (h : (if intervalHasTopSpecial k K then topSpecialFirstLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).WellFormed) :
    (intervalTopFirstProgram n start r k K mode target).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold intervalTopFirstProgram
  split
  · rename_i he
    simp only [he,ite_true] at h
    exact topFirstProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · trivial

theorem intervalTopSecondProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (h : (if intervalHasTopSpecial k K then topSpecialSecondLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).WellFormed) :
    (intervalTopSecondProgram n start r k K mode target).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold intervalTopSecondProgram
  split
  · rename_i he
    simp only [he,ite_true] at h
    exact topSecondProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · trivial

attribute [local irreducible] intervalTopFirstProgram intervalTopSecondProgram traversalFirstProgram traversalSecondProgram

theorem intervalProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : (intervalAddSub r width k K mode signUpdate target).WellFormed) :
    (intervalProgram n start r width k K mode signUpdate target).2.WellFormed := by
  have h0 := adaptive_seq_wellFormed_parts _ _ h
  have h1 := adaptive_seq_wellFormed_parts _ _ h0.2
  have h2 := adaptive_seq_wellFormed_parts _ _ h1.2
  have h3 := adaptive_seq_wellFormed_parts _ _ h2.2
  have h4 := adaptive_seq_wellFormed_parts _ _ h3.2
  have h5 := adaptive_seq_wellFormed_parts _ _ h4.2
  unfold intervalProgram
  apply prependCompiled_wellFormed _ _ h0.1.1
  apply appendCompiled_wellFormed _ _ (intervalTopFirstProgram_wellFormed _ _ _ _ _ _ _ h1.1)
  apply appendCompiled_wellFormed
  · exact traversalFirstProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2.1
  · apply prependCompiled_wellFormed _ _ h3.1.1
    apply appendCompiled_wellFormed
    · exact traversalSecondProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h4.1
    · exact appendCompiled_wellFormed _ _ (intervalTopSecondProgram_wellFormed _ _ _ _ _ _ _ h5.1)
        (literalProgram_wellFormed _ h5.2.1)


theorem intervalInverseProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : (intervalAddSubInverse r width k K mode signUpdate target).WellFormed) :
    (intervalInverseProgram n start r width k K mode signUpdate target).2.WellFormed :=
  intervalProgram_wellFormed _ _ _ _ _ _ _ _ _ h

theorem sequenceProgram_wellFormed_of_source (n start : Nat) (ps : List (FixedSegment n)) (sources : List AdaptiveCircuit)
    (h : (sequenceCircuit sources).WellFormed)
    (hp : List.Forall₂ (fun p source => ∀ start, source.WellFormed → (p start).2.WellFormed) ps sources) :
    (sequenceProgram n ps start).2.WellFormed := by
  induction hp generalizing start with
  | nil => trivial
  | @cons p source ps sources hp hps ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (hp _ hs.1) (ih _ hs.2)

attribute [local irreducible] intervalProgram intervalInverseProgram coefficientProgram coefficientInverseProgram
  phaseProgram phaseInverseProgram intervalAddSub intervalAddSubInverse coefficientPrefixAdaptive coefficientPrefixInverseAdaptive
  phaseUpdateEpochAdaptive phaseUpdateEpochInverseAdaptive

theorem remainderBlockProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (h : (blockBAdaptive r width w).WellFormed) :
    (remainderBlockProgram n start r width w).2.WellFormed := by
  unfold remainderBlockProgram
  rw [← remainderBlockSources_eq r width w] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold remainderBlockSegments remainderBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalProgram_wellFormed n cursor (r.remainder w) width w.start w.stop .sub true .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalProgram_wellFormed n cursor (r.remainder w) width w.start w.stop .add false .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem coefficientBlockProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (h : (blockEAdaptive r width w).WellFormed) :
    (coefficientBlockProgram n start r width w).2.WellFormed := by
  unfold coefficientBlockProgram
  rw [← coefficientBlockSources_eq r width w] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold coefficientBlockSegments coefficientBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientProgram_wellFormed n cursor (r.coefficient w) w.start w.stop .sub false .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientProgram_wellFormed n cursor (r.coefficient w) w.start w.stop .add true .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram blockBAdaptive blockEAdaptive

theorem indexedStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (indexedStepAdaptive r width T).WellFormed) :
    (indexedStepProgram n start r width T).2.WellFormed := by
  unfold indexedStepProgram
  rw [← indexedStepSources_eq r width T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold indexedStepSegments indexedStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact remainderBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).remainder hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).coefficient hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact phaseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem indexedInverseStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (h : (indexedStepInverseAdaptive r 256 T).WellFormed) :
    (indexedInverseStepProgram n start r T).2.WellFormed := by
  unfold indexedInverseStepProgram
  rw [← indexedInverseStepSources_eq r T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold indexedInverseStepSegments indexedInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact phaseInverseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1


attribute [local irreducible] indexedStepProgram indexedInverseStepProgram indexedStepAdaptive indexedStepInverseAdaptive

theorem scheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (width count first start : Nat)
    (h : (indexedScheduleAdaptive r width first count).WellFormed) :
    (scheduleProgram n r width count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (indexedStepProgram_wellFormed _ _ _ _ _ hs.1)
      (ih _ _ hs.2)

theorem inverseScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (h : (indexedScheduleInverseAdaptive r 256 first count).WellFormed) :
    (inverseScheduleProgram n r count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (ih _ _ hs.1)
      (indexedInverseStepProgram_wellFormed _ _ _ _ hs.2)

attribute [local irreducible] scheduleProgram inverseScheduleProgram indexedScheduleAdaptive indexedScheduleInverseAdaptive

theorem eeaForwardProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1EEAForwardAdaptive r).WellFormed) : (eeaForwardProgram n start r).2.WellFormed :=
  scheduleProgram_wellFormed _ _ _ _ _ _ h

theorem eeaReverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1EEAReverseAdaptive r).WellFormed) : (eeaReverseProgram n start r).2.WellFormed :=
  inverseScheduleProgram_wellFormed _ _ _ _ _ h


attribute [local irreducible] eeaForwardProgram eeaReverseProgram preprocessProgram unpreprocessProgram productionParityProgram
  secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection

theorem forwardWrapperProgram_wellFormed (n start : Nat) : (forwardWrapperProgram n start).2.WellFormed := by
  have h := secp256k1EEAForwardWrapper_wellFormed
  unfold forwardWrapperProgram
  rw [← forwardWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold forwardWrapperSegments forwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact preprocessProgram_wellFormed n cursor
  · intro cursor hh
    exact eeaForwardProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem reverseWrapperProgram_wellFormed (n start : Nat) : (reverseWrapperProgram n start).2.WellFormed := by
  have h := secp256k1EEAReverseWrapper_wellFormed
  unfold reverseWrapperProgram
  rw [← reverseWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold reverseWrapperSegments reverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact eeaReverseProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact unpreprocessProgram_wellFormed n cursor
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/MeasuredEEAPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/MeasuredEEAPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

/-! Structural preservation of gate validity. Generic lemmas assume validity of the source gates;
production wrapper lemmas discharge that premise using the fixed source layouts. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] terminalWork1Clear

theorem zeroCellProgram_wellFormed (n start : Nat) (base : Bool) (r bit guard target temporary : Wire)
    (h : (measuredZeroCell base r bit guard target temporary).WellFormed) :
    (zeroCellProgram n start base r bit guard target temporary).2.WellFormed := by
  apply prependCompiled_wellFormed _ _ h.1
  exact andEraseProgram_wellFormed _ _ _ _ _
    (h.1 (.CCX r bit temporary) (by simp [measuredZeroPrefix])).1

theorem upperForwardLeafProgram_wellFormed (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label r).WellFormed) :
    (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold upperForwardLeafProgram
  unfold measuredUpperForwardLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · split <;> rename_i hd <;> (first | rw [if_pos hd] at h | rw [if_neg hd] at h)
    all_goals exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem upperReverseLeafProgram_wellFormed (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label r).WellFormed) :
    (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold upperReverseLeafProgram
  unfold measuredUpperReverseLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem lowerForwardLeafProgram_wellFormed (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label r).WellFormed) :
    (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold lowerForwardLeafProgram
  unfold measuredLowerForwardLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · split <;> rename_i hd <;> (first | rw [if_pos hd] at h | rw [if_neg hd] at h)
    all_goals exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem lowerReverseLeafProgram_wellFormed (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label r).WellFormed) :
    (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold lowerReverseLeafProgram
  unfold measuredLowerReverseLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem rangeLeafProgram_wellFormed (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (hl : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (label : Nat) (dynamic : Wire) (start : Nat)
    (h : (measuredRangeLeaf after r source label dynamic).WellFormed) :
    (rangeLeafProgram n after r leaf label dynamic start).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold rangeLeafProgram
  unfold measuredRangeLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (hl _ _ _ hs.1) (literalProgram_wellFormed _ hs.2.1)
  · exact prependCompiled_wellFormed _ _ h.1 (hl _ _ _ h.2)

theorem rangeScanProgram_wellFormed (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (hl : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (start : Nat) (h : (measuredRangeScan after order tree control r path source).WellFormed) :
    (rangeScanProgram n after order tree control r path leaf start).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold rangeScanProgram
  unfold measuredRangeScan at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · apply prependCompiled_wellFormed _ _ h.1
    exact unaryProgram_wellFormed n order _ _ (rangeLeafProgram_wellFormed n true r leaf source hl) tree control path start h.2
  · have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _
      (unaryProgram_wellFormed n order _ _ (rangeLeafProgram_wellFormed n false r leaf source hl) tree control path start hs.1)
      (literalProgram_wellFormed _ hs.2.1)

theorem upperMapProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (h : (measuredUpperZeroMap k K tree control r t path bitAt dirtyAt).WellFormed) :
    (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  unfold upperMapProgram
  apply appendCompiled_wellFormed
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => upperForwardLeafProgram_wellFormed n cursor k K control t bitAt dirtyAt label dynamic hh) _ hs.1
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => upperReverseLeafProgram_wellFormed n cursor k K t bitAt dirtyAt label dynamic hh) _ hs.2

theorem lowerMapProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (h : (measuredLowerZeroMap k K tree control r t path bitAt dirtyAt).WellFormed) :
    (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  unfold lowerMapProgram
  apply appendCompiled_wellFormed
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => lowerForwardLeafProgram_wellFormed n cursor k K control t bitAt dirtyAt label dynamic hh) _ hs.1
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => lowerReverseLeafProgram_wellFormed n cursor k K t bitAt dirtyAt label dynamic hh) _ hs.2

theorem upperWriterProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (h : (measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets).WellFormed) :
    (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2.WellFormed := by
  unfold measuredHighestPositionWrite at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold upperWriterProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact upperMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.1
  · exact prependCompiled_wellFormed _ _ hs.2.1 (upperMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.2.2)

theorem lowerWriterProgram_wellFormed (n : Nat) (width : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (h : (measuredRightLengthWrite width k K tree control r t path bitAt dirtyAt targets).WellFormed) :
    (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2.WellFormed := by
  unfold measuredRightLengthWrite at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold lowerWriterProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact lowerMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.1
  · exact prependCompiled_wellFormed _ _ hs.2.1 (lowerMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.2.2)

theorem ltUpdateProgram_wellFormed (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (h : (measuredLenUpdateLtUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).WellFormed) :
    (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.WellFormed := by
  unfold measuredLenUpdateLtUnary at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold ltUpdateProgram
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  apply surroundCompiled_wellFormed _ _ _ h.1 ht.2.1
  exact appendCompiled_wellFormed _ _ (upperWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hs.1)
    (upperWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ ht.1)

theorem lrpUpdateProgram_wellFormed (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (h : (measuredLenUpdateLrpUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).WellFormed) :
    (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.WellFormed := by
  unfold measuredLenUpdateLrpUnary at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold lrpUpdateProgram
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  apply surroundCompiled_wellFormed _ _ _ h.1 ht.2.1
  exact appendCompiled_wellFormed _ _ (lowerWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hs.1)
    (lowerWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ ht.1)

theorem upperEndProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndUpper r width w).WellFormed) :
    (upperEndProgram n start r width w).2.WellFormed := by
  exact ltUpdateProgram_wellFormed n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start h

theorem lowerEndProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndLower r width w).WellFormed) :
    (lowerEndProgram n start r width w).2.WellFormed := by
  exact lrpUpdateProgram_wellFormed n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start h

theorem endProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndIteration r width w).WellFormed) :
    (endProgram n start r width w).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold endProgram
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (upperEndProgram_wellFormed _ _ _ _ _ hs.1)
      (lowerEndProgram_wellFormed _ _ _ _ _ hs.2))

theorem endInverseProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndIterationInverse r width w).WellFormed) :
    (endInverseProgram n start r width w).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  unfold endInverseProgram
  exact appendCompiled_wellFormed _ _ (lowerEndProgram_wellFormed _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (upperEndProgram_wellFormed _ _ _ _ _ ht.1)
      (literalProgram_wellFormed _ ht.2.1))

theorem hProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredBlockHForward r width T).WellFormed) :
    (hProgram n start r width T).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold hProgram
  unfold measuredBlockHForward at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h.2
    exact surroundCompiled_wellFormed _ _ _ h.1 hs.2.1 (endProgram_wellFormed _ _ _ _ _ hs.1)
  · trivial

theorem hInverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredBlockHInverse r width T).WellFormed) :
    (hInverseProgram n start r width T).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold hInverseProgram
  unfold measuredBlockHInverse at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h.2
    exact surroundCompiled_wellFormed _ _ _ h.1 hs.2.1 (endInverseProgram_wellFormed _ _ _ _ _ hs.1)
  · trivial

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram
theorem measuredStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredIndexedStep r width T).WellFormed) :
    (measuredStepProgram n start r width T).2.WellFormed := by
  unfold measuredStepProgram
  rw [← measuredStepSources_eq r width T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredStepSegments measuredStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact remainderBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).remainder hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).coefficient hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact phaseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact hProgram_wellFormed n cursor r width T hh

theorem measuredInverseStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (h : (measuredIndexedStepInverse r 256 T).WellFormed) :
    (measuredInverseStepProgram n start r T).2.WellFormed := by
  unfold measuredInverseStepProgram
  rw [← measuredInverseStepSources_eq r T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredInverseStepSegments measuredInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor hh
    exact hInverseProgram_wellFormed n cursor r 256 T hh
  · intro cursor hh
    exact phaseInverseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

attribute [local irreducible] measuredStepProgram measuredInverseStepProgram measuredIndexedStep measuredIndexedStepInverse

theorem measuredScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (width count first start : Nat)
    (h : (measuredIndexedSchedule r width first count).WellFormed) :
    (measuredScheduleProgram n r width count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (measuredStepProgram_wellFormed _ _ _ _ _ hs.1)
      (ih _ _ hs.2)

theorem measuredInverseScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (h : (measuredIndexedScheduleInverse r 256 first count).WellFormed) :
    (measuredInverseScheduleProgram n r count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (ih _ _ hs.1)
      (measuredInverseStepProgram_wellFormed _ _ _ _ hs.2)

attribute [local irreducible] measuredScheduleProgram measuredInverseScheduleProgram measuredIndexedSchedule measuredIndexedScheduleInverse

theorem measuredEEAForwardProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1MeasuredEEAForward r).WellFormed) : (measuredEEAForwardProgram n start r).2.WellFormed :=
  measuredScheduleProgram_wellFormed _ _ _ _ _ _ h

theorem measuredEEAReverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1MeasuredEEAReverse r).WellFormed) : (measuredEEAReverseProgram n start r).2.WellFormed :=
  measuredInverseScheduleProgram_wellFormed _ _ _ _ _ h


attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram preprocessProgram unpreprocessProgram productionParityProgram
  secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection

theorem measuredForwardWrapperProgram_wellFormed (n start : Nat) : (measuredForwardWrapperProgram n start).2.WellFormed := by
  have h := secp256k1MeasuredEEAForwardWrapper_wellFormed
  unfold measuredForwardWrapperProgram
  rw [← measuredForwardWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredForwardWrapperSegments measuredForwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact preprocessProgram_wellFormed n cursor
  · intro cursor hh
    exact measuredEEAForwardProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem measuredReverseWrapperProgram_wellFormed (n start : Nat) : (measuredReverseWrapperProgram n start).2.WellFormed := by
  have h := secp256k1MeasuredEEAReverseWrapper_wellFormed
  unfold measuredReverseWrapperProgram
  rw [← measuredReverseWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredReverseWrapperSegments measuredReverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact measuredEEAReverseProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact unpreprocessProgram_wellFormed n cursor
theorem measuredForwardDataBankProgram_wellFormed (n start : Nat) :
    (measuredForwardDataBankProgram n start).2.WellFormed :=
  (relabelCompiled_wellFormed eeaWorkspaceExchange _).2 (measuredForwardWrapperProgram_wellFormed n start)

theorem measuredReverseDataBankProgram_wellFormed (n start : Nat) :
    (measuredReverseDataBankProgram n start).2.WellFormed :=
  (relabelCompiled_wellFormed eeaWorkspaceExchange _).2 (measuredReverseWrapperProgram_wellFormed n start)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/SquarePhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/SquarePhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem squareAddProgram_wellFormed (n start : Nat) (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=bits.length) (hnd : ([copied,c,r,t,f]++input++acc).Nodup)
    (hq : q∈input) : (squareAddProgram n start input acc bits p q copied c r t f).2.WellFormed := by
  have hqc : q≠copied := by
    intro he
    exact (List.nodup_cons.mp hnd).1 (by simp [← he,hq])
  have hg : CircuitWellFormed [.CX q copied] := by simp [CircuitWellFormed,Gate.WellFormed,hqc]
  exact prependCompiled_wellFormed _ _ hg
    (appendCompiled_wellFormed _ _
      (modularAddProgram_wellFormed n start input acc bits p copied c r t f hlen hne hk hnd)
      (literalProgram_wellFormed _ hg))

theorem squareSubProgram_wellFormed (n start : Nat) (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=bits.length) (hnd : ([copied,c,r,t,f]++input++acc).Nodup)
    (hq : q∈input) : (squareSubProgram n start input acc bits p q copied c r t f).2.WellFormed := by
  have hqc : q≠copied := by
    intro he
    exact (List.nodup_cons.mp hnd).1 (by simp [← he,hq])
  have hg : CircuitWellFormed [.CX q copied] := by simp [CircuitWellFormed,Gate.WellFormed,hqc]
  exact prependCompiled_wellFormed _ _ hg
    (appendCompiled_wellFormed _ _
      (modularSubProgram_wellFormed n start input acc bits p copied c r t f hlen hne hk hnd)
      (literalProgram_wellFormed _ hg))

attribute [local irreducible] squareAddProgram squareSubProgram

theorem squareProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcontrols : ∀ q∈controls,q∈input) :
    (squareProgram n start controls input (a::rest) bits p copied c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [squareProgram]
    apply appendCompiled_wellFormed
    · exact ih _ (fun z hz => hcontrols z (List.mem_cons_of_mem q hz))
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(squareProgram n start qs input (a::rest) bits p copied c r t f).1)
          (start+(squareProgram n start qs input (a::rest) bits p copied c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · exact squareAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
          hnd (hcontrols q (by simp))
      · apply appendCompiled_wellFormed
        · exact modularDoubleProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout [] input (a::rest) c r t f (List.nodup_cons.mp hnd).2)
        · exact squareAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
            hnd (hcontrols q (by simp))

theorem squareInverseProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcontrols : ∀ q∈controls,q∈input) :
    (squareInverseProgram n start controls input (a::rest) bits p copied c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [squareInverseProgram]
    apply appendCompiled_wellFormed
    · exact squareSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
        hnd (hcontrols q (by simp))
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(squareSubProgram n start input (a::rest) bits p q copied c r t f).1)
          (start+(squareSubProgram n start input (a::rest) bits p q copied c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · trivial
      · apply appendCompiled_wellFormed
        · exact modularHalveProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout [] input (a::rest) c r t f (List.nodup_cons.mp hnd).2)
        · exact ih _ (fun z hz => hcontrols z (List.mem_cons_of_mem q hz))
attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_wellFormed (n start : Nat) (x y : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire)
    (hxlen : x.length=(a::rest).length) (hylen : y.length=(a::rest).length)
    (hk : (a::rest).length=correction.length) (hm : (a::rest).length=modulus.length)
    (hsq : ([copied,c,r,t,f]++y++(a::rest)).Nodup)
    (hsub : ([q,copied,f,r,c]++(a::rest)++x).Nodup) :
    (squareSubtractProgram n start x y (a::rest) correction modulus p q copied c r t f).2.WellFormed := by
  unfold squareSubtractProgram
  apply appendCompiled_wellFormed
  · exact squareProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hylen hk hsq (fun _ h => h)
  · apply appendCompiled_wellFormed
    · exact modularSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hxlen.symm
        (by rw [hxlen]; simp) (hxlen.trans hm) hsub
    · exact squareInverseProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hylen hm hsq (fun _ h => h)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/InPlacePhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/InPlacePhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem figure15_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 580 256 ++ List.range' 7 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

private theorem figure15_data_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 7 256 ++ List.range' 580 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega


attribute [local irreducible] hornerProgram hornerInverseProgram

theorem multiplyWorkProgram_wellFormed (n start : Nat) : (multiplyWorkProgram n start).2.WellFormed := by
  have ha : List.range' 7 256 = 7 :: List.range' 8 255 := rfl
  unfold multiplyWorkProgram
  rw [ha]
  apply hornerProgram_wellFormed
  · simp
  · simp [secp256k1ReductionConstantBits]
  · rw [← ha]; exact figure15_layout

theorem multiplyDataProgram_wellFormed (n start : Nat) : (multiplyDataProgram n start).2.WellFormed := by
  have ha : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold multiplyDataProgram
  rw [ha]
  apply hornerProgram_wellFormed
  · simp
  · simp [secp256k1ReductionConstantBits]
  · rw [← ha]; exact figure15_data_layout

theorem unmultiplyDataProgram_wellFormed (n start : Nat) : (unmultiplyDataProgram n start).2.WellFormed := by
  have ha : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold unmultiplyDataProgram
  rw [ha]
  apply hornerInverseProgram_wellFormed
  · simp
  · simp only [List.length_cons, List.length_range', constantBits_length]
  · rw [← ha]; exact figure15_data_layout
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/InPlaceCompletePhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/InPlaceCompletePhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem correctionCompiled_wellFormed (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    (correctionCompiled n start ws prior).2.WellFormed :=
  registerCorrectionProgram_wellFormed _ _ _ trivial

theorem appendLiteral_wellFormed {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (gs : Circuit) (hp : p.2.WellFormed) (hg : CircuitWellFormed gs) :
    (appendLiteral p gs).2.WellFormed :=
  appendCompiled_wellFormed _ _ hp (literalProgram_wellFormed _ hg)

theorem collectProgram_wellFormed (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hn : ∀ cursor prior, (next cursor prior).2.WellFormed)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    (collectProgram n next ws start prior).2.WellFormed := by
  induction ws generalizing start with
  | nil => exact hn _ _
  | cons w ws ih => simpa only [collectProgram,castFinish_wellFormed,Straight.WellFormed] using ih (start+1) _

theorem appendRetaining_wellFormed {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (prior : List (Fin start)) (hp : p.2.WellFormed)
    (hn : ∀ cursor prior, (next cursor prior).2.WellFormed) :
    (appendRetaining p next prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ hp (hn _ _)

private theorem swapOutput_wellFormed : CircuitWellFormed fig15SwapOutput := by
  intro g hg
  simp only [fig15SwapOutput,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hg
  obtain ⟨i,hi,hg⟩ := hg
  rcases hg with rfl | rfl | rfl <;> simp [Gate.WellFormed]

attribute [local irreducible] multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram
  measuredForwardWrapperProgram measuredReverseWrapperProgram measuredForwardDataBankProgram measuredReverseDataBankProgram

theorem divisionCleanupProgram_wellFormed (n start : Nat) : (divisionCleanupProgram n start).2.WellFormed :=
  appendLiteral_wellFormed _ _ (unmultiplyDataProgram_wellFormed _ _) swapOutput_wellFormed

theorem multiplicationCleanupProgram_wellFormed (n start : Nat) : (multiplicationCleanupProgram n start).2.WellFormed := by
  unfold multiplicationCleanupProgram
  exact appendCompiled_wellFormed _ _ (unmultiplyDataProgram_wellFormed _ _)
    (appendLiteral_wellFormed _ _ (measuredReverseDataBankProgram_wellFormed _ _) swapOutput_wellFormed)

attribute [local irreducible] divisionCleanupProgram multiplicationCleanupProgram
theorem divisionCorrectionProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (divisionCorrectionProgram n start prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ (correctionCompiled_wellFormed _ _ _ _) (divisionCleanupProgram_wellFormed _ _)

theorem divisionAfterResetProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (divisionAfterResetProgram n start prior).2.WellFormed := by
  unfold divisionAfterResetProgram
  apply appendRetaining_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredReverseDataBankProgram_wellFormed _ _) (multiplyDataProgram_wellFormed _ _)
  · exact divisionCorrectionProgram_wellFormed n

theorem multiplicationCorrectionProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (multiplicationCorrectionProgram n start prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ (correctionCompiled_wellFormed _ _ _ _) (multiplicationCleanupProgram_wellFormed _ _)

theorem multiplicationAfterResetProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (multiplicationAfterResetProgram n start prior).2.WellFormed := by
  unfold multiplicationAfterResetProgram
  apply appendRetaining_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredForwardDataBankProgram_wellFormed _ _) (multiplyDataProgram_wellFormed _ _)
  · exact multiplicationCorrectionProgram_wellFormed n

attribute [local irreducible] divisionAfterResetProgram multiplicationAfterResetProgram collectProgram
theorem divisionProgram_wellFormed (n start : Nat) : (divisionProgram n start).2.WellFormed := by
  unfold divisionProgram
  apply appendCompiled_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredForwardWrapperProgram_wellFormed _ _) (multiplyWorkProgram_wellFormed _ _)
  · exact collectProgram_wellFormed _ _ (divisionAfterResetProgram_wellFormed n) _ _ _

theorem multiplicationProgram_wellFormed (n start : Nat) : (multiplicationProgram n start).2.WellFormed := by
  unfold multiplicationProgram
  exact appendCompiled_wellFormed _ _ (multiplyWorkProgram_wellFormed _ _)
    (collectProgram_wellFormed _ _ (multiplicationAfterResetProgram_wellFormed n) _ _ _)
end ShorECDLP.Paper2607_13816.ChallengeMigration

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Classical Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem measuredPhysical_unary_literal_view (order : UnaryOrder) (leaf : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (path : List Wire) :
    unaryAdaptiveAction order (fun l c => .unitary (leaf l c) .done) tree control path =
      unaryAction order leaf tree control path := by
  induction tree generalizing control path with
  | leaf l => rfl
  | node bit zero one ihz iho =>
    cases path with
    | nil => rfl
    | cons p ps => cases order <;> simp [unaryAdaptiveAction,unaryAction,ihz,iho]

theorem program_wellFormed (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat)
    (h : (quotientSwap r k K).WellFormed) : (program n start r k K).2.WellFormed := by
  have hp := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hp.2
  unfold program
  apply surroundCompiled_wellFormed _ _ _ hp.1.1 ht.2.1
  apply unaryProgram_wellFormed n .inc _ (fun l c => .unitary (quotientSwapLeaf r k l c) .done)
  · intro label control cursor hh
    exact literalProgram_wellFormed _ hh.1
  · rw [measuredPhysical_unary_literal_view]
    exact ht.1

theorem d2Program_wellFormed (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (h : (blockD2 r w).WellFormed) : (d2Program n start r w).2.WellFormed := by
  have hp := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hp.2
  exact surroundCompiled_wellFormed _ _ _ hp.1.1 ht.2.1
    (program_wellFormed n start (r.quotient w) w.start w.stop ht.1)

theorem dProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (h : (blockD r w).WellFormed) : (dProgram n start r w).2.WellFormed := by
  have hp := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hp.1
  exact surroundCompiled_wellFormed _ _ _ ht.1.1 hp.2.1
    (d2Program_wellFormed n start r w ht.2)

theorem cdProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (blockCD r width T).WellFormed) : (cdProgram n start r width T).2.WellFormed := by
  have hp := adaptive_seq_wellFormed_parts _ _ h
  exact prependCompiled_wellFormed _ _ hp.1.1
    (dProgram_wellFormed n start r _ hp.2)

theorem stepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (step r width T).WellFormed) : (stepProgram n start r width T).2.WellFormed := by
  unfold stepProgram
  rw [← stepSources_eq r width T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold stepSegments stepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))))))
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact remainderBlockProgram_wellFormed n cursor r width _ hh
  · intro cursor hh; exact cdProgram_wellFormed n cursor r width T hh
  · intro cursor hh; exact coefficientBlockProgram_wellFormed n cursor r width _ hh
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact phaseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh; exact hProgram_wellFormed n cursor r width T hh

attribute [local irreducible] stepProgram step

theorem scheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (width count first start : Nat)
    (h : (schedule r width first count).WellFormed) :
    (scheduleProgram n r width count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (stepProgram_wellFormed _ _ _ _ _ hs.1)
      (ih _ _ hs.2)

attribute [local irreducible] scheduleProgram schedule

private theorem measuredPhysical_forward_source_view (r : IndexedStepRegisters) :
    forward r = schedule r 256 1 secp256k1ScheduleLength := rfl
private theorem measuredPhysical_forward_program_view (n start : Nat) (r : IndexedStepRegisters) :
    forwardProgram n start r = scheduleProgram n r 256 secp256k1ScheduleLength 1 start := rfl

theorem forwardProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (forward r).WellFormed) : (forwardProgram n start r).2.WellFormed :=
  (congrArg (fun p : (count : Nat) × Straight n start (start+count) => p.2.WellFormed)
    (measuredPhysical_forward_program_view n start r)).mpr
    (scheduleProgram_wellFormed n r 256 secp256k1ScheduleLength 1 start
      ((congrArg AdaptiveCircuit.WellFormed (measuredPhysical_forward_source_view r)).mp h))

attribute [local irreducible] preprocessProgram productionParityProgram eeaPreprocess secp256k1EEAParityCorrection
attribute [local irreducible] forwardProgram forward canonicalWork2Rotation terminalEpochCompression terminalWork1Clear

theorem wrapperProgram_wellFormed (n start : Nat) (h : wrapper.WellFormed) :
    (wrapperProgram n start).2.WellFormed := by
  unfold wrapperProgram
  rw [← wrapperSources_eq] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold wrapperSegments wrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))))
  · intro cursor hh; exact preprocessProgram_wellFormed n cursor
  · intro cursor hh; exact forwardProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact productionParityProgram_wellFormed n cursor
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
private theorem measuredPhysical_sequence_wf (sources : List AdaptiveCircuit)
    (h : ∀ c ∈ sources, c.WellFormed) : (sequenceCircuit sources).WellFormed := by
  induction sources with
  | nil => trivial
  | cons c cs ih =>
    exact (h c (by simp)).seq (ih (fun x hx => h x (by simp [hx])))

theorem blockCD_wellFormed (r : IndexedStepRegisters) (width T : Nat)
    (hl : IndexedStepLayout r width T)
    (hc : CircuitWellFormed (blockCForward r ++ blockDForward r (certifiedActiveWindows width T).quotientSwap)) :
    (blockCD r width T).WellFormed := by
  have hp := (circuitWellFormed_append _ _).mp hc
  have hd := hp.2
  simp only [blockDForward,circuitWellFormed_append] at hd
  have hd2 := hd.1.2
  change CircuitWellFormed ((before r ++ quotientSwapUnitary (r.quotient (certifiedActiveWindows width T).quotientSwap)
    (certifiedActiveWindows width T).quotientSwap.start (certifiedActiveWindows width T).quotientSwap.stop) ++ after r) at hd2
  simp only [circuitWellFormed_append] at hd2
  have hnew : (blockD2 r (certifiedActiveWindows width T).quotientSwap).WellFormed :=
    (AdaptiveCircuit.WellFormed.seq ⟨hd2.1.1,trivial⟩
      ((quotientSwap_wellFormed _ hl.quotient).seq ⟨hd2.2,trivial⟩))
  unfold blockCD blockD
  exact (show (AdaptiveCircuit.unitary (blockCForward r) .done).WellFormed from ⟨hp.1,trivial⟩).seq
    (((show (AdaptiveCircuit.unitary (blockD1Forward r) .done).WellFormed from ⟨hd.1.1,trivial⟩).seq hnew).seq
      (show (AdaptiveCircuit.unitary (blockD3Forward r) .done).WellFormed from ⟨hd.2,trivial⟩))

theorem step_wellFormed (r : IndexedStepRegisters) (width T : Nat)
    (hl : IndexedStepLayout r width T) : (step r width T).WellFormed := by
  have ho := measuredIndexedStep_wellFormed r width T hl
  rw [← measuredStepSources_eq] at ho
  have hs := sequenceCircuit_wellFormed_members _ ho
  have hc := (hs (.unitary (blockCForward r ++ blockDForward r (certifiedActiveWindows width T).quotientSwap) .done)
    (by simp [measuredStepSources])).1
  rw [← stepSources_eq]
  apply measuredPhysical_sequence_wf
  intro c h
  simp only [stepSources,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs _ (by simp [measuredStepSources])
  · exact hs _ (by simp [measuredStepSources])
  · exact blockCD_wellFormed r width T hl hc
  · exact hs _ (by simp [measuredStepSources])
  · exact hs _ (by simp [measuredStepSources])
  · exact hs _ (by simp [measuredStepSources])
  · exact hs _ (by simp [measuredStepSources])

theorem schedule_wellFormed (r : IndexedStepRegisters) (width first count : Nat)
    (hl : IndexedScheduleLayout r width first count) :
    (schedule r width first count).WellFormed := by
  induction hl with
  | done first => simp [schedule,AdaptiveCircuit.WellFormed,CircuitWellFormed]
  | step head tail ih => simpa only [schedule] using (step_wellFormed _ _ _ head).seq ih

theorem forward_wellFormed : (forward indexedStepProductionRegisters).WellFormed :=
  (congrArg AdaptiveCircuit.WellFormed (measuredPhysical_forward_source_view indexedStepProductionRegisters)).mpr
    (schedule_wellFormed _ _ _ _ secp256k1ScheduleLayout_production)

theorem wrapper_wellFormed : wrapper.WellFormed := by
  have ho := secp256k1MeasuredEEAForwardWrapper_wellFormed
  have hclear := adaptive_seq_wellFormed_parts _ _ ho
  have hparity := adaptive_seq_wellFormed_parts _ _ hclear.1
  have hcanonical := adaptive_seq_wellFormed_parts _ _ hparity.1
  have hpre := adaptive_seq_wellFormed_parts _ _ hcanonical.1
  exact (((hpre.1.seq forward_wellFormed).seq hcanonical.2).seq hparity.2).seq hclear.2

attribute [local irreducible] wrapperProgram multiplyWorkProgram divisionAfterResetProgram collectProgram

theorem divisionProgram_wellFormed (n start : Nat) :
    (divisionProgram n start).2.WellFormed := by
  unfold divisionProgram
  apply appendCompiled_wellFormed
  · exact appendCompiled_wellFormed _ _ (wrapperProgram_wellFormed _ _ wrapper_wellFormed)
      (multiplyWorkProgram_wellFormed _ _)
  · exact collectProgram_wellFormed _ _ (divisionAfterResetProgram_wellFormed n) _ _ _

end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Classical Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] wrapperProgram multiplicationCorrectionProgram multiplyWorkProgram multiplyDataProgram

theorem bankWrapperProgram_wellFormed (n start : Nat) : (bankWrapperProgram n start).2.WellFormed :=
  (relabelCompiled_wellFormed eeaWorkspaceExchange _).2
    (wrapperProgram_wellFormed n start wrapper_wellFormed)

theorem multiplicationAfterResetProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (multiplicationAfterResetProgram n start prior).2.WellFormed := by
  unfold multiplicationAfterResetProgram
  apply appendRetaining_wellFormed
  · exact appendCompiled_wellFormed _ _ (bankWrapperProgram_wellFormed _ _) (multiplyDataProgram_wellFormed _ _)
  · exact ChallengeMigration.multiplicationCorrectionProgram_wellFormed n

attribute [local irreducible] multiplicationAfterResetProgram collectProgram

theorem multiplicationProgram_wellFormed (n start : Nat) : (multiplicationProgram n start).2.WellFormed := by
  unfold multiplicationProgram
  exact appendCompiled_wellFormed _ _ (multiplyWorkProgram_wellFormed _ _)
    (collectProgram_wellFormed _ _ (multiplicationAfterResetProgram_wellFormed n) _ _ _)
end
end ShorECDLP.Entrant.MeasuredQuotient
end

namespace ShorECDLP.Entrant.MeasuredQuotient.Reverse
open Quantum Classical Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem program_wellFormed (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (h : (block r w).WellFormed) : (program n start r w).2.WellFormed := by
  have hp := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hp.1
  exact surroundCompiled_wellFormed _ _ _ ht.1.1 hp.2.1
    (MeasuredQuotient.d2Program_wellFormed n start r w ht.2)

attribute [local irreducible] program block step phaseInverseProgram coefficientInverseProgram intervalInverseProgram hInverseProgram

theorem stepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (h : (step r 256 T).WellFormed) : (stepProgram n start r T).2.WellFormed := by
  unfold stepProgram
  rw [← stepSources_eq r T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold stepSegments stepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))))
  · intro cursor hh; exact hInverseProgram_wellFormed n cursor r 256 T hh
  · intro cursor hh; exact phaseInverseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) _ _ .add true .work2 hh
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) _ _ .sub false .work2 hh
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact program_wellFormed n cursor r _ hh
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 _ _ .add false .work1 hh
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 _ _ .sub true .work1 hh
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1

attribute [local irreducible] stepProgram

theorem scheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (h : (schedule r 256 first count).WellFormed) :
    (scheduleProgram n r count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (ih _ _ hs.1) (stepProgram_wellFormed _ _ _ _ hs.2)

attribute [local irreducible] scheduleProgram schedule
private theorem reverse_program_view (n start : Nat) (r : IndexedStepRegisters) :
    reverseProgram n start r = scheduleProgram n r secp256k1ScheduleLength 1 start := rfl
private theorem reverse_source_view (r : IndexedStepRegisters) :
    reverse r = schedule r 256 1 secp256k1ScheduleLength := rfl

theorem reverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (reverse r).WellFormed) : (reverseProgram n start r).2.WellFormed :=
  (congrArg (fun p : (count : Nat) × Straight n start (start+count) => p.2.WellFormed)
    (reverse_program_view n start r)).mpr
    (scheduleProgram_wellFormed n r secp256k1ScheduleLength 1 start
      ((congrArg AdaptiveCircuit.WellFormed (reverse_source_view r)).mp h))

attribute [local irreducible] unpreprocessProgram productionParityProgram eeaUnpreprocess secp256k1EEAParityCorrection
attribute [local irreducible] reverseProgram reverse canonicalWork2InverseRotation terminalEpochCompression terminalWork1Clear

theorem wrapperProgram_wellFormed (n start : Nat) : (wrapperProgram n start).2.WellFormed := by
  have h := wrapper_wellFormed
  unfold wrapperProgram
  rw [← wrapperSources_eq] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold wrapperSegments wrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))))
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact productionParityProgram_wellFormed n cursor
  · intro cursor hh; exact literalProgram_wellFormed _ hh.1
  · intro cursor hh; exact reverseProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh; exact unpreprocessProgram_wellFormed n cursor

attribute [local irreducible] wrapperProgram divisionCorrectionProgram multiplyWorkProgram multiplyDataProgram

theorem bankWrapperProgram_wellFormed (n start : Nat) : (bankWrapperProgram n start).2.WellFormed :=
  (relabelCompiled_wellFormed eeaWorkspaceExchange _).2 (wrapperProgram_wellFormed n start)

theorem divisionAfterResetProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (divisionAfterResetProgram n start prior).2.WellFormed := by
  unfold divisionAfterResetProgram
  apply appendRetaining_wellFormed
  · exact appendCompiled_wellFormed _ _ (bankWrapperProgram_wellFormed _ _) (multiplyDataProgram_wellFormed _ _)
  · exact ChallengeMigration.divisionCorrectionProgram_wellFormed n

attribute [local irreducible] divisionAfterResetProgram collectProgram MeasuredQuotient.wrapperProgram

theorem divisionProgram_wellFormed (n start : Nat) : (divisionProgram n start).2.WellFormed := by
  unfold divisionProgram
  exact appendCompiled_wellFormed _ _
    (appendCompiled_wellFormed _ _ (MeasuredQuotient.wrapperProgram_wellFormed _ _ MeasuredQuotient.wrapper_wellFormed)
      (multiplyWorkProgram_wellFormed _ _))
    (collectProgram_wellFormed _ _ (divisionAfterResetProgram_wellFormed n) _ _ _)

end
end ShorECDLP.Entrant.MeasuredQuotient.Reverse

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] divisionProgram multiplicationProgram equalityProgram
attribute [local irreducible] ShorECDLP.Entrant.MeasuredQuotient.Reverse.divisionProgram ShorECDLP.Entrant.MeasuredQuotient.multiplicationProgram
private theorem zero_cx_wellFormed : CircuitWellFormed cx := by
  intro g hg
  have he := List.mem_singleton.mp hg
  subst g
  change (837 : Wire) ≠ 263
  decide +kernel

theorem zDivisionProgram_wellFormed (n start : Nat) : (zDivisionProgram n start).2.WellFormed := by
  unfold zDivisionProgram
  apply appendCompiled_wellFormed
  · exact equalityProgram_wellFormed _ _ _ _ _ _ (computeEqConstAdaptive_wellFormed _ _ _ _ layout)
  · apply prependCompiled_wellFormed _ _ zero_cx_wellFormed
    apply appendCompiled_wellFormed
    · exact ShorECDLP.Entrant.MeasuredQuotient.Reverse.divisionProgram_wellFormed _ _
    · apply prependCompiled_wellFormed _ _ zero_cx_wellFormed
      exact equalityProgram_wellFormed _ _ _ _ _ _ (computeEqConstAdaptive_wellFormed _ _ _ _ layout)

theorem zMultiplicationProgram_wellFormed (n start : Nat) : (zMultiplicationProgram n start).2.WellFormed := by
  unfold zMultiplicationProgram
  apply appendCompiled_wellFormed
  · exact equalityProgram_wellFormed _ _ _ _ _ _ (computeEqConstAdaptive_wellFormed _ _ _ _ layout)
  · apply prependCompiled_wellFormed _ _ zero_cx_wellFormed
    apply appendCompiled_wellFormed
    · exact ShorECDLP.Entrant.MeasuredQuotient.multiplicationProgram_wellFormed _ _
    · apply prependCompiled_wellFormed _ _ zero_cx_wellFormed
      exact equalityProgram_wellFormed _ _ _ _ _ _ (computeEqConstAdaptive_wellFormed _ _ _ _ layout)

attribute [local irreducible] squareSubtractProgram

theorem doublesProgram_wellFormed (n k start : Nat) (a : Wire) (rest dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a::rest).length=bits.length) (hd : (a::rest).length=dirty.length)
    (hnd : ([c,r,t,f]++(a::rest)++dirty).Nodup) :
    (ShorECDLP.Entrant.SquareInPlace.doublesProgram n k start (a::rest) dirty bits p c r t f).2.WellFormed := by
  induction k generalizing start with
  | zero => trivial
  | succ k ih =>
    simp only [ShorECDLP.Entrant.SquareInPlace.doublesProgram]
    exact appendCompiled_wellFormed _ _ (modularDoubleProgram_wellFormed n start a rest dirty bits p c r t f hk hd hnd) (ih _)

theorem padsProgram_wellFormed (n k start : Nat) (w : Wire) :
    (ShorECDLP.Entrant.SquareInPlace.padsProgram n k start w).2.WellFormed := by
  induction k generalizing start with
  | zero => trivial
  | succ k ih =>
    simp only [ShorECDLP.Entrant.SquareInPlace.padsProgram]
    exact appendCompiled_wellFormed _ _ trivial (ih _)

private theorem inPlace_square_layout :
    ([558,559,561,562,560] ++ List.range' 580 256 ++ (263 :: List.range' 264 255)).Nodup := by decide +kernel
private theorem inPlace_double_layout :
    ([560,561,562,559] ++ (263 :: List.range' 264 255) ++ List.range' 580 256).Nodup := by decide +kernel

attribute [local irreducible] squareInverseProgram modularDoubleProgram
  ShorECDLP.Entrant.SquareInPlace.doublesProgram ShorECDLP.Entrant.SquareInPlace.padsProgram

theorem inPlaceSquareProgram_wellFormed (n start : Nat) :
    (ShorECDLP.Entrant.SquareInPlace.inPlaceSquareProgram n start).2.WellFormed := by
  have hp : (squareInverseProgram n start (List.range' 580 256) (List.range' 580 256) (263 :: List.range' 264 255)
      (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 559 561 562 560).2.WellFormed :=
    squareInverseProgram_wellFormed n start (List.range' 580 256) (List.range' 580 256) 263 (List.range' 264 255)
      (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 559 561 562 560
      (by simp) (by simp [constantBits_length]) inPlace_square_layout (fun _ h => h)
  have hq := doublesProgram_wellFormed n 255 (start + (squareInverseProgram n start (List.range' 580 256)
      (List.range' 580 256) (263 :: List.range' 264 255) (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 559 561 562 560).1)
      263 (List.range' 264 255) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 560 561 562 559
      (by simp [secp256k1ReductionConstantBits]) (by simp) inPlace_double_layout
  exact appendCompiled_wellFormed _ _ hp hq

attribute [local irreducible] ShorECDLP.Entrant.SquareInPlace.inPlaceSquareProgram in
theorem paddedSquareProgram_wellFormed (n start : Nat) :
    (ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram n start).2.WellFormed := by
  unfold ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram
  exact appendCompiled_wellFormed (ShorECDLP.Entrant.SquareInPlace.inPlaceSquareProgram n start)
    (ShorECDLP.Entrant.SquareInPlace.padsProgram n 131327
      (start + (ShorECDLP.Entrant.SquareInPlace.inPlaceSquareProgram n start).1) 558)
    (inPlaceSquareProgram_wellFormed n start) (padsProgram_wellFormed n 131327 _ 558)

theorem pointSquareProgram_wellFormed (n start : Nat) : (pointSquareProgram n start).2.WellFormed := by
  unfold pointSquareProgram
  apply squareSubtractProgram_wellFormed
  · simp
  · simp
  · simp [secp256k1ReductionConstantBits]
  · simp
  all_goals
    have hw : 7 :: List.range' 8 255 = List.range' 7 256 := rfl
    rw [hw]
    simp only [List.nodup_append]
    refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
    all_goals
      intro a ha b hb he
      subst a
      simp at ha hb
      rcases ha with h | h | h | h | h
      all_goals first | omega | (rcases h with rfl | ⟨hl,hu⟩ <;> omega)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CoordinatePhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CoordinatePhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem fieldLoadOps_physical (field : PointField) : ∀ op ∈ fieldLoadOps field, op.Physical := by
  apply unaryLookupOps_physical
  · exact tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)
  · intro label control hc g hg
    simp only [fieldLeaf,lookupLeafGates,List.mem_map] at hg
    obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
    have ht := (List.of_mem_zip hm).2
    simp only [List.mem_range'] at ht
    simp only [List.mem_cons,pointLookupPath,List.mem_range'] at hc
    change control ≠ target
    rcases hc with rfl | hc
    all_goals intro he; subst target; omega

theorem fieldLoadProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLoadProgram field start).WellFormed := by
  unfold fieldLoadProgram
  rw [castFinish_wellFormed]
  exact lookupProgram_wellFormed _ (fieldLoadOps_physical field) _

attribute [local irreducible] fieldLoadProgram modularAddProgram appendCompiled

theorem fieldLookupAddProgram_wellFormed (field : PointField) (acc : List Wire) (start : Nat)
    (hl : acc.length = 256) (hn : ([836,559,560,561,558] ++ List.range' 7 256 ++ acc).Nodup) :
    (fieldLookupAddProgram field acc start).2.WellFormed := by
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  have ha : add.2.WellFormed := modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _
    (by simpa using hl.symm) (by omega) (by simp [hl,secp256k1ReductionConstantBits]) hn
  exact appendCompiled_wellFormed ⟨32767,fieldLoadProgram field start⟩
    (appendCompiled add ⟨32767,fieldLoadProgram field (start+32767+add.1)⟩)
    (fieldLoadProgram_wellFormed _ _)
    (appendCompiled_wellFormed add ⟨32767,fieldLoadProgram field (start+32767+add.1)⟩ ha (fieldLoadProgram_wellFormed _ _))
private theorem fieldAccumulator_layout (base : Nat) (hb : base=263 ∨ base=580) :
    ([836,559,560,561,558] ++ List.range' 7 256 ++ List.range' base 256).Nodup := by
  rcases hb with rfl | rfl
  all_goals
    simp only [List.nodup_append]
    refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
    all_goals
      intro a ha b hb he
      subst a
      simp at ha hb
      rcases ha with h | h | h | h | h
      all_goals omega

theorem fieldLookupXProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLookupAddProgram field (List.range' 263 256) start).2.WellFormed :=
  fieldLookupAddProgram_wellFormed _ _ _ (by simp) (fieldAccumulator_layout _ (Or.inl rfl))

theorem fieldLookupYProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLookupAddProgram field (List.range' 580 256) start).2.WellFormed :=
  fieldLookupAddProgram_wellFormed _ _ _ (by simp) (fieldAccumulator_layout _ (Or.inr rfl))

attribute [local irreducible] fieldLookupAddProgram yNegateProgram

theorem signedFieldProgram_wellFormed (field : PointField) (start : Nat) :
    (signedFieldProgram field start).2.WellFormed := by
  unfold signedFieldProgram
  exact appendCompiled_wellFormed _ _ (yNegateProgram_wellFormed _)
    (appendCompiled_wellFormed _ _ (fieldLookupYProgram_wellFormed _ _) (yNegateProgram_wellFormed _))

attribute [local irreducible] zDivisionProgram zMultiplicationProgram pointSquareProgram signedFieldProgram xNegateProgram

theorem adaptiveCoordinateProgram_wellFormed (start : Nat) : (adaptiveCoordinateProgram start).2.WellFormed := by
  unfold adaptiveCoordinateProgram
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [adaptiveCoordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fieldLookupXProgram_wellFormed _ _
  · exact signedFieldProgram_wellFormed _ _
  · exact zDivisionProgram_wellFormed _ _
  · exact paddedSquareProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact zMultiplicationProgram_wellFormed _ _
  · exact xNegateProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact signedFieldProgram_wellFormed _ _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ActualPhysical ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ActualPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

/-! Physical validity of the actual first and signed windows and their outer composition. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] adaptiveCoordinateProgram

theorem sharedAdaptiveCoordinateProgram_wellFormed (w : OddWindow) (start : Nat) :
    (sharedAdaptiveCoordinateProgram w start).2.WellFormed :=
  (reindexCompiled_wellFormed _ _).mpr (adaptiveCoordinateProgram_wellFormed start)

attribute [local irreducible] sharedAdaptiveCoordinateProgram sharedYNegateProgram ipxProgram

theorem ipxWindowCore_wellFormed (w : OddWindow) (start : Nat) :
    (ipxWindowCore w start).2.WellFormed := by
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [ipxWindowSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact sharedAdaptiveCoordinateProgram_wellFormed _ _
  · exact sharedYNegateProgram_wellFormed _ _
  · exact ipxProgram_wellFormed _ _
  · exact sharedYNegateProgram_wellFormed _ _

attribute [local irreducible] ipxWindowCore

theorem ipxWindowPrepared_wellFormed (w : OddWindow) (start : Nat) :
    (ipxWindowPrepared w start).2.WellFormed := by
  exact surroundCompiled_wellFormed _ _ _
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (ipxWindowCore_wellFormed w start)

attribute [local irreducible] ipxWindowPrepared

theorem actualIpxWindow_wellFormed (w : OddWindow) (start : Nat) :
    ((actualIpxWindow w).program start).WellFormed := by
  apply shiftStraight_wellFormed
  exact (relabelStraight_wellFormed _ _).mpr (ipxWindowPrepared_wellFormed w 0)

theorem firstLookupOps_physical : ∀ op ∈ firstLookupOps, op.Physical := by
  apply unaryLookupOps_physical
  · exact tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)
  · intro label control hc g hg
    simp only [pointLeaf,lookupLeafGates,List.mem_map] at hg
    obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
    have ht := (List.of_mem_zip hm).2
    change control ≠ target
    have hn : ∀ c ∈ 836 :: List.range' 519 16, c ∉ pointLogicalWires := by
      intro c hc ht
      simp only [List.mem_cons,List.mem_range'] at hc
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_range',List.mem_singleton] at ht
      rcases hc with rfl | hc
      all_goals omega
    exact fun he => hn control hc (he ▸ ht)

theorem firstLookupProgram_wellFormed (start : Nat) : (firstLookupProgram start).WellFormed := by
  unfold firstLookupProgram
  rw [castFinish_wellFormed]
  exact lookupProgram_wellFormed _ firstLookupOps_physical _

attribute [local irreducible] firstLookupProgram

theorem actualFirstWindow_wellFormed (start : Nat) :
    (actualFirstWindow.program start).WellFormed :=
  (reindexStraight_wellFormed _ _).mpr (firstLookupProgram_wellFormed start)

attribute [local irreducible] actualIpxWindow actualFirstWindow

theorem ipxOuterPlan_windowsWellFormed : ipxOuterPlan.WindowsWellFormed := by
  intro w hw start
  change w ∈ ipxLeftWindows ++ ipxRightWindows at hw
  simp only [ipxLeftWindows,ipxRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact actualFirstWindow_wellFormed _
  · exact actualIpxWindow_wellFormed _ _
  · exact actualIpxWindow_wellFormed _ _

attribute [local irreducible] ipxOuterPlan

theorem ipxOuterPlan_round_wellFormed (start : Nat) :
    (ipxOuterPlan.round start).WellFormed :=
  ipxOuterPlan.round_wellFormed ipxOuterPlan_windowsWellFormed start

theorem ipxOuterPlan_repeat_wellFormed (count start : Nat) :
    (ipxOuterPlan.repeat count start).WellFormed :=
  ipxOuterPlan.repeat_wellFormed ipxOuterPlan_windowsWellFormed count start

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/HistoryExecution ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/HistoryExecution.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def historyAfter {s : Nat} (e : Nat) (history : Fin s → Bool) (bits : List Bool) : Fin e → Bool :=
  fun i => (List.ofFn history ++ bits).getD i.val false

theorem historyAfter_nil {s : Nat} (history : Fin s → Bool) : historyAfter s history List.nil = history := by
  funext i
  simp [historyAfter, i.isLt]

theorem historyAfter_cons {s e : Nat} (history : Fin s → Bool) (v : Bool) (bits : List Bool) :
    historyAfter e (Fin.lastCases v history) bits = historyAfter e history (v :: bits) := by
  funext i
  simp only [historyAfter,List.ofFn_succ',Fin.lastCases_castSucc,Fin.lastCases_last,
    List.concat_eq_append,List.append_assoc,List.singleton_append]

/-- Exact ordered branch composition, including the records supplied to the suffix. -/
theorem straight_append_run_history {n s m e : Nat} (p : Straight n s m) (q : Straight n m e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((p.append q).instantiate read history).run =
      (p.instantiate read history).run.flatMap (fun b =>
        (q.instantiate read (historyAfter m history b.history)).run.map (fun c => b.seq c)) := by
  induction p with
  | done =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,List.flatMap_cons,List.flatMap_nil,List.append_nil,historyAfter_nil]
    simp [InstrumentBranch.seq]
  | gate g p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    rfl
  | recordGate i v g p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    rfl
  | measure w p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,List.flatMap_append,Function.comp_def]
    simp only [historyAfter_cons]
    rfl
theorem historyAfter_old {s e : Nat} (history : Fin s → Bool) (bits : List Bool)
    (i : Fin e) (hi : i.val < s) : historyAfter e history bits i = history ⟨i.val,hi⟩ := by
  unfold historyAfter
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [hi]

theorem historyAfter_new {s e : Nat} (history : Fin s → Bool) (bits : List Bool)
    (i : Fin e) (hi : s ≤ i.val) : historyAfter e history bits i = bits.getD (i.val-s) false := by
  unfold historyAfter
  rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
  simp

/-- The Fourier suffix sees the exact new outcomes, not arithmetic-cleanup records. -/
theorem nextBankPrior_map_historyAfter {s : Nat} (count : Nat) (prior : List (Fin s))
    (history : Fin (s+count) → Bool) (bits : List Bool) (hl : bits.length = 16) :
    (nextBankPrior count prior).map (historyAfter (s+count+16) history bits) =
      bits.reverse ++ prior.map (fun i => history ⟨i.val,by omega⟩) := by
  simp only [nextBankPrior,List.map_append,List.map_reverse,List.map_ofFn,List.map_map]
  congr 1
  · congr 1
    have he : List.ofFn (fun i : Fin 16 => bits.getD i.val false) = bits := by
      apply List.ext_getElem
      · simpa using hl.symm
      · intro i hi hj
        simp only [List.getElem_ofFn]
        exact List.getD_eq_getElem _ false hj
    apply Eq.trans _ he
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_def]
    rw [historyAfter_new _ _ _ (by simp)]
    simp
  · apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def]
    exact historyAfter_old _ _ _ (by simpa using Nat.lt_add_right count i.isLt)

/-- The complete ordered instrument of a Fourier bank followed by any straight suffix. -/
theorem fourierProgram_append_run_history {n e : Nat} (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) (q : Straight n (start+ws.length) e)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (((fourierProgram n dir ws start prior).append q).instantiate read history).run =
      (fourierOutcomes ws.length).flatMap (fun bits =>
        (q.instantiate read (historyAfter (start+ws.length) history bits)).run.map
          (fun b => InstrumentBranch.seq ⟨bits,fourierBranch dir ws (prior.map history) bits⟩ b)) := by
  rw [straight_append_run_history,fourierProgram_run,semiclassicalFourier_run,List.flatMap_map]
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/OuterExecution ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/OuterExecution.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

noncomputable def sourceOuterAxis (wires : List Wire) : List AdaptiveCircuit → List Bool → AdaptiveCircuit
  | [], _ => .done
  | call :: calls, prior => .unitary (wires.reverse.map Gate.H)
      (call.seq (fourierContinue .inverse wires prior (sourceOuterAxis wires calls)))

theorem prepareOuterBank_append_run {n s m e : Nat} (wires : List Wire)
    (p : Straight n s m) (q : Straight n m e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (((prepareOuterBank wires p).append q).instantiate read history).run =
      (AdaptiveCircuit.unitary (wires.map Gate.H) ((p.append q).instantiate read history)).run := by
  induction wires with
  | nil =>
    simp only [prepareOuterBank,List.foldr_nil,List.map_nil,AdaptiveCircuit.run]
    change _ = List.map (fun a => a) _
    rw [List.map_id']
  | cons w ws ih =>
    simp only [prepareOuterBank,List.foldr_cons,Straight.append,Straight.instantiate,
      TemplateGate.instantiate,AdaptiveCircuit.run,List.map_cons]
    rw [show (((ws.foldr (fun w p => Straight.gate (.literal (.H w)) p) p).append q).instantiate read history).run =
      (AdaptiveCircuit.unitary (ws.map Gate.H) ((p.append q).instantiate read history)).run from ih]
    simp only [AdaptiveCircuit.run,List.map_map]
    apply List.map_congr_left
    intro a ha
    cases a
    rfl

theorem bankPrior_map_historyAfter {s : Nat} (count : Nat) (prior : List (Fin s))
    (history : Fin s → Bool) (bits : List Bool) :
    (bankPrior count prior).map (historyAfter (s+count) history bits) = prior.map history := by
  simp only [bankPrior,List.map_map]
  apply List.map_congr_left
  intro i hi
  exact historyAfter_old _ _ _ i.isLt

theorem fourierBank_append_run {n e : Nat} (wires : Vector Wire 16) (start : Nat)
    (prior : List (Fin start)) (q : Straight n (start+16) e)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (((castFinish (by simp) (fourierProgram n .inverse wires.toList start prior)).append q).instantiate read history).run =
      (fourierOutcomes 16).flatMap (fun bits =>
        (q.instantiate read (historyAfter (start+16) history bits)).run.map
          (fun b => InstrumentBranch.seq ⟨bits,fourierBranch .inverse wires.toList (prior.map history) bits⟩ b)) := by
  rw [straight_append_run_history,castFinish_instantiate,fourierProgram_run,semiclassicalFourier_run,List.flatMap_map]
  simp

attribute [local irreducible] fourierProgram prepareOuterBank

theorem outerAxis_run {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n))
    (calls : List AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hc : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) ws calls)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((outerAxis wires ws start prior).instantiate read history).run =
      (sourceOuterAxis wires.toList calls (prior.map history)).run := by
  induction hc generalizing start with
  | nil => rfl
  | @cons w call ws calls hw hws ih =>
    simp only [outerAxis,castFinish_instantiate,prepareOuterBank_append_run,sourceOuterAxis,AdaptiveCircuit.run]
    congr 1
    rw [straight_append_run_history,hw]
    rw [AdaptiveCircuit.run_seq]
    unfold Instrument.seq
    apply List.flatMap_congr
    intro a ha
    rw [fourierBank_append_run]
    simp only [fourierContinue_run,Vector.length_toList]
    congr 1
    apply List.flatMap_congr
    intro bits hb
    rw [ih]
    rw [nextBankPrior_map_historyAfter _ _ _ _ ((fourierOutcomes_mem _ _).mp hb)]
    rw [bankPrior_map_historyAfter]
    have ho : prior.map (fun i => historyAfter (start+w.count) history a.history ⟨i.val,by omega⟩) = prior.map history := by
      apply List.map_congr_left
      intro i hi
      exact historyAfter_old _ _ _ i.isLt
    rw [ho]
noncomputable def sourceOuterRound (wires : List Wire) (left right : List AdaptiveCircuit)
    (reset : List Wire) : AdaptiveCircuit :=
  .unitary [.X 836] ((sourceOuterAxis wires left List.nil).seq
    ((sourceOuterAxis wires right List.nil).seq
      (.unitary [.X 836] (measureResetWithCorrection reset (fun _ => [])))))

theorem outerPlan_round_run {n : Nat} (p : OuterPlan n) (left right : List AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hl : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) p.left.toList left)
    (hr : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) p.right.toList right)
    (start : Nat) (history : Fin start → Bool) :
    ((p.round start).instantiate read history).run = (sourceOuterRound p.wires.toList left right p.reset).run := by
  have htail (cursor : Nat) (history : Fin cursor → Bool) :
      ((Straight.gate (.literal (.X 836)) (resetProgram n cursor p.reset)).instantiate read history).run =
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection p.reset (fun _ => []))).run := by
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.run,resetProgram_run]
  have hright (cursor : Nat) (history : Fin cursor → Bool) :
      (((outerAxis p.wires p.right.toList cursor List.nil).append
        (.gate (.literal (.X 836)) (resetProgram n (cursor+axisCount p.right.toList) p.reset))).instantiate read history).run =
        ((sourceOuterAxis p.wires.toList right List.nil).seq
          (.unitary [.X 836] (measureResetWithCorrection p.reset (fun _ => [])))).run := by
    rw [append_run_fixed _ _ _ _ _ (htail _),AdaptiveCircuit.run_seq,outerAxis_run _ _ _ _ hr]
    simp only [List.map_nil,AdaptiveCircuit.run_seq]
  simp only [OuterPlan.round,castFinish_instantiate,Straight.instantiate,TemplateGate.instantiate,sourceOuterRound,AdaptiveCircuit.run]
  congr 1
  rw [append_run_fixed _ _ _ _ _ (hright _),AdaptiveCircuit.run_seq,outerAxis_run _ _ _ _ hl]
  simp only [List.map_nil,AdaptiveCircuit.run_seq]

theorem outerPlan_repeat_run {n : Nat} (p : OuterPlan n) (source : AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hround : ∀ start history, ((p.round start).instantiate read history).run = source.run)
    (count start : Nat) (history : Fin start → Bool) :
    ((p.repeat count start).instantiate read history).run = (repeatWindowProgram source count).run := by
  induction count generalizing start with
  | zero => simp only [OuterPlan.repeat,castFinish_instantiate,repeatWindowProgram,Straight.instantiate]
  | succ k ih =>
    simp only [OuterPlan.repeat,castFinish_instantiate,repeatWindowProgram]
    rw [append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,hround,← AdaptiveCircuit.run_seq]

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ActualExecution ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ActualExecution.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

noncomputable def actualFirstSource (Q : Point) : AdaptiveCircuit :=
  physicalPointLookup (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
    ((2^(16*15)) • G))
noncomputable def actualOddSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (ipxWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide))
noncomputable def actualLeftSources (Q : Point) : List AdaptiveCircuit :=
  actualFirstSource Q :: List.ofFn (fun k : Fin 15 => actualOddSource Q (.left ⟨14-k.val,by omega⟩))
noncomputable def actualRightSources (Q : Point) : List AdaptiveCircuit :=
  List.ofFn (fun k : Fin 13 => actualOddSource Q (.right ⟨12-k.val,by omega⟩))
noncomputable def actualRoundSource (Q : Point) : AdaptiveCircuit :=
  sourceOuterRound streamAddress.reverse (actualLeftSources Q) (actualRightSources Q) resetWires

private theorem forall₂_ofFn {α β : Type} (R : α → β → Prop) {n : Nat}
    (a : Fin n → α) (b : Fin n → β) (h : ∀ i, R (a i) (b i)) : List.Forall₂ R (List.ofFn a) (List.ofFn b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih _ _ (fun i => h i.succ))

theorem actualLeftSources_run (Q : Point) (hQ : order • Q=0) :
    List.Forall₂ (fun w c => ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).run = c.run)
      ipxLeftWindows (actualLeftSources Q) := by
  apply List.Forall₂.cons
  · exact fun start history => actualFirstWindow_run start Q hQ history
  · apply forall₂_ofFn
    intro k start history
    exact actualIpxWindow_run _ start Q hQ history

theorem actualRightSources_run (Q : Point) (hQ : order • Q=0) :
    List.Forall₂ (fun w c => ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).run = c.run)
      ipxRightWindows (actualRightSources Q) := by
  apply forall₂_ofFn
  intro k start history
  exact actualIpxWindow_run _ start Q hQ history

attribute [local irreducible] ipxLeftWindows ipxRightWindows actualLeftSources actualRightSources

theorem ipxOuterPlan_round_run (Q : Point) (hQ : order • Q=0) (start : Nat) (history : Fin start → Bool) :
    ((ipxOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run =
      (actualRoundSource Q).run := by
  exact outerPlan_round_run ipxOuterPlan _ _ _ (actualLeftSources_run Q hQ) (actualRightSources_run Q hQ) start history

attribute [local irreducible] ipxOuterPlan actualRoundSource

theorem ipxOuterPlan_repeat_run (Q : Point) (hQ : order • Q=0) (count start : Nat) (history : Fin start → Bool) :
    ((ipxOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run =
      (repeatWindowProgram (actualRoundSource Q) count).run :=
  outerPlan_repeat_run _ _ _ (ipxOuterPlan_round_run Q hQ) count start history

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/TaggedProbability ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/TaggedProbability.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] fourierOutcomes streamAddress

/-- A terminal instrument may depend on Fourier outcomes, but not erased arithmetic records. -/
noncomputable def fourierContinuationInstrument (prior : List Bool) (next : List Bool → Instrument) : Instrument :=
  (fourierOutcomes 16).flatMap (fun bits => (next bits).map
    (fun b => InstrumentBranch.seq ⟨bits,fourierBranch .inverse streamAddress.reverse prior bits⟩ b))

noncomputable def streamBlockContinuation (call : AdaptiveCircuit) (prior : List Bool)
    (next : List Bool → Instrument) : Instrument :=
  (streamBlockOutcomes call prior).flatMap (fun tagged => (next tagged.1).map (tagged.2.seq))

theorem streamBlockContinuation_eq (call : AdaptiveCircuit) (prior : List Bool)
    (next : List Bool → Instrument) :
    streamBlockContinuation call prior next =
      (AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).run.seq
        (call.run.seq (fourierContinuationInstrument prior next)) := by
  simp only [streamBlockContinuation,streamBlockOutcomes,AdaptiveCircuit.run_seq,
    Instrument.seq,fourierContinuationInstrument,
    show streamAddress.length=16 from by simp [streamAddress],
    List.flatMap_assoc,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro b hb
  apply List.flatMap_congr
  intro bits hbits
  apply List.map_congr_left
  intro c hc
  cases a; cases b; cases c
  simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem unitary_done_seq_bornMass (c : Circuit) (J : Instrument) (ψ : State) :
    ((AdaptiveCircuit.unitary c .done).run.seq J).bornMass ψ = J.bornMass (Quantum.run c ψ) := by
  simp only [AdaptiveCircuit.run,Instrument.seq,List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,
    List.append_nil,Instrument.bornMass,List.map_map,Function.comp_def,InstrumentBranch.seq,LinearMap.comp_apply]
  rfl

/-- Eliminate all arithmetic measurement branches before a Fourier-dependent continuation. -/
theorem streamBlockContinuation_mass {call : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop} (h : CoherentlyImplementsOn call ideal Valid)
    (prior : List Bool) (next : List Bool → Instrument) (ψ : State)
    (hs : SupportedOn Valid (Quantum.run (streamAddress.map Gate.H) ψ)) :
    (streamBlockContinuation call prior next).bornMass ψ =
      (fourierContinuationInstrument prior next).bornMass
        (ideal (Quantum.run (streamAddress.map Gate.H) ψ)) := by
  rw [streamBlockContinuation_eq]
  rw [unitary_done_seq_bornMass]
  exact h.terminalMass hs _


theorem fourierContinuationInstrument_mass (prior : List Bool)
    (next : List Bool → Instrument) (ψ : State) :
    (fourierContinuationInstrument prior next).bornMass ψ =
      ((fourierOutcomes 16).map (fun bits =>
        (next bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ))).sum := by
  simp only [fourierContinuationInstrument, Instrument.bornMass, List.map_flatMap,
    List.map_map, Function.comp_def, InstrumentBranch.seq,
    LinearMap.comp_apply]
  generalize fourierOutcomes 16 = outcomes
  induction outcomes with
  | nil => rfl
  | cons a outcomes ih => simpa only [List.flatMap_cons, List.sum_append,
      List.map_cons, List.sum_cons] using congrArg (_ + ·) ih

/-- A continuation replacement only needs equality on the reached Fourier states. -/
theorem fourierContinuationInstrument_mass_congr (prior : List Bool)
    (next next' : List Bool → Instrument) (ψ : State)
    (h : ∀ bits ∈ fourierOutcomes 16,
      (next bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ) =
      (next' bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ)) :
    (fourierContinuationInstrument prior next).bornMass ψ =
      (fourierContinuationInstrument prior next').bornMass ψ := by
  rw [fourierContinuationInstrument_mass, fourierContinuationInstrument_mass]
  congr 1
  exact List.map_congr_left h
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/AxisProbability ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/AxisProbability.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

noncomputable def selectedSourceAxis (call : OddWindow → AdaptiveCircuit) :
    List OddWindow → List Bool → (List Bool → Instrument) → Instrument
  | [], prior, terminal => terminal prior
  | w :: ws, prior, terminal =>
      streamBlockContinuation (call w) prior
        (fun bits => selectedSourceAxis call ws (bits.reverse ++ prior) terminal)

noncomputable def selectedIdealAxis (Q : Point) :
    List OddWindow → List Bool → (List Bool → Instrument) → Instrument
  | [], prior, terminal => terminal prior
  | w :: ws, prior, terminal =>
      (fourierContinuationInstrument prior
        (fun bits => selectedIdealAxis Q ws (bits.reverse ++ prior) terminal)).map
        (fun b => InstrumentBranch.seq
          ⟨[], (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)).comp
            (Quantum.run (streamAddress.map Gate.H))⟩ b)

theorem selectedIdealAxis_cons_mass (Q : Point) (w : OddWindow) (ws : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) (ψ : State) :
    (selectedIdealAxis Q (w :: ws) prior terminal).bornMass ψ =
      (fourierContinuationInstrument prior
        (fun bits => selectedIdealAxis Q ws (bits.reverse ++ prior) terminal)).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
  simp only [selectedIdealAxis,Instrument.bornMass,List.map_map,Function.comp_def,
    InstrumentBranch.seq,LinearMap.comp_apply]

/-- All arithmetic records may be summed out, including before an arbitrary selected terminal event. -/
theorem selectedSourceAxis_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (call : OddWindow → AdaptiveCircuit) (ws : List OddWindow)
    (hcall : ∀ w ∈ ws, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)) BatchedWindowValid)
    (prior : List Bool) (terminal : List Bool → Instrument)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedSourceAxis call ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal).bornMass ψ := by
  induction ws generalizing prior ψ with
  | nil => rfl
  | cons w ws ih =>
    rw [selectedSourceAxis,streamBlockContinuation_mass (hcall w (by simp)) _ _ _
      (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ),selectedIdealAxis_cons_mass]
    apply fourierContinuationInstrument_mass_congr
    intro bits hbits
    apply ih (fun v hv => hcall v (List.mem_cons_of_mem w hv))
    apply batchedWindowValid_fourierBranch
    · intro v hv
      simpa only [List.mem_reverse] using hv
    · exact actualIpxWindowState_supported Q hQ hn w _
        (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ)


theorem selectedSourceAxis_constant (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow) (prior : List Bool) (tail : AdaptiveCircuit) :
    selectedSourceAxis call ws prior (fun _ => tail.run) =
      (streamAxis (ws.map call) prior tail).run := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih =>
    simp only [selectedSourceAxis,List.map_cons,streamAxis_cons_run,
      streamBlockContinuation,ih]
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/TwoAxisProbability ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/TwoAxisProbability.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

theorem selectedIdealAxis_terminal_congr (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (ws : List OddWindow) (prior : List Bool)
    (terminal terminal' : List Bool → Instrument)
    (he : ∀ prior ψ, SupportedOn BatchedWindowValid ψ →
      (terminal prior).bornMass ψ = (terminal' prior).bornMass ψ)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedIdealAxis Q ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal').bornMass ψ := by
  induction ws generalizing prior ψ with
  | nil => exact he prior ψ hψ
  | cons w ws ih =>
    rw [selectedIdealAxis_cons_mass,selectedIdealAxis_cons_mass]
    apply fourierContinuationInstrument_mass_congr
    intro bits _
    apply ih
    apply batchedWindowValid_fourierBranch
    · intro v hv; simpa only [List.mem_reverse] using hv
    · exact actualIpxWindowState_supported Q hQ hn w _
        (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ)

theorem selectedSourceAxis_terminal_congr (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (call : OddWindow → AdaptiveCircuit) (ws : List OddWindow)
    (hcall : ∀ w ∈ ws, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)) BatchedWindowValid)
    (prior : List Bool) (terminal terminal' : List Bool → Instrument)
    (he : ∀ prior ψ, SupportedOn BatchedWindowValid ψ →
      (terminal prior).bornMass ψ = (terminal' prior).bornMass ψ)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedSourceAxis call ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal').bornMass ψ := by
  rw [selectedSourceAxis_mass Q hQ hn call ws hcall prior terminal ψ hψ]
  exact selectedIdealAxis_terminal_congr Q hQ hn ws prior terminal terminal' he ψ hψ

noncomputable def selectedSourceTwoAxes (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  streamBlockContinuation first List.nil (fun bits =>
    selectedSourceAxis call left bits.reverse (fun lhs =>
      selectedSourceAxis call right List.nil (terminal lhs)))

noncomputable def selectedIdealTwoAxes (Q : Point) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  (fourierContinuationInstrument List.nil (fun bits =>
    selectedIdealAxis Q left bits.reverse (fun lhs =>
      selectedIdealAxis Q right List.nil (terminal lhs)))).map
    (fun b => InstrumentBranch.seq
      ⟨List.nil, (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)).comp
        (Quantum.run (streamAddress.map Gate.H))⟩ b)

/-- Exact selected-event probability for both axes, with Fourier history reset between axes. -/
theorem selectedSourceTwoAxes_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (first : AdaptiveCircuit)
    (hfirst : CoherentlyImplementsOn first
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)) BatchedWindowValid)
    (terminal : List Bool → List Bool → Instrument)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    (selectedSourceTwoAxes first call left right terminal).bornMass ψ =
      (selectedIdealTwoAxes Q left right terminal).bornMass ψ := by
  rw [selectedSourceTwoAxes,streamBlockContinuation_mass hfirst _ _ _
    (firstWindowInput_prepare _ (fun _ h => h) ψ hψ)]
  have hm : (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      (fourierContinuationInstrument List.nil (fun bits =>
        selectedIdealAxis Q left bits.reverse (fun lhs =>
          selectedIdealAxis Q right List.nil (terminal lhs)))).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
    simp only [selectedIdealTwoAxes,Instrument.bornMass,List.map_map,Function.comp_def,
      InstrumentBranch.seq,LinearMap.comp_apply]
  rw [hm]
  apply fourierContinuationInstrument_mass_congr
  intro bits _
  apply selectedSourceAxis_terminal_congr Q hQ hn call left
    (fun w hw => hcall w (List.mem_append_left _ hw))
  · intro lhs φ hφ
    exact selectedSourceAxis_mass Q hQ hn call right
      (fun w hw => hcall w (List.mem_append_right _ hw)) List.nil (terminal lhs) φ hφ
  · apply batchedWindowValid_fourierBranch
    · intro v hv; simpa only [List.mem_reverse] using hv
    · exact actualFirstWindowState_supported Q _
        (firstWindowInput_prepare _ (fun _ h => h) ψ hψ)



theorem selectedSourceTwoAxes_constant (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (tail : AdaptiveCircuit) :
    selectedSourceTwoAxes first call left right (fun _ _ => tail.run) =
      (streamAxis (first :: left.map call) List.nil
        (streamAxis (right.map call) List.nil tail)).run := by
  simp only [selectedSourceTwoAxes,selectedSourceAxis_constant,
    streamAxis_cons_run,streamBlockContinuation,List.append_nil]

theorem actualOddSource_coherent (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) :
    CoherentlyImplementsOn (actualOddSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)) BatchedWindowValid := by
  have h := actualIpxWindow_coherent Q hQ hn w 0 Fin.elim0
  unfold CoherentlyImplementsOn at h ⊢
  rw [actualIpxWindow_run w 0 Q hQ Fin.elim0] at h
  exact h

theorem actualFirstSource_coherent_input (Q : Point) (hQ : order • Q = 0) :
    CoherentlyImplementsOn (actualFirstSource Q)
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput := by
  have h := actualFirstWindow_coherent_input Q hQ 0 Fin.elim0
  unfold CoherentlyImplementsOn at h ⊢
  rw [actualFirstWindow_run 0 Q hQ Fin.elim0] at h
  exact h

theorem actualSourcesTwoAxes_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (left right : List OddWindow) (terminal : List Bool → List Bool → Instrument) :
    (selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right terminal).bornMass
      (ket (zeroBasisState[836 ↦ true])) =
    (selectedIdealTwoAxes Q left right terminal).bornMass (ket (zeroBasisState[836 ↦ true])) :=
  selectedSourceTwoAxes_mass Q hQ hn _ (actualFirstSource_coherent_input Q hQ)
    _ left right (fun w _ => actualOddSource_coherent Q hQ hn w) terminal _
    (supportedOn_ket _ _ firstWindowInput_start)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/FixedWord ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/FixedWord.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The evaluator reads exactly the supplied chronological bits, with its fixed LSB convention. -/
theorem readWord_of_actual_bits (history : List Bool) (positions : List Nat) (bits : List Bool)
    (h : positions.map (fun i => history[i]?) = bits.map some) :
    readWord history positions = some (fourierWordLSB bits) := by
  induction positions generalizing bits with
  | nil =>
    cases bits with
    | nil => rfl
    | cons b bits => simp at h
  | cons i positions ih =>
    cases bits with
    | nil => simp at h
    | cons b bits =>
      have hh : history[i]? = some b ∧
          positions.map (fun j => history[j]?) = bits.map some := by
        simpa only [List.map_cons,List.cons.injEq] using h
      simp only [readWord,hh.1,ih bits hh.2,fourierWordLSB]
      cases b <;> rfl

theorem actual_bits_range (before bits after : List Bool) :
    (List.range' before.length bits.length).map
      (fun i => (before ++ bits ++ after)[i]?) = bits.map some := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map,List.length_range'] at hi
    simp only [List.getElem_map,List.getElem_range']
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,Nat.one_mul]
    rw [List.getElem?_append_left hi,List.getElem?_eq_getElem hi]

theorem readWord_actual_range (before bits after : List Bool) :
    readWord (before ++ bits ++ after) (List.range' before.length bits.length) =
      some (fourierWordLSB bits) :=
  readWord_of_actual_bits _ _ _ (actual_bits_range before bits after)


/-- A transcript decomposition records each arithmetic prefix and the next sixteen Fourier bits. -/
inductive AxisTranscript {n : Nat} : List (OuterWindow n) → List Bool → List Bool → Prop
  | nil : AxisTranscript List.nil List.nil List.nil
  | cons (w : OuterWindow n) (ws : List (OuterWindow n)) (a bits rest out : List Bool)
      (ha : a.length = w.count) (hb : bits.length = 16)
      (ht : AxisTranscript ws rest out) :
      AxisTranscript (w :: ws) (a ++ bits ++ rest) (bits ++ out)

theorem AxisTranscript.actual_bits {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits)
    (before after : List Bool) :
    (axisPositions ws before.length).map (fun i => (before ++ history ++ after)[i]?) =
      bits.map some := by
  induction h generalizing before with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    rw [axisPositions,List.map_append,List.map_append]
    have hhead := actual_bits_range (before ++ a) bs (rest ++ after)
    have htail := ih (before ++ a ++ bs)
    simp only [List.length_append,ha,hb,List.append_assoc] at hhead htail
    simp only [List.append_assoc,Nat.add_assoc]
    rw [hhead,htail]

theorem AxisTranscript.readWord {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits)
    (before after : List Bool) :
    ShorECDLP.Challenge.readWord (before ++ history ++ after) (axisPositions ws before.length) =
      some (fourierWordLSB bits) :=
  readWord_of_actual_bits _ _ _ (h.actual_bits before after)


/-- Transcript blocks are obtained from the actual straight execution, not supplied as an assumption. -/
theorem outerAxis_transcript {n : Nat} (wires : Vector Wire 16)
    (ws : List (OuterWindow n)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((outerAxis wires ws start prior).instantiate read history).run) :
    ∃ bits, AxisTranscript ws b.history bits := by
  induction ws generalizing start b with
  | nil =>
    simp only [outerAxis,Straight.instantiate,AdaptiveCircuit.run,List.mem_singleton] at hb
    subst b
    exact ⟨[],AxisTranscript.nil⟩
  | cons w ws ih =>
    simp only [outerAxis,castFinish_instantiate] at hb
    obtain ⟨h₁,a,rest,ha,hr,he₁,rfl⟩ := straight_append_branch _ _ read history b hb
    obtain ⟨h₂,f,c,hf,hc,he₂,rfl⟩ := straight_append_branch _ _ read h₁ rest hr
    obtain ⟨bits,hbits⟩ := ih _ _ h₂ c hc
    have hla : a.history.length = w.count := by
      have h := straight_history_length _ read history a ha
      omega
    have hlf : f.history.length = 16 := by
      have h := straight_history_length _ read h₁ f hf
      omega
    refine ⟨f.history ++ bits,?_⟩
    simpa only [InstrumentBranch.seq,List.append_assoc] using
      AxisTranscript.cons w ws a.history f.history c.history bits hla hlf hbits

theorem outerAxis_readWord {n : Nat} (wires : Vector Wire 16)
    (ws : List (OuterWindow n)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((outerAxis wires ws start prior).instantiate read history).run)
    (suffix : List Bool) :
    ∃ bits, AxisTranscript ws b.history bits ∧
      readWord (List.ofFn history ++ b.history ++ suffix) (axisPositions ws start) =
        some (fourierWordLSB bits) := by
  obtain ⟨bits,h⟩ := outerAxis_transcript wires ws start prior read history b hb
  exact ⟨bits,h,by simpa only [List.length_ofFn] using h.readWord (List.ofFn history) suffix⟩


theorem AxisTranscript.bits_length {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits) :
    bits.length = ws.length * 16 := by
  induction h with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    simp only [List.length_append,List.length_cons,hb,ih,Nat.add_mul]
    omega

theorem OuterPlan.round_actualWords {n : Nat} (p : OuterPlan n) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.round start).instantiate read history).run) (suffix : List Bool) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.left.toList start) = some (fourierWordLSB left) ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.right.toList (start + axisCount p.left.toList)) =
          some (fourierWordLSB right) := by
  simp only [OuterPlan.round,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.run] at hb
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hb
  obtain ⟨h₁,a,rest,ha,hr,he₁,rfl⟩ := straight_append_branch _ _ read history d hd
  obtain ⟨h₂,f,c,hf,hc,he₂,rfl⟩ := straight_append_branch _ _ read h₁ rest hr
  obtain ⟨left,hl,hlread⟩ := outerAxis_readWord p.wires p.left.toList start List.nil
    read history a ha (f.history ++ c.history ++ suffix)
  obtain ⟨right,hr,hrread⟩ := outerAxis_readWord p.wires p.right.toList _ List.nil
    read h₁ f hf (c.history ++ suffix)
  refine ⟨left,right,?_,?_,?_,?_⟩
  · simpa using hl.bits_length
  · simpa using hr.bits_length
  · change readWord (List.ofFn history ++ (a.seq (f.seq c)).history ++ suffix) _ = _
    simpa only [InstrumentBranch.seq,List.append_assoc] using hlread
  · change readWord (List.ofFn history ++ (a.seq (f.seq c)).history ++ suffix) _ = _
    simpa only [he₁,InstrumentBranch.seq,List.append_assoc] using hrread



theorem OuterPlan.repeat_actualWords {n : Nat} (p : OuterPlan n) (count start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.repeat count start).instantiate read history).run)
    (r : Nat) (hr : r < count) (suffix : List Bool) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.left.toList (start + r*p.stride)) = some (fourierWordLSB left) ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.right.toList (start + r*p.stride + axisCount p.left.toList)) =
          some (fourierWordLSB right) := by
  induction count generalizing start b r with
  | zero => omega
  | succ count ih =>
    simp only [OuterPlan.repeat,castFinish_instantiate] at hb
    obtain ⟨h₁,a,c,ha,hc,he,rfl⟩ := straight_append_branch _ _ read history b hb
    cases r with
    | zero =>
      simpa only [Nat.zero_mul,Nat.add_zero,InstrumentBranch.seq,List.append_assoc] using
        p.round_actualWords start read history a ha (c.history ++ suffix)
    | succ r =>
      have h := ih (start+p.stride) h₁ c hc r (by omega)
      simpa only [he,InstrumentBranch.seq,List.append_assoc,Nat.succ_mul,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem OuterPlan.entry_actualWords (coefficients : List PointCoeff)
    (p : OuterPlan coefficients.length) (Q : Secp256k1.Point)
    (b : InstrumentBranch) (hb : b ∈ ((p.entry coefficients).instantiate Q).run) (r : Fin 56) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord b.history (p.positions r).left.toList = some (fourierWordLSB left) ∧
      readWord b.history (p.positions r).right.toList = some (fourierWordLSB right) := by
  simp only [OuterPlan.entry,StraightEntry.instantiate,castFinish_instantiate] at hb
  have h := p.repeat_actualWords 56 0 (readConstant coefficients.get Q) Fin.elim0 b hb r.val r.isLt List.nil
  simpa only [OuterPlan.positions,Vector.toList,List.toList_toArray,List.ofFn_zero,
    List.nil_append,List.append_nil,Nat.zero_add] using h
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowBranchSum ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowBranchSum.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. The per-round lower
bound `wrappedIdeal_mass_lower` is now the averaged bound `27/50` of `AveragedSuccess` instead of
the protected pointwise bound `163/1000`. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1
noncomputable section
attribute [local irreducible] fourierOutcomes actualIpxWindowState

/-- Physical Fourier coefficients retain the full previous measurement history. -/
theorem branchCoeff_amplitude (dir : PhaseDir) (ws : List Wire)
    (hws : ws.Nodup) (prior bs : List Bool) (s : BasisState) :
    fourierBranchCoeff dir ws prior bs s = fourierBitAmplitude dir (ws.map s) prior bs := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [fourierBranchCoeff, List.map_cons, fourierBitAmplitude]
      rw [ih hws.tail]
      have hm : ws.map (s[w ↦ false]) = ws.map s := by
        apply List.map_congr_left
        intro v hv
        have hvw : v ≠ w := by intro he; subst v; exact (List.nodup_cons.mp hws).1 hv
        simp [upd, hvw]
      rw [hm]

theorem window_branch_uniform (dir : PhaseDir) (ws : List Wire) (hn : ws.Nodup)
    (f : BasisState → BasisState) (prior output : List Bool)
    (s : BasisState) (hz : Clean ws s)
    (hf : ∀ input ∈ fourierOutcomes ws.length,
      ws.map (f (phaseWordState ws input s)) = input) :
    fourierBranch dir ws.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ f (Quantum.run (ws.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ ws.length) •
        ((fourierOutcomes ws.length).map (fun input =>
          fourierBitAmplitude dir input.reverse prior output •
            ket (fourierClear ws.reverse (f (phaseWordState ws input s))))).sum := by
  classical
  rw [phaseHadamards_uniform ws hn s hz, map_smul, map_smul]
  congr 1
  simp only [phaseUniformSum, map_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [show Finsupp.lmapDomain ℂ ℂ f (ket (phaseWordState ws input s)) =
      ket (f (phaseWordState ws input s)) by simp [ket],
    fourierBranch_ket, branchCoeff_amplitude dir ws.reverse (List.nodup_reverse.mpr hn)]
  rw [List.map_reverse, hf input hi]

theorem phaseWordState_preserves (V : BasisState → Prop) (ws : List Wire)
    (hV : ∀ s, V s → ∀ w ∈ ws, ∀ b, V (s[w ↦ b]))
    (input : List Bool) (s : BasisState) (hs : V s) :
    V (phaseWordState ws input s) := by
  induction ws generalizing s input with
  | nil => exact hs
  | cons w ws ih =>
    cases input with
    | nil => exact hs
    | cons b input =>
      exact ih (fun t ht v hv c => hV t ht v (List.mem_cons_of_mem w hv) c)
        input _ (hV s hs w (by simp) b)

theorem actual_window_address_word (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : BatchedWindowValid s)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    streamAddress.map (actualIpxWindowState Q w (phaseWordState streamAddress input s)) = input := by
  have hv : BatchedWindowValid (phaseWordState streamAddress input s) :=
    phaseWordState_preserves BatchedWindowValid streamAddress
      (fun t ht v hv b => batchedWindowValid_address_update t ht v hv b) input s hs
  calc
    _ = streamAddress.map (phaseWordState streamAddress input s) := by
      apply List.map_congr_left
      intro v hva
      exact actualIpxWindowState_frame Q hQ hn w _ hv v
        ((show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hva)
    _ = input := phaseWordState_word streamAddress (by decide +kernel) input hi s

/-- Exact amplitude sum for an actual corrected window and one fixed Fourier
output. All input amplitudes are added before any Born mass is taken. -/
theorem actual_window_branch_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (prior output : List Bool) (s : BasisState)
    (hs : BatchedWindowValid s) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (fourierClear streamAddress.reverse
              (actualIpxWindowState Q w (phaseWordState streamAddress input s))))).sum := by
  simpa only [show streamAddress.length = 16 by decide +kernel] using
    window_branch_uniform .inverse streamAddress (by decide +kernel)
      (actualIpxWindowState Q w) prior output s hz
      (fun input hi => actual_window_address_word Q hQ hn w s hs input
        ((fourierOutcomes_mem _ _).mp hi))

theorem actual_first_address_word (Q : Point) (s : BasisState)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    streamAddress.map (actualFirstWindowState Q (phaseWordState streamAddress input s)) = input := by
  calc
    _ = streamAddress.map (phaseWordState streamAddress input s) := by
      apply List.map_congr_left
      intro v hva
      have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hva
      simp only [actualFirstWindowState, pointWrite, if_neg hp]
    _ = input := phaseWordState_word streamAddress (by decide +kernel) input hi s

/-- The first direct-load window obeys the same amplitude-sum rule, including
infinity rows in its mixed table. -/
theorem actual_first_branch_sum (Q : Point) (prior output : List Bool)
    (s : BasisState) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (fourierClear streamAddress.reverse
              (actualFirstWindowState Q (phaseWordState streamAddress input s))))).sum := by
  simpa only [show streamAddress.length = 16 by decide +kernel] using
    window_branch_uniform .inverse streamAddress (by decide +kernel)
      (actualFirstWindowState Q) prior output s hz
      (fun input hi => actual_first_address_word Q s input ((fourierOutcomes_mem _ _).mp hi))

theorem clear_assigned_point (ws : List Wire) (input : List Bool) (s : BasisState)
    (hz : Clean ws s) (hd : ∀ v ∈ ws, v ∉ pointLogicalWires) (P : Point) :
    fourierClear ws.reverse (pointWrite P (phaseWordState ws input s)) = pointWrite P s := by
  funext v
  rw [fourierClear_apply]
  by_cases hv : v ∈ ws
  · have hp := hd v hv
    simp only [List.mem_reverse, hv, if_true, pointWrite, if_neg hp]
    exact (hz v hv).symm
  · simp only [List.mem_reverse, hv, if_false, pointWrite]
    split
    · rfl
    · exact phaseWordState_frame ws input s v hv

theorem assigned_window_digit (input : List Bool) (hi : input.length = streamAddress.length)
    (s : BasisState) :
    windowRawDigit 0 (phaseWordState streamAddress input s) = boolWordToNat input := by
  have ha (t : BasisState) : tableAddressValue streamAddress t = windowRawDigit 0 t := by
    simp [streamAddress, tableAddressValue, windowRawDigit, windowAddressBits, windowBankStart,
      List.range', wireValues, boolWordToNat]
    omega
  rw [← ha]
  have word := phaseWordState_word streamAddress (by decide +kernel) input hi s
  change boolWordToNat (wireValues streamAddress (phaseWordState streamAddress input s)) = _
  rw [word]


theorem phaseWordState_pointWrite (ws : List Wire) (hd : ∀ w ∈ ws, w ∉ pointLogicalWires)
    (input : List Bool) (P : Point) (s : BasisState) :
    phaseWordState ws input (pointWrite P s) = pointWrite P (phaseWordState ws input s) := by
  induction ws generalizing input s with
  | nil => rfl
  | cons w ws ih =>
    cases input with
    | nil => rfl
    | cons b input =>
      have he : (pointWrite P s)[w ↦ b] = pointWrite P (s[w ↦ b]) := by
        funext v
        have hw := hd w (by simp)
        by_cases hv : v = w
        · subst v; simp [pointWrite, hw, upd]
        · by_cases hp : v ∈ pointLogicalWires <;> simp [pointWrite, hp, upd, hv]
      simp only [phaseWordState, he]
      exact ih (fun v hv => hd v (List.mem_cons_of_mem w hv)) input _

theorem assigned_point_coordinates (input : List Bool) (s : BasisState) (P : Point) :
    pointStateCoordinates (phaseWordState streamAddress input (pointWrite P s)) = fig14PointEncoding P := by
  rw [phaseWordState_pointWrite streamAddress (by decide +kernel), pointWrite_coordinates]

noncomputable def windowDigitPoint (Q : Point) : OddWindow → Nat → Point
  | .left j, digit => signedTableOdd 32768 digit •
      ((2 ^ (16 * j.val)) • signedWindowHalfPoint G order)
  | .right j, digit => signedTableOdd 32768 digit •
      ((2 ^ (16 * j.val)) • signedWindowHalfPoint Q order)

theorem actual_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualIpxWindowState Q w s = pointWrite (P + windowDigitPoint Q w (windowRawDigit 0 s)) s := by
  cases w with
  | left j => exact actual_left_window_digit Q hQ hn j s hs P hP
  | right j => exact actual_right_window_digit Q hQ hn j s hs P hP

theorem actual_window_assigned_clear (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (P : Point) (s : BasisState) (hs : FirstWindowInput s)
    (hz : Clean streamAddress s) (input : List Bool) (hi : input.length = streamAddress.length) :
    fourierClear streamAddress.reverse
      (actualIpxWindowState Q w (phaseWordState streamAddress input (pointWrite P s))) =
      pointWrite (P + windowDigitPoint Q w (boolWordToNat input)) s := by
  have hv : BatchedWindowValid (phaseWordState streamAddress input (pointWrite P s)) :=
    phaseWordState_preserves BatchedWindowValid streamAddress
      (fun t ht v hv b => batchedWindowValid_address_update t ht v hv b)
      input _ (firstWindowInput_pointWrite s hs P)
  have hc : Clean streamAddress (pointWrite P s) := by
    intro v hv
    have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hv
    simpa only [pointWrite, if_neg hp] using hz v hv
  rw [actual_window_digit Q hQ hn w _ hv.1 P (assigned_point_coordinates input s P),
    assigned_window_digit input hi,
    clear_assigned_point streamAddress input (pointWrite P s) hc (by decide +kernel)]
  funext v
  simp only [pointWrite]
  split <;> rfl

theorem actual_first_assigned_clear (Q : Point) (s : BasisState) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    fourierClear streamAddress.reverse (actualFirstWindowState Q (phaseWordState streamAddress input s)) =
      pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
        signedTableOdd 32768 (boolWordToNat input) •
          ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s := by
  rw [actual_first_window_digit, assigned_window_digit input hi,
    clear_assigned_point streamAddress input s hz (by decide +kernel)]

theorem actual_window_point_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (prior output : List Bool) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)
        (Quantum.run (streamAddress.map Gate.H) (ket (pointWrite P s)))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (P + windowDigitPoint Q w (boolWordToNat input)) s))).sum := by
  have hc : Clean streamAddress (pointWrite P s) := by
    intro v hv
    have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hv
    simpa only [pointWrite, if_neg hp] using hz v hv
  rw [actual_window_branch_sum Q hQ hn w prior output _
    (firstWindowInput_pointWrite s hs P) hc]
  apply congrArg (fun φ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) • φ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [actual_window_assigned_clear Q hQ hn w P s hs hz input
    (by simpa only [show streamAddress.length = 16 by decide +kernel] using (fourierOutcomes_mem 16 input).mp hi)]

theorem actual_first_point_sum (Q : Point) (prior output : List Bool)
    (s : BasisState) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
              signedTableOdd 32768 (boolWordToNat input) •
                ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s))).sum := by
  rw [actual_first_branch_sum Q prior output s hz]
  apply congrArg (fun φ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) • φ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [actual_first_assigned_clear Q s hz input
    (by simpa only [show streamAddress.length = 16 by decide +kernel] using (fourierOutcomes_mem 16 input).mp hi)]

/-- Fixed Fourier outputs for an axis, before the terminal event is selected. -/
noncomputable def actualAxisBranch (Q : Point) :
    List (OddWindow × List Bool) → List Bool → State →ₗ[ℂ] State
  | [], _ => LinearMap.id
  | (w, output) :: windows, prior =>
      (actualAxisBranch Q windows (output.reverse ++ prior)).comp
        ((fourierBranch .inverse streamAddress.reverse prior output).comp
          ((Finsupp.lmapDomain ℂ ℂ (actualIpxWindowState Q w)).comp
            (Quantum.run (streamAddress.map Gate.H))))

/-- The exact coherent point-state sum, retaining interference between inputs. -/
noncomputable def pointAxisKernel (Q : Point) (s : BasisState) :
    List (OddWindow × List Bool) → List Bool → Point → State
  | [], _, P => ket (pointWrite P s)
  | (w, output) :: windows, prior, P =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            pointAxisKernel Q s windows (output.reverse ++ prior)
              (P + windowDigitPoint Q w (boolWordToNat input)))).sum

/-- Induction over the actual windows reduces execution to a coherent point sum;
there is no classical mixture over inputs and no exceptional-event loss. -/
theorem actualAxisBranch_point (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (windows : List (OddWindow × List Bool)) (prior : List Bool) (P : Point) :
    actualAxisBranch Q windows prior (ket (pointWrite P s)) =
      pointAxisKernel Q s windows prior P := by
  induction windows generalizing prior P with
  | nil => rfl
  | cons w windows ih =>
    simp only [actualAxisBranch, LinearMap.comp_apply]
    rw [actual_window_point_sum Q hQ hn w.1 prior w.2 P s hs hz]
    simp only [map_smul, map_list_sum, List.map_map, Function.comp_def, ih, pointAxisKernel]

noncomputable def windowOutputPaths : List OddWindow → List (List (OddWindow × List Bool))
  | [] => [[]]
  | w :: windows => (fourierOutcomes 16).flatMap (fun bits =>
      (windowOutputPaths windows).map (fun path => (w, bits) :: path))

theorem selectedIdealAxis_paths (Q : Point) (windows : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) :
    selectedIdealAxis Q windows prior terminal =
      (windowOutputPaths windows).flatMap (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).map (fun b =>
          InstrumentBranch.seq ⟨(path.map Prod.snd).flatten, actualAxisBranch Q path prior⟩ b)) := by
  induction windows generalizing prior with
  | nil =>
    simp only [selectedIdealAxis, windowOutputPaths, List.flatMap_cons, List.flatMap_nil,
      List.map_nil, List.flatten_nil, List.reverse_nil, List.nil_append, List.append_nil,
      actualAxisBranch]
    apply Eq.symm
    exact List.map_id' _
  | cons w windows ih =>
    simp only [selectedIdealAxis, fourierContinuationInstrument, ih, windowOutputPaths,
      List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_map,
      Function.comp_def, List.map_cons, List.flatten_cons, List.reverse_append,
      List.append_assoc, actualAxisBranch]
    apply List.flatMap_congr
    intro output ho
    apply List.flatMap_congr
    intro path hp
    apply List.map_congr_left
    intro b hb
    cases b
    simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem selectedIdealAxis_paths_mass (Q : Point) (windows : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) (ψ : State) :
    (selectedIdealAxis Q windows prior terminal).bornMass ψ =
      ((windowOutputPaths windows).map (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).bornMass
          (actualAxisBranch Q path prior ψ))).sum := by
  rw [selectedIdealAxis_paths]
  simp only [Instrument.bornMass, List.map_flatMap, List.map_map,
    Function.comp_def, InstrumentBranch.seq, LinearMap.comp_apply]
  generalize windowOutputPaths windows = paths
  induction paths with
  | nil => rfl
  | cons path paths ih =>
    simpa only [List.flatMap_cons, List.map_cons, List.sum_cons, List.sum_append] using
      congrArg (_ + ·) ih

theorem selectedIdealAxis_point_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (windows : List OddWindow) (prior : List Bool) (terminal : List Bool → Instrument)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealAxis Q windows prior terminal).bornMass (ket (pointWrite P s)) =
      ((windowOutputPaths windows).map (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).bornMass
          (pointAxisKernel Q s path prior P))).sum := by
  rw [selectedIdealAxis_paths_mass]
  simp only [actualAxisBranch_point Q hQ hn s hs hz]

end
end ShorECDLP.Paper2607_13816.ChallengeMigration

end
