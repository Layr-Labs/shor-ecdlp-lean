import ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation
import ShorECDLP.Submission.Entrant.Streaming.Resources
import ShorECDLP.Submission.«2607_13816».Window.StreamKernel
import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Framework.Quantum.TerminalInterference
import ShorECDLP.Submission.«2607_13816».Window.Uniform
import ShorECDLP.Submission.«2607_13816».Window.SignedAddress
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
import ShorECDLP.Submission.«2607_13816».Challenge.Reindex
import ShorECDLP.Challenge.Decoder
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Challenge.Resources

section

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
  have hfirst : CoherentlyImplementsOn (signedLookupCoordinateProgram xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    restrictCoherent (signedLookupCoordinateProgram_coherent xs ys) (fun s hs => hs.1.1)
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
attribute [local irreducible] divisionProgram multiplicationProgram
theorem zeroDivisionProgram_wellFormed (n start : Nat) : (zeroDivisionProgram n start).2.WellFormed :=
  surroundCompiled_wellFormed _ _ _ fig15ZeroPrepare_wellFormed fig15ZeroRestore_wellFormed (divisionProgram_wellFormed _ _)

theorem zeroMultiplicationProgram_wellFormed (n start : Nat) : (zeroMultiplicationProgram n start).2.WellFormed :=
  surroundCompiled_wellFormed _ _ _ fig15ZeroPrepare_wellFormed fig15ZeroRestore_wellFormed (multiplicationProgram_wellFormed _ _)

attribute [local irreducible] squareSubtractProgram

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

attribute [local irreducible] zeroDivisionProgram zeroMultiplicationProgram pointSquareProgram signedFieldProgram xNegateProgram

theorem coordinateProgram_wellFormed (start : Nat) : (coordinateProgram start).2.WellFormed := by
  unfold coordinateProgram
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [coordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fieldLookupXProgram_wellFormed _ _
  · exact signedFieldProgram_wellFormed _ _
  · exact zeroDivisionProgram_wellFormed _ _
  · exact pointSquareProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact zeroMultiplicationProgram_wellFormed _ _
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
attribute [local irreducible] coordinateProgram

theorem sharedCoordinateProgram_wellFormed (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).2.WellFormed :=
  (reindexCompiled_wellFormed _ _).mpr (coordinateProgram_wellFormed start)

attribute [local irreducible] sharedCoordinateProgram sharedYNegateProgram ipxProgram

theorem ipxWindowCore_wellFormed (w : OddWindow) (start : Nat) :
    (ipxWindowCore w start).2.WellFormed := by
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [ipxWindowSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact sharedCoordinateProgram_wellFormed _ _
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
Moved into the editable Entrant tree; module imports renamed accordingly. -/

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
end

section

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

noncomputable def coordinateSources (Q : Point) (coeffs : Fin 32768 → PointCoeff) : List AdaptiveCircuit :=
  [fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .negX),
   signedPointLookupY (fun l => baseFieldValue (tablePoint coeffs Q l) .negY),
   secp256k1ZeroAllowedDivision, fig14SquareSubtract,
   fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .tripleX),
   secp256k1ZeroAllowedMultiplication, fig14Negate,
   fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .x),
   signedPointLookupY (fun l => baseFieldValue (tablePoint coeffs Q l) .negY)]

theorem coordinateSources_eq (Q : Point) (coeffs : Fin 32768 → PointCoeff) :
    sequenceCircuit (coordinateSources Q coeffs) =
      signedLookupCoordinateProgram (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y) := by
  have hx (P : Point) : baseFieldValue P .x = fieldValue P .x := rfl
  have hn (P : Point) : baseFieldValue P .negX = fieldValue P .negX := rfl
  have hy (P : Point) : baseFieldValue P .negY = fieldValue P .negY := rfl
  have ht (P : Point) : baseFieldValue P .tripleX = fieldValue P .tripleX := rfl
  simp only [coordinateSources, hx, hn, hy, ht, sequenceCircuit, signedLookupCoordinateProgram,
    adaptive_seq_assoc, adaptive_seq_done, field_negX, field_negY, field_tripleX, field_x_mod]

theorem coordinateProgram_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (coordinateProgram start) (readConstant coeffs Q) history =
      (signedLookupCoordinateProgram (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y)).run := by
  unfold coordinateProgram
  rw [← coordinateSources_eq]
  apply sequenceProgram_run
  unfold coordinateSegments coordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fig14LookupX_compiled coeffs .negX cursor Q h
  · intro cursor h
    exact signedFieldProgram_run coeffs .negY cursor Q h
  · intro cursor h
    exact zeroDivisionProgram_run 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled coeffs .tripleX cursor Q h
  · intro cursor h
    exact zeroMultiplicationProgram_run 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled coeffs .x cursor Q h
  · intro cursor h
    exact signedFieldProgram_run coeffs .negY cursor Q h

theorem coordinateProgram_tCount (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (coordinateProgram start) (readConstant coeffs Q) history =
      (signedLookupCoordinateProgram (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y)).tCount := by
  unfold coordinateProgram
  rw [← coordinateSources_eq]
  apply sequenceProgram_tCount
  unfold coordinateSegments coordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .negX _ cursor Q (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount coeffs .negY cursor Q h
  · intro cursor h
    exact zeroDivisionProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .tripleX _ cursor Q (by simp) h
  · intro cursor h
    exact zeroMultiplicationProgram_tCount 32768 cursor _ h
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
attribute [local irreducible] coordinateProgram yNegateProgram
  ipxProgramOf sequenceProgram surroundCompiled relabelCompiled

theorem correction_count (start : Nat) :
    (ipxProgramOf tableRows batchWindowTree pointLookupPath start).1 = 425971 := by
  simp only [ipxProgramOf]
  rw [ipxOps_measurements _ _ _ ipxTree_layout, ipxSchedule_queries, batchWindowTree_nodes]

@[irreducible] def placedProgram (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  ipxProgramOf tableRows batchWindowTree pointLookupPath start

theorem placedProgram_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (placedProgram start) (readConstant coeffs Q) history =
      (placedBatchSource coeffs Q).run := by
  unfold placedProgram compiledRun
  simp only [ipxProgramOf, lookupProgram_run, ipxOps_source, placedBatchSource]

def segments : List (FixedSegment 32768) :=
  [coordinateProgram, yNegateProgram, placedProgram, yNegateProgram]

@[irreducible] noncomputable def sources (coeffs : Fin 32768 → PointCoeff) (Q : Point) : List AdaptiveCircuit :=
  [signedLookupCoordinateProgram (fun l => fieldValue (tablePoint coeffs Q l) .x)
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
  · intro cursor h; exact coordinateProgram_run coeffs cursor Q h
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

theorem coordinate_count (start : Nat) : (coordinateProgram start).1 = 30272702 := by
  have h := sharedCoordinateProgram_count (.right ⟨0, by decide⟩) start
  simpa only [sharedCoordinateProgram, reindexCompiled] using h

theorem negate_count (start : Nat) : (yNegateProgram start).1 = 1022 := by
  have h := sharedYNegateProgram_count (.right ⟨0, by decide⟩) start
  simpa only [sharedYNegateProgram, reindexCompiled] using h

theorem placed_count (start : Nat) : (placedProgram start).1 = 425971 := by
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

theorem core_count (start : Nat) : (core start).1 = 30700717 := by
  have h := sequence_count 32768 segments ([30272702, 1022, 425971, 1022] : List Nat) (by
    unfold segments
    exact List.Forall₂.cons coordinate_count (List.Forall₂.cons negate_count
      (List.Forall₂.cons placed_count (List.Forall₂.cons negate_count .nil)))) start
  unfold core
  exact h

theorem prepared_count (start : Nat) : (prepared start).1 = 30700717 := by
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
  have hfirst : CoherentlyImplementsOn (signedLookupCoordinateProgram xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    restrictCoherent (signedLookupCoordinateProgram_coherent xs ys) (fun s hs => hs.1.1)
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
  (65535, 16) :: List.replicate 7 (30700717, 16) ++ List.replicate 9 (30700717, 15)

@[irreducible] def rightMetadata : List (Nat × Nat) :=
  List.replicate 8 (30700717, 16) ++ List.replicate 9 (30700717, 15)

theorem left_widths : leftMetadata.map Prod.snd = widths := by
  simp [leftMetadata, widths]

theorem right_widths : rightMetadata.map Prod.snd = widths := by
  simp [rightMetadata, widths]

theorem left_record_count : recordCount leftMetadata = 491277270 := by
  norm_num [leftMetadata, recordCount, List.replicate]

theorem right_record_count : recordCount rightMetadata = 521912452 := by
  norm_num [rightMetadata, recordCount, List.replicate]

theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 263 := by
  rw [positions_length, left_widths, widths_sum]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 263 := by
  rw [positions_length, right_widths, widths_sum]

theorem projected_rows : 65536 + 15 * 32768 + 18 * 16384 = 851968 := by norm_num

theorem projected_records : 491277270 + 521912452 + 854 = 1013190576 := by norm_num

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
attribute [local irreducible] coordinateProgram yNegateProgram
  signedLookupCoordinateProgram placedBatchSource windowYNegate ipxProgramOf
  sequenceProgram surroundCompiled relabelCompiled

theorem actual_count : actual.count = 30700717 := by
  unfold actual closedWindow
  rfl

theorem placed_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (placedProgram start) (readConstant coeffs Q) history =
      (placedBatchSource coeffs Q).tCount := by
  unfold placedProgram compiledTCount
  simp only [ipxProgramOf, lookupProgram_tCount, ipxOps_source, placedBatchSource]

theorem batch_t (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    (placedBatchSource coeffs Q).tCount = 3067645 := by
  rw [placedBatchSource, ipxSourceOps_tCount _ _ _ _ ipxTree_layout, ipxSchedule_cost, batchWindowTree_nodes]

theorem sources_t (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    (sequenceCircuit (sources coeffs Q)).tCount = 513314039 := by
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
  · intro cursor h; exact coordinateProgram_tCount coeffs cursor Q h
  · intro cursor h; unfold windowYNegate; exact yNegateProgram_tCount cursor _ h
  · intro cursor h; exact placed_t coeffs cursor Q h
  · intro cursor h; unfold windowYNegate; exact yNegateProgram_tCount cursor _ h

theorem actual_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actual.program start).instantiate (readConstant coeffs Q) history).tCount = 513314039 := by
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

theorem signedWindow_count (w : SignedWindow) : (signedWindow w).count = 30700717 := by
  unfold signedWindow
  exact Physical.actual_count

theorem signedWindow_t (Q : Point) (w : SignedWindow) (start : Nat)
    (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 513314039 := by
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
  right := ⟨(positions rightMetadata 491277270).toArray, by
    simpa only [List.size_toArray, params] using right_positions_length 491277270⟩

def layout : DecodeLayout := ⟨.nearestPair, params, [trialPositions], by simp⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 491277270 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    491277270 ≤ i ∧ i < 1013189722 := by
  have h := positions_bounds rightMetadata 491277270 i
    (show i ∈ positions rightMetadata 491277270 from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/OuterProperties ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

def bodyT (count : Nat) : Nat := if count = 65535 then 458745 else 513314039

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

theorem left_count : axisCount leftWindows = 491277270 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 521912452 := by
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

theorem trialCount_eq : trialCount = 1013190576 := by
  rw [trialCount, left_count, right_count]

/-- One trial, with independent same-axis feedback histories and a final reset. -/
@[irreducible] def trial (start : Nat) : Straight 851968 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

@[irreducible] def program : Straight 851968 0 1013190576 :=
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
    (hb : b ∈ (program.instantiate read Fin.elim0).run) : b.history.length = 1013190576 := by
  exact straight_history_length program read Fin.elim0 b hb

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/BodyPhysical ====

section
namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] batchWindowTree
attribute [local irreducible] coordinateProgram yNegateProgram ipxProgramOf

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
  · exact coordinateProgram_wellFormed cursor
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

theorem placed_slots (start : Nat) : (placedProgram start).2.gateSlots ≤ 1183793236 := by
  unfold placedProgram
  simp only [ipxProgramOf, lookupProgram_slots]
  have h := ipxOps_slots_le tableRows batchWindowTree pointLookupPath ipxSchedule
  rw [ipxSlotBound_schedule, batchWindowTree_nodes] at h
  omega

theorem core_slots (start : Nat) : (core start).2.gateSlots ≤ 2683845980 := by
  have h := sequenceProgram_slots_le 32768 segments
    ([1500000000, 26372, 1183793236, 26372] : List Nat) (by
      unfold segments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
      · intro s; exact coordinateProgram_slots s
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
    (straightWires (coordinateProgram start).2).map (windowAddressPerm 855 (by decide)) ⊆
      completeBatchedSupport := by
  have h := sharedCoordinateProgram_support_static (.right ⟨0, by decide⟩) start
  simpa only [sharedCoordinateProgram, reindexCompiled_support] using h

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

theorem left_t_budget : metadataT leftMetadata 0 = 8213517822 := by
  norm_num [leftMetadata, metadataT, bodyT, List.replicate, fourierSlots]

theorem right_t_budget : metadataT rightMetadata 0 = 8726373116 := by
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
    ((axis leftWindows start List.nil).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 8213517822 := by
  have h := axis_t leftWindows (readConstant mixedCoefficientAt Q)
    (fun w hw => windows_t Q w (List.mem_append_left _ hw)) start List.nil history
  rwa [left_metadata, List.length_nil, left_t_budget] at h

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 8726373116 := by
  have h := axis_t rightWindows (readConstant mixedCoefficientAt Q)
    (fun w hw => windows_t Q w (List.mem_append_right _ hw)) start List.nil history
  rwa [right_metadata, List.length_nil, right_t_budget] at h

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 16939890938 := by
  unfold trial
  exact framed_t_le _ _ _ _ _ history 8213517822 8726373116
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
    (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).tCount ≤ 16939890938 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0

theorem program_measurements (read : ConstantBit 851968 → Bool) :
    (program.instantiate read Fin.elim0).measurementCount = 1013190576 := by
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
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).tModel ≤ 16939890938 ∧
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).measurements = 1013190576 :=
  ⟨program_qubits _, program_t Q, program_measurements _⟩

theorem table_rows_limit : mixedCoefficientTable.length ≤ 983040 := by
  rw [mixedCoefficientTable_length]
  norm_num

theorem one_candidate_check : layout.trials.length * decoderCandidateLimit layout.kind layout.params = 1 := by
  simp [layout, decoderCandidateLimit]

theorem resource_product : 855 * 16939890938 = 14483606751990 := by norm_num

end ShorECDLP.Entrant.Single

end
end
