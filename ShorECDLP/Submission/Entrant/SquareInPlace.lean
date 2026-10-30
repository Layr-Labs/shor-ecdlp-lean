import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlaceSupport
import ShorECDLP.Submission.«2607_13816».Challenge.InPlace
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWrapper
import ShorECDLP.Submission.«2607_13816».Challenge.Wrapper
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredStep
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapper
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleResources
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointStages
import ShorECDLP.Submission.«2607_13816».Window.PointStages
import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareResourceCounts
import ShorECDLP.Submission.«2607_13816».Challenge.Lookup
import ShorECDLP.Submission.«2607_13816».Challenge.Square

namespace ShorECDLP.Entrant.SquareInPlace
open Classical ShorECDLP ShorECDLP.Paper2607_13816
open ShorECDLP.Quantum (CoherentlyImplementsOn)
open ShorECDLP.Paper2607_13816.ChallengeMigration (adaptive_tCount_seq)
open ShorECDLP.Challenge (Straight ConstantBit)

private theorem geometry (input acc : List Wire) (copied c r t f : Wire)
    (hnd : ([copied,c,r,t,f] ++ input ++ acc).Nodup) :
    (∀ w ∈ [copied,c,r,t,f] ++ input, w ∉ acc) := by
  intro w hw ha
  exact (List.nodup_append.mp hnd).2.2 w hw w ha rfl

private theorem double_layout (input acc : List Wire) (copied c r t f : Wire)
    (hnd : ([copied,c,r,t,f] ++ input ++ acc).Nodup) :
    ([f,r,t,c] ++ acc ++ input).Nodup := by
  have hbase : ([c,r,t,f] ++ [] ++ input ++ acc).Nodup := (List.nodup_cons.mp hnd).2
  exact horner_double_layout [] input acc c r t f hbase

private theorem numeric_step (p A Y C m : Nat) (b : Bool) (hm : 0 < m) :
    ((2 * ((2 ^ (m - 1) * A + Y * C) % p)) % p + if b then Y else 0) % p =
      (2 ^ m * A + Y * (b.toNat + 2 * C)) % p := by
  have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mod_add_mod, h2]
  congr 1
  cases b <;> simp [Bool.toNat] <;> ring

/-- Horner square loop from an arbitrary canonical accumulator. -/
theorem loop_value (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (copied c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ q ∈ controls, q ∈ input)
    (hcopy : s copied = false) (hc : s c = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hx : boolWordToNat (wireValues input s) < p)
    (hA : boolWordToNat (wireValues (a :: rest) s) < p)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p) :
    boolWordToNat (wireValues (a :: rest) (squareLoopIdealState controls input (a :: rest) correction p copied c f s)) =
      (2 ^ (controls.length - 1) * boolWordToNat (wireValues (a :: rest) s) +
        boolWordToNat (wireValues input s) * boolWordToNat (wireValues controls s)) % p ∧
    ∀ w, w ∉ a :: rest → squareLoopIdealState controls input (a :: rest) correction p copied c f s w = s w := by
  have hp0 : 0 < p := by omega
  induction controls with
  | nil =>
    constructor
    · change boolWordToNat (wireValues (a :: rest) s) = _
      have h0 : boolWordToNat (wireValues ([] : List Wire) s) = 0 := rfl
      rw [h0, List.length_nil, Nat.zero_sub, pow_zero, Nat.one_mul, Nat.mul_zero, Nat.add_zero]
      exact (Nat.mod_eq_of_lt hA).symm
    · intro w hw; rfl
  | cons q qs ih =>
    have hq := hcontrols q (by simp)
    have hi := ih (fun w hw => hcontrols w (List.mem_cons_of_mem q hw))
    have hg := geometry input (a :: rest) copied c r t f hnd
    have hin : ∀ w ∈ input, w ∉ a :: rest := fun w hw => hg w (by simp [hw])
    by_cases hz : qs = []
    · subst qs
      have ha := squareAddIdealState_correct input (a :: rest) correction p q copied c r t f s
        hlen hk hnd hq hcopy hc hf hp hx hA hconstant
      change boolWordToNat (wireValues (a :: rest) (squareAddIdealState input (a :: rest) correction p q copied c f s)) = _ ∧ _
      refine ⟨?_,ha.2⟩
      rw [ha.1]
      cases hb : s q <;> simp [wireValues,boolWordToNat,hb]
    · let before := squareLoopIdealState qs input (a :: rest) correction p copied c f s
      have hbval : boolWordToNat (wireValues (a :: rest) before) =
          (2 ^ (qs.length - 1) * boolWordToNat (wireValues (a :: rest) s) +
            boolWordToNat (wireValues input s) * boolWordToNat (wireValues qs s)) % p := hi.1
      have hbframe : ∀ w, w ∉ a :: rest → before w = s w := hi.2
      have hcanonical : boolWordToNat (wireValues (a :: rest) before) < p := by rw [hbval]; exact Nat.mod_lt _ hp0
      have hshift : (c :: a :: rest).Nodup := List.nodup_cons.mpr
        ⟨hg c (by simp),(List.nodup_append.mp hnd).2.1⟩
      have hd := modularDoubleIdealState_correct a c rest correction p before hshift
        ((hbframe c (hg c (by simp))).trans hc) hk hp hcanonical hodd hconstant
      let ready := modularDoubleIdealState (a :: rest) correction p c before
      have hrframe : ∀ w, w ∉ a :: rest → ready w = s w := fun w hw => (hd.2 w hw).trans (hbframe w hw)
      have hrinput := horner_frame_word (a :: rest) input s ready hrframe hin
      have hrq : ready q = s q := hrframe q (hin q hq)
      have hrval : boolWordToNat (wireValues (a :: rest) ready) =
          (2 * ((2 ^ (qs.length - 1) * boolWordToNat (wireValues (a :: rest) s) +
            boolWordToNat (wireValues input s) * boolWordToNat (wireValues qs s)) % p)) % p :=
        hd.1.trans (by rw [hbval])
      have ha := squareAddIdealState_correct input (a :: rest) correction p q copied c r t f ready hlen hk hnd hq
        ((hrframe copied (hg copied (by simp))).trans hcopy) ((hrframe c (hg c (by simp))).trans hc)
        ((hrframe f (hg f (by simp))).trans hf) hp (by rw [hrinput]; exact hx)
        (by rw [hrval]; exact Nat.mod_lt _ hp0) hconstant
      have heq : squareLoopIdealState (q :: qs) input (a :: rest) correction p copied c f s =
          squareAddIdealState input (a :: rest) correction p q copied c f ready := by
        simp only [squareLoopIdealState,if_neg hz]; rfl
      rw [heq]
      refine ⟨?_,fun w hw => (ha.2 w hw).trans (hrframe w hw)⟩
      rw [ha.1,hrinput,hrq,hrval]
      have hlenpos : 0 < qs.length := List.length_pos_iff.mpr hz
      have hcv : boolWordToNat (wireValues (q :: qs) s) = (s q).toNat + 2 * boolWordToNat (wireValues qs s) := by
        simp [wireValues]
      rw [hcv, List.length_cons, Nat.add_sub_cancel]
      exact numeric_step p _ _ _ _ (s q) hlenpos


/-- The literal inverse loop undoes the forward loop from any canonical accumulator. -/
theorem inverse_after_forward (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (copied c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hm : (a :: rest).length = modulus.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ bit ∈ controls, bit ∈ input)
    (hcopy : s copied=false) (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hx : boolWordToNat (wireValues input s) < p)
    (hA : boolWordToNat (wireValues (a :: rest) s) < p)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (squareLoopInverse controls input (a :: rest) modulus p copied c r t f).run) :
    branch.kraus (Quantum.ket (squareLoopIdealState controls input (a :: rest) correction p copied c f s)) =
      Quantum.registerXResetMagnitude branch.history.length • Quantum.ket s := by
  have hp0 : 0 < p := by omega
  induction controls generalizing branch with
  | nil =>
    have hd := gidneyDoneBranch branch hb
    rw [hd.2,hd.1]
    simp [Quantum.registerXResetMagnitude,squareLoopIdealState]
  | cons q qs ih =>
    have htail : ∀ bit ∈ qs, bit ∈ input := fun w hw => hcontrols w (List.mem_cons_of_mem q hw)
    have hbit : q ∈ input := hcontrols q (by simp)
    by_cases hqs : qs = []
    · subst qs
      have hsub := squareSub_after_add input (a :: rest) correction modulus p q copied c r t f s
        hbit hlen (by simp) hk hm hnd hc hr ht hf hp hx hA hconstant hmodulus
      apply horner_seq_branch _ .done _ s s hsub ?_ branch hb
      intro b hb
      have hd := gidneyDoneBranch b hb
      rw [hd.2,hd.1]
      simp [Quantum.registerXResetMagnitude]
    · let before := squareLoopIdealState qs input (a :: rest) correction p copied c f s
      let doubled := modularDoubleIdealState (a :: rest) correction p c before
      have hi := loop_value qs input a rest correction p copied c r t f s
        hlen hk hnd htail hcopy hc hf hp hodd hx hA hconstant
      have hg (w : Wire) (hw : w ∈ [copied,c,r,t,f] ++ input) : w ∉ a::rest := by
        intro hh
        exact (List.nodup_append.mp hnd).2.2 w hw w hh rfl
      have hframe (w : Wire) (hw : w ∈ [copied,c,r,t,f] ++ input) : before w = s w := hi.2 w (hg w hw)
      have hvalue : boolWordToNat (wireValues (a :: rest) before) < p := by
        rw [hi.1]; exact Nat.mod_lt _ hp0
      have hdLayout := double_layout input (a :: rest) copied c r t f hnd
      have hshort := (doubling_layout (a :: rest) input f r t c hdLayout).1
      have hd := modularDoubleIdealState_correct a c rest correction p before hshort
        ((hframe c (by simp)).trans hc) hk hp hvalue hodd hconstant
      have hdframe (w : Wire) (hw : w ∈ [copied,c,r,t,f] ++ input) : doubled w = s w :=
        (hd.2 w (hg w hw)).trans (hframe w hw)
      have hdvalue : boolWordToNat (wireValues (a :: rest) doubled) < p := by
        rw [hd.1]; exact Nat.mod_lt _ hp0
      have hdinput : wireValues input doubled = wireValues input s :=
        List.map_congr_left (fun w hw => hdframe w (by simp [hw]))
      have hsub := squareSub_after_add input (a :: rest) correction modulus p q copied c r t f doubled
        hbit hlen (by simp) hk hm hnd ((hdframe c (by simp)).trans hc)
        ((hdframe r (by simp)).trans hr) ((hdframe t (by simp)).trans ht)
        ((hdframe f (by simp)).trans hf) hp (by rw [hdinput]; exact hx) hdvalue hconstant hmodulus
      have hhalve := modularHalve_branch_after_double a rest input correction modulus p f r t c before
        hk hm hlen.symm hdLayout ((hframe f (by simp)).trans hf)
        ((hframe r (by simp)).trans hr) ((hframe t (by simp)).trans ht)
        ((hframe c (by simp)).trans hc) hp hvalue hodd hconstant hmodulus
      simp only [squareLoopInverse,if_neg hqs] at hb
      change branch.kraus (Quantum.ket (squareAddIdealState input (a :: rest) correction p q copied c f (if qs = [] then before else doubled))) = _
      rw [if_neg hqs]
      apply horner_seq_branch _ _ _ doubled s hsub ?_ branch hb
      intro b hb
      exact horner_seq_branch _ _ doubled before s hhalve (fun b hb => ih htail b hb) b hb


/-- Iterated literal modular doublings of one canonical register. -/
def doubles : Nat → List Wire → List Wire → List Bool → Nat → Wire → Wire → Wire → Wire → Quantum.AdaptiveCircuit
  | 0, _, _, _, _, _, _, _, _ => .done
  | k+1, acc, dirty, correction, p, c, r, t, f =>
      (modularDouble acc dirty correction p c r t f).seq (doubles k acc dirty correction p c r t f)

def doublesIdeal : Nat → List Wire → List Bool → Nat → Wire → BasisState → BasisState
  | 0, _, _, _, _, s => s
  | k+1, acc, correction, p, f, s =>
      doublesIdeal k acc correction p f (modularDoubleIdealState acc correction p f s)

theorem doubles_correct (k : Nat) (a : Wire) (rest dirty : List Wire) (correction : List Bool)
    (p : Nat) (c r t f : Wire) (s : BasisState) (hk : (a :: rest).length = correction.length)
    (hd : (a :: rest).length = dirty.length) (hnd : ([c,r,t,f] ++ (a :: rest) ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hx : boolWordToNat (wireValues (a :: rest) s) < p)
    (hodd : p % 2 = 1) (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p) :
    boolWordToNat (wireValues (a :: rest) (doublesIdeal k (a :: rest) correction p f s)) =
      (2 ^ k * boolWordToNat (wireValues (a :: rest) s)) % p ∧
    (∀ w, w ∉ a :: rest → doublesIdeal k (a :: rest) correction p f s w = s w) ∧
    (∀ b ∈ (doubles k (a :: rest) dirty correction p c r t f).run,
      b.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude b.history.length •
        Quantum.ket (doublesIdeal k (a :: rest) correction p f s)) := by
  have hp0 : 0 < p := by omega
  have hl := (doubling_layout (a :: rest) dirty c r t f hnd).1
  have hsep : ∀ w ∈ [c,r,t,f], w ∉ a :: rest := by
    intro w hw ha
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 w hw w ha rfl
  induction k generalizing s with
  | zero =>
    refine ⟨?_, fun w _ => rfl, ?_⟩
    · simp only [doublesIdeal, pow_zero, Nat.one_mul]
      exact (Nat.mod_eq_of_lt hx).symm
    · intro b hb
      have hd := gidneyDoneBranch b hb
      rw [hd.2, hd.1]
      simp [Quantum.registerXResetMagnitude, doublesIdeal]
  | succ k ih =>
    let mid := modularDoubleIdealState (a :: rest) correction p f s
    have hm := modularDoubleIdealState_correct a f rest correction p s hl hf hk hp hx hodd hconstant
    have hmf (w : Wire) (hw : w ∈ [c,r,t,f]) : mid w = s w := hm.2 w (hsep w hw)
    have hmx : boolWordToNat (wireValues (a :: rest) mid) < p := by
      rw [hm.1]; exact Nat.mod_lt _ hp0
    have hi := ih mid ((hmf c (by simp)).trans hc) ((hmf r (by simp)).trans hr)
      ((hmf t (by simp)).trans ht) ((hmf f (by simp)).trans hf) hmx
    refine ⟨?_, ?_, ?_⟩
    · change boolWordToNat (wireValues (a :: rest) (doublesIdeal k (a :: rest) correction p f mid)) = _
      rw [hi.1, hm.1, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]
      congr 1; ring
    · intro w hw
      exact (hi.2.1 w hw).trans (hm.2 w hw)
    · intro b hb
      apply horner_seq_branch _ _ s mid _ ?_ hi.2.2 b hb
      intro b1 hb1
      have hh := modularDouble_branch_correct a rest dirty correction p c r t f s hk hd hnd
        hc hr ht hf hp hx hodd hconstant b1 hb1
      dsimp only at hh
      rw [hh.2, hh.1]


/-- Modular inverse of `2^255` for the secp256k1 field prime. -/
def halfPowerInverse : Nat :=
  66705889445051755814216315116144371036375359769602942646900407208059354494501

private theorem halfPower_inverse : (2 ^ 255 * halfPowerInverse) % ShorECDLP.p = 1 := by
  unfold halfPowerInverse ShorECDLP.p; decide +kernel

private theorem scaled_value (T : Nat) (hT : T < ShorECDLP.p) :
    (2 ^ 255 * ((T * halfPowerInverse) % ShorECDLP.p)) % ShorECDLP.p = T := by
  have hKJ : 2 ^ 255 * halfPowerInverse ≡ 1 [MOD ShorECDLP.p] := by
    unfold Nat.ModEq; rw [halfPower_inverse]; exact (Nat.mod_eq_of_lt (by unfold ShorECDLP.p; decide +kernel)).symm
  have e1 : 2 ^ 255 * ((T * halfPowerInverse) % ShorECDLP.p) ≡ T [MOD ShorECDLP.p] := by
    calc 2 ^ 255 * ((T * halfPowerInverse) % ShorECDLP.p)
        ≡ 2 ^ 255 * (T * halfPowerInverse) [MOD ShorECDLP.p] :=
          Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
      _ = T * (2 ^ 255 * halfPowerInverse) := by ring
      _ ≡ T * 1 [MOD ShorECDLP.p] := Nat.ModEq.mul_left _ hKJ
      _ = T := by ring
  unfold Nat.ModEq at e1
  rw [e1, Nat.mod_eq_of_lt hT]

private theorem forward_value (X Y : Nat) (hX : X < ShorECDLP.p) :
    (2 ^ 255 * ((((X + ShorECDLP.p - (Y * Y) % ShorECDLP.p) % ShorECDLP.p) * halfPowerInverse) % ShorECDLP.p) +
      Y * Y) % ShorECDLP.p = X := by
  have hp0 : 0 < ShorECDLP.p := by unfold ShorECDLP.p; decide +kernel
  set T := (X + ShorECDLP.p - (Y * Y) % ShorECDLP.p) % ShorECDLP.p with hTdef
  have hT : T < ShorECDLP.p := Nat.mod_lt _ hp0
  have e1 : 2 ^ 255 * ((T * halfPowerInverse) % ShorECDLP.p) ≡ T [MOD ShorECDLP.p] := by
    unfold Nat.ModEq; rw [scaled_value T hT, Nat.mod_eq_of_lt hT]
  have e2 : 2 ^ 255 * ((T * halfPowerInverse) % ShorECDLP.p) + Y * Y ≡ T + Y * Y [MOD ShorECDLP.p] :=
    Nat.ModEq.add_right _ e1
  have e3 : T + Y * Y ≡ (X + ShorECDLP.p - (Y * Y) % ShorECDLP.p) + Y * Y [MOD ShorECDLP.p] :=
    Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
  have hR := Nat.mod_lt (Y * Y) hp0
  have hdiv := Nat.mod_add_div (Y * Y) ShorECDLP.p
  have e4 : (X + ShorECDLP.p - (Y * Y) % ShorECDLP.p) + Y * Y =
      X + ShorECDLP.p * (Y * Y / ShorECDLP.p + 1) := by
    rw [Nat.mul_succ]; omega
  have e5 := e2.trans e3
  unfold Nat.ModEq at e5
  rw [e5, e4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]

/-- In-place square subtraction: the inverse square loop runs directly on `x`,
leaving `(x - y^2) / 2^255`, and 255 modular doublings restore the scale. -/
def inPlaceSquare : Quantum.AdaptiveCircuit :=
  (squareLoopInverse (List.range' 580 256) (List.range' 580 256) (List.range' 263 256)
    (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 559 561 562 560).seq
  (doubles 255 (List.range' 263 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p
    560 561 562 559)

/-- Replace the field register `x` by a canonical word. -/
def setX (v : Nat) (s : BasisState) : BasisState :=
  fun w => if 263 ≤ w ∧ w < 519 then (constantBits 256 v).getD (w - 263) false else s w

private theorem setX_values (v : Nat) (s : BasisState) :
    wireValues (List.range' 263 256) (setX v s) = constantBits 256 v := by
  have hlen : (constantBits 256 v).length = 256 := constantBits_length 256 v
  apply List.ext_getElem
  · simp only [wireValues, List.length_map, List.length_range', hlen]
  · intro i h1 h2
    have hi : i < 256 := by rw [hlen] at h2; exact h2
    simp only [wireValues, List.getElem_map, List.getElem_range', setX, Nat.one_mul]
    rw [if_pos (show 263 ≤ 263 + i ∧ 263 + i < 519 by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem]

private theorem setX_value (v : Nat) (s : BasisState) (hv : v < ShorECDLP.p) :
    boolWordToNat (wireValues (List.range' 263 256) (setX v s)) = v := by
  rw [setX_values, boolWordToNat_constantBits, Nat.mod_eq_of_lt]
  exact hv.trans (by unfold ShorECDLP.p; decide +kernel)

private theorem setX_frame (v : Nat) (s : BasisState) (w : Wire) (hw : w ∉ List.range' 263 256) :
    setX v s w = s w := by
  have : ¬ (263 ≤ w ∧ w < 519) := by
    intro h; apply hw; rw [List.mem_range'_1]; omega
  simp only [setX, if_neg this]

private theorem word_ext (ws : List Wire) (s t : BasisState)
    (he : boolWordToNat (wireValues ws s)=boolWordToNat (wireValues ws t))
    (hf : ∀ w, w ∉ ws → s w=t w) : s=t := by
  have hw := boolWordToNat_injective_of_length (by simp [wireValues]) he
  funext w
  by_cases h : w ∈ ws
  · exact List.map_inj_left.mp hw w h
  · exact hf w h

private theorem modulus_value : boolWordToNat (constantBits 256 ShorECDLP.p) = ShorECDLP.p := by
  rw [boolWordToNat_constantBits, Nat.mod_eq_of_lt (by unfold ShorECDLP.p; decide +kernel)]

private theorem square_layout :
    ([558,559,561,562,560] ++ List.range' 580 256 ++ (263 :: List.range' 264 255)).Nodup := by decide +kernel
private theorem double_regs :
    ([560,561,562,559] ++ (263 :: List.range' 264 255) ++ List.range' 580 256).Nodup := by decide +kernel

theorem inPlaceSquare_branch (s : BasisState) (hs : PointLookupValid s)
    (b : Quantum.InstrumentBranch) (hb : b ∈ inPlaceSquare.run) :
    b.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude b.history.length •
      Quantum.ket (fig14SquareSubtractState s) := by
  have hp0 : 0 < ShorECDLP.p := by unfold ShorECDLP.p; decide +kernel
  have hx0 : List.range' 263 256 = 263 :: List.range' 264 255 := rfl
  have hclean (w : Wire) (hw : w ∈ List.range' 519 61) : s w = false :=
    hs.1.1 w (List.mem_append_right _ hw)
  let X := boolWordToNat (wireValues (List.range' 263 256) s)
  let Y := boolWordToNat (wireValues (List.range' 580 256) s)
  have hX : X < ShorECDLP.p := hs.1.2.2.1
  have hY : Y < ShorECDLP.p := hs.1.2.2.2
  let T := (X + ShorECDLP.p - (Y * Y) % ShorECDLP.p) % ShorECDLP.p
  have hT : T < ShorECDLP.p := Nat.mod_lt _ hp0
  let A := (T * halfPowerInverse) % ShorECDLP.p
  have hA : A < ShorECDLP.p := Nat.mod_lt _ hp0
  let s1 := setX A s
  have hs1f (w : Wire) (hw : w ∉ List.range' 263 256) : s1 w = s w := setX_frame A s w hw
  have hs1x : boolWordToNat (wireValues (List.range' 263 256) s1) = A := setX_value A s hA
  have hyx : ∀ w ∈ List.range' 580 256, w ∉ List.range' 263 256 := by
    intro w hw; simp [List.mem_range'] at hw ⊢; omega
  have hs1y : wireValues (List.range' 580 256) s1 = wireValues (List.range' 580 256) s :=
    List.map_congr_left (fun w hw => hs1f w (hyx w hw))
  have hs1c (w : Wire) (hw : w ∈ List.range' 519 61) : s1 w = false := by
    rw [hs1f w (by simp [List.mem_range'] at hw ⊢; omega)]; exact hclean w hw
  -- the forward image of `s1` is `s`
  have hfwd := loop_value (List.range' 580 256) (List.range' 580 256) 263 (List.range' 264 255)
    secp256k1ReductionConstantBits ShorECDLP.p 558 559 561 562 560 s1 (by simp) (by simp [secp256k1ReductionConstantBits])
    square_layout (fun _ h => h) (hs1c 558 (by decide +kernel)) (hs1c 559 (by decide +kernel))
    (hs1c 560 (by decide +kernel)) (by unfold ShorECDLP.p; decide +kernel) (by unfold ShorECDLP.p; decide +kernel)
    (by rw [hs1y]; exact hY) (by rw [← hx0, hs1x]; exact hA)
    (by simpa only [List.length_cons,List.length_range'] using secp256k1ReductionConstant_value)
  have himage : squareLoopIdealState (List.range' 580 256) (List.range' 580 256) (List.range' 263 256)
      secp256k1ReductionConstantBits ShorECDLP.p 558 559 560 s1 = s := by
    apply word_ext (List.range' 263 256)
    · rw [hx0, hfwd.1, ← hx0, hs1x, hs1y, List.length_range', show (256:Nat) - 1 = 255 from rfl]
      exact forward_value X Y hX
    · intro w hw
      rw [hx0] at hw
      exact (hfwd.2 w hw).trans (hs1f w (by rw [hx0]; exact hw))
  -- doubling restores the scale
  have hdbl := doubles_correct 255 263 (List.range' 264 255) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 560 561 562 559 s1 (by simp [secp256k1ReductionConstantBits])
    (by simp) double_regs (hs1c 560 (by decide +kernel)) (hs1c 561 (by decide +kernel))
    (hs1c 562 (by decide +kernel)) (hs1c 559 (by decide +kernel)) (by unfold ShorECDLP.p; decide +kernel)
    (by rw [← hx0, hs1x]; exact hA) (by unfold ShorECDLP.p; decide +kernel)
    (by simpa only [List.length_cons,List.length_range'] using secp256k1ReductionConstant_value)
  have hfinal : doublesIdeal 255 (List.range' 263 256) secp256k1ReductionConstantBits ShorECDLP.p 559 s1 =
      fig14SquareSubtractState s := by
    have hq := fig14SquareSubtractState_correct s hs.1
    rw [hx0] at hq hs1x hs1f ⊢
    apply word_ext (263 :: List.range' 264 255)
    · rw [hq.1, hdbl.1, hs1x, if_pos hs.2]
      exact scaled_value T hT
    · intro w hw
      exact (hdbl.2.1 w hw).trans ((hs1f w hw).trans (hq.2 w hw).symm)
  unfold inPlaceSquare at hb
  rw [← hfinal]
  apply horner_seq_branch _ _ s s1 _ ?_ ?_ b hb
  · intro b1 hb1
    have hh := inverse_after_forward (List.range' 580 256) (List.range' 580 256) 263 (List.range' 264 255)
      secp256k1ReductionConstantBits (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 559 561 562 560 s1
      (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp [constantBits_length]) square_layout (fun _ h => h)
      (hs1c 558 (by decide +kernel)) (hs1c 559 (by decide +kernel)) (hs1c 561 (by decide +kernel))
      (hs1c 562 (by decide +kernel)) (hs1c 560 (by decide +kernel))
      (by unfold ShorECDLP.p; decide +kernel) (by unfold ShorECDLP.p; decide +kernel)
      (by rw [hs1y]; exact hY) (by rw [← hx0, hs1x]; exact hA)
      (by simpa only [List.length_cons,List.length_range'] using secp256k1ReductionConstant_value)
      modulus_value b1 (by rw [← hx0]; exact hb1)
    rw [← hx0, himage] at hh
    exact hh
  · intro b2 hb2
    rw [hx0] at hb2 ⊢
    exact hdbl.2.2 b2 hb2


theorem doubles_wellFormed (k : Nat) (a : Wire) (rest dirty : List Wire) (correction : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a :: rest).length = correction.length)
    (hd : (a :: rest).length = dirty.length) (hnd : ([c,r,t,f] ++ (a :: rest) ++ dirty).Nodup) :
    (doubles k (a :: rest) dirty correction p c r t f).WellFormed := by
  induction k with
  | zero => trivial
  | succ k ih =>
    exact Quantum.AdaptiveCircuit.WellFormed.seq
      (modularDouble_wellFormed a rest dirty correction p c r t f hk hd hnd) ih

theorem inPlaceSquare_wellFormed : inPlaceSquare.WellFormed := by
  unfold inPlaceSquare
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (squareLoopInverse_wellFormed (List.range' 580 256) (List.range' 580 256) 263 (List.range' 264 255)
      (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 559 561 562 560 (by simp)
      (by simp [constantBits_length]) square_layout (fun _ h => h))
    (doubles_wellFormed 255 263 (List.range' 264 255) (List.range' 580 256) secp256k1ReductionConstantBits
      ShorECDLP.p 560 561 562 559 (by simp [secp256k1ReductionConstantBits]) (by simp) double_regs)

private theorem witness_valid : PointLookupValid (fun w => decide (w = 836)) := by
  unfold PointLookupValid Secp256k1ZeroAllowedInputValid Clean
  decide +kernel

theorem inPlaceSquare_coherent :
    CoherentlyImplementsOn inPlaceSquare (Finsupp.lmapDomain ℂ ℂ fig14SquareSubtractState) PointLookupValid :=
  coherent_history_branches _ _ _ inPlaceSquare_wellFormed _ witness_valid
    (fun b hb s hs => inPlaceSquare_branch s hs b hb)

theorem doubles_counts (k : Nat) (A B : List Wire) (K : List Bool) (c r t f : Wire)
    (hA : A.length=256) (hB : B.length=256) (hK : K.length=256) (hk : boolWordToNat K≠0) :
    (doubles k A B K ShorECDLP.p c r t f).tCount = k * 10717 ∧
      (doubles k A B K ShorECDLP.p c r t f).measurementCount = k * 511 := by
  have hd := (modularScaling256_counts A B K c r t f hA hB hK hk).1
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [doubles, adaptive_tCount_seq, modularMeasurements_seq, hd.1, hd.2, ih.1, ih.2]
    constructor <;> rw [Nat.succ_mul, Nat.add_comm]

theorem inPlaceSquare_counts : inPlaceSquare.tCount = 10506566 ∧ inPlaceSquare.measurementCount = 391426 := by
  have hl := (squareLoops256_counts (List.range' 580 256) (List.range' 580 256) (List.range' 263 256)
    (constantBits 256 ShorECDLP.p) 558 559 561 562 560 (by simp) (by simp) (by simp [constantBits_length])
    (by rw [modulus_value]; unfold ShorECDLP.p; decide +kernel)).2
  have hd := doubles_counts 255 (List.range' 263 256) (List.range' 580 256) secp256k1ReductionConstantBits
    560 561 562 559 (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
    (by rw [secp256k1ReductionConstant_value]; decide)
  simp only [List.length_range'] at hl
  unfold inPlaceSquare
  rw [adaptive_tCount_seq, modularMeasurements_seq, hl.1, hl.2, hd.1, hd.2]
  exact ⟨rfl, rfl⟩


open ShorECDLP.Paper2607_13816.ChallengeMigration in
/-- Compiled iterated doublings. -/
def doublesProgram (n : Nat) : Nat → (start : Nat) → List Wire → List Wire → List Bool → Nat →
    Wire → Wire → Wire → Wire → (count : Nat) × Straight n start (start+count)
  | 0, _, _, _, _, _, _, _, _, _ => ⟨0, .done⟩
  | k+1, start, acc, dirty, bits, p, c, r, t, f =>
    let d := modularDoubleProgram n start acc dirty bits p c r t f
    appendCompiled d (doublesProgram n k (start+d.1) acc dirty bits p c r t f)

open ShorECDLP.Paper2607_13816.ChallengeMigration in
/-- Compiled in-place square subtraction. -/
def inPlaceSquareProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let inv := squareInverseProgram n start (List.range' 580 256) (List.range' 580 256) (List.range' 263 256)
    (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 559 561 562 560
  appendCompiled inv (doublesProgram n 255 (start+inv.1) (List.range' 263 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 560 561 562 559)

open ShorECDLP.Paper2607_13816.ChallengeMigration in
theorem doublesProgram_run (n k start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : acc.length = dirty.length) (hk : bits.length = acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (doublesProgram n k start acc dirty bits p c r t f) read history =
      (doubles k acc dirty bits p c r t f).run := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    unfold doublesProgram doubles
    dsimp only
    apply appendCompiled_run_eq
    · exact modularDoubleProgram_run n _ acc dirty bits p c r t f hd hk read history
    · intro h; exact ih _ h

open ShorECDLP.Paper2607_13816.ChallengeMigration in
theorem doublesProgram_tCount (n k start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : acc.length = dirty.length) (hk : bits.length = acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (doublesProgram n k start acc dirty bits p c r t f) read history =
      (doubles k acc dirty bits p c r t f).tCount := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    unfold doublesProgram doubles
    dsimp only
    apply appendCompiled_tCount_eq
    · exact modularDoubleProgram_tCount n _ acc dirty bits p c r t f hd hk read history
    · intro h; exact ih _ h

open ShorECDLP.Paper2607_13816.ChallengeMigration in
theorem inPlaceSquareProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (inPlaceSquareProgram n start) read history = inPlaceSquare.run := by
  unfold inPlaceSquareProgram inPlaceSquare
  dsimp only
  apply appendCompiled_run_eq
  · exact squareInverseProgram_run n start _ _ _ _ _ _ _ _ _ _ (by simp) (by simp [constantBits_length]) (by simp) read history
  · intro h
    exact doublesProgram_run n 255 _ _ _ _ _ _ _ _ _ (by simp) (by simp [secp256k1ReductionConstantBits]) read h

open ShorECDLP.Paper2607_13816.ChallengeMigration in
theorem inPlaceSquareProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (inPlaceSquareProgram n start) read history = inPlaceSquare.tCount := by
  unfold inPlaceSquareProgram inPlaceSquare
  dsimp only
  apply appendCompiled_tCount_eq
  · exact squareInverseProgram_tCount n start _ _ _ _ _ _ _ _ _ _ (by simp) (by simp [constantBits_length]) (by simp) read history
  · intro h
    exact doublesProgram_tCount n 255 _ _ _ _ _ _ _ _ _ (by simp) (by simp [secp256k1ReductionConstantBits]) read h


/-- Measurement padding on a clean wire keeps the record layout of the replaced stage. -/
def pads : Nat → Wire → Quantum.AdaptiveCircuit
  | 0, _ => .done
  | k+1, w => (Quantum.AdaptiveCircuit.xMeasureReset w .done .done).seq (pads k w)

theorem pads_branch (k : Nat) (w : Wire) (s : BasisState) (hw : s w = false)
    (b : Quantum.InstrumentBranch) (hb : b ∈ (pads k w).run) :
    b.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude b.history.length • Quantum.ket s := by
  induction k generalizing b with
  | zero =>
    have hd := gidneyDoneBranch b hb
    rw [hd.2, hd.1]
    simp [Quantum.registerXResetMagnitude]
  | succ k ih =>
    apply horner_seq_branch _ _ s s s ?_ ih b hb
    intro b1 hb1
    rw [Quantum.AdaptiveCircuit.run_xMeasureReset_done] at hb1
    have hs : s[w ↦ false] = s := by
      funext v; by_cases hv : v = w
      · subst hv; simp [upd, hw]
      · simp [upd, hv]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb1
    rcases hb1 with rfl | rfl <;>
      simp [Quantum.xResetKraus_ket, Quantum.xResetCoeff, hw, hs, Quantum.registerXResetMagnitude]

theorem pads_wellFormed (k : Nat) (w : Wire) : (pads k w).WellFormed := by
  induction k with
  | zero => trivial
  | succ k ih => exact Quantum.AdaptiveCircuit.WellFormed.seq ⟨trivial, trivial⟩ ih

theorem pads_counts (k : Nat) (w : Wire) : (pads k w).tCount = 0 ∧ (pads k w).measurementCount = k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [pads, adaptive_tCount_seq, modularMeasurements_seq, ih.1, ih.2]
    exact ⟨rfl, by simp [Quantum.AdaptiveCircuit.measurementCount]; omega⟩

/-- The in-place stage followed by padding to the measurement count of Figure 14's stage. -/
def paddedSquare : Quantum.AdaptiveCircuit := inPlaceSquare.seq (pads 131327 558)

theorem paddedSquare_counts : paddedSquare.tCount = 10506566 ∧ paddedSquare.measurementCount = 522753 := by
  unfold paddedSquare
  rw [adaptive_tCount_seq, modularMeasurements_seq, inPlaceSquare_counts.1, inPlaceSquare_counts.2,
    (pads_counts _ _).1, (pads_counts _ _).2]
  exact ⟨rfl, rfl⟩

theorem paddedSquare_coherent :
    CoherentlyImplementsOn paddedSquare (Finsupp.lmapDomain ℂ ℂ fig14SquareSubtractState) PointLookupValid := by
  refine coherent_history_branches _ _ _
    (Quantum.AdaptiveCircuit.WellFormed.seq inPlaceSquare_wellFormed (pads_wellFormed _ _)) _ witness_valid ?_
  intro b hb s hs
  apply horner_seq_branch _ _ s (fig14SquareSubtractState s) _ (fun b hb => inPlaceSquare_branch s hs b hb) ?_ b hb
  intro b2 hb2
  have hq := fig14SquareSubtractState_correct s hs.1
  apply pads_branch _ _ _ _ b2 hb2
  rw [hq.2 558 (by rw [List.mem_range'_1]; omega)]
  exact hs.1.1 558 (List.mem_append_right _ (by rw [List.mem_range'_1]; omega))

open ShorECDLP.Paper2607_13816.ChallengeMigration in
def padsProgram (n : Nat) : Nat → (start : Nat) → Wire → (count : Nat) × Straight n start (start+count)
  | 0, _, _ => ⟨0, .done⟩
  | k+1, start, w => appendCompiled ⟨1, .measure w .done⟩ (padsProgram n k (start+1) w)

open ShorECDLP.Paper2607_13816.ChallengeMigration in
def paddedSquareProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let sq := inPlaceSquareProgram n start
  appendCompiled sq (padsProgram n 131327 (start+sq.1) 558)

open ShorECDLP.Paper2607_13816.ChallengeMigration in
theorem padsProgram_run (n k start : Nat) (w : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (padsProgram n k start w) read history = (pads k w).run := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    unfold padsProgram pads
    apply appendCompiled_run_eq
    · rfl
    · intro h; exact ih _ h

open ShorECDLP.Paper2607_13816.ChallengeMigration in
theorem padsProgram_tCount (n k start : Nat) (w : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (padsProgram n k start w) read history = (pads k w).tCount := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    unfold padsProgram pads
    apply appendCompiled_tCount_eq
    · rfl
    · intro h; exact ih _ h

open ShorECDLP.Paper2607_13816.ChallengeMigration in
theorem paddedSquareProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (paddedSquareProgram n start) read history = paddedSquare.run := by
  unfold paddedSquareProgram paddedSquare
  apply appendCompiled_run_eq
  · exact inPlaceSquareProgram_run n start read history
  · intro h; exact padsProgram_run n _ _ _ read h

open ShorECDLP.Paper2607_13816.ChallengeMigration in
theorem paddedSquareProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (paddedSquareProgram n start) read history = paddedSquare.tCount := by
  unfold paddedSquareProgram paddedSquare
  apply appendCompiled_tCount_eq
  · exact inPlaceSquareProgram_tCount n start read history
  · intro h; exact padsProgram_tCount n _ _ _ read h

end ShorECDLP.Entrant.SquareInPlace

/-! Coherent measured quotient swaps and their complete field-division compiler.
Supporting proofs are restated from the protected EEA/IndexedStep and Arithmetic/InPlace
sources (ShorECDLP contributors, Apache-2.0). All imports are ordinary public imports. -/
section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem measuredCore_unary_unitary (order : UnaryOrder) (leaf : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (path : List Wire) :
    unaryAdaptiveAction order (fun l c => .unitary (leaf l c) .done) tree control path =
      unaryAction order leaf tree control path := by
  induction tree generalizing control path with
  | leaf l => rfl
  | node bit zero one ihz iho =>
    cases path with
    | nil => rfl
    | cons p ps => cases order <;> simp [unaryAdaptiveAction, unaryAction, ihz, iho]

def program (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  surroundCompiled
    (cuccaroAdd r.lengthT r.lengthQ (r.carry k K) ++ addConstant r.lengthQ r.constantScratch (r.carry k K) 3)
    (subConstant r.lengthQ r.constantScratch (r.carry k K) 3 ++ cuccaroSub r.lengthT r.lengthQ (r.carry k K))
    (unaryProgram n .inc (fun label control _ => ⟨0, literalProgram (quotientSwapLeaf r k label control)⟩)
      (quotientSwapTree r k K) r.control (r.path k K) start)

theorem program_run (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (program n start r k K) read history = (quotientSwap r k K).run := by
  unfold program quotientSwap
  apply surroundCompiled_run
  rw [← measuredCore_unary_unitary]
  apply unaryProgram_run
  intro label control cursor h
  exact literalCompiled_run _ read h

theorem program_tCount (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (program n start r k K) read history = (quotientSwap r k K).tCount := by
  unfold program quotientSwap
  apply surroundCompiled_tCount
  rw [← measuredCore_unary_unitary]
  apply unaryProgram_tCount
  intro label control cursor h
  exact literalCompiled_tCount _ read h

theorem program_coherent (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat)
    (hl : QuotientSwapLayout r k K)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program n start r k K).2.instantiate read history)
      (Quantum.run (quotientSwapUnitary r k K)) (QuotientSwapReady r) := by
  have hr := program_run n start r k K read history
  unfold compiledRun at hr
  simpa only [CoherentlyImplementsOn, hr] using quotientSwap_coherent r hl

theorem program_saving (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat)
    (hl : QuotientSwapLayout r k K)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (program n start r k K) read history + 7*(quotientSwapTree r k K).internalNodes =
      ShorECDLP.tCount (quotientSwapUnitary r k K) := by
  rw [program_tCount, quotientSwap_tCount r hl, quotientSwapUnitary_tCount r hl]
  omega

def before (r : IndexedStepRegisters) : Circuit :=
  [.CX r.phase1 r.control, .CX r.phase2 r.control]

def after (r : IndexedStepRegisters) : Circuit :=
  [.CX r.phase2 r.control, .CX r.phase1 r.control]

def blockD2 (r : IndexedStepRegisters) (w : ActiveWindow) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (before r) .done).seq
    ((quotientSwap (r.quotient w) w.start w.stop).seq (.unitary (after r) .done))

private theorem measuredCore_before_ready (r : IndexedStepRegisters) (n T : Nat)
    (hl : IndexedStepLayout r n T) (s : BasisState) (hs : IndexedStepReady r s) :
    QuotientSwapReady (r.quotient (certifiedActiveWindows n T).quotientSwap)
      (ShorECDLP.Classical.run (before r) s) := by
  intro q hq
  have hsource : q ∈ r.sourceScratch := List.mem_of_mem_take hq
  have hne : q ≠ r.control := by
    intro he
    subst q
    have hnd := hl.phase2Length.2
    have ht : (r.control :: r.sourceScratch).Nodup := (List.nodup_append.mp hnd).2.1
    exact (List.nodup_cons.mp ht).1 hsource
  have hz := hs q (by simp [IndexedStepRegisters.sharedScratch, hsource])
  simpa [before, ShorECDLP.Classical.run, ShorECDLP.Classical.applyGate, upd, hne] using hz

theorem blockD2_coherent (r : IndexedStepRegisters) (n T : Nat)
    (hl : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (blockD2 r (certifiedActiveWindows n T).quotientSwap)
      (Quantum.run (blockD2Forward r (certifiedActiveWindows n T).quotientSwap))
      (IndexedStepReady r) := by
  let w := (certifiedActiveWindows n T).quotientSwap
  have hb := CoherentlyImplementsOn.unitary (before r) (IndexedStepReady r)
  have hq := quotientSwap_coherent (r.quotient w) hl.quotient
  have hfirst := hb.seq hq (by
    intro s hs
    rw [run_ket_agrees_classical (before r) s (by simp [before])]
    exact supportedOn_ket _ _ (measuredCore_before_ready r n T hl s hs))
  have htail := CoherentlyImplementsOn.unitary (after r) (fun _ => True)
  have hfull := hfirst.seq htail (by intro s hs t ht; trivial)
  unfold blockD2
  rw [← circuit_seq_assoc]
  apply hfull.congrIdeal
  intro s _
  change Quantum.run (after r) (Quantum.run (quotientSwapUnitary (r.quotient w) w.start w.stop)
    (Quantum.run (before r) (ket s))) = _
  simp only [blockD2Forward, Quantum.run_append]
  rfl

def nodeBudget (T : Nat) : Nat :=
  (quotientSwapWindow 256 T).stop - (quotientSwapWindow 256 T).start

theorem nodeBudget_total : ((List.range' 1 1620).map nodeBudget).sum = 241534 := by
  decide +kernel
end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace IndexedStepRegisters
private def measuredStepPlain_remainderBase
    (registers : IndexedStepRegisters) (window : ActiveWindow) : IntervalRegisters where
  control := registers.control
  sign := registers.sign
  work1 := windowSlice registers.work1 window
  work2 := windowSlice registers.work2 window
  lengthT := registers.lengthT
  lengthQ := registers.lengthQ
  lengthS := registers.lengthS
  scratch := []

end IndexedStepRegisters

namespace IndexedStepRegisters
private def measuredStepPlain_source_remainder
    (registers : IndexedStepRegisters) (window : ActiveWindow) : IntervalRegisters :=
  { registers.measuredStepPlain_remainderBase window with
    scratch := (registers.shiftEpoch :: (registers.sourceScratch ++
      registers.remainderRepairScratch)).take
        (registers.remainderScratchSize window) }
private theorem measuredStepPlain_view_remainder : remainder = measuredStepPlain_source_remainder := rfl

end IndexedStepRegisters

private def measuredStepPlain_terminalConditionWires (registers : IndexedStepRegisters) : List Wire :=
  registers.phase1 :: registers.lengthRPrime

private def measuredStepPlain_terminalConditionValue (registers : IndexedStepRegisters) : Nat :=
  2 ^ (registers.lengthRPrime.length + 1) - 2

private def measuredStepPlain_toggleTerminal (registers : IndexedStepRegisters) : Circuit :=
  computeControl (measuredStepPlain_terminalConditionWires registers) (measuredStepPlain_terminalConditionValue registers)
    registers.terminal registers.blockScratch

private def measuredStepPlain_toggleRControl
    (registers : IndexedStepRegisters) (conditions : List Wire) (value : Nat)
    (zeroRPrime : Wire) (scratch : List Wire) : Circuit :=
  rControlNonterminal conditions value registers.control registers.lengthRPrime
    zeroRPrime scratch

private def measuredStepPlain_source_blockAForward
    (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    measuredStepPlain_toggleTerminal registers;
    terminalPaddingForward registers.terminalPadding;
    gate! Gate.CX registers.terminal registers.phase1;
    preShiftUnitary registers.preShift;
    gate! Gate.CX registers.terminal registers.phase1;
    terminalEpochSpill registers.terminal registers.shiftEpoch registers.quotientLow;
    measuredStepPlain_toggleTerminal registers
  }
private theorem measuredStepPlain_view_blockAForward : blockAForward = measuredStepPlain_source_blockAForward := rfl

private def measuredStepPlain_remainderSubControl (registers : IndexedStepRegisters) : Circuit :=
  measuredStepPlain_toggleRControl registers ([registers.phase1]) 0 registers.terminal registers.blockScratch

private def measuredStepPlain_remainderPhase2Control (registers : IndexedStepRegisters) : Circuit :=
  measuredStepPlain_toggleRControl registers ([registers.phase1, registers.phase2]) 2
    registers.terminal registers.blockScratch

private def measuredStepPlain_remainderRestoreControl (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    gate! Gate.CCX registers.phase2 registers.sign registers.terminal;
    measuredStepPlain_toggleRControl registers ([registers.phase1, registers.terminal]) 0
      (registers.blockScratch.getD 0 0) (registers.blockScratch.drop 1);
    gate! Gate.CCX registers.phase2 registers.sign registers.terminal
  }

private def measuredStepPlain_source_blockB1Forward
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    measuredStepPlain_remainderSubControl registers;
    intervalAddSubUnitary (registers.remainder window) n window.start window.stop
      .sub true .work1;
    measuredStepPlain_remainderSubControl registers
  }
private theorem measuredStepPlain_view_blockB1Forward : blockB1Forward = measuredStepPlain_source_blockB1Forward := rfl

private def measuredStepPlain_source_blockB2 (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    measuredStepPlain_remainderPhase2Control registers;
    gate! Gate.CX registers.control registers.sign;
    measuredStepPlain_remainderPhase2Control registers
  }
private theorem measuredStepPlain_view_blockB2 : blockB2 = measuredStepPlain_source_blockB2 := rfl

private def measuredStepPlain_source_blockB3Forward
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  circuit! {
    measuredStepPlain_remainderRestoreControl registers;
    intervalAddSubUnitary (registers.remainder window) n window.start window.stop
      .add false .work1;
    measuredStepPlain_remainderRestoreControl registers
  }
private theorem measuredStepPlain_view_blockB3Forward : blockB3Forward = measuredStepPlain_source_blockB3Forward := rfl

private def measuredStepPlain_source_blockCForward (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    measuredStepPlain_toggleTerminal registers;
    terminalEpochRestore registers.terminal registers.shiftEpoch registers.quotientLow;
    measuredStepPlain_toggleTerminal registers
  }
private theorem measuredStepPlain_view_blockCForward : blockCForward = measuredStepPlain_source_blockCForward := rfl

private def measuredStepPlain_phase2LengthControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase1, registers.phase2]) 2 registers.control
    registers.sourceScratch

private def measuredStepPlain_phase3LengthControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase1, registers.phase2]) 1 registers.control
    registers.sourceScratch

private def measuredStepPlain_quotientXorControl (registers : IndexedStepRegisters) : Circuit :=
  [.CX registers.phase1 registers.control, .CX registers.phase2 registers.control]

private def measuredStepPlain_quotientXorControlInverse (registers : IndexedStepRegisters) : Circuit :=
  [.CX registers.phase2 registers.control, .CX registers.phase1 registers.control]

private def measuredStepPlain_lengthCarries (registers : IndexedStepRegisters) : List Wire :=
  registers.sourceScratch.take (registers.lengthQ.length - 1)

private def measuredStepPlain_source_blockD1Forward (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    measuredStepPlain_phase2LengthControl registers;
    controlledIncrement registers.control registers.lengthQ (measuredStepPlain_lengthCarries registers);
    measuredStepPlain_phase2LengthControl registers
  }
private theorem measuredStepPlain_view_blockD1Forward : blockD1Forward = measuredStepPlain_source_blockD1Forward := rfl

private def measuredStepPlain_source_blockD3Forward (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    measuredStepPlain_phase3LengthControl registers;
    controlledDecrement registers.control registers.lengthQ (measuredStepPlain_lengthCarries registers);
    measuredStepPlain_phase3LengthControl registers
  }
private theorem measuredStepPlain_view_blockD3Forward : blockD3Forward = measuredStepPlain_source_blockD3Forward := rfl

private def measuredStepPlain_source_blockD2Forward (registers : IndexedStepRegisters) (window : ActiveWindow) : Circuit :=
  circuit! {
    measuredStepPlain_quotientXorControl registers;
    quotientSwapUnitary (registers.quotient window) window.start window.stop;
    measuredStepPlain_quotientXorControlInverse registers
  }
private theorem measuredStepPlain_view_blockD2Forward : blockD2Forward = measuredStepPlain_source_blockD2Forward := rfl

private def measuredStepPlain_coefficientTemporaryControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase2, registers.sign]) 2 registers.terminal
    registers.blockScratch

private def measuredStepPlain_coefficientSubControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase1, registers.terminal]) 1 registers.control
    registers.blockScratch

private def measuredStepPlain_coefficientAddControl (registers : IndexedStepRegisters) : Circuit :=
  computeControl ([registers.phase1]) 1 registers.control registers.blockScratch

private def measuredStepPlain_source_coefficientSubtractControl (r : IndexedStepRegisters) : Circuit :=
  measuredStepPlain_coefficientTemporaryControl r ++ measuredStepPlain_coefficientSubControl r ++ measuredStepPlain_coefficientTemporaryControl r
private theorem measuredStepPlain_view_coefficientSubtractControl : coefficientSubtractControl = measuredStepPlain_source_coefficientSubtractControl := rfl

private def measuredStepPlain_source_blockESubtractForward (r : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  blockEPrepareForward r n ++
    coefficientPrefixUnitary (r.coefficient window) window.start window.stop .sub false .work2 ++
    measuredStepPlain_coefficientTemporaryControl r ++ measuredStepPlain_coefficientSubControl r ++ measuredStepPlain_coefficientTemporaryControl r
private theorem measuredStepPlain_view_blockESubtractForward : blockESubtractForward = measuredStepPlain_source_blockESubtractForward := rfl

private def measuredStepPlain_source_blockEFinishForward (r : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) : Circuit :=
  [.CX r.phase1 r.sign] ++ measuredStepPlain_coefficientAddControl r ++
    coefficientPrefixUnitary (r.coefficient window) window.start window.stop .add true .work2 ++
    measuredStepPlain_coefficientAddControl r ++ restoreLatestPaperTBoundary r.tBoundary n
private theorem measuredStepPlain_view_blockEFinishForward : blockEFinishForward = measuredStepPlain_source_blockEFinishForward := rfl

private def measuredStepPlain_adaptiveUnitary (circuit : Circuit) : Quantum.AdaptiveCircuit :=
  .unitary circuit .done

private def measuredStepPlain_blockB1Adaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (measuredStepPlain_adaptiveUnitary (measuredStepPlain_remainderSubControl registers)).seq
    ((intervalAddSub (registers.remainder window) n window.start window.stop
      .sub true .work1).seq
      (measuredStepPlain_adaptiveUnitary (measuredStepPlain_remainderSubControl registers)))

private def measuredStepPlain_blockB3Adaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (measuredStepPlain_adaptiveUnitary (measuredStepPlain_remainderRestoreControl registers)).seq
    ((intervalAddSub (registers.remainder window) n window.start window.stop
      .add false .work1).seq
      (measuredStepPlain_adaptiveUnitary (measuredStepPlain_remainderRestoreControl registers)))

private def measuredStepPlain_source_blockBAdaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (measuredStepPlain_blockB1Adaptive registers n window).seq
    ((measuredStepPlain_adaptiveUnitary (blockB2 registers)).seq
      (measuredStepPlain_blockB3Adaptive registers n window))
private theorem measuredStepPlain_view_blockBAdaptive : blockBAdaptive = measuredStepPlain_source_blockBAdaptive := rfl

private def measuredStepPlain_blockEPrefix
    (registers : IndexedStepRegisters) (n : Nat) : Circuit :=
  circuit! {
    measuredStepPlain_coefficientTemporaryControl registers;
    measuredStepPlain_coefficientSubControl registers;
    measuredStepPlain_coefficientTemporaryControl registers;
    prepareLatestPaperTBoundary registers.tBoundary n
  }

private def measuredStepPlain_blockEMiddle (registers : IndexedStepRegisters) : Circuit :=
  circuit! {
    measuredStepPlain_coefficientTemporaryControl registers;
    measuredStepPlain_coefficientSubControl registers;
    measuredStepPlain_coefficientTemporaryControl registers;
    gate! Gate.CX registers.phase1 registers.sign;
    measuredStepPlain_coefficientAddControl registers
  }

private def measuredStepPlain_blockESuffix
    (registers : IndexedStepRegisters) (n : Nat) : Circuit :=
  circuit! {
    measuredStepPlain_coefficientAddControl registers;
    restoreLatestPaperTBoundary registers.tBoundary n
  }

private def measuredStepPlain_blockEFirstAdaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (measuredStepPlain_adaptiveUnitary (measuredStepPlain_blockEPrefix registers n)).seq
    (coefficientPrefixAdaptive (registers.coefficient window)
      window.start window.stop .sub false .work2)

private def measuredStepPlain_blockETailAdaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (measuredStepPlain_adaptiveUnitary (measuredStepPlain_blockEMiddle registers)).seq
    ((coefficientPrefixAdaptive (registers.coefficient window)
      window.start window.stop .add true .work2).seq
      (measuredStepPlain_adaptiveUnitary (measuredStepPlain_blockESuffix registers n)))

private def measuredStepPlain_source_blockEAdaptive
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow) :
    Quantum.AdaptiveCircuit :=
  (measuredStepPlain_blockEFirstAdaptive registers n window).seq
    (measuredStepPlain_blockETailAdaptive registers n window)
private theorem measuredStepPlain_view_blockEAdaptive : blockEAdaptive = measuredStepPlain_source_blockEAdaptive := rfl

private def measuredStepPlain_IndexedStepBorrowedReady
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  Clean registers.aux state

private def measuredStepPlain_source_IndexedStepEpochEncoded
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  if registerMatches (measuredStepPlain_terminalConditionWires registers)
      (measuredStepPlain_terminalConditionValue registers) state then
    state registers.quotientLow = true
  else
    state registers.shiftEpoch = false
private theorem measuredStepPlain_view_IndexedStepEpochEncoded : IndexedStepEpochEncoded = measuredStepPlain_source_IndexedStepEpochEncoded := rfl

private def measuredStepPlain_xorWireState
    (control target : Wire) (state : BasisState) : BasisState :=
  state[target ↦ Bool.xor (state target) (state control)]

private def measuredStepPlain_andXorWireState
    (first second target : Wire) (state : BasisState) : BasisState :=
  state[target ↦ Bool.xor (state target) (state first && state second)]

private def measuredStepPlain_matchXorState
    (controls : List Wire) (value : Nat) (target : Wire)
    (state : BasisState) : BasisState :=
  state[target ↦ Bool.xor (state target)
    (registerMatches controls value state)]

private theorem measuredStepPlain_matchXorState_preserves
    (controls : List Wire) (value : Nat) (target : Wire)
    (state : BasisState) {wire : Wire} (hwire : wire ≠ target) :
    measuredStepPlain_matchXorState controls value target state wire = state wire := by
  simp [measuredStepPlain_matchXorState, upd, hwire]

private def measuredStepPlain_rControlState
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (state : BasisState) : BasisState :=
  state[control ↦ Bool.xor (state control)
    (rControlNonterminalPredicate conditions value
      lengthRPrime zeroRPrime state)]

private def measuredStepPlain_swapWireState
    (left right : Wire) (state : BasisState) : BasisState :=
  state[left ↦ state right][right ↦ state left]

private def measuredStepPlain_controlledSwapState
    (control left right : Wire) (state : BasisState) : BasisState :=
  if state control then measuredStepPlain_swapWireState left right state else state

private def measuredStepPlain_terminalEpochSpillState
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState) : BasisState :=
  measuredStepPlain_controlledSwapState terminal shiftEpoch quotientLow
    (measuredStepPlain_xorWireState terminal quotientLow state)

private def measuredStepPlain_terminalEpochRestoreState
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState) : BasisState :=
  measuredStepPlain_xorWireState terminal quotientLow
    (measuredStepPlain_controlledSwapState terminal shiftEpoch quotientLow state)

private theorem measuredStepPlain_terminalEpochSpillState_preserves
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    {wire : Wire} (hshift : wire ≠ shiftEpoch)
    (hquotient : wire ≠ quotientLow)
    (hterminalQuotient : terminal ≠ quotientLow) :
    measuredStepPlain_terminalEpochSpillState terminal shiftEpoch quotientLow state wire =
      state wire := by
  cases hterminal : state terminal <;>
    simp [measuredStepPlain_terminalEpochSpillState, measuredStepPlain_controlledSwapState, measuredStepPlain_xorWireState,
      measuredStepPlain_swapWireState, upd, hterminal, hshift, hquotient,
      hterminalQuotient]

private theorem measuredStepPlain_terminalEpochRestoreState_preserves
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    {wire : Wire} (hshift : wire ≠ shiftEpoch)
    (hquotient : wire ≠ quotientLow) :
    measuredStepPlain_terminalEpochRestoreState terminal shiftEpoch quotientLow state wire =
      state wire := by
  cases hterminal : state terminal <;>
    simp [measuredStepPlain_terminalEpochRestoreState, measuredStepPlain_controlledSwapState, measuredStepPlain_xorWireState,
      measuredStepPlain_swapWireState, upd, hterminal, hshift, hquotient]

private theorem measuredStepPlain_run_xorWireState
    (control target : Wire) (state : BasisState) :
    run ([.CX control target] : Circuit) state =
      measuredStepPlain_xorWireState control target state := by
  rfl

private theorem measuredStepPlain_run_andXorWireState
    (first second target : Wire) (state : BasisState) :
    run ([.CCX first second target] : Circuit) state =
      measuredStepPlain_andXorWireState first second target state := by
  rfl

private theorem measuredStepPlain_run_terminalEpochSpillState
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow) :
    run (terminalEpochSpill terminal shiftEpoch quotientLow) state =
      measuredStepPlain_terminalEpochSpillState terminal shiftEpoch quotientLow state := by
  simp only [TerminalEpochLayout, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hlayout
  rw [terminalEpochSpill, Classical.run_append,
    run_controlledSwap terminal shiftEpoch quotientLow]
  · rfl
  · exact hlayout.1.1
  · exact hlayout.1.2
  · exact hlayout.2.1

private theorem measuredStepPlain_run_terminalEpochRestoreState
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow) :
    run (terminalEpochRestore terminal shiftEpoch quotientLow) state =
      measuredStepPlain_terminalEpochRestoreState terminal shiftEpoch quotientLow state := by
  simp only [TerminalEpochLayout, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hlayout
  rw [terminalEpochRestore, Classical.run_append,
    run_controlledSwap terminal shiftEpoch quotientLow]
  · rfl
  · exact hlayout.1.1
  · exact hlayout.1.2
  · exact hlayout.2.1

private theorem measuredStepPlain_clean_mono
    {large small : List Wire} {state : BasisState}
    (hclean : Clean large state)
    (hsub : ∀ wire ∈ small, wire ∈ large) : Clean small state := by
  intro wire hwire
  exact hclean wire (hsub wire hwire)

private theorem measuredStepPlain_clean_upd_not_mem
    {wires : List Wire} {state : BasisState} {target : Wire} {value : Bool}
    (hclean : Clean wires state) (houtside : target ∉ wires) :
    Clean wires state[target ↦ value] := by
  intro wire hwire
  rw [upd_other]
  · exact hclean wire hwire
  · intro equality
    subst wire
    exact houtside hwire

private theorem measuredStepPlain_writeReg_apply_outside
    (register : List Wire) (value : Nat) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    writeReg register value state wire = state wire := by
  induction register generalizing value state with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at hwire
      rw [writeReg, ih (state := state[head ↦ value.testBit 0])
        (value := value / 2) hwire.2, upd_other]
      exact hwire.1

private def measuredStepPlain_indexedWriteWireValues : List Wire → List Bool → BasisState → BasisState
  | wire :: wires, bit :: bits, state =>
      (measuredStepPlain_indexedWriteWireValues wires bits state)[wire ↦ bit]
  | _, _, state => state

private theorem measuredStepPlain_indexedWriteWireValues_preservesOutside
    (wires : List Wire) (bits : List Bool) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ wires) :
    measuredStepPlain_indexedWriteWireValues wires bits state wire = state wire := by
  induction wires generalizing bits state with
  | nil => simp [measuredStepPlain_indexedWriteWireValues]
  | cons head tail ih =>
      cases bits with
      | nil => simp [measuredStepPlain_indexedWriteWireValues]
      | cons bit bits =>
          simp only [List.mem_cons, not_or] at hwire
          simp [measuredStepPlain_indexedWriteWireValues, upd, hwire.1, ih bits state hwire.2]

private theorem measuredStepPlain_indexedWireValues_writeWireValues
    (wires : List Wire) (bits : List Bool) (state : BasisState)
    (hnd : wires.Nodup) (hlength : bits.length = wires.length) :
    wireValues wires (measuredStepPlain_indexedWriteWireValues wires bits state) = bits := by
  induction wires generalizing bits state with
  | nil =>
      have : bits = [] := List.length_eq_zero_iff.mp (by simpa using hlength)
      subst bits
      rfl
  | cons head tail ih =>
      cases bits with
      | nil => simp at hlength
      | cons bit bits =>
          have hhead : head ∉ tail := (List.nodup_cons.mp hnd).1
          have htail : tail.Nodup := (List.nodup_cons.mp hnd).2
          have htailLength : bits.length = tail.length := by simpa using hlength
          have htailUpdated :
              wireValues tail
                  ((measuredStepPlain_indexedWriteWireValues tail bits state)[head ↦ bit]) =
                wireValues tail (measuredStepPlain_indexedWriteWireValues tail bits state) := by
            unfold wireValues
            apply List.map_congr_left
            intro wire hwire
            have hne : wire ≠ head := by
              intro equality
              subst wire
              exact hhead hwire
            simp [upd, hne]
          simp only [measuredStepPlain_indexedWriteWireValues, wireValues, List.map_cons]
          change
            (measuredStepPlain_indexedWriteWireValues tail bits state)[head ↦ bit] head ::
                wireValues tail
                  ((measuredStepPlain_indexedWriteWireValues tail bits state)[head ↦ bit]) =
              bit :: bits
          rw [htailUpdated, ih bits state htail htailLength]
          simp [upd]

private theorem measuredStepPlain_indexedWireValues_eq_at
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    {wire : Wire} (hwire : wire ∈ wires) :
    left wire = right wire := by
  induction wires with
  | nil => simp at hwire
  | cons head tail ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq] at hvalues
      rcases List.mem_cons.mp hwire with rfl | hwire
      · exact hvalues.1
      · exact ih hvalues.2 hwire

private theorem measuredStepPlain_indexedState_eq_writeWireValues
    (wires : List Wire) (bits : List Bool)
    (before after : BasisState)
    (hnd : wires.Nodup) (hlength : bits.length = wires.length)
    (hvalues : wireValues wires after = bits)
    (houtside : ∀ wire, wire ∉ wires → after wire = before wire) :
    after = measuredStepPlain_indexedWriteWireValues wires bits before := by
  funext wire
  by_cases hwire : wire ∈ wires
  · apply measuredStepPlain_indexedWireValues_eq_at wires
    calc
      wireValues wires after = bits := hvalues
      _ = wireValues wires (measuredStepPlain_indexedWriteWireValues wires bits before) :=
        (measuredStepPlain_indexedWireValues_writeWireValues wires bits before hnd hlength).symm
    exact hwire
  · rw [houtside wire hwire,
      measuredStepPlain_indexedWriteWireValues_preservesOutside wires bits before hwire]

private theorem measuredStepPlain_indexedIncrementBits_length (carry : Bool) (bits : List Bool) :
    (incrementBits carry bits).length = bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp [incrementBits, ih]

private theorem measuredStepPlain_indexedDecrementBits_length (borrow : Bool) (bits : List Bool) :
    (decrementBits borrow bits).length = bits.length := by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih => simp [decrementBits, ih]

private def measuredStepPlain_indexedIncrementWordState
    (enabled : Bool) (register : List Wire) (state : BasisState) : BasisState :=
  measuredStepPlain_indexedWriteWireValues register
    (incrementBits enabled (wireValues register state)) state

private def measuredStepPlain_indexedDecrementWordState
    (enabled : Bool) (register : List Wire) (state : BasisState) : BasisState :=
  measuredStepPlain_indexedWriteWireValues register
    (decrementBits enabled (wireValues register state)) state

private theorem measuredStepPlain_run_controlledIncrement_indexedState
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledIncrement control register carries) state =
      measuredStepPlain_indexedIncrementWordState (state control) register state := by
  have hcorrect := controlledIncrement_correct control register carries state
    hlength hnd hclean
  apply measuredStepPlain_indexedState_eq_writeWireValues register _ state _
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  · rw [measuredStepPlain_indexedIncrementBits_length]
    simp [wireValues]
  · exact hcorrect.1
  · exact hcorrect.2

private theorem measuredStepPlain_run_controlledDecrement_indexedState
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledDecrement control register carries) state =
      measuredStepPlain_indexedDecrementWordState (state control) register state := by
  have hcorrect := controlledDecrement_correct control register carries state
    hlength hnd hclean
  apply measuredStepPlain_indexedState_eq_writeWireValues register _ state _
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  · rw [measuredStepPlain_indexedDecrementBits_length]
    simp [wireValues]
  · exact hcorrect.1
  · exact hcorrect.2

private theorem measuredStepPlain_indexedIncrementWordState_preservesOutside
    (enabled : Bool) (register : List Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    measuredStepPlain_indexedIncrementWordState enabled register state wire = state wire :=
  measuredStepPlain_indexedWriteWireValues_preservesOutside register _ state hwire

private theorem measuredStepPlain_indexedDecrementWordState_preservesOutside
    (enabled : Bool) (register : List Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    measuredStepPlain_indexedDecrementWordState enabled register state wire = state wire :=
  measuredStepPlain_indexedWriteWireValues_preservesOutside register _ state hwire

private theorem measuredStepPlain_indexedRouteLabel_congr
    (tree : UnaryActionTree) (left right : BasisState)
    (hagrees : ∀ wire ∈ tree.indexWires, left wire = right wire) :
    tree.routeLabel left = tree.routeLabel right := by
  induction tree with
  | leaf => rfl
  | node indexBit zero one ihZero ihOne =>
      simp only [UnaryActionTree.routeLabel]
      rw [hagrees indexBit (by simp [UnaryActionTree.indexWires])]
      split
      · apply ihOne
        intro wire hwire
        exact hagrees wire (by simp [UnaryActionTree.indexWires, hwire])
      · apply ihZero
        intro wire hwire
        exact hagrees wire (by simp [UnaryActionTree.indexWires, hwire])

private theorem measuredStepPlain_run_computeControl_state
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratch : List Wire) (state : BasisState)
    (hlayout : ComputeControlLayout controls target scratch)
    (hclean : Clean scratch state) :
    run (computeControl controls value target scratch) state =
        measuredStepPlain_matchXorState controls value target state ∧
      Clean scratch (measuredStepPlain_matchXorState controls value target state) := by
  have hrun := run_computeControl controls value target scratch state hlayout hclean
  have htarget : target ∉ scratch := by
    obtain ⟨_, htail, _⟩ := List.nodup_append.mp hlayout.2
    exact (List.nodup_cons.mp htail).1
  constructor
  · simpa [measuredStepPlain_matchXorState] using hrun
  · intro wire hwire
    simp [measuredStepPlain_matchXorState, upd,
      show wire ≠ target by intro equality; subst wire; exact htarget hwire,
      hclean wire hwire]

private theorem measuredStepPlain_clean_after_local_circuit
    {large localScratch support : List Wire} {circuit : Circuit}
    {state : BasisState}
    (hlarge : Clean large state)
    (hlocal : Clean localScratch (run circuit state))
    (huses : PaperCircuitUsesOnly support circuit)
    (hintersection : ∀ wire ∈ large, wire ∈ support → wire ∈ localScratch) :
    Clean large (run circuit state) := by
  intro wire hwire
  by_cases hsupport : wire ∈ support
  · exact hlocal wire (hintersection wire hwire hsupport)
  · rw [huses.preservesOutside state hsupport]
    exact hlarge wire hwire

private theorem measuredStepPlain_nodup_middle_ne
    {before middle after : List α} {middleWire outsideWire : α}
    (hnodup : (before ++ (middle ++ after)).Nodup)
    (hmiddle : middleWire ∈ middle)
    (houtside : outsideWire ∈ before ∨ outsideWire ∈ after) :
    middleWire ≠ outsideWire := by
  obtain ⟨_, htail, hcrossBefore⟩ := List.nodup_append.mp hnodup
  obtain ⟨_, _, hsuffix⟩ := List.nodup_append.mp htail
  rcases houtside with hbefore | hafter
  · intro equality
    exact hcrossBefore outsideWire hbefore middleWire
      (List.mem_append_left after hmiddle) equality.symm
  · intro equality
    exact hsuffix middleWire hmiddle outsideWire hafter equality

private theorem measuredStepPlain_registerMatchesFrom_congr
    (register : List Wire) (value bit : Nat) (left right : BasisState)
    (hagrees : ∀ wire ∈ register, left wire = right wire) :
    registerMatchesFrom register value bit left =
      registerMatchesFrom register value bit right := by
  induction register generalizing bit with
  | nil => rfl
  | cons wire wires ih =>
      simp only [registerMatchesFrom]
      rw [hagrees wire (by simp), ih (bit := bit + 1)]
      intro next hnext
      exact hagrees next (by simp [hnext])

private theorem measuredStepPlain_registerMatches_congr
    (register : List Wire) (value : Nat) (left right : BasisState)
    (hagrees : ∀ wire ∈ register, left wire = right wire) :
    registerMatches register value left = registerMatches register value right := by
  exact measuredStepPlain_registerMatchesFrom_congr register value 0 left right hagrees

private theorem measuredStepPlain_matchXorState_clears
    (controls : List Wire) (value : Nat) (target : Wire)
    (initial middle : BasisState)
    (htarget : middle target = registerMatches controls value initial)
    (hcontrols : ∀ wire ∈ controls, middle wire = initial wire) :
    measuredStepPlain_matchXorState controls value target middle target = false := by
  have hpredicate := measuredStepPlain_registerMatches_congr controls value middle initial hcontrols
  simp [measuredStepPlain_matchXorState, htarget, hpredicate]

private theorem measuredStepPlain_wireAnd_congr
    (register : List Wire) (left right : BasisState)
    (hagrees : ∀ wire ∈ register, left wire = right wire) :
    wireAnd register left = wireAnd register right := by
  induction register with
  | nil => rfl
  | cons wire rest ih =>
      simp only [wireAnd]
      rw [hagrees wire (by simp), ih]
      intro next hnext
      exact hagrees next (by simp [hnext])

private theorem measuredStepPlain_rControlNonterminalPredicate_congr
    (conditions : List Wire) (value : Nat) (lengthRPrime : List Wire)
    (zeroRPrime : Wire) (left right : BasisState)
    (hzeroNotConditions : zeroRPrime ∉ conditions)
    (hconditions : ∀ wire ∈ conditions, left wire = right wire)
    (hlength : ∀ wire ∈ lengthRPrime, left wire = right wire) :
    rControlNonterminalPredicate conditions value lengthRPrime zeroRPrime left =
      rControlNonterminalPredicate conditions value lengthRPrime zeroRPrime right := by
  rw [rControlNonterminalPredicate_eq conditions value lengthRPrime zeroRPrime left
      hzeroNotConditions,
    rControlNonterminalPredicate_eq conditions value lengthRPrime zeroRPrime right
      hzeroNotConditions,
    measuredStepPlain_registerMatches_congr conditions (value % 2 ^ conditions.length) left right hconditions,
    measuredStepPlain_wireAnd_congr lengthRPrime left right hlength]

private theorem measuredStepPlain_rControlState_preserves
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ≠ control) :
    measuredStepPlain_rControlState conditions value control lengthRPrime zeroRPrime state wire =
      state wire := by
  simp [measuredStepPlain_rControlState, upd, hwire]

private theorem measuredStepPlain_windowSlice_mem
    (work : List Wire) (window : ActiveWindow) {wire : Wire}
    (hwire : wire ∈ IndexedStepRegisters.windowSlice work window) :
    wire ∈ work :=
  List.mem_of_mem_drop (List.mem_of_mem_take hwire)

private def measuredStepPlain_indexedStepPayload
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime

private def measuredStepPlain_indexedStepAfterPhase1
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime ++
        registers.aux

private def measuredStepPlain_indexedStepAfterPhase2
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.iter, registers.sign] ++ registers.work1 ++ registers.work2 ++
    registers.lengthT ++ registers.lengthQ ++ registers.lengthS ++
      registers.lengthRPrime ++ registers.aux

private def measuredStepPlain_indexedStepAfterSign
    (registers : IndexedStepRegisters) : List Wire :=
  registers.work1 ++ registers.work2 ++ registers.lengthT ++
    registers.lengthQ ++ registers.lengthS ++ registers.lengthRPrime ++
      registers.aux

private def measuredStepPlain_indexedStepBeforeLengthQ
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT

private def measuredStepPlain_indexedStepAfterLengthQ
    (registers : IndexedStepRegisters) : List Wire :=
  registers.lengthS ++ registers.lengthRPrime ++ registers.aux

private def measuredStepPlain_indexedStepBeforeLengthRPrime
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.iter, registers.sign] ++
    registers.work1 ++ registers.work2 ++ registers.lengthT ++
      registers.lengthQ ++ registers.lengthS

private theorem IndexedStepLayout.measuredStepPlain_phase1_ne_after
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ measuredStepPlain_indexedStepAfterPhase1 registers) :
    registers.phase1 ≠ wire := by
  have hphysical :
      (registers.phase1 :: measuredStepPlain_indexedStepAfterPhase1 registers).Nodup := by
    simpa [measuredStepPlain_indexedStepAfterPhase1, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  intro equality
  subst wire
  exact (List.nodup_cons.mp hphysical).1 hwire

private theorem IndexedStepLayout.measuredStepPlain_phase2_ne_after
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ measuredStepPlain_indexedStepAfterPhase2 registers) :
    registers.phase2 ≠ wire := by
  have hphysical :
      (registers.phase1 :: registers.phase2 ::
        measuredStepPlain_indexedStepAfterPhase2 registers).Nodup := by
    simpa [measuredStepPlain_indexedStepAfterPhase2, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  intro equality
  subst wire
  exact (List.nodup_cons.mp (List.nodup_cons.mp hphysical).2).1 hwire

private theorem IndexedStepLayout.measuredStepPlain_sign_ne_after
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ measuredStepPlain_indexedStepAfterSign registers) :
    registers.sign ≠ wire := by
  have hphysical :
      (registers.phase1 :: registers.phase2 :: registers.iter ::
        registers.sign :: measuredStepPlain_indexedStepAfterSign registers).Nodup := by
    simpa [measuredStepPlain_indexedStepAfterSign, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  intro equality
  subst wire
  exact (List.nodup_cons.mp
    (List.nodup_cons.mp
      (List.nodup_cons.mp
        (List.nodup_cons.mp hphysical).2).2).2).1 hwire

private theorem IndexedStepLayout.measuredStepPlain_lengthQ_ne_outside
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {lengthWire outsideWire : Wire}
    (hlength : lengthWire ∈ registers.lengthQ)
    (houtside : outsideWire ∈ measuredStepPlain_indexedStepBeforeLengthQ registers ∨
      outsideWire ∈ measuredStepPlain_indexedStepAfterLengthQ registers) :
    lengthWire ≠ outsideWire := by
  apply measuredStepPlain_nodup_middle_ne
    (before := measuredStepPlain_indexedStepBeforeLengthQ registers)
    (middle := registers.lengthQ)
    (after := measuredStepPlain_indexedStepAfterLengthQ registers) ?_ hlength houtside
  simpa [measuredStepPlain_indexedStepBeforeLengthQ, measuredStepPlain_indexedStepAfterLengthQ,
    IndexedStepRegisters.allWires, List.append_assoc] using hlayout.physical

private theorem IndexedStepLayout.measuredStepPlain_lengthRPrime_ne_outside
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {lengthWire outsideWire : Wire}
    (hlength : lengthWire ∈ registers.lengthRPrime)
    (houtside : outsideWire ∈ measuredStepPlain_indexedStepBeforeLengthRPrime registers ∨
      outsideWire ∈ registers.aux) :
    lengthWire ≠ outsideWire := by
  apply measuredStepPlain_nodup_middle_ne
    (before := measuredStepPlain_indexedStepBeforeLengthRPrime registers)
    (middle := registers.lengthRPrime)
    (after := registers.aux) ?_ hlength houtside
  simpa [measuredStepPlain_indexedStepBeforeLengthRPrime, IndexedStepRegisters.allWires,
    List.append_assoc] using hlayout.physical

private theorem IndexedStepLayout.measuredStepPlain_aux_not_payload
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {auxWire payloadWire : Wire}
    (haux : auxWire ∈ registers.aux)
    (hpayload : payloadWire ∈ measuredStepPlain_indexedStepPayload registers) :
    auxWire ≠ payloadWire := by
  have hphysical :
      (measuredStepPlain_indexedStepPayload registers ++ registers.aux).Nodup := by
    simpa [measuredStepPlain_indexedStepPayload, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  have hcross := (List.nodup_append.mp hphysical).2.2
  intro equality
  exact hcross payloadWire hpayload auxWire haux equality.symm

private theorem IndexedStepLayout.measuredStepPlain_aux_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) : registers.aux.Nodup := by
  have hphysical :
      (measuredStepPlain_indexedStepPayload registers ++ registers.aux).Nodup := by
    simpa [measuredStepPlain_indexedStepPayload, IndexedStepRegisters.allWires,
      List.append_assoc] using hlayout.physical
  exact (List.nodup_append.mp hphysical).2.1

private theorem measuredStepPlain_indexedStep_getD_mem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex

private theorem IndexedStepLayout.measuredStepPlain_control_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∈ registers.aux := by
  exact measuredStepPlain_indexedStep_getD_mem registers.aux 0 0 (by
    rw [hlayout.aux_length]
    omega)

private theorem IndexedStepLayout.measuredStepPlain_shiftEpoch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∈ registers.aux := by
  exact measuredStepPlain_indexedStep_getD_mem registers.aux 1 0 (by
    rw [hlayout.aux_length]
    omega)

private theorem IndexedStepLayout.measuredStepPlain_sourceScratch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.sourceScratch) :
    wire ∈ registers.aux := by
  exact List.mem_of_mem_take (List.mem_of_mem_drop hwire)

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.remainderRepairScratch) :
    wire ∈ registers.aux := by
  exact List.mem_of_mem_drop hwire

private theorem IndexedStepLayout.measuredStepPlain_blockScratch_mem_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.blockScratch) :
    wire ∈ registers.aux := by
  exact hlayout.measuredStepPlain_sourceScratch_mem_aux (List.mem_of_mem_drop hwire)

private theorem IndexedStepLayout.measuredStepPlain_sourceScratch_mem_sharedScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.sourceScratch) :
    wire ∈ registers.sharedScratch := by
  simp [IndexedStepRegisters.sharedScratch, hwire]

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_mem_sharedScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.remainderRepairScratch) :
    wire ∈ registers.sharedScratch := by
  simp [IndexedStepRegisters.sharedScratch, hwire]

private theorem IndexedStepLayout.measuredStepPlain_blockScratch_mem_sharedScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.blockScratch) :
    wire ∈ registers.sharedScratch := by
  exact hlayout.measuredStepPlain_sourceScratch_mem_sharedScratch (List.mem_of_mem_drop hwire)

private theorem IndexedStepLayout.measuredStepPlain_aux_view
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    [registers.control, registers.shiftEpoch] ++
        (registers.sourceScratch ++ registers.remainderRepairScratch) =
      registers.aux := by
  cases haux : registers.aux with
  | nil =>
      have hlength := hlayout.aux_length
      simp [haux] at hlength
  | cons first tail =>
      cases htail : tail with
      | nil =>
          have hlength := hlayout.aux_length
          simp [haux, htail] at hlength
      | cons second rest =>
          have hsplit := List.take_append_drop 18 rest
          simp [IndexedStepRegisters.control, IndexedStepRegisters.shiftEpoch,
            IndexedStepRegisters.sourceScratch,
            IndexedStepRegisters.remainderRepairScratch,
            haux, htail, hsplit]

private theorem IndexedStepLayout.measuredStepPlain_sourceScratch_length
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.sourceScratch.length = 18 := by
  simp [IndexedStepRegisters.sourceScratch, hlayout.aux_length]

private theorem IndexedStepLayout.measuredStepPlain_scratch_view
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal :: registers.blockScratch =
      registers.sourceScratch := by
  cases hscratch : registers.sourceScratch with
  | nil =>
      have hlength := hlayout.measuredStepPlain_sourceScratch_length
      simp [hscratch] at hlength
  | cons terminal rest =>
      simp [IndexedStepRegisters.terminal, IndexedStepRegisters.blockScratch,
        hscratch]

private theorem IndexedStepLayout.measuredStepPlain_aux_view_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ([registers.control, registers.shiftEpoch] ++
      (registers.sourceScratch ++ registers.remainderRepairScratch)).Nodup := by
  rw [hlayout.measuredStepPlain_aux_view]
  exact hlayout.measuredStepPlain_aux_nodup

private theorem IndexedStepLayout.measuredStepPlain_sourceAux_view_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ([registers.control, registers.shiftEpoch] ++
      registers.sourceScratch).Nodup := by
  have hfull := hlayout.measuredStepPlain_aux_view_nodup
  rw [← List.append_assoc] at hfull
  exact (List.nodup_append.mp hfull).1

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_not_sourceAux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ [registers.control, registers.shiftEpoch] ++
      registers.sourceScratch := by
  have hfull := hlayout.measuredStepPlain_aux_view_nodup
  rw [← List.append_assoc] at hfull
  have hcross := (List.nodup_append.mp hfull).2.2
  intro hsource
  exact hcross wire hsource wire hrepair rfl

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_not_sourceScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ registers.sourceScratch := by
  intro hsource
  exact hlayout.measuredStepPlain_remainderRepairScratch_not_sourceAux hrepair (by simp [hsource])

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_ne_control
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ≠ registers.control := by
  intro equality
  exact hlayout.measuredStepPlain_remainderRepairScratch_not_sourceAux hrepair (by simp [equality])

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ≠ registers.shiftEpoch := by
  intro equality
  exact hlayout.measuredStepPlain_remainderRepairScratch_not_sourceAux hrepair (by simp [equality])

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_not_payload
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ measuredStepPlain_indexedStepPayload registers := by
  intro hpayload
  exact (hlayout.measuredStepPlain_aux_not_payload
    (hlayout.measuredStepPlain_remainderRepairScratch_mem_aux hrepair) hpayload) rfl

private theorem IndexedStepLayout.measuredStepPlain_control_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.shiftEpoch := by
  have hnodup :
      (registers.control :: registers.shiftEpoch ::
        registers.sourceScratch).Nodup := by
    simpa only [List.cons_append, List.nil_append] using
      hlayout.measuredStepPlain_sourceAux_view_nodup
  intro equality
  exact (List.nodup_cons.mp hnodup).1 (by simp [equality])

private theorem IndexedStepLayout.measuredStepPlain_control_not_sourceScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.sourceScratch := by
  have hcross := (List.nodup_append.mp hlayout.measuredStepPlain_aux_view_nodup).2.2
  intro hmem
  exact hcross registers.control (by simp) registers.control
    (by simp [hmem]) rfl

private theorem IndexedStepLayout.measuredStepPlain_shiftEpoch_not_sourceScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.sourceScratch := by
  have hcross := (List.nodup_append.mp hlayout.measuredStepPlain_aux_view_nodup).2.2
  intro hmem
  exact hcross registers.shiftEpoch (by simp) registers.shiftEpoch
    (by simp [hmem]) rfl

private theorem IndexedStepLayout.measuredStepPlain_sourceScratch_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.sourceScratch.Nodup := by
  have htail :
      (registers.sourceScratch ++ registers.remainderRepairScratch).Nodup :=
    (List.nodup_append.mp hlayout.measuredStepPlain_aux_view_nodup).2.1
  exact (List.nodup_append.mp htail).1

private theorem IndexedStepLayout.measuredStepPlain_terminal_not_blockScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ registers.blockScratch := by
  have hnodup : (registers.terminal :: registers.blockScratch).Nodup := by
    rw [hlayout.measuredStepPlain_scratch_view]
    exact hlayout.measuredStepPlain_sourceScratch_nodup
  exact (List.nodup_cons.mp hnodup).1

private theorem IndexedStepLayout.measuredStepPlain_remainder_scratch_sub_aux
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    ∀ wire ∈ (registers.remainder window).scratch, wire ∈ registers.aux := by
  intro wire hwire
  have hsource := List.mem_of_mem_take hwire
  simp only [List.mem_cons, List.mem_append] at hsource
  rcases hsource with hshift | hsource | hrepair
  · rw [hshift]
    exact hlayout.measuredStepPlain_shiftEpoch_mem_aux
  · exact hlayout.measuredStepPlain_sourceScratch_mem_aux hsource
  · exact hlayout.measuredStepPlain_remainderRepairScratch_mem_aux hrepair

private theorem IndexedStepLayout.measuredStepPlain_control_not_remainder_scratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    registers.control ∉ (registers.remainder window).scratch := by
  subst window
  change (registers.remainder (certifiedActiveWindows n T).remainder).control ∉
    (registers.remainder (certifiedActiveWindows n T).remainder).scratch
  have hphysical := hlayout.remainder.physical
  rw [IntervalRegisters.allWires] at hphysical
  have hcross := (List.nodup_append.mp hphysical).2.2
  intro hscratch
  exact hcross
    (registers.remainder (certifiedActiveWindows n T).remainder).control (by simp)
    (registers.remainder (certifiedActiveWindows n T).remainder).control (by
      simp only [List.mem_append]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hscratch))))) rfl

private theorem IndexedStepLayout.measuredStepPlain_aux_outside_remainder
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (haux : wire ∈ registers.aux)
    (hcontrol : wire ≠ registers.control)
    (hscratch : wire ∉ (registers.remainder window).scratch) :
    wire ∉ (registers.remainder window).allWires := by
  intro hused
  simp only [IntervalRegisters.allWires, IndexedStepRegisters.measuredStepPlain_view_remainder, IndexedStepRegisters.measuredStepPlain_source_remainder,
    IndexedStepRegisters.measuredStepPlain_remainderBase, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hused
  rcases hused with hcontrols | hwork1 | hwork2 | hlengthT |
      hlengthQ | hlengthS | hscratchUsed
  · rcases hcontrols with hcontrolUsed | hsign
    · exact hcontrol hcontrolUsed
    · exact (hlayout.measuredStepPlain_aux_not_payload haux (by
        simp [measuredStepPlain_indexedStepPayload, hsign])) rfl
  · exact (hlayout.measuredStepPlain_aux_not_payload haux (by
      simp [measuredStepPlain_indexedStepPayload, measuredStepPlain_windowSlice_mem registers.work1 window hwork1])) rfl
  · exact (hlayout.measuredStepPlain_aux_not_payload haux (by
      simp [measuredStepPlain_indexedStepPayload, measuredStepPlain_windowSlice_mem registers.work2 window hwork2])) rfl
  · exact (hlayout.measuredStepPlain_aux_not_payload haux (by
      simp [measuredStepPlain_indexedStepPayload, hlengthT])) rfl
  · exact (hlayout.measuredStepPlain_aux_not_payload haux (by
      simp [measuredStepPlain_indexedStepPayload, hlengthQ])) rfl
  · exact (hlayout.measuredStepPlain_aux_not_payload haux (by
      simp [measuredStepPlain_indexedStepPayload, hlengthS])) rfl
  · exact hscratch hscratchUsed

private theorem IndexedStepLayout.measuredStepPlain_remainder_mem_after_phase1
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hwire : wire ∈ (registers.remainder window).allWires) :
    wire ∈ measuredStepPlain_indexedStepAfterPhase1 registers := by
  simp only [IntervalRegisters.allWires, IndexedStepRegisters.measuredStepPlain_view_remainder, IndexedStepRegisters.measuredStepPlain_source_remainder,
    IndexedStepRegisters.measuredStepPlain_remainderBase, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrols | hwork1 | hwork2 | hlengthT |
      hlengthQ | hlengthS | hscratch
  · rcases hcontrols with rfl | rfl
    · simp [measuredStepPlain_indexedStepAfterPhase1, hlayout.measuredStepPlain_control_mem_aux]
    · simp [measuredStepPlain_indexedStepAfterPhase1]
  · simp [measuredStepPlain_indexedStepAfterPhase1, measuredStepPlain_windowSlice_mem registers.work1 window hwork1]
  · simp [measuredStepPlain_indexedStepAfterPhase1, measuredStepPlain_windowSlice_mem registers.work2 window hwork2]
  · simp [measuredStepPlain_indexedStepAfterPhase1, hlengthT]
  · simp [measuredStepPlain_indexedStepAfterPhase1, hlengthQ]
  · simp [measuredStepPlain_indexedStepAfterPhase1, hlengthS]
  · simp [measuredStepPlain_indexedStepAfterPhase1,
      hlayout.measuredStepPlain_remainder_scratch_sub_aux window wire hscratch]

private theorem IndexedStepLayout.measuredStepPlain_remainder_mem_after_phase2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hwire : wire ∈ (registers.remainder window).allWires) :
    wire ∈ measuredStepPlain_indexedStepAfterPhase2 registers := by
  simp only [IntervalRegisters.allWires, IndexedStepRegisters.measuredStepPlain_view_remainder, IndexedStepRegisters.measuredStepPlain_source_remainder,
    IndexedStepRegisters.measuredStepPlain_remainderBase, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrols | hwork1 | hwork2 | hlengthT |
      hlengthQ | hlengthS | hscratch
  · rcases hcontrols with rfl | rfl
    · simp [measuredStepPlain_indexedStepAfterPhase2, hlayout.measuredStepPlain_control_mem_aux]
    · simp [measuredStepPlain_indexedStepAfterPhase2]
  · simp [measuredStepPlain_indexedStepAfterPhase2, measuredStepPlain_windowSlice_mem registers.work1 window hwork1]
  · simp [measuredStepPlain_indexedStepAfterPhase2, measuredStepPlain_windowSlice_mem registers.work2 window hwork2]
  · simp [measuredStepPlain_indexedStepAfterPhase2, hlengthT]
  · simp [measuredStepPlain_indexedStepAfterPhase2, hlengthQ]
  · simp [measuredStepPlain_indexedStepAfterPhase2, hlengthS]
  · simp [measuredStepPlain_indexedStepAfterPhase2,
      hlayout.measuredStepPlain_remainder_scratch_sub_aux window wire hscratch]

private theorem IndexedStepLayout.measuredStepPlain_phase1_not_remainder
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.phase1 ∉ (registers.remainder window).allWires := by
  intro hused
  exact (hlayout.measuredStepPlain_phase1_ne_after
    (hlayout.measuredStepPlain_remainder_mem_after_phase1 window hused)) rfl

private theorem IndexedStepLayout.measuredStepPlain_phase2_not_remainder
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.phase2 ∉ (registers.remainder window).allWires := by
  intro hused
  exact (hlayout.measuredStepPlain_phase2_ne_after
    (hlayout.measuredStepPlain_remainder_mem_after_phase2 window hused)) rfl

private theorem IndexedStepLayout.measuredStepPlain_lengthRPrime_not_remainder
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hwire : wire ∈ registers.lengthRPrime) :
    wire ∉ (registers.remainder window).allWires := by
  intro hused
  simp only [IntervalRegisters.allWires, IndexedStepRegisters.measuredStepPlain_view_remainder, IndexedStepRegisters.measuredStepPlain_source_remainder,
    IndexedStepRegisters.measuredStepPlain_remainderBase, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hused
  rcases hused with hcontrols | hwork1 | hwork2 | hlengthT |
      hlengthQ | hlengthS | hscratch
  · rcases hcontrols with hcontrol | hsign
    · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inr
        (hcontrol ▸ hlayout.measuredStepPlain_control_mem_aux))) rfl
    · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
        simp [measuredStepPlain_indexedStepBeforeLengthRPrime, hsign]))) rfl
  · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
      simp [measuredStepPlain_indexedStepBeforeLengthRPrime,
        measuredStepPlain_windowSlice_mem registers.work1 window hwork1]))) rfl
  · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
      simp [measuredStepPlain_indexedStepBeforeLengthRPrime,
        measuredStepPlain_windowSlice_mem registers.work2 window hwork2]))) rfl
  · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
      simp [measuredStepPlain_indexedStepBeforeLengthRPrime, hlengthT]))) rfl
  · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
      simp [measuredStepPlain_indexedStepBeforeLengthRPrime, hlengthQ]))) rfl
  · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
      simp [measuredStepPlain_indexedStepBeforeLengthRPrime, hlengthS]))) rfl
  · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inr
      (hlayout.measuredStepPlain_remainder_scratch_sub_aux window wire hscratch))) rfl

private theorem measuredStepPlain_remainderInterval_clean_auxAwayControl
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hclean : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      state wire = false) :
    ∀ wire ∈ registers.aux, wire ≠ registers.control →
      run (intervalAddSubUnitary (registers.remainder window) n
        window.start window.stop mode signUpdate .work1) state wire = false := by
  subst window
  let window := (certifiedActiveWindows n T).remainder
  have hready : IntervalReady (registers.remainder window) state := by
    intro wire hwire
    apply hclean wire (hlayout.measuredStepPlain_remainder_scratch_sub_aux window wire hwire)
    intro equality
    subst wire
    exact hlayout.measuredStepPlain_control_not_remainder_scratch window rfl hwire
  have houtputReady := intervalAddSubUnitary_ready (registers.remainder window) n
    window.start window.stop mode signUpdate .work1 state hlayout.remainder hready
  intro wire haux hcontrol
  by_cases hscratch : wire ∈ (registers.remainder window).scratch
  · exact houtputReady wire hscratch
  · rw [intervalAddSubUnitary_preservesOutside (registers.remainder window) n
      window.start window.stop mode signUpdate .work1 state hlayout.remainder
      (hlayout.measuredStepPlain_aux_outside_remainder window haux hcontrol hscratch)]
    exact hclean wire haux hcontrol

private theorem IndexedStepLayout.measuredStepPlain_terminalPadding_scratch_sub_block
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.terminalPadding.scratch,
      wire ∈ registers.blockScratch := by
  intro wire hwire
  change wire ∈
    registers.blockScratch.getD 0 0 ::
      ((registers.blockScratch.drop 1).take
          (registers.lengthS.length - 2) ++
        [registers.blockScratch.getD (registers.lengthS.length - 1) 0]) at hwire
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hwire
  rcases hwire with hwrapped | htail | hextra
  · rw [hwrapped]
    exact measuredStepPlain_indexedStep_getD_mem registers.blockScratch 0 0 (by
      have := hlayout.terminalPaddingCapacity
      omega)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take htail)
  · rw [hextra]
    exact measuredStepPlain_indexedStep_getD_mem registers.blockScratch
      (registers.lengthS.length - 1) 0 (by
        have := hlayout.terminalPaddingCapacity
        omega)

private theorem IndexedStepLayout.measuredStepPlain_terminalPadding_support_intersection
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.blockScratch,
      wire ∈ registers.terminalPadding.usedWires →
        wire ∈ registers.terminalPadding.scratch := by
  intro wire hblock hsupport
  rw [TerminalPaddingRegisters.usedWires] at hsupport
  rcases List.mem_append.mp hsupport with hprefix | hscratch
  · rcases List.mem_append.mp hprefix with hhead | hlength
    · rcases List.mem_cons.mp hhead with hterminal | hhead
      · subst wire
        exact (hlayout.measuredStepPlain_terminal_not_blockScratch hblock).elim
      · rcases List.mem_cons.mp hhead with hepoch | hwork
        · subst wire
          exact (hlayout.measuredStepPlain_shiftEpoch_not_sourceScratch
            (List.mem_of_mem_drop hblock)).elim
        · change wire ∈ registers.work2 at hwork
          exact (hlayout.measuredStepPlain_aux_not_payload (auxWire := wire) (payloadWire := wire)
            (hlayout.measuredStepPlain_blockScratch_mem_aux hblock)
            (by simp [measuredStepPlain_indexedStepPayload, hwork]) rfl).elim
    · change wire ∈ registers.lengthS at hlength
      exact (hlayout.measuredStepPlain_aux_not_payload (auxWire := wire) (payloadWire := wire)
        (hlayout.measuredStepPlain_blockScratch_mem_aux hblock)
        (by simp [measuredStepPlain_indexedStepPayload, hlength]) rfl).elim
  · exact hscratch

private theorem IndexedStepLayout.measuredStepPlain_preShift_scratch_sub_block
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.preShift.scratch,
      wire ∈ registers.blockScratch := by
  have hreserved :
      ((registers.blockScratch.drop (registers.lengthS.length + 1)).take 3).length = 3 := by
    simpa [IndexedStepRegisters.preShift] using hlayout.preShift.reserved_size
  have hblockLength : registers.lengthS.length + 4 ≤ registers.blockScratch.length := by
    simp only [List.length_take, List.length_drop] at hreserved
    omega
  intro wire hwire
  change wire ∈
    [registers.blockScratch.getD 0 0, registers.blockScratch.getD 1 0] ++
      (registers.blockScratch.drop 2).take (registers.lengthS.length - 1) ++
        (registers.blockScratch.drop (registers.lengthS.length + 1)).take 3 at hwire
  rcases List.mem_append.mp hwire with hprefix | hreservedWire
  · rcases List.mem_append.mp hprefix with hflag | hcarry
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hflag
      rcases hflag with hzero | hboth
      · rw [hzero]
        exact measuredStepPlain_indexedStep_getD_mem registers.blockScratch 0 0 (by omega)
      · rw [hboth]
        exact measuredStepPlain_indexedStep_getD_mem registers.blockScratch 1 0 (by omega)
    · exact List.mem_of_mem_drop (List.mem_of_mem_take hcarry)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hreservedWire)

private theorem IndexedStepLayout.measuredStepPlain_preShift_support_intersection
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.blockScratch,
      wire ∈ registers.preShift.preUsedWires →
        wire ∈ registers.preShift.scratch := by
  intro wire hblock hsupport
  by_cases hscratch : wire ∈ registers.preShift.scratch
  · exact hscratch
  · have hpayload : wire ∈ measuredStepPlain_indexedStepPayload registers := by
      change wire ∈
        [registers.phase1, registers.blockScratch.getD 0 0,
          registers.phase2, registers.blockScratch.getD 1 0] ++
          registers.work2 ++ registers.lengthS ++
            (registers.blockScratch.drop 2).take
              (registers.lengthS.length - 1) at hsupport
      change wire ∉
        [registers.blockScratch.getD 0 0, registers.blockScratch.getD 1 0] ++
          (registers.blockScratch.drop 2).take (registers.lengthS.length - 1) ++
            (registers.blockScratch.drop (registers.lengthS.length + 1)).take 3
          at hscratch
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hsupport hscratch
      simp only [measuredStepPlain_indexedStepPayload, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      aesop
    exact (hlayout.measuredStepPlain_aux_not_payload (auxWire := wire) (payloadWire := wire)
      (hlayout.measuredStepPlain_blockScratch_mem_aux hblock) hpayload rfl).elim

private theorem IndexedStepLayout.measuredStepPlain_postShift_scratch_sub_source
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.postShift.scratch,
      wire ∈ registers.sourceScratch := by
  have hreserved :
      ((registers.sourceScratch.drop (registers.lengthS.length + 1)).take 3).length =
        3 := by
    simpa [IndexedStepRegisters.postShift] using hlayout.postShift.reserved_size
  have hsourceLength :
      registers.lengthS.length + 4 ≤ registers.sourceScratch.length := by
    simp only [List.length_take, List.length_drop] at hreserved
    omega
  intro wire hwire
  change wire ∈
    [registers.sourceScratch.getD registers.lengthS.length 0,
      registers.sourceScratch.getD 0 0] ++
      (registers.sourceScratch.drop 1).take (registers.lengthS.length - 1) ++
        (registers.sourceScratch.drop (registers.lengthS.length + 1)).take 3 at hwire
  rcases List.mem_append.mp hwire with hprefix | hreservedWire
  · rcases List.mem_append.mp hprefix with hflag | hcarry
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hflag
      rcases hflag with hzero | hboth
      · rw [hzero]
        exact measuredStepPlain_indexedStep_getD_mem registers.sourceScratch
          registers.lengthS.length 0 (by omega)
      · rw [hboth]
        exact measuredStepPlain_indexedStep_getD_mem registers.sourceScratch 0 0 (by omega)
    · exact List.mem_of_mem_drop (List.mem_of_mem_take hcarry)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hreservedWire)

private theorem IndexedStepLayout.measuredStepPlain_postShift_support_intersection
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.sharedScratch,
      wire ∈ registers.postShift.postUsedWires →
        wire ∈ registers.postShift.scratch := by
  intro wire hshared hsupport
  by_cases hscratch : wire ∈ registers.postShift.scratch
  · exact hscratch
  · have haux : wire ∈ registers.aux := by
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
        List.mem_append] at hshared
      rcases hshared with rfl | hsource | hrepair
      · exact hlayout.measuredStepPlain_control_mem_aux
      · exact hlayout.measuredStepPlain_sourceScratch_mem_aux hsource
      · exact hlayout.measuredStepPlain_remainderRepairScratch_mem_aux hrepair
    have hpayload : wire ∈ measuredStepPlain_indexedStepPayload registers := by
      change wire ∈
        [registers.phase1, registers.phase2,
          registers.sourceScratch.getD 0 0] ++
          registers.work2 ++ registers.lengthS ++
            (registers.sourceScratch.drop 1).take
              (registers.lengthS.length - 1) at hsupport
      change wire ∉
        [registers.sourceScratch.getD registers.lengthS.length 0,
          registers.sourceScratch.getD 0 0] ++
          (registers.sourceScratch.drop 1).take
              (registers.lengthS.length - 1) ++
            (registers.sourceScratch.drop
              (registers.lengthS.length + 1)).take 3 at hscratch
      simp only [measuredStepPlain_indexedStepPayload, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hsupport hscratch ⊢
      aesop
    exact (hlayout.measuredStepPlain_aux_not_payload (auxWire := wire) (payloadWire := wire)
      haux hpayload rfl).elim

private theorem IndexedStepLayout.measuredStepPlain_phaseUpdate_scratch_sub_source
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.phaseUpdate.scratch,
      wire ∈ registers.sourceScratch := by
  intro wire hwire
  change wire ∈
    [registers.sourceScratch.getD 0 0, registers.sourceScratch.getD 1 0,
      registers.sourceScratch.getD 2 0, registers.sourceScratch.getD 3 0,
      registers.sourceScratch.getD 4 0] ++
        (registers.sourceScratch.drop 5).take
          registers.phaseEqualityScratchSize at hwire
  rcases List.mem_append.mp hwire with hhead | htail
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
    rcases hhead with hzeroQ | hzeroRPrime | hzeroS | hcondition | htemporary
    · rw [hzeroQ]
      exact measuredStepPlain_indexedStep_getD_mem registers.sourceScratch 0 0 (by
        rw [hlayout.measuredStepPlain_sourceScratch_length]
        omega)
    · rw [hzeroRPrime]
      exact measuredStepPlain_indexedStep_getD_mem registers.sourceScratch 1 0 (by
        rw [hlayout.measuredStepPlain_sourceScratch_length]
        omega)
    · rw [hzeroS]
      exact measuredStepPlain_indexedStep_getD_mem registers.sourceScratch 2 0 (by
        rw [hlayout.measuredStepPlain_sourceScratch_length]
        omega)
    · rw [hcondition]
      exact measuredStepPlain_indexedStep_getD_mem registers.sourceScratch 3 0 (by
        rw [hlayout.measuredStepPlain_sourceScratch_length]
        omega)
    · rw [htemporary]
      exact measuredStepPlain_indexedStep_getD_mem registers.sourceScratch 4 0 (by
        rw [hlayout.measuredStepPlain_sourceScratch_length]
        omega)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take htail)

private theorem IndexedStepLayout.measuredStepPlain_tBoundary_usedScratch_sub_block
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.tBoundary.usedScratch,
      wire ∈ registers.blockScratch := by
  intro wire hwire
  change wire ∈
    registers.blockScratch.take registers.lengthT.length ++
      [registers.blockScratch.getD registers.lengthT.length 0] at hwire
  rcases List.mem_append.mp hwire with hconstants | hcarry
  · exact List.mem_of_mem_take hconstants
  · simp only [List.mem_singleton] at hcarry
    rw [hcarry]
    exact measuredStepPlain_indexedStep_getD_mem registers.blockScratch registers.lengthT.length 0
      (by simpa [IndexedStepRegisters.tBoundary, TBoundaryRegisters.width] using
        hlayout.tBoundary.scratch_capacity)

private theorem IndexedStepLayout.measuredStepPlain_tBoundary_words_nodup
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    (registers.lengthT ++ registers.lengthRPrime).Nodup := by
  have hswap :
      (registers.phase2 :: registers.lengthT ++ registers.lengthRPrime).Nodup := by
    apply List.Nodup.sublist ?_ hlayout.tBoundary.physical
    unfold TBoundaryRegisters.allWires
    simpa only [IndexedStepRegisters.tBoundary, List.nil_append,
      List.cons_append, List.append_assoc] using
      List.Sublist.cons₂ registers.phase2
        (List.Sublist.cons registers.tBoundary.carry
          (List.sublist_append_right
            (registers.tBoundary.constants ++ registers.tBoundary.lengthSLow)
            (registers.lengthT ++ registers.lengthRPrime)))
  exact (List.nodup_cons.mp hswap).2

private theorem IndexedStepLayout.measuredStepPlain_coefficient_scratch_sub_block
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    ∀ wire ∈ (registers.coefficient window).scratch,
      wire ∈ registers.blockScratch := by
  intro wire hwire
  exact List.mem_of_mem_take hwire

private theorem IndexedStepLayout.measuredStepPlain_blockScratch_outside_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hblock : wire ∈ registers.blockScratch)
    (hscratch : wire ∉ (registers.coefficient window).scratch) :
    wire ∉ (registers.coefficient window).allWires := by
  intro hused
  change wire ∈
    [registers.control, registers.sign] ++
      (IndexedStepRegisters.windowSlice registers.work1 window ++
        (IndexedStepRegisters.windowSlice registers.work2 window ++
          (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
  rcases List.mem_append.mp hused with hfixed | hrest
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with hcontrol | hsign
    · subst wire
      exact hlayout.measuredStepPlain_control_not_sourceScratch (List.mem_of_mem_drop hblock)
    · exact (hlayout.measuredStepPlain_aux_not_payload
        (hlayout.measuredStepPlain_blockScratch_mem_aux hblock)
        (by simp [measuredStepPlain_indexedStepPayload, hsign])) rfl
  · rcases List.mem_append.mp hrest with hwork1 | hrest
    · exact (hlayout.measuredStepPlain_aux_not_payload
        (hlayout.measuredStepPlain_blockScratch_mem_aux hblock)
        (by simp [measuredStepPlain_indexedStepPayload,
          measuredStepPlain_windowSlice_mem registers.work1 window hwork1])) rfl
    · rcases List.mem_append.mp hrest with hwork2 | hrest
      · exact (hlayout.measuredStepPlain_aux_not_payload
          (hlayout.measuredStepPlain_blockScratch_mem_aux hblock)
          (by simp [measuredStepPlain_indexedStepPayload,
            measuredStepPlain_windowSlice_mem registers.work2 window hwork2])) rfl
      · rcases List.mem_append.mp hrest with hlengthT | hscratchUsed
        · exact (hlayout.measuredStepPlain_aux_not_payload
            (hlayout.measuredStepPlain_blockScratch_mem_aux hblock)
            (by simp [measuredStepPlain_indexedStepPayload, hlengthT])) rfl
        · exact hscratch hscratchUsed

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_not_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow)
    {wire : Wire} (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ (registers.coefficient window).allWires := by
  intro hused
  have hnotPayload := hlayout.measuredStepPlain_remainderRepairScratch_not_payload hrepair
  have hnotSource := hlayout.measuredStepPlain_remainderRepairScratch_not_sourceScratch hrepair
  change wire ∈
    [registers.control, registers.sign] ++
      (IndexedStepRegisters.windowSlice registers.work1 window ++
        (IndexedStepRegisters.windowSlice registers.work2 window ++
          (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
  rcases List.mem_append.mp hused with hfixed | hrest
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with hcontrol | hsign
    · exact (hlayout.measuredStepPlain_remainderRepairScratch_ne_control hrepair hcontrol).elim
    · exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, hsign])
  · rcases List.mem_append.mp hrest with hwork1 | hrest
    · exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload,
        measuredStepPlain_windowSlice_mem registers.work1 window hwork1])
    · rcases List.mem_append.mp hrest with hwork2 | hrest
      · exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload,
          measuredStepPlain_windowSlice_mem registers.work2 window hwork2])
      · rcases List.mem_append.mp hrest with hlengthT | hscratch
        · exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, hlengthT])
        · exact hnotSource (List.mem_of_mem_drop
            (hlayout.measuredStepPlain_coefficient_scratch_sub_block window wire hscratch))

private theorem IndexedStepLayout.measuredStepPlain_phase1_not_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.phase1 ∉ (registers.coefficient window).allWires := by
  intro hused
  have hafter : registers.phase1 ∈ measuredStepPlain_indexedStepAfterPhase1 registers := by
    change registers.phase1 ∈
      [registers.control, registers.sign] ++
        (IndexedStepRegisters.windowSlice registers.work1 window ++
          (IndexedStepRegisters.windowSlice registers.work2 window ++
            (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
    rcases List.mem_append.mp hused with hfixed | hrest
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
      rcases hfixed with hcontrol | hsign
      · rw [hcontrol]
        simp [measuredStepPlain_indexedStepAfterPhase1, hlayout.measuredStepPlain_control_mem_aux]
      · simp [measuredStepPlain_indexedStepAfterPhase1, hsign]
    · rcases List.mem_append.mp hrest with hwork1 | hrest
      · simp [measuredStepPlain_indexedStepAfterPhase1,
          measuredStepPlain_windowSlice_mem registers.work1 window hwork1]
      · rcases List.mem_append.mp hrest with hwork2 | hrest
        · simp [measuredStepPlain_indexedStepAfterPhase1,
            measuredStepPlain_windowSlice_mem registers.work2 window hwork2]
        · rcases List.mem_append.mp hrest with hlengthT | hscratch
          · simp [measuredStepPlain_indexedStepAfterPhase1, hlengthT]
          · simp [measuredStepPlain_indexedStepAfterPhase1,
              hlayout.measuredStepPlain_blockScratch_mem_aux
                (hlayout.measuredStepPlain_coefficient_scratch_sub_block window _ hscratch)]
  exact (hlayout.measuredStepPlain_phase1_ne_after hafter) rfl

private theorem IndexedStepLayout.measuredStepPlain_phase2_not_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.phase2 ∉ (registers.coefficient window).allWires := by
  intro hused
  have hafter : registers.phase2 ∈ measuredStepPlain_indexedStepAfterPhase2 registers := by
    change registers.phase2 ∈
      [registers.control, registers.sign] ++
        (IndexedStepRegisters.windowSlice registers.work1 window ++
          (IndexedStepRegisters.windowSlice registers.work2 window ++
            (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
    rcases List.mem_append.mp hused with hfixed | hrest
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
      rcases hfixed with hcontrol | hsign
      · rw [hcontrol]
        simp [measuredStepPlain_indexedStepAfterPhase2, hlayout.measuredStepPlain_control_mem_aux]
      · simp [measuredStepPlain_indexedStepAfterPhase2, hsign]
    · rcases List.mem_append.mp hrest with hwork1 | hrest
      · simp [measuredStepPlain_indexedStepAfterPhase2,
          measuredStepPlain_windowSlice_mem registers.work1 window hwork1]
      · rcases List.mem_append.mp hrest with hwork2 | hrest
        · simp [measuredStepPlain_indexedStepAfterPhase2,
            measuredStepPlain_windowSlice_mem registers.work2 window hwork2]
        · rcases List.mem_append.mp hrest with hlengthT | hscratch
          · simp [measuredStepPlain_indexedStepAfterPhase2, hlengthT]
          · simp [measuredStepPlain_indexedStepAfterPhase2,
              hlayout.measuredStepPlain_blockScratch_mem_aux
                (hlayout.measuredStepPlain_coefficient_scratch_sub_block window _ hscratch)]
  exact (hlayout.measuredStepPlain_phase2_ne_after hafter) rfl

private theorem IndexedStepLayout.measuredStepPlain_terminal_not_coefficient
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) (window : ActiveWindow) :
    registers.terminal ∉ (registers.coefficient window).allWires := by
  intro hused
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.measuredStepPlain_scratch_view]
    simp
  have hterminalAux := hlayout.measuredStepPlain_sourceScratch_mem_aux hterminalSource
  change registers.terminal ∈
    [registers.control, registers.sign] ++
      (IndexedStepRegisters.windowSlice registers.work1 window ++
        (IndexedStepRegisters.windowSlice registers.work2 window ++
          (registers.lengthT ++ (registers.coefficient window).scratch))) at hused
  rcases List.mem_append.mp hused with hfixed | hrest
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with hcontrol | hsign
    · exact hlayout.measuredStepPlain_control_not_sourceScratch
        (hcontrol ▸ hterminalSource)
    · exact (hlayout.measuredStepPlain_aux_not_payload hterminalAux
        (by simp [measuredStepPlain_indexedStepPayload, hsign])) rfl
  · rcases List.mem_append.mp hrest with hwork1 | hrest
    · exact (hlayout.measuredStepPlain_aux_not_payload hterminalAux
        (by simp [measuredStepPlain_indexedStepPayload,
          measuredStepPlain_windowSlice_mem registers.work1 window hwork1])) rfl
    · rcases List.mem_append.mp hrest with hwork2 | hrest
      · exact (hlayout.measuredStepPlain_aux_not_payload hterminalAux
          (by simp [measuredStepPlain_indexedStepPayload,
            measuredStepPlain_windowSlice_mem registers.work2 window hwork2])) rfl
      · rcases List.mem_append.mp hrest with hlengthT | hscratch
        · exact (hlayout.measuredStepPlain_aux_not_payload hterminalAux
            (by simp [measuredStepPlain_indexedStepPayload, hlengthT])) rfl
        · exact hlayout.measuredStepPlain_terminal_not_blockScratch
            (hlayout.measuredStepPlain_coefficient_scratch_sub_block window _ hscratch)

private def measuredStepPlain_indexedStepShiftPayload
    (registers : IndexedStepRegisters) : List Wire :=
  [registers.phase1, registers.phase2] ++ registers.work2 ++ registers.lengthS

private theorem IndexedStepLayout.measuredStepPlain_preShift_used_payload_or_scratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ registers.preShift.preUsedWires) :
    wire ∈ measuredStepPlain_indexedStepShiftPayload registers ∨
      wire ∈ registers.preShift.scratch := by
  simp only [ShiftRegisters.preUsedWires, ShiftRegisters.scratch,
    IndexedStepRegisters.preShift, measuredStepPlain_indexedStepShiftPayload,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
  aesop

private theorem IndexedStepLayout.measuredStepPlain_remainderRepairScratch_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hrepair : wire ∈ registers.remainderRepairScratch) :
    wire ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.measuredStepPlain_preShift_used_payload_or_scratch hused with hpayload | hscratch
  · apply hlayout.measuredStepPlain_remainderRepairScratch_not_payload hrepair
    simp only [measuredStepPlain_indexedStepShiftPayload, measuredStepPlain_indexedStepPayload,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpayload ⊢
    aesop
  · apply hlayout.measuredStepPlain_remainderRepairScratch_not_sourceScratch hrepair
    exact List.mem_of_mem_drop
      (hlayout.measuredStepPlain_preShift_scratch_sub_block wire hscratch)

private theorem IndexedStepLayout.measuredStepPlain_lengthRPrime_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T)
    {wire : Wire} (hwire : wire ∈ registers.lengthRPrime) :
    wire ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.measuredStepPlain_preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
      simp only [measuredStepPlain_indexedStepShiftPayload, measuredStepPlain_indexedStepBeforeLengthRPrime,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpayload ⊢
      aesop))) rfl
  · exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inr
      (hlayout.measuredStepPlain_blockScratch_mem_aux
        (hlayout.measuredStepPlain_preShift_scratch_sub_block wire hscratch)))) rfl

private theorem IndexedStepLayout.measuredStepPlain_quotientLow_mem_lengthQ
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∈ registers.lengthQ :=
  measuredStepPlain_indexedStep_getD_mem registers.lengthQ 0 0 hlayout.lengthQ_positive

private theorem IndexedStepLayout.measuredStepPlain_quotientLow_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.measuredStepPlain_preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.measuredStepPlain_lengthQ_ne_outside hlayout.measuredStepPlain_quotientLow_mem_lengthQ (by
      simp only [measuredStepPlain_indexedStepShiftPayload, measuredStepPlain_indexedStepBeforeLengthQ,
        measuredStepPlain_indexedStepAfterLengthQ, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hpayload ⊢
      aesop)) rfl
  · exact (hlayout.measuredStepPlain_lengthQ_ne_outside hlayout.measuredStepPlain_quotientLow_mem_lengthQ
      (Or.inr (by
        have haux := hlayout.measuredStepPlain_blockScratch_mem_aux
          (hlayout.measuredStepPlain_preShift_scratch_sub_block registers.quotientLow hscratch)
        simp [measuredStepPlain_indexedStepAfterLengthQ, haux]))) rfl

private theorem IndexedStepLayout.measuredStepPlain_terminal_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.measuredStepPlain_preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.measuredStepPlain_aux_not_payload
      (auxWire := registers.terminal) (payloadWire := registers.terminal)
      (hlayout.measuredStepPlain_sourceScratch_mem_aux (by rw [← hlayout.measuredStepPlain_scratch_view]; simp))
      (by
        simp only [measuredStepPlain_indexedStepPayload,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        simp only [measuredStepPlain_indexedStepShiftPayload, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hpayload
        aesop)) rfl
  · exact hlayout.measuredStepPlain_terminal_not_blockScratch
      (hlayout.measuredStepPlain_preShift_scratch_sub_block registers.terminal hscratch)

private theorem IndexedStepLayout.measuredStepPlain_shiftEpoch_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.measuredStepPlain_preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.measuredStepPlain_aux_not_payload
      (auxWire := registers.shiftEpoch) (payloadWire := registers.shiftEpoch)
      hlayout.measuredStepPlain_shiftEpoch_mem_aux (by
      simp only [measuredStepPlain_indexedStepShiftPayload, measuredStepPlain_indexedStepPayload,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpayload ⊢
      aesop)) rfl
  · exact hlayout.measuredStepPlain_shiftEpoch_not_sourceScratch
      (List.mem_of_mem_drop
        (hlayout.measuredStepPlain_preShift_scratch_sub_block registers.shiftEpoch hscratch))

private theorem IndexedStepLayout.measuredStepPlain_phase1_not_blockScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.phase1 ∉ registers.blockScratch := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.phase1) (payloadWire := registers.phase1)
    (hlayout.measuredStepPlain_blockScratch_mem_aux hmem)
    (by simp [measuredStepPlain_indexedStepPayload]) rfl).elim

private theorem IndexedStepLayout.measuredStepPlain_quotientLow_not_blockScratch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ registers.blockScratch := by
  intro hmem
  have hlow : registers.quotientLow ∈ registers.lengthQ := by
    exact measuredStepPlain_indexedStep_getD_mem registers.lengthQ 0 0 hlayout.lengthQ_positive
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.quotientLow) (payloadWire := registers.quotientLow)
    (hlayout.measuredStepPlain_blockScratch_mem_aux hmem)
    (by simp [measuredStepPlain_indexedStepPayload, hlow]) rfl).elim

private theorem IndexedStepLayout.measuredStepPlain_blockScratch_outside_terminalEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    ∀ wire ∈ registers.blockScratch,
      wire ∉ [registers.terminal, registers.shiftEpoch,
        registers.quotientLow] := by
  intro wire hwire
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  constructor
  · intro equality
    subst wire
    exact hlayout.measuredStepPlain_terminal_not_blockScratch hwire
  constructor
  · intro equality
    subst wire
    exact hlayout.measuredStepPlain_shiftEpoch_not_sourceScratch (List.mem_of_mem_drop hwire)
  · intro equality
    subst wire
    exact hlayout.measuredStepPlain_quotientLow_not_blockScratch hwire

private theorem measuredStepPlain_terminalPaddingForwardState_shiftEpoch_of_terminal_false
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hterminal : state registers.terminal = false)
    (hepochWork : registers.shiftEpoch ∉ registers.work2)
    (hepochLength : registers.shiftEpoch ∉ registers.lengthS)
    (hterminalWork : registers.terminal ∉ registers.work2)
    (hterminalLength : registers.terminal ∉ registers.lengthS) :
    terminalPaddingForwardState registers state registers.shiftEpoch =
      state registers.shiftEpoch := by
  unfold terminalPaddingForwardState
  simp only [upd_same]
  rw [measuredStepPlain_writeReg_apply_outside _ _ _ hepochLength,
    measuredStepPlain_writeReg_apply_outside _ _ _ hepochWork,
    measuredStepPlain_writeReg_apply_outside _ _ _ hterminalLength,
    measuredStepPlain_writeReg_apply_outside _ _ _ hterminalWork, hterminal]
  simp

private theorem IndexedStepLayout.measuredStepPlain_phase1_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.phase1 ∉ registers.work2 := by
  intro hmem
  exact (hlayout.measuredStepPlain_phase1_ne_after (by
    simp [measuredStepPlain_indexedStepAfterPhase1, hmem])) rfl

private theorem IndexedStepLayout.measuredStepPlain_phase1_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.phase1 ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.measuredStepPlain_phase1_ne_after (by
    simp [measuredStepPlain_indexedStepAfterPhase1, hmem])) rfl

private theorem IndexedStepLayout.measuredStepPlain_phase1_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.phase1 ≠ registers.shiftEpoch := by
  exact hlayout.measuredStepPlain_phase1_ne_after (by
    simp [measuredStepPlain_indexedStepAfterPhase1, hlayout.measuredStepPlain_shiftEpoch_mem_aux])

private theorem IndexedStepLayout.measuredStepPlain_lengthRPrime_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ registers.lengthRPrime) : wire ∉ registers.work2 := by
  intro hmem
  exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
    simp [measuredStepPlain_indexedStepBeforeLengthRPrime, hmem]))) rfl

private theorem IndexedStepLayout.measuredStepPlain_lengthRPrime_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ registers.lengthRPrime) : wire ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
    simp [measuredStepPlain_indexedStepBeforeLengthRPrime, hmem]))) rfl

private theorem IndexedStepLayout.measuredStepPlain_lengthRPrime_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ registers.lengthRPrime) : wire ≠ registers.shiftEpoch := by
  exact hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inr hlayout.measuredStepPlain_shiftEpoch_mem_aux)

private theorem IndexedStepLayout.measuredStepPlain_quotientLow_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ registers.work2 := by
  intro hmem
  exact (hlayout.measuredStepPlain_lengthQ_ne_outside hlayout.measuredStepPlain_quotientLow_mem_lengthQ
    (Or.inl (by simp [measuredStepPlain_indexedStepBeforeLengthQ, hmem]))) rfl

private theorem IndexedStepLayout.measuredStepPlain_quotientLow_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.measuredStepPlain_lengthQ_ne_outside hlayout.measuredStepPlain_quotientLow_mem_lengthQ
    (Or.inr (by simp [measuredStepPlain_indexedStepAfterLengthQ, hmem]))) rfl

private theorem IndexedStepLayout.measuredStepPlain_quotientLow_ne_shiftEpoch
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ≠ registers.shiftEpoch := by
  exact hlayout.measuredStepPlain_lengthQ_ne_outside hlayout.measuredStepPlain_quotientLow_mem_lengthQ
    (Or.inr (by simp [measuredStepPlain_indexedStepAfterLengthQ, hlayout.measuredStepPlain_shiftEpoch_mem_aux]))

private theorem IndexedStepLayout.measuredStepPlain_terminalCondition_payload
    {registers : IndexedStepRegisters} {n T : Nat}
    (_hlayout : IndexedStepLayout registers n T) {wire : Wire}
    (hwire : wire ∈ measuredStepPlain_terminalConditionWires registers) :
    wire ∈ measuredStepPlain_indexedStepPayload registers := by
  simp only [measuredStepPlain_terminalConditionWires, measuredStepPlain_indexedStepPayload,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
  aesop

private theorem IndexedStepLayout.measuredStepPlain_control_ne_phase1
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.phase1 := by
  exact hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.control) (payloadWire := registers.phase1)
    hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])

private theorem IndexedStepLayout.measuredStepPlain_control_ne_quotientLow
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.quotientLow := by
  exact hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.control) (payloadWire := registers.quotientLow)
    hlayout.measuredStepPlain_control_mem_aux (by
      simp [measuredStepPlain_indexedStepPayload, hlayout.measuredStepPlain_quotientLow_mem_lengthQ])

private theorem IndexedStepLayout.measuredStepPlain_control_ne_terminal
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ≠ registers.terminal := by
  intro equality
  apply hlayout.measuredStepPlain_control_not_sourceScratch
  rw [equality, ← hlayout.measuredStepPlain_scratch_view]
  simp

private theorem IndexedStepLayout.measuredStepPlain_control_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.work2 := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.control) (payloadWire := registers.control)
    hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.measuredStepPlain_control_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.control) (payloadWire := registers.control)
    hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.measuredStepPlain_control_not_preShift
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.control ∉ registers.preShift.preUsedWires := by
  intro hused
  rcases hlayout.measuredStepPlain_preShift_used_payload_or_scratch hused with hpayload | hscratch
  · exact (hlayout.measuredStepPlain_aux_not_payload
      (auxWire := registers.control) (payloadWire := registers.control)
      hlayout.measuredStepPlain_control_mem_aux (by
        simp only [measuredStepPlain_indexedStepShiftPayload, measuredStepPlain_indexedStepPayload,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpayload ⊢
        aesop)) rfl
  · exact hlayout.measuredStepPlain_control_not_sourceScratch
      (List.mem_of_mem_drop
        (hlayout.measuredStepPlain_preShift_scratch_sub_block registers.control hscratch))

private theorem IndexedStepLayout.measuredStepPlain_shiftEpoch_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.work2 := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.shiftEpoch) (payloadWire := registers.shiftEpoch)
    hlayout.measuredStepPlain_shiftEpoch_mem_aux (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.measuredStepPlain_shiftEpoch_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.shiftEpoch) (payloadWire := registers.shiftEpoch)
    hlayout.measuredStepPlain_shiftEpoch_mem_aux (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.measuredStepPlain_terminal_not_work2
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ registers.work2 := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.terminal) (payloadWire := registers.terminal)
    (hlayout.measuredStepPlain_sourceScratch_mem_aux (by rw [← hlayout.measuredStepPlain_scratch_view]; simp))
    (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.measuredStepPlain_terminal_not_lengthS
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ registers.lengthS := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.terminal) (payloadWire := registers.terminal)
    (hlayout.measuredStepPlain_sourceScratch_mem_aux (by rw [← hlayout.measuredStepPlain_scratch_view]; simp))
    (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl

private theorem IndexedStepLayout.measuredStepPlain_terminal_not_condition
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.terminal ∉ measuredStepPlain_terminalConditionWires registers := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.terminal) (payloadWire := registers.terminal)
    (hlayout.measuredStepPlain_sourceScratch_mem_aux (by rw [← hlayout.measuredStepPlain_scratch_view]; simp))
    (hlayout.measuredStepPlain_terminalCondition_payload hmem)) rfl

private theorem IndexedStepLayout.measuredStepPlain_shiftEpoch_not_condition
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.shiftEpoch ∉ measuredStepPlain_terminalConditionWires registers := by
  intro hmem
  exact (hlayout.measuredStepPlain_aux_not_payload
    (auxWire := registers.shiftEpoch) (payloadWire := registers.shiftEpoch)
    hlayout.measuredStepPlain_shiftEpoch_mem_aux (hlayout.measuredStepPlain_terminalCondition_payload hmem)) rfl

private theorem IndexedStepLayout.measuredStepPlain_quotientLow_not_condition
    {registers : IndexedStepRegisters} {n T : Nat}
    (hlayout : IndexedStepLayout registers n T) :
    registers.quotientLow ∉ measuredStepPlain_terminalConditionWires registers := by
  simp only [measuredStepPlain_terminalConditionWires, List.mem_cons, not_or]
  constructor
  · exact fun equality ↦ (hlayout.measuredStepPlain_phase1_ne_after (by
      simp [measuredStepPlain_indexedStepAfterPhase1, hlayout.measuredStepPlain_quotientLow_mem_lengthQ])) equality.symm
  · intro hmem
    exact (hlayout.measuredStepPlain_lengthRPrime_ne_outside hmem (Or.inl (by
      simp [measuredStepPlain_indexedStepBeforeLengthRPrime, hlayout.measuredStepPlain_quotientLow_mem_lengthQ]))) rfl

private def measuredStepPlain_blockAForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let marked := measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) registers.terminal state
  let padded := terminalPaddingForwardState registers.terminalPadding marked
  let disabled := measuredStepPlain_xorWireState registers.terminal registers.phase1 padded
  let shifted := preShiftState registers.preShift disabled
  let restoredPhase := measuredStepPlain_xorWireState registers.terminal registers.phase1 shifted
  let spilled := measuredStepPlain_terminalEpochSpillState registers.terminal registers.shiftEpoch
    registers.quotientLow restoredPhase
  measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) registers.terminal spilled

private def measuredStepPlain_remainderRestoreControlState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let marked := measuredStepPlain_andXorWireState registers.phase2 registers.sign registers.terminal state
  let enabled := measuredStepPlain_rControlState [registers.phase1, registers.terminal] 0
    registers.control registers.lengthRPrime (registers.blockScratch.getD 0 0) marked
  measuredStepPlain_andXorWireState registers.phase2 registers.sign registers.terminal enabled

private theorem measuredStepPlain_remainderRestoreControlState_preserves
    (registers : IndexedStepRegisters) (state : BasisState) {wire : Wire}
    (hterminal : wire ≠ registers.terminal)
    (hcontrol : wire ≠ registers.control) :
    measuredStepPlain_remainderRestoreControlState registers state wire = state wire := by
  simp [measuredStepPlain_remainderRestoreControlState, measuredStepPlain_andXorWireState, measuredStepPlain_rControlState, upd,
    hterminal, hcontrol]

private def measuredStepPlain_blockB1ForwardState
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  let enabled := measuredStepPlain_rControlState [registers.phase1] 0 registers.control
    registers.lengthRPrime registers.terminal state
  let changed := intervalAddSubState (registers.remainder window) n
    window.start window.stop .sub true .work1 enabled
  measuredStepPlain_rControlState [registers.phase1] 0 registers.control registers.lengthRPrime
    registers.terminal changed

private def measuredStepPlain_blockB2State
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let enabled := measuredStepPlain_rControlState [registers.phase1, registers.phase2] 2
    registers.control registers.lengthRPrime registers.terminal state
  let changed := measuredStepPlain_xorWireState registers.control registers.sign enabled
  measuredStepPlain_rControlState [registers.phase1, registers.phase2] 2 registers.control
    registers.lengthRPrime registers.terminal changed

private def measuredStepPlain_blockB3ForwardState
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  let enabled := measuredStepPlain_remainderRestoreControlState registers state
  let changed := intervalAddSubState (registers.remainder window) n
    window.start window.stop .add false .work1 enabled
  measuredStepPlain_remainderRestoreControlState registers changed

private def measuredStepPlain_blockBForwardState
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  measuredStepPlain_blockB3ForwardState registers n window
    (measuredStepPlain_blockB2State registers (measuredStepPlain_blockB1ForwardState registers n window state))

private def measuredStepPlain_blockCForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let marked := measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) registers.terminal state
  let restored := measuredStepPlain_terminalEpochRestoreState registers.terminal registers.shiftEpoch
    registers.quotientLow marked
  measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) registers.terminal restored

private def measuredStepPlain_quotientPreparedBits
    (registers : QuotientSwapRegisters) (state : BasisState) : List Bool :=
  cuccaroAddBits false
    (constantBits registers.constantScratch.length 3)
    (cuccaroAddBits false (wireValues registers.lengthT state)
      (wireValues registers.lengthQ state))

private def measuredStepPlain_quotientPreparedState
    (registers : QuotientSwapRegisters) (state : BasisState) : BasisState :=
  measuredStepPlain_indexedWriteWireValues registers.lengthQ
    (measuredStepPlain_quotientPreparedBits registers state) state

private def measuredStepPlain_indexedQuotientSwapState
    (registers : QuotientSwapRegisters) (k K : Nat)
    (state : BasisState) : BasisState :=
  quotientSwapState registers k
    ((quotientSwapTree registers k K).routeLabel
      (measuredStepPlain_quotientPreparedState registers state))
    (state registers.control) state

private def measuredStepPlain_blockD1ForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let enabled := measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 2
    registers.control state
  let changed := measuredStepPlain_indexedIncrementWordState (enabled registers.control)
    registers.lengthQ enabled
  measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 2 registers.control changed

private def measuredStepPlain_blockD2ForwardState
    (registers : IndexedStepRegisters) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  let enabled1 := measuredStepPlain_xorWireState registers.phase1 registers.control state
  let enabled2 := measuredStepPlain_xorWireState registers.phase2 registers.control enabled1
  let changed := measuredStepPlain_indexedQuotientSwapState (registers.quotient window)
    window.start window.stop enabled2
  let disabled2 := measuredStepPlain_xorWireState registers.phase2 registers.control changed
  measuredStepPlain_xorWireState registers.phase1 registers.control disabled2

private def measuredStepPlain_blockD3ForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  let enabled := measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 1
    registers.control state
  let changed := measuredStepPlain_indexedDecrementWordState (enabled registers.control)
    registers.lengthQ enabled
  measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 1 registers.control changed

private def measuredStepPlain_blockDForwardState
    (registers : IndexedStepRegisters) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  measuredStepPlain_blockD3ForwardState registers
    (measuredStepPlain_blockD2ForwardState registers window (measuredStepPlain_blockD1ForwardState registers state))

private def measuredStepPlain_tBoundaryPrepareState
    (registers : IndexedStepRegisters) (n : Nat)
    (state : BasisState) : BasisState :=
  let words := prepareLatestPaperTBoundaryWords (state registers.phase2)
    (wireValues registers.lengthT state)
    (wireValues registers.lengthRPrime state)
    (wireValues registers.tBoundary.lengthSLow state) n
  measuredStepPlain_indexedWriteWireValues (registers.lengthT ++ registers.lengthRPrime)
    (words.1 ++ words.2) state

private def measuredStepPlain_tBoundaryRestoreState
    (registers : IndexedStepRegisters) (n : Nat)
    (state : BasisState) : BasisState :=
  let words := restoreLatestPaperTBoundaryWords (state registers.phase2)
    (wireValues registers.lengthT state)
    (wireValues registers.lengthRPrime state)
    (wireValues registers.tBoundary.lengthSLow state) n
  measuredStepPlain_indexedWriteWireValues (registers.lengthT ++ registers.lengthRPrime)
    (words.1 ++ words.2) state

private def measuredStepPlain_blockEForwardState
    (registers : IndexedStepRegisters) (n : Nat) (window : ActiveWindow)
    (state : BasisState) : BasisState :=
  let temporary1 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  let subEnabled := measuredStepPlain_matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary1
  let temporaryCleared1 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subEnabled
  let prepared := measuredStepPlain_tBoundaryPrepareState registers n temporaryCleared1
  let subtracted := coefficientPrefixState (registers.coefficient window)
    window.start window.stop .sub false .work2 prepared
  let temporary2 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subtracted
  let subCleared := measuredStepPlain_matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary2
  let temporaryCleared2 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subCleared
  let signChanged := measuredStepPlain_xorWireState registers.phase1 registers.sign temporaryCleared2
  let addEnabled := measuredStepPlain_matchXorState [registers.phase1] 1 registers.control signChanged
  let added := coefficientPrefixState (registers.coefficient window)
    window.start window.stop .add true .work2 addEnabled
  let addCleared := measuredStepPlain_matchXorState [registers.phase1] 1 registers.control added
  measuredStepPlain_tBoundaryRestoreState registers n addCleared

private theorem measuredStepPlain_tBoundaryPrepareState_preservesOutside
    (registers : IndexedStepRegisters) (n : Nat) (state : BasisState)
    {wire : Wire} (ht : wire ∉ registers.lengthT)
    (hrp : wire ∉ registers.lengthRPrime) :
    measuredStepPlain_tBoundaryPrepareState registers n state wire = state wire := by
  unfold measuredStepPlain_tBoundaryPrepareState
  exact measuredStepPlain_indexedWriteWireValues_preservesOutside _ _ _ (by
    simp [ht, hrp])

private theorem measuredStepPlain_tBoundaryRestoreState_preservesOutside
    (registers : IndexedStepRegisters) (n : Nat) (state : BasisState)
    {wire : Wire} (ht : wire ∉ registers.lengthT)
    (hrp : wire ∉ registers.lengthRPrime) :
    measuredStepPlain_tBoundaryRestoreState registers n state wire = state wire := by
  unfold measuredStepPlain_tBoundaryRestoreState
  exact measuredStepPlain_indexedWriteWireValues_preservesOutside _ _ _ (by
    simp [ht, hrp])

private def measuredStepPlain_blockFForwardState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  postShiftState registers.postShift state

private theorem measuredStepPlain_xorWireState_preserves
    (control target : Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ≠ target) :
    measuredStepPlain_xorWireState control target state wire = state wire := by
  simp [measuredStepPlain_xorWireState, upd, hwire]

private theorem measuredStepPlain_terminalPaddingForwardState_terminal
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T) :
    terminalPaddingForwardState registers.terminalPadding state
        registers.terminal =
      state registers.terminal := by
  have hterminalWork : registers.terminal ∉ registers.work2 := by
    intro hmem
    exact (hlayout.measuredStepPlain_aux_not_payload
      (auxWire := registers.terminal) (payloadWire := registers.terminal)
      (hlayout.measuredStepPlain_sourceScratch_mem_aux (by
        rw [← hlayout.measuredStepPlain_scratch_view]
        simp))
      (by simp [measuredStepPlain_indexedStepPayload, hmem]) rfl).elim
  have hterminalLength : registers.terminal ∉ registers.lengthS := by
    intro hmem
    exact (hlayout.measuredStepPlain_aux_not_payload
      (auxWire := registers.terminal) (payloadWire := registers.terminal)
      (hlayout.measuredStepPlain_sourceScratch_mem_aux (by
        rw [← hlayout.measuredStepPlain_scratch_view]
        simp))
      (by simp [measuredStepPlain_indexedStepPayload, hmem]) rfl).elim
  have hterminalEpoch : registers.terminal ≠ registers.shiftEpoch := by
    have hphysical := hlayout.terminalEpoch
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hphysical
    exact hphysical.1.1
  change terminalPaddingForwardState registers.terminalPadding state
      registers.terminalPadding.terminal =
    state registers.terminalPadding.terminal
  change registers.terminalPadding.terminal ∉
    registers.terminalPadding.work2 at hterminalWork
  change registers.terminalPadding.terminal ∉
    registers.terminalPadding.lengthS at hterminalLength
  change registers.terminalPadding.terminal ≠
    registers.terminalPadding.shiftEpoch at hterminalEpoch
  simp only [terminalPaddingForwardState]
  rw [upd_other _ _ _ hterminalEpoch,
    measuredStepPlain_writeReg_apply_outside _ _ _ hterminalLength,
    measuredStepPlain_writeReg_apply_outside _ _ _ hterminalWork]

private theorem measuredStepPlain_blockAForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (blockAForward registers) state = measuredStepPlain_blockAForwardState registers state ∧
      Clean registers.blockScratch (run (blockAForward registers) state) := by
  let marked := measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) registers.terminal state
  have hblock : Clean registers.blockScratch state := by
    apply measuredStepPlain_clean_mono hready
    intro wire hwire
    exact hlayout.measuredStepPlain_blockScratch_mem_sharedScratch hwire
  have hmarkedRun : run (measuredStepPlain_toggleTerminal registers) state = marked := by
    simpa [measuredStepPlain_toggleTerminal, marked, measuredStepPlain_matchXorState] using
      run_computeControl (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) registers.terminal
        registers.blockScratch state hlayout.terminalControl hblock
  have hterminalNotBlock : registers.terminal ∉ registers.blockScratch :=
    hlayout.measuredStepPlain_terminal_not_blockScratch
  have hmarkedBlock : Clean registers.blockScratch marked := by
    simpa [marked, measuredStepPlain_matchXorState] using
      measuredStepPlain_clean_upd_not_mem hblock hterminalNotBlock
  let padded := terminalPaddingForwardState registers.terminalPadding marked
  have hterminalPaddingReady :
      Clean registers.terminalPadding.scratch marked :=
    measuredStepPlain_clean_mono hmarkedBlock hlayout.measuredStepPlain_terminalPadding_scratch_sub_block
  have hpaddedRun :
      run (terminalPaddingForward registers.terminalPadding) marked = padded := by
    simpa only [padded] using run_terminalPaddingForward registers.terminalPadding
      marked hlayout.terminalPadding hterminalPaddingReady
  have hpaddedLocal : Clean registers.terminalPadding.scratch padded := by
    rw [← hpaddedRun]
    exact terminalPaddingForward_clean registers.terminalPadding marked
      hlayout.terminalPadding hterminalPaddingReady
  have hpaddedBlock : Clean registers.blockScratch padded := by
    rw [← hpaddedRun]
    exact measuredStepPlain_clean_after_local_circuit hmarkedBlock
      (by simpa only [hpaddedRun] using hpaddedLocal)
      (terminalPaddingForward_usesOnly registers.terminalPadding)
      hlayout.measuredStepPlain_terminalPadding_support_intersection
  let disabled := measuredStepPlain_xorWireState registers.terminal registers.phase1 padded
  have hdisabledBlock : Clean registers.blockScratch disabled := by
    simpa [disabled, measuredStepPlain_xorWireState] using
      measuredStepPlain_clean_upd_not_mem hpaddedBlock hlayout.measuredStepPlain_phase1_not_blockScratch
  have hpreReady : ShiftReady registers.preShift disabled :=
    measuredStepPlain_clean_mono hdisabledBlock hlayout.measuredStepPlain_preShift_scratch_sub_block
  let shifted := preShiftState registers.preShift disabled
  have hshiftedRun : run (preShiftUnitary registers.preShift) disabled = shifted := by
    simpa only [shifted] using
      run_preShiftUnitary registers.preShift disabled hlayout.preShift hpreReady
  have hshiftedLocal : ShiftReady registers.preShift shifted := by
    rw [← hshiftedRun]
    exact preShiftUnitary_ready registers.preShift disabled hlayout.preShift hpreReady
  have hshiftedBlock : Clean registers.blockScratch shifted := by
    rw [← hshiftedRun]
    exact measuredStepPlain_clean_after_local_circuit hdisabledBlock
      (by simpa only [hshiftedRun] using hshiftedLocal)
      (preShiftUnitary_usesOnly registers.preShift)
      hlayout.measuredStepPlain_preShift_support_intersection
  let restoredPhase := measuredStepPlain_xorWireState registers.terminal registers.phase1 shifted
  have hrestoredBlock : Clean registers.blockScratch restoredPhase := by
    simpa [restoredPhase, measuredStepPlain_xorWireState] using
      measuredStepPlain_clean_upd_not_mem hshiftedBlock hlayout.measuredStepPlain_phase1_not_blockScratch
  let spilled := measuredStepPlain_terminalEpochSpillState registers.terminal registers.shiftEpoch
    registers.quotientLow restoredPhase
  have hspilledRun : run
      (terminalEpochSpill registers.terminal registers.shiftEpoch registers.quotientLow)
      restoredPhase = spilled := by
    simpa only [spilled] using measuredStepPlain_run_terminalEpochSpillState registers.terminal
      registers.shiftEpoch registers.quotientLow restoredPhase hlayout.terminalEpoch
  have hspilledBlock : Clean registers.blockScratch spilled := by
    rw [← hspilledRun]
    intro wire hwire
    rw [(terminalEpochSpill_usesOnly registers.terminal registers.shiftEpoch
      registers.quotientLow).preservesOutside restoredPhase
        (hlayout.measuredStepPlain_blockScratch_outside_terminalEpoch wire hwire)]
    exact hrestoredBlock wire hwire
  have hunmarkedRun : run (measuredStepPlain_toggleTerminal registers) spilled =
      measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) registers.terminal spilled := by
    simpa [measuredStepPlain_toggleTerminal, measuredStepPlain_matchXorState] using
      run_computeControl (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) registers.terminal
        registers.blockScratch spilled hlayout.terminalControl hspilledBlock
  have hunmarkedBlock : Clean registers.blockScratch
      (measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) registers.terminal spilled) := by
    simpa [measuredStepPlain_matchXorState] using
      measuredStepPlain_clean_upd_not_mem hspilledBlock hlayout.measuredStepPlain_terminal_not_blockScratch
  have hrun :
      run (blockAForward registers) state = measuredStepPlain_blockAForwardState registers state := by
    simp only [measuredStepPlain_view_blockAForward, measuredStepPlain_source_blockAForward, Classical.run_append]
    rw [hmarkedRun, hpaddedRun,
      measuredStepPlain_run_xorWireState registers.terminal registers.phase1 padded,
      hshiftedRun,
      measuredStepPlain_run_xorWireState registers.terminal registers.phase1 shifted,
      hspilledRun, hunmarkedRun]
    rfl
  exact ⟨hrun, by rw [hrun]; exact hunmarkedBlock⟩

private theorem measuredStepPlain_blockAForward_borrowedReady
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state) :
    measuredStepPlain_IndexedStepBorrowedReady registers
      (run (blockAForward registers) state) := by
  let terminalMatch := registerMatches (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) state
  let marked := measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) registers.terminal state
  let padded := terminalPaddingForwardState registers.terminalPadding marked
  let disabled := measuredStepPlain_xorWireState registers.terminal registers.phase1 padded
  let shifted := preShiftState registers.preShift disabled
  let restoredPhase := measuredStepPlain_xorWireState registers.terminal registers.phase1 shifted
  let spilled := measuredStepPlain_terminalEpochSpillState registers.terminal registers.shiftEpoch
    registers.quotientLow restoredPhase
  have hcorrect := measuredStepPlain_blockAForward_correct registers n T state hlayout hready
  have hcontrolFalse : state registers.control = false := by
    exact hready registers.control (by
      simp [IndexedStepRegisters.sharedScratch])
  have hterminalFalse : state registers.terminal = false := by
    exact hready registers.terminal (by
      simp only [IndexedStepRegisters.sharedScratch, List.mem_cons]
      right
      rw [← hlayout.measuredStepPlain_scratch_view]
      simp)
  have hblock : Clean registers.blockScratch state := by
    apply measuredStepPlain_clean_mono hready
    intro wire hwire
    exact hlayout.measuredStepPlain_blockScratch_mem_sharedScratch hwire
  have hterminalEpoch := hlayout.terminalEpoch
  simp only [List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hterminalEpoch
  have hterminalShift : registers.terminal ≠ registers.shiftEpoch :=
    hterminalEpoch.1.1
  have hterminalQuotient : registers.terminal ≠ registers.quotientLow :=
    hterminalEpoch.1.2
  have hshiftQuotient : registers.shiftEpoch ≠ registers.quotientLow :=
    hterminalEpoch.2.1
  have hterminalPhase := hlayout.terminalPhase
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hterminalPhase
  have hphaseTerminal : registers.phase1 ≠ registers.terminal :=
    Ne.symm hterminalPhase.1
  have hmarkedTerminal : marked registers.terminal = terminalMatch := by
    simp [marked, terminalMatch, measuredStepPlain_matchXorState, hterminalFalse]
  have hmarkedControl : marked registers.control = state registers.control := by
    simp [marked, measuredStepPlain_matchXorState, upd, hlayout.measuredStepPlain_control_ne_terminal]
  have hmarkedQuotient : marked registers.quotientLow =
      state registers.quotientLow := by
    simp [marked, measuredStepPlain_matchXorState, upd, Ne.symm hterminalQuotient]
  have hmarkedEpoch : marked registers.shiftEpoch = state registers.shiftEpoch := by
    simp [marked, measuredStepPlain_matchXorState, upd, Ne.symm hterminalShift]
  have hmarkedCondition :
      registerMatches (measuredStepPlain_terminalConditionWires registers)
          (measuredStepPlain_terminalConditionValue registers) marked = terminalMatch := by
    change registerMatches (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) marked =
      registerMatches (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) state
    apply measuredStepPlain_registerMatches_congr
    intro wire hwire
    have hne : wire ≠ registers.terminal := by
      intro equality
      apply hlayout.measuredStepPlain_terminal_not_condition
      simpa [equality] using hwire
    simp [marked, measuredStepPlain_matchXorState, upd, hne]
  have hmarkedBlock : Clean registers.blockScratch marked := by
    simpa [marked, measuredStepPlain_matchXorState] using
      measuredStepPlain_clean_upd_not_mem hblock hlayout.measuredStepPlain_terminal_not_blockScratch
  have hpaddingReady : Clean registers.terminalPadding.scratch marked :=
    measuredStepPlain_clean_mono hmarkedBlock hlayout.measuredStepPlain_terminalPadding_scratch_sub_block
  have hpaddedRun :
      run (terminalPaddingForward registers.terminalPadding) marked = padded := by
    simpa only [padded] using run_terminalPaddingForward registers.terminalPadding
      marked hlayout.terminalPadding hpaddingReady
  have hpaddedLocal : Clean registers.terminalPadding.scratch padded := by
    rw [← hpaddedRun]
    exact terminalPaddingForward_clean registers.terminalPadding marked
      hlayout.terminalPadding hpaddingReady
  have hpaddedBlock : Clean registers.blockScratch padded := by
    rw [← hpaddedRun]
    exact measuredStepPlain_clean_after_local_circuit hmarkedBlock
      (by simpa only [hpaddedRun] using hpaddedLocal)
      (terminalPaddingForward_usesOnly registers.terminalPadding)
      hlayout.measuredStepPlain_terminalPadding_support_intersection
  have hpaddedTerminal : padded registers.terminal = terminalMatch := by
    calc
      padded registers.terminal = marked registers.terminal :=
        measuredStepPlain_terminalPaddingForwardState_terminal registers n T marked hlayout
      _ = terminalMatch := hmarkedTerminal
  have hpaddedControl : padded registers.control = state registers.control := by
    calc
      padded registers.control = marked registers.control :=
        terminalPaddingForwardState_preserves registers.terminalPadding marked
          hlayout.measuredStepPlain_control_not_work2 hlayout.measuredStepPlain_control_not_lengthS
          hlayout.measuredStepPlain_control_ne_shiftEpoch
      _ = state registers.control := hmarkedControl
  have hpaddedQuotient : padded registers.quotientLow =
      state registers.quotientLow := by
    calc
      padded registers.quotientLow = marked registers.quotientLow :=
        terminalPaddingForwardState_preserves registers.terminalPadding marked
          hlayout.measuredStepPlain_quotientLow_not_work2 hlayout.measuredStepPlain_quotientLow_not_lengthS
          hlayout.measuredStepPlain_quotientLow_ne_shiftEpoch
      _ = state registers.quotientLow := hmarkedQuotient
  have hpaddedPhase : padded registers.phase1 = state registers.phase1 := by
    calc
      padded registers.phase1 = marked registers.phase1 :=
        terminalPaddingForwardState_preserves registers.terminalPadding marked
          hlayout.measuredStepPlain_phase1_not_work2 hlayout.measuredStepPlain_phase1_not_lengthS
          hlayout.measuredStepPlain_phase1_ne_shiftEpoch
      _ = state registers.phase1 := by
        simp [marked, measuredStepPlain_matchXorState, upd, hphaseTerminal]
  have hpaddedCondition :
      registerMatches (measuredStepPlain_terminalConditionWires registers)
          (measuredStepPlain_terminalConditionValue registers) padded = terminalMatch := by
    calc
      registerMatches (measuredStepPlain_terminalConditionWires registers)
          (measuredStepPlain_terminalConditionValue registers) padded =
          registerMatches (measuredStepPlain_terminalConditionWires registers)
            (measuredStepPlain_terminalConditionValue registers) marked := by
        apply measuredStepPlain_registerMatches_congr
        intro wire hwire
        simp only [measuredStepPlain_terminalConditionWires, List.mem_cons] at hwire
        rcases hwire with rfl | hlength
        · exact terminalPaddingForwardState_preserves registers.terminalPadding marked
            hlayout.measuredStepPlain_phase1_not_work2 hlayout.measuredStepPlain_phase1_not_lengthS
            hlayout.measuredStepPlain_phase1_ne_shiftEpoch
        · exact terminalPaddingForwardState_preserves registers.terminalPadding marked
            (hlayout.measuredStepPlain_lengthRPrime_not_work2 hlength)
            (hlayout.measuredStepPlain_lengthRPrime_not_lengthS hlength)
            (hlayout.measuredStepPlain_lengthRPrime_ne_shiftEpoch hlength)
      _ = terminalMatch := hmarkedCondition
  have hdisabledBlock : Clean registers.blockScratch disabled := by
    simpa [disabled, measuredStepPlain_xorWireState] using
      measuredStepPlain_clean_upd_not_mem hpaddedBlock hlayout.measuredStepPlain_phase1_not_blockScratch
  have hpreReady : ShiftReady registers.preShift disabled :=
    measuredStepPlain_clean_mono hdisabledBlock hlayout.measuredStepPlain_preShift_scratch_sub_block
  have hpreRun : run (preShiftUnitary registers.preShift) disabled = shifted := by
    simpa only [shifted] using
      run_preShiftUnitary registers.preShift disabled hlayout.preShift hpreReady
  have hdisabledTerminal : disabled registers.terminal = terminalMatch := by
    simp [disabled, measuredStepPlain_xorWireState, upd, Ne.symm hphaseTerminal, hpaddedTerminal]
  have hdisabledControl : disabled registers.control = state registers.control := by
    simp [disabled, measuredStepPlain_xorWireState, upd, hlayout.measuredStepPlain_control_ne_phase1,
      hpaddedControl]
  have hdisabledQuotient : disabled registers.quotientLow =
      state registers.quotientLow := by
    have hne : registers.quotientLow ≠ registers.phase1 := by
      exact fun equality ↦ (hlayout.measuredStepPlain_phase1_ne_after (by
        simp [measuredStepPlain_indexedStepAfterPhase1, hlayout.measuredStepPlain_quotientLow_mem_lengthQ])) equality.symm
    simp [disabled, measuredStepPlain_xorWireState, upd, hne, hpaddedQuotient]
  have hshiftedTerminal : shifted registers.terminal = terminalMatch := by
    rw [← hpreRun,
      preShiftUnitary_preservesOutside registers.preShift disabled
        hlayout.measuredStepPlain_terminal_not_preShift]
    exact hdisabledTerminal
  have hshiftedControl : shifted registers.control = state registers.control := by
    rw [← hpreRun,
      preShiftUnitary_preservesOutside registers.preShift disabled
        hlayout.measuredStepPlain_control_not_preShift]
    exact hdisabledControl
  have hshiftedQuotient : shifted registers.quotientLow =
      state registers.quotientLow := by
    rw [← hpreRun,
      preShiftUnitary_preservesOutside registers.preShift disabled
        hlayout.measuredStepPlain_quotientLow_not_preShift]
    exact hdisabledQuotient
  have hshiftedPhase : shifted registers.phase1 = disabled registers.phase1 := by
    rw [← hpreRun]
    exact preShiftUnitary_preserves_phase1 registers.preShift disabled
      hlayout.preShift hpreReady
  have hrestoredTerminal : restoredPhase registers.terminal = terminalMatch := by
    simp [restoredPhase, measuredStepPlain_xorWireState, upd, Ne.symm hphaseTerminal,
      hshiftedTerminal]
  have hrestoredControl : restoredPhase registers.control = state registers.control := by
    simp [restoredPhase, measuredStepPlain_xorWireState, upd, hlayout.measuredStepPlain_control_ne_phase1,
      hshiftedControl]
  have hrestoredQuotient : restoredPhase registers.quotientLow =
      state registers.quotientLow := by
    have hne : registers.quotientLow ≠ registers.phase1 := by
      exact fun equality ↦ (hlayout.measuredStepPlain_phase1_ne_after (by
        simp [measuredStepPlain_indexedStepAfterPhase1, hlayout.measuredStepPlain_quotientLow_mem_lengthQ])) equality.symm
    simp [restoredPhase, measuredStepPlain_xorWireState, upd, hne, hshiftedQuotient]
  have hrestoredControls : ∀ wire ∈ measuredStepPlain_terminalConditionWires registers,
      restoredPhase wire = state wire := by
    intro wire hwire
    simp only [measuredStepPlain_terminalConditionWires, List.mem_cons] at hwire
    rcases hwire with rfl | hlength
    · simp [restoredPhase, measuredStepPlain_xorWireState, disabled, hshiftedPhase,
        hshiftedTerminal, hpaddedTerminal, hpaddedPhase]
    · have houtside := preShiftUnitary_preservesOutside registers.preShift disabled
        (hlayout.measuredStepPlain_lengthRPrime_not_preShift hlength)
      rw [hpreRun] at houtside
      have hphaseNe : wire ≠ registers.phase1 := by
        exact fun equality ↦
          (hlayout.measuredStepPlain_lengthRPrime_ne_outside hlength (Or.inl (by
            simp [measuredStepPlain_indexedStepBeforeLengthRPrime]))) equality
      have hterminalNe : wire ≠ registers.terminal := by
        exact hlayout.measuredStepPlain_lengthRPrime_ne_outside hlength (Or.inr
          (hlayout.measuredStepPlain_sourceScratch_mem_aux (by rw [← hlayout.measuredStepPlain_scratch_view]; simp)))
      calc
        restoredPhase wire = shifted wire := by
          simp [restoredPhase, measuredStepPlain_xorWireState, upd, hphaseNe]
        _ = disabled wire := houtside
        _ = padded wire := by simp [disabled, measuredStepPlain_xorWireState, upd, hphaseNe]
        _ = marked wire := terminalPaddingForwardState_preserves
          registers.terminalPadding marked
          (hlayout.measuredStepPlain_lengthRPrime_not_work2 hlength)
          (hlayout.measuredStepPlain_lengthRPrime_not_lengthS hlength)
          (hlayout.measuredStepPlain_lengthRPrime_ne_shiftEpoch hlength)
        _ = state wire := by simp [marked, measuredStepPlain_matchXorState, upd, hterminalNe]
  have hrestoredCondition :
      registerMatches (measuredStepPlain_terminalConditionWires registers)
          (measuredStepPlain_terminalConditionValue registers) restoredPhase = terminalMatch := by
    change registerMatches (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) restoredPhase =
      registerMatches (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) state
    exact measuredStepPlain_registerMatches_congr _ _ _ _ hrestoredControls
  have hspilledTerminal : spilled registers.terminal = terminalMatch := by
    calc
      spilled registers.terminal = restoredPhase registers.terminal :=
        measuredStepPlain_terminalEpochSpillState_preserves _ _ _ _ hterminalShift
          hterminalQuotient hterminalQuotient
      _ = terminalMatch := hrestoredTerminal
  have hspilledControl : spilled registers.control = state registers.control := by
    calc
      spilled registers.control = restoredPhase registers.control :=
        measuredStepPlain_terminalEpochSpillState_preserves _ _ _ _
          hlayout.measuredStepPlain_control_ne_shiftEpoch hlayout.measuredStepPlain_control_ne_quotientLow
          hterminalQuotient
      _ = state registers.control := hrestoredControl
  have hspilledControls : ∀ wire ∈ measuredStepPlain_terminalConditionWires registers,
      spilled wire = state wire := by
    intro wire hwire
    have hterminalNe : wire ≠ registers.terminal := by
      intro equality
      exact hlayout.measuredStepPlain_terminal_not_condition (by simpa [equality] using hwire)
    have hepochNe : wire ≠ registers.shiftEpoch := by
      intro equality
      exact hlayout.measuredStepPlain_shiftEpoch_not_condition (by simpa [equality] using hwire)
    have hquotientNe : wire ≠ registers.quotientLow := by
      intro equality
      exact hlayout.measuredStepPlain_quotientLow_not_condition (by simpa [equality] using hwire)
    calc
      spilled wire = restoredPhase wire :=
        measuredStepPlain_terminalEpochSpillState_preserves _ _ _ _ hepochNe hquotientNe
          hterminalQuotient
      _ = state wire := hrestoredControls wire hwire
  have hspilledCondition :
      registerMatches (measuredStepPlain_terminalConditionWires registers)
          (measuredStepPlain_terminalConditionValue registers) spilled = terminalMatch := by
    change registerMatches (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) spilled =
      registerMatches (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) state
    exact measuredStepPlain_registerMatches_congr _ _ _ _ hspilledControls
  have hspilledEpoch : spilled registers.shiftEpoch = false := by
    by_cases hmatch : terminalMatch = true
    · have hquotient : state registers.quotientLow = true := by
        simpa [measuredStepPlain_view_IndexedStepEpochEncoded, measuredStepPlain_source_IndexedStepEpochEncoded, terminalMatch, hmatch] using hencoded
      simp [spilled, measuredStepPlain_terminalEpochSpillState, measuredStepPlain_controlledSwapState, measuredStepPlain_xorWireState,
        measuredStepPlain_swapWireState, upd, hterminalQuotient,
        hshiftQuotient, hrestoredTerminal, hrestoredQuotient,
        hmatch, hquotient]
    · have hmatchFalse : terminalMatch = false := by
        cases hvalue : terminalMatch <;> simp_all
      have hepoch : state registers.shiftEpoch = false := by
        simpa [measuredStepPlain_view_IndexedStepEpochEncoded, measuredStepPlain_source_IndexedStepEpochEncoded, terminalMatch, hmatchFalse] using hencoded
      have hpaddedEpoch : padded registers.shiftEpoch = state registers.shiftEpoch := by
        calc
          padded registers.shiftEpoch = marked registers.shiftEpoch :=
            measuredStepPlain_terminalPaddingForwardState_shiftEpoch_of_terminal_false
              registers.terminalPadding marked (by
                simpa [hmatchFalse] using hmarkedTerminal)
              hlayout.measuredStepPlain_shiftEpoch_not_work2 hlayout.measuredStepPlain_shiftEpoch_not_lengthS
              hlayout.measuredStepPlain_terminal_not_work2 hlayout.measuredStepPlain_terminal_not_lengthS
          _ = state registers.shiftEpoch := hmarkedEpoch
      have hdisabledEpoch : disabled registers.shiftEpoch = state registers.shiftEpoch := by
        simp [disabled, measuredStepPlain_xorWireState, upd, hlayout.measuredStepPlain_phase1_ne_shiftEpoch.symm,
          hpaddedEpoch]
      have hshiftedEpoch : shifted registers.shiftEpoch = state registers.shiftEpoch := by
        rw [← hpreRun,
          preShiftUnitary_preservesOutside registers.preShift disabled
            hlayout.measuredStepPlain_shiftEpoch_not_preShift]
        exact hdisabledEpoch
      have hrestoredEpoch : restoredPhase registers.shiftEpoch =
          state registers.shiftEpoch := by
        simp [restoredPhase, measuredStepPlain_xorWireState, upd,
          hlayout.measuredStepPlain_phase1_ne_shiftEpoch.symm, hshiftedEpoch]
      simp [spilled, measuredStepPlain_terminalEpochSpillState, measuredStepPlain_controlledSwapState, measuredStepPlain_xorWireState,
        upd, hterminalQuotient,
        hshiftQuotient, hrestoredTerminal, hrestoredEpoch, hmatchFalse, hepoch]
  have hfinalTerminal : measuredStepPlain_blockAForwardState registers state registers.terminal = false := by
    change measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
      (measuredStepPlain_terminalConditionValue registers) registers.terminal spilled
        registers.terminal = false
    simp [measuredStepPlain_matchXorState, hspilledTerminal, hspilledCondition]
  have hfinalEpoch : measuredStepPlain_blockAForwardState registers state registers.shiftEpoch = false := by
    change measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
      (measuredStepPlain_terminalConditionValue registers) registers.terminal spilled
        registers.shiftEpoch = false
    simp [measuredStepPlain_matchXorState, upd, Ne.symm hterminalShift, hspilledEpoch]
  have hfinalControl : measuredStepPlain_blockAForwardState registers state registers.control = false := by
    change measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
      (measuredStepPlain_terminalConditionValue registers) registers.terminal spilled
        registers.control = false
    simp [measuredStepPlain_matchXorState, upd, hlayout.measuredStepPlain_control_ne_terminal,
      hspilledControl, hcontrolFalse]
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      measuredStepPlain_blockAForwardState registers state wire = false := by
    intro wire hrepair
    have hnotPayload := hlayout.measuredStepPlain_remainderRepairScratch_not_payload hrepair
    have hnotSource := hlayout.measuredStepPlain_remainderRepairScratch_not_sourceScratch hrepair
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      apply hnotSource
      rw [equality, ← hlayout.measuredStepPlain_scratch_view]
      simp
    have hphase1 : wire ≠ registers.phase1 := by
      intro equality
      apply hnotPayload
      simp [measuredStepPlain_indexedStepPayload, equality]
    have hshift : wire ≠ registers.shiftEpoch :=
      hlayout.measuredStepPlain_remainderRepairScratch_ne_shiftEpoch hrepair
    have hquotient : wire ≠ registers.quotientLow := by
      intro equality
      apply hnotPayload
      simp [measuredStepPlain_indexedStepPayload, equality, hlayout.measuredStepPlain_quotientLow_mem_lengthQ]
    have hwork2 : wire ∉ registers.work2 := by
      intro hmem
      exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, hmem])
    have hlengthS : wire ∉ registers.lengthS := by
      intro hmem
      exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, hmem])
    calc
      measuredStepPlain_blockAForwardState registers state wire = spilled wire := by
        change measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
          (measuredStepPlain_terminalConditionValue registers) registers.terminal spilled wire =
            spilled wire
        exact measuredStepPlain_matchXorState_preserves _ _ _ _ hterminal
      _ = restoredPhase wire := measuredStepPlain_terminalEpochSpillState_preserves _ _ _ _
        hshift hquotient hterminalQuotient
      _ = shifted wire := measuredStepPlain_xorWireState_preserves _ _ _ hphase1
      _ = disabled wire := by
        rw [← hpreRun]
        exact preShiftUnitary_preservesOutside registers.preShift disabled
          (hlayout.measuredStepPlain_remainderRepairScratch_not_preShift hrepair)
      _ = padded wire := measuredStepPlain_xorWireState_preserves _ _ _ hphase1
      _ = marked wire := terminalPaddingForwardState_preserves
        registers.terminalPadding marked hwork2 hlengthS hshift
      _ = state wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hterminal
      _ = false := hready wire
        (hlayout.measuredStepPlain_remainderRepairScratch_mem_sharedScratch hrepair)
  intro wire hwire
  rw [← hlayout.measuredStepPlain_aux_view] at hwire
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire
  by_cases hcontrol : wire = registers.control
  · rw [hcontrol, hcorrect.1]
    exact hfinalControl
  by_cases hepoch : wire = registers.shiftEpoch
  · rw [hepoch, hcorrect.1]
    exact hfinalEpoch
  have htail :
      wire ∈ registers.sourceScratch ++ registers.remainderRepairScratch := by
    simpa [hcontrol, hepoch] using hwire
  rcases List.mem_append.mp htail with hsource | hrepair
  · rw [← hlayout.measuredStepPlain_scratch_view] at hsource
    simp only [List.mem_cons] at hsource
    by_cases hterminal : wire = registers.terminal
    · rw [hterminal, hcorrect.1]
      exact hfinalTerminal
    · have hblockWire : wire ∈ registers.blockScratch := by
        simpa [hterminal] using hsource
      exact hcorrect.2 wire hblockWire
  · rw [hcorrect.1]
    exact hrepairFinal wire hrepair

private theorem measuredStepPlain_blockB1Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : measuredStepPlain_IndexedStepBorrowedReady registers state) :
    run (blockB1Forward registers n window) state =
        measuredStepPlain_blockB1ForwardState registers n window state ∧
      measuredStepPlain_IndexedStepBorrowedReady registers
        (run (blockB1Forward registers n window) state) := by
  have hcontrolFalse : state registers.control = false :=
    hready registers.control hlayout.measuredStepPlain_control_mem_aux
  have hsourceClean : Clean (registers.terminal :: registers.blockScratch) state := by
    intro wire hwire
    apply hready wire
    apply hlayout.measuredStepPlain_sourceScratch_mem_aux
    rw [← hlayout.measuredStepPlain_scratch_view]
    exact hwire
  let predicate := rControlNonterminalPredicate [registers.phase1] 0
    registers.lengthRPrime registers.terminal state
  let enabled := measuredStepPlain_rControlState [registers.phase1] 0 registers.control
    registers.lengthRPrime registers.terminal state
  have henabledRun : run (measuredStepPlain_remainderSubControl registers) state = enabled := by
    simpa [measuredStepPlain_remainderSubControl, measuredStepPlain_toggleRControl, enabled, measuredStepPlain_rControlState] using
      (run_rControlNonterminal [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch state
        hlayout.remainderSub hsourceClean)
  have hcontrolNePhase1 : registers.control ≠ registers.phase1 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by
      simp [measuredStepPlain_indexedStepPayload])
  have henabledAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      enabled wire = false := by
    intro wire haux hcontrol
    change measuredStepPlain_rControlState [registers.phase1] 0 registers.control
      registers.lengthRPrime registers.terminal state wire = false
    rw [measuredStepPlain_rControlState_preserves _ _ _ _ _ _ hcontrol]
    exact hready wire haux
  have henabledReady : IntervalReady (registers.remainder window) enabled := by
    intro wire hwire
    exact henabledAway wire (hlayout.measuredStepPlain_remainder_scratch_sub_aux window wire hwire) (by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_control_not_remainder_scratch window hwindow hwire)
  let changed := intervalAddSubState (registers.remainder window) n
    window.start window.stop .sub true .work1 enabled
  have hchangedRun : run
      (intervalAddSubUnitary (registers.remainder window) n window.start window.stop
        .sub true .work1) enabled = changed := by
    subst window
    simpa only [changed] using
      run_intervalAddSubUnitary_state
        (registers.remainder (certifiedActiveWindows n T).remainder) n
        (certifiedActiveWindows n T).remainder.start
        (certifiedActiveWindows n T).remainder.stop .sub true .work1 enabled
        hlayout.remainder (by simpa using henabledReady)
  have hchangedAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      changed wire = false := by
    intro wire haux hcontrol
    rw [← hchangedRun]
    exact measuredStepPlain_remainderInterval_clean_auxAwayControl registers n T window .sub true enabled
      hlayout hwindow henabledAway wire haux hcontrol
  have hchangedSourceClean : Clean
      (registers.terminal :: registers.blockScratch) changed := by
    intro wire hwire
    have hsource : wire ∈ registers.sourceScratch := by
      rw [← hlayout.measuredStepPlain_scratch_view]
      exact hwire
    exact hchangedAway wire (hlayout.measuredStepPlain_sourceScratch_mem_aux hsource)
      (by intro equality; subst wire; exact hlayout.measuredStepPlain_control_not_sourceScratch hsource)
  have hchangedControl : changed registers.control = enabled registers.control := by
    rw [← hchangedRun]
    subst window
    exact intervalAddSubUnitary_preserves_control
      (registers.remainder (certifiedActiveWindows n T).remainder) n
      (certifiedActiveWindows n T).remainder.start
      (certifiedActiveWindows n T).remainder.stop .sub true .work1 enabled
      hlayout.remainder (by simpa using henabledReady)
  have hphase1 : changed registers.phase1 = state registers.phase1 := by
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .sub true .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.measuredStepPlain_phase1_not_remainder window)]
    exact measuredStepPlain_rControlState_preserves _ _ _ _ _ _ hcontrolNePhase1.symm
  have hlength : ∀ wire ∈ registers.lengthRPrime,
      changed wire = state wire := by
    intro wire hwire
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .sub true .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.measuredStepPlain_lengthRPrime_not_remainder window hwire)]
    have hcontrolNotR : registers.control ∉ registers.lengthRPrime :=
      hlayout.remainderSub.control_not_r
    exact measuredStepPlain_rControlState_preserves _ _ _ _ _ _
      (by intro equality; subst wire; exact hcontrolNotR hwire)
  have hterminalNePhase1 : registers.terminal ≠ registers.phase1 := by
    have hphysical := hlayout.terminalPhase
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hphysical
    exact hphysical.1
  have hpredicate : rControlNonterminalPredicate [registers.phase1] 0
      registers.lengthRPrime registers.terminal changed = predicate := by
    change rControlNonterminalPredicate [registers.phase1] 0
        registers.lengthRPrime registers.terminal changed =
      rControlNonterminalPredicate [registers.phase1] 0
        registers.lengthRPrime registers.terminal state
    exact measuredStepPlain_rControlNonterminalPredicate_congr [registers.phase1] 0
      registers.lengthRPrime registers.terminal changed state
      (by simpa only [List.mem_singleton] using hterminalNePhase1)
      (by
        intro wire hwire
        simp only [List.mem_singleton] at hwire
        subst wire
        exact hphase1)
      hlength
  have henabledControl : enabled registers.control = predicate := by
    simp [enabled, measuredStepPlain_rControlState, predicate, hcontrolFalse]
  have hfinalRun : run (measuredStepPlain_remainderSubControl registers) changed =
      measuredStepPlain_rControlState [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal changed := by
    simpa [measuredStepPlain_remainderSubControl, measuredStepPlain_toggleRControl, measuredStepPlain_rControlState] using
      (run_rControlNonterminal [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch changed
        hlayout.remainderSub hchangedSourceClean)
  have hfinalControl :
      measuredStepPlain_rControlState [registers.phase1] 0 registers.control
          registers.lengthRPrime registers.terminal changed registers.control = false := by
    simp [measuredStepPlain_rControlState, hchangedControl, henabledControl, hpredicate]
  have hrun : run (blockB1Forward registers n window) state =
      measuredStepPlain_blockB1ForwardState registers n window state := by
    simp only [measuredStepPlain_view_blockB1Forward, measuredStepPlain_source_blockB1Forward, Classical.run_append]
    rw [henabledRun, hchangedRun, hfinalRun]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire haux
    by_cases hcontrol : wire = registers.control
    · subst wire
      exact hfinalControl
    · change measuredStepPlain_rControlState [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal changed wire = false
      rw [measuredStepPlain_rControlState_preserves _ _ _ _ _ _ hcontrol]
      exact hchangedAway wire haux hcontrol

private theorem measuredStepPlain_blockB2_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : measuredStepPlain_IndexedStepBorrowedReady registers state) :
    run (blockB2 registers) state = measuredStepPlain_blockB2State registers state ∧
      measuredStepPlain_IndexedStepBorrowedReady registers (run (blockB2 registers) state) := by
  have hcontrolFalse : state registers.control = false :=
    hready registers.control hlayout.measuredStepPlain_control_mem_aux
  have hsourceClean : Clean (registers.terminal :: registers.blockScratch) state := by
    intro wire hwire
    apply hready wire
    apply hlayout.measuredStepPlain_sourceScratch_mem_aux
    rw [← hlayout.measuredStepPlain_scratch_view]
    exact hwire
  let predicate := rControlNonterminalPredicate
    [registers.phase1, registers.phase2] 2 registers.lengthRPrime registers.terminal state
  let enabled := measuredStepPlain_rControlState [registers.phase1, registers.phase2] 2
    registers.control registers.lengthRPrime registers.terminal state
  have henabledRun : run (measuredStepPlain_remainderPhase2Control registers) state = enabled := by
    simpa [measuredStepPlain_remainderPhase2Control, measuredStepPlain_toggleRControl, enabled, measuredStepPlain_rControlState] using
      (run_rControlNonterminal [registers.phase1, registers.phase2] 2 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch state
        hlayout.remainderPhase2 hsourceClean)
  have hcontrolNePhase1 : registers.control ≠ registers.phase1 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hcontrolNeSign : registers.control ≠ registers.sign := by
    have hphysical := hlayout.controlSign
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hphysical
    exact hphysical.1
  have henabledAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      enabled wire = false := by
    intro wire haux hcontrol
    change measuredStepPlain_rControlState [registers.phase1, registers.phase2] 2 registers.control
      registers.lengthRPrime registers.terminal state wire = false
    rw [measuredStepPlain_rControlState_preserves _ _ _ _ _ _ hcontrol]
    exact hready wire haux
  let changed := measuredStepPlain_xorWireState registers.control registers.sign enabled
  have hchangedRun : run ([.CX registers.control registers.sign] : Circuit) enabled =
      changed := by
    exact measuredStepPlain_run_xorWireState registers.control registers.sign enabled
  have hchangedAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      changed wire = false := by
    intro wire haux hcontrol
    have hsign : wire ≠ registers.sign :=
      hlayout.measuredStepPlain_aux_not_payload (auxWire := wire) (payloadWire := registers.sign)
        haux (by simp [measuredStepPlain_indexedStepPayload])
    change measuredStepPlain_xorWireState registers.control registers.sign enabled wire = false
    simp [measuredStepPlain_xorWireState, upd, hsign, henabledAway wire haux hcontrol]
  have hchangedSourceClean : Clean
      (registers.terminal :: registers.blockScratch) changed := by
    intro wire hwire
    have hsource : wire ∈ registers.sourceScratch := by
      rw [← hlayout.measuredStepPlain_scratch_view]
      exact hwire
    exact hchangedAway wire (hlayout.measuredStepPlain_sourceScratch_mem_aux hsource)
      (by intro equality; subst wire; exact hlayout.measuredStepPlain_control_not_sourceScratch hsource)
  have hphase1NeSign : registers.phase1 ≠ registers.sign :=
    hlayout.measuredStepPlain_phase1_ne_after (by simp [measuredStepPlain_indexedStepAfterPhase1])
  have hphase2NeSign : registers.phase2 ≠ registers.sign :=
    hlayout.measuredStepPlain_phase2_ne_after (by simp [measuredStepPlain_indexedStepAfterPhase2])
  have hphase1 : changed registers.phase1 = state registers.phase1 := by
    change measuredStepPlain_xorWireState registers.control registers.sign enabled registers.phase1 =
      state registers.phase1
    rw [show measuredStepPlain_xorWireState registers.control registers.sign enabled registers.phase1 =
      enabled registers.phase1 by simp [measuredStepPlain_xorWireState, upd, hphase1NeSign]]
    exact measuredStepPlain_rControlState_preserves _ _ _ _ _ _ hcontrolNePhase1.symm
  have hphase2 : changed registers.phase2 = state registers.phase2 := by
    change measuredStepPlain_xorWireState registers.control registers.sign enabled registers.phase2 =
      state registers.phase2
    rw [show measuredStepPlain_xorWireState registers.control registers.sign enabled registers.phase2 =
      enabled registers.phase2 by simp [measuredStepPlain_xorWireState, upd, hphase2NeSign]]
    exact measuredStepPlain_rControlState_preserves _ _ _ _ _ _ hcontrolNePhase2.symm
  have hlength : ∀ wire ∈ registers.lengthRPrime,
      changed wire = state wire := by
    intro wire hwire
    have hwireNeControl : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.remainderPhase2.control_not_r hwire
    have hwireNeSign : wire ≠ registers.sign := by
      exact hlayout.measuredStepPlain_lengthRPrime_ne_outside hwire (Or.inl (by
        simp [measuredStepPlain_indexedStepBeforeLengthRPrime]))
    change measuredStepPlain_xorWireState registers.control registers.sign enabled wire = state wire
    rw [show measuredStepPlain_xorWireState registers.control registers.sign enabled wire = enabled wire by
      simp [measuredStepPlain_xorWireState, upd, hwireNeSign]]
    exact measuredStepPlain_rControlState_preserves _ _ _ _ _ _ hwireNeControl
  have hterminalNotConditions : registers.terminal ∉
      [registers.phase1, registers.phase2] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · exact hlayout.measuredStepPlain_aux_not_payload
        (hlayout.measuredStepPlain_sourceScratch_mem_aux (by rw [← hlayout.measuredStepPlain_scratch_view]; simp))
        (by simp [measuredStepPlain_indexedStepPayload])
    · exact hlayout.measuredStepPlain_aux_not_payload
        (hlayout.measuredStepPlain_sourceScratch_mem_aux (by rw [← hlayout.measuredStepPlain_scratch_view]; simp))
        (by simp [measuredStepPlain_indexedStepPayload])
  have hpredicate : rControlNonterminalPredicate
      [registers.phase1, registers.phase2] 2 registers.lengthRPrime
        registers.terminal changed = predicate := by
    change rControlNonterminalPredicate [registers.phase1, registers.phase2] 2
        registers.lengthRPrime registers.terminal changed =
      rControlNonterminalPredicate [registers.phase1, registers.phase2] 2
        registers.lengthRPrime registers.terminal state
    exact measuredStepPlain_rControlNonterminalPredicate_congr _ _ _ _ _ _ hterminalNotConditions
      (by
        intro wire hwire
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
        rcases hwire with rfl | rfl
        · exact hphase1
        · exact hphase2)
      hlength
  have henabledControl : enabled registers.control = predicate := by
    simp [enabled, measuredStepPlain_rControlState, predicate, hcontrolFalse]
  have hchangedControl : changed registers.control = enabled registers.control := by
    simp [changed, measuredStepPlain_xorWireState, upd, hcontrolNeSign]
  have hfinalRun : run (measuredStepPlain_remainderPhase2Control registers) changed =
      measuredStepPlain_rControlState [registers.phase1, registers.phase2] 2 registers.control
        registers.lengthRPrime registers.terminal changed := by
    simpa [measuredStepPlain_remainderPhase2Control, measuredStepPlain_toggleRControl, measuredStepPlain_rControlState] using
      (run_rControlNonterminal [registers.phase1, registers.phase2] 2 registers.control
        registers.lengthRPrime registers.terminal registers.blockScratch changed
        hlayout.remainderPhase2 hchangedSourceClean)
  have hfinalControl :
      measuredStepPlain_rControlState [registers.phase1, registers.phase2] 2 registers.control
          registers.lengthRPrime registers.terminal changed registers.control = false := by
    simp [measuredStepPlain_rControlState, hchangedControl, henabledControl, hpredicate]
  have hrun : run (blockB2 registers) state = measuredStepPlain_blockB2State registers state := by
    simp only [measuredStepPlain_view_blockB2, measuredStepPlain_source_blockB2, Classical.run_append]
    rw [henabledRun, hchangedRun, hfinalRun]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire haux
    by_cases hcontrol : wire = registers.control
    · subst wire
      exact hfinalControl
    · change measuredStepPlain_rControlState [registers.phase1, registers.phase2] 2 registers.control
        registers.lengthRPrime registers.terminal changed wire = false
      rw [measuredStepPlain_rControlState_preserves _ _ _ _ _ _ hcontrol]
      exact hchangedAway wire haux hcontrol

private theorem measuredStepPlain_remainderRestoreControl_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      state wire = false) :
    run (measuredStepPlain_remainderRestoreControl registers) state =
        measuredStepPlain_remainderRestoreControlState registers state ∧
      ∀ wire ∈ registers.aux, wire ≠ registers.control →
        measuredStepPlain_remainderRestoreControlState registers state wire = false := by
  let marked := measuredStepPlain_andXorWireState registers.phase2 registers.sign registers.terminal state
  let enabled := measuredStepPlain_rControlState [registers.phase1, registers.terminal] 0
    registers.control registers.lengthRPrime (registers.blockScratch.getD 0 0) marked
  let middle := measuredStepPlain_toggleRControl registers ([registers.phase1, registers.terminal]) 0
    (registers.blockScratch.getD 0 0) (registers.blockScratch.drop 1)
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.measuredStepPlain_scratch_view]
    simp
  have hterminalAux : registers.terminal ∈ registers.aux :=
    hlayout.measuredStepPlain_sourceScratch_mem_aux hterminalSource
  have hterminalNeControl : registers.terminal ≠ registers.control := by
    intro equality
    exact hlayout.measuredStepPlain_control_not_sourceScratch (equality ▸ hterminalSource)
  have hphase2NeTerminal : registers.phase2 ≠ registers.terminal := by
    have hphysical := hlayout.remainderRestoreCCX
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hphysical
    exact hphysical.1.2
  have hsignNeTerminal : registers.sign ≠ registers.terminal := by
    have hphysical := hlayout.remainderRestoreCCX
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hphysical
    exact hphysical.2.1
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hcontrolNeSign : registers.control ≠ registers.sign :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hmarkedRun : run ([.CCX registers.phase2 registers.sign registers.terminal] :
      Circuit) state = marked := by
    exact measuredStepPlain_run_andXorWireState registers.phase2 registers.sign registers.terminal state
  have hblockPositive : 0 < registers.blockScratch.length := by
    have := hlayout.terminalPaddingCapacity
    omega
  have hmarkedClean : Clean
      (registers.blockScratch.getD 0 0 :: registers.blockScratch.drop 1) marked := by
    intro wire hwire
    have hblock : wire ∈ registers.blockScratch := by
      rcases List.mem_cons.mp hwire with hzero | htail
      · rw [hzero]
        exact measuredStepPlain_indexedStep_getD_mem registers.blockScratch 0 0 hblockPositive
      · exact List.mem_of_mem_drop htail
    have haux := hlayout.measuredStepPlain_blockScratch_mem_aux hblock
    have hcontrol : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_control_not_sourceScratch
        (List.mem_of_mem_drop hblock)
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_terminal_not_blockScratch hblock
    change measuredStepPlain_andXorWireState registers.phase2 registers.sign registers.terminal state wire =
      false
    simp [measuredStepPlain_andXorWireState, upd, hterminal, hclean wire haux hcontrol]
  have henabledRun : run middle marked = enabled := by
    simpa [middle, measuredStepPlain_toggleRControl, enabled, measuredStepPlain_rControlState] using
      (run_rControlNonterminal [registers.phase1, registers.terminal] 0
        registers.control registers.lengthRPrime (registers.blockScratch.getD 0 0)
        (registers.blockScratch.drop 1) marked hlayout.remainderRestore hmarkedClean)
  have hfinalRun : run ([.CCX registers.phase2 registers.sign registers.terminal] :
      Circuit) enabled =
      measuredStepPlain_andXorWireState registers.phase2 registers.sign registers.terminal enabled := by
    exact measuredStepPlain_run_andXorWireState registers.phase2 registers.sign registers.terminal enabled
  have hinnerRun : run
      (.CCX registers.phase2 registers.sign registers.terminal :: middle) state =
      enabled := by
    rw [Classical.run_cons]
    rw [show Classical.applyGate
        (.CCX registers.phase2 registers.sign registers.terminal) state = marked by
      simpa [Classical.run] using hmarkedRun]
    exact henabledRun
  have hrun : run (measuredStepPlain_remainderRestoreControl registers) state =
      measuredStepPlain_remainderRestoreControlState registers state := by
    simp only [measuredStepPlain_remainderRestoreControl, Classical.run_append]
    rw [hinnerRun, hfinalRun]
    rfl
  constructor
  · exact hrun
  · intro wire haux hcontrol
    by_cases hterminal : wire = registers.terminal
    · subst wire
      have hterminalFalse : state registers.terminal = false :=
        hclean registers.terminal hterminalAux hterminalNeControl
      simp [measuredStepPlain_remainderRestoreControlState, measuredStepPlain_andXorWireState,
        measuredStepPlain_rControlState, upd, hterminalFalse, hterminalNeControl,
        hphase2NeTerminal, hsignNeTerminal,
        Ne.symm hcontrolNePhase2, Ne.symm hcontrolNeSign]
    · have hwireFalse := hclean wire haux hcontrol
      simp [measuredStepPlain_remainderRestoreControlState, measuredStepPlain_andXorWireState,
        measuredStepPlain_rControlState, upd, hterminal, hcontrol, hwireFalse]

private theorem measuredStepPlain_blockB3Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : measuredStepPlain_IndexedStepBorrowedReady registers state) :
    run (blockB3Forward registers n window) state =
        measuredStepPlain_blockB3ForwardState registers n window state ∧
      measuredStepPlain_IndexedStepBorrowedReady registers
        (run (blockB3Forward registers n window) state) := by
  have hinitialAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      state wire = false := by
    intro wire hwire _
    exact hready wire hwire
  let enabled := measuredStepPlain_remainderRestoreControlState registers state
  have hfirst := measuredStepPlain_remainderRestoreControl_correct registers n T state hlayout hinitialAway
  have hfirstRun : run (measuredStepPlain_remainderRestoreControl registers) state = enabled := by
    simpa only [enabled] using hfirst.1
  have henabledAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      enabled wire = false := by
    simpa only [enabled] using hfirst.2
  have henabledReady : IntervalReady (registers.remainder window) enabled := by
    intro wire hwire
    exact henabledAway wire (hlayout.measuredStepPlain_remainder_scratch_sub_aux window wire hwire) (by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_control_not_remainder_scratch window hwindow hwire)
  let changed := intervalAddSubState (registers.remainder window) n
    window.start window.stop .add false .work1 enabled
  have hchangedRun : run
      (intervalAddSubUnitary (registers.remainder window) n window.start window.stop
        .add false .work1) enabled = changed := by
    subst window
    simpa only [changed] using
      run_intervalAddSubUnitary_state
        (registers.remainder (certifiedActiveWindows n T).remainder) n
        (certifiedActiveWindows n T).remainder.start
        (certifiedActiveWindows n T).remainder.stop .add false .work1 enabled
        hlayout.remainder (by simpa using henabledReady)
  have hchangedAway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      changed wire = false := by
    intro wire haux hcontrol
    rw [← hchangedRun]
    exact measuredStepPlain_remainderInterval_clean_auxAwayControl registers n T window .add false enabled
      hlayout hwindow henabledAway wire haux hcontrol
  have hsecond := measuredStepPlain_remainderRestoreControl_correct registers n T changed hlayout hchangedAway
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.measuredStepPlain_scratch_view]
    simp
  have hterminalAux : registers.terminal ∈ registers.aux :=
    hlayout.measuredStepPlain_sourceScratch_mem_aux hterminalSource
  have hterminalNeControl : registers.terminal ≠ registers.control := by
    intro equality
    exact hlayout.measuredStepPlain_control_not_sourceScratch (equality ▸ hterminalSource)
  have hcontrolNePhase1 : registers.control ≠ registers.phase1 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hcontrolNeSign : registers.control ≠ registers.sign :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hterminalNePhase1 : registers.terminal ≠ registers.phase1 :=
    hlayout.measuredStepPlain_aux_not_payload hterminalAux (by simp [measuredStepPlain_indexedStepPayload])
  have hterminalNePhase2 : registers.terminal ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hterminalAux (by simp [measuredStepPlain_indexedStepPayload])
  have hterminalNeSign : registers.terminal ≠ registers.sign :=
    hlayout.measuredStepPlain_aux_not_payload hterminalAux (by simp [measuredStepPlain_indexedStepPayload])
  have hphase1 : changed registers.phase1 = state registers.phase1 := by
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .add false .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.measuredStepPlain_phase1_not_remainder window)]
    exact measuredStepPlain_remainderRestoreControlState_preserves registers state
      hterminalNePhase1.symm hcontrolNePhase1.symm
  have hphase2 : changed registers.phase2 = state registers.phase2 := by
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .add false .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.measuredStepPlain_phase2_not_remainder window)]
    exact measuredStepPlain_remainderRestoreControlState_preserves registers state
      hterminalNePhase2.symm hcontrolNePhase2.symm
  have hsign : changed registers.sign = state registers.sign := by
    rw [← hchangedRun]
    have hpreserves : run
        (intervalAddSubUnitary (registers.remainder window) n window.start window.stop
          .add false .work1) enabled registers.sign = enabled registers.sign := by
      subst window
      simpa [IndexedStepRegisters.measuredStepPlain_view_remainder, IndexedStepRegisters.measuredStepPlain_source_remainder, IndexedStepRegisters.measuredStepPlain_remainderBase] using
        intervalAddSubUnitary_preserves_sign_of_false
          (registers.remainder (certifiedActiveWindows n T).remainder) n
          (certifiedActiveWindows n T).remainder.start
          (certifiedActiveWindows n T).remainder.stop .add .work1 enabled
          hlayout.remainder (by simpa using henabledReady)
    rw [hpreserves]
    exact measuredStepPlain_remainderRestoreControlState_preserves registers state
      hterminalNeSign.symm hcontrolNeSign.symm
  have hlength : ∀ wire ∈ registers.lengthRPrime,
      changed wire = state wire := by
    intro wire hwire
    rw [← hchangedRun,
      intervalAddSubUnitary_preservesOutside (registers.remainder window) n
        window.start window.stop .add false .work1 enabled (by
          subst window
          exact hlayout.remainder) (hlayout.measuredStepPlain_lengthRPrime_not_remainder window hwire)]
    have hwireNeTerminal : wire ≠ registers.terminal := by
      exact (hlayout.measuredStepPlain_aux_not_payload hterminalAux (by
        simp [measuredStepPlain_indexedStepPayload, hwire])).symm
    have hwireNeControl : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.remainderRestore.control_not_r hwire
    exact measuredStepPlain_remainderRestoreControlState_preserves registers state
      hwireNeTerminal hwireNeControl
  have hinitialTerminal : state registers.terminal = false :=
    hready registers.terminal hterminalAux
  have hchangedTerminal : changed registers.terminal = false :=
    hchangedAway registers.terminal hterminalAux hterminalNeControl
  let markedInitial := measuredStepPlain_andXorWireState registers.phase2 registers.sign
    registers.terminal state
  let markedChanged := measuredStepPlain_andXorWireState registers.phase2 registers.sign
    registers.terminal changed
  let predicateInitial := rControlNonterminalPredicate
    [registers.phase1, registers.terminal] 0 registers.lengthRPrime
      (registers.blockScratch.getD 0 0) markedInitial
  let predicateChanged := rControlNonterminalPredicate
    [registers.phase1, registers.terminal] 0 registers.lengthRPrime
      (registers.blockScratch.getD 0 0) markedChanged
  have hmarkedPhase1 : markedChanged registers.phase1 =
      markedInitial registers.phase1 := by
    simp [markedChanged, markedInitial, measuredStepPlain_andXorWireState, upd,
      hterminalNePhase1.symm, hphase1]
  have hmarkedTerminal : markedChanged registers.terminal =
      markedInitial registers.terminal := by
    simp [markedChanged, markedInitial, measuredStepPlain_andXorWireState,
      hinitialTerminal, hchangedTerminal, hphase2, hsign]
  have hmarkedLength : ∀ wire ∈ registers.lengthRPrime,
      markedChanged wire = markedInitial wire := by
    intro wire hwire
    have hwireNeTerminal : wire ≠ registers.terminal :=
      (hlayout.measuredStepPlain_aux_not_payload hterminalAux (by
        simp [measuredStepPlain_indexedStepPayload, hwire])).symm
    simp [markedChanged, markedInitial, measuredStepPlain_andXorWireState, upd,
      hwireNeTerminal, hlength wire hwire]
  have hblockPositive : 0 < registers.blockScratch.length := by
    have := hlayout.terminalPaddingCapacity
    omega
  have hzeroBlock : registers.blockScratch.getD 0 0 ∈ registers.blockScratch :=
    measuredStepPlain_indexedStep_getD_mem registers.blockScratch 0 0 hblockPositive
  have hzeroNotConditions : registers.blockScratch.getD 0 0 ∉
      [registers.phase1, registers.terminal] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · exact hlayout.measuredStepPlain_aux_not_payload (hlayout.measuredStepPlain_blockScratch_mem_aux hzeroBlock)
        (by simp [measuredStepPlain_indexedStepPayload])
    · exact fun equality ↦ hlayout.measuredStepPlain_terminal_not_blockScratch
        (equality ▸ hzeroBlock)
  have hpredicate : predicateChanged = predicateInitial := by
    exact measuredStepPlain_rControlNonterminalPredicate_congr _ _ _ _ _ _ hzeroNotConditions
      (by
        intro wire hwire
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
        rcases hwire with rfl | rfl
        · exact hmarkedPhase1
        · exact hmarkedTerminal)
      hmarkedLength
  have hinitialControl : state registers.control = false :=
    hready registers.control hlayout.measuredStepPlain_control_mem_aux
  have henabledControl : enabled registers.control = predicateInitial := by
    simp [enabled, measuredStepPlain_remainderRestoreControlState, markedInitial, predicateInitial,
      measuredStepPlain_andXorWireState, measuredStepPlain_rControlState, upd, hterminalNeControl,
      hterminalNeControl.symm, hcontrolNePhase2.symm,
      hcontrolNeSign.symm, hterminalNePhase2.symm,
      hterminalNeSign.symm, hinitialControl]
  have hchangedControl : changed registers.control = enabled registers.control := by
    rw [← hchangedRun]
    subst window
    exact intervalAddSubUnitary_preserves_control
      (registers.remainder (certifiedActiveWindows n T).remainder) n
      (certifiedActiveWindows n T).remainder.start
      (certifiedActiveWindows n T).remainder.stop .add false .work1 enabled
      hlayout.remainder (by simpa using henabledReady)
  have hfinalControl : measuredStepPlain_remainderRestoreControlState registers changed
      registers.control = false := by
    have hshape : measuredStepPlain_remainderRestoreControlState registers changed registers.control =
        Bool.xor (changed registers.control) predicateChanged := by
      simp [measuredStepPlain_remainderRestoreControlState, markedChanged, predicateChanged,
        measuredStepPlain_andXorWireState, measuredStepPlain_rControlState, upd, hterminalNeControl,
        hterminalNeControl.symm, hcontrolNePhase2.symm,
        hcontrolNeSign.symm, hterminalNePhase2.symm,
        hterminalNeSign.symm]
    rw [hshape, hchangedControl, henabledControl, hpredicate]
    simp
  have hrun : run (blockB3Forward registers n window) state =
      measuredStepPlain_blockB3ForwardState registers n window state := by
    simp only [measuredStepPlain_view_blockB3Forward, measuredStepPlain_source_blockB3Forward, Classical.run_append]
    rw [hfirstRun, hchangedRun, hsecond.1]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    intro wire haux
    by_cases hcontrol : wire = registers.control
    · subst wire
      exact hfinalControl
    · exact hsecond.2 wire haux hcontrol

private theorem measuredStepPlain_blockBForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : measuredStepPlain_IndexedStepBorrowedReady registers state) :
    run (blockBForward registers n window) state =
        measuredStepPlain_blockBForwardState registers n window state ∧
      measuredStepPlain_IndexedStepBorrowedReady registers
        (run (blockBForward registers n window) state) := by
  have hfirst := measuredStepPlain_blockB1Forward_correct registers n T window state hlayout hwindow hready
  have hfirstReady : measuredStepPlain_IndexedStepBorrowedReady registers
      (measuredStepPlain_blockB1ForwardState registers n window state) := by
    rw [← hfirst.1]
    exact hfirst.2
  have hsecond := measuredStepPlain_blockB2_correct registers n T
    (measuredStepPlain_blockB1ForwardState registers n window state) hlayout hfirstReady
  have hsecondReady : measuredStepPlain_IndexedStepBorrowedReady registers
      (measuredStepPlain_blockB2State registers (measuredStepPlain_blockB1ForwardState registers n window state)) := by
    rw [← hsecond.1]
    exact hsecond.2
  have hthird := measuredStepPlain_blockB3Forward_correct registers n T window
    (measuredStepPlain_blockB2State registers (measuredStepPlain_blockB1ForwardState registers n window state))
      hlayout hwindow hsecondReady
  have hrun : run (blockBForward registers n window) state =
      measuredStepPlain_blockBForwardState registers n window state := by
    simp only [blockBForward, Classical.run_append]
    rw [hfirst.1, hsecond.1, hthird.1]
    rfl
  constructor
  · exact hrun
  · rw [hrun]
    change measuredStepPlain_IndexedStepBorrowedReady registers
      (measuredStepPlain_blockB3ForwardState registers n window
        (measuredStepPlain_blockB2State registers (measuredStepPlain_blockB1ForwardState registers n window state)))
    rw [← hthird.1]
    exact hthird.2

private theorem measuredStepPlain_blockCForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : measuredStepPlain_IndexedStepBorrowedReady registers state) :
    run (blockCForward registers) state = measuredStepPlain_blockCForwardState registers state ∧
      IndexedStepReady registers (run (blockCForward registers) state) := by
  let terminalMatch := registerMatches (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) state
  let marked := measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
    (measuredStepPlain_terminalConditionValue registers) registers.terminal state
  have hblock : Clean registers.blockScratch state := by
    intro wire hwire
    exact hready wire (hlayout.measuredStepPlain_blockScratch_mem_aux hwire)
  have hmarkedRun : run (measuredStepPlain_toggleTerminal registers) state = marked := by
    simpa [measuredStepPlain_toggleTerminal, marked, measuredStepPlain_matchXorState] using
      run_computeControl (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) registers.terminal
        registers.blockScratch state hlayout.terminalControl hblock
  have hmarkedBlock : Clean registers.blockScratch marked := by
    simpa [marked, measuredStepPlain_matchXorState] using
      measuredStepPlain_clean_upd_not_mem hblock hlayout.measuredStepPlain_terminal_not_blockScratch
  let restored := measuredStepPlain_terminalEpochRestoreState registers.terminal registers.shiftEpoch
    registers.quotientLow marked
  have hrestoredRun : run
      (terminalEpochRestore registers.terminal registers.shiftEpoch registers.quotientLow)
      marked = restored := by
    simpa only [restored] using measuredStepPlain_run_terminalEpochRestoreState registers.terminal
      registers.shiftEpoch registers.quotientLow marked hlayout.terminalEpoch
  have hrestoredBlock : Clean registers.blockScratch restored := by
    intro wire hwire
    have houtside := hlayout.measuredStepPlain_blockScratch_outside_terminalEpoch wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at houtside
    change restored wire = false
    rw [show restored wire = marked wire by
      exact measuredStepPlain_terminalEpochRestoreState_preserves _ _ _ _ houtside.2.1 houtside.2.2]
    exact hmarkedBlock wire hwire
  have hrestoredCondition : registerMatches (measuredStepPlain_terminalConditionWires registers)
      (measuredStepPlain_terminalConditionValue registers) restored = terminalMatch := by
    change registerMatches (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) restored =
      registerMatches (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) state
    apply measuredStepPlain_registerMatches_congr
    intro wire hwire
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_terminal_not_condition hwire
    have hshift : wire ≠ registers.shiftEpoch := by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_shiftEpoch_not_condition hwire
    have hquotient : wire ≠ registers.quotientLow := by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_quotientLow_not_condition hwire
    rw [show restored wire = marked wire by
      exact measuredStepPlain_terminalEpochRestoreState_preserves _ _ _ _ hshift hquotient]
    simp [marked, measuredStepPlain_matchXorState, upd, hterminal]
  have hunmarkedRun : run (measuredStepPlain_toggleTerminal registers) restored =
      measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) registers.terminal restored := by
    simpa [measuredStepPlain_toggleTerminal, measuredStepPlain_matchXorState] using
      run_computeControl (measuredStepPlain_terminalConditionWires registers)
        (measuredStepPlain_terminalConditionValue registers) registers.terminal
        registers.blockScratch restored hlayout.terminalControl hrestoredBlock
  have hterminalAux : registers.terminal ∈ registers.aux :=
    hlayout.measuredStepPlain_sourceScratch_mem_aux (by rw [← hlayout.measuredStepPlain_scratch_view]; simp)
  have hterminalFalse : state registers.terminal = false :=
    hready registers.terminal hterminalAux
  have hmarkedTerminal : marked registers.terminal = terminalMatch := by
    simp [marked, measuredStepPlain_matchXorState, terminalMatch, hterminalFalse]
  have hterminalEpoch := hlayout.terminalEpoch
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hterminalEpoch
  have hrestoredTerminal : restored registers.terminal = terminalMatch := by
    rw [show restored registers.terminal = marked registers.terminal by
      exact measuredStepPlain_terminalEpochRestoreState_preserves _ _ _ _
        hterminalEpoch.1.1 hterminalEpoch.1.2]
    exact hmarkedTerminal
  have hfinalTerminal : measuredStepPlain_blockCForwardState registers state registers.terminal = false := by
    change measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
      (measuredStepPlain_terminalConditionValue registers) registers.terminal restored
        registers.terminal = false
    simp [measuredStepPlain_matchXorState, hrestoredTerminal, hrestoredCondition]
  have hcontrolFalse : state registers.control = false :=
    hready registers.control hlayout.measuredStepPlain_control_mem_aux
  have hmarkedControl : marked registers.control = false := by
    simp [marked, measuredStepPlain_matchXorState, upd, hlayout.measuredStepPlain_control_ne_terminal, hcontrolFalse]
  have hrestoredControl : restored registers.control = false := by
    rw [show restored registers.control = marked registers.control by
      exact measuredStepPlain_terminalEpochRestoreState_preserves _ _ _ _
        hlayout.measuredStepPlain_control_ne_shiftEpoch hlayout.measuredStepPlain_control_ne_quotientLow]
    exact hmarkedControl
  have hfinalControl : measuredStepPlain_blockCForwardState registers state registers.control = false := by
    change measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
      (measuredStepPlain_terminalConditionValue registers) registers.terminal restored
        registers.control = false
    simp [measuredStepPlain_matchXorState, upd, hlayout.measuredStepPlain_control_ne_terminal, hrestoredControl]
  have hfinalBlock : Clean registers.blockScratch (measuredStepPlain_blockCForwardState registers state) := by
    intro wire hwire
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_terminal_not_blockScratch hwire
    change measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
      (measuredStepPlain_terminalConditionValue registers) registers.terminal restored wire = false
    simp [measuredStepPlain_matchXorState, upd, hterminal, hrestoredBlock wire hwire]
  have hrun : run (blockCForward registers) state =
      measuredStepPlain_blockCForwardState registers state := by
    simp only [measuredStepPlain_view_blockCForward, measuredStepPlain_source_blockCForward, Classical.run_append]
    rw [hmarkedRun, hrestoredRun, hunmarkedRun]
    rfl
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      measuredStepPlain_blockCForwardState registers state wire = false := by
    intro wire hrepair
    have hnotPayload := hlayout.measuredStepPlain_remainderRepairScratch_not_payload hrepair
    have hnotSource := hlayout.measuredStepPlain_remainderRepairScratch_not_sourceScratch hrepair
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      apply hnotSource
      rw [equality, ← hlayout.measuredStepPlain_scratch_view]
      simp
    have hshift := hlayout.measuredStepPlain_remainderRepairScratch_ne_shiftEpoch hrepair
    have hquotient : wire ≠ registers.quotientLow := by
      intro equality
      apply hnotPayload
      simp [measuredStepPlain_indexedStepPayload, equality, hlayout.measuredStepPlain_quotientLow_mem_lengthQ]
    calc
      measuredStepPlain_blockCForwardState registers state wire = restored wire := by
        change measuredStepPlain_matchXorState (measuredStepPlain_terminalConditionWires registers)
          (measuredStepPlain_terminalConditionValue registers) registers.terminal restored wire =
            restored wire
        exact measuredStepPlain_matchXorState_preserves _ _ _ _ hterminal
      _ = marked wire := measuredStepPlain_terminalEpochRestoreState_preserves _ _ _ _
        hshift hquotient
      _ = state wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hterminal
      _ = false := hready wire
        (hlayout.measuredStepPlain_remainderRepairScratch_mem_aux hrepair)
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsource | hrepair
    · exact hfinalControl
    · rw [← hlayout.measuredStepPlain_scratch_view] at hsource
      simp only [List.mem_cons] at hsource
      rcases hsource with rfl | hblockWire
      · exact hfinalTerminal
      · exact hfinalBlock wire hblockWire
    · exact hrepairFinal wire hrepair

private theorem measuredStepPlain_run_quotientSwapUnitary_indexedState
    (registers : QuotientSwapRegisters) {k K : Nat} (state : BasisState)
    (hlayout : QuotientSwapLayout registers k K)
    (hready : QuotientSwapReady registers state) :
    run (quotientSwapUnitary registers k K) state =
      measuredStepPlain_indexedQuotientSwapState registers k K state := by
  let afterAdd := run
    (cuccaroAdd registers.lengthT registers.lengthQ
      (registers.carry k K)) state
  let prepared := run
    (addConstant registers.lengthQ registers.constantScratch
      (registers.carry k K) 3) afterAdd
  let purePrepared := measuredStepPlain_quotientPreparedState registers state
  have hcorrect := quotientSwapUnitary_correct registers state hlayout hready
  have hbits : wireValues registers.lengthQ prepared =
      measuredStepPlain_quotientPreparedBits registers state := by
    simpa [afterAdd, prepared, measuredStepPlain_quotientPreparedBits] using hcorrect.2.2.1
  have hlength : (measuredStepPlain_quotientPreparedBits registers state).length =
      registers.lengthQ.length := by
    have := congrArg List.length hbits
    simpa [wireValues] using this.symm
  have hlengthQNodup : registers.lengthQ.Nodup := by
    have hphysical := hlayout.physical
    rw [QuotientSwapRegisters.allWires] at hphysical
    have hrest := (List.nodup_append.mp hphysical).2.1
    have harithmetic := (List.nodup_append.mp hrest).2.1
    have hqScratch := (List.nodup_append.mp harithmetic).2.1
    exact (List.nodup_append.mp hqScratch).1
  have hpureBits : wireValues registers.lengthQ purePrepared =
      measuredStepPlain_quotientPreparedBits registers state := by
    exact measuredStepPlain_indexedWireValues_writeWireValues registers.lengthQ
      (measuredStepPlain_quotientPreparedBits registers state) state hlengthQNodup hlength
  have hroute : (quotientSwapTree registers k K).routeLabel prepared =
      (quotientSwapTree registers k K).routeLabel purePrepared := by
    apply measuredStepPlain_indexedRouteLabel_congr
    intro wire hwire
    have hlengthWire := quotientSwapTree_indexWires_mem_lengthQ registers
      hlayout.k_le_K hlayout.index_width wire hwire
    exact measuredStepPlain_indexedWireValues_eq_at registers.lengthQ prepared purePrepared
      (hbits.trans hpureBits.symm) hlengthWire
  rw [hcorrect.1, hroute]
  rfl

private theorem measuredStepPlain_indexedQuotientWorkAt_mem_any
    (registers : QuotientSwapRegisters) {k K : Nat}
    (hlayout : QuotientSwapLayout registers k K) (label : Nat) :
    registers.workAt k label ∈ registers.work1 := by
  have hpositive : 0 < registers.work1.length := by
    rw [hlayout.work1_length]
    omega
  by_cases hindex : label - k < registers.work1.length
  · exact measuredStepPlain_indexedStep_getD_mem registers.work1 (label - k)
      (registers.work1.getD 0 0) hindex
  · rw [QuotientSwapRegisters.workAt,
      List.getD_eq_default registers.work1 (registers.work1.getD 0 0)
        (Nat.le_of_not_gt hindex)]
    exact measuredStepPlain_indexedStep_getD_mem registers.work1 0 0 hpositive

private theorem measuredStepPlain_indexedQuotientSwapState_preserves
    (registers : QuotientSwapRegisters) {k K : Nat}
    (state : BasisState) (hlayout : QuotientSwapLayout registers k K)
    {wire : Wire} (hsign : wire ≠ registers.sign)
    (hwork : wire ∉ registers.work1) :
    measuredStepPlain_indexedQuotientSwapState registers k K state wire = state wire := by
  have hworkAt : wire ≠ registers.workAt k
      ((quotientSwapTree registers k K).routeLabel
        (measuredStepPlain_quotientPreparedState registers state)) := by
    intro equality
    subst wire
    exact hwork (measuredStepPlain_indexedQuotientWorkAt_mem_any registers hlayout _)
  unfold measuredStepPlain_indexedQuotientSwapState quotientSwapState
  split <;> simp [upd, hsign, hworkAt]

private theorem measuredStepPlain_blockD1Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      measuredStepPlain_phase2LengthControl registers;
      controlledIncrement registers.control registers.lengthQ (measuredStepPlain_lengthCarries registers);
      measuredStepPlain_phase2LengthControl registers
    }) state = measuredStepPlain_blockD1ForwardState registers state ∧
      IndexedStepReady registers
        (run (circuit! {
          measuredStepPlain_phase2LengthControl registers;
          controlledIncrement registers.control registers.lengthQ
            (measuredStepPlain_lengthCarries registers);
          measuredStepPlain_phase2LengthControl registers
        }) state) := by
  have hsource : Clean registers.sourceScratch state := by
    intro wire hwire
    exact hready wire (by
      simp [IndexedStepRegisters.sharedScratch, hwire])
  let enabled := measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 2
    registers.control state
  have henabled := measuredStepPlain_run_computeControl_state [registers.phase1, registers.phase2] 2
    registers.control registers.sourceScratch state hlayout.phase2Length hsource
  have henabledRun : run (measuredStepPlain_phase2LengthControl registers) state = enabled := by
    simpa [measuredStepPlain_phase2LengthControl, enabled] using henabled.1
  have henabledSource : Clean registers.sourceScratch enabled := by
    simpa only [enabled] using henabled.2
  have hcarries : Clean (measuredStepPlain_lengthCarries registers) enabled := by
    intro wire hwire
    exact henabledSource wire (List.mem_of_mem_take hwire)
  let changed := measuredStepPlain_indexedIncrementWordState (enabled registers.control)
    registers.lengthQ enabled
  have hchangedRun : run
      (controlledIncrement registers.control registers.lengthQ
        (measuredStepPlain_lengthCarries registers)) enabled = changed := by
    simpa only [changed] using measuredStepPlain_run_controlledIncrement_indexedState
      registers.control registers.lengthQ (measuredStepPlain_lengthCarries registers) enabled
      hlayout.lengthCarryCapacity hlayout.lengthCarryPhysical hcarries
  have hchangedSource : Clean registers.sourceScratch changed := by
    intro wire hwire
    have hnotLengthQ : wire ∉ registers.lengthQ := by
      intro hlength
      exact (hlayout.measuredStepPlain_aux_not_payload
        (auxWire := wire) (payloadWire := wire)
        (hlayout.measuredStepPlain_sourceScratch_mem_aux hwire)
        (by simp [measuredStepPlain_indexedStepPayload, hlength])) rfl
    change changed wire = false
    rw [show changed wire = enabled wire by
      exact measuredStepPlain_indexedIncrementWordState_preservesOutside _ _ _ hnotLengthQ]
    exact henabledSource wire hwire
  have hcleared := measuredStepPlain_run_computeControl_state [registers.phase1, registers.phase2] 2
    registers.control registers.sourceScratch changed hlayout.phase2Length hchangedSource
  have hclearedRun : run (measuredStepPlain_phase2LengthControl registers) changed =
      measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 2
        registers.control changed := by
    simpa [measuredStepPlain_phase2LengthControl] using hcleared.1
  have hcontrolFalse : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hphase1NotQ : registers.phase1 ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.measuredStepPlain_phase1_ne_after (by
      simp [measuredStepPlain_indexedStepAfterPhase1, hmem])) rfl
  have hphase2NotQ : registers.phase2 ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.measuredStepPlain_phase2_ne_after (by
      simp [measuredStepPlain_indexedStepAfterPhase2, hmem])) rfl
  have hcontrolNotQ : registers.control ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.measuredStepPlain_aux_not_payload
      (auxWire := registers.control) (payloadWire := registers.control)
      hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl
  have henabledControl : enabled registers.control =
      registerMatches [registers.phase1, registers.phase2] 2 state := by
    simp [enabled, measuredStepPlain_matchXorState, hcontrolFalse]
  have hchangedControl : changed registers.control = enabled registers.control := by
    exact measuredStepPlain_indexedIncrementWordState_preservesOutside _ _ _ hcontrolNotQ
  have hpredicate : registerMatches [registers.phase1, registers.phase2] 2 changed =
      registerMatches [registers.phase1, registers.phase2] 2 state := by
    apply measuredStepPlain_registerMatches_congr
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl
    · change measuredStepPlain_indexedIncrementWordState (enabled registers.control)
        registers.lengthQ enabled registers.phase1 = state registers.phase1
      rw [measuredStepPlain_indexedIncrementWordState_preservesOutside _ _ _ hphase1NotQ]
      simp [enabled, measuredStepPlain_matchXorState, upd, hlayout.measuredStepPlain_control_ne_phase1.symm]
    · change measuredStepPlain_indexedIncrementWordState (enabled registers.control)
        registers.lengthQ enabled registers.phase2 = state registers.phase2
      rw [measuredStepPlain_indexedIncrementWordState_preservesOutside _ _ _ hphase2NotQ]
      simp [enabled, measuredStepPlain_matchXorState, upd, hcontrolNePhase2.symm]
  have hfinalControl : measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 2
      registers.control changed registers.control = false := by
    simp [measuredStepPlain_matchXorState, hchangedControl, henabledControl, hpredicate]
  have hrun : run (circuit! {
      measuredStepPlain_phase2LengthControl registers;
      controlledIncrement registers.control registers.lengthQ (measuredStepPlain_lengthCarries registers);
      measuredStepPlain_phase2LengthControl registers
    }) state = measuredStepPlain_blockD1ForwardState registers state := by
    simp only [Classical.run_append]
    rw [henabledRun, hchangedRun, hclearedRun]
    rfl
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      measuredStepPlain_blockD1ForwardState registers state wire = false := by
    intro wire hrepair
    have hcontrol := hlayout.measuredStepPlain_remainderRepairScratch_ne_control hrepair
    have hnotPayload := hlayout.measuredStepPlain_remainderRepairScratch_not_payload hrepair
    have hnotLengthQ : wire ∉ registers.lengthQ := by
      intro hmem
      exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, hmem])
    calc
      measuredStepPlain_blockD1ForwardState registers state wire = changed wire := by
        change measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 2
          registers.control changed wire = changed wire
        exact measuredStepPlain_matchXorState_preserves _ _ _ _ hcontrol
      _ = enabled wire := measuredStepPlain_indexedIncrementWordState_preservesOutside _ _ _
        hnotLengthQ
      _ = state wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hcontrol
      _ = false := hready wire
        (hlayout.measuredStepPlain_remainderRepairScratch_mem_sharedScratch hrepair)
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsourceWire | hrepair
    · exact hfinalControl
    · exact hcleared.2 wire hsourceWire
    · exact hrepairFinal wire hrepair

private theorem measuredStepPlain_blockD2Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      measuredStepPlain_quotientXorControl registers;
      quotientSwapUnitary (registers.quotient window) window.start window.stop;
      measuredStepPlain_quotientXorControlInverse registers
    }) state = measuredStepPlain_blockD2ForwardState registers window state ∧
      IndexedStepReady registers
        (run (circuit! {
          measuredStepPlain_quotientXorControl registers;
          quotientSwapUnitary (registers.quotient window) window.start window.stop;
          measuredStepPlain_quotientXorControlInverse registers
        }) state) := by
  have hqLayout : QuotientSwapLayout (registers.quotient window)
      window.start window.stop := by
    subst window
    exact hlayout.quotient
  have hcontrolFalse : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hsource : Clean registers.sourceScratch state := by
    intro wire hwire
    exact hready wire (by simp [IndexedStepRegisters.sharedScratch, hwire])
  let enabled1 := measuredStepPlain_xorWireState registers.phase1 registers.control state
  let enabled2 := measuredStepPlain_xorWireState registers.phase2 registers.control enabled1
  have henabledRun : run (measuredStepPlain_quotientXorControl registers) state = enabled2 := by
    rfl
  have henabledSource : Clean registers.sourceScratch enabled2 := by
    intro wire hwire
    have hcontrol : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_control_not_sourceScratch hwire
    simp [enabled2, enabled1, measuredStepPlain_xorWireState, upd, hcontrol,
      hsource wire hwire]
  have hqReady : QuotientSwapReady (registers.quotient window) enabled2 := by
    intro wire hwire
    exact henabledSource wire (List.mem_of_mem_take hwire)
  let changed := measuredStepPlain_indexedQuotientSwapState (registers.quotient window)
    window.start window.stop enabled2
  have hchangedRun : run
      (quotientSwapUnitary (registers.quotient window) window.start window.stop)
      enabled2 = changed := by
    simpa only [changed] using measuredStepPlain_run_quotientSwapUnitary_indexedState
      (registers.quotient window) enabled2 hqLayout hqReady
  have hchangedSource : Clean registers.sourceScratch changed := by
    intro wire hwire
    have hsign : wire ≠ registers.sign :=
      hlayout.measuredStepPlain_aux_not_payload
        (auxWire := wire) (payloadWire := registers.sign)
        (hlayout.measuredStepPlain_sourceScratch_mem_aux hwire) (by simp [measuredStepPlain_indexedStepPayload])
    have hwork : wire ∉ (registers.quotient window).work1 := by
      intro hwindowWire
      change wire ∈ IndexedStepRegisters.windowSlice registers.work1 window at hwindowWire
      have hglobal := measuredStepPlain_windowSlice_mem registers.work1 window hwindowWire
      exact (hlayout.measuredStepPlain_aux_not_payload
        (auxWire := wire) (payloadWire := wire)
        (hlayout.measuredStepPlain_sourceScratch_mem_aux hwire)
        (by simp [measuredStepPlain_indexedStepPayload, hglobal])) rfl
    change changed wire = false
    rw [show changed wire = enabled2 wire by
      exact measuredStepPlain_indexedQuotientSwapState_preserves
        (registers.quotient window) enabled2 hqLayout hsign hwork]
    exact henabledSource wire hwire
  let disabled2 := measuredStepPlain_xorWireState registers.phase2 registers.control changed
  let disabled1 := measuredStepPlain_xorWireState registers.phase1 registers.control disabled2
  have hdisabledRun : run (measuredStepPlain_quotientXorControlInverse registers) changed = disabled1 := by
    rfl
  have hcontrolNeSign : registers.control ≠ registers.sign :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hcontrolNotWork : registers.control ∉
      (registers.quotient window).work1 := by
    intro hwindowWire
    change registers.control ∈
      IndexedStepRegisters.windowSlice registers.work1 window at hwindowWire
    have hglobal := measuredStepPlain_windowSlice_mem registers.work1 window hwindowWire
    exact (hlayout.measuredStepPlain_aux_not_payload
      (auxWire := registers.control) (payloadWire := registers.control)
      hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload, hglobal])) rfl
  have hphase1NeSign : registers.phase1 ≠ registers.sign :=
    hlayout.measuredStepPlain_phase1_ne_after (by simp [measuredStepPlain_indexedStepAfterPhase1])
  have hphase1NotWork : registers.phase1 ∉
      (registers.quotient window).work1 := by
    intro hwindowWire
    change registers.phase1 ∈
      IndexedStepRegisters.windowSlice registers.work1 window at hwindowWire
    exact (hlayout.measuredStepPlain_phase1_ne_after (by
      simp [measuredStepPlain_indexedStepAfterPhase1,
        measuredStepPlain_windowSlice_mem registers.work1 window hwindowWire])) rfl
  have hphase2NeSign : registers.phase2 ≠ registers.sign :=
    hlayout.measuredStepPlain_phase2_ne_after (by simp [measuredStepPlain_indexedStepAfterPhase2])
  have hphase2NotWork : registers.phase2 ∉
      (registers.quotient window).work1 := by
    intro hwindowWire
    change registers.phase2 ∈
      IndexedStepRegisters.windowSlice registers.work1 window at hwindowWire
    exact (hlayout.measuredStepPlain_phase2_ne_after (by
      simp [measuredStepPlain_indexedStepAfterPhase2,
        measuredStepPlain_windowSlice_mem registers.work1 window hwindowWire])) rfl
  have hchangedControl : changed registers.control = enabled2 registers.control := by
    change measuredStepPlain_indexedQuotientSwapState (registers.quotient window)
      window.start window.stop enabled2 registers.control = enabled2 registers.control
    exact measuredStepPlain_indexedQuotientSwapState_preserves
      (registers.quotient window) enabled2 hqLayout hcontrolNeSign hcontrolNotWork
  have hchangedPhase1 : changed registers.phase1 = state registers.phase1 := by
    change measuredStepPlain_indexedQuotientSwapState (registers.quotient window)
      window.start window.stop enabled2 registers.phase1 = state registers.phase1
    rw [measuredStepPlain_indexedQuotientSwapState_preserves (registers.quotient window)
      enabled2 hqLayout hphase1NeSign hphase1NotWork]
    simp [enabled2, enabled1, measuredStepPlain_xorWireState, upd,
      hlayout.measuredStepPlain_control_ne_phase1.symm]
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hphase1NeControl : registers.phase1 ≠ registers.control :=
    Ne.symm hlayout.measuredStepPlain_control_ne_phase1
  have hphase2NeControl : registers.phase2 ≠ registers.control :=
    Ne.symm hcontrolNePhase2
  have hchangedPhase2 : changed registers.phase2 = state registers.phase2 := by
    change measuredStepPlain_indexedQuotientSwapState (registers.quotient window)
      window.start window.stop enabled2 registers.phase2 = state registers.phase2
    rw [measuredStepPlain_indexedQuotientSwapState_preserves (registers.quotient window)
      enabled2 hqLayout hphase2NeSign hphase2NotWork]
    simp [enabled2, enabled1, measuredStepPlain_xorWireState, upd, hcontrolNePhase2.symm]
  have hfinalControl : disabled1 registers.control = false := by
    change measuredStepPlain_xorWireState registers.phase1 registers.control
      (measuredStepPlain_xorWireState registers.phase2 registers.control changed)
        registers.control = false
    cases hp1 : state registers.phase1 <;> cases hp2 : state registers.phase2 <;>
      simp [measuredStepPlain_xorWireState, upd, hphase1NeControl,
        hphase2NeControl, hchangedControl, hchangedPhase1, hchangedPhase2,
        enabled2, enabled1, hcontrolFalse, hp1, hp2]
  have hfinalSource : Clean registers.sourceScratch disabled1 := by
    intro wire hwire
    have hcontrol : wire ≠ registers.control := by
      intro equality
      subst wire
      exact hlayout.measuredStepPlain_control_not_sourceScratch hwire
    simp [disabled1, disabled2, measuredStepPlain_xorWireState, upd, hcontrol,
      hchangedSource wire hwire]
  have hrun : run (circuit! {
      measuredStepPlain_quotientXorControl registers;
      quotientSwapUnitary (registers.quotient window) window.start window.stop;
      measuredStepPlain_quotientXorControlInverse registers
    }) state = measuredStepPlain_blockD2ForwardState registers window state := by
    simp only [Classical.run_append]
    rw [henabledRun, hchangedRun, hdisabledRun]
    rfl
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      measuredStepPlain_blockD2ForwardState registers window state wire = false := by
    intro wire hrepair
    have hcontrol := hlayout.measuredStepPlain_remainderRepairScratch_ne_control hrepair
    have hnotPayload := hlayout.measuredStepPlain_remainderRepairScratch_not_payload hrepair
    have hsign : wire ≠ registers.sign := by
      intro equality
      exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, equality])
    have hwork : wire ∉ (registers.quotient window).work1 := by
      intro hwindowWire
      apply hnotPayload
      simp [measuredStepPlain_indexedStepPayload,
        measuredStepPlain_windowSlice_mem registers.work1 window hwindowWire]
    calc
      measuredStepPlain_blockD2ForwardState registers window state wire = disabled1 wire := by rfl
      _ = disabled2 wire := measuredStepPlain_xorWireState_preserves _ _ _ hcontrol
      _ = changed wire := measuredStepPlain_xorWireState_preserves _ _ _ hcontrol
      _ = enabled2 wire := measuredStepPlain_indexedQuotientSwapState_preserves
        (registers.quotient window) enabled2 hqLayout hsign hwork
      _ = enabled1 wire := measuredStepPlain_xorWireState_preserves _ _ _ hcontrol
      _ = state wire := measuredStepPlain_xorWireState_preserves _ _ _ hcontrol
      _ = false := hready wire
        (hlayout.measuredStepPlain_remainderRepairScratch_mem_sharedScratch hrepair)
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsourceWire | hrepair
    · exact hfinalControl
    · exact hfinalSource wire hsourceWire
    · exact hrepairFinal wire hrepair

private theorem measuredStepPlain_blockD3Forward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (circuit! {
      measuredStepPlain_phase3LengthControl registers;
      controlledDecrement registers.control registers.lengthQ (measuredStepPlain_lengthCarries registers);
      measuredStepPlain_phase3LengthControl registers
    }) state = measuredStepPlain_blockD3ForwardState registers state ∧
      IndexedStepReady registers
        (run (circuit! {
          measuredStepPlain_phase3LengthControl registers;
          controlledDecrement registers.control registers.lengthQ
            (measuredStepPlain_lengthCarries registers);
          measuredStepPlain_phase3LengthControl registers
        }) state) := by
  have hsource : Clean registers.sourceScratch state := by
    intro wire hwire
    exact hready wire (by
      simp [IndexedStepRegisters.sharedScratch, hwire])
  let enabled := measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 1
    registers.control state
  have henabled := measuredStepPlain_run_computeControl_state [registers.phase1, registers.phase2] 1
    registers.control registers.sourceScratch state hlayout.phase3Length hsource
  have henabledRun : run (measuredStepPlain_phase3LengthControl registers) state = enabled := by
    simpa [measuredStepPlain_phase3LengthControl, enabled] using henabled.1
  have henabledSource : Clean registers.sourceScratch enabled := by
    simpa only [enabled] using henabled.2
  have hcarries : Clean (measuredStepPlain_lengthCarries registers) enabled := by
    intro wire hwire
    exact henabledSource wire (List.mem_of_mem_take hwire)
  let changed := measuredStepPlain_indexedDecrementWordState (enabled registers.control)
    registers.lengthQ enabled
  have hchangedRun : run
      (controlledDecrement registers.control registers.lengthQ
        (measuredStepPlain_lengthCarries registers)) enabled = changed := by
    simpa only [changed] using measuredStepPlain_run_controlledDecrement_indexedState
      registers.control registers.lengthQ (measuredStepPlain_lengthCarries registers) enabled
      hlayout.lengthCarryCapacity hlayout.lengthCarryPhysical hcarries
  have hchangedSource : Clean registers.sourceScratch changed := by
    intro wire hwire
    have hnotLengthQ : wire ∉ registers.lengthQ := by
      intro hlength
      exact (hlayout.measuredStepPlain_aux_not_payload
        (auxWire := wire) (payloadWire := wire)
        (hlayout.measuredStepPlain_sourceScratch_mem_aux hwire)
        (by simp [measuredStepPlain_indexedStepPayload, hlength])) rfl
    change changed wire = false
    rw [show changed wire = enabled wire by
      exact measuredStepPlain_indexedDecrementWordState_preservesOutside _ _ _ hnotLengthQ]
    exact henabledSource wire hwire
  have hcleared := measuredStepPlain_run_computeControl_state [registers.phase1, registers.phase2] 1
    registers.control registers.sourceScratch changed hlayout.phase3Length hchangedSource
  have hclearedRun : run (measuredStepPlain_phase3LengthControl registers) changed =
      measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 1
        registers.control changed := by
    simpa [measuredStepPlain_phase3LengthControl] using hcleared.1
  have hcontrolFalse : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload])
  have hphase1NotQ : registers.phase1 ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.measuredStepPlain_phase1_ne_after (by
      simp [measuredStepPlain_indexedStepAfterPhase1, hmem])) rfl
  have hphase2NotQ : registers.phase2 ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.measuredStepPlain_phase2_ne_after (by
      simp [measuredStepPlain_indexedStepAfterPhase2, hmem])) rfl
  have hcontrolNotQ : registers.control ∉ registers.lengthQ := by
    intro hmem
    exact (hlayout.measuredStepPlain_aux_not_payload
      (auxWire := registers.control) (payloadWire := registers.control)
      hlayout.measuredStepPlain_control_mem_aux (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl
  have henabledControl : enabled registers.control =
      registerMatches [registers.phase1, registers.phase2] 1 state := by
    simp [enabled, measuredStepPlain_matchXorState, hcontrolFalse]
  have hchangedControl : changed registers.control = enabled registers.control := by
    exact measuredStepPlain_indexedDecrementWordState_preservesOutside _ _ _ hcontrolNotQ
  have hpredicate : registerMatches [registers.phase1, registers.phase2] 1 changed =
      registerMatches [registers.phase1, registers.phase2] 1 state := by
    apply measuredStepPlain_registerMatches_congr
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl
    · change measuredStepPlain_indexedDecrementWordState (enabled registers.control)
        registers.lengthQ enabled registers.phase1 = state registers.phase1
      rw [measuredStepPlain_indexedDecrementWordState_preservesOutside _ _ _ hphase1NotQ]
      simp [enabled, measuredStepPlain_matchXorState, upd, hlayout.measuredStepPlain_control_ne_phase1.symm]
    · change measuredStepPlain_indexedDecrementWordState (enabled registers.control)
        registers.lengthQ enabled registers.phase2 = state registers.phase2
      rw [measuredStepPlain_indexedDecrementWordState_preservesOutside _ _ _ hphase2NotQ]
      simp [enabled, measuredStepPlain_matchXorState, upd, hcontrolNePhase2.symm]
  have hfinalControl : measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 1
      registers.control changed registers.control = false := by
    simp [measuredStepPlain_matchXorState, hchangedControl, henabledControl, hpredicate]
  have hrun : run (circuit! {
      measuredStepPlain_phase3LengthControl registers;
      controlledDecrement registers.control registers.lengthQ (measuredStepPlain_lengthCarries registers);
      measuredStepPlain_phase3LengthControl registers
    }) state = measuredStepPlain_blockD3ForwardState registers state := by
    simp only [Classical.run_append]
    rw [henabledRun, hchangedRun, hclearedRun]
    rfl
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      measuredStepPlain_blockD3ForwardState registers state wire = false := by
    intro wire hrepair
    have hcontrol := hlayout.measuredStepPlain_remainderRepairScratch_ne_control hrepair
    have hnotPayload := hlayout.measuredStepPlain_remainderRepairScratch_not_payload hrepair
    have hnotLengthQ : wire ∉ registers.lengthQ := by
      intro hmem
      exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, hmem])
    calc
      measuredStepPlain_blockD3ForwardState registers state wire = changed wire := by
        change measuredStepPlain_matchXorState [registers.phase1, registers.phase2] 1
          registers.control changed wire = changed wire
        exact measuredStepPlain_matchXorState_preserves _ _ _ _ hcontrol
      _ = enabled wire := measuredStepPlain_indexedDecrementWordState_preservesOutside _ _ _
        hnotLengthQ
      _ = state wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hcontrol
      _ = false := hready wire
        (hlayout.measuredStepPlain_remainderRepairScratch_mem_sharedScratch hrepair)
  constructor
  · exact hrun
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsourceWire | hrepair
    · exact hfinalControl
    · exact hcleared.2 wire hsourceWire
    · exact hrepairFinal wire hrepair

private theorem measuredStepPlain_blockDForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap)
    (hready : IndexedStepReady registers state) :
    run (blockDForward registers window) state =
        measuredStepPlain_blockDForwardState registers window state ∧
      IndexedStepReady registers (run (blockDForward registers window) state) := by
  have hfirst := measuredStepPlain_blockD1Forward_correct registers n T state hlayout hready
  have hfirstReady : IndexedStepReady registers
      (measuredStepPlain_blockD1ForwardState registers state) := by
    rw [← hfirst.1]
    exact hfirst.2
  have hsecond := measuredStepPlain_blockD2Forward_correct registers n T window
    (measuredStepPlain_blockD1ForwardState registers state) hlayout hwindow hfirstReady
  have hsecondReady : IndexedStepReady registers
      (measuredStepPlain_blockD2ForwardState registers window
        (measuredStepPlain_blockD1ForwardState registers state)) := by
    rw [← hsecond.1]
    exact hsecond.2
  have hthird := measuredStepPlain_blockD3Forward_correct registers n T
    (measuredStepPlain_blockD2ForwardState registers window
      (measuredStepPlain_blockD1ForwardState registers state)) hlayout hsecondReady
  have hrun : run (blockDForward registers window) state =
      measuredStepPlain_blockDForwardState registers window state := by
    calc
      run (blockDForward registers window) state =
          run (circuit! {
            measuredStepPlain_phase3LengthControl registers;
            controlledDecrement registers.control registers.lengthQ
              (measuredStepPlain_lengthCarries registers);
            measuredStepPlain_phase3LengthControl registers
          })
            (run (circuit! {
              measuredStepPlain_quotientXorControl registers;
              quotientSwapUnitary (registers.quotient window)
                window.start window.stop;
              measuredStepPlain_quotientXorControlInverse registers
            })
              (run (circuit! {
                measuredStepPlain_phase2LengthControl registers;
                controlledIncrement registers.control registers.lengthQ
                  (measuredStepPlain_lengthCarries registers);
                measuredStepPlain_phase2LengthControl registers
              }) state)) := by
                simp [blockDForward, measuredStepPlain_view_blockD1Forward, measuredStepPlain_source_blockD1Forward, measuredStepPlain_view_blockD2Forward, measuredStepPlain_source_blockD2Forward, measuredStepPlain_view_blockD3Forward, measuredStepPlain_source_blockD3Forward, Classical.run_append]
      _ = measuredStepPlain_blockDForwardState registers window state := by
        rw [hfirst.1, hsecond.1, hthird.1]
        rfl
  constructor
  · exact hrun
  · rw [hrun]
    change IndexedStepReady registers
      (measuredStepPlain_blockD3ForwardState registers
        (measuredStepPlain_blockD2ForwardState registers window
          (measuredStepPlain_blockD1ForwardState registers state)))
    rw [← hthird.1]
    exact hthird.2

private theorem measuredStepPlain_run_tBoundaryPrepareState
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    run (prepareLatestPaperTBoundary registers.tBoundary n) state =
        measuredStepPlain_tBoundaryPrepareState registers n state ∧
      Clean registers.blockScratch
        (run (prepareLatestPaperTBoundary registers.tBoundary n) state) := by
  have hlocalReady : TBoundaryReady registers.tBoundary state := by
    intro wire hwire
    exact hclean wire (hlayout.measuredStepPlain_tBoundary_usedScratch_sub_block wire hwire)
  have hcorrect := prepareLatestPaperTBoundary_correct registers.tBoundary n state
    hlayout.tBoundary hlocalReady
  dsimp only at hcorrect
  let words := prepareLatestPaperTBoundaryWords (state registers.phase2)
    (wireValues registers.lengthT state)
    (wireValues registers.lengthRPrime state)
    (wireValues registers.tBoundary.lengthSLow state) n
  have hrun : run (prepareLatestPaperTBoundary registers.tBoundary n) state =
      measuredStepPlain_indexedWriteWireValues (registers.lengthT ++ registers.lengthRPrime)
        (words.1 ++ words.2) state := by
    apply measuredStepPlain_indexedState_eq_writeWireValues
    · exact hlayout.measuredStepPlain_tBoundary_words_nodup
    · have hlength := congrArg
          (fun pair : List Bool × List Bool => pair.1.length + pair.2.length)
          hcorrect.1
      simpa [words, wireValues] using hlength.symm
    · have hvalues := congrArg
          (fun pair : List Bool × List Bool => pair.1 ++ pair.2) hcorrect.1
      simpa [words, wireValues] using hvalues
    · intro wire hwire
      simp only [List.mem_append, not_or] at hwire
      exact hcorrect.2.2 wire hwire.1 hwire.2
  constructor
  · simpa only [measuredStepPlain_tBoundaryPrepareState, words] using hrun
  · intro wire hwire
    have haux := hlayout.measuredStepPlain_blockScratch_mem_aux hwire
    have ht : wire ∉ registers.lengthT := by
      intro hlength
      exact (hlayout.measuredStepPlain_aux_not_payload haux
        (by simp [measuredStepPlain_indexedStepPayload, hlength])) rfl
    have hrp : wire ∉ registers.lengthRPrime := by
      intro hlength
      exact (hlayout.measuredStepPlain_aux_not_payload haux
        (by simp [measuredStepPlain_indexedStepPayload, hlength])) rfl
    rw [hcorrect.2.2 wire ht hrp]
    exact hclean wire hwire

private theorem measuredStepPlain_run_tBoundaryRestoreState
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    run (restoreLatestPaperTBoundary registers.tBoundary n) state =
        measuredStepPlain_tBoundaryRestoreState registers n state ∧
      Clean registers.blockScratch
        (run (restoreLatestPaperTBoundary registers.tBoundary n) state) := by
  have hlocalReady : TBoundaryReady registers.tBoundary state := by
    intro wire hwire
    exact hclean wire (hlayout.measuredStepPlain_tBoundary_usedScratch_sub_block wire hwire)
  have hcorrect := restoreLatestPaperTBoundary_correct registers.tBoundary n state
    hlayout.tBoundary hlocalReady
  dsimp only at hcorrect
  let words := restoreLatestPaperTBoundaryWords (state registers.phase2)
    (wireValues registers.lengthT state)
    (wireValues registers.lengthRPrime state)
    (wireValues registers.tBoundary.lengthSLow state) n
  have hrun : run (restoreLatestPaperTBoundary registers.tBoundary n) state =
      measuredStepPlain_indexedWriteWireValues (registers.lengthT ++ registers.lengthRPrime)
        (words.1 ++ words.2) state := by
    apply measuredStepPlain_indexedState_eq_writeWireValues
    · exact hlayout.measuredStepPlain_tBoundary_words_nodup
    · have hlength := congrArg
          (fun pair : List Bool × List Bool => pair.1.length + pair.2.length)
          hcorrect.1
      simpa [words, wireValues] using hlength.symm
    · have hvalues := congrArg
          (fun pair : List Bool × List Bool => pair.1 ++ pair.2) hcorrect.1
      simpa [words, wireValues] using hvalues
    · intro wire hwire
      simp only [List.mem_append, not_or] at hwire
      exact hcorrect.2.2 wire hwire.1 hwire.2
  constructor
  · simpa only [measuredStepPlain_tBoundaryRestoreState, words] using hrun
  · intro wire hwire
    have haux := hlayout.measuredStepPlain_blockScratch_mem_aux hwire
    have ht : wire ∉ registers.lengthT := by
      intro hlength
      exact (hlayout.measuredStepPlain_aux_not_payload haux
        (by simp [measuredStepPlain_indexedStepPayload, hlength])) rfl
    have hrp : wire ∉ registers.lengthRPrime := by
      intro hlength
      exact (hlayout.measuredStepPlain_aux_not_payload haux
        (by simp [measuredStepPlain_indexedStepPayload, hlength])) rfl
    rw [hcorrect.2.2 wire ht hrp]
    exact hclean wire hwire

private theorem measuredStepPlain_run_coefficientPrefixState_from_blockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hclean : Clean registers.blockScratch state) :
    let circuit := coefficientPrefixUnitary (registers.coefficient window)
      window.start window.stop mode signUpdate .work2
    run circuit state = coefficientPrefixState (registers.coefficient window)
        window.start window.stop mode signUpdate .work2 state ∧
      Clean registers.blockScratch (run circuit state) ∧
      run circuit state registers.control = state registers.control ∧
      (signUpdate = false →
        run circuit state registers.sign = state registers.sign) := by
  have hcoefficientLayout : CoefficientPrefixLayout
      (registers.coefficient window) window.start window.stop := by
    subst window
    exact hlayout.coefficient
  have hlocalReady : CoefficientPrefixReady
      (registers.coefficient window) state := by
    intro wire hwire
    exact hclean wire (hlayout.measuredStepPlain_coefficient_scratch_sub_block window wire hwire)
  let circuit := coefficientPrefixUnitary (registers.coefficient window)
    window.start window.stop mode signUpdate .work2
  have hrun : run circuit state = coefficientPrefixState
      (registers.coefficient window) window.start window.stop mode signUpdate
        .work2 state := by
    simpa only [circuit] using run_coefficientPrefixUnitary_state
      (registers.coefficient window) mode signUpdate .work2 state
      hcoefficientLayout hlocalReady
  have hlocalAfter : CoefficientPrefixReady (registers.coefficient window)
      (run circuit state) := by
    simpa only [circuit] using coefficientPrefixUnitary_clean
      (registers.coefficient window) mode signUpdate .work2 state
      hcoefficientLayout hlocalReady
  have hblockAfter : Clean registers.blockScratch (run circuit state) := by
    intro wire hwire
    by_cases hlocal : wire ∈ (registers.coefficient window).scratch
    · exact hlocalAfter wire hlocal
    · rw [show run circuit state wire = state wire by
        simpa only [circuit] using coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) mode signUpdate .work2 state
          hcoefficientLayout
          (hlayout.measuredStepPlain_blockScratch_outside_coefficient window hwire hlocal)]
      exact hclean wire hwire
  have hcontrol : run circuit state registers.control = state registers.control := by
    simpa only [circuit] using coefficientPrefixUnitary_preserves_control
      (registers.coefficient window) mode signUpdate .work2 state
      hcoefficientLayout
  refine ⟨hrun, hblockAfter, hcontrol, ?_⟩
  intro hfalse
  subst signUpdate
  simpa only [circuit] using coefficientPrefixUnitary_preserves_sign_of_false
    (registers.coefficient window) mode .work2 state hcoefficientLayout

private theorem measuredStepPlain_blockEForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hready : IndexedStepReady registers state) :
    run (blockEForward registers n window) state =
        measuredStepPlain_blockEForwardState registers n window state ∧
      IndexedStepReady registers
        (run (blockEForward registers n window) state) := by
  have hcontrolFalse : state registers.control = false :=
    hready registers.control (by simp [IndexedStepRegisters.sharedScratch])
  have hterminalSource : registers.terminal ∈ registers.sourceScratch := by
    rw [← hlayout.measuredStepPlain_scratch_view]
    simp
  have hterminalFalse : state registers.terminal = false :=
    hready registers.terminal (by
      simp [IndexedStepRegisters.sharedScratch, hterminalSource])
  have hblock : Clean registers.blockScratch state := by
    intro wire hwire
    exact hready wire (hlayout.measuredStepPlain_blockScratch_mem_sharedScratch hwire)
  have hterminalAux := hlayout.measuredStepPlain_sourceScratch_mem_aux hterminalSource
  have hcontrolNePhase2 : registers.control ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by
      simp [measuredStepPlain_indexedStepPayload])
  have hcontrolNeSign : registers.control ≠ registers.sign :=
    hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux (by
      simp [measuredStepPlain_indexedStepPayload])
  have hterminalNePhase1 : registers.terminal ≠ registers.phase1 :=
    hlayout.measuredStepPlain_aux_not_payload hterminalAux (by simp [measuredStepPlain_indexedStepPayload])
  have hterminalNePhase2 : registers.terminal ≠ registers.phase2 :=
    hlayout.measuredStepPlain_aux_not_payload hterminalAux (by simp [measuredStepPlain_indexedStepPayload])
  have hterminalNeSign : registers.terminal ≠ registers.sign :=
    hlayout.measuredStepPlain_aux_not_payload hterminalAux (by simp [measuredStepPlain_indexedStepPayload])
  have hfixedNotWords : ∀ wire ∈
      [registers.phase1, registers.phase2, registers.sign,
        registers.control, registers.terminal],
      wire ∉ registers.lengthT ∧ wire ∉ registers.lengthRPrime := by
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl | rfl | rfl | rfl
    · constructor
      · intro hmem
        exact (hlayout.measuredStepPlain_phase1_ne_after (by
          simp [measuredStepPlain_indexedStepAfterPhase1, hmem])) rfl
      · intro hmem
        exact (hlayout.measuredStepPlain_phase1_ne_after (by
          simp [measuredStepPlain_indexedStepAfterPhase1, hmem])) rfl
    · constructor
      · intro hmem
        exact (hlayout.measuredStepPlain_phase2_ne_after (by
          simp [measuredStepPlain_indexedStepAfterPhase2, hmem])) rfl
      · intro hmem
        exact (hlayout.measuredStepPlain_phase2_ne_after (by
          simp [measuredStepPlain_indexedStepAfterPhase2, hmem])) rfl
    · constructor
      · intro hmem
        exact (hlayout.measuredStepPlain_sign_ne_after (by
          simp [measuredStepPlain_indexedStepAfterSign, hmem])) rfl
      · intro hmem
        exact (hlayout.measuredStepPlain_sign_ne_after (by
          simp [measuredStepPlain_indexedStepAfterSign, hmem])) rfl
    · constructor
      · intro hmem
        exact (hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux
          (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl
      · intro hmem
        exact (hlayout.measuredStepPlain_aux_not_payload hlayout.measuredStepPlain_control_mem_aux
          (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl
    · constructor
      · intro hmem
        exact (hlayout.measuredStepPlain_aux_not_payload hterminalAux
          (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl
      · intro hmem
        exact (hlayout.measuredStepPlain_aux_not_payload hterminalAux
          (by simp [measuredStepPlain_indexedStepPayload, hmem])) rfl
  have hcoefficientLayout : CoefficientPrefixLayout
      (registers.coefficient window) window.start window.stop := by
    subst window
    exact hlayout.coefficient
  let temporary1 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  have htemporary1 := measuredStepPlain_run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch state hlayout.coefficientTemporary hblock
  have htemporary1Run : run (measuredStepPlain_coefficientTemporaryControl registers) state =
      temporary1 := by
    simpa [measuredStepPlain_coefficientTemporaryControl, temporary1] using htemporary1.1
  have htemporary1Block : Clean registers.blockScratch temporary1 := by
    simpa only [temporary1] using htemporary1.2
  let subEnabled := measuredStepPlain_matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary1
  have hsubEnabled := measuredStepPlain_run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary1 hlayout.coefficientSub htemporary1Block
  have hsubEnabledRun : run (measuredStepPlain_coefficientSubControl registers) temporary1 =
      subEnabled := by
    simpa [measuredStepPlain_coefficientSubControl, subEnabled] using hsubEnabled.1
  have hsubEnabledBlock : Clean registers.blockScratch subEnabled := by
    simpa only [subEnabled] using hsubEnabled.2
  let temporaryCleared1 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subEnabled
  have htemporaryCleared1 := measuredStepPlain_run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subEnabled hlayout.coefficientTemporary hsubEnabledBlock
  have htemporaryCleared1Run :
      run (measuredStepPlain_coefficientTemporaryControl registers) subEnabled =
        temporaryCleared1 := by
    simpa [measuredStepPlain_coefficientTemporaryControl, temporaryCleared1] using
      htemporaryCleared1.1
  have htemporaryCleared1Block : Clean registers.blockScratch
      temporaryCleared1 := by
    simpa only [temporaryCleared1] using htemporaryCleared1.2
  let prepared := measuredStepPlain_tBoundaryPrepareState registers n temporaryCleared1
  have hprepared := measuredStepPlain_run_tBoundaryPrepareState registers n T temporaryCleared1
    hlayout htemporaryCleared1Block
  have hpreparedBlock : Clean registers.blockScratch prepared := by
    simpa only [prepared, hprepared.1] using hprepared.2
  let subtracted := coefficientPrefixState (registers.coefficient window)
    window.start window.stop .sub false .work2 prepared
  have hsubtracted := measuredStepPlain_run_coefficientPrefixState_from_blockScratch registers n T
    window .sub false prepared hlayout hwindow hpreparedBlock
  dsimp only at hsubtracted
  have hsubtractedBlock : Clean registers.blockScratch subtracted := by
    simpa only [subtracted, hsubtracted.1] using hsubtracted.2.1
  let temporary2 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subtracted
  have htemporary2 := measuredStepPlain_run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subtracted hlayout.coefficientTemporary hsubtractedBlock
  have htemporary2Run : run (measuredStepPlain_coefficientTemporaryControl registers) subtracted =
      temporary2 := by
    simpa [measuredStepPlain_coefficientTemporaryControl, temporary2] using htemporary2.1
  have htemporary2Block : Clean registers.blockScratch temporary2 := by
    simpa only [temporary2] using htemporary2.2
  let subCleared := measuredStepPlain_matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary2
  have hsubCleared := measuredStepPlain_run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary2 hlayout.coefficientSub htemporary2Block
  have hsubClearedRun : run (measuredStepPlain_coefficientSubControl registers) temporary2 =
      subCleared := by
    simpa [measuredStepPlain_coefficientSubControl, subCleared] using hsubCleared.1
  have hsubClearedBlock : Clean registers.blockScratch subCleared := by
    simpa only [subCleared] using hsubCleared.2
  let temporaryCleared2 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subCleared
  have htemporaryCleared2 := measuredStepPlain_run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subCleared hlayout.coefficientTemporary hsubClearedBlock
  have htemporaryCleared2Run :
      run (measuredStepPlain_coefficientTemporaryControl registers) subCleared =
        temporaryCleared2 := by
    simpa [measuredStepPlain_coefficientTemporaryControl, temporaryCleared2] using
      htemporaryCleared2.1
  have htemporaryCleared2Block : Clean registers.blockScratch
      temporaryCleared2 := by
    simpa only [temporaryCleared2] using htemporaryCleared2.2
  let signChanged := measuredStepPlain_xorWireState registers.phase1 registers.sign temporaryCleared2
  have hsignChangedRun : run ([.CX registers.phase1 registers.sign] : Circuit)
      temporaryCleared2 = signChanged := by
    simpa only [signChanged] using
      measuredStepPlain_run_xorWireState registers.phase1 registers.sign temporaryCleared2
  have hsignChangedBlock : Clean registers.blockScratch signChanged := by
    simpa [signChanged, measuredStepPlain_xorWireState] using
      measuredStepPlain_clean_upd_not_mem htemporaryCleared2Block
        (by
          intro hmem
          exact (hlayout.measuredStepPlain_sign_ne_after (by
            simp [measuredStepPlain_indexedStepAfterSign,
              hlayout.measuredStepPlain_blockScratch_mem_aux hmem])) rfl)
  let addEnabled := measuredStepPlain_matchXorState [registers.phase1] 1 registers.control signChanged
  have haddEnabled := measuredStepPlain_run_computeControl_state [registers.phase1] 1
    registers.control registers.blockScratch signChanged hlayout.coefficientAdd
      hsignChangedBlock
  have haddEnabledRun : run (measuredStepPlain_coefficientAddControl registers) signChanged =
      addEnabled := by
    simpa [measuredStepPlain_coefficientAddControl, addEnabled] using haddEnabled.1
  have haddEnabledBlock : Clean registers.blockScratch addEnabled := by
    simpa only [addEnabled] using haddEnabled.2
  let added := coefficientPrefixState (registers.coefficient window)
    window.start window.stop .add true .work2 addEnabled
  have hadded := measuredStepPlain_run_coefficientPrefixState_from_blockScratch registers n T window
    .add true addEnabled hlayout hwindow haddEnabledBlock
  dsimp only at hadded
  have haddedBlock : Clean registers.blockScratch added := by
    simpa only [added, hadded.1] using hadded.2.1
  let addCleared := measuredStepPlain_matchXorState [registers.phase1] 1 registers.control added
  have haddCleared := measuredStepPlain_run_computeControl_state [registers.phase1] 1
    registers.control registers.blockScratch added hlayout.coefficientAdd haddedBlock
  have haddClearedRun : run (measuredStepPlain_coefficientAddControl registers) added =
      addCleared := by
    simpa [measuredStepPlain_coefficientAddControl, addCleared] using haddCleared.1
  have haddClearedBlock : Clean registers.blockScratch addCleared := by
    simpa only [addCleared] using haddCleared.2
  let restored := measuredStepPlain_tBoundaryRestoreState registers n addCleared
  have hrestored := measuredStepPlain_run_tBoundaryRestoreState registers n T addCleared hlayout
    haddClearedBlock
  have hrun : run (blockEForward registers n window) state = restored := by
    simp only [blockEForward, measuredStepPlain_view_blockEFinishForward, measuredStepPlain_source_blockEFinishForward, measuredStepPlain_view_blockESubtractForward, measuredStepPlain_source_blockESubtractForward, blockEPrepareForward, measuredStepPlain_view_coefficientSubtractControl, measuredStepPlain_source_coefficientSubtractControl, Classical.run_append]
    rw [htemporary1Run, hsubEnabledRun, htemporaryCleared1Run,
      hprepared.1, hsubtracted.1, htemporary2Run, hsubClearedRun,
      htemporaryCleared2Run, hsignChangedRun, haddEnabledRun,
      hadded.1, haddClearedRun, hrestored.1]
  have hstate : restored = measuredStepPlain_blockEForwardState registers n window state := by
    rfl
  have htemporary1Control : temporary1 registers.control = false := by
    calc
      temporary1 registers.control = state registers.control := by
        simpa only [temporary1] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal state hlayout.measuredStepPlain_control_ne_terminal
      _ = false := hcontrolFalse
  have htemporary1Terminal : temporary1 registers.terminal =
      registerMatches [registers.phase2, registers.sign] 2 state := by
    simp [temporary1, measuredStepPlain_matchXorState, hterminalFalse]
  have hsubEnabledTerminal : subEnabled registers.terminal =
      temporary1 registers.terminal :=
    measuredStepPlain_matchXorState_preserves _ _ _ _ (Ne.symm hlayout.measuredStepPlain_control_ne_terminal)
  have hsubEnabledControl : subEnabled registers.control =
      registerMatches [registers.phase1, registers.terminal] 1 temporary1 := by
    simp [subEnabled, measuredStepPlain_matchXorState, htemporary1Control]
  have hsubEnabledControls : ∀ wire ∈ [registers.phase2, registers.sign],
      subEnabled wire = state wire := by
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    rcases hwire with rfl | rfl
    · calc
        subEnabled registers.phase2 = temporary1 registers.phase2 := by
          simpa only [subEnabled] using
            measuredStepPlain_matchXorState_preserves [registers.phase1, registers.terminal] 1
              registers.control temporary1 (Ne.symm hcontrolNePhase2)
        _ = state registers.phase2 := by
          simpa only [temporary1] using
            measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
              registers.terminal state (Ne.symm hterminalNePhase2)
    · calc
        subEnabled registers.sign = temporary1 registers.sign := by
          simpa only [subEnabled] using
            measuredStepPlain_matchXorState_preserves [registers.phase1, registers.terminal] 1
              registers.control temporary1 (Ne.symm hcontrolNeSign)
        _ = state registers.sign := by
          simpa only [temporary1] using
            measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
              registers.terminal state (Ne.symm hterminalNeSign)
  have htemporaryCleared1Terminal :
      temporaryCleared1 registers.terminal = false := by
    apply measuredStepPlain_matchXorState_clears [registers.phase2, registers.sign] 2
      registers.terminal state subEnabled
    · exact hsubEnabledTerminal.trans htemporary1Terminal
    · exact hsubEnabledControls
  have htemporaryCleared1Control :
      temporaryCleared1 registers.control = subEnabled registers.control := by
    simpa only [temporaryCleared1] using
      measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
        registers.terminal subEnabled hlayout.measuredStepPlain_control_ne_terminal
  have htemporaryCleared1Phase1 :
      temporaryCleared1 registers.phase1 = state registers.phase1 := by
    calc
      temporaryCleared1 registers.phase1 = subEnabled registers.phase1 := by
        simpa only [temporaryCleared1] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subEnabled (Ne.symm hterminalNePhase1)
      _ = temporary1 registers.phase1 := by
        simpa only [subEnabled] using
          measuredStepPlain_matchXorState_preserves [registers.phase1, registers.terminal] 1
            registers.control temporary1 (Ne.symm hlayout.measuredStepPlain_control_ne_phase1)
      _ = state registers.phase1 := by
        simpa only [temporary1] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal state (Ne.symm hterminalNePhase1)
  have htemporaryCleared1Phase2 :
      temporaryCleared1 registers.phase2 = state registers.phase2 := by
    calc
      temporaryCleared1 registers.phase2 = subEnabled registers.phase2 := by
        simpa only [temporaryCleared1] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subEnabled (Ne.symm hterminalNePhase2)
      _ = state registers.phase2 := hsubEnabledControls _ (by simp)
  have htemporaryCleared1Sign :
      temporaryCleared1 registers.sign = state registers.sign := by
    calc
      temporaryCleared1 registers.sign = subEnabled registers.sign := by
        simpa only [temporaryCleared1] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subEnabled (Ne.symm hterminalNeSign)
      _ = state registers.sign := hsubEnabledControls _ (by simp)
  have hpreparedFixed : ∀ wire ∈
      [registers.phase1, registers.phase2, registers.sign,
        registers.control, registers.terminal],
      prepared wire = temporaryCleared1 wire := by
    intro wire hwire
    simpa only [prepared] using
      measuredStepPlain_tBoundaryPrepareState_preservesOutside registers n temporaryCleared1
        (hfixedNotWords wire hwire).1 (hfixedNotWords wire hwire).2
  have hsubtractedPhase1 : subtracted registers.phase1 = state registers.phase1 := by
    calc
      subtracted registers.phase1 =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.phase1 := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.phase1
      _ = prepared registers.phase1 := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .sub false .work2 prepared
            hcoefficientLayout (hlayout.measuredStepPlain_phase1_not_coefficient window)
      _ = temporaryCleared1 registers.phase1 := hpreparedFixed _ (by simp)
      _ = state registers.phase1 := htemporaryCleared1Phase1
  have hsubtractedPhase2 : subtracted registers.phase2 = state registers.phase2 := by
    calc
      subtracted registers.phase2 =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.phase2 := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.phase2
      _ = prepared registers.phase2 := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .sub false .work2 prepared
            hcoefficientLayout (hlayout.measuredStepPlain_phase2_not_coefficient window)
      _ = temporaryCleared1 registers.phase2 := hpreparedFixed _ (by simp)
      _ = state registers.phase2 := htemporaryCleared1Phase2
  have hsubtractedTerminal : subtracted registers.terminal = false := by
    calc
      subtracted registers.terminal =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.terminal := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.terminal
      _ = prepared registers.terminal := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .sub false .work2 prepared
            hcoefficientLayout (hlayout.measuredStepPlain_terminal_not_coefficient window)
      _ = temporaryCleared1 registers.terminal := hpreparedFixed _ (by simp)
      _ = false := htemporaryCleared1Terminal
  have hsubtractedControl : subtracted registers.control =
      subEnabled registers.control := by
    calc
      subtracted registers.control =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.control := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.control
      _ = prepared registers.control := hsubtracted.2.2.1
      _ = temporaryCleared1 registers.control := hpreparedFixed _ (by simp)
      _ = subEnabled registers.control := htemporaryCleared1Control
  have hsubtractedSign : subtracted registers.sign = state registers.sign := by
    calc
      subtracted registers.sign =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .sub false .work2) prepared
              registers.sign := by
        simpa only [subtracted] using congrFun hsubtracted.1.symm registers.sign
      _ = prepared registers.sign := hsubtracted.2.2.2 rfl
      _ = temporaryCleared1 registers.sign := hpreparedFixed _ (by simp)
      _ = state registers.sign := htemporaryCleared1Sign
  have htemporary2Control : temporary2 registers.control =
      subEnabled registers.control := by
    calc
      temporary2 registers.control = subtracted registers.control := by
        simpa only [temporary2] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subtracted hlayout.measuredStepPlain_control_ne_terminal
      _ = subEnabled registers.control := hsubtractedControl
  have htemporary2Phase1 : temporary2 registers.phase1 =
      temporary1 registers.phase1 := by
    calc
      temporary2 registers.phase1 = subtracted registers.phase1 := by
        simpa only [temporary2] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subtracted (Ne.symm hterminalNePhase1)
      _ = state registers.phase1 := hsubtractedPhase1
      _ = temporary1 registers.phase1 := by
        symm
        simpa only [temporary1] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal state (Ne.symm hterminalNePhase1)
  have htemporary2Terminal : temporary2 registers.terminal =
      temporary1 registers.terminal := by
    have hpredicate : registerMatches [registers.phase2, registers.sign] 2
        subtracted = registerMatches [registers.phase2, registers.sign] 2 state := by
      apply measuredStepPlain_registerMatches_congr
      intro wire hwire
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with rfl | rfl
      · exact hsubtractedPhase2
      · exact hsubtractedSign
    simp [temporary2, measuredStepPlain_matchXorState, hsubtractedTerminal, hpredicate,
      htemporary1Terminal]
  have hsubClearedControl : subCleared registers.control = false := by
    apply measuredStepPlain_matchXorState_clears [registers.phase1, registers.terminal] 1
      registers.control temporary1 temporary2
    · exact htemporary2Control.trans hsubEnabledControl
    · intro wire hwire
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with rfl | rfl
      · exact htemporary2Phase1
      · exact htemporary2Terminal
  have hsubClearedTerminal : subCleared registers.terminal =
      temporary2 registers.terminal := by
    simpa only [subCleared] using
      measuredStepPlain_matchXorState_preserves [registers.phase1, registers.terminal] 1
        registers.control temporary2 (Ne.symm hlayout.measuredStepPlain_control_ne_terminal)
  have hsubClearedPhase2 : subCleared registers.phase2 =
      subtracted registers.phase2 := by
    calc
      subCleared registers.phase2 = temporary2 registers.phase2 := by
        simpa only [subCleared] using
          measuredStepPlain_matchXorState_preserves [registers.phase1, registers.terminal] 1
            registers.control temporary2 (Ne.symm hcontrolNePhase2)
      _ = subtracted registers.phase2 := by
        simpa only [temporary2] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subtracted (Ne.symm hterminalNePhase2)
  have hsubClearedSign : subCleared registers.sign = subtracted registers.sign := by
    calc
      subCleared registers.sign = temporary2 registers.sign := by
        simpa only [subCleared] using
          measuredStepPlain_matchXorState_preserves [registers.phase1, registers.terminal] 1
            registers.control temporary2 (Ne.symm hcontrolNeSign)
      _ = subtracted registers.sign := by
        simpa only [temporary2] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subtracted (Ne.symm hterminalNeSign)
  have htemporaryCleared2Terminal :
      temporaryCleared2 registers.terminal = false := by
    apply measuredStepPlain_matchXorState_clears [registers.phase2, registers.sign] 2
      registers.terminal subtracted subCleared
    · calc
        subCleared registers.terminal = temporary2 registers.terminal :=
          hsubClearedTerminal
        _ = temporary1 registers.terminal := htemporary2Terminal
        _ = registerMatches [registers.phase2, registers.sign] 2 state :=
          htemporary1Terminal
        _ = registerMatches [registers.phase2, registers.sign] 2 subtracted := by
          symm
          apply measuredStepPlain_registerMatches_congr
          intro wire hwire
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
          rcases hwire with rfl | rfl
          · exact hsubtractedPhase2
          · exact hsubtractedSign
    · intro wire hwire
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
      rcases hwire with rfl | rfl
      · exact hsubClearedPhase2
      · exact hsubClearedSign
  have htemporaryCleared2Control : temporaryCleared2 registers.control = false := by
    calc
      temporaryCleared2 registers.control = subCleared registers.control := by
        simpa only [temporaryCleared2] using
          measuredStepPlain_matchXorState_preserves [registers.phase2, registers.sign] 2
            registers.terminal subCleared hlayout.measuredStepPlain_control_ne_terminal
      _ = false := hsubClearedControl
  have hsignChangedControl : signChanged registers.control = false := by
    simpa [signChanged, measuredStepPlain_xorWireState, upd, hcontrolNeSign] using
      htemporaryCleared2Control
  have hsignChangedTerminal : signChanged registers.terminal = false := by
    simpa [signChanged, measuredStepPlain_xorWireState, upd, hterminalNeSign] using
      htemporaryCleared2Terminal
  have haddEnabledControl : addEnabled registers.control =
      registerMatches [registers.phase1] 1 signChanged := by
    simp [addEnabled, measuredStepPlain_matchXorState, hsignChangedControl]
  have haddedControl : added registers.control =
      registerMatches [registers.phase1] 1 signChanged := by
    calc
      added registers.control =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .add true .work2) addEnabled
              registers.control := by
        simpa only [added] using congrFun hadded.1.symm registers.control
      _ = addEnabled registers.control := hadded.2.2.1
      _ = _ := haddEnabledControl
  have haddedPhase1 : added registers.phase1 = signChanged registers.phase1 := by
    calc
      added registers.phase1 =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .add true .work2) addEnabled
              registers.phase1 := by
        simpa only [added] using congrFun hadded.1.symm registers.phase1
      _ = addEnabled registers.phase1 := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .add true .work2 addEnabled
            hcoefficientLayout (hlayout.measuredStepPlain_phase1_not_coefficient window)
      _ = signChanged registers.phase1 := by
        simpa only [addEnabled] using
          measuredStepPlain_matchXorState_preserves [registers.phase1] 1 registers.control
            signChanged (Ne.symm hlayout.measuredStepPlain_control_ne_phase1)
  have haddClearedControl : addCleared registers.control = false := by
    apply measuredStepPlain_matchXorState_clears [registers.phase1] 1 registers.control
      signChanged added haddedControl
    intro wire hwire
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
    subst wire
    exact haddedPhase1
  have haddedTerminal : added registers.terminal = false := by
    calc
      added registers.terminal =
          run (coefficientPrefixUnitary (registers.coefficient window)
            window.start window.stop .add true .work2) addEnabled
              registers.terminal := by
        simpa only [added] using congrFun hadded.1.symm registers.terminal
      _ = addEnabled registers.terminal := by
        exact coefficientPrefixUnitary_preservesOutside
          (registers.coefficient window) .add true .work2 addEnabled
            hcoefficientLayout (hlayout.measuredStepPlain_terminal_not_coefficient window)
      _ = signChanged registers.terminal := by
        simpa only [addEnabled] using
          measuredStepPlain_matchXorState_preserves [registers.phase1] 1 registers.control
            signChanged (Ne.symm hlayout.measuredStepPlain_control_ne_terminal)
      _ = false := hsignChangedTerminal
  have haddClearedTerminal : addCleared registers.terminal = false := by
    calc
      addCleared registers.terminal = added registers.terminal := by
        simpa only [addCleared] using
          measuredStepPlain_matchXorState_preserves [registers.phase1] 1 registers.control added
            (Ne.symm hlayout.measuredStepPlain_control_ne_terminal)
      _ = false := haddedTerminal
  have hrestoredControl : restored registers.control = false := by
    calc
      restored registers.control = addCleared registers.control := by
        simpa only [restored] using
          measuredStepPlain_tBoundaryRestoreState_preservesOutside registers n addCleared
            (hfixedNotWords registers.control (by simp)).1
            (hfixedNotWords registers.control (by simp)).2
      _ = false := haddClearedControl
  have hrestoredTerminal : restored registers.terminal = false := by
    calc
      restored registers.terminal = addCleared registers.terminal := by
        simpa only [restored] using
          measuredStepPlain_tBoundaryRestoreState_preservesOutside registers n addCleared
            (hfixedNotWords registers.terminal (by simp)).1
            (hfixedNotWords registers.terminal (by simp)).2
      _ = false := haddClearedTerminal
  have hrepairFinal : ∀ wire ∈ registers.remainderRepairScratch,
      restored wire = false := by
    intro wire hrepair
    have hnotPayload := hlayout.measuredStepPlain_remainderRepairScratch_not_payload hrepair
    have hnotSource := hlayout.measuredStepPlain_remainderRepairScratch_not_sourceScratch hrepair
    have hcontrol := hlayout.measuredStepPlain_remainderRepairScratch_ne_control hrepair
    have hterminal : wire ≠ registers.terminal := by
      intro equality
      apply hnotSource
      rw [equality, ← hlayout.measuredStepPlain_scratch_view]
      simp
    have hsign : wire ≠ registers.sign := by
      intro equality
      exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, equality])
    have hlengthT : wire ∉ registers.lengthT := by
      intro hmem
      exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, hmem])
    have hlengthRPrime : wire ∉ registers.lengthRPrime := by
      intro hmem
      exact hnotPayload (by simp [measuredStepPlain_indexedStepPayload, hmem])
    have hcoefficient :=
      hlayout.measuredStepPlain_remainderRepairScratch_not_coefficient window hrepair
    calc
      restored wire = addCleared wire :=
        measuredStepPlain_tBoundaryRestoreState_preservesOutside registers n addCleared
          hlengthT hlengthRPrime
      _ = added wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hcontrol
      _ = addEnabled wire := by
        calc
          added wire = run
              (coefficientPrefixUnitary (registers.coefficient window)
                window.start window.stop .add true .work2) addEnabled wire := by
            simpa only [added] using congrFun hadded.1.symm wire
          _ = addEnabled wire := coefficientPrefixUnitary_preservesOutside
            (registers.coefficient window) .add true .work2 addEnabled
              hcoefficientLayout hcoefficient
      _ = signChanged wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hcontrol
      _ = temporaryCleared2 wire := measuredStepPlain_xorWireState_preserves _ _ _ hsign
      _ = subCleared wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hterminal
      _ = temporary2 wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hcontrol
      _ = subtracted wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hterminal
      _ = prepared wire := by
        calc
          subtracted wire = run
              (coefficientPrefixUnitary (registers.coefficient window)
                window.start window.stop .sub false .work2) prepared wire := by
            simpa only [subtracted] using congrFun hsubtracted.1.symm wire
          _ = prepared wire := coefficientPrefixUnitary_preservesOutside
            (registers.coefficient window) .sub false .work2 prepared
              hcoefficientLayout hcoefficient
      _ = temporaryCleared1 wire :=
        measuredStepPlain_tBoundaryPrepareState_preservesOutside registers n temporaryCleared1
          hlengthT hlengthRPrime
      _ = subEnabled wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hterminal
      _ = temporary1 wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hcontrol
      _ = state wire := measuredStepPlain_matchXorState_preserves _ _ _ _ hterminal
      _ = false := hready wire
        (hlayout.measuredStepPlain_remainderRepairScratch_mem_sharedScratch hrepair)
  have hrestoredBlock : Clean registers.blockScratch restored := by
    simpa only [restored, hrestored.1] using hrestored.2
  constructor
  · exact hrun.trans hstate
  · rw [hrun]
    intro wire hwire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons,
      List.mem_append] at hwire
    rcases hwire with rfl | hsource | hrepair
    · exact hrestoredControl
    · rw [← hlayout.measuredStepPlain_scratch_view] at hsource
      simp only [List.mem_cons] at hsource
      rcases hsource with rfl | hblockWire
      · exact hrestoredTerminal
      · exact hrestoredBlock wire hblockWire
    · exact hrepairFinal wire hrepair

private theorem measuredStepPlain_blockFForward_correct
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    run (blockFForward registers) state = measuredStepPlain_blockFForwardState registers state ∧
      IndexedStepReady registers (run (blockFForward registers) state) := by
  have hlocalReady : ShiftReady registers.postShift state := by
    intro wire hwire
    apply hready wire
    exact hlayout.measuredStepPlain_sourceScratch_mem_sharedScratch
      (hlayout.measuredStepPlain_postShift_scratch_sub_source wire hwire)
  have hrun := run_postShiftUnitary registers.postShift state
    hlayout.postShift hlocalReady
  have hlocalAfter := postShiftUnitary_ready registers.postShift state
    hlayout.postShift hlocalReady
  have hglobalAfter : Clean registers.sharedScratch
      (run (postShiftUnitary registers.postShift) state) :=
    measuredStepPlain_clean_after_local_circuit hready hlocalAfter
      (postShiftUnitary_usesOnly registers.postShift)
      hlayout.measuredStepPlain_postShift_support_intersection
  constructor
  · simpa only [blockFForward, measuredStepPlain_blockFForwardState] using hrun
  · simpa only [blockFForward] using hglobalAfter

private theorem measuredStepPlain_toggleTerminal_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (measuredStepPlain_toggleTerminal registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.terminalControl

private theorem measuredStepPlain_blockCForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (blockCForward registers) := by
  simp only [measuredStepPlain_view_blockCForward, measuredStepPlain_source_blockCForward, circuitWellFormed_append]
  exact ⟨⟨measuredStepPlain_toggleTerminal_wellFormed registers n T hlayout,
    terminalEpochRestore_wellFormed _ _ _ hlayout.terminalEpoch⟩,
    measuredStepPlain_toggleTerminal_wellFormed registers n T hlayout⟩

private theorem measuredStepPlain_phase2LengthControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (measuredStepPlain_phase2LengthControl registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.phase2Length

private theorem measuredStepPlain_phase3LengthControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (measuredStepPlain_phase3LengthControl registers) := by
  exact computeControl_wellFormed _ _ _ _ hlayout.phase3Length

private theorem measuredStepPlain_quotientXorControl_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (measuredStepPlain_quotientXorControl registers) := by
  have hphysical := hlayout.quotientControls
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hphysical
  simp [measuredStepPlain_quotientXorControl, CircuitWellFormed, Gate.WellFormed, hphysical]

private theorem measuredStepPlain_quotientXorControlInverse_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    CircuitWellFormed (measuredStepPlain_quotientXorControlInverse registers) := by
  have hphysical := hlayout.quotientControls
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hphysical
  simp [measuredStepPlain_quotientXorControlInverse, CircuitWellFormed, Gate.WellFormed, hphysical]

private theorem measuredStepPlain_blockDForward_wellFormed
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).quotientSwap) :
    CircuitWellFormed (blockDForward registers window) := by
  subst window
  simp only [blockDForward, measuredStepPlain_view_blockD1Forward, measuredStepPlain_source_blockD1Forward, measuredStepPlain_view_blockD2Forward, measuredStepPlain_source_blockD2Forward, measuredStepPlain_view_blockD3Forward, measuredStepPlain_source_blockD3Forward, circuitWellFormed_append, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact measuredStepPlain_phase2LengthControl_wellFormed registers n T hlayout
  · exact controlledIncrement_wellFormed _ _ _ hlayout.lengthCarryPhysical
  · exact measuredStepPlain_phase2LengthControl_wellFormed registers n T hlayout
  · exact measuredStepPlain_quotientXorControl_wellFormed registers n T hlayout
  · exact quotientSwapUnitary_wellFormed _ hlayout.quotient
  · exact measuredStepPlain_quotientXorControlInverse_wellFormed registers n T hlayout
  · exact measuredStepPlain_phase3LengthControl_wellFormed registers n T hlayout
  · exact controlledDecrement_wellFormed _ _ _ hlayout.lengthCarryPhysical
  · exact measuredStepPlain_phase3LengthControl_wellFormed registers n T hlayout

private theorem measuredStepPlain_indexedStep_coherent_seq_circuits
    {first second : Quantum.AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : Quantum.CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : Quantum.CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (Classical.run firstCircuit state)) :
    Quantum.CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [Quantum.run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact Quantum.supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit (Quantum.ket state)).symm

private theorem measuredStepPlain_indexedStep_coherent_strengthen
    {program : Quantum.AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid Stronger : BasisState → Prop}
    (hrefines : Quantum.CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ state, Stronger state → Valid state) :
    Quantum.CoherentlyImplementsOn program ideal Stronger := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hstate ↦
    hbranch state (hsub state hstate)

private theorem measuredStepPlain_remainderSubControl_intervalReady
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : measuredStepPlain_IndexedStepBorrowedReady registers state) :
    IntervalReady (registers.remainder window)
      (run (measuredStepPlain_remainderSubControl registers) state) := by
  have hsourceClean : Clean (registers.terminal :: registers.blockScratch) state := by
    intro wire hwire
    apply hready wire
    apply hlayout.measuredStepPlain_sourceScratch_mem_aux
    rw [← hlayout.measuredStepPlain_scratch_view]
    exact hwire
  have hrun := run_rControlNonterminal [registers.phase1] 0 registers.control
    registers.lengthRPrime registers.terminal registers.blockScratch state
    hlayout.remainderSub hsourceClean
  intro wire hwire
  rw [show run (measuredStepPlain_remainderSubControl registers) state =
      measuredStepPlain_rControlState [registers.phase1] 0 registers.control
        registers.lengthRPrime registers.terminal state by
    simpa [measuredStepPlain_remainderSubControl, measuredStepPlain_toggleRControl, measuredStepPlain_rControlState] using hrun]
  rw [measuredStepPlain_rControlState_preserves _ _ _ _ _ _ (by
    intro equality
    subst wire
    exact hlayout.measuredStepPlain_control_not_remainder_scratch window hwindow hwire)]
  exact hready wire (hlayout.measuredStepPlain_remainder_scratch_sub_aux window wire hwire)

private theorem measuredStepPlain_remainderRestoreControl_intervalReady
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (state : BasisState) (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder)
    (hready : measuredStepPlain_IndexedStepBorrowedReady registers state) :
    IntervalReady (registers.remainder window)
      (run (measuredStepPlain_remainderRestoreControl registers) state) := by
  have haway : ∀ wire ∈ registers.aux, wire ≠ registers.control →
      state wire = false := by
    intro wire hwire _
    exact hready wire hwire
  have hcorrect := measuredStepPlain_remainderRestoreControl_correct registers n T state hlayout haway
  intro wire hwire
  rw [hcorrect.1]
  exact hcorrect.2 wire (hlayout.measuredStepPlain_remainder_scratch_sub_aux window wire hwire) (by
    intro equality
    subst wire
    exact hlayout.measuredStepPlain_control_not_remainder_scratch window hwindow hwire)

private theorem measuredStepPlain_blockB1Adaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    Quantum.CoherentlyImplementsOn
      (measuredStepPlain_blockB1Adaptive registers n window)
      (Quantum.run (blockB1Forward registers n window))
      (measuredStepPlain_IndexedStepBorrowedReady registers) := by
  have hprefix := Quantum.CoherentlyImplementsOn.unitary
    (measuredStepPlain_remainderSubControl registers) (measuredStepPlain_IndexedStepBorrowedReady registers)
  have hinterval := intervalAddSub_coherent (registers.remainder window) n
    window.start window.stop .sub true .work1 (by
      subst window
      exact hlayout.remainder)
  have hprefixInterval := measuredStepPlain_indexedStep_coherent_seq_circuits hprefix hinterval
    (by simp [measuredStepPlain_remainderSubControl, measuredStepPlain_toggleRControl])
    (fun state hready ↦ measuredStepPlain_remainderSubControl_intervalReady registers n T window
      state hlayout hwindow hready)
  have hsuffix := Quantum.CoherentlyImplementsOn.unitary
    (measuredStepPlain_remainderSubControl registers) (fun _ ↦ True)
  have hall := measuredStepPlain_indexedStep_coherent_seq_circuits hprefixInterval hsuffix
    (by simp [measuredStepPlain_remainderSubControl, measuredStepPlain_toggleRControl]) (fun _ _ ↦ trivial)
  simpa [measuredStepPlain_blockB1Adaptive, measuredStepPlain_view_blockB1Forward, measuredStepPlain_source_blockB1Forward, measuredStepPlain_adaptiveUnitary,
    List.append_assoc] using hall

private theorem measuredStepPlain_blockB3Adaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    Quantum.CoherentlyImplementsOn
      (measuredStepPlain_blockB3Adaptive registers n window)
      (Quantum.run (blockB3Forward registers n window))
      (measuredStepPlain_IndexedStepBorrowedReady registers) := by
  have hprefix := Quantum.CoherentlyImplementsOn.unitary
    (measuredStepPlain_remainderRestoreControl registers) (measuredStepPlain_IndexedStepBorrowedReady registers)
  have hinterval := intervalAddSub_coherent (registers.remainder window) n
    window.start window.stop .add false .work1 (by
      subst window
      exact hlayout.remainder)
  have hprefixInterval := measuredStepPlain_indexedStep_coherent_seq_circuits hprefix hinterval
    (by simp [measuredStepPlain_remainderRestoreControl, measuredStepPlain_toggleRControl])
    (fun state hready ↦ measuredStepPlain_remainderRestoreControl_intervalReady registers n T window
      state hlayout hwindow hready)
  have hsuffix := Quantum.CoherentlyImplementsOn.unitary
    (measuredStepPlain_remainderRestoreControl registers) (fun _ ↦ True)
  have hall := measuredStepPlain_indexedStep_coherent_seq_circuits hprefixInterval hsuffix
    (by simp [measuredStepPlain_remainderRestoreControl, measuredStepPlain_toggleRControl]) (fun _ _ ↦ trivial)
  simpa [measuredStepPlain_blockB3Adaptive, measuredStepPlain_view_blockB3Forward, measuredStepPlain_source_blockB3Forward, measuredStepPlain_adaptiveUnitary,
    List.append_assoc] using hall

private theorem measuredStepPlain_blockBAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).remainder) :
    Quantum.CoherentlyImplementsOn
      (blockBAdaptive registers n window)
      (Quantum.run (blockBForward registers n window))
      (measuredStepPlain_IndexedStepBorrowedReady registers) := by
  have hfirst := measuredStepPlain_blockB1Adaptive_coherent registers n T window hlayout hwindow
  have hmiddle := Quantum.CoherentlyImplementsOn.unitary
    (blockB2 registers) (measuredStepPlain_IndexedStepBorrowedReady registers)
  have hlast := measuredStepPlain_blockB3Adaptive_coherent registers n T window hlayout hwindow
  have hmiddleLast := measuredStepPlain_indexedStep_coherent_seq_circuits hmiddle hlast
    (by simp [measuredStepPlain_view_blockB2, measuredStepPlain_source_blockB2, measuredStepPlain_remainderPhase2Control, measuredStepPlain_toggleRControl])
    (fun state hready ↦ (measuredStepPlain_blockB2_correct registers n T state hlayout hready).2)
  have hall := measuredStepPlain_indexedStep_coherent_seq_circuits hfirst hmiddleLast
    (by simp [measuredStepPlain_view_blockB1Forward, measuredStepPlain_source_blockB1Forward, measuredStepPlain_remainderSubControl, measuredStepPlain_toggleRControl])
    (fun state hready ↦
      (measuredStepPlain_blockB1Forward_correct registers n T window state hlayout hwindow hready).2)
  simpa [measuredStepPlain_view_blockBAdaptive, measuredStepPlain_source_blockBAdaptive, blockBForward, List.append_assoc] using hall

private theorem measuredStepPlain_blockEPrefix_cleanBlockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state) :
    Clean registers.blockScratch (run (measuredStepPlain_blockEPrefix registers n) state) := by
  have hblock : Clean registers.blockScratch state := by
    intro wire hwire
    exact hready wire (hlayout.measuredStepPlain_blockScratch_mem_sharedScratch hwire)
  let temporary1 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  have htemporary1 := measuredStepPlain_run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch state hlayout.coefficientTemporary hblock
  let subEnabled := measuredStepPlain_matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary1
  have hsubEnabled := measuredStepPlain_run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary1 hlayout.coefficientSub (by
        simpa only [temporary1] using htemporary1.2)
  let temporaryCleared := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subEnabled
  have htemporaryCleared := measuredStepPlain_run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subEnabled hlayout.coefficientTemporary (by
        simpa only [subEnabled] using hsubEnabled.2)
  have hprepared := measuredStepPlain_run_tBoundaryPrepareState registers n T temporaryCleared
    hlayout (by simpa only [temporaryCleared] using htemporaryCleared.2)
  simp only [measuredStepPlain_blockEPrefix, Classical.run_append]
  rw [show run (measuredStepPlain_coefficientTemporaryControl registers) state = temporary1 by
      simpa [measuredStepPlain_coefficientTemporaryControl, temporary1] using htemporary1.1,
    show run (measuredStepPlain_coefficientSubControl registers) temporary1 = subEnabled by
      simpa [measuredStepPlain_coefficientSubControl, subEnabled] using hsubEnabled.1,
    show run (measuredStepPlain_coefficientTemporaryControl registers) subEnabled = temporaryCleared by
      simpa [measuredStepPlain_coefficientTemporaryControl, temporaryCleared] using
        htemporaryCleared.1]
  exact hprepared.2

private theorem measuredStepPlain_blockEMiddle_preservesBlockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hclean : Clean registers.blockScratch state) :
    Clean registers.blockScratch (run (measuredStepPlain_blockEMiddle registers) state) := by
  let temporary1 := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal state
  have htemporary1 := measuredStepPlain_run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch state hlayout.coefficientTemporary hclean
  let subCleared := measuredStepPlain_matchXorState [registers.phase1, registers.terminal] 1
    registers.control temporary1
  have hsubCleared := measuredStepPlain_run_computeControl_state
    [registers.phase1, registers.terminal] 1 registers.control
      registers.blockScratch temporary1 hlayout.coefficientSub (by
        simpa only [temporary1] using htemporary1.2)
  let temporaryCleared := measuredStepPlain_matchXorState [registers.phase2, registers.sign] 2
    registers.terminal subCleared
  have htemporaryCleared := measuredStepPlain_run_computeControl_state
    [registers.phase2, registers.sign] 2 registers.terminal
      registers.blockScratch subCleared hlayout.coefficientTemporary (by
        simpa only [subCleared] using hsubCleared.2)
  let signChanged := measuredStepPlain_xorWireState registers.phase1 registers.sign temporaryCleared
  have hsignChanged : Clean registers.blockScratch signChanged := by
    apply measuredStepPlain_clean_upd_not_mem (by
      simpa only [temporaryCleared] using htemporaryCleared.2)
    intro hsign
    exact (hlayout.measuredStepPlain_sign_ne_after (by
      simp [measuredStepPlain_indexedStepAfterSign, hlayout.measuredStepPlain_blockScratch_mem_aux hsign])) rfl
  let addEnabled := measuredStepPlain_matchXorState [registers.phase1] 1 registers.control signChanged
  have haddEnabled := measuredStepPlain_run_computeControl_state [registers.phase1] 1
    registers.control registers.blockScratch signChanged hlayout.coefficientAdd
      hsignChanged
  simp only [measuredStepPlain_blockEMiddle, Classical.run_append]
  rw [show run (measuredStepPlain_coefficientTemporaryControl registers) state = temporary1 by
      simpa [measuredStepPlain_coefficientTemporaryControl, temporary1] using htemporary1.1,
    show run (measuredStepPlain_coefficientSubControl registers) temporary1 = subCleared by
      simpa [measuredStepPlain_coefficientSubControl, subCleared] using hsubCleared.1,
    show run (measuredStepPlain_coefficientTemporaryControl registers) subCleared = temporaryCleared by
      simpa [measuredStepPlain_coefficientTemporaryControl, temporaryCleared] using
        htemporaryCleared.1,
    show run ([.CX registers.phase1 registers.sign] : Circuit) temporaryCleared =
        signChanged by exact measuredStepPlain_run_xorWireState _ _ _]
  rw [show run (measuredStepPlain_coefficientAddControl registers) signChanged = addEnabled by
    simpa [measuredStepPlain_coefficientAddControl, addEnabled] using haddEnabled.1]
  simpa only [addEnabled] using haddEnabled.2

private theorem measuredStepPlain_coefficientPrefix_coherent_on_blockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (mode : RippleMode) (signUpdate : Bool)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    Quantum.CoherentlyImplementsOn
      (coefficientPrefixAdaptive (registers.coefficient window)
        window.start window.stop mode signUpdate .work2)
      (Quantum.run (coefficientPrefixUnitary (registers.coefficient window)
        window.start window.stop mode signUpdate .work2))
      (Clean registers.blockScratch) := by
  apply measuredStepPlain_indexedStep_coherent_strengthen
    (coefficientPrefixAdaptive_coherent (registers.coefficient window)
      mode signUpdate .work2 (by
        subst window
        exact hlayout.coefficient))
  intro state hclean wire hwire
  exact hclean wire (hlayout.measuredStepPlain_coefficient_scratch_sub_block window wire hwire)

private theorem measuredStepPlain_coefficientPrefix_preservesBlockScratch
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient)
    (hclean : Clean registers.blockScratch state) :
    Clean registers.blockScratch
      (run (coefficientPrefixUnitary (registers.coefficient window)
        window.start window.stop mode signUpdate .work2) state) := by
  exact (measuredStepPlain_run_coefficientPrefixState_from_blockScratch registers n T window
    mode signUpdate state hlayout hwindow hclean).2.1

private theorem measuredStepPlain_blockEFirstAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    Quantum.CoherentlyImplementsOn
      (measuredStepPlain_blockEFirstAdaptive registers n window)
      (Quantum.run (measuredStepPlain_blockEPrefix registers n ++
        coefficientPrefixUnitary (registers.coefficient window)
          window.start window.stop .sub false .work2))
      (IndexedStepReady registers) := by
  let subCircuit := coefficientPrefixUnitary (registers.coefficient window)
    window.start window.stop .sub false .work2
  have hprefix := Quantum.CoherentlyImplementsOn.unitary
    (measuredStepPlain_blockEPrefix registers n) (IndexedStepReady registers)
  have hsub : Quantum.CoherentlyImplementsOn
      (coefficientPrefixAdaptive (registers.coefficient window)
        window.start window.stop .sub false .work2)
      (Quantum.run subCircuit) (Clean registers.blockScratch) := by
    simpa only [subCircuit] using measuredStepPlain_coefficientPrefix_coherent_on_blockScratch
      registers n T window .sub false hlayout hwindow
  have hprefixSub := measuredStepPlain_indexedStep_coherent_seq_circuits hprefix hsub
    (by simp [measuredStepPlain_blockEPrefix, measuredStepPlain_coefficientTemporaryControl,
      measuredStepPlain_coefficientSubControl])
    (fun state hready ↦
      measuredStepPlain_blockEPrefix_cleanBlockScratch registers n T state hlayout hready)
  simpa only [measuredStepPlain_blockEFirstAdaptive, measuredStepPlain_adaptiveUnitary, subCircuit] using hprefixSub

private theorem measuredStepPlain_blockETailAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    Quantum.CoherentlyImplementsOn
      (measuredStepPlain_blockETailAdaptive registers n window)
      (Quantum.run (measuredStepPlain_blockEMiddle registers ++
        coefficientPrefixUnitary (registers.coefficient window)
          window.start window.stop .add true .work2 ++
        measuredStepPlain_blockESuffix registers n))
      (Clean registers.blockScratch) := by
  let addCircuit := coefficientPrefixUnitary (registers.coefficient window)
    window.start window.stop .add true .work2
  have hmiddle := Quantum.CoherentlyImplementsOn.unitary
    (measuredStepPlain_blockEMiddle registers) (Clean registers.blockScratch)
  have hadd : Quantum.CoherentlyImplementsOn
      (coefficientPrefixAdaptive (registers.coefficient window)
        window.start window.stop .add true .work2)
      (Quantum.run addCircuit) (Clean registers.blockScratch) := by
    simpa only [addCircuit] using measuredStepPlain_coefficientPrefix_coherent_on_blockScratch
      registers n T window .add true hlayout hwindow
  have hmiddleAdd := measuredStepPlain_indexedStep_coherent_seq_circuits hmiddle hadd
    (by simp [measuredStepPlain_blockEMiddle,
      measuredStepPlain_coefficientTemporaryControl, measuredStepPlain_coefficientSubControl,
      measuredStepPlain_coefficientAddControl]) (by
        intro state hclean
        exact measuredStepPlain_blockEMiddle_preservesBlockScratch registers n T state hlayout hclean)
  have hsuffix := Quantum.CoherentlyImplementsOn.unitary
    (measuredStepPlain_blockESuffix registers n) (fun _ ↦ True)
  have hall := measuredStepPlain_indexedStep_coherent_seq_circuits hmiddleAdd hsuffix
    (by simp [measuredStepPlain_blockEMiddle, addCircuit,
      measuredStepPlain_coefficientTemporaryControl, measuredStepPlain_coefficientSubControl,
      measuredStepPlain_coefficientAddControl]) (fun _ _ ↦ trivial)
  simpa only [measuredStepPlain_blockETailAdaptive, measuredStepPlain_adaptiveUnitary, addCircuit,
    List.append_assoc] using hall

private theorem measuredStepPlain_blockEAdaptive_coherent
    (registers : IndexedStepRegisters) (n T : Nat) (window : ActiveWindow)
    (hlayout : IndexedStepLayout registers n T)
    (hwindow : window = (certifiedActiveWindows n T).coefficient) :
    Quantum.CoherentlyImplementsOn
      (blockEAdaptive registers n window)
      (Quantum.run (blockEForward registers n window))
      (IndexedStepReady registers) := by
  let subCircuit := coefficientPrefixUnitary (registers.coefficient window)
    window.start window.stop .sub false .work2
  let firstCircuit := measuredStepPlain_blockEPrefix registers n ++ subCircuit
  let tailCircuit := measuredStepPlain_blockEMiddle registers ++
    coefficientPrefixUnitary (registers.coefficient window)
      window.start window.stop .add true .work2 ++ measuredStepPlain_blockESuffix registers n
  have hfirst : Quantum.CoherentlyImplementsOn
      (measuredStepPlain_blockEFirstAdaptive registers n window) (Quantum.run firstCircuit)
      (IndexedStepReady registers) := by
    simpa only [firstCircuit, subCircuit] using
      measuredStepPlain_blockEFirstAdaptive_coherent registers n T window hlayout hwindow
  have htail : Quantum.CoherentlyImplementsOn
      (measuredStepPlain_blockETailAdaptive registers n window) (Quantum.run tailCircuit)
      (Clean registers.blockScratch) := by
    simpa only [tailCircuit] using
      measuredStepPlain_blockETailAdaptive_coherent registers n T window hlayout hwindow
  have hall := measuredStepPlain_indexedStep_coherent_seq_circuits hfirst htail
    (by simp [firstCircuit, subCircuit, measuredStepPlain_blockEPrefix,
      measuredStepPlain_coefficientTemporaryControl, measuredStepPlain_coefficientSubControl]) (by
        intro state hready
        rw [show firstCircuit = measuredStepPlain_blockEPrefix registers n ++ subCircuit by rfl,
          Classical.run_append]
        exact measuredStepPlain_coefficientPrefix_preservesBlockScratch registers n T window .sub false
          _ hlayout hwindow
          (measuredStepPlain_blockEPrefix_cleanBlockScratch registers n T state hlayout hready))
  simpa [measuredStepPlain_view_blockEAdaptive, measuredStepPlain_source_blockEAdaptive, blockEForward, measuredStepPlain_view_blockEFinishForward, measuredStepPlain_source_blockEFinishForward, measuredStepPlain_view_blockESubtractForward, measuredStepPlain_source_blockESubtractForward, blockEPrepareForward, measuredStepPlain_view_coefficientSubtractControl, measuredStepPlain_source_coefficientSubtractControl, firstCircuit, tailCircuit,
    measuredStepPlain_blockEPrefix, measuredStepPlain_blockEMiddle, measuredStepPlain_blockESuffix, subCircuit,
    List.append_assoc] using hall

private theorem measuredStepPlain_phaseUpdateAdaptive_coherent_of_indexedReady
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Quantum.CoherentlyImplementsOn
      (phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch)
      (Quantum.run (blockGForward registers))
      (IndexedStepReady registers) := by
  apply measuredStepPlain_indexedStep_coherent_strengthen
    (phaseUpdateEpochAdaptive_coherent registers.phaseUpdate registers.shiftEpoch
      hlayout.phaseUpdate)
  intro state hready wire hwire
  exact hready wire (hlayout.measuredStepPlain_sourceScratch_mem_sharedScratch
    (hlayout.measuredStepPlain_phaseUpdate_scratch_sub_source wire hwire))

private theorem measuredStepPlain_blockCDForward_ready
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : measuredStepPlain_IndexedStepBorrowedReady registers state) :
    IndexedStepReady registers
      (run (blockCForward registers ++
        blockDForward registers (certifiedActiveWindows n T).quotientSwap) state) := by
  rw [Classical.run_append]
  have hC := measuredStepPlain_blockCForward_correct registers n T state hlayout hready
  exact (measuredStepPlain_blockDForward_correct registers n T _
    (run (blockCForward registers) state) hlayout rfl hC.2).2

private theorem measuredStepPlain_indexedStepAdaptive_GH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Quantum.CoherentlyImplementsOn
      ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
        (measuredStepPlain_adaptiveUnitary (blockHForward registers n T)))
      (Quantum.run (blockGForward registers ++ blockHForward registers n T))
      (IndexedStepReady registers) := by
  have hphase := measuredStepPlain_phaseUpdateAdaptive_coherent_of_indexedReady registers n T hlayout
  have hend := Quantum.CoherentlyImplementsOn.unitary
    (blockHForward registers n T) (fun _ ↦ True)
  simpa [measuredStepPlain_adaptiveUnitary] using measuredStepPlain_indexedStep_coherent_seq_circuits hphase hend
    (by simp [blockGForward]) (fun _ _ ↦ trivial)

private theorem measuredStepPlain_indexedStepAdaptive_FGH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    Quantum.CoherentlyImplementsOn
      ((measuredStepPlain_adaptiveUnitary (blockFForward registers)).seq
        ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
          (measuredStepPlain_adaptiveUnitary (blockHForward registers n T))))
      (Quantum.run (blockFForward registers ++ blockGForward registers ++
        blockHForward registers n T))
      (IndexedStepReady registers) := by
  have hshift := Quantum.CoherentlyImplementsOn.unitary
    (blockFForward registers) (IndexedStepReady registers)
  have htail := measuredStepPlain_indexedStepAdaptive_GH_coherent registers n T hlayout
  have hall := measuredStepPlain_indexedStep_coherent_seq_circuits hshift htail
    (by simp [blockFForward])
    (fun state hready ↦ (measuredStepPlain_blockFForward_correct registers n T state hlayout hready).2)
  simpa [measuredStepPlain_adaptiveUnitary, List.append_assoc] using hall

private theorem measuredStepPlain_indexedStepAdaptive_EFGH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    let windows := certifiedActiveWindows n T
    Quantum.CoherentlyImplementsOn
      ((blockEAdaptive registers n windows.coefficient).seq
        ((measuredStepPlain_adaptiveUnitary (blockFForward registers)).seq
          ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
            (measuredStepPlain_adaptiveUnitary (blockHForward registers n T)))))
      (Quantum.run (blockEForward registers n windows.coefficient ++
        blockFForward registers ++ blockGForward registers ++
        blockHForward registers n T))
      (IndexedStepReady registers) := by
  let windows := certifiedActiveWindows n T
  have hcoefficient := measuredStepPlain_blockEAdaptive_coherent registers n T windows.coefficient
    hlayout rfl
  have htail := measuredStepPlain_indexedStepAdaptive_FGH_coherent registers n T hlayout
  have hall := measuredStepPlain_indexedStep_coherent_seq_circuits hcoefficient htail
    (by simp [blockEForward, measuredStepPlain_view_blockEFinishForward, measuredStepPlain_source_blockEFinishForward, measuredStepPlain_view_blockESubtractForward, measuredStepPlain_source_blockESubtractForward, blockEPrepareForward, measuredStepPlain_view_coefficientSubtractControl, measuredStepPlain_source_coefficientSubtractControl, measuredStepPlain_coefficientTemporaryControl,
      measuredStepPlain_coefficientSubControl, measuredStepPlain_coefficientAddControl])
    (fun state hready ↦
      (measuredStepPlain_blockEForward_correct registers n T windows.coefficient state
        hlayout rfl hready).2)
  simpa [windows, List.append_assoc] using hall

private theorem measuredStepPlain_indexedStepAdaptive_CDEFGH_coherent
    (registers : IndexedStepRegisters) (n T : Nat)
    (hlayout : IndexedStepLayout registers n T) :
    let windows := certifiedActiveWindows n T
    Quantum.CoherentlyImplementsOn
      ((measuredStepPlain_adaptiveUnitary (blockCForward registers ++
          blockDForward registers windows.quotientSwap)).seq
        ((blockEAdaptive registers n windows.coefficient).seq
          ((measuredStepPlain_adaptiveUnitary (blockFForward registers)).seq
            ((phaseUpdateEpochAdaptive registers.phaseUpdate registers.shiftEpoch).seq
              (measuredStepPlain_adaptiveUnitary (blockHForward registers n T))))))
      (Quantum.run (blockCForward registers ++
        blockDForward registers windows.quotientSwap ++
        blockEForward registers n windows.coefficient ++
        blockFForward registers ++ blockGForward registers ++
        blockHForward registers n T))
      (measuredStepPlain_IndexedStepBorrowedReady registers) := by
  let windows := certifiedActiveWindows n T
  have hprefix := Quantum.CoherentlyImplementsOn.unitary
    (blockCForward registers ++ blockDForward registers windows.quotientSwap)
    (measuredStepPlain_IndexedStepBorrowedReady registers)
  have htail := measuredStepPlain_indexedStepAdaptive_EFGH_coherent registers n T hlayout
  have hall := measuredStepPlain_indexedStep_coherent_seq_circuits hprefix htail
    (by simp [measuredStepPlain_view_blockCForward, measuredStepPlain_source_blockCForward, blockDForward, measuredStepPlain_view_blockD1Forward, measuredStepPlain_source_blockD1Forward, measuredStepPlain_view_blockD2Forward, measuredStepPlain_source_blockD2Forward, measuredStepPlain_view_blockD3Forward, measuredStepPlain_source_blockD3Forward, measuredStepPlain_toggleTerminal,
      measuredStepPlain_phase2LengthControl, measuredStepPlain_phase3LengthControl, measuredStepPlain_quotientXorControl,
      measuredStepPlain_quotientXorControlInverse])
    (fun state hready ↦ measuredStepPlain_blockCDForward_ready registers n T state hlayout hready)
  simpa [windows, measuredStepPlain_adaptiveUnitary, List.append_assoc] using hall

end
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Paper2607_13816
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem measuredStepPlain_seqCoh {a b : AdaptiveCircuit} {u v : Circuit} {P Q : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) Q)
    (hp : Classical.HPFree u) (hq : ∀ s, P s → Q (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have hh := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical _ s hp]
    exact supportedOn_ket _ _ (hq s hs))
  apply hh.congrIdeal
  intro s _
  exact (Quantum.run_append _ _ _).symm

private theorem measuredStepPlain_d1_hp (r : IndexedStepRegisters) (n T : Nat) : Classical.HPFree (blockD1Forward r) := by
  have h := indexedStepUnitary_HPFree r n T
  simp only [indexedStepUnitary, blockDForward, Classical.hpFree_append] at h
  exact h.1.1.1.1.2.1.1

private theorem measuredStepPlain_cd_hp (r : IndexedStepRegisters) (n T : Nat) :
    Classical.HPFree (blockCForward r ++ blockDForward r (certifiedActiveWindows n T).quotientSwap) := by
  have h := indexedStepUnitary_HPFree r n T
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  exact (Classical.hpFree_append _ _).mpr ⟨h.1.1.1.1.1.2,h.1.1.1.1.2⟩

def blockD (r : IndexedStepRegisters) (w : ActiveWindow) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary (blockD1Forward r) .done).seq (blockD2 r w)).seq
    (.unitary (blockD3Forward r) .done)

theorem blockD_coherent (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (blockD r (certifiedActiveWindows n T).quotientSwap)
      (Quantum.run (blockDForward r (certifiedActiveWindows n T).quotientSwap))
      (IndexedStepReady r) := by
  have hd1 := CoherentlyImplementsOn.unitary (blockD1Forward r) (IndexedStepReady r)
  have hd2 := blockD2_coherent r n T hl
  have h12 := measuredStepPlain_seqCoh hd1 hd2 (measuredStepPlain_d1_hp r n T) (by
    intro s hs
    exact (measuredStepPlain_blockD1Forward_correct r n T s hl hs).2)
  have hd3 := CoherentlyImplementsOn.unitary (blockD3Forward r) (fun _ => True)
  have hall := h12.seq hd3 (by intro s hs t ht; trivial)
  apply hall.congrIdeal
  intro s hs
  simp only [blockDForward, Quantum.run_append, LinearMap.comp_apply]

def blockCD (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (blockCForward r) .done).seq
    (blockD r (certifiedActiveWindows n T).quotientSwap)

theorem blockCD_coherent (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (blockCD r n T)
      (Quantum.run (blockCForward r ++ blockDForward r (certifiedActiveWindows n T).quotientSwap))
      (measuredStepPlain_IndexedStepBorrowedReady r) := by
  have hc := CoherentlyImplementsOn.unitary (blockCForward r)
    (measuredStepPlain_IndexedStepBorrowedReady r)
  exact measuredStepPlain_seqCoh hc (blockD_coherent r n T hl) ((Classical.hpFree_append _ _).mp (measuredStepPlain_cd_hp r n T)).1 (by
    intro s hs
    exact (measuredStepPlain_blockCForward_correct r n T s hl hs).2)
def stepStrictH (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (blockAForward r) .done).seq
    ((blockBAdaptive r n (certifiedActiveWindows n T).remainder).seq
      ((blockCD r n T).seq
        ((blockEAdaptive r n (certifiedActiveWindows n T).coefficient).seq
          ((AdaptiveCircuit.unitary (blockFForward r) .done).seq
            ((phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch).seq
              (.unitary (blockHForward r n T) .done))))))

theorem stepStrictH_coherent (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (stepStrictH r n T) (Quantum.run (indexedStepUnitary r n T))
      (fun s => IndexedStepReady r s ∧ IndexedStepEpochEncoded r s) := by
  have hCD := blockCD_coherent r n T hl
  have hwf : CircuitWellFormed
      (blockCForward r ++ blockDForward r (certifiedActiveWindows n T).quotientSwap) :=
    (circuitWellFormed_append _ _).mpr ⟨measuredStepPlain_blockCForward_wellFormed r n T hl,
      measuredStepPlain_blockDForward_wellFormed r n T _ hl rfl⟩
  have hCDtail := replaceInitialUnitary hwf (measuredStepPlain_cd_hp r n T) hCD
    (measuredStepPlain_indexedStepAdaptive_CDEFGH_coherent r n T hl)
  have hB := measuredStepPlain_blockBAdaptive_coherent r n T _ hl rfl
  have hp := indexedStepUnitary_HPFree r n T
  simp only [indexedStepUnitary, Classical.hpFree_append] at hp
  have hBC := measuredStepPlain_seqCoh hB hCDtail hp.1.1.1.1.1.1.2 (by
    intro s hs
    exact (measuredStepPlain_blockBForward_correct r n T _ s hl rfl hs).2)
  have hA := CoherentlyImplementsOn.unitary (blockAForward r)
    (fun s => IndexedStepReady r s ∧ IndexedStepEpochEncoded r s)
  have hall := measuredStepPlain_seqCoh hA hBC hp.1.1.1.1.1.1.1 (by
    intro s hs
    exact measuredStepPlain_blockAForward_borrowedReady r n T s hl hs.1 hs.2)
  simpa only [stepStrictH,indexedStepUnitary,List.append_assoc] using hall

def stepPrefix (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (blockAForward r) .done).seq
    ((blockBAdaptive r n (certifiedActiveWindows n T).remainder).seq
      ((blockCD r n T).seq
        ((blockEAdaptive r n (certifiedActiveWindows n T).coefficient).seq
          ((AdaptiveCircuit.unitary (blockFForward r) .done).seq
            (phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch)))))

theorem stepPrefix_coherent (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (stepPrefix r n T)
      (Quantum.run (indexedStepShiftPrefix r n T ++ blockGForward r))
      (fun s => IndexedStepReady r s ∧ IndexedStepEpochEncoded r s) := by
  apply cancelUnitaryRight (blockHForward_wellFormed r n T hl)
  have h := stepStrictH_coherent r n T hl
  rw [measuredStepPrefix_unitary_factor] at h
  have hf : stepStrictH r n T = (stepPrefix r n T).seq (.unitary (blockHForward r n T) .done) := by
    simp only [stepStrictH,stepPrefix,circuit_seq_assoc]
  rw [← hf]
  exact h

def step (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  (stepPrefix r n T).seq (measuredBlockHForward r n T)

theorem step_coherent (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (step r n T) (Quantum.run (indexedStepUnitary r n T))
      (fun s => IndexedStepReady r s ∧ IndexedStepEpochEncoded r s) := by
  have hp := indexedStepUnitary_HPFree r n T
  rw [measuredStepPrefix_unitary_factor] at hp
  have hpre : Classical.HPFree (indexedStepShiftPrefix r n T ++ blockGForward r) :=
    ((Classical.hpFree_append _ _).mp hp).1
  have hall := measuredStepPlain_seqCoh (stepPrefix_coherent r n T hl) (measuredBlockHForward_coherent r n T hl)
    hpre (by intro s hs; exact indexedStepBeforeEnd_ready r n T hl s hs.1 hs.2)
  simpa only [step,← measuredStepPrefix_unitary_factor] using hall

end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] program remainderBlockProgram coefficientBlockProgram phaseProgram hProgram

def d2Program (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow) :
    (count : Nat) × Straight n start (start+count) :=
  surroundCompiled (before r) (after r) (program n start (r.quotient w) w.start w.stop)

theorem d2Program_run (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (d2Program n start r w) read history = (blockD2 r w).run := by
  exact surroundCompiled_run _ _ _ _ read history (program_run n start (r.quotient w) w.start w.stop read history)

theorem d2Program_tCount (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (d2Program n start r w) read history = (blockD2 r w).tCount := by
  exact surroundCompiled_tCount _ _ _ _ read history (program_tCount n start (r.quotient w) w.start w.stop read history)

def dProgram (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow) :
    (count : Nat) × Straight n start (start+count) :=
  surroundCompiled (blockD1Forward r) (blockD3Forward r) (d2Program n start r w)

theorem dProgram_run (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (dProgram n start r w) read history = (blockD r w).run := by
  simpa only [blockD,circuit_seq_assoc,AdaptiveCircuit.seq] using
    surroundCompiled_run (blockD1Forward r) (blockD3Forward r) (d2Program n start r w)
      (blockD2 r w) read history (d2Program_run n start r w read history)

theorem dProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (dProgram n start r w) read history = (blockD r w).tCount := by
  simpa only [blockD,circuit_seq_assoc,AdaptiveCircuit.seq] using
    surroundCompiled_tCount (blockD1Forward r) (blockD3Forward r) (d2Program n start r w)
      (blockD2 r w) read history (d2Program_tCount n start r w read history)

def cdProgram (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  prependCompiled (blockCForward r) (dProgram n start r (certifiedActiveWindows width T).quotientSwap)

theorem cdProgram_run (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (cdProgram n start r width T) read history = (blockCD r width T).run := by
  apply prependCompiled_run_eq
  exact dProgram_run n start r _ read history

theorem cdProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (cdProgram n start r width T) read history = (blockCD r width T).tCount := by
  apply prependCompiled_tCount_eq
  exact dProgram_tCount n start r _ read history

def stepSources (r : IndexedStepRegisters) (width T : Nat) : List AdaptiveCircuit :=
  ([.unitary (blockAForward r) .done,
    blockBAdaptive r width (certifiedActiveWindows width T).remainder,
    blockCD r width T,
    blockEAdaptive r width (certifiedActiveWindows width T).coefficient,
    .unitary (blockFForward r) .done,
    phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch,
    measuredBlockHForward r width T] : List AdaptiveCircuit)
def stepSegments (n : Nat) (r : IndexedStepRegisters) (width T : Nat) : List (FixedSegment n) :=
  ([(fun _ => ⟨0, literalProgram (blockAForward r)⟩),
    (fun cursor => remainderBlockProgram n cursor r width (certifiedActiveWindows width T).remainder),
    (fun cursor => cdProgram n cursor r width T),
    (fun cursor => coefficientBlockProgram n cursor r width (certifiedActiveWindows width T).coefficient),
    (fun _ => ⟨0, literalProgram (blockFForward r)⟩),
    (fun cursor => phaseProgram n cursor r.phaseUpdate r.shiftEpoch),
    (fun cursor => hProgram n cursor r width T)] : List (FixedSegment n))
theorem stepSources_eq (r : IndexedStepRegisters) (width T : Nat) :
    sequenceCircuit (stepSources r width T) = step r width T := by
  simp only [stepSources, sequenceCircuit, step, stepPrefix, adaptive_seq_assoc, adaptive_seq_done]

def stepProgram (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (stepSegments n r width T) start
attribute [local irreducible] stepProgram
theorem stepProgram_run (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (stepProgram n start r width T) read history = (step r width T).run := by
  unfold stepProgram
  rw [← stepSources_eq r width T]
  apply sequenceProgram_run
  unfold stepSegments stepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact remainderBlockProgram_run n cursor r width (certifiedActiveWindows width T).remainder read h
  · intro cursor h
    exact cdProgram_run n cursor r width T read h
  · intro cursor h
    exact coefficientBlockProgram_run n cursor r width (certifiedActiveWindows width T).coefficient read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact phaseProgram_run n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    exact hProgram_run n cursor r width T read h

theorem stepProgram_tCount (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (stepProgram n start r width T) read history = (step r width T).tCount := by
  unfold stepProgram
  rw [← stepSources_eq r width T]
  apply sequenceProgram_tCount
  unfold stepSegments stepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact remainderBlockProgram_tCount n cursor r width (certifiedActiveWindows width T).remainder read h
  · intro cursor h
    exact cdProgram_tCount n cursor r width T read h
  · intro cursor h
    exact coefficientBlockProgram_tCount n cursor r width (certifiedActiveWindows width T).coefficient read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact phaseProgram_tCount n cursor r.phaseUpdate r.shiftEpoch read h
  · intro cursor h
    exact hProgram_tCount n cursor r width T read h


end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem d_tCount (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    let w := (certifiedActiveWindows n T).quotientSwap
    (blockD r w).tCount + 7*(quotientSwapTree (r.quotient w) w.start w.stop).internalNodes =
      ShorECDLP.tCount (blockDForward r w) := by
  dsimp only
  let w := (certifiedActiveWindows n T).quotientSwap
  have hd : (quotientSwap (r.quotient w) w.start w.stop).tCount +
      7*(quotientSwapTree (r.quotient w) w.start w.stop).internalNodes =
      ShorECDLP.tCount (quotientSwapUnitary (r.quotient w) w.start w.stop) := by
    rw [quotientSwap_tCount _ hl.quotient,quotientSwapUnitary_tCount _ hl.quotient]
    dsimp only [w]
    omega
  simp only [blockD,blockD2,blockDForward,blockD2Forward,adaptive_tCount_seq,
    AdaptiveCircuit.tCount,ShorECDLP.tCount_append]
  change ShorECDLP.tCount (blockD1Forward r) +
    ((0 + ((quotientSwap (r.quotient w) w.start w.stop).tCount + (0 + 0)))) +
    (ShorECDLP.tCount (blockD3Forward r) + 0) +
    7*(quotientSwapTree (r.quotient w) w.start w.stop).internalNodes =
    ShorECDLP.tCount (blockD1Forward r) +
      ((0 + ShorECDLP.tCount (quotientSwapUnitary (r.quotient w) w.start w.stop)) + 0) +
      ShorECDLP.tCount (blockD3Forward r)
  omega

private theorem measuredCost_originalPrefix_view (r : IndexedStepRegisters) (n T : Nat) :
    measuredStepPrefix r n T =
    (AdaptiveCircuit.unitary (blockAForward r) .done).seq
      ((blockBAdaptive r n (certifiedActiveWindows n T).remainder).seq
        ((AdaptiveCircuit.unitary (blockCForward r ++ blockDForward r (certifiedActiveWindows n T).quotientSwap) .done).seq
          ((blockEAdaptive r n (certifiedActiveWindows n T).coefficient).seq
            ((AdaptiveCircuit.unitary (blockFForward r) .done).seq
              (phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch))))) := rfl

theorem step_tCount (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    let w := (certifiedActiveWindows n T).quotientSwap
    (step r n T).tCount + 7*(quotientSwapTree (r.quotient w) w.start w.stop).internalNodes =
      (measuredIndexedStep r n T).tCount := by
  have hd := d_tCount r n T hl
  dsimp only at hd ⊢
  simp only [step,stepPrefix,blockCD,measuredIndexedStep,measuredCost_originalPrefix_view,
    adaptive_tCount_seq,AdaptiveCircuit.tCount,ShorECDLP.tCount_append]
  omega

private theorem measuredCost_quotient_leaf_count (r : QuotientSwapRegisters) (k K : Nat)
    (h : QuotientSwapLayout r k K) : (quotientSwapTree r k K).leaves=K+1-k := by
  rw [unaryAction_leaves_eq_labels_length,quotientSwapTree_labels r h.k_le_K,Finset.length_sort]
  simpa only [quotientSwapLabels,List.length_range'] using
    List.toFinset_card_of_nodup (show (List.range' k (K+1-k)).Nodup from List.nodup_range')

theorem production_nodes (T : Nat) (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    let w := (certifiedActiveWindows 256 T).quotientSwap
    (quotientSwapTree (indexedStepProductionRegisters.quotient w) w.start w.stop).internalNodes = nodeBudget T := by
  dsimp only
  let w := (certifiedActiveWindows 256 T).quotientSwap
  have hq := measuredCost_quotient_leaf_count (indexedStepProductionRegisters.quotient w) w.start w.stop hl.quotient
  have hn := unaryAction_internalNodes_add_one
    (quotientSwapTree (indexedStepProductionRegisters.quotient w) w.start w.stop)
  rw [hq] at hn
  have hk := hl.quotient.k_le_K
  change _ = w.stop-w.start
  dsimp only [w] at hn ⊢
  omega

theorem production_step_tCount (T : Nat) (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    (step indexedStepProductionRegisters 256 T).tCount + 7*nodeBudget T =
      (measuredIndexedStep indexedStepProductionRegisters 256 T).tCount := by
  have h := step_tCount indexedStepProductionRegisters 256 T hl
  dsimp only at h
  rwa [production_nodes T hl] at h
end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def schedule (r : IndexedStepRegisters) (width first : Nat) : Nat → AdaptiveCircuit
  | 0 => .unitary [] .done
  | count+1 => (step r width first).seq (schedule r width (first+1) count)

private theorem measuredSchedule_restrict {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P Q : BasisState → Prop} (h : CoherentlyImplementsOn a v P)
    (hp : ∀ s, Q s → P s) : CoherentlyImplementsOn a v Q := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩
private theorem measuredSchedule_compose {a b : AdaptiveCircuit} {u v : Circuit} {P Q : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) Q)
    (hu : Classical.HPFree u) (hp : ∀ s, P s → Q (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket Q _ (hp s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append u v (ket s)).symm

theorem schedule_coherent (r : IndexedStepRegisters) (width first count : Nat)
    (hl : IndexedScheduleLayout r width first count) :
    CoherentlyImplementsOn (schedule r width first count)
      (Quantum.run (indexedScheduleUnitary r width first count))
      (IndexedScheduleAdaptiveInput r width first count) := by
  induction hl with
  | done first =>
      simpa [schedule,indexedScheduleUnitary] using
        (CoherentlyImplementsOn.unitary ([] : Circuit) (IndexedScheduleAdaptiveInput r width first 0))
  | @step first count head tail ih =>
      have hh := measuredSchedule_restrict (step_coherent r width first head)
        (Q := IndexedScheduleAdaptiveInput r width first (count+1)) (fun _ h => ⟨h.1,h.2.1⟩)
      exact measuredSchedule_compose hh ih (indexedStepUnitary_HPFree r width first) (fun _ h => h.2.2)

def scheduleSaving (first : Nat) : Nat → Nat
  | 0 => 0
  | count+1 => 7*nodeBudget first + scheduleSaving (first+1) count

theorem scheduleSaving_eq_sum (first count : Nat) :
    scheduleSaving first count = 7*((List.range' first count).map nodeBudget).sum := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih => simp only [scheduleSaving,List.range'_succ,List.map_cons,List.sum_cons,ih,Nat.mul_add]

theorem scheduleSaving_total : scheduleSaving 1 1620 = 1690738 := by
  rw [scheduleSaving_eq_sum,nodeBudget_total]

theorem schedule_tCount (first count : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count) :
    (schedule indexedStepProductionRegisters 256 first count).tCount + scheduleSaving first count =
      (measuredIndexedSchedule indexedStepProductionRegisters 256 first count).tCount := by
  induction hl with
  | done first => rfl
  | @step first count head tail ih =>
      have hh := production_step_tCount first head
      simp only [schedule,measuredIndexedSchedule,scheduleSaving,adaptive_tCount_seq]
      omega

def scheduleProgram (n : Nat) (r : IndexedStepRegisters) (width : Nat) :
    (count first start : Nat) → (events : Nat) × Straight n start (start+events)
  | 0, _, _ => ⟨0, literalProgram []⟩
  | count+1, first, start =>
    let step := stepProgram n start r width first
    appendCompiled step (scheduleProgram n r width count (first+1) (start+step.1))


attribute [local irreducible] stepProgram
theorem scheduleProgram_run (n : Nat) (r : IndexedStepRegisters) (width : Nat) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (scheduleProgram n r width count first start) read history =
      (schedule r width first count).run := by
  induction count generalizing first start with
  | zero =>
    exact literalProgram_run [] read history
  | succ count ih =>
    unfold scheduleProgram schedule
    dsimp only
    apply appendCompiled_run_eq
    · exact stepProgram_run n start r width first read history
    · intro h
      exact ih (first+1) _ h

theorem scheduleProgram_tCount (n : Nat) (r : IndexedStepRegisters) (width : Nat) (count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (scheduleProgram n r width count first start) read history =
      (schedule r width first count).tCount := by
  induction count generalizing first start with
  | zero =>
    rfl
  | succ count ih =>
    unfold scheduleProgram schedule
    dsimp only
    apply appendCompiled_tCount_eq
    · exact stepProgram_tCount n start r width first read history
    · intro h
      exact ih (first+1) _ h


end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Classical Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def forward (r : IndexedStepRegisters) : AdaptiveCircuit := schedule r 256 1 secp256k1ScheduleLength
theorem forward_coherent_preprocessed :
    Quantum.CoherentlyImplementsOn (forward indexedStepProductionRegisters)
      (Quantum.run (secp256k1EEAForwardUnitary indexedStepProductionRegisters))
      (fun state => ∃ s : BasisState,
        Clean (List.range' 0 263 ++ List.range' 519 61) s ∧
        0 < boolWordToNat (wireValues (List.range' 263 256) s) ∧
        boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p ∧
        state = eeaPreprocessIdealState s) := by
  have h := schedule_coherent indexedStepProductionRegisters 256 1
    secp256k1ScheduleLength secp256k1ScheduleLayout_production
  obtain ⟨coefficients, aligned, mass⟩ := h
  refine ⟨coefficients, ?_, mass⟩
  apply aligned.imp
  intro branch coefficient hb state hs
  obtain ⟨s, hc, hx, hxp, he⟩ := hs
  apply hb
  rw [he]
  exact secp256k1EEAForward_adaptiveInput s hc hx hxp


private theorem measuredWrapper_basisLift_ket (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by
  simp [ket]
private theorem measuredWrapper_coherent_basis_strengthen {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State} {Valid Stronger : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ s, Stronger s → Valid s) :
    CoherentlyImplementsOn program ideal Stronger := by
  obtain ⟨cs, ha, hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (hsub s hs)),hm⟩
private theorem measuredWrapper_coherent_basis_seq {first second : AdaptiveCircuit}
    {f g : BasisState → BasisState} {Valid Next : BasisState → Prop}
    (hf : CoherentlyImplementsOn first (Finsupp.lmapDomain ℂ ℂ f) Valid)
    (hg : CoherentlyImplementsOn second (Finsupp.lmapDomain ℂ ℂ g) Next)
    (hnext : ∀ s, Valid s → Next (f s)) :
    CoherentlyImplementsOn (first.seq second)
      (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) Valid := by
  have h := hf.seq hg (by
    intro s hs
    rw [measuredWrapper_basisLift_ket]
    exact supportedOn_ket Next _ (hnext s hs))
  apply h.congrIdeal
  intro s _
  simp only [LinearMap.comp_apply,measuredWrapper_basisLift_ket]
private theorem measuredWrapper_coherent_basis_unitary (c : Circuit) (hc : HPFree c)
    (Valid : BasisState → Prop) :
    CoherentlyImplementsOn (.unitary c .done)
      (Finsupp.lmapDomain ℂ ℂ (Classical.run c)) Valid := by
  apply (CoherentlyImplementsOn.unitary c Valid).congrIdeal
  intro s _
  rw [measuredWrapper_basisLift_ket,Quantum.run_ket_agrees_classical c s hc]
/-- Complete forward wrapper with the new measured EEA schedule. -/
def wrapper : AdaptiveCircuit :=
  ((((eeaPreprocess.seq (forward indexedStepProductionRegisters)).seq
    (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
    secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done))
/-- The complete adaptive wrapper has one input-independent normalized branch expansion
for all clean nonzero canonical inputs. Its ideal state carries the proved modular inverse. -/
theorem wrapper_coherent :
    CoherentlyImplementsOn wrapper
      (Finsupp.lmapDomain ℂ ℂ secp256k1EEAOutputIdealState) Secp256k1EEAInputValid := by
  have hc := canonicalWork2Rotation_HPFree
  have hp : CoherentlyImplementsOn eeaPreprocess
      (Finsupp.lmapDomain ℂ ℂ eeaPreprocessIdealState) Secp256k1EEAInputValid :=
    measuredWrapper_coherent_basis_strengthen preprocess_basis_coherent (fun _ h => h.1)
  have hf := forward_coherent_preprocessed.congrIdeal
    (secondIdeal := Finsupp.lmapDomain ℂ ℂ
      (Classical.run (secp256k1EEAForwardUnitary indexedStepProductionRegisters))) (by
        intro s _
        rw [measuredWrapper_basisLift_ket,Quantum.run_ket_agrees_classical (secp256k1EEAForwardUnitary indexedStepProductionRegisters) s
          (indexedScheduleUnitary_HPFree indexedStepProductionRegisters 256 1 secp256k1ScheduleLength)])
  have hpf := measuredWrapper_coherent_basis_seq hp hf (by
    intro s hs
    exact ⟨s,hs.1,hs.2.1,hs.2.2,rfl⟩)
  have he : HPFree terminalEpochCompression := by simp [terminalEpochCompression,mcxVChain_HPFree]
  have hcanonical := measuredWrapper_coherent_basis_seq hpf
    (measuredWrapper_coherent_basis_unitary (canonicalWork2Rotation ++ terminalEpochCompression)
      ((hpFree_append _ _).mpr ⟨hc,he⟩) (fun _ => True)) (fun _ _ => trivial)
  have hparity := measuredWrapper_coherent_basis_seq hcanonical parity_basis_coherent (by
    intro s hs
    have hready := (secp256k1EEAForward_canonical_epoch s hs.1 hs.2.1 hs.2.2).2.2
    have h560 := hready 560 (by decide)
    have h561 := hready 561 (by decide)
    have h562 := hready 562 (by decide)
    simpa only [Classical.run_append] using And.intro h560 (And.intro h561 h562))
  have hclear : HPFree terminalWork1Clear := xorConstant_HPFree _ _
  have hall := measuredWrapper_coherent_basis_seq hparity
    (measuredWrapper_coherent_basis_unitary terminalWork1Clear hclear (fun _ => True)) (fun _ _ => trivial)
  apply hall.congrIdeal
  intro s _
  simp only [measuredWrapper_basisLift_ket]
  exact congrArg ket (by
    simp only [secp256k1EEAOutputIdealState, Classical.run_append])


def forwardProgram (n start : Nat) (r : IndexedStepRegisters) :
    (count : Nat) × Straight n start (start+count) :=
  scheduleProgram n r 256 secp256k1ScheduleLength 1 start

theorem forwardProgram_run (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (forwardProgram n start r) read history = (forward r).run :=
  scheduleProgram_run n r 256 secp256k1ScheduleLength 1 start read history

theorem forwardProgram_tCount (n start : Nat) (r : IndexedStepRegisters)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (forwardProgram n start r) read history = (forward r).tCount :=
  scheduleProgram_tCount n r 256 secp256k1ScheduleLength 1 start read history

attribute [local irreducible] forwardProgram

def wrapperSources  : List AdaptiveCircuit :=
  ([eeaPreprocess,
    forward indexedStepProductionRegisters,
    .unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done,
    secp256k1EEAParityCorrection,
    .unitary (terminalWork1Clear) .done] : List AdaptiveCircuit)
def wrapperSegments (n : Nat)  : List (FixedSegment n) :=
  ([(fun cursor => preprocessProgram n cursor),
    (fun cursor => forwardProgram n cursor indexedStepProductionRegisters),
    (fun _ => ⟨0, literalProgram (canonicalWork2Rotation ++ terminalEpochCompression)⟩),
    (fun cursor => productionParityProgram n cursor),
    (fun _ => ⟨0, literalProgram (terminalWork1Clear)⟩)] : List (FixedSegment n))
theorem wrapperSources_eq  :
    sequenceCircuit (wrapperSources ) = wrapper := by
  simp only [wrapperSources, sequenceCircuit, wrapper, adaptive_seq_assoc, adaptive_seq_done]

def wrapperProgram (n start : Nat)  : (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (wrapperSegments n ) start
attribute [local irreducible] wrapperProgram
theorem wrapperProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (wrapperProgram n start ) read history = (wrapper).run := by
  unfold wrapperProgram
  rw [← wrapperSources_eq ]
  apply sequenceProgram_run
  unfold wrapperSegments wrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact preprocessProgram_run n cursor read h
  · intro cursor h
    exact forwardProgram_run n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact literalCompiled_run _ read h
  · intro cursor h
    exact productionParityProgram_run n cursor read h
  · intro cursor h
    exact literalCompiled_run _ read h

theorem wrapperProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (wrapperProgram n start ) read history = (wrapper).tCount := by
  unfold wrapperProgram
  rw [← wrapperSources_eq ]
  apply sequenceProgram_tCount
  unfold wrapperSegments wrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor h
    exact preprocessProgram_tCount n cursor read h
  · intro cursor h
    exact forwardProgram_tCount n cursor indexedStepProductionRegisters read h
  · intro cursor h
    exact literalCompiled_tCount _ read h
  · intro cursor h
    exact productionParityProgram_tCount n cursor read h
  · intro cursor h
    exact literalCompiled_tCount _ read h


private theorem measuredWrapper_sequence_saving (a x y b c d : AdaptiveCircuit) (saving : Nat)
    (h : x.tCount + saving = y.tCount) :
    ((((a.seq x).seq b).seq c).seq d).tCount + saving =
      ((((a.seq y).seq b).seq c).seq d).tCount := by
  simp only [adaptive_tCount_seq]
  omega

attribute [local irreducible] AdaptiveCircuit.tCount schedule measuredIndexedSchedule

private theorem measuredWrapper_schedule_saving_value (first count saving : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count)
    (hv : scheduleSaving first count = saving) :
    (schedule indexedStepProductionRegisters 256 first count).tCount + saving =
      (measuredIndexedSchedule indexedStepProductionRegisters 256 first count).tCount :=
  (congrArg (fun x => (schedule indexedStepProductionRegisters 256 first count).tCount + x) hv.symm).trans
    (schedule_tCount first count hl)

private theorem measuredWrapper_forward_view (r : IndexedStepRegisters) :
    forward r = schedule r 256 1 secp256k1ScheduleLength := rfl
private theorem measuredWrapper_original_forward_view (r : IndexedStepRegisters) :
    secp256k1MeasuredEEAForward r = measuredIndexedSchedule r 256 1 secp256k1ScheduleLength := rfl

theorem forward_saving : (forward indexedStepProductionRegisters).tCount + 1690738 =
    (secp256k1MeasuredEEAForward indexedStepProductionRegisters).tCount :=
  (congrArg (fun a : AdaptiveCircuit => a.tCount + 1690738)
    (measuredWrapper_forward_view indexedStepProductionRegisters)).trans
    ((measuredWrapper_schedule_saving_value 1 secp256k1ScheduleLength 1690738
      secp256k1ScheduleLayout_production scheduleSaving_total).trans
      (congrArg AdaptiveCircuit.tCount (measuredWrapper_original_forward_view indexedStepProductionRegisters)).symm)

private theorem measuredWrapper_wrapper_view : wrapper =
    ((((eeaPreprocess.seq (forward indexedStepProductionRegisters)).seq
      (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
      secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done)) := rfl
private theorem measuredWrapper_original_wrapper_view : secp256k1MeasuredEEAForwardWrapper =
    ((((eeaPreprocess.seq (secp256k1MeasuredEEAForward indexedStepProductionRegisters)).seq
      (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
      secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done)) := rfl

theorem wrapper_saving : wrapper.tCount + 1690738 = secp256k1MeasuredEEAForwardWrapper.tCount :=
  (congrArg (fun a : AdaptiveCircuit => a.tCount + 1690738) measuredWrapper_wrapper_view).trans
    ((measuredWrapper_sequence_saving eeaPreprocess (forward indexedStepProductionRegisters)
      (secp256k1MeasuredEEAForward indexedStepProductionRegisters)
      (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)
      secp256k1EEAParityCorrection (.unitary terminalWork1Clear .done) 1690738 forward_saving).trans
      (congrArg AdaptiveCircuit.tCount measuredWrapper_original_wrapper_view).symm)
end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The compiled unary traversal emits exactly one erasure record per internal
node when its leaves are literal circuits. -/
theorem unaryProgram_records (n : Nat) (order : UnaryOrder)
    (leaf : Nat → Wire → Circuit) (tree : UnaryActionTree) (control : Wire)
    (paths : List Wire) (hl : tree.Layout control paths) (start : Nat) :
    (unaryProgram n order (fun label control _ => ⟨0,literalProgram (leaf label control)⟩)
      tree control paths start).1 = tree.internalNodes := by
  induction hl generalizing start with
  | leaf label control paths hlocal => simp only [unaryProgram,UnaryActionTree.internalNodes]
  | node bit control path zero one rest hlocal hzero hone ihz iho =>
    cases order <;>
      simp [unaryProgram,prependCompiled,appendCompiled,zeroEraseProgram,
        UnaryActionTree.internalNodes,ihz,iho] <;> omega

/-- Literal prefix and suffix arithmetic emit no records. -/
theorem program_records (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat)
    (hl : QuotientSwapLayout r k K) :
    (program n start r k K).1 = (quotientSwapTree r k K).internalNodes := by
  simp only [program,surroundCompiled,prependCompiled,appendCompiled,Nat.add_zero]
  exact unaryProgram_records n .inc (quotientSwapLeaf r k)
    (quotientSwapTree r k K) r.control (r.path k K) hl.tree start

/-- Source T cost plus seven per new erasure record is exactly the coherent
source cost. With a four-P measured CCX lowering, the net gain is four P per
node; the final record count is unchanged once the removed CCX is accounted for. -/
theorem program_t_record_balance (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat)
    (hl : QuotientSwapLayout r k K) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    compiledTCount (program n start r k K) read history + 7*(program n start r k K).1 =
      ShorECDLP.tCount (quotientSwapUnitary r k K) := by
  rw [program_records n start r k K hl]
  exact program_saving n start r k K hl read history
end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem measuredMeasurements_measurements_seq (a b : AdaptiveCircuit) :
    (a.seq b).measurementCount = a.measurementCount + b.measurementCount := by
  induction a with
  | done => simp only [AdaptiveCircuit.seq,AdaptiveCircuit.measurementCount,Nat.zero_add]
  | unitary gs a ih => simpa only [AdaptiveCircuit.seq,AdaptiveCircuit.measurementCount] using ih
  | xMeasureReset w a b iha ihb =>
    simp only [AdaptiveCircuit.seq,AdaptiveCircuit.measurementCount,iha,ihb,Nat.add_max_add_right]
    omega

theorem d_measurements (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    let w := (certifiedActiveWindows n T).quotientSwap
    (blockD r w).measurementCount = (quotientSwapTree (r.quotient w) w.start w.stop).internalNodes := by
  dsimp only
  simp only [blockD,blockD2,measuredMeasurements_measurements_seq,AdaptiveCircuit.measurementCount,
    quotientSwap_measurementCount _ hl.quotient,Nat.zero_add,Nat.add_zero]

private theorem measuredMeasurements_originalPrefix_measurement_view (r : IndexedStepRegisters) (n T : Nat) :
    measuredStepPrefix r n T =
    (AdaptiveCircuit.unitary (blockAForward r) .done).seq
      ((blockBAdaptive r n (certifiedActiveWindows n T).remainder).seq
        ((AdaptiveCircuit.unitary (blockCForward r ++ blockDForward r (certifiedActiveWindows n T).quotientSwap) .done).seq
          ((blockEAdaptive r n (certifiedActiveWindows n T).coefficient).seq
            ((AdaptiveCircuit.unitary (blockFForward r) .done).seq
              (phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch))))) := rfl

theorem step_measurements (r : IndexedStepRegisters) (n T : Nat) (hl : IndexedStepLayout r n T) :
    let w := (certifiedActiveWindows n T).quotientSwap
    (step r n T).measurementCount = (measuredIndexedStep r n T).measurementCount +
      (quotientSwapTree (r.quotient w) w.start w.stop).internalNodes := by
  have hd := d_measurements r n T hl
  dsimp only at hd ⊢
  simp only [step,stepPrefix,blockCD,measuredIndexedStep,measuredMeasurements_originalPrefix_measurement_view,
    measuredMeasurements_measurements_seq,AdaptiveCircuit.measurementCount]
  omega

def scheduleExtraRecords (first count : Nat) : Nat := ((List.range' first count).map nodeBudget).sum

theorem schedule_measurements (first count : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count) :
    (schedule indexedStepProductionRegisters 256 first count).measurementCount =
      (measuredIndexedSchedule indexedStepProductionRegisters 256 first count).measurementCount +
        scheduleExtraRecords first count := by
  induction hl with
  | done first => rfl
  | @step first count head tail ih =>
    have h := step_measurements indexedStepProductionRegisters 256 first head
    dsimp only at h
    rw [production_nodes first head] at h
    simp only [schedule,measuredIndexedSchedule,measuredMeasurements_measurements_seq,scheduleExtraRecords,
      List.range'_succ,List.map_cons,List.sum_cons] at ih ⊢
    omega

theorem scheduleExtraRecords_total : scheduleExtraRecords 1 1620 = 241534 := nodeBudget_total

/- Generic record-count transfer reproduced from the inherited streaming resources. -/
theorem adaptive_run_nonempty (a : AdaptiveCircuit) : ∃ b, b ∈ a.run := by
  induction a with
  | done => exact ⟨_, List.mem_singleton_self _⟩
  | unitary gs a ih =>
    obtain ⟨b,hb⟩ := ih
    exact ⟨_, List.mem_map_of_mem hb⟩
  | xMeasureReset w a b iha ihb =>
    obtain ⟨c,hc⟩ := iha
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hc)⟩

/-- Uniform actual branch record lengths determine the syntactic measurement count. -/
theorem measurementCount_of_uniform_run (a : AdaptiveCircuit) (k : Nat)
    (h : ∀ b ∈ a.run, b.history.length = k) : a.measurementCount = k := by
  induction a generalizing k with
  | done => exact h ⟨[],LinearMap.id⟩ (List.mem_singleton_self _)
  | unitary gs a ih =>
    apply ih
    intro b hb
    have hh := h _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
    exact hh
  | xMeasureReset w a b iha ihb =>
    have ha : ∀ c ∈ a.run, c.history.length + 1 = k := by
      intro c hc
      exact h _ (List.mem_append_left _ (List.mem_map_of_mem hc))
    have hb : ∀ c ∈ b.run, c.history.length + 1 = k := by
      intro c hc
      exact h _ (List.mem_append_right _ (List.mem_map_of_mem hc))
    have hk : 0 < k := by
      obtain ⟨c,hc⟩ := adaptive_run_nonempty a
      have := ha c hc
      omega
    have hca := iha (k-1) (by intro c hc; have := ha c hc; omega)
    have hcb := ihb (k-1) (by intro c hc; have := hb c hc; omega)
    simp only [AdaptiveCircuit.measurementCount,hca,hcb,max_self]
    omega

/-- Transfer measurement counts through a proved execution binding, without
unfolding the compiled circuit or enumerating its branches. -/
theorem compiled_count_of_run {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (a : AdaptiveCircuit)
    (h : compiledRun p read history = a.run) : p.1 = a.measurementCount := by
  apply Eq.symm
  apply measurementCount_of_uniform_run
  intro b hb
  rw [← h] at hb
  have hh := straight_history_length p.2 read history b hb
  simpa using hh

private theorem measuredMeasurements_schedule_measurements_value (first count extra : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count)
    (hv : scheduleExtraRecords first count = extra) :
    (schedule indexedStepProductionRegisters 256 first count).measurementCount =
      (measuredIndexedSchedule indexedStepProductionRegisters 256 first count).measurementCount + extra :=
  (schedule_measurements first count hl).trans
    (congrArg (fun x => (measuredIndexedSchedule indexedStepProductionRegisters 256 first count).measurementCount + x) hv)

private theorem measuredMeasurements_forward_record_view (r : IndexedStepRegisters) :
    forward r = schedule r 256 1 secp256k1ScheduleLength := rfl
private theorem measuredMeasurements_original_forward_record_view (r : IndexedStepRegisters) :
    secp256k1MeasuredEEAForward r = measuredIndexedSchedule r 256 1 secp256k1ScheduleLength := rfl

theorem forward_measurements : (forward indexedStepProductionRegisters).measurementCount =
    (secp256k1MeasuredEEAForward indexedStepProductionRegisters).measurementCount + 241534 :=
  (congrArg AdaptiveCircuit.measurementCount (measuredMeasurements_forward_record_view indexedStepProductionRegisters)).trans
    ((measuredMeasurements_schedule_measurements_value 1 secp256k1ScheduleLength 241534
      secp256k1ScheduleLayout_production scheduleExtraRecords_total).trans
      (congrArg (fun a : AdaptiveCircuit => a.measurementCount + 241534)
        (measuredMeasurements_original_forward_record_view indexedStepProductionRegisters).symm))

private theorem measuredMeasurements_sequence_records (a x y b c d : AdaptiveCircuit) (extra : Nat)
    (h : x.measurementCount = y.measurementCount + extra) :
    ((((a.seq x).seq b).seq c).seq d).measurementCount =
      ((((a.seq y).seq b).seq c).seq d).measurementCount + extra := by
  simp only [measuredMeasurements_measurements_seq]
  omega

private theorem measuredMeasurements_wrapper_record_view : wrapper =
    ((((eeaPreprocess.seq (forward indexedStepProductionRegisters)).seq
      (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
      secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done)) := rfl
private theorem measuredMeasurements_original_wrapper_record_view : secp256k1MeasuredEEAForwardWrapper =
    ((((eeaPreprocess.seq (secp256k1MeasuredEEAForward indexedStepProductionRegisters)).seq
      (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
      secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done)) := rfl

theorem wrapper_measurements : wrapper.measurementCount =
    secp256k1MeasuredEEAForwardWrapper.measurementCount + 241534 :=
  (congrArg AdaptiveCircuit.measurementCount measuredMeasurements_wrapper_record_view).trans
    ((measuredMeasurements_sequence_records eeaPreprocess (forward indexedStepProductionRegisters)
      (secp256k1MeasuredEEAForward indexedStepProductionRegisters)
      (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)
      secp256k1EEAParityCorrection (.unitary terminalWork1Clear .done) 241534 forward_measurements).trans
      (congrArg (fun a : AdaptiveCircuit => a.measurementCount + 241534) measuredMeasurements_original_wrapper_record_view.symm))

theorem wrapperProgram_count (n start : Nat) :
    (wrapperProgram n start).1 = wrapper.measurementCount :=
  compiled_count_of_run (wrapperProgram n start) (fun _ => false) (fun _ => false)
    wrapper (wrapperProgram_run n start (fun _ => false) (fun _ => false))

theorem wrapperProgram_count_delta (n start : Nat) :
    (wrapperProgram n start).1 = (measuredForwardWrapperProgram n start).1 + 241534 :=
  (wrapperProgram_count n start).trans (wrapper_measurements.trans
    (congrArg (fun x => x + 241534)
      (compiled_count_of_run (measuredForwardWrapperProgram n start) (fun _ => false) (fun _ => false)
        secp256k1MeasuredEEAForwardWrapper
        (measuredForwardWrapperProgram_run n start (fun _ => false) (fun _ => false))).symm))
end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
/- The following ordinary private lemmas and proofs are restated from the
protected Arithmetic.InPlace source (ShorECDLP contributors, Apache-2.0).
All imports are public; no protected private declaration is accessed. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem measuredDivision_figure15_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 580 256 ++ List.range' 7 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega



private theorem measuredDivision_figure15_data_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 7 256 ++ List.range' 580 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

attribute [local irreducible] hornerMul hornerMulInverse



private theorem measuredDivision_figure15_multipliers_wellFormed :
    fig15MultiplyToWork.WellFormed ∧ fig15MultiplyToData.WellFormed ∧
      fig15MultiplyToDataInverse.WellFormed := by
  have ha : List.range' 7 256 = 7 :: List.range' 8 255 := rfl
  have hy : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  refine ⟨?_,?_,?_⟩
  · unfold fig15MultiplyToWork
    rw [ha]
    apply hornerMul_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp [secp256k1ReductionConstantBits]
    · rw [← ha]; exact measuredDivision_figure15_layout
  · unfold fig15MultiplyToData
    rw [hy]
    apply hornerMul_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp [secp256k1ReductionConstantBits]
    · rw [← hy]; exact measuredDivision_figure15_data_layout
  · unfold fig15MultiplyToDataInverse
    rw [hy]
    apply hornerMulInverse_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp only [List.length_cons,List.length_range',constantBits_length]
    · rw [← hy]; exact measuredDivision_figure15_data_layout



private theorem measuredDivision_figure15_swap_wellFormed : CircuitWellFormed fig15SwapOutput := by
  intro g hg
  simp only [fig15SwapOutput,List.mem_flatMap] at hg
  obtain ⟨i,hi,hg⟩ := hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;> norm_num [Gate.WellFormed,Nat.add_right_cancel_iff]

attribute [local irreducible] fig15MultiplyToWork fig15MultiplyToData fig15MultiplyToDataInverse
  secp256k1MeasuredEEAForwardWrapper secp256k1MeasuredEEAForwardInDataBank secp256k1MeasuredEEAReverseInDataBank



private theorem measuredDivision_figure15_unitary_wellFormed (c : Circuit) (h : CircuitWellFormed c) :
    (AdaptiveCircuit.unitary c .done).WellFormed := ⟨h,trivial⟩



private theorem measuredDivision_division_continuation_wellFormed (outcomes : List Bool) :
    (fig15DivisionAfterReset outcomes).WellFormed := by
  exact (((secp256k1MeasuredEEAInDataBank_wellFormed.2.seq measuredDivision_figure15_multipliers_wellFormed.2.1).seq
    (measuredDivision_figure15_unitary_wellFormed _ (registerZCorrection_wellFormed (List.range' 580 256) outcomes))).seq measuredDivision_figure15_multipliers_wellFormed.2.2).seq
      (measuredDivision_figure15_unitary_wellFormed _ measuredDivision_figure15_swap_wellFormed)



private theorem measuredDivision_fig15_after_eea_horner (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    HornerInputValid (List.range' 580 256) (List.range' 7 256) ShorECDLP.p 558 560 561 559
      (secp256k1EEAOutputIdealState s) := by
  have ho := secp256k1EEAOutputIdealState_correct s hs.1.1 hs.1.2.1 hs.1.2.2
  have hword : wireValues (List.range' 580 256) (secp256k1EEAOutputIdealState s) =
      wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro w hw
    exact secp256k1EEAOutputIdealState_preservesOutside s w (by simp at hw; dsimp only [Wire] at *; omega)
  refine ⟨?_,ho.2.2.2.2 558 (by decide +kernel),ho.2.2.2.2 560 (by decide +kernel),
    ho.2.2.2.2 561 (by decide +kernel),ho.2.2.2.1,?_⟩
  · intro w hw
    exact ho.2.2.1 w (by simp at hw ⊢; omega)
  · rw [hword]; exact hs.2


private theorem measuredDivision_coherent_strengthen {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State} {Valid Stronger : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) (hsub : ∀ s, Stronger s → Valid s) :
    CoherentlyImplementsOn program ideal Stronger := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (hsub s hs)),hm⟩


private theorem measuredDivision_basis_lift_ket (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by simp [ket]
attribute [local irreducible] secp256k1EEAOutputIdealState fig15WorkProductState

private theorem measuredDivision_restored_A_word (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    wireValues (List.range' 7 256) (fig15DivisionRestoredState s) =
      wireValues (List.range' 7 256) (fig15WorkProductState (secp256k1EEAOutputIdealState s)) := by
  apply List.map_congr_left
  intro w hw
  simp only [fig15DivisionRestoredState_eq s hs,if_pos hw]


private theorem measuredDivision_restored_horner (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    HornerInputValid (List.range' 7 256) (List.range' 580 256) ShorECDLP.p 558 560 561 559
      (fig15DivisionRestoredState s) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    have ha : w ∉ List.range' 7 256 := by simp at hw ⊢; omega
    simp only [fig15DivisionRestoredState_eq s hs,if_neg ha,if_pos hw]
  · simpa [fig15DivisionRestoredState_eq s hs] using hs.1.1 558 (by decide +kernel)
  · simpa [fig15DivisionRestoredState_eq s hs] using hs.1.1 560 (by decide +kernel)
  · simpa [fig15DivisionRestoredState_eq s hs] using hs.1.1 561 (by decide +kernel)
  · simpa [fig15DivisionRestoredState_eq s hs] using hs.1.1 559 (by decide +kernel)
  · rw [measuredDivision_restored_A_word s hs,(fig15WorkProductState_correct _ (measuredDivision_fig15_after_eea_horner s hs)).1]
    exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos

private theorem measuredDivision_phase_congr (targets : List Wire) (outcomes : List Bool) (s t : BasisState)
    (h : wireValues targets s = wireValues targets t) :
    registerXPhase targets outcomes s = registerXPhase targets outcomes t := by
  induction targets generalizing outcomes with
  | nil => rfl
  | cons w ws ih =>
    cases outcomes with
    | nil => rfl
    | cons b bs =>
      simp only [wireValues,List.map_cons,List.cons.injEq] at h
      simp only [registerXPhase,h.1,ih bs h.2]

private def measuredDivision_divisionResetValid (t : BasisState) : Prop :=
  ∃ s, Secp256k1InPlaceInputValid s ∧
    t = clearRegister (List.range' 580 256) (fig15WorkProductState (secp256k1EEAOutputIdealState s))


private def measuredDivision_divisionRestoreMap : State →ₗ[ℂ] State :=
  (relabelState eeaWorkspaceExchange).comp
    ((Finsupp.lmapDomain ℂ ℂ secp256k1EEAReverseWrapperIdealState).comp
      (relabelState eeaWorkspaceExchange.symm))


private def measuredDivision_divisionRecomputeMap : State →ₗ[ℂ] State :=
  (Finsupp.lmapDomain ℂ ℂ fig15DataProductState).comp measuredDivision_divisionRestoreMap


private def measuredDivision_divisionCorrectMap (outcomes : List Bool) : State →ₗ[ℂ] State :=
  (Quantum.run (registerZCorrection (List.range' 580 256) outcomes)).comp measuredDivision_divisionRecomputeMap


private def measuredDivision_divisionUncomputeMap (outcomes : List Bool) : State →ₗ[ℂ] State :=
  (Finsupp.lmapDomain ℂ ℂ (hornerClearOutput (List.range' 580 256))).comp (measuredDivision_divisionCorrectMap outcomes)


private theorem measuredDivision_division_restore_ket (s : BasisState) :
    measuredDivision_divisionRestoreMap (ket (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      ket (fig15DivisionRestoredState s) := by
  simp only [measuredDivision_divisionRestoreMap,LinearMap.comp_apply,relabelState_ket,measuredDivision_basis_lift_ket,
    fig15DivisionRestoredState]


private theorem measuredDivision_division_recompute_ket (s : BasisState) :
    measuredDivision_divisionRecomputeMap (ket (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      ket (fig15DataProductState (fig15DivisionRestoredState s)) := by
  simp only [measuredDivision_divisionRecomputeMap,LinearMap.comp_apply,measuredDivision_division_restore_ket,measuredDivision_basis_lift_ket]


private theorem measuredDivision_division_correct_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    measuredDivision_divisionCorrectMap outcomes (ket (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (fig15DataProductState (fig15DivisionRestoredState s)) := by
  simp only [measuredDivision_divisionCorrectMap,LinearMap.comp_apply,measuredDivision_division_recompute_ket,
    fig15DivisionRecompute_phase s hs]


private theorem measuredDivision_supported_phase {Valid : BasisState → Prop} (s : BasisState)
    (c : ℂ) (hs : Valid s) : SupportedOn Valid (c • ket s) := by
  intro t ht
  have hts : s=t := by
    by_contra h
    apply ht
    simp only [Finsupp.smul_apply,ket_ne h,smul_zero]
  subst t
  exact hs


private theorem measuredDivision_division_uncompute_state (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    hornerClearOutput (List.range' 580 256)
      (fig15DataProductState (fig15DivisionRestoredState s)) = fig15DivisionRestoredState s := by
  funext w
  by_cases hw : w ∈ List.range' 580 256
  · simp only [hornerClearOutput,if_pos hw]
    exact ((measuredDivision_restored_horner s hs).1 w hw).symm
  · simp only [hornerClearOutput,if_neg hw]
    exact (fig15DataProductState_correct _ (measuredDivision_restored_horner s hs)).2 w hw


private theorem measuredDivision_division_uncompute_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    measuredDivision_divisionUncomputeMap outcomes (ket (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      registerXPhase (List.range' 580 256) outcomes s • ket (fig15DivisionRestoredState s) := by
  simp only [measuredDivision_divisionUncomputeMap,LinearMap.comp_apply,measuredDivision_division_correct_ket s hs,
    map_smul,measuredDivision_basis_lift_ket,measuredDivision_division_uncompute_state s hs]


private theorem measuredDivision_division_continuation_coherent (outcomes : List Bool) :
    CoherentlyImplementsOn (fig15DivisionAfterReset outcomes)
      ((Quantum.run fig15SwapOutput).comp (measuredDivision_divisionUncomputeMap outcomes)) measuredDivision_divisionResetValid := by
  have hr : CoherentlyImplementsOn secp256k1MeasuredEEAReverseInDataBank measuredDivision_divisionRestoreMap measuredDivision_divisionResetValid := by
    apply measuredDivision_coherent_strengthen secp256k1MeasuredEEAReverseInDataBank_coherent_localImage
    rintro t ⟨s,hs,rfl⟩
    exact fig15DivisionReset_inverseReady s hs
  have hm := hr.seq fig15MultiplyToData_coherent (by
    rintro t ⟨s,hs,rfl⟩
    rw [measuredDivision_division_restore_ket]
    exact supportedOn_ket _ _ (measuredDivision_restored_horner s hs))
  have hz := hm.seq (CoherentlyImplementsOn.unitary
    (registerZCorrection (List.range' 580 256) outcomes) (fun _ => True)) (by
      intro t ht u hu; trivial)
  have hi := hz.seq fig15MultiplyToDataInverse_coherent (by
    rintro t ⟨s,hs,rfl⟩
    change SupportedOn _ (measuredDivision_divisionCorrectMap outcomes _)
    rw [measuredDivision_division_correct_ket s hs]
    exact measuredDivision_supported_phase _ _ ⟨fig15DivisionRestoredState s,measuredDivision_restored_horner s hs,rfl⟩)
  exact hi.seq (CoherentlyImplementsOn.unitary fig15SwapOutput (fun _ => True))
    (by intro t ht u hu; trivial)


private def measuredDivision_divisionPreparedValid (t : BasisState) : Prop :=
  ∃ s, Secp256k1InPlaceInputValid s ∧ t = fig15WorkProductState (secp256k1EEAOutputIdealState s)


private def measuredDivision_divisionPreparedOutput (t : BasisState) : BasisState :=
  Classical.run fig15SwapOutput (relabelBasis eeaWorkspaceExchange
    (secp256k1EEAReverseWrapperIdealState (relabelBasis eeaWorkspaceExchange.symm
      (clearRegister (List.range' 580 256) t))))


private theorem measuredDivision_division_prepared_phase (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    registerXPhase (List.range' 580 256) outcomes
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)) =
      registerXPhase (List.range' 580 256) outcomes s := by
  apply measuredDivision_phase_congr
  apply List.map_congr_left
  intro w hw
  rw [(fig15WorkProductState_correct _ (measuredDivision_fig15_after_eea_horner s hs)).2 w (by simp at hw ⊢; omega)]
  exact secp256k1EEAOutputIdealState_preservesOutside s w (by simp at hw; dsimp only [Wire] at *; omega)


private def measuredDivision_divisionWitness : BasisState := fun w => decide (w = 263)


private theorem measuredDivision_divisionWitness_valid : Secp256k1InPlaceInputValid measuredDivision_divisionWitness := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro w hw
    simp only [List.mem_append,List.mem_range'_1] at hw
    simp only [measuredDivision_divisionWitness, decide_eq_false_iff_not]
    dsimp only [Wire] at *
    omega
  · decide +kernel
  · decide +kernel
  · decide +kernel


private theorem measuredDivision_division_swap_hp : Classical.HPFree fig15SwapOutput := by
  intro g hg
  simp only [fig15SwapOutput,List.mem_flatMap] at hg
  obtain ⟨i,hi,hg⟩ := hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;> trivial
attribute [local irreducible] Classical.run Quantum.run relabelBasis measureResetThen fig15DivisionAfterReset
  measuredDivision_divisionPreparedOutput measuredDivision_divisionUncomputeMap


private theorem measuredDivision_division_prepared_output (s : BasisState) :
    measuredDivision_divisionPreparedOutput (fig15WorkProductState (secp256k1EEAOutputIdealState s)) =
      Classical.run fig15SwapOutput (fig15DivisionRestoredState s) := by
  delta measuredDivision_divisionPreparedOutput fig15DivisionRestoredState
  exact Eq.refl _


private theorem measuredDivision_division_final_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    ((Quantum.run fig15SwapOutput).comp (measuredDivision_divisionUncomputeMap outcomes))
      (ket (clearRegister (List.range' 580 256) (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (measuredDivision_divisionPreparedOutput (fig15WorkProductState (secp256k1EEAOutputIdealState s))) := by
  rw [LinearMap.comp_apply,measuredDivision_division_uncompute_ket s hs,map_smul,
    run_ket_agrees_classical _ _ measuredDivision_division_swap_hp,measuredDivision_division_prepared_output]


private theorem measuredDivision_division_reset_correct (outcomes : List Bool) (t : BasisState)
    (ht : measuredDivision_divisionPreparedValid t) :
    measuredDivision_divisionResetValid (clearRegister (List.range' 580 256) t) ∧
    ((Quantum.run fig15SwapOutput).comp (measuredDivision_divisionUncomputeMap outcomes))
      (ket (clearRegister (List.range' 580 256) t)) =
      registerXPhase (List.range' 580 256) outcomes t • ket (measuredDivision_divisionPreparedOutput t) := by
  obtain ⟨s,hs,rfl⟩ := ht
  refine ⟨⟨s,hs,rfl⟩,?_⟩
  rw [measuredDivision_division_prepared_phase s hs]
  exact measuredDivision_division_final_ket s hs outcomes


private theorem measuredDivision_division_reset_coherent :
    CoherentlyImplementsOn (measureResetThen (List.range' 580 256) fig15DivisionAfterReset)
      (Finsupp.lmapDomain ℂ ℂ measuredDivision_divisionPreparedOutput) measuredDivision_divisionPreparedValid :=
  measureResetThen_coherent (List.range' 580 256) fig15DivisionAfterReset
    (fun outcomes => (Quantum.run fig15SwapOutput).comp (measuredDivision_divisionUncomputeMap outcomes))
    (fun _ => measuredDivision_divisionResetValid) measuredDivision_divisionPreparedValid measuredDivision_divisionPreparedOutput List.nodup_range'
    (fun outcomes _ => measuredDivision_division_continuation_wellFormed outcomes)
    measuredDivision_division_continuation_coherent (fun outcomes _ t ht => measuredDivision_division_reset_correct outcomes t ht)
    (fig15WorkProductState (secp256k1EEAOutputIdealState measuredDivision_divisionWitness))
    ⟨measuredDivision_divisionWitness,measuredDivision_divisionWitness_valid,rfl⟩

end
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Entrant.MeasuredQuotient
open Classical Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] wrapper fig15MultiplyToWork secp256k1EEAOutputIdealState
  fig15WorkProductState measureResetThen fig15DivisionAfterReset

def division : AdaptiveCircuit :=
  (wrapper.seq fig15MultiplyToWork).seq
    (measureResetThen (List.range' 580 256) fig15DivisionAfterReset)

theorem divisionPrefix_coherent :
    CoherentlyImplementsOn (wrapper.seq fig15MultiplyToWork)
      (Finsupp.lmapDomain ℂ ℂ (fun s => fig15WorkProductState (secp256k1EEAOutputIdealState s)))
      Secp256k1InPlaceInputValid := by
  have hf := measuredDivision_coherent_strengthen wrapper_coherent
    (Stronger := Secp256k1InPlaceInputValid) (fun s hs => hs.1)
  have hc := hf.seq fig15MultiplyToWork_coherent (by
    intro s hs
    rw [measuredDivision_basis_lift_ket]
    exact supportedOn_ket _ _ (measuredDivision_fig15_after_eea_horner s hs))
  apply hc.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,measuredDivision_basis_lift_ket]

theorem division_coherent :
    CoherentlyImplementsOn division
      (Finsupp.lmapDomain ℂ ℂ fig15DivisionOutputState) Secp256k1InPlaceInputValid := by
  have h := divisionPrefix_coherent.seq measuredDivision_division_reset_coherent (by
    intro s hs
    rw [measuredDivision_basis_lift_ket]
    exact supportedOn_ket _ _ ⟨s,hs,rfl⟩)
  apply h.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,measuredDivision_basis_lift_ket]
  delta measuredDivision_divisionPreparedOutput fig15DivisionOutputState fig15DivisionRestoredState
  rfl

attribute [local irreducible] wrapperProgram divisionAfterResetProgram

def divisionProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let eea := wrapperProgram n start
  let first := appendCompiled eea (multiplyWorkProgram n (start+eea.1))
  appendCompiled first (collectProgram n (divisionAfterResetProgram n)
    (List.range' 580 256) (start+first.1) ([] : List (Fin _)))

theorem divisionProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (divisionProgram n start) read history = division.run := by
  unfold divisionProgram division
  apply appendCompiled_run_eq
  · apply appendCompiled_run_eq
    · exact wrapperProgram_run n start read history
    · intro h; exact multiplyWorkProgram_run n _ read h
  · intro h
    exact collectProgram_run n (divisionAfterResetProgram n) fig15DivisionAfterReset read
      (fun cursor prior h => divisionAfterResetProgram_run n cursor prior read h) _ _ ([] : List (Fin _)) h

theorem divisionProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (divisionProgram n start) read history = division.tCount := by
  unfold divisionProgram division
  apply appendCompiled_tCount_eq
  · apply appendCompiled_tCount_eq
    · exact wrapperProgram_tCount n start read history
    · intro h; exact multiplyWorkProgram_tCount n _ read h
  · intro h
    exact collectProgram_tCount n (divisionAfterResetProgram n) fig15DivisionAfterReset read
      (fun cursor prior h => divisionAfterResetProgram_tCount n cursor prior read h) _ _ ([] : List (Fin _)) h
end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem measuredDivisionCost_measurements_seq (a b : AdaptiveCircuit) :
    (a.seq b).measurementCount = a.measurementCount + b.measurementCount := by
  induction a with
  | done => simp only [AdaptiveCircuit.seq,AdaptiveCircuit.measurementCount,Nat.zero_add]
  | unitary gs a ih => simpa only [AdaptiveCircuit.seq,AdaptiveCircuit.measurementCount] using ih
  | xMeasureReset w a b iha ihb =>
    simp only [AdaptiveCircuit.seq,AdaptiveCircuit.measurementCount,iha,ihb,Nat.add_max_add_right]
    omega

private theorem measuredDivisionCost_source_view : division =
    (wrapper.seq fig15MultiplyToWork).seq
      (measureResetThen (List.range' 580 256) fig15DivisionAfterReset) := rfl
private theorem measuredDivisionCost_original_view : secp256k1InPlaceDivision =
    (secp256k1MeasuredEEAForwardWrapper.seq fig15MultiplyToWork).seq
      (measureResetThen (List.range' 580 256) fig15DivisionAfterReset) := rfl

private theorem measuredDivisionCost_sequence_saving (x y a b : AdaptiveCircuit) (saving : Nat)
    (h : x.tCount + saving = y.tCount) :
    ((x.seq a).seq b).tCount + saving = ((y.seq a).seq b).tCount := by
  simp only [adaptive_tCount_seq]
  omega
private theorem measuredDivisionCost_sequence_records (x y a b : AdaptiveCircuit) (extra : Nat)
    (h : x.measurementCount = y.measurementCount + extra) :
    ((x.seq a).seq b).measurementCount = ((y.seq a).seq b).measurementCount + extra := by
  simp only [measuredDivisionCost_measurements_seq]
  omega
attribute [local irreducible] AdaptiveCircuit.tCount AdaptiveCircuit.measurementCount

theorem division_saving : division.tCount + 1690738 = secp256k1InPlaceDivision.tCount :=
  (congrArg (fun a : AdaptiveCircuit => a.tCount + 1690738) measuredDivisionCost_source_view).trans
    ((measuredDivisionCost_sequence_saving wrapper secp256k1MeasuredEEAForwardWrapper fig15MultiplyToWork
      (measureResetThen (List.range' 580 256) fig15DivisionAfterReset) 1690738 wrapper_saving).trans
      (congrArg AdaptiveCircuit.tCount measuredDivisionCost_original_view).symm)

theorem division_measurements : division.measurementCount =
    secp256k1InPlaceDivision.measurementCount + 241534 :=
  (congrArg AdaptiveCircuit.measurementCount measuredDivisionCost_source_view).trans
    ((measuredDivisionCost_sequence_records wrapper secp256k1MeasuredEEAForwardWrapper fig15MultiplyToWork
      (measureResetThen (List.range' 580 256) fig15DivisionAfterReset) 241534 wrapper_measurements).trans
      (congrArg (fun a : AdaptiveCircuit => a.measurementCount + 241534) measuredDivisionCost_original_view.symm))

theorem division_T : division.tCount = 244370665 := by
  have h := division_saving
  rw [secp256k1InPlaceDivision_T] at h
  omega

theorem division_measurementCount : division.measurementCount = 14948841 :=
  division_measurements.trans (congrArg (fun x => x+241534) secp256k1InPlaceDivision_measurements)

theorem divisionProgram_count (n start : Nat) :
    (divisionProgram n start).1 = division.measurementCount :=
  compiled_count_of_run (divisionProgram n start) (fun _ => false) (fun _ => false)
    division (divisionProgram_run n start (fun _ => false) (fun _ => false))

theorem divisionProgram_count_delta (n start : Nat) :
    (divisionProgram n start).1 = (ChallengeMigration.divisionProgram n start).1 + 241534 :=
  (divisionProgram_count n start).trans (division_measurements.trans
    (congrArg (fun x => x + 241534)
      (compiled_count_of_run (ChallengeMigration.divisionProgram n start) (fun _ => false) (fun _ => false)
        secp256k1InPlaceDivision
        (ChallengeMigration.divisionProgram_run n start (fun _ => false) (fun _ => false))).symm))

theorem divisionProgram_saving (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (divisionProgram n start) read history + 1690738 =
      compiledTCount (ChallengeMigration.divisionProgram n start) read history :=
  (congrArg (fun x => x + 1690738) (divisionProgram_tCount n start read history)).trans
    (division_saving.trans (ChallengeMigration.divisionProgram_tCount n start read history).symm)
end
end ShorECDLP.Entrant.MeasuredQuotient

end

section
namespace ShorECDLP.Entrant.MeasuredQuotient
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem measuredSourceSupport_circuitWires_append (a b : Circuit) :
    circuitWires (a++b) = circuitWires a ++ circuitWires b := List.flatMap_append
private theorem measuredSourceSupport_seq_support_mono {a b c d : AdaptiveCircuit}
    (ha : a.wires ⊆ c.wires) (hb : b.wires ⊆ d.wires) :
    (a.seq b).wires ⊆ (c.seq d).wires := by
  intro w hw
  simp only [modularWires_seq] at hw ⊢
  exact hw.imp (fun h => ha h) (fun h => hb h)

private theorem measuredSourceSupport_erase_wires (a b t : Wire) :
    (eraseZeroAnd a b t).wires ⊆ circuitWires (computeZeroAnd a b t) := by
  simp [eraseZeroAnd,measuredAndErase,measureResetWithCorrection,measuredAndCorrection,
    controlledZ,AdaptiveCircuit.seq,AdaptiveCircuit.wires,computeZeroAnd,circuitWires,gateWires]

theorem unary_wires_subset (order : UnaryOrder) (leaf : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (path : List Wire) :
    (unaryAction order leaf tree control path).wires ⊆
      circuitWires (unaryActionUnitary order leaf tree control path) := by
  induction tree generalizing control path with
  | leaf l => simp [unaryAction,unaryActionUnitary,AdaptiveCircuit.wires]
  | node bit zero one ihz iho =>
    cases path with
    | nil => simp [unaryAction,unaryActionUnitary,AdaptiveCircuit.wires,circuitWires]
    | cons p ps =>
      have hz := ihz p ps
      have ho := iho p ps
      have he := measuredSourceSupport_erase_wires control bit p
      intro w hw
      cases order <;>
        simp only [unaryAction,unaryActionUnitary,AdaptiveCircuit.wires,modularWires_seq,
          measuredSourceSupport_circuitWires_append,List.mem_append] at hw ⊢
      all_goals
        simp only [List.subset_def] at hz ho he
        tauto

theorem quotient_wires_subset (r : QuotientSwapRegisters) (k K : Nat) :
    (quotientSwap r k K).wires ⊆ circuitWires (quotientSwapUnitary r k K) := by
  have ht := unary_wires_subset .inc (quotientSwapLeaf r k) (quotientSwapTree r k K)
    r.control (r.path k K)
  intro w hw
  simp only [quotientSwap,quotientSwapUnitary,modularWires_seq,AdaptiveCircuit.wires,
    measuredSourceSupport_circuitWires_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
  simp only [List.subset_def] at ht
  tauto

theorem d2_wires_subset (r : IndexedStepRegisters) (w : ActiveWindow) :
    (blockD2 r w).wires ⊆ circuitWires (blockD2Forward r w) := by
  have ht := quotient_wires_subset (r.quotient w) w.start w.stop
  change (blockD2 r w).wires ⊆
    circuitWires ((before r ++ quotientSwapUnitary (r.quotient w) w.start w.stop) ++ after r)
  intro q hq
  simp only [blockD2,modularWires_seq,AdaptiveCircuit.wires,measuredSourceSupport_circuitWires_append,
    List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  simp only [List.subset_def] at ht
  tauto

theorem d_wires_subset (r : IndexedStepRegisters) (w : ActiveWindow) :
    (blockD r w).wires ⊆ circuitWires (blockDForward r w) := by
  have ht := d2_wires_subset r w
  intro q hq
  simp only [blockD,blockDForward,modularWires_seq,AdaptiveCircuit.wires,measuredSourceSupport_circuitWires_append,
    List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  simp only [List.subset_def] at ht
  tauto

theorem step_wires_subset (r : IndexedStepRegisters) (width T : Nat) :
    (step r width T).wires ⊆ (measuredIndexedStep r width T).wires := by
  have ht := d_wires_subset r (certifiedActiveWindows width T).quotientSwap
  rw [← stepSources_eq,← measuredStepSources_eq]
  intro q hq
  simp only [stepSources,measuredStepSources,sequenceCircuit,blockCD,modularWires_seq,
    AdaptiveCircuit.wires,measuredSourceSupport_circuitWires_append,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  simp only [List.subset_def] at ht
  tauto

attribute [local irreducible] step measuredIndexedStep

theorem schedule_wires_subset (r : IndexedStepRegisters) (width first count : Nat) :
    (schedule r width first count).wires ⊆ (measuredIndexedSchedule r width first count).wires := by
  induction count generalizing first with
  | zero => simp [schedule,measuredIndexedSchedule,AdaptiveCircuit.wires,circuitWires]
  | succ count ih =>
    simpa only [schedule,measuredIndexedSchedule] using
      measuredSourceSupport_seq_support_mono (step_wires_subset r width first) (ih (first+1))

attribute [local irreducible] schedule measuredIndexedSchedule AdaptiveCircuit.wires
private theorem measuredSourceSupport_forward_view (r : IndexedStepRegisters) :
    forward r = schedule r 256 1 secp256k1ScheduleLength := rfl
private theorem measuredSourceSupport_old_forward_view (r : IndexedStepRegisters) :
    secp256k1MeasuredEEAForward r = measuredIndexedSchedule r 256 1 secp256k1ScheduleLength := rfl

theorem forward_wires_subset (r : IndexedStepRegisters) :
    (forward r).wires ⊆ (secp256k1MeasuredEEAForward r).wires := by
  rw [measuredSourceSupport_forward_view,measuredSourceSupport_old_forward_view]
  exact schedule_wires_subset r 256 1 secp256k1ScheduleLength

private theorem measuredSourceSupport_wrapper_view : wrapper =
    ((((eeaPreprocess.seq (forward indexedStepProductionRegisters)).seq
      (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
      secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done)) := rfl
private theorem measuredSourceSupport_old_wrapper_view : secp256k1MeasuredEEAForwardWrapper =
    ((((eeaPreprocess.seq (secp256k1MeasuredEEAForward indexedStepProductionRegisters)).seq
      (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
      secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done)) := rfl

theorem wrapper_wires_subset : wrapper.wires ⊆ secp256k1MeasuredEEAForwardWrapper.wires := by
  rw [measuredSourceSupport_wrapper_view,measuredSourceSupport_old_wrapper_view]
  exact measuredSourceSupport_seq_support_mono (measuredSourceSupport_seq_support_mono (measuredSourceSupport_seq_support_mono
    (measuredSourceSupport_seq_support_mono (List.Subset.refl _) (forward_wires_subset indexedStepProductionRegisters))
      (List.Subset.refl _)) (List.Subset.refl _)) (List.Subset.refl _)

private theorem measuredSourceSupport_division_view : division =
    (wrapper.seq fig15MultiplyToWork).seq
      (measureResetThen (List.range' 580 256) fig15DivisionAfterReset) := rfl
private theorem measuredSourceSupport_old_division_view : secp256k1InPlaceDivision =
    (secp256k1MeasuredEEAForwardWrapper.seq fig15MultiplyToWork).seq
      (measureResetThen (List.range' 580 256) fig15DivisionAfterReset) := rfl

theorem division_wires_subset : division.wires ⊆ secp256k1InPlaceDivision.wires := by
  rw [measuredSourceSupport_division_view,measuredSourceSupport_old_division_view]
  exact measuredSourceSupport_seq_support_mono (measuredSourceSupport_seq_support_mono wrapper_wires_subset (List.Subset.refl _)) (List.Subset.refl _)

theorem division_wires_bound : division.wires ⊆ List.range 836 :=
  division_wires_subset.trans secp256k1InPlaceDivision_wires_subset
end
end ShorECDLP.Entrant.MeasuredQuotient

end
