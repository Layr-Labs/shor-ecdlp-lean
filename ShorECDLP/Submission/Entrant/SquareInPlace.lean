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
