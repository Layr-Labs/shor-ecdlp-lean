import ShorECDLP.Submission.Entrant.Shift.Tail
import ShorECDLP.Challenge.Decoder
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! EDITABLE. Averaged success of a coarse half-bin readout.

The right phase register has `R + e` qubits, carries the phase `l / r + 1 / 2^(R+1)`, and only
its top `R` bits `b / 2^e` are decoded with the protected `wrappedNumerators` interval.
For every numerator `l` the QPE peak sits at offset `δ_l = 2^e frac((2^(R+1) l + r) / (2 r))`
inside the decoding window of width `W = 2^e`; the window tail is controlled by `Tail.lean`.
As `l` ranges over `1, …, r - 1` the offsets are distinct odd multiples of `W / (2 r)`, so on
average only `O(log W / W)` of the mass misses the window. -/

namespace ShorECDLP.Entrant

namespace WindowMassProof

open Finset

/-! ## Counting -/

lemma card_le_of_spread (S : Finset ℕ) (D : ℕ) (h : ∀ a ∈ S, ∀ b ∈ S, b ≤ a + D) :
    S.card ≤ D + 1 := by
  rcases S.eq_empty_or_nonempty with h0 | hne
  · simp [h0]
  · have hsub : S ⊆ Finset.Icc (S.min' hne) (S.min' hne + D) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨S.min'_le x hx, h _ (S.min'_mem hne) x hx⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    omega

lemma fiber_card (r W m : ℕ) (hr : 0 < r) (hW : 0 < W) :
    ((range r).filter (fun t => W * (2 * t + 1) / (2 * r) = m)).card ≤ (r - 1) / W + 1 := by
  apply card_le_of_spread
  intro a ha b hb
  simp only [mem_filter, mem_range] at ha hb
  have h2r : 0 < 2 * r := by omega
  have h1 : m * (2 * r) ≤ W * (2 * a + 1) := by
    rw [← ha.2]; exact Nat.div_mul_le_self _ _
  have h2 : W * (2 * b + 1) < (2 * r) * (m + 1) := by
    rw [← hb.2]; exact Nat.lt_mul_div_succ _ h2r
  rcases le_or_gt b a with hba | hba
  · exact Nat.le_add_right_of_le hba
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hba.le
    have hk : W * k < r := by
      have h1' : ((m * (2 * r) : ℕ) : ℤ) ≤ ((W * (2 * a + 1) : ℕ) : ℤ) := by exact_mod_cast h1
      have h2' : ((W * (2 * (a + k) + 1) : ℕ) : ℤ) < (((2 * r) * (m + 1) : ℕ) : ℤ) := by
        exact_mod_cast h2
      push_cast at h1' h2'
      have : (W : ℤ) * k < r := by nlinarith
      exact_mod_cast this
    have : k ≤ (r - 1) / W := by
      rw [Nat.le_div_iff_mul_le hW]
      rw [Nat.mul_comm]
      omega
    omega

/-- The offset index of numerator `l`: `(2^(R+1) l + r) mod 2 r = 2 t + 1`. -/
def offsetIndex (r R l : ℕ) : ℕ := ((2 ^ (R + 1) * l + r) % (2 * r)) / 2

lemma offset_odd (r R l : ℕ) (hr : r % 2 = 1) :
    (2 ^ (R + 1) * l + r) % (2 * r) = 2 * offsetIndex r R l + 1 := by
  have hev : (2 ^ (R + 1) * l) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero R)) l)
  have h1 : (2 ^ (R + 1) * l + r) % (2 * r) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 r)]
    omega
  unfold offsetIndex
  omega

lemma offsetIndex_lt (r R l : ℕ) (hr : 0 < r) (hr1 : r % 2 = 1) : offsetIndex r R l < r := by
  have h := offset_odd r R l hr1
  have hlt : (2 ^ (R + 1) * l + r) % (2 * r) < 2 * r := Nat.mod_lt _ (by omega)
  omega

lemma offsetIndex_injOn (r R : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    Set.InjOn (offsetIndex r R) (Finset.Ico 1 r : Set ℕ) := by
  have hodd : r % 2 = 1 := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
  intro l hl l' hl' heq
  simp only [Finset.coe_Ico, Set.mem_Ico] at hl hl'
  have h1 := offset_odd r R l hodd
  have h2 := offset_odd r R l' hodd
  have hmod : 2 ^ (R + 1) * l + r ≡ 2 ^ (R + 1) * l' + r [MOD 2 * r] := by
    unfold Nat.ModEq; rw [h1, h2, heq]
  have hm2 := (Nat.ModEq.add_right_cancel' r hmod).of_mul_left 2
  have hcop : Nat.gcd r (2 ^ (R + 1)) = 1 := by
    have : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
    exact (Nat.Coprime.pow_right (R + 1) this.symm)
  have hl3 := Nat.ModEq.cancel_left_of_coprime hcop hm2
  unfold Nat.ModEq at hl3
  rwa [Nat.mod_eq_of_lt hl.2, Nat.mod_eq_of_lt hl'.2] at hl3

/-! ## The decoding window -/

lemma mem_numeratorInterval (r R l : ℕ) (hr : 0 < r) :
    l ∈ Challenge.numeratorInterval r R ((2 ^ (R + 1) * l + r) / (2 * r)) := by
  set A := 2 ^ (R + 1) * l + r with hA
  set v := A / (2 * r) with hv
  have h2r : 0 < 2 * r := by omega
  have h1 : v * (2 * r) ≤ A := Nat.div_mul_le_self _ _
  have h2 : A < (2 * r) * (v + 1) := Nat.lt_mul_div_succ _ h2r
  have hP : 2 ^ (R + 1) = 2 * 2 ^ R := by rw [pow_succ, Nat.mul_comm]
  unfold Challenge.numeratorInterval
  rw [Finset.mem_Icc]
  have hX : 2 * 2 ^ R * l = 2 ^ (R + 1) * l := by rw [hP]
  constructor
  · apply Nat.div_le_of_le_mul
    have : 2 * r * v ≤ A := by rw [Nat.mul_comm (2 * r)]; exact h1
    rw [Nat.mul_comm (2 * 2 ^ R) l] at hX ⊢
    rw [hX]
    omega
  · rw [Nat.le_div_iff_mul_le (by positivity)]
    have : A < 2 * r * v + 2 * r := by
      have := h2; rw [Nat.mul_add, Nat.mul_one] at this; linarith
    rw [Nat.mul_comm l, hX]
    omega

lemma ampSq_sub_one (N : ℕ) (β : ℝ) (a : ℕ) : ampSq N (β - 1) a = ampSq N β a := by
  have h : ∀ x : ℝ, Complex.exp (Complex.I * ((2 * Real.pi * (x - 1) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
    intro x
    have e : Complex.I * ((2 * Real.pi * (x - 1) : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) - 2 * Real.pi * Complex.I := by
      push_cast; ring
    rw [e, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  unfold ampSq
  rw [show β - 1 - (a : ℝ) / (N : ℝ) = (β - (a : ℝ) / N) - 1 by ring, h]

lemma ampSq_nonneg (N : ℕ) (β : ℝ) (a : ℕ) : 0 ≤ ampSq N β a := Complex.normSq_nonneg _

/-- Capped tail bound at peak offset `δ` in a window of width `W`. -/
noncomputable def capTail (W N δ : ℝ) : ℝ :=
  if 1 ≤ δ ∧ δ ≤ W - 2 then min 1 (203 / 1000 * (1 / δ + 1 / (W - 1 - δ)) + 2 / N) else 1

lemma capTail_nonneg (W N δ : ℝ) (hN : 0 < N) : 0 ≤ capTail W N δ := by
  unfold capTail
  split_ifs with h
  · apply le_min zero_le_one
    have : 0 < δ := by linarith [h.1]
    have : 0 < W - 1 - δ := by linarith [h.2]
    positivity
  · exact zero_le_one

lemma capTail_le_one (W N δ : ℝ) : capTail W N δ ≤ 1 := by
  unfold capTail
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- The right-register phase of numerator `l`. -/
noncomputable def shiftPhase (r R l : ℕ) : ℝ := (l : ℝ) / r + 1 / 2 ^ (R + 1)

set_option maxHeartbeats 1000000 in
lemma fail_le (r R e l : ℕ) (hr : 0 < r) (hl : l < r) :
    ∑ b ∈ range (2 ^ (R + e)), (if l ∈ Challenge.wrappedNumerators r R (b / 2 ^ e) then 0
        else ampSq (2 ^ (R + e)) (shiftPhase r R l) b) ≤
      capTail ((2 ^ e : ℕ) : ℝ) ((2 ^ (R + e) : ℕ) : ℝ)
        (((2 ^ e : ℕ) : ℝ) * (((2 ^ (R + 1) * l + r) % (2 * r) : ℕ) : ℝ) / (2 * r)) := by
  classical
  have hPpos : 0 < 2 ^ R := by positivity
  have hWpos : 0 < 2 ^ e := by positivity
  have hNPW : 2 ^ (R + e) = 2 ^ R * 2 ^ e := pow_add 2 R e
  obtain ⟨v0, hv0⟩ : ∃ v0, v0 = (2 ^ (R + 1) * l + r) / (2 * r) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = (2 ^ (R + 1) * l + r) % (2 * r) := ⟨_, rfl⟩
  rw [← hj]
  have hAdiv : 2 * r * v0 + j = 2 ^ (R + 1) * l + r := by
    rw [hv0, hj]; exact Nat.div_add_mod _ _
  have hv0le : v0 ≤ 2 ^ R := by
    rw [hv0]
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have h1 : 2 ^ R * l < 2 ^ R * r := Nat.mul_lt_mul_of_pos_left hl hPpos
    rw [pow_succ]
    nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set δ : ℝ := ((2 ^ e : ℕ) : ℝ) * (j : ℝ) / (2 * r) with hδ
  have hAR : (2 * (r : ℝ) * v0 + j) = 2 ^ (R + 1) * l + r := by exact_mod_cast hAdiv
  have hident : ((2 ^ (R + e) : ℕ) : ℝ) * shiftPhase r R l = (2 : ℝ) ^ e * v0 + δ := by
    push_cast
    calc (2 : ℝ) ^ (R + e) * shiftPhase r R l =
          2 ^ e * ((2 ^ (R + 1) * l + r) / (2 * r)) := by
          unfold shiftPhase; rw [pow_add, pow_succ]; field_simp
      _ = 2 ^ e * ((2 * r * v0 + j) / (2 * r)) := by rw [hAR]
      _ = 2 ^ e * v0 + δ := by rw [hδ]; push_cast; field_simp
  have hfail1 : ∑ b ∈ range (2 ^ (R + e)), (if l ∈ Challenge.wrappedNumerators r R (b / 2 ^ e)
      then 0 else ampSq (2 ^ (R + e)) (shiftPhase r R l) b) ≤ 1 := by
    calc _ ≤ ∑ b ∈ range (2 ^ (R + e)), ampSq (2 ^ (R + e)) (shiftPhase r R l) b := by
          apply sum_le_sum; intro b _; split_ifs
          · exact ampSq_nonneg _ _ _
          · exact le_rfl
      _ = 1 := parseval _ (by positivity) _
  have hm := mem_numeratorInterval r R l hr
  rw [← hv0] at hm
  unfold capTail
  split_ifs with hδr
  · refine le_min hfail1 ?_
    have hgoal : (203 / 1000 : ℝ) * (1 / δ + 1 / (((2 ^ e : ℕ) : ℝ) - 1 - δ)) +
        2 / ((2 ^ (R + e) : ℕ) : ℝ) =
        406 / 1000 / 2 * (1 / δ + 1 / (((2 ^ e : ℕ) : ℝ) - 1 - δ)) +
          2 / ((2 ^ (R + e) : ℕ) : ℝ) := by
      ring
    rw [hgoal]
    rcases lt_or_eq_of_le hv0le with hlt | heq
    · -- the window `[2^e v0, 2^e v0 + 2^e)` lies inside the register range
      have hsW : 2 ^ e * v0 + 2 ^ e ≤ 2 ^ (R + e) := by
        rw [hNPW]; nlinarith
      have ht := window_tail (2 ^ (R + e)) (2 ^ e) (2 ^ e * v0) ((2 : ℝ) ^ e * v0 + δ) hsW
        (by push_cast; linarith [hδr.1])
        (by have := hδr.2; push_cast at this ⊢; linarith)
      have hcs : (2 : ℝ) ^ e * v0 + δ - ((2 ^ e * v0 : ℕ) : ℝ) = δ := by push_cast; ring
      have hc : ((2 : ℝ) ^ e * v0 + δ) / ((2 ^ (R + e) : ℕ) : ℝ) = shiftPhase r R l := by
        rw [← hident]; field_simp
      rw [hcs, hc] at ht
      refine le_trans (sum_le_sum fun b _ => ?_) ht
      by_cases hb : 2 ^ e * v0 ≤ b ∧ b < 2 ^ e * v0 + 2 ^ e
      · rw [if_pos hb]
        have hdiv : b / 2 ^ e = v0 :=
          Nat.div_eq_of_lt_le (by linarith [hb.1]) (by linarith [hb.2])
        rw [if_pos]
        unfold Challenge.wrappedNumerators
        rw [hdiv]
        exact Finset.mem_union_left _ hm
      · rw [if_neg hb]
        split_ifs
        · exact ampSq_nonneg _ _ _
        · exact le_rfl
    · -- wrap: `v0 = 2^R`, the window is `[0, 2^e)` and the phase is shifted by one turn
      have hsW : 0 + 2 ^ e ≤ 2 ^ (R + e) := by
        rw [hNPW]; nlinarith
      have ht := window_tail (2 ^ (R + e)) (2 ^ e) 0 δ hsW
        (by push_cast; linarith [hδr.1])
        (by have := hδr.2; push_cast at this ⊢; linarith)
      have hcs : δ - ((0 : ℕ) : ℝ) = δ := by simp
      have hc : δ / ((2 ^ (R + e) : ℕ) : ℝ) = shiftPhase r R l - 1 := by
        have hN0 : ((2 ^ (R + e) : ℕ) : ℝ) ≠ 0 := by positivity
        have hNv : ((2 ^ (R + e) : ℕ) : ℝ) = (2 : ℝ) ^ e * v0 := by
          rw [heq, hNPW]; push_cast; ring
        rw [div_eq_iff hN0]
        linear_combination (-1 : ℝ) * hident + hNv
      rw [hcs, hc] at ht
      refine le_trans (sum_le_sum fun b _ => ?_) ht
      by_cases hb : 0 ≤ b ∧ b < 0 + 2 ^ e
      · rw [if_pos hb]
        have hdiv : b / 2 ^ e = 0 := Nat.div_eq_of_lt (by omega)
        rw [if_pos]
        unfold Challenge.wrappedNumerators
        rw [hdiv, if_pos rfl]
        apply Finset.mem_union_right
        rw [heq] at hm
        exact hm
      · rw [if_neg hb, ampSq_sub_one]
        split_ifs
        · exact ampSq_nonneg _ _ _
        · exact le_rfl
  · exact hfail1

/-! ## Averaging over the numerators -/

/-- Group bound for offsets in `[m, m + 1)`. -/
noncomputable def groupBound (W N : ℝ) (m : ℕ) : ℝ :=
  if 1 ≤ m ∧ (m : ℝ) + 3 ≤ W then 203 / 1000 * (1 / (m : ℝ) + 1 / (W - 2 - m)) + 2 / N else 1

lemma capTail_le_group (W N δ : ℝ) (m : ℕ) (hm : (m : ℝ) ≤ δ) (hm' : δ < m + 1) :
    capTail W N δ ≤ groupBound W N m := by
  unfold groupBound
  split_ifs with hg
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hg.1
    have h1 : 1 ≤ δ ∧ δ ≤ W - 2 := ⟨by linarith, by linarith [hg.2]⟩
    unfold capTail
    rw [if_pos h1]
    refine (min_le_right _ _).trans ?_
    have hd : 1 / δ ≤ 1 / (m : ℝ) := one_div_le_one_div_of_le (by linarith) hm
    have hd' : 1 / (W - 1 - δ) ≤ 1 / (W - 2 - m) :=
      one_div_le_one_div_of_le (by linarith [hg.2]) (by linarith)
    nlinarith
  · exact capTail_le_one W N δ

lemma groupBound_sum (W N : ℝ) (M : ℕ) (hW : W = M + 3) (_hN : 0 < N) :
    ∑ m ∈ range (M + 3), groupBound W N m ≤
      3 + 406 / 1000 * (harmonic M : ℝ) + (M : ℝ) * (2 / N) := by
  rw [sum_range_succ, sum_range_succ, sum_range_succ']
  have hb1 : groupBound W N (M + 1) ≤ 1 := by
    unfold groupBound; rw [if_neg]; push_cast; rintro ⟨-, h⟩; linarith
  have hb2 : groupBound W N (M + 2) ≤ 1 := by
    unfold groupBound; rw [if_neg]; push_cast; rintro ⟨-, h⟩; linarith
  have hb0 : groupBound W N 0 = 1 := by unfold groupBound; rw [if_neg]; omega
  have hmid : ∀ m ∈ range M, groupBound W N (m + 1) =
      203 / 1000 * (1 / ((m : ℝ) + 1) + 1 / (((M - 1 - m : ℕ) : ℝ) + 1)) + 2 / N := by
    intro m hm
    rw [mem_range] at hm
    unfold groupBound
    have hm' : (m : ℝ) + 1 ≤ M := by exact_mod_cast hm
    rw [if_pos ⟨by omega, by push_cast; linarith⟩]
    have : ((M - 1 - m : ℕ) : ℝ) + 1 = W - 2 - ((m + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hW]; push_cast; ring
    rw [this]; push_cast; ring
  rw [sum_congr rfl hmid, sum_add_distrib, ← mul_sum, sum_add_distrib, sum_const, card_range,
    nsmul_eq_mul]
  have hrefl : ∑ m ∈ range M, 1 / (((M - 1 - m : ℕ) : ℝ) + 1) =
      ∑ m ∈ range M, 1 / ((m : ℝ) + 1) := by
    rw [← sum_range_reflect (fun m => 1 / ((m : ℝ) + 1)) M]
  have hharm : ∑ m ∈ range M, 1 / ((m : ℝ) + 1) = (harmonic M : ℝ) := by
    rw [harmonic]; push_cast; simp only [one_div]
  rw [hrefl, hharm, hb0]
  linarith

set_option maxHeartbeats 2000000 in
/-- Average success over all nonzero numerators. -/
theorem shift_average (r R e : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (he : 2 ≤ e) :
    ((r : ℝ) - 1) - (((r : ℝ) - 1) / 2 ^ e + 1) *
        (3 + 406 / 1000 * (1 + e * 0.6931471808) + 2 ^ e * (2 / 2 ^ (R + e))) ≤
      ∑ l ∈ Finset.Ico 1 r, ∑ b ∈ range (2 ^ (R + e)),
        (if l ∈ Challenge.wrappedNumerators r R (b / 2 ^ e) then
          ampSq (2 ^ (R + e)) (shiftPhase r R l) b else 0) := by
  classical
  have hr0 : 0 < r := hr.pos
  have hodd : r % 2 = 1 := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
  set W : ℕ := 2 ^ e with hW
  set N : ℕ := 2 ^ (R + e) with hN
  have hW4 : 4 ≤ W := by
    rw [hW]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hNpos : (0 : ℝ) < N := by positivity
  have hWpos : (0 : ℝ) < W := by positivity
  -- success = 1 - failure
  have hsplit : ∀ l, ∑ b ∈ range N, (if l ∈ Challenge.wrappedNumerators r R (b / W) then
      ampSq N (shiftPhase r R l) b else 0) = 1 - ∑ b ∈ range N,
      (if l ∈ Challenge.wrappedNumerators r R (b / W) then 0 else ampSq N (shiftPhase r R l) b) := by
    intro l
    rw [eq_sub_iff_add_eq, ← sum_add_distrib, ← parseval N (by positivity) (shiftPhase r R l)]
    refine sum_congr rfl (fun b _ => ?_)
    split_ifs <;> simp
  simp only [hsplit, sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  push_cast
  -- failure sum
  set G : ℕ → ℝ := fun t => capTail W N ((W : ℝ) * ((2 * t + 1 : ℕ) : ℝ) / (2 * r)) with hG
  have hfail : ∀ l ∈ Finset.Ico 1 r, ∑ b ∈ range N,
      (if l ∈ Challenge.wrappedNumerators r R (b / W) then 0 else ampSq N (shiftPhase r R l) b) ≤
      G (offsetIndex r R l) := by
    intro l hl
    rw [Finset.mem_Ico] at hl
    have h := fail_le r R e l hr0 hl.2
    rw [offset_odd r R l hodd] at h
    exact h
  have hGnn : ∀ t, 0 ≤ G t := fun t => capTail_nonneg _ _ _ hNpos
  have himage : ∑ l ∈ Finset.Ico 1 r, G (offsetIndex r R l) ≤ ∑ t ∈ range r, G t := by
    rw [← sum_image (offsetIndex_injOn r R hr hr2)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro t ht
      rw [mem_image] at ht
      obtain ⟨l, _, rfl⟩ := ht
      exact mem_range.mpr (offsetIndex_lt r R l hr0 hodd)
    · intro t _ _; exact hGnn t
  -- group the offsets
  set g : ℕ → ℕ := fun t => W * (2 * t + 1) / (2 * r) with hg
  have hmaps : ∀ t ∈ range r, g t ∈ range W := by
    intro t ht
    rw [mem_range] at ht ⊢
    rw [hg, Nat.div_lt_iff_lt_mul (by omega)]
    nlinarith
  have hgroup : ∑ t ∈ range r, G t ≤
      (((r : ℝ) - 1) / W + 1) * ∑ m ∈ range W, groupBound W N m := by
    rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
    apply sum_le_sum
    intro m _
    calc ∑ t ∈ range r with g t = m, G t ≤ ∑ t ∈ range r with g t = m, groupBound W N m := by
          apply sum_le_sum
          intro t ht
          rw [mem_filter] at ht
          have h1 : m * (2 * r) ≤ W * (2 * t + 1) := by
            rw [← ht.2]; exact Nat.div_mul_le_self _ _
          have h2 : W * (2 * t + 1) < (2 * r) * (m + 1) := by
            rw [← ht.2]; exact Nat.lt_mul_div_succ _ (by omega)
          have h1' : ((m : ℝ)) * (2 * r) ≤ W * ((2 * t + 1 : ℕ) : ℝ) := by
            exact_mod_cast h1
          have h2' : (W : ℝ) * ((2 * t + 1 : ℕ) : ℝ) < (2 * r) * ((m : ℝ) + 1) := by
            exact_mod_cast h2
          have hr2R : (0 : ℝ) < 2 * r := by positivity
          apply capTail_le_group
          · rw [le_div_iff₀ hr2R]; linarith
          · rw [div_lt_iff₀ hr2R]; linarith
      _ = ((range r).filter (fun t => g t = m)).card * groupBound W N m := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (((r : ℝ) - 1) / W + 1) * groupBound W N m := by
          have hgb : 0 ≤ groupBound W N m := by
            unfold groupBound; split_ifs with h
            · have : (1 : ℝ) ≤ m := by exact_mod_cast h.1
              have : 0 < (W : ℝ) - 2 - m := by linarith [h.2]
              positivity
            · exact zero_le_one
          apply mul_le_mul_of_nonneg_right _ hgb
          have hc := fiber_card r W m hr0 (by omega)
          have hcR : (((range r).filter (fun t => g t = m)).card : ℝ) ≤ ((r - 1) / W : ℕ) + 1 := by
            exact_mod_cast hc
          have hdiv : (((r - 1) / W : ℕ) : ℝ) ≤ ((r : ℝ) - 1) / W := by
            rw [le_div_iff₀ hWpos]
            have := Nat.div_mul_le_self (r - 1) W
            have h' : (((r - 1) / W * W : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast this
            push_cast [Nat.cast_sub (by omega : 1 ≤ r)] at h'
            linarith
          linarith
  -- the group sum
  obtain ⟨M, hM⟩ : ∃ M, W = M + 3 := ⟨W - 3, by omega⟩
  have hgs := groupBound_sum (W : ℝ) N M (by rw [hM]; push_cast; ring) hNpos
  rw [← hM] at hgs
  have hharm : (harmonic M : ℝ) ≤ 1 + e * 0.6931471808 := by
    have h := harmonic_le_one_add_log M
    have hlog : Real.log M ≤ e * 0.6931471808 := by
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · rw [h0]; simp; positivity
      · have hMW : (M : ℝ) ≤ 2 ^ e := by
          have : M ≤ 2 ^ e := by omega
          exact_mod_cast this
        calc Real.log M ≤ Real.log (2 ^ e) := Real.log_le_log (by exact_mod_cast hpos) hMW
          _ = e * Real.log 2 := by rw [Real.log_pow]
          _ ≤ e * 0.6931471808 := by
              apply mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg _)
    linarith
  have hMW : (M : ℝ) ≤ W := by rw [hM]; push_cast; linarith
  have hC : ∑ m ∈ range W, groupBound W N m ≤
      3 + 406 / 1000 * (1 + e * 0.6931471808) + W * (2 / N) := by
    have h2N : (M : ℝ) * (2 / N) ≤ W * (2 / N) :=
      mul_le_mul_of_nonneg_right hMW (by positivity)
    linarith
  have hfactor : 0 ≤ ((r : ℝ) - 1) / W + 1 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr0
    have : 0 ≤ ((r : ℝ) - 1) / W := div_nonneg (by linarith) hWpos.le
    linarith
  have htot := (sum_le_sum hfail).trans (himage.trans (hgroup.trans
    (mul_le_mul_of_nonneg_left hC hfactor)))
  push_cast [hW, hN] at htot ⊢
  linarith

end WindowMassProof

end ShorECDLP.Entrant
