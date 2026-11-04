import ShorECDLP.Submission.Entrant.StackBase

/-! Sharp analytic constants for a 261/208 two-axis readout with 56 right neighbours.

Pure real-analysis lemmas, no circuit content. They replace the three loose steps of
`SinAverage` (`sin (π u) ≥ 3 u`, `∑_{k} 1/(L+k)² ≤ 1/(L-1)`, independent radii on both sides)
by near-exact ones:

* `sin_pi_mul_ge_sharp`: `sin (π u) ≥ 3.141591 u` for `0 < u ≤ 2⁻²⁰`;
* `sum_inv_sq_le_half`: separated points at distance `≥ L` have `∑ 1/φ² ≤ 1/(L - 1/2)`
  (telescoping `1/x² ≤ 1/(x-½) - 1/(x+½)`);
* `pair_max`: if the first bad distances on the two sides satisfy `x ≥ a`, `y ≥ b`,
  `x + y ≥ a + b + 1` (`a ≤ b`), the two-sided tail constant is at most
  `1/(a-½) + 1/(b+½)`. Left 261 (`a = b = 16`): `1/15.5 + 1/16.5`.
  Right with shifts `-28..27` (`a = 27.5`, `b = 28.5`): `1/27 + 1/29`.
* `sharp_budget261`: averaging the weights (`≤ 1/2`, `SinAverage.sum_sin_sq_le`) leaves
  success `≥ 0.990037 > 0.99`. -/

namespace ShorECDLP.Entrant.SharpTail
open Finset
noncomputable section

/-- Telescoping majorant of `1/x²`. -/
theorem inv_sq_le_telescope (x : ℝ) (hx : 1/2 < x) :
    1 / x ^ 2 ≤ 1 / (x - 1/2) - 1 / (x + 1/2) := by
  have h1 : 0 < x - 1/2 := by linarith
  have h2 : 0 < x + 1/2 := by linarith
  have hx0 : 0 < x := by linarith
  have e : 1 / (x - 1/2) - 1 / (x + 1/2) = 1 / ((x - 1/2) * (x + 1/2)) := by
    rw [div_sub_div _ _ h1.ne' h2.ne']
    congr 1
    ring
  rw [e]
  apply one_div_le_one_div_of_le (mul_pos h1 h2)
  nlinarith

theorem sum_range_inv_sq_le_half (L : ℝ) (hL : 1/2 < L) (n : ℕ) :
    ∑ k ∈ range n, 1 / (L + k) ^ 2 ≤ 1 / (L - 1/2) - 1 / (L - 1/2 + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h := inv_sq_le_telescope (L + n) (by linarith)
    have e1 : L + (n : ℝ) - 1/2 = L - 1/2 + n := by ring
    have e2 : L + (n : ℝ) + 1/2 = L - 1/2 + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    linarith

/-- Separated points at distance at least `L`: `∑ 1/φ² ≤ 1/(L - 1/2)`. -/
theorem sum_inv_sq_le_half (S : Finset ℕ) (φ : ℕ → ℝ) (L : ℝ) (hL : 1/2 < L)
    (hφ : ∀ a ∈ S, L ≤ φ a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ 1 / (L - 1/2) := by
  set g : ℕ → ℕ := fun a => ⌊φ a - L⌋₊ with hg
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h2 := Nat.lt_floor_add_one (φ a - L)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb))
    have h4 := Nat.lt_floor_add_one (φ b - L)
    simp only [hg] at hab
    rw [hab] at h1 h2
    apply hsep a ha b hb
    rw [abs_lt]; constructor <;> linarith
  have step1 : ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ ∑ a ∈ S, 1 / (L + g a) ^ 2 := by
    apply sum_le_sum
    intro a ha
    have h1 : (g a : ℝ) ≤ φ a - L := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h0 : (0 : ℝ) ≤ g a := Nat.cast_nonneg _
    have h2 : 0 < L + g a := by linarith
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  have step2 : ∑ a ∈ S, 1 / (L + g a) ^ 2 = ∑ k ∈ S.image g, 1 / (L + k) ^ 2 := by
    rw [sum_image hinj]
  have step3 : ∑ k ∈ S.image g, 1 / (L + k) ^ 2 ≤
      ∑ k ∈ range (S.sup g + 1), 1 / (L + k) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [mem_image] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [mem_range]
      exact Nat.lt_succ_of_le (le_sup ha)
    · intro k _ _
      positivity
  have h4 := sum_range_inv_sq_le_half L hL (S.sup g + 1)
  have h5 : 0 ≤ 1 / (L - 1/2 + ((S.sup g + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) ≤ ((S.sup g + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    apply div_nonneg zero_le_one
    linarith
  linarith

/-- Coupled two-sided maximum. With `a ≤ b`, first bad distances `x ≥ a`, `y ≥ b` and an
integer gap `x + y ≥ a + b + 1`, the worst case is `(a, b + 1)`. -/
theorem pair_max (a b x y : ℝ) (ha : 1/2 < a) (hab : a ≤ b) (hx : a ≤ x) (hy : b ≤ y)
    (hxy : a + b + 1 ≤ x + y) :
    1 / (x - 1/2) + 1 / (y - 1/2) ≤ 1 / (a - 1/2) + 1 / (b + 1/2) := by
  have hA : 0 < a - 1/2 := by linarith
  by_cases hyb : b + 1 ≤ y
  · have h1 : 1 / (x - 1/2) ≤ 1 / (a - 1/2) := one_div_le_one_div_of_le hA (by linarith)
    have h2 : 1 / (y - 1/2) ≤ 1 / (b + 1/2) := one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  · push_neg at hyb
    set t := y - b with ht
    have ht0 : 0 ≤ t := by linarith
    have ht1 : t < 1 := by linarith
    have h1 : 1 / (x - 1/2) ≤ 1 / (a + 1/2 - t) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have hy' : y - 1/2 = b - 1/2 + t := by rw [ht]; ring
    rw [hy']
    have hP : 0 < a + 1/2 - t := by linarith
    have hQ : 0 < b - 1/2 + t := by linarith
    have hB : 0 < b + 1/2 := by linarith
    have key : 1 / (a + 1/2 - t) + 1 / (b - 1/2 + t) ≤ 1 / (a - 1/2) + 1 / (b + 1/2) := by
      rw [div_add_div _ _ hP.ne' hQ.ne', div_add_div _ _ hA.ne' hB.ne',
        div_le_div_iff₀ (mul_pos hP hQ) (mul_pos hA hB)]
      have h1t : 0 ≤ 1 - t := by linarith
      nlinarith [mul_nonneg h1t (mul_nonneg ht0 h1t), mul_nonneg h1t ht0,
        mul_nonneg h1t (sub_nonneg.mpr hab), mul_nonneg (mul_nonneg h1t (sub_nonneg.mpr hab)) hA.le,
        mul_nonneg (mul_nonneg h1t (sub_nonneg.mpr hab)) ht0,
        mul_nonneg (mul_nonneg h1t ht0) ht0, mul_nonneg (mul_nonneg h1t ht0) hA.le,
        mul_nonneg (mul_nonneg h1t (sub_nonneg.mpr hab)) (sub_nonneg.mpr hab)]
    linarith

/-- Left axis, 261 bits: half-bin `L > 16`, integer gap `≥ 33`. -/
theorem left261_pair (x y : ℝ) (hx : 16 ≤ x) (hy : 16 ≤ y) (hxy : 33 ≤ x + y) :
    1 / (x - 1/2) + 1 / (y - 1/2) ≤ 1 / 15.5 + 1 / 16.5 := by
  have h := pair_max 16 16 x y (by norm_num) le_rfl hx hy (by linarith)
  norm_num at h ⊢
  linarith

/-- Right axis, shifts `-28..27` around the rounded peak: `x ≥ 27.5`, `y ≥ 28.5`, gap `57`. -/
theorem right56_pair (x y : ℝ) (hx : 27.5 ≤ x) (hy : 28.5 ≤ y) (hxy : 57 ≤ x + y) :
    1 / (x - 1/2) + 1 / (y - 1/2) ≤ 1 / 27 + 1 / 29 := by
  have h := pair_max 27.5 28.5 x y (by norm_num) (by norm_num) hx hy (by linarith)
  norm_num at h ⊢
  linarith

/-- Near-exact sine lower bound for tiny arguments. -/
theorem sin_pi_mul_ge_sharp (u : ℝ) (hu0 : 0 < u) (hu : u ≤ 1/1048576) :
    (3141591 / 1000000 : ℝ) * u ≤ Real.sin (Real.pi * u) := by
  have hp := Real.pi_gt_d6
  have hp4 := Real.pi_lt_four
  have hx0 : 0 < Real.pi * u := by positivity
  have hx1 : Real.pi * u ≤ 1 := by nlinarith
  have hs := Real.sin_gt_sub_cube hx0 hx1
  have hx4 : Real.pi * u ≤ 4 * u := by nlinarith
  have hsq : (Real.pi * u) ^ 2 ≤ 16 / 1099511627776 := by
    have : (Real.pi * u) ^ 2 ≤ (4 * u) ^ 2 := pow_le_pow_left₀ hx0.le hx4 2
    nlinarith
  have hc : Real.pi * u - (Real.pi * u) ^ 3 / 4 =
      Real.pi * u * (1 - (Real.pi * u) ^ 2 / 4) := by ring
  have hfac : 1 - 4 / 1099511627776 ≤ 1 - (Real.pi * u) ^ 2 / 4 := by linarith
  have hlow : Real.pi * u * (1 - 4 / 1099511627776) ≤ Real.pi * u - (Real.pi * u) ^ 3 / 4 := by
    rw [hc]; exact mul_le_mul_of_nonneg_left hfac hx0.le
  have h3 : (3141591 / 1000000 : ℝ) * u ≤ Real.pi * u * (1 - 4 / 1099511627776) := by
    nlinarith
  linarith

/-- Per-term constant: `9.8695 φ² ≤ (N sin (π φ / N))²` when `φ ≤ N / 2²⁰`. -/
theorem per_term_sharp (N φ : ℝ) (hN : 0 < N) (hφ : 0 < φ) (hsmall : φ / N ≤ 1/1048576) :
    (98695 / 10000 : ℝ) * φ ^ 2 ≤ (N * Real.sin (Real.pi * (φ / N))) ^ 2 := by
  have hu : 0 < φ / N := div_pos hφ hN
  have hs := sin_pi_mul_ge_sharp (φ / N) hu hsmall
  have hNs : (3141591 / 1000000 : ℝ) * φ ≤ N * Real.sin (Real.pi * (φ / N)) := by
    have : N * ((3141591 / 1000000 : ℝ) * (φ / N)) = (3141591 / 1000000 : ℝ) * φ := by
      field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hs hN.le
  have h0 : 0 ≤ (3141591 / 1000000 : ℝ) * φ := by positivity
  have hsq := pow_le_pow_left₀ h0 hNs 2
  nlinarith

/-- Far tail from the existing unweighted `circular_mass` at radius `2^40`. -/
theorem far_tail_2pow40 : 3 / (Real.pi ^ 2 * ((2 : ℝ) ^ 40 - 1)) ≤ (1 : ℝ) / 100000000000 := by
  have hp := Real.pi_gt_three
  have hd : 0 < Real.pi ^ 2 * ((2 : ℝ) ^ 40 - 1) := by
    have : (0 : ℝ) < (2 : ℝ) ^ 40 - 1 := by norm_num
    positivity
  rw [div_le_div_iff₀ hd (by norm_num)]
  have h9 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have : (0 : ℝ) < (2 : ℝ) ^ 40 - 1 := by norm_num
  nlinarith

/-- Final budget: averaged weights `≤ 1/2`, sharp per-term constant, coupled radii on both
axes, far tails at radius `2^40` on both axes, and the excluded character `k = 0`. -/
theorem sharp_budget261 (r : ℝ) (hr : 1000000 ≤ r) :
    (99 : ℝ) / 100 ≤ (1 - 1 / r) * (1 - 2 / 100000000000)
      - (1 / 15.5 + 1 / 16.5) / (2 * (98695 / 10000))
      - (1 / 27 + 1 / 29) / (2 * (98695 / 10000)) := by
  have hr0 : 0 < r := by linarith
  have hinv : 1 / r ≤ (1 : ℝ) / 1000000 := one_div_le_one_div_of_le (by norm_num) hr
  have hinv0 : 0 ≤ 1 / r := by positivity
  norm_num at hinv ⊢
  nlinarith

end
end ShorECDLP.Entrant.SharpTail
