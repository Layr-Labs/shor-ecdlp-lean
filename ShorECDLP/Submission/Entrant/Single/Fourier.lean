import ShorECDLP.Submission.«2607_13816».OrderFinding.WrappedCandidates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds
import ShorECDLP.Submission.Naive.OrderFinding.Proofs.SuccessProbability
import ShorECDLP.Submission.«2607_13816».Window.CharacterMixture
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.Entrant.Single.Physical
import ShorECDLP.Submission.Entrant.Streaming.Semantics
import ShorECDLP.Framework.Quantum.TerminalInterference


/-! Circular Fourier concentration and recorded half-bin rounding.
The sharp pointwise Fourier estimate is inherited from ArthurOstapenko's
single-trial certificate (8c5e5431), retaining its original attribution. -/

-- ==== part: Single/WindowMassSharp ====

section
/- Copied from public promoted submission commit 8321638bca0ea97505a1fae2e711c0f52b0d2a2e. -/

/-! Sharp window mass for quantum phase estimation.

With `N = 2 ^ t ≥ 128 r` outcomes, the QPE outcome distribution for the phase `n / r`
puts mass at least `200 / 201` on the outcomes `a` whose rounding `round (r a / N)`
equals `n`.  Compared with `WindowMass.lean`, the pointwise estimate uses
`sin z ≥ z - z ^ 3 / 6` and `sin z = cos (π / 2 - z) ≥ 1 - (π / 2 - z) ^ 2 / 2`, giving
`1 / sin² z ≤ (3 / 2) (1 / z² + 1 / (π - z)²)` on `(0, π)`, so that
`|amplitude a|² ≤ 3 / (2 π²) (1 / u² + 1 / (N - u)²)`.  The two families of terms are
regrouped by the wrapped distances `phiR`, `phiL` (each injective with values `≥ L`), and a
telescoping estimate bounds the tail by `3 / (π² (L - 1)) < 1 / 201` for `L ≥ 64`. -/

namespace ShorECDLP.Entrant

namespace WindowMassSharpProof

open Finset

lemma nat_eq_of_abs_lt (a b : ℕ) (h : |(a : ℝ) - b| < 1) : a = b := by
  rw [abs_lt] at h
  rcases lt_trichotomy a b with hab | hab | hab
  · have h1 : a + 1 ≤ b := hab
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h1
    linarith [h.1]
  · exact hab
  · have h1 : b + 1 ≤ a := hab
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h1
    linarith [h.2]

lemma sum_range_inv_sq_le (L : ℝ) (hL : 1 < L) (M : ℕ) :
    ∑ k ∈ range M, 1 / (L + k) ^ 2 ≤ 1 / (L - 1) - 1 / (L - 1 + M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h1 : 0 < L - 1 + M := by linarith
    have h2 : 0 < L + M := by linarith
    have : 1 / (L + M) ^ 2 ≤
        1 / (L - 1 + M) - 1 / (L - 1 + ((M + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [show L - 1 + (M + 1) = L + M by ring]
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma sum_inv_sq_le (S : Finset ℕ) (φ : ℕ → ℝ) (L : ℝ) (hL : 1 < L)
    (hφ : ∀ a ∈ S, L ≤ φ a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ 1 / (L - 1) := by
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
  have h4 := sum_range_inv_sq_le L hL (S.sup g + 1)
  have h5 : 0 ≤ 1 / (L - 1 + ((S.sup g + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) ≤ ((S.sup g + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 0 < L - 1 + ((S.sup g + 1 : ℕ) : ℝ) := by linarith
    positivity
  linarith

lemma sin_ge_cubic (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  let f : ℝ → ℝ := fun x => Real.sin x - x + x ^ 3 / 6
  have hd : ∀ x, HasDerivAt f (Real.cos x - 1 + x ^ 2 / 2) x := by
    intro x
    have := ((Real.hasDerivAt_sin x).sub (hasDerivAt_id x)).add ((hasDerivAt_pow 3 x).div_const 6)
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have h := hmono hx
  simp only [f, Real.sin_zero] at h
  linarith

lemma inv_sq_add_inv_sq_ge (z w : ℝ) (hz : 0 < z) (hw : 0 < w) :
    8 / (z + w) ^ 2 ≤ 1 / z ^ 2 + 1 / w ^ 2 := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (z - w), mul_pos hz hw, mul_pos (mul_pos hz hw) (mul_pos hz hw),
    mul_nonneg (mul_pos hz hw).le (sq_nonneg (z - w))]

lemma sin_sq_mul_ge_half (z : ℝ) (hz0 : 0 < z) (hz1 : z ≤ Real.pi / 2) :
    2 / 3 ≤ Real.sin z ^ 2 * (1 / z ^ 2 + 1 / (Real.pi - z) ^ 2) := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hw : 0 < Real.pi - z := by linarith
  have hcub := sin_ge_cubic z hz0.le
  rcases le_total z 1 with h1 | h1
  · -- z ≤ 1
    have hs : 5 * z / 6 ≤ Real.sin z := by nlinarith [mul_pos hz0 hz0]
    have ha : 25 / 36 ≤ Real.sin z ^ 2 * (1 / z ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hb : 0 ≤ Real.sin z ^ 2 * (1 / (Real.pi - z) ^ 2) := by positivity
    rw [mul_add]
    linarith
  rcases le_total z (6 / 5) with h2 | h2
  · -- 1 ≤ z ≤ 6/5
    have hs : 19 * z / 25 ≤ Real.sin z := by nlinarith [mul_pos hz0 hz0]
    have hs2 : 361 * z ^ 2 / 625 ≤ Real.sin z ^ 2 := by nlinarith
    have ha : 361 / 625 ≤ Real.sin z ^ 2 * (1 / z ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    have hb : 5776 / 46225 ≤ Real.sin z ^ 2 * (1 / (Real.pi - z) ^ 2) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (Real.pi - z) ^ 2 ≤ (43 / 20) ^ 2 := by
        apply pow_le_pow_left₀ hw.le
        norm_num at hpi2 ⊢
        linarith
      nlinarith
    rw [mul_add]
    linarith
  · -- 6/5 ≤ z ≤ π/2
    have hy0 : 0 ≤ Real.pi / 2 - z := by linarith
    have hy1 : Real.pi / 2 - z ≤ 3 / 8 := by norm_num at hpi2; linarith
    have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 - z)
    rw [Real.cos_pi_div_two_sub] at hcos
    have hs : 7437 / 8000 ≤ Real.sin z := by nlinarith
    have hs2 : 86 / 100 ≤ Real.sin z ^ 2 := by nlinarith
    have hT := inv_sq_add_inv_sq_ge z (Real.pi - z) hz0 hw
    rw [show z + (Real.pi - z) = Real.pi by ring] at hT
    have hT' : 8 / 10 ≤ 8 / Real.pi ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      norm_num at hpi2
      nlinarith
    have hT0 : 0 ≤ 1 / z ^ 2 + 1 / (Real.pi - z) ^ 2 := by positivity
    nlinarith

lemma sin_sq_mul_ge (z : ℝ) (hz0 : 0 < z) (hz1 : z < Real.pi) :
    2 / 3 ≤ Real.sin z ^ 2 * (1 / z ^ 2 + 1 / (Real.pi - z) ^ 2) := by
  rcases le_total z (Real.pi / 2) with h | h
  · exact sin_sq_mul_ge_half z hz0 h
  · have := sin_sq_mul_ge_half (Real.pi - z) (by linarith) (by linarith)
    rw [Real.sin_pi_sub, sub_sub_cancel] at this
    linarith [add_comm (1 / (Real.pi - z) ^ 2) (1 / z ^ 2)]

lemma amp_normSq_le (N : ℕ) (x : ℝ) (hs : Real.sin (x / 2) ≠ 0) :
    Complex.normSq ((N : ℂ)⁻¹ * ∑ y ∈ range N, Complex.exp (Complex.I * (x : ℂ)) ^ y)
      ≤ (1 / ((N : ℝ) * |Real.sin (x / 2)|)) ^ 2 := by
  set ω := Complex.exp (Complex.I * (x : ℂ)) with hωdef
  have hω1 : ‖ω - 1‖ = 2 * |Real.sin (x / 2)| := by
    rw [hωdef, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs]
    norm_num
  have hpos : 0 < |Real.sin (x / 2)| := abs_pos.mpr hs
  have hω : ω ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hω1
    linarith
  have hωn : ‖ω‖ = 1 := Complex.norm_exp_I_mul_ofReal x
  have hnum : ‖ω ^ N - 1‖ ≤ 2 := by
    calc ‖ω ^ N - 1‖ ≤ ‖ω ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hωn]; norm_num
  rw [geom_sum_eq hω, Complex.normSq_eq_norm_sq, norm_mul, norm_div, norm_inv,
    Complex.norm_natCast, hω1]
  apply pow_le_pow_left₀ (by positivity)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [one_div, mul_inv, ← div_eq_inv_mul, ← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ hNr.le
  rw [div_le_iff₀ (by positivity)]
  have e : |Real.sin (x / 2)|⁻¹ * (2 * |Real.sin (x / 2)|) = 2 := by
    field_simp
  rw [e]
  exact hnum

lemma orth (N : ℕ) (hN : 0 < N) (y y' : ℕ) (hy : y < N) (hy' : y' < N) :
    ∑ a ∈ range N, Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) ^ a =
      if y = y' then (N : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · set z := Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) with hzdef
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hz : z ^ N = 1 := by
      rw [hzdef, ← Complex.exp_nat_mul]
      have : (N : ℂ) * (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) =
          (((y' : ℤ) - y : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    have hz1 : z ≠ 1 := by
      intro h1
      rw [hzdef, Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      have h2pi : (2 * Real.pi * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hc : ((y' : ℂ) - y) = m * N := by
        have := congrArg (fun w => w * N / (2 * Real.pi * Complex.I)) hm
        simp only at this
        field_simp at this
        linear_combination this
      have hi : ((y' : ℤ) - y) = m * N := by exact_mod_cast hc
      have hN' : (0 : ℤ) < N := by exact_mod_cast hN
      have hm1 : m < 1 := by
        by_contra hc'
        push_neg at hc'
        nlinarith
      have hm2 : -1 < m := by
        by_contra hc'
        push_neg at hc'
        nlinarith
      have hm0 : m = 0 := by omega
      subst hm0
      apply h
      omega
    rw [geom_sum_eq hz1, hz, sub_self, zero_div]

/-- The squared QPE amplitude at outcome `a`, for phase `β`. -/
noncomputable def ampSq (N : ℕ) (β : ℝ) (a : ℕ) : ℝ :=
  Complex.normSq (((N : ℂ)⁻¹) * ∑ y ∈ range N,
    Complex.exp (Complex.I * ((2 * Real.pi * (β - (a : ℝ) / (N : ℝ)) : ℝ) : ℂ)) ^ y)

lemma ampSq_expand (N : ℕ) (β : ℝ) (a : ℕ) :
    ((ampSq N β a : ℝ) : ℂ) = ((N : ℂ)⁻¹) ^ 2 * ∑ y ∈ range N, ∑ y' ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * β * ((y : ℂ) - y')) *
        Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) ^ a := by
  unfold ampSq
  rw [← Complex.mul_conj, map_mul, map_inv₀, Complex.conj_natCast, map_sum,
    mul_mul_mul_comm, ← pow_two, sum_mul_sum]
  congr 1
  refine sum_congr rfl (fun y _ => sum_congr rfl (fun y' _ => ?_))
  simp only [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast]
  push_cast
  ring

lemma parseval (N : ℕ) (hN : 0 < N) (β : ℝ) :
    ∑ a ∈ range N, ampSq N β a = 1 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  apply Complex.ofReal_injective
  calc (((∑ a ∈ range N, ampSq N β a : ℝ)) : ℂ)
      = ∑ a ∈ range N, ((N : ℂ)⁻¹) ^ 2 * ∑ y ∈ range N, ∑ y' ∈ range N,
          Complex.exp (2 * Real.pi * Complex.I * β * ((y : ℂ) - y')) *
            Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) ^ a := by
        push_cast
        exact sum_congr rfl (fun a _ => ampSq_expand N β a)
    _ = ((N : ℂ)⁻¹) ^ 2 * ∑ y ∈ range N, ∑ y' ∈ range N,
          Complex.exp (2 * Real.pi * Complex.I * β * ((y : ℂ) - y')) *
            ∑ a ∈ range N, Complex.exp (2 * Real.pi * Complex.I * ((y' : ℂ) - y) / N) ^ a := by
        rw [← mul_sum]
        congr 1
        rw [sum_comm]
        refine sum_congr rfl (fun y _ => ?_)
        rw [sum_comm]
        refine sum_congr rfl (fun y' _ => ?_)
        rw [mul_sum]
    _ = ((N : ℂ)⁻¹) ^ 2 * ∑ y ∈ range N, ∑ y' ∈ range N,
          Complex.exp (2 * Real.pi * Complex.I * β * ((y : ℂ) - y')) *
            (if y = y' then (N : ℂ) else 0) := by
        congr 1
        refine sum_congr rfl (fun y hy => sum_congr rfl (fun y' hy' => ?_))
        rw [orth N hN y y' (mem_range.mp hy) (mem_range.mp hy')]
    _ = ((1 : ℝ) : ℂ) := by
        simp only [mul_ite, mul_zero, sum_ite_eq, mem_range, sub_self, mul_zero,
          Complex.exp_zero, one_mul]
        rw [sum_ite_of_true (fun y hy => mem_range.mp hy), sum_const, card_range, nsmul_eq_mul]
        field_simp
        simp

lemma point_bound_sharp (N : ℕ) (hN : 0 < N) (x u : ℝ) (hu0 : 0 < u) (huN : u < N)
    (hx : x / 2 = Real.pi * u / N ∨ x / 2 = -(Real.pi * u / N)) :
    Complex.normSq ((N : ℂ)⁻¹ * ∑ y ∈ range N, Complex.exp (Complex.I * (x : ℂ)) ^ y)
      ≤ 3 / (2 * Real.pi ^ 2) * (1 / u ^ 2 + 1 / ((N : ℝ) - u) ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set z := Real.pi * u / N with hz
  have hz0 : 0 < z := by positivity
  have hzπ : z < Real.pi := by
    rw [hz, div_lt_iff₀ hNR]
    nlinarith [Real.pi_pos]
  have hspos : 0 < Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz0 hzπ
  have habs : |Real.sin (x / 2)| = Real.sin z := by
    rcases hx with hx | hx <;> rw [hx]
    · exact abs_of_pos hspos
    · rw [Real.sin_neg, abs_neg]; exact abs_of_pos hspos
  have hne : Real.sin (x / 2) ≠ 0 := by
    intro h; rw [h, abs_zero] at habs; linarith
  have h1 := amp_normSq_le N x hne
  rw [habs] at h1
  refine h1.trans ?_
  have key := sin_sq_mul_ge z hz0 hzπ
  have hNu : (N : ℝ) - u ≠ 0 := by linarith
  have hz' : Real.pi - z = Real.pi * ((N : ℝ) - u) / N := by
    rw [hz]; field_simp
  have e : 3 / (2 * Real.pi ^ 2) * (1 / u ^ 2 + 1 / ((N : ℝ) - u) ^ 2) =
      (3 / 2) * (1 / z ^ 2 + 1 / (Real.pi - z) ^ 2) / (N : ℝ) ^ 2 := by
    rw [hz', hz]
    field_simp
  rw [e, div_pow, one_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg (N : ℝ))]

/-- Wrapped distance from `c` going right (mod `N`). -/
noncomputable def phiR (N : ℕ) (c : ℝ) (a : ℕ) : ℝ :=
  if c ≤ (a : ℝ) then (a : ℝ) - c else (N : ℝ) - c + a

/-- Wrapped distance from `c` going left (mod `N`). -/
noncomputable def phiL (N : ℕ) (c : ℝ) (a : ℕ) : ℝ :=
  if (a : ℝ) ≤ c then c - (a : ℝ) else (N : ℝ) + c - a

lemma phiR_sep (N : ℕ) (c : ℝ) (a b : ℕ) (ha : a < N) (hb : b < N)
    (h : |phiR N c a - phiR N c b| < 1) : a = b := by
  have ha' : a + 1 ≤ N := ha
  have hb' : b + 1 ≤ N := hb
  have ha1 : (a : ℝ) + 1 ≤ N := by exact_mod_cast ha'
  have hb1 : (b : ℝ) + 1 ≤ N := by exact_mod_cast hb'
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  apply nat_eq_of_abs_lt
  unfold phiR at h
  rw [abs_lt] at h ⊢
  split_ifs at h <;> constructor <;> linarith [h.1, h.2]

lemma phiL_sep (N : ℕ) (c : ℝ) (a b : ℕ) (ha : a < N) (hb : b < N)
    (h : |phiL N c a - phiL N c b| < 1) : a = b := by
  have ha' : a + 1 ≤ N := ha
  have hb' : b + 1 ≤ N := hb
  have ha1 : (a : ℝ) + 1 ≤ N := by exact_mod_cast ha'
  have hb1 : (b : ℝ) + 1 ≤ N := by exact_mod_cast hb'
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  apply nat_eq_of_abs_lt
  unfold phiL at h
  rw [abs_lt] at h ⊢
  split_ifs at h <;> constructor <;> linarith [h.1, h.2]

lemma window_cases (r N n a : ℕ) (hN : 0 < N) (h : ¬ (2 * r * a + N) / (2 * N) = n) :
    2 * N * n + N ≤ 2 * r * a ∨ 2 * r * a + N < 2 * N * n := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · right
    rw [Nat.div_lt_iff_lt_mul (by omega)] at h
    linarith [h]
  · left
    have h' : n + 1 ≤ (2 * r * a + N) / (2 * N) := h
    rw [Nat.le_div_iff_mul_le (by omega)] at h'
    linarith [h']

lemma window_mass_sharp_aux (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r) (hrN : 128 * r ≤ N) :
    (200 : ℝ) / 201 ≤ ∑ a ∈ range N,
      if (2 * r * a + N) / (2 * N) = n then ampSq N ((n : ℝ) / (r : ℝ)) a else 0 := by
  have hr : 0 < r := by omega
  have hN : 0 < N := by omega
  set β : ℝ := (n : ℝ) / (r : ℝ) with hβ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := (N : ℝ) * n / r with hc
  set L : ℝ := (N : ℝ) / (2 * r) with hL
  have hcr : c * r = N * n := by rw [hc]; field_simp
  have hLr : L * (2 * r) = N := by rw [hL]; field_simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnr' : (n : ℝ) + 1 ≤ r := by exact_mod_cast hnr
  have hrN' : 128 * (r : ℝ) ≤ N := by exact_mod_cast hrN
  have hL64 : 64 ≤ L := by nlinarith
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  have htot := parseval N hN β
  set S := (range N).filter (fun a => ¬ (2 * r * a + N) / (2 * N) = n) with hS
  have hSN : ∀ a ∈ S, a < N := fun a ha => mem_range.mp (mem_filter.mp ha).1
  have hreg : ∀ a ∈ S, c + L ≤ (a : ℝ) ∨ (a : ℝ) + L ≤ c := by
    intro a ha
    rw [mem_filter] at ha
    rcases window_cases r N n a hN ha.2 with h | h
    · left
      have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
      nlinarith
    · right
      have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
      nlinarith
  have hL0 : 0 < L := by linarith
  -- pointwise domination of the tail
  have hpt : ∀ a ∈ S, ampSq N β a ≤
      3 / (2 * Real.pi ^ 2) * (1 / (phiR N c a) ^ 2 + 1 / (phiL N c a) ^ 2) := by
    intro a ha
    have haN : (a : ℝ) < N := by exact_mod_cast hSN a ha
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    rcases hreg a ha with hA | hA
    · have e1 : phiR N c a = (a : ℝ) - c := by
        unfold phiR; rw [if_pos (by linarith)]
      have e2 : phiL N c a = (N : ℝ) - ((a : ℝ) - c) := by
        unfold phiL; rw [if_neg (by linarith)]; ring
      rw [e1, e2]
      exact point_bound_sharp N hN (2 * Real.pi * (β - a / N)) ((a : ℝ) - c)
        (by linarith) (by linarith) (Or.inr (by rw [hc, hβ]; field_simp; ring))
    · have e1 : phiR N c a = (N : ℝ) - (c - (a : ℝ)) := by
        unfold phiR; rw [if_neg (by linarith)]; ring
      have e2 : phiL N c a = c - (a : ℝ) := by
        unfold phiL; rw [if_pos (by linarith)]
      rw [e1, e2, add_comm (1 / ((N : ℝ) - (c - (a : ℝ))) ^ 2)]
      exact point_bound_sharp N hN (2 * Real.pi * (β - a / N)) (c - (a : ℝ))
        (by linarith) (by linarith) (Or.inl (by rw [hc, hβ]; field_simp))
  have hL1 : (1 : ℝ) < L := by linarith
  have sR := sum_inv_sq_le S (phiR N c) L hL1
    (fun a ha => by
      have haN : (a : ℝ) < N := by exact_mod_cast hSN a ha
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      unfold phiR
      split_ifs with h
      · rcases hreg a ha with hA | hA <;> linarith
      · linarith)
    (fun a ha b hb h => phiR_sep N c a b (hSN a ha) (hSN b hb) h)
  have sL := sum_inv_sq_le S (phiL N c) L hL1
    (fun a ha => by
      have haN : (a : ℝ) < N := by exact_mod_cast hSN a ha
      unfold phiL
      split_ifs with h
      · rcases hreg a ha with hA | hA <;> linarith
      · linarith)
    (fun a ha b hb h => phiL_sep N c a b (hSN a ha) (hSN b hb) h)
  have htail : ∑ a ∈ S, ampSq N β a ≤
      3 / (2 * Real.pi ^ 2) * (1 / (L - 1) + 1 / (L - 1)) := by
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum, sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (add_le_add sR sL) (by positivity)
  have hsplit : ∑ a ∈ range N,
      (if (2 * r * a + N) / (2 * N) = n then ampSq N β a else 0) =
      ∑ a ∈ range N, ampSq N β a - ∑ a ∈ S, ampSq N β a := by
    rw [hS, sum_filter, eq_sub_iff_add_eq, ← sum_add_distrib]
    refine sum_congr rfl (fun a _ => ?_)
    split_ifs <;> simp
  have hfin : 3 / (2 * Real.pi ^ 2) * (1 / (L - 1) + 1 / (L - 1)) ≤ 1 / 201 := by
    have hpi := Real.pi_gt_d2
    have hL1' : 0 < L - 1 := by linarith
    rw [show 3 / (2 * Real.pi ^ 2) * (1 / (L - 1) + 1 / (L - 1)) =
        3 / (Real.pi ^ 2 * (L - 1)) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num at hpi
    nlinarith
  rw [hsplit, htot]
  linarith

end WindowMassSharpProof

theorem window_mass_sharp (r t n : ℕ) (hn0 : 0 < n) (hnr : n < r) (hrt : 128 * r ≤ 2 ^ t) :
    (200 : ℝ) / 201 ≤ ∑ a ∈ Finset.range (2 ^ t),
      if (2 * r * a + 2 ^ t) / (2 * 2 ^ t) = n then
        Complex.normSq ((((2 ^ t : ℕ) : ℂ)⁻¹) * ∑ y ∈ Finset.range (2 ^ t),
          Complex.exp (Complex.I * ((2 * Real.pi * ((n : ℝ) / (r : ℝ) - (a : ℝ) / ((2 ^ t : ℕ) : ℝ)) : ℝ) : ℂ)) ^ y)
      else 0 :=
  WindowMassSharpProof.window_mass_sharp_aux r (2 ^ t) n hn0 hnr hrt

end ShorECDLP.Entrant

end

namespace ShorECDLP.Entrant.WindowMassSharpProof
open Finset
noncomputable section

/-- Concentration in a circular interval, including phases near zero. -/
theorem circular_mass (N : Nat) (hN : 0 < N) (β L : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hL : 1 < L) :
    1 - 3 / (Real.pi ^ 2 * (L - 1)) ≤
      ∑ a ∈ range N,
        if phiR N (N * β) a < L ∨ phiL N (N * β) a < L
        then ampSq N β a else 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let c : ℝ := N * β
  have hc0 : 0 ≤ c := mul_nonneg hNR.le hβ0
  have hcN : c < N := by dsimp [c]; nlinarith
  let S := (range N).filter (fun a => ¬ (phiR N c a < L ∨ phiL N c a < L))
  have hSN : ∀ a ∈ S, a < N := fun a ha => mem_range.mp (mem_filter.mp ha).1
  have hR : ∀ a ∈ S, L ≤ phiR N c a := by
    intro a ha
    exact le_of_not_gt (fun h => (mem_filter.mp ha).2 (Or.inl h))
  have hL' : ∀ a ∈ S, L ≤ phiL N c a := by
    intro a ha
    exact le_of_not_gt (fun h => (mem_filter.mp ha).2 (Or.inr h))
  have hpt : ∀ a ∈ S, ampSq N β a ≤
      3 / (2 * Real.pi ^ 2) * (1 / (phiR N c a) ^ 2 + 1 / (phiL N c a) ^ 2) := by
    intro a ha
    have haN : (a : ℝ) < N := by exact_mod_cast hSN a ha
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have hR' := hR a ha
    have hL'' := hL' a ha
    by_cases hca : c ≤ (a : ℝ)
    · have e1 : phiR N c a = (a : ℝ) - c := by simp [phiR, hca]
      have hu : 0 < (a : ℝ) - c := by rw [e1] at hR'; linarith
      have e2 : phiL N c a = (N : ℝ) - ((a : ℝ) - c) := by
        rw [phiL, if_neg (by linarith)]; ring
      rw [e1, e2]
      exact point_bound_sharp N hN (2 * Real.pi * (β - a / N)) ((a : ℝ) - c)
        hu (by linarith) (Or.inr (by dsimp [c]; field_simp; ring))
    · have hca' : (a : ℝ) < c := lt_of_not_ge hca
      have e1 : phiR N c a = (N : ℝ) - (c - (a : ℝ)) := by
        rw [phiR, if_neg hca]; ring
      have e2 : phiL N c a = c - (a : ℝ) := by simp [phiL, hca'.le]
      rw [e1, e2, add_comm (1 / ((N : ℝ) - (c - (a : ℝ))) ^ 2)]
      exact point_bound_sharp N hN (2 * Real.pi * (β - a / N)) (c - (a : ℝ))
        (by linarith) (by linarith) (Or.inl (by dsimp [c]; field_simp))
  have sR := sum_inv_sq_le S (phiR N c) L hL hR
    (fun a ha b hb h => phiR_sep N c a b (hSN a ha) (hSN b hb) h)
  have sL := sum_inv_sq_le S (phiL N c) L hL hL'
    (fun a ha b hb h => phiL_sep N c a b (hSN a ha) (hSN b hb) h)
  have htail : ∑ a ∈ S, ampSq N β a ≤ 3 / (Real.pi ^ 2 * (L - 1)) := by
    calc
      _ ≤ 3 / (2 * Real.pi ^ 2) * (1 / (L - 1) + 1 / (L - 1)) := by
        refine (sum_le_sum hpt).trans ?_
        rw [← mul_sum, sum_add_distrib]
        exact mul_le_mul_of_nonneg_left (add_le_add sR sL) (by positivity)
      _ = _ := by field_simp; ring
  have hsplit : (∑ a ∈ range N,
      if phiR N c a < L ∨ phiL N c a < L then ampSq N β a else 0) =
      (∑ a ∈ range N, ampSq N β a) - ∑ a ∈ S, ampSq N β a := by
    rw [eq_sub_iff_add_eq, show ∑ a ∈ S, ampSq N β a =
      ∑ a ∈ range N, if ¬ (phiR N c a < L ∨ phiL N c a < L) then ampSq N β a else 0
      from sum_filter _ _]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    split_ifs <;> simp
  change _ ≤ ∑ a ∈ range N, if phiR N c a < L ∨ phiL N c a < L then _ else _
  rw [hsplit, parseval N hN β]
  linarith

/-- A 512-outcome radius loses less than one part in a thousand. -/
theorem circular_mass_512 (N : Nat) (hN : 0 < N) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (999 : ℝ) / 1000 ≤ ∑ a ∈ range N,
      if phiR N (N * β) a < 512 ∨ phiL N (N * β) a < 512
      then ampSq N β a else 0 := by
  apply le_trans _ (circular_mass N hN β 512 hβ0 hβ1 (by norm_num))
  have hp := Real.pi_gt_d2
  have hden : 0 < Real.pi ^ 2 * ((512 : ℝ) - 1) := by positivity
  have ht : 3 / (Real.pi ^ 2 * ((512 : ℝ) - 1)) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    norm_num at hp ⊢
    nlinarith
  linarith

end
end ShorECDLP.Entrant.WindowMassSharpProof

namespace ShorECDLP.Entrant.RoundedReadout
noncomputable section

/-- Rounding is locally constant away from its half-integer boundaries. -/
theorem round_stable (x y ε : ℝ)
    (haway : |x - (round x : ℝ)| ≤ 1 / 2 - ε) (hclose : |y - x| < ε) :
    round y = round x := by
  apply round_eq_iff.mpr
  have hx := abs_le.mp haway
  have hy := abs_lt.mp hclose
  constructor <;> linarith

/-- A residue outside a short central interval stays clear of a rounding boundary. -/
theorem residue_away (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (ε : ℝ)
    (hε : 0 ≤ ε)
    (h : u ≤ 1 / 2 - ε ∨ 1 / 2 + ε ≤ u) :
    |u - (round u : ℝ)| ≤ 1 / 2 - ε := by
  rcases h with h | h
  · by_cases he : u = 1 / 2
    · have hz : ε = 0 := by linarith
      subst ε
      simpa using abs_sub_round u
    · have huHalf : u < 1 / 2 := lt_of_le_of_ne (by linarith) he
      have hr : round u = 0 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
      rw [hr]
      simpa only [Int.cast_zero, sub_zero, abs_of_nonneg hu0] using h
  · have hr : round u = 1 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    rw [hr]
    norm_num only [Int.cast_one]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Exact arithmetic for the proposed public resource bounds. -/
theorem target_score : 855 * 15399939344 = 13166948139120 := by norm_num

theorem one_trial_budget :
    2 * (ShorECDLP.order / 2 ^ 203 + 2) ≤ 56 * (2 ^ 49 + 2) := by decide +kernel

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open Finset
noncomputable section

/-- Residues within one part in 1024 of a half-bin boundary are discarded. -/
def boundaryResidues (r : Nat) : Finset Nat :=
  (range r).filter (fun z => 511 * r / 1024 ≤ z ∧ z ≤ 513 * r / 1024 + 1)

theorem boundaryResidues_card (r : Nat) :
    (boundaryResidues r).card ≤ r / 512 + 4 := by
  have hs : boundaryResidues r ⊆ Icc (511 * r / 1024) (513 * r / 1024 + 1) := by
    intro z hz
    exact mem_Icc.mpr (mem_filter.mp hz).2
  have hc := card_le_card hs
  rw [Nat.card_Icc] at hc
  have hhi := Nat.div_mul_le_self (513 * r) 1024
  have hlo := Nat.lt_mul_div_succ (511 * r) (by omega : 0 < 1024)
  have hdiv := Nat.lt_mul_div_succ r (by omega : 0 < 512)
  have hwidth : 513 * r / 1024 + 2 ≤ 511 * r / 1024 + (r / 512 + 4) := by
    nlinarith
  exact hc.trans (Nat.sub_le_of_le_add (by omega))

theorem outside_boundary (r z : Nat) (hr : 0 < r) (hz : z < r)
    (h : z ∉ boundaryResidues r) :
    (z : ℝ) / r ≤ 1 / 2 - 1 / 1024 ∨
      1 / 2 + 1 / 1024 ≤ (z : ℝ) / r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hh : z < 511 * r / 1024 ∨ 513 * r / 1024 + 1 < z := by
    simp only [boundaryResidues, mem_filter, mem_range, hz, true_and, not_and_or,
      not_le] at h
    exact h
  rcases hh with h | h
  · left
    rw [div_le_iff₀ hrR]
    have hf := Nat.div_mul_le_self (511 * r) 1024
    have hn : 1024 * z ≤ 511 * r := by nlinarith
    have hn' : (1024 : ℝ) * z ≤ 511 * r := by exact_mod_cast hn
    linarith
  · right
    rw [le_div_iff₀ hrR]
    have hf := Nat.lt_mul_div_succ (513 * r) (by omega : 0 < 1024)
    have hn : 513 * r ≤ 1024 * z := by nlinarith
    have hn' : (513 : ℝ) * r ≤ 1024 * z := by exact_mod_cast hn
    linarith

theorem outside_boundary_round (r z : Nat) (hr : 0 < r) (hz : z < r)
    (h : z ∉ boundaryResidues r) :
    |(z : ℝ) / r - (round ((z : ℝ) / r) : ℝ)| ≤ 1 / 2 - 1 / 1024 := by
  apply residue_away _ (by positivity) ((div_lt_one (by exact_mod_cast hr)).mpr
    (by exact_mod_cast hz)) _ (by norm_num)
  exact outside_boundary r z hr hz h

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816
open ShorECDLP.Entrant.WindowMassSharpProof
open scoped BigOperators
noncomputable section

theorem ratio_round_away (n r : Nat) (hr : 0 < r)
    (h : n % r ∉ boundaryResidues r) :
    |(n : ℝ) / r - (round ((n : ℝ) / r) : ℝ)| ≤ 1 / 2 - 1 / 1024 := by
  have he : (n : ℝ) / r = (n % r : Nat) / (r : ℝ) + (n / r : Nat) := by
    have hn := congrArg (fun a : Nat => (a : ℝ)) (Nat.mod_add_div n r)
    push_cast at hn
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
    nlinarith
  rw [he, round_add_natCast]
  simp only [Int.cast_add, Int.cast_natCast]
  simpa only [add_sub_add_right_eq_sub] using outside_boundary_round r (n % r) hr
    (Nat.mod_lt _ hr) h

theorem round_nat_ratio (n r : Nat) (hr : 0 < r) :
    round ((n : ℝ) / r) = ((2 * n + r) / (2 * r) : Nat) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hlo := Nat.div_mul_le_self (2 * n + r) (2 * r)
  have hhi := Nat.lt_mul_div_succ (2 * n + r) (by omega : 0 < 2 * r)
  have hl : ((2 * n + r) / (2 * r) : Nat) * (2 * (r : ℝ)) ≤ 2 * n + r := by exact_mod_cast hlo
  have hh : 2 * (n : ℝ) + r < 2 * r * (((2 * n + r) / (2 * r) : Nat) + 1) := by exact_mod_cast hhi
  apply round_eq_iff.mpr
  simp only [Int.cast_natCast]
  constructor
  · rw [le_div_iff₀ hrR]; nlinarith
  · rw [div_lt_iff₀ hrR]; nlinarith

theorem round_half_bin (b D : Nat) (hD : 0 < D) :
    round ((b : ℝ) / (2 * D)) = ((b + D) / (2 * D) : Nat) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hlo := Nat.div_mul_le_self (b + D) (2 * D)
  have hhi := Nat.lt_mul_div_succ (b + D) (by omega : 0 < 2 * D)
  have hl : ((b + D) / (2 * D) : Nat) * (2 * (D : ℝ)) ≤ b + D := by exact_mod_cast hlo
  have hh : (b : ℝ) + D < 2 * D * (((b + D) / (2 * D) : Nat) + 1) := by exact_mod_cast hhi
  apply round_eq_iff.mpr
  simp only [Int.cast_natCast]
  constructor
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * D)]; nlinarith
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * D)]; nlinarith

/-- Circular closeness is ordinary closeness after an integer-period lift. -/
theorem circular_close_lift (M S b : Nat) (hS : 0 < S) (hb : b < M*S) (β L : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : phiR (M*S) ((M*S : Nat) * β) b < L ∨
      phiL (M*S) ((M*S : Nat) * β) b < L) :
    ∃ z : ℤ, |(b : ℝ) / S + z * M - (M : ℝ) * β| < L / S := by
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hMS : (0 : ℝ) < (M*S : Nat) := by exact_mod_cast (show 0 < M*S by omega)
  have hc0 : 0 ≤ ((M*S : Nat) : ℝ) * β := mul_nonneg hMS.le hβ0
  have hcN : ((M*S : Nat) : ℝ) * β < (M*S : Nat) := by nlinarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hbN : (b : ℝ) < (M*S : Nat) := by exact_mod_cast hb
  push_cast at hc0 hcN hbN
  rcases hc with hc | hc
  · unfold phiR at hc
    split_ifs at hc with h
    · refine ⟨0, ?_⟩
      norm_num only [Int.cast_zero, zero_mul, add_zero]
      rw [abs_lt]
      push_cast at hc h
      have he : (b : ℝ) / S * S = b := div_mul_cancel₀ _ hSR.ne'
      constructor
      · rw [← neg_div, div_lt_iff₀ hSR]; nlinarith
      · rw [lt_div_iff₀ hSR]; nlinarith
    · refine ⟨1, ?_⟩
      norm_num only [Int.cast_one, one_mul]
      rw [abs_lt]
      push_cast at hc h
      have he : (b : ℝ) / S * S = b := div_mul_cancel₀ _ hSR.ne'
      constructor
      · rw [← neg_div, div_lt_iff₀ hSR]; nlinarith
      · rw [lt_div_iff₀ hSR]; nlinarith
  · unfold phiL at hc
    split_ifs at hc with h
    · refine ⟨0, ?_⟩
      norm_num only [Int.cast_zero, zero_mul, add_zero]
      rw [abs_lt]
      push_cast at hc h
      have he : (b : ℝ) / S * S = b := div_mul_cancel₀ _ hSR.ne'
      constructor
      · rw [← neg_div, div_lt_iff₀ hSR]; nlinarith
      · rw [lt_div_iff₀ hSR]; nlinarith
    · refine ⟨-1, ?_⟩
      norm_num only [Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      rw [abs_lt]
      push_cast at hc h
      have he : (b : ℝ) / S * S = b := div_mul_cancel₀ _ hSR.ne'
      constructor
      · rw [← neg_div, div_lt_iff₀ hSR]; nlinarith
      · rw [lt_div_iff₀ hSR]; nlinarith

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open scoped BigOperators
noncomputable section
theorem sum_mulMod (r a : Nat) (hr : r.Prime) (ha : ¬ r ∣ a) (H : ℕ → ℝ) :
    ∑ k : Fin r, H ((a * k.val) % r) = ∑ c ∈ Finset.range r, H c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => H ((a*k) % r))]
  haveI := Fact.mk hr
  have hinj : Set.InjOn (fun k => (a*k) % r) (Finset.range r) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have h1 : ((a*x : ℕ) : ZMod r) = ((a*y : ℕ) : ZMod r) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).2 hxy
    have ha' : (a : ZMod r) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    push_cast at h1
    have h2 : (x : ZMod r) = y := mul_left_cancel₀ ha' h1
    have h3 := (ZMod.natCast_eq_natCast_iff' x y r).1 h2
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h3
  have himage : (Finset.range r).image (fun k => (a*k) % r) = Finset.range r := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hc
      exact Finset.mem_range.2 (Nat.mod_lt _ hr.pos)
    · rw [Finset.card_image_of_injOn hinj]
  conv_rhs => rw [← himage]
  rw [Finset.sum_image hinj]

/-- Removing boundary residues and the zero character leaves ample mass. -/
theorem average_boundary_loss (r a : Nat) (hr : r.Prime) (ha : ¬ r ∣ a)
    (hrLarge : 1000000 ≤ r) (mass : Fin r → ℝ)
    (hm0 : ∀ k, 0 ≤ mass k)
    (hm : ∀ k, k.val ≠ 0 → (a*k.val)%r ∉ boundaryResidues r →
      (999 : ℝ)/1000 ≤ mass k) :
    (997 : ℝ)/1000 * r ≤ ∑ k : Fin r, if k.val = 0 then 0 else mass k := by
  classical
  let H : Nat → ℝ := fun z => if z ∈ boundaryResidues r then 0 else 1
  have hH : ∑ z ∈ Finset.range r, H z = (r : ℝ) - (boundaryResidues r).card := by
    have he : ∑ z ∈ Finset.range r, (if z ∈ boundaryResidues r then (1 : ℝ) else 0) =
        (boundaryResidues r).card := by
      rw [← Finset.sum_filter]
      have hf : (Finset.range r).filter (fun z => z ∈ boundaryResidues r) = boundaryResidues r := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
        exact fun h => Finset.mem_range.mp (Finset.mem_filter.mp h).1
      rw [hf]
      simp
    calc
      _ = (∑ _z ∈ Finset.range r, (1 : ℝ)) -
          ∑ z ∈ Finset.range r, if z ∈ boundaryResidues r then 1 else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro z _
        dsimp [H]
        split_ifs <;> norm_num
      _ = _ := by rw [he]; simp
  have hperm := sum_mulMod r a hr ha H
  rw [hH] at hperm
  have hzero : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
    have hr0 : 0 < r := hr.pos
    rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
    simp [hr0]
  have hp : ∀ k : Fin r,
      (999 : ℝ)/1000 * H ((a*k.val)%r) - (if k.val = 0 then 1 else 0) ≤
        if k.val = 0 then 0 else mass k := by
    intro k
    by_cases hk : k.val = 0
    · rw [if_pos hk, if_pos hk]
      dsimp [H]
      split_ifs <;> norm_num
    · rw [if_neg hk, if_neg hk, sub_zero]
      dsimp [H]
      split_ifs with hb
      · simpa using hm0 k
      · simpa using hm k hk hb
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hp k)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hperm, hzero] at hs
  have hc := boundaryResidues_card r
  have hd := Nat.div_mul_le_self r 512
  have hcR : ((boundaryResidues r).card : ℝ) ≤ (r / 512 : Nat) + 4 := by exact_mod_cast hc
  have hdR : (r / 512 : Nat) * (512 : ℝ) ≤ r := by exact_mod_cast hd
  have hrR : (1000000 : ℝ) ≤ r := by exact_mod_cast hrLarge
  linarith

end
end ShorECDLP.Entrant.RoundedReadout
namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816
open ShorECDLP.Entrant.WindowMassSharpProof
open scoped BigOperators
noncomputable section
set_option exponentiation.threshold 300

/-- Add half a coarse bin and drop 21 low bits, wrapping at the endpoint. -/
def coarseRound (b : Nat) : Nat := (b + 2^20) / 2^21 % 2^203

theorem coarseRound_correct (r : Nat) (hr : 0 < r) (k : Fin r) (b : Fin (2^224))
    (haway : (2^203*k.val)%r ∉ boundaryResidues r)
    (hc : phiR (2^224) ((2^224 : Nat) * ((k.val : ℝ) / r)) b.val < 512 ∨
      phiL (2^224) ((2^224 : Nat) * ((k.val : ℝ) / r)) b.val < 512) :
    coarseRound b.val = (reducedPeak r 203 k).val := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hβ0 : 0 ≤ (k.val : ℝ) / r := by positivity
  have hβ1 : (k.val : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast k.isLt)
  have heN : (2^203 : Nat) * 2^21 = 2^224 := by norm_num
  have hlift := circular_close_lift (2^203) (2^21) b.val (by positivity)
    (by simpa only [heN] using b.isLt) ((k.val : ℝ)/r) 512 hβ0 hβ1
    (by simpa only [heN] using hc)
  obtain ⟨z, hz⟩ := hlift
  have hphase := ratio_round_away (2^203 * k.val) r hr haway
  have hephase : ((2^203 * k.val : Nat) : ℝ) / r =
      ((2^203 : Nat) : ℝ) * ((k.val : ℝ) / r) := by push_cast; ring
  rw [hephase] at hphase
  have hclose : |(b.val : ℝ) / (2^21 : Nat) + z * (2^203 : Nat) -
      (2^203 : Nat) * ((k.val : ℝ) / r)| < 1 / 1024 := by
    apply hz.trans_le
    norm_num
  have hs := round_stable _ _ (1/1024) hphase hclose
  have hez : (z : ℝ) * (2^203 : Nat) = ((z * (2^203 : Nat) : ℤ) : ℝ) := by
    simp only [Int.cast_mul, Int.cast_natCast]
  rw [hez, round_add_intCast, ← hephase, round_nat_ratio _ r hr] at hs
  have hh := round_half_bin b.val (2^20) (by positivity)
  have heS : (2 : ℝ) * (2^20 : Nat) = (2^21 : Nat) := by norm_num
  have heD : (2 : Nat) * 2^20 = 2^21 := by norm_num
  rw [heS, heD] at hh
  rw [hh] at hs
  have hm := congrArg (fun x : ℤ => x % (2^203 : Nat)) hs
  dsimp only at hm
  rw [Int.add_mul_emod_self_right] at hm
  have hcast : ((coarseRound b.val : Nat) : ℤ) = ((reducedPeak r 203 k).val : ℤ) := by
    simpa only [coarseRound, reducedPeak, reducedPeakRaw, Int.natCast_mod,
      Nat.mul_assoc] using hm
  exact_mod_cast hcast

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open ShorECDLP.Entrant.WindowMassSharpProof
open scoped BigOperators
noncomputable section

set_option exponentiation.threshold 300

def coarseMass (r : Nat) (k : Fin r) : ℝ := ∑ b : Fin (2^224),
  if coarseRound b.val = (reducedPeak r 203 k).val then
    Complex.normSq (paperPhaseAmplitude 224 ((k.val : ℝ) / r) b.val) else 0

theorem coarseMass_nonneg (r : Nat) (k : Fin r) : 0 ≤ coarseMass r k := by
  unfold coarseMass
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem coarseMass_lower (r : Nat) (hr : 0 < r) (k : Fin r)
    (haway : (2^203*k.val)%r ∉ boundaryResidues r) :
    (999 : ℝ)/1000 ≤ coarseMass r k := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hc := circular_mass_512 (2^224) (by positivity) ((k.val : ℝ)/r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt))
  have hfin : (999 : ℝ)/1000 ≤ ∑ b : Fin (2^224),
      if phiR (2^224) ((2^224 : Nat) * ((k.val : ℝ)/r)) b.val < 512 ∨
        phiL (2^224) ((2^224 : Nat) * ((k.val : ℝ)/r)) b.val < 512
      then Complex.normSq (paperPhaseAmplitude 224 ((k.val : ℝ)/r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2^224) ((2^224 : Nat) * ((k.val : ℝ)/r)) b < 512 ∨
        phiL (2^224) ((2^224 : Nat) * ((k.val : ℝ)/r)) b < 512
      then Complex.normSq (paperPhaseAmplitude 224 ((k.val : ℝ)/r) b) else 0)]
    simpa only [ampSq, paperPhaseAmplitude, eigenvalue] using hc
  refine hfin.trans (Finset.sum_le_sum (fun b _ => ?_))
  dsimp only
  split_ifs with hnear heq
  · rfl
  · exact (heq (coarseRound_correct r hr k b haway hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem coarseMass_average (r a : Nat) (hr : r.Prime) (ha : ¬ r ∣ a)
    (hrLarge : 1000000 ≤ r) :
    (997 : ℝ)/1000 * r ≤ ∑ k : Fin r, if k.val = 0 then 0 else
      coarseMass r ⟨a*k.val % r, Nat.mod_lt _ hr.pos⟩ := by
  have hpow : ¬ r ∣ 2^203 := by
    intro h
    have h2 := hr.dvd_of_dvd_pow h
    have hr2 : r ≤ 2 := Nat.le_of_dvd (by omega) h2
    omega
  apply average_boundary_loss r (2^203*a) hr (by
    intro h
    rcases hr.dvd_mul.mp h with h | h
    · exact hpow h
    · exact ha h) hrLarge _
    (fun k => coarseMass_nonneg _ _)
  intro k _ hk
  apply coarseMass_lower r hr.pos
  simpa only [Nat.mul_mod, Nat.mod_mod, Nat.mul_assoc] using hk

end
end ShorECDLP.Entrant.RoundedReadout
namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

set_option maxRecDepth 4096 in
/-- The left exact-numerator window and the averaged rounded right register combine. -/
theorem rounded_pair_coverage (r n d : Nat) (hr : r.Prime) (hd : ¬ r ∣ d)
    (hrLarge : 1000000 ≤ r) (hprecision : 128*r ≤ 2^n)
    (accept : Fin (2^n) → Fin (2^224) → Prop) [∀ a b, Decidable (accept a b)]
    (haccept : ∀ (k : Fin r), k.val ≠ 0 → ∀ a b,
      nearestNumerator r n a.val = k.val →
      coarseRound b.val = (reducedPeak r 203 ⟨d*k.val%r, Nat.mod_lt _ hr.pos⟩).val →
      accept a b) :
    (200 : ℝ)/201 * (997/1000) ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^224),
      if accept a b then asymmetricPairMass r n 224 d (a,b) else 0 := by
  classical
  let A : Fin r → Fin (2^n) → ℝ := fun k a =>
    Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ)/r) a.val)
  let B : Fin r → Fin (2^224) → ℝ := fun k b =>
    Complex.normSq (paperPhaseAmplitude 224 (((d*k.val%r : Nat) : ℝ)/r) b.val)
  let good : Fin r → Fin (2^n) → Fin (2^224) → Prop := fun k a b =>
    k.val ≠ 0 ∧ nearestNumerator r n a.val = k.val ∧
      coarseRound b.val = (reducedPeak r 203 ⟨d*k.val%r, Nat.mod_lt _ hr.pos⟩).val
  let F : Fin r → Fin (2^n) → Fin (2^224) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  have hA : ∀ k a, 0 ≤ A k a := fun _ _ => Complex.normSq_nonneg _
  have hB : ∀ k b, 0 ≤ B k b := fun _ _ => Complex.normSq_nonneg _
  have hF : ∀ k a b, 0 ≤ F k a b := by
    intro k a b
    dsimp only [F]
    split_ifs
    · exact mul_nonneg (hA k a) (hB k b)
    · exact le_rfl
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hrinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  have hjp : ∀ a : Fin (2^n), ∀ b : Fin (2^224),
      asymmetricPairMass r n 224 d (a,b) = (r : ℝ)⁻¹ * ∑ k : Fin r, A k a * B k b := by
    intro a b
    simp only [asymmetricPairMass, one_div, A, B]
  have step1 :
      ∑ a : Fin (2^n), ∑ b : Fin (2^224), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2^n), ∑ b : Fin (2^224),
          if accept a b then asymmetricPairMass r n 224 d (a,b) else 0 := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    by_cases hp : accept a b
    · rw [if_pos hp, hjp]
      apply mul_le_mul_of_nonneg_left _ hrinv
      apply Finset.sum_le_sum
      intro k _
      dsimp only [F]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hA k a) (hB k b)
    · rw [if_neg hp]
      have hz : ∀ k, F k a b = 0 := by
        intro k
        dsimp only [F]
        rw [if_neg]
        rintro ⟨hk, ha, hb⟩
        exact hp (haccept k hk a b ha hb)
      simp [hz]
  have step2 :
      (r : ℝ)⁻¹ * ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^224), F k a b =
        ∑ a : Fin (2^n), ∑ b : Fin (2^224), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have hleft (k : Fin r) (hk : k.val ≠ 0) :
      (200 : ℝ)/201 ≤ ∑ a : Fin (2^n),
        if nearestNumerator r n a.val = k.val then A k a else 0 := by
    have h := ShorECDLP.Entrant.window_mass_sharp r n k.val
      (Nat.pos_of_ne_zero hk) k.isLt hprecision
    rw [Fin.sum_univ_eq_sum_range (fun a =>
      if nearestNumerator r n a = k.val then
        Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ)/r) a) else 0)]
    simpa only [nearestNumerator, paperPhaseAmplitude, eigenvalue] using h
  have step3 : ∀ k : Fin r,
      (200 : ℝ)/201 * (if k.val = 0 then 0 else
        coarseMass r ⟨d*k.val%r, Nat.mod_lt _ hr.pos⟩) ≤
      ∑ a : Fin (2^n), ∑ b : Fin (2^224), F k a b := by
    intro k
    by_cases hk : k.val = 0
    · rw [if_pos hk, mul_zero]
      exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF k a b))
    · rw [if_neg hk]
      have he : (∑ a : Fin (2^n), ∑ b : Fin (2^224), F k a b) =
          (∑ a : Fin (2^n), if nearestNumerator r n a.val = k.val then A k a else 0) *
            coarseMass r ⟨d*k.val%r, Nat.mod_lt _ hr.pos⟩ := by
        rw [coarseMass, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F, good, B]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [he]
      exact mul_le_mul_of_nonneg_right (hleft k hk) (coarseMass_nonneg _ _)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  rw [← Finset.mul_sum] at hsum
  have havg := coarseMass_average r d hr hd hrLarge
  have hprod : (200 : ℝ)/201 * ((997:ℝ)/1000*r) ≤
      ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^224), F k a b :=
    (mul_le_mul_of_nonneg_left havg (by norm_num)).trans hsum
  have hlower := mul_le_mul_of_nonneg_left hprod hrinv
  have heval : (r : ℝ)⁻¹ * ((200:ℝ)/201 * ((997:ℝ)/1000*r)) =
      (200:ℝ)/201 * ((997:ℝ)/1000) := by field_simp
  rw [heval, step2] at hlower
  exact hlower.trans step1

end
end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816
open scoped BigOperators
noncomputable section
set_option exponentiation.threshold 300

def decoderParams : DecoderParams := ⟨263, 203, by omega, by omega, by omega, by omega⟩

def pairRecovered (d a b : Nat) : Bool :=
  decide ((d : ZMod order) ∈ fixedCandidates decoderParams a (coarseRound b))

theorem pairRecovered_of_character (d : Nat) (k : Fin order) (hk : k.val ≠ 0)
    (a : Fin (2^263)) (b : Fin (2^224))
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 263 a.val = k.val)
    (hb : coarseRound b.val = (reducedPeak order 203
      ⟨d*k.val%order, Nat.mod_lt _ order_prime.pos⟩).val) :
    pairRecovered d a.val b.val = true := by
  haveI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have hk0 : ((k.val : Nat) : ZMod order) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
  apply decide_eq_true
  unfold fixedCandidates
  apply Finset.mem_image.mpr
  refine ⟨d*k.val%order, ?_, ?_⟩
  · change d*k.val%order ∈ wrappedNumeratorCandidates order 203 (coarseRound b.val)
    rw [hb]
    exact reducedPeak_mem_candidates order 203 _
  · change ((d*k.val%order : Nat) : ZMod order) *
      (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 263 a.val : ZMod order)⁻¹ = d
    rw [ha]
    simp only [ZMod.natCast_mod, Nat.cast_mul]
    field_simp

theorem secret_not_dvd (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    ¬ order ∣ d := by
  intro h
  obtain ⟨k, rfl⟩ := h
  apply hn
  rw [hd, mul_nsmul, generator_nsmul_eq_zero, nsmul_zero]

theorem pair_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ)/100 ≤ ∑ a : Fin (2^263), ∑ b : Fin (2^224),
      if pairRecovered d a.val b.val then asymmetricPairMass order 263 224 d (a,b) else 0 := by
  have h := rounded_pair_coverage order 263 d order_prime (secret_not_dvd Q d hn hd)
    (by norm_num [order]) (by norm_num [order])
    (fun a b => pairRecovered d a.val b.val = true)
    (fun k hk a b ha hb => pairRecovered_of_character d k hk a b ha hb)
  exact (by norm_num : (99:ℝ)/100 ≤ 200/201*(997/1000)).trans h

end
end ShorECDLP.Entrant.RoundedReadout


/-! EDITABLE. Single-trial entrant: mixed-width distribution and decoder proofs.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/History ====

section
/-! Dynamic histories for compositional straight-program distribution proofs.
The protected straight semantics and record decomposition are Apache-2.0;
see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Total extension; actual branches have exactly the required record length. -/
def historyAfter {start : Nat} (finish : Nat) (history : Fin start → Bool)
    (bits : List Bool) : Fin finish → Bool :=
  fun i => ((List.ofFn history ++ bits)[i.val]?).getD false

theorem historyAfter_nil {start : Nat} (history : Fin start → Bool) :
    historyAfter start history List.nil = history := by
  funext i
  simp [historyAfter]

theorem historyAfter_step {start : Nat} (finish : Nat) (history : Fin start → Bool)
    (bit : Bool) (bits : List Bool) :
    historyAfter finish (Fin.lastCases bit history) bits =
      historyAfter finish history (bit :: bits) := by
  funext i
  simp only [historyAfter, List.ofFn_succ', Fin.lastCases_castSucc, Fin.lastCases_last,
    List.concat_eq_append, List.append_assoc, List.singleton_append]

theorem historyAfter_list {start finish : Nat} (history : Fin start → Bool)
    (bits : List Bool) (hlen : start + bits.length = finish) :
    List.ofFn (historyAfter finish history bits) = List.ofFn history ++ bits := by
  apply List.ext_getElem
  · simpa using hlen.symm
  · intro i hi hj
    simp only [List.getElem_ofFn, historyAfter]
    rw [List.getElem?_eq_getElem hj, Option.getD_some]

/-- Exact branch enumeration, retaining the history used by the suffix. -/
theorem append_run_history {n start mid finish : Nat}
    (p : Straight n start mid) (q : Straight n mid finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((p.append q).instantiate read history).run =
      ((p.instantiate read history).run).flatMap (fun a =>
        ((q.instantiate read (historyAfter mid history a.history)).run).map a.seq) := by
  induction p with
  | done =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.run,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, historyAfter_nil]
    apply Eq.symm
    apply List.map_id'
  | gate g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.run, ih,
      List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    apply List.map_congr_left
    intro b hb
    rfl
  | recordGate i v g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.run, ih,
      List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    apply List.map_congr_left
    intro b hb
    rfl
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.run, ih,
      List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
      List.flatMap_append]
    congr 1 <;>
      (apply List.flatMap_congr; intro a ha
       simp only [historyAfter_step]
       apply List.map_congr_left; intro b hb; rfl)

theorem historyAfter_old {start finish : Nat} (history : Fin start → Bool)
    (bits : List Bool) (hle : start ≤ finish) (i : Fin start) :
    historyAfter finish history bits ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = history i := by
  simp only [historyAfter]
  rw [List.getElem?_append_left (show i.val < (List.ofFn history).length by
    simpa only [List.length_ofFn] using i.isLt)]
  simp

theorem bankPrior_map {start : Nat} (count : Nat) (prior : List (Fin start))
    (history : Fin start → Bool) (bits : List Bool) :
    (bankPrior count prior).map (historyAfter (start + count) history bits) = prior.map history := by
  simp only [bankPrior, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  exact historyAfter_old history bits (by omega) i

theorem nextPrior_map {start : Nat} (count width : Nat) (prior : List (Fin start))
    (history : Fin start → Bool) (arith bits : List Bool)
    (ha : arith.length = count) (hb : bits.length = width) :
    (nextPrior count width prior).map
      (historyAfter (start + count + width)
        (historyAfter (start + count) history arith) bits) = bits.reverse ++ prior.map history := by
  let h₁ := historyAfter (start + count) history arith
  have hold (i : Fin start) :
      historyAfter (start + count + width) h₁ bits ⟨i.val, by omega⟩ = history i := by
    rw [historyAfter_old h₁ bits (by omega) ⟨i.val, by omega⟩]
    exact historyAfter_old history arith (by omega) i
  have hbits : List.ofFn (fun i : Fin width =>
      historyAfter (start + count + width) h₁ bits ⟨start + count + i.val, by omega⟩) = bits := by
    apply List.ext_getElem
    · simp [hb]
    · intro i hi hj
      simp only [List.getElem_ofFn, historyAfter]
      rw [List.getElem?_append_right (by simp)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem hj, Option.getD_some]
  simp only [nextPrior, List.map_append, List.map_reverse, List.map_ofFn, List.map_map,
    Function.comp_def]
  rw [hbits]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hold i

/-- Preparation contributes no records and is an ordinary Hadamard prefix. -/
theorem prepare_run {n start finish : Nat} (ws : List Wire) (p : Straight n start finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((prepareOuterBank ws p).instantiate read history).run =
      ((p.instantiate read history).run).map (fun b =>
        ({ history := List.nil, kraus := Quantum.run (ws.map Gate.H) } : InstrumentBranch).seq b) := by
  induction ws with
  | nil =>
    simp only [prepareOuterBank, List.foldr_nil, List.map_nil, Quantum.run]
    apply Eq.symm
    apply List.map_id'
  | cons w ws ih =>
    change (AdaptiveCircuit.unitary [.H w]
      ((prepareOuterBank ws p).instantiate read history)).run = _
    simp only [AdaptiveCircuit.run, ih, List.map_map, Function.comp_def, List.map_cons]
    apply List.map_congr_left
    intro b hb
    rfl

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Transcript ====

section
/-! Mixed-width transcript extraction, adapted from the Apache-2.0 licensed
Streaming fixed-word proof; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

inductive Transcript : List (Nat × Nat) → List Bool → List Bool → Prop
  | nil : Transcript List.nil List.nil List.nil
  | cons (count width : Nat) (ws : List (Nat × Nat)) (a bits rest out : List Bool)
      (ha : a.length = count) (hb : bits.length = width)
      (ht : Transcript ws rest out) :
      Transcript ((count, width) :: ws) (a ++ bits ++ rest) (bits ++ out)

theorem Transcript.actual_bits {ws : List (Nat × Nat)} {history bits : List Bool}
    (h : Transcript ws history bits) (before after : List Bool) :
    (positions ws before.length).map (fun i => (before ++ history ++ after)[i]?) = bits.map some := by
  induction h generalizing before with
  | nil => rfl
  | cons count width ws a bs rest out ha hb ht ih =>
    rw [positions, List.map_append, List.map_append]
    have hhead := actual_bits_range (before ++ a) bs (rest ++ after)
    have htail := ih (before ++ a ++ bs)
    simp only [List.length_append, ha, hb, List.append_assoc] at hhead htail
    simp only [List.append_assoc, Nat.add_assoc]
    rw [hhead, htail]

theorem Transcript.readWord {ws : List (Nat × Nat)} {history bits : List Bool}
    (h : Transcript ws history bits) (before after : List Bool) :
    ShorECDLP.Challenge.readWord (before ++ history ++ after) (positions ws before.length) =
      some (fourierWordLSB bits) :=
  readWord_of_actual_bits _ _ _ (h.actual_bits before after)

theorem Transcript.history_length {ws : List (Nat × Nat)} {history bits : List Bool}
    (h : Transcript ws history bits) : history.length = recordCount ws := by
  induction h with
  | nil => rfl
  | cons count width ws a bs rest out ha hb ht ih =>
    simp only [List.length_append, ha, hb, ih, recordCount]

theorem Transcript.bits_length {ws : List (Nat × Nat)} {history bits : List Bool}
    (h : Transcript ws history bits) : bits.length = (ws.map Prod.snd).sum := by
  induction h with
  | nil => rfl
  | cons count width ws a bs rest out ha hb ht ih =>
    simp only [List.length_append, hb, ih, List.map_cons, List.sum_cons]

/-- Every actual straight-axis branch has a mixed-width transcript decomposition. -/
theorem axis_transcript {n : Nat} (ws : List (Window n))
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((axis ws start prior).instantiate read history).run) :
    ∃ bits, Transcript (ws.map (fun w => (w.count, w.wires.length))) b.history bits := by
  induction ws generalizing start b with
  | nil =>
    simp only [axis, Straight.instantiate, AdaptiveCircuit.run, List.mem_singleton] at hb
    subst b
    exact ⟨[], Transcript.nil⟩
  | cons w ws ih =>
    simp only [axis, castFinish_instantiate] at hb
    obtain ⟨h₁, a, rest, ha, hr, he₁, rfl⟩ := straight_append_branch _ _ read history b hb
    obtain ⟨h₂, f, c, hf, hc, he₂, rfl⟩ := straight_append_branch _ _ read h₁ rest hr
    obtain ⟨bits, hbits⟩ := ih _ _ h₂ c hc
    have hla : a.history.length = w.count := by
      have h := straight_history_length _ read history a ha
      omega
    have hlf : f.history.length = w.wires.length := by
      have h := straight_history_length _ read h₁ f hf
      omega
    refine ⟨f.history ++ bits, ?_⟩
    simpa only [List.map_cons, InstrumentBranch.seq, List.append_assoc] using
      Transcript.cons w.count w.wires.length _ a.history f.history c.history bits hla hlf hbits

theorem axis_readWord {n : Nat} (ws : List (Window n))
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((axis ws start prior).instantiate read history).run) (suffix : List Bool) :
    ∃ bits, Transcript (ws.map (fun w => (w.count, w.wires.length))) b.history bits ∧
      ShorECDLP.Challenge.readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions ws start) = some (fourierWordLSB bits) := by
  obtain ⟨bits, h⟩ := axis_transcript ws start prior read history b hb
  exact ⟨bits, h, by simpa only [List.length_ofFn] using h.readWord (List.ofFn history) suffix⟩

/-- Readout for the proposed concrete metadata, allowing an arbitrary reset suffix. -/
theorem layout_readWords (leftHistory rightHistory leftBits rightBits after : List Bool)
    (hl : Transcript leftMetadata leftHistory leftBits)
    (hr : Transcript rightMetadata rightHistory rightBits) :
    ShorECDLP.Challenge.readWord (leftHistory ++ rightHistory ++ after) trialPositions.left.toList =
      some (fourierWordLSB leftBits) ∧
    ShorECDLP.Challenge.readWord (leftHistory ++ rightHistory ++ after) trialPositions.right.toList =
      some (fourierWordLSB rightBits) := by
  have hleft := hl.readWord List.nil (rightHistory ++ after)
  have hright := hr.readWord leftHistory after
  rw [hl.history_length, left_record_count] at hright
  constructor
  · simpa only [List.nil_append, List.length_nil, trialPositions, Vector.toList_mk,
      List.toList_toArray, List.append_assoc] using hleft
  · simpa only [trialPositions, Vector.toList_mk, List.toList_toArray] using hright

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Words ====

section
/-! Mixed-radix path enumeration. Adapted from the Apache-2.0 licensed
Streaming distribution proof; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] fourierOutcomes

/-- Enumerate exactly one fixed-width word per chronological window. -/
def inputWords : List Nat → List (List (List Bool))
  | [] => [[]]
  | w :: ws => (fourierOutcomes w).flatMap (fun input =>
      (inputWords ws).map (fun rest => input :: rest))

theorem inputWords_mem (ws : List Nat) (inputs : List (List Bool)) :
    inputs ∈ inputWords ws ↔ inputs.map List.length = ws := by
  induction ws generalizing inputs with
  | nil => cases inputs <;> simp [inputWords]
  | cons w ws ih =>
    cases inputs with
    | nil => simp [inputWords, List.mem_flatMap]
    | cons input inputs =>
      simp [inputWords, List.mem_flatMap, List.mem_map, List.cons.injEq,
        fourierOutcomes_mem, ih, and_assoc, and_left_comm, and_comm]

theorem flatten_length_of_widths (inputs : List (List Bool)) :
    inputs.flatten.length = (inputs.map List.length).sum := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih => simp only [List.flatten_cons, List.length_append,
      List.map_cons, List.sum_cons, ih]

theorem outcomes_append (n m : Nat) : fourierOutcomes (n + m) =
    (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a ++ b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add, fourierOutcomes, ih, List.flatMap_append, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def, List.cons_append]

theorem inputWords_flatten (ws : List Nat) :
    (inputWords ws).map List.flatten = fourierOutcomes ws.sum := by
  induction ws with
  | nil => simp [inputWords, fourierOutcomes]
  | cons w ws ih =>
    rw [List.sum_cons, outcomes_append]
    simp only [inputWords, List.map_flatMap, List.map_map, Function.comp_def, List.flatten_cons]
    apply congrArg (List.flatMap · (fourierOutcomes w))
    funext input
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map (input ++ ·)) ih

theorem outcomes_reverse_perm (n : Nat) :
    ((fourierOutcomes n).map List.reverse).Perm (fourierOutcomes n) := by
  apply (List.perm_ext_iff_of_nodup
    ((fourierOutcomes_nodup n).map List.reverse_injective) (fourierOutcomes_nodup n)).mpr
  intro bits
  simp only [List.mem_map, fourierOutcomes_mem]
  constructor
  · rintro ⟨xs, hx, rfl⟩
    simpa only [List.length_reverse] using hx
  · intro hb
    exact ⟨bits.reverse, by simpa using hb, List.reverse_reverse bits⟩

theorem inputWords_reverse_perm (ws : List Nat) :
    ((inputWords ws).map (List.map List.reverse)).Perm (inputWords ws) := by
  induction ws with
  | nil => simp [inputWords]
  | cons w ws ih =>
    simp only [inputWords]
    have he : ((fourierOutcomes w).flatMap (fun input =>
        (inputWords ws).map (fun rest => input :: rest))).map (List.map List.reverse) =
      ((fourierOutcomes w).map List.reverse).flatMap (fun input =>
        ((inputWords ws).map (List.map List.reverse)).map (fun rest => input :: rest)) := by
      simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, List.map_cons]
    rw [he]
    exact (outcomes_reverse_perm w).flatMap (fun input _ => ih.map (input :: ·))

theorem inputWords_msb_perm (ws : List Nat) :
    ((inputWords ws).map (fun inputs => (inputs.map List.reverse).flatten)).Perm
      (fourierOutcomes ws.sum) := by
  have hp := (inputWords_reverse_perm ws).map List.flatten
  simpa only [List.map_map, Function.comp_def, inputWords_flatten] using hp

/-- Physical banks hold little-endian digits in most-significant-first order. -/
def scalarWord (inputs : List (List Bool)) : List Bool :=
  (inputs.map List.reverse).flatten.reverse

theorem scalarWord_perm (ws : List Nat) :
    ((inputWords ws).map scalarWord).Perm (fourierOutcomes ws.sum) := by
  have hp : ((inputWords ws).map scalarWord).Perm
      ((fourierOutcomes ws.sum).map List.reverse) := by
    simpa only [List.map_map, Function.comp_def, scalarWord] using
      (inputWords_msb_perm ws).map List.reverse
  exact hp.trans (outcomes_reverse_perm ws.sum)

theorem scalarWord_value (inputs : List (List Bool)) :
    boolWordToNat (scalarWord inputs) = fourierWordMSB (inputs.map List.reverse).flatten := by
  simpa only [scalarWord, List.reverse_reverse] using
    (fourierWordMSB_reverse (scalarWord inputs)).symm

theorem inputWords_sum {A : Type} [AddCommMonoid A] (ws : List Nat)
    (f : List Bool → A) :
    ((inputWords ws).map (fun outputs => f outputs.flatten)).sum =
      ((fourierOutcomes ws.sum).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun xs => (xs.map f).sum) (inputWords_flatten ws)

theorem scalarWords_sum {A : Type} [AddCommMonoid A] (ws : List Nat)
    (f : List Bool → A) :
    ((inputWords ws).map (fun inputs => f (scalarWord inputs))).sum =
      ((fourierOutcomes ws.sum).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using ((scalarWord_perm ws).map f).sum_eq

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Refinement ====

section
/-! History-dependent physical refinement. Arithmetic records are retained in
execution and erased only by the protected coherent terminal-mass theorem.
Apache-2.0 Streaming proof infrastructure; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option pp.maxSteps 40
attribute [local irreducible] fourierOutcomes

structure WindowModel {n : Nat} (read : ConstantBit n → Bool) where
  physical : Window n
  point : Nat → Secp256k1.Point
  bias : Secp256k1.Point
  ideal : State →ₗ[ℂ] State
  valid : BasisState → Prop
  nodup : physical.wires.Nodup
  coherent : ∀ start history, CoherentlyImplementsOn
    ((physical.program start).instantiate read history) ideal valid

def WindowModel.step {n : Nat} {read : ConstantBit n → Bool} (w : WindowModel read)
    (prior bits : List Bool) : State →ₗ[ℂ] State :=
  (fourierBranch .inverse w.physical.wires prior bits).comp
    (w.ideal.comp (Quantum.run (w.physical.wires.reverse.map Gate.H)))

/-- Newest-first Fourier tags accompany the full physical record and Kraus map. -/
def taggedAxis {n : Nat} {read : ConstantBit n → Bool} :
    List (WindowModel read) → (start : Nat) → (Fin start → Bool) →
      List (Fin start) → List (List Bool × InstrumentBranch)
  | List.nil, _, history, prior => [(prior.map history, ⟨[], LinearMap.id⟩)]
  | w :: ws, start, history, prior =>
      (((prepareOuterBank w.physical.wires.reverse (w.physical.program start)).instantiate read history).run).flatMap
        (fun a =>
          let h₁ := historyAfter (start + w.physical.count) history a.history
          (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
            let h₂ := historyAfter (start + w.physical.count + w.physical.wires.length) h₁ bits
            let f : InstrumentBranch := ⟨bits, fourierBranch .inverse w.physical.wires (prior.map history) bits⟩
            (taggedAxis ws _ h₂ (nextPrior w.physical.count w.physical.wires.length prior)).map
              (fun b => (b.1, a.seq (f.seq b.2)))))

def selectedAxis {n : Nat} {read : ConstantBit n → Bool} (ws : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool) (prior : List (Fin start))
    (terminal : List Bool → Instrument) : Instrument :=
  (taggedAxis ws start history prior).flatMap (fun a => (terminal a.1).map a.2.seq)

def idealAxis {n : Nat} {read : ConstantBit n → Bool} :
    List (WindowModel read) → List Bool → (List Bool → Instrument) → Instrument
  | List.nil, prior, terminal => terminal prior
  | w :: ws, prior, terminal =>
      (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
        (idealAxis ws (bits.reverse ++ prior) terminal).map
          (fun b => ({history := bits, kraus := w.step prior bits} : InstrumentBranch).seq b))

/-- Reachability states only support facts for the exact ideal prefixes. -/
def Ready {n : Nat} {read : ConstantBit n → Bool} : List (WindowModel read) → State → Prop
  | List.nil, _ => True
  | w :: ws, ψ =>
      SupportedOn w.valid (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ) ∧
        ∀ prior bits, Ready ws (w.step prior bits ψ)

theorem support_smul {V : BasisState → Prop} (c : ℂ) {ψ : State}
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])

theorem Ready.smul {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (ψ : State) (hψ : Ready ws ψ) (c : ℂ) : Ready ws (c • ψ) := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · rw [map_smul]
      exact support_smul c hψ.1
    · intro prior bits
      rw [map_smul]
      exact ih _ (hψ.2 prior bits)

theorem flat_mass {A : Type} (xs : List A) (f : A → Instrument) (ψ : State) :
    Instrument.bornMass (xs.flatMap f) ψ = (xs.map (fun x => (f x).bornMass ψ)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.flatMap_cons, Instrument.bornMass, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons] using congrArg (_ + ·) ih

theorem prefixed_mass (b : InstrumentBranch) (I : Instrument) (ψ : State) :
    Instrument.bornMass (I.map b.seq) ψ = I.bornMass (b.kraus ψ) := by
  simp only [Instrument.bornMass, List.map_map, Function.comp_def, InstrumentBranch.seq,
    LinearMap.comp_apply]


theorem seq_mass (I J : Instrument) (ψ : State) :
    (I.seq J).bornMass ψ = (I.map (fun b => J.bornMass (b.kraus ψ))).sum := by
  simp only [Instrument.seq, flat_mass, prefixed_mass]

theorem idealAxis_cons_mass {n : Nat} {read : ConstantBit n → Bool}
    (w : WindowModel read) (ws : List (WindowModel read)) (prior : List Bool)
    (terminal : List Bool → Instrument) (ψ : State) :
    (idealAxis (w :: ws) prior terminal).bornMass ψ =
      ((fourierOutcomes w.physical.wires.length).map (fun bits =>
        (idealAxis ws (bits.reverse ++ prior) terminal).bornMass (w.step prior bits ψ))).sum := by
  simp only [idealAxis, flat_mass, prefixed_mass]

theorem axis_run_tagged {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) :
    ((axis (ws.map WindowModel.physical) start prior).instantiate read history).run =
      (taggedAxis ws start history prior).map Prod.snd := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, axis, castFinish_instantiate]
    rw [append_run_history]
    simp only [taggedAxis, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    rw [append_run_history]
    simp only [castFinish_instantiate]
    rw [fourierProgram_run, semiclassicalFourier_run, bankPrior_map]
    simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro bits hb
    rw [ih]
    simp only [List.map_map, Function.comp_def]

theorem selectedAxis_constant {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (J : Instrument) :
    selectedAxis ws start history prior (fun _ => J) =
      ((axis (ws.map WindowModel.physical) start prior).instantiate read history).run.seq J := by
  rw [axis_run_tagged]
  simp only [selectedAxis, Instrument.seq, List.flatMap_map]

theorem taggedAxis_transcript {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxis ws start history prior) :
    ∃ bits, Transcript (ws.map (fun w => (w.physical.count, w.physical.wires.length)))
        tagged.2.history bits ∧ tagged.1 = bits.reverse ++ prior.map history := by
  induction ws generalizing start tagged with
  | nil =>
    simp only [taggedAxis, List.mem_singleton] at ht
    subst tagged
    exact ⟨[], Transcript.nil, rfl⟩
  | cons w ws ih =>
    obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨bits, hb, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b, hbt, rfl⟩ := List.mem_map.mp ht
    obtain ⟨out, htrans, htag⟩ := ih _ _ _ b hbt
    have hla : a.history.length = w.physical.count := by
      have h := straight_history_length _ read history a ha
      omega
    have hlb := (fourierOutcomes_mem _ _).mp hb
    refine ⟨bits ++ out, ?_, ?_⟩
    · simpa only [List.map_cons, InstrumentBranch.seq, List.append_assoc] using
        Transcript.cons w.physical.count w.physical.wires.length _ a.history bits b.2.history out hla hlb htrans
    · rw [htag, nextPrior_map _ _ _ _ _ _ hla hlb]
      simp only [List.reverse_append, List.append_assoc]

theorem taggedAxis_readWord {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxis ws start history List.nil) (after : List Bool) :
    ShorECDLP.Challenge.readWord (List.ofFn history ++ tagged.2.history ++ after)
      (axisPositions (ws.map WindowModel.physical) start) =
        some (fourierWordLSB tagged.1.reverse) := by
  obtain ⟨bits, htrans, htag⟩ := taggedAxis_transcript ws start history List.nil tagged ht
  rw [htag]
  simpa only [List.map_nil, List.append_nil, List.reverse_reverse, List.length_ofFn,
    axisPositions, List.map_map, Function.comp_def] using htrans.readWord (List.ofFn history) after

theorem selectedAxis_cons {n : Nat} {read : ConstantBit n → Bool}
    (w : WindowModel read) (ws : List (WindowModel read)) (start : Nat)
    (history : Fin start → Bool) (prior : List (Fin start))
    (terminal : List Bool → Instrument) :
    selectedAxis (w :: ws) start history prior terminal =
      (((prepareOuterBank w.physical.wires.reverse (w.physical.program start)).instantiate read history).run).flatMap
        (fun a => (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
          let h₁ := historyAfter (start + w.physical.count) history a.history
          let h₂ := historyAfter (start + w.physical.count + w.physical.wires.length) h₁ bits
          (selectedAxis ws _ h₂ (nextPrior w.physical.count w.physical.wires.length prior) terminal).map
            (a.seq ({history := bits, kraus := fourierBranch .inverse w.physical.wires (prior.map history) bits} : InstrumentBranch)).seq)) := by
  simp only [selectedAxis, taggedAxis, List.flatMap_assoc, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro bits hb
  apply List.flatMap_congr
  intro b hbt
  apply List.map_congr_left
  intro c hc
  rcases a with ⟨ah, ak⟩
  rcases b with ⟨tag, bh, bk⟩
  rcases c with ⟨ch, ck⟩
  simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem selectedAxis_cons_mass {n : Nat} {read : ConstantBit n → Bool}
    (w : WindowModel read) (ws : List (WindowModel read)) (start : Nat)
    (history : Fin start → Bool) (prior : List (Fin start))
    (terminal : List Bool → Instrument) (ψ : State) :
    (selectedAxis (w :: ws) start history prior terminal).bornMass ψ =
      (((w.physical.program start).instantiate read history).run.map (fun a =>
        ((fourierOutcomes w.physical.wires.length).map (fun bits =>
          let h₁ := historyAfter (start + w.physical.count) history a.history
          let h₂ := historyAfter (start + w.physical.count + w.physical.wires.length) h₁ bits
          (selectedAxis ws _ h₂ (nextPrior w.physical.count w.physical.wires.length prior) terminal).bornMass
            (fourierBranch .inverse w.physical.wires (prior.map history) bits
              (a.kraus (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ))))).sum)).sum := by
  rw [selectedAxis_cons, prepare_run]
  simp only [flat_mass, prefixed_mass, List.flatMap_map,
    InstrumentBranch.seq, LinearMap.comp_apply, List.nil_append]


/-- Eliminate internal arithmetic records while preserving every adaptive Fourier phase. -/
theorem selectedAxis_mass {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (terminal : List Bool → Instrument)
    (ψ : State) (hψ : Ready ws ψ) :
    (selectedAxis ws start history prior terminal).bornMass ψ =
      (idealAxis ws (prior.map history) terminal).bornMass ψ := by
  induction ws generalizing start ψ with
  | nil =>
    simp only [selectedAxis, taggedAxis, List.flatMap_cons, List.flatMap_nil, List.append_nil, idealAxis]
    exact prefixed_mass ⟨[], LinearMap.id⟩ _ ψ
  | cons w ws ih =>
    let J : Instrument := (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
      (idealAxis ws (bits.reverse ++ prior.map history) terminal).map
        ({history := bits, kraus := fourierBranch .inverse w.physical.wires (prior.map history) bits} : InstrumentBranch).seq)
    have he :
        (selectedAxis (w :: ws) start history prior terminal).bornMass ψ =
          (((w.physical.program start).instantiate read history).run.seq J).bornMass
            (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ) := by
      rw [selectedAxis_cons_mass, seq_mass]
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      unfold J
      simp only [flat_mass, prefixed_mass]
      apply congrArg List.sum
      apply List.map_congr_left
      intro bits hb
      obtain ⟨c, hc⟩ := (w.coherent start history).branch_coefficient a ha
      have hstate := hc.on_supported hψ.1
      have hready : Ready ws (fourierBranch .inverse w.physical.wires (prior.map history) bits
          (a.kraus (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ))) := by
        rw [hstate, map_smul]
        exact Ready.smul ws _ (hψ.2 (prior.map history) bits) c
      rw [ih _ _ _ _ hready]
      have hla : a.history.length = w.physical.count := by
        have h := straight_history_length _ read history a ha
        omega
      rw [nextPrior_map _ _ _ _ _ _ hla ((fourierOutcomes_mem _ _).mp hb)]
    rw [he, (w.coherent start history).terminalMass hψ.1 J]
    rw [idealAxis_cons_mass]
    simp only [J, flat_mass, prefixed_mass, WindowModel.step, LinearMap.comp_apply]

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/TwoAxes ====

section
/-! Two history-dependent straight axes, resetting Fourier feedback between
axes. Apache-2.0 Streaming proof pattern; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

theorem Ready.append_left {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (ψ : State) (hψ : Ready (left ++ right) ψ) :
    Ready left ψ := by
  induction left generalizing ψ with
  | nil => trivial
  | cons w ws ih => exact ⟨hψ.1, fun prior bits => ih _ (hψ.2 prior bits)⟩

/-- Every physical left-axis branch reaches the right-axis validity domain. -/
theorem taggedAxis_ready_tail {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxis left start history prior) (ψ : State)
    (hψ : Ready (left ++ right) ψ) : Ready right (tagged.2.kraus ψ) := by
  induction left generalizing start tagged ψ with
  | nil =>
    simp only [taggedAxis, List.mem_singleton] at ht
    subst tagged
    exact hψ
  | cons w ws ih =>
    obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨bits, hb, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b, hbt, rfl⟩ := List.mem_map.mp ht
    rw [prepare_run] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hc⟩ := (w.coherent start history).branch_coefficient a₀ ha₀
    have hs := hc.on_supported hψ.1
    have hready : Ready (ws ++ right)
        (fourierBranch .inverse w.physical.wires (prior.map history) bits
          (a₀.kraus (Quantum.run (w.physical.wires.reverse.map Gate.H) ψ))) := by
      rw [hs, map_smul]
      exact Ready.smul _ _ (hψ.2 (prior.map history) bits) c
    exact ih _ _ _ b hbt _ hready

def taggedTwoAxes {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool) :
    List ((List Bool × List Bool) × InstrumentBranch) :=
  (taggedAxis left start history List.nil).flatMap (fun l =>
    (taggedAxis right (start + axisCount (left.map WindowModel.physical))
      (historyAfter _ history l.2.history) List.nil).map (fun r => ((l.1, r.1), l.2.seq r.2)))

def selectedTwoAxes {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  (taggedTwoAxes left right start history).flatMap (fun a =>
    (terminal a.1.1 a.1.2).map a.2.seq)

def idealTwoAxes {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read))
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  idealAxis left List.nil (fun lhs => idealAxis right List.nil (terminal lhs))

theorem twoAxes_run_tagged {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool) :
    (((axis (left.map WindowModel.physical) start List.nil).append
      (axis (right.map WindowModel.physical) (start + axisCount (left.map WindowModel.physical))
        List.nil)).instantiate read history).run =
      (taggedTwoAxes left right start history).map Prod.snd := by
  rw [append_run_history, axis_run_tagged]
  simp only [taggedTwoAxes, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  rw [axis_run_tagged]
  simp only [List.map_map, Function.comp_def]

theorem selectedTwoAxes_expand {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) :
    selectedTwoAxes left right start history terminal =
      (taggedAxis left start history List.nil).flatMap (fun l =>
        (selectedAxis right (start + axisCount (left.map WindowModel.physical))
          (historyAfter _ history l.2.history) List.nil (terminal l.1)).map l.2.seq) := by
  simp only [selectedTwoAxes, taggedTwoAxes, selectedAxis, List.flatMap_assoc,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro l hl
  apply List.flatMap_congr
  intro r hr
  apply List.map_congr_left
  intro b hb
  rcases l with ⟨lt, lh, lk⟩
  rcases r with ⟨rt, rh, rk⟩
  rcases b with ⟨bh, bk⟩
  simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

/-- Exact physical-to-ideal selected-event mass with all arithmetic histories retained. -/
theorem selectedTwoAxes_mass {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) (ψ : State)
    (hψ : Ready (left ++ right) ψ) :
    (selectedTwoAxes left right start history terminal).bornMass ψ =
      (idealTwoAxes left right terminal).bornMass ψ := by
  rw [selectedTwoAxes_expand, flat_mass]
  simp only [prefixed_mass]
  have he : ((taggedAxis left start history List.nil).map (fun l =>
      (idealAxis right List.nil (terminal l.1)).bornMass (l.2.kraus ψ))).sum =
        (selectedAxis left start history List.nil (fun lhs => idealAxis right List.nil (terminal lhs))).bornMass ψ := by
    simp only [selectedAxis, flat_mass, prefixed_mass]
  calc
    _ = ((taggedAxis left start history List.nil).map (fun l =>
        (idealAxis right List.nil (terminal l.1)).bornMass (l.2.kraus ψ))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro l hl
      simpa only [List.map_nil] using selectedAxis_mass right _ _ List.nil (terminal l.1) _
        (taggedAxis_ready_tail left right start history List.nil l hl ψ hψ)
    _ = _ := he.trans (selectedAxis_mass left start history List.nil _ ψ (Ready.append_left left right ψ hψ))

def physicalAxes {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool) : Instrument :=
  (((axis (left.map WindowModel.physical) start List.nil).append
    (axis (right.map WindowModel.physical) (start + axisCount (left.map WindowModel.physical))
      List.nil)).instantiate read history).run

theorem selectedTwoAxes_constant {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (J : Instrument) : selectedTwoAxes left right start history (fun _ _ => J) =
      (physicalAxes left right start history).seq J := by
  unfold physicalAxes
  rw [twoAxes_run_tagged]
  simp only [selectedTwoAxes, Instrument.seq, List.flatMap_map]

theorem taggedAxis_history_length {n : Nat} {read : ConstantBit n → Bool}
    (ws : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxis ws start history prior) :
    tagged.2.history.length = axisCount (ws.map WindowModel.physical) := by
  have hb : tagged.2 ∈ ((axis (ws.map WindowModel.physical) start prior).instantiate read history).run := by
    rw [axis_run_tagged]
    exact List.mem_map.mpr ⟨tagged, ht, rfl⟩
  have h := straight_history_length _ read history tagged.2 hb
  omega

theorem taggedTwoAxes_readWords {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool)
    (tagged : (List Bool × List Bool) × InstrumentBranch)
    (ht : tagged ∈ taggedTwoAxes left right start history) (after : List Bool) :
    ShorECDLP.Challenge.readWord (List.ofFn history ++ tagged.2.history ++ after)
      (axisPositions (left.map WindowModel.physical) start) =
        some (fourierWordLSB tagged.1.1.reverse) ∧
    ShorECDLP.Challenge.readWord (List.ofFn history ++ tagged.2.history ++ after)
      (axisPositions (right.map WindowModel.physical)
        (start + axisCount (left.map WindowModel.physical))) =
        some (fourierWordLSB tagged.1.2.reverse) := by
  obtain ⟨l, hl, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  have hleft := taggedAxis_readWord left start history l hl (r.2.history ++ after)
  have hright := taggedAxis_readWord right _ _ r hr after
  have hlen := taggedAxis_history_length left start history List.nil l hl
  rw [historyAfter_list history l.2.history (by omega)] at hright
  constructor
  · simpa only [InstrumentBranch.seq, List.append_assoc] using hleft
  · simpa only [InstrumentBranch.seq, List.append_assoc] using hright

def pairAccept (left right : List Nat) (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  ((ShorECDLP.Challenge.readWord history left).bind (fun a =>
    (ShorECDLP.Challenge.readWord history right).map (accept a))).getD false

/-- Filtering the real sparse transcript is exactly selecting the two Fourier tags. -/
theorem selectedTwoAxes_fixed_filter {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (J : Instrument) (accept : Nat → Nat → Bool) :
    selectedTwoAxes left right 0 Fin.elim0 (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil) =
      ((physicalAxes left right 0 Fin.elim0).seq J).filter (fun b =>
        pairAccept (axisPositions (left.map WindowModel.physical) 0)
          (axisPositions (right.map WindowModel.physical)
            (axisCount (left.map WindowModel.physical))) accept b.history) := by
  rw [← selectedTwoAxes_constant left right 0 Fin.elim0 J]
  rw [selectedTwoAxes, selectedTwoAxes, List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hp (b : InstrumentBranch) :
      pairAccept (axisPositions (left.map WindowModel.physical) 0)
        (axisPositions (right.map WindowModel.physical) (axisCount (left.map WindowModel.physical)))
        accept (a.2.seq b).history =
          accept (fourierWordLSB a.1.1.reverse) (fourierWordLSB a.1.2.reverse) := by
    have h := taggedTwoAxes_readWords left right 0 Fin.elim0 a ha b.history
    simp only [List.ofFn_zero, List.nil_append, Nat.zero_add] at h
    simp only [pairAccept, InstrumentBranch.seq, h.1, h.2, Option.bind_some,
      Option.map_some, Option.getD_some]
  rw [List.filter_map]
  simp only [Function.comp_def, hp]
  split <;> simp_all

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/JointMass ====

section
/-! Width-independent point Fourier distribution, using the protected character
expansion (Apache-2.0; see LICENSE and NOTICE). -/
namespace ShorECDLP.Entrant.Single
open Quantum Secp256k1 ShorECDLP.Paper2607_13816
open Quantum.OrderFinding
open scoped BigOperators
noncomputable section

/-- The coherent Fourier sum, before measuring the point register. -/
def idealPointState (Q : Point) (root : BasisState) (n m : Nat) (x y : List Bool) : State :=
  let c : ℂ := ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (n + m)
  c • ((fourierOutcomes n).map (fun a =>
    ((fourierOutcomes m).map (fun b =>
      (c * dyadicFourierKernel .inverse n (boolWordToNat a) (fourierWordLSB x) *
        dyadicFourierKernel .inverse m (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) root))).sum)).sum

/-- Character expansion applies at any two precisions and any framed root state. -/
theorem idealPointState_mass (Q : Point) (d : Nat) (hd : Q = d • G)
    (root : BasisState) (n m : Nat) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = m)
    (out : Fin (2 ^ n) × Fin (2 ^ m))
    (hox : fourierWordLSB x = out.1.val) (hoy : fourierWordLSB y = out.2.val) :
    normSq (idealPointState Q root n m x y) = asymmetricPairMass order n m d out := by
  unfold idealPointState
  rw [pointDoubleSum_normalize _ _ _ _ _ G Q d hd root, pow_add]
  exact asymmetric_point_character_mass order_prime G generator_order root n m d x y hx hy out hox hoy

/-- An event is selected only after each coherent point sum is complete. -/
def idealEventMass (Q : Point) (root : BasisState) (n m : Nat)
    (accept : Nat → Nat → Bool) : ℝ :=
  ((fourierOutcomes n).map (fun x => ((fourierOutcomes m).map (fun y =>
    if accept (fourierWordLSB x) (fourierWordLSB y) then
      normSq (idealPointState Q root n m x y) else 0)).sum)).sum

theorem outcome_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : List Bool → A) :
    ((fourierOutcomes n).map f).sum = ∑ v : Fin (2 ^ n), f (paperOutcomeBits n v) := by
  rw [← List.sum_toFinset _ (fourierOutcomes_nodup n)]
  symm
  apply Finset.sum_bij (fun v _ => paperOutcomeBits n v)
  · intro v _
    exact List.mem_toFinset.mpr ((fourierOutcomes_mem n _).mpr (paperOutcomeBits_length n v))
  · intro a _ b _ h
    exact paperOutcomeBits_injective n h
  · intro bs hbs
    have hl := (fourierOutcomes_mem n bs).mp (List.mem_toFinset.mp hbs)
    have hv : fourierWordLSB bs < 2 ^ n := by simpa [hl] using fourierWordLSB_lt bs
    refine ⟨⟨fourierWordLSB bs, hv⟩, Finset.mem_univ _, ?_⟩
    apply fourierWordLSB_injective _ _
    · rw [paperOutcomeBits_length, hl]
    · exact paperOutcomeBits_word n _
  · intro _ _; rfl

theorem idealEventMass_distribution (Q : Point) (d : Nat) (hd : Q = d • G)
    (root : BasisState) (n m : Nat) (accept : Nat → Nat → Bool) :
    idealEventMass Q root n m accept =
      ∑ a : Fin (2 ^ n), ∑ b : Fin (2 ^ m),
        if accept a.val b.val then asymmetricPairMass order n m d (a, b) else 0 := by
  unfold idealEventMass
  simp_rw [outcome_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [paperOutcomeBits_word]
  split_ifs
  · exact idealPointState_mass Q d hd root n m _ _ (paperOutcomeBits_length n a)
      (paperOutcomeBits_length m b) (a, b) (paperOutcomeBits_word n a) (paperOutcomeBits_word m b)
  · rfl


end
end ShorECDLP.Entrant.Single

end

-- ==== part: Single/MixedKernel ====

section
/-! Exact mixed-radix Fourier composition, adapted from the Apache-2.0
Streaming distribution proof; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
attribute [local irreducible] fourierOutcomes

structure DigitWindow where
  width : Nat
  point : Nat → Point
  bias : Point := 0

def pathWidths (path : List (DigitWindow × List Bool)) : List Nat :=
  path.map (fun w => w.1.width)

def pathEnd : List (DigitWindow × List Bool) → List (List Bool) → Point → Point
  | (w, _) :: windows, input :: inputs, P =>
      pathEnd windows inputs (P + w.point (boolWordToNat input))
  | _, _, P => P

def inputWeight : List (DigitWindow × List Bool) → List Bool → List (List Bool) → ℂ
  | (w, output) :: windows, prior, input :: inputs =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) *
        fourierBitAmplitude .inverse input.reverse prior output *
          inputWeight windows (output.reverse ++ prior) inputs
  | _, _, _ => 1

def pointKernel (root : BasisState) :
    List (DigitWindow × List Bool) → List Bool → Point → State
  | List.nil, _, P => ket (pointWrite P root)
  | (w, output) :: windows, prior, P =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            pointKernel root windows (output.reverse ++ prior)
              (P + w.point (boolWordToNat input)))).sum

theorem flat_sum {A B : Type} [AddCommMonoid B] (xs : List A) (f : A → List B) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

theorem pointKernel_inputs (root : BasisState)
    (path : List (DigitWindow × List Bool)) (prior : List Bool) (P : Point) :
    pointKernel root path prior P =
      ((inputWords (pathWidths path)).map (fun inputs =>
        inputWeight path prior inputs • ket (pointWrite (pathEnd path inputs P) root))).sum := by
  induction path generalizing prior P with
  | nil => simp [pointKernel, pathWidths, inputWords, inputWeight, pathEnd]
  | cons w path ih =>
    simp only [pointKernel, pathWidths, List.map_cons, inputWords, List.map_flatMap,
      List.map_map, Function.comp_def, inputWeight, pathEnd, flat_sum]
    simp_rw [ih]
    simp only [smul_smul, List.smul_sum, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro input hi
    congr 1
    apply List.map_congr_left
    intro inputs his
    rw [mul_assoc]

def inputPairs (path : List (DigitWindow × List Bool)) (inputs : List (List Bool)) :
    List (List Bool × List Bool) :=
  (path.zip inputs).map (fun p => (p.2.reverse, p.1.2))

theorem inputWeight_amplitude (path : List (DigitWindow × List Bool))
    (prior : List Bool) (inputs : List (List Bool)) (hl : inputs.length = path.length) :
    inputWeight path prior inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (pathWidths path).sum) *
        windowFourierAmplitude .inverse (inputPairs path inputs) prior := by
  induction path generalizing prior inputs with
  | nil =>
    have he : inputs = List.nil := List.length_eq_zero_iff.mp hl
    subst inputs
    simp [inputWeight, inputPairs, windowFourierAmplitude, pathWidths]
  | cons w path ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      have ht : inputs.length = path.length := by simpa using hl
      simp only [inputWeight, inputPairs, List.zip_cons_cons, List.map_cons,
        windowFourierAmplitude, pathWidths, List.sum_cons]
      rw [ih _ inputs ht, pow_add]
      dsimp only [pathWidths, inputPairs]
      ring

theorem inputPairs_fst (path : List (DigitWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = path.length) :
    (inputPairs path inputs).map Prod.fst = inputs.map List.reverse := by
  induction path generalizing inputs with
  | nil =>
    have he : inputs = List.nil := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w path ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [inputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

theorem inputPairs_snd (path : List (DigitWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = path.length) :
    (inputPairs path inputs).map Prod.snd = path.map Prod.snd := by
  induction path generalizing inputs with
  | nil =>
    have he : inputs = List.nil := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w path ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [inputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

/-- Equal widths are required only for the corresponding input and output bank. -/
theorem inputPairs_lengths (path : List (DigitWindow × List Bool))
    (inputs : List (List Bool))
    (ho : ∀ w ∈ path, w.2.length = w.1.width)
    (hi : inputs.map List.length = pathWidths path) :
    ∀ pair ∈ inputPairs path inputs, pair.2.length = pair.1.length := by
  induction path generalizing inputs with
  | nil => simp [inputPairs]
  | cons w path ih =>
    cases inputs with
    | nil => simp [pathWidths] at hi
    | cons input inputs =>
      have hh : input.length = w.1.width ∧ inputs.map List.length = pathWidths path := by
        simpa only [List.map_cons, pathWidths, List.cons.injEq] using hi
      intro pair hp
      simp only [inputPairs, List.zip_cons_cons, List.map_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simpa only [List.length_reverse, hh.1] using ho w (by simp)
      · exact ih inputs (fun v hv => ho v (List.mem_cons_of_mem w hv)) hh.2 pair hp

theorem inputWeight_kernel (path : List (DigitWindow × List Bool))
    (inputs : List (List Bool))
    (ho : ∀ w ∈ path, w.2.length = w.1.width)
    (hi : inputs.map List.length = pathWidths path) :
    inputWeight path List.nil inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (2 * (pathWidths path).sum)) *
        dyadicFourierKernel .inverse (pathWidths path).sum
          (boolWordToNat (scalarWord inputs)) (fourierWordLSB (path.map Prod.snd).flatten) := by
  have hl : inputs.length = path.length := by
    have h := congrArg List.length hi
    simpa only [List.length_map, pathWidths] using h
  have hlen : (inputs.map List.reverse).flatten.length = (pathWidths path).sum := by
    rw [flatten_length_of_widths, List.map_map]
    simpa only [Function.comp_def, List.length_reverse] using congrArg List.sum hi
  rw [inputWeight_amplitude path List.nil inputs hl,
    windowFourierAmplitude_kernel .inverse _ (inputPairs_lengths path inputs ho hi),
    inputPairs_fst path inputs hl, inputPairs_snd path inputs hl, hlen,
    ← mul_assoc, ← pow_add, show (pathWidths path).sum + (pathWidths path).sum =
      2 * (pathWidths path).sum by omega, ← scalarWord_value]

/-- Compose exact per-window linear branches before computing any probability. -/
def axisBranch (step : DigitWindow → List Bool → List Bool → State →ₗ[ℂ] State) :
    List (DigitWindow × List Bool) → List Bool → State →ₗ[ℂ] State
  | List.nil, _ => LinearMap.id
  | (w, output) :: path, prior =>
      (axisBranch step path (output.reverse ++ prior)).comp (step w prior output)

theorem axisBranch_point
    (step : DigitWindow → List Bool → List Bool → State →ₗ[ℂ] State)
    (root : BasisState) (path : List (DigitWindow × List Bool))
    (hstep : ∀ w ∈ path, ∀ prior P,
      step w.1 prior w.2 (ket (pointWrite P root)) =
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.1.width) •
          ((fourierOutcomes w.1.width).map (fun input =>
            fourierBitAmplitude .inverse input.reverse prior w.2 •
              ket (pointWrite (P + w.1.point (boolWordToNat input)) root))).sum)
    (prior : List Bool) (P : Point) :
    axisBranch step path prior (ket (pointWrite P root)) = pointKernel root path prior P := by
  induction path generalizing prior P with
  | nil => rfl
  | cons w path ih =>
    simp only [axisBranch, LinearMap.comp_apply]
    rw [hstep w (by simp)]
    simp only [map_smul, map_list_sum, List.map_map, Function.comp_def]
    simp_rw [ih (fun v hv => hstep v (List.mem_cons_of_mem w hv))]
    rfl

def twoInputState (root : BasisState) (left right : List (DigitWindow × List Bool))
    (P : Point) : State :=
  ((inputWords (pathWidths left)).map (fun inputsL =>
    ((inputWords (pathWidths right)).map (fun inputsR =>
      (inputWeight left List.nil inputsL * inputWeight right List.nil inputsR) •
        ket (pointWrite (pathEnd right inputsR (pathEnd left inputsL P)) root))).sum)).sum

theorem two_axes_input_state
    (step : DigitWindow → List Bool → List Bool → State →ₗ[ℂ] State)
    (root : BasisState) (left right : List (DigitWindow × List Bool))
    (hstep : ∀ w ∈ left ++ right, ∀ prior P,
      step w.1 prior w.2 (ket (pointWrite P root)) =
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.1.width) •
          ((fourierOutcomes w.1.width).map (fun input =>
            fourierBitAmplitude .inverse input.reverse prior w.2 •
              ket (pointWrite (P + w.1.point (boolWordToNat input)) root))).sum)
    (P : Point) :
    axisBranch step right List.nil (axisBranch step left List.nil (ket (pointWrite P root))) =
      twoInputState root left right P := by
  rw [axisBranch_point step root left (fun w hw => hstep w (List.mem_append_left _ hw)),
    pointKernel_inputs]
  simp only [map_list_sum, map_smul, List.map_map, Function.comp_def]
  simp_rw [axisBranch_point step root right (fun w hw => hstep w (List.mem_append_right _ hw)),
    pointKernel_inputs]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul, twoInputState]

theorem twoInputState_ideal (Q : Point) (root : BasisState)
    (left right : List (DigitWindow × List Bool)) (P : Point)
    (hol : ∀ w ∈ left, w.2.length = w.1.width)
    (hor : ∀ w ∈ right, w.2.length = w.1.width)
    (hrec : ∀ inputsL ∈ inputWords (pathWidths left),
      ∀ inputsR ∈ inputWords (pathWidths right),
      pathEnd right inputsR (pathEnd left inputsL P) =
        boolWordToNat (scalarWord inputsL) • G + boolWordToNat (scalarWord inputsR) • Q) :
    twoInputState root left right P =
      idealPointState Q root (pathWidths left).sum (pathWidths right).sum
        (left.map Prod.snd).flatten (right.map Prod.snd).flatten := by
  let n := (pathWidths left).sum
  let m := (pathWidths right).sum
  let c : ℂ := (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (n + m))
  let f (a b : List Bool) : State :=
    (c * (c * dyadicFourierKernel .inverse n (boolWordToNat a)
      (fourierWordLSB (left.map Prod.snd).flatten) *
      dyadicFourierKernel .inverse m (boolWordToNat b)
        (fourierWordLSB (right.map Prod.snd).flatten))) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) root)
  have he : twoInputState root left right P =
      ((inputWords (pathWidths left)).map (fun inputsL =>
        ((inputWords (pathWidths right)).map (fun inputsR =>
          f (scalarWord inputsL) (scalarWord inputsR))).sum)).sum := by
    unfold twoInputState
    apply congrArg List.sum
    apply List.map_congr_left
    intro inputsL hl
    apply congrArg List.sum
    apply List.map_congr_left
    intro inputsR hr
    rw [hrec inputsL hl inputsR hr, inputWeight_kernel left inputsL hol
      ((inputWords_mem _ _).mp hl), inputWeight_kernel right inputsR hor
        ((inputWords_mem _ _).mp hr)]
    unfold f c
    congr 1
    change _ = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (n + m)) * _
    rw [show 2 * (pathWidths left).sum = n + n by dsimp [n, m]; omega,
      show 2 * (pathWidths right).sum = m + m by dsimp [n, m]; omega]
    simp only [pow_add]
    ring
  rw [he]
  have hinner (a : List Bool) :
      ((inputWords (pathWidths right)).map (fun inputs => f a (scalarWord inputs))).sum =
        ((fourierOutcomes (pathWidths right).sum).map (f a)).sum :=
    scalarWords_sum _ (f a)
  simp_rw [hinner]
  rw [scalarWords_sum (pathWidths left)
    (fun a => ((fourierOutcomes (pathWidths right).sum).map (f a)).sum)]
  unfold f idealPointState
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul]
  rfl

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/Reconstruction ====

section
/-! Mixed-radix scalar reconstruction. Offset cancellation is a group identity,
independent of the arithmetic implementation and of the Fourier outputs. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

theorem scalarWord_cons (input : List Bool) (inputs : List (List Bool)) :
    boolWordToNat (scalarWord (input :: inputs)) =
      boolWordToNat input * 2 ^ inputs.flatten.length + boolWordToNat (scalarWord inputs) := by
  rw [scalarWord_value, List.map_cons, List.flatten_cons, fourierWordMSB_append,
    fourierWordMSB_reverse, ← scalarWord_value]
  have he : (inputs.map List.reverse).flatten.length = inputs.flatten.length := by
    simp only [flatten_length_of_widths, List.map_map, Function.comp_def, List.length_reverse]
  rw [he]

def biasSum (bias : DigitWindow → Point) (path : List (DigitWindow × List Bool)) : Point :=
  (path.map (fun w => bias w.1)).sum

/-- Suffix widths determine significance; each centered digit has a fixed bias. -/
def DescendingWeights (P : Point) (bias : DigitWindow → Point) :
    List (DigitWindow × List Bool) → Prop
  | [] => True
  | (w, _) :: rest =>
      (∀ v, w.point v + bias w = (v * 2 ^ (pathWidths rest).sum) • P) ∧
        DescendingWeights P bias rest

/-- Centered digit biases cancel before any character expansion is used. -/
theorem pathEnd_reconstruct (P : Point) (bias : DigitWindow → Point)
    (path : List (DigitWindow × List Bool)) (hw : DescendingWeights P bias path)
    (inputs : List (List Bool)) (hi : inputs.map List.length = pathWidths path) (A : Point) :
    pathEnd path inputs A + biasSum bias path =
      A + boolWordToNat (scalarWord inputs) • P := by
  induction path generalizing inputs A with
  | nil =>
    have hn : inputs = [] := by simpa only [pathWidths, List.map_nil, List.map_eq_nil_iff] using hi
    subst inputs
    simp [pathEnd, biasSum, scalarWord]
  | cons w path ih =>
    cases inputs with
    | nil => simp [pathWidths] at hi
    | cons input inputs =>
      have hh : input.length = w.1.width ∧ inputs.map List.length = pathWidths path := by
        simpa only [List.map_cons, pathWidths, List.cons.injEq] using hi
      have hsuf : inputs.flatten.length = (pathWidths path).sum := by
        rw [flatten_length_of_widths, hh.2]
      have ht := ih hw.2 inputs hh.2 (A + w.1.point (boolWordToNat input))
      change pathEnd path inputs (A + w.1.point (boolWordToNat input)) +
        (bias w.1 + biasSum bias path) = A + boolWordToNat (scalarWord (input :: inputs)) • P
      rw [scalarWord_cons, hsuf, add_nsmul]
      calc
        _ = (pathEnd path inputs (A + w.1.point (boolWordToNat input)) +
            biasSum bias path) + bias w.1 := by abel
        _ = (A + w.1.point (boolWordToNat input) + boolWordToNat (scalarWord inputs) • P) +
            bias w.1 := by rw [ht]
        _ = A + (w.1.point (boolWordToNat input) + bias w.1) +
            boolWordToNat (scalarWord inputs) • P := by abel
        _ = _ := by rw [hw.1]; abel

theorem two_axes_reconstruct (Q : Point)
    (biasL biasR : DigitWindow → Point) (left right : List (DigitWindow × List Bool))
    (hwL : DescendingWeights G biasL left) (hwR : DescendingWeights Q biasR right)
    (A : Point) (hA : A = biasSum biasL left + biasSum biasR right)
    (inputsL : List (List Bool)) (inputsR : List (List Bool))
    (hiL : inputsL.map List.length = pathWidths left)
    (hiR : inputsR.map List.length = pathWidths right) :
    pathEnd right inputsR (pathEnd left inputsL A) =
      boolWordToNat (scalarWord inputsL) • G + boolWordToNat (scalarWord inputsR) • Q := by
  have hl := pathEnd_reconstruct G biasL left hwL inputsL hiL A
  have hr := pathEnd_reconstruct Q biasR right hwR inputsR hiR (pathEnd left inputsL A)
  rw [eq_sub_iff_add_eq.mpr hr, eq_sub_iff_add_eq.mpr hl, hA]
  abel

/-- A compositional version of the full-state identity, with only per-digit
weights and fixed offset cancellation as arithmetic premises. -/
theorem twoInputState_ideal_of_weights (Q : Point) (root : BasisState)
    (left right : List (DigitWindow × List Bool)) (A : Point)
    (hol : ∀ w ∈ left, w.2.length = w.1.width)
    (hor : ∀ w ∈ right, w.2.length = w.1.width)
    (biasL biasR : DigitWindow → Point)
    (hwL : DescendingWeights G biasL left) (hwR : DescendingWeights Q biasR right)
    (hA : A = biasSum biasL left + biasSum biasR right) :
    twoInputState root left right A =
      idealPointState Q root (pathWidths left).sum (pathWidths right).sum
        (left.map Prod.snd).flatten (right.map Prod.snd).flatten := by
  apply twoInputState_ideal Q root left right A hol hor
  intro inputsL hl inputsR hr
  exact two_axes_reconstruct Q biasL biasR left right hwL hwR A hA inputsL inputsR
    ((inputWords_mem _ _).mp hl) ((inputWords_mem _ _).mp hr)

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/Paths ====

section
/-! Output-path expansion for arbitrary window banks, preserving the complete
linear branch before taking its Born mass. Apache-2.0 Streaming proof pattern;
see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Paper2607_13816
noncomputable section
attribute [local irreducible] fourierOutcomes

def outputPaths {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool} :
    List (WindowModel read) → List (List (WindowModel read × List Bool))
  | List.nil => [[]]
  | w :: ws => (fourierOutcomes w.physical.wires.length).flatMap (fun bits =>
      (outputPaths ws).map (fun path => (w, bits) :: path))

def modelBranch {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool} :
    List (WindowModel read × List Bool) → List Bool → State →ₗ[ℂ] State
  | List.nil, _ => LinearMap.id
  | (w, bits) :: ws, prior =>
      (modelBranch ws (bits.reverse ++ prior)).comp (w.step prior bits)

theorem idealAxis_paths {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (prior : List Bool) (terminal : List Bool → Instrument) :
    idealAxis ws prior terminal =
      (outputPaths ws).flatMap (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).map (fun b =>
          ({history := (path.map Prod.snd).flatten, kraus := modelBranch path prior} : InstrumentBranch).seq b)) := by
  induction ws generalizing prior with
  | nil =>
    simp only [idealAxis, outputPaths, List.flatMap_cons, List.flatMap_nil, List.map_nil,
      List.flatten_nil, List.reverse_nil, List.nil_append, List.append_nil, modelBranch]
    exact (List.map_id' _).symm
  | cons w ws ih =>
    simp only [idealAxis, outputPaths, ih, List.map_flatMap, List.flatMap_map,
      List.flatMap_assoc, List.map_map, Function.comp_def, List.map_cons,
      List.flatten_cons, List.reverse_append, List.append_assoc, modelBranch]
    apply List.flatMap_congr
    intro bits hb
    apply List.flatMap_congr
    intro path hp
    apply List.map_congr_left
    intro b hbt
    cases b
    simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem idealAxis_paths_mass {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (prior : List Bool) (terminal : List Bool → Instrument)
    (ψ : State) :
    (idealAxis ws prior terminal).bornMass ψ =
      ((outputPaths ws).map (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).bornMass
          (modelBranch path prior ψ))).sum := by
  rw [idealAxis_paths]
  simp only [flat_mass, prefixed_mass]

theorem outputPaths_zip {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) :
    outputPaths ws = (inputWords (ws.map (fun w => w.physical.wires.length))).map (ws.zip ·) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [outputPaths, List.map_cons, inputWords, List.map_flatMap,
      List.map_map, Function.comp_def, List.zip_cons_cons, ih]

def logicalPath {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (logical : WindowModel read → DigitWindow) (path : List (WindowModel read × List Bool)) :
    List (DigitWindow × List Bool) := path.map (fun w => (logical w.1, w.2))

theorem modelBranch_point {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (logical : WindowModel read → DigitWindow) (root : BasisState)
    (path : List (WindowModel read × List Bool))
    (hrule : ∀ w ∈ path, ∀ prior P,
      w.1.step prior w.2 (ket (pointWrite P root)) =
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (logical w.1).width) •
          ((fourierOutcomes (logical w.1).width).map (fun input =>
            fourierBitAmplitude .inverse input.reverse prior w.2 •
              ket (pointWrite (P + (logical w.1).point (boolWordToNat input)) root))).sum)
    (prior : List Bool) (P : Point) :
    modelBranch path prior (ket (pointWrite P root)) =
      pointKernel root (logicalPath logical path) prior P := by
  induction path generalizing prior P with
  | nil => rfl
  | cons w path ih =>
    simp only [modelBranch, LinearMap.comp_apply]
    rw [hrule w (by simp)]
    simp only [map_smul, map_list_sum, List.map_map, Function.comp_def]
    simp_rw [ih (fun v hv => hrule v (List.mem_cons_of_mem w hv))]
    rfl

def modelDigit {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (w : WindowModel read) : DigitWindow := ⟨w.physical.wires.length, w.point, w.bias⟩

def PointRule {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (root : BasisState) (w : WindowModel read) : Prop :=
  ∀ prior bits P, w.step prior bits (ket (pointWrite P root)) =
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.physical.wires.length) •
      ((fourierOutcomes w.physical.wires.length).map (fun input =>
        fourierBitAmplitude .inverse input.reverse prior bits •
          ket (pointWrite (P + w.point (boolWordToNat input)) root))).sum

def FirstRule {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (root : BasisState) (ψ : State) (w : WindowModel read) : Prop :=
  ∀ prior bits, w.step prior bits ψ =
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.physical.wires.length) •
      ((fourierOutcomes w.physical.wires.length).map (fun input =>
        fourierBitAmplitude .inverse input.reverse prior bits •
          ket (pointWrite (w.point (boolWordToNat input)) root))).sum

theorem modelBranch_initial {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (root : BasisState) (ψ : State) (first : WindowModel read) (firstBits : List Bool)
    (path : List (WindowModel read × List Bool)) (hfirst : FirstRule root ψ first)
    (hrule : ∀ w ∈ path, PointRule root w.1) (prior : List Bool) :
    modelBranch ((first, firstBits) :: path) prior ψ =
      pointKernel root (logicalPath modelDigit ((first, firstBits) :: path)) prior 0 := by
  simp only [modelBranch, LinearMap.comp_apply]
  rw [hfirst]
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def]
  simp_rw [modelBranch_point modelDigit root path (fun w hw prior P => hrule w hw prior w.2 P)]
  simp only [pointKernel, logicalPath, List.map_cons, modelDigit, zero_add]

theorem two_modelBranches_input {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (root : BasisState) (ψ : State) (first : WindowModel read) (firstBits : List Bool)
    (left right : List (WindowModel read × List Bool))
    (hfirst : FirstRule root ψ first) (hrule : ∀ w ∈ left ++ right, PointRule root w.1) :
    modelBranch right List.nil (modelBranch ((first, firstBits) :: left) List.nil ψ) =
      twoInputState root (logicalPath modelDigit ((first, firstBits) :: left))
        (logicalPath modelDigit right) 0 := by
  rw [modelBranch_initial root ψ first firstBits left hfirst
    (fun w hw => hrule w (List.mem_append_left _ hw)), pointKernel_inputs]
  simp only [map_list_sum, map_smul, List.map_map, Function.comp_def]
  simp_rw [modelBranch_point modelDigit root right
    (fun w hw prior P => hrule w (List.mem_append_right _ hw) prior w.2 P), pointKernel_inputs]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul, twoInputState]

theorem outputPath_models {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (path : List (WindowModel read × List Bool))
    (hp : path ∈ outputPaths ws) : path.map Prod.fst = ws := by
  induction ws generalizing path with
  | nil =>
    have he : path = List.nil := List.mem_singleton.mp hp
    subst path
    rfl
  | cons w ws ih =>
    obtain ⟨bits, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hp
    simp only [List.map_cons, ih rest hr]

theorem outputPath_lengths {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (path : List (WindowModel read × List Bool))
    (hp : path ∈ outputPaths ws) :
    ∀ w ∈ logicalPath modelDigit path, w.2.length = w.1.width := by
  induction ws generalizing path with
  | nil =>
    have he : path = List.nil := by simpa only [outputPaths, List.mem_singleton] using hp
    subst path
    simp [logicalPath]
  | cons w ws ih =>
    obtain ⟨bits, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hp
    intro v hv
    simp only [logicalPath, List.map_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (fourierOutcomes_mem _ _).mp hb
    · exact ih rest hr v hv

def ModelWeights {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (P : Point) : List (WindowModel read) → Prop
  | List.nil => True
  | w :: ws =>
      (∀ v, w.point v + w.bias =
        (v * 2 ^ (ws.map (fun w => w.physical.wires.length)).sum) • P) ∧ ModelWeights P ws

theorem outputPath_widths {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (path : List (WindowModel read × List Bool))
    (hp : path ∈ outputPaths ws) :
    pathWidths (logicalPath modelDigit path) = ws.map (fun w => w.physical.wires.length) := by
  have he := congrArg (List.map (fun w : WindowModel read => w.physical.wires.length))
    (outputPath_models ws path hp)
  simpa only [pathWidths, logicalPath, modelDigit, List.map_map, Function.comp_def] using he

theorem outputPath_bias {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (ws : List (WindowModel read)) (path : List (WindowModel read × List Bool))
    (hp : path ∈ outputPaths ws) :
    biasSum DigitWindow.bias (logicalPath modelDigit path) = (ws.map WindowModel.bias).sum := by
  have he := congrArg (fun ms : List (WindowModel read) => (ms.map WindowModel.bias).sum)
    (outputPath_models ws path hp)
  simpa only [biasSum, logicalPath, modelDigit, List.map_map, Function.comp_def] using he

theorem outputPath_weights {n : Nat} {read : ShorECDLP.Challenge.ConstantBit n → Bool}
    (P : Point) (ws : List (WindowModel read)) (hw : ModelWeights P ws)
    (path : List (WindowModel read × List Bool)) (hp : path ∈ outputPaths ws) :
    DescendingWeights P DigitWindow.bias (logicalPath modelDigit path) := by
  induction ws generalizing path with
  | nil =>
    have he : path = List.nil := List.mem_singleton.mp hp
    subst path
    trivial
  | cons w ws ih =>
    obtain ⟨bits, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hp
    constructor
    · change ∀ v, w.point v + w.bias =
        (v * 2 ^ (pathWidths (logicalPath modelDigit rest)).sum) • P
      rw [outputPath_widths ws rest hr]
      exact hw.1
    · exact ih hw.2 rest hr

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/EventMass ====

section
/-! Selected-event distribution for arbitrary window banks and a terminal reset
that preserves Born mass. Apache-2.0 Streaming proof pattern; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section

theorem idealTwoAxes_paths_mass {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (terminal : List Bool → List Bool → Instrument)
    (ψ : State) :
    (idealTwoAxes left right terminal).bornMass ψ =
      ((outputPaths left).map (fun lp => ((outputPaths right).map (fun rp =>
        (terminal (lp.map Prod.snd).flatten.reverse (rp.map Prod.snd).flatten.reverse).bornMass
          (modelBranch rp List.nil (modelBranch lp List.nil ψ)))).sum)).sum := by
  rw [idealTwoAxes, idealAxis_paths_mass]
  simp_rw [idealAxis_paths_mass]
  simp only [List.append_nil]

def precision {n : Nat} {read : ConstantBit n → Bool} (ws : List (WindowModel read)) : Nat :=
  (ws.map (fun w => w.physical.wires.length)).sum

/-- The branch-level premise is an equality of coherent states, before norms. -/
def KernelLaw {n : Nat} {read : ConstantBit n → Bool} (Q : Point) (root : BasisState)
    (left right : List (WindowModel read)) (ψ : State) : Prop :=
  ∀ lp ∈ outputPaths left, ∀ rp ∈ outputPaths right,
    modelBranch rp List.nil (modelBranch lp List.nil ψ) =
      idealPointState Q root (precision left) (precision right)
        (lp.map Prod.snd).flatten (rp.map Prod.snd).flatten


/-- The full coherent two-axis kernel follows from per-window point rules and
mixed-radix weights; no joint-distribution premise is needed. -/
theorem kernelLaw_of_windows {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State) (first : WindowModel read)
    (left right : List (WindowModel read))
    (hfirst : FirstRule root ψ first)
    (hpoint : ∀ w ∈ left ++ right, PointRule root w)
    (hleft : ModelWeights G (first :: left)) (hright : ModelWeights Q right)
    (hbias : ((first :: left).map WindowModel.bias).sum + (right.map WindowModel.bias).sum = 0) :
    KernelLaw Q root (first :: left) right ψ := by
  intro lp hl rp hr
  obtain ⟨firstBits, hfb, hl⟩ := List.mem_flatMap.mp hl
  obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hl
  have hlpath : (first, firstBits) :: tail ∈ outputPaths (first :: left) :=
    List.mem_flatMap.mpr ⟨firstBits, hfb, List.mem_map.mpr ⟨tail, htail, rfl⟩⟩
  have hrules : ∀ w ∈ tail ++ rp, PointRule root w.1 := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · apply hpoint w.1
      apply List.mem_append_left
      rw [← outputPath_models left tail htail]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    · apply hpoint w.1
      apply List.mem_append_right
      rw [← outputPath_models right rp hr]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
  rw [two_modelBranches_input root ψ first firstBits tail rp hfirst hrules]
  rw [twoInputState_ideal_of_weights Q root _ _ 0
    (outputPath_lengths _ _ hlpath) (outputPath_lengths _ _ hr)
    DigitWindow.bias DigitWindow.bias
    (outputPath_weights G _ hleft _ hlpath) (outputPath_weights Q _ hright _ hr) (by
      rw [outputPath_bias _ _ hlpath, outputPath_bias _ _ hr]
      exact hbias.symm)]
  rw [outputPath_widths _ _ hlpath, outputPath_widths _ _ hr]
  simp only [logicalPath, List.map_map, Function.comp_def]
  rfl

theorem inputWords_length (ws : List Nat) (outputs : List (List Bool))
    (ho : outputs ∈ inputWords ws) : outputs.length = ws.length := by
  have h := congrArg List.length ((inputWords_mem _ _).mp ho)
  simpa only [List.length_map] using h

/-- Coherent branch sums and exact output enumeration imply the full joint event law. -/
theorem idealTwoAxes_event_mass {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (left right : List (WindowModel read)) (ψ : State)
    (hkernel : KernelLaw Q root left right ψ) (J : Instrument)
    (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (idealTwoAxes left right (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass ψ =
      idealEventMass Q root (precision left) (precision right) accept := by
  rw [idealTwoAxes_paths_mass, outputPaths_zip, outputPaths_zip]
  simp only [List.map_map, Function.comp_def]
  have he :
      ((inputWords (left.map (fun w => w.physical.wires.length))).map (fun outputsL =>
        ((inputWords (right.map (fun w => w.physical.wires.length))).map (fun outputsR =>
          if accept (fourierWordLSB outputsL.flatten) (fourierWordLSB outputsR.flatten) then
            normSq (idealPointState Q root (precision left) (precision right)
              outputsL.flatten outputsR.flatten) else 0)).sum)).sum =
        idealEventMass Q root (precision left) (precision right) accept := by
    let f (lhs rhs : List Bool) : ℝ :=
      if accept (fourierWordLSB lhs) (fourierWordLSB rhs) then
        normSq (idealPointState Q root (precision left) (precision right) lhs rhs) else 0
    change ((inputWords (left.map (fun w => w.physical.wires.length))).map (fun outputsL =>
      ((inputWords (right.map (fun w => w.physical.wires.length))).map (fun outputsR =>
        f outputsL.flatten outputsR.flatten)).sum)).sum =
      ((fourierOutcomes (precision left)).map (fun lhs =>
        ((fourierOutcomes (precision right)).map (f lhs)).sum)).sum
    have hi (lhs : List Bool) :
        ((inputWords (right.map (fun w => w.physical.wires.length))).map (fun outputs =>
          f lhs outputs.flatten)).sum = ((fourierOutcomes (precision right)).map (f lhs)).sum :=
      inputWords_sum _ (f lhs)
    simp_rw [hi]
    exact inputWords_sum _ (fun lhs => ((fourierOutcomes (precision right)).map (f lhs)).sum)
  rw [← he]
  apply congrArg List.sum
  apply List.map_congr_left
  intro outputsL hl
  apply congrArg List.sum
  apply List.map_congr_left
  intro outputsR hr
  have hll : outputsL.length = left.length := by
    simpa only [List.length_map] using inputWords_length _ outputsL hl
  have hrr : outputsR.length = right.length := by
    simpa only [List.length_map] using inputWords_length _ outputsR hr
  have hls : (left.zip outputsL).map Prod.snd = outputsL := List.map_snd_zip (by omega)
  have hrs : (right.zip outputsR).map Prod.snd = outputsR := List.map_snd_zip (by omega)
  have hkl : left.zip outputsL ∈ outputPaths left := by
    rw [outputPaths_zip]
    exact List.mem_map.mpr ⟨outputsL, hl, rfl⟩
  have hkr : right.zip outputsR ∈ outputPaths right := by
    rw [outputPaths_zip]
    exact List.mem_map.mpr ⟨outputsR, hr, rfl⟩
  rw [hkernel _ hkl _ hkr, hls, hrs]
  simp only [List.reverse_reverse]
  split_ifs
  · exact hJ _
  · rfl

/-- Physical arithmetic records have no effect on the selected joint event. -/
theorem physicalTwoAxes_event_mass {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (left right : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool) (ψ : State)
    (hready : Ready (left ++ right) ψ) (hkernel : KernelLaw Q root left right ψ)
    (J : Instrument) (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedTwoAxes left right start history (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass ψ =
      idealEventMass Q root (precision left) (precision right) accept := by
  rw [selectedTwoAxes_mass left right start history _ ψ hready]
  exact idealTwoAxes_event_mass Q root left right ψ hkernel J hJ accept

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/WindowKernel ====

section
/-! Coherent mixed-width window sums. Adapted from the Apache-2.0 Streaming
window proof; see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
attribute [local irreducible] fourierOutcomes

theorem bank_nodup (width : Nat) : (bank width).Nodup := by
  by_cases hw : width = 15
  · rw [bank, if_pos hw]; decide +kernel
  · rw [bank, if_neg hw]; exact List.nodup_range'

theorem bank_width (w : SignedWindow) : (bank w.width).length = w.width := by
  cases w <;> simp [bank, SignedWindow.width]

theorem bank_subset (width : Nat) : ∀ v ∈ bank width, v ∈ streamAddress := by
  intro v hv
  by_cases hw : width = 15
  · rw [bank, if_pos hw] at hv
    exact (show ∀ v ∈ List.range' 855 14 ++ [870], v ∈ streamAddress by decide +kernel) v hv
  · simpa only [bank, if_neg hw, streamAddress] using hv

theorem bank_not_point (width : Nat) : ∀ v ∈ bank width, v ∉ pointLogicalWires := by
  intro v hv
  exact (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v
    (bank_subset width v hv)

theorem bank_not_padding (width : Nat) (hw : width = 15) : 869 ∉ bank width := by
  rw [bank, if_pos hw]; decide +kernel

theorem bank_clean (width : Nat) (s : BasisState) (hz : Clean streamAddress s) :
    Clean (bank width) s := fun v hv => hz v (bank_subset width v hv)

theorem point_bank_clean (width : Nat) (P : Point) (s : BasisState)
    (hz : Clean streamAddress s) : Clean (bank width) (pointWrite P s) := by
  intro v hv
  simpa only [pointWrite_frame P s v (bank_not_point width v hv)] using
    bank_clean width s hz v hv

theorem assigned_valid (w : SignedWindow) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) (input : List Bool) :
    WindowValid w (phaseWordState (bank w.width) input (pointWrite P s)) := by
  constructor
  · exact phaseWordState_preserves BatchedWindowValid (bank w.width)
      (fun t ht v hv b => batchedWindowValid_address_update t ht v
        (bank_subset w.width v hv) b) input _ (firstWindowInput_pointWrite s hs P)
  · intro hw
    rw [phaseWordState_frame _ _ _ 869 (bank_not_padding w.width hw),
      pointWrite_frame P s 869 (by decide +kernel)]
    exact hz 869 (by decide +kernel)

theorem assigned_coordinates (width : Nat) (P : Point) (s : BasisState) (input : List Bool) :
    pointStateCoordinates (phaseWordState (bank width) input (pointWrite P s)) =
      fig14PointEncoding P := by
  rw [phaseWordState_pointWrite _ (bank_not_point width), pointWrite_coordinates]

theorem assigned_digit (width : Nat) (s : BasisState) (input : List Bool)
    (hi : input.length = (bank width).length) :
    digit width (phaseWordState (bank width) input s) = boolWordToNat input := by
  have he (ws : List Wire) (t : BasisState) :
      tableAddressValue ws t = boolWordToNat (wireValues ws t) := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      change (t w).toNat + 2 * tableAddressValue ws t =
        (t w).toNat + 2 * boolWordToNat (wireValues ws t)
      rw [ih]
  rw [digit, he, phaseWordState_word _ (bank_nodup width) input hi s]

theorem signed_assigned_clear {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = w.width) :
    fourierClear (bank w.width).reverse
      (law.update Q w (phaseWordState (bank w.width) input (pointWrite P s))) =
      pointWrite (P + increment Q w (boolWordToNat input)) s := by
  rw [law.correct Q w _ hQ hn (assigned_valid w P s hs hz input) P
    (assigned_coordinates w.width P s input),
    assigned_digit w.width _ input (hi.trans (bank_width w).symm),
    clear_assigned_point _ input (pointWrite P s) (point_bank_clean w.width P s hz)
      (bank_not_point w.width), pointWrite_overwrite]

theorem signed_address_word {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = w.width) :
    (bank w.width).map
      (law.update Q w (phaseWordState (bank w.width) input (pointWrite P s))) = input := by
  rw [law.correct Q w _ hQ hn (assigned_valid w P s hs hz input) P
    (assigned_coordinates w.width P s input)]
  have he : (bank w.width).map
      (pointWrite (P + increment Q w (digit w.width
        (phaseWordState (bank w.width) input (pointWrite P s))))
          (phaseWordState (bank w.width) input (pointWrite P s))) =
      (bank w.width).map (phaseWordState (bank w.width) input (pointWrite P s)) := by
    apply List.map_congr_left
    intro v hv
    exact pointWrite_frame _ _ v (bank_not_point w.width v hv)
  rw [he]
  exact phaseWordState_word _ (bank_nodup w.width) input
    (hi.trans (bank_width w).symm) _

/-- A signed window sums input amplitudes coherently, at either bank width. -/
theorem signed_window_point_sum {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow)
    (prior output : List Bool) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse (bank w.width).reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (law.update Q w)
        (Quantum.run ((bank w.width).map Gate.H) (ket (pointWrite P s)))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (P + increment Q w (boolWordToNat input)) s))).sum := by
  rw [window_branch_uniform .inverse (bank w.width) (bank_nodup w.width)
    (law.update Q w) prior output _ (point_bank_clean w.width P s hz)
    (fun input hi => signed_address_word law Q hQ hn w P s hs hz input
      (by simpa only [bank_width] using (fourierOutcomes_mem _ _).mp hi)), bank_width]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [signed_assigned_clear law Q hQ hn w P s hs hz input ((fourierOutcomes_mem _ _).mp hi)]

/-- The initial direct load uses the same variable-width Fourier rule. -/
theorem first_window_point_sum (Q : Point) (prior output : List Bool)
    (s : BasisState) (hz : Clean streamAddress s) :
    fourierBranch .inverse (bank 16).reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (firstUpdate Q)
        (Quantum.run ((bank 16).map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (initialPoint Q (boolWordToNat input)) s))).sum := by
  have hlen : (bank 16).length = 16 := by decide +kernel
  rw [window_branch_uniform .inverse (bank 16) (bank_nodup 16)
    (firstUpdate Q) prior output s (bank_clean 16 s hz) (by
      intro input hi
      have he : (bank 16).map (firstUpdate Q (phaseWordState (bank 16) input s)) =
          (bank 16).map (phaseWordState (bank 16) input s) := by
        apply List.map_congr_left
        intro v hv
        exact pointWrite_frame _ _ v (bank_not_point 16 v hv)
      rw [he]
      exact phaseWordState_word _ (bank_nodup 16) input
        ((fourierOutcomes_mem _ _).mp hi) s), hlen]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  unfold firstUpdate
  rw [assigned_digit 16 s input (by simpa only [hlen] using (fourierOutcomes_mem _ _).mp hi),
    clear_assigned_point _ input s (bank_clean 16 s hz) (bank_not_point 16)]

end
end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Support ====

section
/-! Finite-support facts adapted from the Apache-2.0 Streaming validity proofs;
see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single.Support
open Quantum
noncomputable section

theorem add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ + φ) := by
  intro s hs
  by_cases h : ψ s = 0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h

theorem smul {V : BasisState → Prop} (c : ℂ) {ψ : State}
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])

theorem list_sum {A : Type} {V : BasisState → Prop} (xs : List A) (f : A → State)
    (hf : ∀ a ∈ xs, SupportedOn V (f a)) : SupportedOn V (xs.map f).sum := by
  induction xs with
  | nil => exact supportedOn_zero V
  | cons a xs ih =>
    exact add (hf a (by simp)) (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

theorem linear (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
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
    exact add (smul c (hL s hvs)) (ih hvψ)

end
end ShorECDLP.Entrant.Single.Support

end

-- ==== part: Single/WindowModels ====

section
/-! Instantiate history-aware refinement using only the mixed-window contract.
Concrete bodies may later discharge that contract without changing this proof. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

/-- Coherent superpositions of valid point encodings with a fixed clean frame. -/
def pointFamily (root : BasisState) (s : BasisState) : Prop :=
  ∃ P : Point, s = pointWrite P root

def signedModel {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (hwires : ∀ w, (physical w).wires = (bank w.width).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow) :
    WindowModel (readConstant coeffs Q) where
  physical := physical w
  point := increment Q w
  bias := offsetScalar w.width w.exponent • w.base Q
  ideal := Finsupp.lmapDomain ℂ ℂ (law.update Q w)
  valid := WindowValid w
  nodup := by rw [hwires]; exact List.nodup_reverse.mpr (bank_nodup w.width)
  coherent := law.coherent w Q hQ hn

theorem signedModel_step {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (hwires : ∀ w, (physical w).wires = (bank w.width).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow)
    (prior bits : List Bool) (P : Point) (root : BasisState)
    (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (signedModel law hwires Q hQ hn w).step prior bits (ket (pointWrite P root)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (P + increment Q w (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, signedModel, hwires, List.reverse_reverse, LinearMap.comp_apply]
  exact signed_window_point_sum law Q hQ hn w prior bits P root hs hz

theorem signedModel_prepared {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (hwires : ∀ w, (physical w).wires = (bank w.width).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (signedModel law hwires Q hQ hn w).valid
      (Quantum.run ((signedModel law hwires Q hQ hn w).physical.wires.reverse.map Gate.H) ψ) := by
  simp only [signedModel, hwires, List.reverse_reverse]
  apply Support.linear (pointFamily root) (WindowValid w) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [phaseHadamards_uniform _ (bank_nodup w.width) _ (point_bank_clean w.width P root hz)]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact supportedOn_ket _ _ (assigned_valid w P root hs hz input)

theorem signedModel_preserves {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (hwires : ∀ w, (physical w).wires = (bank w.width).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (prior bits : List Bool) (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (pointFamily root) ((signedModel law hwires Q hQ hn w).step prior bits ψ) := by
  apply Support.linear (pointFamily root) (pointFamily root) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [signedModel_step law hwires Q hQ hn w prior bits P root hs hz]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

theorem ready_signed {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (hwires : ∀ w, (physical w).wires = (bank w.width).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List SignedWindow)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    Ready (ws.map (signedModel law hwires Q hQ hn)) ψ := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · exact signedModel_prepared law hwires Q hQ hn w root hs hz ψ hψ
    · intro prior bits
      exact ih _ (signedModel_preserves law hwires Q hQ hn w root hs hz prior bits ψ hψ)

def firstModel {n : Nat} {coeffs : Fin n → PointCoeff} (physical : Window n)
    (law : WindowLaw coeffs physical firstUpdate FirstWindowInput)
    (hwires : physical.wires = (bank 16).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : WindowModel (readConstant coeffs Q) where
  physical := physical
  point := initialPoint Q
  bias := -(leftOffset • G + rightOffset • Q)
  ideal := Finsupp.lmapDomain ℂ ℂ (firstUpdate Q)
  valid := FirstWindowInput
  nodup := by rw [hwires]; exact List.nodup_reverse.mpr (bank_nodup 16)
  coherent := law Q hQ hn

theorem firstModel_step {n : Nat} {coeffs : Fin n → PointCoeff} (physical : Window n)
    (law : WindowLaw coeffs physical firstUpdate FirstWindowInput)
    (hwires : physical.wires = (bank 16).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (prior bits : List Bool) (root : BasisState) (hz : Clean streamAddress root) :
    (firstModel physical law hwires Q hQ hn).step prior bits (ket root) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (initialPoint Q (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, firstModel, hwires, List.reverse_reverse, LinearMap.comp_apply]
  exact first_window_point_sum Q prior bits root hz

theorem ready_first_signed {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (hwires : ∀ w, (physical w).wires = (bank w.width).reverse)
    (first : Window n) (hfirst : WindowLaw coeffs first firstUpdate FirstWindowInput)
    (hfirstWires : first.wires = (bank 16).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List SignedWindow)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready (firstModel first hfirst hfirstWires Q hQ hn ::
      ws.map (signedModel law hwires Q hQ hn)) (ket root) := by
  constructor
  · simp only [firstModel, hfirstWires, List.reverse_reverse]
    exact firstWindowInput_prepare _ (bank_subset 16) _ (supportedOn_ket _ _ hs)
  · intro prior bits
    apply ready_signed law hwires Q hQ hn ws root hs hz
    rw [firstModel_step first hfirst hfirstWires Q hQ hn prior bits root hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

theorem signedModel_pointRule {n : Nat} {coeffs : Fin n → PointCoeff}
    {physical : SignedWindow → Window n} (law : SignedWindowLaw coeffs physical)
    (hwires : ∀ w, (physical w).wires = (bank w.width).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (signedModel law hwires Q hQ hn w) := by
  intro prior bits P
  simpa only [signedModel, hwires, List.length_reverse, bank_width] using
    signedModel_step law hwires Q hQ hn w prior bits P root hs hz

theorem firstModel_firstRule {n : Nat} {coeffs : Fin n → PointCoeff} (physical : Window n)
    (law : WindowLaw coeffs physical firstUpdate FirstWindowInput)
    (hwires : physical.wires = (bank 16).reverse)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hz : Clean streamAddress root) :
    FirstRule root (ket root) (firstModel physical law hwires Q hQ hn) := by
  intro prior bits
  have hlen : (bank 16).length = 16 := by decide +kernel
  simpa only [firstModel, hwires, List.length_reverse, hlen] using
    firstModel_step physical law hwires Q hQ hn prior bits root hz

end
end ShorECDLP.Entrant.Single.Distribution

end


/-! EDITABLE. Single-trial entrant: concrete single-trial success.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Distribution ====

section
/-! Distribution proof entry point for the mixed-width single-trial construction. -/

end

-- ==== part: Single/Scalar ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

/-- The fixed mixed-width offset cancels the centered odd-digit bias. -/
theorem increment_offset (Q : Point) (hQ : order • Q = 0) (w : SignedWindow) (v : Nat) :
    increment Q w v + offsetScalar w.width w.exponent • w.base Q =
      (v * 2^w.exponent) • w.base Q := by
  let P := w.base Q
  have hr : order • P = 0 := by
    cases w with
    | left16 _ | left15 _ => exact generator_nsmul_eq_zero
    | right16 _ => exact hQ
  have hh : halfOrder ≤ 2^(w.width-1) + order := by
    have hl : halfOrder ≤ order := by norm_num [halfOrder, order]
    exact hl.trans (Nat.le_add_left _ _)
  have he : (2^(w.width-1) + order - halfOrder) • P + halfOrder • P =
      2^(w.width-1) • P := by
    rw [← add_nsmul, Nat.sub_add_cancel hh, add_nsmul, hr, add_zero]
  have hoff : offsetScalar w.width w.exponent • P =
      2^(w.width-1) • (2^w.exponent • P) - (halfOrder * 2^w.exponent) • P := by
    unfold offsetScalar
    rw [mul_smul, smul_comm (2^(w.width-1) + order - halfOrder) (2^w.exponent),
      eq_sub_iff_add_eq.mpr he, nsmul_sub]
    simp only [mul_smul]
    rw [smul_comm (2^w.exponent) (2^(w.width-1)), smul_comm (2^w.exponent) halfOrder]
  let H := (halfOrder * 2^w.exponent) • P
  have hd : H + H = 2^w.exponent • P := by
    change (halfOrder * 2^w.exponent) • P + (halfOrder * 2^w.exponent) • P = _
    rw [mul_smul, smul_comm halfOrder (2^w.exponent), ← nsmul_add]
    exact congrArg (fun R : Point => 2^w.exponent • R)
      (signedWindowHalfPoint_double P order (by decide +kernel) hr)
  have hp : (2 : Int)^w.width = 2 * (2^(w.width-1) : Nat) := by
    cases w <;> norm_num [SignedWindow.width]
  have hcalc : ((2*(v:Int)-(2:Int)^w.width+1) • H) +
      (2^(w.width-1) • (H+H) - H) = v • (H+H) := by
    rw [hp]
    module
  change ((2*(v:Int)-(2:Int)^w.width+1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2^w.exponent) P).symm

/-- Scalar reconstruction expressed without division or modular representatives. -/
theorem increment_eq_unsigned_sub_offset (Q : Point) (hQ : order • Q = 0)
    (w : SignedWindow) (v : Nat) :
    increment Q w v = (v * 2^w.exponent) • w.base Q -
      offsetScalar w.width w.exponent • w.base Q :=
  eq_sub_iff_add_eq.mpr (increment_offset Q hQ w v)

theorem left_offsets :
    (leftSigned.map (fun w => offsetScalar w.width w.exponent)).sum = leftOffset := by
  simp [leftSigned, leftOffset, widths, exponents, List.ofFn_succ,
    SignedWindow.width, SignedWindow.exponent]

theorem right_offsets :
    (rightSigned.map (fun w => offsetScalar w.width w.exponent)).sum = rightOffset := by
  simp [rightSigned, rightOffset, rightWidths, rightExponents, List.ofFn_succ,
    SignedWindow.width, SignedWindow.exponent]

theorem left_base (Q : Point) (w : SignedWindow) (hw : w ∈ leftSigned) : w.base Q = G := by
  simp only [leftSigned, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem right_base (Q : Point) (w : SignedWindow) (hw : w ∈ rightSigned) : w.base Q = Q := by
  simp only [rightSigned, List.mem_ofFn] at hw
  obtain ⟨i, rfl⟩ := hw
  rfl

theorem increments_sum (Q : Point) (hQ : order • Q = 0) (ws : List SignedWindow)
    (P : Point) (hbase : ∀ w ∈ ws, w.base Q = P) (values : SignedWindow → Nat) :
    (ws.map (fun w => increment Q w (values w))).sum =
      (ws.map (fun w => values w * 2^w.exponent)).sum • P -
        (ws.map (fun w => offsetScalar w.width w.exponent)).sum • P := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [increment_eq_unsigned_sub_offset Q hQ w, hbase w (by simp),
      ih (fun v hv => hbase v (List.mem_cons_of_mem w hv))]
    simp only [add_nsmul]
    abel

/-- The direct-load offsets cancel all 33 signed biases exactly. -/
theorem unsigned_reconstruction (Q : Point) (hQ : order • Q = 0)
    (first : Nat) (values : SignedWindow → Nat) :
    initialPoint Q first + (leftSigned.map (fun w => increment Q w (values w))).sum +
      (rightSigned.map (fun w => increment Q w (values w))).sum =
    (first * 2^247 + (leftSigned.map (fun w => values w * 2^w.exponent)).sum) • G +
      (rightSigned.map (fun w => values w * 2^w.exponent)).sum • Q := by
  rw [increments_sum Q hQ leftSigned G (left_base Q) values,
    increments_sum Q hQ rightSigned Q (right_base Q) values, left_offsets, right_offsets]
  unfold initialPoint
  simp only [add_nsmul]
  abel

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Setup ====

section
/-! The complete distribution theorem is parameterized by coherent physical
windows. Counts and Fourier order are explicit interface obligations. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option pp.maxSteps 60

structure Setup {n : Nat} (coeffs : Fin n → PointCoeff) where
  first : Window n
  signed : SignedWindow → Window n
  firstLaw : WindowLaw coeffs first firstUpdate FirstWindowInput
  signedLaw : SignedWindowLaw coeffs signed
  firstWires : first.wires = (bank 16).reverse
  signedWires : ∀ w, (signed w).wires = (bank w.width).reverse
  firstCount : first.count = 65535
  signedCount : ∀ w, (signed w).count = 30700717

def Setup.firstModel {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : WindowModel (readConstant coeffs Q) :=
  Distribution.firstModel s.first s.firstLaw s.firstWires Q hQ hn

def Setup.signedModel {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow) :
    WindowModel (readConstant coeffs Q) := ShorECDLP.Entrant.Single.Distribution.signedModel s.signedLaw s.signedWires Q hQ hn w

@[irreducible] def Setup.leftModels {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : List (WindowModel (readConstant coeffs Q)) :=
  s.firstModel Q hQ hn :: leftSigned.map (s.signedModel Q hQ hn)

@[irreducible] def Setup.rightModels {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : List (WindowModel (readConstant coeffs Q)) :=
  rightSigned.map (s.signedModel Q hQ hn)

def SignedWeights (Q P : Point) : List SignedWindow → Prop
  | List.nil => True
  | w :: ws => w.base Q = P ∧ w.exponent = (ws.map SignedWindow.width).sum ∧ SignedWeights Q P ws

theorem left_signed_weights (Q : Point) : SignedWeights Q G leftSigned := by
  norm_num [leftSigned, List.ofFn_succ, SignedWeights, SignedWindow.width,
    SignedWindow.exponent, SignedWindow.base]

theorem right_signed_weights (Q : Point) : SignedWeights Q Q rightSigned := by
  norm_num [rightSigned, List.ofFn_succ, SignedWeights, SignedWindow.width,
    SignedWindow.exponent, SignedWindow.base]

theorem Setup.signed_length {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow) :
    (s.signedModel Q hQ hn w).physical.wires.length = w.width := by
  simp only [Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel, s.signedWires, List.length_reverse, bank_width]

theorem Setup.modelWeights {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q P : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (ws : List SignedWindow) (hw : SignedWeights Q P ws) :
    ModelWeights P (ws.map (s.signedModel Q hQ hn)) := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · intro v
      change increment Q w v + offsetScalar w.width w.exponent • w.base Q = _
      have hwidths : ((ws.map (s.signedModel Q hQ hn)).map
          (fun w => w.physical.wires.length)).sum = (ws.map SignedWindow.width).sum := by
        simp only [List.map_map, Function.comp_def, s.signed_length]
      rw [hwidths, ← hw.2.1, ← hw.1]
      exact increment_offset Q hQ w v
    · exact ih hw.2.2

theorem left_signed_width : (leftSigned.map SignedWindow.width).sum = 247 := by
  norm_num [leftSigned, List.ofFn_succ, SignedWindow.width]

theorem right_signed_width : (rightSigned.map SignedWindow.width).sum = 224 := by
  norm_num [rightSigned, List.ofFn_succ, SignedWindow.width]

theorem Setup.left_weights {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ModelWeights G (s.leftModels Q hQ hn) := by
  rw [Setup.leftModels]
  constructor
  · intro v
    change initialPoint Q v + -(leftOffset • G + rightOffset • Q) = _
    have hwidths : ((leftSigned.map (s.signedModel Q hQ hn)).map
        (fun w => w.physical.wires.length)).sum = 247 := by
      simp only [List.map_map, Function.comp_def, s.signed_length, left_signed_width]
    rw [hwidths]
    unfold initialPoint
    simp only [add_nsmul]
    abel
  · exact s.modelWeights Q G hQ hn leftSigned (left_signed_weights Q)

theorem Setup.right_weights {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ModelWeights Q (s.rightModels Q hQ hn) := by
  rw [Setup.rightModels]
  exact s.modelWeights Q Q hQ hn rightSigned (right_signed_weights Q)

theorem sum_nat_smul (xs : List Nat) (P : Point) : (xs.map (fun k => k • P)).sum = xs.sum • P := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, add_nsmul]

theorem Setup.signed_bias_sum {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q P : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List SignedWindow)
    (hbase : ∀ w ∈ ws, w.base Q = P) :
    ((ws.map (s.signedModel Q hQ hn)).map WindowModel.bias).sum =
      (ws.map (fun w => offsetScalar w.width w.exponent)).sum • P := by
  rw [← sum_nat_smul]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  change offsetScalar w.width w.exponent • w.base Q = _
  rw [hbase w hw]

theorem Setup.bias_cancels {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ((s.leftModels Q hQ hn).map WindowModel.bias).sum +
      ((s.rightModels Q hQ hn).map WindowModel.bias).sum = 0 := by
  rw [Setup.leftModels, Setup.rightModels, List.map_cons, List.sum_cons,
    s.signed_bias_sum Q G hQ hn leftSigned (left_base Q),
    s.signed_bias_sum Q Q hQ hn rightSigned (right_base Q), left_offsets, right_offsets]
  change -(leftOffset • G + rightOffset • Q) + leftOffset • G + rightOffset • Q = 0
  abel

def initialRoot : BasisState := zeroBasisState[836 ↦ true]

theorem initialRoot_input : FirstWindowInput initialRoot := firstWindowInput_start

theorem initialRoot_clean : Clean streamAddress initialRoot := by
  intro v hv
  have he := (show ∀ v ∈ streamAddress, v ≠ 836 by decide +kernel) v hv
  simp only [initialRoot, upd, if_neg he, zeroBasisState]

theorem Setup.ready {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    Ready (s.leftModels Q hQ hn ++ s.rightModels Q hQ hn) (ket initialRoot) := by
  rw [Setup.leftModels, Setup.rightModels, List.cons_append, ← List.map_append]
  exact ready_first_signed s.signedLaw s.signedWires s.first s.firstLaw s.firstWires
    Q hQ hn (leftSigned ++ rightSigned) initialRoot initialRoot_input initialRoot_clean

theorem Setup.kernel {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    KernelLaw Q initialRoot (s.leftModels Q hQ hn) (s.rightModels Q hQ hn) (ket initialRoot) := by
  rw [Setup.leftModels, Setup.rightModels]
  apply kernelLaw_of_windows Q initialRoot (ket initialRoot) (s.firstModel Q hQ hn)
    (leftSigned.map (s.signedModel Q hQ hn)) (rightSigned.map (s.signedModel Q hQ hn))
  · exact firstModel_firstRule s.first s.firstLaw s.firstWires Q hQ hn initialRoot initialRoot_clean
  · intro w hw
    rw [← List.map_append] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact signedModel_pointRule s.signedLaw s.signedWires Q hQ hn v
      initialRoot initialRoot_input initialRoot_clean
  · simpa only [Setup.leftModels] using s.left_weights Q hQ hn
  · simpa only [Setup.rightModels] using s.right_weights Q hQ hn
  · simpa only [Setup.leftModels, Setup.rightModels] using s.bias_cancels Q hQ hn

theorem Setup.left_precision {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : precision (s.leftModels Q hQ hn) = 263 := by
  rw [precision, Setup.leftModels, List.map_cons, List.sum_cons]
  have hlen : (bank 16).length = 16 := by decide +kernel
  simp only [Setup.firstModel, ShorECDLP.Entrant.Single.Distribution.firstModel, s.firstWires, List.length_reverse, hlen,
    List.map_map, Function.comp_def, s.signed_length, left_signed_width]

theorem Setup.right_precision {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : precision (s.rightModels Q hQ hn) = 224 := by
  rw [precision, Setup.rightModels]
  simp only [List.map_map, Function.comp_def, s.signed_length, right_signed_width]

theorem Setup.left_metadata {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ((s.leftModels Q hQ hn).map WindowModel.physical).map
      (fun w => (w.count, w.wires.length)) = leftMetadata := by
  have hlen : (bank 16).length = 16 := by decide +kernel
  simp only [Setup.leftModels, List.map_cons, List.map_map, Function.comp_def,
    Setup.firstModel, ShorECDLP.Entrant.Single.Distribution.firstModel, Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel, s.firstCount, s.signedCount,
    s.firstWires, s.signedWires, List.length_reverse, hlen, bank_width]
  simp [leftSigned, leftMetadata, List.ofFn_succ, SignedWindow.width]

theorem Setup.right_metadata {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ((s.rightModels Q hQ hn).map WindowModel.physical).map
      (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp only [Setup.rightModels, List.map_map, Function.comp_def,
    Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel, s.signedCount, s.signedWires, List.length_reverse, bank_width]
  simp [rightSigned, rightMetadata, List.ofFn_succ, SignedWindow.width]

theorem Setup.left_count {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    axisCount ((s.leftModels Q hQ hn).map WindowModel.physical) = 491277270 := by
  rw [← recordCount_eq_axisCount, s.left_metadata, left_record_count]

theorem Setup.left_positions {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (start : Nat) :
    axisPositions ((s.leftModels Q hQ hn).map WindowModel.physical) start = positions leftMetadata start := by
  rw [axisPositions, s.left_metadata]

theorem Setup.right_positions {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (start : Nat) :
    axisPositions ((s.rightModels Q hQ hn).map WindowModel.physical) start = positions rightMetadata start := by
  rw [axisPositions, s.right_metadata]


end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/ConcreteDistribution ====

section
/-! Connect the distribution theorem to the real coherent bodies. Fourier
metadata is most-significant-first; lookup addresses remain little-endian. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option pp.maxSteps 60

theorem firstInputLaw : WindowLaw mixedCoefficientAt firstWindow firstUpdate FirstWindowInput := by
  intro Q hQ _hn start history
  obtain ⟨cs, hc, hm⟩ := firstWindow_coherent Q hQ start history
  exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (firstWindowInput_lookup s hs)), hm⟩

/-- All premises of the abstract distribution theorem are supplied by real bodies. -/
def concreteSetup : Setup mixedCoefficientAt where
  first := firstWindow
  signed := signedWindow
  firstLaw := firstInputLaw
  signedLaw := concreteSignedWindowLaw
  firstWires := by unfold firstWindow; rfl
  signedWires := signedWindow_wires
  firstCount := by unfold firstWindow; rfl
  signedCount := fun w => signedWindow_count w

def terminalInstrument : Instrument :=
  (AdaptiveCircuit.unitary [.X 836]
    (measureResetWithCorrection resetWires (fun _ => List.nil))).run

theorem terminalInstrument_mass (ψ : State) : terminalInstrument.bornMass ψ = normSq ψ := by
  calc
    _ = (measureResetWithCorrection resetWires (fun _ => List.nil)).run.bornMass
        (Quantum.run [.X 836] ψ) := by
      simp only [terminalInstrument, AdaptiveCircuit.run, Instrument.bornMass,
        List.map_map, Function.comp_def]
      rfl
    _ = normSq (Quantum.run [.X 836] ψ) := resetRegister_mass _ _
    _ = normSq ψ := normSq_run _ (by simp [CircuitWellFormed, Gate.WellFormed]) ψ


theorem concrete_model_left (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (concreteSetup.leftModels Q hQ hn).map WindowModel.physical = ShorECDLP.Entrant.Single.leftWindows := by
  simp only [Setup.leftModels, Setup.firstModel, ShorECDLP.Entrant.Single.Distribution.firstModel, Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel,
    concreteSetup, ShorECDLP.Entrant.Single.leftWindows, List.map_cons, List.map_map, Function.comp_def]

theorem concrete_model_right (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (concreteSetup.rightModels Q hQ hn).map WindowModel.physical = ShorECDLP.Entrant.Single.rightWindows := by
  simp only [Setup.rightModels, Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel,
    concreteSetup, ShorECDLP.Entrant.Single.rightWindows, List.map_map, Function.comp_def]

def physicalAxesData {n : Nat} (left right : List (Window n)) (read : ConstantBit n → Bool)
    (start : Nat) (history : Fin start → Bool) : Instrument :=
  (((axis left start List.nil).append (axis right (start + axisCount left) List.nil)).instantiate read history).run

theorem physicalAxes_asData {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool) :
    physicalAxes left right start history = physicalAxesData (left.map WindowModel.physical)
      (right.map WindowModel.physical) read start history := rfl

theorem prefix_filter_mass (I : Instrument) (gs : Circuit) (accept : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((I.map (fun b =>
      ({history := List.nil, kraus := Quantum.run gs} : InstrumentBranch).seq b)).filter
        (fun b => accept b.history)) ψ =
      Instrument.bornMass (I.filter (fun b => accept b.history)) (Quantum.run gs ψ) := by
  rw [List.filter_map]
  simp only [Function.comp_def, InstrumentBranch.seq, List.nil_append, Instrument.bornMass,
    List.map_map, LinearMap.comp_apply]

theorem append_run_fixed_right {n start a b finish : Nat}
    (p : Straight n start a) (q : Straight n a b) (r : Straight n b finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hr : ∀ h, (r.instantiate read h).run = target.run) :
    ((p.append (q.append r)).instantiate read history).run =
      ((p.append q).instantiate read history).run.seq target.run := by
  rw [append_run_history]
  simp_rw [append_run_fixed q r read _ target hr, AdaptiveCircuit.run_seq]
  rw [append_run_history]
  simp only [Instrument.seq, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro x hx
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro z hz
  rcases x with ⟨xh, xk⟩
  rcases y with ⟨yh, yk⟩
  rcases z with ⟨zh, zk⟩
  simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem straight_gate_run {n start finish : Nat} (g : TemplateGate n) (p : Straight n start finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((Straight.gate g p).instantiate read history).run =
      ((p.instantiate read history).run).map (fun b =>
        ({history := List.nil, kraus := Quantum.run (g.instantiate read)} : InstrumentBranch).seq b) := rfl

attribute [local irreducible] axis resetProgram

theorem unitary_run_map (gs : Circuit) (tail : AdaptiveCircuit) :
    (AdaptiveCircuit.unitary gs tail).run = tail.run.map (fun b =>
      ({history := List.nil, kraus := Quantum.run gs} : InstrumentBranch).seq b) := rfl

theorem framed_reset_run {n start a b finish out : Nat}
    (p : Straight n start a) (q : Straight n a b) (r : Straight n b finish) (h : finish = out)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hr : ∀ history, (r.instantiate read history).run = target.run) :
    ((framed p q r h).instantiate read history).run =
      (((p.append q).instantiate read history).run.seq (AdaptiveCircuit.unitary [.X 836] target).run).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  have ht : ∀ history, ((Straight.gate (.literal (.X 836)) r).instantiate read history).run =
      (AdaptiveCircuit.unitary [.X 836] target).run := by
    intro history
    rw [straight_gate_run, hr history, unitary_run_map]
    rfl
  rw [framed_run, unitary_run_map, append_run_fixed_right _ _ _ _ _ _ ht]

theorem program_run_data (read : ConstantBit 901120 → Bool) :
    (ShorECDLP.Entrant.Single.program.instantiate read Fin.elim0).run =
      ((physicalAxesData leftWindows rightWindows read 0 Fin.elim0).seq terminalInstrument).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  calc
    _ = ((ShorECDLP.Entrant.Single.trial 0).instantiate read Fin.elim0).run := by
      unfold ShorECDLP.Entrant.Single.program
      rw [castFinish_instantiate]
    _ = _ := by
      have hf : 0 + axisCount leftWindows + axisCount rightWindows + 854 = 0 + trialCount := by
        unfold trialCount
        omega
      simpa only [ShorECDLP.Entrant.Single.trial, physicalAxesData, terminalInstrument] using
        framed_reset_run (axis leftWindows 0 List.nil)
          (axis rightWindows (0 + axisCount leftWindows) List.nil)
          (resetBody (0 + axisCount leftWindows + axisCount rightWindows)) hf read Fin.elim0
          (measureResetWithCorrection resetWires (fun _ => List.nil))
          (resetBody_run _ read)

theorem concrete_axes_data (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    physicalAxes (concreteSetup.leftModels Q hQ hn) (concreteSetup.rightModels Q hQ hn) 0 Fin.elim0 =
      physicalAxesData leftWindows rightWindows (readConstant mixedCoefficientAt Q) 0 Fin.elim0 := by
  change physicalAxesData _ _ _ _ _ = _
  rw [concrete_model_left Q hQ hn, concrete_model_right Q hQ hn]

/-- Bind the distribution proof to the shared assembled program, including its reset. -/
theorem assembled_program_run (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (ShorECDLP.Entrant.Single.program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).run =
      ((physicalAxes (concreteSetup.leftModels Q hQ hn) (concreteSetup.rightModels Q hQ hn)
        0 Fin.elim0).seq terminalInstrument).map
          (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  exact (program_run_data (readConstant mixedCoefficientAt Q)).trans
    (congrArg (fun I : Instrument => (I.seq terminalInstrument).map
      (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b))
        (concrete_axes_data Q hQ hn).symm)


end
end ShorECDLP.Entrant.Single.Distribution

end

namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section

def fineEvent (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  pairAccept trialPositions.left.toList trialPositions.right.toList accept history

theorem Setup.event_mass {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hn : Q ≠ 0) (hQ : order • Q = 0)
    (J : Instrument) (hJ : ∀ ψ, J.bornMass ψ = normSq ψ) (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((physicalAxes (s.leftModels Q hQ hn) (s.rightModels Q hQ hn) 0 Fin.elim0).seq J).filter
        (fun b => fineEvent accept b.history)) (ket initialRoot) =
      idealEventMass Q initialRoot 263 224 accept := by
  have hm := physicalTwoAxes_event_mass Q initialRoot (s.leftModels Q hQ hn)
    (s.rightModels Q hQ hn) 0 Fin.elim0 (ket initialRoot) (s.ready Q hQ hn)
    (s.kernel Q hQ hn) J hJ accept
  rw [selectedTwoAxes_fixed_filter, s.left_count, s.left_positions, s.right_positions,
    s.left_precision, s.right_precision] at hm
  simpa only [fineEvent, trialPositions, Vector.toList_mk, List.toList_toArray] using hm

theorem program_event_mass (Q : Point) (hn : Q ≠ 0) (hQ : order • Q = 0)
    (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((ShorECDLP.Entrant.Single.program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent accept b.history)) (ket zeroBasisState) =
      idealEventMass Q initialRoot 263 224 accept := by
  rw [assembled_program_run Q hQ hn,
    prefix_filter_mass _ ([Gate.X 836]) (fineEvent accept) (ket zeroBasisState)]
  have hs : Quantum.run [.X 836] (ket zeroBasisState) = ket initialRoot := by
    simp [Quantum.run, applyGate_ket, onKet, initialRoot, zeroBasisState]
  rw [hs]
  exact concreteSetup.event_mass Q hn hQ terminalInstrument terminalInstrument_mass accept

theorem program_rounded_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ)/100 ≤ Instrument.bornMass
      (((ShorECDLP.Entrant.Single.program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent (ShorECDLP.Entrant.RoundedReadout.pairRecovered d) b.history))
      (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by
    rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [program_event_mass Q hn hQ, idealEventMass_distribution Q d hd]
  exact ShorECDLP.Entrant.RoundedReadout.pair_success Q d hn hd

end
end ShorECDLP.Entrant.Single.Distribution
