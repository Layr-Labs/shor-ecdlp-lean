import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds


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
  ·
    have hs : 5 * z / 6 ≤ Real.sin z := by nlinarith [mul_pos hz0 hz0]
    have ha : 25 / 36 ≤ Real.sin z ^ 2 * (1 / z ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hb : 0 ≤ Real.sin z ^ 2 * (1 / (Real.pi - z) ^ 2) := by positivity
    rw [mul_add]
    linarith
  rcases le_total z (6 / 5) with h2 | h2
  ·
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
  ·
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

noncomputable def phiR (N : ℕ) (c : ℝ) (a : ℕ) : ℝ :=
  if c ≤ (a : ℝ) then (a : ℝ) - c else (N : ℝ) - c + a

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
