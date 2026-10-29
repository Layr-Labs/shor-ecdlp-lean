import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds

/-! Window mass for quantum phase estimation.

With `N = 2 ^ t ≥ 128 r` outcomes, the QPE outcome distribution for the phase `n / r`
puts mass at least `9951 / 10000` on the outcomes `a` whose rounding `round (r a / N)`
equals `n`.  The proof combines Parseval (total mass `1`) with the pointwise bound
`|amplitude a|² ≤ (4 / π²) (1 / (4 u²) + 1 / (4 (N - u)²)) + 1 / N²`, `u = |a - N n / r|`,
obtained from the geometric series and `x ≤ tan x`, and a telescoping tail estimate in which
the wrap-around terms start at distance `2 N / (2 r)`. -/

namespace ShorECDLP.Entrant

namespace WindowMassProof

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
    ∑ k ∈ range M, 1 / (4 * (L + k) ^ 2) ≤ 1 / (4 * (L - 1)) - 1 / (4 * (L - 1 + M)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h1 : 0 < L - 1 + M := by linarith
    have h2 : 0 < L + M := by linarith
    have : 1 / (4 * (L + M) ^ 2) ≤
        1 / (4 * (L - 1 + M)) - 1 / (4 * (L - 1 + ((M + 1 : ℕ) : ℝ))) := by
      push_cast
      rw [show L - 1 + (M + 1) = L + M by ring]
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma sum_inv_sq_le (S : Finset ℕ) (φ : ℕ → ℝ) (L : ℝ) (hL : 1 < L)
    (hφ : ∀ a ∈ S, L ≤ φ a)
    (hsep : ∀ a b : ℕ, φ a - φ b = a - b ∨ φ a - φ b = b - a) :
    ∑ a ∈ S, 1 / (4 * (φ a) ^ 2) ≤ 1 / (4 * (L - 1)) := by
  set g : ℕ → ℕ := fun a => ⌊φ a - L⌋₊ with hg
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h2 := Nat.lt_floor_add_one (φ a - L)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb))
    have h4 := Nat.lt_floor_add_one (φ b - L)
    simp only [hg] at hab
    rw [hab] at h1 h2
    apply nat_eq_of_abs_lt
    rcases hsep a b with h | h
    · rw [abs_lt]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith
  have step1 : ∑ a ∈ S, 1 / (4 * (φ a) ^ 2) ≤ ∑ a ∈ S, 1 / (4 * (L + g a) ^ 2) := by
    apply sum_le_sum
    intro a ha
    have h1 : (g a : ℝ) ≤ φ a - L := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h0 : (0 : ℝ) ≤ g a := Nat.cast_nonneg _
    have h2 : 0 < L + g a := by linarith
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  have step2 : ∑ a ∈ S, 1 / (4 * (L + g a) ^ 2) =
      ∑ k ∈ S.image g, 1 / (4 * (L + k) ^ 2) := by
    rw [sum_image hinj]
  have step3 : ∑ k ∈ S.image g, 1 / (4 * (L + k) ^ 2) ≤
      ∑ k ∈ range (S.sup g + 1), 1 / (4 * (L + k) ^ 2) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [mem_image] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [mem_range]
      exact Nat.lt_succ_of_le (le_sup ha)
    · intro k _ _
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      have : 0 < L + k := by linarith
      positivity
  have h4 := sum_range_inv_sq_le L hL (S.sup g + 1)
  have h5 : 0 ≤ 1 / (4 * (L - 1 + ((S.sup g + 1 : ℕ) : ℝ))) := by
    have : (0 : ℝ) ≤ ((S.sup g + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 0 < L - 1 + ((S.sup g + 1 : ℕ) : ℝ) := by linarith
    positivity
  linarith

/-- `x² ≤ sin² x · (1 + x²)` on `(0, π / 2]`, from `x ≤ tan x`. -/
lemma sq_le_sin_sq_mul (x : ℝ) (h0 : 0 < x) (h1 : x ≤ Real.pi / 2) :
    x ^ 2 ≤ Real.sin x ^ 2 * (1 + x ^ 2) := by
  rcases h1.lt_or_eq with h1 | h1
  · have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
    have ht := Real.lt_tan h0 h1
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc] at ht
    have hxc : 0 ≤ x * Real.cos x := by positivity
    have h2 : (x * Real.cos x) ^ 2 ≤ Real.sin x ^ 2 := pow_le_pow_left₀ hxc ht.le 2
    have hc2 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by linarith [Real.sin_sq_add_cos_sq x]
    rw [mul_pow, hc2] at h2
    nlinarith
  · rw [h1, Real.sin_pi_div_two]
    nlinarith

/-- Sharp inverse-sine bound: `1 / (N sin (π v / N))² ≤ 1 / (π v)² + 1 / N²` for `v ≤ N / 2`. -/
lemma inv_sin_sq_le (N v : ℝ) (hN : 0 < N) (hv : 0 < v) (hvN : v ≤ N / 2) :
    1 / (N * Real.sin (Real.pi * v / N)) ^ 2 ≤ 1 / (Real.pi ^ 2 * v ^ 2) + 1 / N ^ 2 := by
  set x := Real.pi * v / N with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ Real.pi / 2 := by
    rw [hx, div_le_iff₀ hN]
    nlinarith [Real.pi_pos]
  have key := sq_le_sin_sq_mul x hx0 hx1
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hNx : (Real.pi * v) ^ 2 = N ^ 2 * x ^ 2 := by
    rw [hx]; field_simp
  calc 1 / (N * Real.sin x) ^ 2 ≤ (1 + x ^ 2) / (Real.pi * v) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), hNx]
        have h3 := mul_le_mul_of_nonneg_left key (sq_nonneg N)
        have e : (1 + x ^ 2) * (N * Real.sin x) ^ 2 = N ^ 2 * (Real.sin x ^ 2 * (1 + x ^ 2)) := by
          ring
        rw [e]
        linarith
    _ = 1 / (Real.pi ^ 2 * v ^ 2) + 1 / N ^ 2 := by
        rw [hx]
        field_simp

/-- The pointwise tail bound on the circle, with the constant `4 / π² ≤ 406 / 1000`. -/
lemma inv_sin_sq_le' (N u : ℝ) (hN : 0 < N) (hu0 : 0 < u) (huN : u < N) :
    1 / (N * Real.sin (Real.pi * u / N)) ^ 2 ≤
      (406 / 1000) * (1 / (4 * u ^ 2) + 1 / (4 * (N - u) ^ 2)) + 1 / N ^ 2 := by
  have hpi : 4 / Real.pi ^ 2 ≤ 406 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_gt_d2]
  have hK : ∀ v : ℝ, 0 < v → 1 / (Real.pi ^ 2 * v ^ 2) ≤ (406 / 1000) * (1 / (4 * v ^ 2)) := by
    intro v hv
    have e : 1 / (Real.pi ^ 2 * v ^ 2) = (4 / Real.pi ^ 2) * (1 / (4 * v ^ 2)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hpi (by positivity)
  rcases le_total u (N / 2) with h | h
  · have h1 := inv_sin_sq_le N u hN hu0 h
    have h2 := hK u hu0
    have h3 : 0 ≤ (406 / 1000 : ℝ) * (1 / (4 * (N - u) ^ 2)) := by positivity
    rw [mul_add]
    linarith
  · have e : Real.sin (Real.pi * u / N) = Real.sin (Real.pi * (N - u) / N) := by
      rw [← Real.sin_pi_sub]
      congr 1
      field_simp
    rw [e]
    have h1 := inv_sin_sq_le N (N - u) hN (by linarith) (by linarith)
    have h2 := hK (N - u) (by linarith)
    have h3 : 0 ≤ (406 / 1000 : ℝ) * (1 / (4 * u ^ 2)) := by positivity
    rw [mul_add]
    linarith

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

lemma point_bound (N : ℕ) (hN : 0 < N) (x u : ℝ) (hu0 : 0 < u) (huN : u < N)
    (hx : x / 2 = Real.pi * u / N ∨ x / 2 = -(Real.pi * u / N)) :
    Complex.normSq ((N : ℂ)⁻¹ * ∑ y ∈ range N, Complex.exp (Complex.I * (x : ℂ)) ^ y)
      ≤ (406 / 1000) * (1 / (4 * u ^ 2) + 1 / (4 * ((N : ℝ) - u) ^ 2)) + 1 / (N : ℝ) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hspos : 0 < Real.sin (Real.pi * u / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hNR]
    nlinarith [Real.pi_pos]
  have habs : |Real.sin (x / 2)| = Real.sin (Real.pi * u / N) := by
    rcases hx with hx | hx <;> rw [hx]
    · exact abs_of_pos hspos
    · rw [Real.sin_neg, abs_neg]; exact abs_of_pos hspos
  have hne : Real.sin (x / 2) ≠ 0 := by
    intro h; rw [h, abs_zero] at habs; linarith
  have h1 := amp_normSq_le N x hne
  rw [habs, div_pow, one_pow] at h1
  exact h1.trans (inv_sin_sq_le' N u hNR hu0 huN)

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

set_option maxHeartbeats 1000000 in
lemma window_mass_aux (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r) (hrN : 128 * r ≤ N)
    (hNbig : 1000000 ≤ N) :
    (9951 : ℝ) / 10000 ≤ ∑ a ∈ range N,
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
  have hNbig' : (1000000 : ℝ) ≤ N := by exact_mod_cast hNbig
  have hL64 : 64 ≤ L := by nlinarith
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  have htot := parseval N hN β
  set K : ℝ := 406 / 1000 with hK
  have hK0 : 0 ≤ K := by norm_num [hK]
  set e : ℝ := 1 / (N : ℝ) ^ 2 with he
  -- pointwise domination of the tail
  have hpt : ∀ a ∈ range N, (if (2 * r * a + N) / (2 * N) = n then 0 else ampSq N β a) ≤
      (if c + L ≤ (a : ℝ) then
          K * (1 / (4 * ((a : ℝ) - c) ^ 2) + 1 / (4 * ((N : ℝ) - ((a : ℝ) - c)) ^ 2)) + e
        else 0) +
      (if (a : ℝ) + L ≤ c then
          K * (1 / (4 * (c - (a : ℝ)) ^ 2) + 1 / (4 * ((N : ℝ) - (c - (a : ℝ))) ^ 2)) + e
        else 0) := by
    intro a ha
    have haN : (a : ℝ) < N := by exact_mod_cast mem_range.mp ha
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have he0 : 0 ≤ e := by positivity
    have hi₂ : 0 ≤ (if c + L ≤ (a : ℝ) then
        K * (1 / (4 * ((a : ℝ) - c) ^ 2) + 1 / (4 * ((N : ℝ) - ((a : ℝ) - c)) ^ 2)) + e
          else 0) := by
      split_ifs <;> positivity
    have hi₁ : 0 ≤ (if (a : ℝ) + L ≤ c then
        K * (1 / (4 * (c - (a : ℝ)) ^ 2) + 1 / (4 * ((N : ℝ) - (c - (a : ℝ))) ^ 2)) + e
          else 0) := by
      split_ifs <;> positivity
    by_cases hw : (2 * r * a + N) / (2 * N) = n
    · rw [if_pos hw]
      linarith
    · rw [if_neg hw]
      rcases window_cases r N n a hN hw with h | h
      · have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
        have hA : c + L ≤ (a : ℝ) := by nlinarith
        rw [if_pos hA]
        have hb := point_bound N hN (2 * Real.pi * (β - a / N)) ((a : ℝ) - c)
          (by linarith) (by linarith) (Or.inr (by rw [hc, hβ]; field_simp; ring))
        have : ampSq N β a ≤
            K * (1 / (4 * ((a : ℝ) - c) ^ 2) + 1 / (4 * ((N : ℝ) - ((a : ℝ) - c)) ^ 2)) + e := hb
        linarith
      · have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
        have hA : (a : ℝ) + L ≤ c := by nlinarith
        rw [if_pos hA]
        have hb := point_bound N hN (2 * Real.pi * (β - a / N)) (c - (a : ℝ))
          (by linarith) (by linarith) (Or.inl (by rw [hc, hβ]; field_simp))
        have : ampSq N β a ≤
            K * (1 / (4 * (c - (a : ℝ)) ^ 2) + 1 / (4 * ((N : ℝ) - (c - (a : ℝ))) ^ 2)) + e := hb
        linarith
  have hL1 : (1 : ℝ) < L := by linarith
  set SA := (range N).filter (fun a : ℕ => c + L ≤ (a : ℝ)) with hSA
  set SB := (range N).filter (fun a : ℕ => (a : ℝ) + L ≤ c) with hSB
  -- the four tail sums; the wrap-around ones start at distance `2 L`
  have s1 := sum_inv_sq_le SA (fun a : ℕ => (a : ℝ) - c) L hL1
    (fun a ha => by rw [hSA, mem_filter] at ha; linarith [ha.2])
    (fun a b => Or.inl (by ring))
  have s2 := sum_inv_sq_le SA (fun a : ℕ => (N : ℝ) - ((a : ℝ) - c)) (2 * L + 1)
    (by linarith)
    (fun a ha => by
      rw [hSA, mem_filter, mem_range] at ha
      have : (a : ℝ) + 1 ≤ N := by exact_mod_cast ha.1
      linarith)
    (fun a b => Or.inr (by ring))
  have s3 := sum_inv_sq_le SB (fun a : ℕ => c - (a : ℝ)) L hL1
    (fun a ha => by rw [hSB, mem_filter] at ha; linarith [ha.2])
    (fun a b => Or.inr (by ring))
  have s4 := sum_inv_sq_le SB (fun a : ℕ => (N : ℝ) - (c - (a : ℝ))) (2 * L) (by linarith)
    (fun a _ => by
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      linarith)
    (fun a b => Or.inl (by ring))
  have hcardA : (SA.card : ℝ) ≤ N := by
    exact_mod_cast (card_filter_le _ _).trans (card_range N).le
  have hcardB : (SB.card : ℝ) ≤ N := by
    exact_mod_cast (card_filter_le _ _).trans (card_range N).le
  have hsumA : ∑ a ∈ SA,
      (K * (1 / (4 * ((a : ℝ) - c) ^ 2) + 1 / (4 * ((N : ℝ) - ((a : ℝ) - c)) ^ 2)) + e) =
      K * (∑ a ∈ SA, 1 / (4 * ((a : ℝ) - c) ^ 2) +
        ∑ a ∈ SA, 1 / (4 * ((N : ℝ) - ((a : ℝ) - c)) ^ 2)) + SA.card * e := by
    rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
  have hsumB : ∑ a ∈ SB,
      (K * (1 / (4 * (c - (a : ℝ)) ^ 2) + 1 / (4 * ((N : ℝ) - (c - (a : ℝ))) ^ 2)) + e) =
      K * (∑ a ∈ SB, 1 / (4 * (c - (a : ℝ)) ^ 2) +
        ∑ a ∈ SB, 1 / (4 * ((N : ℝ) - (c - (a : ℝ))) ^ 2)) + SB.card * e := by
    rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
  have hce : ∀ m : ℝ, m ≤ N → m * e ≤ 1 / 1000000 := by
    intro m hm
    rw [he, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num), one_mul, sq]
    have h2 : (N : ℝ) * 1000000 ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_left hNbig' hNR.le
    linarith
  have hb1 : 1 / (4 * (L - 1)) ≤ 1 / 252 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hb2 : 1 / (4 * (2 * L + 1 - 1)) ≤ 1 / 512 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hb4 : 1 / (4 * (2 * L - 1)) ≤ 1 / 508 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have htail : ∑ a ∈ range N, (if (2 * r * a + N) / (2 * N) = n then 0 else ampSq N β a) ≤
      49 / 10000 := by
    refine (sum_le_sum hpt).trans ?_
    rw [sum_add_distrib, ← sum_filter, ← sum_filter, ← hSA, ← hSB, hsumA, hsumB]
    have hA1 := mul_le_mul_of_nonneg_left (add_le_add (s1.trans hb1) (s2.trans hb2)) hK0
    have hB1 := mul_le_mul_of_nonneg_left (add_le_add (s3.trans hb1) (s4.trans hb4)) hK0
    have hA2 := hce _ hcardA
    have hB2 := hce _ hcardB
    simp only at hA1 hB1
    linarith only [hA1, hB1, hA2, hB2, hK]
  have hsplit : ∑ a ∈ range N,
      (if (2 * r * a + N) / (2 * N) = n then ampSq N β a else 0) =
      ∑ a ∈ range N, ampSq N β a -
        ∑ a ∈ range N, (if (2 * r * a + N) / (2 * N) = n then 0 else ampSq N β a) := by
    rw [eq_sub_iff_add_eq, ← sum_add_distrib]
    refine sum_congr rfl (fun a _ => ?_)
    split_ifs <;> simp
  rw [hsplit, htot]
  linarith

end WindowMassProof

theorem window_mass (r t n : ℕ) (hn0 : 0 < n) (hnr : n < r) (hrt : 128 * r ≤ 2 ^ t)
    (hbig : 1000000 ≤ 2 ^ t) :
    (9951 : ℝ) / 10000 ≤ ∑ a ∈ Finset.range (2 ^ t),
      if (2 * r * a + 2 ^ t) / (2 * 2 ^ t) = n then
        Complex.normSq ((((2 ^ t : ℕ) : ℂ)⁻¹) * ∑ y ∈ Finset.range (2 ^ t),
          Complex.exp (Complex.I * ((2 * Real.pi * ((n : ℝ) / (r : ℝ) - (a : ℝ) / ((2 ^ t : ℕ) : ℝ)) : ℝ) : ℂ)) ^ y)
      else 0 :=
  WindowMassProof.window_mass_aux r (2 ^ t) n hn0 hnr hrt hbig

end ShorECDLP.Entrant
