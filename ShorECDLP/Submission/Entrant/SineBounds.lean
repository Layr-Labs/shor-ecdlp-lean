import ShorECDLP.Submission.Entrant.SineCircuit

/-! Analytical success probability lower bound (`≥ 9911 / 10000`) for the 10-bit centered sine
window at precisions `(L, R) = (258, 204)` with `K = 3` neighbouring right shifts `{-1, 0, +1}`.

Structure:
1. Discrete Parseval (`dft_parseval`) → exact unit mass `sinePhaseAmplitude_parseval`.
2. Factorization `sinePhaseAmplitude M β a = N⁻¹ * W(ω^B) * G(B, ω)` →
   - Far tail (`512 < phiR ∧ 512 < phiL`): `≤ 12 / 1000000` via 1024-point Parseval on first differences.
   - Closed form & small/medium pointwise bounds on `3/2 ≤ φ ≤ 512`:
     `small (≤ 17): ≤ (508/10000) * cos²(πNβ) / (φ² - 1/4)²`
     `medium (16..512): ≤ (31/100) * cos²(πNβ) / (φ - 1/2)⁴`, summing over both sides to `≤ (68/1000000) * cos²(πNβ)`.
3. Elementary box bounds in `|σ| ∈ [0, 1/2]` using rational `smallSumQ` and `cos x ≤ min(1 - x²/2 + x⁴/24, π/2 - x)`:
   - Left axis (`258` bits, `4 * order < 2^258`): `miss_L ≤ (586/100000) * cos²(πNβ) + 12/1000000`.
   - Right axis (`204` bits, `3` shifts `-1, 0, +1`): `miss_R ≤ 136/100000 + (900/100000) * cos²(πNβ) + 12/1000000`.
4. Exact character average `∑_{k : Fin r} cos²(π M k / r) = r / 2` for `r` prime, `r ∤ M` →
   `sine_pair_success` (`≥ 9911 / 10000`) and `decoder_budget258`. -/

set_option Elab.async false

namespace ShorECDLP.Entrant.SineBounds
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Entrant.SineCircuit ShorECDLP.Entrant.WindowMassSharpProof
open ShorECDLP.Entrant.NeighborReadout ShorECDLP.Entrant.SinAverage ShorECDLP.Entrant.SinAverage261
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 300
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-! ### Part 1: Elementary trig & DFT Parseval -/

theorem eigenvalue_normSq (θ : ℝ) : Complex.normSq (eigenvalue θ) = 1 := by
  unfold eigenvalue
  rw [Complex.normSq_eq_norm_sq, show Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ) =
    ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I, one_pow]

theorem eigenvalue_int (m : ℤ) : eigenvalue (m : ℝ) = 1 := by
  unfold eigenvalue
  rw [show Complex.I * ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_int_mul_two_pi_mul_I]

theorem eigenvalue_add_int (θ : ℝ) (m : ℤ) : eigenvalue (θ + m) = eigenvalue θ := by
  rw [eigenvalue_add, eigenvalue_int, mul_one]

theorem eigenvalue_sub_int (θ : ℝ) (m : ℤ) : eigenvalue (θ - m) = eigenvalue θ := by
  simpa [sub_eq_add_neg] using eigenvalue_add_int θ (-m)

theorem normSq_eigenvalue_sub_one (θ : ℝ) :
    Complex.normSq (eigenvalue θ - 1) = 4 * Real.sin (Real.pi * θ) ^ 2 := by
  unfold eigenvalue
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num,
    show 2 * Real.pi * θ / 2 = Real.pi * θ by ring, mul_pow, sq_abs]
  norm_num

theorem normSq_eigenvalue_add_one (θ : ℝ) :
    Complex.normSq (eigenvalue θ + 1) = 4 * Real.cos (Real.pi * θ) ^ 2 := by
  have h1 : eigenvalue θ + 1 = -(eigenvalue (θ - 1/2) - 1) := by
    have hhalf : eigenvalue (-(1/2 : ℝ)) = -1 := by
      unfold eigenvalue
      have : Complex.I * ((2 * Real.pi * (-(1/2 : ℝ)) : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    have hsub : eigenvalue (θ - 1/2) = -eigenvalue θ := by
      rw [sub_eq_add_neg, eigenvalue_add, hhalf]; ring
    rw [hsub]; ring
  rw [h1, Complex.normSq_neg, normSq_eigenvalue_sub_one]
  have hs : Real.sin (Real.pi * (θ - 1/2)) = -Real.cos (Real.pi * θ) := by
    rw [show Real.pi * (θ - 1/2) = Real.pi * θ - Real.pi / 2 by ring, Real.sin_sub_pi_div_two]
  rw [hs, neg_sq]

theorem sin_jordan (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1/2) :
    2 * u ≤ Real.sin (Real.pi * u) := by
  have hx0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le hu0
  have hx : Real.pi * u ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin hx0 hx
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have he : 2 / Real.pi * (Real.pi * u) = 2 * u := by field_simp [hpi.ne']
  linarith

theorem cos_le_taylor4 (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv : ∀ t : ℝ, HasDerivAt f (Real.sin t - t + t ^ 3 / 6) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s ^ 2 / 2 + s ^ 4 / 24) (-t + t ^ 3 / 6) t := by
      have ha : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
      have hb : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
        simpa [mul_comm] using (hasDerivAt_pow 2 t).div_const (2 : ℝ)
      have hc : HasDerivAt (fun s : ℝ => s ^ 4 / 24) (t ^ 3 / 6) t := by
        convert (hasDerivAt_pow 4 t).div_const (24 : ℝ) using 1; ring
      convert (ha.sub hb).add hc using 1; ring
    convert h1.sub (Real.hasDerivAt_cos t) using 1; ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (show Differentiable ℝ f from fun t => (hderiv t).differentiableAt).continuous.continuousOn
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
      rw [(hderiv t).deriv]
      linarith [sin_ge_cubic t ht0]
  have h0 : f 0 ≤ f x := hmono (by simp) (by simpa using hx) hx
  simp only [f, Real.cos_zero] at h0
  linarith

theorem cos_le_pi_div_two_sub (x : ℝ) (hx : x ≤ Real.pi / 2) :
    Real.cos x ≤ Real.pi / 2 - x := by
  rw [← Real.sin_pi_div_two_sub]
  exact Real.sin_le (by linarith)

/-- General discrete Parseval identity on `Finset.range N`. -/
theorem dft_parseval (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ) :
    ∑ a ∈ range N, Complex.normSq (∑ x ∈ range N, f x * eigenvalue (-((a * x : ℕ) : ℝ) / N)) =
      (N : ℝ) * ∑ x ∈ range N, Complex.normSq (f x) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have horth (x y : ℕ) (hx : x < N) (hy : y < N) :
      (∑ a ∈ range N, eigenvalue (-((a * x : ℕ) : ℝ) / N) *
        starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N))) = if x = y then (N : ℂ) else 0 := by
    have hterm (a : ℕ) :
        eigenvalue (-((a * x : ℕ) : ℝ) / N) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N)) =
        eigenvalue (((y : ℝ) - (x : ℝ)) / N) ^ a := by
      unfold eigenvalue
      rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      congr 1; push_cast; ring
    simp_rw [hterm]
    by_cases hxy : x = y
    · subst hxy
      simp [eigenvalue]
    · rw [if_neg hxy]
      set ω : ℂ := eigenvalue (((y : ℝ) - (x : ℝ)) / N)
      have hne : ω ≠ 1 := by
        intro h1
        unfold ω eigenvalue at h1
        rw [Complex.exp_eq_one_iff] at h1
        obtain ⟨k, hk⟩ := h1
        have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
          exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero
        have hratio : ((((y : ℝ) - (x : ℝ)) / N : ℝ) : ℂ) = (k : ℂ) := by
          apply mul_right_cancel₀ h2pi
          calc
            ((((y : ℝ) - (x : ℝ)) / N : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
              = Complex.I * ((2 * Real.pi * (((y : ℝ) - (x : ℝ)) / N) : ℝ) : ℂ) := by push_cast; ring
            _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
        have hR : ((y : ℝ) - (x : ℝ)) / N = k := by exact_mod_cast hratio
        have hmul : (y : ℝ) - (x : ℝ) = (k : ℝ) * (N : ℝ) := (div_eq_iff hNR.ne').mp hR
        have hZ : (y : ℤ) - (x : ℤ) = k * (N : ℤ) := by exact_mod_cast hmul
        have hlt1 : -(N : ℤ) < (y : ℤ) - (x : ℤ) := by omega
        have hlt2 : (y : ℤ) - (x : ℤ) < (N : ℤ) := by omega
        have hk0 : k = 0 := by nlinarith
        subst hk0
        omega
      rw [geom_sum_eq hne]
      have hpow : ω ^ N = 1 := by
        unfold ω
        rw [eigenvalue_pow_eq_eigenvalue_mul]
        have harg : (N : ℝ) * (((y : ℝ) - (x : ℝ)) / N) = ((y : ℤ) - (x : ℤ) : ℤ) := by
          push_cast; field_simp [hNR.ne']
        rw [harg, eigenvalue_int]
      rw [hpow, sub_self, zero_div]
  have hC : (∑ a ∈ range N, ((∑ x ∈ range N, f x * eigenvalue (-((a * x : ℕ) : ℝ) / N)) *
      starRingEnd ℂ (∑ y ∈ range N, f y * eigenvalue (-((a * y : ℕ) : ℝ) / N)))) =
      (N : ℂ) * ∑ x ∈ range N, f x * starRingEnd ℂ (f x) := by
    simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner (x : ℕ) (hx : x ∈ range N) :
        (∑ a ∈ range N, ∑ y ∈ range N,
          f x * eigenvalue (-((a * x : ℕ) : ℝ) / N) *
            (starRingEnd ℂ (f y) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N)))) =
        (N : ℂ) * (f x * starRingEnd ℂ (f x)) := by
      rw [Finset.sum_comm]
      have hy (y : ℕ) (hy : y ∈ range N) :
          (∑ a ∈ range N,
            f x * eigenvalue (-((a * x : ℕ) : ℝ) / N) *
              (starRingEnd ℂ (f y) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N)))) =
          if x = y then (N : ℂ) * (f x * starRingEnd ℂ (f x)) else 0 := by
        have hrw : ∀ a ∈ range N,
            f x * eigenvalue (-((a * x : ℕ) : ℝ) / N) *
              (starRingEnd ℂ (f y) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N))) =
            (f x * starRingEnd ℂ (f y)) *
              (eigenvalue (-((a * x : ℕ) : ℝ) / N) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N))) := by
          intro a _; ring
        rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, horth x y (mem_range.mp hx) (mem_range.mp hy)]
        split_ifs with hxy
        · subst hxy; ring
        · ring
      rw [Finset.sum_congr rfl hy]
      simp [mem_range.mp hx]
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  have hre := congrArg Complex.re hC
  have hns : ∀ z : ℂ, (z * starRingEnd ℂ z).re = Complex.normSq z := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum] at hre
  simpa only [hns] using hre

/-- Exact sum of `cos (2π M k / r)` is `0` when `0 < r` and `¬ r ∣ M`. -/
theorem sum_cos_eq_zero (r M : ℕ) (hr : 0 < r) (hndvd : ¬ r ∣ M) :
    ∑ k ∈ range r, Real.cos (2 * Real.pi * M * (k : ℝ) / r) = 0 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set ω : ℂ := eigenvalue ((M : ℝ) / r)
  have hterm (k : ℕ) : Real.cos (2 * Real.pi * M * (k : ℝ) / r) = (ω ^ k).re := by
    rw [eigenvalue_pow_eq_eigenvalue_mul]
    unfold eigenvalue
    rw [show Complex.I * ((2 * Real.pi * ((k : ℝ) * ((M : ℝ) / r)) : ℝ) : ℂ) =
      ((2 * Real.pi * M * (k : ℝ) / r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  have hsum : ∑ k ∈ range r, Real.cos (2 * Real.pi * M * (k : ℝ) / r) = (∑ k ∈ range r, ω ^ k).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  have hne : ω ≠ 1 := by
    intro h1
    unfold ω eigenvalue at h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hratio : (((M : ℝ) / r : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_right_cancel₀ h2pi
      calc
        (((M : ℝ) / r : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
          = Complex.I * ((2 * Real.pi * ((M : ℝ) / r) : ℝ) : ℂ) := by push_cast; ring
        _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
    have hR : (M : ℝ) / r = n := by exact_mod_cast hratio
    have hmul : (M : ℝ) = (n : ℝ) * (r : ℝ) := (div_eq_iff hrR.ne').mp hR
    have hZ : (M : ℤ) = n * (r : ℤ) := by exact_mod_cast hmul
    have hn0 : 0 ≤ n := by nlinarith
    lift n to ℕ using hn0
    have hN : M = r * n := by rw [mul_comm] at hZ; exact_mod_cast hZ
    exact hndvd ⟨n, hN⟩
  have hpow : ω ^ r = 1 := by
    unfold ω
    rw [eigenvalue_pow_eq_eigenvalue_mul]
    have harg : (r : ℝ) * ((M : ℝ) / r) = ((M : ℤ) : ℝ) := by push_cast; field_simp [hrR.ne']
    rw [harg, eigenvalue_int]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div, Complex.zero_re]

/-- Exact average of `cos²(π M k / r)` over `Fin r` when `¬ r ∣ M`. -/
theorem sum_cos_sq_eq (r M : ℕ) (hr : 0 < r) (hndvd : ¬ r ∣ M) :
    ∑ k : Fin r, Real.cos (Real.pi * M * (k.val : ℝ) / r) ^ 2 = (r : ℝ) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => Real.cos (Real.pi * M * (k : ℝ) / r) ^ 2)]
  have he : ∀ k ∈ range r, Real.cos (Real.pi * M * (k : ℝ) / r) ^ 2 =
      1 / 2 + Real.cos (2 * Real.pi * M * (k : ℝ) / r) / 2 := by
    intro k _
    rw [Real.cos_sq, show 2 * (Real.pi * (M : ℝ) * (k : ℝ) / r) = 2 * Real.pi * M * (k : ℝ) / r by ring]
  have hsum2 : ∑ k ∈ range r, Real.cos (2 * Real.pi * M * (k : ℝ) / r) / 2 = 0 := by
    rw [← Finset.sum_div, sum_cos_eq_zero r M hr hndvd, zero_div]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, hsum2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero]
  ring

theorem cos_sq_mod (r m t : ℕ) (hr : 0 < r) :
    Real.cos (Real.pi * m * ((t % r : ℕ) : ℝ) / r) ^ 2 = Real.cos (Real.pi * m * t / r) ^ 2 := by
  have hrR : (r : ℝ) ≠ 0 := by positivity
  have ht : (t : ℝ) = ((t % r : ℕ) : ℝ) + r * ((t / r : ℕ) : ℝ) := by
    have := Nat.mod_add_div t r
    exact_mod_cast this.symm
  have he : Real.pi * m * ((t % r : ℕ) : ℝ) / r =
      Real.pi * m * t / r - ((m * (t / r) : ℕ) : ℝ) * Real.pi := by
    rw [ht]; push_cast; field_simp; ring
  rw [he, Real.cos_sub_nat_mul_pi, mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq,
    one_pow, one_mul]

/-! ### Part 2: Factorization, Parseval, and Far Tail (`≤ 12 / 1000000`) -/

def sineW (z : ℂ) : ℂ := ∑ u ∈ range 1024, sineWeight 10 u * z ^ u

def geomB (B : ℕ) (ω : ℂ) : ℂ := ∑ j ∈ range B, ω ^ j

theorem range_mul_sum {A : Type*} [AddCommMonoid A] (P Q : ℕ) (f : ℕ → A) :
    ∑ x ∈ range (P * Q), f x = ∑ u ∈ range P, ∑ j ∈ range Q, f (u * Q + j) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem sinePhaseAmplitude_factor (M : ℕ) (hM : 10 ≤ M) (β : ℝ) (a : ℕ) :
    let B : ℕ := 2 ^ (M - 10)
    let ω := eigenvalue (β - (a : ℝ) / (2 ^ M : ℕ))
    sinePhaseAmplitude M β a = ((2 ^ M : ℕ) : ℂ)⁻¹ * sineW (ω ^ B) * geomB B ω := by
  dsimp only
  set B : ℕ := 2 ^ (M - 10)
  set ω := eigenvalue (β - (a : ℝ) / (2 ^ M : ℕ))
  have hBpos : 0 < B := pow_pos (by decide) _
  have hN : 2 ^ M = 1024 * B := by
    have : 2 ^ M = 2 ^ 10 * 2 ^ (M - 10) := by rw [← pow_add, Nat.add_sub_cancel' hM]
    simpa [B] using this
  unfold sinePhaseAmplitude sineW geomB
  rw [mul_assoc, Finset.sum_mul_sum]
  congr 1
  change ∑ x ∈ range (2 ^ M), sineWeight 10 (x / B) * ω ^ x = _
  rw [hN, range_mul_sum 1024 B]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro j hj
  have hjlt : j < B := mem_range.mp hj
  have hdiv : (u * B + j) / B = u := by
    rw [Nat.mul_comm u B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hjlt, Nat.add_zero]
  rw [hdiv, pow_add, Nat.mul_comm u B, pow_mul, mul_assoc]

theorem sineWeight_sum_normSq :
    ∑ u ∈ range 1024, Complex.normSq (sineWeight 10 u) = 1024 := by
  have he : ∀ u ∈ range 1024,
      Complex.normSq (sineWeight 10 u) = 1 - Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * (u : ℝ) / (1024 : ℕ)) := by
    intro u _
    rw [sineWeight_normSq, Real.sin_sq_eq_half_sub]
    have harg : 2 * (Real.pi * (u : ℝ) / (2 : ℝ) ^ 10) = 2 * Real.pi * ((1 : ℕ) : ℝ) * (u : ℝ) / (1024 : ℕ) := by
      push_cast; norm_num; ring
    rw [harg]; ring
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, sum_cos_eq_zero 1024 1 (by decide) (by decide)]
  simp

theorem sinePhaseAmplitude_parseval (M : ℕ) (hM : 10 ≤ M) (β : ℝ) :
    ∑ a ∈ range (2 ^ M), Complex.normSq (sinePhaseAmplitude M β a) = 1 := by
  set N := 2 ^ M
  set B := 2 ^ (M - 10)
  have hNpos : 0 < N := pow_pos (by decide) M
  have hBpos : 0 < B := pow_pos (by decide) _
  have hNB : N = 1024 * B := by
    have : 2 ^ M = 2 ^ 10 * 2 ^ (M - 10) := by rw [← pow_add, Nat.add_sub_cancel' hM]
    simpa [N, B] using this
  let f : ℕ → ℂ := fun x => sineWeight 10 (x / B) * eigenvalue (β * x)
  have hamp (a : ℕ) :
      Complex.normSq (sinePhaseAmplitude M β a) =
        ((N : ℝ) ^ 2)⁻¹ * Complex.normSq (∑ x ∈ range N, f x * eigenvalue (-((a * x : ℕ) : ℝ) / N)) := by
    unfold sinePhaseAmplitude
    rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast, ← sq]
    congr 2
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [f]
    rw [mul_assoc, ← eigenvalue_add, eigenvalue_pow_eq_eigenvalue_mul]
    congr 2; dsimp only [N]; push_cast; ring
  simp_rw [hamp]
  rw [← Finset.mul_sum, dft_parseval N hNpos f]
  have hf_norm (x : ℕ) : Complex.normSq (f x) = Complex.normSq (sineWeight 10 (x / B)) := by
    dsimp only [f]
    rw [Complex.normSq_mul, eigenvalue_normSq, mul_one]
  simp_rw [hf_norm]
  have hsum : ∑ x ∈ range N, Complex.normSq (sineWeight 10 (x / B)) = (N : ℝ) := by
    rw [hNB, range_mul_sum 1024 B]
    have hinner (u : ℕ) (_ : u ∈ range 1024) :
        ∑ j ∈ range B, Complex.normSq (sineWeight 10 ((u * B + j) / B)) =
          (B : ℝ) * Complex.normSq (sineWeight 10 u) := by
      have hcongr : ∀ j ∈ range B,
          Complex.normSq (sineWeight 10 ((u * B + j) / B)) = Complex.normSq (sineWeight 10 u) := by
        intro j hj
        rw [Nat.mul_comm u B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt (mem_range.mp hj), Nat.add_zero]
      rw [Finset.sum_congr rfl hcongr]
      simp
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, sineWeight_sum_normSq]
    push_cast; ring
  rw [hsum]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  field_simp [hNR]

theorem one_sub_mul_sineW (z : ℂ) :
    (1 - z) * sineW z =
      (-sineWeight 10 1023 * z ^ 1024) +
      ∑ u ∈ range 1023, (sineWeight 10 (u + 1) - sineWeight 10 u) * z ^ (u + 1) := by
  unfold sineW
  rw [sub_mul, one_mul, Finset.mul_sum]
  have hsplit : ∑ u ∈ range 1024, sineWeight 10 u * z ^ u =
      sineWeight 10 0 * z ^ 0 + ∑ u ∈ range 1023, sineWeight 10 (u + 1) * z ^ (u + 1) :=
    (Finset.sum_range_succ' (fun u => sineWeight 10 u * z ^ u) 1023).trans (add_comm _ _)
  have hsplit2 : ∑ u ∈ range 1024, z * (sineWeight 10 u * z ^ u) =
      (∑ u ∈ range 1023, sineWeight 10 u * z ^ (u + 1)) + sineWeight 10 1023 * z ^ 1024 := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl; intro u _; rw [pow_succ]; ring
    · rw [show (1024 : ℕ) = 1023 + 1 from rfl, pow_succ]; ring
  have hw0 : sineWeight 10 0 = 0 := by simp [sineWeight]
  rw [hsplit, hsplit2, hw0, zero_mul, zero_add]
  have hsub : (∑ u ∈ range 1023, sineWeight 10 (u + 1) * z ^ (u + 1)) -
      (∑ u ∈ range 1023, sineWeight 10 u * z ^ (u + 1)) =
      ∑ u ∈ range 1023, (sineWeight 10 (u + 1) - sineWeight 10 u) * z ^ (u + 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro u _; ring
  rw [← hsub]; ring

theorem sineW_diff_parseval (M : ℕ) (hM : 10 ≤ M) (β : ℝ) :
    let B : ℕ := 2 ^ (M - 10)
    ∑ r ∈ range 1024, Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
      sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) ≤ 2 * Real.pi ^ 2 := by
  dsimp only
  set B : ℕ := 2 ^ (M - 10)
  let d : ℕ → ℂ := fun u =>
    if u = 0 then -sineWeight 10 1023 * eigenvalue ((1024 * B : ℕ) * β)
    else sineWeight 10 u - sineWeight 10 (u - 1)
  let g : ℕ → ℂ := fun u => d u * eigenvalue ((B : ℝ) * β * u)
  have hmatch (r : ℕ) :
      Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
        sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) =
      Complex.normSq (∑ u ∈ range 1024, g u * eigenvalue (-((r * u : ℕ) : ℝ) / 1024)) := by
    set z := eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024)
    have hneg : (z - 1) * sineW z = -((1 - z) * sineW z) := by ring
    rw [hneg, Complex.normSq_neg, one_sub_mul_sineW]
    congr 1
    have hz1024 : z ^ 1024 = eigenvalue ((1024 * B : ℕ) * β) := by
      unfold z
      rw [eigenvalue_pow_eq_eigenvalue_mul]
      have harg : ((1024 : ℕ) : ℝ) * ((B : ℝ) * β - (r : ℝ) / 1024) = ((1024 * B : ℕ) : ℝ) * β - (r : ℤ) := by
        push_cast; ring
      rw [harg, eigenvalue_sub_int]
    have hzu (u : ℕ) : g u * eigenvalue (-((r * u : ℕ) : ℝ) / 1024) = d u * z ^ u := by
      dsimp only [g, z]
      rw [mul_assoc, ← eigenvalue_add, eigenvalue_pow_eq_eigenvalue_mul]
      congr 2; push_cast; ring
    simp_rw [hzu]
    rw [Finset.sum_range_succ' _ 1023]
    simp only [d, ↓reduceIte, pow_zero, mul_one, hz1024, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    ring
  simp_rw [hmatch]
  have hdft := dft_parseval 1024 (by decide) g
  simp only [Nat.cast_ofNat] at hdft
  rw [hdft]
  have hg (u : ℕ) (_ : u ∈ range 1024) : Complex.normSq (g u) ≤ 2 * (Real.pi / 1024) ^ 2 := by
    dsimp only [g]
    rw [Complex.normSq_mul, eigenvalue_normSq, mul_one]
    by_cases hu : u = 0
    · simp only [d, hu, ↓reduceIte, Complex.normSq_mul, Complex.normSq_neg, eigenvalue_normSq,
        mul_one, sineWeight_normSq]
      have hsin : Real.sin (Real.pi * (1023 : ℝ) / (2 : ℝ) ^ 10) = Real.sin (Real.pi / 1024) := by
        rw [show Real.pi * (1023 : ℝ) / (2 : ℝ) ^ 10 = Real.pi - Real.pi / 1024 by norm_num; ring,
          Real.sin_pi_sub]
      rw [Nat.cast_ofNat, hsin]
      have hpi1024 : 0 < Real.pi / 1024 := div_pos Real.pi_pos (by norm_num)
      have hle : Real.sin (Real.pi / 1024) ≤ Real.pi / 1024 := Real.sin_le hpi1024.le
      have h0 : 0 ≤ Real.sin (Real.pi / 1024) := Real.sin_nonneg_of_nonneg_of_le_pi hpi1024.le
        (by linarith [Real.pi_pos])
      nlinarith
    · simp only [d, hu, ↓reduceIte]
      rw [sineWeight_eq_sin, sineWeight_eq_sin, ← mul_sub, Complex.normSq_mul, Complex.normSq_mul,
        Complex.normSq_ofReal, Complex.normSq_I, mul_one, Real.mul_self_sqrt (by norm_num),
        ← Complex.ofReal_sub, Complex.normSq_ofReal, ← sq]
      have hlip := Real.abs_sin_sub_sin_le (Real.pi * (u : ℝ) / (2 : ℝ) ^ 10)
        (Real.pi * ((u - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 10)
      have h1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu
      have hdiff : Real.pi * (u : ℝ) / (2 : ℝ) ^ 10 - Real.pi * ((u - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 10 =
          Real.pi / 1024 := by
        rw [Nat.cast_sub h1]; push_cast; norm_num; ring
      have hpi1024 : 0 < Real.pi / 1024 := div_pos Real.pi_pos (by norm_num)
      rw [hdiff, abs_of_pos hpi1024] at hlip
      have hsq : (Real.sin (Real.pi * (u : ℝ) / (2 : ℝ) ^ 10) -
          Real.sin (Real.pi * ((u - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 10)) ^ 2 ≤ (Real.pi / 1024) ^ 2 := by
        calc
          _ = |Real.sin (Real.pi * (u : ℝ) / (2 : ℝ) ^ 10) -
              Real.sin (Real.pi * ((u - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 10)| ^ 2 := (sq_abs _).symm
          _ ≤ (Real.pi / 1024) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlip 2
      linarith
  have hsum := Finset.sum_le_sum hg
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hcalc : (1024 : ℝ) * ((1024 : ℝ) * (2 * (Real.pi / 1024) ^ 2)) = 2 * Real.pi ^ 2 := by ring
  nlinarith

theorem sum_inv_sq_half_ge (S : Finset ℕ) (φ : ℕ → ℝ)
    (hφ : ∀ q ∈ S, (1 / 2 : ℝ) ≤ φ q)
    (hsep : ∀ q1 ∈ S, ∀ q2 ∈ S, |φ q1 - φ q2| < 1 → q1 = q2) :
    ∑ q ∈ S, 1 / (φ q) ^ 2 ≤ 5 := by
  let S0 := S.filter (fun q => φ q < 3 / 2)
  let S1 := S.filter (fun q => 3 / 2 ≤ φ q)
  have hS1 : S.filter (fun q => ¬ φ q < 3 / 2) = S1 := by
    ext q; simp [S1, not_lt]
  have hpart : ∑ q ∈ S, 1 / (φ q) ^ 2 = (∑ q ∈ S0, 1 / (φ q) ^ 2) + ∑ q ∈ S1, 1 / (φ q) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun q => φ q < 3 / 2), hS1]
  have h0 : ∑ q ∈ S0, 1 / (φ q) ^ 2 ≤ 4 := by
    by_cases he : S0 = ∅
    · simp [he]
    · obtain ⟨q0, hq0⟩ := Finset.nonempty_iff_ne_empty.mpr he
      have hsub : S0 ⊆ {q0} := by
        intro q hq
        rw [Finset.mem_singleton]
        have h1 := Finset.mem_filter.mp hq
        have h2 := Finset.mem_filter.mp hq0
        have hp1 := hφ q h1.1
        have hp2 := hφ q0 h2.1
        exact hsep q h1.1 q0 h2.1 (abs_lt.mpr ⟨by linarith [h1.2, h2.2], by linarith [h1.2, h2.2]⟩)
      have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q => 1 / (φ q) ^ 2) hsub (fun _ _ _ => by positivity)
      rw [Finset.sum_singleton] at hle
      have hp0 := hφ q0 (Finset.mem_filter.mp hq0).1
      have h4 : 1 / (φ q0) ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
  have h1 : ∑ q ∈ S1, 1 / (φ q) ^ 2 ≤ 1 := by
    have hi := sum_inv_sq_le_first S1 φ (3 / 2) (by norm_num)
      (fun q hq => (Finset.mem_filter.mp hq).2)
      (fun q1 hq1 q2 hq2 => hsep q1 (Finset.mem_filter.mp hq1).1 q2 (Finset.mem_filter.mp hq2).1)
    unfold tailBound at hi
    linarith
  linarith

theorem phiR_add_phiL (N : ℕ) (c : ℝ) (a : ℕ) (hne : (a : ℝ) ≠ c) :
    phiR N c a + phiL N c a = N := by
  unfold phiR phiL
  by_cases h : c ≤ (a : ℝ)
  · have hlt : ¬ (a : ℝ) ≤ c := fun h2 => hne (le_antisymm h2 h)
    rw [if_pos h, if_neg hlt]; ring
  · have hle : (a : ℝ) ≤ c := le_of_not_ge h
    rw [if_neg h, if_pos hle]; ring

theorem abs_sin_phiR_half (N : ℕ) (hN : 0 < N) (β : ℝ) (a : ℕ)
    (hd : 0 < phiR N ((N : ℝ) * β) a) (hle : phiR N ((N : ℝ) * β) a ≤ (N : ℝ) / 2) :
    |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (phiR N ((N : ℝ) * β) a / N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 ≤ Real.sin (Real.pi * (phiR N ((N : ℝ) * β) a / N)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    have : phiR N ((N : ℝ) * β) a / N ≤ 1 / 2 := (div_le_iff₀ hNR).mpr (by linarith)
    nlinarith [Real.pi_pos]
  by_cases hca : (N : ℝ) * β ≤ a
  · have he : Real.pi * (β - (a : ℝ) / N) = -(Real.pi * (phiR N ((N : ℝ) * β) a / N)) := by
      simp only [phiR, if_pos hca]; field_simp [hNR.ne']; ring
    rw [he, Real.sin_neg, abs_neg, abs_of_nonneg hpos]
  · have he : Real.pi * (β - (a : ℝ) / N) = Real.pi - Real.pi * (phiR N ((N : ℝ) * β) a / N) := by
      simp only [phiR, if_neg hca]; field_simp [hNR.ne']; ring
    rw [he, Real.sin_pi_sub, abs_of_nonneg hpos]

theorem abs_sin_phiL_half (N : ℕ) (hN : 0 < N) (β : ℝ) (a : ℕ)
    (hd : 0 < phiL N ((N : ℝ) * β) a) (hle : phiL N ((N : ℝ) * β) a ≤ (N : ℝ) / 2) :
    |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (phiL N ((N : ℝ) * β) a / N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 ≤ Real.sin (Real.pi * (phiL N ((N : ℝ) * β) a / N)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    have : phiL N ((N : ℝ) * β) a / N ≤ 1 / 2 := (div_le_iff₀ hNR).mpr (by linarith)
    nlinarith [Real.pi_pos]
  by_cases hca : (a : ℝ) ≤ (N : ℝ) * β
  · have he : Real.pi * (β - (a : ℝ) / N) = Real.pi * (phiL N ((N : ℝ) * β) a / N) := by
      simp only [phiL, if_pos hca]; field_simp [hNR.ne']
    rw [he, abs_of_nonneg hpos]
  · have he : Real.pi * (β - (a : ℝ) / N) = Real.pi * (phiL N ((N : ℝ) * β) a / N) - Real.pi := by
      simp only [phiL, if_neg hca]; field_simp [hNR.ne']; ring
    rw [he, Real.sin_sub_pi, abs_neg, abs_of_nonneg hpos]

theorem phiR_sep_1024 (N : ℕ) (B : ℕ) (hN : N = 1024 * B) (c : ℝ) (r : ℕ)
    (q1 q2 : ℕ) (hq1 : q1 < B) (hq2 : q2 < B)
    (h : |phiR N c (1024 * q1 + r) / 1024 - phiR N c (1024 * q2 + r) / 1024| < 1) :
    q1 = q2 := by
  have h1024 : |phiR N c (1024 * q1 + r) - phiR N c (1024 * q2 + r)| < 1024 := by
    have := mul_lt_mul_of_pos_right h (by norm_num : (0 : ℝ) < 1024)
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1024), ← abs_mul] at this
    simpa [sub_mul, div_mul_cancel₀] using this
  unfold phiR at h1024
  split_ifs at h1024 <;>
    (have hNR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hN
     have hZ : |(q1 : ℤ) - (q2 : ℤ)| < 1 ∨ |(q1 : ℤ) - (q2 : ℤ) + (B : ℤ)| < 1 ∨
         |(q1 : ℤ) - (q2 : ℤ) - (B : ℤ)| < 1 := by
       try rw [hNR] at h1024
       first
       | left; have : |(q1 : ℝ) - (q2 : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
       | right; left; have : |(q1 : ℝ) - (q2 : ℝ) + (B : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
       | right; right; have : |(q1 : ℝ) - (q2 : ℝ) - (B : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
     rcases hZ with hZ | hZ | hZ <;> rw [abs_lt] at hZ <;> omega)

theorem phiL_sep_1024 (N : ℕ) (B : ℕ) (hN : N = 1024 * B) (c : ℝ) (r : ℕ)
    (q1 q2 : ℕ) (hq1 : q1 < B) (hq2 : q2 < B)
    (h : |phiL N c (1024 * q1 + r) / 1024 - phiL N c (1024 * q2 + r) / 1024| < 1) :
    q1 = q2 := by
  have h1024 : |phiL N c (1024 * q1 + r) - phiL N c (1024 * q2 + r)| < 1024 := by
    have := mul_lt_mul_of_pos_right h (by norm_num : (0 : ℝ) < 1024)
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1024), ← abs_mul] at this
    simpa [sub_mul, div_mul_cancel₀] using this
  unfold phiL at h1024
  split_ifs at h1024 <;>
    (have hNR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hN
     have hZ : |(q1 : ℤ) - (q2 : ℤ)| < 1 ∨ |(q1 : ℤ) - (q2 : ℤ) + (B : ℤ)| < 1 ∨
         |(q1 : ℤ) - (q2 : ℤ) - (B : ℤ)| < 1 := by
       try rw [hNR] at h1024
       first
       | left; have : |(q1 : ℝ) - (q2 : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
       | right; left; have : |(q1 : ℝ) - (q2 : ℝ) + (B : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
       | right; right; have : |(q1 : ℝ) - (q2 : ℝ) - (B : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
     rcases hZ with hZ | hZ | hZ <;> rw [abs_lt] at hZ <;> omega)

/-- Far-tail bound: total mass outside circular radius `512` is at most `12 / 1000000`. -/
theorem sinePhaseAmplitude_far_tail (M : ℕ) (hM : 11 ≤ M) (β : ℝ) :
    (∑ a ∈ range (2 ^ M),
      if 512 < phiR (2 ^ M) ((2 ^ M : ℕ) * β) a ∧ 512 < phiL (2 ^ M) ((2 ^ M : ℕ) * β) a
      then Complex.normSq (sinePhaseAmplitude M β a) else 0) ≤ 12 / 1000000 := by
  set N := 2 ^ M
  set B := 2 ^ (M - 10)
  have hM10 : 10 ≤ M := by omega
  have hNpos : 0 < N := pow_pos (by decide) M
  have hBpos : 0 < B := pow_pos (by decide) _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hNB : N = 1024 * B := by
    have : 2 ^ M = 2 ^ 10 * 2 ^ (M - 10) := by rw [← pow_add, Nat.add_sub_cancel' hM10]
    simpa [N, B] using this
  have hNBR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hNB
  have hreidx :
      (∑ a ∈ range N,
        if 512 < phiR N ((N : ℝ) * β) a ∧ 512 < phiL N ((N : ℝ) * β) a
        then Complex.normSq (sinePhaseAmplitude M β a) else 0) =
      ∑ r ∈ range 1024, ∑ q ∈ range B,
        if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧ 512 < phiL N ((N : ℝ) * β) (q * 1024 + r)
        then Complex.normSq (sinePhaseAmplitude M β (q * 1024 + r)) else 0 := by
    rw [Finset.sum_comm, hNB, Nat.mul_comm 1024 B, range_mul_sum B 1024]
  rw [hreidx]
  have hper_r (r : ℕ) (hr : r ∈ range 1024) :
      (∑ q ∈ range B,
        if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧ 512 < phiL N ((N : ℝ) * β) (q * 1024 + r)
        then Complex.normSq (sinePhaseAmplitude M β (q * 1024 + r)) else 0) ≤
      (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 *
        Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
          sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) := by
    set zr := eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024)
    set num := Complex.normSq ((zr - 1) * sineW zr)
    have hnum0 : 0 ≤ num := Complex.normSq_nonneg _
    let Rq := (range B).filter (fun q =>
      512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧ phiR N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2)
    let Lq := (range B).filter (fun q =>
      512 < phiL N ((N : ℝ) * β) (q * 1024 + r) ∧ phiL N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2)
    have hpt (q : ℕ) (hq : q ∈ range B) (hfar : 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧
        512 < phiL N ((N : ℝ) * β) (q * 1024 + r)) :
        Complex.normSq (sinePhaseAmplitude M β (q * 1024 + r)) ≤
          num / (16 * (1024 : ℝ) ^ 2) *
            ((if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧
                 phiR N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2
              then 1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 else 0) +
             (if 512 < phiL N ((N : ℝ) * β) (q * 1024 + r) ∧
                 phiL N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2
              then 1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 else 0)) := by
      set a := q * 1024 + r
      set ω := eigenvalue (β - (a : ℝ) / N)
      have hωB : ω ^ B = zr := by
        unfold ω zr
        rw [eigenvalue_pow_eq_eigenvalue_mul]
        have harg : (B : ℝ) * (β - (a : ℝ) / N) = ((B : ℝ) * β - (r : ℝ) / 1024) - (q : ℤ) := by
          dsimp only [a]; rw [hNBR]; push_cast; field_simp [hBR.ne']; ring
        rw [harg, eigenvalue_sub_int]
      have hne_c : (a : ℝ) ≠ (N : ℝ) * β := by
        intro heq
        have h0 : phiR N ((N : ℝ) * β) a = 0 := by simp [phiR, heq]
        linarith [hfar.1]
      have hsum_phi := phiR_add_phiL N ((N : ℝ) * β) a hne_c
      have hbd (d : ℝ) (hd : 512 < d) (hd2 : d ≤ (N : ℝ) / 2)
          (habs : |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (d / N))) :
          Complex.normSq (sinePhaseAmplitude M β a) ≤
            num / (16 * (1024 : ℝ) ^ 2) * (1 / (d / 1024) ^ 2) := by
        have hsin_ge : 2 * (d / N) ≤ Real.sin (Real.pi * (d / N)) :=
          sin_jordan (d / N) (by positivity) ((div_le_iff₀ hNR).mpr (by linarith))
        have hsin_pos : 0 < |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by
          rw [habs]; linarith [show (0 : ℝ) < 2 * (d / N) by positivity]
        have hω1 : ω ≠ 1 := by
          intro h1
          have h0 := normSq_eigenvalue_sub_one (β - (a : ℝ) / N)
          change Complex.normSq (ω - 1) = _ at h0
          rw [h1, sub_self, Complex.normSq_zero] at h0
          have hsp : 0 < 4 * Real.sin (Real.pi * (β - (a : ℝ) / N)) ^ 2 := by
            have := sq_pos_of_pos hsin_pos; rw [sq_abs] at this; linarith
          linarith
        have hfac := sinePhaseAmplitude_factor M hM10 β a
        change sinePhaseAmplitude M β a = ((N : ℂ)⁻¹) * sineW (ω ^ B) * geomB B ω at hfac
        rw [hfac, hωB, geomB, geom_sum_eq hω1, hωB]
        have heq : (N : ℂ)⁻¹ * sineW zr * ((zr - 1) / (ω - 1)) =
            (N : ℂ)⁻¹ * ((zr - 1) * sineW zr) / (ω - 1) := by ring
        rw [heq, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast,
          normSq_eigenvalue_sub_one]
        have hden_ge : 16 * (d / N) ^ 2 ≤ 4 * Real.sin (Real.pi * (β - (a : ℝ) / N)) ^ 2 := by
          rw [← sq_abs (Real.sin _), habs]
          have hsq : (2 * (d / N)) ^ 2 ≤ Real.sin (Real.pi * (d / N)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hsin_ge 2
          nlinarith
        have h1 : ((N : ℝ) * N)⁻¹ * num / (4 * Real.sin (Real.pi * (β - (a : ℝ) / N)) ^ 2) ≤
            ((N : ℝ) * N)⁻¹ * num / (16 * (d / N) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
        refine h1.trans_eq ?_
        have hd0 : d ≠ 0 := by linarith
        field_simp [hNR.ne', hd0]
      by_cases hR : phiR N ((N : ℝ) * β) a ≤ (N : ℝ) / 2
      · have h1 := hbd _ hfar.1 hR (abs_sin_phiR_half N hNpos β a (by linarith [hfar.1]) hR)
        rw [if_pos ⟨hfar.1, hR⟩]
        have h2 : 0 ≤ (if 512 < phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a ≤ (N : ℝ) / 2
            then 1 / (phiL N ((N : ℝ) * β) a / 1024) ^ 2 else 0) := by split_ifs <;> positivity
        have hmul : 0 ≤ num / (16 * (1024 : ℝ) ^ 2) := by positivity
        nlinarith
      · have hL : phiL N ((N : ℝ) * β) a ≤ (N : ℝ) / 2 := by linarith
        have h1 := hbd _ hfar.2 hL (abs_sin_phiL_half N hNpos β a (by linarith [hfar.2]) hL)
        rw [if_neg (fun h => hR h.2), if_pos ⟨hfar.2, hL⟩]
        have hmul : 0 ≤ num / (16 * (1024 : ℝ) ^ 2) := by positivity
        nlinarith
    have hsum1 :
        (∑ q ∈ range B,
          if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧ 512 < phiL N ((N : ℝ) * β) (q * 1024 + r)
          then Complex.normSq (sinePhaseAmplitude M β (q * 1024 + r)) else 0) ≤
        num / (16 * (1024 : ℝ) ^ 2) *
          ((∑ q ∈ Rq, 1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2) +
           (∑ q ∈ Lq, 1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      have hRq : ∑ q ∈ Rq, num / (16 * (1024 : ℝ) ^ 2) *
            (1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2) =
          ∑ q ∈ range B, num / (16 * (1024 : ℝ) ^ 2) *
            (if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧
                phiR N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2
             then 1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro q _; split_ifs <;> ring
      have hLq : ∑ q ∈ Lq, num / (16 * (1024 : ℝ) ^ 2) *
            (1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2) =
          ∑ q ∈ range B, num / (16 * (1024 : ℝ) ^ 2) *
            (if 512 < phiL N ((N : ℝ) * β) (q * 1024 + r) ∧
                phiL N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2
             then 1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro q _; split_ifs <;> ring
      rw [hRq, hLq, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro q hq
      rw [← mul_add]
      by_cases hfar : 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧
          512 < phiL N ((N : ℝ) * β) (q * 1024 + r)
      · rw [if_pos hfar]
        exact hpt q hq hfar
      · rw [if_neg hfar]
        apply mul_nonneg (by positivity)
        apply add_nonneg <;> (split_ifs <;> positivity)
    have hR5 : ∑ q ∈ Rq, 1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 ≤ 5 := by
      apply sum_inv_sq_half_ge Rq (fun q => phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024)
      · intro q hq; have := (Finset.mem_filter.mp hq).2.1; linarith
      · intro q1 hq1 q2 hq2 hlt
        rw [Nat.mul_comm q1 1024, Nat.mul_comm q2 1024] at hlt
        exact phiR_sep_1024 N B hNB ((N : ℝ) * β) r q1 q2
          (mem_range.mp (Finset.mem_filter.mp hq1).1) (mem_range.mp (Finset.mem_filter.mp hq2).1) hlt
    have hL5 : ∑ q ∈ Lq, 1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 ≤ 5 := by
      apply sum_inv_sq_half_ge Lq (fun q => phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024)
      · intro q hq; have := (Finset.mem_filter.mp hq).2.1; linarith
      · intro q1 hq1 q2 hq2 hlt
        rw [Nat.mul_comm q1 1024, Nat.mul_comm q2 1024] at hlt
        exact phiL_sep_1024 N B hNB ((N : ℝ) * β) r q1 q2
          (mem_range.mp (Finset.mem_filter.mp hq1).1) (mem_range.mp (Finset.mem_filter.mp hq2).1) hlt
    calc
      _ ≤ num / (16 * (1024 : ℝ) ^ 2) * (5 + 5) := hsum1.trans (mul_le_mul_of_nonneg_left (add_le_add hR5 hL5) (by positivity))
      _ = (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 * num := by ring
  calc
    _ ≤ ∑ r ∈ range 1024, (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 *
          Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
            sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) := Finset.sum_le_sum hper_r
    _ = (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 * ∑ r ∈ range 1024,
          Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
            sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) := by rw [← Finset.mul_sum]
    _ ≤ (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 * (2 * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left (sineW_diff_parseval M hM10 β) (by positivity)
    _ ≤ 12 / 1000000 := by
          have hpi : Real.pi < 3141593 / 1000000 := by
            have := Real.pi_lt_d6; norm_num at this ⊢; linarith
          have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
          nlinarith

/-! ### Part 3: Closed form & small/medium pointwise bounds -/

theorem sineW_closed_form (z : ℂ) (θ : ℝ) (hz : z = eigenvalue θ)
    (hp : Real.sin (Real.pi * (θ + 1 / 2048)) ≠ 0)
    (hm : Real.sin (Real.pi * (θ - 1 / 2048)) ≠ 0) :
    Complex.normSq (sineW z) =
      Real.cos (Real.pi * (1024 * θ)) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 /
        (2 * Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2) := by
  set ζ : ℂ := eigenvalue (1 / 2048)
  set ζm : ℂ := eigenvalue (-(1 / 2048))
  have hζp : ζ * z = eigenvalue (θ + 1 / 2048) := by
    rw [hz, ← eigenvalue_add]; congr 1; ring
  have hζm : ζm * z = eigenvalue (θ - 1 / 2048) := by
    rw [hz, ← eigenvalue_add]; congr 1; ring
  have hp_ne : ζ * z ≠ 1 := by
    intro h1
    have h0 := normSq_eigenvalue_sub_one (θ + 1 / 2048)
    rw [← hζp, h1, sub_self, Complex.normSq_zero] at h0
    have : 0 < 4 * Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 := by
      have := sq_pos_of_ne_zero hp; linarith
    linarith
  have hm_ne : ζm * z ≠ 1 := by
    intro h1
    have h0 := normSq_eigenvalue_sub_one (θ - 1 / 2048)
    rw [← hζm, h1, sub_self, Complex.normSq_zero] at h0
    have : 0 < 4 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2 := by
      have := sq_pos_of_ne_zero hm; linarith
    linarith
  have hζ1024 : ζ ^ 1024 = -1 := by
    unfold ζ
    rw [eigenvalue_pow_eq_eigenvalue_mul]
    unfold eigenvalue
    have : Complex.I * ((2 * Real.pi * (((1024 : ℕ) : ℝ) * (1 / 2048)) : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  have hζm1024 : ζm ^ 1024 = -1 := by
    unfold ζm
    rw [eigenvalue_pow_eq_eigenvalue_mul]
    unfold eigenvalue
    have : Complex.I * ((2 * Real.pi * (((1024 : ℕ) : ℝ) * (-(1 / 2048))) : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hW : sineW z = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      ((∑ u ∈ range 1024, (ζ * z) ^ u) - ∑ u ∈ range 1024, (ζm * z) ^ u) := by
    unfold sineW
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    unfold sineWeight ζ ζm
    rw [mul_pow, mul_pow, eigenvalue_pow_eq_eigenvalue_mul, eigenvalue_pow_eq_eigenvalue_mul]
    unfold eigenvalue
    have ha : Complex.I * ((2 * Real.pi * ((u : ℝ) * (1 / 2048)) : ℝ) : ℂ) =
        Complex.I * ((Real.pi * (u : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ) := by push_cast; norm_num; ring
    have hb : Complex.I * ((2 * Real.pi * ((u : ℝ) * (-(1 / 2048))) : ℝ) : ℂ) =
        -(Complex.I * ((Real.pi * (u : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ)) := by push_cast; norm_num; ring
    rw [ha, hb]; ring
  rw [hW, geom_sum_eq hp_ne, geom_sum_eq hm_ne, mul_pow, mul_pow, hζ1024, hζm1024]
  have hcomb : ((-1) * z ^ 1024 - 1) / (ζ * z - 1) - ((-1) * z ^ 1024 - 1) / (ζm * z - 1) =
      (z ^ 1024 + 1) * ((ζ - ζm) * z) / ((ζ * z - 1) * (ζm * z - 1)) := by
    have h1 : ζ * z - 1 ≠ 0 := sub_ne_zero.mpr hp_ne
    have h2 : ζm * z - 1 ≠ 0 := sub_ne_zero.mpr hm_ne
    rw [div_sub_div _ _ h1 h2]; congr 1; ring
  rw [hcomb, Complex.normSq_mul, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, ← sq, inv_pow, Real.sq_sqrt (by norm_num)]
  have hz1024 : z ^ 1024 = eigenvalue (1024 * θ) := by
    rw [hz, eigenvalue_pow_eq_eigenvalue_mul]; push_cast; rfl
  have hdiff : Complex.normSq (ζ - ζm) = 4 * Real.sin (Real.pi / 1024) ^ 2 := by
    have hmul : ζ - ζm = ζm * (eigenvalue (1 / 1024) - 1) := by
      unfold ζ ζm
      rw [mul_sub, mul_one, ← eigenvalue_add]
      congr 2; ring
    rw [hmul, Complex.normSq_mul, eigenvalue_normSq, one_mul, normSq_eigenvalue_sub_one,
      show Real.pi * (1 / 1024 : ℝ) = Real.pi / 1024 by ring]
  rw [hz1024, hζp, hζm, hz, eigenvalue_normSq, mul_one, normSq_eigenvalue_add_one, hdiff,
    normSq_eigenvalue_sub_one, normSq_eigenvalue_sub_one]
  ring

/-- Exact closed form of `Complex.normSq (sinePhaseAmplitude M β a)` in terms of `φ = phiR` or `phiL`. -/
theorem sinePhaseAmplitude_closed_form (M : ℕ) (hM : 204 ≤ M) (β : ℝ) (a : ℕ) (φ : ℝ)
    (hlo : 3 / 2 ≤ φ) (hhi : φ ≤ 512)
    (hφ : φ = phiR (2 ^ M) ((2 ^ M : ℕ) * β) a ∨ φ = phiL (2 ^ M) ((2 ^ M : ℕ) * β) a) :
    let N := (2 ^ M : ℕ)
    Complex.normSq (sinePhaseAmplitude M β a) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 *
        Real.sin (Real.pi * φ / 1024) ^ 2 /
      (2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2) := by
  dsimp only
  set N := (2 ^ M : ℕ)
  set B := 2 ^ (M - 10)
  have hM10 : 10 ≤ M := by omega
  have hNpos : 0 < N := pow_pos (by decide) M
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNB : N = 1024 * B := by
    have : 2 ^ M = 2 ^ 10 * 2 ^ (M - 10) := by rw [← pow_add, Nat.add_sub_cancel' hM10]
    simpa [N, B] using this
  have hNBR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hNB
  have hNbig : (1024 : ℝ) ≤ N := by
    have : 1024 ≤ N := by rw [hNB]; exact Nat.le_mul_of_pos_right 1024 (pow_pos (by decide) _)
    exact_mod_cast this
  set θ := (B : ℝ) * (β - (a : ℝ) / N)
  set ω := eigenvalue (β - (a : ℝ) / N)
  have hωB : ω ^ B = eigenvalue θ := by
    unfold ω θ; rw [eigenvalue_pow_eq_eigenvalue_mul]
  -- Relate `1024 * θ = N * β - a` to `± φ` modulo `N` (hence also modulo `1024`)
  have hrel : ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧ ∃ k : ℤ,
      (N : ℝ) * β - (a : ℝ) = sgn * φ + (k : ℝ) * (N : ℝ) := by
    rcases hφ with rfl | rfl
    · unfold phiR; split_ifs
      · exact ⟨-1, Or.inr rfl, 0, by ring⟩
      · exact ⟨-1, Or.inr rfl, 1, by ring⟩
    · unfold phiL; split_ifs
      · exact ⟨1, Or.inl rfl, 0, by ring⟩
      · exact ⟨1, Or.inl rfl, -1, by ring⟩
  obtain ⟨sgn, hsgn, k, hrel⟩ := hrel
  have hθ : θ = (sgn * φ) / 1024 + (k * B : ℤ) := by
    unfold θ
    have hB0 : (B : ℝ) ≠ 0 := by positivity
    have : (N : ℝ) * (β - (a : ℝ) / N) = (N : ℝ) * β - (a : ℝ) := by field_simp [hNR.ne']
    have : (1024 : ℝ) * ((B : ℝ) * (β - (a : ℝ) / N)) = sgn * φ + (k : ℝ) * (1024 * (B : ℝ)) := by
      rw [← mul_assoc, ← hNBR, this, hrel, hNBR]
    push_cast; linarith
  have hneg1_sq : ∀ m : ℤ, ((-1 : ℝ) ^ m) ^ 2 = 1 := fun m => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num
  have hsin_sq_shift : ∀ (u : ℝ) (m : ℤ), Real.sin (u + (m : ℝ) * Real.pi) ^ 2 = Real.sin u ^ 2 := by
    intro u m
    rw [Real.sin_add_int_mul_pi, mul_pow, hneg1_sq, one_mul]
  have hcos_sq_shift : ∀ (u : ℝ) (m : ℤ), Real.cos (u + (m : ℝ) * Real.pi) ^ 2 = Real.cos u ^ 2 := by
    intro u m
    rw [Real.cos_add_int_mul_pi, mul_pow, hneg1_sq, one_mul]
  have hsinN : Real.sin (Real.pi * (β - (a : ℝ) / N)) ^ 2 = Real.sin (Real.pi * φ / N) ^ 2 := by
    have harg : Real.pi * (β - (a : ℝ) / N) = sgn * (Real.pi * φ / N) + (k : ℝ) * Real.pi := by
      have h1 : (N : ℝ) * (β - (a : ℝ) / N) = sgn * φ + (k : ℝ) * (N : ℝ) := by
        rw [← hrel]; field_simp [hNR.ne']
      have h2 : β - (a : ℝ) / N = sgn * φ / N + (k : ℝ) := by
        field_simp [hNR.ne'] at h1 ⊢; linarith
      rw [h2]; ring
    rw [harg, hsin_sq_shift]
    rcases hsgn with rfl | rfl <;> simp
  have hsinθ : Real.sin (Real.pi * θ) ^ 2 = Real.sin (Real.pi * φ / 1024) ^ 2 := by
    rw [hθ, show Real.pi * (sgn * φ / 1024 + ((k * B : ℤ) : ℝ)) =
      sgn * (Real.pi * φ / 1024) + ((k * B : ℤ) : ℝ) * Real.pi by ring, hsin_sq_shift]
    rcases hsgn with rfl | rfl <;> simp
  have hcos1024 : Real.cos (Real.pi * (1024 * θ)) ^ 2 = Real.cos (Real.pi * (N : ℝ) * β) ^ 2 := by
    have harg : Real.pi * (1024 * θ) = Real.pi * (N : ℝ) * β + (((-(a : ℤ) : ℤ) : ℝ)) * Real.pi := by
      unfold θ
      have : (1024 : ℝ) * ((B : ℝ) * (β - (a : ℝ) / N)) = (N : ℝ) * β - (a : ℝ) := by
        rw [← mul_assoc, ← hNBR]; field_simp [hNR.ne']
      rw [this]; rw [Int.cast_neg, Int.cast_natCast]; ring
    rw [harg, hcos_sq_shift]
  have hsinPM :
      Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2 =
      Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 := by
    rw [hθ]
    rw [show Real.pi * (sgn * φ / 1024 + ((k * B : ℤ) : ℝ) + 1 / 2048) =
        Real.pi * (sgn * φ + 1 / 2) / 1024 + ((k * B : ℤ) : ℝ) * Real.pi by ring, hsin_sq_shift]
    rw [show Real.pi * (sgn * φ / 1024 + ((k * B : ℤ) : ℝ) - 1 / 2048) =
        Real.pi * (sgn * φ - 1 / 2) / 1024 + ((k * B : ℤ) : ℝ) * Real.pi by ring, hsin_sq_shift]
    rcases hsgn with rfl | rfl
    · simp
    · have ha : Real.pi * (-1 * φ + 1 / 2) / 1024 = -(Real.pi * (φ - 1 / 2) / 1024) := by ring
      have hb : Real.pi * (-1 * φ - 1 / 2) / 1024 = -(Real.pi * (φ + 1 / 2) / 1024) := by ring
      rw [ha, hb, Real.sin_neg, Real.sin_neg, neg_sq, neg_sq, mul_comm]
  have hpos_p : 0 < Real.sin (Real.pi * (φ + 1 / 2) / 1024) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hpos_m : 0 < Real.sin (Real.pi * (φ - 1 / 2) / 1024) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hpos_N : 0 < Real.sin (Real.pi * φ / N) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
      have h1 : φ / N ≤ 1 / 2 := (div_le_iff₀ hNR).mpr (by linarith)
      have h2 : Real.pi * φ / N = Real.pi * (φ / N) := by ring
      nlinarith [Real.pi_pos])
  have hpm_ne : Real.sin (Real.pi * (θ + 1 / 2048)) ≠ 0 ∧ Real.sin (Real.pi * (θ - 1 / 2048)) ≠ 0 := by
    have hprod_pos : 0 < Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2 := by
      rw [hsinPM]; positivity
    constructor
    · intro hz; rw [hz, zero_pow (by decide), zero_mul] at hprod_pos; exact lt_irrefl 0 hprod_pos
    · intro hz; rw [hz, zero_pow (by decide), mul_zero] at hprod_pos; exact lt_irrefl 0 hprod_pos
  have hω_ne : ω ≠ 1 := by
    intro h1
    have h0 := normSq_eigenvalue_sub_one (β - (a : ℝ) / N)
    change Complex.normSq (ω - 1) = _ at h0
    rw [h1, sub_self, Complex.normSq_zero, hsinN] at h0
    have : 0 < 4 * Real.sin (Real.pi * φ / N) ^ 2 := by positivity
    linarith
  have hfac := sinePhaseAmplitude_factor M hM10 β a
  change sinePhaseAmplitude M β a = ((N : ℂ)⁻¹) * sineW (ω ^ B) * geomB B ω at hfac
  rw [hfac, hωB, geomB, geom_sum_eq hω_ne, hωB]
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast,
    Complex.normSq_div, normSq_eigenvalue_sub_one, normSq_eigenvalue_sub_one,
    sineW_closed_form (eigenvalue θ) θ rfl hpm_ne.1 hpm_ne.2,
    hcos1024, hsinθ, hsinN]
  have hrw_den : 2 * Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2 =
      2 * (Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2) := by
    rw [mul_assoc, hsinPM]
  rw [hrw_den]
  field_simp [hNR.ne', hpos_N.ne', hpos_p.ne', hpos_m.ne']

/-- Small-range sharp pointwise bound (`3/2 ≤ φ ≤ 17`, `M ≥ 204`). -/
theorem sinePhaseAmplitude_small_bound (M : ℕ) (hM : 204 ≤ M) (β : ℝ) (a : ℕ) (φ : ℝ)
    (hlo : 3 / 2 ≤ φ) (hhi : φ ≤ 17)
    (hφ : φ = phiR (2 ^ M) ((2 ^ M : ℕ) * β) a ∨ φ = phiL (2 ^ M) ((2 ^ M : ℕ) * β) a) :
    Complex.normSq (sinePhaseAmplitude M β a) ≤
      (508 / 10000 : ℝ) * Real.cos (Real.pi * ((2 ^ M : ℕ) : ℝ) * β) ^ 2 / (φ ^ 2 - 1 / 4) ^ 2 := by
  set N := (2 ^ M : ℕ)
  have hNbig : (2 ^ 204 : ℝ) ≤ (N : ℝ) := by
    have : 2 ^ 204 ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hM
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by linarith [show (0 : ℝ) < 2 ^ 204 by positivity]
  rw [sinePhaseAmplitude_closed_form M hM β a φ hlo (by linarith) hφ]
  have hpi_lo : (3141592 / 1000000 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpi_hi : Real.pi < (3141593 / 1000000 : ℝ) := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  -- Upper bounds on numerator sines
  have hnum1 : Real.sin (Real.pi / 1024) ^ 2 ≤ (3141593 / 1000000 / 1024 : ℝ) ^ 2 := by
    have h0 : 0 ≤ Real.sin (Real.pi / 1024) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
    have hle : Real.sin (Real.pi / 1024) ≤ 3141593 / 1000000 / 1024 :=
      (Real.sin_le (by positivity)).trans (by linarith)
    exact pow_le_pow_left₀ h0 hle 2
  have hnum2 : Real.sin (Real.pi * φ / 1024) ^ 2 ≤ ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 := by
    have h0 : 0 ≤ Real.sin (Real.pi * φ / 1024) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    have hle : Real.sin (Real.pi * φ / 1024) ≤ (3141593 / 1000000 : ℝ) * φ / 1024 :=
      (Real.sin_le (by positivity)).trans (by nlinarith)
    exact pow_le_pow_left₀ h0 hle 2
  -- Lower bound on `N * sin(π φ / N)`
  have hNsin : (3141591 / 1000000 : ℝ) * φ ≤ (N : ℝ) * Real.sin (Real.pi * φ / N) := by
    have hu : φ / N ≤ 1 / 2 ^ 20 := by
      rw [div_le_iff₀ hNR]
      have : (2 : ℝ) ^ 20 * 17 ≤ (2 : ℝ) ^ 204 := by norm_num
      nlinarith
    have h := sin_pi_mul_ge_sharp (φ / N) (by positivity) hu
    have hm := mul_le_mul_of_nonneg_left h hNR.le
    rw [show Real.pi * (φ / N) = Real.pi * φ / N by ring] at hm
    calc (3141591 / 1000000 : ℝ) * φ = (N : ℝ) * ((3141591 / 1000000 : ℝ) * (φ / N)) := by
          field_simp [hNR.ne']
      _ ≤ _ := hm
  -- Lower bound on `sin(π u / 1024)` for `0 ≤ u ≤ 35/2`:
  -- `1 - (3.141593 * 17.5 / 1024)^2 / 6 > 99951 / 100000`
  have hsin_small (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 35 / 2) :
      (314005 / 100000 : ℝ) * (u / 1024) ≤ Real.sin (Real.pi * u / 1024) := by
    have hx0 : 0 ≤ Real.pi * u / 1024 := by positivity
    have hx_le : Real.pi * u / 1024 ≤ (3141593 / 1000000 : ℝ) * (35 / 2) / 1024 := by nlinarith
    have hx_ge : (3141592 / 1000000 : ℝ) * (u / 1024) ≤ Real.pi * u / 1024 := by nlinarith
    have hc := sin_ge_cubic (Real.pi * u / 1024) hx0
    have hsq : (Real.pi * u / 1024) ^ 2 ≤ ((3141593 / 1000000 : ℝ) * (35 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ hx0 hx_le 2
    have hfac : 1 - (Real.pi * u / 1024) ^ 2 / 6 ≥ 99951 / 100000 := by
      have : ((3141593 / 1000000 : ℝ) * (35 / 2) / 1024) ^ 2 / 6 ≤ 49 / 100000 := by norm_num
      linarith
    have hprod : (Real.pi * u / 1024) * (99951 / 100000 : ℝ) ≤
        Real.pi * u / 1024 - (Real.pi * u / 1024) ^ 3 / 6 := by nlinarith
    have hcoef : (314005 / 100000 : ℝ) ≤ (3141592 / 1000000 : ℝ) * (99951 / 100000 : ℝ) := by norm_num
    nlinarith
  have hsp := hsin_small (φ + 1 / 2) (by linarith) (by linarith)
  have hsm := hsin_small (φ - 1 / 2) (by linarith) (by linarith)
  have hφm : 0 < φ - 1 / 2 := by linarith
  have hden_ge :
      2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
        ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 *
        ((314005 / 100000 : ℝ) * ((φ - 1 / 2) / 1024)) ^ 2 ≤
      2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 := by
    have h1 : ((3141591 / 1000000 : ℝ) * φ) ^ 2 ≤ (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hNsin 2
    have h2 : ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 ≤ Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsp 2
    have h3 : ((314005 / 100000 : ℝ) * ((φ - 1 / 2) / 1024)) ^ 2 ≤ Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsm 2
    have h12 : 2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
          ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 ≤
        2 * ((N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2) *
          Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 :=
      mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    have h123 := mul_le_mul h12 h3 (by positivity) (by positivity)
    linarith [show 2 * ((N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2) *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 =
      2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 by ring]
  have hnum_le :
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 *
        Real.sin (Real.pi * φ / 1024) ^ 2 ≤
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 *
        ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 := by
    have h12 := mul_le_mul hnum1 hnum2 (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left h12 (sq_nonneg (Real.cos (Real.pi * (N : ℝ) * β)))
    linarith [show Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (Real.sin (Real.pi / 1024) ^ 2 * Real.sin (Real.pi * φ / 1024) ^ 2) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 * Real.sin (Real.pi * φ / 1024) ^ 2 by ring,
      show Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * ((3141593 / 1000000 / 1024 : ℝ) ^ 2 * ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 * ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 by ring]
  have hφ_pos : 0 < φ := by linarith
  have hsq_pos : 0 < φ ^ 2 - 1 / 4 := by nlinarith
  have hden_pos : 0 < 2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
      ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 *
      ((314005 / 100000 : ℝ) * ((φ - 1 / 2) / 1024)) ^ 2 := by positivity
  refine (div_le_div₀ (by positivity) hnum_le hden_pos hden_ge).trans ?_
  have hsimp :
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 *
        ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 /
      (2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
        ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 *
        ((314005 / 100000 : ℝ) * ((φ - 1 / 2) / 1024)) ^ 2) =
      ((3141593 / 1000000 : ℝ) ^ 4 / (2 * (3141591 / 1000000 : ℝ) ^ 2 * (314005 / 100000 : ℝ) ^ 4)) *
        Real.cos (Real.pi * (N : ℝ) * β) ^ 2 / (φ ^ 2 - 1 / 4) ^ 2 := by
    have hpm : (φ + 1 / 2) * (φ - 1 / 2) = φ ^ 2 - 1 / 4 := by ring
    have h1 : φ + 1 / 2 ≠ 0 := by linarith
    have h2 : φ - 1 / 2 ≠ 0 := by linarith
    rw [← hpm]
    field_simp [hφ_pos.ne', h1, h2]
  rw [hsimp]
  have hconst : (3141593 / 1000000 : ℝ) ^ 4 /
      (2 * (3141591 / 1000000 : ℝ) ^ 2 * (314005 / 100000 : ℝ) ^ 4) ≤ 508 / 10000 := by norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (sq_nonneg _)) (sq_nonneg _)

/-- Medium-range pointwise bound (`16 ≤ φ ≤ 512`, `M ≥ 204`). -/
theorem sinePhaseAmplitude_med_bound (M : ℕ) (hM : 204 ≤ M) (β : ℝ) (a : ℕ) (φ : ℝ)
    (hlo : 16 ≤ φ) (hhi : φ ≤ 512)
    (hφ : φ = phiR (2 ^ M) ((2 ^ M : ℕ) * β) a ∨ φ = phiL (2 ^ M) ((2 ^ M : ℕ) * β) a) :
    Complex.normSq (sinePhaseAmplitude M β a) ≤
      (31 / 100 : ℝ) * Real.cos (Real.pi * ((2 ^ M : ℕ) : ℝ) * β) ^ 2 / (φ - 1 / 2) ^ 4 := by
  set N := (2 ^ M : ℕ)
  have hNbig : (2 ^ 204 : ℝ) ≤ (N : ℝ) := by
    have : 2 ^ 204 ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hM
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by linarith [show (0 : ℝ) < 2 ^ 204 by positivity]
  rw [sinePhaseAmplitude_closed_form M hM β a φ (by linarith) hhi hφ]
  have hpi_hi : Real.pi < (3141593 / 1000000 : ℝ) := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hnum1 : Real.sin (Real.pi / 1024) ^ 2 ≤ (3141593 / 1000000 / 1024 : ℝ) ^ 2 := by
    have h0 : 0 ≤ Real.sin (Real.pi / 1024) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    exact pow_le_pow_left₀ h0 ((Real.sin_le (by positivity)).trans (by linarith)) 2
  have hnum2 : Real.sin (Real.pi * φ / 1024) ^ 2 ≤ ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 := by
    have h0 : 0 ≤ Real.sin (Real.pi * φ / 1024) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    exact pow_le_pow_left₀ h0 ((Real.sin_le (by positivity)).trans (by nlinarith)) 2
  have hNsin : (3141591 / 1000000 : ℝ) * φ ≤ (N : ℝ) * Real.sin (Real.pi * φ / N) := by
    have hu : φ / N ≤ 1 / 2 ^ 20 := by
      rw [div_le_iff₀ hNR]
      have : (2 : ℝ) ^ 20 * 512 ≤ (2 : ℝ) ^ 204 := by norm_num
      nlinarith
    have h := sin_pi_mul_ge_sharp (φ / N) (by positivity) hu
    have hm := mul_le_mul_of_nonneg_left h hNR.le
    rw [show Real.pi * (φ / N) = Real.pi * φ / N by ring] at hm
    calc (3141591 / 1000000 : ℝ) * φ = (N : ℝ) * ((3141591 / 1000000 : ℝ) * (φ / N)) := by
          field_simp [hNR.ne']
      _ ≤ _ := hm
  have hsm : 2 * ((φ - 1 / 2) / 1024) ≤ Real.sin (Real.pi * (φ - 1 / 2) / 1024) := by
    rw [show Real.pi * (φ - 1 / 2) / 1024 = Real.pi * ((φ - 1 / 2) / 1024) by ring]
    exact sin_jordan ((φ - 1 / 2) / 1024) (by linarith) (by linarith)
  have hsp : 2 * ((φ - 1 / 2) / 1024) ≤ Real.sin (Real.pi * (φ + 1 / 2) / 1024) := by
    by_cases h512 : φ + 1 / 2 ≤ 512
    · have hj := sin_jordan ((φ + 1 / 2) / 1024) (by linarith) (by linarith)
      rw [show Real.pi * ((φ + 1 / 2) / 1024) = Real.pi * (φ + 1 / 2) / 1024 by ring] at hj
      linarith
    · have hsub : Real.sin (Real.pi * (φ + 1 / 2) / 1024) =
          Real.sin (Real.pi * ((1023.5 - φ) / 1024)) := by
        rw [show Real.pi * (φ + 1 / 2) / 1024 = Real.pi - Real.pi * ((1023.5 - φ) / 1024) by ring,
          Real.sin_pi_sub]
      rw [hsub]
      have hj := sin_jordan ((1023.5 - φ) / 1024) (by linarith) (by linarith)
      linarith
  have hden_ge :
      2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
        (2 * ((φ - 1 / 2) / 1024)) ^ 2 * (2 * ((φ - 1 / 2) / 1024)) ^ 2 ≤
      2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 := by
    have h1 : ((3141591 / 1000000 : ℝ) * φ) ^ 2 ≤ (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hNsin 2
    have h2 : (2 * ((φ - 1 / 2) / 1024)) ^ 2 ≤ Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hsp 2
    have h3 : (2 * ((φ - 1 / 2) / 1024)) ^ 2 ≤ Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hsm 2
    have h12 : 2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 * (2 * ((φ - 1 / 2) / 1024)) ^ 2 ≤
        2 * ((N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2) *
          Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 :=
      mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    have h123 := mul_le_mul h12 h3 (by positivity) (by positivity)
    linarith [show 2 * ((N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2) *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 =
      2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 by ring]
  have hnum_le :
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 *
        Real.sin (Real.pi * φ / 1024) ^ 2 ≤
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 *
        ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 := by
    have h12 := mul_le_mul hnum1 hnum2 (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left h12 (sq_nonneg (Real.cos (Real.pi * (N : ℝ) * β)))
    linarith [show Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (Real.sin (Real.pi / 1024) ^ 2 * Real.sin (Real.pi * φ / 1024) ^ 2) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 * Real.sin (Real.pi * φ / 1024) ^ 2 by ring,
      show Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * ((3141593 / 1000000 / 1024 : ℝ) ^ 2 * ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 * ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 by ring]
  have hφ_pos : 0 < φ := by linarith
  have hm_pos : 0 < φ - 1 / 2 := by linarith
  have hden_pos : 0 < 2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
      (2 * ((φ - 1 / 2) / 1024)) ^ 2 * (2 * ((φ - 1 / 2) / 1024)) ^ 2 := by positivity
  refine (div_le_div₀ (by positivity) hnum_le hden_pos hden_ge).trans ?_
  have hsimp :
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 *
        ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 /
      (2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
        (2 * ((φ - 1 / 2) / 1024)) ^ 2 * (2 * ((φ - 1 / 2) / 1024)) ^ 2) =
      ((3141593 / 1000000 : ℝ) ^ 4 / (32 * (3141591 / 1000000 : ℝ) ^ 2)) *
        Real.cos (Real.pi * (N : ℝ) * β) ^ 2 / (φ - 1 / 2) ^ 4 := by
    field_simp [hφ_pos.ne', hm_pos.ne']; ring
  rw [hsimp]
  have hconst : (3141593 / 1000000 : ℝ) ^ 4 / (32 * (3141591 / 1000000 : ℝ) ^ 2) ≤ 31 / 100 := by
    norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (sq_nonneg _)) (by positivity)

/-! ### Part 4: Summing small & medium tails -/

theorem sum_range_inv_fourth (R : ℝ) (hR : 1 < R) (M : ℕ) :
    ∑ k ∈ range M, 1 / (R + k) ^ 4 ≤ 1 / (3 * (R - 1) ^ 3) - 1 / (3 * (R - 1 + M) ^ 3) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hx : 1 < R + M := by linarith
    have hstep : 1 / (R + M) ^ 4 ≤
        1 / (3 * (R - 1 + M) ^ 3) - 1 / (3 * (R - 1 + ((M + 1 : ℕ) : ℝ)) ^ 3) := by
      set x := R + M
      have hx1 : 0 < x - 1 := by linarith
      have hx0 : 0 < x := by linarith
      have hre : R - 1 + ((M + 1 : ℕ) : ℝ) = x := by push_cast; dsimp [x]; ring
      have hre2 : R - 1 + M = x - 1 := by dsimp [x]; ring
      rw [hre, hre2, div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have hpoly : (1 * (3 * x ^ 3) - 3 * (x - 1) ^ 3 * 1) * x ^ 4 -
          1 * (3 * (x - 1) ^ 3 * (3 * x ^ 3)) = 3 * x ^ 3 * (6 * x ^ 2 - 8 * x + 3) := by ring
      have hq : 0 < 6 * x ^ 2 - 8 * x + 3 := by nlinarith [sq_nonneg (x - 2 / 3)]
      have hpos : 0 < 3 * x ^ 3 * (6 * x ^ 2 - 8 * x + 3) := mul_pos (by positivity) hq
      linarith
    linarith

theorem sum_inv_fourth_ge (S : Finset ℕ) (φ : ℕ → ℝ) (R : ℝ) (hR : 3 / 2 < R)
    (hφ : ∀ a ∈ S, R ≤ φ a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a - 1 / 2) ^ 4 ≤ 1 / (3 * (R - 3 / 2) ^ 3) := by
  set g : ℕ → ℕ := fun a => ⌊φ a - R⌋₊
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h2 := Nat.lt_floor_add_one (φ a - R)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb))
    have h4 := Nat.lt_floor_add_one (φ b - R)
    dsimp only [g] at hab; rw [hab] at h1 h2
    exact hsep a ha b hb (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have h1 : ∑ a ∈ S, 1 / (φ a - 1 / 2) ^ 4 ≤ ∑ a ∈ S, 1 / ((R - 1 / 2) + g a) ^ 4 := by
    apply Finset.sum_le_sum; intro a ha
    have hfl : (g a : ℝ) ≤ φ a - R := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h0 : 0 < (R - 1 / 2) + g a := by linarith [Nat.cast_nonneg (α := ℝ) (g a)]
    exact one_div_le_one_div_of_le (pow_pos h0 4) (pow_le_pow_left₀ h0.le (by linarith) 4)
  have h2 : ∑ a ∈ S, 1 / ((R - 1 / 2) + g a) ^ 4 = ∑ k ∈ S.image g, 1 / ((R - 1 / 2) + k) ^ 4 := by
    rw [Finset.sum_image hinj]
  have h3 : ∑ k ∈ S.image g, 1 / ((R - 1 / 2) + k) ^ 4 ≤
      ∑ k ∈ range (S.sup g + 1), 1 / ((R - 1 / 2) + k) ^ 4 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      exact mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup ha))
    · intro k _ _; positivity
  have h4 := sum_range_inv_fourth (R - 1 / 2) (by linarith) (S.sup g + 1)
  have h5 : 0 ≤ 1 / (3 * (R - 1 / 2 - 1 + ((S.sup g + 1 : ℕ) : ℝ)) ^ 3) := by
    have : (0 : ℝ) ≤ ((S.sup g + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 0 < R - 1 / 2 - 1 + ((S.sup g + 1 : ℕ) : ℝ) := by linarith
    positivity
  have hre : R - 1 / 2 - 1 = R - 3 / 2 := by ring
  rw [hre] at h4 h5
  linarith

theorem sum_small_tail (S : Finset ℕ) (φ : ℕ → ℝ) (R : ℝ) (K : ℕ)
    (hR : 1 < R)
    (hφ : ∀ a ∈ S, R ≤ φ a ∧ φ a < R + K)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a ^ 2 - 1 / 4) ^ 2 ≤ ∑ k ∈ range K, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 := by
  set g : ℕ → ℕ := fun a => ⌊φ a - R⌋₊
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha).1)
    have h2 := Nat.lt_floor_add_one (φ a - R)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb).1)
    have h4 := Nat.lt_floor_add_one (φ b - R)
    dsimp only [g] at hab; rw [hab] at h1 h2
    exact hsep a ha b hb (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have h1 : ∑ a ∈ S, 1 / (φ a ^ 2 - 1 / 4) ^ 2 ≤ ∑ a ∈ S, 1 / ((R + g a) ^ 2 - 1 / 4) ^ 2 := by
    apply Finset.sum_le_sum; intro a ha
    have hfl : (g a : ℝ) ≤ φ a - R := Nat.floor_le (sub_nonneg.mpr (hφ a ha).1)
    have h0 : 0 < R + g a := by linarith [Nat.cast_nonneg (α := ℝ) (g a)]
    have hpos : 0 < (R + g a) ^ 2 - 1 / 4 := by nlinarith
    have hle : (R + g a) ^ 2 - 1 / 4 ≤ φ a ^ 2 - 1 / 4 := by nlinarith
    exact one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hle 2)
  have h2 : ∑ a ∈ S, 1 / ((R + g a) ^ 2 - 1 / 4) ^ 2 =
      ∑ k ∈ S.image g, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 := by rw [Finset.sum_image hinj]
  have h3 : ∑ k ∈ S.image g, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 ≤
      ∑ k ∈ range K, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      rw [mem_range]
      exact Nat.floor_lt (sub_nonneg.mpr (hφ a ha).1) |>.mpr (by linarith [(hφ a ha).2])
    · intro k _ _; positivity
  linarith

/-- Master two-sided circular mass lower bound for `sinePhaseAmplitude` (`M ≥ 204`). -/
theorem sine_circular_mass_two (M : ℕ) (hM : 204 ≤ M) (β : ℝ)
    (R1 R2 : ℝ) (K1 K2 : ℕ)
    (hR1_lo : 3 / 2 ≤ R1) (hR2_lo : 3 / 2 ≤ R2)
    (hR1_hi : R1 + K1 ≤ 17) (hR2_hi : R2 + K2 ≤ 17)
    (hM1 : 16 ≤ R1 + K1) (hM2 : 16 ≤ R2 + K2) :
    1 - Real.cos (Real.pi * ((2 ^ M : ℕ) : ℝ) * β) ^ 2 *
        ((508 / 10000 : ℝ) *
          ((∑ k ∈ range K1, 1 / ((R1 + k) ^ 2 - 1 / 4) ^ 2) +
           (∑ k ∈ range K2, 1 / ((R2 + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000) -
        12 / 1000000 ≤
      ∑ a ∈ range (2 ^ M),
        if phiR (2 ^ M) ((2 ^ M : ℕ) * β) a < R1 ∨ phiL (2 ^ M) ((2 ^ M : ℕ) * β) a < R2
        then Complex.normSq (sinePhaseAmplitude M β a) else 0 := by
  classical
  set N := 2 ^ M
  set c := ((N : ℕ) : ℝ) * β
  set cs := Real.cos (Real.pi * (N : ℝ) * β) ^ 2
  have hcs0 : 0 ≤ cs := sq_nonneg _
  have hM10 : 10 ≤ M := by omega
  have hM11 : 11 ≤ M := by omega
  let RSs := (range N).filter (fun a => R1 ≤ phiR N c a ∧ phiR N c a < R1 + K1)
  let RSm := (range N).filter (fun a => R1 + K1 ≤ phiR N c a ∧ phiR N c a ≤ 512)
  let LSs := (range N).filter (fun a => R2 ≤ phiL N c a ∧ phiL N c a < R2 + K2)
  let LSm := (range N).filter (fun a => R2 + K2 ≤ phiL N c a ∧ phiL N c a ≤ 512)
  have hRSs : ∑ a ∈ RSs, Complex.normSq (sinePhaseAmplitude M β a) ≤
      (508 / 10000 : ℝ) * cs * ∑ k ∈ range K1, 1 / ((R1 + k) ^ 2 - 1 / 4) ^ 2 := by
    have hpt : ∀ a ∈ RSs, Complex.normSq (sinePhaseAmplitude M β a) ≤
        ((508 / 10000 : ℝ) * cs) * (1 / (phiR N c a ^ 2 - 1 / 4) ^ 2) := by
      intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      have h := sinePhaseAmplitude_small_bound M hM β a (phiR N c a) (by linarith [hd.1])
        (by linarith [hd.2]) (Or.inl rfl)
      linarith [show ((508 / 10000 : ℝ) * cs) * (1 / (phiR N c a ^ 2 - 1 / 4) ^ 2) =
        (508 / 10000 : ℝ) * cs / (phiR N c a ^ 2 - 1 / 4) ^ 2 by ring]
    calc
      _ ≤ ∑ a ∈ RSs, ((508 / 10000 : ℝ) * cs) * (1 / (phiR N c a ^ 2 - 1 / 4) ^ 2) :=
        Finset.sum_le_sum hpt
      _ = ((508 / 10000 : ℝ) * cs) * ∑ a ∈ RSs, 1 / (phiR N c a ^ 2 - 1 / 4) ^ 2 := by
        rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_small_tail RSs (phiR N c) R1 K1 (by linarith)
          (fun a ha => (Finset.mem_filter.mp ha).2)
          (fun a ha b hb => phiR_sep N c a b (mem_range.mp (Finset.mem_filter.mp ha).1)
            (mem_range.mp (Finset.mem_filter.mp hb).1))) (by positivity)
  have hLSs : ∑ a ∈ LSs, Complex.normSq (sinePhaseAmplitude M β a) ≤
      (508 / 10000 : ℝ) * cs * ∑ k ∈ range K2, 1 / ((R2 + k) ^ 2 - 1 / 4) ^ 2 := by
    have hpt : ∀ a ∈ LSs, Complex.normSq (sinePhaseAmplitude M β a) ≤
        ((508 / 10000 : ℝ) * cs) * (1 / (phiL N c a ^ 2 - 1 / 4) ^ 2) := by
      intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      have h := sinePhaseAmplitude_small_bound M hM β a (phiL N c a) (by linarith [hd.1])
        (by linarith [hd.2]) (Or.inr rfl)
      linarith [show ((508 / 10000 : ℝ) * cs) * (1 / (phiL N c a ^ 2 - 1 / 4) ^ 2) =
        (508 / 10000 : ℝ) * cs / (phiL N c a ^ 2 - 1 / 4) ^ 2 by ring]
    calc
      _ ≤ ∑ a ∈ LSs, ((508 / 10000 : ℝ) * cs) * (1 / (phiL N c a ^ 2 - 1 / 4) ^ 2) :=
        Finset.sum_le_sum hpt
      _ = ((508 / 10000 : ℝ) * cs) * ∑ a ∈ LSs, 1 / (phiL N c a ^ 2 - 1 / 4) ^ 2 := by
        rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_small_tail LSs (phiL N c) R2 K2 (by linarith)
          (fun a ha => (Finset.mem_filter.mp ha).2)
          (fun a ha b hb => phiL_sep N c a b (mem_range.mp (Finset.mem_filter.mp ha).1)
            (mem_range.mp (Finset.mem_filter.mp hb).1))) (by positivity)
  have hRSm : ∑ a ∈ RSm, Complex.normSq (sinePhaseAmplitude M β a) ≤ (34 / 1000000 : ℝ) * cs := by
    have hpt : ∀ a ∈ RSm, Complex.normSq (sinePhaseAmplitude M β a) ≤
        ((31 / 100 : ℝ) * cs) * (1 / (phiR N c a - 1 / 2) ^ 4) := by
      intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      have h := sinePhaseAmplitude_med_bound M hM β a (phiR N c a) (by linarith [hd.1]) hd.2 (Or.inl rfl)
      linarith [show ((31 / 100 : ℝ) * cs) * (1 / (phiR N c a - 1 / 2) ^ 4) =
        (31 / 100 : ℝ) * cs / (phiR N c a - 1 / 2) ^ 4 by ring]
    have hsum := sum_inv_fourth_ge RSm (phiR N c) 16 (by norm_num)
      (fun a ha => by linarith [(Finset.mem_filter.mp ha).2.1])
      (fun a ha b hb => phiR_sep N c a b (mem_range.mp (Finset.mem_filter.mp ha).1)
        (mem_range.mp (Finset.mem_filter.mp hb).1))
    calc
      _ ≤ ((31 / 100 : ℝ) * cs) * ∑ a ∈ RSm, 1 / (phiR N c a - 1 / 2) ^ 4 := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hpt
      _ ≤ ((31 / 100 : ℝ) * cs) * (1 / (3 * (16 - 3 / 2 : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (34 / 1000000 : ℝ) * cs := by
        have : (31 / 100 : ℝ) * (1 / (3 * (16 - 3 / 2 : ℝ) ^ 3)) ≤ 34 / 1000000 := by norm_num
        nlinarith
  have hLSm : ∑ a ∈ LSm, Complex.normSq (sinePhaseAmplitude M β a) ≤ (34 / 1000000 : ℝ) * cs := by
    have hpt : ∀ a ∈ LSm, Complex.normSq (sinePhaseAmplitude M β a) ≤
        ((31 / 100 : ℝ) * cs) * (1 / (phiL N c a - 1 / 2) ^ 4) := by
      intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      have h := sinePhaseAmplitude_med_bound M hM β a (phiL N c a) (by linarith [hd.1]) hd.2 (Or.inr rfl)
      linarith [show ((31 / 100 : ℝ) * cs) * (1 / (phiL N c a - 1 / 2) ^ 4) =
        (31 / 100 : ℝ) * cs / (phiL N c a - 1 / 2) ^ 4 by ring]
    have hsum := sum_inv_fourth_ge LSm (phiL N c) 16 (by norm_num)
      (fun a ha => by linarith [(Finset.mem_filter.mp ha).2.1])
      (fun a ha b hb => phiL_sep N c a b (mem_range.mp (Finset.mem_filter.mp ha).1)
        (mem_range.mp (Finset.mem_filter.mp hb).1))
    calc
      _ ≤ ((31 / 100 : ℝ) * cs) * ∑ a ∈ LSm, 1 / (phiL N c a - 1 / 2) ^ 4 := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hpt
      _ ≤ ((31 / 100 : ℝ) * cs) * (1 / (3 * (16 - 3 / 2 : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (34 / 1000000 : ℝ) * cs := by
        have : (31 / 100 : ℝ) * (1 / (3 * (16 - 3 / 2 : ℝ) ^ 3)) ≤ 34 / 1000000 := by norm_num
        nlinarith
  have hfar := sinePhaseAmplitude_far_tail M hM11 β
  have hcov (a : ℕ) :
      (if ¬ (phiR N c a < R1 ∨ phiL N c a < R2) then Complex.normSq (sinePhaseAmplitude M β a) else 0) ≤
      (if R1 ≤ phiR N c a ∧ phiR N c a < R1 + K1 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
      (if R1 + K1 ≤ phiR N c a ∧ phiR N c a ≤ 512 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
      (if R2 ≤ phiL N c a ∧ phiL N c a < R2 + K2 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
      (if R2 + K2 ≤ phiL N c a ∧ phiL N c a ≤ 512 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
      (if 512 < phiR N c a ∧ 512 < phiL N c a then Complex.normSq (sinePhaseAmplitude M β a) else 0) := by
    have ha0 : 0 ≤ Complex.normSq (sinePhaseAmplitude M β a) := Complex.normSq_nonneg _
    by_cases hb : ¬ (phiR N c a < R1 ∨ phiL N c a < R2)
    · rw [if_pos hb]
      have hr : R1 ≤ phiR N c a := le_of_not_gt (fun h => hb (Or.inl h))
      have hl : R2 ≤ phiL N c a := le_of_not_gt (fun h => hb (Or.inr h))
      by_cases h1 : phiR N c a < R1 + K1
      · rw [if_pos ⟨hr, h1⟩]; split_ifs <;> linarith
      · rw [if_neg (fun h => h1 h.2)]
        by_cases h2 : phiR N c a ≤ 512
        · rw [if_pos ⟨le_of_not_gt h1, h2⟩]; split_ifs <;> linarith
        · rw [if_neg (fun h => h2 h.2)]
          by_cases h3 : phiL N c a < R2 + K2
          · rw [if_pos ⟨hl, h3⟩]; split_ifs <;> linarith
          · rw [if_neg (fun h => h3 h.2)]
            by_cases h4 : phiL N c a ≤ 512
            · rw [if_pos ⟨le_of_not_gt h3, h4⟩]; split_ifs <;> linarith
            · rw [if_neg (fun h => h4 h.2), if_pos ⟨lt_of_not_ge h2, lt_of_not_ge h4⟩]; linarith
    · rw [if_neg hb]; split_ifs <;> linarith
  have hbad : (∑ a ∈ range N,
      if ¬ (phiR N c a < R1 ∨ phiL N c a < R2) then Complex.normSq (sinePhaseAmplitude M β a) else 0) ≤
      cs * ((508 / 10000 : ℝ) *
          ((∑ k ∈ range K1, 1 / ((R1 + k) ^ 2 - 1 / 4) ^ 2) +
           (∑ k ∈ range K2, 1 / ((R2 + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000) + 12 / 1000000 := by
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ range N) => hcov a)
    simp only [Finset.sum_add_distrib] at hsum
    have h1 := hRSs
    simp only [RSs, Finset.sum_filter] at h1
    have h2 := hRSm
    simp only [RSm, Finset.sum_filter] at h2
    have h3 := hLSs
    simp only [LSs, Finset.sum_filter] at h3
    have h4 := hLSm
    simp only [LSm, Finset.sum_filter] at h4
    linarith
  have htot : (∑ a ∈ range N,
      if phiR N c a < R1 ∨ phiL N c a < R2 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
    (∑ a ∈ range N,
      if ¬ (phiR N c a < R1 ∨ phiL N c a < R2) then Complex.normSq (sinePhaseAmplitude M β a) else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert sinePhaseAmplitude_parseval M hM10 β using 1
    apply Finset.sum_congr rfl; intro a _; split_ifs <;> ring
  linarith

/-! ### Part 5: Rational small-sum evaluators and Left/Right axis box bounds -/

def smallSumQ : ℕ → ℚ → ℚ
  | 0, _ => 0
  | K + 1, R => smallSumQ K R + 1 / ((R + K) ^ 2 - 1 / 4) ^ 2

theorem smallSum_cast (K : ℕ) (R : ℚ) :
    ∑ k ∈ range K, 1 / (((R : ℝ) + k) ^ 2 - 1 / 4) ^ 2 = ((smallSumQ K R : ℚ) : ℝ) := by
  induction K with
  | zero => simp [smallSumQ]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, smallSumQ]
    push_cast; rfl

theorem smallSum_antitone (K : ℕ) (R R' : ℝ) (h1 : 1 < R) (hle : R ≤ R') :
    ∑ k ∈ range K, 1 / ((R' + k) ^ 2 - 1 / 4) ^ 2 ≤ ∑ k ∈ range K, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 := by
  apply Finset.sum_le_sum; intro k _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < (R + k) ^ 2 - 1 / 4 := by nlinarith
  have hsq : (R + k) ^ 2 - 1 / 4 ≤ (R' + k) ^ 2 - 1 / 4 := by nlinarith
  exact one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hsq 2)

theorem left_box_sum (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (508 / 10000 : ℝ) *
      ((∑ k ∈ range 14, 1 / ((3 - t + k) ^ 2 - 1 / 4) ^ 2) +
       (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ 586 / 100000 := by
  have hbox (a b : ℚ) (ha : (a : ℝ) ≤ t) (hb : t ≤ (b : ℝ)) (h1 : (0 : ℚ) ≤ a) (h2 : b ≤ 1 / 2)
      (hcheck : (508 / 10000 : ℚ) * (smallSumQ 14 (3 - b) + smallSumQ 14 (2 + a)) + 68 / 1000000 ≤
        586 / 100000) :
      (508 / 10000 : ℝ) *
        ((∑ k ∈ range 14, 1 / ((3 - t + k) ^ 2 - 1 / 4) ^ 2) +
         (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ 586 / 100000 := by
    have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
    have hbR : (b : ℝ) ≤ 1 / 2 := by
      have h := Rat.cast_le (K := ℝ).mpr h2; push_cast at h; exact h
    have hA := smallSum_antitone 14 ((3 - b : ℚ) : ℝ) (3 - t) (by push_cast; linarith) (by push_cast; linarith)
    have hB := smallSum_antitone 14 ((2 + a : ℚ) : ℝ) (2 + t) (by push_cast; linarith) (by push_cast; linarith)
    rw [smallSum_cast] at hA hB
    have hR : (508 / 10000 : ℝ) * (((smallSumQ 14 (3 - b) : ℚ) : ℝ) + ((smallSumQ 14 (2 + a) : ℚ) : ℝ)) +
        68 / 1000000 ≤ 586 / 100000 := by
      have h := Rat.cast_le (K := ℝ).mpr hcheck; push_cast at h; exact h
    linarith
  by_cases h1 : t ≤ 1 / 16
  · exact hbox 0 (1 / 16) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
  · by_cases h2 : t ≤ 1 / 4
    · exact hbox (1 / 16) (1 / 4) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
    · exact hbox (1 / 4) (1 / 2) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)

def cosUbQ (a : ℚ) : ℚ :=
  let xlo := (3141592 / 1000000 : ℚ) * a
  let xhi := (3141593 / 1000000 : ℚ) * a
  min (1 - xlo ^ 2 / 2 + xhi ^ 4 / 24) ((3141593 / 1000000 : ℚ) * (1 / 2 - a))

theorem cos_le_cosUbQ (a : ℚ) (t : ℝ) (ha0 : (0 : ℚ) ≤ a) (ha : (a : ℝ) ≤ t) (ht : t ≤ 1 / 2) :
    0 ≤ Real.cos (Real.pi * t) ∧ Real.cos (Real.pi * t) ≤ (cosUbQ a : ℝ) := by
  have hpi_lo : (3141592 / 1000000 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpi_hi : Real.pi < (3141593 / 1000000 : ℝ) := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha0
  have hcos0 : 0 ≤ Real.cos (Real.pi * t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hanti : Real.cos (Real.pi * t) ≤ Real.cos (Real.pi * (a : ℝ)) := by
    apply Real.strictAntiOn_cos.antitoneOn
    · exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    · exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    · nlinarith [Real.pi_pos]
  refine ⟨hcos0, hanti.trans ?_⟩
  simp only [cosUbQ, Rat.cast_min]
  apply le_min
  · have htay := cos_le_taylor4 (Real.pi * (a : ℝ)) (by positivity)
    have hxlo : (3141592 / 1000000 : ℝ) * (a : ℝ) ≤ Real.pi * (a : ℝ) := by nlinarith
    have hxhi : Real.pi * (a : ℝ) ≤ (3141593 / 1000000 : ℝ) * (a : ℝ) := by nlinarith
    have hsq : ((3141592 / 1000000 : ℝ) * (a : ℝ)) ^ 2 ≤ (Real.pi * (a : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hxlo 2
    have h4 : (Real.pi * (a : ℝ)) ^ 4 ≤ ((3141593 / 1000000 : ℝ) * (a : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hxhi 4
    push_cast; linarith
  · have hlin := cos_le_pi_div_two_sub (Real.pi * (a : ℝ)) (by nlinarith [Real.pi_pos])
    push_cast
    have : Real.pi / 2 - Real.pi * (a : ℝ) = Real.pi * (1 / 2 - (a : ℝ)) := by ring
    nlinarith

theorem right_box_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.cos (Real.pi * t) ^ 2 *
      ((508 / 10000 : ℝ) *
        ((∑ k ∈ range 15, 1 / ((2 - t + k) ^ 2 - 1 / 4) ^ 2) +
         (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000) ≤
    136 / 100000 + (900 / 100000 : ℝ) * Real.cos (Real.pi * t) ^ 2 := by
  have hbox (a b : ℚ) (ha : (a : ℝ) ≤ t) (hb : t ≤ (b : ℝ)) (h1 : (0 : ℚ) ≤ a) (h2 : b ≤ 1 / 2)
      (hcheck : ((508 / 10000 : ℚ) * (smallSumQ 15 (2 - b) + smallSumQ 14 (2 + a)) + 68 / 1000000 -
        900 / 100000) * (cosUbQ a) ^ 2 ≤ 136 / 100000) :
      Real.cos (Real.pi * t) ^ 2 *
        ((508 / 10000 : ℝ) *
          ((∑ k ∈ range 15, 1 / ((2 - t + k) ^ 2 - 1 / 4) ^ 2) +
           (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000) ≤
      136 / 100000 + (900 / 100000 : ℝ) * Real.cos (Real.pi * t) ^ 2 := by
    have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
    have hbR : (b : ℝ) ≤ 1 / 2 := by
      have h := Rat.cast_le (K := ℝ).mpr h2; push_cast at h; exact h
    have hA := smallSum_antitone 15 ((2 - b : ℚ) : ℝ) (2 - t) (by push_cast; linarith) (by push_cast; linarith)
    have hB := smallSum_antitone 14 ((2 + a : ℚ) : ℝ) (2 + t) (by push_cast; linarith) (by push_cast; linarith)
    rw [smallSum_cast] at hA hB
    set S_hi : ℝ := (508 / 10000 : ℝ) * (((smallSumQ 15 (2 - b) : ℚ) : ℝ) + ((smallSumQ 14 (2 + a) : ℚ) : ℝ)) +
      68 / 1000000
    have hS : (508 / 10000 : ℝ) *
          ((∑ k ∈ range 15, 1 / ((2 - t + k) ^ 2 - 1 / 4) ^ 2) +
           (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ S_hi := by
      dsimp only [S_hi]; linarith
    have hR : (S_hi - 900 / 100000) * ((cosUbQ a : ℚ) : ℝ) ^ 2 ≤ 136 / 100000 := by
      dsimp only [S_hi]
      have h := Rat.cast_le (K := ℝ).mpr hcheck; push_cast at h; exact h
    have hcos := cos_le_cosUbQ a t h1 ha ht1
    have hcs_le : Real.cos (Real.pi * t) ^ 2 ≤ ((cosUbQ a : ℚ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hcos.1 hcos.2 2
    by_cases hpos : 0 ≤ S_hi - 900 / 100000
    · nlinarith [sq_nonneg (Real.cos (Real.pi * t))]
    · nlinarith [sq_nonneg (Real.cos (Real.pi * t))]
  by_cases h1 : t ≤ 1 / 24
  · exact hbox 0 (1 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
  · by_cases h2 : t ≤ 2 / 24
    · exact hbox (1 / 24) (2 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
    · by_cases h3 : t ≤ 3 / 24
      · exact hbox (2 / 24) (3 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
      · by_cases h4 : t ≤ 4 / 24
        · exact hbox (3 / 24) (4 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
        · by_cases h5 : t ≤ 5 / 24
          · exact hbox (4 / 24) (5 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
          · by_cases h6 : t ≤ 6 / 24
            · exact hbox (5 / 24) (6 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
            · by_cases h7 : t ≤ 7 / 24
              · exact hbox (6 / 24) (7 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
              · by_cases h8 : t ≤ 8 / 24
                · exact hbox (7 / 24) (8 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
                · by_cases h9 : t ≤ 9 / 24
                  · exact hbox (8 / 24) (9 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
                  · by_cases h10 : t ≤ 10 / 24
                    · exact hbox (9 / 24) (10 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
                    · by_cases h11 : t ≤ 11 / 24
                      · exact hbox (10 / 24) (11 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
                      · exact hbox (11 / 24) (1 / 2) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)

/-! ### Part 6: Left (`258`) and Right (`204`, 3 shifts) window coverage & main success theorem -/

theorem cos_sq_eq_abs_round (c : ℝ) :
    Real.cos (Real.pi * c) ^ 2 = Real.cos (Real.pi * |c - round c|) ^ 2 := by
  have h1 : Real.pi * c = Real.pi * (c - round c) + (round c : ℝ) * Real.pi := by ring
  have hsq : ((-1 : ℝ) ^ round c) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num
  rw [h1, Real.cos_add_int_mul_pi, mul_pow, hsq, one_mul]
  rcases le_or_gt 0 (c - round c) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, mul_neg, Real.cos_neg]

/-- Left axis (`L = 258`, `4 * r < 2^258`): nearest-numerator coverage bound. -/
theorem sine_left_mass_258 (r n : ℕ) (hn0 : 0 < n) (hnr : n < r) (hrN : 4 * r < 2 ^ 258) :
    1 - Real.cos (Real.pi * ((2 ^ 258 : ℕ) : ℝ) * ((n : ℝ) / r)) ^ 2 * (586 / 100000 : ℝ) -
        12 / 1000000 ≤
      ∑ a ∈ range (2 ^ 258),
        if (2 * r * a + 2 ^ 258) / (2 * 2 ^ 258) = n
        then Complex.normSq (sinePhaseAmplitude 258 ((n : ℝ) / r) a) else 0 := by
  set N := 2 ^ 258
  have hr : 0 < r := by omega
  have hN : 0 < N := pow_pos (by decide) 258
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set β : ℝ := (n : ℝ) / r
  set c : ℝ := (N : ℝ) * β
  set L : ℝ := (N : ℝ) / (2 * r)
  have hcr : c * r = N * n := by dsimp only [c, β]; field_simp [hrR.ne']
  have hLr : L * (2 * r) = N := by dsimp only [L]; field_simp [hrR.ne']
  have hL2 : 2 < L := by
    have : 4 * (r : ℝ) < N := by exact_mod_cast hrN
    nlinarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnr' : (n : ℝ) + 1 ≤ r := by exact_mod_cast hnr
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  set m : ℤ := round c
  set σ : ℝ := c - m
  have hσ : |σ| ≤ 1 / 2 := abs_sub_round c
  have hσ1 := (abs_le.mp hσ).1
  have hσ2 := (abs_le.mp hσ).2
  set R1 : ℝ := if 0 ≤ σ then 3 - σ else 2 - σ
  set R2 : ℝ := if 0 ≤ σ then 2 + σ else 3 + σ
  have hR_sum :
      (508 / 10000 : ℝ) *
        ((∑ k ∈ range 14, 1 / ((R1 + k) ^ 2 - 1 / 4) ^ 2) +
         (∑ k ∈ range 14, 1 / ((R2 + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ 586 / 100000 := by
    by_cases hs : 0 ≤ σ
    · simp only [R1, R2, if_pos hs]
      exact left_box_sum σ hs hσ2
    · simp only [R1, R2, if_neg hs]
      have hL := left_box_sum (-σ) (by linarith) (by linarith)
      have he1 : 3 - -σ = 3 + σ := by ring
      have he2 : 2 + -σ = 2 - σ := by ring
      rw [he1, he2, add_comm (∑ k ∈ range 14, 1 / ((3 + σ + ↑k) ^ 2 - 1 / 4) ^ 2)] at hL
      exact hL
  have hcirc := sine_circular_mass_two 258 (by decide) β R1 R2 14 14
    (by unfold R1; split_ifs <;> linarith)
    (by unfold R2; split_ifs <;> linarith)
    (by unfold R1; push_cast; split_ifs <;> linarith)
    (by unfold R2; push_cast; split_ifs <;> linarith)
    (by unfold R1; push_cast; split_ifs <;> linarith)
    (by unfold R2; push_cast; split_ifs <;> linarith)
  have hweak :
      1 - Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (586 / 100000 : ℝ) - 12 / 1000000 ≤
      ∑ a ∈ range N,
        if phiR N c a < R1 ∨ phiL N c a < R2
        then Complex.normSq (sinePhaseAmplitude 258 β a) else 0 := by
    have hm := mul_le_mul_of_nonneg_left hR_sum (sq_nonneg (Real.cos (Real.pi * (N : ℝ) * β)))
    change 1 - Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * _ - _ ≤
      ∑ a ∈ range N, if phiR N c a < R1 ∨ phiL N c a < R2
      then Complex.normSq (sinePhaseAmplitude 258 β a) else 0 at hcirc
    linarith
  refine hweak.trans (Finset.sum_le_sum (fun a ha => ?_))
  have haN : (a : ℝ) < N := by exact_mod_cast (mem_range.mp ha)
  have hgood : (phiR N c a < R1 ∨ phiL N c a < R2) → (2 * r * a + N) / (2 * N) = n := by
    intro hnear
    by_contra hbad
    rcases window_cases r N n a hN hbad with h | h
    · have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
      have hca : c + L ≤ (a : ℝ) := by nlinarith
      have hpr : R1 ≤ phiR N c a := by
        unfold phiR
        rw [if_pos (by linarith)]
        by_cases hs : 0 ≤ σ
        · simp only [R1, if_pos hs]
          have hgt : (m : ℝ) + 2 < (a : ℝ) := by linarith
          have hZ : m + 2 < (a : ℤ) := by exact_mod_cast hgt
          have hZ' : (m : ℝ) + 3 ≤ (a : ℝ) := by exact_mod_cast (show m + 3 ≤ (a : ℤ) by omega)
          linarith
        · simp only [R1, if_neg hs]
          have hgt : (m : ℝ) + 1 < (a : ℝ) := by linarith
          have hZ : m + 1 < (a : ℤ) := by exact_mod_cast hgt
          have hZ' : (m : ℝ) + 2 ≤ (a : ℝ) := by exact_mod_cast (show m + 2 ≤ (a : ℤ) by omega)
          linarith
      have hpl : R2 ≤ phiL N c a := by
        unfold phiL
        rw [if_neg (by linarith)]
        unfold R2; split_ifs <;> linarith
      rcases hnear with hn | hn <;> linarith
    · have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
      have hca : (a : ℝ) < c - L := by nlinarith
      have hpl : R2 ≤ phiL N c a := by
        unfold phiL
        rw [if_pos (by linarith)]
        by_cases hs : 0 ≤ σ
        · simp only [R2, if_pos hs]
          have hlt : (a : ℝ) < (m : ℝ) - 1 := by linarith
          have hZ : (a : ℤ) < m - 1 := by exact_mod_cast hlt
          have hZ' : (a : ℝ) ≤ (m : ℝ) - 2 := by exact_mod_cast (show (a : ℤ) ≤ m - 2 by omega)
          linarith
        · simp only [R2, if_neg hs]
          have hlt : (a : ℝ) < (m : ℝ) - 2 := by linarith
          have hZ : (a : ℤ) < m - 2 := by exact_mod_cast hlt
          have hZ' : (a : ℝ) ≤ (m : ℝ) - 3 := by exact_mod_cast (show (a : ℤ) ≤ m - 3 by omega)
          linarith
      have hpr : R1 ≤ phiR N c a := by
        unfold phiR
        rw [if_neg (by linarith)]
        unfold R1; split_ifs <;> linarith
      rcases hnear with hn | hn <;> linarith
  split_ifs with hn hg
  · exact le_rfl
  · exact (hg (hgood hn)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- Modular 204-bit neighbour word `b + j (mod 2^204)`. -/
def neighborWord204 (b : ℕ) (j : ℤ) : ℕ := ((((b : ℤ) + j) % (2 ^ 204 : ℕ))).toNat

def rightGood3 (r : ℕ) (k : Fin r) (b : Fin (2 ^ 204)) : Prop :=
  ∃ j : ℤ, -1 ≤ j ∧ j ≤ 1 ∧ neighborWord204 b.val j = (reducedPeak r 204 k).val

theorem neighbor_coverage3 (r : ℕ) (hr : 0 < r) (k : Fin r) (b : Fin (2 ^ 204))
    (hc : phiR (2 ^ 204) (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)) b.val <
        2 - (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r) - round (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r))) ∨
      phiL (2 ^ 204) (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)) b.val <
        2 + (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r) - round (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)))) :
    rightGood3 r k b := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)
  set m : ℤ := round c
  have hround := abs_le.mp (abs_sub_round c)
  have hkr : (k.val : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast k.isLt)
  have hc0 : 0 ≤ c := by positivity
  have hcN : c < ((2 ^ 204 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((2 ^ 204 : ℕ) : ℝ) := by positivity
    dsimp only [c]; nlinarith
  have hb0 : (0 : ℝ) ≤ (b.val : ℝ) := Nat.cast_nonneg _
  have hbN : (b.val : ℝ) < ((2 ^ 204 : ℕ) : ℝ) := by exact_mod_cast b.isLt
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℤ, (-2 : ℝ) < (m : ℝ) - ((b.val : ℝ) + z * ((2 ^ 204 : ℕ) : ℝ)) ∧
      (m : ℝ) - ((b.val : ℝ) + z * ((2 ^ 204 : ℕ) : ℝ)) < 2 := by
    rcases hc with hc | hc
    · unfold phiR at hc
      split_ifs at hc with h
      · exact ⟨0, by simp only [Int.cast_zero, zero_mul, add_zero]; linarith,
          by simp only [Int.cast_zero, zero_mul, add_zero]; linarith⟩
      · exact ⟨1, by simp only [Int.cast_one, one_mul]; linarith,
          by simp only [Int.cast_one, one_mul]; linarith⟩
    · unfold phiL at hc
      split_ifs at hc with h
      · exact ⟨0, by simp only [Int.cast_zero, zero_mul, add_zero]; linarith,
          by simp only [Int.cast_zero, zero_mul, add_zero]; linarith⟩
      · exact ⟨-1, by simp only [Int.cast_neg, Int.cast_one, neg_one_mul]; linarith,
          by simp only [Int.cast_neg, Int.cast_one, neg_one_mul]; linarith⟩
  set j : ℤ := m - ((b.val : ℤ) + z * ((2 ^ 204 : ℕ) : ℤ))
  have hjR : (j : ℝ) = (m : ℝ) - ((b.val : ℝ) + z * ((2 ^ 204 : ℕ) : ℝ)) := by
    dsimp only [j]; push_cast; ring
  have hj1 : (-2 : ℤ) < j := by exact_mod_cast (show (-2 : ℝ) < (j : ℝ) by rw [hjR]; exact hz1)
  have hj2 : j < 2 := by exact_mod_cast (show (j : ℝ) < 2 by rw [hjR]; exact hz2)
  refine ⟨j, by omega, by omega, ?_⟩
  have he : m = (reducedPeakRaw r 204 k : ℤ) := by
    have hc' : c = ((2 ^ 204 * k.val : ℕ) : ℝ) / r := by dsimp only [c]; push_cast; ring
    rw [show m = round c from rfl, hc', ShorECDLP.Entrant.RoundedReadout.round_nat_ratio _ r hr]
    simp only [reducedPeakRaw, Nat.mul_assoc]
  have hmod : (reducedPeakRaw r 204 k : ℤ) % (2 ^ 204 : ℕ) = ((b.val : ℤ) + j) % (2 ^ 204 : ℕ) := by
    rw [← he]
    dsimp only [j]
    rw [show (b.val : ℤ) + (m - ((b.val : ℤ) + z * ((2 ^ 204 : ℕ) : ℤ))) =
      m + (-z) * ((2 ^ 204 : ℕ) : ℤ) by ring, Int.add_mul_emod_self_right]
  have ht := congrArg Int.toNat hmod
  simpa only [neighborWord204, reducedPeak, ← Int.natCast_mod, Int.toNat_natCast] using ht.symm

def sineRightMass3 (r : ℕ) (k : Fin r) : ℝ := by
  classical
  exact ∑ b : Fin (2 ^ 204), if rightGood3 r k b then
    Complex.normSq (sinePhaseAmplitude 204 ((k.val : ℝ) / r) b.val) else 0

theorem sine_right_mass_204 (r : ℕ) (hr : 0 < r) (k : Fin r) :
    1 - 136 / 100000 - (900 / 100000 : ℝ) * Real.cos (Real.pi * ((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2 -
        12 / 1000000 ≤ sineRightMass3 r k := by
  classical
  set β : ℝ := (k.val : ℝ) / r
  set c : ℝ := ((2 ^ 204 : ℕ) : ℝ) * β
  set σ : ℝ := c - round c
  have hσ := abs_le.mp (abs_sub_round c)
  have hcos_eq : Real.cos (Real.pi * ((2 ^ 204 : ℕ) : ℝ) * β) ^ 2 = Real.cos (Real.pi * |σ|) ^ 2 := by
    rw [mul_assoc]; exact cos_sq_eq_abs_round c
  have hstep :
      1 - 136 / 100000 - (900 / 100000 : ℝ) * Real.cos (Real.pi * ((2 ^ 204 : ℕ) : ℝ) * β) ^ 2 -
        12 / 1000000 ≤
      ∑ b ∈ range (2 ^ 204),
        if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b) else 0 := by
    by_cases hs : 0 ≤ σ
    · have hcirc := sine_circular_mass_two 204 (by decide) β (2 - σ) (2 + σ) 15 14
        (by linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      have hbox := right_box_bound σ hs hσ.2
      rw [hcos_eq, abs_of_nonneg hs] at hcirc ⊢
      change _ ≤ ∑ b ∈ range (2 ^ 204),
        if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b) else 0 at hcirc
      linarith
    · have hcirc := sine_circular_mass_two 204 (by decide) β (2 - σ) (2 + σ) 14 15
        (by linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      have hbox := right_box_bound (-σ) (by linarith) (by linarith)
      rw [hcos_eq, abs_of_neg (lt_of_not_ge hs)] at hcirc ⊢
      have he1 : 2 - -σ = 2 + σ := by ring
      have he2 : 2 + -σ = 2 - σ := by ring
      rw [he1, he2, add_comm (∑ k ∈ range 15, 1 / ((2 + σ + ↑k) ^ 2 - 1 / 4) ^ 2)] at hbox
      change _ ≤ ∑ b ∈ range (2 ^ 204),
        if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b) else 0 at hcirc
      linarith
  have hfin :
      ∑ b ∈ range (2 ^ 204),
        (if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b) else 0) =
      ∑ b : Fin (2 ^ 204),
        if phiR (2 ^ 204) c b.val < 2 - σ ∨ phiL (2 ^ 204) c b.val < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b.val) else 0 :=
    (Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
      then Complex.normSq (sinePhaseAmplitude 204 β b) else 0) (2 ^ 204)).symm
  rw [hfin] at hstep
  refine hstep.trans (Finset.sum_le_sum (fun b _ => ?_))
  dsimp only [sineRightMass3]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage3 r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

def params258 : DecoderParams := ⟨258, 204, by decide, by decide, by decide, by decide⟩

def pairRecovered258 (d a b : ℕ) : Bool :=
  decide (∃ i : Fin 3, (d : ZMod order) ∈ fixedCandidates params258 a (neighborWord204 b ((i.val : ℤ) - 1)))

theorem pairRecovered258_of_character (d : ℕ) (k : Fin order) (hk : k.val ≠ 0)
    (a : Fin (2 ^ 258)) (b : Fin (2 ^ 204))
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 258 a.val = k.val)
    (hb : rightGood3 order ⟨d * k.val % order, Nat.mod_lt _ order_prime.pos⟩ b) :
    pairRecovered258 d a.val b.val = true := by
  classical
  obtain ⟨j, hlo, hhi, hj⟩ := hb
  let i : Fin 3 := ⟨(j + 1).toNat, by omega⟩
  have hi : (i.val : ℤ) - 1 = j := by dsimp [i]; omega
  haveI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have hk0 : ((k.val : ℕ) : ZMod order) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
  apply decide_eq_true
  refine ⟨i, ?_⟩
  rw [hi]
  unfold fixedCandidates
  apply Finset.mem_image.mpr
  refine ⟨d * k.val % order, ?_, ?_⟩
  · change d * k.val % order ∈ wrappedNumeratorCandidates order 204 (neighborWord204 b.val j)
    rw [hj]
    exact reducedPeak_mem_candidates order 204 _
  · change ((d * k.val % order : ℕ) : ZMod order) *
        (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 258 a.val : ZMod order)⁻¹ = d
    rw [ha]
    simp only [ZMod.natCast_mod, Nat.cast_mul]
    field_simp

theorem precision258 : 4 * order < 2 ^ 258 := by norm_num [order]

theorem order_not_dvd_pow2 (k : ℕ) : ¬ order ∣ 2 ^ k := by
  intro h
  have h2 := order_prime.dvd_of_dvd_pow h
  have hlt : 2 < order := by norm_num [order]
  exact (Nat.le_of_dvd (by decide) h2).not_gt hlt

theorem order_not_dvd_of_ne_zero (Q : Point) (d : ℕ) (hn : Q ≠ 0) (hd : Q = d • G) :
    ¬ order ∣ d := by
  rintro ⟨m, rfl⟩
  apply hn
  rw [hd, mul_comm, mul_smul, generator_nsmul_eq_zero, nsmul_zero]

/-- Main ideal recovery lower bound (`≥ 9911 / 10000`) for the 10-bit sine-windowed `(258, 204, K=3)` circuit. -/
theorem sine_pair_success (Q : Point) (d : ℕ) (hn : Q ≠ 0) (hd : Q = d • G) :
    (9911 / 10000 : ℝ) ≤ ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204),
      if pairRecovered258 d a.val b.val then sinePairMass order 258 204 d (a, b) else 0 := by
  classical
  let r := order
  have hr : r.Prime := order_prime
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hrinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  let A : Fin r → Fin (2 ^ 258) → ℝ := fun k a =>
    Complex.normSq (sinePhaseAmplitude 258 ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2 ^ 204) → ℝ := fun k b =>
    Complex.normSq (sinePhaseAmplitude 204 (((d * k.val % r : ℕ) : ℝ) / r) b.val)
  let good : Fin r → Fin (2 ^ 258) → Fin (2 ^ 204) → Prop := fun k a b =>
    k.val ≠ 0 ∧ ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a.val = k.val ∧
      rightGood3 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b
  let F : Fin r → Fin (2 ^ 258) → Fin (2 ^ 204) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let cL : Fin r → ℝ := fun k => Real.cos (Real.pi * ((2 ^ 258 : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let cR : Fin r → ℝ := fun k =>
    Real.cos (Real.pi * ((2 ^ 204 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2
  have step1 :
      ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204),
          if pairRecovered258 d a.val b.val then sinePairMass r 258 204 d (a, b) else 0 := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    by_cases hp : pairRecovered258 d a.val b.val = true
    · rw [if_pos hp]
      unfold sinePairMass
      apply mul_le_mul_of_nonneg_left _ hrinv
      apply Finset.sum_le_sum; intro k _
      dsimp only [F, A, B]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    · rw [if_neg hp]
      have hz : ∀ k, F k a b = 0 := by
        intro k; dsimp only [F]; rw [if_neg]
        rintro ⟨hk, ha, hb⟩
        exact hp (pairRecovered258_of_character d k hk a b ha hb)
      simp [hz]
  have step2 :
      (r : ℝ)⁻¹ * ∑ k : Fin r, ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), F k a b =
        ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
  have step3 (k : Fin r) :
      (if k.val = 0 then (0 : ℝ) else (1 - 24 / 1000000 - 136 / 100000 : ℝ)) -
        cL k * (586 / 100000) - cR k * (900 / 100000) ≤
      ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), F k a b := by
    have hcL0 : 0 ≤ cL k := sq_nonneg _
    have hcR0 : 0 ≤ cR k := sq_nonneg _
    have hcL1 : cL k ≤ 1 := Real.cos_sq_le_one _
    have hcR1 : cR k ≤ 1 := Real.cos_sq_le_one _
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), F k a b :=
        Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => by
          dsimp only [F, A, B]; split_ifs
          · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
          · exact le_rfl))
      linarith
    · rw [if_neg hk]
      have he : (∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), F k a b) =
          (∑ a : Fin (2 ^ 258), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a.val = k.val then A k a else 0) *
            sineRightMass3 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ := by
        rw [sineRightMass3, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        dsimp only [F, good, B]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [he]
      have hleft : 1 - cL k * (586 / 100000) - 12 / 1000000 ≤
          ∑ a : Fin (2 ^ 258), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a.val = k.val then A k a else 0 := by
        have h := sine_left_mass_258 r k.val (Nat.pos_of_ne_zero hk) k.isLt precision258
        dsimp only [A, cL]
        rw [Fin.sum_univ_eq_sum_range (fun a => if ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a = k.val then
          Complex.normSq (sinePhaseAmplitude 258 ((k.val : ℝ) / r) a) else 0) (2 ^ 258)]
        simpa only [ShorECDLP.Quantum.OrderFinding.nearestNumerator] using h
      have hright : 1 - (136 / 100000 + cR k * (900 / 100000)) - 12 / 1000000 ≤
          sineRightMass3 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ := by
        have h := sine_right_mass_204 r hr.pos ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩
        dsimp only [cR]; linarith
      have hp := prod_lower
        (∑ a : Fin (2 ^ 258), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a.val = k.val then A k a else 0)
        (sineRightMass3 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩)
        (cL k * (586 / 100000)) (136 / 100000 + cR k * (900 / 100000))
        (12 / 1000000)
        (mul_nonneg hcL0 (by norm_num))
        (by linarith [hcR0])
        (by norm_num)
        hleft hright (by linarith [hcL1]) (by linarith [hcR1])
      linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  have hcount : (∑ k : Fin r, if k.val = 0 then (0 : ℝ) else (1 - 24 / 1000000 - 136 / 100000 : ℝ)) =
      ((r : ℝ) - 1) * (1 - 24 / 1000000 - 136 / 100000) := by
    have hz : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
      simp [hr.pos]
    calc
      _ = ∑ k : Fin r, ((1 - 24 / 1000000 - 136 / 100000 : ℝ) -
            (1 - 24 / 1000000 - 136 / 100000) * (if k.val = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro k _; split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcount, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  have hcL_sum : ∑ k : Fin r, cL k = (r : ℝ) / 2 := by
    have h := sum_cos_sq_eq r (2 ^ 258) hr.pos (order_not_dvd_pow2 258)
    simpa only [cL, mul_div_assoc] using h
  have hcR_sum : ∑ k : Fin r, cR k = (r : ℝ) / 2 := by
    have hndvd : ¬ r ∣ 2 ^ 204 * d := by
      intro h
      rcases hr.dvd_mul.mp h with h1 | h2
      · exact order_not_dvd_pow2 204 h1
      · exact order_not_dvd_of_ne_zero Q d hn hd h2
    have h := sum_cos_sq_eq r (2 ^ 204 * d) hr.pos hndvd
    rw [← h]
    apply Finset.sum_congr rfl; intro k _
    dsimp only [cR]
    rw [← mul_div_assoc, cos_sq_mod r (2 ^ 204) (d * k.val) hr.pos]
    have harg : Real.pi * ((2 ^ 204 * d : ℕ) : ℝ) * (k.val : ℝ) / (r : ℝ) =
        Real.pi * ((2 ^ 204 : ℕ) : ℝ) * ((d * k.val : ℕ) : ℝ) / (r : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul]; ring
    rw [harg]
  rw [hcL_sum, hcR_sum] at hsum
  have hlower := mul_le_mul_of_nonneg_left hsum hrinv
  have heval : (r : ℝ)⁻¹ * (((r : ℝ) - 1) * (1 - 24 / 1000000 - 136 / 100000) -
      (r : ℝ) / 2 * (586 / 100000) - (r : ℝ) / 2 * (900 / 100000)) =
      (1 - 1 / (r : ℝ)) * (1 - 24 / 1000000 - 136 / 100000) - 586 / 200000 - 900 / 200000 := by
    field_simp [hrR.ne']; ring
  rw [heval, step2] at hlower
  have hrbig_nat : 1000000 ≤ r := by dsimp only [r]; norm_num [order]
  have hrbig : (1000000 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrbig_nat
  have hinv : 1 / (r : ℝ) ≤ (1 : ℝ) / 1000000 := one_div_le_one_div_of_le (by norm_num) hrbig
  have hnum : (9911 / 10000 : ℝ) ≤ (1 - 1 / (r : ℝ)) * (1 - 24 / 1000000 - 136 / 100000) -
      586 / 200000 - 900 / 200000 := by linarith
  exact hnum.trans (hlower.trans step1)

theorem decoder_budget258 : 3 * (2 * (order / 2 ^ 204 + 2)) ≤ 56 * (2 ^ 49 + 2) := by
  norm_num [order]

#print axioms sine_pair_success
#print axioms decoder_budget258

end
end ShorECDLP.Entrant.SineBounds
