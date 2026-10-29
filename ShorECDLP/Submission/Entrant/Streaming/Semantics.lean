import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedVerified
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Submission.«2607_13816».Window.StreamHistory
import ShorECDLP.Framework.Quantum.TerminalInterference
import ShorECDLP.Submission.«2607_13816».Window.StreamKernel
import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows
import ShorECDLP.Submission.«2607_13816».Window.RawDistribution
import ShorECDLP.Submission.«2607_13816».Window.Repetition
import ShorECDLP.Framework.Quantum.AdaptiveFrame
import ShorECDLP.Submission.«2607_13816».Window.Uniform
import ShorECDLP.Submission.«2607_13816».Window.StreamSamplingSuccess

/-! EDITABLE. Streaming entrant, module `Semantics`: physical execution of the compiled rounds and the per-round success bound.

This module concatenates the former per-file modules `AveragedSuccess`, `BatchBoundary`,
`BatchedWindowState`, `BatchedWindowCoherent`, `PreparedBatch`, `ActualWindow`,
`WindowPhysical`, `ModularPhysical`, `EEACenterPhysical`, `EEAStructuralPhysical`,
`EEAIntervalPhysical`, `MeasuredEEAPhysical`, `SquarePhysical`, `InPlacePhysical`,
`InPlaceCompletePhysical`, `CoordinatePhysical`, `ActualPhysical`, `HistoryExecution`,
`OuterExecution`, `ActualExecution`, `SourceAxis`, `TaggedProbability`, `WindowValidity`,
`AxisProbability`, `FirstValidity`, `CrossWindowWeights`, `CrossWindowPoint`,
`TwoAxisProbability`, `FixedWord`, `TaggedAxis`, `TaggedTwoAxes`, `ActualPair`, `DecoderBridge`,
`RoundBoundary`, `WindowBranchSum`, `IdealDistribution` (in this order). Each former file is one
`namespace` block below, marked `-- ==== part: <Name> ====`, with its provenance note. Only the
import lines changed. Dropped because an identical private copy occurs earlier in this module:
`FirstValidity.support_add`, `FirstValidity.support_smul`. Renamed because an earlier part has a
different private lemma of the same name: `support_linear` to `support_linear_firstValidity`.

Why few modules: the kernel replay loads the complete import closure (about 4.3 GB) once per
Entrant module, in parallel across its worker threads, so its peak memory grows with the number
of Entrant modules. -/

-- ==== part: AveragedSuccess ====

/-! EDITABLE. An averaged per-round success bound for the reduced two-axis decoder.

The protected bound `reducedVerifiedMass_lower` keeps, for every nonzero character `k`, only the
mass at the nearest Fourier pair and bounds each axis by the worst case `4/π²`, which gives
`((r-1)/r)(4/π²)² ≈ 0.164`. Here the same peak outputs are used, but the two axis probabilities
are averaged over `k` instead of bounded pointwise:

* each axis probability at its nearest bin is at least `sinc²(t)`, where `t ∈ [-1/2, 1/2]` is the
  signed distance (in bins) to that bin, and `sinc²(t) ≥ 1 - x²/3 + 2x⁴/45 - x⁶/315` with
  `x = πt` (from the eighth-order Taylor upper bound of `cos`, proved by derivative comparison);
* since `r` is an odd prime, `k ↦ 2ⁿk mod r` and `k ↦ 2ᵐdk mod r` are bijections of `ℤ/r`, so
  the bin distances of both axes run exactly over the grid `{s/r : |s| ≤ (r-1)/2}`; the grid
  average of the polynomial is a closed form in `r` (power sums of degree 2, 4, 6);
* `xy ≥ x + y - 1` on `[0,1]²` joins the two axes.

For a prime `r ≥ 10⁶` this gives at least `27/50` per round, for every nonzero `d`. -/

namespace ShorECDLP.Entrant.Averaged
open Real ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators

noncomputable section

/-! ### Taylor bounds for `sin` and `cos` -/

/-- Comparison on `[0, ∞)` by derivatives. -/
theorem le_of_deriv_le {f g f' g' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (h0 : f 0 = g 0) (hd : ∀ x, 0 ≤ x → f' x ≤ g' x) {x : ℝ} (hx : 0 ≤ x) : f x ≤ g x := by
  have hmono : MonotoneOn (fun y => g y - f y) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => g' y - f' y) (convex_Ici 0)
    · exact (continuous_iff_continuousAt.2 fun y => ((hg y).sub (hf y)).continuousAt).continuousOn
    · intro y _
      exact ((hg y).sub (hf y)).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact sub_nonneg.2 (hd y (le_of_lt hy))
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [h0, sub_self] at h
  linarith

theorem sin_ge3 {x : ℝ} (hx : 0 ≤ x) : x - x^3/6 ≤ sin x :=
  le_of_deriv_le (f := fun y => y - y^3/6) (f' := fun y => 1 - y^2/2)
    (fun y => by
      refine ((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).congr_deriv ?_
      norm_num; ring)
    hasDerivAt_sin (by simp) (fun _ _ => one_sub_sq_div_two_le_cos) hx

theorem cos_le4 {x : ℝ} (hx : 0 ≤ x) : cos x ≤ 1 - x^2/2 + x^4/24 :=
  le_of_deriv_le (g := fun y => 1 - y^2/2 + y^4/24) (g' := fun y => -y + y^3/6)
    hasDerivAt_cos
    (fun y => by
      refine (((hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 4 y).div_const 24)).congr_deriv ?_
      norm_num; ring)
    (by simp) (fun y hy => by have := sin_ge3 hy; linarith) hx

theorem sin_le5 {x : ℝ} (hx : 0 ≤ x) : sin x ≤ x - x^3/6 + x^5/120 :=
  le_of_deriv_le (g := fun y => y - y^3/6 + y^5/120) (g' := fun y => 1 - y^2/2 + y^4/24)
    hasDerivAt_sin
    (fun y => by
      refine (((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
        ((hasDerivAt_pow 5 y).div_const 120)).congr_deriv ?_
      norm_num; ring)
    (by simp) (fun _ hy => cos_le4 hy) hx

theorem cos_ge6 {x : ℝ} (hx : 0 ≤ x) : 1 - x^2/2 + x^4/24 - x^6/720 ≤ cos x :=
  le_of_deriv_le (f := fun y => 1 - y^2/2 + y^4/24 - y^6/720)
    (f' := fun y => -y + y^3/6 - y^5/120)
    (fun y => by
      refine ((((hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 4 y).div_const 24)).sub
        ((hasDerivAt_pow 6 y).div_const 720)).congr_deriv ?_
      norm_num; ring)
    hasDerivAt_cos (by simp) (fun y hy => by have := sin_le5 hy; linarith) hx

theorem sin_ge7 {x : ℝ} (hx : 0 ≤ x) : x - x^3/6 + x^5/120 - x^7/5040 ≤ sin x :=
  le_of_deriv_le (f := fun y => y - y^3/6 + y^5/120 - y^7/5040)
    (f' := fun y => 1 - y^2/2 + y^4/24 - y^6/720)
    (fun y => by
      refine ((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
        ((hasDerivAt_pow 5 y).div_const 120)).sub
        ((hasDerivAt_pow 7 y).div_const 5040)).congr_deriv ?_
      norm_num; ring)
    hasDerivAt_sin (by simp) (fun _ hy => cos_ge6 hy) hx

theorem cos_le8_nonneg {x : ℝ} (hx : 0 ≤ x) :
    cos x ≤ 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 :=
  le_of_deriv_le (g := fun y => 1 - y^2/2 + y^4/24 - y^6/720 + y^8/40320)
    (g' := fun y => -y + y^3/6 - y^5/120 + y^7/5040)
    hasDerivAt_cos
    (fun y => by
      refine (((((hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 4 y).div_const 24)).sub
        ((hasDerivAt_pow 6 y).div_const 720)).add
        ((hasDerivAt_pow 8 y).div_const 40320)).congr_deriv ?_
      norm_num; ring)
    (by simp) (fun y hy => by have := sin_ge7 hy; linarith) hx

theorem cos_le8 (x : ℝ) : cos x ≤ 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 := by
  rcases le_total 0 x with hx | hx
  · exact cos_le8_nonneg hx
  · calc cos x = cos (-x) := (cos_neg x).symm
      _ ≤ 1 - (-x)^2/2 + (-x)^4/24 - (-x)^6/720 + (-x)^8/40320 := cos_le8_nonneg (by linarith)
      _ = 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 := by ring

/-- The even polynomial lower bound of `sinc²`, as a function of `x²`. -/
def sincPoly (y : ℝ) : ℝ := 1 - y/3 + 2*y^2/45 - y^3/315

theorem sq_mul_sincPoly_le (x : ℝ) : x^2 * sincPoly (x^2) ≤ sin x ^ 2 := by
  rw [sin_sq_eq_half_sub]
  have h := cos_le8 (2*x)
  have e : 1/2 - (1 - (2*x)^2/2 + (2*x)^4/24 - (2*x)^6/720 + (2*x)^8/40320)/2 =
      x^2 * sincPoly (x^2) := by
    unfold sincPoly; ring
  linarith

/-! ### One Fourier axis -/

private theorem norm_eigenvalue_sub_one' (delta : ℝ) :
    ‖eigenvalue delta - 1‖ = ‖2 * Real.sin (Real.pi * delta)‖ := by
  unfold eigenvalue
  convert Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * delta) using 1 ; ring_nf

private theorem norm_eigenvalue_pow_sub_one' (N : Nat) (delta : ℝ) :
    ‖eigenvalue delta ^ N - 1‖ = ‖2 * Real.sin (Real.pi * (N : ℝ) * delta)‖ := by
  rw [eigenvalue_pow_eq_eigenvalue_mul]
  convert norm_eigenvalue_sub_one' ((N : ℝ) * delta) using 1 ; ring_nf

/-- The normalized geometric average is at least `sincPoly ((π N δ)²)`, for every `δ`. -/
theorem average_normSq_ge (N : Nat) (hN : 0 < N) (delta : ℝ) :
    sincPoly ((Real.pi * N * delta)^2) ≤
      Complex.normSq (((N:ℂ)⁻¹) * ∑ y ∈ Finset.range N, eigenvalue delta ^ y) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  by_cases hdelta : delta = 0
  · subst hdelta
    have hsum : (∑ y ∈ Finset.range N, eigenvalue 0 ^ y) = (N:ℂ) := by simp [eigenvalue]
    rw [hsum, inv_mul_cancel₀ (by exact_mod_cast hN.ne')]
    simp [sincPoly]
  · set S := ∑ y ∈ Finset.range N, eigenvalue delta ^ y with hS
    have hgeom : S * (eigenvalue delta - 1) = eigenvalue delta ^ N - 1 := geom_sum_mul _ N
    have hn : ‖S‖ * ‖eigenvalue delta - 1‖ = ‖eigenvalue delta ^ N - 1‖ := by
      rw [← norm_mul, hgeom]
    rw [norm_eigenvalue_sub_one', norm_eigenvalue_pow_sub_one', Real.norm_eq_abs,
      Real.norm_eq_abs] at hn
    have hsq : ‖S‖^2 * Real.sin (Real.pi * delta)^2 = Real.sin (Real.pi * N * delta)^2 := by
      have h2 := congrArg (fun t : ℝ => t^2) hn
      simp only [mul_pow, sq_abs] at h2
      linarith
    set X := Real.pi * N * delta with hX
    have hX0 : X ≠ 0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero hNR.ne') hdelta
    have h1 := sq_mul_sincPoly_le X
    have h2 : Real.sin (Real.pi * delta)^2 ≤ (Real.pi * delta)^2 := sin_sq_le_sq
    have hpd : (Real.pi * delta)^2 = X^2 / (N:ℝ)^2 := by
      rw [hX]; field_simp
    have h3 : X^2 * sincPoly (X^2) ≤ X^2 * (‖S‖^2 / (N:ℝ)^2) := by
      calc X^2 * sincPoly (X^2) ≤ Real.sin X ^ 2 := h1
        _ = ‖S‖^2 * Real.sin (Real.pi * delta)^2 := hsq.symm
        _ ≤ ‖S‖^2 * (Real.pi * delta)^2 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = X^2 * (‖S‖^2 / (N:ℝ)^2) := by rw [hpd]; ring
    have hnorm : Complex.normSq ((N:ℂ)⁻¹ * S) = ‖S‖^2 / (N:ℝ)^2 := by
      rw [Complex.normSq_eq_norm_sq, norm_mul, norm_inv, Complex.norm_natCast]
      field_simp
    rw [hnorm]
    exact le_of_mul_le_mul_left h3 (by positivity)

/-- Folded grid distance `min(c, r - c)` of a residue `c < r`. -/
def foldDist (r c : Nat) : Nat := if 2*c < r then c else r - c

/-- The nearest-bin probability for numerator `j/r` at `2^p` bins, in grid form. -/
theorem axis_lower (p r j : Nat) (hr : 0 < r) (hodd : r % 2 = 1) :
    sincPoly ((Real.pi * (foldDist r ((2^p*j) % r) : ℝ) / r)^2) ≤
      Complex.normSq (paperPhaseAmplitude p ((j:ℝ)/r) ((2*2^p*j + r)/(2*r))) := by
  unfold paperPhaseAmplitude
  refine le_trans (le_of_eq ?_) (average_normSq_ge (2^p) (by positivity) _)
  congr 1
  set A := 2^p*j with hA
  set q := A / r
  set c := A % r
  have hdm : r * q + c = A := Nat.div_add_mod A r
  have hc : c < r := Nat.mod_lt A hr
  have hv : (2*2^p*j + r)/(2*r) = (2*c + r)/(2*r) + q := by
    have e : 2*2^p*j + r = (2*c + r) + 2*r*q := by rw [mul_assoc, ← hA, ← hdm]; ring
    rw [e, Nat.add_mul_div_left _ _ (by omega : 0 < 2*r)]
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hNR : (0:ℝ) < ((2^p:Nat):ℝ) := by positivity
  have hAR : ((2^p:Nat):ℝ) * (j:ℝ) = (r:ℝ) * q + c := by exact_mod_cast hdm.symm
  unfold foldDist
  by_cases h2c : 2*c < r
  · have hb : (2*c + r)/(2*r) = 0 := Nat.div_eq_of_lt (by omega)
    rw [hv, hb, zero_add, if_pos h2c]
    have e : ((2^p:Nat):ℝ) * ((j:ℝ)/r - (q:ℝ)/((2^p:Nat):ℝ)) = (c:ℝ)/r := by
      field_simp; linarith
    rw [mul_assoc, e]; ring
  · have hb : (2*c + r)/(2*r) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hv, hb, if_neg h2c, Nat.cast_sub hc.le]
    push_cast
    have e : ((2^p:Nat):ℝ) * ((j:ℝ)/r - ((1:ℝ) + q)/((2^p:Nat):ℝ)) = ((c:ℝ) - r)/r := by
      field_simp; linarith
    push_cast at e
    rw [mul_assoc, e]; ring

private theorem eigenvalue_period' (phase : ℝ) : eigenvalue (phase-1)=eigenvalue phase := by
  unfold eigenvalue
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-1, ?_⟩
  push_cast
  ring

private theorem amplitude_endpoint' (precision : Nat) (phase : ℝ) :
    paperPhaseAmplitude precision phase (2^precision) = paperPhaseAmplitude precision phase 0 := by
  unfold paperPhaseAmplitude
  simp only [Nat.cast_zero, zero_div, sub_zero]
  have hN : ((2^precision:Nat):ℝ) ≠ 0 := by positivity
  simp only [div_self hN, eigenvalue_period']

/-- The wrapped second-axis peak has the same amplitude as its unwrapped rounding. -/
theorem reducedPeak_amplitude (r precision : Nat) (k : Fin r) (phase : ℝ) :
    paperPhaseAmplitude precision phase (reducedPeak r precision k).val =
      paperPhaseAmplitude precision phase (reducedPeakRaw r precision k) := by
  have hle := reducedPeakRaw_le r precision k
  by_cases heq : reducedPeakRaw r precision k = 2^precision
  · simp only [reducedPeak, heq, Nat.mod_self, amplitude_endpoint']
  · simp only [reducedPeak,
      Nat.mod_eq_of_lt (by omega : reducedPeakRaw r precision k < 2^precision)]

/-! ### Grid averages -/

/-- Multiplication by a unit permutes the residues. -/
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

/-- Folding the residues `0, …, 2M` onto `0, …, M`. -/
theorem sum_fold (M : Nat) (F : ℕ → ℝ) :
    ∑ c ∈ Finset.range (2*M+1), F (foldDist (2*M+1) c) =
      2 * ∑ s ∈ Finset.range (M+1), F s - F 0 := by
  rw [show 2*M+1 = (M+1) + M by ring, Finset.sum_range_add]
  have h1 : ∑ c ∈ Finset.range (M+1), F (foldDist (M+1+M) c) = ∑ c ∈ Finset.range (M+1), F c := by
    apply Finset.sum_congr rfl
    intro c hc
    have := Finset.mem_range.1 hc
    unfold foldDist
    rw [if_pos (by omega)]
  have h2 : ∑ x ∈ Finset.range M, F (foldDist (M+1+M) (M+1+x)) =
      ∑ x ∈ Finset.range M, F (x+1) := by
    rw [← Finset.sum_range_reflect (fun x => F (x+1)) M]
    apply Finset.sum_congr rfl
    intro x hx
    have := Finset.mem_range.1 hx
    unfold foldDist
    rw [if_neg (by omega)]
    congr 1
    omega
  rw [h1, h2, Finset.sum_range_succ' F M]
  ring

/-- Closed form of the polynomial summed over `s = 0, …, m` at `a·s²`. -/
def closedForm (m a : ℝ) : ℝ :=
  (m+1) - a/3 * (m*(m+1)*(2*m+1)/6)
    + 2*a^2/45 * (m*(m+1)*(2*m+1)*(3*m^2+3*m-1)/30)
    - a^3/315 * (m*(m+1)*(2*m+1)*(3*m^4+6*m^3-3*m+1)/42)

theorem sum_sincPoly (M : Nat) (a : ℝ) :
    ∑ s ∈ Finset.range (M+1), sincPoly (a * (s:ℝ)^2) = closedForm M a := by
  induction M with
  | zero => simp [closedForm, sincPoly]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    unfold closedForm sincPoly
    push_cast
    ring

/-- The terms of the grid average below `1 - 1/r`, written in `w = a·m(m+1) ≈ π²/4`. -/
def gridDeficit (a w : ℝ) : ℝ :=
  (2/9)*w - (4/675)*(3*w^2 - a*w) + (2/6615)*(3*w^3 - 3*a*w^2 + a^2*w)

theorem closedForm_identity (m a : ℝ) :
    2*(2*closedForm m a - 1) - (2*m+1) - 1 = 2*m - (2*m+1) * gridDeficit a (a*(m*(m+1))) := by
  unfold closedForm gridDeficit
  ring

theorem gridDeficit_le (a w : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1/10^11) (hw1 : w ≤ 2.4675) :
    gridDeficit a w ≤ 0.45373 := by
  unfold gridDeficit
  have hg : (2/9)*w - (4/225)*w^2 + (2/2205)*w^3 ≤ 0.45372 := by
    have hb : 0 ≤ 2/9 - (4/225)*(w + 2.4675) + (2/2205)*(w^2 + w*2.4675 + 2.4675^2) := by
      nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hw1) hb]
  have h1 : a*w ≤ 3/10^11 := by nlinarith
  have h2 : 0 ≤ a*w^2 := by positivity
  have h3 : a^2*w ≤ 3/10^11 := by nlinarith
  nlinarith

/-- The numerical bound at a large odd modulus `r = 2m+1`. -/
theorem averaged_numeric (m : ℝ) (hm : 500000 ≤ m) :
    (27:ℝ)/50 ≤ (1/(2*m+1)) *
      (2*(2*closedForm m (Real.pi^2/(2*m+1)^2) - 1) - (2*m+1) - 1) := by
  rw [closedForm_identity]
  have hr0 : 0 < 2*m+1 := by linarith
  have hpi1 := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hpi2 : Real.pi^2 < 9.8697 := by nlinarith
  have hr2 : (10:ℝ)^12 ≤ (2*m+1)^2 := by nlinarith
  have ha0 : 0 ≤ Real.pi^2/(2*m+1)^2 := by positivity
  have ha1 : Real.pi^2/(2*m+1)^2 ≤ 1/10^11 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hq : m*(m+1) ≤ (2*m+1)^2/4 := by nlinarith
  have hw1 : Real.pi^2/(2*m+1)^2 * (m*(m+1)) ≤ 2.4675 := by
    have h := mul_le_mul_of_nonneg_left hq ha0
    have e : Real.pi^2/(2*m+1)^2 * ((2*m+1)^2/4) = Real.pi^2/4 := by field_simp
    linarith
  have hB := gridDeficit_le _ _ ha0 ha1 hw1
  have hinv : 1/(2*m+1) ≤ 1/1000000 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; linarith
  have e : ∀ B : ℝ, (1/(2*m+1))*(2*m - (2*m+1)*B) = 1 - 1/(2*m+1) - B := by
    intro B; field_simp; ring
  rw [e]
  linarith

theorem grid_sum (r M : Nat) (hM : r = 2*M+1) :
    ∑ c ∈ Finset.range r, sincPoly ((Real.pi * (foldDist r c : ℝ) / r)^2) =
      2 * closedForm M (Real.pi^2/(r:ℝ)^2) - 1 := by
  subst hM
  have h := sum_fold M (fun s => sincPoly ((Real.pi * (s:ℝ) / ((2*M+1:ℕ):ℝ))^2))
  beta_reduce at h
  rw [h, ← sum_sincPoly M]
  have e : ∀ s : ℕ, sincPoly ((Real.pi * (s:ℝ) / ((2*M+1:ℕ):ℝ))^2) =
      sincPoly (Real.pi^2/((2*M+1:ℕ):ℝ)^2 * (s:ℝ)^2) := by
    intro s; congr 1; ring
  have h0 : sincPoly ((Real.pi * ((0:ℕ):ℝ) / ((2*M+1:ℕ):ℝ))^2) = 1 := by simp [sincPoly]
  rw [h0, Finset.sum_congr rfl (fun s _ => e s)]

/-! ### The averaged coverage bound -/

/-- Averaged success of the reduced decoder: at least `27/50` for a prime `r > 10⁶`. -/
theorem reducedCoverageMass_averaged (r n m d : Nat) [Fact (Nat.Prime r)]
    (hprecision : r < 2^n) (hr : 1000001 ≤ r) (hd : ¬ r ∣ d) :
    (27:ℝ)/50 ≤ reducedCoverageMass r n m d := by
  classical
  have hrp := Fact.out (p := Nat.Prime r)
  have hr0 : 0 < r := hrp.pos
  have hodd : r % 2 = 1 := Nat.odd_iff.1 (hrp.odd_of_ne_two (by omega))
  have hpow : ∀ p, ¬ r ∣ 2^p := by
    intro p h
    have h2 := Nat.le_of_dvd two_pos (hrp.dvd_of_dvd_pow h)
    omega
  have hmd : ¬ r ∣ 2^m * d := by
    intro h
    rcases (Nat.Prime.dvd_mul hrp).1 h with h1 | h1
    · exact hpow m h1
    · exact hd h1
  obtain ⟨M, hM⟩ : ∃ M, r = 2*M+1 := ⟨r/2, by omega⟩
  let S : Finset (Fin r) := Finset.univ.filter (fun k => k.val ≠ 0)
  let peak := asymmetricPairPeak r n m d hprecision
  let f : (Fin (2^n) × Fin (2^m)) → ℝ := fun out =>
    if (d:ZMod r) ∈ reducedShiftCandidates r n m out
      then asymmetricPairMass r n m d out else 0
  let PL : Fin r → ℝ := fun k =>
    Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hprecision k).val)
  let PR : Fin r → ℝ := fun k =>
    Complex.normSq (paperPhaseAmplitude m ((((d*k.val)%r:Nat):ℝ)/r)
      (reducedPeak r m (paperCharacterProduct d k)).val)
  let T : ℝ := ∑ c ∈ Finset.range r, sincPoly ((Real.pi * (foldDist r c : ℝ) / r)^2)
  have hf : ∀ out, 0 ≤ f out := by
    intro out
    dsimp [f]
    split
    · exact asymmetricPairMass_nonneg _ _ _ _ _
    · rfl
  -- the k-th summand at the k-th peak
  have hp : ∀ k ∈ S, (1/(r:ℝ)) * (PL k * PR k) ≤ f (peak k) := by
    intro k hk
    have hn : k.val ≠ 0 := (Finset.mem_filter.mp hk).2
    have hkz : (k.val : ZMod r) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      simp only [ZMod.val_natCast_of_lt k.isLt, ZMod.val_zero] at hv
      exact hn hv
    have hm : (d:ZMod r) ∈ reducedShiftCandidates r n m (asymmetricPairPeak r n m d hprecision k) :=
      reducedShiftCandidates_correct r n m d hprecision k hkz
    dsimp only [f, peak]
    rw [if_pos hm]
    unfold asymmetricPairMass
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum
      (f := fun i : Fin r =>
        Complex.normSq (paperPhaseAmplitude n ((i.val:ℝ)/r) (paperPeak r n hprecision k).val) *
        Complex.normSq (paperPhaseAmplitude m ((((d*i.val)%r:Nat):ℝ)/r)
          (reducedPeak r m (paperCharacterProduct d k)).val))
      (fun i _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (Finset.mem_univ k)
  have hSe : S = Finset.univ.erase (⟨0, hr0⟩ : Fin r) := by
    ext k
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro hn he; exact hn (congrArg Fin.val he)
    · intro hn he; exact hn (Fin.ext he)
  have hsum_le : ∑ k ∈ S, (1/(r:ℝ)) * (PL k * PR k) ≤ reducedCoverageMass r n m d := by
    calc
      ∑ k ∈ S, (1/(r:ℝ)) * (PL k * PR k) ≤ ∑ k ∈ S, f (peak k) := Finset.sum_le_sum hp
      _ = ∑ out ∈ S.image peak, f out := by
        rw [Finset.sum_image]
        intro k _ l _ he
        exact asymmetricPairPeak_injective r n m d hprecision he
      _ ≤ ∑ out, f out := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun out _ _ => hf out)
      _ = reducedCoverageMass r n m d := rfl
  -- both axis probabilities lie in [0, 1]
  have hPL1 : ∀ k, PL k ≤ 1 := fun k =>
    (Finset.single_le_sum
      (f := fun v : Fin (2^n) => Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) v.val))
      (fun v _ => Complex.normSq_nonneg _)
      (Finset.mem_univ (paperPeak r n hprecision k))).trans_eq
      (paperPhaseAmplitude_totalMass ((k.val:ℝ)/r) n)
  have hPR1 : ∀ k, PR k ≤ 1 := fun k =>
    (Finset.single_le_sum
      (f := fun v : Fin (2^m) =>
        Complex.normSq (paperPhaseAmplitude m ((((d*k.val)%r:Nat):ℝ)/r) v.val))
      (fun v _ => Complex.normSq_nonneg _)
      (Finset.mem_univ (reducedPeak r m (paperCharacterProduct d k)))).trans_eq
      (paperPhaseAmplitude_totalMass ((((d*k.val)%r:Nat):ℝ)/r) m)
  have hprod : ∀ k, PL k + PR k - 1 ≤ PL k * PR k := by
    intro k
    nlinarith [mul_nonneg (sub_nonneg.2 (hPL1 k)) (sub_nonneg.2 (hPR1 k))]
  -- both axis averages are exact grid averages
  have hL : T ≤ ∑ k : Fin r, PL k := by
    have e := sum_mulMod r (2^n) hrp (hpow n)
      (fun c => sincPoly ((Real.pi * (foldDist r c : ℝ) / r)^2))
    rw [show T = _ from e.symm]
    apply Finset.sum_le_sum
    intro k _
    exact axis_lower n r k.val hr0 hodd
  have hR : T ≤ ∑ k : Fin r, PR k := by
    have e := sum_mulMod r (2^m * d) hrp hmd
      (fun c => sincPoly ((Real.pi * (foldDist r c : ℝ) / r)^2))
    rw [show T = _ from e.symm]
    apply Finset.sum_le_sum
    intro k _
    have hj : (2^m * d * k.val) % r = (2^m * ((d*k.val) % r)) % r := by
      rw [Nat.mul_mod_mod, mul_assoc]
    dsimp only [PR]
    rw [hj, reducedPeak_amplitude]
    exact axis_lower m r ((d*k.val)%r) hr0 hodd
  have hS : ∑ k : Fin r, (PL k + PR k - 1) ≤ ∑ k ∈ S, (PL k + PR k - 1) + 1 := by
    rw [hSe, ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hr0⟩ : Fin r))]
    linarith [hPL1 ⟨0, hr0⟩, hPR1 ⟨0, hr0⟩]
  have hsplit : ∑ k : Fin r, (PL k + PR k - 1) =
      ∑ k : Fin r, PL k + ∑ k : Fin r, PR k - r := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp
  have key : (1/(r:ℝ)) * (2*T - r - 1) ≤ reducedCoverageMass r n m d := by
    calc (1/(r:ℝ)) * (2*T - r - 1) ≤ (1/(r:ℝ)) * ∑ k ∈ S, (PL k + PR k - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ∑ k ∈ S, (1/(r:ℝ)) * (PL k + PR k - 1) := Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ S, (1/(r:ℝ)) * (PL k * PR k) :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hprod k) (by positivity))
      _ ≤ reducedCoverageMass r n m d := hsum_le
  have hT : T = 2 * closedForm M (Real.pi^2/(r:ℝ)^2) - 1 := grid_sum r M hM
  have hrR : (r:ℝ) = 2*(M:ℝ)+1 := by rw [hM]; push_cast; ring
  rw [hT, hrR] at key
  have hM5 : (500000:ℝ) ≤ M := by
    have : 500000 ≤ M := by omega
    exact_mod_cast this
  exact (averaged_numeric M hM5).trans key

/-- The averaged per-round bound for secp256k1 at the protected 256/208-bit precisions. -/
theorem reducedVerifiedMass_averaged (Q : Secp256k1.Point) (d : Nat) (hQd : Q = d • Secp256k1.G)
    (hQ : Q ≠ 0) : (27:ℝ)/50 ≤ reducedVerifiedMass Q d := by
  letI : Fact (Nat.Prime order) := ⟨Secp256k1.order_prime⟩
  rw [reducedVerifiedMass_eq Q d hQd]
  refine reducedCoverageMass_averaged order 256 208 d reducedLeftPrecision_order
    (by decide +kernel) ?_
  rintro ⟨t, rfl⟩
  apply hQ
  rw [hQd, mul_smul, smul_comm, Secp256k1.generator_nsmul_eq_zero, nsmul_zero]

end
end ShorECDLP.Entrant.Averaged

-- ==== part: BatchBoundary ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchBoundary.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge

def batchWorkspace : List Wire := List.range' 1024 2565 ++ List.range' 4102 512
def BatchedPointReady (s : BasisState) : Prop := PointLookupValid s ∧ Clean batchWorkspace s

theorem batchWorkspace_outside (w : Wire) (hw : w ∈ batchWorkspace) : w ∉ pointLogicalWires := by
  simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  dsimp only [Wire] at *
  omega

theorem batchPlacement_aux (w : Wire) (hw : w ∈ 836::pointLookupPath) : batchPlacement w=w := by
  change batchPlacementFn w=w
  simp only [pointLookupPath,List.mem_cons,List.mem_range'_1] at hw
  unfold batchPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem batchedPointReady_batch (s : BasisState) (hs : BatchedPointReady s) :
    BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro w hw
    change s (batchPlacement w)=false
    rw [batchPlacement_aux w (List.mem_cons_of_mem _ hw)]
    apply hs.1.1.1 w
    simp only [pointLookupPath,List.mem_range'_1] at hw
    simp only [List.mem_append,List.mem_range'_1]
    omega
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    change s (batchPlacement (1024+3079+i.val))=false
    rw [batchPlacement_high _ (by dsimp only [Wire]; omega)]
    apply hs.2
    simp only [batchWorkspace,List.mem_append,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · change s (batchPlacement 4102)=false
    rw [batchPlacement_high _ (by decide)]
    exact hs.2 _ (by simp [batchWorkspace])
  · change s (batchPlacement 836)=true
    rw [batchPlacement_aux _ (by simp)]
    exact hs.1.2

theorem batchedPointReady_words (s : BasisState) (hs : BatchedPointReady s) :
    ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm s) ∘ batchWord 1024 j = fun _ => false := by
  intro j hj
  funext i
  change s (batchPlacement (batchWord 1024 j i))=false
  have hlo : 1024 ≤ batchWord 1024 j i := by dsimp [batchWord,Wire]; omega
  have hhi : batchWord 1024 j i < 3589 := by
    have hjv : j.val ≠ 5 := by intro he; apply hj; exact Fin.ext he
    dsimp [batchWord]
    dsimp only [Wire]
    omega
  rw [batchPlacement_endpoints _ hlo hhi]
  exact hs.2 _ (by simp only [batchWorkspace,List.mem_append,List.mem_range'_1]; dsimp only [Wire] at *; omega)

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

theorem batchPlacement_address (w : Wire) (hw : w ∈ pointLookupAddress) : batchPlacement w=w := by
  change batchPlacementFn w=w
  simp only [pointLookupAddress,List.mem_range'_1] at hw
  unfold batchPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

private theorem address_frame (bits : List Wire) (s t : BasisState)
    (h : ∀ w ∈ bits, s w=t w) : tableAddressValue bits s=tableAddressValue bits t := by
  induction bits with
  | nil => rfl
  | cons w ws ih =>
    simp only [tableAddressValue,h w (by simp),ih (fun w hw => h w (by simp [hw]))]

theorem batchWindowTree_route (s : BasisState) :
    batchWindowTree.routeLabel (relabelBasis batchPlacement.symm s) = tableAddressValue pointLookupAddress s := by
  rw [batchWindowTree,tableAddressTree_route,zero_add,one_mul]
  apply address_frame
  intro w hw
  change s (batchPlacement w)=s w
  rw [batchPlacement_address w hw]

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

-- ==== part: BatchedWindowState ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchedWindowState.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
noncomputable def signedBatchState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  windowYNegateState (placedBatchState Q w (windowYNegateState s))

theorem pointWrite_frame_eq (P : Point) (s t : BasisState)
    (h : ∀ w, w ∉ pointLogicalWires → s w=t w) : pointWrite P s=pointWrite P t := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hw]
  · simp only [pointWrite,if_neg hw,h w hw]

theorem signedBatchState_pointWrite (Q : Point) (w : OddWindow) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s)
    (hb : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm (windowYNegateState s)))
    (hz : ∀ j : Fin 6, j ≠ 5 →
      (relabelBasis batchPlacement.symm (windowYNegateState s)) ∘ batchWord 1024 j = fun _ => false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    signedBatchState Q w s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  have he := placedBatchState_pointWrite Q w _ hb hz ht hC hr P' hd
  have hsign : placedBatchState Q w (windowYNegateState s) 854 = s 854 :=
    (placedBatchState_frame Q w _ hb hz 854 (by decide +kernel)).trans
      ((windowYNegateState_correct s hs).2 854 (by decide +kernel))
  have hv := placedBatchState_ready Q w _ hb hz ht hC hr P' hd
  have hc := placedBatchState_coordinates Q w _ hb hz ht hC hr P' hd
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
  have hn := windowYNegateState_batchedReady t ht
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
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState t))))) = .some hC := by
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
  have he := signedBatchState_pointWrite Q w t ht.1.1 (batchedPointReady_batch _ hn)
    (batchedPointReady_words _ hn) hC hr' P hd
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
    (hs : Secp256k1ZeroAllowedInputValid s)
    (hb : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm (windowYNegateState s)))
    (hz : ∀ j : Fin 6, j ≠ 5 →
      (relabelBasis batchPlacement.symm (windowYNegateState s)) ∘ batchWord 1024 j = fun _ => false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    Secp256k1ZeroAllowedInputValid (placedBatchState Q w (windowYNegateState s)) := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  exact placedBatchState_ready Q w _ hb hz ht hC hr P' hd

def SignedBatchReady (Q : Point) (w : OddWindow) (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y),
    constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC ∧
    ∃ P : Point, pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: BatchedWindowCoherent ====

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
  (windowYNegate.seq (placedBatchSource Q w)).seq windowYNegate

theorem signedBatchSource_coherent (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn (signedBatchSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (signedBatchState Q w)) (SignedBatchReady Q w) := by
  have hneg : CoherentlyImplementsOn windowYNegate (Finsupp.lmapDomain ℂ ℂ windowYNegateState)
      (SignedBatchReady Q w) := restrictCoherent windowYNegate_coherent (fun s hs => hs.1.1.1)
  have hfirst := composeCoherent hneg (placedBatchSource_state Q w) (fun s hs =>
    batchedPointReady_batch _ (windowYNegateState_batchedReady s hs.1))
  have hlast := composeCoherent hfirst windowYNegate_coherent (by
    intro s hs
    obtain ⟨hr,x,y,hC,hrow,P,hdata⟩ := hs
    have hn := windowYNegateState_batchedReady s hr
    exact signedBatchState_middle_ready Q w s hr.1.1 (batchedPointReady_batch _ hn)
      (batchedPointReady_words _ hn) hC hrow P hdata)
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
  have hn := windowYNegateState_batchedReady t ht
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
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState t))))) = .some hC := by
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
  exact ⟨ht,x,y,hC,hr',P,hd⟩

def BatchedWindowValid (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ P : Point, pointStateCoordinates s=fig14PointEncoding P

theorem batchedWindowSources_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) :
    CoherentlyImplementsOn (sequenceCircuit (batchedWindowSources Q w))
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
  simpa only [batchedWindowSources,sequenceCircuit,signedBatchSource,adaptive_seq_assoc,adaptive_seq_done,
    batchedWindowState,xs,ys] using h
theorem batchedWindowCore_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((batchedWindowCore w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState Q w)) BatchedWindowValid := by
  have h := batchedWindowSources_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := batchedWindowCore_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: PreparedBatch ====

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
    rw [batchPrepareState_frame s w (by
      simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
      simp only [pointLookupAddress,List.mem_range'_1]
      omega)]
    exact hs.2 w hw

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

theorem batchedWindowPreparedSource_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) :
    CoherentlyImplementsOn (batchedWindowPreparedSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)) BatchedWindowValid := by
  have hc := composeCoherent (batchedWindowSources_coherent Q hQ hn w) batchPrepare_coherent
    (batchedWindowState_valid Q hQ hn w)
  have h := composeCoherent (f := batchPrepareState)
    (g := fun s => batchPrepareState (batchedWindowState Q w s))
    batchPrepare_coherent hc batchPrepareState_valid
  exact h

theorem batchedWindowPrepared_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((batchedWindowPrepared w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)) BatchedWindowValid := by
  have h := batchedWindowPreparedSource_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := batchedWindowPrepared_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: ActualWindow ====

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
  change windowAddressSwap 855 w=w
  simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
  unfold windowAddressSwap
  split_ifs <;> (try dsimp only [Wire] at *) <;> omega

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

noncomputable def actualBatchedWindowState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm 855 (by decide))
    (preparedBatchState Q w (relabelBasis (windowAddressPerm 855 (by decide)).symm s))

theorem actualBatchedWindow_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn (((actualBatchedWindow w).program start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
  have h := (batchedWindowPreparedSource_coherent Q hQ hn w).relabel (windowAddressPerm 855 (by decide))
  have hr : CoherentlyImplementsOn ((batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide)))
      ((relabelState (windowAddressPerm 855 (by decide))).comp
        ((Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)).comp
          (relabelState (windowAddressPerm 855 (by decide)).symm))) BatchedWindowValid := by
    obtain ⟨cs,hc,hm⟩ := h
    exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (actualWindow_pullback_valid s hs)),hm⟩
  have he : CoherentlyImplementsOn ((batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide)))
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
    apply hr.congrIdeal
    intro s hs
    simp [actualBatchedWindowState,LinearMap.comp_apply,relabelState,ket]
  unfold CoherentlyImplementsOn at he ⊢
  rw [actualBatchedWindow_run w start Q hQ history]
  exact he

theorem actualBatchedWindowState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))
        else -windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))) s := by
  unfold actualBatchedWindowState
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


theorem actualBatchedWindowState_selected (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
        else -windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) s := by
  rw [actualBatchedWindowState_correct Q hQ hn w s hs P hP,actualWindow_selected_address s hs]

theorem actualBatchedWindowState_valid (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (actualBatchedWindowState Q w s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

theorem actualBatchedWindowState_frame (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) (v : Wire) (hv : v∉pointLogicalWires) :
    actualBatchedWindowState Q w s v=s v := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected Q hQ hn w s hs P hP]
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

-- ==== part: WindowPhysical ====

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

-- ==== part: ModularPhysical ====

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

-- ==== part: EEACenterPhysical ====

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

-- ==== part: EEAStructuralPhysical ====

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

-- ==== part: EEAIntervalPhysical ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEAIntervalPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

/-! Structural preservation of gate validity. Generic lemmas assume source syntax validity;
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

-- ==== part: MeasuredEEAPhysical ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/MeasuredEEAPhysical.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

/-! Structural preservation of gate validity. Generic lemmas assume source syntax validity;
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

-- ==== part: SquarePhysical ====

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

-- ==== part: InPlacePhysical ====

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

-- ==== part: InPlaceCompletePhysical ====

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

-- ==== part: CoordinatePhysical ====

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

-- ==== part: ActualPhysical ====

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

attribute [local irreducible] sharedCoordinateProgram sharedYNegateProgram placedBatchProgram

theorem batchedWindowCore_wellFormed (w : OddWindow) (start : Nat) :
    (batchedWindowCore w start).2.WellFormed := by
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [batchedWindowSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact sharedCoordinateProgram_wellFormed _ _
  · exact sharedYNegateProgram_wellFormed _ _
  · exact placedBatchProgram_wellFormed _ _
  · exact sharedYNegateProgram_wellFormed _ _

attribute [local irreducible] batchedWindowCore

theorem batchedWindowPrepared_wellFormed (w : OddWindow) (start : Nat) :
    (batchedWindowPrepared w start).2.WellFormed := by
  exact surroundCompiled_wellFormed _ _ _
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (batchedWindowCore_wellFormed w start)

attribute [local irreducible] batchedWindowPrepared

theorem actualBatchedWindow_wellFormed (w : OddWindow) (start : Nat) :
    ((actualBatchedWindow w).program start).WellFormed := by
  apply shiftStraight_wellFormed
  exact (relabelStraight_wellFormed _ _).mpr (batchedWindowPrepared_wellFormed w 0)

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

attribute [local irreducible] actualBatchedWindow actualFirstWindow

theorem batchedOuterPlan_windowsWellFormed : batchedOuterPlan.WindowsWellFormed := by
  intro w hw start
  change w ∈ actualLeftWindows ++ actualRightWindows at hw
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact actualFirstWindow_wellFormed _
  · exact actualBatchedWindow_wellFormed _ _
  · exact actualBatchedWindow_wellFormed _ _

attribute [local irreducible] batchedOuterPlan

theorem batchedOuterPlan_round_wellFormed (start : Nat) :
    (batchedOuterPlan.round start).WellFormed :=
  batchedOuterPlan.round_wellFormed batchedOuterPlan_windowsWellFormed start

theorem batchedOuterPlan_repeat_wellFormed (count start : Nat) :
    (batchedOuterPlan.repeat count start).WellFormed :=
  batchedOuterPlan.repeat_wellFormed batchedOuterPlan_windowsWellFormed count start

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: HistoryExecution ====

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

-- ==== part: OuterExecution ====

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

-- ==== part: ActualExecution ====

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
  (batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide))
noncomputable def actualLeftSources (Q : Point) : List AdaptiveCircuit :=
  actualFirstSource Q :: List.ofFn (fun k : Fin 15 => actualOddSource Q (.left ⟨14-k.val,by omega⟩))
noncomputable def actualRightSources (Q : Point) : List AdaptiveCircuit :=
  List.ofFn (fun k : Fin 13 => actualOddSource Q (.right ⟨12-k.val,by omega⟩))
noncomputable def actualRoundSource (Q : Point) : AdaptiveCircuit :=
  sourceOuterRound streamAddress.reverse (actualLeftSources Q) (actualRightSources Q) batchedResetWires

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
      actualLeftWindows (actualLeftSources Q) := by
  apply List.Forall₂.cons
  · exact fun start history => actualFirstWindow_run start Q hQ history
  · apply forall₂_ofFn
    intro k start history
    exact actualBatchedWindow_run _ start Q hQ history

theorem actualRightSources_run (Q : Point) (hQ : order • Q=0) :
    List.Forall₂ (fun w c => ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).run = c.run)
      actualRightWindows (actualRightSources Q) := by
  apply forall₂_ofFn
  intro k start history
  exact actualBatchedWindow_run _ start Q hQ history

attribute [local irreducible] actualLeftWindows actualRightWindows actualLeftSources actualRightSources

theorem batchedOuterPlan_round_run (Q : Point) (hQ : order • Q=0) (start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run =
      (actualRoundSource Q).run := by
  exact outerPlan_round_run batchedOuterPlan _ _ _ (actualLeftSources_run Q hQ) (actualRightSources_run Q hQ) start history

attribute [local irreducible] batchedOuterPlan actualRoundSource

theorem batchedOuterPlan_repeat_run (Q : Point) (hQ : order • Q=0) (count start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run =
      (repeatWindowProgram (actualRoundSource Q) count).run :=
  outerPlan_repeat_run _ _ _ (batchedOuterPlan_round_run Q hQ) count start history

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: SourceAxis ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/SourceAxis.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem fourierContinue_seq (dir : PhaseDir) (ws : List Wire) (prior : List Bool)
    (next : List Bool → AdaptiveCircuit) (tail : AdaptiveCircuit) :
    (fourierContinue dir ws prior next).seq tail =
      fourierContinue dir ws prior (fun h => (next h).seq tail) := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih => simp only [fourierContinue,AdaptiveCircuit.seq,ih]

theorem sourceOuterAxis_seq_streamAxis (calls : List AdaptiveCircuit) (prior : List Bool)
    (tail : AdaptiveCircuit) :
    (sourceOuterAxis streamAddress.reverse calls prior).seq tail = streamAxis calls prior tail := by
  induction calls generalizing prior with
  | nil => rfl
  | cons call calls ih =>
    simp only [sourceOuterAxis,streamAxis,List.reverse_reverse,AdaptiveCircuit.seq]
    rw [circuit_seq_assoc,fourierContinue_seq]
    simp only [ih]

theorem sourceOuterRound_streamAxis (left right : List AdaptiveCircuit) (reset : List Wire) :
    sourceOuterRound streamAddress.reverse left right reset =
      AdaptiveCircuit.unitary [.X 836] (streamAxis left List.nil
        (streamAxis right List.nil (.unitary [.X 836] (measureResetWithCorrection reset (fun _ => []))))) := by
  simp only [sourceOuterRound,sourceOuterAxis_seq_streamAxis]

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: TaggedProbability ====

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

-- ==== part: WindowValidity ====

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
  obtain ⟨⟨⟨hclean,hzero,hxbound,hybound⟩,hq⟩,hworkspace⟩ := hs.1
  refine ⟨⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro v hv
    rw [hcore v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)]
    exact hclean v hv
  · rw [hcore 837 (by decide)]; exact hzero
  · rw [hx]; exact hxbound
  · rw [hy]; exact hybound
  · rw [hcore 836 (by decide)]; exact hq
  · intro v hv
    have hv' : 1024 ≤ v := by simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
    have hne : v ≠ w := by dsimp only [Wire] at *; omega
    simpa only [upd,if_neg hne] using hworkspace v hv
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


theorem actualBatchedWindowState_supported (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (ψ : State)
    (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w) ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  simpa [ket] using supportedOn_ket BatchedWindowValid _
    (actualBatchedWindowState_valid Q hQ hn w s hs)

theorem actualBatchedWindow_branch_supported (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (start : Nat) (history : Fin start → Bool)
    (b : InstrumentBranch)
    (hb : b ∈ (((actualBatchedWindow w).program start).instantiate
      (readConstant coefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (b.kraus ψ) := by
  obtain ⟨c,hc⟩ := (actualBatchedWindow_coherent Q hQ hn w start history).branch_coefficient b hb
  rw [hc.on_supported hψ]
  exact support_smul c (actualBatchedWindowState_supported Q hQ hn w ψ hψ)
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: AxisProbability ====

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
          ⟨[], (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)).comp
            (Quantum.run (streamAddress.map Gate.H))⟩ b)

theorem selectedIdealAxis_cons_mass (Q : Point) (w : OddWindow) (ws : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) (ψ : State) :
    (selectedIdealAxis Q (w :: ws) prior terminal).bornMass ψ =
      (fourierContinuationInstrument prior
        (fun bits => selectedIdealAxis Q ws (bits.reverse ++ prior) terminal)).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
  simp only [selectedIdealAxis,Instrument.bornMass,List.map_map,Function.comp_def,
    InstrumentBranch.seq,LinearMap.comp_apply]

/-- All arithmetic records may be summed out, including before an arbitrary selected terminal event. -/
theorem selectedSourceAxis_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (call : OddWindow → AdaptiveCircuit) (ws : List OddWindow)
    (hcall : ∀ w ∈ ws, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
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
    · exact actualBatchedWindowState_supported Q hQ hn w _
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

-- ==== part: FirstValidity ====

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
    have hb : 1024 ≤ v := by
      simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    exact hs.2 v (by dsimp only [Wire] at *; omega) (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)

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



private theorem support_linear_firstValidity (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
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
  apply support_linear_firstValidity FirstWindowInput FirstWindowInput (applyGate (.H w)) ?_ ψ hψ
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
  apply support_linear_firstValidity FirstWindowInput BatchedWindowValid _ ?_ ψ hψ
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

-- ==== part: CrossWindowWeights ====

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

-- ==== part: CrossWindowPoint ====

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
    actualBatchedWindowState Q (.left j) s =
      pointWrite (P + signedTableOdd 32768 (windowRawDigit 0 s) •
        ((2 ^ (16 * j.val)) • signedWindowHalfPoint G order)) s := by
  rw [actualBatchedWindowState_selected Q hQ hn (.left j) s hs P hP]
  simp only [windowPoint, reused_window_selected_odd]

/-- The corrected actual right window has precisely its scalar digit action. -/
theorem actual_right_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (j : Fin 13) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualBatchedWindowState Q (.right j) s =
      pointWrite (P + signedTableOdd 32768 (windowRawDigit 0 s) •
        ((2 ^ (16 * j.val)) • signedWindowHalfPoint Q order)) s := by
  rw [actualBatchedWindowState_selected Q hQ hn (.right j) s hs P hP]
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

-- ==== part: TwoAxisProbability ====

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
    · exact actualBatchedWindowState_supported Q hQ hn w _
        (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ)

theorem selectedSourceAxis_terminal_congr (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (call : OddWindow → AdaptiveCircuit) (ws : List OddWindow)
    (hcall : ∀ w ∈ ws, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
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
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
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
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
  have h := actualBatchedWindow_coherent Q hQ hn w 0 Fin.elim0
  unfold CoherentlyImplementsOn at h ⊢
  rw [actualBatchedWindow_run w 0 Q hQ Fin.elim0] at h
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

-- ==== part: FixedWord ====

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

-- ==== part: TaggedAxis ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/TaggedAxis.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

noncomputable def taggedSourceAxis (call : OddWindow → AdaptiveCircuit) :
    List OddWindow → List Bool → List (List Bool × InstrumentBranch)
  | [], prior => [(prior,⟨[],LinearMap.id⟩)]
  | w :: ws, prior => (streamBlockOutcomes (call w) prior).flatMap (fun a =>
      (taggedSourceAxis call ws (a.1.reverse ++ prior)).map (fun b => (b.1,a.2.seq b.2)))

theorem selectedSourceAxis_tagged (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow) (prior : List Bool) (terminal : List Bool → Instrument) :
    selectedSourceAxis call ws prior terminal =
      (taggedSourceAxis call ws prior).flatMap (fun a =>
        (terminal a.1).map a.2.seq) := by
  induction ws generalizing prior with
  | nil =>
    simp only [selectedSourceAxis,taggedSourceAxis,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    have he : (InstrumentBranch.seq ⟨[],LinearMap.id⟩) = (fun b => b) := by
      funext b
      cases b
      simp [InstrumentBranch.seq]
    rw [he,List.map_id']
  | cons w ws ih =>
    simp only [selectedSourceAxis,streamBlockContinuation,taggedSourceAxis,ih,
      List.flatMap_assoc,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    apply List.flatMap_congr
    intro b hb
    apply List.map_congr_left
    intro c hc
    cases a with | mk atag a =>
      cases b with | mk btag b =>
        cases a; cases b; cases c
        simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem streamBlockOutcomes_split (call : AdaptiveCircuit) (count : Nat)
    (hcount : ∀ b ∈ call.run, b.history.length = count) (prior : List Bool)
    (tagged : List Bool × InstrumentBranch) (ht : tagged ∈ streamBlockOutcomes call prior) :
    ∃ a : List Bool, a.length = count ∧ tagged.1.length = 16 ∧
      tagged.2.history = a ++ tagged.1 := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp ht
  have hl : bs.length = 16 := by
    simpa only [streamAddress,List.length_range'] using
      (fourierOutcomes_mem streamAddress.length bs).mp hbs
  simp only [AdaptiveCircuit.seq,AdaptiveCircuit.run] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact ⟨b.history,hcount b hb,hl,rfl⟩

theorem taggedSourceAxis_transcript (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (prior : List Bool) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis call ws prior) :
    ∃ bits, AxisTranscript (ws.map actualBatchedWindow) tagged.2.history bits ∧
      tagged.1 = bits.reverse ++ prior := by
  induction ws generalizing prior tagged with
  | nil =>
    simp only [taggedSourceAxis,List.mem_singleton] at ht
    subst tagged
    exact ⟨[],AxisTranscript.nil,rfl⟩
  | cons w ws ih =>
    obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    obtain ⟨ar,har,hbits,hhist⟩ := streamBlockOutcomes_split (call w) _ (hcount w (by simp)) prior a ha
    obtain ⟨bits,htrans,hprior⟩ := ih (fun v hv => hcount v (List.mem_cons_of_mem w hv)) _ b hb
    refine ⟨a.1 ++ bits,?_,?_⟩
    · simpa only [List.map_cons,InstrumentBranch.seq,hhist,List.append_assoc] using
        AxisTranscript.cons (actualBatchedWindow w) (ws.map actualBatchedWindow)
          ar a.1 b.2.history bits har hbits htrans
    · simpa only [List.reverse_append,List.append_assoc] using hprior

theorem actualOddSource_history_length (Q : Point) (hQ : order • Q = 0) (w : OddWindow)
    (b : InstrumentBranch) (hb : b ∈ (actualOddSource Q w).run) :
    b.history.length = (actualBatchedWindow w).count := by
  have he := actualBatchedWindow_run w 0 Q hQ Fin.elim0
  change _ = (actualOddSource Q w).run at he
  rw [← he] at hb
  simpa only [Nat.zero_add,Nat.sub_zero] using
    straight_history_length ((actualBatchedWindow w).program 0) (readConstant coefficientAt Q) Fin.elim0 b hb


/-- Fixed positions read the same Fourier tag used by selectedSourceAxis, not arithmetic records. -/
theorem taggedSourceAxis_readWord (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis call ws List.nil)
    (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (ws.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.reverse) := by
  obtain ⟨bits,htrans,htag⟩ := taggedSourceAxis_transcript call ws hcount List.nil tagged ht
  rw [htag,List.append_nil,List.reverse_reverse]
  exact htrans.readWord before after

theorem actualTaggedAxis_readWord (Q : Point) (hQ : order • Q = 0)
    (ws : List OddWindow) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis (actualOddSource Q) ws List.nil)
    (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (ws.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.reverse) :=
  taggedSourceAxis_readWord _ ws (fun w _ b hb => actualOddSource_history_length Q hQ w b hb)
    tagged ht before after


/-- Event filtering by fixed record positions is exactly Fourier-tag selection. -/
theorem selectedSourceAxis_fixed_filter (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (tail : AdaptiveCircuit) (accept : Nat → Bool) :
    selectedSourceAxis call ws List.nil
      (fun tag => if accept (fourierWordLSB tag.reverse) then tail.run else []) =
      (streamAxis (ws.map call) List.nil tail).run.filter
        (fun b => (readWord b.history (axisPositions (ws.map actualBatchedWindow) 0)).any accept) := by
  rw [← selectedSourceAxis_constant call ws List.nil tail]
  rw [selectedSourceAxis_tagged,selectedSourceAxis_tagged,List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hp (b : InstrumentBranch) :
      (readWord (a.2.seq b).history (axisPositions (ws.map actualBatchedWindow) 0)).any accept =
        accept (fourierWordLSB a.1.reverse) := by
    have h := taggedSourceAxis_readWord call ws hcount a ha List.nil b.history
    change (readWord (a.2.history ++ b.history) _).any accept = _
    simpa only [List.nil_append,List.length_nil,Option.any_some] using congrArg (fun x => x.any accept) h
  rw [List.filter_map]
  simp only [Function.comp_def,hp]
  split <;> simp_all
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: TaggedTwoAxes ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/TaggedTwoAxes.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

theorem AxisTranscript.history_length {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits) :
    history.length = axisCount ws := by
  induction h with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    simp only [List.length_append,ha,hb,ih,axisCount]

noncomputable def taggedSourceTwoAxes (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow) :
    List ((List Bool × List Bool) × InstrumentBranch) :=
  (streamBlockOutcomes first List.nil).flatMap (fun a =>
    (taggedSourceAxis call left a.1.reverse).flatMap (fun l =>
      (taggedSourceAxis call right List.nil).map (fun r => ((l.1,r.1),a.2.seq (l.2.seq r.2)))))

theorem selectedSourceTwoAxes_tagged (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) :
    selectedSourceTwoAxes first call left right terminal =
      (taggedSourceTwoAxes first call left right).flatMap (fun a =>
        (terminal a.1.1 a.1.2).map a.2.seq) := by
  simp only [selectedSourceTwoAxes,streamBlockContinuation,selectedSourceAxis_tagged,
    taggedSourceTwoAxes,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,
    List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro l hl
  apply List.flatMap_congr
  intro r hr
  apply List.map_congr_left
  intro b hb
  rcases a with ⟨atag,a⟩; rcases l with ⟨lt,l⟩; rcases r with ⟨rt,r⟩
  cases a; cases l; cases r; cases b
  simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem taggedSourceTwoAxes_readWords (first : AdaptiveCircuit)
    (hfirst : ∀ b ∈ first.run, b.history.length = actualFirstWindow.count)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, ∀ b ∈ (call w).run,
      b.history.length = (actualBatchedWindow w).count)
    (tagged : (List Bool × List Bool) × InstrumentBranch)
    (ht : tagged ∈ taggedSourceTwoAxes first call left right) (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.1.reverse) ∧
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (right.map actualBatchedWindow)
        (before.length + axisCount (actualFirstWindow :: left.map actualBatchedWindow))) =
        some (fourierWordLSB tagged.1.2.reverse) := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨l,hl,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
  obtain ⟨ar,har,hbs,hah⟩ := streamBlockOutcomes_split first _ hfirst List.nil a ha
  obtain ⟨lbs,hlt,hltag⟩ := taggedSourceAxis_transcript call left
    (fun w hw => hcall w (List.mem_append_left _ hw)) a.1.reverse l hl
  obtain ⟨rbs,hrt,hrtag⟩ := taggedSourceAxis_transcript call right
    (fun w hw => hcall w (List.mem_append_right _ hw)) List.nil r hr
  have hleft : AxisTranscript (actualFirstWindow :: left.map actualBatchedWindow)
      (a.2.history ++ l.2.history) (a.1 ++ lbs) := by
    rw [hah]
    exact AxisTranscript.cons _ _ ar a.1 l.2.history lbs har hbs hlt
  have hlword := hleft.readWord before (r.2.history ++ after)
  have hrword := hrt.readWord (before ++ a.2.history ++ l.2.history) after
  have hllength := hleft.history_length
  constructor
  · simpa only [InstrumentBranch.seq,List.append_assoc,hltag,← List.reverse_append,
      List.reverse_reverse] using hlword
  · have he : (before ++ a.2.history ++ l.2.history).length =
        before.length + axisCount (actualFirstWindow :: left.map actualBatchedWindow) := by
      simpa only [List.length_append,Nat.add_assoc] using congrArg (before.length + ·) hllength
    rw [he] at hrword
    simpa only [InstrumentBranch.seq,List.append_assoc,hrtag,List.append_nil,
      List.reverse_reverse] using hrword

theorem actualFirstSource_history_length (Q : Point) (hQ : order • Q = 0)
    (b : InstrumentBranch) (hb : b ∈ (actualFirstSource Q).run) :
    b.history.length = actualFirstWindow.count := by
  have he := actualFirstWindow_run 0 Q hQ Fin.elim0
  change _ = (actualFirstSource Q).run at he
  rw [← he] at hb
  simpa only [Nat.zero_add,Nat.sub_zero] using
    straight_history_length (actualFirstWindow.program 0) (readConstant coefficientAt Q) Fin.elim0 b hb


/-- Select a pair of evaluator words, rejecting either missing word. -/
def fixedPairAccept (left right : List Nat) (accept : Nat → Nat → Bool)
    (history : List Bool) : Bool :=
  ((readWord history left).bind (fun lhs => (readWord history right).map (accept lhs))).getD false

theorem selectedSourceTwoAxes_fixed_filter (first : AdaptiveCircuit)
    (hfirst : ∀ b ∈ first.run, b.history.length = actualFirstWindow.count)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, ∀ b ∈ (call w).run,
      b.history.length = (actualBatchedWindow w).count)
    (tail : AdaptiveCircuit) (accept : Nat → Nat → Bool) :
    selectedSourceTwoAxes first call left right (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then tail.run else []) =
      (streamAxis (first :: left.map call) List.nil
        (streamAxis (right.map call) List.nil tail)).run.filter (fun (b : InstrumentBranch) =>
          fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
            (axisPositions (right.map actualBatchedWindow)
              (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept b.history) := by
  rw [← selectedSourceTwoAxes_constant first call left right tail]
  rw [selectedSourceTwoAxes_tagged,selectedSourceTwoAxes_tagged,List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hp (b : InstrumentBranch) :
      fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
        (axisPositions (right.map actualBatchedWindow)
          (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept (a.2.seq b).history =
      accept (fourierWordLSB a.1.1.reverse) (fourierWordLSB a.1.2.reverse) := by
    have h := taggedSourceTwoAxes_readWords first hfirst call left right hcall a ha List.nil b.history
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at h
    simp only [fixedPairAccept,InstrumentBranch.seq,h.1,h.2,Option.bind_some,
      Option.map_some,Option.getD_some]
  rw [List.filter_map]
  simp only [Function.comp_def,hp]
  split <;> simp_all

/-- The same two fixed words drive event selection on the actual source and on its ideal image. -/
theorem actualSources_fixedPair_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (left right : List OddWindow) (tail : AdaptiveCircuit) (accept : Nat → Nat → Bool) :
    Instrument.bornMass ((streamAxis (actualFirstSource Q :: left.map (actualOddSource Q)) List.nil
      (streamAxis (right.map (actualOddSource Q)) List.nil tail)).run.filter (fun (b : InstrumentBranch) =>
        fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
          (axisPositions (right.map actualBatchedWindow)
            (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept b.history))
      (ket (zeroBasisState[836 ↦ true])) =
    (selectedIdealTwoAxes Q left right (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then tail.run else [])).bornMass
      (ket (zeroBasisState[836 ↦ true])) := by
  rw [← selectedSourceTwoAxes_fixed_filter (actualFirstSource Q)
    (fun b hb => actualFirstSource_history_length Q hQ b hb) (actualOddSource Q) left right
    (fun w _ b hb => actualOddSource_history_length Q hQ w b hb) tail accept]
  exact actualSourcesTwoAxes_mass Q hQ hn left right _
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: ActualPair ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ActualPair.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] actualFirstWindow actualBatchedWindow actualFirstSource actualOddSource
attribute [local irreducible] streamAddress fourierOutcomes streamAxis sourceOuterRound measureResetWithCorrection batchedResetWires actualRoundSource selectedIdealTwoAxes

def leftOddIndices : List OddWindow := List.ofFn (fun k : Fin 15 => .left ⟨14-k.val,by omega⟩)
def rightOddIndices : List OddWindow := List.ofFn (fun k : Fin 13 => .right ⟨12-k.val,by omega⟩)

theorem actualLeftSources_indices (Q : Point) : actualLeftSources Q =
    actualFirstSource Q :: leftOddIndices.map (actualOddSource Q) := by
  simp only [actualLeftSources,leftOddIndices,List.map_ofFn,Function.comp_def]
theorem actualRightSources_indices (Q : Point) : actualRightSources Q =
    rightOddIndices.map (actualOddSource Q) := by
  simp only [actualRightSources,rightOddIndices,List.map_ofFn,Function.comp_def]
theorem actualLeftWindows_indices : actualLeftWindows =
    actualFirstWindow :: leftOddIndices.map actualBatchedWindow := by
  simp only [actualLeftWindows,leftOddIndices,List.map_ofFn,Function.comp_def]
theorem actualRightWindows_indices : actualRightWindows =
    rightOddIndices.map actualBatchedWindow := by
  simp only [actualRightWindows,rightOddIndices,List.map_ofFn,Function.comp_def]

theorem unitary_history_filter_mass (g : Circuit) (next : AdaptiveCircuit)
    (accept : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((AdaptiveCircuit.unitary g next).run.filter (fun b => accept b.history)) ψ =
      Instrument.bornMass (next.run.filter (fun b => accept b.history)) (Quantum.run g ψ) := by
  simp only [AdaptiveCircuit.run,List.filter_map,Instrument.bornMass,List.map_map,Function.comp_def]
  rfl

def actualRoundFixedAccept (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  fixedPairAccept (batchedOuterPlan.positions ⟨0,by decide⟩).left.toList
    (batchedOuterPlan.positions ⟨0,by decide⟩).right.toList accept history

private theorem positions_zero {n : Nat} (p : OuterPlan n) :
    (p.positions ⟨0,by decide⟩).left.toList = axisPositions p.left.toList 0 ∧
    (p.positions ⟨0,by decide⟩).right.toList = axisPositions p.right.toList (axisCount p.left.toList) := by
  simp only [OuterPlan.positions,Vector.toList,List.toList_toArray,Nat.zero_mul,Nat.zero_add]
  trivial

private theorem actual_left : batchedOuterPlan.left.toList = actualLeftWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]
private theorem actual_right : batchedOuterPlan.right.toList = actualRightWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]

theorem actualRoundFixedAccept_positions (accept : Nat → Nat → Bool) (history : List Bool) :
    actualRoundFixedAccept accept history =
      fixedPairAccept (axisPositions (actualFirstWindow :: leftOddIndices.map actualBatchedWindow) 0)
        (axisPositions (rightOddIndices.map actualBatchedWindow)
          (axisCount (actualFirstWindow :: leftOddIndices.map actualBatchedWindow))) accept history := by
  rw [actualRoundFixedAccept,(positions_zero batchedOuterPlan).1,(positions_zero batchedOuterPlan).2,
    actual_left,actual_right,actualLeftWindows_indices,actualRightWindows_indices]

/-- Fixed positions of the actual layout select the same event in the actual round and ideal two-axis model. -/
theorem actualRoundSource_fixedPair_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (accept : Nat → Nat → Bool) :
    Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept accept b.history)) (ket zeroBasisState) =
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,unitary_history_filter_mass]
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  rw [hx,actualLeftSources_indices,actualRightSources_indices]
  simp only [actualRoundFixedAccept_positions]
  exact actualSources_fixedPair_mass Q hQ hn leftOddIndices rightOddIndices _ accept


noncomputable def wrappedPairAccept (params : DecoderParams) (Q : Point) (left right : Nat) : Bool := by
  classical
  exact ((fixedCandidates params left right).toList.find? (fun c => decide (c.val • G = Q))).isSome

def actualSingleRoundLayout : DecodeLayout :=
  ⟨.wrappedShift,legacyDecoderParams,[batchedOuterPlan.positions ⟨0,by decide⟩],by decide⟩

theorem wrappedTrial_verified_isSome (params : DecoderParams) (Q : Point)
    (positions : TrialPositions params) (history : List Bool) :
    (verifiedCandidate ⟨.wrappedShift,params,[positions],by simp⟩ Q history).isSome =
      fixedPairAccept positions.left.toList positions.right.toList (wrappedPairAccept params Q) history := by
  classical
  simp only [verifiedCandidate,candidates,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    decodeTrial,trialCandidates,fixedPairAccept]
  cases hl : readWord history positions.left.toList <;>
    cases hr : readWord history positions.right.toList <;>
    simp only [Option.bind_none,Option.bind_some,Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,List.find?_nil,Option.isSome_none,fixedCandidates_take]
  rfl

theorem actualSingleRound_verified_isSome (Q : Point) (history : List Bool) :
    (verifiedCandidate actualSingleRoundLayout Q history).isSome =
      actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) history :=
  wrappedTrial_verified_isSome _ Q _ history

/-- The compiled round's acceptance is evaluated by the protected verifiedCandidate function. -/
theorem actualCompiledRound_verified_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    Instrument.bornMass
      (((batchedOuterPlan.round 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate actualSingleRoundLayout Q b.history).isSome)) (ket zeroBasisState) =
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if wrappedPairAccept legacyDecoderParams Q (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) := by
  rw [batchedOuterPlan_round_run Q hQ 0 Fin.elim0]
  simp only [actualSingleRound_verified_isSome]
  exact actualRoundSource_fixedPair_mass Q hQ hn _
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: DecoderBridge ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/DecoderBridge.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. The per-round lower
bound `wrappedIdeal_mass_lower` is now the averaged bound `27/50` of `AveragedSuccess` instead of
the protected pointwise bound `163/1000`. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
open scoped BigOperators

theorem fixedCandidates_legacy_eq (out : Fin (2^256) × Fin (2^208)) :
    fixedCandidates legacyDecoderParams out.1.val out.2.val = reducedShiftCandidates order 256 208 out := rfl

theorem wrappedPairAccept_legacy_iff (Q : Point) (out : Fin (2^256) × Fin (2^208)) :
    wrappedPairAccept legacyDecoderParams Q out.1.val out.2.val = true ↔
      (reducedVerifiedCandidate Q out).isSome = true := by
  classical
  rw [wrappedPairAccept,fixedCandidates_legacy_eq]
  simp only [List.find?_isSome,Finset.mem_toList,decide_eq_true_eq]
  unfold reducedVerifiedCandidate
  split_ifs with h
  · simp only [Option.isSome_some,iff_true]; exact h
  · simp only [Option.isSome_none,Bool.false_eq_true,iff_false]; exact h

attribute [local irreducible] wrappedPairAccept reducedVerifiedCandidate

theorem old_accept_implies_wrapped (Q : Point) (out : List Bool × List Bool)
    (h : reducedRawDecoderAccept Q out = true) :
    wrappedPairAccept legacyDecoderParams Q (fourierWordLSB out.1) (fourierWordLSB out.2) = true := by
  unfold reducedRawDecoderAccept reducedRawPublicDecode at h
  split_ifs at h with hl
  · let out' : Fin (2^256) × Fin (2^208) :=
      (⟨fourierWordLSB out.1, by simpa [hl.1] using fourierWordLSB_lt out.1⟩,
       ⟨fourierWordLSB out.2, by simpa [hl.2] using fourierWordLSB_lt out.2⟩)
    exact (wrappedPairAccept_legacy_iff Q out').mpr h
  · simp at h

theorem wrappedAccept_paperOutcomes (Q : Point) (out : Fin (2^256) × Fin (2^208)) :
    wrappedPairAccept legacyDecoderParams Q
      (fourierWordLSB (paperOutcomeBits 256 out.1)) (fourierWordLSB (paperOutcomeBits 208 out.2)) =
      reducedRawDecoderAccept Q (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [paperOutcomeBits_word]
  rw [wrappedPairAccept_legacy_iff]
  simp [reducedRawDecoderAccept,reducedRawPublicDecode,paperOutcomeBits_length,paperOutcomeBits_word]

theorem wrappedIdeal_mass_eq (Q : Point) (hG : G≠0) (hQ : Q≠0) (hrQ : order • Q=0) :
    reducedRawIdealFourierEventMass G Q
      (fun xy => wrappedPairAccept legacyDecoderParams Q (fourierWordLSB xy.1) (fourierWordLSB xy.2)) =
      reducedRawIdealFourierEventMass G Q (reducedRawDecoderAccept Q) := by
  rw [reducedRawIdealFourierEventMass_distribution G Q hG hQ generator_nsmul_eq_zero hrQ,
      reducedRawIdealFourierEventMass_distribution G Q hG hQ generator_nsmul_eq_zero hrQ]
  apply Finset.sum_congr rfl
  intro out _
  rw [wrappedAccept_paperOutcomes]

theorem wrappedIdeal_mass_lower (Q : Point) (hG : G≠0) (hQ : Q≠0) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    (27:ℝ)/50 ≤ reducedRawIdealFourierEventMass G Q
      (fun xy => wrappedPairAccept legacyDecoderParams Q (fourierWordLSB xy.1) (fourierWordLSB xy.2)) := by
  rw [wrappedIdeal_mass_eq Q hG hQ hrQ,reducedRawIdealDecoder_eq Q hG hQ hrQ d hQd,
    reducedPhysicalVerifiedMass_eq Q hG hQ hrQ d hQd]
  exact ShorECDLP.Entrant.Averaged.reducedVerifiedMass_averaged Q d hQd hQ
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: RoundBoundary ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/RoundBoundary.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] streamAddress fourierOutcomes actualFirstSource actualOddSource fourierBranch Quantum.run
private theorem smul_support {V : BasisState → Prop} (c : ℂ) {ψ : State}
    (h : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply h s
  intro he
  exact hs (by simp [he])

/-- Continuation composition preserves reached-state predicates branch by branch. -/
theorem streamBlockContinuation_supported {V W : BasisState → Prop}
    (call : AdaptiveCircuit) (prior : List Bool) (next : List Bool → Instrument)
    (hcall : ∀ b ∈ call.run, ∀ ψ, SupportedOn V ψ → SupportedOn BatchedWindowValid (b.kraus ψ))
    (hnext : ∀ bits b, b ∈ next bits → ∀ ψ, SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn V (Quantum.run (streamAddress.map Gate.H) ψ))
    (b : InstrumentBranch) (hb : b ∈ streamBlockContinuation call prior next) :
    SupportedOn W (b.kraus ψ) := by
  rw [streamBlockContinuation_eq] at hb
  have hu : (AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).run =
      [⟨List.nil, Quantum.run (streamAddress.map Gate.H)⟩] := AdaptiveCircuit.run_unitary_done _
  rw [hu] at hb
  simp only [Instrument.seq,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hb
  obtain ⟨bc,hbc,rfl⟩ := List.mem_map.mp hb
  obtain ⟨c,hc,hmap⟩ := List.mem_flatMap.mp hbc
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hmap
  rw [fourierContinuationInstrument] at hf
  obtain ⟨bits,hbits,hfm⟩ := List.mem_flatMap.mp hf
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hfm
  change SupportedOn W (d.kraus (fourierBranch .inverse streamAddress.reverse prior bits
    (c.kraus (Quantum.run (streamAddress.map Gate.H) ψ))))
  exact hnext bits d hd _ (batchedWindowValid_fourierBranch .inverse streamAddress.reverse
    (fun w hw => List.mem_reverse.mp hw) prior bits _ (hcall c hc _ hψ))

theorem actualSourceAxis_supported (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (ws : List OddWindow) (prior : List Bool) (next : List Bool → Instrument)
    (W : BasisState → Prop)
    (hnext : ∀ bits b, b ∈ next bits → ∀ ψ, SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ)
    (b : InstrumentBranch) (hb : b ∈ selectedSourceAxis (actualOddSource Q) ws prior next) :
    SupportedOn W (b.kraus ψ) := by
  induction ws generalizing prior ψ b with
  | nil => exact hnext prior b hb ψ hψ
  | cons w ws ih =>
    apply streamBlockContinuation_supported (V := BatchedWindowValid) (W := W) (actualOddSource Q w) prior _ ?_ ?_ ψ
      (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ) b hb
    · intro c hc φ hφ
      obtain ⟨a,ha⟩ := (actualOddSource_coherent Q hQ hn w).branch_coefficient c hc
      rw [ha.on_supported hφ]
      exact smul_support a (actualBatchedWindowState_supported Q hQ hn w φ hφ)
    · intro bits c hc φ hφ
      exact ih _ φ hφ c hc

theorem actualSourceTwoAxes_supported (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (left right : List OddWindow) (next : List Bool → List Bool → Instrument)
    (W : BasisState → Prop)
    (hnext : ∀ lhs rhs b, b ∈ next lhs rhs → ∀ ψ,
      SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ)
    (b : InstrumentBranch)
    (hb : b ∈ selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right next) :
    SupportedOn W (b.kraus ψ) := by
  apply streamBlockContinuation_supported (V := FirstWindowInput) (W := W)
    (actualFirstSource Q) List.nil _ ?_ ?_ ψ
    (firstWindowInput_prepare _ (fun _ h => h) ψ hψ) b hb
  · intro c hc φ hφ
    obtain ⟨a,ha⟩ := (actualFirstSource_coherent_input Q hQ).branch_coefficient c hc
    rw [ha.on_supported hφ]
    exact smul_support a (actualFirstWindowState_supported Q φ hφ)
  · intro bits c hc φ hφ
    apply actualSourceAxis_supported Q hQ hn left bits.reverse _ W ?_ φ hφ c hc
    intro lhs d hd χ hχ
    exact actualSourceAxis_supported Q hQ hn right List.nil _ W (hnext lhs) χ hχ d hd

theorem batchedReset_flag_absent : 837 ∉ batchedResetWires := by
  simp [batchedResetWires,resetWires]

theorem actualRoundTail_zeroFlag (b : InstrumentBranch)
    (hb : b ∈ (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection batchedResetWires (fun _ => []))).run)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn (fun s => s 837=false) (b.kraus ψ) := by
  refine AdaptiveCircuit.branch_frame _ 837 false ?_ b hb ψ ?_
  · simp only [AdaptiveCircuit.wires,List.mem_append,not_or]
    constructor
    · simp [circuitWires,gateWires]
    · intro h
      exact batchedReset_flag_absent (resetRegister_support _ h)
  · intro s hs
    exact (hψ s hs).1.1.1.2.1

theorem actualAxesTail_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (left right : List OddWindow) (b : InstrumentBranch)
    (hb : b ∈ selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right
      (fun _ _ => (AdaptiveCircuit.unitary [.X 836]
        (measureResetWithCorrection batchedResetWires (fun _ => []))).run)) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket (zeroBasisState[836 ↦ true]))) := by
  exact actualSourceTwoAxes_supported Q hQ hn left right _ _
    (fun _ _ => actualRoundTail_zeroFlag) _
    (supportedOn_ket _ _ firstWindowInput_start) b hb

theorem actualRoundSource_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket zeroBasisState)) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,actualLeftSources_indices,actualRightSources_indices] at hb
  rw [AdaptiveCircuit.run, ← selectedSourceTwoAxes_constant] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  change SupportedOn (fun s => s 837=false) (c.kraus (Quantum.run [.X 836] (ket zeroBasisState)))
  rw [hx]
  exact actualAxesTail_zeroFlag Q hQ hn leftOddIndices rightOddIndices c hc

theorem actualCompiledRound_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket zeroBasisState)) := by
  rw [batchedOuterPlan_round_run Q hQ start history] at hb
  exact actualRoundSource_zeroFlag Q hQ hn b hb
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: WindowBranchSum ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowBranchSum.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1
noncomputable section
attribute [local irreducible] fourierOutcomes actualBatchedWindowState

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
    streamAddress.map (actualBatchedWindowState Q w (phaseWordState streamAddress input s)) = input := by
  have hv : BatchedWindowValid (phaseWordState streamAddress input s) :=
    phaseWordState_preserves BatchedWindowValid streamAddress
      (fun t ht v hv b => batchedWindowValid_address_update t ht v hv b) input s hs
  calc
    _ = streamAddress.map (phaseWordState streamAddress input s) := by
      apply List.map_congr_left
      intro v hva
      exact actualBatchedWindowState_frame Q hQ hn w _ hv v
        ((show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hva)
    _ = input := phaseWordState_word streamAddress (by decide +kernel) input hi s

/-- Exact amplitude sum for an actual corrected window and one fixed Fourier
output. All input amplitudes are added before any Born mass is taken. -/
theorem actual_window_branch_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (prior output : List Bool) (s : BasisState)
    (hs : BatchedWindowValid s) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (fourierClear streamAddress.reverse
              (actualBatchedWindowState Q w (phaseWordState streamAddress input s))))).sum := by
  simpa only [show streamAddress.length = 16 by decide +kernel] using
    window_branch_uniform .inverse streamAddress (by decide +kernel)
      (actualBatchedWindowState Q w) prior output s hz
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
    actualBatchedWindowState Q w s = pointWrite (P + windowDigitPoint Q w (windowRawDigit 0 s)) s := by
  cases w with
  | left j => exact actual_left_window_digit Q hQ hn j s hs P hP
  | right j => exact actual_right_window_digit Q hQ hn j s hs P hP

theorem actual_window_assigned_clear (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (P : Point) (s : BasisState) (hs : FirstWindowInput s)
    (hz : Clean streamAddress s) (input : List Bool) (hi : input.length = streamAddress.length) :
    fourierClear streamAddress.reverse
      (actualBatchedWindowState Q w (phaseWordState streamAddress input (pointWrite P s))) =
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
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
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
          ((Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)).comp
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

-- ==== part: IdealDistribution ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/IdealDistribution.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1
noncomputable section
attribute [local irreducible] fourierOutcomes

def axisInputWords : Nat → List (List (List Bool))
  | 0 => [[]]
  | n+1 => (fourierOutcomes 16).flatMap (fun input =>
      (axisInputWords n).map (fun rest => input :: rest))

def axisInputEnd (Q : Point) : List (OddWindow × List Bool) → List (List Bool) → Point → Point
  | (w, _) :: windows, input :: inputs, P =>
      axisInputEnd Q windows inputs (P + windowDigitPoint Q w (boolWordToNat input))
  | _, _, P => P

def axisInputWeight : List (OddWindow × List Bool) → List Bool → List (List Bool) → ℂ
  | (_, output) :: windows, prior, input :: inputs =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) *
        fourierBitAmplitude .inverse input.reverse prior output *
          axisInputWeight windows (output.reverse ++ prior) inputs
  | _, _, _ => 1

private theorem flat_sum {A B : Type} [AddCommMonoid B] (xs : List A) (f : A → List B) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

theorem pointAxisKernel_inputs (Q : Point) (s : BasisState)
    (windows : List (OddWindow × List Bool)) (prior : List Bool) (P : Point) :
    pointAxisKernel Q s windows prior P =
      ((axisInputWords windows.length).map (fun inputs =>
        axisInputWeight windows prior inputs • ket (pointWrite (axisInputEnd Q windows inputs P) s))).sum := by
  induction windows generalizing prior P with
  | nil => simp [pointAxisKernel, axisInputWords, axisInputWeight, axisInputEnd]
  | cons w windows ih =>
    simp only [pointAxisKernel, List.length_cons, axisInputWords, List.map_flatMap,
      List.map_map, Function.comp_def, axisInputWeight, axisInputEnd, flat_sum]
    simp_rw [ih]
    simp only [smul_smul, List.smul_sum, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro input hi
    congr 1
    apply List.map_congr_left
    intro inputs his
    rw [mul_assoc]
def axisInputPairs (windows : List (OddWindow × List Bool)) (inputs : List (List Bool)) :
    List (List Bool × List Bool) :=
  (windows.zip inputs).map (fun p => (p.2.reverse, p.1.2))

theorem axisInputWeight_amplitude (windows : List (OddWindow × List Bool))
    (prior : List Bool) (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    axisInputWeight windows prior inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (16 * windows.length)) *
        windowFourierAmplitude .inverse (axisInputPairs windows inputs) prior := by
  induction windows generalizing prior inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs
    simp [axisInputWeight, axisInputPairs, windowFourierAmplitude]
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      have ht : inputs.length = windows.length := by simpa using hl
      simp only [axisInputWeight, axisInputPairs, List.zip_cons_cons, List.map_cons,
        windowFourierAmplitude, List.length_cons]
      rw [ih _ inputs ht]
      change _ = _ * (fourierBitAmplitude .inverse input.reverse prior w.2 *
        windowFourierAmplitude .inverse (axisInputPairs windows inputs) (w.2.reverse ++ prior))
      rw [show 16 * (windows.length + 1) = 16 + 16 * windows.length by omega, pow_add]
      ring

theorem axisInputPairs_lengths (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool))
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    ∀ pair ∈ axisInputPairs windows inputs, pair.2.length = pair.1.length := by
  intro pair hp
  unfold axisInputPairs at hp
  obtain ⟨p, hzip, he⟩ := List.mem_map.mp hp
  subst pair
  have hw := List.of_mem_zip hzip
  simp only [List.length_reverse]
  rw [ho p.1 hw.1, hi p.2 hw.2]

/-- The coefficient of a whole input path has the exact full-axis kernel,
including both Hadamard preparation and Fourier normalization. -/
theorem axisInputWeight_kernel (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length)
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    axisInputWeight windows List.nil inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (16 * windows.length)) *
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ ((axisInputPairs windows inputs).map Prod.fst).flatten.length) *
        dyadicFourierKernel .inverse ((axisInputPairs windows inputs).map Prod.fst).flatten.length
          (fourierWordMSB ((axisInputPairs windows inputs).map Prod.fst).flatten)
          (fourierWordLSB ((axisInputPairs windows inputs).map Prod.snd).flatten) := by
  rw [axisInputWeight_amplitude windows List.nil inputs hl,
    windowFourierAmplitude_kernel .inverse _ (axisInputPairs_lengths windows inputs ho hi)]
  ring

theorem fourierOutcomes_reverse_perm (n : Nat) :
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

theorem fourierOutcomes_append (n m : Nat) : fourierOutcomes (n + m) =
    (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a ++ b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add, fourierOutcomes, ih, List.flatMap_append, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def, List.cons_append]

theorem axisInputWords_flatten (n : Nat) :
    (axisInputWords n).map List.flatten = fourierOutcomes (16 * n) := by
  induction n with
  | zero => simp [axisInputWords, fourierOutcomes]
  | succ n ih =>
    rw [show 16 * (n + 1) = 16 + 16 * n by omega, fourierOutcomes_append]
    simp only [axisInputWords, List.map_flatMap, List.map_map, Function.comp_def, List.flatten_cons]
    apply congrArg (List.flatMap · (fourierOutcomes 16))
    funext input
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map (input ++ ·)) ih

theorem axisInputWords_mem (n : Nat) (inputs : List (List Bool)) :
    inputs ∈ axisInputWords n ↔ inputs.length = n ∧ ∀ bits ∈ inputs, bits.length = 16 := by
  induction n generalizing inputs with
  | zero => cases inputs <;> simp [axisInputWords]
  | succ n ih =>
    cases inputs with
    | nil => simp [axisInputWords, List.mem_flatMap]
    | cons input inputs =>
      simp [axisInputWords, List.mem_flatMap, List.mem_map, List.cons.injEq,
        fourierOutcomes_mem, ih, and_assoc, and_left_comm, and_comm]

theorem axisInputWords_reverse_perm (n : Nat) :
    ((axisInputWords n).map (List.map List.reverse)).Perm (axisInputWords n) := by
  induction n with
  | zero => simp [axisInputWords]
  | succ n ih =>
    simp only [axisInputWords]
    have he : ((fourierOutcomes 16).flatMap (fun input =>
        (axisInputWords n).map (fun rest => input :: rest))).map (List.map List.reverse) =
      ((fourierOutcomes 16).map List.reverse).flatMap (fun input =>
        ((axisInputWords n).map (List.map List.reverse)).map (fun rest => input :: rest)) := by
      simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, List.map_cons]
    rw [he]
    exact (fourierOutcomes_reverse_perm 16).flatMap (fun input _ => ih.map (input :: ·))

/-- Reversing each physical input window gives every full MSB-first input word
exactly once, so regrouping the coherent sum does not change multiplicity. -/
theorem axisInputWords_msb_perm (n : Nat) :
    ((axisInputWords n).map (fun inputs => (inputs.map List.reverse).flatten)).Perm
      (fourierOutcomes (16 * n)) := by
  have hp := (axisInputWords_reverse_perm n).map List.flatten
  simpa only [List.map_map, Function.comp_def, axisInputWords_flatten] using hp

theorem axisInputEnd_sum (Q : Point) (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (P : Point) :
    axisInputEnd Q windows inputs P = P +
      ((windows.zip inputs).map (fun p => windowDigitPoint Q p.1.1 (boolWordToNat p.2))).sum := by
  induction windows generalizing inputs P with
  | nil => simp [axisInputEnd]
  | cons w windows ih =>
    cases inputs with
    | nil => simp [axisInputEnd]
    | cons input inputs =>
      simp only [axisInputEnd, List.zip_cons_cons, List.map_cons, List.sum_cons, ih]
      exact add_assoc _ _ _

theorem axisInputPairs_fst (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    (axisInputPairs windows inputs).map Prod.fst = inputs.map List.reverse := by
  induction windows generalizing inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [axisInputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

theorem axisInputPairs_snd (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    (axisInputPairs windows inputs).map Prod.snd = windows.map Prod.snd := by
  induction windows generalizing inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [axisInputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

/-- A path has one preparation factor and one Fourier factor per input bit. -/
theorem axisInputWeight_full_kernel (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length)
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    axisInputWeight windows List.nil inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (32 * windows.length)) *
        dyadicFourierKernel .inverse (16 * windows.length)
          (fourierWordMSB (inputs.map List.reverse).flatten)
          (fourierWordLSB (windows.map Prod.snd).flatten) := by
  have hlen : (inputs.map List.reverse).flatten.length = 16 * windows.length := by
    rw [fixed_windows_flatten_length 16 _]
    · simp only [List.length_map, hl]
    · intro bits hb
      obtain ⟨input, hm, he⟩ := List.mem_map.mp hb
      subst bits
      simpa only [List.length_reverse] using hi input hm
  rw [axisInputWeight_kernel windows inputs hl ho hi,
    axisInputPairs_fst windows inputs hl, axisInputPairs_snd windows inputs hl, hlen,
    ← pow_add, show 16 * windows.length + 16 * windows.length = 32 * windows.length by omega]

def descendingOddValue : List Nat → Int
  | [] => 0
  | d :: ds => signedTableOdd 32768 d * 65536 ^ ds.length + descendingOddValue ds

private theorem signedValue_append (xs ys : List Int) :
    signedWindowValue 65536 (xs ++ ys) =
      signedWindowValue 65536 xs + (65536 : Int) ^ xs.length * signedWindowValue 65536 ys := by
  induction xs with
  | nil => simp [signedWindowValue]
  | cons x xs ih =>
    simp only [List.cons_append, signedWindowValue, List.length_cons, ih, pow_succ]
    ring

theorem descendingOddValue_reverse (digits : List Nat) :
    descendingOddValue digits = signedWindowValue 65536 (digits.reverse.map (signedTableOdd 32768)) := by
  induction digits with
  | nil => rfl
  | cons d ds ih =>
    simp only [descendingOddValue, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, signedValue_append, List.length_map, List.length_reverse,
      signedWindowValue, ih]
    ring

/-- Each chronological window uses the descending power belonging to its
remaining suffix. This proposition concerns only fixed labels and weights. -/
def DescendingAxisWeights (Q P : Point) : List (OddWindow × List Bool) → Prop
  | [] => True
  | (w, _) :: windows =>
      (∀ digit, windowDigitPoint Q w digit =
        signedTableOdd 32768 digit • (65536 ^ windows.length • signedWindowHalfPoint P order)) ∧
      DescendingAxisWeights Q P windows

theorem axisInputEnd_weighted (Q P : Point) (windows : List (OddWindow × List Bool))
    (hw : DescendingAxisWeights Q P windows) (inputs : List (List Bool))
    (hl : inputs.length = windows.length) (A : Point) :
    axisInputEnd Q windows inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint P order := by
  induction windows generalizing inputs A with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs
    simp [axisInputEnd, descendingOddValue]
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      have ht : inputs.length = windows.length := by simpa using hl
      simp only [axisInputEnd]
      rw [ih hw.2 inputs ht, hw.1]
      simp only [List.map_cons, descendingOddValue, List.length_map, ht, add_zsmul]
      rw [mul_zsmul, show (65536 : Int) ^ windows.length = ((65536 ^ windows.length : Nat) : Int) by norm_cast, natCast_zsmul]
      exact add_assoc _ _ _

def DescendingLabelWeights (Q P : Point) : List OddWindow → Prop
  | [] => True
  | w :: windows =>
      (∀ digit, windowDigitPoint Q w digit =
        signedTableOdd 32768 digit • (65536 ^ windows.length • signedWindowHalfPoint P order)) ∧
      DescendingLabelWeights Q P windows

theorem descendingLabelWeights_zip (Q P : Point) (windows : List OddWindow)
    (hw : DescendingLabelWeights Q P windows) (outputs : List (List Bool))
    (hl : outputs.length = windows.length) : DescendingAxisWeights Q P (windows.zip outputs) := by
  induction windows generalizing outputs with
  | nil => simp [DescendingAxisWeights]
  | cons w windows ih =>
    cases outputs with
    | nil => simp at hl
    | cons output outputs =>
      have ht : outputs.length = windows.length := by simpa using hl
      simp only [List.zip_cons_cons, DescendingAxisWeights, List.length_zip, ht, min_self]
      exact ⟨hw.1, ih hw.2 outputs ht⟩

theorem left_labels_weights (Q : Point) : DescendingLabelWeights Q G leftOddIndices := by
  norm_num [leftOddIndices, List.ofFn_succ, DescendingLabelWeights, windowDigitPoint, pow_mul]

theorem right_labels_weights (Q : Point) : DescendingLabelWeights Q Q rightOddIndices := by
  norm_num [rightOddIndices, List.ofFn_succ, DescendingLabelWeights, windowDigitPoint, pow_mul]

theorem left_axis_input_end (Q : Point) (outputs inputs : List (List Bool))
    (ho : outputs.length = 15) (hi : inputs.length = 15) (A : Point) :
    axisInputEnd Q (leftOddIndices.zip outputs) inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint G order := by
  apply axisInputEnd_weighted
  · apply descendingLabelWeights_zip Q G _ (left_labels_weights Q) outputs
    simpa only [leftOddIndices, List.length_ofFn] using ho
  · simpa only [List.length_zip, leftOddIndices, List.length_ofFn, ho, min_self] using hi

theorem right_axis_input_end (Q : Point) (outputs inputs : List (List Bool))
    (ho : outputs.length = 13) (hi : inputs.length = 13) (A : Point) :
    axisInputEnd Q (rightOddIndices.zip outputs) inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint Q order := by
  apply axisInputEnd_weighted
  · apply descendingLabelWeights_zip Q Q _ (right_labels_weights Q) outputs
    simpa only [rightOddIndices, List.length_ofFn] using ho
  · simpa only [List.length_zip, rightOddIndices, List.length_ofFn, ho, min_self] using hi

theorem actual_two_axes_input_end (Q : Point) (hQ : order • Q = 0)
    (first : List Bool) (left right outputsL outputsR : List (List Bool))
    (hl : left.length = 15) (hr : right.length = 13)
    (hol : outputsL.length = 15) (hor : outputsR.length = 13) :
    axisInputEnd Q (rightOddIndices.zip outputsR) right
      (axisInputEnd Q (leftOddIndices.zip outputsL) left
        (axisWindowOffset G 16 + axisWindowOffset Q 13 +
          signedTableOdd 32768 (boolWordToNat first) •
            ((2 ^ (16 * 15)) • signedWindowHalfPoint G order))) =
      windowValue 65536 ((first :: left).map boolWordToNat).reverse • G +
        windowValue 65536 (right.map boolWordToNat).reverse • Q := by
  rw [right_axis_input_end Q outputsR right hor hr,
    left_axis_input_end Q outputsL left hol hl]
  have hgroup := two_axis_signed_digits Q hQ
    ((first :: left).map boolWordToNat).reverse (right.map boolWordToNat).reverse
    (by simp only [List.length_reverse, List.length_map, List.length_cons, hl])
    (by simp only [List.length_reverse, List.length_map, hr])
  rw [← descendingOddValue_reverse, ← descendingOddValue_reverse] at hgroup
  rw [← hgroup]
  simp only [List.map_cons, descendingOddValue, List.length_map, hl, add_zsmul, mul_zsmul]
  rw [show (65536 : Int) ^ 15 = ((65536 ^ 15 : Nat) : Int) by norm_cast, natCast_zsmul,
    show 2 ^ (16 * 15) = 65536 ^ 15 by decide +kernel]
  abel

/-- The actual two-axis branch is one coherent sum over all three input
blocks: the direct first load, the remaining left windows, and the right axis. -/
theorem actual_two_axes_state_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (firstOutput : List Bool) (left right : List (OddWindow × List Bool))
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    actualAxisBranch Q right List.nil
      (actualAxisBranch Q left firstOutput.reverse
        (fourierBranch .inverse streamAddress.reverse List.nil firstOutput
          (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
            (Quantum.run (streamAddress.map Gate.H) (ket s))))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun firstInput =>
          fourierBitAmplitude .inverse firstInput.reverse List.nil firstOutput •
            ((axisInputWords left.length).map (fun inputsL =>
              axisInputWeight left firstOutput.reverse inputsL •
                ((axisInputWords right.length).map (fun inputsR =>
                  axisInputWeight right List.nil inputsR •
                    ket (pointWrite
                      (axisInputEnd Q right inputsR
                        (axisInputEnd Q left inputsL
                          (axisWindowOffset G 16 + axisWindowOffset Q 13 +
                            signedTableOdd 32768 (boolWordToNat firstInput) •
                              ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)))) s))).sum)).sum)).sum := by
  rw [actual_first_point_sum Q List.nil firstOutput s hz]
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def,
    actualAxisBranch_point Q hQ hn s hs hz]
  simp_rw [pointAxisKernel_inputs]
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def,
    actualAxisBranch_point Q hQ hn s hs hz, pointAxisKernel_inputs]

def inputScalarWord (inputs : List (List Bool)) : List Bool :=
  (inputs.map List.reverse).flatten.reverse

theorem inputScalarWord_perm (n : Nat) :
    ((axisInputWords n).map inputScalarWord).Perm (fourierOutcomes (16 * n)) := by
  have hp := (axisInputWords_msb_perm n).map List.reverse
  simpa only [List.map_map, Function.comp_def, inputScalarWord] using
    hp.trans (fourierOutcomes_reverse_perm (16 * n))

theorem inputScalarWord_value (inputs : List (List Bool))
    (hi : ∀ bits ∈ inputs, bits.length = 16) :
    boolWordToNat (inputScalarWord inputs) =
      windowValue 65536 (inputs.map boolWordToNat).reverse := by
  rw [← fourierWordMSB_reverse]
  simp only [inputScalarWord, List.reverse_reverse]
  have h := input_windows_value 16 (inputs.map List.reverse) (by
    intro bits hb
    obtain ⟨input, hm, he⟩ := List.mem_map.mp hb
    subst bits
    simpa only [List.length_reverse] using hi input hm)
  simpa only [List.map_map, Function.comp_def, fourierWordMSB_reverse] using h

theorem two_axis_input_kernel (left right : List (OddWindow × List Bool))
    (inputsL inputsR : List (List Bool)) (hl : left.length = 16) (hr : right.length = 13)
    (hil : inputsL.length = left.length) (hir : inputsR.length = right.length)
    (hol : ∀ w ∈ left, w.2.length = 16) (hor : ∀ w ∈ right, w.2.length = 16)
    (hbl : ∀ bits ∈ inputsL, bits.length = 16) (hbr : ∀ bits ∈ inputsR, bits.length = 16) :
    axisInputWeight left List.nil inputsL * axisInputWeight right List.nil inputsR =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928) *
        dyadicFourierKernel .inverse 256 (boolWordToNat (inputScalarWord inputsL))
          (fourierWordLSB (left.map Prod.snd).flatten) *
        dyadicFourierKernel .inverse 208 (boolWordToNat (inputScalarWord inputsR))
          (fourierWordLSB (right.map Prod.snd).flatten) := by
  rw [axisInputWeight_full_kernel left inputsL hil hol hbl,
    axisInputWeight_full_kernel right inputsR hir hor hbr, hl, hr]
  have hw (inputs : List (List Bool)) :
      fourierWordMSB (inputs.map List.reverse).flatten = boolWordToNat (inputScalarWord inputs) := by
    simpa only [inputScalarWord, List.reverse_reverse] using
      fourierWordMSB_reverse (inputScalarWord inputs)
  rw [hw, hw, show (928 : Nat) = 32 * 16 + 32 * 13 by decide, pow_add]
  ring

theorem axisInputWords_sum_succ {A : Type} [AddCommMonoid A] (n : Nat)
    (f : List (List Bool) → A) :
    ((axisInputWords (n + 1)).map f).sum =
      ((fourierOutcomes 16).map (fun input =>
        ((axisInputWords n).map (fun inputs => f (input :: inputs))).sum)).sum := by
  simp only [axisInputWords, List.map_flatMap, List.map_map, Function.comp_def, flat_sum]

def twoAxisInputState (Q : Point) (s : BasisState) (x y : List Bool) : State :=
  ((axisInputWords 16).map (fun inputsL =>
    ((axisInputWords 13).map (fun inputsR =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
        dyadicFourierKernel .inverse 256 (boolWordToNat (inputScalarWord inputsL)) (fourierWordLSB x) *
        dyadicFourierKernel .inverse 208 (boolWordToNat (inputScalarWord inputsR)) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat (inputScalarWord inputsL) • G +
        boolWordToNat (inputScalarWord inputsR) • Q) s))).sum)).sum

theorem actual_two_axes_input_state (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (firstOutput : List Bool) (outputsL outputsR : List (List Bool))
    (ho0 : firstOutput.length = 16) (hol : outputsL.length = 15) (hor : outputsR.length = 13)
    (hbl : ∀ bits ∈ outputsL, bits.length = 16) (hbr : ∀ bits ∈ outputsR, bits.length = 16)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    actualAxisBranch Q (rightOddIndices.zip outputsR) List.nil
      (actualAxisBranch Q (leftOddIndices.zip outputsL) firstOutput.reverse
        (fourierBranch .inverse streamAddress.reverse List.nil firstOutput
          (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
            (Quantum.run (streamAddress.map Gate.H) (ket s))))) =
      twoAxisInputState Q s (firstOutput :: outputsL).flatten outputsR.flatten := by
  have hll : (leftOddIndices.zip outputsL).length = 15 := by
    simp only [List.length_zip, leftOddIndices, List.length_ofFn, hol, min_self]
  have hrl : (rightOddIndices.zip outputsR).length = 13 := by
    simp only [List.length_zip, rightOddIndices, List.length_ofFn, hor, min_self]
  rw [actual_two_axes_state_sum Q hQ hn firstOutput _ _ s hs hz, hll, hrl,
    twoAxisInputState, axisInputWords_sum_succ 15]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro firstInput hf
  apply congrArg List.sum
  apply List.map_congr_left
  intro inputsL hlm
  apply congrArg List.sum
  apply List.map_congr_left
  intro inputsR hrm
  have hf' := (fourierOutcomes_mem 16 firstInput).mp hf
  have hl' := (axisInputWords_mem 15 inputsL).mp hlm
  have hr' := (axisInputWords_mem 13 inputsR).mp hrm
  have hli : ∀ bits ∈ firstInput :: inputsL, bits.length = 16 := by
    intro bits hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hf'
    · exact hl'.2 bits hb
  rw [actual_two_axes_input_end Q hQ firstInput inputsL inputsR outputsL outputsR
    hl'.1 hr'.1 hol hor,
    ← inputScalarWord_value (firstInput :: inputsL) hli,
    ← inputScalarWord_value inputsR hr'.2]
  apply congrArg (fun c : ℂ => c • ket (pointWrite
    (boolWordToNat (inputScalarWord (firstInput :: inputsL)) • G +
      boolWordToNat (inputScalarWord inputsR) • Q) s))
  let left : List (OddWindow × List Bool) := (.left ⟨0, by decide⟩, firstOutput) :: leftOddIndices.zip outputsL
  have hcoef := two_axis_input_kernel left (rightOddIndices.zip outputsR)
    (firstInput :: inputsL) inputsR (by simp only [left, List.length_cons, hll]) hrl
    (by simp only [left, List.length_cons, hll, hl'.1]) (hr'.1.trans hrl.symm)
    (by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ho0
      · exact hbl w.2 (List.of_mem_zip hw).2)
    (fun w hw => hbr w.2 (List.of_mem_zip hw).2) hli hr'.2
  have hls : (leftOddIndices.zip outputsL).map Prod.snd = outputsL :=
    List.map_snd_zip (by simp only [leftOddIndices, List.length_ofFn, hol, le_refl])
  have hrs : (rightOddIndices.zip outputsR).map Prod.snd = outputsR :=
    List.map_snd_zip (by simp only [rightOddIndices, List.length_ofFn, hor, le_refl])
  simpa only [left, axisInputWeight, List.map_cons, hls, hrs, List.nil_append, List.append_nil,
    mul_assoc] using hcoef

theorem inputScalarWord_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : List Bool → A) :
    ((axisInputWords n).map (fun inputs => f (inputScalarWord inputs))).sum =
      ((fourierOutcomes (16 * n)).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using ((inputScalarWord_perm n).map f).sum_eq

def idealPointState (Q : Point) (s : BasisState) (x y : List Bool) : State :=
  ((fourierOutcomes 256).map (fun a =>
    ((fourierOutcomes 208).map (fun b =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
        dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x) *
        dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) s))).sum)).sum

theorem twoAxisInputState_ideal (Q : Point) (s : BasisState) (x y : List Bool) :
    twoAxisInputState Q s x y = idealPointState Q s x y := by
  let f (a b : List Bool) : State :=
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
      dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x) *
      dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) s)
  change ((axisInputWords 16).map (fun inputs =>
    ((axisInputWords 13).map (fun other => f (inputScalarWord inputs) (inputScalarWord other))).sum)).sum =
    ((fourierOutcomes 256).map (fun a => ((fourierOutcomes 208).map (f a)).sum)).sum
  simp_rw [inputScalarWord_sum (A := State) 13]
  exact inputScalarWord_sum (A := State) 16 (fun a => ((fourierOutcomes 208).map (f a)).sum)

theorem stream_kernel_idealPointState (Q : Point) (x y : List Bool) :
    measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) y
      (measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls G Q))) x
        (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput G Q) (streamPreparedEntry G Q))) =
      idealPointState Q (scalarRootFlip zeroBasisState) x y := by
  rw [streamFourierKernel_point_sum]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul, idealPointState]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  apply congrArg (fun c : ℂ => c • ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q)
    (scalarRootFlip zeroBasisState)))
  rw [show (928 : Nat) = 464 + 464 by decide, pow_add]
  ring

theorem windowOutputPaths_zip (windows : List OddWindow) :
    windowOutputPaths windows = (axisInputWords windows.length).map (windows.zip ·) := by
  induction windows with
  | nil => rfl
  | cons w windows ih =>
    simp only [windowOutputPaths, List.length_cons, axisInputWords, List.map_flatMap,
      List.map_map, Function.comp_def, List.zip_cons_cons, ih]

/-- Expose both chronological output paths while preserving the terminal event. -/
theorem selectedIdealTwoAxes_paths_mass (Q : Point) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) (ψ : State) :
    (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      ((fourierOutcomes 16).map (fun first =>
        ((windowOutputPaths left).map (fun lp =>
          ((windowOutputPaths right).map (fun rp =>
            (terminal ((lp.map Prod.snd).flatten.reverse ++ first.reverse)
              (rp.map Prod.snd).flatten.reverse).bornMass
                (actualAxisBranch Q rp List.nil (actualAxisBranch Q lp first.reverse
                  (fourierBranch .inverse streamAddress.reverse List.nil first
                    (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
                      (Quantum.run (streamAddress.map Gate.H) ψ))))))).sum)).sum)).sum := by
  have he : (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      (fourierContinuationInstrument List.nil (fun bits =>
        selectedIdealAxis Q left bits.reverse (fun lhs =>
          selectedIdealAxis Q right List.nil (terminal lhs)))).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
    simp only [selectedIdealTwoAxes, Instrument.bornMass, List.map_map, Function.comp_def,
      InstrumentBranch.seq, LinearMap.comp_apply]
  rw [he, fourierContinuationInstrument_mass]
  simp_rw [selectedIdealAxis_paths_mass]
  simp only [List.append_nil]

theorem selectedIdealTwoAxes_word_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (terminal : List Bool → List Bool → Instrument)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices terminal).bornMass (ket s) =
      ((axisInputWords 16).map (fun outputsL =>
        ((axisInputWords 13).map (fun outputsR =>
          (terminal outputsL.flatten.reverse outputsR.flatten.reverse).bornMass
            (idealPointState Q s outputsL.flatten outputsR.flatten))).sum)).sum := by
  rw [selectedIdealTwoAxes_paths_mass, windowOutputPaths_zip, windowOutputPaths_zip]
  simp only [show leftOddIndices.length = 15 by simp [leftOddIndices],
    show rightOddIndices.length = 13 by simp [rightOddIndices], List.map_map, Function.comp_def]
  rw [axisInputWords_sum_succ (A := ℝ) 15]
  apply congrArg List.sum
  apply List.map_congr_left
  intro firstOutput hf
  apply congrArg List.sum
  apply List.map_congr_left
  intro outputsL hlm
  apply congrArg List.sum
  apply List.map_congr_left
  intro outputsR hrm
  have hf' := (fourierOutcomes_mem 16 firstOutput).mp hf
  have hl' := (axisInputWords_mem 15 outputsL).mp hlm
  have hr' := (axisInputWords_mem 13 outputsR).mp hrm
  have hls : (leftOddIndices.zip outputsL).map Prod.snd = outputsL :=
    List.map_snd_zip (by simp only [leftOddIndices, List.length_ofFn, hl'.1, le_refl])
  have hrs : (rightOddIndices.zip outputsR).map Prod.snd = outputsR :=
    List.map_snd_zip (by simp only [rightOddIndices, List.length_ofFn, hr'.1, le_refl])
  rw [hls, hrs, actual_two_axes_input_state Q hQ hn firstOutput outputsL outputsR
    hf' hl'.1 hr'.1 hl'.2 hr'.2 s hs hz, twoAxisInputState_ideal]
  simp only [List.flatten_cons, List.reverse_append]

theorem outputWords_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : List Bool → A) :
    ((axisInputWords n).map (fun outputs => f outputs.flatten)).sum =
      ((fourierOutcomes (16 * n)).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun xs => (xs.map f).sum) (axisInputWords_flatten n)

/-- Exact output distribution of the full corrected 256/208-bit streaming
computation, expressed against an arbitrary output-dependent terminal instrument. -/
theorem selectedIdealTwoAxes_output_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (terminal : List Bool → List Bool → Instrument)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices terminal).bornMass (ket s) =
      ((fourierOutcomes 256).map (fun lhs =>
        ((fourierOutcomes 208).map (fun rhs =>
          (terminal lhs.reverse rhs.reverse).bornMass (idealPointState Q s lhs rhs))).sum)).sum := by
  rw [selectedIdealTwoAxes_word_mass Q hQ hn terminal s hs hz]
  let f (lhs rhs : List Bool) : ℝ :=
    (terminal lhs.reverse rhs.reverse).bornMass (idealPointState Q s lhs rhs)
  change ((axisInputWords 16).map (fun outputs =>
    ((axisInputWords 13).map (fun other => f outputs.flatten other.flatten)).sum)).sum =
    ((fourierOutcomes 256).map (fun lhs => ((fourierOutcomes 208).map (f lhs)).sum)).sum
  simp_rw [outputWords_sum (A := ℝ) 13]
  exact outputWords_sum (A := ℝ) 16 (fun lhs => ((fourierOutcomes 208).map (f lhs)).sum)

private theorem unitary_prefix_mass (c : Circuit) (tail : AdaptiveCircuit) (ψ : State) :
    (AdaptiveCircuit.unitary c tail).run.bornMass ψ = tail.run.bornMass (Quantum.run c ψ) := by
  simp only [AdaptiveCircuit.run, Instrument.bornMass, List.map_map, Function.comp_def]
  rfl

theorem actual_terminal_mass (ψ : State) :
    (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection batchedResetWires (fun _ => []))).run.bornMass ψ = normSq ψ := by
  calc
    _ = (measureResetWithCorrection batchedResetWires (fun _ => [])).run.bornMass
        (Quantum.run [.X 836] ψ) := unitary_prefix_mass _ _ _
    _ = normSq (Quantum.run [.X 836] ψ) := resetRegister_mass _ _
    _ = normSq ψ := normSq_run _ (by simp [CircuitWellFormed, Gate.WellFormed]) ψ

/-- The complete corrected streaming computation has exactly the ideal 256/208
Fourier event distribution, for any Boolean acceptance predicate. -/
theorem selectedIdealTwoAxes_event_eq (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (accept : Nat → Nat → Bool) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836]
          (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) =
      reducedRawIdealFourierEventMass G Q (fun xy =>
        accept (fourierWordLSB xy.1) (fourierWordLSB xy.2)) := by
  rw [selectedIdealTwoAxes_output_mass Q hQ hn _ _ firstWindowInput_start
    (by
      intro v hv
      have hb : 855 ≤ v := by simpa [streamAddress, List.mem_range'_1] using (And.left (by
        simpa [streamAddress, List.mem_range'_1] using hv : 855 ≤ v ∧ v < 855 + 16))
      simp [upd, zeroBasisState, show v ≠ 836 by dsimp only [Wire] at *; omega])]
  rw [← streamIdealFourierEventMass_eq G Q G_ne_zero hn generator_nsmul_eq_zero hQ]
  unfold streamFourierKernelEventMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro lhs hl
  apply congrArg List.sum
  apply List.map_congr_left
  intro rhs hr
  simp only [List.reverse_reverse]
  split_ifs
  · rw [actual_terminal_mass, stream_kernel_idealPointState]
    rfl
  · rfl

end
end ShorECDLP.Paper2607_13816.ChallengeMigration
