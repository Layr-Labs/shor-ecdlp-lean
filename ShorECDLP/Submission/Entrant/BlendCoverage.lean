import ShorECDLP.Submission.Entrant.SharpCoverage
namespace ShorECDLP.Entrant.BlendCDF
open Quantum Challenge Secp256k1 SinAverage261 SinAverage WindowMassSharpProof RoundedReadout NeighborReadout
open Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation Finset
open scoped BigOperators
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 300
set_option linter.unusedSimpArgs false

theorem tail_half (r : ℝ) (hr : 1/2<r) : tailBound r≤1/(r-1/2) := by
  have hr0 : 0<r := by linarith
  have hrm : 0<r-1/2 := by linarith
  have hrp : 0<r+1/2 := by linarith
  unfold tailBound
  rw [div_add_div _ _ (pow_ne_zero 2 hr0.ne') hrp.ne',
    div_le_div_iff₀ (mul_pos (sq_pos_of_pos hr0) hrp) hrm]
  nlinarith

theorem right_pair44 (e : ℝ) (he : |e|≤1/2) :
    tailBound (23-e)+tailBound (22+e)≤(44/483:ℝ) := by
  obtain ⟨heL,heU⟩ := abs_le.mp he
  have hx : 0<(23:ℝ)-e-1/2 := by linarith
  have hy : 0<(22:ℝ)+e-1/2 := by linarith
  have hp : (483:ℝ)≤(23-e-1/2)*(22+e-1/2) := by
    nlinarith [mul_nonneg (show 0≤1/2+e by linarith) (show 0≤1/2-e by linarith)]
  have hsum : 1/(23-e-1/2)+1/(22+e-1/2)≤(44/483:ℝ) := by
    rw [div_add_div _ _ hx.ne' hy.ne',div_le_iff₀ (mul_pos hx hy)]
    nlinarith
  exact (add_le_add (tail_half _ (by linarith)) (tail_half _ (by linarith))).trans hsum
def rightGood44 (r : Nat) (k : Fin r) (b : Fin (2^208)) : Prop :=
  ∃ j : ℤ, -22 ≤ j ∧ j ≤ 21 ∧ neighborWord b.val j = (reducedPeak r 208 k).val

/-- Directed coverage: a sample within `23 − e` to the right or `22 + e` to the left of the
peak is mapped onto the reduced peak by one of the shifts `−22..21`. -/
theorem neighbor_coverage44 (r : Nat) (hr : 0 < r) (k : Fin r) (b : Fin (2^208))
    (hc : phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 23 - peakOffset r k ∨
      phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 22 + peakOffset r k) :
    rightGood44 r k b := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r) with hcdef
  set m : ℤ := round c with hm
  have hpo : peakOffset r k = c - m := rfl
  rw [hpo] at hc
  have hround : |c - m| ≤ 1/2 := abs_sub_round c
  have hr1 := (abs_le.mp hround).1
  have hr2 := (abs_le.mp hround).2
  have hc0 : 0 ≤ c := by positivity
  have hkr : (k.val : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast k.isLt)
  have hNpos : (0 : ℝ) < ((2^208 : Nat) : ℝ) := by positivity
  have hcN : c < ((2^208 : Nat) : ℝ) := by
    rw [hcdef]; nlinarith
  have hb0 : (0 : ℝ) ≤ (b.val : ℝ) := Nat.cast_nonneg _
  have hbN : (b.val : ℝ) < ((2^208 : Nat) : ℝ) := by exact_mod_cast b.isLt
  have hNZ : (((2^208 : Nat) : ℤ) : ℝ) = ((2^208 : Nat) : ℝ) := Int.cast_natCast _
  have hN2 : ((2^208 : Nat) : ℝ) =
      411376139330301510538742295639337626245683966408394965837152256 := by norm_num
  -- an integer lift `B = b + z·2^208` with `m − B ∈ [−22, 21]`
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℤ, (-23 : ℝ) < (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) ∧
      (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) < 22 := by
    rcases hc with hc | hc
    · unfold phiR at hc
      split_ifs at hc with h
      · exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩
      · exact ⟨1, by push_cast; linarith, by push_cast; linarith⟩
    · unfold phiL at hc
      split_ifs at hc with h
      · exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩
      · exact ⟨-1, by push_cast; linarith, by push_cast; linarith⟩
  set j : ℤ := m - ((b.val : ℤ) + z * ((2^208 : Nat) : ℤ)) with hj
  have hjR : (j : ℝ) = (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) := by
    rw [hj]; push_cast; ring
  have hj1 : (-23 : ℤ) < j := by
    have h1 : (-23 : ℝ) < (j : ℝ) := by rw [hjR]; exact hz1
    exact_mod_cast h1
  have hj2 : j < 22 := by
    have h2 : (j : ℝ) < 22 := by rw [hjR]; exact hz2
    exact_mod_cast h2
  refine ⟨j, by omega, by omega, ?_⟩
  have he : m = (reducedPeakRaw r 208 k : ℤ) := by
    have hc' : c = ((2^208*k.val : Nat) : ℝ)/r := by rw [hcdef]; push_cast; ring
    rw [hm, hc', round_nat_ratio _ r hr]
    simp only [reducedPeakRaw, Nat.mul_assoc]
  have hmod : (reducedPeakRaw r 208 k : ℤ) % (2^208 : Nat) = ((b.val : ℤ) + j) % (2^208 : Nat) := by
    rw [← he, hj, show (b.val : ℤ) + (m - ((b.val : ℤ) + z * ((2^208 : Nat) : ℤ))) =
      m + (-z) * ((2^208 : Nat) : ℤ) by ring, Int.add_mul_emod_self_right]
  have ht := congrArg Int.toNat hmod
  simpa only [neighborWord, reducedPeak, ← Int.natCast_mod, Int.toNat_natCast] using ht.symm

noncomputable def rightMass44 (r : Nat) (k : Fin r) : ℝ := by
  classical
  exact ∑ b : Fin (2^208), if rightGood44 r k b then
    Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0

theorem rightMass44_weighted (r : Nat) (hr : 0 < r) (k : Fin r) :
    1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((44/483) / (3141591 / 1000000 : ℝ) ^ 2) - 1 / 10^12 ≤ rightMass44 r k := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hpo := abs_le.mp (peakOffset_abs r k)
  have h := circular_mass_two (2^208) (by norm_num) ((k.val : ℝ) / r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt))
    (23 - peakOffset r k) (22 + peakOffset r k) (by linarith) (by linarith)
  have hpair := right_pair44 (peakOffset r k) (peakOffset_abs r k)
  have hs0 : 0 ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 := div_nonneg (sq_nonneg _) (by norm_num)
  have hweak : Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 *
        (tailBound (23 - peakOffset r k) + tailBound (22 + peakOffset r k)) ≤
      Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((44/483) / (3141591 / 1000000 : ℝ) ^ 2) := by
    calc _ ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
          (3141591 / 1000000 : ℝ) ^ 2 * (44/483) := mul_le_mul_of_nonneg_left hpair hs0
      _ = _ := by ring
  have hfin : 1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 *
        (tailBound (23 - peakOffset r k) + tailBound (22 + peakOffset r k)) - 1 / 10^12 ≤
      ∑ b : Fin (2^208),
      if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 23 - peakOffset r k ∨
        phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 22 + peakOffset r k
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b < 23 - peakOffset r k ∨
        phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b < 22 + peakOffset r k
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b) else 0)]
    simpa only [ampSq, paperPhaseAmplitude, eigenvalue] using h
  refine le_trans (by linarith) (hfin.trans (Finset.sum_le_sum (fun b _ => ?_)))
  dsimp only [rightMass44]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage44 r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl


theorem right_pair6 (e : ℝ) (he : |e|≤1/2) :
    tailBound (4-e)+tailBound (3+e)≤(1504/2025:ℝ) := by
  obtain ⟨heL,heU⟩:=abs_le.mp he
  let x : ℝ:=4-e
  let y : ℝ:=3+e
  have hx : 0<x := by dsimp [x];linarith
  have hy : 0<y := by dsimp [y];linarith
  have hsum : x+y=7 := by dsimp [x,y];ring
  have hp : 45/4≤x*y := by
    have h:=mul_nonneg (show 0≤e+1/2 by linarith) (show 0≤1/2-e by linarith)
    dsimp [x,y];nlinarith
  have hp2 : (45/4:ℝ)^2≤(x*y)^2:=pow_le_pow_left₀ (by norm_num) hp 2
  have hs2 : (x+y)^2=(49:ℝ):=by rw [hsum];norm_num
  have hs : 1/x^2+1/y^2≤(424/2025:ℝ):=by
    rw [div_add_div _ _ (pow_ne_zero 2 hx.ne') (pow_ne_zero 2 hy.ne'),
      div_le_iff₀ (mul_pos (sq_pos_of_pos hx) (sq_pos_of_pos hy))]
    nlinarith
  have hl : 1/(x+1/2)+1/(y+1/2)≤(8/15:ℝ):=by
    rw [div_add_div _ _ (by linarith : x+1/2≠0) (by linarith : y+1/2≠0),
      div_le_iff₀ (mul_pos (by linarith : 0<x+1/2) (by linarith : 0<y+1/2))]
    nlinarith
  change tailBound x+tailBound y≤_
  unfold tailBound
  linarith
def rightGood6 (r : Nat) (k : Fin r) (b : Fin (2^208)) : Prop :=
  ∃ j : ℤ, -3 ≤ j ∧ j ≤ 2 ∧ neighborWord b.val j = (reducedPeak r 208 k).val

/-- Directed coverage: a sample within `4 − e` to the right or `3 + e` to the left of the
peak is mapped onto the reduced peak by one of the shifts `−3..2`. -/
theorem neighbor_coverage6 (r : Nat) (hr : 0 < r) (k : Fin r) (b : Fin (2^208))
    (hc : phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 4 - peakOffset r k ∨
      phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 3 + peakOffset r k) :
    rightGood6 r k b := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r) with hcdef
  set m : ℤ := round c with hm
  have hpo : peakOffset r k = c - m := rfl
  rw [hpo] at hc
  have hround : |c - m| ≤ 1/2 := abs_sub_round c
  have hr1 := (abs_le.mp hround).1
  have hr2 := (abs_le.mp hround).2
  have hc0 : 0 ≤ c := by positivity
  have hkr : (k.val : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast k.isLt)
  have hNpos : (0 : ℝ) < ((2^208 : Nat) : ℝ) := by positivity
  have hcN : c < ((2^208 : Nat) : ℝ) := by
    rw [hcdef]; nlinarith
  have hb0 : (0 : ℝ) ≤ (b.val : ℝ) := Nat.cast_nonneg _
  have hbN : (b.val : ℝ) < ((2^208 : Nat) : ℝ) := by exact_mod_cast b.isLt
  have hNZ : (((2^208 : Nat) : ℤ) : ℝ) = ((2^208 : Nat) : ℝ) := Int.cast_natCast _
  have hN2 : ((2^208 : Nat) : ℝ) =
      411376139330301510538742295639337626245683966408394965837152256 := by norm_num
  -- an integer lift `B = b + z·2^208` with `m − B ∈ [−3, 2]`
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℤ, (-4 : ℝ) < (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) ∧
      (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) < 3 := by
    rcases hc with hc | hc
    · unfold phiR at hc
      split_ifs at hc with h
      · exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩
      · exact ⟨1, by push_cast; linarith, by push_cast; linarith⟩
    · unfold phiL at hc
      split_ifs at hc with h
      · exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩
      · exact ⟨-1, by push_cast; linarith, by push_cast; linarith⟩
  set j : ℤ := m - ((b.val : ℤ) + z * ((2^208 : Nat) : ℤ)) with hj
  have hjR : (j : ℝ) = (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) := by
    rw [hj]; push_cast; ring
  have hj1 : (-4 : ℤ) < j := by
    have h1 : (-4 : ℝ) < (j : ℝ) := by rw [hjR]; exact hz1
    exact_mod_cast h1
  have hj2 : j < 3 := by
    have h2 : (j : ℝ) < 3 := by rw [hjR]; exact hz2
    exact_mod_cast h2
  refine ⟨j, by omega, by omega, ?_⟩
  have he : m = (reducedPeakRaw r 208 k : ℤ) := by
    have hc' : c = ((2^208*k.val : Nat) : ℝ)/r := by rw [hcdef]; push_cast; ring
    rw [hm, hc', round_nat_ratio _ r hr]
    simp only [reducedPeakRaw, Nat.mul_assoc]
  have hmod : (reducedPeakRaw r 208 k : ℤ) % (2^208 : Nat) = ((b.val : ℤ) + j) % (2^208 : Nat) := by
    rw [← he, hj, show (b.val : ℤ) + (m - ((b.val : ℤ) + z * ((2^208 : Nat) : ℤ))) =
      m + (-z) * ((2^208 : Nat) : ℤ) by ring, Int.add_mul_emod_self_right]
  have ht := congrArg Int.toNat hmod
  simpa only [neighborWord, reducedPeak, ← Int.natCast_mod, Int.toNat_natCast] using ht.symm

noncomputable def rightMass6 (r : Nat) (k : Fin r) : ℝ := by
  classical
  exact ∑ b : Fin (2^208), if rightGood6 r k b then
    Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0

theorem rightMass6_weighted (r : Nat) (hr : 0 < r) (k : Fin r) :
    1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((1504/2025) / (3141591 / 1000000 : ℝ) ^ 2) - 1 / 10^12 ≤ rightMass6 r k := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hpo := abs_le.mp (peakOffset_abs r k)
  have h := circular_mass_two (2^208) (by norm_num) ((k.val : ℝ) / r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt))
    (4 - peakOffset r k) (3 + peakOffset r k) (by linarith) (by linarith)
  have hpair := right_pair6 (peakOffset r k) (peakOffset_abs r k)
  have hs0 : 0 ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 := div_nonneg (sq_nonneg _) (by norm_num)
  have hweak : Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 *
        (tailBound (4 - peakOffset r k) + tailBound (3 + peakOffset r k)) ≤
      Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((1504/2025) / (3141591 / 1000000 : ℝ) ^ 2) := by
    calc _ ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
          (3141591 / 1000000 : ℝ) ^ 2 * (1504/2025) := mul_le_mul_of_nonneg_left hpair hs0
      _ = _ := by ring
  have hfin : 1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 *
        (tailBound (4 - peakOffset r k) + tailBound (3 + peakOffset r k)) - 1 / 10^12 ≤
      ∑ b : Fin (2^208),
      if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 4 - peakOffset r k ∨
        phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 3 + peakOffset r k
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b < 4 - peakOffset r k ∨
        phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b < 3 + peakOffset r k
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b) else 0)]
    simpa only [ampSq, paperPhaseAmplitude, eigenvalue] using h
  refine le_trans (by linarith) (hfin.trans (Finset.sum_le_sum (fun b _ => ?_)))
  dsimp only [rightMass6]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage6 r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem left_pair48 (x y : ℝ) (hx : 48 ≤ x) (hy : 48 ≤ y) (hxy : 97 ≤ x+y) :
    tailBound x + tailBound y ≤ (384/9215:ℝ) := by
  have old (x y : ℝ) (hx : 48 ≤ x) (hy : 48 ≤ y) (hxy : 97 ≤ x+y) :
      1/(x-1/2)+1/(y-1/2) ≤ (384/9215:ℝ) := by
    have hx' : 0 < x-1/2 := by linarith
    have hy' : 0 < y-1/2 := by linarith
    rw [div_add_div _ _ hx'.ne' hy'.ne', div_le_div_iff₀ (mul_pos hx' hy') (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have bound (r : ℝ) (hr : 1/2 < r) : tailBound r ≤ 1/(r-1/2) := by
    have hr0 : 0 < r := by linarith
    have hrm : 0 < r-1/2 := by linarith
    have hrp : 0 < r+1/2 := by linarith
    unfold tailBound
    rw [div_add_div _ _ (pow_ne_zero 2 hr0.ne') hrp.ne', div_le_div_iff₀ (mul_pos (sq_pos_of_pos hr0) hrp) hrm]
    nlinarith
  linarith [old x y hx hy hxy, bound x (by linarith), bound y (by linarith)]


theorem rightMass6_uniform (r : Nat) (hr : 0<r) (k : Fin r) : (9/10:ℝ)≤rightMass6 r k := by
  have h:=rightMass6_weighted r hr k
  have hs : Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r))^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)),
      sq_nonneg (Real.cos (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)))]
  have hm := mul_le_mul_of_nonneg_right hs (by norm_num : 0≤(1504/2025:ℝ)/(3141591/1000000)^2)
  have hc : (1504/2025:ℝ)/(3141591/1000000)^2+1/10^12≤1/10 := by norm_num
  nlinarith

def leftGood3 (r N n a : Nat) : Prop :=
  (2*r*a+N)/(2*N)=n ∨
    (2*r*((a+32)%N)+N)/(2*N)=n ∨
      (2*r*((a+N-32)%N)+N)/(2*N)=n

instance leftGood3_decidable (r N n a : Nat) : Decidable (leftGood3 r N n a) := by
  unfold leftGood3
  infer_instance

theorem nearest_cell (r N n a : Nat) (hN : 0<N) (hr : 0<(r:ℝ))
    (c L : ℝ) (hc : c*r=N*n) (hL : L*(2*r)=N)
    (haL : ⌈c-L⌉≤(a:ℤ)) (haU : (a:ℤ)<⌈c+L⌉) :
    (2*r*a+N)/(2*N)=n := by
  by_contra hbad
  rcases window_cases r N n a hN hbad with h | h
  · have he : (2*N*n+N:ℝ)≤2*r*a := by exact_mod_cast h
    have hca : c+L≤(a:ℝ) := by nlinarith
    have hh : ⌈c+L⌉≤(a:ℤ) := Int.ceil_le.mpr (by push_cast; exact hca)
    omega
  · have he : (2*r*a+N:ℝ)<2*N*n := by exact_mod_cast h
    have hca : (a:ℝ)<c-L := by nlinarith
    have hh : (a:ℤ)<⌈c-L⌉ := Int.lt_ceil.mpr (by push_cast; exact hca)
    omega

theorem wide_cell_good (r N n a : Nat) (hN : 0<N) (hr : 0<(r:ℝ))
    (haN : a<N) (c L : ℝ) (hc : c*r=N*n) (hL : L*(2*r)=N)
    (hA : (32:ℤ)≤⌈c-L⌉) (hB : ⌈c+L⌉+32≤(N:ℤ))
    (hgap : (32:ℤ)≤⌈c+L⌉-⌈c-L⌉)
    (haL : ⌈c-L⌉-32≤(a:ℤ)) (haU : (a:ℤ)<⌈c+L⌉+32) :
    leftGood3 r N n a := by
  by_cases hlo : (a:ℤ)<⌈c-L⌉
  · have hlow : ⌈c-L⌉≤((a+32:Nat):ℤ) := by omega
    have hhigh : ((a+32:Nat):ℤ)<⌈c+L⌉ := by omega
    have hmod : (a+32)%N=a+32 := Nat.mod_eq_of_lt (by omega)
    exact Or.inr (Or.inl (by rw [hmod];exact nearest_cell r N n (a+32) hN hr c L hc hL hlow hhigh))
  by_cases hhi : ⌈c+L⌉≤(a:ℤ)
  · have ha32 : 32≤a := by omega
    have hlow : ⌈c-L⌉≤((a-32:Nat):ℤ) := by omega
    have hhigh : ((a-32:Nat):ℤ)<⌈c+L⌉ := by omega
    have he : a+N-32=(a-32)+N := by omega
    have hmod : (a+N-32)%N=a-32 := by rw [he,Nat.add_mod];simp [Nat.mod_eq_of_lt (by omega : a-32<N)]
    exact Or.inr (Or.inr (by rw [hmod];exact nearest_cell r N n (a-32) hN hr c L hc hL hlow hhigh))
  · exact Or.inl (nearest_cell r N n a hN hr c L hc hL (by omega) (by omega))


theorem window_mass_left_wide (r N n : Nat) (hn0 : 2≤n) (hnr : n+2≤r)
    (hNbig : 2^60≤N) (hrN : 32*r≤N) :
    1-Real.sin (Real.pi*N*((n:ℝ)/r))^2*((384/9215)/(3141591/1000000:ℝ)^2)-1/10^12≤
      ∑a∈range N,if leftGood3 r N n a then ampSq N ((n:ℝ)/r) a else 0 := by
  classical
  have hr : 0<r := by omega
  have hN : 0<N := lt_of_lt_of_le (by positivity) hNbig
  set β : ℝ := (n:ℝ)/r with hβ
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hnR : (n:ℝ)<r := by exact_mod_cast (by omega : n<r)
  set c : ℝ := (N:ℝ)*n/r with hc
  set L : ℝ := (N:ℝ)/(2*r) with hL
  have hcr : c*r=N*n := by rw [hc];field_simp
  have hLr : L*(2*r)=N := by rw [hL];field_simp
  have hn2 : (2:ℝ)≤n := by exact_mod_cast hn0
  have hnr2 : (n:ℝ)+2≤r := by exact_mod_cast hnr
  have hrNR : 32*(r:ℝ)≤N := by exact_mod_cast hrN
  have hL16 : 16≤L := by nlinarith
  have hc4L : 4*L≤c := by nlinarith
  have hcN : c≤N-4*L := by nlinarith
  have hβ0 : 0≤β := by rw [hβ];positivity
  have hβ1 : β<1 := by rw [hβ];exact (div_lt_one hrR).mpr hnR
  have hcβ : (N:ℝ)*β=c := by rw [hc,hβ];ring
  have bU1 : c+L≤(⌈c+L⌉:ℝ) := Int.le_ceil _
  have bU2 : (⌈c+L⌉:ℝ)<c+L+1 := Int.ceil_lt_add_one _
  have bL1 : c-L≤(⌈c-L⌉:ℝ) := Int.le_ceil _
  have bL2 : (⌈c-L⌉:ℝ)<c-L+1 := Int.ceil_lt_add_one _
  have hA : (32:ℤ)≤⌈c-L⌉ := by
    have he : (32:ℝ)≤(⌈c-L⌉:ℝ) := by linarith
    exact_mod_cast he
  have hB : ⌈c+L⌉+32≤(N:ℤ) := by
    have he : (⌈c+L⌉:ℝ)+32≤N := by linarith
    exact_mod_cast he
  have hgap : (32:ℤ)≤⌈c+L⌉-⌈c-L⌉ := by
    have he : (31:ℝ)<((⌈c+L⌉-⌈c-L⌉:ℤ):ℝ) := by push_cast;linarith
    have hz : (31:ℤ)<⌈c+L⌉-⌈c-L⌉ := by exact_mod_cast he
    omega
  let W : ℝ := L+32
  have hW : 48≤W := by dsimp [W];linarith
  have wU1 : c+W≤(⌈c+W⌉:ℝ) := Int.le_ceil _
  have wU2 : (⌈c+W⌉:ℝ)<c+W+1 := Int.ceil_lt_add_one _
  have wL1 : c-W≤(⌈c-W⌉:ℝ) := Int.le_ceil _
  have wL2 : (⌈c-W⌉:ℝ)<c-W+1 := Int.ceil_lt_add_one _
  have hcW : W+1≤c ∧ W+1≤N-c := by dsimp [W];constructor <;> linarith
  have wg : (96:ℤ)≤⌈c+W⌉-⌈c-W⌉ := by
    have he : (95:ℝ)<((⌈c+W⌉-⌈c-W⌉:ℤ):ℝ) := by push_cast;linarith
    have hz : (95:ℤ)<⌈c+W⌉-⌈c-W⌉ := by exact_mod_cast he
    omega
  set R1 : ℝ := (⌈c+W⌉:ℝ)-c with hR1
  set R2 : ℝ := c-(⌈c-W⌉:ℝ)+1 with hR2
  have wgR : (96:ℝ)≤(⌈c+W⌉:ℝ)-(⌈c-W⌉:ℝ) := by exact_mod_cast wg
  have hp := left_pair48 R1 R2 (by rw [hR1];linarith) (by rw [hR2];linarith)
    (by rw [hR1,hR2];linarith)
  have hm := circular_mass_two N hNbig β hβ0 hβ1 R1 R2
    (by rw [hR1];linarith) (by rw [hR2];linarith)
  rw [hcβ] at hm
  have hs0 : 0≤Real.sin (Real.pi*N*β)^2/(3141591/1000000:ℝ)^2 := by positivity
  have hw : Real.sin (Real.pi*N*β)^2/(3141591/1000000:ℝ)^2*(tailBound R1+tailBound R2)≤
      Real.sin (Real.pi*N*β)^2*((384/9215)/(3141591/1000000:ℝ)^2) := by
    calc _≤Real.sin (Real.pi*N*β)^2/(3141591/1000000:ℝ)^2*(384/9215) :=
      mul_le_mul_of_nonneg_left hp hs0
    _=_ := by ring
  refine le_trans (by linarith) (hm.trans ?_)
  apply Finset.sum_le_sum
  intro a ha
  have haN : (a:ℝ)<N := by exact_mod_cast (mem_range.mp ha)
  have ha0 : (0:ℝ)≤a := Nat.cast_nonneg _
  have hgood : (phiR N c a<R1 ∨ phiL N c a<R2)→leftGood3 r N n a := by
    intro hn
    by_cases hhi : ⌈c+W⌉≤(a:ℤ)
    · have he : (⌈c+W⌉:ℝ)≤a := by exact_mod_cast hhi
      have hpr : R1≤phiR N c a := by
        unfold phiR
        rw [if_pos (by linarith)]
        rw [hR1];linarith
      have hpl : R2≤phiL N c a := by
        unfold phiL
        rw [if_neg (by linarith)]
        rw [hR2];linarith [hcW.1]
      rcases hn with h|h <;> linarith
    by_cases hlo : (a:ℤ)<⌈c-W⌉
    · have he : (a:ℝ)+1≤(⌈c-W⌉:ℝ) := by
        have hz : (a:ℤ)+1≤⌈c-W⌉ := by omega
        exact_mod_cast hz
      have hpr : R1≤phiR N c a := by
        unfold phiR
        rw [if_neg (by linarith)]
        rw [hR1];linarith [hcW.2]
      have hpl : R2≤phiL N c a := by
        unfold phiL
        rw [if_pos (by linarith)]
        rw [hR2];linarith
      rcases hn with h|h <;> linarith
    · have heU : ⌈c+W⌉=⌈c+L⌉+32 := by simpa [W,add_assoc] using (Int.ceil_add_intCast (c+L) 32)
      have heL : ⌈c-W⌉=⌈c-L⌉-32 := by simpa [W,sub_sub] using (Int.ceil_sub_intCast (c-L) 32)
      apply wide_cell_good r N n a hN hrR (mem_range.mp ha) c L hcr hLr hA hB hgap
      · omega
      · omega
  have hp0 : 0≤ampSq N β a := Complex.normSq_nonneg _
  split_ifs with hn hg
  · exact le_rfl
  · exact (hg (hgood hn)).elim
  · exact hp0
  · exact le_rfl

end
end ShorECDLP.Entrant.BlendCDF


namespace ShorECDLP.Entrant.BlendProbability
open scoped BigOperators
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem product_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι→ℝ) (g : κ→ℝ) :
    (∑ a,∑ b,f a*g b)=(∑ a,f a)*(∑ b,g b) := by
  symm
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

theorem blend_mass_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι→ℝ) (B : κ→ℝ) (hA : ∀a,0≤A a) (hB : ∀b,0≤B b)
    (hA1 : ∑a,A a=1) (hB1 : ∑b,B b=1)
    (LP LW : ι→Bool) (RI RW : κ→Bool) :
    (∑a,if LW a then A a else 0)+(∑b,if RW b then B b else 0)-1-
      (1-∑a,if LP a then A a else 0)*(1-∑b,if RI b then B b else 0)≤
      ∑a,∑b,if (LP a && RW b)||(LW a && RI b) then A a*B b else 0 := by
  classical
  have hp (a : ι) (b : κ) :
      (if LW a then A a else 0)*B b+A a*(if RW b then B b else 0)-A a*B b-
        (if !LP a then A a else 0)*(if !RI b then B b else 0)≤
        if (LP a && RW b)||(LW a && RI b) then A a*B b else 0 := by
    cases hp : LP a <;> cases hw : LW a <;> cases hi : RI b <;> cases hr : RW b <;>
      simp only [hp,hw,hi,hr,Bool.false_eq_true,Bool.not_false,Bool.not_true,
        Bool.and_false,Bool.and_true,Bool.false_and,Bool.true_and,Bool.or_false,
        Bool.or_true,Bool.false_or,Bool.true_or,if_true,if_false,zero_mul,mul_zero,
        zero_add,add_zero,sub_zero]
    all_goals nlinarith [mul_nonneg (hA a) (hB b)]
  have hCA : (∑a,if !LP a then A a else 0)=1-∑a,if LP a then A a else 0 := by
    have hh : (∑a,if LP a then A a else 0)+(∑a,if !LP a then A a else 0)=1 := by
      rw [←Finset.sum_add_distrib]
      convert hA1 using 1
      apply Finset.sum_congr rfl
      intro a _
      cases hh : LP a <;> simp [hh]
    linarith
  have hCB : (∑b,if !RI b then B b else 0)=1-∑b,if RI b then B b else 0 := by
    have hh : (∑b,if RI b then B b else 0)+(∑b,if !RI b then B b else 0)=1 := by
      rw [←Finset.sum_add_distrib]
      convert hB1 using 1
      apply Finset.sum_congr rfl
      intro b _
      cases hh : RI b <;> simp [hh]
    linarith
  have hs := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) =>
    Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => hp a b))
  simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hs
  simpa only [product_sum,hA1,hB1,hCA,hCB,mul_one,one_mul] using hs


theorem event_le_one {ι : Type*} [Fintype ι] (A : ι→ℝ) (hA : ∀a,0≤A a)
    (hA1 : ∑a,A a=1) (P : ι→Bool) : (∑a,if P a then A a else 0)≤1 := by
  calc _≤∑a,A a := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs <;> first | exact le_rfl | exact hA a
    _=1 := hA1

theorem blend_loss {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι→ℝ) (B : κ→ℝ) (hA : ∀a,0≤A a) (hB : ∀b,0≤B b)
    (hA1 : ∑a,A a=1) (hB1 : ∑b,B b=1)
    (LP LW : ι→Bool) (RI RW : κ→Bool)
    (EP EW ER : ℝ) (hEP : 0≤EP)
    (hLP : 1-EP≤∑a,if LP a then A a else 0)
    (hLW : 1-EW≤∑a,if LW a then A a else 0)
    (hRW : 1-ER≤∑b,if RW b then B b else 0)
    (hRI : (9/10:ℝ)≤∑b,if RI b then B b else 0) :
    1-EW-ER-EP/10≤∑a,∑b,if (LP a && RW b)||(LW a && RI b) then A a*B b else 0 := by
  have h := blend_mass_lower A B hA hB hA1 hB1 LP LW RI RW
  have hI := event_le_one B hB hB1 RI
  have hp : 1-(∑a,if LP a then A a else 0)≤EP := by linarith
  have hi : 1-(∑b,if RI b then B b else 0)≤(1/10:ℝ) := by linarith
  have hm := mul_le_mul hp hi (show 0≤1-(∑b,if RI b then B b else 0) by linarith) hEP
  nlinarith

end
end ShorECDLP.Entrant.BlendProbability


namespace ShorECDLP.Entrant.BlendCoverage
open NeighborReadout Quantum Challenge Secp256k1 BlendCDF BlendProbability SinAverage261 SinAverage WindowMassSharpProof
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation Finset
open scoped BigOperators
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 300

def CP : ℝ := (128/1023)/(3141591/1000000:ℝ)^2
def CW : ℝ := (384/9215)/(3141591/1000000:ℝ)^2
def CR : ℝ := (44/483)/(3141591/1000000:ℝ)^2

def mixedGood (r n d : Nat) (hr : 0<r) (k : Fin r)
    (a : Fin (2^n)) (b : Fin (2^208)) : Bool := by
  classical
  let q : Fin r := ⟨d*k.val%r,Nat.mod_lt _ hr⟩
  exact (decide (ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val=k.val) && decide (rightGood44 r q b)) ||
    (decide (leftGood3 r (2^n) k.val a.val) && decide (rightGood6 r q b))

theorem paper_mass_one (n : Nat) (β : ℝ) :
    (∑a : Fin (2^n),Complex.normSq (paperPhaseAmplitude n β a.val))=1 := by
  rw [Fin.sum_univ_eq_sum_range (fun a=>Complex.normSq (paperPhaseAmplitude n β a))]
  simpa only [paperPhaseAmplitude,eigenvalue,ampSq] using (parseval (2^n) (by positivity) β)

theorem character_lower (r n d : Nat) (hr : 0<r) (hNbig : 2^60≤2^n) (hprec : 32*r≤2^n)
    (k : Fin r) (hk2 : 2≤k.val) (hkr : k.val+2≤r) :
    1-(CW+CP/10)*Real.sin (Real.pi*((2^n:Nat):ℝ)*((k.val:ℝ)/r))^2-
      CR*Real.sin (Real.pi*((2^208:Nat):ℝ)*(((d*k.val%r:Nat):ℝ)/r))^2-21/10000000000000≤
      ∑a : Fin (2^n),∑b : Fin (2^208),if mixedGood r n d hr k a b then
        Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) a.val)*
          Complex.normSq (paperPhaseAmplitude 208 (((d*k.val%r:Nat):ℝ)/r) b.val) else 0 := by
  classical
  let A : Fin (2^n)→ℝ := fun a=>Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) a.val)
  let B : Fin (2^208)→ℝ := fun b=>Complex.normSq (paperPhaseAmplitude 208 (((d*k.val%r:Nat):ℝ)/r) b.val)
  let q : Fin r := ⟨d*k.val%r,Nat.mod_lt _ hr⟩
  let LP : Fin (2^n)→Bool := fun a=>decide (ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val=k.val)
  let LW : Fin (2^n)→Bool := fun a=>decide (leftGood3 r (2^n) k.val a.val)
  let RI : Fin (2^208)→Bool := fun b=>decide (rightGood6 r q b)
  let RW : Fin (2^208)→Bool := fun b=>decide (rightGood44 r q b)
  let sL : ℝ := Real.sin (Real.pi*((2^n:Nat):ℝ)*((k.val:ℝ)/r))^2
  let sR : ℝ := Real.sin (Real.pi*((2^208:Nat):ℝ)*(((d*k.val%r:Nat):ℝ)/r))^2
  have hA : ∀a,0≤A a := fun _=>Complex.normSq_nonneg _
  have hB : ∀b,0≤B b := fun _=>Complex.normSq_nonneg _
  have hA1 : ∑a,A a=1 := paper_mass_one _ _
  have hB1 : ∑b,B b=1 := paper_mass_one _ _
  have hLP : 1-(CP*sL+1/10^12)≤∑a,if LP a then A a else 0 := by
    have h:=window_mass_left_two r (2^n) k.val (by omega) k.isLt hNbig hprec
    simp only [LP,A,decide_eq_true_eq]
    rw [Fin.sum_univ_eq_sum_range (fun a=>if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a=k.val then Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) a) else 0)]
    simpa only [CP,sL,ShorECDLP.Quantum.OrderFinding.nearestNumerator,paperPhaseAmplitude,eigenvalue,ampSq,sub_sub,mul_comm] using h
  have hLW : 1-(CW*sL+1/10^12)≤∑a,if LW a then A a else 0 := by
    have h:=window_mass_left_wide r (2^n) k.val hk2 hkr hNbig hprec
    simp only [LW,A,decide_eq_true_eq]
    rw [Fin.sum_univ_eq_sum_range (fun a=>if leftGood3 r (2^n) k.val a then Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) a) else 0)]
    simpa only [CW,sL,paperPhaseAmplitude,eigenvalue,ampSq,sub_sub,mul_comm] using h
  have hRI : (9/10:ℝ)≤∑b,if RI b then B b else 0 := by
    have h:=rightMass6_uniform r hr q
    simpa only [RI,B,rightMass6,q,decide_eq_true_eq] using h
  have hRW : 1-(CR*sR+1/10^12)≤∑b,if RW b then B b else 0 := by
    have h:=rightMass44_weighted r hr q
    simpa only [RW,B,CR,sR,rightMass44,q,sub_sub,mul_comm,decide_eq_true_eq] using h
  have hEP : 0≤CP*sL+1/10^12 := by
    have hc : 0≤CP := by norm_num [CP]
    have hs : 0≤sL := sq_nonneg _
    exact add_nonneg (mul_nonneg hc hs) (by norm_num)
  have h:=blend_loss A B hA hB hA1 hB1 LP LW RI RW
    (CP*sL+1/10^12) (CW*sL+1/10^12) (CR*sR+1/10^12) hEP hLP hLW hRW hRI
  change _≤∑a,∑b,if (LP a&&RW b)||(LW a&&RI b) then A a*B b else 0
  dsimp only [sL,sR] at h
  nlinarith


theorem character_count (r : Nat) (hr : 4≤r) (C : ℝ) :
    (∑k : Fin r,if 2≤k.val ∧ k.val+2≤r then C else 0)=((r:ℝ)-3)*C := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun k=>if 2≤k ∧ k+2≤r then C else 0)]
  rw [←Finset.sum_filter]
  have hs : (Finset.range r).filter (fun k=>2≤k ∧ k+2≤r)=Finset.Icc 2 (r-2) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  rw [hs]
  simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul]
  have he : r-2+1-2=r-3 := by omega
  rw [he,Nat.cast_sub (by omega : 3≤r)]
  norm_num

theorem averaged_blend_coverage (r n d : Nat) (hr : r.Prime) (hr4 : 4≤r)
    (hNbig : 2^60≤2^n) (hprecision : 32*r≤2^n)
    (accept : Fin (2^n)→Fin (2^208)→Prop) [∀a b,Decidable (accept a b)]
    (haccept : ∀k : Fin r,2≤k.val→k.val+2≤r→∀a b,
      mixedGood r n d hr.pos k a b=true→accept a b) :
    (1-3/(r:ℝ))*(1-21/10000000000000)-(CW+CP/10)/2-CR/2≤
      ∑a : Fin (2^n),∑b : Fin (2^208),if accept a b then asymmetricPairMass r n 208 d (a,b) else 0 := by
  classical
  let A : Fin r → Fin (2^n) → ℝ := fun k a =>
    Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2^208) → ℝ := fun k b =>
    Complex.normSq (paperPhaseAmplitude 208 (((d * k.val % r : Nat) : ℝ) / r) b.val)
  let good : Fin r→Fin (2^n)→Fin (2^208)→Prop := fun k a b=>
    2≤k.val ∧ k.val+2≤r ∧ mixedGood r n d hr.pos k a b=true
  let F : Fin r → Fin (2^n) → Fin (2^208) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let sL : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^n : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let sR : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^208 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2
  let CL : ℝ := CW+CP/10
  let CR : ℝ := BlendCoverage.CR
  have hCL : 0≤CL := by norm_num [CL,CW,CP]
  have hCR : 0≤CR := by norm_num [CR,BlendCoverage.CR]
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
  have hjp : ∀ a : Fin (2^n), ∀ b : Fin (2^208),
      asymmetricPairMass r n 208 d (a, b) = (r : ℝ)⁻¹ * ∑ k : Fin r, A k a * B k b := by
    intro a b
    simp only [asymmetricPairMass, one_div, A, B]
  have step1 :
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2^n), ∑ b : Fin (2^208),
          if accept a b then asymmetricPairMass r n 208 d (a, b) else 0 := by
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
        exact hp (haccept k hk ha a b hb)
      simp [hz]
  have step2 :
      (r : ℝ)⁻¹ * ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b =
        ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]

  have step3 (k : Fin r) :
      (if 2≤k.val ∧ k.val+2≤r then (1-21/10000000000000:ℝ) else 0)-sL k*CL-sR k*CR≤
        ∑a : Fin (2^n),∑b : Fin (2^208),F k a b := by
    by_cases hv : 2≤k.val ∧ k.val+2≤r
    · rw [if_pos hv]
      rw [show (1-21/10000000000000:ℝ)-sL k*CL-sR k*CR=
        1-CL*sL k-CR*sR k-21/10000000000000 by ring]
      have h:=character_lower r n d hr.pos hNbig hprecision k hv.1 hv.2
      simpa only [F,good,hv.1,hv.2,true_and,A,B,CL,CR,sL,sR,mul_comm] using h
    · rw [if_neg hv]
      have h0 : 0≤∑a : Fin (2^n),∑b : Fin (2^208),F k a b :=
        Finset.sum_nonneg (fun a _=>Finset.sum_nonneg (fun b _=>hF k a b))
      have hL0:=mul_nonneg (sq_nonneg (Real.sin (Real.pi*((2^n:Nat):ℝ)*((k.val:ℝ)/r)))) hCL
      have hR0:=mul_nonneg (sq_nonneg (Real.sin (Real.pi*((2^208:Nat):ℝ)*(((d*k.val%r:Nat):ℝ)/r)))) hCR
      dsimp only [sL,sR]
      linarith
  have hsum:=Finset.sum_le_sum (fun k (_ : k∈Finset.univ)=>step3 k)
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,character_count r hr4,
    ←Finset.sum_mul,←Finset.sum_mul] at hsum
  have hL:=left_weight_sum r n
  have hR:=right_weight_sum r d hr.pos
  have hlow : ((r:ℝ)-3)*(1-21/10000000000000)-(r:ℝ)/2*CL-(r:ℝ)/2*CR≤
      ∑k : Fin r,∑a : Fin (2^n),∑b : Fin (2^208),F k a b := by
    have h1 : (∑k : Fin r,sL k)*CL≤(r:ℝ)/2*CL := mul_le_mul_of_nonneg_right hL hCL
    have h2 : (∑k : Fin r,sR k)*CR≤(r:ℝ)/2*CR := mul_le_mul_of_nonneg_right hR hCR
    linarith
  have hlower:=mul_le_mul_of_nonneg_left hlow hrinv
  have heval : (r:ℝ)⁻¹*(((r:ℝ)-3)*(1-21/10000000000000)-(r:ℝ)/2*CL-(r:ℝ)/2*CR)=
      (1-3/(r:ℝ))*(1-21/10000000000000)-CL/2-CR/2 := by field_simp
  rw [heval,step2] at hlower
  exact hlower.trans step1


def leftAt (a : Nat) (i : Fin 56) : Nat :=
  if i.val<44 then a else if i.val<50 then (a+32)%2^261 else (a+2^261-32)%2^261

def offsetAt (i : Fin 56) : ℤ :=
  if i.val<44 then (i.val:ℤ)-22 else if i.val<50 then (i.val:ℤ)-47 else (i.val:ℤ)-53

def recoveredBlend (d a b : Nat) : Bool := by
  classical
  exact decide (∃i : Fin 56,(d:ZMod order)∈fixedCandidates params261 (leftAt a i) (neighborWord b (offsetAt i)))

theorem candidate_of_peak (d : Nat) (k : Fin order) (hk : k.val≠0) (a b : Nat)
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 261 a=k.val)
    (hb : b=(reducedPeak order 208 ⟨d*k.val%order,Nat.mod_lt _ order_prime.pos⟩).val) :
    (d:ZMod order)∈fixedCandidates params261 a b := by
  classical
  haveI : Fact (Nat.Prime order):=⟨order_prime⟩
  have hk0 : ((k.val:Nat):ZMod order)≠0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
  unfold fixedCandidates
  apply Finset.mem_image.mpr
  refine ⟨d*k.val%order,?_,?_⟩
  · change d*k.val%order∈wrappedNumeratorCandidates order 208 b
    rw [hb]
    exact reducedPeak_mem_candidates order 208 _
  · change ((d*k.val%order:Nat):ZMod order)*
      (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 261 a:ZMod order)⁻¹=d
    rw [ha]
    simp only [ZMod.natCast_mod,Nat.cast_mul]
    field_simp

theorem primary_witness (d a b : Nat) (j : ℤ) (hlo : -22≤j) (hhi : j≤21)
    (h : (d:ZMod order)∈fixedCandidates params261 a (neighborWord b j)) :
    recoveredBlend d a b=true := by
  classical
  let i : Fin 56:=⟨(j+22).toNat,by omega⟩
  have hi : i.val<44 := by dsimp [i];omega
  have ho : offsetAt i=j := by simp only [offsetAt,hi,if_true];dsimp [i];omega
  apply decide_eq_true
  refine ⟨i,?_⟩
  simpa only [leftAt,hi,if_true,ho] using h

theorem plus_witness (d a b : Nat) (j : ℤ) (hlo : -3≤j) (hhi : j≤2)
    (h : (d:ZMod order)∈fixedCandidates params261 ((a+32)%2^261) (neighborWord b j)) :
    recoveredBlend d a b=true := by
  classical
  let i : Fin 56:=⟨(j+47).toNat,by omega⟩
  have hi : ¬i.val<44 := by dsimp [i];omega
  have hi' : i.val<50 := by dsimp [i];omega
  have ho : offsetAt i=j := by simp only [offsetAt,hi,hi',if_true,if_false];dsimp [i];omega
  apply decide_eq_true
  refine ⟨i,?_⟩
  simpa only [leftAt,hi,hi',if_true,if_false,ho] using h

theorem minus_witness (d a b : Nat) (j : ℤ) (hlo : -3≤j) (hhi : j≤2)
    (h : (d:ZMod order)∈fixedCandidates params261 ((a+2^261-32)%2^261) (neighborWord b j)) :
    recoveredBlend d a b=true := by
  classical
  let i : Fin 56:=⟨(j+53).toNat,by omega⟩
  have hi : ¬i.val<44 := by dsimp [i];omega
  have hi' : ¬i.val<50 := by dsimp [i];omega
  have ho : offsetAt i=j := by simp only [offsetAt,hi,hi',if_false];dsimp [i];omega
  apply decide_eq_true
  refine ⟨i,?_⟩
  simpa only [leftAt,hi,hi',if_false,ho] using h

theorem recovered_of_mixed (d : Nat) (k : Fin order) (hk : k.val≠0)
    (a : Fin (2^261)) (b : Fin (2^208))
    (h : mixedGood order 261 d order_prime.pos k a b=true) :
    recoveredBlend d a.val b.val=true := by
  classical
  simp only [mixedGood,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨ha,hb⟩|⟨ha,hb⟩
  · obtain ⟨j,hlo,hhi,hj⟩:=hb
    exact primary_witness d a.val b.val j hlo hhi (candidate_of_peak d k hk _ _ ha hj)
  · obtain ⟨j,hlo,hhi,hj⟩:=hb
    rcases ha with ha|ha|ha
    · exact primary_witness d a.val b.val j (by omega) (by omega) (candidate_of_peak d k hk _ _ ha hj)
    · exact plus_witness d a.val b.val j hlo hhi (candidate_of_peak d k hk _ _ ha hj)
    · exact minus_witness d a.val b.val j hlo hhi (candidate_of_peak d k hk _ _ ha hj)

theorem large_order_floor (r : ℝ) (hr : (10:ℝ)^12≤r) :
    (99263/100000:ℝ)≤(1-3/r)*(1-21/10000000000000)-(CW+CP/10)/2-CR/2 := by
  have hi : 1/r≤(1:ℝ)/10^12:=one_div_le_one_div_of_le (by norm_num) hr
  have hn : (99263/100000:ℝ)≤(1-3/10^12)*(1-21/10000000000000)-(CW+CP/10)/2-CR/2 := by norm_num [CW,CP,CR]
  have hp : (0:ℝ)<1-21/10000000000000 := by norm_num
  have hh : 3/r≤(3:ℝ)/10^12 := by simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤3)
  nlinarith

theorem recovered_success (d : Nat) :
    (99263/100000:ℝ)≤∑a : Fin (2^261),∑b : Fin (2^208),
      if recoveredBlend d a.val b.val then asymmetricPairMass order 261 208 d (a,b) else 0 := by
  classical
  have h:=averaged_blend_coverage order 261 d order_prime (by norm_num [order])
    (by norm_num) precision261 (fun a b=>recoveredBlend d a.val b.val=true)
    (fun k hk2 hkr a b hm=>recovered_of_mixed d k (by omega) a b hm)
  exact (large_order_floor order (by norm_num [order])).trans h

end
end ShorECDLP.Entrant.BlendCoverage

namespace ShorECDLP.Entrant.NestedProbability
open BlendProbability BlendCDF BlendCoverage
open scoped BigOperators
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem nested_mass {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι→ℝ) (B : κ→ℝ) (LP LW : ι→Bool) (RI RW : κ→Bool)
    (hPL : ∀a,LP a=true→LW a=true) (hIR : ∀b,RI b=true→RW b=true) :
    (∑a,∑b,if (LP a&&RW b)||(LW a&&RI b) then A a*B b else 0)=
      (∑a,if LP a then A a else 0)*(∑b,if RW b then B b else 0)+
      ((∑a,if LW a then A a else 0)-(∑a,if LP a then A a else 0))*(∑b,if RI b then B b else 0) := by
  have he (a : ι) (b : κ) :
      (if (LP a&&RW b)||(LW a&&RI b) then A a*B b else 0)=
      (if LP a then A a else 0)*(if RW b then B b else 0)+
      (if LW a then A a else 0)*(if RI b then B b else 0)-
      (if LP a then A a else 0)*(if RI b then B b else 0) := by
    have h1:=hPL a
    have h2:=hIR b
    cases hp:LP a <;> cases hw:LW a <;> cases hi:RI b <;> cases hr:RW b <;>
      simp_all
  simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [product_sum,product_sum,product_sum]
  ring

theorem nested_loss {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι→ℝ) (B : κ→ℝ) (hA : ∀a,0≤A a)
    (hA1 : ∑a,A a=1)
    (LP LW : ι→Bool) (RI RW : κ→Bool)
    (hPL : ∀a,LP a=true→LW a=true) (hIR : ∀b,RI b=true→RW b=true)
    (EP EW ER γ : ℝ) (hER : 0≤ER) (hg0 : 0≤γ) (hg1 : γ≤1)
    (hLP : 1-EP≤∑a,if LP a then A a else 0)
    (hLW : 1-EW≤∑a,if LW a then A a else 0)
    (hRW : 1-ER≤∑b,if RW b then B b else 0)
    (hRI : 1-γ≤∑b,if RI b then B b else 0) :
    1-(1-γ)*EW-γ*EP-ER≤∑a,∑b,if (LP a&&RW b)||(LW a&&RI b) then A a*B b else 0 := by
  have he:=nested_mass A B LP LW RI RW hPL hIR
  have hp0 : 0≤∑a,if LP a then A a else 0 := Finset.sum_nonneg (fun a _=>by split_ifs;exact hA a;rfl)
  have hwp : (∑a,if LP a then A a else 0)≤∑a,if LW a then A a else 0 := by
    apply Finset.sum_le_sum
    intro a _
    cases hp:LP a <;> cases hw:LW a <;> simp_all
  have hp1:=event_le_one A hA hA1 LP
  have hleft:=mul_le_mul_of_nonneg_left hRW hp0
  have hinner:=mul_le_mul_of_nonneg_left hRI (sub_nonneg.mpr hwp)
  have hper:=mul_le_mul_of_nonneg_right hp1 hER
  have hpp:=mul_le_mul_of_nonneg_left hLP hg0
  have hww:=mul_le_mul_of_nonneg_left hLW (sub_nonneg.mpr hg1)
  nlinarith

theorem inner_six_sharp (r : Nat) (hr : 0<r) (k : Fin r) :
    (9247/10000:ℝ)≤rightMass6 r k := by
  have h:=rightMass6_weighted r hr k
  have hs : Real.sin (Real.pi*((2^208:Nat):ℝ)*((k.val:ℝ)/r))^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*((2^208:Nat):ℝ)*((k.val:ℝ)/r)),
      sq_nonneg (Real.cos (Real.pi*((2^208:Nat):ℝ)*((k.val:ℝ)/r)))]
  have hm:=mul_le_mul_of_nonneg_right hs (by norm_num : 0≤(1504/2025:ℝ)/(3141591/1000000)^2)
  have hc : (1504/2025:ℝ)/(3141591/1000000)^2+1/10^12≤753/10000 := by norm_num
  nlinarith

end
end ShorECDLP.Entrant.NestedProbability

namespace ShorECDLP.Entrant.NestedCoverage
open Quantum Challenge Secp256k1 BlendCDF BlendProbability BlendCoverage NestedProbability SinAverage261 SinAverage WindowMassSharpProof
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation Finset
open scoped BigOperators
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 300
set_option linter.unusedSimpArgs false

def CL : ℝ := (9247/10000)*CW+(753/10000)*CP

theorem character_lower (r n d : Nat) (hr : 0<r) (hNbig : 2^60≤2^n) (hprec : 32*r≤2^n)
    (k : Fin r) (hk2 : 2≤k.val) (hkr : k.val+2≤r) :
    1-CL*Real.sin (Real.pi*((2^n:Nat):ℝ)*((k.val:ℝ)/r))^2-
      CR*Real.sin (Real.pi*((2^208:Nat):ℝ)*(((d*k.val%r:Nat):ℝ)/r))^2-21/10000000000000≤
      ∑a : Fin (2^n),∑b : Fin (2^208),if mixedGood r n d hr k a b then
        Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) a.val)*
          Complex.normSq (paperPhaseAmplitude 208 (((d*k.val%r:Nat):ℝ)/r) b.val) else 0 := by
  classical
  let A : Fin (2^n)→ℝ := fun a=>Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) a.val)
  let B : Fin (2^208)→ℝ := fun b=>Complex.normSq (paperPhaseAmplitude 208 (((d*k.val%r:Nat):ℝ)/r) b.val)
  let q : Fin r := ⟨d*k.val%r,Nat.mod_lt _ hr⟩
  let LP : Fin (2^n)→Bool := fun a=>decide (ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val=k.val)
  let LW : Fin (2^n)→Bool := fun a=>decide (leftGood3 r (2^n) k.val a.val)
  let RI : Fin (2^208)→Bool := fun b=>decide (rightGood6 r q b)
  let RW : Fin (2^208)→Bool := fun b=>decide (rightGood44 r q b)
  let sL : ℝ := Real.sin (Real.pi*((2^n:Nat):ℝ)*((k.val:ℝ)/r))^2
  let sR : ℝ := Real.sin (Real.pi*((2^208:Nat):ℝ)*(((d*k.val%r:Nat):ℝ)/r))^2
  have hA : ∀a,0≤A a := fun _=>Complex.normSq_nonneg _
  have hB : ∀b,0≤B b := fun _=>Complex.normSq_nonneg _
  have hA1 : ∑a,A a=1 := paper_mass_one _ _
  have hB1 : ∑b,B b=1 := paper_mass_one _ _
  have hLP : 1-(CP*sL+1/10^12)≤∑a,if LP a then A a else 0 := by
    have h:=window_mass_left_two r (2^n) k.val (by omega) k.isLt hNbig hprec
    simp only [LP,A,decide_eq_true_eq]
    rw [Fin.sum_univ_eq_sum_range (fun a=>if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a=k.val then Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) a) else 0)]
    simpa only [CP,sL,ShorECDLP.Quantum.OrderFinding.nearestNumerator,paperPhaseAmplitude,eigenvalue,ampSq,sub_sub,mul_comm] using h
  have hLW : 1-(CW*sL+1/10^12)≤∑a,if LW a then A a else 0 := by
    have h:=window_mass_left_wide r (2^n) k.val hk2 hkr hNbig hprec
    simp only [LW,A,decide_eq_true_eq]
    rw [Fin.sum_univ_eq_sum_range (fun a=>if leftGood3 r (2^n) k.val a then Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) a) else 0)]
    simpa only [CW,sL,paperPhaseAmplitude,eigenvalue,ampSq,sub_sub,mul_comm] using h
  have hRI : (9247/10000:ℝ)≤∑b,if RI b then B b else 0 := by
    have h:=inner_six_sharp r hr q
    simpa only [RI,B,rightMass6,q,decide_eq_true_eq] using h
  have hRW : 1-(CR*sR+1/10^12)≤∑b,if RW b then B b else 0 := by
    have h:=rightMass44_weighted r hr q
    simpa only [RW,B,CR,sR,rightMass44,q,sub_sub,mul_comm,decide_eq_true_eq] using h
  have hER : 0≤CR*sR+1/10^12 := by
    have hc : 0≤CR := by norm_num [CR]
    have hs : 0≤sR := sq_nonneg _
    exact add_nonneg (mul_nonneg hc hs) (by norm_num)
  have hPL : ∀a,LP a=true→LW a=true := by
    intro a ha
    change decide (leftGood3 r (2^n) k.val a.val)=true
    apply decide_eq_true
    exact Or.inl (of_decide_eq_true ha)
  have hIR : ∀b,RI b=true→RW b=true := by
    intro b hb
    change decide (rightGood44 r q b)=true
    apply decide_eq_true
    obtain ⟨j,hlo,hhi,hj⟩:=of_decide_eq_true hb
    exact ⟨j,by omega,by omega,hj⟩
  have h:=nested_loss A B hA hA1 LP LW RI RW hPL hIR
    (CP*sL+1/10^12) (CW*sL+1/10^12) (CR*sR+1/10^12) (753/10000) hER
    (by norm_num) (by norm_num) hLP hLW hRW ((by norm_num : (1-(753/10000:ℝ))=9247/10000).trans_le hRI)
  change _≤∑a,∑b,if (LP a&&RW b)||(LW a&&RI b) then A a*B b else 0
  dsimp only [sL,sR] at h
  dsimp only [CL]
  nlinarith


theorem character_count (r : Nat) (hr : 4≤r) (C : ℝ) :
    (∑k : Fin r,if 2≤k.val ∧ k.val+2≤r then C else 0)=((r:ℝ)-3)*C := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun k=>if 2≤k ∧ k+2≤r then C else 0)]
  rw [←Finset.sum_filter]
  have hs : (Finset.range r).filter (fun k=>2≤k ∧ k+2≤r)=Finset.Icc 2 (r-2) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  rw [hs]
  simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul]
  have he : r-2+1-2=r-3 := by omega
  rw [he,Nat.cast_sub (by omega : 3≤r)]
  norm_num

theorem averaged_blend_coverage (r n d : Nat) (hr : r.Prime) (hr4 : 4≤r)
    (hNbig : 2^60≤2^n) (hprecision : 32*r≤2^n)
    (accept : Fin (2^n)→Fin (2^208)→Prop) [∀a b,Decidable (accept a b)]
    (haccept : ∀k : Fin r,2≤k.val→k.val+2≤r→∀a b,
      mixedGood r n d hr.pos k a b=true→accept a b) :
    (1-3/(r:ℝ))*(1-21/10000000000000)-CL/2-CR/2≤
      ∑a : Fin (2^n),∑b : Fin (2^208),if accept a b then asymmetricPairMass r n 208 d (a,b) else 0 := by
  classical
  let A : Fin r → Fin (2^n) → ℝ := fun k a =>
    Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2^208) → ℝ := fun k b =>
    Complex.normSq (paperPhaseAmplitude 208 (((d * k.val % r : Nat) : ℝ) / r) b.val)
  let good : Fin r→Fin (2^n)→Fin (2^208)→Prop := fun k a b=>
    2≤k.val ∧ k.val+2≤r ∧ mixedGood r n d hr.pos k a b=true
  let F : Fin r → Fin (2^n) → Fin (2^208) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let sL : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^n : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let sR : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^208 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2
  let CL : ℝ := CL
  let CR : ℝ := BlendCoverage.CR
  have hCL : 0≤CL := by norm_num [CL,ShorECDLP.Entrant.NestedCoverage.CL,CW,CP]
  have hCR : 0≤CR := by norm_num [CR,BlendCoverage.CR]
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
  have hjp : ∀ a : Fin (2^n), ∀ b : Fin (2^208),
      asymmetricPairMass r n 208 d (a, b) = (r : ℝ)⁻¹ * ∑ k : Fin r, A k a * B k b := by
    intro a b
    simp only [asymmetricPairMass, one_div, A, B]
  have step1 :
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2^n), ∑ b : Fin (2^208),
          if accept a b then asymmetricPairMass r n 208 d (a, b) else 0 := by
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
        exact hp (haccept k hk ha a b hb)
      simp [hz]
  have step2 :
      (r : ℝ)⁻¹ * ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b =
        ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]

  have step3 (k : Fin r) :
      (if 2≤k.val ∧ k.val+2≤r then (1-21/10000000000000:ℝ) else 0)-sL k*CL-sR k*CR≤
        ∑a : Fin (2^n),∑b : Fin (2^208),F k a b := by
    by_cases hv : 2≤k.val ∧ k.val+2≤r
    · rw [if_pos hv]
      rw [show (1-21/10000000000000:ℝ)-sL k*CL-sR k*CR=
        1-CL*sL k-CR*sR k-21/10000000000000 by ring]
      have h:=character_lower r n d hr.pos hNbig hprecision k hv.1 hv.2
      simpa only [F,good,hv.1,hv.2,true_and,A,B,CL,CR,sL,sR,mul_comm] using h
    · rw [if_neg hv]
      have h0 : 0≤∑a : Fin (2^n),∑b : Fin (2^208),F k a b :=
        Finset.sum_nonneg (fun a _=>Finset.sum_nonneg (fun b _=>hF k a b))
      have hL0:=mul_nonneg (sq_nonneg (Real.sin (Real.pi*((2^n:Nat):ℝ)*((k.val:ℝ)/r)))) hCL
      have hR0:=mul_nonneg (sq_nonneg (Real.sin (Real.pi*((2^208:Nat):ℝ)*(((d*k.val%r:Nat):ℝ)/r)))) hCR
      dsimp only [sL,sR]
      linarith
  have hsum:=Finset.sum_le_sum (fun k (_ : k∈Finset.univ)=>step3 k)
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,character_count r hr4,
    ←Finset.sum_mul,←Finset.sum_mul] at hsum
  have hL:=left_weight_sum r n
  have hR:=right_weight_sum r d hr.pos
  have hlow : ((r:ℝ)-3)*(1-21/10000000000000)-(r:ℝ)/2*CL-(r:ℝ)/2*CR≤
      ∑k : Fin r,∑a : Fin (2^n),∑b : Fin (2^208),F k a b := by
    have h1 : (∑k : Fin r,sL k)*CL≤(r:ℝ)/2*CL := mul_le_mul_of_nonneg_right hL hCL
    have h2 : (∑k : Fin r,sR k)*CR≤(r:ℝ)/2*CR := mul_le_mul_of_nonneg_right hR hCR
    linarith
  have hlower:=mul_le_mul_of_nonneg_left hlow hrinv
  have heval : (r:ℝ)⁻¹*(((r:ℝ)-3)*(1-21/10000000000000)-(r:ℝ)/2*CL-(r:ℝ)/2*CR)=
      (1-3/(r:ℝ))*(1-21/10000000000000)-CL/2-CR/2 := by field_simp
  rw [heval,step2] at hlower
  exact hlower.trans step1


theorem large_order_floor (r : ℝ) (hr : (10:ℝ)^12≤r) :
    (992955517/1000000000:ℝ)≤(1-3/r)*(1-21/10000000000000)-CL/2-CR/2 := by
  have hi : 1/r≤(1:ℝ)/10^12:=one_div_le_one_div_of_le (by norm_num) hr
  have hn : (992955517/1000000000:ℝ)≤(1-3/10^12)*(1-21/10000000000000)-CL/2-CR/2 := by norm_num [CL,CW,CP,CR]
  have hp : (0:ℝ)<1-21/10000000000000 := by norm_num
  have hh : 3/r≤(3:ℝ)/10^12 := by simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤3)
  nlinarith

theorem recovered_success (d : Nat) :
    (992955517/1000000000:ℝ)≤∑a : Fin (2^261),∑b : Fin (2^208),
      if recoveredBlend d a.val b.val then asymmetricPairMass order 261 208 d (a,b) else 0 := by
  classical
  have h:=averaged_blend_coverage order 261 d order_prime (by norm_num [order])
    (by norm_num) precision261 (fun a b=>recoveredBlend d a.val b.val=true)
    (fun k hk2 hkr a b hm=>recovered_of_mixed d k (by omega) a b hm)
  exact (large_order_floor order (by norm_num [order])).trans h

end
end ShorECDLP.Entrant.NestedCoverage
