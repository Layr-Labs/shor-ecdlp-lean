import ShorECDLP.Submission.Entrant.Prefix
namespace ShorECDLP.Entrant.Precision260CDF
open SinAverage261 WindowMassSharpProof
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
theorem left_pair (x y : ℝ) (hx : 8 ≤ x) (hy : 8 ≤ y) (hxy : 17 ≤ x+y) :
    tailBound x + tailBound y ≤ (64/255:ℝ) := by
  have old (x y : ℝ) (hx : 8 ≤ x) (hy : 8 ≤ y) (hxy : 17 ≤ x+y) :
      1/(x-1/2)+1/(y-1/2) ≤ (64/255:ℝ) := by
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

open Quantum Challenge Secp256k1
open SinAverage261 SinAverage WindowMassSharpProof RoundedReadout NeighborReadout
open Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation Finset
open scoped BigOperators
set_option exponentiation.threshold 300
theorem window_mass_left_primary (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r)
    (hNbig : 2^60 ≤ N) (hrN : 16 * r ≤ N) :
    1 - Real.sin (Real.pi * N * ((n : ℝ) / (r : ℝ))) ^ 2 *
        (((64 / 255)) / (3141591 / 1000000 : ℝ) ^ 2) - 1 / 10^12 ≤
      ∑ a ∈ range N,
        if (2 * r * a + N) / (2 * N) = n then ampSq N ((n : ℝ) / (r : ℝ)) a else 0 := by
  have hr : 0 < r := by omega
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hNbig
  set β : ℝ := (n : ℝ) / (r : ℝ) with hβ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR0 : (0 : ℝ) ≤ n := by positivity
  have hnR : (n : ℝ) < r := by exact_mod_cast hnr
  set c : ℝ := (N : ℝ) * n / r with hc
  set L : ℝ := (N : ℝ) / (2 * r) with hL
  have hcr : c * r = N * n := by rw [hc]; field_simp
  have hLr : L * (2 * r) = N := by rw [hL]; field_simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnr' : (n : ℝ) + 1 ≤ r := by exact_mod_cast hnr
  have hrN' : 16 * (r : ℝ) ≤ N := by exact_mod_cast hrN
  have hL16 : 8 ≤ L := by nlinarith
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβ1 : β < 1 := by rw [hβ]; exact (div_lt_one hrR).2 hnR
  have hcβ : (N : ℝ) * β = c := by rw [hβ, hc]; ring
  -- exact radii of the two excluded half-lines
  have hA1 : c + L ≤ (⌈c + L⌉ : ℝ) := Int.le_ceil _
  have hA2 : (⌈c + L⌉ : ℝ) < c + L + 1 := Int.ceil_lt_add_one _
  have hB1 : c - L ≤ (⌈c - L⌉ : ℝ) := Int.le_ceil _
  have hB2 : (⌈c - L⌉ : ℝ) < c - L + 1 := Int.ceil_lt_add_one _
  set R1 : ℝ := (⌈c + L⌉ : ℝ) - c with hR1
  set R2 : ℝ := c - (⌈c - L⌉ : ℝ) + 1 with hR2
  have hgap : (16 : ℝ) ≤ (⌈c + L⌉ : ℝ) - (⌈c - L⌉ : ℝ) := by
    have hz : (15 : ℝ) < ((⌈c + L⌉ - ⌈c - L⌉ : ℤ) : ℝ) := by push_cast; linarith
    have hz' : (15 : ℤ) < ⌈c + L⌉ - ⌈c - L⌉ := by exact_mod_cast hz
    have hz'' : (16 : ℤ) ≤ ⌈c + L⌉ - ⌈c - L⌉ := by omega
    have hz''' : (16 : ℝ) ≤ ((⌈c + L⌉ - ⌈c - L⌉ : ℤ) : ℝ) := by exact_mod_cast hz''
    push_cast at hz'''
    exact hz'''
  have hpair := left_pair R1 R2 (by rw [hR1]; linarith) (by rw [hR2]; linarith)
    (by rw [hR1, hR2]; linarith)
  have hmass := circular_mass_two N hNbig β hβ0 hβ1 R1 R2 (by rw [hR1]; linarith)
    (by rw [hR2]; linarith)
  rw [hcβ] at hmass
  have hs0 : 0 ≤ Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 := by positivity
  have hweak : Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 *
      (tailBound R1 + tailBound R2) ≤
      Real.sin (Real.pi * N * β) ^ 2 * (((64 / 255)) / (3141591 / 1000000 : ℝ) ^ 2) := by
    calc _ ≤ Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 * ((64 / 255)) :=
          mul_le_mul_of_nonneg_left hpair hs0
      _ = _ := by ring
  refine le_trans (by linarith) (hmass.trans ?_)
  apply Finset.sum_le_sum
  intro a ha
  have haN : (a : ℝ) < N := by exact_mod_cast (mem_range.mp ha)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hgood : (phiR N c a < R1 ∨ phiL N c a < R2) →
      (2 * r * a + N) / (2 * N) = n := by
    intro hnear
    by_contra hbad
    rcases window_cases r N n a hN hbad with h | h
    · have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
      have hca : c + L ≤ (a : ℝ) := by nlinarith
      have hceil : ⌈c + L⌉ ≤ (a : ℤ) := Int.ceil_le.mpr (by push_cast; exact hca)
      have hceil' : (⌈c + L⌉ : ℝ) ≤ (a : ℝ) := by exact_mod_cast hceil
      have hpr : R1 ≤ phiR N c a := by
        unfold phiR
        rw [if_pos (by linarith)]
        rw [hR1]; linarith
      have hpl : R2 ≤ phiL N c a := by
        unfold phiL
        rw [if_neg (by linarith)]
        rw [hR2]; linarith
      rcases hnear with hn | hn <;> linarith
    · have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
      have hca : (a : ℝ) < c - L := by nlinarith
      have hceil : (a : ℤ) < ⌈c - L⌉ := Int.lt_ceil.mpr (by push_cast; exact hca)
      have hceil1 : (a : ℤ) + 1 ≤ ⌈c - L⌉ := hceil
      have hceil' : (a : ℝ) + 1 ≤ (⌈c - L⌉ : ℝ) := by exact_mod_cast hceil1
      have hpr : R1 ≤ phiR N c a := by
        unfold phiR
        rw [if_neg (by linarith)]
        rw [hR1]; linarith
      have hpl : R2 ≤ phiL N c a := by
        unfold phiL
        rw [if_pos (by linarith)]
        rw [hR2]; linarith
      rcases hnear with hn | hn <;> linarith
  have hnneg : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
  split_ifs with hn hg
  · exact le_rfl
  · exact (hg (hgood hn)).elim
  · exact hnneg
  · exact le_rfl


end
end ShorECDLP.Entrant.Precision260CDF
