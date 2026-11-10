import ShorECDLP.Submission.Entrant.Prefix
namespace ShorECDLP.Entrant.SharpCoverage
open SinAverage261 WindowMassSharpProof
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem tail_anti (x y : ℝ) (hx : 0<x) (hxy : x≤y) : tailBound y≤tailBound x := by
  have hy : 0<y := lt_of_lt_of_le hx hxy
  unfold tailBound
  apply add_le_add
  · exact one_div_le_one_div_of_le (sq_pos_of_pos hx) (pow_le_pow_left₀ hx.le hxy 2)
  · exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem left_pair_sharp (x y : ℝ) (hx : 16≤x) (hy : 16≤y) (hxy : 33≤x+y) :
    tailBound x+tailBound y≤(128/1023:ℝ)-68/10000000 := by
  have hnum : tailBound 16+tailBound 17≤(128/1023:ℝ)-68/10000000 := by norm_num [tailBound]
  by_cases hX : 17≤x
  · have h1:=tail_anti 17 x (by norm_num) hX
    have h2:=tail_anti 16 y (by norm_num) hy
    linarith
  by_cases hY : 17≤y
  · exact (add_le_add (tail_anti 16 x (by norm_num) hx) (tail_anti 17 y (by norm_num) hY)).trans hnum
  let z : ℝ := 33-x
  have hz : 16≤z := by dsimp [z]; linarith
  have hzy : z≤y := by dsimp [z]; linarith
  have hx0 : 0<x := by linarith
  have hz0 : 0<z := by linarith
  have hsum : x+z=33 := by dsimp [z]; ring
  have hprod : 272≤x*z := by
    have h:=mul_nonneg (show 0≤x-16 by linarith) (show 0≤17-x by linarith)
    dsimp [z]
    nlinarith
  have hp2 : (272:ℝ)^2≤(x*z)^2 := pow_le_pow_left₀ (by norm_num) hprod 2
  have hsum2 : (x+z)^2=(1089:ℝ) := by rw [hsum]; norm_num
  have hsq : 1/x^2+1/z^2≤(545/73984:ℝ) := by
    rw [div_add_div _ _ (pow_ne_zero 2 hx0.ne') (pow_ne_zero 2 hz0.ne'),
      div_le_iff₀ (mul_pos (sq_pos_of_pos hx0) (sq_pos_of_pos hz0))]
    nlinarith
  have hlin : 1/(x+1/2)+1/(z+1/2)≤(136/1155:ℝ) := by
    rw [div_add_div _ _ (by linarith : x+1/2≠0) (by linarith : z+1/2≠0),
      div_le_iff₀ (mul_pos (by linarith : 0<x+1/2) (by linarith : 0<z+1/2))]
    nlinarith
  have hn : (545/73984+136/1155:ℝ)≤128/1023-68/10000000 := by norm_num
  have hm := tail_anti z y hz0 hzy
  unfold tailBound at hm ⊢
  linarith


open Quantum Challenge Secp256k1
open SinAverage261 SinAverage WindowMassSharpProof RoundedReadout NeighborReadout
open Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation Finset
open scoped BigOperators
set_option exponentiation.threshold 300
theorem window_mass_left_sharp (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r)
    (hNbig : 2^60 ≤ N) (hrN : 32 * r ≤ N) :
    1 - Real.sin (Real.pi * N * ((n : ℝ) / (r : ℝ))) ^ 2 *
        (((128 / 1023) - 68/10000000) / (3141591 / 1000000 : ℝ) ^ 2) - 1 / 10^12 ≤
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
  have hrN' : 32 * (r : ℝ) ≤ N := by exact_mod_cast hrN
  have hL16 : 16 ≤ L := by nlinarith
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
  have hgap : (32 : ℝ) ≤ (⌈c + L⌉ : ℝ) - (⌈c - L⌉ : ℝ) := by
    have hz : (31 : ℝ) < ((⌈c + L⌉ - ⌈c - L⌉ : ℤ) : ℝ) := by push_cast; linarith
    have hz' : (31 : ℤ) < ⌈c + L⌉ - ⌈c - L⌉ := by exact_mod_cast hz
    have hz'' : (32 : ℤ) ≤ ⌈c + L⌉ - ⌈c - L⌉ := by omega
    have hz''' : (32 : ℝ) ≤ ((⌈c + L⌉ - ⌈c - L⌉ : ℤ) : ℝ) := by exact_mod_cast hz''
    push_cast at hz'''
    exact hz'''
  have hpair := left_pair_sharp R1 R2 (by rw [hR1]; linarith) (by rw [hR2]; linarith)
    (by rw [hR1, hR2]; linarith)
  have hmass := circular_mass_two N hNbig β hβ0 hβ1 R1 R2 (by rw [hR1]; linarith)
    (by rw [hR2]; linarith)
  rw [hcβ] at hmass
  have hs0 : 0 ≤ Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 := by positivity
  have hweak : Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 *
      (tailBound R1 + tailBound R2) ≤
      Real.sin (Real.pi * N * β) ^ 2 * (((128 / 1023) - 68/10000000) / (3141591 / 1000000 : ℝ) ^ 2) := by
    calc _ ≤ Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 * ((128 / 1023) - 68/10000000) :=
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

theorem averaged_pair_coverage_sharp (r n d : Nat) (hr : r.Prime)
    (hNbig : 2^60 ≤ 2^n) (hprecision : 32 * r ≤ 2^n)
    (accept : Fin (2^n) → Fin (2^208) → Prop) [∀ a b, Decidable (accept a b)]
    (haccept : ∀ (k : Fin r), k.val ≠ 0 → ∀ a b,
      ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val →
      rightGood56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b →
      accept a b) :
    (1 - 1 / (r : ℝ)) * (1 - 2 / 10^12) - (((128 / 1023) - 68/10000000) / (3141591 / 1000000 : ℝ) ^ 2) / 2 -
      (((56 / 783 - 7 / 10000000)) / (3141591 / 1000000 : ℝ) ^ 2) / 2 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208),
      if accept a b then asymmetricPairMass r n 208 d (a, b) else 0 := by
  classical
  let A : Fin r → Fin (2^n) → ℝ := fun k a =>
    Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2^208) → ℝ := fun k b =>
    Complex.normSq (paperPhaseAmplitude 208 (((d * k.val % r : Nat) : ℝ) / r) b.val)
  let good : Fin r → Fin (2^n) → Fin (2^208) → Prop := fun k a b =>
    k.val ≠ 0 ∧ ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val ∧
      rightGood56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b
  let F : Fin r → Fin (2^n) → Fin (2^208) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let sL : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^n : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let sR : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^208 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2
  let CL : ℝ := ((128 / 1023) - 68/10000000) / (3141591 / 1000000 : ℝ) ^ 2
  let CR : ℝ := ((56 / 783 - 7 / 10000000)) / (3141591 / 1000000 : ℝ) ^ 2
  have hCL : 0 ≤ CL ∧ CL ≤ 1/2 := by constructor <;> norm_num [CL]
  have hCR : 0 ≤ CR ∧ CR ≤ 1/2 := by constructor <;> norm_num [CR]
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
        exact hp (haccept k hk a b ha hb)
      simp [hz]
  have step2 :
      (r : ℝ)⁻¹ * ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b =
        ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have hleft (k : Fin r) (hk : k.val ≠ 0) :
      1 - sL k * CL - 1 / 10^12 ≤ ∑ a : Fin (2^n),
        if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val then A k a else 0 := by
    have h := window_mass_left_sharp r (2^n) k.val
      (Nat.pos_of_ne_zero hk) k.isLt hNbig hprecision
    rw [Fin.sum_univ_eq_sum_range (fun a =>
      if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a = k.val then
        Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a) else 0)]
    simpa only [ShorECDLP.Quantum.OrderFinding.nearestNumerator, paperPhaseAmplitude,
      eigenvalue] using h
  have hright (k : Fin r) :
      1 - sR k * CR - 1 / 10^12 ≤ rightMass56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ :=
    rightMass56_weighted r hr.pos ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩
  have step3 : ∀ k : Fin r,
      (if k.val = 0 then 0 else (1 - 2 / 10^12 : ℝ)) - sL k * CL - sR k * CR ≤
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    intro k
    have hsL : 0 ≤ sL k := sq_nonneg _
    have hsR : 0 ≤ sR k := sq_nonneg _
    have hsL1 : sL k ≤ 1 := Real.sin_sq_le_one _
    have hsR1 : sR k ≤ 1 := Real.sin_sq_le_one _
    have hAL : 0 ≤ sL k * CL := mul_nonneg hsL hCL.1
    have hAR : 0 ≤ sR k * CR := mul_nonneg hsR hCR.1
    have hAL1 : sL k * CL ≤ 1/2 := by nlinarith [hCL.2]
    have hAR1 : sR k * CR ≤ 1/2 := by nlinarith [hCR.2]
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b :=
        Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF k a b))
      linarith
    · rw [if_neg hk]
      have he : (∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b) =
          (∑ a : Fin (2^n), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val
            then A k a else 0) * rightMass56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ := by
        rw [rightMass56, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F, good, B]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [he]
      have hp := prod_lower _ _ (sL k * CL) (sR k * CR) (1 / 10^12) hAL hAR (by norm_num)
        (hleft k hk) (hright k) (by linarith) (by linarith)
      linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  have hcount : (∑ k : Fin r, (if k.val = 0 then (0 : ℝ) else (1 - 2 / 10^12))) =
      ((r : ℝ) - 1) * (1 - 2 / 10^12) := by
    have hz : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
      simp [hr.pos]
    calc
      _ = ∑ k : Fin r, ((1 - 2 / 10^12 : ℝ) - (1 - 2 / 10^12) * (if k.val = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcount, ← Finset.sum_mul,
    ← Finset.sum_mul] at hsum
  have hL := left_weight_sum r n
  have hR := right_weight_sum r d hr.pos
  have hlow : ((r : ℝ) - 1) * (1 - 2 / 10^12) - (r : ℝ) / 2 * CL - (r : ℝ) / 2 * CR ≤
      ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    have h1 : (∑ k : Fin r, sL k) * CL ≤ (r : ℝ) / 2 * CL :=
      mul_le_mul_of_nonneg_right hL hCL.1
    have h2 : (∑ k : Fin r, sR k) * CR ≤ (r : ℝ) / 2 * CR :=
      mul_le_mul_of_nonneg_right hR hCR.1
    linarith
  have hlower := mul_le_mul_of_nonneg_left hlow hrinv
  have heval : (r : ℝ)⁻¹ * (((r : ℝ) - 1) * (1 - 2 / 10^12) - (r : ℝ) / 2 * CL -
      (r : ℝ) / 2 * CR) = (1 - 1 / (r : ℝ)) * (1 - 2 / 10^12) - CL / 2 - CR / 2 := by
    field_simp
  rw [heval, step2] at hlower
  exact hlower.trans step1

theorem large_order_floor_sharp (r : ℝ) (hr : (10 : ℝ)^12 ≤ r) :
    (990038369 /1000000000 : ℝ) ≤
      (1 - 1 / r) * (1 - 2 / 10^12) -
        (((128 / 1023) - 68/10000000) / (3141591 / 1000000 : ℝ)^2) / 2 -
        (((56 / 783 - 7 / 10000000)) / (3141591 / 1000000 : ℝ)^2) / 2 := by
  have hi : 1 / r ≤ (1 : ℝ) / 10^12 :=
    one_div_le_one_div_of_le (by norm_num) hr
  have hbase : (990038369 /1000000000 : ℝ) ≤
      (1 - 1 / 10^12) * (1 - 2 / 10^12) -
        (((128 / 1023) - 68/10000000) / (3141591 / 1000000 : ℝ)^2) / 2 -
        (((56 / 783 - 7 / 10000000)) / (3141591 / 1000000 : ℝ)^2) / 2 := by norm_num
  have hpos : (0 : ℝ) < 1 - 2 / 10^12 := by norm_num
  nlinarith


theorem improved_pair_success_sharp (d : Nat) :
    (990038369 : ℝ) /1000000000 ≤ ∑ a : Fin (2^261), ∑ b : Fin (2^208),
      if pairRecovered261 d a.val b.val then
        asymmetricPairMass order 261 208 d (a,b) else 0 := by
  have h := averaged_pair_coverage_sharp order 261 d order_prime (by decide +kernel) precision261
    (fun a b => pairRecovered261 d a.val b.val = true)
    (fun k hk a b ha hb => pairRecovered261_of_character d k hk a b ha hb)
  exact (large_order_floor_sharp order (by norm_num [order])).trans h


end
end ShorECDLP.Entrant.SharpCoverage
