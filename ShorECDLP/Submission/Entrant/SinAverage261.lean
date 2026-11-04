import ShorECDLP.Submission.Entrant.SinAverage

/-! Averaged success bound for a 261/208 two-axis readout with 56 right neighbour words.

Same argument as `SinAverage`, with sharper constants:
* per term `sin (πu) ≥ 3.141591·u` for `u ≤ 2⁻²⁰` (`sin_pi_mul_ge_sharp`);
* separated tail sums `Σ 1/φ² ≤ 1/(R − 1/2)` by telescoping (`sum_inv_sq_le_half`);
* two radii, one per direction (`circular_mass_two`), with the far tail cut at `2^40`;
* left radii `R1, R2 ≥ 16` with `R1 + R2 ≥ 33` (`left_pair`), right radii
  `29 − e, 28 + e` with `|e| ≤ 1/2` (`right_pair`). -/

namespace ShorECDLP.Entrant.SinAverage261
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Entrant.WindowMassSharpProof ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Entrant.RoundedReadout ShorECDLP.Entrant.SinAverage
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 300

theorem sin_pi_mul_ge_sharp (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2^20) :
    (3141591 / 1000000 : ℝ) * u ≤ Real.sin (Real.pi * u) := by
  have hpL : (3141592 : ℝ) / 1000000 < Real.pi := by
    have h := Real.pi_gt_d6
    norm_num at h ⊢
    linarith
  have hpU : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hpu0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le hu0
  have hpu : Real.pi * u ≤ 4 * u := mul_le_mul_of_nonneg_right hpU hu0
  have hu2 : u ^ 2 ≤ (1 / 2^20 : ℝ) ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have hu3 : u ^ 3 ≤ u / 2^40 := by
    have h := mul_le_mul_of_nonneg_left hu2 hu0
    calc u ^ 3 = u * u ^ 2 := by ring
      _ ≤ u * (1 / 2^20 : ℝ) ^ 2 := h
      _ = u / 2^40 := by ring
  have hcube : (Real.pi * u) ^ 3 ≤ 64 * (u / 2^40) := by
    calc (Real.pi * u) ^ 3 ≤ (4 * u) ^ 3 := pow_le_pow_left₀ hpu0 hpu 3
      _ = 64 * u ^ 3 := by ring
      _ ≤ 64 * (u / 2^40) := mul_le_mul_of_nonneg_left hu3 (by norm_num)
  have hs := sin_ge_cubic (Real.pi * u) hpu0
  have hp := mul_le_mul_of_nonneg_right hpL.le hu0
  linarith

/-- Local sharp bound from the exact numerator and a sine lower bound on the distance `φ`. -/
theorem ampSq_sharp_of_abs (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat) (φ : ℝ)
    (hd : 0 < φ) (hsmall : φ / (N : ℝ) ≤ 1 / 2^20)
    (he : |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (φ / (N : ℝ)))) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / ((3141591 / 1000000 : ℝ) ^ 2 * φ ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow := sin_pi_mul_ge_sharp (φ / (N : ℝ)) (div_nonneg hd.le hNR.le) hsmall
  have hu : 0 < φ / (N : ℝ) := div_pos hd hNR
  have hpos : 0 < |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by rw [he]; linarith
  have hne : Real.sin (Real.pi * (β - (a : ℝ) / N)) ≠ 0 := abs_pos.mp hpos
  refine (ampSq_le_weighted N hN β a hne).trans ?_
  have hφ : (N : ℝ) * (φ / (N : ℝ)) = φ := mul_div_cancel₀ φ hNR.ne'
  have h3 : (3141591 / 1000000 : ℝ) * φ ≤
      (N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hlow hNR.le
    calc (3141591 / 1000000 : ℝ) * φ =
          (N : ℝ) * ((3141591 / 1000000 : ℝ) * (φ / (N : ℝ))) := by
            rw [mul_left_comm, hφ]
      _ ≤ _ := hm
  have h9 : (3141591 / 1000000 : ℝ) ^ 2 * φ ^ 2 ≤
      ((N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))|) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h3 2
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h9

theorem ampSq_phiR_sharp (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiR N ((N : ℝ) * β) a)
    (hsmall : phiR N ((N : ℝ) * β) a / (N : ℝ) ≤ 1 / 2^20) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 /
      ((3141591 / 1000000 : ℝ) ^ 2 * (phiR N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_sharp_of_abs N hN β a _ hd hsmall
    (abs_sin_phiR N hN β a hd (hsmall.trans (by norm_num)))

theorem ampSq_phiL_sharp (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiL N ((N : ℝ) * β) a)
    (hsmall : phiL N ((N : ℝ) * β) a / (N : ℝ) ≤ 1 / 2^20) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 /
      ((3141591 / 1000000 : ℝ) ^ 2 * (phiL N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_sharp_of_abs N hN β a _ hd hsmall
    (abs_sin_phiL N hN β a hd (hsmall.trans (by norm_num)))

/-- Telescoping with `1/x² ≤ 1/(x − 1/2) − 1/(x + 1/2)`. -/
theorem sum_range_inv_sq_le_half (R : ℝ) (hR : 1/2 < R) (M : ℕ) :
    ∑ k ∈ range M, 1 / (R + k) ^ 2 ≤ 1 / (R - 1/2) - 1 / (R - 1/2 + M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h1 : 0 < R - 1/2 + M := by linarith
    have h2 : 0 < R + M := by linarith
    have h3 : 0 < R + 1/2 + M := by linarith
    have hstep : 1 / (R + M) ^ 2 ≤
        1 / (R - 1/2 + M) - 1 / (R - 1/2 + ((M + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [show R - 1/2 + (M + 1) = R + 1/2 + M by ring]
      rw [div_sub_div _ _ h1.ne' h3.ne', div_le_div_iff₀ (pow_pos h2 2) (mul_pos h1 h3)]
      nlinarith
    linarith

theorem sum_inv_sq_le_half (S : Finset ℕ) (φ : ℕ → ℝ) (R : ℝ) (hR : 1/2 < R)
    (hφ : ∀ a ∈ S, R ≤ φ a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ 1 / (R - 1/2) := by
  set g : ℕ → ℕ := fun a => ⌊φ a - R⌋₊ with hg
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h2 := Nat.lt_floor_add_one (φ a - R)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb))
    have h4 := Nat.lt_floor_add_one (φ b - R)
    simp only [hg] at hab
    rw [hab] at h1 h2
    apply hsep a ha b hb
    rw [abs_lt]; constructor <;> linarith
  have step1 : ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ ∑ a ∈ S, 1 / (R + g a) ^ 2 := by
    apply sum_le_sum
    intro a ha
    have h1 : (g a : ℝ) ≤ φ a - R := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h0 : (0 : ℝ) ≤ g a := Nat.cast_nonneg _
    have h2 : 0 < R + g a := by linarith
    apply one_div_le_one_div_of_le (pow_pos h2 2)
    nlinarith
  have step2 : ∑ a ∈ S, 1 / (R + g a) ^ 2 = ∑ k ∈ S.image g, 1 / (R + k) ^ 2 := by
    rw [sum_image hinj]
  have step3 : ∑ k ∈ S.image g, 1 / (R + k) ^ 2 ≤
      ∑ k ∈ range (S.sup g + 1), 1 / (R + k) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [mem_image] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [mem_range]
      exact Nat.lt_succ_of_le (le_sup ha)
    · intro k _ _
      positivity
  have h4 := sum_range_inv_sq_le_half R hR (S.sup g + 1)
  have h5 : 0 ≤ 1 / (R - 1/2 + ((S.sup g + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) ≤ ((S.sup g + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact one_div_nonneg.mpr (by linarith)
  linarith

theorem directed_tail_sharp (N : Nat) (β : ℝ) (S : Finset Nat) (d : Nat → ℝ) (s R : ℝ)
    (hs : 0 ≤ s) (hR : 1/2 < R) (hd : ∀ a ∈ S, R ≤ d a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |d a - d b| < 1 → a = b)
    (hpt : ∀ a ∈ S, ampSq N β a ≤ s / ((3141591 / 1000000 : ℝ) ^ 2 * (d a) ^ 2)) :
    ∑ a ∈ S, ampSq N β a ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R - 1/2)) := by
  have hi := sum_inv_sq_le_half S d R hR hd hsep
  calc
    _ ≤ ∑ a ∈ S, (s / (3141591 / 1000000 : ℝ) ^ 2) * (1 / (d a) ^ 2) := by
      apply Finset.sum_le_sum
      intro a ha
      calc ampSq N β a ≤ s / ((3141591 / 1000000 : ℝ) ^ 2 * (d a) ^ 2) := hpt a ha
        _ = (s / (3141591 / 1000000 : ℝ) ^ 2) * (1 / (d a) ^ 2) := by
          rw [div_mul_div_comm, mul_one]
    _ = (s / (3141591 / 1000000 : ℝ) ^ 2) * (∑ a ∈ S, 1 / (d a) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)

theorem far_tail_sharp : 3 / (Real.pi ^ 2 * ((2 : ℝ) ^ 40 - 1)) ≤ (1 : ℝ) / 10 ^ 12 := by
  have hp := Real.pi_gt_three
  have hp2 : 9 < Real.pi ^ 2 := by nlinarith
  have h40 : (0 : ℝ) < (2 : ℝ) ^ 40 - 1 := by norm_num
  have hd : 0 < Real.pi ^ 2 * ((2 : ℝ) ^ 40 - 1) := mul_pos (by positivity) h40
  rw [div_le_div_iff₀ hd (by norm_num)]
  have h9 : 9 * ((2 : ℝ) ^ 40 - 1) ≤ Real.pi ^ 2 * ((2 : ℝ) ^ 40 - 1) :=
    mul_le_mul_of_nonneg_right hp2.le h40.le
  have hn : (3 : ℝ) * 10 ^ 12 ≤ 1 * (9 * ((2 : ℝ) ^ 40 - 1)) := by norm_num
  linarith

/-- Weighted circular concentration with one radius per direction. -/
theorem circular_mass_two (N : Nat) (hNbig : 2^60 ≤ N) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R1 R2 : ℝ) (hR1 : 1 ≤ R1) (hR2 : 1 ≤ R2) :
    1 - Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 *
        (1 / (R1 - 1/2) + 1 / (R2 - 1/2)) - 1 / 10^12 ≤
      ∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2
        then ampSq N β a else 0 := by
  classical
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hNbig
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNreal : (2 : ℝ) ^ 60 ≤ N := by exact_mod_cast hNbig
  set s := Real.sin (Real.pi * N * β) ^ 2 with hsdef
  have hs0 : 0 ≤ s := sq_nonneg _
  let RS := (Finset.range N).filter
    (fun a => R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 2^40)
  let LS := (Finset.range N).filter
    (fun a => R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 2^40)
  have hsm : ∀ φ : ℝ, φ < 2^40 → φ / (N : ℝ) ≤ 1 / 2^20 := by
    intro φ hφ
    rw [div_le_iff₀ hNR]
    have : (1 / 2^20 : ℝ) * 2^60 = 2^40 := by norm_num
    nlinarith
  have rBound : ∑ a ∈ RS, ampSq N β a ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2)) := by
    apply directed_tail_sharp N β RS (phiR N ((N : ℝ) * β)) s R1 hs0 (by linarith)
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiR_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      exact ampSq_phiR_sharp N hN β a (by linarith [hd.1]) (hsm _ hd.2)
  have lBound : ∑ a ∈ LS, ampSq N β a ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R2 - 1/2)) := by
    apply directed_tail_sharp N β LS (phiL N ((N : ℝ) * β)) s R2 hs0 (by linarith)
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiL_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      exact ampSq_phiL_sharp N hN β a (by linarith [hd.1]) (hsm _ hd.2)
  have fBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40)
      then ampSq N β a else 0) ≤ (1 : ℝ) / 10^12 := by
    have hc := circular_mass N hN β (2^40) hβ0 hβ1 (by norm_num)
    have hs : (∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) +
      (∑ a ∈ Finset.range N,
        if ¬(phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40)
        then ampSq N β a else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert parseval N hN β using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    rw [eq_sub_of_add_eq' hs]
    exact (sub_le_comm.mp hc).trans far_tail_sharp
  have cover (a : Nat) :
      (if ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
        then ampSq N β a else 0) ≤
      (if R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) +
      (if R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) +
      (if ¬(phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40)
        then ampSq N β a else 0) := by
    have ha0 : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
    by_cases hb : ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
    · rw [if_pos hb]
      have hr : R1 ≤ phiR N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inl h))
      have hl : R2 ≤ phiL N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inr h))
      by_cases hRR : R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 2^40
      · rw [if_pos hRR]
        split_ifs <;> linarith
      · rw [if_neg hRR]
        by_cases hLL : R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 2^40
        · rw [if_pos hLL]
          split_ifs <;> linarith
        · rw [if_neg hLL]
          have hf : ¬(phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40) := by
            rintro (h | h)
            · exact hRR ⟨hr, h⟩
            · exact hLL ⟨hl, h⟩
          rw [if_pos hf]
          linarith
    · rw [if_neg hb]
      split_ifs <;> linarith
  have badBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
      then ampSq N β a else 0) ≤
      s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2)) +
        s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R2 - 1/2)) + 1 / 10^12 := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.range N) => cover a)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    have hRs : (∑ a ∈ Finset.range N,
        if R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2)) := by
      simpa only [RS, Finset.sum_filter] using rBound
    have hLs : (∑ a ∈ Finset.range N,
        if R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R2 - 1/2)) := by
      simpa only [LS, Finset.sum_filter] using lBound
    exact h.trans (add_le_add (add_le_add hRs hLs) fBound)
  have htotal : (∑ a ∈ Finset.range N,
      if phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2
      then ampSq N β a else 0) +
    (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
      then ampSq N β a else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert parseval N hN β using 1
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> ring
  have he : s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2) + 1 / (R2 - 1/2)) =
      s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2)) +
        s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R2 - 1/2)) := by ring
  linarith

theorem left_pair (x y : ℝ) (hx : 16 ≤ x) (hy : 16 ≤ y) (hxy : 33 ≤ x + y) :
    1 / (x - 1/2) + 1 / (y - 1/2) ≤ 128 / 1023 := by
  have hx' : 0 < x - 1/2 := by linarith
  have hy' : 0 < y - 1/2 := by linarith
  rw [div_add_div _ _ hx'.ne' hy'.ne', div_le_div_iff₀ (mul_pos hx' hy') (by norm_num)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem right_pair (e : ℝ) (he : |e| ≤ 1/2) :
    1 / ((29 - e) - 1/2) + 1 / ((28 + e) - 1/2) ≤ 56 / 783 := by
  have h := abs_le.mp he
  have hx : 0 < (29 - e) - 1/2 := by linarith
  have hy : 0 < (28 + e) - 1/2 := by linarith
  rw [div_add_div _ _ hx.ne' hy.ne', div_le_div_iff₀ (mul_pos hx hy) (by norm_num)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3/2 - e by linarith) (show (0 : ℝ) ≤ 1/2 + e by linarith)]

/-- Nearest-numerator window at half-width `N/(2r) ≥ 16`, with exact integer radii. -/
theorem window_mass_left_two (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r)
    (hNbig : 2^60 ≤ N) (hrN : 32 * r ≤ N) :
    1 - Real.sin (Real.pi * N * ((n : ℝ) / (r : ℝ))) ^ 2 *
        ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) - 1 / 10^12 ≤
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
  have hpair := left_pair R1 R2 (by rw [hR1]; linarith) (by rw [hR2]; linarith)
    (by rw [hR1, hR2]; linarith)
  have hmass := circular_mass_two N hNbig β hβ0 hβ1 R1 R2 (by rw [hR1]; linarith)
    (by rw [hR2]; linarith)
  rw [hcβ] at hmass
  have hs0 : 0 ≤ Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 := by positivity
  have hweak : Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 *
      (1 / (R1 - 1/2) + 1 / (R2 - 1/2)) ≤
      Real.sin (Real.pi * N * β) ^ 2 * ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) := by
    calc _ ≤ Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 * (128 / 1023) :=
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

/-- Offset of the right peak from its nearest integer. -/
def peakOffset (r : Nat) (k : Fin r) : ℝ :=
  ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r) - round (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r))

theorem peakOffset_abs (r : Nat) (k : Fin r) : |peakOffset r k| ≤ 1/2 := abs_sub_round _

def rightGood56 (r : Nat) (k : Fin r) (b : Fin (2^208)) : Prop :=
  ∃ j : ℤ, -28 ≤ j ∧ j ≤ 27 ∧ neighborWord b.val j = (reducedPeak r 208 k).val

/-- Directed coverage: a sample within `29 − e` to the right or `28 + e` to the left of the
peak is mapped onto the reduced peak by one of the shifts `−28..27`. -/
theorem neighbor_coverage56 (r : Nat) (hr : 0 < r) (k : Fin r) (b : Fin (2^208))
    (hc : phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 29 - peakOffset r k ∨
      phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 28 + peakOffset r k) :
    rightGood56 r k b := by
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
  -- an integer lift `B = b + z·2^208` with `m − B ∈ [−28, 27]`
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℤ, (-29 : ℝ) < (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) ∧
      (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) < 28 := by
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
  have hj1 : (-29 : ℤ) < j := by
    have h1 : (-29 : ℝ) < (j : ℝ) := by rw [hjR]; exact hz1
    exact_mod_cast h1
  have hj2 : j < 28 := by
    have h2 : (j : ℝ) < 28 := by rw [hjR]; exact hz2
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

noncomputable def rightMass56 (r : Nat) (k : Fin r) : ℝ := by
  classical
  exact ∑ b : Fin (2^208), if rightGood56 r k b then
    Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0

theorem rightMass56_weighted (r : Nat) (hr : 0 < r) (k : Fin r) :
    1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) - 1 / 10^12 ≤ rightMass56 r k := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hpo := abs_le.mp (peakOffset_abs r k)
  have h := circular_mass_two (2^208) (by norm_num) ((k.val : ℝ) / r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt))
    (29 - peakOffset r k) (28 + peakOffset r k) (by linarith) (by linarith)
  have hpair := right_pair (peakOffset r k) (peakOffset_abs r k)
  have hs0 : 0 ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 := div_nonneg (sq_nonneg _) (by norm_num)
  have hweak : Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 *
        (1 / ((29 - peakOffset r k) - 1/2) + 1 / ((28 + peakOffset r k) - 1/2)) ≤
      Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) := by
    calc _ ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
          (3141591 / 1000000 : ℝ) ^ 2 * (56 / 783) := mul_le_mul_of_nonneg_left hpair hs0
      _ = _ := by ring
  have hfin : 1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 *
        (1 / ((29 - peakOffset r k) - 1/2) + 1 / ((28 + peakOffset r k) - 1/2)) - 1 / 10^12 ≤
      ∑ b : Fin (2^208),
      if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 29 - peakOffset r k ∨
        phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 28 + peakOffset r k
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b < 29 - peakOffset r k ∨
        phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b < 28 + peakOffset r k
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b) else 0)]
    simpa only [ampSq, paperPhaseAmplitude, eigenvalue] using h
  refine le_trans (by linarith) (hfin.trans (Finset.sum_le_sum (fun b _ => ?_)))
  dsimp only [rightMass56]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage56 r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem prod_lower (x y A B f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : 0 ≤ f)
    (hx : 1 - A - f ≤ x) (hy : 1 - B - f ≤ y) (hA1 : A + f ≤ 1) (hB1 : B + f ≤ 1) :
    1 - 2 * f - A - B ≤ x * y := by
  have h := mul_le_mul hx hy (by linarith) (by linarith)
  nlinarith [mul_nonneg (add_nonneg hA hf) (add_nonneg hB hf)]

theorem averaged_pair_coverage261 (r n d : Nat) (hr : r.Prime)
    (hNbig : 2^60 ≤ 2^n) (hprecision : 32 * r ≤ 2^n)
    (accept : Fin (2^n) → Fin (2^208) → Prop) [∀ a b, Decidable (accept a b)]
    (haccept : ∀ (k : Fin r), k.val ≠ 0 → ∀ a b,
      ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val →
      rightGood56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b →
      accept a b) :
    (1 - 1 / (r : ℝ)) * (1 - 2 / 10^12) - ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) / 2 -
      ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) / 2 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208),
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
  let CL : ℝ := (128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2
  let CR : ℝ := (56 / 783) / (3141591 / 1000000 : ℝ) ^ 2
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
    have h := window_mass_left_two r (2^n) k.val
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

theorem success_budget261 (r : ℝ) (hr : 1000000 ≤ r) :
    (99 : ℝ) / 100 ≤ (1 - 1 / r) * (1 - 2 / 10^12) -
      ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) / 2 -
      ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) / 2 := by
  have hr0 : 0 < r := by linarith
  have hinv : 1 / r ≤ (1 : ℝ) / 1000000 :=
    one_div_le_one_div_of_le (by norm_num) hr
  have hC : ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) / 2 +
      ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) / 2 ≤ 9963 / 1000000 := by norm_num
  nlinarith

theorem precision261 : 32 * order ≤ 2^261 := by norm_num [order]

def params261 : DecoderParams := ⟨261,208,by decide,by decide,by decide,by decide⟩

def pairRecovered261 (d a b : Nat) : Bool :=
  decide (∃i : Fin 56,(d : ZMod order)∈fixedCandidates params261 a (neighborWord b ((i.val : ℤ)-28)))

theorem pairRecovered261_of_character (d : Nat) (k : Fin order) (hk : k.val≠0)
    (a : Fin (2^261)) (b : Fin (2^208))
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 261 a.val=k.val)
    (hb : rightGood56 order ⟨d*k.val%order,Nat.mod_lt _ order_prime.pos⟩ b) :
    pairRecovered261 d a.val b.val=true := by
  classical
  obtain ⟨j,hlo,hhi,hj⟩:=hb
  let i : Fin 56:=⟨(j+28).toNat,by omega⟩
  have hi : (i.val : ℤ)-28=j := by dsimp [i];omega
  haveI : Fact (Nat.Prime order):=⟨order_prime⟩
  have hk0 : ((k.val : Nat) : ZMod order)≠0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
  apply decide_eq_true
  refine ⟨i,?_⟩
  rw [hi]
  unfold fixedCandidates
  apply Finset.mem_image.mpr
  refine ⟨d*k.val%order,?_,?_⟩
  · change d*k.val%order∈wrappedNumeratorCandidates order 208 (neighborWord b.val j)
    rw [hj]
    exact reducedPeak_mem_candidates order 208 _
  · change ((d*k.val%order : Nat) : ZMod order)*
      (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 261 a.val : ZMod order)⁻¹=d
    rw [ha]
    simp only [ZMod.natCast_mod,Nat.cast_mul]
    field_simp

theorem pair_success261 (Q : Point) (d : Nat) (_hn : Q≠0) (_hd : Q=d•G) :
    (99 : ℝ)/100 ≤ ∑a : Fin (2^261),∑b : Fin (2^208),
      if pairRecovered261 d a.val b.val then asymmetricPairMass order 261 208 d (a,b) else 0 := by
  have h:=averaged_pair_coverage261 order 261 d order_prime (by norm_num) precision261
    (fun a b=>pairRecovered261 d a.val b.val=true)
    (fun k hk a b ha hb=>pairRecovered261_of_character d k hk a b ha hb)
  exact (success_budget261 order (by norm_num [order])).trans h

theorem decoder_budget261 : 56 * (2*(order/2^208+2)) ≤ 56*(2^49+2) := by
  norm_num [order]

end
end ShorECDLP.Entrant.SinAverage261
