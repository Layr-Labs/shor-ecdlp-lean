import ShorECDLP.Submission.Entrant.StackBase

/-! Averaged success bound for a 262/208 two-axis readout.

Pointwise window bounds lose a factor two: the QPE amplitude carries the numerator
`sin²(π N β)`, and averaged over the nonzero characters `k` this weight is at most `1/2`
(`sum_sin_sq_le`). The tail mass of each axis is therefore bounded by a multiple of that
weight, and the union bound per character is averaged over `k`. -/

namespace ShorECDLP.Entrant.SinAverage
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Entrant.WindowMassSharpProof ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 300

/-- Geometric sum with its exact numerator. -/
theorem amp_normSq_le_sin (N : ℕ) (x : ℝ) (hs : Real.sin (x / 2) ≠ 0) :
    Complex.normSq ((N : ℂ)⁻¹ * ∑ y ∈ range N, Complex.exp (Complex.I * (x : ℂ)) ^ y)
      ≤ Real.sin ((N : ℝ) * x / 2) ^ 2 / ((N : ℝ) * |Real.sin (x / 2)|) ^ 2 := by
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
  have hωN : ω ^ N = Complex.exp (Complex.I * (((N : ℝ) * x : ℝ) : ℂ)) := by
    rw [hωdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnum : ‖ω ^ N - 1‖ = 2 * |Real.sin ((N : ℝ) * x / 2)| := by
    rw [hωN, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs]
    norm_num
  rw [geom_sum_eq hω, Complex.normSq_eq_norm_sq, norm_mul, norm_div, norm_inv,
    Complex.norm_natCast, hω1, hnum]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_of_eq
  rw [show (N : ℝ)⁻¹ * (2 * |Real.sin ((N : ℝ) * x / 2)| / (2 * |Real.sin (x / 2)|)) =
      |Real.sin ((N : ℝ) * x / 2)| / ((N : ℝ) * |Real.sin (x / 2)|) by field_simp]
  rw [div_pow, sq_abs]

/-- `sin² (π(Nβ - a)) = sin² (πNβ)` for an integer outcome `a`. -/
theorem ampSq_le_weighted (N : ℕ) (hN : 0 < N) (β : ℝ) (a : ℕ)
    (hs : Real.sin (Real.pi * (β - (a : ℝ) / N)) ≠ 0) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 /
      ((N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))|) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (2 * Real.pi * (β - (a : ℝ) / N)) / 2 = Real.pi * (β - (a : ℝ) / N) := by ring
  have h := amp_normSq_le_sin N (2 * Real.pi * (β - (a : ℝ) / N)) (by rw [hx]; exact hs)
  rw [hx] at h
  have hNx : (N : ℝ) * (2 * Real.pi * (β - (a : ℝ) / N)) / 2 =
      Real.pi * N * β - a * Real.pi := by
    field_simp
  have hsq : Real.sin (Real.pi * N * β - a * Real.pi) ^ 2 = Real.sin (Real.pi * N * β) ^ 2 := by
    rw [Real.sin_sub_nat_mul_pi, mul_pow, ← pow_mul, mul_comm a 2, pow_mul, neg_one_sq,
      one_pow, one_mul]
  rw [hNx, hsq] at h
  exact h

/-- Local weighted bound from a sine lower bound on the directed distance `φ`. -/
theorem ampSq_weighted_of_abs (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat) (φ : ℝ)
    (hd : 0 < φ) (hsmall : φ / (N : ℝ) ≤ 1/16)
    (he : |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (φ / (N : ℝ)))) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (9 * φ ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow := sin_pi_mul_ge_three (φ / (N : ℝ)) (div_nonneg hd.le hNR.le) hsmall
  have hu : 0 < φ / (N : ℝ) := div_pos hd hNR
  have hpos : 0 < |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by rw [he]; linarith
  have hne : Real.sin (Real.pi * (β - (a : ℝ) / N)) ≠ 0 := abs_pos.mp hpos
  refine (ampSq_le_weighted N hN β a hne).trans ?_
  have h3 : 3 * φ ≤ (N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by
    rw [he]
    calc 3 * φ = (N : ℝ) * (3 * (φ / (N : ℝ))) := by field_simp
      _ ≤ (N : ℝ) * Real.sin (Real.pi * (φ / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hlow hNR.le
  have h9 : 9 * φ ^ 2 ≤ ((N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))|) ^ 2 := by
    nlinarith
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h9

theorem ampSq_phiR_weighted (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiR N ((N : ℝ) * β) a)
    (hsmall : phiR N ((N : ℝ) * β) a / (N : ℝ) ≤ 1/16) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (9 * (phiR N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_weighted_of_abs N hN β a _ hd hsmall (abs_sin_phiR N hN β a hd hsmall)

theorem ampSq_phiL_weighted (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiL N ((N : ℝ) * β) a)
    (hsmall : phiL N ((N : ℝ) * β) a / (N : ℝ) ≤ 1/16) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (9 * (phiL N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_weighted_of_abs N hN β a _ hd hsmall (abs_sin_phiL N hN β a hd hsmall)

theorem directed_tail_weighted (N : Nat) (β : ℝ) (S : Finset Nat) (d : Nat → ℝ) (s R : ℝ)
    (hs : 0 ≤ s) (hR : 1 < R) (hd : ∀ a ∈ S, R ≤ d a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |d a - d b| < 1 → a = b)
    (hpt : ∀ a ∈ S, ampSq N β a ≤ s / (9 * (d a) ^ 2)) :
    ∑ a ∈ S, ampSq N β a ≤ s / 9 * (1 / (R - 1)) := by
  have hi := sum_inv_sq_le S d R hR hd hsep
  calc
    _ ≤ ∑ a ∈ S, (s / 9) * (1 / (d a) ^ 2) := by
      apply Finset.sum_le_sum
      intro a ha
      have hda : 0 < d a := by linarith [hd a ha]
      calc ampSq N β a ≤ s / (9 * (d a) ^ 2) := hpt a ha
        _ = (s / 9) * (1 / (d a) ^ 2) := by field_simp
    _ = (s / 9) * (∑ a ∈ S, 1 / (d a) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (s / 9) * (1 / (R - 1)) := mul_le_mul_of_nonneg_left hi (by positivity)

/-- Circular concentration within radius `R`, weighted by the numerator `sin² (πNβ)`. -/
theorem circular_mass_weighted (N : Nat) (hNbig : 65536 ≤ N) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R : ℝ) (hR : 1 < R) :
    1 - Real.sin (Real.pi * N * β) ^ 2 * (2 / (9 * (R - 1))) - 1/10000 ≤
      ∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R
        then ampSq N β a else 0 := by
  classical
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNreal : (65536 : ℝ) ≤ N := by exact_mod_cast hNbig
  set s := Real.sin (Real.pi * N * β) ^ 2 with hsdef
  have hs0 : 0 ≤ s := sq_nonneg _
  let RS := (Finset.range N).filter
    (fun a => R ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 4096)
  let LS := (Finset.range N).filter
    (fun a => R ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 4096)
  have rBound : ∑ a ∈ RS, ampSq N β a ≤ s / 9 * (1 / (R - 1)) := by
    apply directed_tail_weighted N β RS (phiR N ((N : ℝ) * β)) s R hs0 hR
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiR_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiR_weighted N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      nlinarith [hd.2]
  have lBound : ∑ a ∈ LS, ampSq N β a ≤ s / 9 * (1 / (R - 1)) := by
    apply directed_tail_weighted N β LS (phiL N ((N : ℝ) * β)) s R hs0 hR
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiL_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiL_weighted N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      nlinarith [hd.2]
  have fBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096)
      then ampSq N β a else 0) ≤ (1 : ℝ) / 10000 := by
    have hc := circular_mass N hN β 4096 hβ0 hβ1 (by norm_num)
    have hs : (∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) +
      (∑ a ∈ Finset.range N,
        if ¬(phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096)
        then ampSq N β a else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert parseval N hN β using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    linarith [far_tail_budget]
  have cover (a : Nat) :
      (if ¬(phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R)
        then ampSq N β a else 0) ≤
      (if R ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) +
      (if R ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) +
      (if ¬(phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096)
        then ampSq N β a else 0) := by
    have ha0 : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
    by_cases hb : ¬(phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R)
    · rw [if_pos hb]
      have hr : R ≤ phiR N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inl h))
      have hl : R ≤ phiL N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inr h))
      by_cases hRR : R ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 4096
      · rw [if_pos hRR]
        split_ifs <;> linarith
      · rw [if_neg hRR]
        by_cases hLL : R ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 4096
        · rw [if_pos hLL]
          split_ifs <;> linarith
        · rw [if_neg hLL]
          have hf : ¬(phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096) := by
            rintro (h | h)
            · exact hRR ⟨hr, h⟩
            · exact hLL ⟨hl, h⟩
          rw [if_pos hf]
          linarith
    · rw [if_neg hb]
      split_ifs <;> linarith
  have badBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R)
      then ampSq N β a else 0) ≤ s * (2 / (9 * (R - 1))) + 1/10000 := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.range N) => cover a)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    have hRs : (∑ a ∈ Finset.range N,
        if R ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) ≤ s / 9 * (1 / (R - 1)) := by
      simpa only [RS, Finset.sum_filter] using rBound
    have hLs : (∑ a ∈ Finset.range N,
        if R ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) ≤ s / 9 * (1 / (R - 1)) := by
      simpa only [LS, Finset.sum_filter] using lBound
    have he : s / 9 * (1 / (R - 1)) + s / 9 * (1 / (R - 1)) = s * (2 / (9 * (R - 1))) := by
      have hR1 : R - 1 ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have htotal : (∑ a ∈ Finset.range N,
      if phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R
      then ampSq N β a else 0) +
    (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R)
      then ampSq N β a else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert parseval N hN β using 1
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> ring
  linarith

/-- Nearest-numerator window at half-width `N/(2r) ≥ 32`. -/
theorem window_mass_left_weighted (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r)
    (hNbig : 65536 ≤ N) (hrN : 64 * r ≤ N) :
    1 - Real.sin (Real.pi * N * ((n : ℝ) / (r : ℝ))) ^ 2 * (2 / 279) - 1/10000 ≤
      ∑ a ∈ range N,
        if (2 * r * a + N) / (2 * N) = n then ampSq N ((n : ℝ) / (r : ℝ)) a else 0 := by
  have hr : 0 < r := by omega
  have hN : 0 < N := by omega
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
  have hrN' : 64 * (r : ℝ) ≤ N := by exact_mod_cast hrN
  have hL32 : 32 ≤ L := by nlinarith
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβ1 : β < 1 := by rw [hβ]; exact (div_lt_one hrR).2 hnR
  have hmass := circular_mass_weighted N hNbig β hβ0 hβ1 32 (by norm_num)
  have hcβ : (N : ℝ) * β = c := by rw [hβ, hc]; ring
  rw [hcβ, show (2 : ℝ) / (9 * (32 - 1)) = 2 / 279 by norm_num] at hmass
  apply hmass.trans
  apply Finset.sum_le_sum
  intro a ha
  have haN : (a : ℝ) < N := by exact_mod_cast (mem_range.mp ha)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hgood : (phiR N c a < 32 ∨ phiL N c a < 32) →
      (2 * r * a + N) / (2 * N) = n := by
    intro hnear
    by_contra hbad
    have hreg : c + L ≤ (a : ℝ) ∨ (a : ℝ) + L ≤ c := by
      rcases window_cases r N n a hN hbad with h | h
      · left
        have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
        nlinarith
      · right
        have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
        nlinarith
    have hR : L ≤ phiR N c a := by
      unfold phiR
      split_ifs with h
      · rcases hreg with hA | hA <;> linarith
      · linarith
    have hL' : L ≤ phiL N c a := by
      unfold phiL
      split_ifs with h
      · rcases hreg with hA | hA <;> linarith
      · linarith
    rcases hnear with hn | hn <;> linarith
  have hnneg : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
  split_ifs with hn hg
  · exact le_rfl
  · exact (hg (hgood hn)).elim
  · exact hnneg
  · exact le_rfl

/-- Right axis: the 55 neighbouring words cover radius 27, weighted. -/
theorem rightMass_weighted (r : Nat) (hr : 0 < r) (k : Fin r) :
    1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 * (2 / 234) - 1/10000 ≤
      rightMass r k := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := circular_mass_weighted (2^208) (by norm_num) ((k.val : ℝ) / r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt)) 27 (by norm_num)
  rw [show (2 : ℝ) / (9 * (27 - 1)) = 2 / 234 by norm_num] at h
  have hfin : 1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 * (2 / 234) -
      1/10000 ≤ ∑ b : Fin (2^208),
      if phiR (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b.val < 27 ∨
        phiL (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b.val < 27
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b < 27 ∨
        phiL (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b < 27
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b) else 0)]
    simpa only [ampSq, paperPhaseAmplitude, eigenvalue] using h
  refine hfin.trans (Finset.sum_le_sum (fun b _ => ?_))
  dsimp only [rightMass]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- `∑_{k<r} cos(2πMk/r) ∈ {0, r}`, in particular nonnegative. -/
theorem sum_cos_nonneg (r M : ℕ) :
    0 ≤ ∑ k ∈ range r, Real.cos (k * (2 * Real.pi * M / r)) := by
  set θ : ℝ := 2 * Real.pi * M / r with hθ
  set ω : ℂ := Complex.exp (θ * Complex.I) with hω
  have hterm : ∀ k : ℕ, Real.cos (k * θ) = (ω ^ k).re := by
    intro k
    rw [hω, ← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast
    ring
  have hsum : ∑ k ∈ range r, Real.cos (k * θ) = (∑ k ∈ range r, ω ^ k).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  by_cases h1 : ω = 1
  · simp [h1]
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hr' : ω ^ r = 1 := by
      rw [hω, ← Complex.exp_nat_mul]
      have : (r : ℂ) * ((θ : ℂ) * Complex.I) = (M : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hθ]
        push_cast
        field_simp
      rw [this]
      exact Complex.exp_nat_mul_two_pi_mul_I M
    rw [geom_sum_eq h1, hr', sub_self, zero_div, Complex.zero_re]

/-- Average of the weight over all characters. -/
theorem sum_sin_sq_le (r M : ℕ) :
    ∑ k : Fin r, Real.sin (Real.pi * M * (k.val : ℝ) / r) ^ 2 ≤ (r : ℝ) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => Real.sin (Real.pi * M * (k : ℝ) / r) ^ 2)]
  have h := sum_cos_nonneg r M
  have he : ∀ k ∈ range r, Real.sin (Real.pi * M * (k : ℝ) / r) ^ 2 =
      1/2 - Real.cos (k * (2 * Real.pi * M / r)) / 2 := by
    intro k _
    rw [Real.sin_sq_eq_half_sub]
    congr 3
    ring
  have h2 : ∑ k ∈ range r, Real.cos (k * (2 * Real.pi * M / r)) / 2 =
      (∑ k ∈ range r, Real.cos (k * (2 * Real.pi * M / r))) / 2 := by
    rw [Finset.sum_div]
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, h2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

theorem sin_sq_mod (r m t : ℕ) (hr : 0 < r) :
    Real.sin (Real.pi * m * ((t % r : ℕ) : ℝ) / r) ^ 2 = Real.sin (Real.pi * m * t / r) ^ 2 := by
  have hrR : (r : ℝ) ≠ 0 := by positivity
  have ht : (t : ℝ) = ((t % r : ℕ) : ℝ) + r * ((t / r : ℕ) : ℝ) := by
    have := Nat.mod_add_div t r
    exact_mod_cast this.symm
  have he : Real.pi * m * ((t % r : ℕ) : ℝ) / r =
      Real.pi * m * t / r - ((m * (t / r) : ℕ) : ℝ) * Real.pi := by
    rw [ht]
    push_cast
    field_simp
    ring
  rw [he, Real.sin_sub_nat_mul_pi, mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq,
    one_pow, one_mul]

theorem left_weight_sum (r n : ℕ) :
    ∑ k : Fin r, Real.sin (Real.pi * ((2^n : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2 ≤ (r : ℝ) / 2 := by
  have h := sum_sin_sq_le r (2^n)
  simpa only [mul_div_assoc] using h

theorem right_weight_sum (r d : ℕ) (hr : 0 < r) :
    ∑ k : Fin r, Real.sin (Real.pi * ((2^208 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2 ≤
      (r : ℝ) / 2 := by
  have h := sum_sin_sq_le r (2^208 * d)
  refine le_of_eq_of_le (Finset.sum_congr rfl (fun k _ => ?_)) h
  rw [← mul_div_assoc, sin_sq_mod r (2^208) (d * k.val) hr]
  congr 2
  push_cast
  ring

theorem averaged_pair_coverage (r n d : Nat) (hr : r.Prime)
    (hNbig : 65536 ≤ 2^n) (hprecision : 64 * r ≤ 2^n)
    (accept : Fin (2^n) → Fin (2^208) → Prop) [∀ a b, Decidable (accept a b)]
    (haccept : ∀ (k : Fin r), k.val ≠ 0 → ∀ a b,
      ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val →
      rightGood r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b →
      accept a b) :
    (1 - 1 / (r : ℝ)) * (1 - 2/10000) - 1/279 - 1/234 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208),
      if accept a b then asymmetricPairMass r n 208 d (a, b) else 0 := by
  classical
  let A : Fin r → Fin (2^n) → ℝ := fun k a =>
    Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2^208) → ℝ := fun k b =>
    Complex.normSq (paperPhaseAmplitude 208 (((d * k.val % r : Nat) : ℝ) / r) b.val)
  let good : Fin r → Fin (2^n) → Fin (2^208) → Prop := fun k a b =>
    k.val ≠ 0 ∧ ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val ∧
      rightGood r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b
  let F : Fin r → Fin (2^n) → Fin (2^208) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let sL : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^n : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let sR : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^208 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2
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
      1 - sL k * (2 / 279) - 1/10000 ≤ ∑ a : Fin (2^n),
        if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val then A k a else 0 := by
    have h := window_mass_left_weighted r (2^n) k.val
      (Nat.pos_of_ne_zero hk) k.isLt hNbig hprecision
    rw [Fin.sum_univ_eq_sum_range (fun a =>
      if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a = k.val then
        Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a) else 0)]
    simpa only [ShorECDLP.Quantum.OrderFinding.nearestNumerator, paperPhaseAmplitude,
      eigenvalue] using h
  have hright (k : Fin r) :
      1 - sR k * (2 / 234) - 1/10000 ≤ rightMass r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ :=
    rightMass_weighted r hr.pos ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩
  have step3 : ∀ k : Fin r,
      (if k.val = 0 then 0 else (1 - 2/10000 : ℝ)) - sL k * (2 / 279) - sR k * (2 / 234) ≤
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    intro k
    have hsL : 0 ≤ sL k := sq_nonneg _
    have hsR : 0 ≤ sR k := sq_nonneg _
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b :=
        Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF k a b))
      nlinarith
    · rw [if_neg hk]
      have he : (∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b) =
          (∑ a : Fin (2^n), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val
            then A k a else 0) * rightMass r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ := by
        rw [rightMass, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F, good, B]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [he]
      have hl := hleft k hk
      have hrt := hright k
      have hsL1 : sL k ≤ 1 := Real.sin_sq_le_one _
      have hsR1 : sR k ≤ 1 := Real.sin_sq_le_one _
      have hl0 : 0 ≤ 1 - sL k * (2 / 279) - 1/10000 := by linarith
      have hr0 : 0 ≤ 1 - sR k * (2 / 234) - 1/10000 := by linarith
      have hprod := mul_le_mul hl hrt hr0 (hl0.trans hl)
      nlinarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  have hcount : (∑ k : Fin r, (if k.val = 0 then (0 : ℝ) else (1 - 2/10000))) =
      ((r : ℝ) - 1) * (1 - 2/10000) := by
    have hz : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
      simp [hr.pos]
    calc
      _ = ∑ k : Fin r, ((1 - 2/10000 : ℝ) - (1 - 2/10000) * (if k.val = 0 then 1 else 0)) := by
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
  have hlow : ((r : ℝ) - 1) * (1 - 2/10000) - (r : ℝ) / 2 * (2 / 279) - (r : ℝ) / 2 * (2 / 234) ≤
      ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    have h1 : (∑ k : Fin r, sL k) * (2 / 279) ≤ (r : ℝ) / 2 * (2 / 279) :=
      mul_le_mul_of_nonneg_right hL (by norm_num)
    have h2 : (∑ k : Fin r, sR k) * (2 / 234) ≤ (r : ℝ) / 2 * (2 / 234) :=
      mul_le_mul_of_nonneg_right hR (by norm_num)
    linarith
  have hlower := mul_le_mul_of_nonneg_left hlow hrinv
  have heval : (r : ℝ)⁻¹ * (((r : ℝ) - 1) * (1 - 2/10000) - (r : ℝ) / 2 * (2 / 279) -
      (r : ℝ) / 2 * (2 / 234)) = (1 - 1 / (r : ℝ)) * (1 - 2/10000) - 1/279 - 1/234 := by
    field_simp
  rw [heval, step2] at hlower
  exact hlower.trans step1

theorem success_budget (r : ℝ) (hr : 1000000 ≤ r) :
    (99 : ℝ)/100 ≤ (1 - 1 / r) * (1 - 2/10000) - 1/279 - 1/234 := by
  have hr0 : 0 < r := by linarith
  have hinv : 1 / r ≤ (1 : ℝ) / 1000000 :=
    one_div_le_one_div_of_le (by norm_num) hr
  nlinarith

theorem precision262 : 64 * order ≤ 2^262 := by norm_num [order]

def params262 : DecoderParams := ⟨262,208,by decide,by decide,by decide,by decide⟩
def pairRecovered262 (d a b : Nat) : Bool :=
  decide (∃i : Fin 55,(d : ZMod order)∈fixedCandidates params262 a (neighborWord b ((i.val : ℤ)-27)))

theorem pairRecovered262_of_character (d : Nat) (k : Fin order) (hk : k.val≠0)
    (a : Fin (2^262)) (b : Fin (2^208))
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 262 a.val=k.val)
    (hb : rightGood order ⟨d*k.val%order,Nat.mod_lt _ order_prime.pos⟩ b) :
    pairRecovered262 d a.val b.val=true := by
  classical
  obtain ⟨j,hlo,hhi,hj⟩:=hb
  let i : Fin 55:=⟨(j+27).toNat,by omega⟩
  have hi : (i.val : ℤ)-27=j := by dsimp [i];omega
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
      (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 262 a.val : ZMod order)⁻¹=d
    rw [ha]
    simp only [ZMod.natCast_mod,Nat.cast_mul]
    field_simp

theorem pair_success262 (Q : Point) (d : Nat) (_hn : Q≠0) (_hd : Q=d•G) :
    (99 : ℝ)/100 ≤ ∑a : Fin (2^262),∑b : Fin (2^208),
      if pairRecovered262 d a.val b.val then asymmetricPairMass order 262 208 d (a,b) else 0 := by
  have h:=averaged_pair_coverage order 262 d order_prime (by norm_num) precision262
    (fun a b=>pairRecovered262 d a.val b.val=true)
    (fun k hk a b ha hb=>pairRecovered262_of_character d k hk a b ha hb)
  exact (success_budget order (by norm_num [order])).trans h

theorem decoder_budget262 :
    55*decoderCandidateLimit .wrappedShift params262 ≤ budget55 := by
  norm_num [decoderCandidateLimit,trialCandidateLimit,params262,budget55,order]

end
end ShorECDLP.Entrant.SinAverage
