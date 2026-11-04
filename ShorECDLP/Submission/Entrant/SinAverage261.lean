import ShorECDLP.Submission.Entrant.SinAverage
import ShorECDLP.Submission.Entrant.SharpTail
import ShorECDLP.Submission.Entrant.NeighborSuffix56

/-! Averaged success bound for a 261/208 two-axis readout with 56 right neighbours.

Same argument as `SinAverage` (weights `sin² (π N β)` average to at most `1/2`), with the
sharp constants of `SharpTail`: per-term `9.8695 φ²` instead of `9 φ²`, tail sums
`1/(R - 1/2)` instead of `1/(R - 1)`, two coupled radii per axis, far split at `1099511627776`. -/

namespace ShorECDLP.Entrant.SinAverage261
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Entrant.WindowMassSharpProof ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open ShorECDLP.Entrant.SinAverage ShorECDLP.Entrant.SharpTail
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 300

theorem ampSq_weighted_sharp (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat) (φ : ℝ)
    (hd : 0 < φ) (hsmall : φ / (N : ℝ) ≤ 1/1048576)
    (he : |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (φ / (N : ℝ)))) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (98695/10000 * φ ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow := per_term_sharp (N : ℝ) φ hNR hd hsmall
  have hu : 0 < φ / (N : ℝ) := div_pos hd hNR
  have hsl := sin_pi_mul_ge_sharp (φ / N) hu hsmall
  have hsinpos : 0 < Real.sin (Real.pi * (φ / (N : ℝ))) := by nlinarith
  have hpos : 0 < |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by rw [he]; exact hsinpos
  have hne : Real.sin (Real.pi * (β - (a : ℝ) / N)) ≠ 0 := abs_pos.mp hpos
  refine (ampSq_le_weighted N hN β a hne).trans ?_
  have h9 : 98695/10000 * φ ^ 2 ≤ ((N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))|) ^ 2 := by
    rw [he]; exact hlow
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h9

theorem ampSq_phiR_sharp (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiR N ((N : ℝ) * β) a)
    (hsmall : phiR N ((N : ℝ) * β) a / (N : ℝ) ≤ 1/1048576) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (98695/10000 * (phiR N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_weighted_sharp N hN β a _ hd hsmall
    (abs_sin_phiR N hN β a hd (hsmall.trans (by norm_num)))

theorem ampSq_phiL_sharp (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiL N ((N : ℝ) * β) a)
    (hsmall : phiL N ((N : ℝ) * β) a / (N : ℝ) ≤ 1/1048576) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (98695/10000 * (phiL N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_weighted_sharp N hN β a _ hd hsmall
    (abs_sin_phiL N hN β a hd (hsmall.trans (by norm_num)))

theorem directed_tail_sharp (N : Nat) (β : ℝ) (S : Finset Nat) (d : Nat → ℝ) (s R : ℝ)
    (hs : 0 ≤ s) (hR : 1/2 < R) (hd : ∀ a ∈ S, R ≤ d a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |d a - d b| < 1 → a = b)
    (hpt : ∀ a ∈ S, ampSq N β a ≤ s / (98695/10000 * (d a) ^ 2)) :
    ∑ a ∈ S, ampSq N β a ≤ s / (98695/10000) * (1 / (R - 1/2)) := by
  have hi := sum_inv_sq_le_half S d R hR hd hsep
  calc
    _ ≤ ∑ a ∈ S, (s / (98695/10000)) * (1 / (d a) ^ 2) := by
      apply Finset.sum_le_sum
      intro a ha
      have hda : 0 < d a := by linarith [hd a ha]
      calc ampSq N β a ≤ s / (98695/10000 * (d a) ^ 2) := hpt a ha
        _ = (s / (98695/10000)) * (1 / (d a) ^ 2) := by field_simp
    _ = (s / (98695/10000)) * (∑ a ∈ S, 1 / (d a) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (s / (98695/10000)) * (1 / (R - 1/2)) := mul_le_mul_of_nonneg_left hi (by positivity)

/-- Two-radii weighted circular concentration with the sharp constants. -/
theorem circular_mass_weighted2 (N : Nat) (hNbig : 2^60 ≤ N) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R1 R2 : ℝ) (hR1 : 1/2 < R1) (hR2 : 1/2 < R2) :
    1 - Real.sin (Real.pi * N * β) ^ 2 * ((1 / (R1 - 1/2) + 1 / (R2 - 1/2)) / (98695/10000)) - 1/100000000000 ≤
      ∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2
        then ampSq N β a else 0 := by
  classical
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNreal : (2^60 : ℝ) ≤ N := by exact_mod_cast hNbig
  set s := Real.sin (Real.pi * N * β) ^ 2 with hsdef
  have hs0 : 0 ≤ s := sq_nonneg _
  let RS := (Finset.range N).filter
    (fun a => R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 1099511627776)
  let LS := (Finset.range N).filter
    (fun a => R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 1099511627776)
  have rBound : ∑ a ∈ RS, ampSq N β a ≤ s / (98695/10000) * (1 / (R1 - 1/2)) := by
    apply directed_tail_sharp N β RS (phiR N ((N : ℝ) * β)) s R1 hs0 hR1
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiR_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiR_sharp N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      linarith [hd.2]
  have lBound : ∑ a ∈ LS, ampSq N β a ≤ s / (98695/10000) * (1 / (R2 - 1/2)) := by
    apply directed_tail_sharp N β LS (phiL N ((N : ℝ) * β)) s R2 hs0 hR2
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiL_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiL_sharp N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      linarith [hd.2]
  have fBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < 1099511627776 ∨ phiL N ((N : ℝ) * β) a < 1099511627776)
      then ampSq N β a else 0) ≤ (1 : ℝ) / 100000000000 := by
    have hc := circular_mass N hN β (1099511627776) hβ0 hβ1 (by norm_num)
    have hs : (∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < 1099511627776 ∨ phiL N ((N : ℝ) * β) a < 1099511627776
        then ampSq N β a else 0) +
      (∑ a ∈ Finset.range N,
        if ¬(phiR N ((N : ℝ) * β) a < 1099511627776 ∨ phiL N ((N : ℝ) * β) a < 1099511627776)
        then ampSq N β a else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert parseval N hN β using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    have hf : 3 / (Real.pi ^ 2 * ((1099511627776 : ℝ) - 1)) ≤ (1 : ℝ) / 100000000000 := by
      have h := far_tail_2pow40
      norm_num at h ⊢
      exact h
    linarith
  have cover (a : Nat) :
      (if ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
        then ampSq N β a else 0) ≤
      (if R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 1099511627776
        then ampSq N β a else 0) +
      (if R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 1099511627776
        then ampSq N β a else 0) +
      (if ¬(phiR N ((N : ℝ) * β) a < 1099511627776 ∨ phiL N ((N : ℝ) * β) a < 1099511627776)
        then ampSq N β a else 0) := by
    have ha0 : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
    by_cases hb : ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
    · rw [if_pos hb]
      have hr : R1 ≤ phiR N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inl h))
      have hl : R2 ≤ phiL N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inr h))
      by_cases hRR : R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 1099511627776
      · rw [if_pos hRR]
        split_ifs <;> linarith
      · rw [if_neg hRR]
        by_cases hLL : R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 1099511627776
        · rw [if_pos hLL]
          split_ifs <;> linarith
        · rw [if_neg hLL]
          have hf : ¬(phiR N ((N : ℝ) * β) a < 1099511627776 ∨ phiL N ((N : ℝ) * β) a < 1099511627776) := by
            rintro (h | h)
            · exact hRR ⟨hr, h⟩
            · exact hLL ⟨hl, h⟩
          rw [if_pos hf]
          linarith
    · rw [if_neg hb]
      split_ifs <;> linarith
  have badBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
      then ampSq N β a else 0) ≤ s * ((1 / (R1 - 1/2) + 1 / (R2 - 1/2)) / (98695/10000)) + 1/100000000000 := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.range N) => cover a)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    have hRs : (∑ a ∈ Finset.range N,
        if R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 1099511627776
        then ampSq N β a else 0) ≤ s / (98695/10000) * (1 / (R1 - 1/2)) := by
      simpa only [RS, Finset.sum_filter] using rBound
    have hLs : (∑ a ∈ Finset.range N,
        if R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 1099511627776
        then ampSq N β a else 0) ≤ s / (98695/10000) * (1 / (R2 - 1/2)) := by
      simpa only [LS, Finset.sum_filter] using lBound
    have he : s / (98695/10000) * (1 / (R1 - 1/2)) + s / (98695/10000) * (1 / (R2 - 1/2)) =
        s * ((1 / (R1 - 1/2) + 1 / (R2 - 1/2)) / (98695/10000)) := by
      ring
    linarith
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
  linarith


/-- Nearest-numerator window at half-width `L = N/(2r) ∈ (16, 17]`, coupled radii. -/
theorem window_mass_left261 (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r)
    (hNbig : 2^60 ≤ N) (hrN : 32 * r < N) (hrN2 : N ≤ 34 * r) :
    1 - Real.sin (Real.pi * N * ((n : ℝ) / (r : ℝ))) ^ 2 * ((2/31 + 2/33) / (98695/10000))
      - 1/100000000000 ≤
      ∑ a ∈ range N,
        if (2 * r * a + N) / (2 * N) = n then ampSq N ((n : ℝ) / (r : ℝ)) a else 0 := by
  have hr : 0 < r := by omega
  have hN : 0 < N := by omega
  set β : ℝ := (n : ℝ) / (r : ℝ) with hβ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (n : ℝ) < r := by exact_mod_cast hnr
  set c : ℝ := (N : ℝ) * n / r with hc
  set L : ℝ := (N : ℝ) / (2 * r) with hL
  have hcr : c * r = N * n := by rw [hc]; field_simp
  have hLr : L * (2 * r) = N := by rw [hL]; field_simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnr' : (n : ℝ) + 1 ≤ r := by exact_mod_cast hnr
  have hrN' : 32 * (r : ℝ) < N := by exact_mod_cast hrN
  have hrN2' : (N : ℝ) ≤ 34 * r := by exact_mod_cast hrN2
  have hL16 : 16 < L := by nlinarith
  have hL17 : L ≤ 17 := by nlinarith
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβ1 : β < 1 := by rw [hβ]; exact (div_lt_one hrR).2 hnR
  set R1 : ℝ := (⌈c + L⌉ : ℝ) - c with hR1
  set R2 : ℝ := c - (⌈c - L⌉ : ℝ) + 1 with hR2
  have hceil1 := Int.le_ceil (c + L)
  have hceil1' := Int.ceil_lt_add_one (c + L)
  have hceil2 := Int.le_ceil (c - L)
  have hceil2' := Int.ceil_lt_add_one (c - L)
  have hR1L : L ≤ R1 := by rw [hR1]; linarith
  have hR2L : L < R2 := by rw [hR2]; linarith
  have hR1u : R1 < L + 1 := by rw [hR1]; linarith
  have hR2u : R2 ≤ L + 1 := by rw [hR2]; linarith
  have hgap : (33 : ℝ) ≤ R1 + R2 := by
    have hm : (31 : ℝ) < ((⌈c + L⌉ - ⌈c - L⌉ : ℤ) : ℝ) := by push_cast; linarith
    have hm' : (31 : ℤ) < ⌈c + L⌉ - ⌈c - L⌉ := by exact_mod_cast hm
    have hm'' : (32 : ℤ) ≤ ⌈c + L⌉ - ⌈c - L⌉ := by omega
    have hm3 : (32 : ℝ) ≤ ((⌈c + L⌉ - ⌈c - L⌉ : ℤ) : ℝ) := by exact_mod_cast hm''
    push_cast at hm3
    rw [hR1, hR2]; linarith
  have hpair := left261_pair R1 R2 (by linarith) (by linarith) hgap
  have hconst : 1 / (R1 - 1/2) + 1 / (R2 - 1/2) ≤ 2/31 + 2/33 := by
    have e : (1 : ℝ) / 15.5 + 1 / 16.5 = 2/31 + 2/33 := by norm_num
    linarith
  have hmass := circular_mass_weighted2 N hNbig β hβ0 hβ1 R1 R2 (by linarith) (by linarith)
  have hcβ : (N : ℝ) * β = c := by rw [hβ, hc]; ring
  rw [hcβ] at hmass
  have hs0 : 0 ≤ Real.sin (Real.pi * N * β) ^ 2 := sq_nonneg _
  have hmono : Real.sin (Real.pi * N * β) ^ 2 * ((1 / (R1 - 1/2) + 1 / (R2 - 1/2)) / (98695/10000)) ≤
      Real.sin (Real.pi * N * β) ^ 2 * ((2/31 + 2/33) / (98695/10000)) := by
    apply mul_le_mul_of_nonneg_left _ hs0
    exact div_le_div_of_nonneg_right hconst (by norm_num)
  have hmass' : 1 - Real.sin (Real.pi * N * β) ^ 2 * ((2/31 + 2/33) / (98695/10000))
      - 1/100000000000 ≤ ∑ a ∈ Finset.range N,
        if phiR N c a < R1 ∨ phiL N c a < R2 then ampSq N β a else 0 := by
    linarith
  apply hmass'.trans
  apply Finset.sum_le_sum
  intro a ha
  have haN : (a : ℝ) < N := by exact_mod_cast (mem_range.mp ha)
  have haN1 : (a : ℝ) + 1 ≤ N := by exact_mod_cast (mem_range.mp ha)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hgood : (phiR N c a < R1 ∨ phiL N c a < R2) →
      (2 * r * a + N) / (2 * N) = n := by
    intro hnear
    have hwin : c - L ≤ (a : ℝ) ∧ (a : ℝ) < c + L := by
      rcases hnear with hn | hn
      · unfold phiR at hn
        split_ifs at hn with h
        · have h1 : (a : ℝ) < (⌈c + L⌉ : ℝ) := by rw [hR1] at hn; linarith
          have h2 : (a : ℤ) < ⌈c + L⌉ := by exact_mod_cast h1
          have h3 := Int.lt_ceil.mp h2
          push_cast at h3
          constructor <;> linarith
        · exfalso; linarith
      · unfold phiL at hn
        split_ifs at hn with h
        · have h1 : (⌈c - L⌉ : ℝ) - 1 < (a : ℝ) := by rw [hR2] at hn; linarith
          have h2 : ⌈c - L⌉ - 1 < (a : ℤ) := by exact_mod_cast h1
          have h3 : ⌈c - L⌉ ≤ (a : ℤ) := by omega
          have h4 := Int.ceil_le.mp h3
          push_cast at h4
          constructor <;> linarith
        · exfalso; linarith
    by_contra hbad
    rcases window_cases r N n a hN hbad with h | h
    · have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
      have : c + L ≤ (a : ℝ) := by nlinarith
      linarith [hwin.2]
    · have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
      have : (a : ℝ) < c - L := by nlinarith
      linarith [hwin.1]
  have hnneg : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
  split_ifs with hn hg
  · exact le_rfl
  · exact (hg (hgood hn)).elim
  · exact hnneg
  · exact le_rfl

def rightGood56 (r : Nat) (k : Fin r) (b : Fin (2^208)) : Prop :=
  ∃ j : ℤ, -28 ≤ j ∧ j ≤ 27 ∧ neighborWord b.val j = (reducedPeak r 208 k).val

noncomputable def rightMass56 (r : Nat) (k : Fin r) : ℝ := by
  classical
  exact ∑ b : Fin (2^208), if rightGood56 r k b then
    Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0

theorem peak_round (r : Nat) (hr : 0 < r) (k : Fin r) :
    round ((2^208 : Nat) * ((k.val : ℝ) / r)) = (reducedPeakRaw r 208 k : ℤ) := by
  have hc : (2^208 : Nat) * ((k.val : ℝ) / r) = ((2^208 * k.val : Nat) : ℝ) / r := by
    push_cast; ring
  rw [hc, round_nat_ratio _ r hr]
  simp only [reducedPeakRaw, Nat.mul_assoc]

theorem word_of_lift (r : Nat) (k : Fin r) (b : Nat) (B z : ℤ)
    (hB : B = (b : ℤ) + z * (2^208 : Nat)) :
    neighborWord b ((reducedPeakRaw r 208 k : ℤ) - B) = (reducedPeak r 208 k).val := by
  have hm : ((b : ℤ) + ((reducedPeakRaw r 208 k : ℤ) - B)) % (2^208 : Nat) =
      (reducedPeakRaw r 208 k : ℤ) % (2^208 : Nat) := by
    rw [hB, show (b : ℤ) + ((reducedPeakRaw r 208 k : ℤ) - ((b : ℤ) + z * (2^208 : Nat))) =
      (reducedPeakRaw r 208 k : ℤ) + (-z) * (2^208 : Nat) by ring]
    exact Int.add_mul_emod_self_right _ _ _
  unfold neighborWord
  rw [hm]
  simp only [reducedPeak, ← Int.natCast_mod, Int.toNat_natCast]

/-- Shifts `-28..27`: right radius `29 - e`, left radius `28 + e`, `e = c - round c`. -/
theorem neighbor_coverage56 (r : Nat) (hr : 0 < r) (k : Fin r) (b : Fin (2^208)) (e : ℝ)
    (he : e = (2^208 : Nat) * ((k.val : ℝ) / r) - round ((2^208 : Nat) * ((k.val : ℝ) / r)))
    (hc : phiR (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b.val < 29 - e ∨
      phiL (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b.val < 28 + e) :
    rightGood56 r k b := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := (2^208 : Nat) * ((k.val : ℝ) / r) with hcdef
  set p : ℤ := (reducedPeakRaw r 208 k : ℤ) with hpdef
  have hround : round c = p := peak_round r hr k
  have hcp : |c - (p : ℝ)| ≤ 1/2 := by rw [← hround]; exact abs_sub_round c
  have hcp' := abs_le.mp hcp
  have hep : e = c - p := by rw [he, hround]
  have hNR : (0 : ℝ) < ((2^208 : Nat) : ℝ) := by positivity
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hcN : c < ((2^208 : Nat) : ℝ) := by
    rw [hcdef]
    have hk : (k.val : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast k.isLt)
    nlinarith
  have hp0 : (0 : ℤ) ≤ p := by
    have : (-1 : ℝ) < (p : ℝ) := by linarith
    have : (-1 : ℤ) < p := by exact_mod_cast this
    omega
  have hb0 : (0 : ℝ) ≤ (b.val : ℝ) := Nat.cast_nonneg _
  have hbN : (b.val : ℝ) < ((2^208 : Nat) : ℝ) := by exact_mod_cast b.isLt
  have hbNz : (b.val : ℤ) < ((2^208 : Nat) : ℤ) := by exact_mod_cast b.isLt
  have key : ∃ B z : ℤ, B = (b.val : ℤ) + z * (2^208 : Nat) ∧ p - 27 ≤ B ∧ B ≤ p + 28 := by
    rcases hc with hc | hc
    · unfold phiR at hc
      split_ifs at hc with h
      · refine ⟨b.val, 0, by ring, ?_, ?_⟩
        · have h1 : (p : ℝ) - 1 < (b.val : ℝ) := by linarith
          have h2 : p - 1 < (b.val : ℤ) := by exact_mod_cast h1
          omega
        · have h1 : (b.val : ℝ) < (p : ℝ) + 29 := by linarith
          have h2 : (b.val : ℤ) < p + 29 := by exact_mod_cast h1
          omega
      · refine ⟨b.val + (2^208 : Nat), 1, by ring, ?_, ?_⟩
        · have h1 : (p : ℝ) - 1 < (b.val : ℝ) + ((2^208 : Nat) : ℝ) := by linarith
          have h2 : p - 1 < (b.val : ℤ) + ((2^208 : Nat) : ℤ) := by exact_mod_cast h1
          omega
        · have h1 : (b.val : ℝ) + ((2^208 : Nat) : ℝ) < (p : ℝ) + 29 := by linarith
          have h2 : (b.val : ℤ) + ((2^208 : Nat) : ℤ) < p + 29 := by exact_mod_cast h1
          omega
    · unfold phiL at hc
      split_ifs at hc with h
      · refine ⟨b.val, 0, by ring, ?_, ?_⟩
        · have h1 : (p : ℝ) - 28 < (b.val : ℝ) := by linarith
          have h2 : p - 28 < (b.val : ℤ) := by exact_mod_cast h1
          omega
        · have h1 : (b.val : ℝ) < (p : ℝ) + 1 := by linarith
          have h2 : (b.val : ℤ) < p + 1 := by exact_mod_cast h1
          omega
      · refine ⟨b.val - (2^208 : Nat), -1, by ring, ?_, ?_⟩
        · have h1 : (p : ℝ) - 28 < (b.val : ℝ) - ((2^208 : Nat) : ℝ) := by linarith
          have h2 : p - 28 < (b.val : ℤ) - ((2^208 : Nat) : ℤ) := by exact_mod_cast h1
          omega
        · omega
  obtain ⟨B, z, hB, hlo, hhi⟩ := key
  refine ⟨p - B, by omega, by omega, ?_⟩
  exact word_of_lift r k b.val B z hB

/-- Right axis: the 56 neighbouring words, weighted, sharp constants. -/
theorem rightMass_weighted56 (r : Nat) (hr : 0 < r) (k : Fin r) :
    1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
      ((1/27 + 1/29) / (98695/10000)) - 1/100000000000 ≤ rightMass56 r k := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set e : ℝ := (2^208 : Nat) * ((k.val : ℝ) / r) - round ((2^208 : Nat) * ((k.val : ℝ) / r))
    with hedef
  have he1 := abs_le.mp (abs_sub_round ((2^208 : Nat) * ((k.val : ℝ) / r)))
  rw [← hedef] at he1
  have h := circular_mass_weighted2 (2^208) (by norm_num) ((k.val : ℝ) / r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt)) (29 - e) (28 + e)
    (by linarith) (by linarith)
  have hpair := right56_pair (28 + e) (29 - e) (by linarith) (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 := sq_nonneg _
  have hmono : Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
      ((1 / (29 - e - 1/2) + 1 / (28 + e - 1/2)) / (98695/10000)) ≤
      Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
      ((1/27 + 1/29) / (98695/10000)) := by
    apply mul_le_mul_of_nonneg_left _ hs0
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith
  have hfin : 1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
      ((1/27 + 1/29) / (98695/10000)) - 1/100000000000 ≤ ∑ b : Fin (2^208),
      if phiR (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b.val < 29 - e ∨
        phiL (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b.val < 28 + e
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b < 29 - e ∨
        phiL (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b < 28 + e
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b) else 0)]
    have h' : 1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((1/27 + 1/29) / (98695/10000)) - 1/100000000000 ≤ ∑ a ∈ Finset.range (2^208),
        if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) a < 29 - e ∨
          phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) a < 28 + e
        then ampSq (2^208) ((k.val : ℝ) / r) a else 0 := by
      linarith
    simpa only [ampSq, paperPhaseAmplitude, eigenvalue] using h'
  refine hfin.trans (Finset.sum_le_sum (fun b _ => ?_))
  dsimp only [rightMass56]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage56 r hr k b e hedef hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem averaged_pair_coverage261 (r n d : Nat) (hr : r.Prime)
    (hNbig : 2^60 ≤ 2^n) (hprecision : 32 * r < 2^n) (hprecision2 : 2^n ≤ 34 * r)
    (accept : Fin (2^n) → Fin (2^208) → Prop) [∀ a b, Decidable (accept a b)]
    (haccept : ∀ (k : Fin r), k.val ≠ 0 → ∀ a b,
      ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val →
      rightGood56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b →
      accept a b) :
    (1 - 1 / (r : ℝ)) * (1 - 2/100000000000) - ((2/31 + 2/33) / (98695/10000)) / 2 - ((1/27 + 1/29) / (98695/10000)) / 2 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208),
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
      1 - sL k * ((2/31 + 2/33) / (98695/10000)) - 1/100000000000 ≤ ∑ a : Fin (2^n),
        if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val then A k a else 0 := by
    have h := window_mass_left261 r (2^n) k.val
      (Nat.pos_of_ne_zero hk) k.isLt hNbig hprecision hprecision2
    rw [Fin.sum_univ_eq_sum_range (fun a =>
      if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a = k.val then
        Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a) else 0)]
    simpa only [ShorECDLP.Quantum.OrderFinding.nearestNumerator, paperPhaseAmplitude,
      eigenvalue] using h
  have hright (k : Fin r) :
      1 - sR k * ((1/27 + 1/29) / (98695/10000)) - 1/100000000000 ≤ rightMass56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ :=
    rightMass_weighted56 r hr.pos ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩
  have step3 : ∀ k : Fin r,
      (if k.val = 0 then 0 else (1 - 2/100000000000 : ℝ)) - sL k * ((2/31 + 2/33) / (98695/10000)) - sR k * ((1/27 + 1/29) / (98695/10000)) ≤
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
      have hl := hleft k hk
      have hrt := hright k
      have hsL1 : sL k ≤ 1 := Real.sin_sq_le_one _
      have hsR1 : sR k ≤ 1 := Real.sin_sq_le_one _
      have hl0 : 0 ≤ 1 - sL k * ((2/31 + 2/33) / (98695/10000)) - 1/100000000000 := by linarith
      have hr0 : 0 ≤ 1 - sR k * ((1/27 + 1/29) / (98695/10000)) - 1/100000000000 := by linarith
      have hprod := mul_le_mul hl hrt hr0 (hl0.trans hl)
      nlinarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  have hcount : (∑ k : Fin r, (if k.val = 0 then (0 : ℝ) else (1 - 2/100000000000))) =
      ((r : ℝ) - 1) * (1 - 2/100000000000) := by
    have hz : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
      simp [hr.pos]
    calc
      _ = ∑ k : Fin r, ((1 - 2/100000000000 : ℝ) - (1 - 2/100000000000) * (if k.val = 0 then 1 else 0)) := by
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
  have hlow : ((r : ℝ) - 1) * (1 - 2/100000000000) - (r : ℝ) / 2 * ((2/31 + 2/33) / (98695/10000)) - (r : ℝ) / 2 * ((1/27 + 1/29) / (98695/10000)) ≤
      ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    have h1 : (∑ k : Fin r, sL k) * ((2/31 + 2/33) / (98695/10000)) ≤ (r : ℝ) / 2 * ((2/31 + 2/33) / (98695/10000)) :=
      mul_le_mul_of_nonneg_right hL (by norm_num)
    have h2 : (∑ k : Fin r, sR k) * ((1/27 + 1/29) / (98695/10000)) ≤ (r : ℝ) / 2 * ((1/27 + 1/29) / (98695/10000)) :=
      mul_le_mul_of_nonneg_right hR (by norm_num)
    linarith
  have hlower := mul_le_mul_of_nonneg_left hlow hrinv
  have heval : (r : ℝ)⁻¹ * (((r : ℝ) - 1) * (1 - 2/100000000000) - (r : ℝ) / 2 * ((2/31 + 2/33) / (98695/10000)) -
      (r : ℝ) / 2 * ((1/27 + 1/29) / (98695/10000))) = (1 - 1 / (r : ℝ)) * (1 - 2/100000000000) - ((2/31 + 2/33) / (98695/10000)) / 2 - ((1/27 + 1/29) / (98695/10000)) / 2 := by
    field_simp
  rw [heval, step2] at hlower
  exact hlower.trans step1



theorem success_budget261 (r : ℝ) (hr : 1000000 ≤ r) :
    (99 : ℝ)/100 ≤ (1 - 1 / r) * (1 - 2/100000000000) - ((2/31 + 2/33) / (98695/10000)) / 2 -
      ((1/27 + 1/29) / (98695/10000)) / 2 := by
  have hr0 : 0 < r := by linarith
  have hinv : 1 / r ≤ (1 : ℝ) / 1000000 :=
    one_div_le_one_div_of_le (by norm_num) hr
  have hinv0 : 0 ≤ 1 / r := by positivity
  nlinarith

theorem precision261 : 32 * order < 2^261 := by norm_num [order]
theorem precision261b : 2^261 ≤ 34 * order := by norm_num [order]

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
  have h:=averaged_pair_coverage261 order 261 d order_prime (by norm_num) precision261 precision261b
    (fun a b=>pairRecovered261 d a.val b.val=true)
    (fun k hk a b ha hb=>pairRecovered261_of_character d k hk a b ha hb)
  exact (success_budget261 order (by norm_num [order])).trans h

theorem decoder_budget261 :
    56*decoderCandidateLimit .wrappedShift params261 ≤ budget55 := by
  norm_num [decoderCandidateLimit,trialCandidateLimit,params261,budget55,order]

end
end ShorECDLP.Entrant.SinAverage261
