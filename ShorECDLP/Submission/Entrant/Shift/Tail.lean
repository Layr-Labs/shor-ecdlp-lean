import ShorECDLP.Submission.Entrant.WindowMass

/-! EDITABLE. Mass outside an asymmetric window of a fine QPE register.

For a window `[s₀, s₀ + W)` of outcomes and a peak `c = s₀ + δ` with `1 ≤ δ ≤ W - 2`,
the QPE mass outside the window is at most `(K / 2) (1 / δ + 1 / (W - 1 - δ)) + 2 / N`,
`K = 406 / 1000 ≥ 4 / π²`. -/

namespace ShorECDLP.Entrant

namespace WindowMassProof

open Finset

set_option maxHeartbeats 1000000 in
lemma window_tail (N W s0 : ℕ) (c : ℝ) (hsW : s0 + W ≤ N)
    (hδ1 : 1 ≤ c - s0) (hδ2 : c - s0 ≤ (W : ℝ) - 2) :
    ∑ a ∈ range N, (if s0 ≤ a ∧ a < s0 + W then 0 else ampSq N (c / N) a) ≤
      (406 / 1000) / 2 * (1 / (c - s0) + 1 / ((W : ℝ) - 1 - (c - s0))) + 2 / (N : ℝ) := by
  have hW2 : (2 : ℝ) ≤ W := by linarith
  have hNW : ((s0 : ℝ) + W) ≤ N := by exact_mod_cast hsW
  have hs0 : (0 : ℝ) ≤ s0 := Nat.cast_nonneg _
  have hNR : (0 : ℝ) < N := by linarith
  have hN : 0 < N := by exact_mod_cast hNR
  set δ : ℝ := c - s0 with hδ
  set β : ℝ := c / N with hβ
  set K : ℝ := 406 / 1000 with hK
  have hK0 : 0 ≤ K := by norm_num [hK]
  set e : ℝ := 1 / (N : ℝ) ^ 2 with he
  have hpt : ∀ a ∈ range N, (if s0 ≤ a ∧ a < s0 + W then 0 else ampSq N β a) ≤
      (if s0 + W ≤ a then
          K * (1 / (4 * ((a : ℝ) - c) ^ 2) + 1 / (4 * ((N : ℝ) - ((a : ℝ) - c)) ^ 2)) + e
        else 0) +
      (if a < s0 then
          K * (1 / (4 * (c - (a : ℝ)) ^ 2) + 1 / (4 * ((N : ℝ) - (c - (a : ℝ))) ^ 2)) + e
        else 0) := by
    intro a ha
    have haN : (a : ℝ) < N := by exact_mod_cast mem_range.mp ha
    have he0 : 0 ≤ e := by positivity
    have hi₂ : 0 ≤ (if s0 + W ≤ a then
        K * (1 / (4 * ((a : ℝ) - c) ^ 2) + 1 / (4 * ((N : ℝ) - ((a : ℝ) - c)) ^ 2)) + e
          else 0) := by
      split_ifs <;> positivity
    have hi₁ : 0 ≤ (if a < s0 then
        K * (1 / (4 * (c - (a : ℝ)) ^ 2) + 1 / (4 * ((N : ℝ) - (c - (a : ℝ))) ^ 2)) + e
          else 0) := by
      split_ifs <;> positivity
    by_cases hw : s0 ≤ a ∧ a < s0 + W
    · rw [if_pos hw]
      linarith
    · rw [if_neg hw]
      rcases Nat.lt_or_ge a s0 with h | h
      · have h' : (a : ℝ) + 1 ≤ s0 := by exact_mod_cast h
        rw [if_pos h, if_neg (by omega)]
        have hb := point_bound N hN (2 * Real.pi * (β - a / N)) (c - (a : ℝ))
          (by linarith) (by linarith) (Or.inl (by rw [hβ]; field_simp))
        have : ampSq N β a ≤
            K * (1 / (4 * (c - (a : ℝ)) ^ 2) + 1 / (4 * ((N : ℝ) - (c - (a : ℝ))) ^ 2)) + e := hb
        linarith
      · have h2 : s0 + W ≤ a := by omega
        have h' : (s0 : ℝ) + W ≤ a := by exact_mod_cast h2
        rw [if_pos h2, if_neg (by omega)]
        have hb := point_bound N hN (2 * Real.pi * (β - a / N)) ((a : ℝ) - c)
          (by linarith) (by linarith) (Or.inr (by rw [hβ]; field_simp; ring))
        have : ampSq N β a ≤
            K * (1 / (4 * ((a : ℝ) - c) ^ 2) + 1 / (4 * ((N : ℝ) - ((a : ℝ) - c)) ^ 2)) + e := hb
        linarith
  set SA := (range N).filter (fun a : ℕ => s0 + W ≤ a) with hSA
  set SB := (range N).filter (fun a : ℕ => a < s0) with hSB
  have s1 := sum_inv_sq_le SA (fun a : ℕ => (a : ℝ) - c) ((W : ℝ) - δ) (by linarith)
    (fun a ha => by
      rw [hSA, mem_filter] at ha
      have : (s0 : ℝ) + W ≤ a := by exact_mod_cast ha.2
      linarith)
    (fun a b => Or.inl (by ring))
  have s2 := sum_inv_sq_le SA (fun a : ℕ => (N : ℝ) - ((a : ℝ) - c)) (δ + 1) (by linarith)
    (fun a ha => by
      rw [hSA, mem_filter, mem_range] at ha
      have : (a : ℝ) + 1 ≤ N := by exact_mod_cast ha.1
      linarith)
    (fun a b => Or.inr (by ring))
  have s3 := sum_inv_sq_le SB (fun a : ℕ => c - (a : ℝ)) (δ + 1) (by linarith)
    (fun a ha => by
      rw [hSB, mem_filter] at ha
      have : (a : ℝ) + 1 ≤ s0 := by exact_mod_cast ha.2
      linarith)
    (fun a b => Or.inr (by ring))
  have s4 := sum_inv_sq_le SB (fun a : ℕ => (N : ℝ) - (c - (a : ℝ))) ((W : ℝ) - δ) (by linarith)
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
  have hce : ∀ m : ℝ, m ≤ N → m * e ≤ 1 / N := by
    intro m hm
    rw [he, mul_one_div, div_le_div_iff₀ (by positivity) hNR, one_mul, sq]
    exact mul_le_mul_of_nonneg_right hm hNR.le
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter, ← hSA, ← hSB, hsumA, hsumB]
  have hA1 := mul_le_mul_of_nonneg_left (add_le_add s1 s2) hK0
  have hB1 := mul_le_mul_of_nonneg_left (add_le_add s3 s4) hK0
  have hA2 := hce _ hcardA
  have hB2 := hce _ hcardB
  simp only at hA1 hB1
  have e1 : (W : ℝ) - δ - 1 = (W : ℝ) - 1 - δ := by ring
  have e2 : δ + 1 - 1 = δ := by ring
  rw [e1, e2] at hA1 hB1
  have hfin : K * (1 / (4 * ((W : ℝ) - 1 - δ)) + 1 / (4 * δ)) +
      K * (1 / (4 * δ) + 1 / (4 * ((W : ℝ) - 1 - δ))) =
      K / 2 * (1 / δ + 1 / ((W : ℝ) - 1 - δ)) := by
    have : 0 < δ := by linarith
    have : 0 < (W : ℝ) - 1 - δ := by linarith
    field_simp
    ring
  have h2N : 1 / (N : ℝ) + 1 / N = 2 / N := by ring
  linarith only [hA1, hB1, hA2, hB2, hfin, h2N]

end WindowMassProof

end ShorECDLP.Entrant
