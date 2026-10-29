import ShorECDLP.Submission.Naive.OrderFinding.Proofs.SuccessProbability

/-! EDITABLE. Single-trial success from rounding-window mass.

For every nonzero character `k`, the joint distribution of the two phase
registers is a product of two phase-estimation distributions.  If each
distribution puts mass at least `c` on the samples that round to the correct
numerator, the canonical postprocessing recovers the secret with probability
at least `((r - 1) / r) * c ^ 2`. -/

namespace ShorECDLP.Entrant
open ShorECDLP.Quantum ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

/-- A pair in the two correct rounding windows decodes to the secret. -/
theorem postprocess_of_windows {r t d : ℕ} (hr : Nat.Prime r)
    (k : Fin r) (hk : k.val ≠ 0) (a b : Fin (2 ^ t))
    (ha : nearestNumerator r t a.val = k.val)
    (hb : nearestNumerator r t b.val = (k.val * d) % r) :
    orderFindingPostprocess r t hr (a, b) = some (d : ZMod r) := by
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  have hk0 : ((k.val : ℕ) : ZMod r) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
  unfold orderFindingPostprocess
  simp only [ha, hb, ZMod.natCast_mod, Nat.cast_mul]
  rw [if_neg hk0]
  congr 1
  field_simp

theorem mod_mul_ne_zero {r d : ℕ} (hr : Nat.Prime r) (hd : d % r ≠ 0) (k : Fin r)
    (hk : k.val ≠ 0) : (k.val * d) % r ≠ 0 := by
  intro h
  have hdvd : r ∣ k.val * d := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h1 | h1
  · exact hk (Nat.eq_zero_of_dvd_of_lt h1 k.isLt)
  · exact hd (Nat.mod_eq_zero_of_dvd h1)

/-- Generic single-trial lower bound from a rounding-window mass bound. -/
theorem success_of_window_mass {G : Type*} [AddCommGroup G] {w r d t : ℕ}
    (enc : PointEncoding G w) (oracle : State →ₗ[ℂ] State) (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire) (anc : Wire) (s : BasisState)
    (hsetting : ECDLPSetting P Q r d)
    (hspec : ECDLPOracleSpec enc oracle P Q aReg bReg pointReg oracleWork)
    (hsetup : OrderFindingSetup enc aReg bReg pointReg oracleWork anc t s)
    (hd : d % r ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (hwin : ∀ n : ℕ, 0 < n → n < r →
      c ≤ ∑ a : Fin (2 ^ t),
        if nearestNumerator r t a.val = n then
          Complex.normSq (qpeAmplitude t ((n : ℝ) / (r : ℝ)) a.val) else 0) :
    ((r - 1 : ℝ) / r) * (c * c) ≤
      orderFindingSuccessProbability r t d hsetting.prime_order aReg bReg
        (orderFinding aReg bReg anc oracle (ket s)) := by
  classical
  have hr := hsetting.prime_order
  set ψ := orderFinding aReg bReg anc oracle (ket s) with hψ
  let A : Fin r → Fin (2 ^ t) → ℝ := fun k a =>
    Complex.normSq (qpeAmplitude t ((k.val : ℝ) / (r : ℝ)) a.val)
  let B : Fin r → Fin (2 ^ t) → ℝ := fun k b =>
    Complex.normSq (qpeAmplitude t ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) b.val)
  let good : Fin r → Fin (2 ^ t) → Fin (2 ^ t) → Prop := fun k a b =>
    k.val ≠ 0 ∧ nearestNumerator r t a.val = k.val ∧
      nearestNumerator r t b.val = (k.val * d) % r
  let F : Fin r → Fin (2 ^ t) → Fin (2 ^ t) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  have hA : ∀ k a, 0 ≤ A k a := fun _ _ => Complex.normSq_nonneg _
  have hB : ∀ k b, 0 ≤ B k b := fun _ _ => Complex.normSq_nonneg _
  have hF : ∀ k a b, 0 ≤ F k a b := by
    intro k a b
    dsimp only [F]
    split_ifs
    · exact mul_nonneg (hA k a) (hB k b)
    · exact le_rfl
  have hrinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  have hjp : ∀ a b : Fin (2 ^ t),
      jointRegisterProbability aReg bReg a.val b.val ψ =
        (r : ℝ)⁻¹ * ∑ k : Fin r, A k a * B k b := by
    intro a b
    have h := jointRegisterProbability_orderFinding_eq_character_average
      enc oracle P Q aReg bReg pointReg oracleWork anc s hsetting hspec hsetup a b
    simpa only [characterWeight] using h
  -- Step 1: restrict every character to its own pair of rounding windows.
  have step1 :
      ∑ a : Fin (2 ^ t), ∑ b : Fin (2 ^ t), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        orderFindingSuccessProbability r t d hr aReg bReg ψ := by
    unfold orderFindingSuccessProbability
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    by_cases hp : orderFindingPostprocess r t hr (a, b) = some (d : ZMod r)
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
        exact hp (postprocess_of_windows hr k hk a b ha hb)
      simp [hz]
  -- Step 2: exchange the order of summation.
  have step2 :
      ∑ k : Fin r, (r : ℝ)⁻¹ * ∑ a : Fin (2 ^ t), ∑ b : Fin (2 ^ t), F k a b =
        ∑ a : Fin (2 ^ t), ∑ b : Fin (2 ^ t), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  -- Step 3: each nonzero character contributes at least `c * c / r`.
  have step3 : ∀ k : Fin r,
      (if k.val = 0 then 0 else (r : ℝ)⁻¹ * (c * c)) ≤
        (r : ℝ)⁻¹ * ∑ a : Fin (2 ^ t), ∑ b : Fin (2 ^ t), F k a b := by
    intro k
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      apply mul_nonneg hrinv
      exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF k a b))
    · rw [if_neg hk]
      apply mul_le_mul_of_nonneg_left _ hrinv
      have hprod :
          ∑ a : Fin (2 ^ t), ∑ b : Fin (2 ^ t), F k a b =
            (∑ a : Fin (2 ^ t),
                if nearestNumerator r t a.val = k.val then A k a else 0) *
              (∑ b : Fin (2 ^ t),
                if nearestNumerator r t b.val = (k.val * d) % r then B k b else 0) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F, good]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [hprod]
      have hka := hwin k.val (Nat.pos_of_ne_zero hk) k.isLt
      have hkb := hwin ((k.val * d) % r)
        (Nat.pos_of_ne_zero (mod_mul_ne_zero hr hd k hk)) (Nat.mod_lt _ hr.pos)
      exact mul_le_mul hka hkb hc (le_trans hc hka)
  calc
    ((r - 1 : ℝ) / r) * (c * c) =
        ∑ k : Fin r, (if k.val = 0 then 0 else (r : ℝ)⁻¹ * (c * c)) :=
      (nonzero_character_baseline_sum hr (c * c)).symm
    _ ≤ ∑ k : Fin r, (r : ℝ)⁻¹ * ∑ a : Fin (2 ^ t), ∑ b : Fin (2 ^ t), F k a b :=
      Finset.sum_le_sum (fun k _ => step3 k)
    _ = ∑ a : Fin (2 ^ t), ∑ b : Fin (2 ^ t), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := step2
    _ ≤ orderFindingSuccessProbability r t d hr aReg bReg ψ := step1

end
end ShorECDLP.Entrant
