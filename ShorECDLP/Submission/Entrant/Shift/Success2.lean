import ShorECDLP.Submission.Entrant.Shift.Probability
import ShorECDLP.Submission.Entrant.Shift.Phase
import ShorECDLP.Submission.Entrant.Shift.Average
import ShorECDLP.Submission.Entrant.Success
import ShorECDLP.Submission.Naive.Challenge.Probability

/-! EDITABLE. Single-trial success of the `wrappedShift` readout with a narrow right register.

The left register (`pa` qubits) is rounded to the nearest numerator `k`; the right register
(`R + e` qubits, half-bin shifted by `halfShift`) is read through its top `R` bits and decoded
with the protected `wrappedNumerators` interval.  Because `k ↦ k d mod r` permutes the nonzero
residues, the right-register failure is the average failure over all numerators, which
`shift_average` bounds. -/

namespace ShorECDLP.Entrant
open Quantum Secp256k1 Challenge NaiveChallenge
open ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

private theorem regValue_bound2 (ws : List Wire) (s : BasisState) :
    regValue ws s < 2 ^ ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      rw [regValue_cons, List.length_cons, Nat.pow_succ]
      by_cases h : s w <;> simp [h] <;> omega

theorem jointProbability_event2 (aReg bReg : List Wire) (pa pb : Nat)
    (ha : aReg.length = pa) (hb : bReg.length = pb)
    (event : Nat → Nat → Bool) (ψ : State) :
    (∑ a : Fin (2^pa), ∑ b : Fin (2^pb),
      if event a.val b.val then
        Quantum.OrderFinding.jointRegisterProbability aReg bReg a.val b.val ψ else 0) =
      basisMass (fun s => event (regValue aReg s) (regValue bReg s)) ψ := by
  classical
  unfold Quantum.OrderFinding.jointRegisterProbability basisMass Finsupp.sum
  have hexpand (a : Fin (2^pa)) (b : Fin (2^pb)) :
      (if event a.val b.val then
        ∑ s ∈ ψ.support, if regValue aReg s = a.val ∧ regValue bReg s = b.val
          then Complex.normSq (ψ s) else 0 else 0) =
      ∑ s ∈ ψ.support, if regValue aReg s = a.val ∧ regValue bReg s = b.val
        then (if event a.val b.val then Complex.normSq (ψ s) else 0) else 0 := by
    cases event a.val b.val <;> simp
  simp_rw [hexpand]
  calc
    _ = ∑ a : Fin (2^pa), ∑ s ∈ ψ.support, ∑ b : Fin (2^pb),
      if regValue aReg s = a.val ∧ regValue bReg s = b.val
        then (if event a.val b.val then Complex.normSq (ψ s) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ s ∈ ψ.support, ∑ a : Fin (2^pa), ∑ b : Fin (2^pb),
      if regValue aReg s = a.val ∧ regValue bReg s = b.val
        then (if event a.val b.val then Complex.normSq (ψ s) else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      let a : Fin (2^pa) := ⟨regValue aReg s, by simpa [ha] using regValue_bound2 aReg s⟩
      let b : Fin (2^pb) := ⟨regValue bReg s, by simpa [hb] using regValue_bound2 bReg s⟩
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp [a, b]
        · intro b' _ hne
          have hbval : regValue bReg s ≠ b'.val := by
            intro h
            exact hne (Fin.ext h.symm)
          simp [hbval]
        · simp
      · intro a' _ hne
        have haval : regValue aReg s ≠ a'.val := by
          intro h
          exact hne (Fin.ext h.symm)
        simp [haval]
      · simp

theorem zObserve_eventProbability2 (aReg bReg : List Wire) (pa pb : Nat)
    (ha : aReg.length = pa) (hb : bReg.length = pb)
    (event : Nat → Nat → Bool) (ψ : State) :
    recordMass (zObserve (aReg ++ bReg)).run (pairEvent aReg.length event) ψ =
    ∑ a : Fin (2^pa), ∑ b : Fin (2^pb),
      if event a.val b.val then
        Quantum.OrderFinding.jointRegisterProbability aReg bReg a.val b.val ψ else 0 := by
  rw [recordMass_zObserve, jointProbability_event2 aReg bReg pa pb ha hb]
  simp [pairEvent, bitsValue_map]

/-- `k ↦ k d mod r` permutes the nonzero residues. -/
theorem sum_mul_mod_perm (r d : ℕ) (hr : r.Prime) (hd : d % r ≠ 0) (f : ℕ → ℝ) :
    ∑ k : Fin r, (if k.val = 0 then 0 else f ((k.val * d) % r)) =
      ∑ l ∈ Finset.Ico 1 r, f l := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then 0 else f ((k * d) % r)) r,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hr.pos, if_pos rfl, zero_add]
  have hcongr : ∑ k ∈ Finset.Ico (0 + 1) r, (if k = 0 then 0 else f ((k * d) % r)) =
      ∑ k ∈ Finset.Ico 1 r, f ((k * d) % r) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [if_neg (by omega)]
  rw [hcongr]
  have hcop : Nat.gcd r d = 1 :=
    (Nat.Prime.coprime_iff_not_dvd hr).mpr (fun h => hd (Nat.mod_eq_zero_of_dvd h))
  have hinj : Set.InjOn (fun k => (k * d) % r) (Finset.Ico 1 r : Set ℕ) := by
    intro k hk k' hk' heq
    simp only [Finset.coe_Ico, Set.mem_Ico] at hk hk'
    have h1 : k * d ≡ k' * d [MOD r] := heq
    have h2 := Nat.ModEq.cancel_right_of_coprime hcop h1
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hk.2, Nat.mod_eq_of_lt hk'.2] at h2
  have hsub : (Finset.Ico 1 r).image (fun k => (k * d) % r) ⊆ Finset.Ico 1 r := by
    intro l hl
    rw [Finset.mem_image] at hl
    obtain ⟨k, hk, rfl⟩ := hl
    rw [Finset.mem_Ico] at hk ⊢
    exact ⟨Nat.pos_of_ne_zero (mod_mul_ne_zero hr hd ⟨k, hk.2⟩ (by simp; omega)),
      Nat.mod_lt _ hr.pos⟩
  have himg : (Finset.Ico 1 r).image (fun k => (k * d) % r) = Finset.Ico 1 r :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  rw [← Finset.sum_image (f := f) hinj, himg]

theorem normSq_qpe_eq_ampSq (M : ℕ) (φ : ℝ) (b : ℕ) :
    Complex.normSq (qpeAmplitude M φ b) = WindowMassProof.ampSq (2 ^ M) φ b := by
  simp only [qpeAmplitude, WindowMassProof.ampSq, eigenvalue]

set_option maxHeartbeats 1000000 in
/-- Single-trial success for the shifted narrow right register. -/
theorem shift_success {G' : Type*} [AddCommGroup G'] {w d pa R e pb : ℕ} (hpb : R + e = pb)
    (enc : PointEncoding G' w) (oracle : State →ₗ[ℂ] State) (P Q : G')
    (aReg bReg pointReg oracleWork : List Wire) (anc : Wire) (s : BasisState)
    (params : DecoderParams) (hpl : params.leftBits = pa) (hpr : params.rightBits = R)
    (hsetting : ECDLPSetting P Q order d)
    (hspec : ECDLPOracleSpec enc oracle P Q aReg bReg pointReg oracleWork)
    (hsetup : Quantum.OrderFinding.Two.Setup2 enc aReg bReg pointReg oracleWork anc pa pb s)
    (hd : d % order ≠ 0) (he : 2 ≤ e) (c : ℝ) (hc : 0 ≤ c)
    (hwin : ∀ n : ℕ, 0 < n → n < order →
      c ≤ ∑ a : Fin (2 ^ pa),
        if Challenge.nearestNumerator order pa a.val = n then
          Complex.normSq (qpeAmplitude pa ((n : ℝ) / (order : ℝ)) a.val) else 0) :
    c * (((order : ℝ) - 1) - (((order : ℝ) - 1) / 2 ^ e + 1) *
        (3 + 406 / 1000 * (1 + e * 0.6931471808) + 2 ^ e * (2 / 2 ^ (R + e)))) / order ≤
      ∑ a : Fin (2 ^ pa), ∑ b : Fin (2 ^ pb),
        if (d : ZMod order) ∈ fixedCandidates params a.val (b.val / 2 ^ e) then
          jointRegisterProbability aReg bReg a.val b.val
            (Quantum.OrderFinding.Two.orderFindingShift aReg bReg anc
              (Quantum.OrderFinding.Two.halfShift bReg (R + 1)) oracle (ket s))
        else 0 := by
  classical
  subst hpb
  haveI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have hr := hsetting.prime_order
  have hr2 : order ≠ 2 := by norm_num [order]
  set r := order with hrdef
  set ψ := Quantum.OrderFinding.Two.orderFindingShift aReg bReg anc
    (Quantum.OrderFinding.Two.halfShift bReg (R + 1)) oracle (ket s) with hψ
  have hbNodup : bReg.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp
      (List.nodup_append.mp hspec.registers_nodup).1).1).2.1
  have hshift := Quantum.OrderFinding.Two.halfShift_spec bReg (R + 1) (R + e) hbNodup
    hsetup.b_width
  let A : Fin r → Fin (2 ^ pa) → ℝ := fun k a =>
    Complex.normSq (qpeAmplitude pa ((k.val : ℝ) / (r : ℝ)) a.val)
  let B : Fin r → Fin (2 ^ (R + e)) → ℝ := fun k b =>
    Complex.normSq (qpeAmplitude (R + e)
      ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ) + 1 / 2 ^ (R + 1)) b.val)
  let good : Fin r → Fin (2 ^ pa) → Fin (2 ^ (R + e)) → Prop := fun k a b =>
    k.val ≠ 0 ∧ Challenge.nearestNumerator r pa a.val = k.val ∧
      (k.val * d) % r ∈ Challenge.wrappedNumerators r R (b.val / 2 ^ e)
  let F : Fin r → Fin (2 ^ pa) → Fin (2 ^ (R + e)) → ℝ := fun k a b =>
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
  have hjp : ∀ (a : Fin (2 ^ pa)) (b : Fin (2 ^ (R + e))),
      jointRegisterProbability aReg bReg a.val b.val ψ = (r : ℝ)⁻¹ * ∑ k : Fin r, A k a * B k b := by
    intro a b
    have h := Quantum.OrderFinding.Two.jointRegisterProbability_orderFinding_eq_character_average2
      enc oracle P Q aReg bReg pointReg oracleWork anc s _ hshift hsetting hspec hsetup a b
    simpa only [Quantum.OrderFinding.Two.characterWeight2] using h
  have hgood : ∀ k a b, good k a b →
      (d : ZMod r) ∈ fixedCandidates params a.val (b.val / 2 ^ e) := by
    rintro k a b ⟨hk, ha, hb⟩
    unfold fixedCandidates
    rw [hpl, hpr, Finset.mem_image]
    refine ⟨(k.val * d) % r, hb, ?_⟩
    rw [ha]
    have hk0 : ((k.val : ℕ) : ZMod r) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
    rw [ZMod.natCast_mod, Nat.cast_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
  -- Step 1: restrict to good triples.
  have step1 :
      ∑ a : Fin (2 ^ pa), ∑ b : Fin (2 ^ (R + e)), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2 ^ pa), ∑ b : Fin (2 ^ (R + e)),
          if (d : ZMod r) ∈ fixedCandidates params a.val (b.val / 2 ^ e) then
            jointRegisterProbability aReg bReg a.val b.val ψ else 0 := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    by_cases hp : (d : ZMod r) ∈ fixedCandidates params a.val (b.val / 2 ^ e)
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
        intro hg
        exact hp (hgood k a b hg)
      simp [hz]
  -- Step 2: exchange the order of summation.
  have step2 :
      ∑ k : Fin r, (r : ℝ)⁻¹ * ∑ a : Fin (2 ^ pa), ∑ b : Fin (2 ^ (R + e)), F k a b =
        ∑ a : Fin (2 ^ pa), ∑ b : Fin (2 ^ (R + e)), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  -- the right-register mass of numerator `l`
  let β : ℕ → ℝ := fun l => ∑ b ∈ Finset.range (2 ^ (R + e)),
    (if l ∈ Challenge.wrappedNumerators r R (b / 2 ^ e) then
      WindowMassProof.ampSq (2 ^ (R + e)) (WindowMassProof.shiftPhase r R l) b else 0)
  -- Step 3: each nonzero character contributes at least `c β(l_k) / r`.
  have step3 : ∀ k : Fin r,
      (if k.val = 0 then 0 else (r : ℝ)⁻¹ * (c * β ((k.val * d) % r))) ≤
        (r : ℝ)⁻¹ * ∑ a : Fin (2 ^ pa), ∑ b : Fin (2 ^ (R + e)), F k a b := by
    intro k
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      apply mul_nonneg hrinv
      exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF k a b))
    · rw [if_neg hk]
      apply mul_le_mul_of_nonneg_left _ hrinv
      have hprod :
          ∑ a : Fin (2 ^ pa), ∑ b : Fin (2 ^ (R + e)), F k a b =
            (∑ a : Fin (2 ^ pa),
                if Challenge.nearestNumerator r pa a.val = k.val then A k a else 0) *
              (∑ b : Fin (2 ^ (R + e)),
                if (k.val * d) % r ∈ Challenge.wrappedNumerators r R (b.val / 2 ^ e)
                then B k b else 0) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F, good]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      have hβ : (∑ b : Fin (2 ^ (R + e)),
          if (k.val * d) % r ∈ Challenge.wrappedNumerators r R (b.val / 2 ^ e)
          then B k b else 0) = β ((k.val * d) % r) := by
        dsimp only [β, B]
        rw [Fin.sum_univ_eq_sum_range (fun b => if (k.val * d) % r ∈
          Challenge.wrappedNumerators r R (b / 2 ^ e) then Complex.normSq (qpeAmplitude (R + e)
            ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ) + 1 / 2 ^ (R + 1)) b) else 0)]
        apply Finset.sum_congr rfl
        intro b _
        rw [normSq_qpe_eq_ampSq]
        rfl
      rw [hprod, hβ]
      have hka := hwin k.val (Nat.pos_of_ne_zero hk) k.isLt
      have hβ0 : 0 ≤ β ((k.val * d) % r) := by
        apply Finset.sum_nonneg
        intro b _
        split_ifs
        · exact WindowMassProof.ampSq_nonneg _ _ _
        · exact le_rfl
      exact mul_le_mul_of_nonneg_right hka hβ0
  have havg := WindowMassProof.shift_average r R e hr hr2 he
  have hperm := sum_mul_mod_perm r d hr hd (fun l => (r : ℝ)⁻¹ * (c * β l))
  have hfac : ∑ l ∈ Finset.Ico 1 r, (r : ℝ)⁻¹ * (c * β l) =
      (r : ℝ)⁻¹ * c * ∑ l ∈ Finset.Ico 1 r, β l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc
    c * (((r : ℝ) - 1) - (((r : ℝ) - 1) / 2 ^ e + 1) *
        (3 + 406 / 1000 * (1 + e * 0.6931471808) + 2 ^ e * (2 / 2 ^ (R + e)))) / r
        ≤ (r : ℝ)⁻¹ * c * ∑ l ∈ Finset.Ico 1 r, β l := by
          rw [div_eq_inv_mul, ← mul_assoc, mul_comm (r : ℝ)⁻¹ c, mul_assoc, mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hc
          apply mul_le_mul_of_nonneg_left _ hrinv
          exact havg
    _ = ∑ k : Fin r, (if k.val = 0 then 0 else (r : ℝ)⁻¹ * (c * β ((k.val * d) % r))) := by
          rw [hperm, hfac]
    _ ≤ ∑ k : Fin r, (r : ℝ)⁻¹ * ∑ a : Fin (2 ^ pa), ∑ b : Fin (2 ^ (R + e)), F k a b :=
          Finset.sum_le_sum (fun k _ => step3 k)
    _ = _ := step2
    _ ≤ _ := step1

end
end ShorECDLP.Entrant
