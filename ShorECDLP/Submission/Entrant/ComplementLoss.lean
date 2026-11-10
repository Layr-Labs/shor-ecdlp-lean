import ShorECDLP.Submission.Entrant.Prefix

namespace ShorECDLP.Entrant.ComplementLoss
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem mass_upper (psi phi : State) (eps : ℝ) :
    eps*normSq (psi+phi) ≤ (eps+eps^2)*normSq psi + (1+eps)*normSq phi := by
  classical
  let S := psi.support ∪ phi.support
  have ha : (psi+phi).support ⊆ S := Finsupp.support_add
  rw [mass_on psi S Finset.subset_union_left,mass_on phi S Finset.subset_union_right,
    mass_on (psi+phi) S ha]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  simp only [Finsupp.add_apply,Complex.normSq_apply,Complex.add_re,Complex.add_im]
  nlinarith [sq_nonneg (eps*(psi s).re-(phi s).re),sq_nonneg (eps*(psi s).im-(phi s).im)]

theorem expectation_upper {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi phi : State)
    (accept : (Fin e → Bool) → Bool) (eps : ℝ) :
    eps*expectation read p history (psi+phi) accept ≤
    (eps+eps^2)*expectation read p history psi accept +
      (1+eps)*expectation read p history phi accept := by
  induction p generalizing psi phi with
  | done =>
    simp only [expectation]
    split_ifs
    · exact mass_upper psi phi eps
    · simp
  | gate g p ih =>
    simpa only [expectation,map_add] using ih history
      (Quantum.run (g.instantiate read) psi) (Quantum.run (g.instantiate read) phi) accept
  | recordGate i v g p ih =>
    simpa only [expectation,map_add] using ih history
      (Quantum.run (if history i=v then [g] else []) psi)
      (Quantum.run (if history i=v then [g] else []) phi) accept
  | measure w p ih =>
    have h0 := ih (Fin.lastCases false history) (xResetKraus w false psi) (xResetKraus w false phi) accept
    have h1 := ih (Fin.lastCases true history) (xResetKraus w true psi) (xResetKraus w true phi) accept
    simp only [expectation,map_add]
    linarith

theorem expectation_neg {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read p history (-psi) accept = expectation read p history psi accept := by
  induction p generalizing psi with
  | done => simp [expectation]
  | gate g p ih => simp only [expectation,map_neg,ih]
  | recordGate i v g p ih => simp only [expectation,map_neg,ih]
  | measure w p ih => simp only [expectation,map_neg,ih]

theorem expectation_compl {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed) :
    expectation read p history psi accept +
      expectation read p history psi (fun h => !accept h) = normSq psi := by
  induction p generalizing psi with
  | done => cases ha : accept history <;> simp [expectation,ha]
  | gate g p ih =>
    simp only [expectation]
    rw [ih _ _ accept hp.2]
    exact normSq_run _ (g.instantiate_wellFormed read hp.1) psi
  | recordGate i v g p ih =>
    simp only [expectation]
    rw [ih _ _ accept hp.2]
    apply normSq_run
    split_ifs
    · simpa [CircuitWellFormed] using hp.1
    · simp [CircuitWellFormed]
  | measure w p ih =>
    have h0 := ih (Fin.lastCases false history) (xResetKraus w false psi) accept hp
    have h1 := ih (Fin.lastCases true history) (xResetKraus w true psi) accept hp
    have hm := normSq_xResetKraus_false_add_true w psi
    simp only [expectation]
    linarith

theorem loss {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi phi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (delta : ℝ) (hd : 0 < delta) (hn : normSq phi = normSq psi)
    (he : normSq (phi-psi) ≤ delta^2*normSq psi) :
    expectation read p history phi accept ≤ expectation read p history psi accept + delta*normSq psi := by
  have hA := expectation_upper read p history psi (phi-psi) accept delta
  have hB := expectation_upper read p history phi (psi-phi) (fun h => !accept h) delta
  have hsumA : psi+(phi-psi)=phi := by abel
  have hsumB : phi+(psi-phi)=psi := by abel
  rw [hsumA] at hA
  rw [hsumB] at hB
  have hphi := expectation_compl read p history phi accept hp
  have hpsi := expectation_compl read p history psi accept hp
  rw [hn] at hphi
  have hdiff := expectation_compl read p history (phi-psi) accept hp
  have hneg : psi-phi = -(phi-psi) := by abel
  rw [hneg,expectation_neg] at hB
  have hscaled := mul_le_mul_of_nonneg_left he (show 0 ≤ 1+delta by positivity)
  have hprod : (delta*(2+delta)) * (expectation read p history phi accept - expectation read p history psi accept) ≤
      (delta*(2+delta)) * (delta*normSq psi) := by nlinarith
  have hpos : 0 < delta*(2+delta) := by positivity
  have hle := (mul_le_mul_iff_right₀ hpos).mp hprod
  linarith
theorem phase_loss {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (dir : PhaseDir) (k : Nat) (t : Wire) (delta : ℝ) (hd : 0 < delta)
    (ha : (phaseAngle dir k/2)^2 ≤ delta^2) :
    expectation read p history (applyGate (.P dir k t) psi) accept ≤
      expectation read p history psi accept + delta*normSq psi := by
  have hw : Complex.normSq (Complex.exp (Complex.I * ((-(phaseAngle dir k/2) : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  let phi := Complex.exp (Complex.I * ((-(phaseAngle dir k/2) : ℝ) : ℂ)) • applyGate (.P dir k t) psi
  have hphi : expectation read p history phi accept =
      expectation read p history (applyGate (.P dir k t) psi) accept := by
    simp only [phi, AndGadget.expectation_smul, hw, one_mul]
  have hn : normSq phi = normSq psi := by
    simp only [phi, centered_smul_mass, hw, one_mul]
    exact applyGate_preservesNormSq _ (by trivial) psi
  rw [← hphi]
  have hdiff : normSq (phi-psi) ≤ delta^2 * normSq psi :=
    (phase_centered_mass dir k t psi).trans
      (mul_le_mul_of_nonneg_right ha (mass_nonneg psi))
  exact loss read p history psi phi accept hp delta hd hn hdiff

theorem dropped_loss {n s e} (read : ConstantBit n → Bool) (p : Straight n s e)
    (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool)
    (hp : p.WellFormed) (g : Gate) (hg : largePhase 27 g = true) :
    expectation read p history (applyGate g psi) accept ≤
      expectation read p history psi accept + charge g*normSq psi := by
  cases g <;> simp only [largePhase, Bool.false_eq_true, decide_eq_true_eq] at hg
  case P dir k t =>
    have hd : 0 < (6283186/1000000:ℝ)/(2:ℝ)^(k+1) := by positivity
    have hangle : (phaseAngle dir k/2)^2 ≤ ((6283186/1000000:ℝ)/(2:ℝ)^(k+1))^2 := by
      have hpi := Real.pi_lt_d6
      have hb : 2*Real.pi/(2:ℝ)^k/2 ≤ (6283186/1000000:ℝ)/(2:ℝ)^(k+1) := by
        rw [pow_succ, div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have hz : 0 ≤ 2*Real.pi/(2:ℝ)^k/2 := by positivity
      cases dir <;> simp only [phaseAngle, neg_div, neg_sq] <;> nlinarith
    simpa only [charge, hg, if_true] using
      phase_loss read p history psi accept hp dir k t _ hd hangle

theorem dropped_loss27 {n s e} (read : ConstantBit n → Bool) (p : Straight n s e)
    (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool)
    (hp : p.WellFormed) (g : ShorECDLP.Gate) (hg : largePhase 26 g = true)
    (hg27 : largePhase 27 g = false) :
    expectation read p history (applyGate g psi) accept ≤
      expectation read p history psi accept + unit*normSq psi := by
  cases g <;> simp only [largePhase, Bool.false_eq_true] at hg hg27
  case P dir k t =>
    have h1 : 26 < k := by simpa using hg
    have h2 : ¬ 27 < k := by simpa using hg27
    have hk : k = 27 := by omega
    subst hk
    have hd : 0 < (6283186/1000000:ℝ)/(2)^28 := by positivity
    have hangle : (phaseAngle dir (27:Nat)/2)^2 ≤ ((6283186/1000000:ℝ)/(2)^28)^2 := by
      have hpi := Real.pi_lt_d6
      have hb : 2*Real.pi/(2:ℝ)^27/2 ≤ (6283186/1000000:ℝ)/(2)^28 := by
        rw [pow_succ, div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have hz : 0 ≤ 2*Real.pi/(2:ℝ)^27/2 := by positivity
      cases dir <;> simp only [phaseAngle, neg_div, neg_sq] <;> nlinarith
    have hunit : (6283186/1000000:ℝ)/(2)^28 = unit := rfl
    simpa only [hunit] using
      phase_loss read p history psi accept hp dir (27:Nat) t _ hd hangle

theorem trimN_expectation {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (N : Nat) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed) :
    expectation read p history psi accept ≤
      expectation read (trimN N p) history psi accept +
      (errorCost p + N*unit)*normSq psi := by
  induction p generalizing psi N with
  | done =>
    have hu : (0:ℝ) ≤ unit := by simp only [unit]; positivity
    have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hpsi : (0:ℝ) ≤ normSq psi := mass_nonneg psi
    have hprod : (0:ℝ) ≤ (↑N*unit)*normSq psi :=
      mul_nonneg (mul_nonneg hN hu) hpsi
    simp [trimN, errorCost, expectation]
    exact hprod
  | measure w p ih =>
    have h0 := ih N (Fin.lastCases false history) (xResetKraus w false psi) accept hp
    have h1 := ih N (Fin.lastCases true history) (xResetKraus w true psi) accept hp
    have hm := normSq_xResetKraus_false_add_true w psi
    have hme := congrArg (fun x : ℝ => (errorCost p + N*unit)*x) hm
    simp only [trimN, errorCost, expectation]
    nlinarith
  | recordGate i v g p ih =>
    by_cases h27 : largePhase 27 g = true
    · have hi := ih N history psi accept hp.2
      have hs := dropped_loss read p history psi accept hp.2 g h27
      simp only [trimN, h27, if_true, errorCost, expectation]
      by_cases hr : history i = v
      · simp only [hr, if_true, run_singleton]
        nlinarith
      · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
        have hsq : (0:ℝ) ≤ normSq psi := mass_nonneg psi
        have hu2 : (0:ℝ) ≤ unit := by simp only [unit]; positivity
        have hn := mul_nonneg (charge_nonneg g) (mass_nonneg psi)
        nlinarith
    · have h27f : largePhase 27 g = false := Bool.eq_false_iff.mpr h27
      by_cases hN : (decide (N > 0) && largePhase 26 g) = true
      · have hg26 : largePhase 26 g = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
          exact hN.2
        have hs := dropped_loss27 read p history psi accept hp.2 g hg26 h27f
        have hi := ih (N - 1) history psi accept hp.2
        have hc0 : charge g = 0 := charge_false g h27f
        have hNpos : 0 < N := by
          have h := hN
          simp at h
          exact h.1
        have hcast : ((N - 1 : Nat) : ℝ) = (N:ℝ) - 1 := Nat.cast_pred hNpos
        simp only [hcast] at hi
        simp only [trimN, h27f, Bool.false_eq_true, if_false, hN, if_true,
          errorCost, hc0, zero_add, expectation]
        by_cases hr : history i = v
        · simp only [hr, if_true, run_singleton]
          nlinarith
        · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
          have hsq : (0:ℝ) ≤ normSq psi := mass_nonneg psi
          have hu2 : (0:ℝ) ≤ unit := by simp only [unit]; positivity
          have hn := mul_nonneg (charge_nonneg g) (mass_nonneg psi)
          nlinarith
      · have hNf : (decide (N > 0) && largePhase 26 g) = false :=
          Bool.eq_false_iff.mpr hN
        have hi := ih N history (run (if history i=v then [g] else []) psi)
          accept hp.2
        have hc0 : charge g = 0 := charge_false g h27f
        have hn : normSq (run (if history i=v then [g] else []) psi) = normSq psi := by
          apply normSq_run
          split_ifs
          · simpa [ShorECDLP.CircuitWellFormed] using hp.1
          · simp [ShorECDLP.CircuitWellFormed]
        rw [hn] at hi
        simp only [trimN, h27f, if_false, hNf, if_false, errorCost, hc0,
          zero_add, expectation]
        exact hi
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases h27 : largePhase 27 g = true
      · have hs := dropped_loss read p history psi accept hp.2 g h27
        have hi := ih N history psi accept hp.2
        simp only [trimN, h27, if_true, errorCost, expectation,
          TemplateGate.instantiate, run_singleton]
        nlinarith
      · have h27f : largePhase 27 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 26 g) = true
        · have hg26 : largePhase 26 g = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
            exact hN.2
          have hs := dropped_loss27 read p history psi accept hp.2 g hg26 h27f
          have hi := ih (N - 1) history psi accept hp.2
          have hc0 : charge g = 0 := charge_false g h27f
          have hNpos : 0 < N := by
            have h := hN
            simp at h
            exact h.1
          have hcast : ((N - 1 : Nat) : ℝ) = (N:ℝ) - 1 := Nat.cast_pred hNpos
          simp only [hcast] at hi
          simp only [trimN, h27f, Bool.false_eq_true, if_false, hN, if_true,
            errorCost, hc0, zero_add, expectation, TemplateGate.instantiate,
            run_singleton]
          nlinarith
        · have hNf : (decide (N > 0) && largePhase 26 g) = false :=
            Bool.eq_false_iff.mpr hN
          have hi := ih N history (applyGate g psi) accept hp.2
          rw [normSq_gate g hp.1 psi] at hi
          have hc0 : charge g = 0 := charge_false g h27f
          simp only [trimN, h27f, if_false, hNf, if_false, errorCost, hc0,
            zero_add, expectation, TemplateGate.instantiate, run_singleton]
          exact hi
    | whenBit r v g =>
      by_cases h27 : largePhase 27 g = true
      · have hi := ih N history psi accept hp.2
        have hs := dropped_loss read p history psi accept hp.2 g h27
        simp only [trimN, h27, if_true, errorCost, expectation, TemplateGate.instantiate]
        by_cases hr : read r = v
        · simp only [hr, if_true, run_singleton]
          nlinarith
        · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
          have hsq : (0:ℝ) ≤ normSq psi := mass_nonneg psi
          have hu2 : (0:ℝ) ≤ unit := by simp only [unit]; positivity
          have hn := mul_nonneg (charge_nonneg g) (mass_nonneg psi)
          nlinarith
      · have h27f : largePhase 27 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 26 g) = true
        · have hg26 : largePhase 26 g = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
            exact hN.2
          have hs := dropped_loss27 read p history psi accept hp.2 g hg26 h27f
          have hi := ih (N - 1) history psi accept hp.2
          have hc0 : charge g = 0 := charge_false g h27f
          have hNpos : 0 < N := by
            have h := hN
            simp at h
            exact h.1
          have hcast : ((N - 1 : Nat) : ℝ) = (N:ℝ) - 1 := Nat.cast_pred hNpos
          simp only [hcast] at hi
          simp only [trimN, h27f, Bool.false_eq_true, if_false, hN, if_true,
            errorCost, hc0, zero_add, expectation, TemplateGate.instantiate]
          by_cases hr : read r = v
          · simp only [hr, if_true, run_singleton]
            nlinarith
          · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
            have hsq : (0:ℝ) ≤ normSq psi := mass_nonneg psi
            have hu2 : (0:ℝ) ≤ unit := by simp only [unit]; positivity
            have hn := mul_nonneg (charge_nonneg g) (mass_nonneg psi)
            nlinarith
        · have hNf : (decide (N > 0) && largePhase 26 g) = false :=
            Bool.eq_false_iff.mpr hN
          have hi := ih N history (run ((TemplateGate.whenBit r v g).instantiate read) psi)
            accept hp.2
          rw [normSq_template read (.whenBit r v g) hp.1 psi] at hi
          have hc0 : charge g = 0 := charge_false g h27f
          simp only [trimN, h27f, if_false, hNf, if_false, errorCost, hc0,
            zero_add, expectation]
          exact hi


#print axioms trimN_expectation
end
end ShorECDLP.Entrant.ComplementLoss
