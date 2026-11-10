import ShorECDLP.Submission.Entrant.Phase23Partial
namespace ShorECDLP.Entrant.SqrtLoss
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28 ComplementLoss AffineLoss
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem young_square (F E D : ℝ) (hE : 0≤E) (hD : 0≤D)
    (h : ∀eps : ℝ,0<eps→F≤(1+eps)*E+(1+eps⁻¹)*D) :
    F≤(Real.sqrt E+Real.sqrt D)^2 := by
  by_cases he0 : E=0
  · simp only [he0,Real.sqrt_zero,zero_add,Real.sq_sqrt hD]
    by_cases hd0 : D=0
    · have hu:=h 1 (by norm_num)
      simp only [he0,hd0,mul_zero,add_zero] at hu
      simpa only [hd0] using hu
    · have hd : 0<D := lt_of_le_of_ne hD (Ne.symm hd0)
      by_contra hf
      have hg : 0<F-D := by linarith
      have hu:=h (2*D/(F-D)) (div_pos (mul_pos (by norm_num) hd) hg)
      have hi : (1+(2*D/(F-D))⁻¹)*D=D+(F-D)/2 := by
        field_simp
      simp only [he0,mul_zero,zero_add] at hu
      rw [hi] at hu
      linarith
  · have he : 0<E := lt_of_le_of_ne hE (Ne.symm he0)
    by_cases hd0 : D=0
    · simp only [hd0,Real.sqrt_zero,add_zero,Real.sq_sqrt hE]
      by_contra hf
      have hg : 0<F-E := by linarith
      have hu:=h ((F-E)/(2*E)) (div_pos hg (mul_pos (by norm_num) he))
      have hi : (1+(F-E)/(2*E))*E=E+(F-E)/2 := by field_simp
      simp only [hd0,mul_zero,add_zero] at hu
      rw [hi] at hu
      linarith
    · have hd : 0<D := lt_of_le_of_ne hD (Ne.symm hd0)
      let se:=Real.sqrt E
      let sd:=Real.sqrt D
      have hse : 0<se := Real.sqrt_pos.mpr he
      have hsd : 0<sd := Real.sqrt_pos.mpr hd
      have hse2 : se^2=E := Real.sq_sqrt hE
      have hsd2 : sd^2=D := Real.sq_sqrt hD
      have hu:=h (sd/se) (div_pos hsd hse)
      have hi : (1+sd/se)*E+(1+(sd/se)⁻¹)*D=(se+sd)^2 := by
        rw [←hse2,←hsd2]
        field_simp
        ring
      rw [hi] at hu
      exact hu


theorem expectation_sqrt_lipschitz {n s e} (read : ConstantBit n→Bool)
    (p : Straight n s e) (history : Fin s→Bool) (psi phi : State)
    (accept : (Fin e→Bool)→Bool) (hp : p.WellFormed) :
    Real.sqrt (expectation read p history phi accept)≤
      Real.sqrt (expectation read p history psi accept)+Real.sqrt (normSq (phi-psi)) := by
  have hy : ∀eps : ℝ,0<eps→expectation read p history phi accept≤
      (1+eps)*expectation read p history psi accept+(1+eps⁻¹)*normSq (phi-psi) := by
    intro eps heps
    have hu:=expectation_upper read p history psi (phi-psi) accept eps
    have hs : psi+(phi-psi)=phi := by abel
    rw [hs] at hu
    have hd:=expectation_le_mass read p history (phi-psi) accept hp
    have hm:=mul_le_mul_of_nonneg_left hd (show 0≤1+eps by linarith)
    have hh : eps*expectation read p history phi accept≤
        (eps+eps^2)*expectation read p history psi accept+(1+eps)*normSq (phi-psi) := by linarith
    apply (mul_le_mul_iff_right₀ heps).mp
    have heq : eps*((1+eps)*expectation read p history psi accept+(1+eps⁻¹)*normSq (phi-psi))=
        (eps+eps^2)*expectation read p history psi accept+(1+eps)*normSq (phi-psi) := by
      field_simp
      ring
    rw [heq]
    exact hh
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  exact young_square _ _ _ (AffineLoss.expectation_nonneg _ _ _ _ _) (mass_nonneg _) hy

theorem phase_sqrt_lipschitz {n s e} (read : ConstantBit n→Bool)
    (p : Straight n s e) (history : Fin s→Bool) (psi : State)
    (accept : (Fin e→Bool)→Bool) (hp : p.WellFormed)
    (dir : PhaseDir) (k : Nat) (t : Wire) (delta : ℝ) (hd : 0≤delta)
    (ha : (phaseAngle dir k/2)^2≤delta^2) :
    Real.sqrt (expectation read p history psi accept)≤
      Real.sqrt (expectation read p history (applyGate (.P dir k t) psi) accept)+delta*Real.sqrt (normSq psi) := by
  have hw : Complex.normSq (Complex.exp (Complex.I*((-(phaseAngle dir k/2):ℝ):ℂ)))=1 := by
    rw [Complex.normSq_eq_norm_sq,Complex.norm_exp]
    simp
  let phi:=Complex.exp (Complex.I*((-(phaseAngle dir k/2):ℝ):ℂ)) • applyGate (.P dir k t) psi
  have hphi : expectation read p history phi accept=
      expectation read p history (applyGate (.P dir k t) psi) accept := by
    simp only [phi,AndGadget.expectation_smul,hw,one_mul]
  have hdiff : normSq (psi-phi)≤delta^2*normSq psi := by
    have hn : psi-phi=-(phi-psi) := by abel
    rw [hn,normSq_neg]
    exact (phase_centered_mass dir k t psi).trans
      (mul_le_mul_of_nonneg_right ha (mass_nonneg psi))
  have hs : Real.sqrt (normSq (psi-phi))≤delta*Real.sqrt (normSq psi) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hd (Real.sqrt_nonneg _),?_⟩
    simpa only [mul_pow,Real.sq_sqrt (mass_nonneg psi)] using hdiff
  have h:=expectation_sqrt_lipschitz read p history phi psi accept hp
  rw [hphi] at h
  linarith

end
end ShorECDLP.Entrant.SqrtLoss

namespace ShorECDLP.Entrant.SqrtLoss
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28 ComplementLoss AffineLoss
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem sqrt_cauchy (E0 E1 M0 M1 : ℝ) (hE0 : 0≤E0) (hE1 : 0≤E1) (hM0 : 0≤M0) (hM1 : 0≤M1) :
    Real.sqrt E0*Real.sqrt M0+Real.sqrt E1*Real.sqrt M1≤
      Real.sqrt (E0+E1)*Real.sqrt (M0+M1) := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    _≤((Real.sqrt E0)^2+(Real.sqrt E1)^2)*((Real.sqrt M0)^2+(Real.sqrt M1)^2) := by
      nlinarith [sq_nonneg (Real.sqrt E0*Real.sqrt M1-Real.sqrt E1*Real.sqrt M0)]
    _=(E0+E1)*(M0+M1) := by rw [Real.sq_sqrt hE0,Real.sq_sqrt hE1,Real.sq_sqrt hM0,Real.sq_sqrt hM1]
    _=(Real.sqrt (E0+E1)*Real.sqrt (M0+M1))^2 := by
      rw [mul_pow,Real.sq_sqrt (add_nonneg hE0 hE1),Real.sq_sqrt (add_nonneg hM0 hM1)]

theorem sqrt_pair (F0 F1 E0 E1 M0 M1 C : ℝ)
    (hE0 : 0≤E0) (hE1 : 0≤E1) (hM0 : 0≤M0) (hM1 : 0≤M1) (hC : 0≤C)
    (h0 : Real.sqrt F0≤Real.sqrt E0+C*Real.sqrt M0)
    (h1 : Real.sqrt F1≤Real.sqrt E1+C*Real.sqrt M1) :
    Real.sqrt (F0+F1)≤Real.sqrt (E0+E1)+C*Real.sqrt (M0+M1) := by
  have hF0 := (Real.sqrt_le_iff.mp h0).2
  have hF1 := (Real.sqrt_le_iff.mp h1).2
  have hCS := sqrt_cauchy E0 E1 M0 M1 hE0 hE1 hM0 hM1
  have hc:=mul_le_mul_of_nonneg_left hCS (show 0≤2*C by positivity)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  calc
    _≤(Real.sqrt E0+C*Real.sqrt M0)^2+(Real.sqrt E1+C*Real.sqrt M1)^2 := add_le_add hF0 hF1
    _=(E0+E1)+2*C*(Real.sqrt E0*Real.sqrt M0+Real.sqrt E1*Real.sqrt M1)+C^2*(M0+M1) := by
      simp only [add_sq,mul_pow,Real.sq_sqrt hE0,Real.sq_sqrt hE1,Real.sq_sqrt hM0,Real.sq_sqrt hM1]
      ring
    _≤(E0+E1)+2*C*(Real.sqrt (E0+E1)*Real.sqrt (M0+M1))+C^2*(M0+M1) := by linarith
    _=(Real.sqrt (E0+E1)+C*Real.sqrt (M0+M1))^2 := by
      simp only [add_sq,mul_pow,Real.sq_sqrt (add_nonneg hE0 hE1),Real.sq_sqrt (add_nonneg hM0 hM1)]
      ring

end
end ShorECDLP.Entrant.SqrtLoss

namespace ShorECDLP.Entrant.SqrtLoss
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28 ComplementLoss AffineLoss Phase23Partial
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem dropped_sqrt {n s e} (read : ConstantBit n→Bool)
    (p : Straight n s e) (history : Fin s→Bool) (psi : State)
    (accept : (Fin e→Bool)→Bool) (hp : p.WellFormed)
    (g : Gate) (hg : largePhase 19 g=true) :
    Real.sqrt (expectation read p history psi accept)≤
      Real.sqrt (expectation read p history (applyGate g psi) accept)+charge23 g*Real.sqrt (normSq psi) := by
  cases g <;> simp only [largePhase,Bool.false_eq_true,decide_eq_true_eq] at hg
  case P dir k t =>
    have hd : 0≤(6283186/1000000:ℝ)/2^(k+1) := by positivity
    have ha : (phaseAngle dir k/2)^2≤((6283186/1000000:ℝ)/2^(k+1))^2 := by
      have hpi:=Real.pi_lt_d6
      have hb : 2*Real.pi/(2:ℝ)^k/2≤(6283186/1000000:ℝ)/(2:ℝ)^(k+1) := by
        rw [pow_succ,div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have hz : 0≤2*Real.pi/(2:ℝ)^k/2 := by positivity
      cases dir <;> simp only [phaseAngle,neg_div,neg_sq] <;> nlinarith
    simpa only [charge23,hg,if_true] using phase_sqrt_lipschitz read p history psi accept hp dir k t _ hd ha

theorem band_sqrt {n s e} (read : ConstantBit n→Bool)
    (p : Straight n s e) (history : Fin s→Bool) (psi : State)
    (accept : (Fin e→Bool)→Bool) (hp : p.WellFormed)
    (g : Gate) (hg : largePhase 18 g=true) (hf : largePhase 19 g=false) :
    Real.sqrt (expectation read p history psi accept)≤
      Real.sqrt (expectation read p history (applyGate g psi) accept)+unit23*Real.sqrt (normSq psi) := by
  cases g <;> simp only [largePhase,Bool.false_eq_true,decide_eq_true_eq] at hg hf
  case P dir k t =>
    have hk : k=19 := by
      have h1 : 18<k := by simpa using hg
      have h2 : ¬19<k := by simpa using hf
      omega
    subst k
    have ha : (phaseAngle dir 19/2)^2≤unit23^2 := by
      have hpi:=Real.pi_lt_d6
      have hb : 2*Real.pi/(2:ℝ)^19/2≤unit23 := by norm_num [unit23];linarith
      have hz : 0≤2*Real.pi/(2:ℝ)^19/2 := by positivity
      cases dir <;> simp only [phaseAngle,neg_div,neg_sq] <;> nlinarith
    exact phase_sqrt_lipschitz read p history psi accept hp dir 19 t unit23 unit23_pos.le ha

end
end ShorECDLP.Entrant.SqrtLoss

namespace ShorECDLP.Entrant.SqrtLoss
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28 ComplementLoss AffineLoss Phase23Partial
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem compose_sqrt (F E G M C D : ℝ)
    (h1 : Real.sqrt F≤Real.sqrt E+C*Real.sqrt M)
    (h2 : Real.sqrt E≤Real.sqrt G+D*Real.sqrt M) :
    Real.sqrt F≤Real.sqrt G+(D+C)*Real.sqrt M := by nlinarith

theorem conditional_sqrt {n s e} (read : ConstantBit n→Bool)
    (p : Straight n s e) (history : Fin s→Bool) (psi : State) (accept : (Fin e→Bool)→Bool)
    (g : Gate) (P : Prop) [Decidable P] (F C D : ℝ) (hd : 0≤D)
    (h1 : Real.sqrt F≤Real.sqrt (expectation read p history psi accept)+C*Real.sqrt (normSq psi))
    (h2 : Real.sqrt (expectation read p history psi accept)≤
      Real.sqrt (expectation read p history (applyGate g psi) accept)+D*Real.sqrt (normSq psi)) :
    Real.sqrt F≤Real.sqrt (expectation read p history (Quantum.run (if P then [g] else []) psi) accept)+
      (D+C)*Real.sqrt (normSq psi) := by
  by_cases hP : P
  · simpa only [hP,if_true,run_singleton] using compose_sqrt _ _ _ _ _ _ h1 h2
  · simp only [hP,if_false,run_nil,LinearMap.id_coe,id_eq]
    have hn:=mul_nonneg hd (Real.sqrt_nonneg (normSq psi))
    nlinarith

theorem trimN_sqrt {n s e} (read : ConstantBit n→Bool)
    (p : Straight n s e) (N : Nat) (history : Fin s→Bool) (psi : State)
    (accept : (Fin e→Bool)→Bool) (hp : p.WellFormed) :
    Real.sqrt (expectation read (Phase23Partial.trimN N p) history psi accept)≤
      Real.sqrt (expectation read p history psi accept)+activeCost N p*Real.sqrt (normSq psi) := by
  induction p generalizing N psi with
  | done => simp [Phase23Partial.trimN,activeCost,expectation]
  | measure w p ih =>
    have h0:=ih N (Fin.lastCases false history) (xResetKraus w false psi) accept hp
    have h1:=ih N (Fin.lastCases true history) (xResetKraus w true psi) accept hp
    have h:=sqrt_pair _ _ _ _ _ _ (activeCost N p)
      (AffineLoss.expectation_nonneg read p (Fin.lastCases false history) (xResetKraus w false psi) accept)
      (AffineLoss.expectation_nonneg read p (Fin.lastCases true history) (xResetKraus w true psi) accept)
      (mass_nonneg (xResetKraus w false psi)) (mass_nonneg (xResetKraus w true psi))
      (activeCost_nonneg N p) h0 h1
    rw [normSq_xResetKraus_false_add_true] at h
    simpa only [Phase23Partial.trimN,activeCost,expectation] using h
  | recordGate i v g p ih =>
    by_cases hg : largePhase 19 g=true
    · have hi:=ih N history psi accept hp.2
      have hs:=dropped_sqrt read p history psi accept hp.2 g hg
      have h:=conditional_sqrt read p history psi accept g (history i=v) _ _ _ (charge23_nonneg g) hi hs
      simpa only [Phase23Partial.trimN,hg,if_true,activeCost,expectation,TemplateGate.instantiate,run_singleton] using h
    · have hgf : largePhase 19 g=false := Bool.eq_false_iff.mpr hg
      by_cases hb : (decide (N>0)&&largePhase 18 g)=true
      · have hNb : 0<N ∧ largePhase 18 g=true := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using hb
        have hband := hNb.2
        have hi:=ih (N-1) history psi accept hp.2
        have hs:=band_sqrt read p history psi accept hp.2 g hband hgf
        have h:=conditional_sqrt read p history psi accept g (history i=v) _ _ _ unit23_pos.le hi hs
        simpa only [Phase23Partial.trimN,hgf,Bool.false_eq_true,if_false,hb,if_true,activeCost,expectation,TemplateGate.instantiate,run_singleton] using h
      · have hbf : (decide (N>0)&&largePhase 18 g)=false := Bool.eq_false_iff.mpr hb
        have hi:=ih N history (Quantum.run (if history i=v then [g] else []) psi) accept hp.2
        have hn : normSq (Quantum.run (if history i=v then [g] else []) psi)=normSq psi := by
          apply normSq_run
          split_ifs
          · simpa [CircuitWellFormed] using hp.1
          · simp [CircuitWellFormed]
        rw [hn] at hi
        simpa only [Phase23Partial.trimN,hgf,Bool.false_eq_true,if_false,hbf,activeCost,expectation,TemplateGate.instantiate] using hi
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases hg : largePhase 19 g=true
      · have hi:=ih N history psi accept hp.2
        have hs:=dropped_sqrt read p history psi accept hp.2 g hg
        have h:=compose_sqrt _ _ _ _ _ _ hi hs
        simpa only [Phase23Partial.trimN,hg,if_true,activeCost,expectation,TemplateGate.instantiate,run_singleton] using h
      · have hgf : largePhase 19 g=false := Bool.eq_false_iff.mpr hg
        by_cases hb : (decide (N>0)&&largePhase 18 g)=true
        · have hNb : 0<N ∧ largePhase 18 g=true := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using hb
          have hband := hNb.2
          have hi:=ih (N-1) history psi accept hp.2
          have hs:=band_sqrt read p history psi accept hp.2 g hband hgf
          have h:=compose_sqrt _ _ _ _ _ _ hi hs
          simpa only [Phase23Partial.trimN,hgf,Bool.false_eq_true,if_false,hb,if_true,activeCost,expectation,TemplateGate.instantiate,run_singleton] using h
        · have hbf : (decide (N>0)&&largePhase 18 g)=false := Bool.eq_false_iff.mpr hb
          have hi:=ih N history (Quantum.run ((TemplateGate.literal (tableSize:=n) g).instantiate read) psi) accept hp.2
          have hn:=normSq_template read (TemplateGate.literal (tableSize:=n) g) hp.1 psi
          rw [hn] at hi
          simpa only [Phase23Partial.trimN,hgf,Bool.false_eq_true,if_false,hbf,activeCost,expectation,TemplateGate.instantiate] using hi
    | whenBit r v g =>
      by_cases hg : largePhase 19 g=true
      · have hi:=ih N history psi accept hp.2
        have hs:=dropped_sqrt read p history psi accept hp.2 g hg
        have h:=conditional_sqrt read p history psi accept g (read r=v) _ _ _ (charge23_nonneg g) hi hs
        simpa only [Phase23Partial.trimN,hg,if_true,activeCost,expectation,TemplateGate.instantiate,run_singleton] using h
      · have hgf : largePhase 19 g=false := Bool.eq_false_iff.mpr hg
        by_cases hb : (decide (N>0)&&largePhase 18 g)=true
        · have hNb : 0<N ∧ largePhase 18 g=true := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using hb
          have hband := hNb.2
          have hi:=ih (N-1) history psi accept hp.2
          have hs:=band_sqrt read p history psi accept hp.2 g hband hgf
          have h:=conditional_sqrt read p history psi accept g (read r=v) _ _ _ unit23_pos.le hi hs
          simpa only [Phase23Partial.trimN,hgf,Bool.false_eq_true,if_false,hb,if_true,activeCost,expectation,TemplateGate.instantiate,run_singleton] using h
        · have hbf : (decide (N>0)&&largePhase 18 g)=false := Bool.eq_false_iff.mpr hb
          have hi:=ih N history (Quantum.run ((TemplateGate.whenBit (tableSize:=n) r v g).instantiate read) psi) accept hp.2
          have hn:=normSq_template read (TemplateGate.whenBit (tableSize:=n) r v g) hp.1 psi
          rw [hn] at hi
          simpa only [Phase23Partial.trimN,hgf,Bool.false_eq_true,if_false,hbf,activeCost,expectation,TemplateGate.instantiate] using hi

end
end ShorECDLP.Entrant.SqrtLoss
