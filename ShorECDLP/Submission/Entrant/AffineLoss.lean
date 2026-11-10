import ShorECDLP.Submission.Entrant.ComplementLoss
import ShorECDLP.Submission.Entrant.Schedule27
namespace ShorECDLP.Entrant.AffineLoss
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28 ComplementLoss
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option Elab.async false
attribute [local irreducible] List.ofFn
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem affine_loss {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi phi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (delta : ℝ) (hd : 0 < delta)
    (he : normSq (phi-psi) ≤ delta^2*normSq psi) :
    expectation read p history phi accept ≤
      (1+10*delta)*expectation read p history psi accept +
        (delta/10+delta^2)*normSq psi := by
  have h := expectation_upper read p history psi (phi-psi) accept (10*delta)
  have hs : psi+(phi-psi)=phi := by abel
  rw [hs] at h
  have hu := expectation_le_mass read p history (phi-psi) accept hp
  have hm := mul_le_mul_of_nonneg_left (hu.trans he) (show 0 ≤ 1+10*delta by positivity)
  have hh : 10*delta * expectation read p history phi accept ≤
      10*delta*((1+10*delta)*expectation read p history psi accept +
        (delta/10+delta^2)*normSq psi) := by nlinarith
  exact (mul_le_mul_iff_right₀ (show 0<10*delta by positivity)).mp hh


theorem phase_affine {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (dir : PhaseDir) (k : Nat) (t : Wire) (delta : ℝ) (hd : 0 < delta)
    (ha : (phaseAngle dir k/2)^2 ≤ delta^2) :
    expectation read p history psi accept ≤
      (1+10*delta)*expectation read p history (applyGate (.P dir k t) psi) accept +
        (delta/10+delta^2)*normSq psi := by
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
  have hdiff : normSq (psi-phi) ≤ delta^2 * normSq phi := by
    rw [hn]
    have hneg : psi-phi = -(phi-psi) := by abel
    rw [hneg, normSq_neg]
    exact (phase_centered_mass dir k t psi).trans
      (mul_le_mul_of_nonneg_right ha (mass_nonneg psi))
  simpa only [hphi,hn] using affine_loss read p history phi psi accept hp delta hd hdiff

def charge23 : Gate → ℝ
  | .P _ k _ => if 23 < k then (6283186/1000000:ℝ)/2^(k+1) else 0
  | _ => 0

def cost23 {n s e} : Straight n s e → ℝ
  | .done => 0
  | .gate (.literal g) p => charge23 g + cost23 p
  | .gate (.whenBit _ _ g) p => charge23 g + cost23 p
  | .recordGate _ _ g p => charge23 g + cost23 p
  | .measure _ p => cost23 p

theorem charge23_nonneg (g : Gate) : 0 ≤ charge23 g := by
  cases g <;> simp only [charge23] <;> positivity

theorem cost23_nonneg {n s e} (p : Straight n s e) : 0 ≤ cost23 p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> exact add_nonneg (charge23_nonneg _) ih
  | recordGate i v g p ih => exact add_nonneg (charge23_nonneg _) ih
  | measure w p ih => exact ih

theorem charge23_false (g : Gate) (h : largePhase 23 g = false) : charge23 g = 0 := by
  cases g <;> simp_all [largePhase,charge23]

theorem dropped_affine {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (g : Gate) (hg : largePhase 23 g = true) :
    expectation read p history psi accept ≤
      (1+10*charge23 g)*expectation read p history (applyGate g psi) accept +
        (charge23 g/10+(charge23 g)^2)*normSq psi := by
  cases g <;> simp only [largePhase, Bool.false_eq_true,decide_eq_true_eq] at hg
  case P dir k t =>
    have hd : 0 < (6283186/1000000:ℝ)/2^(k+1) := by positivity
    have ha : (phaseAngle dir k/2)^2 ≤ ((6283186/1000000:ℝ)/2^(k+1))^2 := by
      have hpi := Real.pi_lt_d6
      have hb : 2*Real.pi/(2:ℝ)^k/2 ≤ (6283186/1000000:ℝ)/(2:ℝ)^(k+1) := by
        rw [pow_succ, div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have hz : 0 ≤ 2*Real.pi/(2:ℝ)^k/2 := by positivity
      cases dir <;> simp only [phaseAngle, neg_div, neg_sq] <;> nlinarith
    simpa only [charge23,hg,if_true] using phase_affine read p history psi accept hp dir k t _ hd ha

theorem compose_bound (c d E F G M : ℝ) (hc : 0≤c) (hd : 0≤d)
    (hsmall : c+d ≤ 1/5000) (hE : 0≤E) (hM : 0≤M)
    (hF : F ≤ (1+10*d)*E+(d/10+d^2)*M)
    (hG : G ≤ (1+(10021/1000)*c)*F+(10021/100000)*c*M) :
    G ≤ (1+(10021/1000)*(c+d))*E+(10021/100000)*(c+d)*M := by
  have hcoef : (1+(10021/1000)*c)*(1+10*d) ≤ 1+(10021/1000)*(c+d) := by nlinarith
  have herr : (1+(10021/1000)*c)*(d/10+d^2)+(10021/100000)*c ≤ (10021/100000)*(c+d) := by
    have hcd : c*d ≤ (1/5000)*d := mul_le_mul_of_nonneg_right (by linarith : c≤1/5000) hd
    have hdd : d*d ≤ (1/5000)*d := mul_le_mul_of_nonneg_right (by linarith : d≤1/5000) hd
    have hcdd : c*(d*d) ≤ (1/5000)*(d*d) := mul_le_mul_of_nonneg_right (by linarith : c≤1/5000) (mul_nonneg hd hd)
    have hadd := mul_le_mul_of_nonneg_right hsmall hd
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hF (show 0≤1+(10021/1000)*c by positivity)
  have h1 := mul_le_mul_of_nonneg_right hcoef hE
  have h2 := mul_le_mul_of_nonneg_right herr hM
  nlinarith

theorem expectation_nonneg {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) : 0 ≤ expectation read p history psi accept := by
  induction p generalizing psi with
  | done => simp only [expectation]; split_ifs; exact mass_nonneg psi; rfl
  | gate g p ih => exact ih history _ accept
  | recordGate i v g p ih => exact ih history _ accept
  | measure w p ih => exact add_nonneg (ih _ _ accept) (ih _ _ accept)

theorem idle_affine (d E M : ℝ) (hd : 0≤d) (hE : 0≤E) (hM : 0≤M) :
    E ≤ (1+10*d)*E+(d/10+d^2)*M := by
  nlinarith [mul_nonneg hd hE,mul_nonneg (show 0≤d/10+d^2 by positivity) hM]

theorem trim23_expectation {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (hb : cost23 p ≤ 1/5000) :
    expectation read (trim 23 p) history psi accept ≤
      (1+(10021/1000)*cost23 p)*expectation read p history psi accept +
        (10021/100000)*cost23 p*normSq psi := by
  induction p generalizing psi with
  | done => simp [trim,cost23,expectation]
  | measure w p ih =>
    have h0 := ih (Fin.lastCases false history) (xResetKraus w false psi) accept hp hb
    have h1 := ih (Fin.lastCases true history) (xResetKraus w true psi) accept hp hb
    have hm := normSq_xResetKraus_false_add_true w psi
    simp only [trim,cost23,expectation]
    apply (add_le_add h0 h1).trans_eq
    rw [← hm]
    ring
  | recordGate i v g p ih =>
    by_cases hg : largePhase 23 g = true
    · have hc := charge23_nonneg g
      have ht := cost23_nonneg p
      have hb' : cost23 p ≤ 1/5000 := by simpa only [cost23] using (show charge23 g+cost23 p ≤ 1/5000 from hb) |> fun h => by linarith
      have hi := ih history psi accept hp.2 hb'
      have hs := dropped_affine read p history psi accept hp.2 g hg
      have hE := expectation_nonneg read p history (applyGate g psi) accept
      have hM := mass_nonneg psi
      have hidle := idle_affine (charge23 g) (expectation read p history psi accept) (normSq psi) hc (expectation_nonneg read p history psi accept) hM
      simp only [trim,hg,if_true,cost23,expectation]
      by_cases hr : history i=v
      · simp only [hr,if_true,run_singleton]
        simpa only [add_comm] using compose_bound (cost23 p) (charge23 g) _ _ _ _ ht hc (show cost23 p+charge23 g ≤ 1/5000 by simpa only [cost23,add_comm] using hb) hE hM hs hi
      · simp only [hr,if_false,run_nil,LinearMap.id_coe,id_eq]
        simpa only [add_comm] using compose_bound (cost23 p) (charge23 g) _ _ _ _ ht hc (show cost23 p+charge23 g ≤ 1/5000 by simpa only [cost23,add_comm] using hb) (expectation_nonneg read p history psi accept) hM hidle hi
    · have hgf : largePhase 23 g = false := Bool.eq_false_iff.mpr hg
      have hz := charge23_false g hgf
      have hb' : cost23 p ≤ 1/5000 := by simpa only [cost23,hz,zero_add] using hb
      have hi := ih history (Quantum.run (if history i=v then [g] else []) psi) accept hp.2 hb'
      have hn : normSq (Quantum.run (if history i=v then [g] else []) psi) = normSq psi := by
        apply normSq_run
        split_ifs
        · simpa [CircuitWellFormed] using hp.1
        · simp [CircuitWellFormed]
      rw [hn] at hi
      simpa only [trim,hgf,Bool.false_eq_true,if_false,cost23,hz,zero_add,expectation] using hi
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases hg : largePhase 23 g = true
      · have hc := charge23_nonneg g
        have ht := cost23_nonneg p
        have hb' : cost23 p ≤ 1/5000 := by simpa only [cost23] using (show charge23 g+cost23 p ≤ 1/5000 from hb) |> fun h => by linarith
        have hi := ih history psi accept hp.2 hb'
        have hs := dropped_affine read p history psi accept hp.2 g hg
        have hE := expectation_nonneg read p history (applyGate g psi) accept
        have hM := mass_nonneg psi
        simp only [trim,hg,if_true,cost23,expectation, TemplateGate.instantiate,run_singleton]
        simpa only [add_comm] using compose_bound (cost23 p) (charge23 g) _ _ _ _ ht hc (show cost23 p+charge23 g ≤ 1/5000 by simpa only [cost23,add_comm] using hb) hE hM hs hi
      · have hgf : largePhase 23 g = false := Bool.eq_false_iff.mpr hg
        have hz := charge23_false g hgf
        have hb' : cost23 p ≤ 1/5000 := by simpa only [cost23,hz,zero_add] using hb
        have hi := ih history (Quantum.run [g] psi) accept hp.2 hb'
        have hn : normSq (Quantum.run [g] psi) = normSq psi := by
          apply normSq_run
          simpa [CircuitWellFormed] using hp.1
        rw [hn] at hi
        simpa only [trim,hgf,Bool.false_eq_true,if_false,cost23,hz,zero_add,expectation, TemplateGate.instantiate] using hi
    | whenBit r v g =>
      by_cases hg : largePhase 23 g = true
      · have hc := charge23_nonneg g
        have ht := cost23_nonneg p
        have hb' : cost23 p ≤ 1/5000 := by simpa only [cost23] using (show charge23 g+cost23 p ≤ 1/5000 from hb) |> fun h => by linarith
        have hi := ih history psi accept hp.2 hb'
        have hs := dropped_affine read p history psi accept hp.2 g hg
        have hE := expectation_nonneg read p history (applyGate g psi) accept
        have hM := mass_nonneg psi
        have hidle := idle_affine (charge23 g) (expectation read p history psi accept) (normSq psi) hc (expectation_nonneg read p history psi accept) hM
        simp only [trim,hg,if_true,cost23,expectation,TemplateGate.instantiate]
        by_cases hr : read r=v
        · simp only [hr,if_true,run_singleton]
          simpa only [add_comm] using compose_bound (cost23 p) (charge23 g) _ _ _ _ ht hc (show cost23 p+charge23 g ≤ 1/5000 by simpa only [cost23,add_comm] using hb) hE hM hs hi
        · simp only [hr,if_false,run_nil,LinearMap.id_coe,id_eq]
          simpa only [add_comm] using compose_bound (cost23 p) (charge23 g) _ _ _ _ ht hc (show cost23 p+charge23 g ≤ 1/5000 by simpa only [cost23,add_comm] using hb) (expectation_nonneg read p history psi accept) hM hidle hi
      · have hgf : largePhase 23 g = false := Bool.eq_false_iff.mpr hg
        have hz := charge23_false g hgf
        have hb' : cost23 p ≤ 1/5000 := by simpa only [cost23,hz,zero_add] using hb
        have hi := ih history (Quantum.run ((TemplateGate.whenBit r v g).instantiate read) psi) accept hp.2 hb'
        have hn : normSq (Quantum.run ((TemplateGate.whenBit r v g).instantiate read) psi) = normSq psi :=
          normSq_template read (.whenBit r v g) hp.1 psi
        rw [hn] at hi
        simpa only [trim,hgf,Bool.false_eq_true,if_false,cost23,hz,zero_add,expectation, TemplateGate.instantiate] using hi


open Secp256k1 Single Single.Distribution
set_option linter.unnecessarySeqFocus false

def potential23 (k : Nat) : ℝ := (6283186/1000000:ℝ)/(2:ℝ)^(max 24 k)
def unit23 : ℝ := (6283186/1000000:ℝ)/2^24

theorem error_zero {n s e} (p : Straight n s e) (h : residue p = 0) : cost23 p = 0 := by
  induction p with
  | done => rfl
  | measure w p ih => exact ih h
  | recordGate i v g p ih =>
    have ht : residue p = 0 := by simp only [residue] at h; omega
    have hg : charge23 g = 0 := by cases g <;> simp_all [residue,tCost,charge23]
    simp [cost23,hg,ih ht]
  | gate g p ih =>
    have ht : residue p = 0 := by cases g <;> simp only [residue] at h <;> omega
    cases g with
    | literal g =>
      have hg : charge23 g = 0 := by cases g <;> simp_all [residue,primitivePhaseCost,charge23]
      simp [cost23,hg,ih ht]
    | whenBit r v g =>
      have hg : charge23 g = 0 := by cases g <;> simp_all [residue,tCost,charge23]
      simp [cost23,hg,ih ht]

theorem error_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    cost23 (p.append q) = cost23 p + cost23 q := by
  induction p with
  | done => simp [Straight.append,cost23]
  | gate g p ih => cases g <;> simp [Straight.append,cost23,ih,add_assoc]
  | recordGate => simp_all [Straight.append,cost23,add_assoc]
  | measure => simp_all [Straight.append,cost23]

theorem error_cast {n s e f} (p : Straight n s e) (h : e=f) : cost23 (castFinish h p) = cost23 p := by subst f; rfl

theorem error_prepare {n s e} (ws : List Wire) (p : Straight n s e) :
    cost23 (prepareOuterBank ws p) = cost23 p := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [prepareOuterBank,cost23,charge23] using ih

theorem error_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    cost23 (reindexStraight f p) = cost23 p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp_all [reindexStraight,reindexGate,cost23]
  | recordGate => simp_all [reindexStraight,cost23]
  | measure => simp_all [reindexStraight,cost23]
theorem sharp_unit : unit23 = (6283186/1000000:ℝ)/2^24 := rfl
theorem charge_balance (dir : PhaseDir) (w : Wire) (k : Nat) :
    charge23 (.P dir k w) + potential23 (k+1) = potential23 k := by
  by_cases hk : 23 < k
  · have h1 : max 24 k = k := max_eq_right (by omega)
    have h2 : max 24 (k+1) = k+1 := max_eq_right (by omega)
    simp only [charge23,hk,if_true,potential23,h1,h2,pow_succ]
    have hp : (2:ℝ)^k ≠ 0 := by positivity
    field_simp
    <;> ring
  · have h1 : max 24 k = 24 := max_eq_left (by omega)
    have h2 : max 24 (k+1) = 24 := max_eq_left (by omega)
    simp [charge23,hk,potential23,h1,h2]


theorem error_feedback_balance {n s e} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    cost23 (feedbackProgram dir w indices k p) + potential23 (k+indices.length) =
      potential23 k + cost23 p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram,add_comm]
  | cons i is ih =>
    have hi := ih (k+1)
    have hc := charge_balance dir w k
    have he : k + (i::is).length = (k+1)+is.length := by simp; omega
    simp only [feedbackProgram,cost23,he]
    linarith

def account : Nat → Nat → ℝ
  | 0,_ => 0
  | n+1,p => unit23 - potential23 (p+2) + account n (p+1)

theorem account_append (a b p : Nat) :
    account (a+b) p = account a p + account b (p+a) := by
  induction a generalizing p with
  | zero => simp [account]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [account,ih]
    have he : p+(a+1) = (p+1)+a := by omega
    rw [he]
    ring

theorem error_fourier_exact (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    cost23 (fourierProgram n dir ws start prior) = account ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [fourierProgram,cost23,account]
  | cons w ws ih =>
    simp only [fourierProgram,error_cast]
    have hi := ih (start+1) (Fin.last start :: prior.map Fin.castSucc)
    have hf := error_feedback_balance dir w prior 2 (.measure w
      (fourierProgram n dir ws (start+1) (Fin.last start :: prior.map Fin.castSucc)))
    have he : potential23 2 = unit23 := by norm_num [potential23,unit23]
    simp only [cost23,hi,he,List.length_cons,List.length_map] at hf hi
    rw [List.length_cons,account]
    have hn : 2+prior.length = prior.length+2 := by omega
    rw [hn] at hf
    linarith


theorem potential_half (k : Nat) (hk : 24 ≤ k) :
    2*potential23 (k+1) = potential23 k := by
  have h1 : max 24 k = k := max_eq_right hk
  have h2 : max 24 (k+1) = k+1 := max_eq_right (by omega)
  simp only [potential23,h1,h2,pow_succ]
  ring

theorem account_geometric (n p : Nat) (hp : 22 ≤ p) :
    account n p + 2*potential23 (p+2) = (n:ℝ)*unit23 + 2*potential23 (p+n+2) := by
  induction n generalizing p with
  | zero => simp [account]
  | succ n ih =>
    have hi := ih (p+1) (by omega)
    have hh := potential_half (p+2) (by omega)
    have he : p+2+1 = p+1+2 := by omega
    rw [he] at hh
    have he2 : p+(n+1)+2 = (p+1)+n+2 := by omega
    simp only [account,Nat.cast_add,Nat.cast_one,he2]
    linarith

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem joint_error : account 261 0 + account 208 0 ≤ (1685/4:ℝ)*unit23 := by
  have hz : account 22 0 = 0 := by norm_num [account,potential23,unit23]
  rw [show 261=22+239 from rfl, show 208=22+186 from rfl,account_append,account_append,hz]
  norm_num only [zero_add]
  have h1 := account_geometric 239 22 (by decide)
  have h2 := account_geometric 186 22 (by decide)
  norm_num [potential23,unit23] at h1 h2 ⊢
  rw [show 263=255+8 from rfl,pow_add] at h1
  norm_num at h1
  linarith

theorem error_axis_exact {n} (ws : List (Window n))
    (hz : ∀ w ∈ ws, ∀ start, cost23 (w.program start) = 0)
    (start : Nat) (prior : List (Fin start)) :
    cost23 (axis ws start prior) =
      account ((ws.map (fun w => w.wires.length)).sum) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis,cost23,account]
  | cons w ws ih =>
    simp only [axis,error_cast,error_append,error_prepare]
    rw [hz w (by simp) start,zero_add]
    have hf := error_fourier_exact n .inverse w.wires (start+w.count) (bankPrior w.count prior)
    have hi := ih (fun v hv s => hz v (List.mem_cons_of_mem w hv) s)
      (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior)
    rw [hf,hi]
    simp only [bankPrior,nextPrior,List.length_append,List.length_reverse,List.length_ofFn,List.length_map,List.map_cons,List.sum_cons,account_append]
    rw [Nat.add_comm w.wires.length prior.length]



open Width16Schedule ConditionalCatalyst
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
set_option linter.unusedSectionVars false
attribute [local irreducible] Width16Schedule.sourceEntry Width16Schedule.program
  Width16Schedule.fullProgram Width16Schedule.readout Single.fixedEntry Single.axis

theorem axis_width_sum {n} {ws : List (Single.Window n)} {widths : List Nat}
    (h : List.Forall₂ (fun w c => w.wires.length = c) ws widths) :
    (ws.map (fun w => w.wires.length)).sum = widths.sum := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons,List.sum_cons,head,ih]

theorem full_error (impl : Width16Schedule.Implementation) (reset : List Wire) :
    cost23 (Width16Schedule.fullProgram impl reset) ≤ (1685/4:ℝ)*unit23 := by
  have hA := error_axis_exact ([impl.headA])
    (by
      intro w hw start
      apply error_zero
      rcases List.mem_singleton.mp hw with rfl
      exact impl.headA_zero start) 0 List.nil
  have hB := error_axis_exact ([impl.headB])
    (by
      intro w hw start
      apply error_zero
      rcases List.mem_singleton.mp hw with rfl
      exact impl.headB_zero start) (mixS1 impl.headA 0) List.nil
  have hL := error_axis_exact (leftBodies impl)
    (by
      intro w hw start
      apply error_zero
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
      exact impl.signed_zero d start) (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0)
  have hR := error_axis_exact (rightBodies impl)
    (by
      intro w hw start
      apply error_zero
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
      exact impl.signed_zero d start)
    (mixS3 impl.headA impl.headB (leftBodies impl) 0) (mixPriorR impl.headA impl.headB (leftBodies impl) 0)
  rw [mixPriorL_length] at hL
  rw [mixPriorR_length] at hR
  rw [axis_width_sum (left_width_relation impl)] at hL
  rw [axis_width_sum (right_width_relation impl)] at hR
  have hsA : (([impl.headA]).map (fun w => w.wires.length)).sum = 10 := by
    simp [impl.headA_width]
  have hsB : (([impl.headB]).map (fun w => w.wires.length)).sum = 8 := by
    simp [impl.headB_width]
  rw [hsA, List.length_nil] at hA
  rw [hsB, List.length_nil] at hB
  have hlw : leftWidthsBody.sum = 251 := by simp [leftWidthsBody, List.replicate]
  have hrw : rightWidthsBody.sum = 200 := by simp [rightWidthsBody, List.replicate]
  rw [hlw] at hL
  rw [hrw] at hR
  have hz (n start : Nat) (ws : List Wire) : residue (resetProgram n start ws) = 0 := by
    induction ws generalizing start with
    | nil => simp [resetProgram,residue]
    | cons w ws ih => simpa [resetProgram,residue_cast,residue] using ih (start+1)
  have hreset : cost23 (resetProgram 1769472
      (mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0) reset) = 0 :=
    error_zero _ (hz _ _ _)
  have hro : cost23 (Width16Schedule.readout impl reset) = 0 := by
    apply error_zero
    simp only [Width16Schedule.readout,residue_cast,ApproximatePhase34.residue_suffix56]
  have hacc1 : account 261 0 = account 10 0 + account 251 10 := by
    have := account_append 10 251 0
    simpa using this
  have hacc2 : account 208 0 = account 8 0 + account 200 8 := by
    have := account_append 8 200 0
    simpa using this
  simp only [Width16Schedule.fullProgram,error_append,Width16Schedule.program,Single.framed,error_cast,cost23,charge23,zero_add,hreset,hro,mixHead,mixTail]
  linarith [joint_error]

theorem source_error (impl : Width16Schedule.Implementation) (reset : List Wire) :
    cost23 (Width16Schedule.sourceEntry impl reset).program ≤ (1685/4:ℝ)*unit23 := by
  unfold Width16Schedule.sourceEntry Single.fixedEntry
  rw [error_reindex]
  exact full_error impl reset


def droppedSlots23 : Nat → Nat → Nat
  | 0, _ => 0
  | width+1, prior => (prior - 22) + droppedSlots23 width (prior + 1)

def metadataDropped23 : List Nat → Nat → Nat
  | [], _ => 0
  | width :: ws, prior => droppedSlots23 width prior + metadataDropped23 ws (prior + width)

theorem removed23_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    removed 23 (p.append q) = removed 23 p + removed 23 q := by
  induction p with
  | done => simp [Straight.append, removed]
  | gate g p ih => cases g <;> simp [Straight.append, removed, ih, Nat.add_assoc]
  | recordGate i v g p ih => simp_all [Straight.append, removed, Nat.add_assoc]
  | measure w p ih => simp_all [Straight.append, removed]

theorem removed23_cast {n s e f} (p : Straight n s e) (h : e = f) :
    removed 23 (castFinish h p) = removed 23 p := by subst f; rfl

theorem removed23_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    removed 23 (reindexStraight f p) = removed 23 p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [reindexStraight, reindexGate, removed, ih]
    | whenBit r v g => simp_all [reindexStraight, reindexGate, removed, ih]
  | recordGate => simp_all [reindexStraight, removed]
  | measure => simp_all [reindexStraight, removed]

theorem removed23_feedback {n s e} (dir : ShorECDLP.PhaseDir) (w : ShorECDLP.Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    removed 23 (feedbackProgram dir w indices k p) =
      (indices.length - min indices.length (24 - k)) + removed 23 p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih =>
    simp only [feedbackProgram, removed, largePhase, ih, List.length_cons]
    by_cases hk : 23 < k
    · simp only [hk, decide_true, Bool.toNat_true]
      omega
    · simp only [hk, decide_false, Bool.toNat_false]
      omega

theorem removed23_prepare {n s e} (ws : List ShorECDLP.Wire) (p : Straight n s e) :
    removed 23 (prepareOuterBank ws p) = removed 23 p := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [prepareOuterBank, removed, largePhase] using ih

theorem removed_fourier23 (n : Nat) (dir : ShorECDLP.PhaseDir) (ws : List ShorECDLP.Wire)
    (start : Nat) (prior : List (Fin start)) :
    removed 23 (fourierProgram n dir ws start prior) = droppedSlots23 ws.length prior.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp [fourierProgram, removed23_cast, removed23_feedback,
      removed, ih, droppedSlots23]; omega

theorem weighted23_removed_framed {n s m k e f} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    removed 23 (Single.framed p q r h) = removed 23 p + removed 23 q + removed 23 r := by
  simp [Single.framed, removed, removed23_cast, removed23_append, largePhase, Nat.add_assoc]

theorem weighted23_removed_fixedEntry {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e) :
    removed 23 (Single.fixedEntry f p).program = removed 23 p := by
  unfold Single.fixedEntry
  exact removed23_reindex p _

theorem removed_axis23 [body : Single.WindowBody] [ledger : Single.ProducerResources body] {n}
    (ws : List (Single.Window n)) (widths : List Nat)
    (hw : List.Forall₂ (fun w c => w.wires.length = c) ws widths)
    (start : Nat) (prior : List (Fin start)) :
    metadataDropped23 widths prior.length ≤ removed 23 (Single.axis ws start prior) := by
  induction ws generalizing widths start with
  | nil => cases hw; simp [metadataDropped23,Single.axis,removed]
  | cons w ws ih =>
    cases hw with
    | cons head tail =>
      rename_i c widths
      simp only [Single.axis, removed23_cast, removed23_append, removed23_prepare, removed_fourier23,
        bankPrior_length]
      have ht := ih widths tail (start+w.count+w.wires.length) (Single.nextPrior w.count w.wires.length prior)
      rw [Single.nextPrior_length] at ht
      simp only [metadataDropped23]
      rw [head] at *
      omega

theorem exact_metadata23 : metadataDropped23 [10] 0 + metadataDropped23 [8] 0 +
    metadataDropped23 leftWidthsBody 10 + metadataDropped23 rightWidthsBody 8 = 45646 := by
  decide +kernel

theorem source_removed23 (impl : Implementation) (reset : List Wire) :
    45646 ≤ removed 23 (sourceEntry impl reset).program := by
  have hA := removed_axis23 ([impl.headA]) ([10]) (headA_width_relation impl) 0 List.nil
  have hB := removed_axis23 ([impl.headB]) ([8]) (headB_width_relation impl)
    (mixS1 impl.headA 0) List.nil
  have hL := removed_axis23 (leftBodies impl) leftWidthsBody (left_width_relation impl)
    (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0)
  have hR := removed_axis23 (rightBodies impl) rightWidthsBody (right_width_relation impl)
    (mixS3 impl.headA impl.headB (leftBodies impl) 0)
    (mixPriorR impl.headA impl.headB (leftBodies impl) 0)
  rw [mixPriorL_length] at hL
  rw [mixPriorR_length] at hR
  simp only [List.length_nil] at hA hB
  have hm := exact_metadata23
  unfold sourceEntry
  rw [weighted23_removed_fixedEntry]
  simp only [fullProgram,removed23_append,Width16Schedule.program,weighted23_removed_framed,
    mixHead,mixTail,removed23_append]
  omega
theorem dropped_weight23 (g : Gate) (hg : largePhase 23 g = true) :
    ConditionalCatalyst.weightedGate g = 1 ∧ ConditionalCatalyst.weightedLiteral g = 1 := by
  cases g <;> simp only [largePhase, Bool.false_eq_true, decide_eq_true_eq] at hg
  case P dir k t =>
    have hk : k ≠ 2 := by omega
    simp [ConditionalCatalyst.weightedGate, ConditionalCatalyst.weightedLiteral,
      ConditionalCatalyst.phaseTwoGate_P, hk, tCost]

theorem weight4_trim23 {n s e} (p : Straight n s e) :
    ConditionalCatalyst.weight4 (trim 23 p) + removed 23 p = ConditionalCatalyst.weight4 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases hg : largePhase 23 g = true
      · have hw := (dropped_weight23 g hg).2
        simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight4, hw]
        omega
      · have hgf : largePhase 23 g = false := Bool.eq_false_iff.mpr hg
        simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add, ConditionalCatalyst.weight4]
        omega
    | whenBit r v g =>
      by_cases hg : largePhase 23 g = true
      · have hw := (dropped_weight23 g hg).1
        simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight4, hw]
        omega
      · have hgf : largePhase 23 g = false := Bool.eq_false_iff.mpr hg
        simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add, ConditionalCatalyst.weight4]
        omega
  | recordGate i v g p ih =>
    by_cases hg : largePhase 23 g = true
    · have hw := (dropped_weight23 g hg).1
      simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight4, hw]
      omega
    · have hgf : largePhase 23 g = false := Bool.eq_false_iff.mpr hg
      simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add, ConditionalCatalyst.weight4]
      omega
  | measure w p ih => exact ih

theorem trim_t23 {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    ((trim 23 p).instantiate read history).tCount ≤ (p.instantiate read history).tCount := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g <;> simp only [trim] <;> split_ifs <;>
      simp only [Straight.instantiate, AdaptiveCircuit.tCount] <;>
      (have h := ih history; omega)
  | recordGate i v g p ih =>
    simp only [trim]; split_ifs <;>
      simp only [Straight.instantiate, AdaptiveCircuit.tCount] <;>
      (have h := ih history; omega)
  | measure w p ih =>
    simp only [trim, Straight.instantiate, AdaptiveCircuit.tCount]
    exact max_le_max (ih _) (ih _)

theorem trim_added23 {n s e} (p : Straight n s e) : added (trim 23 p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp [trim, largePhase, added, ih] <;> split_ifs <;> simp_all [added]
    | whenBit r v g => simp only [trim]; split_ifs <;> simpa only [added] using ih
  | recordGate i v g p ih => simp only [trim]; split_ifs <;> simpa only [added] using ih
  | measure w p ih => exact ih



#print axioms source_removed23
#print axioms weight4_trim23
end
end ShorECDLP.Entrant.AffineLoss
