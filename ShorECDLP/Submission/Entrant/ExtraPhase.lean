import ShorECDLP.Submission.Entrant.Schedule27
import ShorECDLP.Submission.Entrant.ComplementLoss

namespace ShorECDLP.Entrant.ExtraPhase
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28 ConditionalCatalyst
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule
open ComplementLoss
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

def phase26 : Gate → Bool
  | .P _ k _ => decide (k=26)
  | _ => false

def drop26 {n s e} (N : Nat) : Straight n s e → Straight n s e
  | .done => .done
  | .gate (.literal g) p =>
      if decide (N>0) && phase26 g then drop26 (N-1) p
      else .gate (.literal g) (drop26 N p)
  | .gate (.whenBit r v g) p =>
      if decide (N>0) && phase26 g then drop26 (N-1) p
      else .gate (.whenBit r v g) (drop26 N p)
  | .recordGate i v g p =>
      if decide (N>0) && phase26 g then drop26 (N-1) p
      else .recordGate i v g (drop26 N p)
  | .measure w p => .measure w (drop26 N p)

theorem phase26_loss {n s e} (read : ConstantBit n → Bool) (p : Straight n s e)
    (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool)
    (hp : p.WellFormed) (g : Gate) (hg : phase26 g = true) :
    expectation read p history (applyGate g psi) accept ≤
      expectation read p history psi accept + (2*unit)*normSq psi := by
  cases g <;> simp only [phase26,Bool.false_eq_true] at hg
  case P dir k t =>
    have hk : k=26 := by simpa using hg
    subst hk
    apply phase_loss read p history psi accept hp dir 26 t (2*unit) (by unfold unit; positivity)
    have hpi := Real.pi_lt_d6
    have hpp := Real.pi_pos
    cases dir <;> norm_num [phaseAngle,unit] <;> nlinarith

theorem drop26_expectation {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (N : Nat) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed) :
    expectation read p history psi accept ≤ expectation read (drop26 N p) history psi accept +
      (N:ℝ)*(2*unit)*normSq psi := by
  have hu : 0 ≤ unit := by unfold unit; positivity
  induction p generalizing N psi with
  | done =>
    simp only [drop26,expectation]
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    have hm := mass_nonneg psi
    have hprod : 0 ≤ (N:ℝ)*(2*unit)*normSq psi :=
      mul_nonneg (mul_nonneg hn (mul_nonneg (by norm_num) hu)) hm
    linarith
  | measure w p ih =>
    have h0 := ih N (Fin.lastCases false history) (xResetKraus w false psi) accept hp
    have h1 := ih N (Fin.lastCases true history) (xResetKraus w true psi) accept hp
    have hm := normSq_xResetKraus_false_add_true w psi
    have he := congrArg (fun x : ℝ => (N:ℝ)*(2*unit)*x) hm
    simp only [drop26,expectation]
    linarith
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases h : (decide (N>0) && phase26 g) = true
      · have hd : 0 < N ∧ phase26 g = true := by
          simpa only [Bool.and_eq_true,decide_eq_true_eq] using h
        have hn : 0 < N := by simpa using hd.1
        have hc : ((N-1:Nat):ℝ) = (N:ℝ)-1 := Nat.cast_pred hn
        have hs := phase26_loss read p history psi accept hp.2 g hd.2
        have hi := ih (N-1) history psi accept hp.2
        rw [hc] at hi
        simp only [drop26,h,if_true,expectation,TemplateGate.instantiate,run_singleton]
        nlinarith
      · have hf := Bool.eq_false_iff.mpr h
        have hi := ih N history (applyGate g psi) accept hp.2
        rw [normSq_gate g hp.1 psi] at hi
        simpa only [drop26,hf,if_false,expectation,TemplateGate.instantiate,run_singleton] using hi
    | whenBit r v g =>
      by_cases h : (decide (N>0) && phase26 g) = true
      · have hd : 0 < N ∧ phase26 g = true := by
          simpa only [Bool.and_eq_true,decide_eq_true_eq] using h
        have hn : 0 < N := by simpa using hd.1
        have hc : ((N-1:Nat):ℝ) = (N:ℝ)-1 := Nat.cast_pred hn
        have hs := phase26_loss read p history psi accept hp.2 g hd.2
        have hi := ih (N-1) history psi accept hp.2
        rw [hc] at hi
        simp only [drop26,h,if_true,expectation,TemplateGate.instantiate]
        by_cases hr : read r=v
        · simp only [hr,if_true,run_singleton]; nlinarith
        · simp only [hr,if_false,run_nil,LinearMap.id_coe,id_eq]
          have hm := mass_nonneg psi
          nlinarith
      · have hf := Bool.eq_false_iff.mpr h
        have hi := ih N history (run ((TemplateGate.whenBit r v g).instantiate read) psi) accept hp.2
        rw [normSq_template read (.whenBit r v g) hp.1 psi] at hi
        simpa only [drop26,hf,if_false,expectation] using hi
  | recordGate i v g p ih =>
    by_cases h : (decide (N>0) && phase26 g) = true
    · have hd : 0 < N ∧ phase26 g = true := by
          simpa only [Bool.and_eq_true,decide_eq_true_eq] using h
      have hn : 0 < N := by simpa using hd.1
      have hc : ((N-1:Nat):ℝ) = (N:ℝ)-1 := Nat.cast_pred hn
      have hs := phase26_loss read p history psi accept hp.2 g hd.2
      have hi := ih (N-1) history psi accept hp.2
      rw [hc] at hi
      simp only [drop26,h,if_true,expectation]
      by_cases hr : history i=v
      · simp only [hr,if_true,run_singleton]; nlinarith
      · simp only [hr,if_false,run_nil,LinearMap.id_coe,id_eq]
        have hm := mass_nonneg psi
        nlinarith
    · have hf := Bool.eq_false_iff.mpr h
      have hi := ih N history (run (if history i=v then [g] else []) psi) accept hp.2
      have he : normSq (run (if history i=v then [g] else []) psi) = normSq psi := by
        apply normSq_run
        split_ifs
        · simpa [CircuitWellFormed] using hp.1
        · simp [CircuitWellFormed]
      rw [he] at hi
      simpa only [drop26,hf,if_false,expectation] using hi


theorem drop26_wellFormed {n s e} (N : Nat) (p : Straight n s e)
    (hp : p.WellFormed) : (drop26 N p).WellFormed := by
  induction p generalizing N with
  | done => trivial
  | gate g p ih =>
    cases g <;> simp only [drop26] <;> split_ifs <;>
      first | exact ih _ hp.2 | exact ⟨hp.1, ih _ hp.2⟩
  | recordGate i v g p ih =>
    simp only [drop26] <;> split_ifs <;>
      first | exact ih _ hp.2 | exact ⟨hp.1, ih _ hp.2⟩
  | measure w p ih => simp only [drop26]; exact ih _ hp

theorem drop26_within {n s e} (N : Nat) (p : Straight n s e) (ws : List ShorECDLP.Wire)
    (hp : Within ws p) : Within ws (drop26 N p) := by
  induction p generalizing N with
  | done => trivial
  | gate g p ih =>
    cases g <;> simp only [drop26] <;> split_ifs <;>
      first | exact ih _ hp.2 | exact ⟨hp.1, ih _ hp.2⟩
  | recordGate i v g p ih =>
    simp only [drop26] <;> split_ifs <;>
      first | exact ih _ hp.2 | exact ⟨hp.1, ih _ hp.2⟩
  | measure w p ih => exact ⟨hp.1, ih _ hp.2⟩

theorem drop26_slots {n s e} (N : Nat) (p : Straight n s e) :
    (drop26 N p).gateSlots ≤ p.gateSlots := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g <;> simp only [drop26] <;> split_ifs <;>
      simp only [Straight.gateSlots] <;> (have h1 := ih N; have h2 := ih (N - 1); omega)
  | recordGate i v g p ih =>
    simp only [drop26] <;> split_ifs <;>
      simp only [Straight.gateSlots] <;> (have h1 := ih N; have h2 := ih (N - 1); omega)
  | measure w p ih => simp only [drop26, Straight.gateSlots]; exact ih _

theorem drop26_t {n s e} (N : Nat) (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    ((drop26 N p).instantiate read history).tCount ≤ (p.instantiate read history).tCount := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g <;> simp only [drop26] <;> split_ifs <;>
      simp only [Straight.instantiate, AdaptiveCircuit.tCount] <;>
      (have h1 := ih N history; have h2 := ih (N - 1) history; omega)
  | recordGate i v g p ih =>
    simp only [drop26] <;> split_ifs <;>
      simp only [Straight.instantiate, AdaptiveCircuit.tCount] <;>
      (have h1 := ih N history; have h2 := ih (N - 1) history; omega)
  | measure w p ih =>
    simp only [drop26, Straight.instantiate, AdaptiveCircuit.tCount]
    exact max_le_max (ih _ _) (ih _ _)


def count26 {n s e} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p => (phase26 g).toNat + count26 p
  | .gate (.whenBit _ _ g) p => (phase26 g).toNat + count26 p
  | .recordGate _ _ g p => (phase26 g).toNat + count26 p
  | .measure _ p => count26 p

def spent26 {n s e} (N : Nat) : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p =>
      if decide (N>0) && phase26 g then 1 + spent26 (N-1) p else spent26 N p
  | .gate (.whenBit _ _ g) p =>
      if decide (N>0) && phase26 g then 1 + spent26 (N-1) p else spent26 N p
  | .recordGate _ _ g p =>
      if decide (N>0) && phase26 g then 1 + spent26 (N-1) p else spent26 N p
  | .measure _ p => spent26 N p

theorem spent26_eq {n s e} (N : Nat) (p : Straight n s e) :
    spent26 N p = min N (count26 p) := by
  induction p generalizing N with
  | done => simp [spent26,count26]
  | gate g p ih =>
    cases g <;> rename_i g
    all_goals
      cases hg : phase26 g <;> by_cases hn : 0 < N <;>
        simp only [spent26,count26,hg,hn,decide_true,decide_false,Bool.and_true,Bool.and_false,
          Bool.false_eq_true,if_false,if_true,Bool.toNat_true,Bool.toNat_false,zero_add]
      all_goals have hi := ih N; have hj := ih (N-1); omega
  | recordGate i v g p ih =>
    cases hg : phase26 g <;> by_cases hn : 0 < N <;>
      simp only [spent26,count26,hg,hn,decide_true,decide_false,Bool.and_true,Bool.and_false,
        Bool.false_eq_true,if_false,if_true,Bool.toNat_true,Bool.toNat_false,zero_add]
    all_goals have hi := ih N; have hj := ih (N-1); omega
  | measure w p ih => exact ih N

theorem phase26_weight (g : Gate) (hg : phase26 g = true) :
    weightedGate g = 1 ∧ weightedLiteral g = 1 := by
  cases g <;> simp only [phase26,Bool.false_eq_true] at hg
  case P dir k t =>
    have hk : k=26 := by simpa using hg
    subst hk
    constructor <;> rfl

theorem drop26_weight {n s e} (N : Nat) (p : Straight n s e) :
    weight4 (drop26 N p) + spent26 N p = weight4 p := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases h : (decide (N>0) && phase26 g) = true
      · have hg : phase26 g = true := by have ht := h; simp only [Bool.and_eq_true,decide_eq_true_eq] at ht; exact ht.2
        have hw := (phase26_weight g hg).2
        simp only [drop26,spent26,h,if_true,weight4,hw]
        have hi := ih (N-1); omega
      · have hf := Bool.eq_false_iff.mpr h
        simp only [drop26,spent26,hf,Bool.false_eq_true,if_false,weight4]
        have hi := ih N; omega
    | whenBit r v g =>
      by_cases h : (decide (N>0) && phase26 g) = true
      · have hg : phase26 g = true := by have ht := h; simp only [Bool.and_eq_true,decide_eq_true_eq] at ht; exact ht.2
        have hw := (phase26_weight g hg).1
        simp only [drop26,spent26,h,if_true,weight4,hw]
        have hi := ih (N-1); omega
      · have hf := Bool.eq_false_iff.mpr h
        simp only [drop26,spent26,hf,Bool.false_eq_true,if_false,weight4]
        have hi := ih N; omega
  | recordGate i v g p ih =>
    by_cases h : (decide (N>0) && phase26 g) = true
    · have hg : phase26 g = true := by have ht := h; simp only [Bool.and_eq_true,decide_eq_true_eq] at ht; exact ht.2
      have hw := (phase26_weight g hg).1
      simp only [drop26,spent26,h,if_true,weight4,hw]
      have hi := ih (N-1); omega
    · have hf := Bool.eq_false_iff.mpr h
      simp only [drop26,spent26,hf,Bool.false_eq_true,if_false,weight4]
      have hi := ih N; omega
  | measure w p ih => exact ih N
theorem drop26_added {n s e} (N : Nat) (p : Straight n s e) :
    added (drop26 N p) = added p := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases h : (decide (N>0) && phase26 g) = true
      · have hg : phase26 g = true := by
          have ht := h
          simp only [Bool.and_eq_true,decide_eq_true_eq] at ht
          exact ht.2
        cases g <;> simp only [phase26,Bool.false_eq_true] at hg
        simp only [drop26,h,if_true,added]
        exact ih (N-1)
      · have hf := Bool.eq_false_iff.mpr h
        cases g <;> simp only [drop26,hf,Bool.false_eq_true,if_false,added,ih]
    | whenBit r v g =>
      simp only [drop26]
      split_ifs <;> simp only [added]
      · exact ih (N-1)
      · exact ih N
  | recordGate i v g p ih =>
    simp only [drop26]
    split_ifs <;> simp only [added]
    · exact ih (N-1)
    · exact ih N
  | measure w p ih => exact ih N

theorem count26_trimN {n s e} (N : Nat) (p : Straight n s e) :
    count26 (trimN N p) = count26 p := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      cases g <;> try simp [trimN,largePhase,count26,phase26,ih]
      case P dir k t =>
        by_cases hk : k=26
        · subst hk; simp [trimN,largePhase,count26,phase26,ih]
        · split_ifs <;> simp [count26,phase26,hk,ih]
    | whenBit r v g =>
      cases g <;> try simp [trimN,largePhase,count26,phase26,ih]
      case P dir k t =>
        by_cases hk : k=26
        · subst hk; simp [trimN,largePhase,count26,phase26,ih]
        · split_ifs <;> simp [count26,phase26,hk,ih]
  | recordGate i v g p ih =>
    cases g <;> try simp [trimN,largePhase,count26,phase26,ih]
    case P dir k t =>
      by_cases hk : k=26
      · subst hk; simp [trimN,largePhase,count26,phase26,ih]
      · split_ifs <;> simp [count26,phase26,hk,ih]
  | measure w p ih => exact ih N

#print axioms drop26_weight
#print axioms drop26_added
#print axioms count26_trimN
theorem phase26_count_identity (g : Gate) :
    (phase26 g).toNat + (largePhase 26 g).toNat = (largePhase 25 g).toNat := by
  cases g <;> try rfl
  case P dir k t =>
    by_cases hk : k=26
    · subst hk; rfl
    · by_cases hg : 26<k
      · have h25 : 25<k := by omega
        simp [phase26,largePhase,hk,hg,h25]
      · have h25 : ¬25<k := by omega
        simp [phase26,largePhase,hk,hg,h25]

theorem count26_removed {n s e} (p : Straight n s e) :
    count26 p + removed 26 p = removed 25 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => simp only [count26,removed]; have h := phase26_count_identity g; omega
    | whenBit r v g => simp only [count26,removed]; have h := phase26_count_identity g; omega
  | recordGate i v g p ih => simp only [count26,removed]; have h := phase26_count_identity g; omega
  | measure w p ih => exact ih

#print axioms count26_removed
def droppedSlots25 : Nat → Nat → Nat
  | 0, _ => 0
  | width+1, prior => (prior - 24) + droppedSlots25 width (prior + 1)

def metadataDropped25 : List Nat → Nat → Nat
  | [], _ => 0
  | width :: ws, prior => droppedSlots25 width prior + metadataDropped25 ws (prior + width)

theorem removed25_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    removed 25 (p.append q) = removed 25 p + removed 25 q := by
  induction p with
  | done => simp [Straight.append, removed]
  | gate g p ih => cases g <;> simp [Straight.append, removed, ih, Nat.add_assoc]
  | recordGate i v g p ih => simp_all [Straight.append, removed, Nat.add_assoc]
  | measure w p ih => simp_all [Straight.append, removed]

theorem removed25_cast {n s e f} (p : Straight n s e) (h : e = f) :
    removed 25 (castFinish h p) = removed 25 p := by subst f; rfl

theorem removed25_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    removed 25 (reindexStraight f p) = removed 25 p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [reindexStraight, reindexGate, removed, ih]
    | whenBit r v g => simp_all [reindexStraight, reindexGate, removed, ih]
  | recordGate => simp_all [reindexStraight, removed]
  | measure => simp_all [reindexStraight, removed]

theorem removed25_feedback {n s e} (dir : ShorECDLP.PhaseDir) (w : ShorECDLP.Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    removed 25 (feedbackProgram dir w indices k p) =
      (indices.length - min indices.length (26 - k)) + removed 25 p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih =>
    simp only [feedbackProgram, removed, largePhase, ih, List.length_cons]
    by_cases hk : 25 < k
    · simp only [hk, decide_true, Bool.toNat_true]
      omega
    · simp only [hk, decide_false, Bool.toNat_false]
      omega

theorem removed25_prepare {n s e} (ws : List ShorECDLP.Wire) (p : Straight n s e) :
    removed 25 (prepareOuterBank ws p) = removed 25 p := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [prepareOuterBank, removed, largePhase] using ih

theorem removed_fourier25 (n : Nat) (dir : ShorECDLP.PhaseDir) (ws : List ShorECDLP.Wire)
    (start : Nat) (prior : List (Fin start)) :
    removed 25 (fourierProgram n dir ws start prior) = droppedSlots25 ws.length prior.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp [fourierProgram, removed25_cast, removed25_feedback,
      removed, ih, droppedSlots25]; omega

theorem weighted25_removed_framed {n s m k e f} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    removed 25 (Single.framed p q r h) = removed 25 p + removed 25 q + removed 25 r := by
  simp [Single.framed, removed, removed25_cast, removed25_append, largePhase, Nat.add_assoc]

theorem weighted25_removed_fixedEntry {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e) :
    removed 25 (Single.fixedEntry f p).program = removed 25 p := by
  unfold Single.fixedEntry
  exact removed25_reindex p _

theorem largePhase_mono (g : ShorECDLP.Gate) :
    (largePhase 26 g).toNat ≤ (largePhase 25 g).toNat := by
  cases g with
  | P dir k t =>
    simp only [largePhase]
    by_cases h : 26 < k
    · have h25 : 25 < k := by omega
      simp [h, h25, Bool.toNat_true]
    · simp [h, Bool.toNat_false, Nat.zero_le]
  | X t => simp only [largePhase, Bool.toNat_false] <;> omega
  | H t => simp only [largePhase, Bool.toNat_false] <;> omega
  | CX a b => simp only [largePhase, Bool.toNat_false] <;> omega
  | CCX a b c => simp only [largePhase, Bool.toNat_false] <;> omega

theorem largePhase_mono_true (g : ShorECDLP.Gate) (h : largePhase 26 g = true) :
    largePhase 25 g = true := by
  cases g with
  | P dir k t =>
    simp only [largePhase] at h ⊢
    have h26 : 26 < k := by simpa using h
    have h25 : 25 < k := by omega
    simp [h25]
  | X t => simp only [largePhase, Bool.false_eq_true] at h
  | H t => simp only [largePhase, Bool.false_eq_true] at h
  | CX a b => simp only [largePhase, Bool.false_eq_true] at h
  | CCX a b c => simp only [largePhase, Bool.false_eq_true] at h

theorem removed26_le_removed25 {n s e} (p : Straight n s e) :
    removed 26 p ≤ removed 25 p := by
  induction p with
  | done => simp only [removed]; omega
  | gate g p ih =>
    cases g with
    | literal g => simp only [removed]; exact Nat.add_le_add (largePhase_mono g) ih
    | whenBit r v g => simp only [removed]; exact Nat.add_le_add (largePhase_mono g) ih
  | recordGate i v g p ih => simp only [removed]; exact Nat.add_le_add (largePhase_mono g) ih
  | measure w p ih => simp only [removed]; exact ih

theorem droppedSlots_mono (w prior : Nat) :
    _root_.droppedSlots26 w prior ≤ droppedSlots25 w prior := by
  induction w generalizing prior with
  | zero => simp only [_root_.droppedSlots26, droppedSlots25]; omega
  | succ w ih =>
    simp only [_root_.droppedSlots26, droppedSlots25]
    exact Nat.add_le_add (by omega) (ih (prior + 1))

theorem metadataDropped_mono (ws : List Nat) (p : Nat) :
    _root_.metadataDropped26 ws p ≤ metadataDropped25 ws p := by
  induction ws generalizing p with
  | nil => simp only [_root_.metadataDropped26, metadataDropped25]; omega
  | cons w ws ih =>
    simp only [_root_.metadataDropped26, metadataDropped25]
    exact Nat.add_le_add (droppedSlots_mono w p) (ih (p + w))

/-- The count difference of the two cutoffs accumulates through `Single.axis`. -/
theorem removed_axis_diff [body : Single.WindowBody] [ledger : Single.ProducerResources body] {n}
    (ws : List (Single.Window n)) (widths : List Nat)
    (hw : List.Forall₂ (fun w c => w.wires.length = c) ws widths)
    (start : Nat) (prior : List (Fin start)) :
    metadataDropped25 widths prior.length - _root_.metadataDropped26 widths prior.length ≤
      removed 25 (Single.axis ws start prior) - removed 26 (Single.axis ws start prior) := by
  induction ws generalizing widths start with
  | nil =>
    cases hw
    simp only [metadataDropped25, _root_.metadataDropped26, Single.axis, removed]
    omega
  | cons w ws ih =>
    cases hw with
    | cons head tail =>
      rename_i c widths
      simp only [Single.axis, removed25_cast, _root_.removed26_cast,
        removed25_append, _root_.removed26_append, removed25_prepare,
        _root_.removed26_prepare, removed_fourier25,
        _root_.removed_fourier26, bankPrior_length]
      have ht := ih widths tail (start + w.count + w.wires.length)
        (Single.nextPrior w.count w.wires.length prior)
      rw [Single.nextPrior_length] at ht
      simp only [metadataDropped25, _root_.metadataDropped26]
      have hA := removed26_le_removed25 (w.program start)
      have hR := removed26_le_removed25
        (Single.axis ws (start + w.count + c) (Single.nextPrior w.count c prior))
      have hD := droppedSlots_mono c prior.length
      have hm := metadataDropped_mono widths (prior.length + c)
      rw [head] at *
      omega


variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]

theorem exact_band_metadata :
    (metadataDropped25 [9] 0 - _root_.metadataDropped26 [9] 0) +
    (metadataDropped25 [8] 0 - _root_.metadataDropped26 [8] 0) +
    (metadataDropped25 leftWidthsBody 9 - _root_.metadataDropped26 leftWidthsBody 9) +
    (metadataDropped25 rightWidthsBody 8 - _root_.metadataDropped26 rightWidthsBody 8) = 418 := by
  decide +kernel

theorem axes_band_count (impl : Implementation) (start : Nat) :
    418 ≤ (removed 25 (mixHead impl.headA start) +
      removed 25 (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) start)) -
      (removed 26 (mixHead impl.headA start) +
      removed 26 (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) start)) := by
  have hA := removed_axis_diff ([impl.headA]) ([9]) (headA_width_relation impl) start List.nil
  have hB := removed_axis_diff ([impl.headB]) ([8]) (headB_width_relation impl)
    (mixS1 impl.headA start) List.nil
  have hL := removed_axis_diff (leftBodies impl) leftWidthsBody (left_width_relation impl)
    (mixS2 impl.headA impl.headB start) (mixPriorL impl.headA impl.headB start)
  have hR := removed_axis_diff (rightBodies impl) rightWidthsBody (right_width_relation impl)
    (mixS3 impl.headA impl.headB (leftBodies impl) start)
    (mixPriorR impl.headA impl.headB (leftBodies impl) start)
  rw [mixPriorL_length] at hL
  rw [mixPriorR_length] at hR
  simp only [List.length_nil] at hA hB
  have hb := exact_band_metadata
  have m1 := removed26_le_removed25 (Single.axis ([impl.headA]) start List.nil)
  have m2 := removed26_le_removed25 (Single.axis ([impl.headB]) (mixS1 impl.headA start) List.nil)
  have m3 := removed26_le_removed25 (Single.axis (leftBodies impl)
    (mixS2 impl.headA impl.headB start) (mixPriorL impl.headA impl.headB start))
  have m4 := removed26_le_removed25 (Single.axis (rightBodies impl)
    (mixS3 impl.headA impl.headB (leftBodies impl) start)
    (mixPriorR impl.headA impl.headB (leftBodies impl) start))
  simp only [mixHead, mixTail, removed25_append, _root_.removed26_append]
  omega

theorem fullProgram_band_count (impl : Implementation) (reset : List Wire) :
    418 ≤ removed 25 (fullProgram impl reset) - removed 26 (fullProgram impl reset) := by
  have h := axes_band_count impl 0
  have hz := removed26_le_removed25
    (resetProgram 1769472 (mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0) reset)
  have hro := removed26_le_removed25 (readout impl reset)
  simp only [fullProgram, removed25_append, _root_.removed26_append,
    Width16Schedule.program, weighted25_removed_framed, _root_.weighted26_removed_framed]
  omega


theorem source_count26 (impl : Implementation) (reset : List Wire) :
    418 ≤ count26 (sourceEntry impl reset).program := by
  have hb := fullProgram_band_count impl reset
  have he := count26_removed (sourceEntry impl reset).program
  have h25 : removed 25 (sourceEntry impl reset).program = removed 25 (fullProgram impl reset) := by
    unfold sourceEntry
    exact weighted25_removed_fixedEntry _ _
  have h26 : removed 26 (sourceEntry impl reset).program = removed 26 (fullProgram impl reset) := by
    unfold sourceEntry
    exact _root_.weighted26_removed_fixedEntry _ _
  rw [h25,h26] at he
  omega

theorem source_spent26 (impl : Implementation) (reset : List Wire) :
    spent26 397 (trimN 417 (sourceEntry impl reset).program) = 397 := by
  rw [spent26_eq,count26_trimN]
  have h := source_count26 impl reset
  omega

#print axioms source_spent26
end
end ShorECDLP.Entrant.ExtraPhase
