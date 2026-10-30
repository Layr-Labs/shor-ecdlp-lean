import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd
import ShorECDLP.Challenge.StraightLine
import ShorECDLP.Framework.Quantum.AdaptiveFrame
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapperCounts
import ShorECDLP.Framework.Quantum.AdaptiveDisjoint

section

/-! Measurement-assisted Toffoli synthesis using a reusable clean ancillary wire.
The temporary AND follows Gidney, Quantum 2, 74 (2018). Its four T rotations and
one S rotation cost five in the challenge's P-count model. -/
namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Paper2607_13816
noncomputable section
set_option maxHeartbeats 200000

attribute [local irreducible] Quantum.applyGate Quantum.run Quantum.ket
set_option linter.unusedSimpArgs false


private theorem upd_twice (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]
private theorem upd_self (s : BasisState) (q : Wire) : s[q ↦ s q] = s := by
  funext w
  by_cases h : w = q <;> simp [upd, h]

private theorem phase_square (dir : PhaseDir) (k : Nat) :
    phaseCoeff dir (k+1)^2 = phaseCoeff dir k := by
  rw [phaseCoeff, ← Complex.exp_nat_mul, phaseCoeff]
  congr 1
  cases dir <;> simp only [phaseAngle, pow_succ] <;> push_cast <;> field_simp

private theorem phase_two : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

private theorem phase_two_inverse : phaseCoeff .inverse 2 = -Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_neg_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

/-- Diagonal phase on the XOR of a control and target. -/
def xorPhase (dir : PhaseDir) (a q : Wire) : Circuit :=
  [.CX a q, .P dir 3 q, .CX a q]

private theorem xorPhase_ket (dir : PhaseDir) (a q : Wire) (ha : a ≠ q)
    (s : BasisState) :
    Quantum.run (xorPhase dir a q) (ket s) =
      (if s q ^^ s a then phaseCoeff dir 3 else 1) • ket s := by
  simp only [xorPhase, Quantum.run_cons, Quantum.run_nil, applyGate_CX_ket,
    applyGate_P_ket, map_smul, upd_same, upd_other _ _ _ ha,
    upd_twice, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, upd_self]

/-- Four diagonal parity phases; additional Clifford CNOTs keep the proof modular. -/
def parityPhase (a b q : Wire) : Circuit :=
  [.P .forward 3 q] ++ xorPhase .inverse a q ++
    [.CX a q] ++ xorPhase .forward b q ++ [.CX a q] ++ xorPhase .inverse b q

private theorem parityPhase_ket (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q)
    (s : BasisState) :
    Quantum.run (parityPhase a b q) (ket s) =
      (if s a && s b then (if s q then Complex.I else -Complex.I) else 1) • ket s := by
  have hmul := phaseCoeff_mul_adjoint .forward 3
  have himul := phaseCoeff_adjoint_mul .forward 3
  have hsq := phase_square .forward 2
  have hisq := phase_square .inverse 2
  rw [phase_two] at hsq
  rw [phase_two_inverse] at hisq
  change phaseCoeff .forward 3 * phaseCoeff .inverse 3 = 1 at hmul
  change phaseCoeff .inverse 3 * phaseCoeff .forward 3 = 1 at himul
  simp only [parityPhase, Quantum.run_append, Quantum.run_singleton,
    applyGate_P_ket, applyGate_CX_ket, map_smul, xorPhase_ket _ a q ha,
    xorPhase_ket _ b q hb, upd_same, upd_other _ _ _ ha, upd_other _ _ _ hb,
    upd_twice, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, upd_self, smul_smul]
  cases ha' : s a <;> cases hb' : s b <;> cases hq : s q <;>
    simp only [ha', hb', hq, Bool.false_and, Bool.true_and,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, mul_one, one_mul,
      ← pow_two, hsq, hisq, mul_assoc, hmul, himul, one_pow]

/-- Exact temporary AND on a clean target; S is counted as one P rotation. -/
def andCompute (a b q : Wire) : Circuit :=
  [.H q] ++ parityPhase a b q ++ [.H q, .P .forward 2 q]

private theorem invSqrtTwo_square :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1/2 : ℂ) := by
  have h : Real.sqrt 2 ≠ 0 := by positivity
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    field_simp
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa using hc

/-- No data-dependent phase remains on the clean-target subspace. -/
theorem andCompute_ket (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q)
    (s : BasisState) (hq : s q = false) :
    Quantum.run (andCompute a b q) (ket s) = ket (s[q ↦ s a && s b]) := by
  have hs : s[q ↦ false] = s := by simpa only [hq] using upd_self s q
  have hsq : ((↑(Real.sqrt 2) : ℂ)⁻¹)^2 = (1/2 : ℂ) := by
    simpa [pow_two] using invSqrtTwo_square
  simp only [andCompute, Quantum.run_append, Quantum.run_cons, Quantum.run_nil,
    LinearMap.id_coe, id_eq, applyGate_H_ket, map_add, map_smul,
    parityPhase_ket a b q ha hb, upd_other _ _ _ ha, upd_other _ _ _ hb,
    upd_same, hq, Bool.false_eq_true, if_false, if_true, mul_one,
    applyGate_P_ket, phase_two, upd_twice]
  cases ha' : s a <;> cases hb' : s b <;>
    simp [ha', hb', hs, hq, smul_add, smul_smul, mul_add, add_mul,
      invSqrtTwo_square, Complex.I_mul_I]
  all_goals match_scalars <;> ring_nf
  all_goals norm_num [hsq, Complex.I_sq]

/-- One branch of AND-compute, target update, and corrected X erasure. -/
def toffoliBranch (a b t q : Wire) (outcome : Bool) : State →ₗ[ℂ] State :=
  (Quantum.run (if outcome then controlledZ a b else [])).comp
    ((xResetKraus q outcome).comp (Quantum.run (andCompute a b q ++ [.CX q t])))

private theorem reset_after_update (s : BasisState) (q t : Wire) (hqt : q ≠ t)
    (hq : s q = false) (v z : Bool) :
    s[q ↦ v][t ↦ z][q ↦ false] = s[t ↦ z] := by
  funext w
  by_cases hwq : w = q <;> by_cases hwt : w = t <;> simp_all [upd]

/-- Both outcomes have the same data-independent amplitude, with no residual phase. -/
theorem toffoliBranch_ket (a b t q : Wire) (outcome : Bool)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (hat : a ≠ t) (hbt : b ≠ t) (hqt : q ≠ t)
    (s : BasisState) (hq : s q = false) :
    toffoliBranch a b t q outcome (ket s) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • applyGate (.CCX a b t) (ket s) := by
  simp only [toffoliBranch, LinearMap.comp_apply, Quantum.run_append,
    andCompute_ket a b q haq hbq s hq, Quantum.run_singleton, applyGate_CX_ket,
    upd_same, upd_other _ _ _ (Ne.symm hqt), xResetKraus_ket,
    upd_other _ _ _ hqt, reset_after_update s q t hqt hq, map_smul,
    applyGate_CCX_ket, xResetCoeff]
  cases outcome <;> simp only [Bool.false_eq_true, if_false, if_true,
    Quantum.run_nil, run_controlledZ_ket a b _ hab,
    upd_other _ _ _ hat, upd_other _ _ _ hbt]
  all_goals cases ha : s a <;> cases hb : s b <;>
    simp [ha, hb, smul_smul]

/-- The primitive also holds on arbitrary supported superpositions. -/
theorem toffoliBranch_supported (a b t q : Wire) (outcome : Bool)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (hat : a ≠ t) (hbt : b ≠ t) (hqt : q ≠ t)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    toffoliBranch a b t q outcome psi =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • applyGate (.CCX a b t) psi := by
  have h : BranchCoherentOn (applyGate (.CCX a b t)) (fun s => s q = false)
      ⟨[], toffoliBranch a b t q outcome⟩ (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) :=
    fun s hs => toffoliBranch_ket a b t q outcome hab haq hbq hat hbt hqt s hs
  exact h.on_supported hpsi

/-- Every rotation, including S, is charged. -/
theorem andCompute_tCount (a b q : Wire) : ShorECDLP.tCount (andCompute a b q) = 5 := by
  rfl

theorem andCompute_wellFormed (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q) :
    CircuitWellFormed (andCompute a b q) := by
  simp [andCompute, parityPhase, xorPhase, CircuitWellFormed, Gate.WellFormed, ha, hb]

end
end ShorECDLP.Entrant.AndGadget
end

section

/-! A static record-preserving compiler for measurement-assisted Toffoli gates. -/
namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- The compiler records the location of every original measurement. -/
structure Lowered (n oldFinish start : Nat) where
  finish : Nat
  program : Straight n start finish
  records : Fin oldFinish → Fin finish

/-- Execute a fixed literal prefix. -/
def literals {n s e : Nat} (gs : Circuit) (next : Straight n s e) : Straight n s e :=
  gs.foldr (fun g tail => .gate (.literal g) tail) next

/-- The selected phase correction uses Clifford gates only. -/
def toffoliPrefix {n s e : Nat} (a b target scratch : Wire)
    (next : Straight n (s+1) e) : Straight n s e :=
  literals (andCompute a b scratch ++ [.CX scratch target])
    (.measure scratch
      (.recordGate (Fin.last s) true (.H b)
        (.recordGate (Fin.last s) true (.CX a b)
          (.recordGate (Fin.last s) true (.H b) next))))

/-- Only unconditional literal Toffolis are replaced. Original conditional gates
and their record references remain exactly represented. -/
def lower {n oldStart oldFinish : Nat} (scratch : Wire)
    (p : Straight n oldStart oldFinish) (start : Nat)
    (records : Fin oldStart → Fin start) : Lowered n oldFinish start :=
  match p with
  | .done => ⟨start, .done, records⟩
  | .gate (.literal (.CCX a b t)) next =>
      let r := lower scratch next (start+1) (fun i => (records i).castSucc)
      ⟨r.finish, toffoliPrefix a b t scratch r.program, r.records⟩
  | .gate g next =>
      let r := lower scratch next start records
      ⟨r.finish, .gate g r.program, r.records⟩
  | .recordGate i v g next =>
      let r := lower scratch next start records
      ⟨r.finish, .recordGate (records i) v g r.program, r.records⟩
  | .measure w next =>
      let r := lower scratch next (start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc))
      ⟨r.finish, .measure w r.program, r.records⟩

/-- Number of new records, independent of all constant values and outcomes. -/
def added {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal (.CCX _ _ _)) next => 1 + added next
  | .gate _ next => added next
  | .recordGate _ _ _ next => added next
  | .measure _ next => added next

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section

/-- Backward evaluation against a predicate on the complete record. -/
def expectation {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) : ℝ :=
  match p with
  | .done => if accept history then normSq psi else 0
  | .gate g next => expectation read next history (Quantum.run (g.instantiate read) psi) accept
  | .recordGate i v g next => expectation read next history
      (Quantum.run (if history i = v then [g] else []) psi) accept
  | .measure w next =>
      expectation read next (Fin.lastCases false history) (xResetKraus w false psi) accept +
      expectation read next (Fin.lastCases true history) (xResetKraus w true psi) accept

/-- The static record cost of an appended program is additive. -/
theorem added_append {n s m e : Nat} (p : Straight n s m) (q : Straight n m e) :
    added (p.append q) = added p + added q := by
  induction p with
  | done => simp [Straight.append, added]
  | gate g p ih =>
      cases g with
      | literal g => cases g <;> simp [Straight.append, added, ih, Nat.add_assoc]
      | whenBit r v g => simp [Straight.append, added, ih]
  | recordGate i v g p ih => exact ih q
  | measure w p ih => exact ih q

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- The new cursor is the old remaining record count plus one per lowered gate. -/
theorem lower_finish {n s e : Nat} (scratch : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) :
    (lower scratch p start records).finish + s = start + e + added p := by
  induction p generalizing start with
  | done => simp [lower, added, Nat.add_comm]
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g <;> simp only [lower, added]
          all_goals have h := ih (start := start) records
          all_goals try omega
          exact (by have h := ih (start := start+1) (fun i => (records i).castSucc); omega)
      | whenBit r v g => exact ih start records
  | recordGate i v g p ih => exact ih start records
  | measure w p ih =>
      simp only [lower, added]
      have h := ih (start := start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc))
      omega

/-- Old references into the initial prefix keep their values. -/
theorem lower_initial {n s e : Nat} (scratch : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (i : Fin s) :
    ((lower scratch p start records).records (i.castLE p.cursor_mono)).val = (records i).val := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g <;> simp only [lower]
          all_goals apply ih
      | whenBit r v g => exact ih start records i
  | recordGate j v g p ih => exact ih start records i
  | measure w p ih =>
      simp only [lower]
      have h := ih (start := start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) i.castSucc
      simpa only [Fin.castLE, Fin.val_castSucc, Fin.lastCases_castSucc] using h

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private theorem state_normSq_smul (c : ℂ) (psi : State) :
    normSq (c • psi) = Complex.normSq c * normSq psi := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

theorem expectation_smul {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (c : ℂ) :
    expectation read p history (c • psi) accept =
      Complex.normSq c * expectation read p history psi accept := by
  induction p generalizing psi with
  | done => simp only [expectation]; split <;> simp [state_normSq_smul]
  | gate g p ih => simp only [expectation, map_smul, ih]
  | recordGate i v g p ih => simp only [expectation, map_smul, ih]
  | measure w p ih => simp only [expectation, map_smul, ih, mul_add]

theorem expectation_literals {n s e : Nat} (read : ConstantBit n → Bool)
    (gs : Circuit) (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read (literals gs p) history psi accept =
      expectation read p history (Quantum.run gs psi) accept := by
  induction gs generalizing psi with
  | nil => simp [literals, Quantum.run_nil]
  | cons g gs ih =>
      simp only [literals, List.foldr_cons, expectation, TemplateGate.instantiate,
        Quantum.run_nil, Quantum.run_cons]
      exact ih (applyGate g psi)

theorem expectation_toffoliPrefix {n s e : Nat} (read : ConstantBit n → Bool)
    (a b t q : Wire) (p : Straight n (s+1) e) (history : Fin s → Bool)
    (psi : State) (accept : (Fin e → Bool) → Bool) :
    expectation read (toffoliPrefix a b t q p) history psi accept =
      expectation read p (Fin.lastCases false history) (toffoliBranch a b t q false psi) accept +
      expectation read p (Fin.lastCases true history) (toffoliBranch a b t q true psi) accept := by
  simp only [toffoliPrefix, expectation_literals, expectation, Fin.lastCases_last,
    Bool.false_eq_true, if_false, if_true, Quantum.run_nil,
    toffoliBranch, LinearMap.comp_apply, controlledZ,
    Quantum.run_cons, Quantum.run_nil]

/-- The source never accesses the new ancillary wire. -/
def Fresh {n s e : Nat} (q : Wire) : Straight n s e → Prop
  | .done => True
  | .gate (.literal g) p => q ∉ gateWires g ∧ Fresh q p
  | .gate (.whenBit _ _ g) p => q ∉ gateWires g ∧ Fresh q p
  | .recordGate _ _ g p => q ∉ gateWires g ∧ Fresh q p
  | .measure w p => q ≠ w ∧ Fresh q p

private theorem gate_frame (q : Wire) (gs : Circuit) (hq : q ∉ circuitWires gs)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (Quantum.run gs psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary gs .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[], Quantum.run gs⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hpsi
  exact h

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private theorem reset_frame (q w : Wire) (hq : q ≠ w) (outcome : Bool)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (xResetKraus w outcome psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[outcome], xResetKraus w outcome⟩ ?_ psi hpsi
  cases outcome <;>
    simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_append, List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem half_amplitude :
    Complex.normSq (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1/2 : ℝ) := by
  simp only [Complex.normSq_ofReal]
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- Compilation preserves every predicate on the original measurement record. -/
theorem lower_expectation {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (newHistory : Fin start → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool)
    (hmap : newHistory ∘ records = history) (hf : Fresh q p) (hwf : p.WellFormed)
    (hpsi : SupportedOn (fun s => s q = false) psi) :
    expectation read (lower q p start records).program newHistory psi
        (fun h => accept (h ∘ (lower q p start records).records)) =
      expectation read p history psi accept := by
  induction p generalizing start psi with
  | done => simp only [lower, expectation, hmap]
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              obtain ⟨hf, htail⟩ := hf
              have hqs : q ≠ a ∧ q ≠ b ∧ q ≠ t := by simpa [gateWires] using hf
              have hw : a ≠ b ∧ a ≠ t ∧ b ≠ t := hwf.1
              have hp : SupportedOn (fun s => s q = false) (applyGate (.CCX a b t) psi) := by
                simpa only [Quantum.run_singleton] using gate_frame q ([.CCX a b t] : Circuit)
                  (by simpa [circuitWires] using hf) psi hpsi
              simp only [lower, expectation_toffoliPrefix]
              rw [toffoliBranch_supported a b t q false hw.1 hqs.1.symm hqs.2.1.symm
                    hw.2.1 hw.2.2 hqs.2.2 psi hpsi,
                  toffoliBranch_supported a b t q true hw.1 hqs.1.symm hqs.2.1.symm
                    hw.2.1 hw.2.2 hqs.2.2 psi hpsi,
                  expectation_smul, expectation_smul]
              have hm (outcome : Bool) :
                  (Fin.lastCases outcome newHistory) ∘ (fun i => (records i).castSucc) = history := by
                simpa only [Function.comp_def, Fin.lastCases_castSucc] using hmap
              rw [ih (start+1) (fun i => (records i).castSucc) history
                    (Fin.lastCases false newHistory) _ accept (hm false) htail hwf.2 hp,
                  ih (start+1) (fun i => (records i).castSucc) history
                    (Fin.lastCases true newHistory) _ accept (hm true) htail hwf.2 hp]
              simp only [expectation, TemplateGate.instantiate, Quantum.run_singleton, half_amplitude]
              ring
          | X t | H t | CX a t | P dir k t =>
              simp only [lower, expectation]
              apply ih start records history newHistory _ accept hmap hf.2 hwf.2
              apply gate_frame q _ ?_ psi hpsi
              simpa [TemplateGate.instantiate, circuitWires] using hf.1
      | whenBit r v g =>
          simp only [lower, expectation]
          apply ih start records history newHistory _ accept hmap hf.2 hwf.2
          apply gate_frame q _ ?_ psi hpsi
          simp only [TemplateGate.instantiate]
          split
          · simpa [circuitWires] using hf.1
          · simp [circuitWires]
  | recordGate i v g p ih =>
      have hm : newHistory (records i) = history i := congrFun hmap i
      simp only [lower, expectation, hm]
      apply ih start records history newHistory _ accept hmap hf.2 hwf.2
      apply gate_frame q _ ?_ psi hpsi
      split
      · simpa [circuitWires] using hf.1
      · simp [circuitWires]
  | measure w p ih =>
      simp only [lower, expectation]
      congr 1
      all_goals
        apply ih (start+1)
          (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) _ _ _ accept ?_ hf.2 hwf
          (reset_frame q w hf.1 _ psi hpsi)
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        all_goals simp [Function.comp_def, ← hmap]

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
set_option linter.unusedSimpArgs false

theorem literals_slots {n s e : Nat} (gs : Circuit) (p : Straight n s e) :
    (literals gs p).gateSlots = gs.length + p.gateSlots := by
  induction gs with
  | nil => simp [literals]
  | cons g gs ih =>
      change 1 + (literals gs p).gateSlots = (gs.length+1) + p.gateSlots
      rw [ih]
      omega

theorem toffoliPrefix_slots {n s e : Nat} (a b t q : Wire) (p : Straight n (s+1) e) :
    (toffoliPrefix a b t q p).gateSlots = 19 + p.gateSlots := by
  simp [toffoliPrefix, literals_slots, andCompute, parityPhase, xorPhase, Straight.gateSlots]
  omega

theorem lower_slots {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) :
    (lower q p start records).program.gateSlots = p.gateSlots + 18 * added p := by
  induction p generalizing start with
  | done => simp [lower, added, Straight.gateSlots]
  | gate g p ih =>
      cases g with
      | literal g => cases g <;>
          simp [lower, added, Straight.gateSlots, toffoliPrefix_slots, ih] <;> omega
      | whenBit r v g => simp [lower, added, Straight.gateSlots, ih, Nat.add_assoc]
  | recordGate i v g p ih => simp [lower, added, Straight.gateSlots, ih, Nat.add_assoc]
  | measure w p ih => exact ih _ _

theorem literals_wellFormed {n s e : Nat} (gs : Circuit) (p : Straight n s e)
    (hg : CircuitWellFormed gs) (hp : p.WellFormed) : (literals gs p).WellFormed := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp), ih (fun k hk => hg k (by simp [hk]))⟩

theorem lower_wellFormed {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (hf : Fresh q p) (hp : p.WellFormed) :
    (lower q p start records).program.WellFormed := by
  induction p generalizing start with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hq : q ≠ a ∧ q ≠ b ∧ q ≠ t := by simpa [gateWires] using hf.1
              have hw : a ≠ b ∧ a ≠ t ∧ b ≠ t := hp.1
              apply literals_wellFormed
              · exact (circuitWellFormed_append _ _).mpr
                  ⟨andCompute_wellFormed a b q hq.1.symm hq.2.1.symm,
                    by simpa [CircuitWellFormed, Gate.WellFormed] using hq.2.2⟩
              · exact ⟨trivial, hw.1, trivial, ih _ _ hf.2 hp.2⟩
          | X t | H t | CX a t | P dir k t => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
      | whenBit r v g => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
  | recordGate i v g p ih => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
  | measure w p ih => exact ih _ _ hf.2 hp

theorem literals_t {n s e : Nat} (read : ConstantBit n → Bool)
    (gs : Circuit) (p : Straight n s e) (history : Fin s → Bool) :
    ((literals gs p).instantiate read history).tCount =
      ShorECDLP.tCount gs + (p.instantiate read history).tCount := by
  induction gs with
  | nil => simp [literals, ShorECDLP.tCount]
  | cons g gs ih =>
      change ShorECDLP.tCount [g] + ((literals gs p).instantiate read history).tCount = _
      rw [ih]
      simp [ShorECDLP.tCount, Nat.add_assoc]

theorem toffoliPrefix_t {n s e : Nat} (read : ConstantBit n → Bool)
    (a b t q : Wire) (p : Straight n (s+1) e) (history : Fin s → Bool) :
    ((toffoliPrefix a b t q p).instantiate read history).tCount =
      5 + max (p.instantiate read (Fin.lastCases false history)).tCount
        (p.instantiate read (Fin.lastCases true history)).tCount := by
  simp [toffoliPrefix, literals_t, andCompute, parityPhase, xorPhase,
    Straight.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount, tCost]

/-- Exact T reduction, including arbitrary original record-controlled gates. -/
theorem lower_t {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (newHistory : Fin start → Bool)
    (hmap : newHistory ∘ records = history) :
    ((lower q p start records).program.instantiate read newHistory).tCount + 2 * added p =
      (p.instantiate read history).tCount := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hm (outcome : Bool) :
                  (Fin.lastCases outcome newHistory) ∘ (fun i => (records i).castSucc) = history := by
                simpa only [Function.comp_def, Fin.lastCases_castSucc] using hmap
              have h0 := ih (start+1) (fun i => (records i).castSucc) history
                (Fin.lastCases false newHistory) (hm false)
              have h1 := ih (start+1) (fun i => (records i).castSucc) history
                (Fin.lastCases true newHistory) (hm true)
              simp only [lower, toffoliPrefix_t, added, Straight.instantiate,
                TemplateGate.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tCost] at *
              omega
          | X t | H t | CX a t | P dir k t =>
              have h := ih start records history newHistory hmap
              simp only [lower, added, Straight.instantiate, TemplateGate.instantiate,
                AdaptiveCircuit.tCount] at *
              omega
      | whenBit r v g =>
          have h := ih start records history newHistory hmap
          simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount] at *
          omega
  | recordGate i v g p ih =>
      have h := ih start records history newHistory hmap
      have hm : newHistory (records i) = history i := congrFun hmap i
      simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount, hm] at *
      omega
  | measure w p ih =>
      have hm (outcome : Bool) : (Fin.lastCases outcome newHistory) ∘
          (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) =
          Fin.lastCases outcome history := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        all_goals simp [Function.comp_def, ← hmap]
      have h0 := ih (start+1) _ (Fin.lastCases false history) (Fin.lastCases false newHistory) (hm false)
      have h1 := ih (start+1) _ (Fin.lastCases true history) (Fin.lastCases true newHistory) (hm true)
      simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount] at *
      omega

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private def prependBranch (outcome : Option Bool) (before : State →ₗ[ℂ] State)
    (branch : InstrumentBranch) : InstrumentBranch :=
  ⟨outcome.toList ++ branch.history, branch.kraus.comp before⟩
private theorem run_unitary (gs : Circuit) (tail : AdaptiveCircuit) :
    (AdaptiveCircuit.unitary gs tail).run = tail.run.map (prependBranch none (Quantum.run gs)) := rfl
private theorem run_measure (q : Wire) (a b : AdaptiveCircuit) :
    (AdaptiveCircuit.xMeasureReset q a b).run =
      a.run.map (prependBranch (some false) (xResetKraus q false)) ++
      b.run.map (prependBranch (some true) (xResetKraus q true)) := rfl

/-- Sum probability mass selected by an arbitrary transcript predicate. -/
def selectedMass (I : Instrument) (psi : State) (accept : List Bool → Bool) : ℝ :=
  (I.map (fun b => if accept b.history then normSq (b.kraus psi) else 0)).sum

theorem selectedMass_filter (I : Instrument) (psi : State) (accept : List Bool → Bool) :
    selectedMass I psi accept = Instrument.bornMass (I.filter (fun b => accept b.history)) psi := by
  induction I with
  | nil => rfl
  | cons b I ih =>
      cases hb : accept b.history <;> simp [selectedMass, Instrument.bornMass, hb] at * <;> exact ih

private theorem selectedMass_prefix (I : Instrument) (outcome : Option Bool)
    (before : State →ₗ[ℂ] State) (psi : State) (accept : List Bool → Bool) :
    selectedMass (I.map (prependBranch outcome before)) psi accept =
      selectedMass I (before psi) (fun xs => accept (outcome.toList ++ xs)) := by
  simp [selectedMass, prependBranch, List.map_map, Function.comp_def, LinearMap.comp_apply]

/-- Read the initial prefix followed by the newly emitted record. -/
def fullHistory {s : Nat} (e : Nat) (history : Fin s → Bool) (tail : List Bool) : Fin e → Bool :=
  fun i => (List.ofFn history ++ tail).getD i.val false

private theorem fullHistory_nil {s : Nat} (history : Fin s → Bool) :
    fullHistory s history List.nil = history := by
  funext i
  simp [fullHistory, i.isLt]

private theorem fullHistory_cons {s e : Nat} (history : Fin s → Bool) (b : Bool) (tail : List Bool) :
    fullHistory e history (b :: tail) = fullHistory e (Fin.lastCases b history) tail := by
  unfold fullHistory
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append,
    List.append_assoc, List.singleton_append]

/-- The recursive expectation is precisely the protected instrument Born mass. -/
theorem expectation_selectedMass {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read p history psi accept =
      selectedMass (p.instantiate read history).run psi (fun xs => accept (fullHistory e history xs)) := by
  induction p generalizing psi with
  | done => simp [expectation, Straight.instantiate, AdaptiveCircuit.run,
      selectedMass, fullHistory_nil]
  | gate g p ih =>
      simp only [expectation, Straight.instantiate, run_unitary, selectedMass_prefix,
        Option.toList_none, List.nil_append]
      exact ih history _ accept
  | recordGate i v g p ih =>
      simp only [expectation, Straight.instantiate, run_unitary, selectedMass_prefix,
        Option.toList_none, List.nil_append]
      exact ih history _ accept
  | measure w p ih =>
      simp only [expectation, Straight.instantiate, run_measure]
      rw [show ∀ a b : Instrument, selectedMass (a ++ b) psi
          (fun xs => accept (fullHistory _ history xs)) =
          selectedMass a psi (fun xs => accept (fullHistory _ history xs)) +
          selectedMass b psi (fun xs => accept (fullHistory _ history xs)) by
        intros; simp [selectedMass]]
      simp only [selectedMass_prefix, Option.toList_some, List.singleton_append, fullHistory_cons]
      rw [ih, ih]

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

/-- Invalid old positions remain invalid after record remapping. -/
def redirect {e f : Nat} (records : Fin e → Fin f) (i : Nat) : Nat :=
  if h : i < e then (records ⟨i,h⟩).val else f

def redirectedLayout {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout) : DecodeLayout where
  kind := layout.kind
  params := layout.params
  trials := layout.trials.map (fun t => ⟨t.left.map (redirect records), t.right.map (redirect records)⟩)
  trials_le := by simpa using layout.trials_le

private theorem redirect_get {e f : Nat} (records : Fin e → Fin f)
    (xs : List Bool) (hlen : xs.length = f) (i : Nat) :
    xs[redirect records i]? =
      (List.ofFn (fun j : Fin e => xs.getD (records j).val false))[i]? := by
  by_cases hi : i < e
  · have hr : (records ⟨i,hi⟩).val < xs.length := by simp [hlen]
    simp [redirect, hi, List.getElem?_eq_getElem hr]
  · have he : e ≤ i := by omega
    simp [redirect, hi, List.getElem?_eq_none (by omega : xs.length ≤ f)]

theorem readWord_redirect {e f : Nat} (records : Fin e → Fin f)
    (xs : List Bool) (hlen : xs.length = f) (positions : List Nat) :
    readWord xs (positions.map (redirect records)) =
      readWord (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) positions := by
  induction positions with
  | nil => rfl
  | cons i positions ih => simp only [List.map_cons, readWord, redirect_get records xs hlen, ih]

theorem candidates_redirect {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout)
    (xs : List Bool) (hlen : xs.length = f) :
    candidates (redirectedLayout records layout) xs =
      candidates layout (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) := by
  simp only [candidates, redirectedLayout, List.flatMap_map]
  apply List.flatMap_congr
  intro t ht
  cases layout.kind <;>
    simp [decodeTrial, trialCandidates, Vector.toList_map, readWord_redirect records xs hlen]

theorem verified_redirect {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout)
    (Q : Secp256k1.Point) (xs : List Bool) (hlen : xs.length = f) :
    verifiedCandidate (redirectedLayout records layout) Q xs =
      verifiedCandidate layout Q (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) := by
  unfold verifiedCandidate
  rw [candidates_redirect records layout xs hlen]

private theorem ofFn_fullHistory {e : Nat} (xs : List Bool) (hlen : xs.length = e) :
    List.ofFn (fullHistory e Fin.elim0 xs) = xs := by
  subst e
  change List.ofFn (fun i : Fin xs.length => xs.getD i.val false) = xs
  simpa only [List.getD_eq_getElem xs false (Fin.isLt _)] using List.ofFn_getElem xs

/-- Bridge the finite-record predicate to the protected decoder and Born sum. -/
theorem expectation_verified {n e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n 0 e) (layout : DecodeLayout) (Q : Secp256k1.Point) (psi : State) :
    expectation read p Fin.elim0 psi
      (fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome) =
      Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [expectation_selectedMass, ← selectedMass_filter (p.instantiate read Fin.elim0).run psi
    (fun xs => (verifiedCandidate layout Q xs).isSome)]
  unfold selectedMass
  congr 1
  apply List.map_congr_left
  intro b hb
  have hl : b.history.length = e := by
    simpa using straight_history_length p read Fin.elim0 b hb
  change (if (verifiedCandidate layout Q (List.ofFn (fullHistory e Fin.elim0 b.history))).isSome then _ else _) = _
  rw [ofFn_fullHistory b.history hl]

/-- The remapped protected decoder has exactly the original success probability. -/
theorem lower_verified {n e : Nat} (q : Wire) (p : Straight n 0 e)
    (read : ConstantBit n → Bool) (layout : DecodeLayout) (Q : Secp256k1.Point)
    (psi : State) (hf : Fresh q p) (hwf : p.WellFormed)
    (hpsi : SupportedOn (fun s => s q = false) psi) :
    Instrument.bornMass
      (((lower q p 0 Fin.elim0).program.instantiate read Fin.elim0).run.filter
        (fun b => (verifiedCandidate (redirectedLayout (lower q p 0 Fin.elim0).records layout)
          Q b.history).isSome)) psi =
    Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [← expectation_verified, ← expectation_verified]
  have he : (fun h => (verifiedCandidate (redirectedLayout (lower q p 0 Fin.elim0).records layout)
        Q (List.ofFn h)).isSome) =
      (fun h => (verifiedCandidate layout Q (List.ofFn (h ∘ (lower q p 0 Fin.elim0).records))).isSome) := by
    funext h
    rw [verified_redirect _ _ _ _ List.length_ofFn]
    simp [Function.comp_def]
  rw [he]
  exact lower_expectation q p 0 Fin.elim0 read Fin.elim0 Fin.elim0 psi (fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome)
    (by funext i; exact Fin.elim0 i) hf hwf hpsi

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- Static support, including every optional gate slot. -/
def Within {n s e : Nat} (ws : List Wire) : Straight n s e → Prop
  | .done => True
  | .gate (.literal g) p => gateWires g ⊆ ws ∧ Within ws p
  | .gate (.whenBit _ _ g) p => gateWires g ⊆ ws ∧ Within ws p
  | .recordGate _ _ g p => gateWires g ⊆ ws ∧ Within ws p
  | .measure w p => w ∈ ws ∧ Within ws p

theorem Within.fresh {n s e : Nat} {ws : List Wire} {p : Straight n s e}
    (h : Within ws p) (q : Wire) (hq : q ∉ ws) : Fresh q p := by
  induction p with
  | done => trivial
  | gate g p ih =>
      cases g <;> exact ⟨fun hq' => hq (h.1 hq'), ih h.2⟩
  | recordGate i v g p ih => exact ⟨fun hq' => hq (h.1 hq'), ih h.2⟩
  | measure w p ih => exact ⟨fun he => hq (he ▸ h.1), ih h.2⟩

theorem Within.mono {n s e : Nat} {ws vs : List Wire} {p : Straight n s e}
    (h : Within ws p) (hs : ws ⊆ vs) : Within vs p := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨h.1.trans hs, ih h.2⟩
  | recordGate i v g p ih => exact ⟨h.1.trans hs, ih h.2⟩
  | measure w p ih => exact ⟨hs h.1, ih h.2⟩

theorem Within.instantiate {n s e : Nat} {ws : List Wire} {p : Straight n s e}
    (h : Within ws p) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).wires ⊆ ws := by
  induction p with
  | done => simp [Straight.instantiate, AdaptiveCircuit.wires]
  | gate g p ih =>
      cases g with
      | literal g => simpa [Straight.instantiate, TemplateGate.instantiate,
          AdaptiveCircuit.wires, circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
      | whenBit r v g =>
          simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires]
          split
          · simpa [circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
          · simpa [circuitWires] using ih h.2 history
  | recordGate i v g p ih =>
      simp only [Straight.instantiate, AdaptiveCircuit.wires]
      split
      · simpa [circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
      · simpa [circuitWires] using ih h.2 history
  | measure w p ih =>
      exact List.cons_subset.mpr ⟨h.1, List.append_subset.mpr ⟨ih h.2 _, ih h.2 _⟩⟩

theorem within_of_instantiate {n s e : Nat} (p : Straight n s e) (ws : List Wire)
    (h : ∀ read history, (p.instantiate read history).wires ⊆ ws) : Within ws p := by
  induction p with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          constructor
          · intro w hw
            exact h (fun _ => false) (fun _ => false)
              (by simp [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
          · apply ih
            intro read history w hw
            exact h read history (List.mem_append_right _ hw)
      | whenBit r v g =>
          constructor
          · intro w hw
            exact h (fun _ => v) (fun _ => false)
              (by simp [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
          · apply ih
            intro read history w hw
            exact h read history (List.mem_append_right _ hw)
  | recordGate i v g p ih =>
      constructor
      · intro w hw
        exact h (fun _ => false) (fun _ => v)
          (by simp [Straight.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
      · apply ih
        intro read history w hw
        exact h read history (List.mem_append_right _ hw)
  | @measure s e w p ih =>
      constructor
      · exact h (fun _ => false) (fun _ => false) (List.mem_cons_self)
      · apply ih
        intro read history v hv
        let before : Fin s → Bool := fun i => history i.castSucc
        have he : Fin.lastCases (history (Fin.last s)) before = history := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [before]
        rw [← he] at hv
        apply h read before
        cases hb : history (Fin.last s) <;>
          simp only [hb] at hv <;>
          simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_cons, List.mem_append]
        · exact Or.inr (Or.inl hv)
        · exact Or.inr (Or.inr hv)

theorem within_literals {n s e : Nat} (ws : List Wire) (gs : Circuit) (p : Straight n s e)
    (hg : circuitWires gs ⊆ ws) (hp : Within ws p) : Within ws (literals gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
      have hh : gateWires g ⊆ ws ∧ circuitWires gs ⊆ ws := by
        simpa only [circuitWires, List.flatMap_cons, List.append_subset] using hg
      exact ⟨hh.1, ih hh.2⟩

theorem lower_within {n s e : Nat} (q : Wire) (p : Straight n s e) (ws : List Wire)
    (hp : Within ws p) (start : Nat) (records : Fin s → Fin start) :
    Within (q :: ws) (lower q p start records).program := by
  induction p generalizing start with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hs : a ∈ ws ∧ b ∈ ws ∧ t ∈ ws := by simpa [gateWires] using hp.1
              apply within_literals
              · simp [andCompute, parityPhase, xorPhase, circuitWires, gateWires,
                  List.cons_subset, hs.1, hs.2.1, hs.2.2]
              · exact ⟨by simp, by simp [gateWires, hs.2.1],
                  by simp [gateWires, hs.1, hs.2.1], by simp [gateWires, hs.2.1], ih hp.2 _ _⟩
          | X t | H t | CX a t | P dir k t =>
              exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
      | whenBit r v g => exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
  | recordGate i v g p ih => exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
  | measure w p ih => exact ⟨List.mem_cons_of_mem _ hp.1, ih hp.2 _ _⟩

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section

/-- Package the transformed straight program with unchanged public coefficients. -/
def lowerEntry (q : Wire) (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := (lower q entry.program 0 Fin.elim0).finish
  program := (lower q entry.program 0 Fin.elim0).program

def lowerLayout (q : Wire) (entry : StraightEntry) (layout : DecodeLayout) : DecodeLayout :=
  redirectedLayout (lower q entry.program 0 Fin.elim0).records layout

/-- Certificate transport uses only a proved count of eligible literal Toffolis. -/
theorem lower_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds newBounds : Bounds) (q : Wire) (ws : List Wire)
    (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hq : q ∉ ws)
    (hslots : entry.program.gateSlots + 18 * added entry.program ≤ limits.gateSlots)
    (hrecords : entry.finalCursor + added entry.program ≤ limits.measurements)
    (hqubits : ws.length + 1 ≤ newBounds.qubits)
    (ht : bounds.tModel ≤ newBounds.tModel + 2 * added entry.program)
    (hm : entry.finalCursor + added entry.program ≤ newBounds.measurements) :
    Certificate limits (lowerLayout q entry layout) (lowerEntry q entry) newBounds where
  gateBudget := by simpa only [lowerEntry, lower_slots] using hslots
  recordBudget := by
    have h := lower_finish q entry.program 0 Fin.elim0
    simp only [Nat.add_zero, Nat.zero_add] at h
    simpa only [lowerEntry] using h.le.trans hrecords
  tableBudget := cert.tableBudget
  candidateBudget := by simpa [lowerLayout, redirectedLayout] using cert.candidateBudget
  wellFormed := lower_wellFormed q entry.program 0 Fin.elim0 (hs.fresh q hq) cert.wellFormed
  resources := by
    intro Q
    have hsup := (lower_within q entry.program ws hs 0 Fin.elim0).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((lowerEntry q entry).instantiate Q).wires.dedup.toFinset).card ≤ (q :: ws).length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (q :: ws))
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((lowerEntry q entry).instantiate Q).qubitCount ≤ newBounds.qubits := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc.trans hqubits
    have htc := lower_t q entry.program 0 Fin.elim0 (readConstant entry.coefficients.get Q)
      Fin.elim0 Fin.elim0 (by funext i; exact Fin.elim0 i)
    have hto := (cert.resources Q).2.1
    have hmc := (lower q entry.program 0 Fin.elim0).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hfinish := lower_finish q entry.program 0 Fin.elim0
    refine ⟨hqc, ?_, ?_⟩
    · change ((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      change (entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel at hto
      omega
    · change ((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ newBounds.measurements
      omega
  success := by
    intro Q d hn hd
    change 99 / 100 ≤ Instrument.bornMass
      (((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate (redirectedLayout (lower q entry.program 0 Fin.elim0).records layout)
          Q b.history).isSome)) (ket zeroBasisState)
    rw [lower_verified q entry.program _ layout Q _ (hs.fresh q hq) cert.wellFormed
      (supportedOn_ket _ _ rfl)]
    exact cert.success Q d hn hd

end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem added_cast {n s e f} (p : Straight n s e) (h : e=f) :
    added (ChallengeMigration.castFinish h p) = added p := by subst f; rfl

theorem added_relabel {n s e} (p : Straight n s e) (f : Wire ≃ Wire) :
    added (relabelStraight f p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [relabelStraight, relabelTemplateGate, Gate.relabel, added]
    | whenBit r v g => simp_all [relabelStraight, relabelTemplateGate, added]
  | recordGate => simp_all [relabelStraight, added]
  | measure => simp_all [relabelStraight, added]

theorem added_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    added (reindexStraight f p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [reindexStraight, reindexGate, added]
    | whenBit r v g => simp_all [reindexStraight, reindexGate, added]
  | recordGate => simp_all [reindexStraight, added]
  | measure => simp_all [reindexStraight, added]

theorem added_shift {n s e} (p : Straight n s e) (offset : Nat) :
    added (shiftStraight offset p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [shiftStraight, added]
    | whenBit r v g => simp_all [shiftStraight, added]
  | recordGate => simp_all [shiftStraight, added]
  | measure => simp_all [shiftStraight, added, added_cast]

def ccxCount : Circuit → Nat
  | [] => 0
  | .CCX _ _ _ :: gs => Nat.succ (ccxCount gs)
  | _ :: gs => ccxCount gs

theorem added_literal {n s} (gs : Circuit) :
    added (literalProgram gs : Straight n s s) = ccxCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [literalProgram, gateProgram, added, ccxCount, Nat.add_comm]

def AtLeast {n s e} (p : Straight n s e) (count : Nat) : Prop := count ≤ added p
namespace AtLeast
 theorem zero {n s e} (p : Straight n s e) : AtLeast p 0 := Nat.zero_le _
 theorem castCount {n s e d f} {p : Straight n s e} (hp : AtLeast p d) (h : d=f) : AtLeast p f := h ▸ hp
 theorem castFinish {n s e f d} {p : Straight n s e} (hp : AtLeast p d) (h : e=f) :
     AtLeast (ChallengeMigration.castFinish h p) d := by simpa only [AtLeast, added_cast] using hp
 theorem append {n s m e d f} {p : Straight n s m} {q : Straight n m e}
     (hp : AtLeast p d) (hq : AtLeast q f) : AtLeast (p.append q) (d+f) := by
   unfold AtLeast at *; rw [added_append]; omega
 theorem appendCompiled {n start d f}
     (p : (count : Nat) × Straight n start (start+count))
     (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
     (hp : AtLeast p.2 d) (hq : AtLeast q.2 f) :
     AtLeast (ChallengeMigration.appendCompiled p q).2 (d+f) := by
   unfold ChallengeMigration.appendCompiled
   exact (hp.append hq).castFinish _
 theorem sequenceCons {n start d f} (p : FixedSegment n) (ps : List (FixedSegment n))
     (hp : AtLeast (p start).2 d)
     (hq : AtLeast (sequenceProgram n ps (start+(p start).1)).2 f) :
     AtLeast (sequenceProgram n (p::ps) start).2 (d+f) := appendCompiled (p start) (sequenceProgram n ps (start+(p start).1)) hp hq
 theorem surroundCompiled {n start d} (before after : Circuit)
     (p : (count : Nat) × Straight n start (start+count)) (hp : AtLeast p.2 d) :
     AtLeast (ChallengeMigration.surroundCompiled before after p).2 d := by
   unfold ChallengeMigration.surroundCompiled ChallengeMigration.prependCompiled
   exact ((zero (literalProgram before)).append
     ((appendCompiled p ⟨0,literalProgram after⟩ hp (zero _)).castCount (Nat.add_zero d))).castCount (Nat.zero_add d)
 theorem relabel {n s e d} {p : Straight n s e} (hp : AtLeast p d) (f : Wire ≃ Wire) :
     AtLeast (relabelStraight f p) d := by simpa [AtLeast, added_relabel] using hp
 theorem reindex {n m s e d} {p : Straight n s e} (hp : AtLeast p d) (f : Fin n → Fin m) :
     AtLeast (reindexStraight f p) d := by simpa [AtLeast, added_reindex] using hp
 theorem shift {n s e d} {p : Straight n s e} (hp : AtLeast p d) (offset : Nat) :
     AtLeast (shiftStraight offset p) d := by simpa [AtLeast, added_shift] using hp
end AtLeast

attribute [local irreducible] sequenceProgram appendCompiled literalProgram
 remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
 preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
 measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
 divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
 zeroMultiplicationProgram xNegateProgram coordinateProgram


theorem ccxCount_primitive (gs : Circuit) :
    ccxCount gs = (primitiveResources (.unitary gs .done)).toffoli := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [ccxCount, primitiveResources, gidneyToffoliCount, gidneyGateCount, Nat.add_comm]

theorem aCount (n s : Nat) : AtLeast (literalProgram (blockAForward indexedStepProductionRegisters) : Straight n s s) 906 := by
  rw [AtLeast, added_literal, ccxCount_primitive]
  rw [blockAForward259_primitive _ indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift indexedStepProduction_layout.work2_length
    (by decide) (by decide) (by decide)]

theorem fCount (n s : Nat) : AtLeast (literalProgram (blockFForward indexedStepProductionRegisters) : Straight n s s) 566 := by
  rw [AtLeast, added_literal, ccxCount_primitive]
  unfold blockFForward
  rw [postShiftUnitary259_primitive _ indexedStepProduction_layout.postShift
    indexedStepProduction_layout.work2_length (by decide)]

theorem stepCount (n start T : Nat) :
    AtLeast (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 1472 := by
  unfold measuredStepProgram measuredStepSegments
  refine (AtLeast.sequenceCons (d := 906) (f := 566) _ _ (aCount n _) ?_)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 566) (f := 0) _ _ (fCount n _) (AtLeast.zero _)).castCount (by omega)

theorem scheduleCount (n : Nat) (count first start : Nat) :
    AtLeast (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 (count*1472) := by
  induction count generalizing first start with
  | zero => exact AtLeast.zero _
  | succ count ih =>
    simp only [measuredScheduleProgram]
    exact (AtLeast.appendCompiled _ _ (stepCount n start first) (ih (first+1) _)).castCount (by omega)

theorem wrapperCount (n start : Nat) :
    AtLeast (measuredForwardWrapperProgram n start).2 2384640 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 2384640) (f := 0) _ _ (show AtLeast (measuredEEAForwardProgram n _ indexedStepProductionRegisters).2 2384640 from by unfold measuredEEAForwardProgram; exact scheduleCount n 1620 1 _) (AtLeast.zero _)).castCount (by omega)

theorem divisionCount (n start : Nat) : AtLeast (divisionProgram n start).2 2384640 := by
  unfold divisionProgram
  refine (AtLeast.appendCompiled (d := 2384640) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (wrapperCount n start) (AtLeast.zero _)).castCount (by omega)

theorem zeroDivisionCount (n start : Nat) : AtLeast (zeroDivisionProgram n start).2 2384640 := by
  unfold zeroDivisionProgram
  exact AtLeast.surroundCompiled _ _ _ (divisionCount n start)

theorem coordinateCount (start : Nat) : AtLeast (coordinateProgram start).2 2384640 := by
  unfold coordinateProgram coordinateSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons _ _ (zeroDivisionCount 32768 _) (AtLeast.zero _)).castCount (by omega)
end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def residue {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p => primitivePhaseCost g + residue p
  | .gate (.whenBit _ _ g) p => tCost g + residue p
  | .recordGate _ _ g p => tCost g + residue p
  | .measure _ p => residue p

@[simp] theorem residue_done {n s : Nat} : residue (Straight.done : Straight n s s) = 0 := rfl

theorem residue_t {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    (p.instantiate read history).tCount ≤ 7 * added p + residue p := by
  induction p with
  | done => simp [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
  | gate g p ih =>
    have h := ih history
    cases g with
    | literal g => cases g <;>
        simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
          tCount, tCost, primitivePhaseCost, added, residue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at * <;> omega
    | whenBit r v g =>
        simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount, added, residue]
        split <;> simp only [tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  | recordGate i v g p ih =>
      have h := ih history
      simp only [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
      split <;> simp only [tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  | measure w p ih =>
      have hf := ih (Fin.lastCases false history)
      have ht := ih (Fin.lastCases true history)
      simp only [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
      omega

theorem residue_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    residue (p.append q) = residue p + residue q := by
  induction p with
  | done => simp [Straight.append, residue]
  | gate g p ih => cases g <;> simp [Straight.append, residue, ih, Nat.add_assoc]
  | recordGate => simp_all [Straight.append, residue, Nat.add_assoc]
  | measure => simp_all [Straight.append, residue]

theorem residue_cast {n s e f} (p : Straight n s e) (h : e=f) :
    residue (castFinish h p) = residue p := by subst f; rfl

theorem residue_literal {n s} (gs : Circuit) :
    residue (literalProgram gs : Straight n s s) = (gs.map primitivePhaseCost).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp_all [literalProgram, gateProgram, residue]

theorem residue_literal_HPFree {n s} (gs : Circuit) (h : Classical.HPFree gs) :
    residue (literalProgram gs : Straight n s s) = 0 := by
  rw [residue_literal, primitivePhaseCost_of_HPFree gs h]

theorem residue_recordGates {n s e} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    residue (recordGates i gs p) = tCount gs + residue p := by
  induction gs with
  | nil => simp [recordGates, tCount]
  | cons g gs ih => simp [recordGates, residue, tCount, ih, Nat.add_assoc]

@[simp] theorem residue_andErase (n s a b t : Nat) :
    residue (andEraseProgram n s a b t) = 0 := by
  simp [andEraseProgram, residue, residue_recordGates, controlledZ, tCount, tCost]

@[simp] theorem residue_compiled {n start}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    residue (appendCompiled p q).2 = residue p.2 + residue q.2 := by
  simp only [appendCompiled, residue_cast, residue_append]

@[simp] theorem residue_prepend {n start} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    residue (prependCompiled gs p).2 = (gs.map primitivePhaseCost).sum + residue p.2 := by
  simp only [prependCompiled, residue_append, residue_literal]

@[simp] theorem residue_surround {n start} (gs hs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    residue (surroundCompiled gs hs p).2 =
      (gs.map primitivePhaseCost).sum + residue p.2 + (hs.map primitivePhaseCost).sum := by
  simp [surroundCompiled, residue_literal, Nat.add_assoc]

@[simp] theorem residue_vchainTail (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) :
    residue (vchainTailProgram n controls acc target scratch start).2 = 0 := by
  induction controls generalizing acc scratch start with
  | nil => rfl
  | cons control controls ih =>
    cases controls with
    | nil => simp [vchainTailProgram, residue_literal, primitivePhaseCost]
    | cons next controls =>
      cases scratch with
      | nil => rfl
      | cons work scratch => simp only [vchainTailProgram, residue_prepend, residue_compiled,
          ih, residue_andErase]; rfl

@[simp] theorem residue_vchain (n start : Nat) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    residue (vchainProgram n start controls target scratch).2 = 0 := by
  unfold vchainProgram
  split <;> simp_all [residue, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleMaj (n start control target addend carry scratch : Nat) :
    residue (rippleMajProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleMajProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleUma (n start control target addend carry scratch : Nat) :
    residue (rippleUmaProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleUmaProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleMajInv (n start control target addend carry scratch : Nat) :
    residue (rippleMajInvProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleMajInvProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleUmaInv (n start control target addend carry scratch : Nat) :
    residue (rippleUmaInvProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleUmaInvProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleFirst (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    residue (rippleFirstProgram n start mode control target addend carry scratch).2 = 0 := by
  cases mode <;> simp [rippleFirstProgram]

@[simp] theorem residue_rippleSecond (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    residue (rippleSecondProgram n start mode control target addend carry scratch).2 = 0 := by
  cases mode <;> simp [rippleSecondProgram]

@[simp] theorem residue_zeroErase (n start a b w : Nat) :
    residue (zeroEraseProgram n start a b w).2 = 0 := by
  simp [zeroEraseProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_dualErase (n start a i x b j y : Nat) :
    residue (dualEraseProgram n start a i x b j y).2 = 0 := by
  simp [dualEraseProgram]

def compiledResidue {n start} (p : (count : Nat) × Straight n start (start+count)) : Nat := residue p.2

@[simp] theorem residue_ite {n start} (c : Prop) [Decidable c]
    (p q : (count : Nat) × Straight n start (start+count)) :
    residue (if c then p else q).2 = if c then residue p.2 else residue q.2 := by
  change compiledResidue (if c then p else q) = _
  split <;> rfl


theorem residue_unary (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (hl : ∀ label control start, residue (leaf label control start).2 = 0)
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) (start : Nat) :
    residue (unaryProgram n order leaf tree q path start).2 = 0 := by
  change compiledResidue (unaryProgram n order leaf tree q path start) = 0
  induction tree generalizing q path start with
  | leaf label => rw [unaryProgram.eq_1]; exact hl label q start
  | node bit zero one ihz iho =>
    cases path with
    | nil => rw [unaryProgram.eq_3]; rfl
    | cons p ps =>
      rw [unaryProgram.eq_2]
      simp only [compiledResidue] at ihz iho
      cases order <;>
        simp [compiledResidue, ihz, iho, computeZeroAnd, primitivePhaseCost]

theorem residue_dual (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (hl : ∀ label a b start, residue (leaf label a b start).2 = 0)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) :
    residue (dualProgram n order leaf tree a b xs ys start).2 = 0 := by
  change compiledResidue (dualProgram n order leaf tree a b xs ys start) = 0
  induction tree generalizing a b xs ys start with
  | leaf label => rw [dualProgram.eq_1]; exact hl label a b start
  | node i j zero one ihz iho =>
    cases xs with
    | nil => rw [dualProgram.eq_3] <;> simp [compiledResidue, residue]
    | cons x xs => cases ys with
      | nil => rw [dualProgram.eq_3] <;> simp [compiledResidue, residue]
      | cons y ys =>
        rw [dualProgram.eq_2]
        simp only [compiledResidue] at ihz iho
        cases order <;>
          simp [compiledResidue, ihz, iho, computeZeroAnd, primitivePhaseCost]

@[simp] theorem phaseCost_zeroMask (ws : List Wire) (v : Nat) :
    ((zeroMask ws v).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (zeroMask_HPFree ws v)

@[simp] theorem phaseCost_endpointLeafToggle (top : Bool) (label : Nat) (a b c : Wire) :
    ((endpointLeafToggle top label a b c).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (endpointLeafToggle_HPFree top label a b c)

@[simp] theorem residue_equality (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) : residue (equalityProgram n start register value flag scratch).2 = 0 := by
  simp [equalityProgram, residue_literal]

@[simp] theorem residue_toggleEquality (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) :
    residue (toggleEqualityProgram n start root register value acc flag scratch).2 = 0 := by
  simp [toggleEqualityProgram, primitivePhaseCost]

@[simp] theorem residue_intervalFirst (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    residue (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 = 0 := by
  simp [intervalFirstProgram, residue_literal]

@[simp] theorem residue_topFirst (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    residue (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 = 0 := by
  simp [topFirstProgram]

@[simp] theorem residue_traversalFirst (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    residue (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 = 0 := by
  unfold traversalFirstProgram
  apply residue_dual
  intros
  apply residue_intervalFirst

@[simp] theorem residue_coefficientFirst (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    residue (coefficientFirstProgram n start r k K mode target label control).2 = 0 := by
  simp [coefficientFirstProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_intervalSecond (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    residue (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 = 0 := by
  simp [intervalSecondProgram, residue_literal]

@[simp] theorem residue_topSecond (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    residue (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 = 0 := by
  simp [topSecondProgram]

@[simp] theorem residue_traversalSecond (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    residue (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 = 0 := by
  unfold traversalSecondProgram
  apply residue_dual
  intros
  apply residue_intervalSecond

@[simp] theorem residue_coefficientSecond (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    residue (coefficientSecondProgram n start r k K mode target label control).2 = 0 := by
  simp [coefficientSecondProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_coefficient (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    residue (coefficientProgram n start r k K mode signUpdate target).2 = 0 := by
  have hl : ∀ label control start, residue (coefficientFirstProgram n start r k K mode target label control).2 = 0 := by simp
  have hr : ∀ label control start, residue (coefficientSecondProgram n start r k K mode target label control).2 = 0 := by simp
  cases signUpdate <;> simp [coefficientProgram, residue_unary _ _ _ hl, residue_unary _ _ _ hr,
    residue_literal, coefficientPrefixSignCircuit, primitivePhaseCost]

@[simp] theorem residue_coefficientInverse (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    residue (coefficientInverseProgram n start r k K mode signUpdate target).2 = 0 := by
  simp [coefficientInverseProgram]

attribute [local simp] primitivePhaseCost_of_HPFree

@[simp] theorem residue_intervalTopFirst (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    residue (intervalTopFirstProgram n start r k K mode target).2 = 0 := by
  change compiledResidue (intervalTopFirstProgram n start r k K mode target) = 0
  unfold intervalTopFirstProgram
  split <;> simp [compiledResidue, residue_literal]
@[simp] theorem residue_intervalTopSecond (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    residue (intervalTopSecondProgram n start r k K mode target).2 = 0 := by
  change compiledResidue (intervalTopSecondProgram n start r k K mode target) = 0
  unfold intervalTopSecondProgram
  split <;> simp [compiledResidue, residue_literal]

@[simp] theorem residue_interval (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    residue (intervalProgram n start r width k K mode signUpdate target).2 = 0 := by
  cases signUpdate <;> simp [intervalProgram, residue_literal, intervalSignUpdate, primitivePhaseCost]

@[simp] theorem residue_intervalInverse (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    residue (intervalInverseProgram n start r width k K mode signUpdate target).2 = 0 := by
  simp [intervalInverseProgram]

theorem residue_sequence (n : Nat) (ps : List (FixedSegment n))
    (hp : ∀ p ∈ ps, ∀ start, residue (p start).2 = 0) (start : Nat) :
    residue (sequenceProgram n ps start).2 = 0 := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    simp only [sequenceProgram, residue_compiled]
    rw [hp p (by simp), ih (by intro q hq; exact hp q (by simp [hq]))]

theorem residue_phaseSegments (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (core : Circuit) (hc : (core.map primitivePhaseCost).sum = 0) :
    residue (sequenceProgram n (phaseSegments n r shift core) start).2 = 0 := by
  apply residue_sequence
  intro p hp s
  simp only [phaseSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h <;>
    subst p <;> simp [residue_literal, primitivePhaseCost, hc]

@[simp] theorem residue_phase (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    residue (phaseProgram n start r shift).2 = 0 := by
  unfold phaseProgram
  apply residue_phaseSegments
  simp [phaseCoreGates, primitivePhaseCost]

@[simp] theorem residue_phaseInverse (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    residue (phaseInverseProgram n start r shift).2 = 0 := by
  unfold phaseInverseProgram
  apply residue_phaseSegments
  simp [phaseInverseCoreGates, primitivePhaseCost]

private theorem blockB2_classical (r : IndexedStepRegisters) : Classical.HPFree (blockB2 r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  have hb : Classical.HPFree (blockBForward r 256 (certifiedActiveWindows 256 1).remainder) := by tauto
  simp only [blockBForward, Classical.hpFree_append] at hb
  tauto

@[simp] theorem residue_remainderBlock (n start : Nat) (r : IndexedStepRegisters)
    (width : Nat) (w : ActiveWindow) :
    residue (remainderBlockProgram n start r width w).2 = 0 := by
  unfold remainderBlockProgram remainderBlockSegments
  simp [sequenceProgram, residue_literal, primitivePhaseCost, blockB2_classical]

@[simp] theorem residue_coefficientBlock (n start : Nat) (r : IndexedStepRegisters)
    (width : Nat) (w : ActiveWindow) :
    residue (coefficientBlockProgram n start r width w).2 = 0 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  simp [sequenceProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_zeroCell (n start : Nat) (base : Bool) (r bit guard target temporary : Wire) :
    residue (zeroCellProgram n start base r bit guard target temporary).2 = 0 := by
  cases base <;> simp [zeroCellProgram, measuredZeroPrefix, primitivePhaseCost]

@[simp] theorem residue_upperForwardLeaf (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label ≤ K
  · by_cases he : label = K <;> simp [upperForwardLeafProgram, h, he]
  · simp [upperForwardLeafProgram, h]

@[simp] theorem residue_upperReverseLeaf (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label < K <;> simp [upperReverseLeafProgram, h]

@[simp] theorem residue_lowerForwardLeaf (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label ≤ K
  · by_cases he : label = k <;> simp [lowerForwardLeafProgram, h, he]
  · simp [lowerForwardLeafProgram, h]

@[simp] theorem residue_lowerReverseLeaf (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k < label ∧ label ≤ K <;> simp [lowerReverseLeafProgram, h]

@[simp] theorem residue_rangeLeaf (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n)
    (hl : ∀ label control start, residue (leaf label control start).2 = 0)
    (label : Nat) (dynamic : Wire) (start : Nat) :
    residue (rangeLeafProgram n after r leaf label dynamic start).2 = 0 := by
  cases after <;> simp [rangeLeafProgram, hl, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rangeScan (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (start : Nat)
    (hl : ∀ label control start, residue (leaf label control start).2 = 0) :
    residue (rangeScanProgram n after order tree control r path leaf start).2 = 0 := by
  have hr (after : Bool) : ∀ label control start,
      residue (rangeLeafProgram n after r leaf label control start).2 = 0 := by simp [hl]
  cases after <;> simp [rangeScanProgram, residue_unary _ _ _ (hr _), residue_literal, primitivePhaseCost]

@[simp] theorem residue_upperMap (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    residue (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2 = 0 := by
  simp [upperMapProgram]

@[simp] theorem residue_lowerMap (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    residue (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2 = 0 := by
  simp [lowerMapProgram]

@[simp] theorem phaseCost_highestWrites (k K : Nat) (targets : List Wire) (dirtyAt : Nat → Wire) :
    ((highestPositionDirtyWrites k K targets dirtyAt).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (by simp [highestPositionDirtyWrites])
@[simp] theorem phaseCost_rightWrites (width k K : Nat) (targets : List Wire) (dirtyAt : Nat → Wire) :
    ((rightLengthDirtyWrites width k K targets dirtyAt).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (by simp [rightLengthDirtyWrites])

@[simp] theorem residue_upperWriter (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    residue (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2 = 0 := by
  simp [upperWriterProgram]

@[simp] theorem residue_lowerWriter (n width k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    residue (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2 = 0 := by
  simp [lowerWriterProgram]

@[simp] theorem residue_ltUpdate (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    residue (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 = 0 := by
  simp [ltUpdateProgram]
@[simp] theorem residue_lrpUpdate (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    residue (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 = 0 := by
  simp [lrpUpdateProgram]

@[simp] theorem residue_upperEnd (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (upperEndProgram n start r width w).2 = 0 := by
  simp [upperEndProgram, residue_literal]

@[simp] theorem residue_lowerEnd (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (lowerEndProgram n start r width w).2 = 0 := by
  simp [lowerEndProgram, residue_literal]

@[simp] theorem residue_end (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (endProgram n start r width w).2 = 0 := by
  simp [endProgram, residue_literal]

@[simp] theorem residue_endInverse (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (endInverseProgram n start r width w).2 = 0 := by
  simp [endInverseProgram, residue_literal]

@[simp] private theorem blockHPrefix_classical (r : IndexedStepRegisters) : Classical.HPFree (blockHPrefix r) := by
  simp [blockHPrefix]
@[simp] private theorem blockHSuffix_classical (r : IndexedStepRegisters) : Classical.HPFree (blockHSuffix r) := by
  simp [blockHSuffix]

@[simp] theorem residue_h (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (hProgram n start r width T).2 = 0 := by
  simp [hProgram, residue_literal, primitivePhaseCost]
@[simp] theorem residue_hInverse (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (hInverseProgram n start r width T).2 = 0 := by
  simp [hInverseProgram, residue_literal, primitivePhaseCost]

@[simp] private theorem blockAForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockAForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockCForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockCForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockFForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockFForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockAInverse_classical (r : IndexedStepRegisters) : Classical.HPFree (blockAInverse r) := by
  have h := indexedStepInverseUnitary_HPFree r 256 1
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockCInverse_classical (r : IndexedStepRegisters) : Classical.HPFree (blockCInverse r) := by
  have h := indexedStepInverseUnitary_HPFree r 256 1
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockDForward_classical (r : IndexedStepRegisters) (width T : Nat) :
    Classical.HPFree (blockDForward r (certifiedActiveWindows width T).quotientSwap) := by
  have h := indexedStepUnitary_HPFree r width T
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockDInverse_classical (r : IndexedStepRegisters) (width T : Nat) :
    Classical.HPFree (blockDInverse r (certifiedActiveWindows width T).quotientSwap) := by
  have h := indexedStepInverseUnitary_HPFree r width T
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] theorem residue_measuredStep (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (measuredStepProgram n start r width T).2 = 0 := by
  simp [measuredStepProgram, measuredStepSegments, sequenceProgram, residue_literal, primitivePhaseCost]

@[simp] theorem phaseCost_adjoint (gs : Circuit) :
    ((gs.adjoint).map primitivePhaseCost).sum = (gs.map primitivePhaseCost).sum := by
  have h := congrArg PrimitiveResources.phase (primitiveResources_unitary_adjoint gs .done)
  simpa [primitiveResources, gidneyGateCount] using h

@[simp] theorem residue_measuredInverseStep (n start : Nat) (r : IndexedStepRegisters) (T : Nat) :
    residue (measuredInverseStepProgram n start r T).2 = 0 := by
  simp [measuredInverseStepProgram, measuredInverseStepSegments, sequenceProgram,
    residue_literal, primitivePhaseCost, blockB2_classical]

@[simp] theorem residue_measuredSchedule (n : Nat) (r : IndexedStepRegisters)
    (width count first start : Nat) :
    residue (measuredScheduleProgram n r width count first start).2 = 0 := by
  induction count generalizing first start with
  | zero => rfl
  | succ count ih => simp only [measuredScheduleProgram, residue_compiled, residue_measuredStep, ih, Nat.zero_add]

@[simp] theorem residue_measuredInverseSchedule (n : Nat) (r : IndexedStepRegisters)
    (count first start : Nat) :
    residue (measuredInverseScheduleProgram n r count first start).2 = 0 := by
  induction count generalizing first start with
  | zero => rfl
  | succ count ih => simp only [measuredInverseScheduleProgram, residue_compiled, residue_measuredInverseStep, ih, Nat.zero_add]

end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem ccx_cost_le (gs : Circuit) : 7 * ccxCount gs ≤ tCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;>
      simp only [ccxCount, tCount, List.map_cons, List.sum_cons, tCost] at * <;> omega

theorem adaptive_ccx_cost_le (p : AdaptiveCircuit) : 7 * (primitiveResources p).toffoli ≤ p.tCount := by
  induction p with
  | done => rfl
  | unitary gs p ih =>
      have hg := ccx_cost_le gs
      rw [ccxCount_primitive] at hg
      simp only [primitiveResources, gidneyToffoliCount, gidneyGateCount, AdaptiveCircuit.tCount] at *
      omega
  | xMeasureReset w f t ihf iht =>
      simp only [primitiveResources, gidneyToffoliCount, gidneyGateCount, AdaptiveCircuit.tCount] at *
      omega

attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram
 secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse added residue
 primitiveResources AdaptiveCircuit.tCount

theorem forwardCoreFullCount (n start : Nat) :
    AtLeast (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 15772489 := by
  have hs := secp256k1MeasuredEEAForward_toffoli indexedStepProductionRegisters
    secp256k1ScheduleLayout_production (by decide)
  rw [secp256k1EEAForwardPrimitive_certificate] at hs
  have hl := adaptive_ccx_cost_le (secp256k1MeasuredEEAForward indexedStepProductionRegisters)
  have ht := measuredEEAForwardProgram_tCount n start indexedStepProductionRegisters
    (fun _ => false) (fun _ => false)
  have hr := residue_t (measuredEEAForwardProgram n start indexedStepProductionRegisters).2
    (fun _ => false) (fun _ => false)
  have hz : residue (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 = 0 := by
    unfold measuredEEAForwardProgram
    exact residue_measuredSchedule _ _ _ _ _ _
  unfold AtLeast
  unfold compiledTCount at ht
  change (primitiveResources (secp256k1MeasuredEEAForward indexedStepProductionRegisters)).toffoli + 1681736 = 17454225 at hs
  omega

theorem reverseCoreFullCount (n start : Nat) :
    AtLeast (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 15772489 := by
  have hs := secp256k1MeasuredEEAReverse_toffoli indexedStepProductionRegisters
    secp256k1ScheduleLayout_production (by decide)
  rw [secp256k1EEAReversePrimitive_certificate] at hs
  have hl := adaptive_ccx_cost_le (secp256k1MeasuredEEAReverse indexedStepProductionRegisters)
  have ht := measuredEEAReverseProgram_tCount n start indexedStepProductionRegisters
    (fun _ => false) (fun _ => false)
  have hr := residue_t (measuredEEAReverseProgram n start indexedStepProductionRegisters).2
    (fun _ => false) (fun _ => false)
  have hz : residue (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 = 0 := by
    unfold measuredEEAReverseProgram
    exact residue_measuredInverseSchedule _ _ _ _ _
  unfold AtLeast
  unfold compiledTCount at ht
  change (primitiveResources (secp256k1MeasuredEEAReverse indexedStepProductionRegisters)).toffoli + 1681736 = 17454225 at hs
  omega
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
 measuredForwardWrapperProgram measuredReverseWrapperProgram

theorem forwardWrapperFullCount (n start : Nat) :
    AtLeast (measuredForwardWrapperProgram n start).2 15772489 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 15772489) (f := 0) _ _
    (forwardCoreFullCount n _) (AtLeast.zero _)).castCount (by omega)

theorem reverseWrapperFullCount (n start : Nat) :
    AtLeast (measuredReverseWrapperProgram n start).2 15772489 := by
  unfold measuredReverseWrapperProgram measuredReverseWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 15772489) (f := 0) _ _
    (reverseCoreFullCount n _) (AtLeast.zero _)).castCount (by omega)

theorem AtLeast.relabelCompiled {n start d} (p : (count : Nat) × Straight n start (start+count))
    (hp : AtLeast p.2 d) (f : Wire ≃ Wire) : AtLeast (ChallengeMigration.relabelCompiled f p).2 d := hp.relabel f
def CompiledAtLeast {n start} (p : (count : Nat) × Straight n start (start+count)) (d : Nat) : Prop := AtLeast p.2 d

theorem AtLeast.measure {n s e d} (w : Wire) {p : Straight n (s+1) e} (hp : AtLeast p d) :
    AtLeast (.measure w p) d := by simpa only [AtLeast, added] using hp

theorem AtLeast.collect {n d}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hn : ∀ cursor prior, AtLeast (next cursor prior).2 d)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    AtLeast (collectProgram n next ws start prior).2 d := by
  change CompiledAtLeast (collectProgram n next ws start prior) d
  induction ws generalizing start with
  | nil => exact hn start prior
  | cons w ws ih =>
    rw [collectProgram]
    dsimp only [CompiledAtLeast]
    apply AtLeast.castFinish
    apply AtLeast.measure
    exact ih (start+1) _

theorem forwardBankCount (n start : Nat) :
    AtLeast (measuredForwardDataBankProgram n start).2 15772489 :=
  AtLeast.relabelCompiled _ (forwardWrapperFullCount n start) eeaWorkspaceExchange

theorem reverseBankCount (n start : Nat) :
    AtLeast (measuredReverseDataBankProgram n start).2 15772489 :=
  AtLeast.relabelCompiled _ (reverseWrapperFullCount n start) eeaWorkspaceExchange

attribute [local irreducible] measuredForwardDataBankProgram measuredReverseDataBankProgram
 multiplyDataProgram multiplyWorkProgram unmultiplyDataProgram divisionAfterResetProgram divisionProgram
 multiplicationAfterResetProgram multiplicationCleanupProgram multiplicationCorrectionProgram
 multiplicationProgram coordinateProgram zeroDivisionProgram zeroMultiplicationProgram

theorem divisionAfterCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (divisionAfterResetProgram n start prior).2 15772489 := by
  unfold divisionAfterResetProgram appendRetaining
  refine (AtLeast.appendCompiled (d := 15772489) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCount n start) (AtLeast.zero _)).castCount (by omega)

theorem divisionBothCount (n start : Nat) : AtLeast (divisionProgram n start).2 31544978 := by
  unfold divisionProgram
  refine AtLeast.appendCompiled (d := 15772489) (f := 15772489) _ _ ?_ ?_
  · exact (AtLeast.appendCompiled _ _ (forwardWrapperFullCount n start) (AtLeast.zero _)).castCount (by omega)
  · exact AtLeast.collect (divisionAfterResetProgram n) (divisionAfterCount n) _ _ _

theorem multiplicationCleanupCount (n start : Nat) :
    AtLeast (multiplicationCleanupProgram n start).2 15772489 := by
  unfold multiplicationCleanupProgram appendLiteral
  refine (AtLeast.appendCompiled (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCount n _) (AtLeast.zero _)).castCount (by omega)

theorem multiplicationCorrectionCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationCorrectionProgram n start prior).2 15772489 := by
  unfold multiplicationCorrectionProgram
  exact (AtLeast.appendCompiled _ _ (AtLeast.zero _) (multiplicationCleanupCount n _)).castCount (by omega)

theorem multiplicationAfterCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationAfterResetProgram n start prior).2 31544978 := by
  unfold multiplicationAfterResetProgram appendRetaining
  refine AtLeast.appendCompiled (d := 15772489) (f := 15772489) _ _ ?_ (multiplicationCorrectionCount n _ _)
  exact (AtLeast.appendCompiled _ _ (forwardBankCount n start) (AtLeast.zero _)).castCount (by omega)

theorem multiplicationBothCount (n start : Nat) : AtLeast (multiplicationProgram n start).2 31544978 := by
  unfold multiplicationProgram
  refine (AtLeast.appendCompiled (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact AtLeast.collect (multiplicationAfterResetProgram n) (multiplicationAfterCount n) _ _ _

theorem coordinateAllCount (start : Nat) : AtLeast (coordinateProgram start).2 63089956 := by
  unfold coordinateProgram coordinateSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 63089956) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 63089956) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine AtLeast.sequenceCons (d := 31544978) (f := 31544978) _ _ ?_ ?_
  · unfold zeroDivisionProgram
    exact AtLeast.surroundCompiled _ _ _ (divisionBothCount _ _)
  · refine (AtLeast.sequenceCons (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
    refine (AtLeast.sequenceCons (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
    refine (AtLeast.sequenceCons (d := 31544978) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
    unfold zeroMultiplicationProgram
    exact AtLeast.surroundCompiled _ _ _ (multiplicationBothCount _ _)

end
end ShorECDLP.Entrant.AndGadget
end
section
set_option Elab.async false
namespace ShorECDLP.Entrant.Catalyst
open Quantum Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket
set_option linter.unusedSimpArgs false

def prepare (q : Wire) : Circuit := [.H q, .P .forward 2 q]
def kick (t q : Wire) : Circuit := [.CX t q] ++ controlledZ t q
private theorem phase_two : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring
private theorem upd_twice (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]

theorem kick_ket (t q : Wire) (ht : t ≠ q) (s : BasisState) (hq : s q = false) :
    Quantum.run (kick t q) (Quantum.run (prepare q) (ket s)) =
      Quantum.run (prepare q) (applyGate (.P .forward 2 t) (ket s)) := by
  simp only [kick, prepare, Quantum.run_append, Quantum.run_cons, Quantum.run_nil,
    LinearMap.id_coe, id_eq, applyGate_H_ket, applyGate_P_ket, map_add, map_smul,
    applyGate_CX_ket, run_controlledZ_ket t q _ ht, upd_same, upd_other _ _ _ ht,
    upd_twice, phase_two, hq, Bool.false_eq_true, if_false, if_true, mul_one]
  cases hs : s t <;> simp [hs, smul_add, smul_smul, Complex.I_mul_I]
  all_goals match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

theorem linear_on_supported (A B : State →ₗ[ℂ] State) (V : BasisState → Prop)
    (h : ∀ s, V s → A (ket s) = B (ket s)) (psi : State) (hp : SupportedOn V psi) :
    A psi = B psi := by
  have hb : BranchCoherentOn B V ⟨[],A⟩ 1 := by
    intro s hs
    simpa only [one_smul] using h s hs
  simpa only [one_smul] using hb.on_supported hp

theorem linear_comp_supported (A B C D : State →ₗ[ℂ] State) (V : BasisState → Prop)
    (h : ∀ s, V s → A (B (ket s)) = C (D (ket s))) (psi : State) (hp : SupportedOn V psi) :
    A (B psi) = C (D psi) := linear_on_supported (A.comp B) (C.comp D) V h psi hp

theorem kick_supported (t q : Wire) (ht : t ≠ q) (psi : State)
    (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (kick t q) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (applyGate (.P .forward 2 t) psi) :=
  linear_comp_supported (Quantum.run (kick t q)) (Quantum.run (prepare q))
    (Quantum.run (prepare q)) (applyGate (.P .forward 2 t)) _
    (kick_ket t q ht) psi hp

theorem prepare_gate (q : Wire) (g : Gate) (hq : q ∉ gateWires g) (psi : State) :
    applyGate g (Quantum.run (prepare q) psi) = Quantum.run (prepare q) (applyGate g psi) := by
  simp only [prepare, Quantum.run_cons, Quantum.run_nil, LinearMap.id_coe, id_eq]
  rw [applyGate_P_commute g q .forward 2 hq, applyGate_H_commute g q hq]

theorem prepare_reset (q w : Wire) (hq : q ≠ w) (b : Bool) (psi : State) :
    xResetKraus w b (Quantum.run (prepare q) psi) = Quantum.run (prepare q) (xResetKraus w b psi) := by
  simp only [prepare, Quantum.run_cons, Quantum.run_nil, LinearMap.id_coe, id_eq]
  rw [xReset_P_commute w q b .forward 2 hq,
    ← applyGate_reset_commute (.H q) w b (by simpa [gateWires, ne_comm] using hq)]
open Challenge AndGadget

def replacement (q : Wire) : Gate → Circuit
  | .P .forward 2 t => kick t q
  | g => [g]

def savedGate : Gate → Nat
  | .P .forward 2 _ => 1
  | _ => 0

def compile {n s e} (q : Wire) : Straight n s e → Straight n s e
  | .done => .done
  | .gate (.literal g) next => literals (replacement q g) (compile q next)
  | .gate (.whenBit r v g) next => .gate (.whenBit r v g) (compile q next)
  | .recordGate i v g next => .recordGate i v g (compile q next)
  | .measure w next => .measure w (compile q next)

def saved {n s e} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) next => savedGate g + saved next
  | .gate _ next => saved next
  | .recordGate _ _ _ next => saved next
  | .measure _ next => saved next

theorem replacement_correct (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (psi : State) (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (replacement q g) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (applyGate g psi) := by
  unfold replacement
  split
  · rename_i t
    exact kick_supported t q (by simpa [gateWires, ne_comm] using hq) psi hp
  · simpa only [Quantum.run_singleton] using prepare_gate q g hq psi

private theorem gate_frame (q : Wire) (gs : Circuit) (hq : q ∉ circuitWires gs)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (Quantum.run gs psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary gs .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[], Quantum.run gs⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hpsi
  exact h

private theorem reset_frame (q w : Wire) (hq : q ≠ w) (outcome : Bool)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (xResetKraus w outcome psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[outcome], xResetKraus w outcome⟩ ?_ psi hpsi
  cases outcome <;>
    simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_append, List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem compile_expectation {n s e} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hf : Fresh q p)
    (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (compile q p) history (Quantum.run (prepare q) psi) accept =
      expectation read p history psi accept := by
  induction p generalizing psi with
  | done =>
    simp only [compile, expectation, normSq_run (prepare q) (by simp [prepare, CircuitWellFormed, Gate.WellFormed])]
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [compile, expectation_literals, replacement_correct q g hf.1 psi hp,
        expectation, TemplateGate.instantiate, Quantum.run_singleton]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    | whenBit r v g =>
      simp only [compile, expectation, TemplateGate.instantiate]
      split
      · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
      · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | recordGate i v g p ih =>
    simp only [compile, expectation]
    split
    · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | measure w p ih =>
    simp only [compile, expectation, prepare_reset q w hf.1]
    rw [ih _ _ accept hf.2 (reset_frame q w hf.1 false psi hp), ih _ _ accept hf.2 (reset_frame q w hf.1 true psi hp)]

theorem replacement_t (q : Wire) (g : Gate) :
    ShorECDLP.tCount (replacement q g) + savedGate g = tCost g := by
  unfold replacement savedGate
  split
  · rfl
  · rename_i g h
    cases g <;> simp_all [tCount, tCost]

theorem literals_t {n s e} (gs : Circuit) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((literals gs p).instantiate read history).tCount =
      ShorECDLP.tCount gs + (p.instantiate read history).tCount := AndGadget.literals_t read gs p history

theorem compile_t {n s e} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((compile q p).instantiate read history).tCount + saved p =
      (p.instantiate read history).tCount := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [compile, literals_t, saved, Straight.instantiate, TemplateGate.instantiate,
        AdaptiveCircuit.tCount, tCount, List.sum_cons, List.map_cons, List.map_nil, List.sum_nil]
      have h := replacement_t q g
      simp only [ShorECDLP.tCount] at h
      have hi := ih history
      omega
    | whenBit r v g =>
      simp only [compile, saved, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount]
      have hi := ih history
      omega
  | recordGate i v g p ih =>
    simp only [compile, saved, Straight.instantiate, AdaptiveCircuit.tCount]
    have hi := ih history
    omega
  | measure w p ih =>
    simp only [compile, saved, Straight.instantiate, AdaptiveCircuit.tCount]
    have h0 := ih (Fin.lastCases false history)
    have h1 := ih (Fin.lastCases true history)
    omega

theorem replacement_wellFormed (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (hg : Gate.WellFormed g) : CircuitWellFormed (replacement q g) := by
  unfold replacement
  split
  · rename_i t
    have ht : t ≠ q := by simpa [gateWires, ne_comm] using hq
    simp [kick, controlledZ, CircuitWellFormed, Gate.WellFormed, ht]
  · simpa [CircuitWellFormed] using hg

theorem literals_wellFormed {n s e} (gs : Circuit) (p : Straight n s e)
    (hg : CircuitWellFormed gs) (hp : p.WellFormed) : (literals gs p).WellFormed := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
    exact ⟨hg g (by simp), ih (by intro a ha; exact hg a (by simp [ha]))⟩

theorem compile_wellFormed {n s e} (q : Wire) (p : Straight n s e)
    (hf : Fresh q p) (hp : p.WellFormed) : (compile q p).WellFormed := by
  induction p with
  | done => trivial
  | gate g p ih =>
    cases g with
    | literal g => exact literals_wellFormed _ _ (replacement_wellFormed q g hf.1 hp.1) (ih hf.2 hp.2)
    | whenBit => exact ⟨hp.1, ih hf.2 hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hf.2; exact hp.2⟩
  | measure w p ih => exact ih hf.2 hp

theorem replacement_wires (q : Wire) (g : Gate) :
    circuitWires (replacement q g) ⊆ q :: gateWires g := by
  unfold replacement
  split
  · simp [kick, controlledZ, circuitWires, gateWires, List.subset_def]
  · simp [circuitWires]

theorem literals_within {n s e} (ws : List Wire) (gs : Circuit) (p : Straight n s e)
    (hg : circuitWires gs ⊆ ws) (hp : Within ws p) : Within ws (literals gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
    have h : gateWires g ⊆ ws ∧ circuitWires gs ⊆ ws := by simpa [circuitWires] using hg
    exact ⟨h.1, ih h.2⟩

theorem compile_within {n s e} (q : Wire) (p : Straight n s e) (ws : List Wire)
    (hp : Within ws p) : Within (q::ws) (compile q p) := by
  induction p with
  | done => trivial
  | gate g p ih =>
    cases g with
    | literal g =>
      apply literals_within
      · exact (replacement_wires q g).trans (List.cons_subset_cons q hp.1)
      · exact ih hp.2
    | whenBit => exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), ih hp.2⟩
  | recordGate => exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), by apply_assumption; exact hp.2⟩
  | measure => exact ⟨List.mem_cons_of_mem q hp.1, by apply_assumption; exact hp.2⟩

theorem replacement_length (q : Wire) (g : Gate) :
    (replacement q g).length = 1 + 3 * savedGate g := by
  unfold replacement savedGate
  split <;> rfl

theorem compile_slots {n s e} (q : Wire) (p : Straight n s e) :
    (compile q p).gateSlots = p.gateSlots + 3 * saved p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp [compile, saved, literals_slots, replacement_length, Straight.gateSlots, ih] <;> omega
  | recordGate => simp_all [compile, saved, Straight.gateSlots]; omega
  | measure => exact (by apply_assumption)

theorem saved_le_slots {n s e} (p : Straight n s e) : saved p ≤ p.gateSlots := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      have hg : savedGate g ≤ 1 := by unfold savedGate; split <;> omega
      simp only [saved, Straight.gateSlots]
      omega
    | whenBit => simp only [saved, Straight.gateSlots]; omega
  | recordGate => simp only [saved, Straight.gateSlots]; omega
  | measure => exact (by apply_assumption)

theorem saved_literals {n s e} (gs : Circuit) (p : Straight n s e) :
    saved (literals gs p) = (gs.map savedGate).sum + saved p := by
  induction gs with
  | nil => simp [literals]
  | cons g gs ih =>
    change savedGate g + saved (literals gs p) = _
    rw [ih]
    simp [Nat.add_assoc]

theorem saved_toffoliPrefix {n s e} (a b t q : Wire) (p : Straight n (s+1) e) :
    saved (toffoliPrefix a b t q p) = 1 + saved p := by
  simp [toffoliPrefix, saved_literals, andCompute, parityPhase, xorPhase, saved, savedGate]

theorem saved_lower {n s e} (q : Wire) (p : Straight n s e) (start : Nat)
    (records : Fin s → Fin start) :
    saved (lower q p start records).program = added p + saved p := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp [lower, added, saved, saved_toffoliPrefix, ih, savedGate] <;> omega
    | whenBit => exact ih _ _
  | recordGate => exact (by apply_assumption)
  | measure => exact (by apply_assumption)

def compileEntry (q : Wire) (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := entry.finalCursor
  program := literals (prepare q) (compile q entry.program)

theorem compile_verified {n e} (q : Wire) (p : Straight n 0 e)
    (read : ConstantBit n → Bool) (layout : DecodeLayout) (Q : Secp256k1.Point)
    (psi : State) (hf : Fresh q p) (hp : SupportedOn (fun s => s q = false) psi) :
    Instrument.bornMass (((literals (prepare q) (compile q p)).instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi =
    Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [← expectation_verified, ← expectation_verified, expectation_literals]
  exact compile_expectation q p read Fin.elim0 psi _ hf hp

theorem compileEntry_within (q : Wire) (entry : StraightEntry) (ws : List Wire)
    (hp : Within ws entry.program) : Within (q::ws) (compileEntry q entry).program := by
  apply literals_within
  · simp [prepare, circuitWires, gateWires, List.subset_def]
  · exact compile_within q entry.program ws hp

theorem compile_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds newBounds : Bounds) (q : Wire) (ws : List Wire)
    (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hq : q ∉ ws)
    (hslots : entry.program.gateSlots + 3 * saved entry.program + 2 ≤ limits.gateSlots)
    (hqubits : ws.length + 1 ≤ newBounds.qubits)
    (ht : bounds.tModel + 1 ≤ newBounds.tModel + saved entry.program)
    (hm : entry.finalCursor ≤ newBounds.measurements) :
    Certificate limits layout (compileEntry q entry) newBounds where
  gateBudget := by simpa [compileEntry, literals_slots, compile_slots, prepare, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hslots
  recordBudget := cert.recordBudget
  tableBudget := cert.tableBudget
  candidateBudget := cert.candidateBudget
  wellFormed := literals_wellFormed _ _ (by simp [prepare, CircuitWellFormed, Gate.WellFormed])
    (compile_wellFormed q entry.program (hs.fresh q hq) cert.wellFormed)
  resources := by
    intro Q
    have hsup := (compileEntry_within q entry ws hs).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((compileEntry q entry).instantiate Q).wires.dedup.toFinset).card ≤ (q :: ws).length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (q :: ws))
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((compileEntry q entry).instantiate Q).qubitCount ≤ newBounds.qubits := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc.trans hqubits
    have htc := compile_t q entry.program (readConstant entry.coefficients.get Q) Fin.elim0
    have hto := (cert.resources Q).2.1
    have hmc := (compileEntry q entry).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    refine ⟨hqc, ?_, ?_⟩
    · change ((literals (prepare q) (compile q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      rw [literals_t]
      change 1 + ((compile q entry.program).instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      change (entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel at hto
      omega
    · change ((compileEntry q entry).program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ newBounds.measurements
      have he : ((compileEntry q entry).program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount = entry.finalCursor := by
        simpa only [Nat.add_zero] using hmc
      exact he.le.trans hm
  success := by
    intro Q d hn hd
    change 99 / 100 ≤ Instrument.bornMass
      (((literals (prepare q) (compile q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState)
    rw [compile_verified q entry.program _ layout Q _ (hs.fresh q hq)
      (supportedOn_ket _ _ rfl)]
    exact cert.success Q d hn hd

end
end ShorECDLP.Entrant.Catalyst
end
