import ShorECDLP.Submission.Entrant.StackBase
-- Assembly bundle: generic compiler stages
section
/-! Body-parametric 29-addition Streaming producer and retained public compiler interfaces.
Bundled for bounded kernel-replay memory. Original Apache-2.0 provenance is retained. -/

-- ==== bundle: Compiler ====

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
 theorem reindex {n m s e d} {p : Straight n s e} (hp : AtLeast p d) (f : Fin n → Fin m) :
     AtLeast (reindexStraight f p) d := by simpa [AtLeast, added_reindex] using hp
end AtLeast

attribute [local irreducible] sequenceProgram appendCompiled literalProgram
 remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
 preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
 measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
 divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
 zeroMultiplicationProgram xNegateProgram coordinateProgram










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



attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram
 secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse added residue
 primitiveResources AdaptiveCircuit.tCount


attribute [local irreducible] sequenceProgram appendCompiled literalProgram
 measuredForwardWrapperProgram measuredReverseWrapperProgram








attribute [local irreducible] measuredForwardDataBankProgram measuredReverseDataBankProgram
 multiplyDataProgram multiplyWorkProgram unmultiplyDataProgram divisionAfterResetProgram divisionProgram
 multiplicationAfterResetProgram multiplicationCleanupProgram multiplicationCorrectionProgram
 multiplicationProgram coordinateProgram zeroDivisionProgram zeroMultiplicationProgram








end
end ShorECDLP.Entrant.AndGadget
end

-- ==== bundle: Catalyst ====

section
set_option Elab.async false
namespace ShorECDLP.Entrant.Catalyst
open Quantum Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket
set_option linter.unusedSimpArgs false

def prepare (q : Wire) : Circuit := [.H q, .P .forward 2 q]
def kick (t q : Wire) : Circuit := [.CX t q] ++ controlledZ t q
private theorem phase_two_bundleCatalyst : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring
private theorem upd_twice_bundleCatalyst (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]

theorem kick_ket (t q : Wire) (ht : t ≠ q) (s : BasisState) (hq : s q = false) :
    Quantum.run (kick t q) (Quantum.run (prepare q) (ket s)) =
      Quantum.run (prepare q) (applyGate (.P .forward 2 t) (ket s)) := by
  simp only [kick, prepare, Quantum.run_append, Quantum.run_cons, Quantum.run_nil,
    LinearMap.id_coe, id_eq, applyGate_H_ket, applyGate_P_ket, map_add, map_smul,
    applyGate_CX_ket, run_controlledZ_ket t q _ ht, upd_same, upd_other _ _ _ ht,
    upd_twice_bundleCatalyst, phase_two_bundleCatalyst, hq, Bool.false_eq_true, if_false, if_true, mul_one]
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

private theorem gate_frame_bundleCatalyst (q : Wire) (gs : Circuit) (hq : q ∉ circuitWires gs)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (Quantum.run gs psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary gs .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[], Quantum.run gs⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hpsi
  exact h

private theorem reset_frame_bundleCatalyst (q w : Wire) (hq : q ≠ w) (outcome : Bool)
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
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame_bundleCatalyst q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    | whenBit r v g =>
      simp only [compile, expectation, TemplateGate.instantiate]
      split
      · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame_bundleCatalyst q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
      · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | recordGate i v g p ih =>
    simp only [compile, expectation]
    split
    · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame_bundleCatalyst q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | measure w p ih =>
    simp only [compile, expectation, prepare_reset q w hf.1]
    rw [ih _ _ accept hf.2 (reset_frame_bundleCatalyst q w hf.1 false psi hp), ih _ _ accept hf.2 (reset_frame_bundleCatalyst q w hf.1 true psi hp)]

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

-- ==== bundle: Single/CompilerInterface ====

set_option linter.unusedSectionVars false
set_option maxRecDepth 4096

/-! The generic neighbor producer supplies the static support premise of both public compilers. -/
namespace ShorECDLP.Entrant.Rounded
open Quantum ShorECDLP.Challenge ShorECDLP.Entrant.AndGadget
open ShorECDLP.Paper2607_13816.ChallengeMigration




variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
attribute [local irreducible] entry program readout Single.fixedEntry lowerEntry




end ShorECDLP.Entrant.Rounded

end

-- Assembly bundle: unchanged EEA regression root
section
/-! Regression for the 29-addition, 55-neighbor physical producer before global lowering. -/
namespace ShorECDLP.Entrant.EEARegression
open Challenge
noncomputable section
set_option maxRecDepth 10000

local instance bodyInstance : Single.WindowBody := Single.eeaBody
local instance resourcesInstance : Single.ProducerResources bodyInstance := Single.eeaResources



end
end ShorECDLP.Entrant.EEARegression

end


section
-- WEX compiler credit: core
/-! WEX compiler credit. Residue decomposition follows the public Credit and
CreditWindow development of i34-9 and its later frontier integrations.
Apache-2.0; the imported arithmetic and compiler notices are retained. -/
namespace ShorECDLP.Entrant.WEXCredit
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false



/-- The residue-free identity holds for every reader and every history. -/
theorem exact_t {n s e : Nat} (p : Straight n s e) (hz : residue p = 0)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).tCount = 7 * added p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      have hp : residue p = 0 := by simp only [residue] at hz; omega
      have hg : primitivePhaseCost g = 0 := by simp only [residue] at hz; omega
      have ht := ih hp history
      cases g <;> simp_all [Straight.instantiate, TemplateGate.instantiate,
        AdaptiveCircuit.tCount, ShorECDLP.tCount, tCost, added, primitivePhaseCost]
      omega
    | whenBit r v g =>
      have hp : residue p = 0 := by simp only [residue] at hz; omega
      have hg : tCost g = 0 := by simp only [residue] at hz; omega
      have ht := ih hp history
      simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount, added]
      split <;> simp [ShorECDLP.tCount, hg, ht]
  | recordGate i v g p ih =>
    have hp : residue p = 0 := by simp only [residue] at hz; omega
    have hg : tCost g = 0 := by simp only [residue] at hz; omega
    have ht := ih hp history
    simp only [Straight.instantiate, AdaptiveCircuit.tCount, added]
    split <;> simp [ShorECDLP.tCount, hg, ht]
  | measure w p ih =>
    have hp : residue p = 0 := hz
    have h0 := ih hp (Fin.lastCases false history)
    have h1 := ih hp (Fin.lastCases true history)
    simp only [Straight.instantiate, AdaptiveCircuit.tCount, added, h0, h1, Nat.max_self]

theorem residue_naive_cast {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    residue (NaiveChallenge.castFinish h p) = residue p := by subst f; rfl

theorem added_naive_cast {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    added (NaiveChallenge.castFinish h p) = added p := by subst f; rfl

theorem residue_bridge_records {n s e : Nat} (r : Fin s) (v : Bool)
    (gs : Circuit) (p : Straight n s e) :
    residue (Bridge.recordGates r v gs p) = ShorECDLP.tCount gs + residue p := by
  induction gs with
  | nil => simp [Bridge.recordGates, ShorECDLP.tCount]
  | cons g gs ih => simp [Bridge.recordGates, residue, ShorECDLP.tCount, ih, Nat.add_assoc]

/-- Every vendored instruction is classical or a measured Clifford correction. -/
theorem literal_residue {n : Nat} (p : ECDSAAdd.Program) (start : Nat) :
    residue (Bridge.translate (WEX.literalT (n := n) p) start) = 0 := by
  induction p generalizing start with
  | nil => simp [WEX.literalT, Bridge.translate, residue_naive_cast, residue]
  | cons i p ih =>
    simp only [WEX.literalT] at ih
    cases i <;> simp only [WEX.literalT, List.map_cons, Bridge.translate,
      Bridge.TInstr.step, Bridge.TInstr.meas, Nat.add_zero, residue_naive_cast,
      residue_bridge_records, Bridge.tCount_corrs, residue, primitivePhaseCost,
      Nat.zero_add, ih]

theorem literal_added {n : Nat} (p : ECDSAAdd.Program) (start : Nat) :
    added (Bridge.translate (WEX.literalT (n := n) p) start) = ECDSAAdd.toffoliCount p := by
  have h := exact_t _ (literal_residue (n := n) p start) (fun _ => false) (fun _ => false)
  rw [WEX.literal_program_tCount] at h
  omega

def templateResidue {n : Nat} : TemplateGate n → Nat
  | .literal g => primitivePhaseCost g
  | .whenBit _ _ g => tCost g

theorem residue_gate_program {n s : Nat} (gs : List (TemplateGate n)) :
    residue (gateProgram gs : Straight n s s) = (gs.map templateResidue).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [gateProgram, residue, templateResidue, ih]

def lookupResidue {n : Nat} : LookupOp n → Nat
  | .gates gs => (gs.map templateResidue).sum
  | .erase _ _ _ => 0

theorem residue_lookup {n : Nat} (ops : List (LookupOp n)) (start : Nat) :
    residue (lookupProgram n ops start) = (ops.map lookupResidue).sum := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp [lookupProgram, residue_append, residue_gate_program, ih, lookupResidue]
    | erase a b t => simp [lookupProgram, residue_cast, residue_append, ih, lookupResidue]

theorem residue_unary {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (hl : ∀ label root, ((leaf label root).map templateResidue).sum = 0)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire) :
    ((unaryLookupOps leaf tree root paths).map lookupResidue).sum = 0 := by
  induction tree generalizing root paths with
  | leaf label => simp [unaryLookupOps, lookupResidue, hl]
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp [unaryLookupOps]
    | cons p ps => simp [unaryLookupOps, ihz, iho, computeZeroAnd,
        ordinaryOp, lookupResidue, templateResidue, primitivePhaseCost]

theorem residue_port_leaf {n : Nat} (ports : List (WEX.LookupPort n))
    (address : Nat) (root : Wire) :
    ((WEX.portLeaf ports address root).map templateResidue).sum = 0 := by
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [WEX.portLeaf, templateResidue, tCost] using ih

/-- The protected traversal and its reader-controlled leaves have zero residue. -/
theorem port_residue {n : Nat} (ports : List (WEX.LookupPort n))
    (bits paths : List Wire) (root start : Nat) :
    residue (lookupProgram n (WEX.portOps ports bits paths root) start) = 0 := by
  rw [residue_lookup, WEX.portOps]
  exact residue_unary _ (residue_port_leaf ports) _ _ _



/-- Structural credit for every WEX code list, independent of its geometry. -/
theorem compile_residue {n : Nat} (bits paths : List Wire) (root : Wire)
    (code : WEX.WCode n) (start : Nat) :
    residue (WEX.compile bits paths root code start) = 0 := by
  induction code generalizing start with
  | nil => rfl
  | cons i code ih =>
    cases i with
    | literal p => simp [WEX.compile, residue_naive_cast, residue_append, literal_residue, ih]
    | lookup control ports => simp [WEX.compile, residue_naive_cast, residue_append, port_residue, ih]

theorem compile_added {n : Nat} (bits paths : List Wire) (root : Wire)
    (code : WEX.WCode n) (hl : WEX.LookupLayouts bits paths root code) (start : Nat) :
    added (WEX.compile bits paths root code start) =
      WEX.literalToffolis code + WEX.traversals code * (2 ^ bits.length - 1) := by
  have h := exact_t _ (compile_residue bits paths root code start) (fun _ => false) (fun _ => false)
  rw [WEX.compile_tCount _ _ _ _ _ hl] at h
  simp only [Nat.mul_assoc] at h
  omega







/-- The physical signed-address reflection consists only of CX gates. -/
theorem signed_address_credit {n s : Nat} (q sign : Wire) (bits : List Wire) :
    residue (literalProgram (signedAddressCircuit q sign bits) : Straight n s s) = 0 ∧
      added (literalProgram (signedAddressCircuit q sign bits) : Straight n s s) = 0 := by
  constructor
  · exact residue_literal_HPFree _ (signedAddressCircuit_HPFree q sign bits)
  · rw [added_literal]
    simp only [signedAddressCircuit, tableXorGates]
    have h (c : Wire) (ws : List Wire) : ccxCount (ws.map (Gate.CX c)) = 0 := by
      induction ws <;> simp_all [ccxCount]
    have ha (gs hs : Circuit) : ccxCount (gs ++ hs) = ccxCount gs + ccxCount hs := by
      induction gs with
      | nil => simp [ccxCount]
      | cons g gs ih => cases g <;> simp_all [ccxCount] <;> omega
    rw [ha, h, h]


/-- Combined exact identity for both frontier compiler stages, before Y preparation. -/
theorem four_identity {n s e : Nat} (q y : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((Catalyst.compile y (lower q p s id).program).instantiate read history).tCount +
      3 * added p + Catalyst.saved p = (p.instantiate read history).tCount := by
  have ha := lower_t q p s id read history history (by rfl)
  have hy := Catalyst.compile_t y (lower q p s id).program read history
  rw [Catalyst.saved_lower] at hy
  omega


/-- A companion to the unchanged body contract, with a start-independent count. -/
structure BodyCredit (body : Single.WindowBody) (count : Nat) : Prop where
  zero : ∀ start, residue (body.program start) = 0
  count_eq : ∀ start, added (body.program start) = count

theorem residue_reindex {n m s e : Nat} (p : Straight n s e) (f : Fin n → Fin m) :
    residue (reindexStraight f p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp_all [reindexStraight, reindexGate, residue]
  | recordGate => simp_all [reindexStraight, residue]
  | measure => simp_all [reindexStraight, residue]

theorem first_residue (start : Nat) : residue (Single.firstWindow.program start) = 0 := by
  unfold Single.firstWindow
  dsimp only
  rw [residue_reindex, firstLookupProgram, residue_cast, residue_lookup, firstLookupOps]
  apply residue_unary
  intro label root
  unfold pointLeaf
  generalize (pointRefs _).zip pointLogicalWires = ports
  unfold lookupLeafGates
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [templateResidue, tCost] using ih

theorem first_count [body : Single.WindowBody] [Single.ProducerResources body] (start : Nat) : AtLeast (Single.firstWindow.program start) 65535 := by
  have ht := Single.firstWindow_t_uniform 0 start (fun _ => false)
  have hc := exact_t _ (first_residue start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  unfold AtLeast
  omega

theorem gate_credit {n s e c : Nat} (g : TemplateGate n) {p : Straight n s e}
    (hp : AtLeast p c) : AtLeast (.gate g p) c := by
  cases g with
  | literal g => cases g <;> simp_all [AtLeast, added] <;> omega
  | whenBit => exact hp

theorem prepare_credit {n s e c : Nat} (ws : List Wire) {p : Straight n s e}
    (hp : AtLeast p c) : AtLeast (prepareOuterBank ws p) c := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact gate_credit _ ih

theorem framed_credit {n s m k e f dl dr : Nat} (p : Straight n s m)
    (q : Straight n m k) (r : Straight n k e) (h : e = f)
    (hp : AtLeast p dl) (hq : AtLeast q dr) : AtLeast (Single.framed p q r h) (dl + dr) := by
  unfold Single.framed
  exact gate_credit _ ((hp.append ((hq.append (gate_credit _ (AtLeast.zero _))).castCount
    (Nat.add_zero dr))).castFinish h)

structure CountedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  credit : ∀ start, AtLeast (source.program start) saving

theorem counted_axis {n : Nat} : (ps : List (CountedWindow n)) → (start : Nat) →
    (prior : List (Fin start)) →
    AtLeast (Single.axis (ps.map CountedWindow.source) start prior)
      ((ps.map CountedWindow.saving).sum)
  | [], _, _ => AtLeast.zero _
  | p :: ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine AtLeast.castFinish ?_ _
    refine AtLeast.castCount (AtLeast.append (f := (ps.map CountedWindow.saving).sum)
      (prepare_credit _ (p.credit start)) ?_) (by omega)
    exact (AtLeast.append (AtLeast.zero _) (counted_axis ps _
      (Single.nextPrior p.source.count p.source.wires.length prior))).castCount (by omega)

theorem fixedEntry_credit {n e d : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (hp : AtLeast p d) : AtLeast (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

section Producer
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
variable {c : Nat} (hc : BodyCredit body c)
include hc

theorem signed_credit (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) c := by
  unfold Single.signedWindow
  simpa only [AtLeast, added_reindex] using (hc.count_eq start).ge

def leftCounted : List (CountedWindow 917504) :=
  ⟨Single.firstWindow, 65535, first_count⟩ :: Single.leftSigned.map
    (fun w => ⟨Single.signedWindow w, c, signed_credit hc w⟩)
def rightCounted : List (CountedWindow 917504) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w, c, signed_credit hc w⟩)

/-- Eligible parent credit ignores Clifford framing, feedback, resets and readout. -/
theorem parent_credit : AtLeast Rounded.entry.program (65535 + 29 * c) := by
  have hl := counted_axis (leftCounted hc) 0 List.nil
  have hr := counted_axis (rightCounted hc) (0 + Single.axisCount Single.leftWindows) List.nil
  have hls : (leftCounted hc).map CountedWindow.source = Single.leftWindows := by
    simp [leftCounted, Single.leftWindows]
  have hrs : (rightCounted hc).map CountedWindow.source = Single.rightWindows := by
    simp [rightCounted, Single.rightWindows]
  have hln : ((leftCounted hc).map CountedWindow.saving).sum = 65535 + 16 * c := by
    simp [leftCounted, Single.leftSigned]
    omega
  have hrn : ((rightCounted hc).map CountedWindow.saving).sum = 13 * c := by
    simp [rightCounted, Single.rightSigned]
    omega
  rw [hls, hln] at hl
  rw [hrs, hrn] at hr
  have ht : AtLeast (Single.trial 0) (65535 + 29 * c) := by
    unfold Single.trial
    exact (framed_credit _ _ _ _ hl hr).castCount (by omega)
  have hp : AtLeast Single.program (65535 + 29 * c) := by
    unfold Single.program
    exact ht.castFinish _
  unfold Rounded.entry Rounded.program
  apply fixedEntry_credit
  exact (hp.append (AtLeast.zero _)).castCount (by omega)

/-- Exact component credit supplies a T bound even when the declared body bound is loose. -/
theorem signed_t (w : Single.SignedWindow) (start : Nat)
    (read : ConstantBit 917504 → Bool) (history : Fin start → Bool) :
    (((Single.signedWindow w).program start).instantiate read history).tCount = 7 * c := by
  unfold Single.signedWindow
  rw [reindexStraight_instantiate, exact_t _ (hc.zero start), hc.count_eq start]

def creditLeftCosts : List (Nat × Nat) :=
  (458745, 16) :: Single.leftSigned.map (fun w => (7 * c, w.width))
def creditRightCosts : List (Nat × Nat) :=
  Single.rightSigned.map (fun w => (7 * c, w.width))

theorem signed_costs (ws : List Single.SignedWindow) (read : ConstantBit 917504 → Bool) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1)
      (ws.map Single.signedWindow) (ws.map (fun w => (7 * c, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => (signed_t hc w start read h).le⟩ ih
    rw [Single.signedWindow_wires, List.length_reverse, Single.bank_length _ (Single.window_width w)]

theorem producer_t (Q : Secp256k1.Point) :
    (Rounded.program.instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤
      7 * (65535 + 29 * c) + 56773 := by
  let read := readConstant Single.mixedCoefficientAt Q
  have lc : List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1) Single.leftWindows
      (creditLeftCosts (c := c)) := by
    unfold Single.leftWindows creditLeftCosts
    refine .cons ⟨?_, fun start h => (Single.firstWindow_t_uniform Q start h).le⟩
      (signed_costs hc Single.leftSigned read)
    simp only [Single.firstWindow, List.length_reverse]
    decide
  have hl := Single.axis_t Single.leftWindows read _ lc 0 List.nil Fin.elim0
  have hr : ∀ h, ((Single.axis Single.rightWindows
      (0 + Single.axisCount Single.leftWindows) List.nil).instantiate read h).tCount ≤
      Single.metadataT (creditRightCosts (c := c)) 0 := by
    intro h
    apply Single.axis_t Single.rightWindows read _ _ _ List.nil h
    unfold Single.rightWindows creditRightCosts
    exact signed_costs hc Single.rightSigned read
  have hln : Single.metadataT (creditLeftCosts (c := c)) 0 = 458745 + 16 * (7 * c) + 35245 := by
    simp [creditLeftCosts, Single.leftSigned, List.ofFn_succ, Single.SignedWindow.width,
      Single.metadataT, fourierSlots]
    omega
  have hrn : Single.metadataT (creditRightCosts (c := c)) 0 = 13 * (7 * c) + 21528 := by
    simp [creditRightCosts, Single.rightSigned, List.ofFn_succ, Single.SignedWindow.width,
      Single.metadataT, fourierSlots]
    omega
  have ht := Single.framed_t_le (Single.axis Single.leftWindows 0 List.nil)
    (Single.axis Single.rightWindows (0 + Single.axisCount Single.leftWindows) List.nil)
    (Single.resetBody (0 + Single.axisCount Single.leftWindows + Single.axisCount Single.rightWindows))
    (show 0 + Single.axisCount Single.leftWindows + Single.axisCount Single.rightWindows +
      body.reset.length = 0 + Single.trialCount from by unfold Single.trialCount; omega)
    read Fin.elim0 _ _ hl hr (Single.resetBody_t _ read)
  have hp : (Single.program.instantiate read Fin.elim0).tCount ≤
      Single.metadataT (creditLeftCosts (c := c)) 0 +
        Single.metadataT (creditRightCosts (c := c)) 0 := by
    unfold Single.program Single.trial
    simpa only [castFinish_instantiate] using ht
  have hs := outer_append_t_le Single.program Rounded.readout read Fin.elim0 0
    (fun h => (Rounded.readout_t read h).le)
  change ((Single.program.append Rounded.readout).instantiate read Fin.elim0).tCount ≤ _
  rw [hln] at hp
  rw [hrn] at hp
  omega

end Producer
/-- Both compiler stages with their two fresh workspace wires. -/
def fourEntry (q y : Wire) (entry : StraightEntry) : StraightEntry :=
  Catalyst.compileEntry y (lowerEntry q entry)

def fourBounds (entry : StraightEntry) (ws : List Wire) (credit residual : Nat) : Bounds :=
  ⟨ws.length + 2, 4 * credit + residual + 1, entry.finalCursor + added entry.program⟩

/-- A source certificate and a lower credit suffice; existing literal S gates help further. -/
theorem four_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (ws : List Wire) (credit residual : Nat) (q y : Wire)
    (cert : Certificate limits layout entry
      ⟨ws.length, 7 * credit + residual, entry.finalCursor⟩)
    (hs : Within ws entry.program) (hq : q ∉ ws) (hy : y ∉ q :: ws)
    (hc : credit ≤ added entry.program)
    (hslots : entry.program.gateSlots + 21 * added entry.program +
      3 * Catalyst.saved entry.program + 2 ≤ limits.gateSlots)
    (hrecords : entry.finalCursor + added entry.program ≤ limits.measurements) :
    Certificate limits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ws credit residual) := by
  let middle : Bounds := ⟨ws.length + 1, 5 * credit + residual,
    entry.finalCursor + added entry.program⟩
  have hm : Certificate limits (lowerLayout q entry layout) (lowerEntry q entry) middle :=
    lower_certificate limits layout entry _ middle q ws cert hs hq
      (by omega) hrecords (by rfl) (by dsimp [middle]; omega) (by rfl)
  apply Catalyst.compile_certificate limits (lowerLayout q entry layout) (lowerEntry q entry)
    middle _ y (q :: ws) hm (lower_within q entry.program ws hs 0 Fin.elim0) hy
  · simp only [lowerEntry, lower_slots, Catalyst.saved_lower]
    omega
  · simp [fourBounds]
  · have h := Catalyst.saved_lower q entry.program 0 Fin.elim0
    change 5 * credit + residual + 1 ≤ 4 * credit + residual + 1 +
      Catalyst.saved (lower q entry.program 0 Fin.elim0).program
    omega
  · have h := lower_finish q entry.program 0 Fin.elim0
    change (lower q entry.program 0 Fin.elim0).finish ≤ entry.finalCursor + added entry.program
    omega

section ProducerCompiler
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
variable {c : Nat} (hc : BodyCredit body c)
include hc


end ProducerCompiler

attribute [local irreducible] Nat.add Nat.mul ECDSAAdd.toffoliCount ECDSAAdd.Baselines.normalizeProgram
  WEX.literalToffolis WEX.normalizeW WEX.wFiniteOne WEX.rowAddCode
  WEX.compile Bridge.translate WEX.nProgram WEX.addProgram WEX.prefixProgram WEX.suffixProgram


theorem n_residue (start : Nat) : residue (WEX.nProgram start) = 0 := by
  unfold WEX.nProgram WEX.literalFixed
  rw [residue_naive_cast]
  exact literal_residue _ _

theorem n_added (start : Nat) : added (WEX.nProgram start) =
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram) := by
  unfold WEX.nProgram WEX.literalFixed
  rw [added_naive_cast, literal_added]



theorem prefix_credit (start : Nat) :
    residue (WEX.prefixProgram start) = 0 ∧ added (WEX.prefixProgram start) = 0 := by
  have h := signed_address_credit (n := 32768) (s := start) 836 870 WEX.windowBits
  unfold WEX.prefixProgram
  simp only [residue_append, added_append, h.1, h.2, Nat.add_zero]
  exact ⟨by simp [residue_literal, primitivePhaseCost], by simp [added_literal, ccxCount]⟩

theorem suffix_credit (start : Nat) :
    residue (WEX.suffixProgram start) = 0 ∧ added (WEX.suffixProgram start) = 0 := by
  have h := signed_address_credit (n := 32768) (s := start) 836 870 WEX.windowBits
  unfold WEX.suffixProgram
  simp only [residue_append, added_append, h.1, h.2, Nat.zero_add]
  exact ⟨by simp [residue_literal, primitivePhaseCost], by simp [added_literal, ccxCount]⟩




end
end ShorECDLP.Entrant.WEXCredit

end


section
-- WEX compiler credit: compose
namespace ShorECDLP.Entrant.WEXCredit
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
/-- Exact structural credit composes without expanding either input program. -/
def ProgramCredit {n s e : Nat} (p : Straight n s e) (count : Nat) : Prop :=
  residue p = 0 ∧ added p = count

theorem credit_append {n s m e c d : Nat} {p : Straight n s m} {q : Straight n m e}
    (hp : ProgramCredit p c) (hq : ProgramCredit q d) : ProgramCredit (p.append q) (c + d) := by
  rcases hp with ⟨hp0, hpc⟩
  rcases hq with ⟨hq0, hqc⟩
  simp only [ProgramCredit, residue_append, added_append, hp0, hpc, hq0, hqc, Nat.zero_add]
  exact ⟨True.intro, True.intro⟩

theorem credit_cast {n s e f c : Nat} (h : e = f) {p : Straight n s e}
    (hp : ProgramCredit p c) : ProgramCredit (castFinish h p) c := by
  simpa only [ProgramCredit, residue_cast, added_cast] using hp

theorem credit_naive_cast {n s e f c : Nat} (h : e = f) {p : Straight n s e}
    (hp : ProgramCredit p c) : ProgramCredit (NaiveChallenge.castFinish h p) c := by
  simpa only [ProgramCredit, residue_naive_cast, added_naive_cast] using hp







end
end ShorECDLP.Entrant.WEXCredit

end


section
-- Final WEX assembly glue
namespace ShorECDLP.Entrant.WEXFinal
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

local instance bodyInstance : Single.WindowBody := WEX.compactBody
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEX.compactBody
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)


attribute [local irreducible] WEX.compile Bridge.translate WEX.literalFixed WEX.compilerFixed
  WEX.nProgram WEX.addProgram WEX.prefixProgram WEX.suffixProgram
  ECDSAAdd.toffoliCount ECDSAAdd.Baselines.normalizeProgram WEX.literalToffolis WEX.normalizeW
  Straight.instantiate AdaptiveCircuit.tCount Nat.add Nat.mul

def windowCCX : Nat :=
  2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram) +
    WEX.literalToffolis (WEX.normalizeW (WEX.rowAddCode WEX.probeRows)) + 21*32767


attribute [local irreducible] windowCCX AndGadget.added








attribute [local irreducible] Rounded.entry Rounded.program Single.fixedEntry
  AndGadget.lower Catalyst.saved Catalyst.compile WEX.compactBody








attribute [local irreducible] fourEntry lowerLayout









end
end ShorECDLP.Entrant.WEXFinal



end

namespace ShorECDLP.Entrant.Schedule33








end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.WindowMassSharpProof
open Finset
noncomputable section
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 300

end
end ShorECDLP.Entrant.WindowMassSharpProof

namespace ShorECDLP.Entrant.Schedule33

open ShorECDLP.Secp256k1



end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 300

end
end ShorECDLP.Entrant.NeighborReadout

namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 300
def params265 : DecoderParams := ⟨265,208,by decide,by decide,by decide,by decide⟩




end
end ShorECDLP.Entrant.NeighborReadout

namespace ShorECDLP.Entrant.Schedule33
open ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

noncomputable def increment (P : Point) (width exponent v : Nat) : Point :=
  ((2 * (v : Int) - (2 : Int)^width + 1) : Int) •
    ((Single.halfOrder * 2^exponent) • P)

theorem increment_offset (P : Point) (hr : order • P = 0)
    (width exponent v : Nat) (hw : width = 13 ∨ width = 14) :
    increment P width exponent v + Single.offsetScalar width exponent • P =
      (v * 2^exponent) • P := by
  have hh : Single.halfOrder ≤ 2^(width-1) + order := by
    have hl : Single.halfOrder ≤ order := by norm_num [Single.halfOrder, order]
    exact hl.trans (Nat.le_add_left _ _)
  have he : (2^(width-1) + order - Single.halfOrder) • P + Single.halfOrder • P =
      2^(width-1) • P := by
    rw [← add_nsmul, Nat.sub_add_cancel hh, add_nsmul, hr, add_zero]
  have hoff : Single.offsetScalar width exponent • P =
      2^(width-1) • (2^exponent • P) - (Single.halfOrder * 2^exponent) • P := by
    unfold Single.offsetScalar
    rw [mul_smul, smul_comm (2^(width-1) + order - Single.halfOrder) (2^exponent),
      eq_sub_iff_add_eq.mpr he, nsmul_sub]
    simp only [mul_smul]
    rw [smul_comm (2^exponent) (2^(width-1)), smul_comm (2^exponent) Single.halfOrder]
  let H := (Single.halfOrder * 2^exponent) • P
  have hd : H + H = 2^exponent • P := by
    change (Single.halfOrder * 2^exponent) • P + (Single.halfOrder * 2^exponent) • P = _
    rw [mul_smul, smul_comm Single.halfOrder (2^exponent), ← nsmul_add]
    exact congrArg (fun R : Point => 2^exponent • R)
      (signedWindowHalfPoint_double P order (by decide +kernel) hr)
  have hp : (2 : Int)^width = 2 * (2^(width-1) : Nat) := by
    rcases hw with rfl | rfl <;> norm_num
  have hcalc : ((2*(v:Int)-(2:Int)^width+1) • H) +
      (2^(width-1) • (H+H) - H) = v • (H+H) := by
    rw [hp]
    module
  change ((2*(v:Int)-(2:Int)^width+1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2^exponent) P).symm

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33

inductive Digit where
  | left14 (index : Fin 16)
  | left13 (index : Fin 2)
  | right14 (index : Fin 13)
  | right13 (index : Fin 2)

def Digit.width : Digit → Nat
  | .left14 _ | .right14 _ => 14
  | .left13 _ | .right13 _ => 13

def Digit.exponent : Digit → Nat
  | .left14 j => 236 - 14 * j.val
  | .left13 j => 13 - 13 * j.val
  | .right14 j => 194 - 14 * j.val
  | .right13 j => 13 - 13 * j.val

def firstRow (a : Fin 65536) : Fin 319488 := ⟨a.val, by omega⟩

def row : (w : Digit) → Fin (2^(w.width-1)) → Fin 319488
  | .left14 j, a => ⟨65536 + j.val*8192 + a.val, by
    have h : a.val < 8192 := by
      simpa only [Digit.width] using a.isLt
    omega⟩
  | .left13 j, a => ⟨196608 + j.val*4096 + a.val, by
    have h : a.val < 4096 := by
      simpa only [Digit.width] using a.isLt
    omega⟩
  | .right14 j, a => ⟨204800 + j.val*8192 + a.val, by
    have h : a.val < 8192 := by
      simpa only [Digit.width] using a.isLt
    omega⟩
  | .right13 j, a => ⟨311296 + j.val*4096 + a.val, by
    have h : a.val < 4096 := by
      simpa only [Digit.width] using a.isLt
    omega⟩

theorem width_cases (w : Digit) : w.width = 13 ∨ w.width = 14 := by
  cases w <;> simp [Digit.width]



open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

def leftDigits : List Digit := List.ofFn (fun j : Fin 16 => .left14 j) ++
  List.ofFn (fun j : Fin 2 => .left13 j)

def rightDigits : List Digit := List.ofFn (fun j : Fin 13 => .right14 j) ++
  List.ofFn (fun j : Fin 2 => .right13 j)

theorem left_widths : leftDigits.map Digit.width =
    List.replicate 16 14 ++ List.replicate 2 13 := by
  simp [leftDigits, List.ofFn_succ, Digit.width, List.replicate]

theorem right_widths : rightDigits.map Digit.width =
    List.replicate 13 14 ++ List.replicate 2 13 := by
  simp [rightDigits, List.ofFn_succ, Digit.width, List.replicate]



def leftOffset : Nat := (leftDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum

def rightOffset : Nat := (rightDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum

def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients (v * 2^250 + leftOffset) rightOffset

def signedCoefficients (w : Digit) (a : Nat) : PointCoeff :=
  match w with
  | .left14 _ | .left13 _ => coefficients (Single.oddScalar w.exponent a) 0
  | .right14 _ | .right13 _ => coefficients 0 (Single.oddScalar w.exponent a)

def coefficientAt (i : Fin 319488) : PointCoeff :=
  if i.val < 65536 then initialCoefficients i.val
  else if i.val < 196608 then
    coefficients (Single.oddScalar (236 - 14 * ((i.val - 65536) / 8192)) ((i.val - 65536) % 8192)) 0
  else if i.val < 204800 then
    coefficients (Single.oddScalar (13 - 13 * ((i.val - 196608) / 4096)) ((i.val - 196608) % 4096)) 0
  else if i.val < 311296 then
    coefficients 0 (Single.oddScalar (194 - 14 * ((i.val - 204800) / 8192)) ((i.val - 204800) % 8192))
  else coefficients 0 (Single.oddScalar (13 - 13 * ((i.val - 311296) / 4096)) ((i.val - 311296) % 4096))

theorem coefficientAt_first (a : Fin 65536) :
    coefficientAt (firstRow a) = initialCoefficients a.val := by
  simp [coefficientAt, firstRow, a.isLt]


theorem coefficientAt_row (w : Digit) (a : Fin (2^(w.width-1))) :
    coefficientAt (row w a) = signedCoefficients w a.val := by
  cases w with
  | left14 j =>
    have ha : a.val < 8192 := by
      simpa only [Digit.width] using a.isLt
    have he : (row (.left14 j) a).val < 196608 := by simp only [row]; omega
    have hj : ((row (.left14 j) a).val - 65536) / 8192 = j.val := by simp only [row]; omega
    have hh : ((row (.left14 j) a).val - 65536) % 8192 = a.val := by simp only [row]; omega
    have hn : ¬ (row (.left14 j) a).val < 65536 := by simp only [row]; omega
    simp [coefficientAt, hn, he, hj, hh, signedCoefficients, Digit.exponent]
  | left13 j =>
    have ha : a.val < 4096 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.left13 j) a).val < 65536 := by simp only [row]; omega
    have he : (row (.left13 j) a).val < 204800 := by simp only [row]; omega
    have hbase : ¬ (row (.left13 j) a).val < 196608 := by simp only [row]; omega
    have hj : ((row (.left13 j) a).val - 196608) / 4096 = j.val := by simp only [row]; omega
    have hh : ((row (.left13 j) a).val - 196608) % 4096 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, he, hj, hh, signedCoefficients, Digit.exponent]
  | right14 j =>
    have ha : a.val < 8192 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.right14 j) a).val < 65536 := by simp only [row]; omega
    have hn1 : ¬ (row (.right14 j) a).val < 196608 := by simp only [row]; omega
    have he : (row (.right14 j) a).val < 311296 := by simp only [row]; omega
    have hbase : ¬ (row (.right14 j) a).val < 204800 := by simp only [row]; omega
    have hj : ((row (.right14 j) a).val - 204800) / 8192 = j.val := by simp only [row]; omega
    have hh : ((row (.right14 j) a).val - 204800) % 8192 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, hn1, he, hj, hh, signedCoefficients, Digit.exponent]
  | right13 j =>
    have ha : a.val < 4096 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.right13 j) a).val < 65536 := by simp only [row]; omega
    have hn1 : ¬ (row (.right13 j) a).val < 196608 := by simp only [row]; omega
    have hn2 : ¬ (row (.right13 j) a).val < 204800 := by simp only [row]; omega
    have hbase : ¬ (row (.right13 j) a).val < 311296 := by simp only [row]; omega
    have hj : ((row (.right13 j) a).val - 311296) / 4096 = j.val := by simp only [row]; omega
    have hh : ((row (.right13 j) a).val - 311296) % 4096 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, hn1, hn2, hj, hh, signedCoefficients, Digit.exponent]


open ShorECDLP.Secp256k1

noncomputable def Digit.base (Q : Point) : Digit → Point
  | .left14 _ | .left13 _ => G
  | .right14 _ | .right13 _ => Q

noncomputable def positivePoint (Q : Point) (w : Digit) (a : Nat) : Point :=
  Single.oddScalar w.exponent a • w.base Q

theorem signedCoefficients_point (Q : Point) (hQ : order • Q = 0)
    (w : Digit) (a : Nat) :
    constantPoint Q (signedCoefficients w a) = positivePoint Q w a := by
  cases w <;> simp [signedCoefficients, coefficients_point _ _ Q hQ,
    positivePoint, Digit.base]

theorem positivePoint_ne_zero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (address : Nat) (ha : address < 2^(w.width-1)) :
    positivePoint Q w address ≠ 0 := by
  let P := w.base Q
  have hp : P ≠ 0 := by
    cases w with
    | left14 _ | left13 _ => exact G_ne_zero
    | right14 _ | right13 _ => exact hn
  have hr : order • P = 0 := by
    cases w with
    | left14 _ | left13 _ => exact generator_nsmul_eq_zero
    | right14 _ | right13 _ => exact hQ
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf P = order := addOrderOf_eq_prime hr hp
  have hw : 2^(w.width-1) ≤ 32768 := by cases w <;> norm_num [Digit.width]
  have hl : 65535 < order := by norm_num [order]
  have hs : 0 < 2*address+1 ∧ 2*address+1 < order := by omega
  have hh : 0 < Single.halfOrder ∧ Single.halfOrder < order := by
    dsimp [Single.halfOrder]; omega
  have hodd : ¬ order ∣ 2*address+1 :=
    fun h => (Nat.le_of_dvd hs.1 h).not_gt hs.2
  have hhalf : ¬ order ∣ Single.halfOrder := fun h => (Nat.le_of_dvd hh.1 h).not_gt hh.2
  have htwo : ¬ order ∣ 2 := fun h => (Nat.le_of_dvd (by decide : 0 < 2) h).not_gt (by omega)
  intro hz
  have he : ((2*address+1)*2^w.exponent*Single.halfOrder) • P = 0 := by
    simpa only [positivePoint, Single.oddScalar] using hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  rw [ho] at hd
  rcases order_prime.dvd_mul.mp hd with hd | hd
  · rcases order_prime.dvd_mul.mp hd with hd | hd
    · exact hodd hd
    · exact htwo (order_prime.dvd_of_dvd_pow hd)
  · exact hhalf hd


open Quantum ShorECDLP.Paper2607_13816

noncomputable def initialPoint (Q : Point) (v : Nat) : Point :=
  (v * 2^250 + leftOffset) • G + rightOffset • Q

theorem initialCoefficients_point (Q : Point) (hQ : order • Q = 0) (v : Nat) :
    constantPoint Q (initialCoefficients v) = initialPoint Q v := by
  unfold initialCoefficients initialPoint
  exact coefficients_point _ _ Q hQ

noncomputable def firstUpdate (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (initialPoint Q (Single.digit 16 s)) s

def firstWindow : Single.Window 319488 :=
  ⟨(Single.bank 16).reverse, 65535, fun start => reindexStraight firstRow (firstLookupProgram start)⟩

theorem initialLookup_circuit (Q : Point) (hQ : order • Q = 0) :
    lookupCircuit (readConstant (fun i : Fin 65536 => initialCoefficients i.val) Q) firstLookupOps =
      physicalPointLookup (initialPoint Q) := by
  rw [firstLookupOps, unaryLookupOps_circuit]
  unfold physicalPointLookup directPointLookup tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  obtain ⟨i, hi, he⟩ := tableAddressTree_label _ 0 1 l hl
  have hlt : l < 65536 := by simpa [he] using hi
  rw [pointLeaf_instantiate]
  simp only [Nat.mod_eq_of_lt hlt, initialCoefficients_point Q hQ, pointTableMask]

theorem firstWindow_run (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant coefficientAt Q) history).run =
      (physicalPointLookup (initialPoint Q)).run := by
  unfold firstWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex firstRow _ _ Q coefficientAt_first]
  rw [firstLookupProgram, castFinish_instantiate, lookupProgram_run, initialLookup_circuit Q hQ]

theorem firstWindow_coherent (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    CoherentlyImplementsOn ((firstWindow.program start).instantiate
      (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (firstUpdate Q))
      (DirectPointLookupValid (List.range' 519 16) 836) := by
  unfold CoherentlyImplementsOn
  rw [firstWindow_run Q hQ start history]
  exact physicalPointLookup_coherent (initialPoint Q)


theorem firstWindow_t (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 458745 := by
  unfold firstWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex firstRow _ _ Q coefficientAt_first]
  rw [firstLookupProgram, castFinish_instantiate, lookupProgram_tCount, initialLookup_circuit Q hQ]
  exact (physicalPointLookup_resources _).1

attribute [local irreducible] firstLookupProgram

set_option maxRecDepth 10000 in
theorem firstWindow_wellFormed (start : Nat) : (firstWindow.program start).WellFormed := by
  unfold firstWindow
  exact (reindexStraight_wellFormed firstRow (firstLookupProgram start)).mpr (firstLookupProgram_wellFormed start)

theorem firstWindow_slots (start : Nat) : (firstWindow.program start).gateSlots ≤ 3000000000 := by
  have h := actualFirstWindow_slots start
  simp only [actualFirstWindow, reindexStraight_gateSlots] at h
  unfold firstWindow
  rw [reindexStraight_gateSlots]
  exact h.trans (by norm_num)

theorem firstWindow_support (start : Nat) :
    straightWires (firstWindow.program start) ⊆ resetWires := by
  have h := actualFirstWindow_support_static start
  simp only [actualFirstWindow, straightWires_reindex] at h
  unfold firstWindow
  rw [straightWires_reindex]
  exact h

theorem first_residue (start : Nat) : AndGadget.residue (firstWindow.program start) = 0 := by
  have h := WEXCredit.first_residue start
  unfold Single.firstWindow at h
  unfold firstWindow
  simpa only [WEXCredit.residue_reindex] using h


theorem first_count (start : Nat) : AndGadget.AtLeast (firstWindow.program start) 65535 := by
  have ht := firstWindow_t 0 (by simp) start (fun _ => false)
  have hc := WEXCredit.exact_t _ (first_residue start)
    (readConstant coefficientAt 0) (fun _ => false)
  unfold AndGadget.AtLeast
  omega

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration




end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open ShorECDLP.Paper2607_13816.ChallengeMigration

def leftCosts (cost14 cost13 : Nat) : List (Nat × Nat) :=
  (458745, 16) :: List.replicate 16 (cost14, 14) ++ List.replicate 2 (cost13, 13)

def rightCosts (cost14 cost13 : Nat) : List (Nat × Nat) :=
  List.replicate 13 (cost14, 14) ++ List.replicate 2 (cost13, 13)

theorem left_t_budget (cost14 cost13 : Nat) :
    Single.metadataT (leftCosts cost14 cost13) 0 =
      458745 + 16 * cost14 + 2 * cost13 + 35245 := by
  simp [leftCosts, List.replicate, Single.metadataT, fourierSlots]
  omega

theorem right_t_budget (cost14 cost13 : Nat) :
    Single.metadataT (rightCosts cost14 cost13) 0 =
      13 * cost14 + 2 * cost13 + 21528 := by
  simp [rightCosts, List.replicate, Single.metadataT, fourierSlots]
  omega

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Paper2607_13816.ChallengeMigration

def SignedWeights (Q P : Point) : List Digit → Prop
  | [] => True
  | w :: ws => w.base Q = P ∧ w.exponent = (ws.map Digit.width).sum ∧ SignedWeights Q P ws

theorem left_signed_weights (Q : Point) : SignedWeights Q G leftDigits := by
  norm_num [leftDigits, List.ofFn_succ, SignedWeights, Digit.width, Digit.exponent, Digit.base]

theorem right_signed_weights (Q : Point) : SignedWeights Q Q rightDigits := by
  norm_num [rightDigits, List.ofFn_succ, SignedWeights, Digit.width, Digit.exponent, Digit.base]

theorem modelWeights {n : Nat} {read : ConstantBit n → Bool}
    (Q P : Point) (hr : order • P = 0) (f : Digit → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = w.width)
    (hpoint : ∀ w v, (f w).point v = increment (w.base Q) w.width w.exponent v)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (ws : List Digit) (hw : SignedWeights Q P ws) : ModelWeights P (ws.map f) := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · intro v
      have hwidths : ((ws.map f).map (fun w => w.physical.wires.length)).sum =
          (ws.map Digit.width).sum := by
        simp only [List.map_map, Function.comp_def, hwidth]
      rw [hwidths, ← hw.2.1, hpoint, hbias, hw.1]
      exact increment_offset P hr w.width w.exponent v (width_cases w)
    · exact ih hw.2.2

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Paper2607_13816.ChallengeMigration

theorem left_base (Q : Point) (w : Digit) (hw : w ∈ leftDigits) : w.base Q = G := by
  simp only [leftDigits, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem right_base (Q : Point) (w : Digit) (hw : w ∈ rightDigits) : w.base Q = Q := by
  simp only [rightDigits, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem left_modelWeights {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (first : WindowModel read) (f : Digit → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = w.width)
    (hpoint : ∀ w v, (f w).point v = increment (w.base Q) w.width w.exponent v)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (hfirst : ∀ v, first.point v = initialPoint Q v)
    (hfirstBias : first.bias = -(leftOffset • G + rightOffset • Q)) :
    ModelWeights G (first :: leftDigits.map f) := by
  constructor
  · intro v
    have hwidths : ((leftDigits.map f).map (fun w => w.physical.wires.length)).sum = 250 := by
      simp only [List.map_map, Function.comp_def, hwidth, left_widths]
      norm_num [List.replicate]
    rw [hwidths, hfirst, hfirstBias]
    unfold initialPoint
    simp only [add_nsmul]
    abel
  · exact modelWeights Q G generator_nsmul_eq_zero f hwidth hpoint hbias leftDigits (left_signed_weights Q)

theorem sum_nsmul (xs : List Nat) (P : Point) : (xs.map (fun k => k • P)).sum = xs.sum • P := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, add_nsmul]

theorem signed_bias_sum {n : Nat} {read : ConstantBit n → Bool}
    (Q P : Point) (f : Digit → WindowModel read)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (ws : List Digit) (hbase : ∀ w ∈ ws, w.base Q = P) :
    ((ws.map f).map WindowModel.bias).sum =
      (ws.map (fun w => Single.offsetScalar w.width w.exponent)).sum • P := by
  rw [← sum_nsmul]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  rw [hbias, hbase w hw]

theorem model_bias_cancels {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (first : WindowModel read) (f : Digit → WindowModel read)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (hfirstBias : first.bias = -(leftOffset • G + rightOffset • Q)) :
    ((first :: leftDigits.map f).map WindowModel.bias).sum +
      ((rightDigits.map f).map WindowModel.bias).sum = 0 := by
  simp only [List.map_cons, List.sum_cons]
  rw [signed_bias_sum Q G f hbias leftDigits (left_base Q),
    signed_bias_sum Q Q f hbias rightDigits (right_base Q), hfirstBias]
  change -(leftOffset • G + rightOffset • Q) + leftOffset • G + rightOffset • Q = 0
  abel

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Paper2607_13816.ChallengeMigration
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]

theorem model_kernel {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (hQ : order • Q = 0) (root : BasisState) (ψ : State)
    (first : WindowModel read) (f : Digit → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = w.width)
    (hpoint : ∀ w v, (f w).point v = increment (w.base Q) w.width w.exponent v)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (hfirstPoint : ∀ v, first.point v = initialPoint Q v)
    (hfirstBias : first.bias = -(leftOffset • G + rightOffset • Q))
    (hfirstRule : FirstRule root ψ first)
    (hpointRule : ∀ w ∈ leftDigits ++ rightDigits, PointRule root (f w)) :
    KernelLaw Q root (first :: leftDigits.map f) (rightDigits.map f) ψ := by
  apply kernelLaw_of_windows Q root ψ first (leftDigits.map f) (rightDigits.map f)
  · exact hfirstRule
  · intro w hw
    rw [← List.map_append] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hpointRule v hv
  · exact left_modelWeights Q first f hwidth hpoint hbias hfirstPoint hfirstBias
  · exact modelWeights Q Q hQ f hwidth hpoint hbias rightDigits (right_signed_weights Q)
  · exact model_bias_cancels Q first f hbias hfirstBias

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

def logicalValue13 (low : Nat) (sign : Bool) : Nat := low + 4096 * sign.toNat
def logicalValue14 (low : Nat) (sign : Bool) : Nat := low + 8192 * sign.toNat
theorem padded_address13 (low : Nat) (sign : Bool) (hlow : low < 4096) :
    signedTableAddress 32768 (Single.paddedValue low sign) % 4096 =
      signedTableAddress 4096 (logicalValue13 low sign) := by
  cases sign with
  | false =>
    have hbig : low < 32768 := by omega
    have hsub : 32767 - low = 28672 + (4095 - low) := by omega
    have hrem : 4095 - low < 4096 := by omega
    simp only [Single.paddedValue, logicalValue13, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      signedTableAddress, if_pos hbig, if_pos hlow]
    rw [hsub, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hrem]
  | true =>
    have hbig : ¬ low + 32768 < 32768 := by omega
    have hsmall : ¬ low + 4096 < 4096 := by omega
    simp only [Single.paddedValue, logicalValue13, Bool.toNat_true, Nat.mul_one,
      signedTableAddress, if_neg hbig, if_neg hsmall]
    have h1 : low + 32768 - 32768 = low := by omega
    have h2 : low + 4096 - 4096 = low := by omega
    rw [h1, h2, Nat.mod_eq_of_lt hlow]

theorem padded_address14 (low : Nat) (sign : Bool) (hlow : low < 8192) :
    signedTableAddress 32768 (Single.paddedValue low sign) % 8192 =
      signedTableAddress 8192 (logicalValue14 low sign) := by
  cases sign with
  | false =>
    have hbig : low < 32768 := by omega
    have hsub : 32767 - low = 24576 + (8191 - low) := by omega
    have hrem : 8191 - low < 8192 := by omega
    simp only [Single.paddedValue, logicalValue14, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      signedTableAddress, if_pos hbig, if_pos hlow]
    rw [hsub, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hrem]
  | true =>
    have hbig : ¬ low + 32768 < 32768 := by omega
    have hsmall : ¬ low + 8192 < 8192 := by omega
    simp only [Single.paddedValue, logicalValue14, Bool.toNat_true, Nat.mul_one,
      signedTableAddress, if_neg hbig, if_neg hsmall]
    have h1 : low + 32768 - 32768 = low := by omega
    have h2 : low + 8192 - 8192 = low := by omega
    rw [h1, h2, Nat.mod_eq_of_lt hlow]



open Quantum

theorem address_append (xs ys : List Wire) (s : BasisState) :
    tableAddressValue (xs ++ ys) s =
      tableAddressValue xs s + 2^xs.length * tableAddressValue ys s := by
  induction xs with
  | nil => simp [tableAddressValue]
  | cons x xs ih =>
    simp only [List.cons_append, tableAddressValue, List.length_cons, ih, pow_succ]
    ring

def bank (width : Nat) : List Wire := List.range' 855 (width-1) ++ [870]

def digit (width : Nat) (s : BasisState) : Nat := tableAddressValue (bank width) s

theorem bank_length (width : Nat) (hw : width = 13 ∨ width = 14) :
    (bank width).length = width := by
  rcases hw with rfl | rfl <;> simp [bank]

theorem digit13_low (s : BasisState) :
    digit 13 s = logicalValue13 (tableAddressValue (List.range' 855 12) s) (s 870) := by
  change tableAddressValue (List.range' 855 12 ++ [870]) s =
    tableAddressValue (List.range' 855 12) s + 4096 * (s 870).toNat
  rw [address_append]
  simp [tableAddressValue]

theorem digit14_low (s : BasisState) :
    digit 14 s = logicalValue14 (tableAddressValue (List.range' 855 13) s) (s 870) := by
  change tableAddressValue (List.range' 855 13 ++ [870]) s =
    tableAddressValue (List.range' 855 13) s + 8192 * (s 870).toNat
  rw [address_append]
  simp [tableAddressValue]

theorem physical_padding13 (s : BasisState) (h867 : s 867 = false)
    (h868 : s 868 = false) (h869 : s 869 = false) :
    windowRawDigit 0 s = Single.paddedValue (tableAddressValue (List.range' 855 12) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, Single.paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat, h867, h868, h869]

theorem physical_padding14 (s : BasisState) (h868 : s 868 = false) (h869 : s 869 = false) :
    windowRawDigit 0 s = Single.paddedValue (tableAddressValue (List.range' 855 13) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, Single.paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat, h868, h869]


theorem bank_nodup (width : Nat) (hw : width = 13 ∨ width = 14) : (bank width).Nodup := by
  rcases hw with rfl | rfl <;> decide +kernel

theorem bank_subset (width : Nat) (hw : width = 13 ∨ width = 14) :
    ∀ v ∈ bank width, v ∈ streamAddress := by
  rcases hw with rfl | rfl <;> decide +kernel

theorem bank_not_point (width : Nat) (hw : width = 13 ∨ width = 14) :
    ∀ v ∈ bank width, v ∉ pointLogicalWires := by
  intro v hv
  exact (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v
    (bank_subset width hw v hv)

theorem digit_low_sign (width : Nat) (hw : width = 13 ∨ width = 14) (s : BasisState) :
    digit width s < 2^(width-1) ↔ s 870 = false := by
  rcases hw with rfl | rfl
  · rw [digit13_low]
    have hb := tableAddressValue_lt (List.range' 855 12) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue13]
  · rw [digit14_low]
    have hb := tableAddressValue_lt (List.range' 855 13) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue14]

theorem selected_address_alias (width : Nat) (hw : width = 13 ∨ width = 14) (s : BasisState)
    (h868 : s 868 = false) (h869 : s 869 = false) (h867 : width = 13 → s 867 = false) :
    signedTableAddress 32768 (windowRawDigit 0 s) % 2^(width-1) =
      signedTableAddress (2^(width-1)) (digit width s) := by
  rcases hw with rfl | rfl
  · rw [physical_padding13 s (h867 rfl) h868 h869, digit13_low]
    exact padded_address13 _ _ (by simpa using tableAddressValue_lt (List.range' 855 12) s)
  · rw [physical_padding14 s h868 h869, digit14_low]
    exact padded_address14 _ _ (by simpa using tableAddressValue_lt (List.range' 855 13) s)

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open ShorECDLP.Secp256k1 ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

theorem selected_increment (Q : Point) (w : Digit) (s : BasisState)
    (h868 : s 868 = false) (h869 : s 869 = false) (h867 : w.width = 13 → s 867 = false) :
    (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))) =
      increment (w.base Q) w.width w.exponent (digit w.width s) := by
  have hpow : (2 : Int)^w.width = 2 * (2^(w.width-1) : Nat) := by
    rcases width_cases w with hw | hw <;> rw [hw] <;> norm_num
  have hs : (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))) =
      signedTableOdd (2^(w.width-1)) (digit w.width s) •
        ((Single.halfOrder * 2^w.exponent) • w.base Q) := by
    simp only [positivePoint, selected_address_alias w.width (width_cases w) s h868 h869 h867,
      Single.oddScalar, mul_smul]
    rw [smul_comm Single.halfOrder (2^w.exponent)]
    cases h : s 870
    · rw [if_neg (by decide), signedTableOdd, if_pos ((digit_low_sign w.width (width_cases w) s).mpr h)]
      simp only [neg_zsmul, natCast_zsmul]
    · rw [if_pos rfl, signedTableOdd, if_neg (by
        intro hh
        have he := (digit_low_sign w.width (width_cases w) s).mp hh
        simp [h] at he)]
      simp only [natCast_zsmul]
  rw [hs, signedTableOdd_value]
  unfold increment
  rw [hpow]

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

def paddedRow (w : Digit) (a : Fin 32768) : Fin 319488 :=
  row w ⟨a.val % 2^(w.width-1), Nat.mod_lt _ (pow_pos (by decide) _)⟩

noncomputable def windowCoefficients (w : Digit) : Fin 32768 → PointCoeff :=
  fun a => coefficientAt (paddedRow w a)

theorem window_table_point (Q : Point) (hQ : order • Q = 0) (w : Digit) (a : Nat) :
    constantPoint Q (windowCoefficients w ⟨a % 32768, Nat.mod_lt _ (by decide)⟩) =
      positivePoint Q w (a % 2^(w.width-1)) := by
  unfold windowCoefficients paddedRow
  rw [coefficientAt_row, signedCoefficients_point Q hQ]
  have ha : a % 32768 % 2^(w.width-1) = a % 2^(w.width-1) := by
    cases w <;> norm_num [Digit.width]
  simp only [ha]

variable [b : Single.WindowBody]

def WindowValid (w : Digit) (s : BasisState) : Prop :=
  Single.BodyValid b s ∧ s 868 = false ∧ s 869 = false ∧ (w.width = 13 → s 867 = false)

def signedWindow (w : Digit) : Single.Window 319488 :=
  ⟨(bank w.width).reverse, b.records,
    fun start => reindexStraight (paddedRow w) (b.program start)⟩


noncomputable def windowUpdate (Q : Point) (w : Digit) : BasisState → BasisState :=
  b.update (windowCoefficients w) Q

theorem windowUpdate_correct (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (s : BasisState) (hs : WindowValid w s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    windowUpdate Q w s = pointWrite (P + increment (w.base Q) w.width w.exponent (digit w.width s)) s := by
  have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
    intro a
    have he := window_table_point Q hQ w a.val
    simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
    rw [he]
    exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
  unfold windowUpdate
  rw [b.correct _ Q hQ htable s hs.1.1 P hP, b.active s hs.1.1, if_pos rfl]
  have ha := signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)
  have he := window_table_point Q hQ w (signedTableAddress 32768 (windowRawDigit 0 s))
  simp only [Nat.mod_eq_of_lt ha] at he
  rw [he, selected_increment Q w s hs.2.1 hs.2.2.1 hs.2.2.2]

theorem signedWindow_coherent (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((signedWindow w).program start |>.instantiate
      (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w) := by
  have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
    intro a
    have he := window_table_point Q hQ w a.val
    simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
    rw [he]
    exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
  have h := b.coherent (windowCoefficients w) Q hQ htable start history
  unfold signedWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
  obtain ⟨cs, hc, hm⟩ := h
  exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩




theorem signedWindow_wires (w : Digit) : (signedWindow w).wires = (bank w.width).reverse := rfl

theorem signedWindow_count (w : Digit) : (signedWindow w).count = b.records := rfl

theorem signedWindow_wellFormed (w : Digit) (start : Nat) :
    ((signedWindow w).program start).WellFormed := by
  unfold signedWindow
  exact (reindexStraight_wellFormed (paddedRow w) (b.program start)).mpr (b.wellFormed start)

theorem signedWindow_slots (w : Digit) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ b.slotBound := by
  unfold signedWindow
  rw [reindexStraight_gateSlots]
  exact b.slots start

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
variable [b : Single.WindowBody]
noncomputable section
attribute [local irreducible] fourierOutcomes

omit b in
theorem bank_padding868 (w : Digit) : 868 ∉ bank w.width := by
  rcases width_cases w with h | h <;> rw [h] <;> decide +kernel

omit b in
theorem bank_padding869 (w : Digit) : 869 ∉ bank w.width := by
  rcases width_cases w with h | h <;> rw [h] <;> decide +kernel

omit b in
theorem bank_padding867 (w : Digit) (hw : w.width = 13) : 867 ∉ bank w.width := by
  rw [hw]
  decide +kernel

omit b in
theorem bank_clean (width : Nat) (hw : width = 13 ∨ width = 14)
    (s : BasisState) (hz : Clean streamAddress s) : Clean (bank width) s :=
  fun v hv => hz v (bank_subset width hw v hv)

omit b in
theorem point_bank_clean (width : Nat) (hw : width = 13 ∨ width = 14)
    (P : Point) (s : BasisState) (hz : Clean streamAddress s) :
    Clean (bank width) (pointWrite P s) := by
  intro v hv
  simpa only [pointWrite_frame P s v (bank_not_point width hw v hv)] using
    bank_clean width hw s hz v hv

theorem assigned_valid (w : Digit) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) (input : List Bool) :
    WindowValid w (phaseWordState (bank w.width) input (pointWrite P s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact phaseWordState_preserves (Single.BodyValid b) (bank w.width)
      (fun t ht v hv bit => Single.bodyValid_address t ht v
        (bank_subset w.width (width_cases w) v hv) bit) input _ (Single.bodyValid_first s hs P)
  · rw [phaseWordState_frame _ _ _ 868 (bank_padding868 w),
      pointWrite_frame P s 868 (by decide +kernel)]
    exact hz 868 (by decide +kernel)
  · rw [phaseWordState_frame _ _ _ 869 (bank_padding869 w),
      pointWrite_frame P s 869 (by decide +kernel)]
    exact hz 869 (by decide +kernel)
  · intro hw
    rw [phaseWordState_frame _ _ _ 867 (bank_padding867 w hw),
      pointWrite_frame P s 867 (by decide +kernel)]
    exact hz 867 (by decide +kernel)

omit b in
theorem assigned_coordinates (width : Nat) (hw : width = 13 ∨ width = 14)
    (P : Point) (s : BasisState) (input : List Bool) :
    pointStateCoordinates (phaseWordState (bank width) input (pointWrite P s)) =
      fig14PointEncoding P := by
  rw [phaseWordState_pointWrite _ (bank_not_point width hw), pointWrite_coordinates]

omit b in
theorem assigned_digit (width : Nat) (hw : width = 13 ∨ width = 14)
    (s : BasisState) (input : List Bool) (hi : input.length = (bank width).length) :
    digit width (phaseWordState (bank width) input s) = boolWordToNat input := by
  have he (ws : List Wire) (t : BasisState) :
      tableAddressValue ws t = boolWordToNat (wireValues ws t) := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      change (t w).toNat + 2 * tableAddressValue ws t =
        (t w).toNat + 2 * boolWordToNat (wireValues ws t)
      rw [ih]
  rw [digit, he, phaseWordState_word _ (bank_nodup width hw) input hi s]

theorem signed_assigned_clear (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = w.width) :
    fourierClear (bank w.width).reverse
      (windowUpdate Q w (phaseWordState (bank w.width) input (pointWrite P s))) =
      pointWrite (P + increment (w.base Q) w.width w.exponent (boolWordToNat input)) s := by
  rw [windowUpdate_correct Q hQ hn w _ (assigned_valid w P s hs hz input) P
    (assigned_coordinates w.width (width_cases w) P s input),
    assigned_digit w.width (width_cases w) _ input (hi.trans (bank_length _ (width_cases w)).symm),
    clear_assigned_point _ input (pointWrite P s) (point_bank_clean w.width (width_cases w) P s hz)
      (bank_not_point w.width (width_cases w)), pointWrite_overwrite]


theorem signed_address_word (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = w.width) :
    (bank w.width).map
      (windowUpdate Q w (phaseWordState (bank w.width) input (pointWrite P s))) = input := by
  rw [windowUpdate_correct Q hQ hn w _ (assigned_valid w P s hs hz input) P
    (assigned_coordinates w.width (width_cases w) P s input)]
  have he : (bank w.width).map
      (pointWrite (P + increment (w.base Q) w.width w.exponent (digit w.width
        (phaseWordState (bank w.width) input (pointWrite P s))))
          (phaseWordState (bank w.width) input (pointWrite P s))) =
      (bank w.width).map (phaseWordState (bank w.width) input (pointWrite P s)) := by
    apply List.map_congr_left
    intro v hv
    exact pointWrite_frame _ _ v (bank_not_point w.width (width_cases w) v hv)
  rw [he]
  exact phaseWordState_word _ (bank_nodup w.width (width_cases w)) input
    (hi.trans (bank_length _ (width_cases w)).symm) _

theorem signed_window_point_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (prior output : List Bool) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse (bank w.width).reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)
        (Quantum.run ((bank w.width).map Gate.H) (ket (pointWrite P s)))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (P + increment (w.base Q) w.width w.exponent (boolWordToNat input)) s))).sum := by
  rw [window_branch_uniform .inverse (bank w.width) (bank_nodup w.width (width_cases w))
    (windowUpdate Q w) prior output _ (point_bank_clean w.width (width_cases w) P s hz)
    (fun input hi => signed_address_word Q hQ hn w P s hs hz input
      (by simpa only [bank_length _ (width_cases w)] using (fourierOutcomes_mem _ _).mp hi)),
    bank_length _ (width_cases w)]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [signed_assigned_clear Q hQ hn w P s hs hz input ((fourierOutcomes_mem _ _).mp hi)]

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
attribute [local irreducible] fourierOutcomes

theorem first_window_point_sum (Q : Point) (prior output : List Bool)
    (s : BasisState) (hz : Clean streamAddress s) :
    fourierBranch .inverse (Single.bank 16).reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (firstUpdate Q)
        (Quantum.run ((Single.bank 16).map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (initialPoint Q (boolWordToNat input)) s))).sum := by
  have hlen : (Single.bank 16).length = 16 := by decide +kernel
  rw [window_branch_uniform .inverse (Single.bank 16) (Single.bank_nodup 16)
    (firstUpdate Q) prior output s (Single.bank_clean 16 s hz) (by
      intro input hi
      have he : (Single.bank 16).map (firstUpdate Q (phaseWordState (Single.bank 16) input s)) =
          (Single.bank 16).map (phaseWordState (Single.bank 16) input s) := by
        apply List.map_congr_left
        intro v hv
        exact pointWrite_frame _ _ v (Single.bank_not_point 16 v hv)
      rw [he]
      exact phaseWordState_word _ (Single.bank_nodup 16) input
        ((fourierOutcomes_mem _ _).mp hi) s), hlen]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  unfold firstUpdate
  rw [Single.assigned_digit 16 s input (by simpa only [hlen] using (fourierOutcomes_mem _ _).mp hi),
    clear_assigned_point _ input s (Single.bank_clean 16 s hz) (Single.bank_not_point 16)]

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
attribute [local irreducible] fourierOutcomes

def signedModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit) :
    WindowModel (readConstant coefficientAt Q) where
  physical := signedWindow w
  point := increment (w.base Q) w.width w.exponent
  bias := Single.offsetScalar w.width w.exponent • w.base Q
  ideal := Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)
  valid := WindowValid w
  nodup := by rw [signedWindow_wires]; exact List.nodup_reverse.mpr (bank_nodup w.width (width_cases w))
  coherent := signedWindow_coherent Q hQ hn w

def firstModel (Q : Point) (hQ : order • Q = 0) : WindowModel (readConstant coefficientAt Q) where
  physical := firstWindow
  point := initialPoint Q
  bias := -(leftOffset • G + rightOffset • Q)
  ideal := Finsupp.lmapDomain ℂ ℂ (firstUpdate Q)
  valid := FirstWindowInput
  nodup := by change (Single.bank 16).reverse.Nodup; exact List.nodup_reverse.mpr (Single.bank_nodup 16)
  coherent := by
    intro start history
    obtain ⟨cs, hc, hm⟩ := firstWindow_coherent Q hQ start history
    exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (firstWindowInput_lookup s hs)), hm⟩

omit ledger in
theorem signedModel_step (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (prior bits : List Bool) (P : Point) (root : BasisState)
    (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (signedModel Q hQ hn w).step prior bits (ket (pointWrite P root)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (P + increment (w.base Q) w.width w.exponent (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, signedModel, signedWindow_wires, List.reverse_reverse, LinearMap.comp_apply]
  exact signed_window_point_sum Q hQ hn w prior bits P root hs hz

theorem firstModel_step (Q : Point) (hQ : order • Q = 0)
    (prior bits : List Bool) (root : BasisState) (hz : Clean streamAddress root) :
    (firstModel Q hQ).step prior bits (ket root) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (initialPoint Q (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, firstModel, firstWindow, List.reverse_reverse, LinearMap.comp_apply]
  exact first_window_point_sum Q prior bits root hz

omit ledger in
theorem signedModel_pointRule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (signedModel Q hQ hn w) := by
  intro prior bits P
  simpa only [signedModel, signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)] using
    signedModel_step Q hQ hn w prior bits P root hs hz

theorem firstModel_firstRule (Q : Point) (hQ : order • Q = 0)
    (root : BasisState) (hz : Clean streamAddress root) :
    FirstRule root (ket root) (firstModel Q hQ) := by
  intro prior bits
  have hlen : (Single.bank 16).length = 16 := by decide +kernel
  simpa only [firstModel, firstWindow, List.length_reverse, hlen] using
    firstModel_step Q hQ prior bits root hz


omit ledger in
theorem signedModel_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (signedModel Q hQ hn w).valid
      (Quantum.run ((signedModel Q hQ hn w).physical.wires.reverse.map Gate.H) ψ) := by
  simp only [signedModel, signedWindow_wires, List.reverse_reverse]
  apply Support.linear (pointFamily root) (WindowValid w) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [phaseHadamards_uniform _ (bank_nodup w.width (width_cases w)) _
    (point_bank_clean w.width (width_cases w) P root hz)]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact supportedOn_ket _ _ (assigned_valid w P root hs hz input)

omit ledger in
theorem signedModel_preserves (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (prior bits : List Bool) (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (pointFamily root) ((signedModel Q hQ hn w).step prior bits ψ) := by
  apply Support.linear (pointFamily root) (pointFamily root) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [signedModel_step Q hQ hn w prior bits P root hs hz]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

omit ledger in
theorem ready_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    Ready (ws.map (signedModel Q hQ hn)) ψ := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · exact signedModel_prepared Q hQ hn w root hs hz ψ hψ
    · intro prior bits
      exact ih _ (signedModel_preserves Q hQ hn w root hs hz prior bits ψ hψ)

theorem ready_first_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready (firstModel Q hQ :: ws.map (signedModel Q hQ hn)) (ket root) := by
  constructor
  · simp only [firstModel, firstWindow, List.reverse_reverse]
    exact firstWindowInput_prepare _ (Single.bank_subset 16) _ (supportedOn_ket _ _ hs)
  · intro prior bits
    apply ready_signed Q hQ hn ws root hs hz
    rw [firstModel_step Q hQ prior bits root hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section

theorem concrete_ready (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready ((firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn)) ++
      rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  rw [List.cons_append, ← List.map_append]
  exact ready_first_signed Q hQ hn (leftDigits ++ rightDigits) root hs hz

theorem concrete_kernel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    KernelLaw Q root (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  apply model_kernel Q hQ root (ket root) (firstModel Q hQ) (signedModel Q hQ hn)
  · intro w
    simp only [signedModel, signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]
  · intro w v
    rfl
  · intro w
    rfl
  · intro v
    rfl
  · rfl
  · exact firstModel_firstRule Q hQ root hz
  · intro w _
    exact signedModel_pointRule Q hQ hn w root hs hz

theorem left_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn)) = 266 := by
  rw [precision, List.map_cons, List.sum_cons]
  have hlen : (Single.bank 16).length = 16 := by decide +kernel
  simp only [firstModel, firstWindow, List.length_reverse, hlen, List.map_map, Function.comp_def,
    signedModel, signedWindow_wires, bank_length _ (width_cases _), left_widths]
  norm_num [List.replicate]

omit ledger in
theorem right_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (rightDigits.map (signedModel Q hQ hn)) = 208 := by
  rw [precision]
  simp only [List.map_map, Function.comp_def, signedModel, signedWindow_wires,
    List.length_reverse, bank_length _ (width_cases _), right_widths]
  norm_num [List.replicate]


theorem concrete_event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (start : Nat) (history : Fin start → Bool) (J : Instrument)
    (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedTwoAxes (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) start history (fun lhs rhs =>
        if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass (ket root) =
      idealEventMass Q root 266 208 accept := by
  rw [physicalTwoAxes_event_mass Q root _ _ start history _
    (concrete_ready Q hQ hn root hs hz) (concrete_kernel Q hQ hn root hs hz) J hJ accept,
    left_precision Q hQ hn, right_precision Q hQ hn]

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody]
noncomputable section
attribute [local irreducible] resetProgram

def leftWindows : List (Single.Window 319488) := firstWindow :: leftDigits.map signedWindow

def rightWindows : List (Single.Window 319488) := rightDigits.map signedWindow

def leftMetadata : List (Nat × Nat) :=
  (65535, 16) :: List.replicate 16 (b.records, 14) ++ List.replicate 2 (b.records, 13)

def rightMetadata : List (Nat × Nat) :=
  List.replicate 13 (b.records, 14) ++ List.replicate 2 (b.records, 13)

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftDigits, signedWindow_count, signedWindow_wires,
    Digit.width, bank, firstWindow, Single.bank, leftMetadata, List.ofFn_succ, List.replicate]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightDigits, signedWindow_count, signedWindow_wires,
    Digit.width, bank, rightMetadata, List.ofFn_succ, List.replicate]

theorem left_record_count : recordCount leftMetadata = 65535 + 18 * b.records + 266 := by
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_record_count : recordCount rightMetadata = 15 * b.records + 208 := by
  simp [rightMetadata, recordCount, List.replicate]
  omega

variable [ledger : Single.ProducerResources b]

theorem left_count : axisCount leftWindows = 65535 + 18 * b.records + 266 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 15 * b.records + 208 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

def resetBody (start : Nat) : Straight 319488 start (start + b.reset.length) :=
  resetProgram 319488 start b.reset

omit ledger in
theorem resetBody_run (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).run =
      (measureResetWithCorrection b.reset (fun _ => [])).run := by
  unfold resetBody
  rw [resetProgram_run]

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + b.reset.length

theorem trialCount_eq : trialCount = 65535 + 33 * b.records + 474 + b.reset.length := by
  rw [trialCount, left_count, right_count]
  omega

def trial (start : Nat) : Straight 319488 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

def program : Straight 319488 0 (65535 + 33 * b.records + 474 + b.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section

theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 266 := by
  rw [positions_length]
  simp [leftMetadata, List.replicate]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length]
  simp [rightMetadata, List.replicate]

def trialPositions : TrialPositions NeighborReadout.params where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (65535 + 18 * b.records + 266)).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params] using right_positions_length (65535 + 18 * b.records + 266)⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 65535 + 18 * b.records + 266 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (65535 + 18 * b.records + 266) ≤ i ∧ i < 65535 + 33 * b.records + 474 := by
  have h := positions_bounds rightMetadata (65535 + 18 * b.records + 266) i
    (show i ∈ positions rightMetadata (65535 + 18 * b.records + 266) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

def finePositions : List (Fin (65535 + 33 * b.records + 474 + b.reset.length)) :=
  trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(right_position_bound i.val i.property).2.trans_le (by omega)⟩

theorem finePositions_length : finePositions.length = 208 := by
  simp [finePositions, NeighborReadout.params]

def fineBits : Vector (Fin (65535 + 33 * b.records + 474 + b.reset.length)) 208 :=
  Vector.ofFn fun i=> finePositions[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout : Straight 319488 (65535 + 33 * b.records + 474 + b.reset.length)
    (65535 + 33 * b.records + 474 + b.reset.length + 34114) :=
  castFinish (by omega) (NeighborReadout.neighborSuffix 319488
    (65535 + 33 * b.records + 474 + b.reset.length) 208 fineBits)

def fullProgram : Straight 319488 0 (65535 + 33 * b.records + 474 + b.reset.length + 34114) :=
  program.append readout

def positionsFor (ps : Vector Nat 208) : TrialPositions NeighborReadout.params where
  left := trialPositions.left
  right := ps

def layout : DecodeLayout := ⟨.wrappedShift, NeighborReadout.params,
  (NeighborReadout.rightWords fineBits).map positionsFor, by
    simp only [List.length_map, NeighborReadout.rightWords_length]; decide⟩

theorem readout_wellFormed : readout.WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact NeighborReadout.neighborSuffix_wellFormed 319488 (65535 + 33 * b.records + 474 + b.reset.length) 208 fineBits

theorem readout_t (read : ConstantBit 319488 → Bool)
    (h : Fin (65535 + 33 * b.records + 474 + b.reset.length) → Bool) :
    (readout.instantiate read h).tCount = 0 := by
  unfold readout
  rw [castFinish_instantiate]
  exact NeighborReadout.neighborSuffix_t 319488 (65535 + 33 * b.records + 474 + b.reset.length) 208 fineBits read h

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
attribute [local irreducible] Single.axis resetProgram

theorem concrete_model_left (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn)).map WindowModel.physical = leftWindows := by
  simp only [firstModel, signedModel, leftWindows, List.map_cons, List.map_map, Function.comp_def]

omit ledger in
theorem concrete_model_right (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightDigits.map (signedModel Q hQ hn)).map WindowModel.physical = rightWindows := by
  simp only [signedModel, rightWindows, List.map_map, Function.comp_def]

omit ledger in
theorem left_positions (start : Nat) : axisPositions leftWindows start = positions leftMetadata start := by
  rw [Single.axisPositions, left_metadata]

omit ledger in
theorem right_positions (start : Nat) : axisPositions rightWindows start = positions rightMetadata start := by
  rw [Single.axisPositions, right_metadata]

def fineEvent (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  pairAccept trialPositions.left.toList trialPositions.right.toList accept history

theorem event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (J : Instrument) (hJ : ∀ ψ, J.bornMass ψ = normSq ψ) (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((physicalAxes (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq J).filter
        (fun b => fineEvent accept b.history)) (ket root) =
      idealEventMass Q root 266 208 accept := by
  have hm := concrete_event_mass Q hQ hn root hs hz 0 Fin.elim0 J hJ accept
  rw [selectedTwoAxes_fixed_filter, concrete_model_left Q hQ hn, concrete_model_right Q hQ hn,
    left_count, left_positions, right_positions] at hm
  simpa only [fineEvent, trialPositions, Vector.toList_mk, List.toList_toArray] using hm

theorem program_run_data (read : ConstantBit 319488 → Bool) :
    (program.instantiate read Fin.elim0).run =
      ((physicalAxesData leftWindows rightWindows read 0 Fin.elim0).seq terminalInstrument).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  calc
    _ = ((trial 0).instantiate read Fin.elim0).run := by
      unfold program
      rw [castFinish_instantiate]
    _ = _ := by
      have hf : 0 + axisCount leftWindows + axisCount rightWindows + b.reset.length = 0 + trialCount := by
        unfold trialCount
        omega
      simpa only [trial, physicalAxesData, terminalInstrument] using
        framed_reset_run (axis leftWindows 0 List.nil)
          (axis rightWindows (0 + axisCount leftWindows) List.nil)
          (resetBody (0 + axisCount leftWindows + axisCount rightWindows)) hf read Fin.elim0
          (measureResetWithCorrection b.reset (fun _ => List.nil))
          (resetBody_run _ read)

theorem assembled_program_run (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).run =
      ((physicalAxes (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq terminalInstrument).map
          (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  apply (program_run_data (readConstant coefficientAt Q)).trans
  apply congrArg (fun I : Instrument => (I.seq terminalInstrument).map
    (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b))
  change physicalAxesData leftWindows rightWindows _ _ _ = physicalAxesData _ _ _ _ _
  rw [concrete_model_left Q hQ hn, concrete_model_right Q hQ hn]

theorem program_event_mass (Q : Point) (hn : Q ≠ 0) (hQ : order • Q = 0)
    (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((program.instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent accept b.history)) (ket zeroBasisState) =
      idealEventMass Q initialRoot 266 208 accept := by
  rw [assembled_program_run Q hQ hn,
    prefix_filter_mass _ ([Gate.X 836]) (fineEvent accept) (ket zeroBasisState)]
  have hs : Quantum.run [.X 836] (ket zeroBasisState) = ket initialRoot := by
    simp [Quantum.run, applyGate_ket, onKet, initialRoot, zeroBasisState]
  rw [hs]
  exact event_mass Q hQ hn initialRoot initialRoot_input initialRoot_clean
    terminalInstrument terminalInstrument_mass accept

theorem program_neighbor_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ)/100 ≤ Instrument.bornMass
      (((program.instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent (NeighborReadout.pairRecovered d) b.history)) (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by
    rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [program_event_mass Q hn hQ, idealEventMass_distribution Q d hd]
  exact NeighborReadout.pair_success Q d hn hd

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution RoundedReadout
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem fineBits_vals : fineBits.map Fin.val=trialPositions.right := by
  apply Vector.ext
  intro i hi
  simp [fineBits,finePositions]
  rfl

theorem program_clean (read : ConstantBit 319488 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (program.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [program_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  simp only [Single.Distribution.terminalInstrument, AdaptiveCircuit.run] at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean body.reset ledger.reset_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 ledger.reset_zero, h s hs 1 ledger.reset_one⟩

theorem verified_of_reads (ps : Vector Nat 208) (hps : ps∈NeighborReadout.rightWords fineBits)
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist trialPositions.left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d : ZMod order)∈fixedCandidates NeighborReadout.params a b) :
    (verifiedCandidate layout Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order),?_,?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨positionsFor ps,List.mem_map.mpr ⟨ps,hps,rfl⟩,?_⟩
    simpa only [decodeTrial,trialCandidates,positionsFor,layout,hl,hr,fixedCandidates_take,Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq,ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order];exact Nat.mod_mod _ _)

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q=d•G)
    (read : ConstantBit 319488→Bool) (history : Fin (65535 + 33 * body.records + 474 + body.reset.length)→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : fineEvent (NeighborReadout.pairRecovered d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈(readout.instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate layout Q (List.ofFn history++b.history)).isSome := by
  have hr:=NeighborReadout.input_read fineBits history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩:=Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩:=of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩:=NeighborReadout.neighborSuffix_reads 319488 (65535 + 33 * body.records + 474 + body.reset.length) fineBits
    read history ψ hψ b (by simpa only [readout, castFinish_instantiate] using hb) hn ((i.val : ℤ)-27) (by have h:=i.isLt;omega)
  apply verified_of_reads ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h:=left_position_bound j hj
    simpa only [List.length_ofFn] using h.trans (by omega : (65535 + 18 * body.records + 266)<(65535 + 33 * body.records + 474 + body.reset.length))

theorem program_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99/100 : ℝ) ≤ Instrument.bornMass ((fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) := by
  apply (program_neighbor_success Q d hn hd).trans
  unfold fullProgram
  rw [Single.append_run_history]
  apply Rounded.appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout.instantiate_wellFormed _ _ readout_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = (65535 + 33 * body.records + 474 + body.reset.length) := by
      have h := straight_history_length program (readConstant coefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter (65535 + 33 * body.records + 474 + body.reset.length) Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant coefficientAt Q)
      (Single.historyAfter (65535 + 33 * body.records + 474 + body.reset.length) Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local irreducible] firstLookupProgram resetProgram leftWindows rightWindows resetBody

omit body ledger in
theorem firstWindow_t_uniform (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 458745 := by
  have h := WEXCredit.exact_t _ (first_residue start) (readConstant coefficientAt Q) history
  have h0 := WEXCredit.exact_t _ (first_residue start) (readConstant coefficientAt 0) (fun _ => false)
  have ht := firstWindow_t 0 (by simp) start (fun _ => false)
  omega

omit ledger in
theorem signedWindow_t (Q : Point) (w : Digit) (start : Nat) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount ≤ body.tBound := by
  unfold signedWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
  exact body.tCount _ Q start history

omit ledger in
theorem windows_cases (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows) :
    w = firstWindow ∨ ∃ s, w = signedWindow s := by
  simp only [leftWindows, rightWindows, List.mem_append, List.mem_cons, List.mem_map] at hw
  rcases hw with (h | ⟨s, _, h⟩) | ⟨s, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h.symm⟩
  · exact Or.inr ⟨s, h.symm⟩

omit ledger in
theorem windows_wellFormed (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).WellFormed := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_wellFormed start
  · exact signedWindow_wellFormed s start

def windowSlots : Nat := max 3000000000 body.slotBound

omit ledger in
theorem windows_slots (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).gateSlots ≤ windowSlots := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact (firstWindow_slots start).trans (Nat.le_max_left _ _)
  · exact (signedWindow_slots s start).trans (Nat.le_max_right _ _)

omit ledger in
theorem resetBody_wellFormed (start : Nat) : (resetBody start).WellFormed := by
  unfold resetBody
  exact resetProgram_wellFormed _ _ _

omit ledger in
theorem resetBody_slots (start : Nat) : (resetBody start).gateSlots = 0 := by
  unfold resetBody
  rw [resetProgram_gateSlots]

omit ledger in
theorem resetBody_t (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).tCount = 0 := by
  unfold resetBody
  rw [resetProgram_t]

theorem trial_wellFormed (start : Nat) : (trial start).WellFormed := by
  unfold trial
  apply framed_wellFormed
  · exact axis_wellFormed leftWindows (fun w hw => windows_wellFormed w (List.mem_append_left _ hw)) _ _
  · exact axis_wellFormed rightWindows (fun w hw => windows_wellFormed w (List.mem_append_right _ hw)) _ _
  · exact resetBody_wellFormed _

omit ledger in
theorem slots_budget : metadataSlots windowSlots leftMetadata 0 +
    metadataSlots windowSlots rightMetadata 0 + 2 = 34 * windowSlots + 57249 := by
  simp [leftMetadata, rightMetadata, metadataSlots, List.replicate, fourierSlots]
  omega

theorem trial_slots (start : Nat) : (trial start).gateSlots ≤ 34 * windowSlots + 57249 := by
  have hl := axis_slots leftWindows windowSlots
    (fun w hw => windows_slots w (List.mem_append_left _ hw)) start List.nil
  have hr := axis_slots rightWindows windowSlots
    (fun w hw => windows_slots w (List.mem_append_right _ hw)) (start + axisCount leftWindows) List.nil
  rw [left_metadata] at hl
  rw [right_metadata] at hr
  simp only [List.length_nil] at hl hr
  unfold trial
  rw [framed_slots, resetBody_slots]
  have h := slots_budget
  omega

theorem program_wellFormed : program.WellFormed := by
  unfold program
  rw [castFinish_wellFormed]
  exact trial_wellFormed 0

theorem program_slots : program.gateSlots ≤ 34 * windowSlots + 57249 := by
  unfold program
  rw [castFinish_gateSlots]
  exact trial_slots 0


omit ledger in
theorem signed_costs (Q : Point) (ws : List Digit) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      (ws.map signedWindow) (ws.map (fun w => (body.tBound, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => signedWindow_t Q w start h⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

omit ledger in
theorem left_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      leftWindows (leftCosts body.tBound body.tBound) := by
  have he : leftCosts body.tBound body.tBound =
      (458745, 16) :: leftDigits.map (fun w => (body.tBound, w.width)) := by
    simp [leftCosts, leftDigits, List.ofFn_succ, Digit.width, List.replicate]
  rw [he]
  unfold leftWindows
  refine .cons ⟨?_, fun start h => (firstWindow_t_uniform Q start h).le⟩ (signed_costs Q leftDigits)
  simp only [firstWindow, List.length_reverse]
  decide

omit ledger in
theorem right_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      rightWindows (rightCosts body.tBound body.tBound) := by
  have he : rightCosts body.tBound body.tBound =
      rightDigits.map (fun w => (body.tBound, w.width)) := by
    simp [rightCosts, rightDigits, List.ofFn_succ, Digit.width, List.replicate]
  rw [he]
  simpa only [rightWindows] using signed_costs Q rightDigits

theorem left_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      458745 + 18 * body.tBound + 35245 := by
  have h := axis_t leftWindows (readConstant coefficientAt Q) (leftCosts body.tBound body.tBound)
    (left_costs Q) start List.nil history
  have hm := left_t_budget body.tBound body.tBound
  simp only [List.length_nil, hm] at h
  omega

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      15 * body.tBound + 21528 := by
  have h := axis_t rightWindows (readConstant coefficientAt Q) (rightCosts body.tBound body.tBound)
    (right_costs Q) start List.nil history
  have hm := right_t_budget body.tBound body.tBound
  simp only [List.length_nil, hm] at h
  omega

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      458745 + 33 * body.tBound + 56773 := by
  unfold trial
  apply (framed_t_le _ _ _ _ _ history (458745 + 18 * body.tBound + 35245)
    (15 * body.tBound + 21528) (left_axis_t Q start history)
    (fun h => right_axis_t Q _ h) (fun h => resetBody_t _ _ h)).trans
  omega

theorem program_t (Q : Point) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      458745 + 33 * body.tBound + 56773 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0


theorem stream_support : streamAddress ⊆ ledger.support := by
  intro v hv
  exact ledger.initial_support (List.mem_append_right _ hv)

theorem windows_bank_support (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows) :
    w.wires ⊆ ledger.support := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · unfold firstWindow
    intro v hv
    apply stream_support
    simpa only [List.mem_reverse, Single.bank, show (16 : Nat) ≠ 15 by decide, if_false, streamAddress] using hv
  · rw [signedWindow_wires]
    intro v hv
    exact stream_support (bank_subset s.width (width_cases s) v (List.mem_reverse.mp hv))

theorem windows_support (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows)
    (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ ledger.support := by
  apply (straight_instantiate_support _ read history).trans
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact (firstWindow_support start).trans ledger.initial_support
  · unfold signedWindow
    rw [straightWires_reindex]
    exact ledger.body_wires start

private theorem flag_support : (836 : Wire) ∈ ledger.support := by
  apply ledger.initial_support
  simp [resetWires]

theorem resetBody_support (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).wires ⊆ ledger.support := by
  unfold resetBody
  exact resetProgram_support _ _ _ _ read history ledger.reset_support

theorem left_axis_support (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support leftWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_left _ hw))
    (fun w hw => windows_support w (List.mem_append_left _ hw)) start List.nil read history

theorem right_axis_support (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support rightWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_right _ hw))
    (fun w hw => windows_support w (List.mem_append_right _ hw)) start List.nil read history

theorem trial_support (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((trial start).instantiate read history).wires ⊆ ledger.support := by
  unfold trial
  exact framed_support _ _ _ _ read history ledger.support flag_support
    (left_axis_support start read history) (fun h => right_axis_support _ read h)
    (fun h => resetBody_support _ read h)

theorem program_support (read : ConstantBit 319488 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ ledger.support := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_support 0 read Fin.elim0

theorem readout_support (read : ConstantBit 319488 → Bool)
    (h : Fin (65535 + 33 * body.records + 474 + body.reset.length) → Bool) :
    (readout.instantiate read h).wires ⊆ ledger.support := by
  unfold readout
  rw [castFinish_instantiate]
  apply (NeighborReadout.neighborSuffix_support 319488
    (65535 + 33 * body.records + 474 + body.reset.length) 208 fineBits read h).trans
  have hs : [0,1] ⊆ resetWires := by simp [List.subset_def, resetWires]
  exact hs.trans ledger.initial_support

theorem fullProgram_support (read : ConstantBit 319488 → Bool) :
    (fullProgram.instantiate read Fin.elim0).wires ⊆ ledger.support :=
  outer_append_support _ _ read Fin.elim0 ledger.support (program_support read) (readout_support read)

theorem fullProgram_qubits (read : ConstantBit 319488 → Bool) :
    (fullProgram.instantiate read Fin.elim0).qubitCount ≤ ledger.support.length := by
  have hs : (fullProgram.instantiate read Fin.elim0).wires.dedup.toFinset ⊆
      ledger.support.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (fullProgram_support read (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount] using hc

theorem fullProgram_t (Q : Point) :
    (fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      458745 + 33 * body.tBound + 56773 := by
  have h := outer_append_t_le program readout (readConstant coefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  change ((program.append readout).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤ _
  exact h.trans (by simpa only [Nat.add_zero] using program_t Q)

theorem fullProgram_wellFormed : fullProgram.WellFormed :=
  straight_append_wellFormed _ _ program_wellFormed readout_wellFormed

theorem fullProgram_slots : fullProgram.gateSlots ≤ 34 * windowSlots + 176648 := by
  unfold fullProgram
  rw [Straight.gateSlots_append]
  have hr : readout.gateSlots = 119399 := by
    unfold readout
    rw [castFinish_gateSlots]
    exact NeighborReadout.neighborSuffix_slots 319488
      (65535 + 33 * body.records + 474 + body.reset.length) 208 fineBits
  rw [hr]
  have h := program_slots
  omega


def entry : StraightEntry := Single.fixedEntry coefficientAt fullProgram

def bounds : Bounds := ⟨ledger.support.length, 458745 + 33 * body.tBound + 56773,
  65535 + 33 * body.records + 474 + body.reset.length + 34114⟩

theorem certificate
    (hSlots : 34 * windowSlots + 176648 ≤ officialLimits.gateSlots)
    (hRecords : 65535 + 33 * body.records + 474 + body.reset.length + 34114 ≤ officialLimits.measurements) :
    Certificate officialLimits layout entry bounds where
  gateBudget := by
    rw [entry, Single.fixedEntry_slots]
    exact fullProgram_slots.trans hSlots
  recordBudget := by
    exact hRecords
  tableBudget := by
    rw [entry, Single.fixedEntry_rows]
    decide
  candidateBudget := by
    change 55 * (2*(order/2^208+2)) ≤ 56*(2^49+2)
    exact NeighborReadout.decoder_budget
  wellFormed := by
    rw [entry, Single.fixedEntry_wellFormed]
    exact fullProgram_wellFormed
  resources := by
    intro Q
    rw [entry, Single.fixedEntry_instantiate]
    exact ⟨fullProgram_qubits _, fullProgram_t Q, (fullProgram.measurementCount _ _).le⟩
  success := by
    intro Q d hn hd
    rw [entry, Single.fixedEntry_instantiate]
    exact program_success Q d hn hd

end
end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody]
noncomputable section

def count (r13 r14 : Nat) (w : Digit) : Nat := if w.width = 13 then r13 else r14

class Programs (body : Single.WindowBody) where
  records13 : Nat
  records14 : Nat
  cost13 : Nat
  cost14 : Nat
  program : (w : Digit) → (start : Nat) → Straight 319488 start
    (start + count records13 records14 w)
  coherent : ∀ Q, order • Q = 0 → Q ≠ 0 → ∀ w start history,
    CoherentlyImplementsOn ((program w start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w)
  wellFormed : ∀ w start, (program w start).WellFormed
  slots : ∀ w start, (program w start).gateSlots ≤ body.slotBound
  wires : ∀ w start, straightWires (program w start) ⊆ body.support
  tCount : ∀ Q w start history,
    ((program w start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count cost13 cost14 w

variable [impl : Programs body]

def signedWindow (w : Digit) : Single.Window 319488 :=
  ⟨(bank w.width).reverse, count impl.records13 impl.records14 w, impl.program w⟩

def signedModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit) :
    WindowModel (readConstant coefficientAt Q) where
  physical := signedWindow w
  point := increment (w.base Q) w.width w.exponent
  bias := Single.offsetScalar w.width w.exponent • w.base Q
  ideal := Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)
  valid := WindowValid w
  nodup := by
    change (bank w.width).reverse.Nodup
    exact List.nodup_reverse.mpr (bank_nodup w.width (width_cases w))
  coherent := impl.coherent Q hQ hn w

theorem signedModel_step (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (prior bits : List Bool) (P : Point) (root : BasisState)
    (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (signedModel Q hQ hn w).step prior bits (ket (pointWrite P root)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (P + increment (w.base Q) w.width w.exponent (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, signedModel, signedWindow, List.reverse_reverse, LinearMap.comp_apply]
  exact signed_window_point_sum Q hQ hn w prior bits P root hs hz

theorem signedModel_pointRule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (signedModel Q hQ hn w) := by
  intro prior bits P
  simpa only [signedModel, signedWindow, List.length_reverse, bank_length _ (width_cases w)] using
    signedModel_step Q hQ hn w prior bits P root hs hz

theorem signedModel_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (signedModel Q hQ hn w).valid
      (Quantum.run ((signedModel Q hQ hn w).physical.wires.reverse.map Gate.H) ψ) := by
  simp only [signedModel, signedWindow, List.reverse_reverse]
  apply Support.linear (pointFamily root) (WindowValid w) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [phaseHadamards_uniform _ (bank_nodup w.width (width_cases w)) _
    (point_bank_clean w.width (width_cases w) P root hz)]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact supportedOn_ket _ _ (assigned_valid w P root hs hz input)

theorem signedModel_preserves (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (prior bits : List Bool) (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (pointFamily root) ((signedModel Q hQ hn w).step prior bits ψ) := by
  apply Support.linear (pointFamily root) (pointFamily root) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [signedModel_step Q hQ hn w prior bits P root hs hz]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

theorem ready_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    Ready (ws.map (signedModel Q hQ hn)) ψ := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · exact signedModel_prepared Q hQ hn w root hs hz ψ hψ
    · intro prior bits
      exact ih _ (signedModel_preserves Q hQ hn w root hs hz prior bits ψ hψ)

end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [impl : Programs body]
noncomputable section
attribute [local irreducible] resetProgram

def leftWindows : List (Single.Window 319488) := Schedule33.firstWindow :: leftDigits.map signedWindow

def rightWindows : List (Single.Window 319488) := rightDigits.map signedWindow

def leftMetadata : List (Nat × Nat) :=
  (65535, 16) :: List.replicate 16 (impl.records14, 14) ++ List.replicate 2 (impl.records13, 13)

def rightMetadata : List (Nat × Nat) :=
  List.replicate 13 (impl.records14, 14) ++ List.replicate 2 (impl.records13, 13)

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftDigits, signedWindow, count,
    Digit.width, bank, Schedule33.firstWindow, Single.bank, leftMetadata, List.ofFn_succ, List.replicate]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightDigits, signedWindow, count,
    Digit.width, bank, rightMetadata, List.ofFn_succ, List.replicate]

theorem left_record_count : recordCount leftMetadata = 65535 + 16 * impl.records14 + 2 * impl.records13 + 266 := by
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_record_count : recordCount rightMetadata = 13 * impl.records14 + 2 * impl.records13 + 208 := by
  simp [rightMetadata, recordCount, List.replicate]
  omega

variable [ledger : Single.ProducerResources body]

theorem left_count : axisCount leftWindows = 65535 + 16 * impl.records14 + 2 * impl.records13 + 266 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 13 * impl.records14 + 2 * impl.records13 + 208 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + body.reset.length

theorem trialCount_eq : trialCount =
    65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length := by
  rw [trialCount, left_count, right_count]
  omega

def trial (start : Nat) : Straight 319488 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (Schedule33.resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

def program : Straight 319488 0 (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section

theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 266 := by
  rw [positions_length]
  simp [leftMetadata, List.replicate]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length]
  simp [rightMetadata, List.replicate]

def trialPositions : TrialPositions NeighborReadout.params where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (65535 + 16 * impl.records14 + 2 * impl.records13 + 266)).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params] using right_positions_length (65535 + 16 * impl.records14 + 2 * impl.records13 + 266)⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 65535 + 16 * impl.records14 + 2 * impl.records13 + 266 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (65535 + 16 * impl.records14 + 2 * impl.records13 + 266) ≤ i ∧ i < 65535 + 29 * impl.records14 + 4 * impl.records13 + 474 := by
  have h := positions_bounds rightMetadata (65535 + 16 * impl.records14 + 2 * impl.records13 + 266) i
    (show i ∈ positions rightMetadata (65535 + 16 * impl.records14 + 2 * impl.records13 + 266) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

def finePositions : List (Fin (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length)) :=
  trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(right_position_bound i.val i.property).2.trans_le (by omega)⟩

theorem finePositions_length : finePositions.length = 208 := by
  simp [finePositions, NeighborReadout.params]

def fineBits : Vector (Fin (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length)) 208 :=
  Vector.ofFn fun i=> finePositions[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout : Straight 319488 (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length)
    (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length + 34114) :=
  castFinish (by omega) (NeighborReadout.neighborSuffix 319488
    (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) 208 fineBits)

def fullProgram : Straight 319488 0 (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length + 34114) :=
  program.append readout

def positionsFor (ps : Vector Nat 208) : TrialPositions NeighborReadout.params where
  left := trialPositions.left
  right := ps

def layout : DecodeLayout := ⟨.wrappedShift, NeighborReadout.params,
  (NeighborReadout.rightWords fineBits).map positionsFor, by
    simp only [List.length_map, NeighborReadout.rightWords_length]; decide⟩

theorem readout_wellFormed : readout.WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact NeighborReadout.neighborSuffix_wellFormed 319488 (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) 208 fineBits

theorem readout_t (read : ConstantBit 319488 → Bool)
    (h : Fin (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) → Bool) :
    (readout.instantiate read h).tCount = 0 := by
  unfold readout
  rw [castFinish_instantiate]
  exact NeighborReadout.neighborSuffix_t 319488 (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) 208 fineBits read h

end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section

theorem ready_first_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready (Schedule33.firstModel Q hQ :: ws.map (signedModel Q hQ hn)) (ket root) := by
  constructor
  · simp only [Schedule33.firstModel, Schedule33.firstWindow, List.reverse_reverse]
    exact firstWindowInput_prepare _ (Single.bank_subset 16) _ (supportedOn_ket _ _ hs)
  · intro prior bits
    apply ready_signed Q hQ hn ws root hs hz
    rw [Schedule33.firstModel_step Q hQ prior bits root hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

theorem concrete_ready (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready ((firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn)) ++
      rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  rw [List.cons_append, ← List.map_append]
  exact ready_first_signed Q hQ hn (leftDigits ++ rightDigits) root hs hz

theorem concrete_kernel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    KernelLaw Q root (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  apply model_kernel Q hQ root (ket root) (firstModel Q hQ) (signedModel Q hQ hn)
  · intro w
    simp only [signedModel, signedWindow, List.length_reverse, bank_length _ (width_cases w)]
  · intro w v
    rfl
  · intro w
    rfl
  · intro v
    rfl
  · rfl
  · exact firstModel_firstRule Q hQ root hz
  · intro w _
    exact signedModel_pointRule Q hQ hn w root hs hz

theorem left_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn)) = 266 := by
  rw [precision, List.map_cons, List.sum_cons]
  have hlen : (Single.bank 16).length = 16 := by decide +kernel
  simp only [firstModel, firstWindow, List.length_reverse, hlen, List.map_map, Function.comp_def,
    signedModel, signedWindow, bank_length _ (width_cases _), left_widths]
  norm_num [List.replicate]

omit ledger in
theorem right_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (rightDigits.map (signedModel Q hQ hn)) = 208 := by
  rw [precision]
  simp only [List.map_map, Function.comp_def, signedModel, signedWindow,
    List.length_reverse, bank_length _ (width_cases _), right_widths]
  norm_num [List.replicate]


theorem concrete_event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (start : Nat) (history : Fin start → Bool) (J : Instrument)
    (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedTwoAxes (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) start history (fun lhs rhs =>
        if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass (ket root) =
      idealEventMass Q root 266 208 accept := by
  rw [physicalTwoAxes_event_mass Q root _ _ start history _
    (concrete_ready Q hQ hn root hs hz) (concrete_kernel Q hQ hn root hs hz) J hJ accept,
    left_precision Q hQ hn, right_precision Q hQ hn]

end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
attribute [local irreducible] Single.axis resetProgram

theorem concrete_model_left (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn)).map WindowModel.physical = leftWindows := by
  simp only [firstModel, signedModel, leftWindows, List.map_cons, List.map_map, Function.comp_def]

omit ledger in
theorem concrete_model_right (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightDigits.map (signedModel Q hQ hn)).map WindowModel.physical = rightWindows := by
  simp only [signedModel, rightWindows, List.map_map, Function.comp_def]

omit ledger in
theorem left_positions (start : Nat) : axisPositions leftWindows start = positions leftMetadata start := by
  rw [Single.axisPositions, left_metadata]

omit ledger in
theorem right_positions (start : Nat) : axisPositions rightWindows start = positions rightMetadata start := by
  rw [Single.axisPositions, right_metadata]

def fineEvent (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  pairAccept trialPositions.left.toList trialPositions.right.toList accept history

theorem event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (J : Instrument) (hJ : ∀ ψ, J.bornMass ψ = normSq ψ) (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((physicalAxes (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq J).filter
        (fun b => fineEvent accept b.history)) (ket root) =
      idealEventMass Q root 266 208 accept := by
  have hm := concrete_event_mass Q hQ hn root hs hz 0 Fin.elim0 J hJ accept
  rw [selectedTwoAxes_fixed_filter, concrete_model_left Q hQ hn, concrete_model_right Q hQ hn,
    left_count, left_positions, right_positions] at hm
  simpa only [fineEvent, trialPositions, Vector.toList_mk, List.toList_toArray] using hm

theorem program_run_data (read : ConstantBit 319488 → Bool) :
    (program.instantiate read Fin.elim0).run =
      ((physicalAxesData leftWindows rightWindows read 0 Fin.elim0).seq terminalInstrument).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  calc
    _ = ((trial 0).instantiate read Fin.elim0).run := by
      unfold program
      rw [castFinish_instantiate]
    _ = _ := by
      have hf : 0 + axisCount leftWindows + axisCount rightWindows + body.reset.length = 0 + trialCount := by
        unfold trialCount
        omega
      simpa only [trial, physicalAxesData, terminalInstrument] using
        framed_reset_run (axis leftWindows 0 List.nil)
          (axis rightWindows (0 + axisCount leftWindows) List.nil)
          (resetBody (0 + axisCount leftWindows + axisCount rightWindows)) hf read Fin.elim0
          (measureResetWithCorrection body.reset (fun _ => List.nil))
          (resetBody_run _ read)

theorem assembled_program_run (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).run =
      ((physicalAxes (firstModel Q hQ :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq terminalInstrument).map
          (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  apply (program_run_data (readConstant coefficientAt Q)).trans
  apply congrArg (fun I : Instrument => (I.seq terminalInstrument).map
    (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b))
  change physicalAxesData leftWindows rightWindows _ _ _ = physicalAxesData _ _ _ _ _
  rw [concrete_model_left Q hQ hn, concrete_model_right Q hQ hn]

theorem program_event_mass (Q : Point) (hn : Q ≠ 0) (hQ : order • Q = 0)
    (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((program.instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent accept b.history)) (ket zeroBasisState) =
      idealEventMass Q initialRoot 266 208 accept := by
  rw [assembled_program_run Q hQ hn,
    prefix_filter_mass _ ([Gate.X 836]) (fineEvent accept) (ket zeroBasisState)]
  have hs : Quantum.run [.X 836] (ket zeroBasisState) = ket initialRoot := by
    simp [Quantum.run, applyGate_ket, onKet, initialRoot, zeroBasisState]
  rw [hs]
  exact event_mass Q hQ hn initialRoot initialRoot_input initialRoot_clean
    terminalInstrument terminalInstrument_mass accept

theorem program_neighbor_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ)/100 ≤ Instrument.bornMass
      (((program.instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent (NeighborReadout.pairRecovered d) b.history)) (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by
    rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [program_event_mass Q hn hQ, idealEventMass_distribution Q d hd]
  exact NeighborReadout.pair_success Q d hn hd

end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33 RoundedReadout
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem fineBits_vals : fineBits.map Fin.val=trialPositions.right := by
  apply Vector.ext
  intro i hi
  simp [fineBits,finePositions]
  rfl

theorem program_clean (read : ConstantBit 319488 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (program.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [program_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  simp only [Single.Distribution.terminalInstrument, AdaptiveCircuit.run] at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean body.reset ledger.reset_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 ledger.reset_zero, h s hs 1 ledger.reset_one⟩

theorem verified_of_reads (ps : Vector Nat 208) (hps : ps∈NeighborReadout.rightWords fineBits)
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist trialPositions.left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d : ZMod order)∈fixedCandidates NeighborReadout.params a b) :
    (verifiedCandidate layout Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order),?_,?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨positionsFor ps,List.mem_map.mpr ⟨ps,hps,rfl⟩,?_⟩
    simpa only [decodeTrial,trialCandidates,positionsFor,layout,hl,hr,fixedCandidates_take,Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq,ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order];exact Nat.mod_mod _ _)

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q=d•G)
    (read : ConstantBit 319488→Bool) (history : Fin (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length)→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : fineEvent (NeighborReadout.pairRecovered d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈(readout.instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate layout Q (List.ofFn history++b.history)).isSome := by
  have hr:=NeighborReadout.input_read fineBits history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩:=Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩:=of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩:=NeighborReadout.neighborSuffix_reads 319488 (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) fineBits
    read history ψ hψ b (by simpa only [readout, castFinish_instantiate] using hb) hn ((i.val : ℤ)-27) (by have h:=i.isLt;omega)
  apply verified_of_reads ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h:=left_position_bound j hj
    simpa only [List.length_ofFn] using h.trans (by omega : (65535 + 16 * impl.records14 + 2 * impl.records13 + 266)<(65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length))

theorem program_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99/100 : ℝ) ≤ Instrument.bornMass ((fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) := by
  apply (program_neighbor_success Q d hn hd).trans
  unfold fullProgram
  rw [Single.append_run_history]
  apply Rounded.appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout.instantiate_wellFormed _ _ readout_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) := by
      have h := straight_history_length program (readConstant coefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant coefficientAt Q)
      (Single.historyAfter (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local irreducible] firstLookupProgram resetProgram leftWindows rightWindows resetBody

omit ledger in
theorem signedWindow_wires (w : Digit) : (signedWindow w).wires = (bank w.width).reverse := rfl

omit ledger in
theorem signedWindow_t (Q : Point) (w : Digit) (start : Nat) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count impl.cost13 impl.cost14 w := impl.tCount Q w start history

omit ledger in
theorem signedWindow_wellFormed (w : Digit) (start : Nat) :
    ((signedWindow w).program start).WellFormed := impl.wellFormed w start

omit ledger in
theorem signedWindow_slots (w : Digit) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ body.slotBound := impl.slots w start

omit ledger in
theorem windows_cases (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows) :
    w = firstWindow ∨ ∃ s, w = signedWindow s := by
  simp only [leftWindows, rightWindows, List.mem_append, List.mem_cons, List.mem_map] at hw
  rcases hw with (h | ⟨s, _, h⟩) | ⟨s, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h.symm⟩
  · exact Or.inr ⟨s, h.symm⟩

omit ledger in
theorem windows_wellFormed (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).WellFormed := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_wellFormed start
  · exact signedWindow_wellFormed s start

def windowSlots : Nat := max 3000000000 body.slotBound

omit ledger in
theorem windows_slots (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).gateSlots ≤ windowSlots := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact (firstWindow_slots start).trans (Nat.le_max_left _ _)
  · exact (signedWindow_slots s start).trans (Nat.le_max_right _ _)

theorem trial_wellFormed (start : Nat) : (trial start).WellFormed := by
  unfold trial
  apply framed_wellFormed
  · exact axis_wellFormed leftWindows (fun w hw => windows_wellFormed w (List.mem_append_left _ hw)) _ _
  · exact axis_wellFormed rightWindows (fun w hw => windows_wellFormed w (List.mem_append_right _ hw)) _ _
  · exact resetBody_wellFormed _

omit ledger in
theorem slots_budget : metadataSlots windowSlots leftMetadata 0 +
    metadataSlots windowSlots rightMetadata 0 + 2 = 34 * windowSlots + 57249 := by
  simp [leftMetadata, rightMetadata, metadataSlots, List.replicate, fourierSlots]
  omega

theorem trial_slots (start : Nat) : (trial start).gateSlots ≤ 34 * windowSlots + 57249 := by
  have hl := axis_slots leftWindows windowSlots
    (fun w hw => windows_slots w (List.mem_append_left _ hw)) start List.nil
  have hr := axis_slots rightWindows windowSlots
    (fun w hw => windows_slots w (List.mem_append_right _ hw)) (start + axisCount leftWindows) List.nil
  rw [left_metadata] at hl
  rw [right_metadata] at hr
  simp only [List.length_nil] at hl hr
  unfold trial
  rw [framed_slots, resetBody_slots]
  have h := slots_budget
  omega

theorem program_wellFormed : program.WellFormed := by
  unfold program
  rw [castFinish_wellFormed]
  exact trial_wellFormed 0

theorem program_slots : program.gateSlots ≤ 34 * windowSlots + 57249 := by
  unfold program
  rw [castFinish_gateSlots]
  exact trial_slots 0


omit ledger in
theorem signed_costs (Q : Point) (ws : List Digit) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      (ws.map signedWindow) (ws.map (fun w => (count impl.cost13 impl.cost14 w, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => signedWindow_t Q w start h⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

omit ledger in
theorem left_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      leftWindows (leftCosts impl.cost14 impl.cost13) := by
  have he : leftCosts impl.cost14 impl.cost13 =
      (458745, 16) :: leftDigits.map (fun w => (count impl.cost13 impl.cost14 w, w.width)) := by
    simp [leftCosts, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  unfold leftWindows
  refine .cons ⟨?_, fun start h => (firstWindow_t_uniform Q start h).le⟩ (signed_costs Q leftDigits)
  simp only [firstWindow, List.length_reverse]
  decide

omit ledger in
theorem right_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      rightWindows (rightCosts impl.cost14 impl.cost13) := by
  have he : rightCosts impl.cost14 impl.cost13 =
      rightDigits.map (fun w => (count impl.cost13 impl.cost14 w, w.width)) := by
    simp [rightCosts, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  simpa only [rightWindows] using signed_costs Q rightDigits

theorem left_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      458745 + 16 * impl.cost14 + 2 * impl.cost13 + 35245 := by
  have h := axis_t leftWindows (readConstant coefficientAt Q) (leftCosts impl.cost14 impl.cost13)
    (left_costs Q) start List.nil history
  have hm := left_t_budget impl.cost14 impl.cost13
  simp only [List.length_nil, hm] at h
  omega

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      13 * impl.cost14 + 2 * impl.cost13 + 21528 := by
  have h := axis_t rightWindows (readConstant coefficientAt Q) (rightCosts impl.cost14 impl.cost13)
    (right_costs Q) start List.nil history
  have hm := right_t_budget impl.cost14 impl.cost13
  simp only [List.length_nil, hm] at h
  omega

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      458745 + 29 * impl.cost14 + 4 * impl.cost13 + 56773 := by
  unfold trial
  apply (framed_t_le _ _ _ _ _ history (458745 + 16 * impl.cost14 + 2 * impl.cost13 + 35245)
    (13 * impl.cost14 + 2 * impl.cost13 + 21528) (left_axis_t Q start history)
    (fun h => right_axis_t Q _ h) (fun h => resetBody_t _ _ h)).trans
  omega

theorem program_t (Q : Point) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      458745 + 29 * impl.cost14 + 4 * impl.cost13 + 56773 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0


class SupportCover (body : Single.WindowBody) (ledger : Single.ProducerResources body) : Prop where
  covers : body.support ⊆ ledger.support

variable [cover : SupportCover body ledger]

omit impl cover in
theorem stream_support : streamAddress ⊆ ledger.support := by
  intro v hv
  exact ledger.initial_support (List.mem_append_right _ hv)

omit cover in
theorem windows_bank_support (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows) :
    w.wires ⊆ ledger.support := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · unfold firstWindow
    intro v hv
    apply stream_support
    simpa only [List.mem_reverse, Single.bank, show (16 : Nat) ≠ 15 by decide, if_false, streamAddress] using hv
  · rw [signedWindow_wires]
    intro v hv
    exact stream_support (bank_subset s.width (width_cases s) v (List.mem_reverse.mp hv))

theorem windows_support (w : Single.Window 319488) (hw : w ∈ leftWindows ++ rightWindows)
    (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ ledger.support := by
  apply (straight_instantiate_support _ read history).trans
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact (firstWindow_support start).trans ledger.initial_support
  · exact (impl.wires s start).trans cover.covers

omit impl cover in
private theorem flag_support : (836 : Wire) ∈ ledger.support := by
  apply ledger.initial_support
  simp [resetWires]

omit impl cover in
theorem resetBody_support (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).wires ⊆ ledger.support := by
  unfold resetBody
  exact resetProgram_support _ _ _ _ read history ledger.reset_support

theorem left_axis_support (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support leftWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_left _ hw))
    (fun w hw => windows_support w (List.mem_append_left _ hw)) start List.nil read history

theorem right_axis_support (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support rightWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_right _ hw))
    (fun w hw => windows_support w (List.mem_append_right _ hw)) start List.nil read history

theorem trial_support (start : Nat) (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    ((trial start).instantiate read history).wires ⊆ ledger.support := by
  unfold trial
  exact framed_support _ _ _ _ read history ledger.support flag_support
    (left_axis_support start read history) (fun h => right_axis_support _ read h)
    (fun h => resetBody_support _ read h)

theorem program_support (read : ConstantBit 319488 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ ledger.support := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_support 0 read Fin.elim0

omit cover in
theorem readout_support (read : ConstantBit 319488 → Bool)
    (h : Fin (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) → Bool) :
    (readout.instantiate read h).wires ⊆ ledger.support := by
  unfold readout
  rw [castFinish_instantiate]
  apply (NeighborReadout.neighborSuffix_support 319488
    (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) 208 fineBits read h).trans
  have hs : [0,1] ⊆ resetWires := by simp [List.subset_def, resetWires]
  exact hs.trans ledger.initial_support

theorem fullProgram_support (read : ConstantBit 319488 → Bool) :
    (fullProgram.instantiate read Fin.elim0).wires ⊆ ledger.support :=
  outer_append_support _ _ read Fin.elim0 ledger.support (program_support read) (readout_support read)

theorem fullProgram_qubits (read : ConstantBit 319488 → Bool) :
    (fullProgram.instantiate read Fin.elim0).qubitCount ≤ ledger.support.length := by
  have hs : (fullProgram.instantiate read Fin.elim0).wires.dedup.toFinset ⊆
      ledger.support.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (fullProgram_support read (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount] using hc

omit cover in
theorem fullProgram_t (Q : Point) :
    (fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      458745 + 29 * impl.cost14 + 4 * impl.cost13 + 56773 := by
  have h := outer_append_t_le program readout (readConstant coefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  change ((program.append readout).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤ _
  exact h.trans (by simpa only [Nat.add_zero] using program_t Q)

omit cover in
theorem fullProgram_wellFormed : fullProgram.WellFormed :=
  straight_append_wellFormed _ _ program_wellFormed readout_wellFormed

omit cover in
theorem fullProgram_slots : fullProgram.gateSlots ≤ 34 * windowSlots + 176648 := by
  unfold fullProgram
  rw [Straight.gateSlots_append]
  have hr : readout.gateSlots = 119399 := by
    unfold readout
    rw [castFinish_gateSlots]
    exact NeighborReadout.neighborSuffix_slots 319488
      (65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length) 208 fineBits
  rw [hr]
  have h := program_slots
  omega


def entry : StraightEntry := Single.fixedEntry coefficientAt fullProgram

def bounds : Bounds := ⟨ledger.support.length, 458745 + 29 * impl.cost14 + 4 * impl.cost13 + 56773,
  65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length + 34114⟩

theorem certificate
    (hSlots : 34 * windowSlots + 176648 ≤ officialLimits.gateSlots)
    (hRecords : 65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length + 34114 ≤ officialLimits.measurements) :
    Certificate officialLimits layout entry bounds where
  gateBudget := by
    rw [entry, Single.fixedEntry_slots]
    exact fullProgram_slots.trans hSlots
  recordBudget := by
    exact hRecords
  tableBudget := by
    rw [entry, Single.fixedEntry_rows]
    decide
  candidateBudget := by
    change 55 * (2*(order/2^208+2)) ≤ 56*(2^49+2)
    exact NeighborReadout.decoder_budget
  wellFormed := by
    rw [entry, Single.fixedEntry_wellFormed]
    exact fullProgram_wellFormed
  resources := by
    intro Q
    rw [entry, Single.fixedEntry_instantiate]
    exact ⟨fullProgram_qubits _, fullProgram_t Q, (fullProgram.measurementCount _ _).le⟩
  success := by
    intro Q d hn hd
    rw [entry, Single.fixedEntry_instantiate]
    exact program_success Q d hn hd

end
end ShorECDLP.Entrant.Schedule33.Flexible
namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] leftWindows rightWindows program fullProgram readout entry Single.axis

structure ProgramCredit (c13 c14 : Nat) : Prop where
  zero : ∀ w start, residue (impl.program w start) = 0
  count_eq : ∀ w start, added (impl.program w start) = count c13 c14 w

variable {c13 c14 : Nat} (hc : ProgramCredit c13 c14)
include hc

omit ledger in
theorem signed_credit (w : Digit) (start : Nat) :
    AtLeast ((signedWindow w).program start) (count c13 c14 w) := by
  simpa only [signedWindow, AtLeast] using (hc.count_eq w start).ge

def leftCounted : List (CountedWindow 319488) :=
  ⟨Schedule33.firstWindow, 65535, Schedule33.first_count⟩ :: leftDigits.map
    (fun w => ⟨signedWindow w, count c13 c14 w, signed_credit hc w⟩)

def rightCounted : List (CountedWindow 319488) :=
  rightDigits.map (fun w => ⟨signedWindow w, count c13 c14 w, signed_credit hc w⟩)

theorem parent_credit : AtLeast entry.program (65535 + 29 * c14 + 4 * c13) := by
  have hl := counted_axis (leftCounted hc) 0 List.nil
  have hr := counted_axis (rightCounted hc) (0 + Single.axisCount leftWindows) List.nil
  have hls : (leftCounted hc).map CountedWindow.source = leftWindows := by
    simp [leftCounted, leftWindows]
  have hrs : (rightCounted hc).map CountedWindow.source = rightWindows := by
    simp [rightCounted, rightWindows]
  have hln : ((leftCounted hc).map CountedWindow.saving).sum = 65535 + 16 * c14 + 2 * c13 := by
    simp [leftCounted, leftDigits, List.ofFn_succ, Digit.width, count]
    omega
  have hrn : ((rightCounted hc).map CountedWindow.saving).sum = 13 * c14 + 2 * c13 := by
    simp [rightCounted, rightDigits, List.ofFn_succ, Digit.width, count]
    omega
  rw [hls, hln] at hl
  rw [hrs, hrn] at hr
  have ht : AtLeast (trial 0) (65535 + 29 * c14 + 4 * c13) := by
    unfold trial
    exact (framed_credit _ _ _ _ hl hr).castCount (by omega)
  have hp : AtLeast program (65535 + 29 * c14 + 4 * c13) := by
    unfold program
    exact ht.castFinish _
  unfold entry fullProgram
  apply fixedEntry_credit
  exact (hp.append (AtLeast.zero _)).castCount (by omega)

omit ledger in
theorem signed_t (w : Digit) (start : Nat)
    (read : ConstantBit 319488 → Bool) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate read history).tCount =
      7 * count c13 c14 w := by
  unfold signedWindow
  rw [exact_t _ (hc.zero w start), hc.count_eq w start]

def creditLeftCosts : List (Nat × Nat) := leftCosts (7*c14) (7*c13)
def creditRightCosts : List (Nat × Nat) := rightCosts (7*c14) (7*c13)

omit ledger in
theorem signed_costs_credit (ws : List Digit) (read : ConstantBit 319488 → Bool) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1)
      (ws.map signedWindow) (ws.map (fun w => (7 * count c13 c14 w, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => (signed_t hc w start read h).le⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

theorem producer_t (Q : Point) :
    (fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      7 * (65535 + 29 * c14 + 4 * c13) + 56773 := by
  let read := readConstant coefficientAt Q
  have lc : List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1) leftWindows
      (creditLeftCosts (c13 := c13) (c14 := c14)) := by
    have he : creditLeftCosts (c13 := c13) (c14 := c14) =
        (458745,16) :: leftDigits.map (fun w => (7 * count c13 c14 w, w.width)) := by
      simp [creditLeftCosts, leftCosts, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
    rw [he]
    unfold leftWindows
    refine .cons ⟨?_, fun start h => (Schedule33.firstWindow_t_uniform Q start h).le⟩
      (signed_costs_credit hc leftDigits read)
    simp only [Schedule33.firstWindow, List.length_reverse]
    decide
  have hl := Single.axis_t leftWindows read _ lc 0 List.nil Fin.elim0
  have hr : ∀ h, ((Single.axis rightWindows
      (0 + Single.axisCount leftWindows) List.nil).instantiate read h).tCount ≤
      Single.metadataT (creditRightCosts (c13 := c13) (c14 := c14)) 0 := by
    intro h
    apply Single.axis_t rightWindows read _ _ _ List.nil h
    have he : creditRightCosts (c13 := c13) (c14 := c14) =
        rightDigits.map (fun w => (7 * count c13 c14 w, w.width)) := by
      simp [creditRightCosts, rightCosts, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
    rw [he]
    simpa only [rightWindows] using signed_costs_credit hc rightDigits read
  have hln : Single.metadataT (creditLeftCosts (c13 := c13) (c14 := c14)) 0 =
      458745 + 16 * (7*c14) + 2 * (7*c13) + 35245 := left_t_budget _ _
  have hrn : Single.metadataT (creditRightCosts (c13 := c13) (c14 := c14)) 0 =
      13 * (7*c14) + 2 * (7*c13) + 21528 := right_t_budget _ _
  have ht := Single.framed_t_le (Single.axis leftWindows 0 List.nil)
    (Single.axis rightWindows (0 + Single.axisCount leftWindows) List.nil)
    (Schedule33.resetBody (0 + Single.axisCount leftWindows + Single.axisCount rightWindows))
    (show 0 + Single.axisCount leftWindows + Single.axisCount rightWindows +
      body.reset.length = 0 + trialCount from by unfold trialCount; omega)
    read Fin.elim0 _ _ hl hr (Schedule33.resetBody_t _ read)
  have hp : (program.instantiate read Fin.elim0).tCount ≤
      Single.metadataT (creditLeftCosts (c13 := c13) (c14 := c14)) 0 +
        Single.metadataT (creditRightCosts (c13 := c13) (c14 := c14)) 0 := by
    unfold program trial
    simpa only [castFinish_instantiate] using ht
  have hs := outer_append_t_le program readout read Fin.elim0 0
    (fun h => (readout_t read h).le)
  unfold fullProgram
  change ((program.append readout).instantiate read Fin.elim0).tCount ≤ _
  rw [hln] at hp
  rw [hrn] at hp
  omega


omit hc body impl ledger in
private theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m)
    (ws : List Wire) (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hp.2⟩
  | measure => exact ⟨hp.1, by apply_assumption; exact hp.2⟩

variable [cover : SupportCover body ledger]

omit hc body impl ledger in
private theorem fixedEntry_within {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (ws : List Wire) (hp : Within ws p) : Within ws (Single.fixedEntry f p).program := by
  unfold Single.fixedEntry
  exact within_reindex p _ ws hp

omit hc in
theorem fullProgram_within : Within ledger.support fullProgram := by
  apply within_of_instantiate
  intro read history
  have he : history = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst history
  exact fullProgram_support read

omit hc in
theorem compiler_within : Within ledger.support entry.program := by
  unfold entry
  exact fixedEntry_within coefficientAt fullProgram ledger.support fullProgram_within

theorem four_certificate (q y : Wire)
    (hBaseSlots : 34 * windowSlots + 176648 ≤ officialLimits.gateSlots)
    (hBaseRecords : 65535 + 29 * impl.records14 + 4 * impl.records13 + 474 +
      body.reset.length + 34114 ≤ officialLimits.measurements)
    (hq : q ∉ ledger.support) (hy : y ∉ q :: ledger.support)
    (hslots : entry.program.gateSlots + 21 * added entry.program +
      3 * Catalyst.saved entry.program + 2 ≤ officialLimits.gateSlots)
    (hrecords : entry.finalCursor + added entry.program ≤ officialLimits.measurements) :
    Certificate officialLimits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ledger.support (65535 + 29 * c14 + 4 * c13) 56773) := by
  have base := certificate hBaseSlots hBaseRecords
  have source : Certificate officialLimits layout entry
      ⟨ledger.support.length, 7 * (65535 + 29 * c14 + 4 * c13) + 56773, entry.finalCursor⟩ :=
    { base with
      resources := by
        intro Q
        refine ⟨(base.resources Q).1, ?_, ?_⟩
        change (entry.instantiate Q).tCount ≤ _
        rw [entry, Single.fixedEntry_instantiate]
        · exact producer_t hc Q
        · simpa only [bounds, entry, Single.fixedEntry] using (base.resources Q).2.2 }
  exact WEXCredit.four_certificate officialLimits layout entry ledger.support
    (65535 + 29 * c14 + 4 * c13) 56773 q y source compiler_within hq hy
    (parent_credit hc) hslots hrecords

end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 4096


end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 4096


end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
variable [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] entry program fullProgram readout Single.fixedEntry AndGadget.added Catalyst.saved

omit cover in
theorem source_cursor : entry.finalCursor =
    65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length + 34114 := by
  unfold entry
  rw [Single.fixedEntry_cursor]

omit cover in
theorem source_slots : entry.program.gateSlots ≤ 34 * windowSlots + 176648 := by
  unfold entry
  rw [Single.fixedEntry_slots]
  exact fullProgram_slots

theorem source_counts (q y : Wire) (sourceBound : Nat)
    (hBaseSlots : 34 * windowSlots + 176648 ≤ officialLimits.gateSlots)
    (hBaseRecords : 65535 + 29 * impl.records14 + 4 * impl.records13 + 474 +
      body.reset.length + 34114 ≤ officialLimits.measurements)
    (hSource : 458745 + 29 * impl.cost14 + 4 * impl.cost13 + 56773 ≤ sourceBound) :
    added entry.program ≤ sourceBound ∧ Catalyst.saved entry.program ≤ sourceBound := by
  have h := four_identity q y entry.program (readConstant entry.coefficients.get 0) Fin.elim0
  have ht := ((certificate hBaseSlots hBaseRecords).resources 0).2.1
  change (entry.program.instantiate (readConstant entry.coefficients.get 0) Fin.elim0).tCount ≤
    458745 + 29 * impl.cost14 + 4 * impl.cost13 + 56773 at ht
  omega

theorem bounded_four_certificate {c13 c14 : Nat} (hc : ProgramCredit c13 c14)
    (q y : Wire) (sourceBound : Nat)
    (hBaseSlots : 34 * windowSlots + 176648 ≤ officialLimits.gateSlots)
    (hBaseRecords : 65535 + 29 * impl.records14 + 4 * impl.records13 + 474 +
      body.reset.length + 34114 ≤ officialLimits.measurements)
    (hSource : 458745 + 29 * impl.cost14 + 4 * impl.cost13 + 56773 ≤ sourceBound)
    (hSlots : 34 * windowSlots + 176648 + 24 * sourceBound + 2 ≤ officialLimits.gateSlots)
    (hRecords : 65535 + 29 * impl.records14 + 4 * impl.records13 + 474 + body.reset.length +
      34114 + sourceBound ≤ officialLimits.measurements)
    (hq : q ∉ ledger.support) (hy : y ∉ q :: ledger.support) :
    Certificate officialLimits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ledger.support (65535 + 29 * c14 + 4 * c13) 56773) := by
  have hc' := source_counts q y sourceBound hBaseSlots hBaseRecords hSource
  have hs := source_slots
  have hm := source_cursor
  apply four_certificate hc q y hBaseSlots hBaseRecords hq hy
  · omega
  · omega

end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33

theorem windowCoefficients_halfAlias (w : Digit) (a : Fin 32768) :
    windowCoefficients w a = windowCoefficients w
      ⟨a.val % 16384, by have h := Nat.mod_lt a.val (by decide : 0 < 16384); omega⟩ := by
  unfold windowCoefficients paddedRow
  congr 2
  apply Fin.ext
  cases w <;> norm_num [Digit.width]

end ShorECDLP.Entrant.Schedule33

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def HalfAliased (coeffs : Fin 32768 → PointCoeff) : Prop :=
  ∀ a : Fin 32768, coeffs a = coeffs ⟨a.val % 16384, by
    have h := Nat.mod_lt a.val (by decide : 0 < 16384)
    omega⟩

structure UniformNarrow (body : Single.WindowBody) where
  records : Nat
  tBound : Nat
  credit : Nat
  program : (start : Nat) → Straight 32768 start (start + records)
  coherent : ∀ coeffs Q, order • Q = 0 → (∀ a, constantPoint Q (coeffs a) ≠ 0) →
    HalfAliased coeffs → ∀ start history,
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (body.update coeffs Q)) (Single.BodyValid body)
  wellFormed : ∀ start, (program start).WellFormed
  slots : ∀ start, (program start).gateSlots ≤ body.slotBound
  wires : ∀ start, straightWires (program start) ⊆ body.support
  tCount : ∀ start read history, ((program start).instantiate read history).tCount ≤ tBound
  zero : ∀ start, residue (program start) = 0
  count_eq : ∀ start, added (program start) = credit

def uniformPrograms (n : UniformNarrow body) : Programs body where
  records13 := n.records
  records14 := n.records
  cost13 := n.tBound
  cost14 := n.tBound
  program := fun w start => castFinish (by simp [count]) (reindexStraight (paddedRow w) (n.program start))
  coherent := by
    intro Q hQ hn w start history
    have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
      intro a
      have he := window_table_point Q hQ w a.val
      simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
      rw [he]
      exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
    have halias : HalfAliased (windowCoefficients w) := windowCoefficients_halfAlias w
    have h := n.coherent (windowCoefficients w) Q hQ htable halias start history
    rw [castFinish_instantiate, reindexStraight_instantiate,
      readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
    obtain ⟨cs, hc, hm⟩ := h
    exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
  wellFormed := by
    intro w start
    rw [castFinish_wellFormed]
    exact (reindexStraight_wellFormed _ _).mpr (n.wellFormed start)
  slots := by
    intro w start
    rw [castFinish_gateSlots, reindexStraight_gateSlots]
    exact n.slots start
  wires := by
    intro w start
    rw [straightWires_castFinish, straightWires_reindex]
    exact n.wires start
  tCount := by
    intro Q w start history
    rw [castFinish_instantiate, reindexStraight_instantiate]
    simpa only [count, ite_self] using n.tCount start _ history


end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
variable [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000



end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule265
open ShorECDLP.Paper2607_13816.ChallengeMigration










end ShorECDLP.Entrant.Schedule265

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] compile codeRecords literalRecords literalToffolis ECDSAAdd.measurementCount ECDSAAdd.toffoliCount

def narrowBits : List Wire := List.range' 855 14

theorem narrow_sublist : (narrowBits ++ windowPaths).Sublist (windowBits ++ windowPaths) := by
  have he : windowBits = narrowBits ++ [869] := by
    simpa only [windowBits, narrowBits] using
      (List.range'_concat (s := 855) (n := 14) (step := 1))
  rw [he, List.append_assoc]
  exact List.Sublist.append (List.Sublist.refl _) (List.Sublist.cons _ (List.Sublist.refl _))

theorem narrow_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ rowAddCode rows, PlacedPair narrowBits windowPaths windowRoot i := by
  intro i hi
  have hp := rowAddCode_placed rows i hi
  cases i with
  | literal p =>
    intro w hw
    exact hp w ((List.Sublist.cons₂ windowRoot narrow_sublist).subset hw)
  | lookup c ports =>
    refine ⟨(List.Sublist.cons₂ _ narrow_sublist).nodup hp.1, hp.2.1, hp.2.2.1, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw ht
    exact List.disjoint_left.mp hp.2.2.2
      ((List.Sublist.cons₂ _ (List.Sublist.cons₂ _ narrow_sublist)).subset hw) ht

theorem narrow_records : codeRecords narrowBits windowPaths windowRoot
    (normalizeW (rowAddCode probeRows)) = 1900942 := by
  have layouts := pair_layouts_of_placed narrowBits windowPaths windowRoot _
    (by simp [narrowBits,windowPaths]) (pair_placed_normalize _ _ _ _ (narrow_placed probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  have counts := ((finite23_literal_counts streamLayout probeRows).2.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).2)
  simp only [rowAddCode,literalRecords_append,wLiteral,literalRecords,ECDSAAdd.measurementCount,
    Nat.zero_add,Nat.add_zero,counts,traversals_append,traversals_finite23]
  norm_num [narrowBits,traversals]

theorem rowAddCode_run_any (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (s : BasisState) (hs : liveReady s) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (rowAddCode probeRows))
      a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ =
        ⟨false,pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q a) s⟩ := by
  rw [specialize_normalize_run]
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P,hP⟩ := hs.1.2
  have secp := hs.1.1.1.1
  have hq := hs.1.1.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (ECDSAAdd.Arithmetic.regValue_zero _ _).mpr
      (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  cases he : Bridge.toB C with
  | zero =>
    have hzero : C = 0 := congrArg ECDSAAdd.ShorPort.toA he
    exact (hC hzero).elim
  | @some cx cy hc =>
    have ce : C = ECDSAAdd.ShorPort.toA (.some hc) := congrArg ECDSAAdd.ShorPort.toA he
    have hr : ECDSAAdd.ShorPort.RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
      ECDSAAdd.ShorPort.readConstant_rowReads coeffs Q _ _ ce
    have ho : order • (.some hc : ECDSAAdd.Secp256k1.Point) = 0 := by
      rw [← he]
      exact hord
    have hp2 := torsion_unit_remainder_ne_zero (.some hc) order 2
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [order])
    have hp3 := torsion_unit_remainder_ne_zero (.some hc) order 3
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [order])
    have hd : (.some hc : ECDSAAdd.Secp256k1.Point)+.some hc ≠ 0 := by
      simpa only [two_nsmul] using hp2
    have ht : (.some hc : ECDSAAdd.Secp256k1.Point)+.some hc+.some hc ≠ 0 := by
      simpa only [show (3 : Nat) = 2+1 from rfl, succ_nsmul, two_nsmul] using hp3
    have en := ECDSAAdd.ShorPort.enables_true hc hd ht
    have hdo : order • ((.some hc : ECDSAAdd.Secp256k1.Point)+.some hc) = 0 := by
      rw [nsmul_add, ho, zero_add]
    have inst := tight_stream_program_equiv (readConstant coeffs Q) probeRows a hc hr en.1 en.2 hd hdo
    have wrapped := programEquivalent_append
      (programEquivalent_append (programEquivalent_refl ([.X 838])) inst)
      (programEquivalent_refl ([.X 838]))
    simp only [rowAddCode, specialize_append, specialize_literal, specialize_finite23,
      ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    change ECDSAAdd.run (([.X 838]) ++ _ ++ ([.X 838])) m ⟨false,s⟩ = _
    rw [wrapped.2 m ⟨false,s⟩]
    have result := rowAdd_stream_run s P secp hP hq work hc m
    simpa only [inputPoint_eq s P hP, ← ce] using result



def narrowRowState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q (tableAddressValue narrowBits s)) s

theorem narrow_row_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn
      ((compile narrowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows)) start).instantiate
        (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (narrowRowState coeffs Q)) liveReady := by
  have h := pair_compile_specialization_coherent (readConstant coeffs Q) narrowBits windowPaths windowRoot
    (normalizeW (rowAddCode probeRows)) (by simp [narrowBits,windowPaths])
    (pair_placed_normalize _ _ _ _ (narrow_placed probeRows)) liveReady (narrowRowState coeffs Q)
    (by intro s hs m; exact rowAddCode_run_any _ coeffs Q hQ hn s hs m) start history
  obtain ⟨cs, aligned, mass⟩ := h
  exact ⟨cs, aligned.imp (fun _ _ hb s hs => hb s
    ⟨fun w hw => hs.2.1 w (List.mem_append_right _ hw), hs.2.2, hs⟩), mass⟩

theorem narrow_address_append (xs ys : List Wire) (s : BasisState) :
    tableAddressValue (xs ++ ys) s =
      tableAddressValue xs s + 2^xs.length * tableAddressValue ys s := by
  induction xs with
  | nil => simp [tableAddressValue]
  | cons x xs ih =>
    simp only [List.cons_append, tableAddressValue, List.length_cons, ih, pow_succ]
    ring

theorem narrow_address (s : BasisState) :
    tableAddressValue windowBits s % 16384 = tableAddressValue narrowBits s := by
  have he : windowBits = narrowBits ++ [869] := by
    simpa only [windowBits, narrowBits] using
      (List.range'_concat (s := 855) (n := 14) (step := 1))
  rw [he, narrow_address_append]
  have hb : tableAddressValue narrowBits s < 16384 := by
    simpa [narrowBits] using tableAddressValue_lt narrowBits s
  simp only [show narrowBits.length = 14 by simp [narrowBits], show 2 ^ 14 = 16384 by norm_num]
  omega


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def narrowRowSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  source (readConstant coeffs Q) narrowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))

theorem narrowRowSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (narrowRowSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (narrowRowState coeffs Q)) liveReady := by
  obtain ⟨cs, aligned, mass⟩ := narrow_row_coherent coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs, ?_, mass⟩
  simpa only [compile_run, narrowRowSource] using aligned

def narrowMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (signSource.seq (narrowRowSource coeffs Q)).seq signSource

def narrowMiddleState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  signPointState (narrowRowState coeffs Q (signPointState s))

theorem narrowMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (narrowMiddleSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (narrowMiddleState coeffs Q)) liveReady := by
  have hs : CoherentlyImplementsOn signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady := windowSign_coherent
  have first := composeCoherent hs (narrowRowSource_coherent coeffs Q hQ hn)
    (fun s h => liveReady_write _ s h)
  have all := composeCoherent first hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  exact all

@[simp] theorem narrow_write_address (P : Point) (s : BasisState) :
    tableAddressValue narrowBits (pointWrite P s) = tableAddressValue narrowBits s := by
  apply tableAddressValue_congr
  intro w hw
  apply pointWrite_frame
  simp only [narrowBits, List.mem_range'_1] at hw
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem narrowMiddle_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    narrowMiddleState coeffs Q s = pointWrite
      (P + if s 870 then Single.Physical.tablePoint coeffs Q (tableAddressValue narrowBits s)
        else -Single.Physical.tablePoint coeffs Q (tableAddressValue narrowBits s)) s := by
  by_cases hb : s 870 = true
  · simp [narrowMiddleState, signPointState, narrowRowState, inputPoint_eq s P hP,
      pointWrite_overwrite, hb]
  · have hf : s 870 = false := Bool.eq_false_iff.mpr hb
    simp [narrowMiddleState, signPointState, narrowRowState, inputPoint_eq s P hP,
      pointWrite_overwrite, hf, add_comm]

def narrowBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (prefixSource.seq (narrowMiddleSource coeffs Q)).seq suffixSource

def narrowBodyState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  suffixState (narrowMiddleState coeffs Q (prefixState s))

theorem narrowBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (narrowBodySource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (narrowBodyState coeffs Q)) windowReady := by
  have h := composeCoherent prefix_coherent (narrowMiddle_coherent coeffs Q hQ hn)
    (fun s hs => windowPrepare_live _ (rootFlip_live s hs))
  exact composeCoherent (f := fun s => narrowMiddleState coeffs Q (prefixState s)) (g := suffixState)
    h suffix_coherent (fun _ _ => trivial)


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def HalfAliased (coeffs : Fin 32768 → PointCoeff) : Prop :=
  ∀ a : Fin 32768, coeffs a = coeffs ⟨a.val % 16384, by
    have h := Nat.mod_lt a.val (by decide : 0 < 16384)
    omega⟩

theorem narrow_table (coeffs : Fin 32768 → PointCoeff) (Q : Point) (h : HalfAliased coeffs)
    (s : BasisState) :
    Single.Physical.tablePoint coeffs Q (tableAddressValue narrowBits s) =
      Single.Physical.tablePoint coeffs Q (tableAddressValue windowBits s) := by
  have hn : tableAddressValue narrowBits s < 32768 := by
    have hb := tableAddressValue_lt narrowBits s
    change tableAddressValue narrowBits s < 16384 at hb
    exact lt_trans hb (by decide)
  have hw : tableAddressValue windowBits s < 32768 := by
    change tableAddressValue windowBits s < 32768
    exact tableAddressValue_lt windowBits s
  have hc : coeffs ⟨tableAddressValue narrowBits s, hn⟩ =
      coeffs ⟨tableAddressValue windowBits s, hw⟩ := by
    have he : (⟨tableAddressValue narrowBits s, hn⟩ : Fin 32768) =
        ⟨tableAddressValue windowBits s % 16384, by have ht := Nat.mod_lt (tableAddressValue windowBits s) (by decide : 0 < 16384); omega⟩ := by
      apply Fin.ext
      exact (narrow_address s).symm
    rw [he]
    exact (h ⟨tableAddressValue windowBits s, hw⟩).symm
  unfold Single.Physical.tablePoint
  simp only [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hw]
  exact congrArg (constantPoint Q) hc

theorem narrowBodyState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (halias : HalfAliased coeffs) (s : BasisState) (hs : windowReady s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    narrowBodyState coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
          signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
          signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)) else 0) s := by
  have hp : pointStateCoordinates (prefixState s) = fig14PointEncoding P :=
    (windowPrepareState_coordinates (rootFlip s)).trans (rootFlip_coordinates s P hs.1.1.1.1 hP)
  have hsign : prefixState s 870 = s 870 := by
    rw [prefixState,windowPrepareState_frame _ _ (by decide +kernel)]
    simp [rootFlip,ECDSAAdd.writeBit,windowRoot]
  rw [narrowBodyState,narrowMiddle_correct coeffs Q _ P hp,suffix_pointWrite,outer_inverse,
    hsign,narrow_table coeffs Q halias,prefix_address s (windowReady_active s hs)]
  simp only [windowReady_active s hs]
  simp only [if_pos True.intro]
  simp only [Single.Physical.tablePoint,Nat.mod_eq_of_lt
    (signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s))]


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] compile Bridge.translate codeRecords Bridge.tmplMeas literalT
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.measurementCount ECDSAAdd.toffoliCount
  Nat.add Straight.instantiate AdaptiveCircuit.run AdaptiveCircuit.tCount literalToffolis

def narrowAddProgram (start : Nat) : Straight 32768 start (start+1900942) :=
  NaiveChallenge.castFinish (congrArg (fun k => start+k) narrow_records)
    (compile narrowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows)) start)

def narrowBodyProgram (start : Nat) : Straight 32768 start (start+1902986) :=
  NaiveChallenge.castFinish (by omega)
    (((((prefixProgram start).append (nProgram start)).append (narrowAddProgram (start+1022))).append
      (nProgram (start+1022+1900942))).append (suffixProgram (start+1022+1900942+1022)))

theorem narrowAddProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (history : Fin start → Bool) :
    ((narrowAddProgram start).instantiate (readConstant coeffs Q) history).run = (narrowRowSource coeffs Q).run := by
  rw [narrowAddProgram,NaiveChallenge.instantiate_castFinish,compile_run]
  rfl

theorem narrowBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (history : Fin start → Bool) :
    ((narrowBodyProgram start).instantiate (readConstant coeffs Q) history).run = (narrowBodySource coeffs Q).run := by
  rw [narrowBodyProgram,NaiveChallenge.instantiate_castFinish]
  rw [append_run_fixed _ _ _ _ _ (fun h => suffixProgram_run _ _ h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => nProgram_run _ _ h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => narrowAddProgram_run _ coeffs Q h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => nProgram_run _ _ h),AdaptiveCircuit.run_seq,prefixProgram_run]
  simp only [← AdaptiveCircuit.run_seq,narrowBodySource,narrowMiddleSource,adaptive_seq_assoc]

theorem narrowAddProgram_wellFormed (start : Nat) : (narrowAddProgram start).WellFormed := by
  rw [narrowAddProgram,NaiveChallenge.wellFormed_castFinish]
  exact pair_compile_wellFormed narrowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    (by simp [narrowBits,windowPaths])
    (pair_placed_normalize _ _ _ _ (narrow_placed probeRows))
    (normalized_literals_valid _ (rowAddCode_physical probeRows)) start

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEXCredit
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] WEX.compile WEX.nProgram WEX.prefixProgram WEX.suffixProgram
  WEX.narrowAddProgram WEX.narrowBodyProgram ECDSAAdd.toffoliCount
  ECDSAAdd.Baselines.normalizeProgram WEX.literalToffolis WEX.normalizeW Nat.add Nat.mul

theorem narrow_add_residue (start : Nat) : residue (WEX.narrowAddProgram start) = 0 := by
  unfold WEX.narrowAddProgram
  rw [residue_naive_cast]
  exact compile_residue _ _ _ _ _

theorem narrow_add_added (start : Nat) : added (WEX.narrowAddProgram start) =
    WEX.literalToffolis (WEX.normalizeW (WEX.rowAddCode WEX.probeRows)) + 21 * 16383 := by
  have layouts := WEX.pair_layouts_of_placed WEX.narrowBits WEX.windowPaths WEX.windowRoot _
    (by simp [WEX.narrowBits, WEX.windowPaths])
    (WEX.pair_placed_normalize _ _ _ _ (WEX.narrow_placed WEX.probeRows))
  unfold WEX.narrowAddProgram
  rw [added_naive_cast, compile_added _ _ _ _ layouts, WEX.traversals_normalize]
  have ht : WEX.traversals (WEX.rowAddCode WEX.probeRows) = 21 := by
    rw [WEX.rowAddCode, WEX.traversals_append, WEX.traversals_append,
      WEX.traversals_finite23]
    simp only [WEX.wLiteral, WEX.traversals, Nat.zero_add, Nat.add_zero]
  generalize WEX.literalToffolis (WEX.normalizeW (WEX.rowAddCode WEX.probeRows)) = k
  rw [ht]
  norm_num [WEX.narrowBits]

theorem narrow_body_credit (start : Nat) : ProgramCredit (WEX.narrowBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram) +
      WEX.literalToffolis (WEX.normalizeW (WEX.rowAddCode WEX.probeRows)) + 21 * 16383) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram)
  let b := WEX.literalToffolis (WEX.normalizeW (WEX.rowAddCode WEX.probeRows))
  have hl : ProgramCredit (WEX.nProgram start) a := ⟨n_residue start,n_added start⟩
  have ha : ProgramCredit (WEX.narrowAddProgram (start+1022)) (b+21*16383) :=
    ⟨narrow_add_residue _,narrow_add_added _⟩
  have hr : ProgramCredit (WEX.nProgram (start+1022+1900942)) a := ⟨n_residue _,n_added _⟩
  have ht := credit_append (credit_append (credit_append (credit_append (prefix_credit start) hl) ha) hr)
    (suffix_credit (start+1022+1900942+1022))
  have hn : (((0 + a) + (b + 21 * 16383)) + a) + 0 = 2*a+b+21*16383 := by omega
  have ht : ProgramCredit _ (2*a+b+21*16383) := hn ▸ ht
  unfold WEX.narrowBodyProgram
  exact credit_naive_cast _ ht

end
end ShorECDLP.Entrant.WEXCredit

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
attribute [local irreducible] compile Bridge.translate ECDSAAdd.wires

theorem narrowAddProgram_source (start : Nat) : ChallengeMigration.straightWires (narrowAddProgram start) ⊆ sourceSupport := by
  rw [narrowAddProgram,support_castFinish]
  apply compile_support narrowBits windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    sourceSupport (start := start)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro p hp
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
    cases j with
    | literal q =>
      cases he
      rw [ECDSAAdd.Baselines.normalize_wires]
      simp only [rowAddCode,List.mem_append] at hj
      rcases hj with (hj | hj) | hj
      · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hj
        subst q
        intro w hw
        have he : w = 838 := by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw
        subst w
        exact List.mem_toFinset.mpr ((sourceSupport_mem 838).mpr (Or.inl (by decide +kernel)))
      · exact finiteOne_literal_source probeRows q (tight_finite_literal_subset streamLayout probeRows q (finite23_literal_subset streamLayout probeRows q hj))
      · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hj
        subst q
        intro w hw
        have he : w = 838 := by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw
        subst w
        exact List.mem_toFinset.mpr ((sourceSupport_mem 838).mpr (Or.inl (by decide +kernel)))
    | lookup c ports => cases he
  · intro c ports hc
    have h := List.all_eq_true.mp row_sourceLookupOK _ hc
    have h : (∀ q ∈ c, fixedPort q ∨ oldWork q) ∧
        (∀ w ∈ portTargets ports, fixedPort w ∨ oldWork w) := by
      simpa [sourceLookupOK,List.all_eq_true] using h
    exact ⟨fun q hq => (sourceSupport_mem q).mpr (h.1 q hq),
      fun w hw => (sourceSupport_mem w).mpr (h.2 w hw)⟩


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem narrowBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : HalfAliased coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((narrowBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) windowReady := by
  have h := narrowBodySource_coherent coeffs Q hQ hn
  have he := h.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) (by
    intro s hs
    obtain ⟨P,hP⟩ := hs.1.2
    have he : narrowBodyState coeffs Q s = bodyState coeffs Q s := by
      rw [narrowBodyState_correct coeffs Q halias s hs P hP,bodyState_correct coeffs Q s hs P hP]
    simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,he])
  obtain ⟨cs,aligned,mass⟩ := he
  refine ⟨cs,?_,mass⟩
  rw [narrowBodyProgram_run]
  exact aligned

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEXCredit
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] WEX.compile WEX.nProgram WEX.prefixProgram WEX.suffixProgram
  WEX.narrowAddProgram WEX.narrowBodyProgram ECDSAAdd.toffoliCount
  ECDSAAdd.Baselines.normalizeProgram WEX.literalToffolis WEX.normalizeW Nat.add Nat.mul

theorem narrow_body_t_bound (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((WEX.narrowBodyProgram start).instantiate read history).tCount ≤ 17555608 := by
  have hn := ECDSAAdd.Baselines.normalize_toffoli WEX.windowSignProgram
  rw [WEX.windowSign_counts.1] at hn
  have ha := WEX.literalToffolis_normalize (WEX.rowAddCode WEX.probeRows)
  have hc := (WEX.finite23_literal_counts WEX.streamLayout WEX.probeRows).1.trans
    (WEX.tight_finite_literal_counts WEX.streamLayout WEX.streamLayout_widths WEX.streamLayout_nodup WEX.probeRows).1
  have hrow : WEX.literalToffolis (WEX.rowAddCode WEX.probeRows) = 2161857 := by
    simp only [WEX.rowAddCode,WEX.literalToffolis_append,WEX.wLiteral,WEX.literalToffolis,ECDSAAdd.toffoliCount,
      Nat.zero_add,Nat.add_zero,hc]
  rw [hrow] at ha
  have hs := narrow_body_credit start
  have ht := exact_t (WEX.narrowBodyProgram start) hs.1 read history
  rw [hs.2] at ht
  omega

end
end ShorECDLP.Entrant.WEXCredit

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] compile Bridge.translate codeRecords Bridge.tmplMeas literalT
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.measurementCount ECDSAAdd.toffoliCount
  Nat.add Straight.instantiate AdaptiveCircuit.run AdaptiveCircuit.tCount literalToffolis
  Straight.gateSlots codeSlots literalSlotSum portTotal

theorem narrowBodyProgram_wellFormed (start : Nat) : (narrowBodyProgram start).WellFormed := by
  rw [narrowBodyProgram,NaiveChallenge.wellFormed_castFinish]
  apply ChallengeMigration.straight_append_wellFormed
  · apply ChallengeMigration.straight_append_wellFormed
    · apply ChallengeMigration.straight_append_wellFormed
      · exact ChallengeMigration.straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nProgram_wellFormed start)
      · exact narrowAddProgram_wellFormed _
    · exact nProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem narrowAddProgram_slots (start : Nat) : (narrowAddProgram start).gateSlots =
    codeSlots narrowBits (normalizeW (rowAddCode probeRows)) := by
  rw [narrowAddProgram,NaiveChallenge.gateSlots_castFinish]
  apply compile_slots
  exact pair_layouts_of_placed narrowBits windowPaths windowRoot _
    (by simp [narrowBits,windowPaths]) (pair_placed_normalize _ _ _ _ (narrow_placed probeRows))

theorem narrowRow_slots_bound (start : Nat) : (narrowAddProgram start).gateSlots ≤ 1000000000 := by
  rw [narrowAddProgram_slots]
  have bound := codeSlots_bound narrowBits (normalizeW (rowAddCode probeRows))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at bound
  have literal := rowAdd_literal_slots_bound
  have ports := rowAdd_portTotal
  have trav : traversals (rowAddCode probeRows) = 21 := by
    simp only [rowAddCode,traversals_append,wLiteral,traversals_finite23,traversals]
  rw [trav] at bound
  have hlen : narrowBits.length = 14 := by simp [narrowBits]
  rw [hlen] at bound
  norm_num at bound
  omega

theorem narrowBodyProgram_slots (start : Nat) : (narrowBodyProgram start).gateSlots ≤ 1100000000 := by
  rw [narrowBodyProgram,NaiveChallenge.gateSlots_castFinish]
  simp only [Straight.gateSlots_append,nProgram_slots,narrowAddProgram_slots,prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := sign_slots_bound
  have row := narrowRow_slots_bound start
  rw [narrowAddProgram_slots] at row
  omega

theorem narrowBodyProgram_source (start : Nat) :
    ChallengeMigration.straightWires (narrowBodyProgram start) ⊆ sourceSupport := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ sourceSupport := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  have hs (k : Nat) : ChallengeMigration.straightWires (suffixProgram k) ⊆ sourceSupport := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  rw [narrowBodyProgram,support_castFinish]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,nProgram_source _⟩,narrowAddProgram_source _⟩,nProgram_source _⟩,hs _⟩

def narrowCompactProgram (start : Nat) : Straight 32768 start (start+1902986) :=
  relabelStraight compactPerm (narrowBodyProgram start)

theorem narrowCompactProgram_support (start : Nat) :
    ChallengeMigration.straightWires (narrowCompactProgram start) ⊆ List.range 1634 := by
  rw [narrowCompactProgram,straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr (compactPerm_bound v (narrowBodyProgram_source start hv))

theorem narrowCompactProgram_slots (start : Nat) : (narrowCompactProgram start).gateSlots ≤ 1100000000 := by
  rw [narrowCompactProgram,relabelStraight_slots]
  exact narrowBodyProgram_slots start

theorem narrowCompactProgram_t (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((narrowCompactProgram start).instantiate read history).tCount ≤ 17555608 := by
  rw [narrowCompactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]
  exact WEXCredit.narrow_body_t_bound start read history

theorem narrowCompactProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : HalfAliased coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((narrowCompactProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := (narrowBodyProgram_coherent coeffs Q hQ hn halias start history).relabel compactPerm
  have hr : CoherentlyImplementsOn
      (((narrowBodyProgram start).instantiate (readConstant coeffs Q) history).relabel compactPerm)
      ((relabelState compactPerm).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState compactPerm.symm)))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,hc,hm⟩ := h
    refine ⟨cs,hc.imp (fun _ _ hb s hs => hb s hs.1),hm⟩
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
    (by intro s _; simp [compactState,compactPull,LinearMap.comp_apply,relabelState,ket])
  rw [narrowCompactProgram,relabelStraight_instantiate]
  exact he

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.Schedule33.UniformFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem residue_relabel {n s e : Nat} (p : Straight n s e) (f : Wire ≃ Wire) :
    residue (relabelStraight f p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [relabelStraight,relabelTemplateGate,Gate.relabel,residue,primitivePhaseCost]
    | whenBit r v g => cases g <;> simp_all [relabelStraight,relabelTemplateGate,Gate.relabel,residue,tCost]
  | recordGate i v g p ih => cases g <;> simp_all [relabelStraight,Gate.relabel,residue,tCost]
  | measure => simp_all [relabelStraight,residue]


attribute [local irreducible] WEX.compactBody WEX.compactState WEX.compactReady
  WEX.narrowCompactProgram WEX.narrowBodyProgram WEX.compile WEX.normalizeW
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount WEX.literalToffolis Nat.add Nat.mul

private theorem n_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : HalfAliased coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((WEX.narrowCompactProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (WEX.compactBody.update coeffs Q)) (Single.BodyValid WEX.compactBody) := by
  have h := WEX.narrowCompactProgram_coherent coeffs Q hQ hn halias start history
  simpa only [Single.BodyValid, WEX.compactBody] using h

private theorem n_slots (start : Nat) : (WEX.narrowCompactProgram start).gateSlots ≤ WEX.compactBody.slotBound := by
  have h := WEX.narrowCompactProgram_slots start
  simpa only [WEX.compactBody] using h

private theorem n_wires (start : Nat) : straightWires (WEX.narrowCompactProgram start) ⊆ WEX.compactBody.support := by
  have h := WEX.narrowCompactProgram_support start
  simpa only [WEX.compactBody] using h

private theorem n_zero (start : Nat) : residue (WEX.narrowCompactProgram start) = 0 := by
  rw [WEX.narrowCompactProgram, residue_relabel]
  exact (WEXCredit.narrow_body_credit start).1

private theorem n_count (start : Nat) : added (WEX.narrowCompactProgram start) =
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram) +
      WEX.literalToffolis (WEX.normalizeW (WEX.rowAddCode WEX.probeRows)) + 21 * 16383) := by
  rw [WEX.narrowCompactProgram, added_relabel]
  exact (WEXCredit.narrow_body_credit start).2


def narrow : UniformNarrow WEX.compactBody where
  records := 1902986
  tBound := 17555608
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram) +
    WEX.literalToffolis (WEX.normalizeW (WEX.rowAddCode WEX.probeRows)) + 21 * 16383
  program := WEX.narrowCompactProgram
  coherent := n_coherent
  wellFormed := by
    intro start
    rw [WEX.narrowCompactProgram]
    exact (relabelStraight_wellFormed WEX.compactPerm (WEX.narrowBodyProgram start)).mpr
      (WEX.narrowBodyProgram_wellFormed start)
  slots := n_slots
  wires := n_wires
  tCount := WEX.narrowCompactProgram_t
  zero := n_zero
  count_eq := n_count


end
end ShorECDLP.Entrant.Schedule33.UniformFinal

namespace ShorECDLP.Entrant.Schedule33.UniformFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] narrow WEX.compactBody WEX.narrowCompactProgram WEX.narrowBodyProgram
  WEX.compile WEX.normalizeW ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount WEX.literalToffolis
  Nat.add Nat.mul AndGadget.added

private theorem count_bound_from_t (t c : Nat) (he : t = 7*c) (hb : t ≤ 17555608) :
    c ≤ 2507944 := by omega

theorem narrow_cost_upper : narrow.tBound ≤ 17555608 := by
  rw [narrow]

theorem narrow_credit_upper : narrow.credit ≤ 2507944 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow.program 0) (narrow.zero 0) read Fin.elim0
  have hc := narrow.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count_bound_from_t _ _ he' (ht.trans narrow_cost_upper)
end
end ShorECDLP.Entrant.Schedule33.UniformFinal

namespace ShorECDLP.Entrant.Schedule33.UniformFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] narrow WEX.narrowCompactProgram WEX.narrowBodyProgram
  WEX.compile WEX.normalizeW ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount WEX.literalToffolis
  Nat.add Nat.mul AndGadget.added

local instance bodyInstance : Single.WindowBody := WEX.compactBody
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEX.compactBody
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
local instance programInstance : Programs bodyInstance := uniformPrograms narrow


end
end ShorECDLP.Entrant.Schedule33.UniformFinal


namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

attribute [local irreducible] compile codeRecords literalRecords literalToffolis ECDSAAdd.measurementCount ECDSAAdd.toffoliCount

def widthBits (k : Nat) : List Wire := List.range' 855 k

theorem width_bits_split (k : Nat) (hk : k ≤ 15) :
    windowBits = widthBits k ++ List.range' (855 + k) (15 - k) := by
  have he : k + (15 - k) = 15 := Nat.add_sub_of_le hk
  simpa only [windowBits,widthBits,Nat.one_mul,he] using
    (List.range'_append (s := 855) (m := k) (n := 15-k) (step := 1)).symm

theorem width_sublist (k : Nat) (hk : k ≤ 15) :
    (widthBits k ++ windowPaths).Sublist (windowBits ++ windowPaths) := by
  rw [width_bits_split k hk, List.append_assoc]
  exact List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _)


theorem width_placed (k : Nat) (hk : k ≤ 15) (rows : Nat → Fin 32768) :
    ∀ i ∈ rowAddCode rows, PlacedPair (widthBits k) windowPaths windowRoot i := by
  intro i hi
  have hp := rowAddCode_placed rows i hi
  cases i with
  | literal p =>
    intro w hw
    exact hp w ((List.Sublist.cons₂ windowRoot (width_sublist k hk)).subset hw)
  | lookup c ports =>
    refine ⟨(List.Sublist.cons₂ _ (width_sublist k hk)).nodup hp.1, hp.2.1, hp.2.2.1, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw ht
    exact List.disjoint_left.mp hp.2.2.2
      ((List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (width_sublist k hk))).subset hw) ht

theorem width_records (k : Nat) (hk : k ≤ 15) :
    codeRecords (widthBits k) windowPaths windowRoot (normalizeW (rowAddCode probeRows)) =
      1556899 + 21 * (2 ^ k - 1) := by
  have layouts := pair_layouts_of_placed (widthBits k) windowPaths windowRoot _
    (by simpa [widthBits,windowPaths] using hk) (pair_placed_normalize _ _ _ _ (width_placed k hk probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  have counts := ((finite23_literal_counts streamLayout probeRows).2.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).2)
  simp only [rowAddCode,literalRecords_append,wLiteral,literalRecords,ECDSAAdd.measurementCount,
    Nat.zero_add,Nat.add_zero,counts,traversals_append,traversals_finite23]
  simp [widthBits,traversals]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge ShorECDLP.Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
theorem width_address (k : Nat) (hk : k ≤ 15) (s : BasisState) :
    tableAddressValue windowBits s % (2 ^ k) = tableAddressValue (widthBits k) s := by
  rw [width_bits_split k hk, narrow_address_append]
  have hlen : (widthBits k).length = k := by simp [widthBits]
  rw [hlen]
  have hbound : tableAddressValue (widthBits k) s < 2 ^ k := by
    simpa only [hlen] using tableAddressValue_lt (widthBits k) s
  simp [Nat.add_mod, Nat.mod_eq_of_lt hbound]

theorem width_credit (k : Nat) (hk : k ≤ 15) (start : Nat) :
    WEXCredit.ProgramCredit (compile (widthBits k) windowPaths windowRoot
      (normalizeW (rowAddCode probeRows)) start)
      (literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2 ^ k - 1)) := by
  have layouts := pair_layouts_of_placed (widthBits k) windowPaths windowRoot _
    (by simpa [widthBits,windowPaths] using hk) (pair_placed_normalize _ _ _ _ (width_placed k hk probeRows))
  constructor
  · exact WEXCredit.compile_residue _ _ _ _ _
  · rw [WEXCredit.compile_added _ _ _ _ layouts, traversals_normalize]
    have ht : traversals (rowAddCode probeRows) = 21 := by
      simp only [rowAddCode,traversals_append,wLiteral,traversals_finite23,traversals]
    rw [ht]
    simp [widthBits]

def widthRowState (k : Nat) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (s : BasisState) : BasisState :=
  pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q (tableAddressValue (widthBits k) s)) s

theorem width_row_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn
      ((compile (widthBits k) windowPaths windowRoot (normalizeW (rowAddCode probeRows)) start).instantiate
        (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (widthRowState k coeffs Q)) liveReady := by
  have h := pair_compile_specialization_coherent (readConstant coeffs Q) (widthBits k) windowPaths windowRoot
    (normalizeW (rowAddCode probeRows)) (by simpa [widthBits,windowPaths] using hk)
    (pair_placed_normalize _ _ _ _ (width_placed k hk probeRows)) liveReady (widthRowState k coeffs Q)
    (by intro s hs m; exact rowAddCode_run_any _ coeffs Q hQ hn s hs m) start history
  obtain ⟨cs, aligned, mass⟩ := h
  exact ⟨cs, aligned.imp (fun _ _ hb s hs => hb s
    ⟨fun w hw => hs.2.1 w (List.mem_append_right _ hw), hs.2.2, hs⟩), mass⟩

def widthRowSource (k : Nat) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) : AdaptiveCircuit :=
  source (readConstant coeffs Q) (widthBits k) windowPaths windowRoot (normalizeW (rowAddCode probeRows))

theorem widthRowSource_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (widthRowSource k coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (widthRowState k coeffs Q)) liveReady := by
  obtain ⟨cs, aligned, mass⟩ := width_row_coherent k hk coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs, ?_, mass⟩
  simpa only [compile_run, widthRowSource] using aligned

def widthMiddleSource (k : Nat) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) : AdaptiveCircuit :=
  (signSource.seq (widthRowSource k coeffs Q)).seq signSource

def widthMiddleState (k : Nat) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (s : BasisState) : BasisState :=
  signPointState (widthRowState k coeffs Q (signPointState s))

theorem widthMiddle_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (widthMiddleSource k coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (widthMiddleState k coeffs Q)) liveReady := by
  have hs : CoherentlyImplementsOn signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady := windowSign_coherent
  have first := composeCoherent hs (widthRowSource_coherent k hk coeffs Q hQ hn)
    (fun s h => liveReady_write _ s h)
  have all := composeCoherent first hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  exact all

theorem width_bits_subset (k : Nat) (hk : k ≤ 15) : widthBits k ⊆ windowBits := by
  rw [width_bits_split k hk]
  exact List.subset_append_left _ _

@[simp] theorem width_write_address (k : Nat) (hk : k ≤ 15)
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    tableAddressValue (widthBits k) (pointWrite P s) = tableAddressValue (widthBits k) s := by
  apply tableAddressValue_congr
  intro w hw
  exact pointWrite_frame P s w (fun hp => window_address_outside_point w hp (width_bits_subset k hk hw))

theorem widthMiddle_correct (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (s : BasisState) (P : ShorECDLP.Secp256k1.Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    widthMiddleState k coeffs Q s = pointWrite
      (P + if s 870 then Single.Physical.tablePoint coeffs Q (tableAddressValue (widthBits k) s)
        else -Single.Physical.tablePoint coeffs Q (tableAddressValue (widthBits k) s)) s := by
  by_cases hb : s 870 = true
  · simp [widthMiddleState, signPointState, widthRowState, inputPoint_eq s P hP,
      pointWrite_overwrite, hb, width_write_address k hk]
  · have hf : s 870 = false := Bool.eq_false_iff.mpr hb
    simp [widthMiddleState, signPointState, widthRowState, inputPoint_eq s P hP,
      pointWrite_overwrite, hf, add_comm, width_write_address k hk]


def WidthAliased (k : Nat) (coeffs : Fin 32768 → PointCoeff) : Prop :=
  ∀ a : Fin 32768, coeffs a = coeffs ⟨a.val % (2 ^ k), by have h := Nat.mod_le a.val (2 ^ k); omega⟩

theorem width_table (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (h : WidthAliased k coeffs) (s : BasisState) :
    Single.Physical.tablePoint coeffs Q (tableAddressValue (widthBits k) s) =
      Single.Physical.tablePoint coeffs Q (tableAddressValue windowBits s) := by
  have hw : tableAddressValue windowBits s < 32768 := by
    change tableAddressValue windowBits s < 32768
    exact tableAddressValue_lt windowBits s
  have hn : tableAddressValue (widthBits k) s < 32768 := by
    rw [← width_address k hk s]
    exact lt_of_le_of_lt (Nat.mod_le _ _) hw
  have hc : coeffs ⟨tableAddressValue (widthBits k) s, hn⟩ =
      coeffs ⟨tableAddressValue windowBits s, hw⟩ := by
    have he : (⟨tableAddressValue (widthBits k) s, hn⟩ : Fin 32768) =
        ⟨tableAddressValue windowBits s % (2 ^ k), by have ht := Nat.mod_le (tableAddressValue windowBits s) (2 ^ k); omega⟩ := by
      apply Fin.ext
      exact (width_address k hk s).symm
    rw [he]
    exact (h ⟨tableAddressValue windowBits s, hw⟩).symm
  unfold Single.Physical.tablePoint
  simp only [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hw]
  exact congrArg (constantPoint Q) hc

def widthBodySource (k : Nat) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (widthMiddleSource k coeffs Q)).seq suffixSource

def widthBodyState (k : Nat) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (s : BasisState) : BasisState :=
  suffixState (widthMiddleState k coeffs Q (prefixState s))

theorem widthBodySource_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (widthBodySource k coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (widthBodyState k coeffs Q)) windowReady := by
  have h := composeCoherent prefix_coherent (widthMiddle_coherent k hk coeffs Q hQ hn)
    (fun s hs => windowPrepare_live _ (rootFlip_live s hs))
  exact composeCoherent (f := fun s => widthMiddleState k coeffs Q (prefixState s)) (g := suffixState)
    h suffix_coherent (fun _ _ => trivial)

theorem widthBodyState_correct (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (halias : WidthAliased k coeffs) (s : BasisState)
    (hs : windowReady s) (P : ShorECDLP.Secp256k1.Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    widthBodyState k coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
          signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
          signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)) else 0) s := by
  have hp : pointStateCoordinates (prefixState s) = fig14PointEncoding P :=
    (windowPrepareState_coordinates (rootFlip s)).trans (rootFlip_coordinates s P hs.1.1.1.1 hP)
  have hsign : prefixState s 870 = s 870 := by
    rw [prefixState,windowPrepareState_frame _ _ (by decide +kernel)]
    simp [rootFlip,ECDSAAdd.writeBit,windowRoot]
  rw [widthBodyState,widthMiddle_correct k hk coeffs Q _ P hp,suffix_pointWrite,outer_inverse,
    hsign,width_table k hk coeffs Q halias,prefix_address s (windowReady_active s hs)]
  simp only [windowReady_active s hs]
  simp only [if_pos True.intro]
  simp only [Single.Physical.tablePoint,Nat.mod_eq_of_lt
    (signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s))]

attribute [local irreducible] Bridge.translate Bridge.tmplMeas literalT
  ECDSAAdd.Baselines.normalizeProgram Nat.add Straight.instantiate AdaptiveCircuit.run AdaptiveCircuit.tCount

def widthAddRecords (k : Nat) : Nat := 1556899 + 21 * (2 ^ k - 1)
def widthBodyRecords (k : Nat) : Nat := 1558943 + 21 * (2 ^ k - 1)

def widthAddProgram (k : Nat) (hk : k ≤ 15) (start : Nat) :
    Straight 32768 start (start + widthAddRecords k) :=
  NaiveChallenge.castFinish (congrArg (fun m => start + m) (width_records k hk))
    (compile (widthBits k) windowPaths windowRoot (normalizeW (rowAddCode probeRows)) start)

def widthBodyProgram (k : Nat) (hk : k ≤ 15) (start : Nat) :
    Straight 32768 start (start + widthBodyRecords k) :=
  NaiveChallenge.castFinish (by unfold widthBodyRecords widthAddRecords; omega)
    (((((prefixProgram start).append (nProgram start)).append
      (widthAddProgram k hk (start + 1022))).append
      (nProgram (start + 1022 + widthAddRecords k))).append
      (suffixProgram (start + 1022 + widthAddRecords k + 1022)))

theorem widthAddProgram_run (k : Nat) (hk : k ≤ 15) (start : Nat)
    (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (history : Fin start → Bool) :
    ((widthAddProgram k hk start).instantiate (readConstant coeffs Q) history).run =
      (widthRowSource k coeffs Q).run := by
  rw [widthAddProgram,NaiveChallenge.instantiate_castFinish,compile_run]
  rfl

theorem widthBodyProgram_run (k : Nat) (hk : k ≤ 15) (start : Nat)
    (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (history : Fin start → Bool) :
    ((widthBodyProgram k hk start).instantiate (readConstant coeffs Q) history).run =
      (widthBodySource k coeffs Q).run := by
  rw [widthBodyProgram,NaiveChallenge.instantiate_castFinish]
  rw [append_run_fixed _ _ _ _ _ (fun h => suffixProgram_run _ _ h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => nProgram_run _ _ h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => widthAddProgram_run k hk _ coeffs Q h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => nProgram_run _ _ h),AdaptiveCircuit.run_seq,prefixProgram_run]
  simp only [← AdaptiveCircuit.run_seq,widthBodySource,widthMiddleSource,adaptive_seq_assoc]

theorem widthAddProgram_wellFormed (k : Nat) (hk : k ≤ 15) (start : Nat) :
    (widthAddProgram k hk start).WellFormed := by
  rw [widthAddProgram,NaiveChallenge.wellFormed_castFinish]
  exact pair_compile_wellFormed (widthBits k) windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    (by simpa [widthBits,windowPaths] using hk)
    (pair_placed_normalize _ _ _ _ (width_placed k hk probeRows))
    (normalized_literals_valid _ (rowAddCode_physical probeRows)) start

theorem widthBodyProgram_wellFormed (k : Nat) (hk : k ≤ 15) (start : Nat) :
    (widthBodyProgram k hk start).WellFormed := by
  rw [widthBodyProgram,NaiveChallenge.wellFormed_castFinish]
  apply ChallengeMigration.straight_append_wellFormed
  · apply ChallengeMigration.straight_append_wellFormed
    · apply ChallengeMigration.straight_append_wellFormed
      · exact ChallengeMigration.straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nProgram_wellFormed start)
      · exact widthAddProgram_wellFormed k hk _
    · exact nProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem widthBodyProgram_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (halias : WidthAliased k coeffs)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((widthBodyProgram k hk start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) windowReady := by
  have h := widthBodySource_coherent k hk coeffs Q hQ hn
  have he := h.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) (by
    intro s hs
    obtain ⟨P,hP⟩ := hs.1.2
    have he : widthBodyState k coeffs Q s = bodyState coeffs Q s := by
      rw [widthBodyState_correct k hk coeffs Q halias s hs P hP,bodyState_correct coeffs Q s hs P hP]
    simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,he])
  obtain ⟨cs,aligned,mass⟩ := he
  refine ⟨cs,?_,mass⟩
  rw [widthBodyProgram_run]
  exact aligned

theorem widthAddProgram_credit (k : Nat) (hk : k ≤ 15) (start : Nat) :
    WEXCredit.ProgramCredit (widthAddProgram k hk start)
      (literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2 ^ k - 1)) := by
  unfold widthAddProgram
  exact WEXCredit.credit_naive_cast _ (width_credit k hk start)

theorem widthBodyProgram_credit (k : Nat) (hk : k ≤ 15) (start : Nat) :
    WEXCredit.ProgramCredit (widthBodyProgram k hk start)
      (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
        literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2 ^ k - 1)) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)
  let b := literalToffolis (normalizeW (rowAddCode probeRows))
  have hl : WEXCredit.ProgramCredit (nProgram start) a := ⟨WEXCredit.n_residue start,WEXCredit.n_added start⟩
  have ha : WEXCredit.ProgramCredit (widthAddProgram k hk (start + 1022)) (b + 21 * (2 ^ k - 1)) :=
    widthAddProgram_credit k hk _
  have hr : WEXCredit.ProgramCredit (nProgram (start + 1022 + widthAddRecords k)) a :=
    ⟨WEXCredit.n_residue _, WEXCredit.n_added _⟩
  have ht := WEXCredit.credit_append (WEXCredit.credit_append (WEXCredit.credit_append
    (WEXCredit.credit_append (WEXCredit.prefix_credit start) hl) ha) hr)
    (WEXCredit.suffix_credit (start + 1022 + widthAddRecords k + 1022))
  have hn : (((0 + a) + (b + 21 * (2 ^ k - 1))) + a) + 0 = 2 * a + b + 21 * (2 ^ k - 1) := by omega
  have ht : WEXCredit.ProgramCredit _ (2 * a + b + 21 * (2 ^ k - 1)) := hn ▸ ht
  unfold widthBodyProgram
  exact WEXCredit.credit_naive_cast _ ht


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Schedule33.UniformFinal
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] WEX.compactBody WEX.narrowCompactProgram WEX.narrowBodyProgram
  WEX.compile WEX.normalizeW ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount WEX.literalToffolis
  Nat.add Nat.mul AndGadget.added

private theorem narrow_program_eq : narrow.program 0 = narrowCompactProgram 0 := by
  rfl


theorem narrow_credit_relation :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * 16383 = narrow.credit := by
  have hc := narrow.count_eq 0
  rw [narrow_program_eq] at hc
  have hn : added (narrowCompactProgram 0) =
      2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
        literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * 16383 := by
    rw [narrowCompactProgram, added_relabel]
    exact (WEXCredit.narrow_body_credit 0).2
  exact hn.symm.trans hc

private theorem compare_count (a b tree c : Nat) (he : 2*a+b+21*16383 = c)
    (hc : c ≤ 2507944) : 2*a+b+21*tree ≤ 2163901+21*tree := by omega

theorem generic_count_upper (k : Nat) :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2^k-1) ≤
      2163901 + 21 * (2^k-1) := by
  exact compare_count (ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram))
    (literalToffolis (normalizeW (rowAddCode probeRows))) (2^k-1) narrow.credit
    narrow_credit_relation narrow_credit_upper

theorem widthBodyProgram_tBound (k : Nat) (hk : k ≤ 15) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((widthBodyProgram k hk start).instantiate read history).tCount ≤
      7 * (2163901 + 21 * (2 ^ k - 1)) := by
  have hs := widthBodyProgram_credit k hk start
  have ht := WEXCredit.exact_t (widthBodyProgram k hk start) hs.1 read history
  have he := ht.trans (congrArg (fun n : Nat => 7*n) hs.2)
  exact (le_of_eq he).trans (Nat.mul_le_mul_left 7 (generic_count_upper k))

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge ShorECDLP.Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] compile Bridge.translate ECDSAAdd.wires codeRecords Bridge.tmplMeas literalT
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.measurementCount ECDSAAdd.toffoliCount
  Nat.add Straight.instantiate AdaptiveCircuit.run AdaptiveCircuit.tCount literalToffolis
  Straight.gateSlots codeSlots literalSlotSum portTotal

theorem widthAddProgram_source (k : Nat) (hk : k ≤ 15) (start : Nat) :
    ChallengeMigration.straightWires (widthAddProgram k hk start) ⊆ sourceSupport := by
  rw [widthAddProgram,support_castFinish]
  apply compile_support (widthBits k) windowPaths windowRoot (normalizeW (rowAddCode probeRows))
    sourceSupport (start := start)
  · decide +kernel
  · exact (width_bits_subset k hk).trans (by decide +kernel)
  · decide +kernel
  · intro p hp
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
    cases j with
    | literal q =>
      cases he
      rw [ECDSAAdd.Baselines.normalize_wires]
      simp only [rowAddCode,List.mem_append] at hj
      rcases hj with (hj | hj) | hj
      · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hj
        subst q
        intro w hw
        have he : w = 838 := by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw
        subst w
        exact List.mem_toFinset.mpr ((sourceSupport_mem 838).mpr (Or.inl (by decide +kernel)))
      · exact finiteOne_literal_source probeRows q (tight_finite_literal_subset streamLayout probeRows q (finite23_literal_subset streamLayout probeRows q hj))
      · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hj
        subst q
        intro w hw
        have he : w = 838 := by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw
        subst w
        exact List.mem_toFinset.mpr ((sourceSupport_mem 838).mpr (Or.inl (by decide +kernel)))
    | lookup c ports => cases he
  · intro c ports hc
    have h := List.all_eq_true.mp row_sourceLookupOK _ hc
    have h : (∀ q ∈ c, fixedPort q ∨ oldWork q) ∧
        (∀ w ∈ portTargets ports, fixedPort w ∨ oldWork w) := by
      simpa [sourceLookupOK,List.all_eq_true] using h
    exact ⟨fun q hq => (sourceSupport_mem q).mpr (h.1 q hq),
      fun w hw => (sourceSupport_mem w).mpr (h.2 w hw)⟩

theorem widthAddProgram_slots (k : Nat) (hk : k ≤ 15) (start : Nat) :
    (widthAddProgram k hk start).gateSlots = codeSlots (widthBits k) (normalizeW (rowAddCode probeRows)) := by
  rw [widthAddProgram,NaiveChallenge.gateSlots_castFinish]
  apply compile_slots
  exact pair_layouts_of_placed (widthBits k) windowPaths windowRoot _
    (by simpa [widthBits,windowPaths] using hk) (pair_placed_normalize _ _ _ _ (width_placed k hk probeRows))

theorem widthRow_slots_bound (k : Nat) (hk : k = 12 ∨ k = 13) (start : Nat) :
    (widthAddProgram k (by omega) start).gateSlots ≤ 1000000000 := by
  rw [widthAddProgram_slots]
  have bound := codeSlots_bound (widthBits k) (normalizeW (rowAddCode probeRows))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at bound
  have literal := rowAdd_literal_slots_bound
  have ports := rowAdd_portTotal
  have trav : traversals (rowAddCode probeRows) = 21 := by
    simp only [rowAddCode,traversals_append,wLiteral,traversals_finite23,traversals]
  rw [trav] at bound
  have hlen : (widthBits k).length = k := by simp [widthBits]
  rw [hlen] at bound
  rcases hk with rfl | rfl <;> norm_num at bound <;> omega

theorem widthBodyProgram_slots (k : Nat) (hk : k = 12 ∨ k = 13) (start : Nat) :
    (widthBodyProgram k (by omega) start).gateSlots ≤ 1100000000 := by
  rw [widthBodyProgram,NaiveChallenge.gateSlots_castFinish]
  simp only [Straight.gateSlots_append,nProgram_slots,widthAddProgram_slots,prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := sign_slots_bound
  have row := widthRow_slots_bound k hk start
  rw [widthAddProgram_slots] at row
  omega

theorem widthBodyProgram_source (k : Nat) (hk : k ≤ 15) (start : Nat) :
    ChallengeMigration.straightWires (widthBodyProgram k hk start) ⊆ sourceSupport := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ sourceSupport := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ sourceSupport := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  rw [widthBodyProgram,support_castFinish]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,nProgram_source _⟩,widthAddProgram_source k hk _⟩,nProgram_source _⟩,hs _⟩
end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def reducedAddress (k : Nat) (a : Fin 32768) : Fin 32768 :=
  ⟨a.val % 2^k, (Nat.mod_le _ _).trans_lt a.isLt⟩

def ModAliased (k : Nat) (coeffs : Fin 32768 → PointCoeff) : Prop :=
  ∀ a, coeffs a = coeffs (reducedAddress k a)

omit body in
theorem coefficients_aliased (w : Digit) : ModAliased (w.width-1) (windowCoefficients w) := by
  intro a
  unfold windowCoefficients paddedRow reducedAddress
  congr 2
  apply Fin.ext
  simp only [Nat.mod_mod]

structure ModNarrow (body : Single.WindowBody) (k : Nat) where
  records : Nat
  tBound : Nat
  credit : Nat
  program : (start : Nat) → Straight 32768 start (start + records)
  coherent : ∀ coeffs Q, order • Q = 0 → (∀ a, constantPoint Q (coeffs a) ≠ 0) →
    ModAliased k coeffs → ∀ start history,
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (body.update coeffs Q)) (Single.BodyValid body)
  wellFormed : ∀ start, (program start).WellFormed
  slots : ∀ start, (program start).gateSlots ≤ body.slotBound
  wires : ∀ start, straightWires (program start) ⊆ body.support
  tCount : ∀ start read history, ((program start).instantiate read history).tCount ≤ tBound
  zero : ∀ start, residue (program start) = 0
  count_eq : ∀ start, added (program start) = credit

def dualPrograms (n13 : ModNarrow body 12) (n14 : ModNarrow body 13) : Programs body where
  records13 := n13.records
  records14 := n14.records
  cost13 := n13.tBound
  cost14 := n14.tBound
  program := fun w start =>
    if h : w.width = 13 then
      castFinish (by simp [count,h]) (reindexStraight (paddedRow w) (n13.program start))
    else castFinish (by simp [count,h]) (reindexStraight (paddedRow w) (n14.program start))
  coherent := by
    intro Q hQ hn w start history
    have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
      intro a
      have he := window_table_point Q hQ w a.val
      simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
      rw [he]
      exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
    by_cases hw : w.width = 13
    · have ha : ModAliased 12 (windowCoefficients w) := by
        simpa only [hw, Nat.reduceSub] using coefficients_aliased w
      have h := n13.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_pos hw, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
    · have hw14 : w.width = 14 := (width_cases w).resolve_left hw
      have ha : ModAliased 13 (windowCoefficients w) := by
        simpa only [hw14, Nat.reduceSub] using coefficients_aliased w
      have h := n14.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_neg hw, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
  wellFormed := by
    intro w start
    by_cases h : w.width = 13
    · rw [dif_pos h, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n13.wellFormed start)
    · rw [dif_neg h, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n14.wellFormed start)
  slots := by
    intro w start
    by_cases h : w.width = 13
    · rw [dif_pos h, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n13.slots start
    · rw [dif_neg h, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n14.slots start
  wires := by
    intro w start
    by_cases h : w.width = 13
    · rw [dif_pos h, straightWires_castFinish, straightWires_reindex]
      exact n13.wires start
    · rw [dif_neg h, straightWires_castFinish, straightWires_reindex]
      exact n14.wires start
  tCount := by
    intro Q w start history
    by_cases h : w.width = 13
    · rw [dif_pos h, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h, if_true] using n13.tCount start _ history
    · rw [dif_neg h, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h, if_false] using n14.tCount start _ history

theorem dualProgramCredit (n13 : ModNarrow body 12) (n14 : ModNarrow body 13) :
    @ProgramCredit body (dualPrograms n13 n14) n13.credit n14.credit := by
  refine @ProgramCredit.mk body (dualPrograms n13 n14) n13.credit n14.credit ?_ ?_
  · intro w start
    by_cases h : w.width = 13
    · change residue (if h : w.width = 13 then castFinish _ (reindexStraight (paddedRow w) (n13.program start))
        else castFinish _ (reindexStraight (paddedRow w) (n14.program start))) = 0
      rw [dif_pos h, residue_cast, residue_reindex]
      exact n13.zero start
    · change residue (if h : w.width = 13 then castFinish _ (reindexStraight (paddedRow w) (n13.program start))
        else castFinish _ (reindexStraight (paddedRow w) (n14.program start))) = 0
      rw [dif_neg h, residue_cast, residue_reindex]
      exact n14.zero start
  · intro w start
    by_cases h : w.width = 13
    · change added (if h : w.width = 13 then castFinish _ (reindexStraight (paddedRow w) (n13.program start))
        else castFinish _ (reindexStraight (paddedRow w) (n14.program start))) = count n13.credit n14.credit w
      rw [dif_pos h, added_cast, added_reindex, n13.count_eq start]
      simp [count,h]
    · change added (if h : w.width = 13 then castFinish _ (reindexStraight (paddedRow w) (n13.program start))
        else castFinish _ (reindexStraight (paddedRow w) (n14.program start))) = count n13.credit n14.credit w
      rw [dif_neg h, added_cast, added_reindex, n14.count_eq start]
      simp [count,h]


variable [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]







end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge NaiveChallenge ShorECDLP.Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] compactBody compactState compactPerm
  widthBodyProgram widthAddProgram compile Bridge.translate ECDSAAdd.Baselines.normalizeProgram
  ECDSAAdd.toffoliCount literalToffolis normalizeW Nat.add Nat.mul AndGadget.added

def widthCompactProgram (k : Nat) (hk : k ≤ 15) (start : Nat) :
    Straight 32768 start (start + widthBodyRecords k) :=
  relabelStraight compactPerm (widthBodyProgram k hk start)

theorem widthCompactProgram_support (k : Nat) (hk : k ≤ 15) (start : Nat) :
    ChallengeMigration.straightWires (widthCompactProgram k hk start) ⊆ List.range 1634 := by
  rw [widthCompactProgram,straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr (compactPerm_bound v (widthBodyProgram_source k hk start hv))

theorem widthCompactProgram_slots (k : Nat) (hk : k = 12 ∨ k = 13) (start : Nat) :
    (widthCompactProgram k (by omega) start).gateSlots ≤ 1100000000 := by
  rw [widthCompactProgram,relabelStraight_slots]
  exact widthBodyProgram_slots k hk start

theorem widthCompactProgram_t (k : Nat) (hk : k ≤ 15) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((widthCompactProgram k hk start).instantiate read history).tCount ≤
      7 * (2163901 + 21 * (2 ^ k - 1)) := by
  rw [widthCompactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]
  exact widthBodyProgram_tBound k hk start read history

theorem widthCompactProgram_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : Point) (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WidthAliased k coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((widthCompactProgram k hk start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := (widthBodyProgram_coherent k hk coeffs Q hQ hn halias start history).relabel compactPerm
  have hr : CoherentlyImplementsOn
      (((widthBodyProgram k hk start).instantiate (readConstant coeffs Q) history).relabel compactPerm)
      ((relabelState compactPerm).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState compactPerm.symm)))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,hc,hm⟩ := h
    refine ⟨cs,hc.imp (fun _ _ hb s hs => hb s hs.1),hm⟩
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
    (by intro s _; simp [compactState,compactPull,LinearMap.comp_apply,relabelState,ket])
  rw [widthCompactProgram,relabelStraight_instantiate]
  exact he

private theorem residue_relabel {n s e : Nat} (p : Straight n s e) (f : Wire ≃ Wire) :
    residue (relabelStraight f p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [relabelStraight,relabelTemplateGate,Gate.relabel,residue,primitivePhaseCost]
    | whenBit r v g => cases g <;> simp_all [relabelStraight,relabelTemplateGate,Gate.relabel,residue,tCost]
  | recordGate i v g p ih => cases g <;> simp_all [relabelStraight,Gate.relabel,residue,tCost]
  | measure => simp_all [relabelStraight,residue]

theorem widthCompactProgram_credit (k : Nat) (hk : k ≤ 15) (start : Nat) :
    WEXCredit.ProgramCredit (widthCompactProgram k hk start)
      (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
        literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2 ^ k - 1)) := by
  constructor
  · rw [widthCompactProgram,residue_relabel]
    exact (widthBodyProgram_credit k hk start).1
  · rw [widthCompactProgram,added_relabel]
    exact (widthBodyProgram_credit k hk start).2

def widthNarrow (k : Nat) (hk : k = 12 ∨ k = 13) : ModNarrow compactBody k where
  records := widthBodyRecords k
  tBound := 7 * (2163901 + 21 * (2 ^ k - 1))
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
    literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2 ^ k - 1)
  program := widthCompactProgram k (by omega)
  coherent := by
    intro coeffs Q hQ hn halias start history
    have ha : WidthAliased k coeffs := by simpa only [WidthAliased, ModAliased, reducedAddress] using halias
    have h := widthCompactProgram_coherent k (by omega) coeffs Q hQ hn ha start history
    simpa only [Single.BodyValid, compactBody] using h
  wellFormed := by
    intro start
    rw [widthCompactProgram]
    exact (relabelStraight_wellFormed compactPerm (widthBodyProgram k (by omega) start)).mpr
      (widthBodyProgram_wellFormed k (by omega) start)
  slots := by
    intro start
    have h := widthCompactProgram_slots k hk start
    simpa only [compactBody] using h
  wires := by
    intro start
    have h := widthCompactProgram_support k (by omega) start
    simpa only [compactBody] using h
  tCount := widthCompactProgram_t k (by omega)
  zero := fun start => (widthCompactProgram_credit k (by omega) start).1
  count_eq := fun start => (widthCompactProgram_credit k (by omega) start).2

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.Schedule33.MatchedFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] WEX.widthNarrow WEX.widthCompactProgram WEX.widthBodyProgram
  WEX.compile WEX.normalizeW ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount WEX.literalToffolis
  Nat.add Nat.mul AndGadget.added

def narrow12 : ModNarrow WEX.compactBody 12 := WEX.widthNarrow 12 (Or.inl rfl)
def narrow13 : ModNarrow WEX.compactBody 13 := WEX.widthNarrow 13 (Or.inr rfl)

attribute [local irreducible] narrow12 narrow13








local instance bodyInstance : Single.WindowBody := WEX.compactBody
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEX.compactBody
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
local instance programInstance : Programs bodyInstance := dualPrograms narrow12 narrow13


end
end ShorECDLP.Entrant.Schedule33.MatchedFinal

section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
namespace ShorECDLP.Entrant.ScheduleFirst18
open Classical Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def bits : List Wire := List.range' 855 16 ++ [537, 538]
def paths : List Wire := List.range' 519 18

def ops : List (LookupOp 262144) :=
  unaryLookupOps (fun l q => pointLeaf ⟨l%262144,Nat.mod_lt _ (by decide)⟩ q)
    (tableAddressTree bits 0 1) 836 paths

theorem ops_measurements : lookupMeasurements ops = 262143 := by
  rw [ops,unaryLookupOps_measurements _ _ _ _
    (tableAddressTree_layout _ _ _ _ _ (by decide) (by decide))]
  have h := tableAddressTree_nodes bits 0 1
  change (tableAddressTree bits 0 1).internalNodes+1 = 262144 at h
  omega

def program (start : Nat) : Straight 262144 start (start+262143) :=
  castFinish (by rw [ops_measurements]) (lookupProgram 262144 ops start)

noncomputable def tablePoint (coeffs : Fin 262144 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a%262144,Nat.mod_lt _ (by decide)⟩)

noncomputable def source (table : Nat → Point) : AdaptiveCircuit :=
  directPointLookup table bits paths 836

theorem ops_circuit (coeffs : Fin 262144 → PointCoeff) (Q : Point) :
    lookupCircuit (readConstant coeffs Q) ops = source (tablePoint coeffs Q) := by
  rw [ops,unaryLookupOps_circuit]
  unfold source directPointLookup tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  rw [pointLeaf_instantiate]
  rfl

theorem program_run (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).run =
      (source (tablePoint coeffs Q)).run := by
  rw [program,castFinish_instantiate,lookupProgram_run,ops_circuit]

theorem source_coherent (table : Nat → Point) :
    CoherentlyImplementsOn (source table)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (table (tableAddressValue bits s)) s))
      (DirectPointLookupValid paths 836) := by
  apply directPointLookup_coherent table bits paths 836 (by decide) (by decide)
  apply List.disjoint_left.mpr
  intro w hw hp
  simp only [bits,paths,List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hp
  dsimp only [Wire] at *
  omega

theorem program_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q (tableAddressValue bits s)) s))
      (DirectPointLookupValid paths 836) := by
  unfold CoherentlyImplementsOn
  rw [program_run]
  exact source_coherent _

theorem source_tCount (table : Nat → Point) : (source table).tCount = 1835001 := by
  unfold source
  rw [directPointLookup_tCount _ _ _ _ (by decide) (by decide)]
  rfl

theorem program_tCount (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).tCount = 1835001 := by
  rw [program,castFinish_instantiate,lookupProgram_tCount,ops_circuit,source_tCount]

theorem ops_physical : ∀ op ∈ ops, op.Physical := by
  apply unaryLookupOps_physical
  · exact tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)
  · intro label control hc g hg
    simp only [pointLeaf,lookupLeafGates,List.mem_map] at hg
    obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
    have ht := (List.of_mem_zip hm).2
    change control ≠ target
    have hn : ∀ c ∈ 836::paths, c ∉ pointLogicalWires := by
      intro c hc ht
      simp only [paths,List.mem_cons,List.mem_range'_1] at hc
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_range'_1,List.mem_singleton] at ht
      dsimp only [Wire] at *
      omega
    exact fun he => hn control hc (he ▸ ht)

theorem program_wellFormed (start : Nat) : (program start).WellFormed := by
  unfold program
  rw [castFinish_wellFormed]
  exact lookupProgram_wellFormed _ ops_physical _

theorem program_slots (start : Nat) : (program start).gateSlots ≤ 1000000000 := by
  have h := unaryLookupOps_slots_le
    (fun l q => pointLeaf ⟨l%262144,Nat.mod_lt _ (by decide)⟩ q)
    513 (fun _ q => pointLeaf_slots _ q) (tableAddressTree bits 0 1) 836 paths
  have hn := tableAddressTree_nodes bits 0 1
  change (tableAddressTree bits 0 1).internalNodes+1 = 262144 at hn
  simpa only [program,castFinish_gateSlots,lookupProgram_slots,ops] using
    (show lookupSlots (unaryLookupOps (fun l q => pointLeaf ⟨l%262144,Nat.mod_lt _ (by decide)⟩ q)
      (tableAddressTree bits 0 1) 836 paths) ≤ 1000000000 by omega)


def support : List Wire := 836 :: bits ++ paths ++ pointLogicalWires

theorem program_support (start : Nat) : straightWires (program start) ⊆ support := by
  have hl : ∀ op ∈ ops, lookupOpWires op ⊆ support := by
    apply unaryLookupOps_support
    · simp [support]
    · intro w hw
      simp [support,hw]
    · intro w hw
      have hb := (tableAddressTree_mem_index bits 0 1 w).mp hw
      simp [support,hb]
    · intro label q hq
      apply lookupLeafGates_support _ _ _ hq
      intro port hp
      have ht := (List.of_mem_zip hp).2
      simp [support,ht]
  simp only [program,straightWires_castFinish,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact hl op hop hw

end ShorECDLP.Entrant.ScheduleFirst18


set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ShorECDLP.Entrant.ScheduleFirst18
open Classical Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration

def Input (s : BasisState) : Prop := s 836=true ∧ ∀ v,v≠836 → v∉bits → s v=false

theorem input_of_strong (s : BasisState) (hs : FirstWindowInput s) : Input s := by
  refine ⟨hs.1,?_⟩
  intro v hv ha
  apply hs.2 v hv
  intro hh
  apply ha
  simp only [streamAddress] at hh
  exact List.mem_append_left _ hh

theorem input_lookup (s : BasisState) (hs : Input s) : DirectPointLookupValid paths 836 s := by
  refine ⟨?_,?_,hs.1⟩
  · intro v hv
    have mem : 519≤v ∧ v<537 := by simpa [paths,List.mem_range'_1] using hv
    apply hs.2 v (by dsimp only [Wire] at *; omega)
    simp only [bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · intro v hv
    have mem : 263≤v ∧ v<519 ∨ 580≤v ∧ v<836 ∨ v=838 := by
      simpa [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_range'_1,or_assoc] using hv
    apply hs.2 v (by dsimp only [Wire] at *; omega)
    simp only [bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1]
    dsimp only [Wire] at *
    omega

theorem input_update (s : BasisState) (hs : Input s) (w : Wire) (hw : w∈bits) (b : Bool) :
    Input (s[w↦b]) := by
  have ne : (836:Wire)≠w := by
    simp only [bits,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at hw
    dsimp only [Wire] at *
    omega
  refine ⟨by simpa only [upd,if_neg ne] using hs.1,?_⟩
  intro v hv ha
  have nvw : v≠w := by intro e; exact ha (e ▸ hw)
  simpa only [upd,if_neg nvw] using hs.2 v hv ha


private theorem support_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ+φ) := by
  intro s hs
  by_cases h : ψ s=0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h
private theorem support_smul {V : BasisState → Prop} {ψ : State} (c : ℂ)
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])

private theorem support_linear_FirstValidity (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn W (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn W (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz,hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u=s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,he,map_smul]
    exact support_add (support_smul c (hL s hvs)) (ih hvψ)

theorem input_H (w : Wire) (hw : w∈bits) (ψ : State) (hψ : SupportedOn Input ψ) :
    SupportedOn Input (applyGate (.H w) ψ) := by
  apply support_linear_FirstValidity Input Input (applyGate (.H w)) ?_ ψ hψ
  intro s hs
  rw [applyGate_ket]
  exact support_add
    (support_smul _ (supportedOn_ket _ _ (input_update s hs w hw false)))
    (support_smul _ (supportedOn_ket _ _ (input_update s hs w hw true)))

theorem input_prepare (ws : List Wire) (hws : ∀ w∈ws,w∈bits) (ψ : State) (hψ : SupportedOn Input ψ) :
    SupportedOn Input (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons w ws ih =>
    exact ih (fun v hv=>hws v (List.mem_cons_of_mem w hv)) _
      (input_H w (hws w (by simp)) ψ hψ)
end ShorECDLP.Entrant.ScheduleFirst18


namespace ShorECDLP.Entrant.ScheduleFirst18
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem program_residue (start : Nat) : residue (program start) = 0 := by
  rw [program, residue_cast, residue_lookup, ops]
  apply WEXCredit.residue_unary
  intro label root
  unfold pointLeaf
  generalize (pointRefs _).zip pointLogicalWires = ports
  unfold lookupLeafGates
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [templateResidue, tCost] using ih

theorem program_credit (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) : added (program start) = 262143 := by
  have h := exact_t (program start) (program_residue start) (readConstant coeffs Q) history
  have ht := program_tCount coeffs Q start history
  omega
end ShorECDLP.Entrant.ScheduleFirst18


namespace ShorECDLP.Entrant.Single
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes

theorem first18_nodup : ScheduleFirst18.bits.Nodup := by decide +kernel

theorem first18_not_point : ∀ v ∈ ScheduleFirst18.bits, v ∉ pointLogicalWires := by decide +kernel

theorem first18_clean (s : BasisState) (hs : FirstWindowInput s)
    (hz : Clean streamAddress s) : Clean ScheduleFirst18.bits s := by
  intro v hv
  simp only [ScheduleFirst18.bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with hv | rfl | rfl
  · exact hz v hv
  · exact hs.2 537 (by decide) (by decide +kernel)
  · exact hs.2 538 (by decide) (by decide +kernel)

theorem first18_assigned_digit (s : BasisState) (input : List Bool)
    (hi : input.length = ScheduleFirst18.bits.length) :
    tableAddressValue ScheduleFirst18.bits (phaseWordState ScheduleFirst18.bits input s) = boolWordToNat input := by
  have he (ws : List Wire) (t : BasisState) :
      tableAddressValue ws t = boolWordToNat (wireValues ws t) := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      change (t w).toNat + 2 * tableAddressValue ws t =
        (t w).toNat + 2 * boolWordToNat (wireValues ws t)
      rw [ih]
  rw [he,phaseWordState_word _ first18_nodup input hi s]


end
end ShorECDLP.Entrant.Single


namespace ShorECDLP.Entrant.ScheduleFirst18
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def window {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨bits.reverse, 262143, fun start => reindexStraight rows (program start)⟩

end
end ShorECDLP.Entrant.ScheduleFirst18


namespace ShorECDLP.Entrant.ScheduleFirst18
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single AndGadget WEXCredit
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] program

theorem support_in_reset : support ⊆ resetWires := by decide +kernel

theorem window_wellFormed {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((window rows).program start).WellFormed := by
  unfold window
  exact (reindexStraight_wellFormed rows (program start)).mpr (program_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((window rows).program start).gateSlots ≤ 1000000000 := by
  unfold window
  rw [reindexStraight_gateSlots]
  exact program_slots start

theorem window_support {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    straightWires ((window rows).program start) ⊆ resetWires := by
  unfold window
  rw [straightWires_reindex]
  exact (program_support start).trans support_in_reset

theorem window_t {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    (((window rows).program start).instantiate (readConstant coeffs Q) history).tCount = 1835001 := by
  unfold window
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact program_tCount (fun a => coeffs (rows a)) Q start history


theorem window_credit {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    added ((window rows).program start) = 262143 := by
  unfold window
  rw [added_reindex]
  exact program_credit (fun a => coeffs (rows a)) Q start history
end
end ShorECDLP.Entrant.ScheduleFirst18


namespace ShorECDLP.Entrant.ScheduleFirst18
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def update (init : Point → Nat → Point) (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (init Q (tableAddressValue bits s)) s

def windowGeneric {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨bits.reverse, 262143, fun start => reindexStraight rows (program start)⟩

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 262144,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    WindowLaw coeffs (windowGeneric rows) (update init) Input := by
  intro Q hQ hn start history
  have h := program_coherent (fun a => coeffs (rows a)) Q start history
  have hvalid : CoherentlyImplementsOn
      ((program start).instantiate (readConstant (fun a => coeffs (rows a)) Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite
        (tablePoint (fun a => coeffs (rows a)) Q (tableAddressValue bits s)) s)) Input := by
    obtain ⟨cs, halign, hmass⟩ := h
    exact ⟨cs, halign.imp (fun _ _ hb s hs => hb s (input_lookup s hs)), hmass⟩
  have hupdate : (fun s => pointWrite
      (tablePoint (fun a => coeffs (rows a)) Q (tableAddressValue bits s)) s) = update init Q := by
    funext s
    unfold tablePoint update
    have hbound : tableAddressValue bits s < 262144 := by
      have hb := tableAddressValue_lt bits s
      have hlen : bits.length = 18 := by decide +kernel
      simpa only [hlen] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid
end
end ShorECDLP.Entrant.ScheduleFirst18


namespace ShorECDLP.Entrant.Single
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes

theorem first18_window_point_sum_generic (init : Point → Nat → Point) (Q : Point) (prior output : List Bool)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse ScheduleFirst18.bits.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (ScheduleFirst18.update init Q)
        (Quantum.run (ScheduleFirst18.bits.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 18) •
        ((fourierOutcomes 18).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (init Q (boolWordToNat input)) s))).sum := by
  have hlen : ScheduleFirst18.bits.length = 18 := by decide +kernel
  rw [window_branch_uniform .inverse ScheduleFirst18.bits first18_nodup
    (ScheduleFirst18.update init Q) prior output s (first18_clean s hs hz) (by
      intro input hi
      have he : ScheduleFirst18.bits.map (ScheduleFirst18.update init Q (phaseWordState ScheduleFirst18.bits input s)) =
          ScheduleFirst18.bits.map (phaseWordState ScheduleFirst18.bits input s) := by
        apply List.map_congr_left
        intro v hv
        exact pointWrite_frame _ _ v (first18_not_point v hv)
      rw [he]
      exact phaseWordState_word _ first18_nodup input
        ((fourierOutcomes_mem _ _).mp hi) s), hlen]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 18) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  unfold ScheduleFirst18.update
  rw [first18_assigned_digit s input (by simpa only [hlen] using (fourierOutcomes_mem _ _).mp hi),
    clear_assigned_point _ input s (first18_clean s hs hz) first18_not_point]
end
end ShorECDLP.Entrant.Single


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000




inductive Digit where
  | left15 (index : Fin 9)
  | left14 (index : Fin 8)
  | right15 (index : Fin 12)
  | right14 (index : Fin 2)

def Digit.width : Digit → Nat
  | .left15 _ | .right15 _ => 15
  | .left14 _ | .right14 _ => 14

def Digit.exponent : Digit → Nat
  | .left15 j => 232 - 15 * j.val
  | .left14 j => 98 - 14 * j.val
  | .right15 j => 193 - 15 * j.val
  | .right14 j => 14 - 14 * j.val

def firstRow (a : Fin 262144) : Fin 688128 := ⟨a.val, by omega⟩

def row : (w : Digit) → Fin (2^(w.width-1)) → Fin 688128
  | .left15 j, a => ⟨262144 + j.val*16384 + a.val, by
    have h : a.val < 16384 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .left14 j, a => ⟨409600 + j.val*8192 + a.val, by
    have h : a.val < 8192 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .right15 j, a => ⟨475136 + j.val*16384 + a.val, by
    have h : a.val < 16384 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .right14 j, a => ⟨671744 + j.val*8192 + a.val, by
    have h : a.val < 8192 := by simpa only [Digit.width] using a.isLt
    omega⟩

theorem width_cases (w : Digit) : w.width = 14 ∨ w.width = 15 := by
  cases w <;> simp [Digit.width]

def leftDigits : List Digit := List.ofFn (fun j : Fin 9 => .left15 j) ++
  List.ofFn (fun j : Fin 8 => .left14 j)
def rightDigits : List Digit := List.ofFn (fun j : Fin 12 => .right15 j) ++
  List.ofFn (fun j : Fin 2 => .right14 j)


def leftOffset : Nat := (leftDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum
def rightOffset : Nat := (rightDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum

def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients (v * 2^247 + leftOffset) rightOffset

def signedCoefficients (w : Digit) (a : Nat) : PointCoeff :=
  match w with
  | .left15 _ | .left14 _ => coefficients (Single.oddScalar w.exponent a) 0
  | .right15 _ | .right14 _ => coefficients 0 (Single.oddScalar w.exponent a)

def coefficientAt (i : Fin 688128) : PointCoeff :=
  if i.val < 262144 then initialCoefficients i.val
  else if i.val < 409600 then
    coefficients (Single.oddScalar (232 - 15 * ((i.val - 262144) / 16384)) ((i.val - 262144) % 16384)) 0
  else if i.val < 475136 then
    coefficients (Single.oddScalar (98 - 14 * ((i.val - 409600) / 8192)) ((i.val - 409600) % 8192)) 0
  else if i.val < 671744 then
    coefficients 0 (Single.oddScalar (193 - 15 * ((i.val - 475136) / 16384)) ((i.val - 475136) % 16384))
  else coefficients 0 (Single.oddScalar (14 - 14 * ((i.val - 671744) / 8192)) ((i.val - 671744) % 8192))


theorem coefficientAt_row (w : Digit) (a : Fin (2^(w.width-1))) :
    coefficientAt (row w a) = signedCoefficients w a.val := by
  cases w with
  | left15 j =>
    have ha : a.val < 16384 := by
      simpa only [Digit.width] using a.isLt
    have he : (row (.left15 j) a).val < 409600 := by simp only [row]; omega
    have hbase : ¬ (row (.left15 j) a).val < 262144 := by simp only [row]; omega
    have hj : ((row (.left15 j) a).val - 262144) / 16384 = j.val := by simp only [row]; omega
    have hh : ((row (.left15 j) a).val - 262144) % 16384 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, he, hj, hh, signedCoefficients, Digit.exponent]
  | left14 j =>
    have ha : a.val < 8192 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.left14 j) a).val < 262144 := by simp only [row]; omega
    have he : (row (.left14 j) a).val < 475136 := by simp only [row]; omega
    have hbase : ¬ (row (.left14 j) a).val < 409600 := by simp only [row]; omega
    have hj : ((row (.left14 j) a).val - 409600) / 8192 = j.val := by simp only [row]; omega
    have hh : ((row (.left14 j) a).val - 409600) % 8192 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, he, hj, hh, signedCoefficients, Digit.exponent]
  | right15 j =>
    have ha : a.val < 16384 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.right15 j) a).val < 262144 := by simp only [row]; omega
    have hn1 : ¬ (row (.right15 j) a).val < 409600 := by simp only [row]; omega
    have he : (row (.right15 j) a).val < 671744 := by simp only [row]; omega
    have hbase : ¬ (row (.right15 j) a).val < 475136 := by simp only [row]; omega
    have hj : ((row (.right15 j) a).val - 475136) / 16384 = j.val := by simp only [row]; omega
    have hh : ((row (.right15 j) a).val - 475136) % 16384 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, hn1, he, hj, hh, signedCoefficients, Digit.exponent]
  | right14 j =>
    have ha : a.val < 8192 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.right14 j) a).val < 262144 := by simp only [row]; omega
    have hn1 : ¬ (row (.right14 j) a).val < 409600 := by simp only [row]; omega
    have hn2 : ¬ (row (.right14 j) a).val < 475136 := by simp only [row]; omega
    have hbase : ¬ (row (.right14 j) a).val < 671744 := by simp only [row]; omega
    have hj : ((row (.right14 j) a).val - 671744) / 8192 = j.val := by simp only [row]; omega
    have hh : ((row (.right14 j) a).val - 671744) % 8192 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, hn1, hn2, hj, hh, signedCoefficients, Digit.exponent]

end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000



def firstWindow : Single.Window 688128 := ScheduleFirst18.windowGeneric firstRow


end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def Digit.base (Q : Point) : Digit → Point
  | .left15 _ | .left14 _ => G
  | .right15 _ | .right14 _ => Q

noncomputable def positivePoint (Q : Point) (w : Digit) (a : Nat) : Point :=
  Single.oddScalar w.exponent a • w.base Q

theorem signedCoefficients_point (Q : Point) (hQ : order • Q = 0)
    (w : Digit) (a : Nat) :
    constantPoint Q (signedCoefficients w a) = positivePoint Q w a := by
  cases w <;> simp [signedCoefficients, coefficients_point _ _ Q hQ,
    positivePoint, Digit.base]

theorem positivePoint_ne_zero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (address : Nat) (ha : address < 2^(w.width-1)) :
    positivePoint Q w address ≠ 0 := by
  let P := w.base Q
  have hp : P ≠ 0 := by
    cases w with
    | left15 _ | left14 _ => exact G_ne_zero
    | right15 _ | right14 _ => exact hn
  have hr : order • P = 0 := by
    cases w with
    | left15 _ | left14 _ => exact generator_nsmul_eq_zero
    | right15 _ | right14 _ => exact hQ
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf P = order := addOrderOf_eq_prime hr hp
  have hw : 2^(w.width-1) ≤ 32768 := by cases w <;> norm_num [Digit.width]
  have hl : 65535 < order := by norm_num [order]
  have hs : 0 < 2*address+1 ∧ 2*address+1 < order := by omega
  have hh : 0 < Single.halfOrder ∧ Single.halfOrder < order := by
    dsimp [Single.halfOrder]; omega
  have hodd : ¬ order ∣ 2*address+1 :=
    fun h => (Nat.le_of_dvd hs.1 h).not_gt hs.2
  have hhalf : ¬ order ∣ Single.halfOrder := fun h => (Nat.le_of_dvd hh.1 h).not_gt hh.2
  have htwo : ¬ order ∣ 2 := fun h => (Nat.le_of_dvd (by decide : 0 < 2) h).not_gt (by omega)
  intro hz
  have he : ((2*address+1)*2^w.exponent*Single.halfOrder) • P = 0 := by
    simpa only [positivePoint, Single.oddScalar] using hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  rw [ho] at hd
  rcases order_prime.dvd_mul.mp hd with hd | hd
  · rcases order_prime.dvd_mul.mp hd with hd | hd
    · exact hodd hd
    · exact htwo (order_prime.dvd_of_dvd_pow hd)
  · exact hhalf hd





open Quantum ShorECDLP.Paper2607_13816







def bank (width : Nat) : List Wire := List.range' 855 (width-1) ++ [870]













def paddedRow (w : Digit) (a : Fin 32768) : Fin 688128 :=
  row w ⟨a.val % 2^(w.width-1), Nat.mod_lt _ (pow_pos (by decide) _)⟩

noncomputable def windowCoefficients (w : Digit) : Fin 32768 → PointCoeff :=
  fun a => coefficientAt (paddedRow w a)

theorem window_table_point (Q : Point) (hQ : order • Q = 0) (w : Digit) (a : Nat) :
    constantPoint Q (windowCoefficients w ⟨a % 32768, Nat.mod_lt _ (by decide)⟩) =
      positivePoint Q w (a % 2^(w.width-1)) := by
  unfold windowCoefficients paddedRow
  rw [coefficientAt_row, signedCoefficients_point Q hQ]
  have ha : a % 32768 % 2^(w.width-1) = a % 2^(w.width-1) := by
    cases w <;> norm_num [Digit.width]
  simp only [ha]






end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
variable [b : Single.WindowBody]

def WindowValid (w : Digit) (s : BasisState) : Prop :=
  Single.BodyValid b s ∧ s 869 = false ∧ (w.width = 14 → s 868 = false)

def signedWindow (w : Digit) : Single.Window 688128 :=
  ⟨(bank w.width).reverse, b.records,
    fun start => reindexStraight (paddedRow w) (b.program start)⟩


noncomputable def windowUpdate (Q : Point) (w : Digit) : BasisState → BasisState :=
  b.update (windowCoefficients w) Q











end

end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000













section
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]


end

end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
variable [b : Single.WindowBody]
noncomputable section
attribute [local irreducible] fourierOutcomes











end
end

end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes












end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000




end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000


end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody]
noncomputable section
attribute [local irreducible] resetProgram

def leftWindows : List (Single.Window 688128) := firstWindow :: leftDigits.map signedWindow

def rightWindows : List (Single.Window 688128) := rightDigits.map signedWindow

def leftMetadata : List (Nat × Nat) :=
  (262143, 18) :: List.replicate 9 (body.records, 15) ++ List.replicate 8 (body.records, 14)

def rightMetadata : List (Nat × Nat) :=
  List.replicate 12 (body.records, 15) ++ List.replicate 2 (body.records, 14)

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftDigits, signedWindow,
    Digit.width, bank, firstWindow, ScheduleFirst18.windowGeneric, ScheduleFirst18.bits, leftMetadata, List.ofFn_succ, List.replicate]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightDigits, signedWindow,
    Digit.width, bank, rightMetadata, List.ofFn_succ, List.replicate]

theorem left_record_count : recordCount leftMetadata = 262143 + 17 * body.records + 265 := by
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_record_count : recordCount rightMetadata = 14 * body.records + 208 := by
  simp [rightMetadata, recordCount, List.replicate]
  omega

variable [ledger : Single.ProducerResources body]

theorem left_count : axisCount leftWindows = 262143 + 17 * body.records + 265 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 14 * body.records + 208 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

def resetBody (start : Nat) : Straight 688128 start (start + body.reset.length) :=
  resetProgram 688128 start body.reset


def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + body.reset.length

theorem trialCount_eq : trialCount = 262143 + 31 * body.records + 473 + body.reset.length := by
  rw [trialCount, left_count, right_count]
  omega

def trial (start : Nat) : Straight 688128 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

def program : Straight 688128 0 (262143 + 31 * body.records + 473 + body.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end
end


section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 265 := by
  rw [positions_length]
  simp [leftMetadata, List.replicate]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length]
  simp [rightMetadata, List.replicate]

def trialPositions : TrialPositions NeighborReadout.params265 where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params265] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (262143 + 17 * body.records + 265)).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params265] using right_positions_length (262143 + 17 * body.records + 265)⟩


theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (262143 + 17 * body.records + 265) ≤ i ∧ i < 262143 + 31 * body.records + 473 := by
  have h := positions_bounds rightMetadata (262143 + 17 * body.records + 265) i
    (show i ∈ positions rightMetadata (262143 + 17 * body.records + 265) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

def finePositions : List (Fin (262143 + 31 * body.records + 473 + body.reset.length)) :=
  trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(right_position_bound i.val i.property).2.trans_le (by omega)⟩

theorem finePositions_length : finePositions.length = 208 := by
  simp [finePositions, NeighborReadout.params265]

def fineBits : Vector (Fin (262143 + 31 * body.records + 473 + body.reset.length)) 208 :=
  Vector.ofFn fun i=> finePositions[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout : Straight 688128 (262143 + 31 * body.records + 473 + body.reset.length)
    (262143 + 31 * body.records + 473 + body.reset.length + 34114) :=
  castFinish (by omega) (NeighborReadout.neighborSuffix 688128
    (262143 + 31 * body.records + 473 + body.reset.length) 208 fineBits)

def fullProgram : Straight 688128 0 (262143 + 31 * body.records + 473 + body.reset.length + 34114) :=
  program.append readout

def positionsFor (ps : Vector Nat 208) : TrialPositions NeighborReadout.params265 where
  left := trialPositions.left
  right := ps

def layout : DecodeLayout := ⟨.wrappedShift, NeighborReadout.params265,
  (NeighborReadout.rightWords fineBits).map positionsFor, by
    simp only [List.length_map, NeighborReadout.rightWords_length]; decide⟩



end
end

end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] Single.axis resetProgram











end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution RoundedReadout
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000






end
end ShorECDLP.Entrant.Schedule31Eighteen265


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes

def count (c14 c15 : Nat) (w : Digit) : Nat := if w.width = 14 then c14 else c15

class Programs (body : Single.WindowBody) where
  records14 : Nat
  records15 : Nat
  cost14 : Nat
  cost15 : Nat
  program : (w : Digit) → (start : Nat) → Straight 688128 start
    (start + count records14 records15 w)
  coherent : ∀ Q, order • Q = 0 → Q ≠ 0 → ∀ w start history,
    CoherentlyImplementsOn ((program w start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w)
  wellFormed : ∀ w start, (program w start).WellFormed
  slots : ∀ w start, (program w start).gateSlots ≤ body.slotBound
  wires : ∀ w start, straightWires (program w start) ⊆ body.support
  tCount : ∀ Q w start history,
    ((program w start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count cost14 cost15 w

variable [impl : Programs b]

def signedWindow (w : Digit) : Single.Window 688128 :=
  ⟨(bank w.width).reverse, count impl.records14 impl.records15 w, impl.program w⟩








end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000




end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000


end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body]
noncomputable section
attribute [local irreducible] resetProgram

def leftWindows : List (Single.Window 688128) := firstWindow :: leftDigits.map signedWindow

def rightWindows : List (Single.Window 688128) := rightDigits.map signedWindow

def leftMetadata : List (Nat × Nat) :=
  (262143, 18) :: List.replicate 9 (impl.records15, 15) ++ List.replicate 8 (impl.records14, 14)

def rightMetadata : List (Nat × Nat) :=
  List.replicate 12 (impl.records15, 15) ++ List.replicate 2 (impl.records14, 14)

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftDigits, signedWindow,
    Digit.width, count, bank, firstWindow, ScheduleFirst18.windowGeneric, ScheduleFirst18.bits, leftMetadata, List.ofFn_succ, List.replicate]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightDigits, signedWindow,
    Digit.width, count, bank, rightMetadata, List.ofFn_succ, List.replicate]

theorem left_record_count : recordCount leftMetadata = 262143 + 9 * impl.records15 + 8 * impl.records14 + 265 := by
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_record_count : recordCount rightMetadata = 12 * impl.records15 + 2 * impl.records14 + 208 := by
  simp [rightMetadata, recordCount, List.replicate]
  omega

variable [ledger : Single.ProducerResources body]

theorem left_count : axisCount leftWindows = 262143 + 9 * impl.records15 + 8 * impl.records14 + 265 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 12 * impl.records15 + 2 * impl.records14 + 208 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

def resetBody (start : Nat) : Straight 688128 start (start + body.reset.length) :=
  resetProgram 688128 start body.reset


def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + body.reset.length

theorem trialCount_eq : trialCount = 262143 + 21 * impl.records15 + 10 * impl.records14 + 473 + body.reset.length := by
  rw [trialCount, left_count, right_count]
  omega

def trial (start : Nat) : Straight 688128 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

def program : Straight 688128 0 (262143 + 21 * impl.records15 + 10 * impl.records14 + 473 + body.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end
end


section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 265 := by
  rw [positions_length]
  simp [leftMetadata, List.replicate]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length]
  simp [rightMetadata, List.replicate]

def trialPositions : TrialPositions NeighborReadout.params265 where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params265] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (262143 + 9 * impl.records15 + 8 * impl.records14 + 265)).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params265] using right_positions_length (262143 + 9 * impl.records15 + 8 * impl.records14 + 265)⟩


theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (262143 + 9 * impl.records15 + 8 * impl.records14 + 265) ≤ i ∧ i < 262143 + 21 * impl.records15 + 10 * impl.records14 + 473 := by
  have h := positions_bounds rightMetadata (262143 + 9 * impl.records15 + 8 * impl.records14 + 265) i
    (show i ∈ positions rightMetadata (262143 + 9 * impl.records15 + 8 * impl.records14 + 265) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

def finePositions : List (Fin (262143 + 21 * impl.records15 + 10 * impl.records14 + 473 + body.reset.length)) :=
  trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(right_position_bound i.val i.property).2.trans_le (by omega)⟩

theorem finePositions_length : finePositions.length = 208 := by
  simp [finePositions, NeighborReadout.params265]

def fineBits : Vector (Fin (262143 + 21 * impl.records15 + 10 * impl.records14 + 473 + body.reset.length)) 208 :=
  Vector.ofFn fun i=> finePositions[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout : Straight 688128 (262143 + 21 * impl.records15 + 10 * impl.records14 + 473 + body.reset.length)
    (262143 + 21 * impl.records15 + 10 * impl.records14 + 473 + body.reset.length + 34114) :=
  castFinish (by omega) (NeighborReadout.neighborSuffix 688128
    (262143 + 21 * impl.records15 + 10 * impl.records14 + 473 + body.reset.length) 208 fineBits)

def fullProgram : Straight 688128 0 (262143 + 21 * impl.records15 + 10 * impl.records14 + 473 + body.reset.length + 34114) :=
  program.append readout

def positionsFor (ps : Vector Nat 208) : TrialPositions NeighborReadout.params265 where
  left := trialPositions.left
  right := ps

def layout : DecodeLayout := ⟨.wrappedShift, NeighborReadout.params265,
  (NeighborReadout.rightWords fineBits).map positionsFor, by
    simp only [List.length_map, NeighborReadout.rightWords_length]; decide⟩



end
end

end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] Single.axis resetProgram











end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution RoundedReadout
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000






end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit body in
theorem coefficients_aliased (w : Digit) : ModAliased (w.width-1) (windowCoefficients w) := by
  intro a
  unfold windowCoefficients paddedRow reducedAddress
  congr 2
  apply Fin.ext
  simp only [Nat.mod_mod]

omit body in
theorem coefficients_half_aliased (w : Digit) : HalfAliased (windowCoefficients w) := by
  intro a
  unfold windowCoefficients paddedRow
  congr 2
  apply Fin.ext
  cases w <;> norm_num [Digit.width]

def dualPrograms (n14 : ModNarrow body 13) (n15 : UniformNarrow body) : Programs body where
  records14 := n14.records
  records15 := n15.records
  cost14 := n14.tBound
  cost15 := n15.tBound
  program := fun w start =>
    if h : w.width = 14 then
      castFinish (by simp [count,h]) (reindexStraight (paddedRow w) (n14.program start))
    else castFinish (by simp [count,h]) (reindexStraight (paddedRow w) (n15.program start))
  coherent := by
    intro Q hQ hn w start history
    have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
      intro a
      have he := window_table_point Q hQ w a.val
      simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
      rw [he]
      exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
    by_cases hw : w.width = 14
    · have ha : ModAliased 13 (windowCoefficients w) := by
        simpa only [hw, Nat.reduceSub] using coefficients_aliased w
      have h := n14.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_pos hw, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
    · have hw15 : w.width = 15 := (width_cases w).resolve_left hw
      have ha : HalfAliased (windowCoefficients w) := coefficients_half_aliased w
      have h := n15.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_neg hw, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
  wellFormed := by
    intro w start
    by_cases h : w.width = 14
    · rw [dif_pos h, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n14.wellFormed start)
    · rw [dif_neg h, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n15.wellFormed start)
  slots := by
    intro w start
    by_cases h : w.width = 14
    · rw [dif_pos h, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n14.slots start
    · rw [dif_neg h, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n15.slots start
  wires := by
    intro w start
    by_cases h : w.width = 14
    · rw [dif_pos h, straightWires_castFinish, straightWires_reindex]
      exact n14.wires start
    · rw [dif_neg h, straightWires_castFinish, straightWires_reindex]
      exact n15.wires start
  tCount := by
    intro Q w start history
    by_cases h : w.width = 14
    · rw [dif_pos h, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h, if_true] using n14.tCount start _ history
    · rw [dif_neg h, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h, if_false] using n15.tCount start _ history

end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ScheduleFirst18.program resetProgram leftWindows rightWindows resetBody





























end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ScheduleFirst18.program resetProgram leftWindows rightWindows resetBody

class SupportCover (body : Single.WindowBody) (ledger : Single.ProducerResources body) : Prop where
  covers : body.support ⊆ ledger.support

variable [cover : SupportCover body ledger]

















def entry : StraightEntry := Single.fixedEntry coefficientAt fullProgram



end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] leftWindows rightWindows program fullProgram readout entry Single.axis ScheduleFirst18.program


structure ProgramCredit (c14 c15 : Nat) : Prop where
  zero : ∀ w start, residue (impl.program w start) = 0
  count_eq : ∀ w start, added (impl.program w start) = count c14 c15 w

variable {c14 c15 : Nat} (hc : ProgramCredit c14 c15)
include hc











variable [cover : SupportCover body ledger]





end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
variable [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] entry program fullProgram readout Single.fixedEntry AndGadget.added Catalyst.saved





end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000


end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


/-!
A generic measured table clear with a three-bit low address and eight unary
wires. The actual Straight program, coherent clearing law and exact resource
ledger are proved for arbitrary constant readers and incoming histories.

The unary schedules and measured-AND primitives adapt the Apache-2.0 protected
library; the combined table/record CNOT compiler is expressed in its existing
first-order grammar.
-/
namespace ShorECDLP.Entrant.Schedule31Eighteen265.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000


end
end ShorECDLP.Entrant.Schedule31Eighteen265.Flexible


namespace ShorECDLP.Entrant.Stack31Plain
open Quantum ShorECDLP.Secp256k1 Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
local instance bodyInstance : Single.WindowBody := WEX.compactBody
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEX.compactBody
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : Schedule31Eighteen265.Flexible.SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
def n14 : ModNarrow WEX.compactBody 13 := Schedule33.MatchedFinal.narrow13
def n15 : UniformNarrow WEX.compactBody := Schedule33.UniformFinal.narrow
local instance programInstance : Schedule31Eighteen265.Flexible.Programs bodyInstance :=
  Schedule31Eighteen265.Flexible.dualPrograms n14 n15


attribute [local irreducible] n14 n15 WEX.compactBody Nat.add Nat.mul AndGadget.added

end
end ShorECDLP.Entrant.Stack31Plain

end


section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 3000000

/-- Combine one table bit and one existing record bit using four CNOTs. -/
def mixedCX {n start : Nat} (ref : ConstantBit n) (value : Bool)
    (record : Fin start) (control scratch target : Wire) : Straight n start start :=
  .gate (.whenBit ref value (.CX control scratch))
    (.recordGate record true (.CX scratch target)
      (.gate (.whenBit ref value (.CX control scratch))
        (.recordGate record true (.CX scratch target) .done)))

def mixedCircuit (table record : Bool) (control scratch target : Wire) : Circuit :=
  (if table then [.CX control scratch] else []) ++
  (if record then [.CX scratch target] else []) ++
  (if table then [.CX control scratch] else []) ++
  (if record then [.CX scratch target] else [])

private theorem unitaryPrefix (a b : Circuit) (p : AdaptiveCircuit)
    (hp : p.run = (AdaptiveCircuit.unitary b .done).run) :
    (AdaptiveCircuit.unitary a p).run = (AdaptiveCircuit.unitary (a ++ b) .done).run := by
  change p.run.map _ = _
  rw [hp, AdaptiveCircuit.run_unitary_done]
  change ([{ history := [], kraus := (Quantum.run b).comp (Quantum.run a) }] : Instrument) =
    ([{ history := [], kraus := Quantum.run (a ++ b) }] : Instrument)
  rw [Quantum.run_append_map]

theorem mixedCX_run {n start : Nat} (ref : ConstantBit n) (value : Bool)
    (record : Fin start) (control scratch target : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((mixedCX ref value record control scratch target).instantiate read history).run =
      (AdaptiveCircuit.unitary
        (mixedCircuit (decide (read ref = value)) (history record) control scratch target) .done).run := by
  have h (a b : Circuit) :
      (AdaptiveCircuit.unitary a (.unitary b (.unitary a (.unitary b .done)))).run =
        (AdaptiveCircuit.unitary (a ++ b ++ a ++ b) .done).run := by
    simpa only [List.append_assoc] using unitaryPrefix a _ _
      (unitaryPrefix b _ _ (unitaryPrefix a b _ rfl))
  by_cases ht : read ref = value <;> cases hr : history record <;>
    simpa [mixedCX, mixedCircuit, Straight.instantiate, TemplateGate.instantiate,
      ht, hr] using h (if read ref = value then [.CX control scratch] else [])
        (if history record then [.CX scratch target] else [])

theorem mixedCircuit_classical (table record : Bool) (control scratch target : Wire)
    (hcs : control ≠ scratch) (hct : control ≠ target) (hst : scratch ≠ target)
    (s : BasisState) :
    Classical.run (mixedCircuit table record control scratch target) s =
      Classical.run (if table && record then [.CX control target] else []) s := by
  funext w
  cases table <;> cases record <;>
    by_cases hw : w = target <;> by_cases hs : w = scratch <;>
    simp_all [mixedCircuit, Classical.run, Classical.applyGate, upd]
  all_goals cases s target <;> cases s scratch <;> cases s control <;> rfl



theorem mixedCX_tCount {n start : Nat} (ref : ConstantBit n) (value : Bool)
    (record : Fin start) (control scratch target : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((mixedCX ref value record control scratch target).instantiate read history).tCount = 0 := by
  by_cases ht : read ref = value <;> cases hr : history record <;>
    simp [mixedCX, Straight.instantiate, TemplateGate.instantiate,
      ht, hr, AdaptiveCircuit.tCount, ShorECDLP.tCount, ShorECDLP.tCost]

theorem mixedCX_slots {n start : Nat} (ref : ConstantBit n) (value : Bool)
    (record : Fin start) (control scratch target : Wire) :
    (mixedCX ref value record control scratch target).gateSlots = 4 := rfl



theorem mixedCX_support {n start : Nat} (ref : ConstantBit n) (value : Bool)
    (record : Fin start) (control scratch target : Wire) :
    NaiveChallenge.straightWires (mixedCX ref value record control scratch target) =
      [control, scratch, scratch, target, control, scratch, scratch, target] := rfl

/-- One binary-to-unary split, with a clean new child. -/
def splitCircuit (bit parent child : Wire) : Circuit :=
  [.CCX bit parent child, .CX child parent]

def splitState (bit parent child : Wire) (s : BasisState) : BasisState :=
  Classical.run (splitCircuit bit parent child) s

theorem splitState_parent (bit parent child : Wire) (s : BasisState)
    (hpc : parent ≠ child) (hc : s child = false) :
    splitState bit parent child s parent = (s parent && !s bit) := by
  cases hb : s bit <;> cases hp : s parent <;>
    simp [splitState, splitCircuit, Classical.run, Classical.applyGate, upd,
      hpc, hb, hp, hc]

theorem splitState_child (bit parent child : Wire) (s : BasisState)
    (hc : s child = false) :
    splitState bit parent child s child = (s bit && s parent) := by
  by_cases hpc : parent = child
  · subst parent
    simp [splitState, splitCircuit, Classical.run, Classical.applyGate, upd, hc]
  · simp [splitState, splitCircuit, Classical.run, Classical.applyGate, upd, hpc, Ne.symm hpc, hc]

theorem splitState_frame (bit parent child : Wire) (s : BasisState) (w : Wire)
    (hp : w ≠ parent) (hc : w ≠ child) : splitState bit parent child s w = s w := by
  simp [splitState, splitCircuit, Classical.run, Classical.applyGate, upd, hp, hc]

/-- The exact relation required before reversing a routed unary split. -/
def SplitReady (bit parent child : Wire) (s : BasisState) : Prop :=
  s child = (s bit && Bool.xor (s parent) (s child))

/-- Reverse the CNOT, then erase the computed AND with protected feedback. -/
def eraseSplit (n start : Nat) (bit parent child : Wire) : Straight n start (start+1) :=
  .gate (.literal (.CX child parent)) (andEraseProgram n start bit parent child)

theorem eraseSplit_run (n start : Nat) (bit parent child : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((eraseSplit n start bit parent child).instantiate read history).run =
      ((AdaptiveCircuit.unitary [.CX child parent] .done).seq
        (measuredAndErase bit parent child)).run := by
  simp [eraseSplit, Straight.instantiate, TemplateGate.instantiate,
    AdaptiveCircuit.seq, AdaptiveCircuit.run, andEraseProgram_run]

theorem eraseSplit_coherent (n start : Nat) (bit parent child : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hbp : bit ≠ parent) (hbc : bit ≠ child) (hpc : parent ≠ child) :
    CoherentlyImplementsOn
      ((eraseSplit n start bit parent child).instantiate read history)
      ((clearRegisterMap [child]).comp (Quantum.run [.CX child parent]))
      (SplitReady bit parent child) := by
  unfold CoherentlyImplementsOn
  rw [eraseSplit_run]
  apply CoherentlyImplementsOn.seq
    (CoherentlyImplementsOn.unitary [.CX child parent] (SplitReady bit parent child))
    (measuredAndErase_coherent bit parent child hbp hbc hpc)
  intro s hs
  rw [run_ket_agrees_classical _ _ (by simp)]
  apply supportedOn_ket
  simpa [PathAndComputed, SplitReady, Classical.run, Classical.applyGate, upd,
    hbp, Ne.symm hpc] using hs

theorem eraseSplit_tCount (n start : Nat) (bit parent child : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((eraseSplit n start bit parent child).instantiate read history).tCount = 0 := by
  simp [eraseSplit, Straight.instantiate, TemplateGate.instantiate,
    AdaptiveCircuit.tCount, ShorECDLP.tCount, ShorECDLP.tCost, andEraseProgram_tCount]

theorem eraseSplit_slots (n start : Nat) (bit parent child : Wire) :
    (eraseSplit n start bit parent child).gateSlots = 4 := rfl



theorem splitState_ready (bit parent child : Wire) (s : BasisState)
    (hbp : bit ≠ parent) (hbc : bit ≠ child) (hpc : parent ≠ child)
    (hc : s child = false) : SplitReady bit parent child (splitState bit parent child s) := by
  cases hb : s bit <;> cases hp : s parent <;>
    simp [SplitReady, splitState, splitCircuit, Classical.run, Classical.applyGate,
      upd, hbp, hbc, hpc, Ne.symm hpc, hc, hb, hp]



theorem eraseSplit_wellFormed (n start : Nat) (bit parent child : Wire)
    (hbp : bit ≠ parent) (hpc : parent ≠ child) :
    (eraseSplit n start bit parent child).WellFormed := by
  exact ⟨Ne.symm hpc, andEraseProgram_wellFormed n start bit parent child hbp⟩

theorem eraseSplit_support (n start : Nat) (bit parent child : Wire) :
    NaiveChallenge.straightWires (eraseSplit n start bit parent child) =
      [child, parent, child, parent, bit, parent, parent] := rfl

theorem splitCircuit_tCount (bit parent child : Wire) :
    ShorECDLP.tCount (splitCircuit bit parent child) = 7 := rfl

theorem splitCircuit_slots (bit parent child : Wire) :
    (splitCircuit bit parent child).length = 2 := rfl











/-- A clean-child routing cell. -/
structure SplitCell where
  bit : Wire
  parent : Wire
  child : Wire

def SplitCell.circuit (c : SplitCell) : Circuit := splitCircuit c.bit c.parent c.child

def SplitCell.Physical (c : SplitCell) : Prop :=
  c.bit ≠ c.parent ∧ c.bit ≠ c.child ∧ c.parent ≠ c.child

def splitNetwork : List SplitCell → Circuit
  | [] => []
  | c :: cs => c.circuit ++ splitNetwork cs

def NetworkReady : List SplitCell → BasisState → Prop
  | [], _ => True
  | c :: cs, s => s c.child = false ∧ NetworkReady cs (Classical.run c.circuit s)

def NetworkComputed (cs : List SplitCell) (s : BasisState) : Prop :=
  ∃ initial, NetworkReady cs initial ∧ Classical.run (splitNetwork cs) initial = s

def inverseSplit (c : SplitCell) : Circuit := [.CX c.child c.parent, .CCX c.bit c.parent c.child]

def inverseNetwork : List SplitCell → Circuit
  | [] => []
  | c :: cs => inverseNetwork cs ++ inverseSplit c

theorem split_inverse (c : SplitCell) (s : BasisState) (hp : c.Physical)
    (hc : s c.child = false) :
    Classical.run (inverseSplit c) (Classical.run c.circuit s) = s := by
  funext w
  by_cases hwp : w = c.parent <;> by_cases hwc : w = c.child <;>
    simp_all [inverseSplit, SplitCell.circuit, splitCircuit, Classical.run,
      Classical.applyGate, upd, hp.1, hp.2.1, hp.2.2, Ne.symm hp.2.2]

theorem inverseNetwork_correct (cs : List SplitCell)
    (hp : ∀ c ∈ cs, c.Physical) (s : BasisState) (hs : NetworkReady cs s) :
    Classical.run (inverseNetwork cs) (Classical.run (splitNetwork cs) s) = s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [NetworkReady] at hs
    rw [splitNetwork, Classical.run_append, inverseNetwork, Classical.run_append,
      ih (fun d hd => hp d (by simp [hd])) _ hs.2]
    exact split_inverse c s (hp c (by simp)) hs.1

theorem inverseNetwork_hp (cs : List SplitCell) : Classical.HPFree (inverseNetwork cs) := by
  induction cs with
  | nil => simp [inverseNetwork]
  | cons c cs ih => simpa [inverseNetwork, inverseSplit] using ih

def eraseNetwork (n : Nat) : (cs : List SplitCell) → (start : Nat) →
    Straight n start (start + cs.length)
  | [], _ => .done
  | c :: cs, start => castFinish (by simp; omega)
      ((eraseNetwork n cs start).append (eraseSplit n (start + cs.length) c.bit c.parent c.child))

def eraseNetworkSource : List SplitCell → AdaptiveCircuit
  | [] => .done
  | c :: cs => (eraseNetworkSource cs).seq
      ((AdaptiveCircuit.unitary [.CX c.child c.parent] .done).seq
        (measuredAndErase c.bit c.parent c.child))

theorem eraseNetwork_source (n : Nat) (cs : List SplitCell) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((eraseNetwork n cs start).instantiate read history).run = (eraseNetworkSource cs).run := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simp only [eraseNetwork, castFinish_instantiate, eraseNetworkSource]
    rw [append_run_fixed _ _ _ _ _ (fun h => eraseSplit_run n _ c.bit c.parent c.child read h),
      AdaptiveCircuit.run_seq, ih, ← AdaptiveCircuit.run_seq]

theorem eraseNetwork_coherent (cs : List SplitCell) (hp : ∀ c ∈ cs, c.Physical) :
    CoherentlyImplementsOn (eraseNetworkSource cs)
      (Quantum.run (inverseNetwork cs)) (NetworkComputed cs) := by
  induction cs with
  | nil => exact CoherentlyImplementsOn.unitary [] _
  | cons c cs ih =>
    have hc := hp c (by simp)
    have ht := ih (fun d hd => hp d (by simp [hd]))
    have htail : CoherentlyImplementsOn (eraseNetworkSource cs)
        (Quantum.run (inverseNetwork cs)) (NetworkComputed (c :: cs)) := by
      obtain ⟨coeff, hcoeff, hmass⟩ := ht
      refine ⟨coeff, hcoeff.imp ?_, hmass⟩
      intro b z hb s hs
      apply hb s
      obtain ⟨initial, hi, rfl⟩ := hs
      exact ⟨Classical.run c.circuit initial, hi.2, by simp [splitNetwork, Classical.run_append]⟩
    have hhead : CoherentlyImplementsOn
        ((AdaptiveCircuit.unitary [.CX c.child c.parent] .done).seq
          (measuredAndErase c.bit c.parent c.child))
        (Quantum.run (inverseSplit c)) (SplitReady c.bit c.parent c.child) := by
      obtain ⟨coeff, hcoeff, hmass⟩ := eraseSplit_coherent 1 0 c.bit c.parent c.child
        (fun _ => false) Fin.elim0 hc.1 hc.2.1 hc.2.2
      refine ⟨coeff, ?_, hmass⟩
      rw [eraseSplit_run] at hcoeff
      apply hcoeff.imp
      intro b z hb s hs
      rw [hb s hs]
      congr 1
      rw [LinearMap.comp_apply]
      rw [show inverseSplit c = [.CX c.child c.parent] ++ [.CCX c.bit c.parent c.child] from rfl,
        Quantum.run_append, run_ket_agrees_classical _ _ (by simp), clearRegisterMap_ket]
      have he : PathAndComputed c.bit c.parent c.child
          (Classical.run [.CX c.child c.parent] s) := by
        simpa [PathAndComputed, SplitReady, Classical.run, Classical.applyGate, upd,
          hc.1, Ne.symm hc.2.2] using hs
      rw [run_ket_agrees_classical _ _ (by simp)]
      congr 1
      funext w
      by_cases hw : w = c.child <;>
        simp_all [PathAndComputed, clearRegister, Classical.run, Classical.applyGate, upd]
    have hh := htail.seq hhead (by
      intro s hs
      obtain ⟨initial, hi, rfl⟩ := hs
      rw [run_ket_agrees_classical _ _ (inverseNetwork_hp cs), splitNetwork,
        Classical.run_append, inverseNetwork_correct cs (fun d hd => hp d (by simp [hd])) _ hi.2]
      apply supportedOn_ket
      exact splitState_ready c.bit c.parent c.child initial hc.1 hc.2.1 hc.2.2 hi.1)
    simpa only [eraseNetworkSource, inverseNetwork, Quantum.run_append_map] using hh


/-! ### Generic unary split network

Level `j` splits every live marker `hot i` (`i < 2^j`) on address bit `j` into `hot i` and
`hot (i + 2^j)`.  After `b` levels exactly the marker at the binary value of the `b` low bits is
set.  This generalizes the hand-written three-bit network. -/

def hotLevelN (bitsN hotN : Nat → Wire) (j : Nat) : List SplitCell :=
  (List.range (2^j)).map fun i => ⟨bitsN j, hotN i, hotN (i + 2^j)⟩

def hotNetN (bitsN hotN : Nat → Wire) : Nat → List SplitCell
  | 0 => []
  | j+1 => hotNetN bitsN hotN j ++ hotLevelN bitsN hotN j

def addrN (bitsN : Nat → Wire) (s : BasisState) : Nat → Nat
  | 0 => 0
  | j+1 => addrN bitsN s j + 2^j * (s (bitsN j)).toNat

theorem addrN_lt (bitsN : Nat → Wire) (s : BasisState) : ∀ j, addrN bitsN s j < 2^j
  | 0 => by simp [addrN]
  | j+1 => by
    have h := addrN_lt bitsN s j
    have hp : 2^(j+1) = 2^j + 2^j := by rw [pow_succ]; omega
    cases hb : s (bitsN j) <;> simp only [addrN, hb, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem splitNetwork_append (xs ys : List SplitCell) :
    splitNetwork (xs ++ ys) = splitNetwork xs ++ splitNetwork ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simp [splitNetwork, ih]

theorem networkReady_append (xs ys : List SplitCell) (s : BasisState) :
    NetworkReady (xs ++ ys) s ↔
      NetworkReady xs s ∧ NetworkReady ys (Classical.run (splitNetwork xs) s) := by
  induction xs generalizing s with
  | nil => simp [NetworkReady, splitNetwork, Classical.run]
  | cons c cs ih =>
    simp only [List.cons_append, NetworkReady, splitNetwork, Classical.run_append, ih, and_assoc]

theorem hotNetN_length (bitsN hotN : Nat → Wire) : ∀ j, (hotNetN bitsN hotN j).length = 2^j - 1
  | 0 => rfl
  | j+1 => by
    have h := hotNetN_length bitsN hotN j
    have hp : 1 ≤ 2^j := Nat.one_le_two_pow
    simp only [hotNetN, hotLevelN, List.length_append, List.length_map, List.length_range, h, pow_succ]
    omega

theorem mem_hotNetN (bitsN hotN : Nat → Wire) (J : Nat) (c : SplitCell) (hc : c ∈ hotNetN bitsN hotN J) :
    ∃ j i, j < J ∧ i < 2^j ∧ c = ⟨bitsN j, hotN i, hotN (i + 2^j)⟩ := by
  induction J with
  | zero => simp [hotNetN] at hc
  | succ J ih =>
    simp only [hotNetN, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨j, i, hj, hi, rfl⟩ := ih hc
      exact ⟨j, i, by omega, hi, rfl⟩
    · simp only [hotLevelN, List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      exact ⟨J, i, by omega, hi, rfl⟩

/-- Wire hypotheses for a `b`-bit network. -/
structure HotLayout (b : Nat) (bitsN hotN : Nat → Wire) : Prop where
  inj : ∀ x y, x < 2^b → y < 2^b → hotN x = hotN y → x = y
  disj : ∀ j x, j < b → x < 2^b → bitsN j ≠ hotN x

theorem pow_level_lt {j b : Nat} (hj : j < b) (i : Nat) (hi : i < 2^j) : i + 2^j < 2^b := by
  have h1 : 2^(j+1) ≤ 2^b := Nat.pow_le_pow_right (by decide) hj
  have h2 : 2^(j+1) = 2^j + 2^j := by rw [pow_succ]; omega
  omega

theorem level_partial (b : Nat) (bitsN hotN : Nat → Wire) (hL : HotLayout b bitsN hotN)
    (j : Nat) (hj : j < b) (a : Nat) (ha : a < 2^j) (t : BasisState)
    (ht : ∀ x, x < 2^b → t (hotN x) = decide (x = a)) :
    ∀ m, m ≤ 2^j →
      (∀ x, x < 2^b →
        Classical.run (splitNetwork ((List.range m).map fun i => (⟨bitsN j, hotN i, hotN (i + 2^j)⟩ : SplitCell))) t (hotN x) =
          if x < m then (decide (x = a) && !t (bitsN j))
          else if 2^j ≤ x ∧ x < 2^j + m then (decide (x - 2^j = a) && t (bitsN j))
          else decide (x = a)) ∧
      (∀ w, (∀ x, x < 2^b → w ≠ hotN x) →
        Classical.run (splitNetwork ((List.range m).map fun i => (⟨bitsN j, hotN i, hotN (i + 2^j)⟩ : SplitCell))) t w = t w) ∧
      NetworkReady ((List.range m).map fun i => (⟨bitsN j, hotN i, hotN (i + 2^j)⟩ : SplitCell)) t := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [if_neg (by omega), if_neg (by omega)]
      exact ht x hx
    · intro w _
      rfl
    · simp [NetworkReady]
  | succ m ih =>
    intro hm
    obtain ⟨hv, hf, hr⟩ := ih (by omega)
    have hm2 : m + 2^j < 2^b := pow_level_lt hj m (by omega)
    have hm1 : m < 2^b := by omega
    set u := Classical.run (splitNetwork ((List.range m).map fun i => (⟨bitsN j, hotN i, hotN (i + 2^j)⟩ : SplitCell))) t with hu
    have hbit : u (bitsN j) = t (bitsN j) := hf _ (fun x hx => hL.disj j x hj hx)
    have hchild : u (hotN (m + 2^j)) = false := by
      have h := hv (m + 2^j) hm2
      rw [if_neg (by omega), if_neg (by omega)] at h
      rw [h]
      exact decide_eq_false (by omega)
    have hparent : u (hotN m) = decide (m = a) := by
      have h := hv m hm1
      rw [if_neg (by omega), if_neg (by omega)] at h
      exact h
    have hpc : hotN m ≠ hotN (m + 2^j) := by
      intro he; have := hL.inj _ _ hm1 hm2 he; omega
    have hstep : Classical.run (splitNetwork ((List.range (m+1)).map fun i => (⟨bitsN j, hotN i, hotN (i + 2^j)⟩ : SplitCell))) t =
        splitState (bitsN j) (hotN m) (hotN (m + 2^j)) u := by
      rw [List.range_succ, List.map_append, splitNetwork_append, Classical.run_append, ← hu]
      simp [splitNetwork, SplitCell.circuit, splitState]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [hstep]
      by_cases hxm : x = m
      · subst hxm
        rw [splitState_parent _ _ _ u hpc hchild, hparent, hbit, if_pos (by omega)]
      · by_cases hxc : x = m + 2^j
        · subst hxc
          rw [splitState_child _ _ _ u hchild, hparent, hbit, if_neg (by omega), if_pos (by omega),
            show m + 2^j - 2^j = m by omega, Bool.and_comm]
        · have hnp : hotN x ≠ hotN m := fun he => hxm (hL.inj _ _ hx hm1 he)
          have hnc : hotN x ≠ hotN (m + 2^j) := fun he => hxc (hL.inj _ _ hx hm2 he)
          rw [splitState_frame _ _ _ u _ hnp hnc, hv x hx]
          by_cases h1 : x < m
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1, if_neg (show ¬ x < m + 1 by omega)]
            by_cases h2 : 2^j ≤ x ∧ x < 2^j + m
            · rw [if_pos h2, if_pos (show 2^j ≤ x ∧ x < 2^j + (m + 1) by omega)]
            · rw [if_neg h2, if_neg (show ¬ (2^j ≤ x ∧ x < 2^j + (m + 1)) by omega)]
    · intro w hw
      rw [hstep, splitState_frame _ _ _ u _ (hw m hm1) (hw _ hm2)]
      exact hf w hw
    · rw [List.range_succ, List.map_append, networkReady_append]
      refine ⟨hr, ?_⟩
      simp only [List.map_cons, List.map_nil, NetworkReady, and_true]
      rw [← hu]
      exact hchild

theorem level_run (b : Nat) (bitsN hotN : Nat → Wire) (hL : HotLayout b bitsN hotN)
    (j : Nat) (hj : j < b) (a : Nat) (ha : a < 2^j) (t : BasisState)
    (ht : ∀ x, x < 2^b → t (hotN x) = decide (x = a)) :
    (∀ x, x < 2^b → Classical.run (splitNetwork (hotLevelN bitsN hotN j)) t (hotN x) =
        decide (x = a + 2^j * (t (bitsN j)).toNat)) ∧
      (∀ w, (∀ x, x < 2^b → w ≠ hotN x) → Classical.run (splitNetwork (hotLevelN bitsN hotN j)) t w = t w) ∧
      NetworkReady (hotLevelN bitsN hotN j) t := by
  obtain ⟨hv, hf, hr⟩ := level_partial b bitsN hotN hL j hj a ha t ht (2^j) le_rfl
  refine ⟨?_, hf, hr⟩
  intro x hx
  have hv := hv x hx
  unfold hotLevelN
  rw [hv]
  have hp : 2^(j+1) = 2^j + 2^j := by rw [pow_succ]; omega
  have hjb : 2^(j+1) ≤ 2^b := Nat.pow_le_pow_right (by decide) hj
  cases hb : t (bitsN j)
  · simp only [Bool.not_false, Bool.and_true, Bool.and_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    by_cases h1 : x < 2^j
    · rw [if_pos h1]
    · rw [if_neg h1]
      have : x ≠ a := by omega
      by_cases h2 : 2^j ≤ x ∧ x < 2^j + 2^j
      · rw [if_pos h2, decide_eq_false this]
      · rw [if_neg h2]
  · simp only [Bool.not_true, Bool.and_true, Bool.and_false, Bool.toNat_true, Nat.mul_one]
    by_cases h1 : x < 2^j
    · rw [if_pos h1, decide_eq_false (show x ≠ a + 2^j by omega)]
    · rw [if_neg h1]
      by_cases h2 : 2^j ≤ x ∧ x < 2^j + 2^j
      · rw [if_pos h2]
        exact decide_eq_decide.mpr (by omega)
      · rw [if_neg h2, decide_eq_false (show x ≠ a by omega), decide_eq_false (show x ≠ a + 2^j by omega)]

theorem net_run (b : Nat) (bitsN hotN : Nat → Wire) (hL : HotLayout b bitsN hotN) (t0 : BasisState)
    (h0 : ∀ x, x < 2^b → t0 (hotN x) = decide (x = 0)) :
    ∀ J, J ≤ b →
      (∀ x, x < 2^b → Classical.run (splitNetwork (hotNetN bitsN hotN J)) t0 (hotN x) =
        decide (x = addrN bitsN t0 J)) ∧
      (∀ w, (∀ x, x < 2^b → w ≠ hotN x) → Classical.run (splitNetwork (hotNetN bitsN hotN J)) t0 w = t0 w) ∧
      NetworkReady (hotNetN bitsN hotN J) t0 := by
  intro J
  induction J with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; simpa [hotNetN, splitNetwork, Classical.run, addrN] using h0 x hx
    · intro w _; simp [hotNetN, splitNetwork, Classical.run]
    · simp [hotNetN, NetworkReady]
  | succ J ih =>
    intro hJ
    obtain ⟨hv, hf, hr⟩ := ih (by omega)
    let u := Classical.run (splitNetwork (hotNetN bitsN hotN J)) t0
    have hbit : u (bitsN J) = t0 (bitsN J) := hf _ (fun x hx => hL.disj J x (by omega) hx)
    obtain ⟨lv, lf, lr⟩ := level_run b bitsN hotN hL J (by omega) (addrN bitsN t0 J)
      (addrN_lt bitsN t0 J) u hv
    have he : Classical.run (splitNetwork (hotNetN bitsN hotN (J+1))) t0 =
        Classical.run (splitNetwork (hotLevelN bitsN hotN J)) u := by
      simp only [hotNetN, splitNetwork_append, Classical.run_append, u]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [he, lv x hx, hbit]
      rfl
    · intro w hw
      rw [he, lf w hw]
      exact hf w hw
    · simp only [hotNetN, networkReady_append]
      exact ⟨hr, lr⟩


theorem splitNetwork_frame (cs : List SplitCell) (s : BasisState) (w : Wire)
    (hw : ∀ c ∈ cs, w ≠ c.parent ∧ w ≠ c.child) :
    Classical.run (splitNetwork cs) s w = s w := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rw [splitNetwork, Classical.run_append, ih _ (fun d hd => hw d (by simp [hd]))]
    exact splitState_frame c.bit c.parent c.child s w (hw c (by simp)).1 (hw c (by simp)).2


/-- Nat-indexed views of the seven low address wires and the 128 unary wires. -/
def lowN (low : Fin 7 → Wire) (j : Nat) : Wire := if h : j < 7 then low ⟨j, h⟩ else low 0
def hotNat (hot : Fin 128 → Wire) (x : Nat) : Wire := if h : x < 128 then hot ⟨x, h⟩ else hot 0

/-- The low-address bank: seven address bits split into 128 unary wires. -/
def hotNetwork (low : Fin 7 → Wire) (hot : Fin 128 → Wire) : List SplitCell :=
  hotNetN (lowN low) (hotNat hot) 7

def hotPrepare (low : Fin 7 → Wire) (hot : Fin 128 → Wire) : Circuit :=
  [.X (hot 0)] ++ splitNetwork (hotNetwork low hot)

def hotAddress (low : Fin 7 → Wire) (s : BasisState) : Nat := addrN (lowN low) s 7

def HotClean (hot : Fin 128 → Wire) (s : BasisState) : Prop := ∀ i, s (hot i) = false

theorem hotNetwork_length (low : Fin 7 → Wire) (hot : Fin 128 → Wire) :
    (hotNetwork low hot).length = 127 := by
  simp [hotNetwork, hotNetN_length]

theorem hotLayout_of (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    HotLayout 7 (lowN low) (hotNat hot) := by
  constructor
  · intro x y hx hy he
    have hx' : x < 128 := by simpa using hx
    have hy' : y < 128 := by simpa using hy
    simp only [hotNat, hx', hy', dite_true] at he
    exact congrArg Fin.val (hi he)
  · intro j x hj hx
    have hx' : x < 128 := by simpa using hx
    simp only [lowN, hotNat, hj, hx', dite_true]
    exact hd _ _

theorem mem_hotNetwork (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (c : SplitCell)
    (hc : c ∈ hotNetwork low hot) :
    ∃ j : Fin 7, ∃ x y : Fin 128, c = ⟨low j, hot x, hot y⟩ ∧ x ≠ y := by
  obtain ⟨j, i, hj, hi, rfl⟩ := mem_hotNetN _ _ 7 c hc
  have h2 : i + 2^j < 2^7 := pow_level_lt hj i hi
  have h2' : i + 2^j < 128 := by simpa using h2
  have h1 : i < 128 := by omega
  refine ⟨⟨j, hj⟩, ⟨i, h1⟩, ⟨i + 2^j, h2'⟩, ?_, ?_⟩
  · simp [lowN, hotNat, hj, h1, h2']
  · intro he
    have := congrArg Fin.val he
    have hp : 0 < 2^j := by positivity
    simp at this

theorem hotNetwork_physical (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    ∀ c ∈ hotNetwork low hot, c.Physical := by
  intro c hc
  obtain ⟨j, x, y, rfl, hxy⟩ := mem_hotNetwork low hot c hc
  exact ⟨hd j x, hd j y, fun he => hxy (hi he)⟩

theorem hotStart (hot : Fin 128 → Wire) (hi : Function.Injective hot)
    (s : BasisState) (hs : HotClean hot s) :
    ∀ x, x < 2^7 → Classical.run [.X (hot 0)] s (hotNat hot x) = decide (x = 0) := by
  intro x hx
  have hx' : x < 128 := by simpa using hx
  simp only [hotNat, hx', dite_true]
  by_cases h0 : x = 0
  · subst h0
    simp [Classical.run, Classical.applyGate, upd, hs 0]
  · have hne : hot ⟨x, hx'⟩ ≠ hot 0 := fun he => h0 (congrArg Fin.val (hi he))
    simp [Classical.run, Classical.applyGate, upd, hne, hs ⟨x, hx'⟩, h0]

theorem addrN_congr (bitsN : Nat → Wire) (s t : BasisState) :
    ∀ J, (∀ j, j < J → s (bitsN j) = t (bitsN j)) → addrN bitsN s J = addrN bitsN t J
  | 0, _ => rfl
  | J+1, h => by
    simp only [addrN, addrN_congr bitsN s t J (fun j hj => h j (by omega)), h J (by omega)]

theorem hotNetwork_ready (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean hot s) :
    NetworkReady (hotNetwork low hot) (Classical.run [.X (hot 0)] s) :=
  (net_run 7 (lowN low) (hotNat hot) (hotLayout_of low hot hi hd) _ (hotStart hot hi s hs) 7 le_rfl).2.2

theorem hotPrepare_marker (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean hot s) (i : Fin 128) :
    Classical.run (hotPrepare low hot) s (hot i) = decide (i.val = hotAddress low s) := by
  have h := (net_run 7 (lowN low) (hotNat hot) (hotLayout_of low hot hi hd) _ (hotStart hot hi s hs) 7 le_rfl).1
    i.val (by simp)
  have hhot : hotNat hot i.val = hot i := by simp [hotNat, i.isLt]
  rw [hhot] at h
  rw [hotPrepare, Classical.run_append, hotNetwork, h, hotAddress]
  congr 2
  apply addrN_congr
  intro j hj
  have hj' : j < 7 := hj
  simp only [lowN, hj', dite_true]
  have hne : low ⟨j, hj'⟩ ≠ hot 0 := hd _ _
  simp [Classical.run, Classical.applyGate, upd, hne]

theorem hotPrepare_frame (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (s : BasisState) (w : Wire) (hw : ∀ i, w ≠ hot i) :
    Classical.run (hotPrepare low hot) s w = s w := by
  rw [hotPrepare, Classical.run_append, splitNetwork_frame _ _ _ (by
    intro c hc
    obtain ⟨j, x, y, rfl, _⟩ := mem_hotNetwork low hot c hc
    exact ⟨hw x, hw y⟩)]
  simp [Classical.run, Classical.applyGate, upd, hw]

theorem hotAddress_bound (low : Fin 7 → Wire) (s : BasisState) : hotAddress low s < 128 := by
  have h := addrN_lt (lowN low) s 7
  simpa [hotAddress] using h

attribute [irreducible] hotNetwork


private theorem hadamard_twice (w : Wire) (ψ : State) :
    applyGate (.H w) (applyGate (.H w) ψ) = ψ :=
  applyGate_adjoint_applyGate (.H w) trivial ψ

theorem cx_hadamard_eigen (control target : Wire) (hct : control ≠ target) (s : BasisState) :
    applyGate (.CX control target) (applyGate (.H target) (ket s)) =
      (if s control && s target then (-1 : ℂ) else 1) • applyGate (.H target) (ket s) := by
  have h := congrArg (fun ψ => applyGate (.H target) ψ)
    (run_controlledZ_ket control target s hct)
  cases hc : s control <;> cases ht : s target <;>
    simpa [controlledZ, hadamard_twice, hc, ht] using h

theorem gate_hadamards_commute (g : Gate) (ws : List Wire)
    (hw : ∀ w ∈ ws, w ∉ gateWires g) (ψ : State) :
    applyGate g (Quantum.run (ws.map Gate.H) ψ) =
      Quantum.run (ws.map Gate.H) (applyGate g ψ) := by
  induction ws generalizing ψ with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, Quantum.run_cons]
    rw [ih (fun v hv => hw v (by simp [hv])), applyGate_H_commute g w (hw w (by simp))]

theorem cx_hadamards_eigen (control target : Wire) (ws : List Wire)
    (hn : ws.Nodup) (hc : control ∉ ws) (ht : target ∈ ws) (s : BasisState) :
    applyGate (.CX control target) (Quantum.run (ws.map Gate.H) (ket s)) =
      (if s control && s target then (-1 : ℂ) else 1) •
        Quantum.run (ws.map Gate.H) (ket s) := by
  induction ws generalizing s with
  | nil => simp at ht
  | cons w ws ih =>
    have hcw : control ≠ w := by intro h; exact hc (by simp [h])
    have hcs : control ∉ ws := fun h => hc (by simp [h])
    have hns := (List.nodup_cons.mp hn).2
    by_cases htw : target = w
    · subst target
      simp only [List.map_cons, Quantum.run_cons]
      rw [gate_hadamards_commute _ ws (by
        intro v hv
        simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => hcs (h ▸ hv), fun h => (List.nodup_cons.mp hn).1 (h ▸ hv)⟩),
        cx_hadamard_eigen control w hcw, map_smul]
    · have hts : target ∈ ws := (List.mem_cons.mp ht).resolve_left htw
      simp only [List.map_cons, Quantum.run_cons, applyGate_H_ket, map_add, map_smul]
      rw [ih hns hcs hts (s[w ↦ false]), ih hns hcs hts (s[w ↦ true])]
      simp only [upd_other _ _ _ hcw, upd_other _ _ _ htw]
      module

def xorPhase (control : Wire) (targets : List Wire) (s : BasisState) : ℂ :=
  (targets.map fun w => if s control && s w then (-1 : ℂ) else 1).prod

theorem xor_hadamards_eigen (control : Wire) (targets ws : List Wire)
    (hn : ws.Nodup) (hc : control ∉ ws) (ht : targets ⊆ ws) (s : BasisState) :
    Quantum.run (tableXorGates control targets) (Quantum.run (ws.map Gate.H) (ket s)) =
      xorPhase control targets s • Quantum.run (ws.map Gate.H) (ket s) := by
  induction targets with
  | nil => simp [tableXorGates, xorPhase]
  | cons t ts ih =>
    simp only [tableXorGates, List.map_cons, Quantum.run_cons]
    rw [cx_hadamards_eigen control t ws hn hc (ht (by simp)) s, map_smul,
      show List.map (Gate.CX control) ts = tableXorGates control ts from rfl,
      ih (fun w hw => ht (by simp [hw]))]
    simp [xorPhase, smul_smul]



def historyPrefix {base start : Nat} (hb : base ≤ start) (history : Fin start → Bool) : Fin base → Bool :=
  fun i => history ⟨i.val, lt_of_lt_of_le i.isLt hb⟩

theorem historyPrefix_last {base start : Nat} (hb : base ≤ start)
    (history : Fin start → Bool) (bit : Bool) :
    historyPrefix (Nat.le_trans hb (Nat.le_succ start)) (Fin.lastCases bit history) =
      historyPrefix hb history := by
  funext i
  change Fin.lastCases bit history
    ((⟨i.val, lt_of_lt_of_le i.isLt hb⟩ : Fin start).castSucc) =
      history ⟨i.val, lt_of_lt_of_le i.isLt hb⟩
  exact Fin.lastCases_castSucc _

theorem append_run_prefix {n base a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n → Bool) (hb : base ≤ a) (history : Fin a → Bool)
    (saved : Fin base → Bool) (hs : historyPrefix hb history = saved)
    (target : AdaptiveCircuit)
    (hq : ∀ h, historyPrefix (hb.trans p.cursor_mono) h = saved →
      (q.instantiate read h).run = target.run) :
    ((p.append q).instantiate read history).run = ((p.instantiate read history).seq target).run := by
  induction p with
  | done => exact hq history hs
  | gate g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq, AdaptiveCircuit.run]
    rw [ih q hb history hs hq]
  | recordGate i v g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq, AdaptiveCircuit.run]
    rw [ih q hb history hs hq]
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq, AdaptiveCircuit.run]
    rw [ih q (hb.trans (Nat.le_succ _)) _ ((historyPrefix_last hb history false).trans hs) hq,
      ih q (hb.trans (Nat.le_succ _)) _ ((historyPrefix_last hb history true).trans hs) hq]

structure RecordPort (n base : Nat) where
  ref : Nat → ConstantBit n
  value : Bool
  record : Fin base
  target : Wire

def recordLeaf {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (row control : Nat) : (start : Nat) → base ≤ start → Straight n start start
  | start, hb =>
    match ports with
    | [] => .done
    | p :: ps => (mixedCX (p.ref row) p.value ⟨p.record.val, lt_of_lt_of_le p.record.isLt hb⟩
        control scratch p.target).append (recordLeaf ps scratch row control start hb)

def recordLeafCircuit {n base : Nat} (ports : List (RecordPort n base))
    (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) : Circuit :=
  ports.flatMap fun p => mixedCircuit (decide (read (p.ref row) = p.value))
    (saved p.record) control scratch p.target

theorem recordLeaf_run {n base : Nat} (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base ≤ start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((recordLeaf ports scratch row control start hb).instantiate read history).run =
      (AdaptiveCircuit.unitary (recordLeafCircuit ports scratch row control read (historyPrefix hb history)) .done).run := by
  induction ports generalizing history with
  | nil =>
    change AdaptiveCircuit.done.run = (AdaptiveCircuit.unitary [] .done).run
    rw [AdaptiveCircuit.run_unitary_done]
    rfl
  | cons p ps ih =>
    simp only [recordLeaf, recordLeafCircuit, List.flatMap_cons]
    rw [append_run_prefix _ _ read hb history _ rfl _ (by
      intro h hh; rw [ih h, hh])]
    rw [AdaptiveCircuit.run_seq, mixedCX_run, ← AdaptiveCircuit.run_seq]
    exact unitaryPrefix _ _ _ rfl

/-- A fixed traversal schedule whose leaves may read an earlier record bank. -/
inductive RecordLookupOp where
  | gates (gs : Circuit)
  | leaf (row control : Nat)
  | erase (a b t : Wire)

def recordMeasurements : List RecordLookupOp → Nat
  | [] => 0
  | .gates _ :: ops => recordMeasurements ops
  | .leaf _ _ :: ops => recordMeasurements ops
  | .erase _ _ _ :: ops => 1 + recordMeasurements ops

def recordUnaryOps : UnaryActionTree → Wire → List Wire → List RecordLookupOp
  | .leaf row, root, _ => [.leaf row root]
  | .node bit zero one, root, path :: rest =>
      [.gates (computeZeroAnd root bit path)] ++ recordUnaryOps zero path rest ++
      [.gates [.CX root path]] ++ recordUnaryOps one path rest ++
      [.gates [.CX root path], .gates [.X bit], .erase root bit path, .gates [.X bit]]
  | .node _ _ _, _, [] => []

def recordLookupProgram {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire) :
    (ops : List RecordLookupOp) → (start : Nat) → base ≤ start →
      Straight n start (start + recordMeasurements ops)
  | [], _, _ => .done
  | .gates gs :: ops, start, hb =>
      (literalProgram gs).append (recordLookupProgram ports scratch ops start hb)
  | .leaf row control :: ops, start, hb =>
      (recordLeaf ports scratch row control start hb).append (recordLookupProgram ports scratch ops start hb)
  | .erase a b t :: ops, start, hb => castFinish (by simp [recordMeasurements]; omega)
      ((andEraseProgram n start a b t).append
        (recordLookupProgram ports scratch ops (start + 1) (hb.trans (Nat.le_succ start))))

def recordLookupSource {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (read : ConstantBit n → Bool) (saved : Fin base → Bool) : List RecordLookupOp → AdaptiveCircuit
  | [] => .done
  | .gates gs :: ops => .unitary gs (recordLookupSource ports scratch read saved ops)
  | .leaf row control :: ops => .unitary (recordLeafCircuit ports scratch row control read saved)
      (recordLookupSource ports scratch read saved ops)
  | .erase a b t :: ops => (measuredAndErase a b t).seq (recordLookupSource ports scratch read saved ops)

theorem recordLookup_run {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (ops : List RecordLookupOp) (start : Nat) (hb : base ≤ start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((recordLookupProgram ports scratch ops start hb).instantiate read history).run =
      (recordLookupSource ports scratch read (historyPrefix hb history) ops).run := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
      simp only [recordLookupProgram, recordLookupSource]
      rw [append_run_prefix _ _ read hb history _ rfl _ (by
        intro h hh; rw [ih, hh]), AdaptiveCircuit.run_seq, literalProgram_run,
        ← AdaptiveCircuit.run_seq]
      rfl
    | leaf row control =>
      simp only [recordLookupProgram, recordLookupSource]
      rw [append_run_prefix _ _ read hb history _ rfl _ (by
        intro h hh; rw [ih, hh]), AdaptiveCircuit.run_seq, recordLeaf_run,
        ← AdaptiveCircuit.run_seq]
      rfl
    | erase a b t =>
      simp only [recordLookupProgram, castFinish_instantiate, recordLookupSource]
      rw [append_run_prefix _ _ read hb history _ rfl _ (by
        intro h hh; rw [ih, hh]), AdaptiveCircuit.run_seq, andEraseProgram_run,
        ← AdaptiveCircuit.run_seq]


theorem recordLookupSource_append {n base : Nat} (ports : List (RecordPort n base))
    (scratch : Wire) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (xs ys : List RecordLookupOp) :
    recordLookupSource ports scratch read saved (xs ++ ys) =
      (recordLookupSource ports scratch read saved xs).seq (recordLookupSource ports scratch read saved ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [recordLookupSource, ih, AdaptiveCircuit.seq, adaptive_seq_assoc]

theorem recordUnary_source {n base : Nat} (ports : List (RecordPort n base))
    (scratch : Wire) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire) :
    recordLookupSource ports scratch read saved (recordUnaryOps tree root paths) =
      unaryAction .inc (fun row control => recordLeafCircuit ports scratch row control read saved) tree root paths := by
  induction tree generalizing root paths with
  | leaf row => rfl
  | node bit zero one ihz iho =>
    cases paths with
    | nil => rfl
    | cons path rest =>
      simp [recordUnaryOps, recordLookupSource_append, recordLookupSource, ihz, iho,
        unaryAction, eraseZeroAnd, AdaptiveCircuit.seq]

theorem recordLeafCircuit_hp {n base : Nat} (ports : List (RecordPort n base))
    (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) :
    Classical.HPFree (recordLeafCircuit ports scratch row control read saved) := by
  induction ports with
  | nil => simp [recordLeafCircuit]
  | cons p ps ih =>
    simp only [recordLeafCircuit, List.flatMap_cons, Classical.hpFree_append] at ih ⊢
    refine ⟨?_, ih⟩
    cases decide (read (p.ref row) = p.value) <;> cases saved p.record <;>
      simp [mixedCircuit]


def recordTargets {n base : Nat} (ports : List (RecordPort n base)) (row : Nat)
    (read : ConstantBit n → Bool) (saved : Fin base → Bool) : List Wire :=
  (ports.filter fun p => decide (read (p.ref row) = p.value) && saved p.record).map RecordPort.target

theorem recordLeafCircuit_classical {n base : Nat} (ports : List (RecordPort n base))
    (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (hcs : control ≠ scratch)
    (hp : ∀ p ∈ ports, control ≠ p.target ∧ scratch ≠ p.target) (s : BasisState) :
    Classical.run (recordLeafCircuit ports scratch row control read saved) s =
      Classical.run (tableXorGates control (recordTargets ports row read saved)) s := by
  induction ports generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [recordLeafCircuit, List.flatMap_cons, Classical.run_append]
    rw [mixedCircuit_classical _ _ _ _ _ hcs (hp p (by simp)).1 (hp p (by simp)).2]
    change Classical.run (recordLeafCircuit ps scratch row control read saved) _ = _
    rw [ih (fun d hd => hp d (by simp [hd]))]
    by_cases ht : read (p.ref row) = p.value <;> cases hr : saved p.record <;>
      simp [recordTargets, tableXorGates, ht, hr, Classical.run_cons]

def xorMany : List Wire → Bool → BasisState → BasisState
  | [], _, s => s
  | w :: ws, active, s => xorMany ws active (s[w ↦ s w ^^ active])

theorem xorMany_false (ws : List Wire) (s : BasisState) : xorMany ws false s = s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    rw [xorMany, ih]
    funext v
    by_cases h : v = w <;> simp_all [upd]

theorem xorMany_frame (ws : List Wire) (active : Bool) (s : BasisState)
    (w : Wire) (hw : w ∉ ws) : xorMany ws active s w = s w := by
  induction ws generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.mem_cons, not_or] at hw
    rw [xorMany, ih _ hw.2, upd_other _ _ _ hw.1]

theorem tableXorGates_many (control : Wire) (ws : List Wire)
    (hc : control ∉ ws) (s : BasisState) :
    Classical.run (tableXorGates control ws) s = xorMany ws (s control) s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    have hcw : control ≠ w := fun h => hc (by simp [h])
    have hct : control ∉ ws := fun h => hc (by simp [h])
    simp only [tableXorGates, List.map_cons, Classical.run_cons, Classical.applyGate]
    rw [show List.map (Gate.CX control) ws = tableXorGates control ws from rfl, ih hct,
      upd_other _ _ _ hcw]
    rfl

theorem xorMany_outside (ws : List Wire) (active : Bool) (protectedWires : List Wire)
    (left right : BasisState) (h : AgreesOutside protectedWires left right) :
    AgreesOutside protectedWires (xorMany ws active left) (xorMany ws active right) := by
  induction ws generalizing left right with
  | nil => exact h
  | cons w ws ih =>
    apply ih
    intro v hv
    by_cases he : v = w
    · subst v
      simp [upd, h w hv]
    · simpa [upd, he] using h v hv

theorem logicalTree_selected (leaf : Nat → Bool → BasisState → BasisState)
    (hf : ∀ row s, leaf row false s = s) (tree : UnaryActionTree)
    (active : Bool) (route s : BasisState) :
    tree.runLogicalTree .inc leaf active route s = leaf (tree.routeLabel route) active s := by
  induction tree generalizing active s with
  | leaf row => rfl
  | node bit zero one ihz iho =>
    cases active <;> cases hr : route bit <;>
      simp [UnaryActionTree.runLogicalTree, UnaryActionTree.routeLabel, ihz, iho, hf, hr]


theorem recordTargets_mem {n base : Nat} (ports : List (RecordPort n base)) (row : Nat)
    (read : ConstantBit n → Bool) (saved : Fin base → Bool) (w : Wire)
    (hw : w ∈ recordTargets ports row read saved) : ∃ p ∈ ports, p.target = w := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
  exact ⟨p, (List.mem_filter.mp hp).1, rfl⟩

theorem recordLeaf_preserves {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (read : ConstantBit n → Bool) (saved : Fin base → Bool) (protectedWires : List Wire)
    (hs : scratch ∉ protectedWires) (ht : ∀ p ∈ ports, p.target ∉ protectedWires)
    (hst : ∀ p ∈ ports, scratch ≠ p.target) :
    UnaryLeafPreserves (fun row control => recordLeafCircuit ports scratch row control read saved) protectedWires := by
  intro row control hc s w hw
  have hn : ∀ v ∈ protectedWires, v ∉ recordTargets ports row read saved := by
    intro v hv hm
    obtain ⟨p, hp, he⟩ := recordTargets_mem ports row read saved v hm
    exact ht p hp (he.symm ▸ hv)
  rw [recordLeafCircuit_classical ports scratch row control read saved
    (fun h => hs (h ▸ hc)) (fun p hp => ⟨fun h => ht p hp (h ▸ hc), hst p hp⟩),
    tableXorGates_many control _ (hn control hc), xorMany_frame _ _ _ _ (hn w hw)]

theorem recordUnary_classical {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths)
    (ht : ∀ p ∈ ports, p.target ∉ root :: tree.indexWires.dedup ++ paths)
    (hst : ∀ p ∈ ports, scratch ≠ p.target) (s : BasisState) (hc : Clean paths s) :
    Classical.run (unaryActionUnitary .inc
      (fun row control => recordLeafCircuit ports scratch row control read saved) tree root paths) s =
      xorMany (recordTargets ports (tree.routeLabel s) read saved) (s root) s := by
  let protectedWires := root :: tree.indexWires.dedup ++ paths
  have hn : ∀ row v, v ∈ protectedWires → v ∉ recordTargets ports row read saved := by
    intro row v hv hm
    obtain ⟨p, hp, he⟩ := recordTargets_mem ports row read saved v hm
    exact ht p hp (he.symm ▸ hv)
  rw [run_unaryActionUnitary_as_runLogicalTree .inc _
    (fun row control => Classical.run (recordLeafCircuit ports scratch row control read saved))
    (fun row active => xorMany (recordTargets ports row read saved) active)
    tree root paths protectedWires s hl (by intro row control s; rfl) (by
      intro row control hcontrol state
      dsimp only
      rw [recordLeafCircuit_classical ports scratch row control read saved
        (fun h => hs (h ▸ hcontrol))
        (fun p hp => ⟨fun h => ht p hp (h ▸ hcontrol), hst p hp⟩),
        tableXorGates_many control _ (hn row control hcontrol)])
    (recordLeaf_preserves ports scratch read saved _ hs ht hst) (by
      intro row active state wire hwire
      exact xorMany_frame _ _ _ _ (hn row wire hwire)) (by
      intro row active left right h _
      exact xorMany_outside _ _ _ _ _ h) (fun _ h => h) hc,
    logicalTree_selected _ (fun row state => xorMany_false _ state)]

def basisIdeal (f : BasisState → BasisState) (phase : BasisState → ℂ) : State →ₗ[ℂ] State :=
  Finsupp.linearCombination ℂ (fun s => phase s • ket (f s))

@[simp] theorem basisIdeal_ket (f : BasisState → BasisState) (phase : BasisState → ℂ) (s : BasisState) :
    basisIdeal f phase (ket s) = phase s • ket (f s) := by simp [basisIdeal, ket]


theorem supported_smul_state {P : BasisState → Prop} {ψ : State}
    (h : SupportedOn P ψ) (z : ℂ) : SupportedOn P (z • ψ) := by
  intro s hs
  apply h s
  intro he
  apply hs
  simp [Finsupp.smul_apply, he]

theorem supported_add_state {P : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn P ψ) (hφ : SupportedOn P φ) : SupportedOn P (ψ + φ) := by
  intro s hs
  by_cases hz : ψ s = 0
  · apply hφ s
    simpa [Finsupp.add_apply, hz] using hs
  · exact hψ s hz

theorem hadamards_supported (P : BasisState → Prop) (ws : List Wire)
    (hu : ∀ s, P s → ∀ w ∈ ws, ∀ b, P (s[w ↦ b])) (s : BasisState) (hs : P s) :
    SupportedOn P (Quantum.run (ws.map Gate.H) (ket s)) := by
  induction ws generalizing s with
  | nil => exact supportedOn_ket P s hs
  | cons w ws ih =>
    simp only [List.map_cons, Quantum.run_cons, applyGate_H_ket, map_add, map_smul]
    apply supported_add_state <;> apply supported_smul_state <;> apply ih
    all_goals first | exact fun t ht v hv b => hu t ht v (by simp [hv]) b | exact hu s hs w (by simp) _

theorem equal_on_hadamards (A B : State →ₗ[ℂ] State) (ws : List Wire) (s : BasisState)
    (h : ∀ t, (∀ w, w ∉ ws → t w = s w) → A (ket t) = B (ket t)) :
    A (Quantum.run (ws.map Gate.H) (ket s)) = B (Quantum.run (ws.map Gate.H) (ket s)) := by
  induction ws generalizing s with
  | nil => exact h s (by intro w hw; rfl)
  | cons w ws ih =>
    simp only [List.map_cons, Quantum.run_cons, applyGate_H_ket, map_add, map_smul]
    have ht (b : Bool) : A (Quantum.run (ws.map Gate.H) (ket (s[w ↦ b]))) =
        B (Quantum.run (ws.map Gate.H) (ket (s[w ↦ b]))) := by
      apply ih
      intro t he
      apply h t
      intro v hv
      simp only [List.mem_cons, not_or] at hv
      rw [he v hv.2, upd_other _ _ _ hv.1]
    rw [ht false, ht true]


def phaseLookupSource {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (tree : UnaryActionTree) (root : Wire) (paths bank : List Wire) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (bank.map Gate.H) .done).seq
    ((recordLookupSource ports scratch read saved (recordUnaryOps tree root paths)).seq
      (.unitary (Circuit.adjoint (bank.map Gate.H)) .done))

def phaseLookupFactor {n base : Nat} (ports : List (RecordPort n base))
    (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) : ℂ :=
  xorPhase root (recordTargets ports (tree.routeLabel s) read saved) s

theorem phaseLookup_coherent {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (tree : UnaryActionTree) (root : Wire) (paths bank : List Wire)
    (hl : tree.Layout root paths) (hn : bank.Nodup)
    (hd : bank.Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths)
    (hp : ∀ p ∈ ports, p.target ∈ bank) (hst : ∀ p ∈ ports, scratch ≠ p.target) :
    CoherentlyImplementsOn (phaseLookupSource ports scratch read saved tree root paths bank)
      (basisIdeal id (phaseLookupFactor ports read saved tree root)) (Clean paths) := by
  let protectedWires := root :: tree.indexWires.dedup ++ paths
  have hdb : ∀ w ∈ protectedWires, w ∉ bank := by
    intro w hw hb
    exact List.disjoint_left.mp hd hb hw
  have hpt : ∀ p ∈ ports, p.target ∉ protectedWires := by
    intro p hpp h
    exact hdb p.target h (hp p hpp)
  have htargets : ∀ row, recordTargets ports row read saved ⊆ bank := by
    intro row w hw
    obtain ⟨p, hpp, he⟩ := recordTargets_mem ports row read saved w hw
    exact he ▸ hp p hpp
  have hroot : root ∉ bank := hdb root (by simp [protectedWires])
  have hq := unaryAction_coherent .inc
    (fun row control => recordLeafCircuit ports scratch row control read saved)
    tree root paths hl (recordLeaf_preserves ports scratch read saved _ hs hpt hst)
    (fun row control => recordLeafCircuit_hp ports scratch row control read saved)
  have hafter := hq.seq (CoherentlyImplementsOn.unitary
    (Circuit.adjoint (bank.map Gate.H)) (fun _ => True)) (by
      intro s hclean v hv
      trivial)
  have hbefore := (CoherentlyImplementsOn.unitary (bank.map Gate.H) (Clean paths)).seq hafter (by
    intro s hclean
    apply hadamards_supported (Clean paths) bank _ s hclean
    intro t ht w hw bit v hv
    rw [upd_other _ _ _ (by
      intro he
      subst v
      exact hdb w (by simp [protectedWires, hv]) hw)]
    exact ht v hv)
  have hsource : phaseLookupSource ports scratch read saved tree root paths bank =
      (AdaptiveCircuit.unitary (bank.map Gate.H) .done).seq
        ((unaryAction .inc (fun row control => recordLeafCircuit ports scratch row control read saved)
          tree root paths).seq (.unitary (Circuit.adjoint (bank.map Gate.H)) .done)) := by
    rw [phaseLookupSource, recordUnary_source]
  rw [hsource]
  apply hbefore.congrIdeal
  intro s hclean
  simp only [LinearMap.comp_apply, basisIdeal_ket, id_eq]
  have he : Quantum.run (unaryActionUnitary .inc
      (fun row control => recordLeafCircuit ports scratch row control read saved) tree root paths)
        (Quantum.run (bank.map Gate.H) (ket s)) =
      Quantum.run (tableXorGates root (recordTargets ports (tree.routeLabel s) read saved))
        (Quantum.run (bank.map Gate.H) (ket s)) := by
    apply equal_on_hadamards
    intro t ht
    have htclean : Clean paths t := by
      intro w hw
      rw [ht w (hdb w (by simp [protectedWires, hw]))]
      exact hclean w hw
    have hr : tree.routeLabel t = tree.routeLabel s := by
      apply tree.routeLabel_congr t s
      intro w hw
      apply ht
      exact hdb w (by simp [protectedWires, hw])
    rw [run_ket_agrees_classical _ _ (unaryActionUnitary_HPFree .inc _ tree root paths
      (fun row control => recordLeafCircuit_hp ports scratch row control read saved)),
      recordUnary_classical ports scratch read saved tree root paths hl hs hpt hst t htclean,
      hr, run_ket_agrees_classical _ _ (tableXorGates_HPFree _ _),
      tableXorGates_many root _ (fun hm => hroot (htargets _ hm))]
  rw [he, xor_hadamards_eigen root _ bank hn hroot (htargets _) s, map_smul,
    run_adjoint_run _ (by intro g hg; obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg; trivial)]
  rfl


theorem recordLeaf_tCount {n base : Nat} (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base ≤ start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((recordLeaf ports scratch row control start hb).instantiate read history).tCount = 0 := by
  induction ports generalizing history with
  | nil => rfl
  | cons p ps ih =>
    rw [recordLeaf, append_tCount_fixed _ _ _ _ _ (fun h => ih h), mixedCX_tCount]

theorem recordLeaf_slots {n base : Nat} (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base ≤ start) :
    (recordLeaf ports scratch row control start hb).gateSlots = 4 * ports.length := by
  induction ports with
  | nil => rfl
  | cons p ps ih => simp [recordLeaf, Straight.gateSlots_append, mixedCX_slots, ih]; omega

def recordT : List RecordLookupOp → Nat
  | [] => 0
  | .gates gs :: ops => ShorECDLP.tCount gs + recordT ops
  | .leaf _ _ :: ops => recordT ops
  | .erase _ _ _ :: ops => recordT ops

def recordSlots (portCount : Nat) : List RecordLookupOp → Nat
  | [] => 0
  | .gates gs :: ops => gs.length + recordSlots portCount ops
  | .leaf _ _ :: ops => 4 * portCount + recordSlots portCount ops
  | .erase _ _ _ :: ops => 3 + recordSlots portCount ops

theorem recordLookup_tCount {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (ops : List RecordLookupOp) (start : Nat) (hb : base ≤ start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((recordLookupProgram ports scratch ops start hb).instantiate read history).tCount = recordT ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
      rw [recordLookupProgram, append_tCount_fixed _ _ _ _ _ (fun h => ih _ _ h),
        literalProgram_tCount]
      rfl
    | leaf row control =>
      rw [recordLookupProgram, append_tCount_fixed _ _ _ _ _ (fun h => ih _ _ h), recordLeaf_tCount]
      simp [recordT]
    | erase a b t =>
      rw [recordLookupProgram, castFinish_instantiate,
        append_tCount_fixed _ _ _ _ _ (fun h => ih _ _ h), andEraseProgram_tCount]
      simp [recordT]

theorem recordLookup_slots {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (ops : List RecordLookupOp) (start : Nat) (hb : base ≤ start) :
    (recordLookupProgram ports scratch ops start hb).gateSlots = recordSlots ports.length ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp [recordLookupProgram, recordSlots, Straight.gateSlots_append,
        literalProgram, gateProgram_slots, ih]
    | leaf row control => simp [recordLookupProgram, recordSlots, Straight.gateSlots_append,
        recordLeaf_slots, ih]
    | erase a b t =>
      simp [recordLookupProgram, recordSlots, castFinish_gateSlots, Straight.gateSlots_append,
        ih, andEraseProgram, recordGates, controlledZ, Straight.gateSlots]

theorem recordMeasurements_append (xs ys : List RecordLookupOp) :
    recordMeasurements (xs ++ ys) = recordMeasurements xs + recordMeasurements ys := by
  induction xs with
  | nil => simp [recordMeasurements]
  | cons x xs ih => cases x <;> simp [recordMeasurements, ih, Nat.add_assoc]

theorem recordT_append (xs ys : List RecordLookupOp) : recordT (xs ++ ys) = recordT xs + recordT ys := by
  induction xs with
  | nil => simp [recordT]
  | cons x xs ih => cases x <;> simp [recordT, ih, Nat.add_assoc]

theorem recordSlots_append (k : Nat) (xs ys : List RecordLookupOp) :
    recordSlots k (xs ++ ys) = recordSlots k xs + recordSlots k ys := by
  induction xs with
  | nil => simp [recordSlots]
  | cons x xs ih => cases x <;> simp [recordSlots, ih, Nat.add_assoc]

theorem recordUnary_counts (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (k : Nat) :
    recordMeasurements (recordUnaryOps tree root paths) = tree.internalNodes ∧
      recordT (recordUnaryOps tree root paths) = 7 * tree.internalNodes ∧
      recordSlots k (recordUnaryOps tree root paths) =
        4 * k * tree.leaves + 10 * tree.internalNodes := by
  induction hl with
  | leaf row root paths hn => simp [recordUnaryOps, recordMeasurements, recordT, recordSlots,
      UnaryActionTree.internalNodes, UnaryActionTree.leaves]
  | node bit root path zero one rest hn hz ho ihz iho =>
    simp only [recordUnaryOps, recordMeasurements_append, recordT_append, recordSlots_append,
      recordMeasurements, recordT, recordSlots, ihz.1, iho.1, ihz.2.1, iho.2.1,
      ihz.2.2, iho.2.2, UnaryActionTree.internalNodes, UnaryActionTree.leaves,
      computeZeroAnd, ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      ShorECDLP.tCost, List.length_cons, List.length_nil, Nat.mul_add]
    omega


structure ClearPort (n : Nat) where
  ref : Nat → ConstantBit n
  value : Bool
  target : Wire

def phasePorts {n base : Nat} (hot : Fin 128 → Wire)
    (items : List (ClearPort n × Fin base)) : List (RecordPort n base) :=
  items.flatMap fun item => List.ofFn fun i : Fin 128 =>
    ⟨fun h => item.1.ref (128 * h + i.val), item.1.value, item.2, hot i⟩

def boolRecord (bit : Bool) : Fin 2 := if bit then 1 else 0

def boolHistory (i : Fin 2) : Bool := decide (i = 1)

def logicalPorts {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (hot : Fin 128 → Wire) : List (RecordPort n 2) :=
  phasePorts hot (data.zip (outcomes.map boolRecord))

def hotBank (hot : Fin 128 → Wire) : List Wire := List.ofFn hot

def fixupSource {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (hotPrepare low hot) .done).seq
    ((phaseLookupSource (logicalPorts data outcomes hot) scratch read boolHistory
      tree root paths (hotBank hot)).seq
      ((eraseNetworkSource (hotNetwork low hot)).seq (.unitary [.X (hot 0)] .done)))

def fixupProgram {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) :
    Straight n base (base + recordMeasurements (recordUnaryOps tree root paths) + 127) :=
  (literalProgram (hotPrepare low hot)).append
    ((literalProgram ((hotBank hot).map Gate.H)).append
      ((recordLookupProgram (phasePorts hot (data.zip refs)) scratch
        (recordUnaryOps tree root paths) base (Nat.le_refl base)).append
        ((literalProgram (Circuit.adjoint ((hotBank hot).map Gate.H))).append
          (castFinish (by simp [hotNetwork_length])
            ((eraseNetwork n (hotNetwork low hot)
              (base + recordMeasurements (recordUnaryOps tree root paths))).append
              (literalProgram [.X (hot 0)]))))))

/-- Record references are submitted data; only the protected evaluator reads them. -/
def measureThen {n R : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor + R)) :
    (wires : List Wire) → (start : Nat) → List (Fin start) → Straight n start (start + wires.length + R)
  | [], start, refs => next start refs
  | w :: ws, start, refs => castFinish (by simp; omega)
      (.measure w (measureThen next ws (start + 1) (refs.map Fin.castSucc ++ [Fin.last start])))

def measuredClear {n : Nat} (data : List (ClearPort n)) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    Straight n start (start + data.length + (recordMeasurements (recordUnaryOps tree root paths) + 127)) :=
  castFinish (by simp) (measureThen (R := recordMeasurements (recordUnaryOps tree root paths) + 127)
    (fun cursor refs => castFinish (by omega) (fixupProgram data refs low hot tree root scratch paths))
    (data.map ClearPort.target) start ([] : List (Fin start)))

def LoadedClear {n : Nat} (data : List (ClearPort n)) (read : ConstantBit n → Bool)
    (low : Fin 7 → Wire) (tree : UnaryActionTree) (root : Wire) (s : BasisState) : Prop :=
  ∀ p ∈ data, s p.target = (s root && decide (read (p.ref (128 * tree.routeLabel s + hotAddress low s)) = p.value))


theorem phasePorts_targets {n base : Nat} (hot : Fin 128 → Wire)
    (items : List (ClearPort n × Fin base)) :
    ∀ p ∈ phasePorts hot items, p.target ∈ hotBank hot := by
  intro p hp
  obtain ⟨item, _, hi⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem splitNetwork_hp (cs : List SplitCell) : Classical.HPFree (splitNetwork cs) := by
  induction cs with
  | nil => simp [splitNetwork]
  | cons c cs ih => simp [splitNetwork, SplitCell.circuit, splitCircuit, ih]

theorem hotPrepare_hp (low : Fin 7 → Wire) (hot : Fin 128 → Wire) :
    Classical.HPFree (hotPrepare low hot) := by
  simp [hotPrepare, splitNetwork_hp]

def fixupFactor {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) : ℂ :=
  phaseLookupFactor (logicalPorts data outcomes hot) read boolHistory tree root
    (Classical.run (hotPrepare low hot) s)

theorem classical_x_twice (w : Wire) (s : BasisState) :
    Classical.run [.X w] (Classical.run [.X w] s) = s := by
  funext v
  by_cases hv : v = w <;> simp_all [Classical.run, Classical.applyGate, upd]

theorem fixupSource_coherent {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot)
    (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths)
    (hshot : scratch ∉ hotBank hot) :
    CoherentlyImplementsOn (fixupSource data outcomes read low hot tree root scratch paths)
      (basisIdeal id (fixupFactor data outcomes read low hot tree root))
      (fun s => HotClean hot s ∧ Clean paths s) := by
  have hp := phasePorts_targets hot (data.zip (outcomes.map boolRecord))
  have htarget : ∀ p ∈ logicalPorts data outcomes hot, scratch ≠ p.target := by
    intro p hpp he
    exact hshot (he.symm ▸ hp p hpp)
  have hq := phaseLookup_coherent (logicalPorts data outcomes hot) scratch read boolHistory
    tree root paths (hotBank hot) hl (List.nodup_ofFn.mpr hi) hbank hs hp htarget
  have hpre := (CoherentlyImplementsOn.unitary (hotPrepare low hot)
    (fun s => HotClean hot s ∧ Clean paths s)).seq hq (by
      intro s hvalid
      rw [run_ket_agrees_classical _ _ (hotPrepare_hp low hot)]
      apply supportedOn_ket
      intro w hw
      rw [hotPrepare_frame low hot s w (by
        intro i he
        exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) (by simp [hw]))]
      exact hvalid.2 w hw)
  have hn := eraseNetwork_coherent (hotNetwork low hot) (hotNetwork_physical low hot hi hdlow)
  have hpost := hn.seq (CoherentlyImplementsOn.unitary [.X (hot 0)] (fun _ => True)) (by
    intro s hvalid v hv
    trivial)
  have htotal := hpre.seq hpost (by
    intro s hvalid
    simp only [LinearMap.comp_apply]
    rw [run_ket_agrees_classical _ _ (hotPrepare_hp low hot), basisIdeal_ket]
    apply supported_smul_state
    apply supportedOn_ket
    exact ⟨Classical.run [.X (hot 0)] s, hotNetwork_ready low hot hi hdlow s hvalid.1,
      by simp [hotPrepare]⟩)
  rw [fixupSource, ← adaptive_seq_assoc]
  apply htotal.congrIdeal
  intro s hvalid
  simp only [LinearMap.comp_apply]
  rw [run_ket_agrees_classical _ _ (hotPrepare_hp low hot), basisIdeal_ket]
  simp only [map_smul, id_eq]
  rw [run_ket_agrees_classical _ _ (inverseNetwork_hp (hotNetwork low hot))]
  rw [hotPrepare, Classical.run_append,
    inverseNetwork_correct (hotNetwork low hot) (hotNetwork_physical low hot hi hdlow) _
      (hotNetwork_ready low hot hi hdlow s hvalid.1),
    run_ket_agrees_classical _ _ (by simp), classical_x_twice]
  simp only [basisIdeal_ket, id_eq]
  rfl


@[simp] theorem boolHistory_record (b : Bool) : boolHistory (boolRecord b) = b := by cases b <;> rfl

theorem recordTargets_append {n base : Nat} (xs ys : List (RecordPort n base))
    (row : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) :
    recordTargets (xs ++ ys) row read saved = recordTargets xs row read saved ++ recordTargets ys row read saved := by
  simp [recordTargets]

theorem xorPhase_append (root : Wire) (xs ys : List Wire) (s : BasisState) :
    xorPhase root (xs ++ ys) s = xorPhase root xs s * xorPhase root ys s := by simp [xorPhase]

theorem xorPhase_recordTargets {n base : Nat} (ports : List (RecordPort n base))
    (row root : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) (s : BasisState) :
    xorPhase root (recordTargets ports row read saved) s =
      (ports.map fun p => if decide (read (p.ref row) = p.value) && saved p.record then
        (if s root && s p.target then (-1 : ℂ) else 1) else 1).prod := by
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    by_cases ht : read (p.ref row) = p.value <;> cases hr : saved p.record <;>
      simp_all [recordTargets, xorPhase]

theorem phasePorts_block (p : ClearPort n) (m : Bool) (hot : Fin 128 → Wire)
    (read : ConstantBit n → Bool) (row root : Nat) (s : BasisState) (selected : Fin 128)
    (hm : ∀ i, s (hot i) = decide (i = selected)) :
    xorPhase root (recordTargets (phasePorts hot ([(p, boolRecord m)])) row read boolHistory) s =
      if m && (s root && decide (read (p.ref (128 * row + selected.val)) = p.value)) then (-1 : ℂ) else 1 := by
  rw [xorPhase_recordTargets]
  simp only [phasePorts, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_ofFn,
    List.prod_ofFn, Function.comp_def]
  rw [Finset.prod_eq_single selected]
  · rw [hm selected]
    cases hm0 : m <;> cases hr : s root <;>
      by_cases hrd : read (p.ref (12128 * row + selected.val)) = p.value <;>
      simp [boolHistory, boolRecord]
  · intro i _ hi
    rw [hm i]
    simp [hi]
  · simp

theorem logicalPorts_cons (p : ClearPort n) (ps : List (ClearPort n)) (m : Bool)
    (ms : List Bool) (hot : Fin 128 → Wire) :
    logicalPorts (p :: ps) (m :: ms) hot = phasePorts hot ([(p, boolRecord m)]) ++ logicalPorts ps ms hot := by
  simp [logicalPorts, phasePorts]

theorem phaseFactor_loaded {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (hot : Fin 128 → Wire) (tree : UnaryActionTree) (root : Wire)
    (original prepared : BasisState) (selected : Fin 128)
    (hm : ∀ i, prepared (hot i) = decide (i = selected))
    (hw : ∀ p ∈ data, original p.target =
      (prepared root && decide (read (p.ref (128 * tree.routeLabel prepared + selected.val)) = p.value))) :
    phaseLookupFactor (logicalPorts data outcomes hot) read boolHistory tree root prepared =
      registerXPhase (data.map ClearPort.target) outcomes original := by
  unfold phaseLookupFactor
  induction data generalizing outcomes with
  | nil => simp [logicalPorts, phasePorts, recordTargets, xorPhase, registerXPhase]
  | cons p ps ih =>
    cases outcomes with
    | nil => simp [logicalPorts, phasePorts, recordTargets, xorPhase, registerXPhase]
    | cons m ms =>
      rw [logicalPorts_cons, recordTargets_append, xorPhase_append, phasePorts_block p m hot read _ root prepared selected hm,
        ih ms (fun q hq => hw q (by simp [hq]))]
      simp only [List.map_cons, registerXPhase, hw p (by simp)]

theorem measureThen_run {n R : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor + R))
    (source : List Bool → AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hn : ∀ cursor refs history, ((next cursor refs).instantiate read history).run = (source (refs.map history)).run)
    (wires : List Wire) (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((measureThen next wires start refs).instantiate read history).run =
      (measureResetThen wires (fun outcomes => source (refs.map history ++ outcomes))).run := by
  induction wires generalizing start with
  | nil => simpa [measureThen, measureResetThen] using hn start refs history
  | cons w ws ih =>
    simp only [measureThen, castFinish_instantiate, Straight.instantiate, measureResetThen, AdaptiveCircuit.run]
    rw [ih, ih]
    have hm (bit : Bool) :
        (refs.map Fin.castSucc ++ [Fin.last start]).map (Fin.lastCases bit history) = refs.map history ++ [bit] := by
      simp [List.map_map, Fin.lastCases_castSucc, Fin.lastCases_last]
    simp only [hm, List.append_assoc, List.singleton_append]


theorem flatMap_ofFn_congr {α β γ : Type} : ∀ {k : Nat} (F : α → List γ) (G : β → List γ)
    (A : Fin k → α) (B : Fin k → β), (∀ i, F (A i) = G (B i)) →
    (List.ofFn A).flatMap F = (List.ofFn B).flatMap G
  | 0, _, _, _, _, _ => by simp
  | k+1, F, G, A, B, h => by
    simp only [List.ofFn_succ, List.flatMap_cons]
    rw [h 0, flatMap_ofFn_congr F G (fun i => A i.succ) (fun i => B i.succ) (fun i => h i.succ)]

theorem phasePorts_cons {n base : Nat} (hot : Fin 128 → Wire)
    (item : ClearPort n × Fin base) (items : List (ClearPort n × Fin base)) :
    phasePorts hot (item :: items) = phasePorts hot ([item]) ++ phasePorts hot items := by simp [phasePorts]

theorem recordLeafCircuit_append {n base : Nat} (xs ys : List (RecordPort n base))
    (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) :
    recordLeafCircuit (xs ++ ys) scratch row control read saved =
      recordLeafCircuit xs scratch row control read saved ++ recordLeafCircuit ys scratch row control read saved := by
  simp [recordLeafCircuit]

theorem phasePorts_resolve {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 128 → Wire) (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) :
    recordLeafCircuit (phasePorts hot (data.zip refs)) scratch row control read saved =
      recordLeafCircuit (logicalPorts data (refs.map saved) hot) scratch row control read boolHistory := by
  induction data generalizing refs with
  | nil => rfl
  | cons p ps ih =>
    cases refs with
    | nil => rfl
    | cons r rs =>
      simp only [List.zip_cons_cons, List.map_cons]
      rw [phasePorts_cons, logicalPorts_cons, recordLeafCircuit_append, recordLeafCircuit_append]
      rw [ih rs]
      congr 1
      simp only [phasePorts, List.flatMap_cons, List.flatMap_nil, List.append_nil, recordLeafCircuit]
      apply flatMap_ofFn_congr
      intro i
      cases hm : saved r <;> simp [boolRecord, boolHistory]

theorem recordSource_resolve {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 128 → Wire) (scratch : Wire) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (ops : List RecordLookupOp) :
    recordLookupSource (phasePorts hot (data.zip refs)) scratch read saved ops =
      recordLookupSource (logicalPorts data (refs.map saved) hot) scratch read boolHistory ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [recordLookupSource, ih]
    | leaf row control => simp only [recordLookupSource, phasePorts_resolve, ih]
    | erase a b t => simp only [recordLookupSource, ih]

theorem unitary_run_congr (gs : Circuit) {p q : AdaptiveCircuit} (h : p.run = q.run) :
    (AdaptiveCircuit.unitary gs p).run = (AdaptiveCircuit.unitary gs q).run := by
  simp only [AdaptiveCircuit.run, h]

theorem fixupProgram_run {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (history : Fin base → Bool) :
    ((fixupProgram data refs low hot tree root scratch paths).instantiate read history).run =
      (fixupSource data (refs.map history) read low hot tree root scratch paths).run := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).run =
      ((eraseNetworkSource (hotNetwork low hot)).seq (.unitary [.X (hot 0)] .done)).run := by
    rw [append_run_fixed _ _ _ _ _ (fun h => literalProgram_run [.X (hot 0)] read h),
      AdaptiveCircuit.run_seq, eraseNetwork_source, ← AdaptiveCircuit.run_seq]
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank hot).map Gate.H))).append
        (castFinish (f := cursor + 127) (by simp [hotNetwork_length])
          ((eraseNetwork n (hotNetwork low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).run =
      (AdaptiveCircuit.unitary (Circuit.adjoint ((hotBank hot).map Gate.H))
        ((eraseNetworkSource (hotNetwork low hot)).seq (.unitary [.X (hot 0)] .done))).run := by
    rw [literalProgram_append_run]
    apply unitary_run_congr
    rw [castFinish_instantiate, hpost]
  have hsource : fixupSource data (refs.map history) read low hot tree root scratch paths =
      .unitary (hotPrepare low hot) (.unitary ((hotBank hot).map Gate.H)
        ((recordLookupSource (logicalPorts data (refs.map history) hot) scratch read boolHistory
          (recordUnaryOps tree root paths)).seq
          (.unitary (Circuit.adjoint ((hotBank hot).map Gate.H))
            ((eraseNetworkSource (hotNetwork low hot)).seq (.unitary [.X (hot 0)] .done))))) := by
    simp only [fixupSource, phaseLookupSource, adaptive_seq_assoc, AdaptiveCircuit.seq]
  rw [hsource, fixupProgram, literalProgram_append_run]
  apply unitary_run_congr
  rw [literalProgram_append_run]
  apply unitary_run_congr
  rw [append_run_fixed _ _ _ _ _ (fun h => htail _ h),
    AdaptiveCircuit.run_seq, recordLookup_run]
  have hh : historyPrefix (Nat.le_refl base) history = history := rfl
  rw [hh, recordSource_resolve, ← AdaptiveCircuit.run_seq]

theorem measuredClear_run {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear data low hot tree root scratch paths start).instantiate read history).run =
      (measureResetThen (data.map ClearPort.target)
        (fun outcomes => fixupSource data outcomes read low hot tree root scratch paths)).run := by
  rw [measuredClear, castFinish_instantiate,
    measureThen_run _ (fun outcomes => fixupSource data outcomes read low hot tree root scratch paths) read
      (by intro cursor refs h; rw [castFinish_instantiate, fixupProgram_run])]
  rfl


theorem splitNetwork_wellFormed (cs : List SplitCell) (hp : ∀ c ∈ cs, c.Physical) :
    CircuitWellFormed (splitNetwork cs) := by
  induction cs with
  | nil => simp [splitNetwork, CircuitWellFormed]
  | cons c cs ih =>
    have hc := hp c (by simp)
    simp only [splitNetwork, circuitWellFormed_append]
    exact ⟨by simp [SplitCell.circuit, splitCircuit, CircuitWellFormed, Gate.WellFormed, hc.1, hc.2.1, hc.2.2,
      Ne.symm hc.2.2], ih (fun d hd => hp d (by simp [hd]))⟩

theorem eraseNetworkSource_wellFormed (cs : List SplitCell) (hp : ∀ c ∈ cs, c.Physical) :
    (eraseNetworkSource cs).WellFormed := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    have hc := hp c (by simp)
    apply (ih (fun d hd => hp d (by simp [hd]))).seq
    apply AdaptiveCircuit.WellFormed.seq
    · exact ⟨by simpa [CircuitWellFormed, Gate.WellFormed] using Ne.symm hc.2.2, trivial⟩
    · exact measuredAndErase_wellFormed c.bit c.parent c.child hc.1

theorem recordLeafCircuit_wellFormed {n base : Nat} (ports : List (RecordPort n base))
    (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (hc : control ≠ scratch) (ht : ∀ p ∈ ports, scratch ≠ p.target) :
    CircuitWellFormed (recordLeafCircuit ports scratch row control read saved) := by
  induction ports with
  | nil => simp [recordLeafCircuit, CircuitWellFormed]
  | cons p ps ih =>
    simp only [recordLeafCircuit, List.flatMap_cons, circuitWellFormed_append]
    refine ⟨?_, ih (fun q hq => ht q (by simp [hq]))⟩
    cases decide (read (p.ref row) = p.value) <;> cases saved p.record <;>
      simp [mixedCircuit, CircuitWellFormed, Gate.WellFormed, hc, ht p (by simp)]

theorem phaseLookupSource_wellFormed {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (tree : UnaryActionTree) (root : Wire) (paths bank : List Wire) (hl : tree.Layout root paths)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths)
    (ht : ∀ p ∈ ports, scratch ≠ p.target) :
    (phaseLookupSource ports scratch read saved tree root paths bank).WellFormed := by
  have hH : CircuitWellFormed (bank.map Gate.H) := by
    intro g hg
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
    trivial
  rw [phaseLookupSource, recordUnary_source]
  apply AdaptiveCircuit.WellFormed.seq
  · exact ⟨hH, trivial⟩
  · apply AdaptiveCircuit.WellFormed.seq
    · apply unaryAction_wellFormed .inc _ tree root paths hl
      intro row _ control hc
      exact recordLeafCircuit_wellFormed ports scratch row control read saved
        (fun he => hs (he ▸ hc)) ht
    · exact ⟨(circuitWellFormed_adjoint _).mpr hH, trivial⟩

theorem fixupSource_wellFormed {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank hot) :
    (fixupSource data outcomes read low hot tree root scratch paths).WellFormed := by
  rw [fixupSource]
  apply AdaptiveCircuit.WellFormed.seq
  · refine ⟨?_, trivial⟩
    rw [hotPrepare, circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed, Gate.WellFormed],
      splitNetwork_wellFormed _ (hotNetwork_physical low hot hi hdlow)⟩
  · apply AdaptiveCircuit.WellFormed.seq
    · apply phaseLookupSource_wellFormed _ _ _ _ _ _ _ _ hl hs
      intro p hp he
      exact hshot (he.symm ▸ phasePorts_targets hot _ p hp)
    · apply AdaptiveCircuit.WellFormed.seq
      · exact eraseNetworkSource_wellFormed _ (hotNetwork_physical low hot hi hdlow)
      · exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], trivial⟩

theorem clearRegister_frame (ws : List Wire) (s : BasisState) (w : Wire) (hw : w ∉ ws) :
    clearRegister ws s w = s w := by
  induction ws generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.mem_cons, not_or] at hw
    rw [clearRegister, ih _ hw.2, upd_other _ _ _ hw.1]




theorem eraseNetwork_tCount (n : Nat) (cs : List SplitCell) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((eraseNetwork n cs start).instantiate read history).tCount = 0 := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [eraseNetwork, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => eraseSplit_tCount n _ c.bit c.parent c.child read h), ih]

theorem eraseNetwork_slots (n : Nat) (cs : List SplitCell) (start : Nat) :
    (eraseNetwork n cs start).gateSlots = 4 * cs.length := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simp only [eraseNetwork, castFinish_gateSlots, Straight.gateSlots_append, ih, eraseSplit_slots, List.length_cons]
    omega

theorem hadamards_tCount (ws : List Wire) : ShorECDLP.tCount (ws.map Gate.H) = 0 := by
  simp [ShorECDLP.tCount, List.map_map, Function.comp_def, ShorECDLP.tCost]

theorem splitNetwork_tCount (cs : List SplitCell) : ShorECDLP.tCount (splitNetwork cs) = 7 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [splitNetwork, ShorECDLP.tCount_append, ih, SplitCell.circuit, splitCircuit_tCount, List.length_cons]
    ring

theorem splitNetwork_length (cs : List SplitCell) : (splitNetwork cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [splitNetwork, List.length_append, ih, SplitCell.circuit, splitCircuit_slots, List.length_cons]
    ring

theorem hotPrepare_tCount (low : Fin 7 → Wire) (hot : Fin 128 → Wire) :
    ShorECDLP.tCount (hotPrepare low hot) = 889 := by
  rw [hotPrepare, ShorECDLP.tCount_append, splitNetwork_tCount, hotNetwork_length]
  rfl

theorem hotPrepare_length (low : Fin 7 → Wire) (hot : Fin 128 → Wire) :
    (hotPrepare low hot).length = 255 := by
  rw [hotPrepare, List.length_append, splitNetwork_length, hotNetwork_length]
  rfl

theorem phasePorts_length {n base : Nat} (hot : Fin 128 → Wire) (items : List (ClearPort n × Fin base)) :
    (phasePorts hot items).length = 128 * items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rw [phasePorts_cons, List.length_append, ih]
    simp only [phasePorts, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.length_ofFn, List.length_nil, List.length_cons]
    omega

theorem fixupProgram_tCount {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (history : Fin base → Bool) :
    ((fixupProgram data refs low hot tree root scratch paths).instantiate read history).tCount =
      7 * tree.internalNodes + 889 := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).tCount = 0 := by
    rw [append_tCount_fixed _ _ _ _ _ (fun h => literalProgram_tCount [.X (hot 0)] read h), eraseNetwork_tCount]
    rfl
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank hot).map Gate.H))).append
        (castFinish (f := cursor + 127) (by simp [hotNetwork_length])
          ((eraseNetwork n (hotNetwork low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).tCount = 0 := by
    rw [literalProgram_append_tCount, castFinish_instantiate, hpost, ShorECDLP.tCount_adjoint, hadamards_tCount]
  simp only [fixupProgram, literalProgram_append_tCount]
  rw [append_tCount_fixed _ _ _ _ _ (fun h => htail _ h), recordLookup_tCount,
    (recordUnary_counts tree root paths hl 0).2.1, hotPrepare_tCount, hadamards_tCount]
  omega

theorem measureThen_tCount {n R t : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor + R))
    (read : ConstantBit n → Bool)
    (hn : ∀ cursor refs history, ((next cursor refs).instantiate read history).tCount = t)
    (wires : List Wire) (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((measureThen next wires start refs).instantiate read history).tCount = t := by
  induction wires generalizing start with
  | nil => exact hn start refs history
  | cons w ws ih =>
    simp only [measureThen, castFinish_instantiate, Straight.instantiate, AdaptiveCircuit.tCount, ih, max_self]

theorem measuredClear_tCount {n : Nat} (data : List (ClearPort n))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear data low hot tree root scratch paths start).instantiate read history).tCount =
      7 * (tree.internalNodes + 127) := by
  rw [measuredClear, castFinish_instantiate, measureThen_tCount _ read (by
    intro cursor refs h
    rw [castFinish_instantiate, fixupProgram_tCount data refs low hot tree root scratch paths hl])]
  omega


theorem fixupProgram_slots {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) :
    (fixupProgram data refs low hot tree root scratch paths).gateSlots =
      512 * min data.length refs.length * tree.leaves + 10 * tree.internalNodes + 1020 := by
  simp only [fixupProgram, Straight.gateSlots_append, literalProgram_slots, castFinish_gateSlots]
  rw [recordLookup_slots, (recordUnary_counts tree root paths hl _).2.2, eraseNetwork_slots]
  simp only [phasePorts_length, List.length_zip, hotPrepare_length, hotBank,
    List.length_ofFn, List.length_map, Circuit.adjoint, List.length_reverse,
    hotNetwork_length, List.length_cons, List.length_nil]
  ring

theorem measureThen_slots {n R : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor + R))
    (f : Nat → Nat) (hn : ∀ cursor refs, (next cursor refs).gateSlots = f refs.length)
    (wires : List Wire) (start : Nat) (refs : List (Fin start)) :
    (measureThen next wires start refs).gateSlots = f (refs.length + wires.length) := by
  induction wires generalizing start with
  | nil => simpa [measureThen] using hn start refs
  | cons w ws ih =>
    simp only [measureThen, castFinish_gateSlots, Straight.gateSlots, ih,
      List.length_append, List.length_map, List.length_cons, List.length_nil]
    congr 1
    omega

theorem measuredClear_slots {n : Nat} (data : List (ClearPort n))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) (start : Nat) :
    (measuredClear data low hot tree root scratch paths start).gateSlots =
      512 * data.length * tree.leaves + 10 * tree.internalNodes + 1020 := by
  rw [measuredClear, castFinish_gateSlots, measureThen_slots _
    (fun k => 512 * min data.length k * tree.leaves + 10 * tree.internalNodes + 1020)
    (by intro cursor refs; rw [castFinish_gateSlots, fixupProgram_slots data refs low hot tree root scratch paths hl])]
  simp


theorem circuitWires_append (xs ys : Circuit) :
    circuitWires (xs ++ ys) = circuitWires xs ++ circuitWires ys := by simp [circuitWires]






theorem static_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    NaiveChallenge.straightWires (p.append q) =
      NaiveChallenge.straightWires p ++ NaiveChallenge.straightWires q := by
  induction p with
  | done => rfl
  | gate g next ih => simp [Straight.append, NaiveChallenge.straightWires, ih, List.append_assoc]
  | recordGate _ _ _ next ih => simp [Straight.append, NaiveChallenge.straightWires, ih, List.append_assoc]
  | measure _ next ih => simp [Straight.append, NaiveChallenge.straightWires, ih]

theorem static_cast {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    NaiveChallenge.straightWires (castFinish h p) = NaiveChallenge.straightWires p := by subst f; rfl

theorem literal_static {n s : Nat} (gs : Circuit) :
    NaiveChallenge.straightWires (literalProgram (n := n) (s := s) gs) = circuitWires gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa [literalProgram, gateProgram, NaiveChallenge.straightWires,
      NaiveChallenge.slotGate, circuitWires] using congrArg (List.append (gateWires g)) ih


def recordWireList {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire) :
    List RecordLookupOp → List Wire
  | [] => []
  | .gates gs :: ops => circuitWires gs ++ recordWireList ports scratch ops
  | .leaf _ control :: ops =>
      (ports.flatMap fun p => [control, scratch, scratch, p.target, control, scratch, scratch, p.target]) ++
        recordWireList ports scratch ops
  | .erase a b t :: ops => [t, b, a, b, b] ++ recordWireList ports scratch ops

theorem recordLeaf_static {n base : Nat} (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base ≤ start) :
    NaiveChallenge.straightWires (recordLeaf ports scratch row control start hb) =
      ports.flatMap (fun p => [control, scratch, scratch, p.target, control, scratch, scratch, p.target]) := by
  induction ports with
  | nil => rfl
  | cons p ps ih => simp [recordLeaf, static_append, mixedCX_support, ih]

theorem recordLookup_static {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (ops : List RecordLookupOp) (start : Nat) (hb : base ≤ start) :
    NaiveChallenge.straightWires (recordLookupProgram ports scratch ops start hb) = recordWireList ports scratch ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp [recordLookupProgram, static_append, literal_static, ih, recordWireList]
    | leaf row control => simp [recordLookupProgram, static_append, recordLeaf_static, ih, recordWireList]
    | erase a b t => simp [recordLookupProgram, static_cast, static_append, ih, recordWireList,
        andEraseProgram, recordGates, controlledZ, NaiveChallenge.straightWires, gateWires]

def RecordOpWithin {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (support : List Wire) : RecordLookupOp → Prop
  | .gates gs => circuitWires gs ⊆ support
  | .leaf _ control => control ∈ support ∧ scratch ∈ support ∧ ∀ p ∈ ports, p.target ∈ support
  | .erase a b t => a ∈ support ∧ b ∈ support ∧ t ∈ support

theorem recordWireList_within {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (ops : List RecordLookupOp) (support : List Wire)
    (hp : ∀ op ∈ ops, RecordOpWithin ports scratch support op) : recordWireList ports scratch ops ⊆ support := by
  induction ops with
  | nil => simp [recordWireList]
  | cons op ops ih =>
    have ht := ih (fun o ho => hp o (by simp [ho]))
    have hh := hp op (by simp)
    cases op with
    | gates gs => exact List.append_subset.mpr ⟨hh, ht⟩
    | leaf row control =>
      apply List.append_subset.mpr
      refine ⟨?_, ht⟩
      intro w hw
      obtain ⟨p, hpp, hw⟩ := List.mem_flatMap.mp hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hh.1 | exact hh.2.1 | exact hh.2.2 p hpp
    | erase a b t =>
      apply List.append_subset.mpr
      refine ⟨?_, ht⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hh.1 | exact hh.2.1 | exact hh.2.2

theorem recordUnary_within {n base : Nat} (ports : List (RecordPort n base)) (scratch : Wire)
    (tree : UnaryActionTree) (root : Wire) (paths support : List Wire)
    (hr : root ∈ support) (hs : scratch ∈ support)
    (hi : tree.indexWires ⊆ support) (ha : paths ⊆ support)
    (hp : ∀ p ∈ ports, p.target ∈ support) :
    ∀ op ∈ recordUnaryOps tree root paths, RecordOpWithin ports scratch support op := by
  induction tree generalizing root paths with
  | leaf row => simpa [recordUnaryOps, RecordOpWithin] using
      (⟨hr, hs, hp⟩ : root ∈ support ∧ scratch ∈ support ∧ ∀ p ∈ ports, p.target ∈ support)
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp [recordUnaryOps]
    | cons path rest =>
      have hbit : bit ∈ support := hi (by simp [UnaryActionTree.indexWires])
      have hpath : path ∈ support := ha (by simp)
      have hrest : rest ⊆ support := fun w hw => ha (by simp [hw])
      have hz := ihz path rest hpath (fun w hw => hi (by simp [UnaryActionTree.indexWires, hw])) hrest
      have ho := iho path rest hpath (fun w hw => hi (by simp [UnaryActionTree.indexWires, hw])) hrest
      have hc : RecordOpWithin ports scratch support (.gates (computeZeroAnd root bit path)) := by
        intro w hw
        simp [computeZeroAnd, circuitWires, gateWires] at hw
        aesop
      have hcx : RecordOpWithin ports scratch support (.gates [.CX root path]) := by
        intro w hw
        simp [circuitWires, gateWires] at hw
        aesop
      have hx : RecordOpWithin ports scratch support (.gates [.X bit]) := by
        intro w hw
        have he : w = bit := by simpa [circuitWires, gateWires] using hw
        exact he.symm ▸ hbit
      have he : RecordOpWithin ports scratch support (.erase root bit path) := ⟨hr, hbit, hpath⟩
      simp only [recordUnaryOps, List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies]
      exact ⟨⟨⟨⟨⟨hc, fun _ => trivial⟩, hz⟩, ⟨hcx, fun _ => trivial⟩⟩, ho⟩, hcx, hx, he, hx, fun _ => trivial⟩

def clearSupport {n : Nat} (data : List (ClearPort n)) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire) : List Wire :=
  data.map ClearPort.target ++ List.ofFn low ++ hotBank hot ++ (root :: tree.indexWires.dedup ++ paths)


theorem static_within_append {n a b c : Nat} {p : Straight n a b} {q : Straight n b c} {S : List Wire}
    (hp : NaiveChallenge.straightWires p ⊆ S) (hq : NaiveChallenge.straightWires q ⊆ S) :
    NaiveChallenge.straightWires (p.append q) ⊆ S := by rw [static_append]; exact List.append_subset.mpr ⟨hp, hq⟩

theorem splitNetwork_within (cs : List SplitCell) (S : List Wire)
    (hp : ∀ c ∈ cs, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S) : circuitWires (splitNetwork cs) ⊆ S := by
  induction cs with
  | nil => simp [splitNetwork, circuitWires]
  | cons c cs ih =>
    have hc := hp c (by simp)
    rw [splitNetwork, circuitWires_append]
    apply List.append_subset.mpr
    refine ⟨?_, ih (fun d hd => hp d (by simp [hd]))⟩
    intro w hw
    simp [SplitCell.circuit, splitCircuit, circuitWires, gateWires] at hw
    aesop

theorem hotNetwork_within (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) :
    ∀ c ∈ hotNetwork low hot, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S := by
  intro c hc
  obtain ⟨j, x, y, rfl, _⟩ := mem_hotNetwork low hot c hc
  exact ⟨hl _, hh _, hh _⟩

theorem hotPrepare_within (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) : circuitWires (hotPrepare low hot) ⊆ S := by
  rw [hotPrepare, circuitWires_append]
  exact List.append_subset.mpr ⟨by simpa [circuitWires, gateWires] using hh 0,
    splitNetwork_within _ S (hotNetwork_within low hot S hl hh)⟩

theorem hadamards_wires (ws : List Wire) : circuitWires (ws.map Gate.H) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [circuitWires, gateWires] using congrArg (List.cons w) ih

theorem hadamards_adjoint_wires (ws : List Wire) :
    circuitWires (Circuit.adjoint (ws.map Gate.H)) = ws.reverse := by
  simp only [Circuit.adjoint, List.map_reverse, List.map_map, Function.comp_def, Gate.adjoint]
  rw [← List.map_reverse]
  exact hadamards_wires ws.reverse

theorem eraseNetwork_within (n : Nat) (cs : List SplitCell) (start : Nat) (S : List Wire)
    (hp : ∀ c ∈ cs, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S) :
    NaiveChallenge.straightWires (eraseNetwork n cs start) ⊆ S := by
  induction cs generalizing start with
  | nil => simp [eraseNetwork, NaiveChallenge.straightWires]
  | cons c cs ih =>
    have hc := hp c (by simp)
    rw [eraseNetwork, static_cast]
    apply static_within_append (ih _ (fun d hd => hp d (by simp [hd])))
    rw [eraseSplit_support]
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    aesop

theorem fixupProgram_within {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths S : List Wire)
    (hr : root ∈ S) (hs : scratch ∈ S) (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S)
    (hi : tree.indexWires ⊆ S) (ha : paths ⊆ S) :
    NaiveChallenge.straightWires (fixupProgram data refs low hot tree root scratch paths) ⊆ S := by
  have hb : hotBank hot ⊆ S := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact hh i
  unfold fixupProgram
  apply static_within_append
  · rw [literal_static]
    exact hotPrepare_within low hot S hl hh
  · apply static_within_append
    · rw [literal_static, hadamards_wires]
      exact hb
    · apply static_within_append
      · rw [recordLookup_static]
        apply recordWireList_within
        exact recordUnary_within _ scratch tree root paths S hr hs hi ha
          (fun p hp => hb (phasePorts_targets hot _ p hp))
      · apply static_within_append
        · rw [literal_static, hadamards_adjoint_wires]
          intro w hw
          exact hb (List.mem_reverse.mp hw)
        · rw [static_cast]
          apply static_within_append (eraseNetwork_within n _ _ S (hotNetwork_within low hot S hl hh))
          rw [literal_static]
          simpa [circuitWires, gateWires] using hh 0

theorem measureThen_within {n R : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor + R))
    (S : List Wire) (hn : ∀ cursor refs, NaiveChallenge.straightWires (next cursor refs) ⊆ S)
    (wires : List Wire) (start : Nat) (refs : List (Fin start)) (hw : wires ⊆ S) :
    NaiveChallenge.straightWires (measureThen next wires start refs) ⊆ S := by
  induction wires generalizing start with
  | nil => exact hn start refs
  | cons w ws ih =>
    rw [measureThen, static_cast]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hw (by simp)
    · exact ih _ _ (fun t ht => hw (by simp [ht])) hv

















theorem addressTree_leaves (bits : List Wire) (base stride : Nat) :
    (tableAddressTree bits base stride).leaves = 2 ^ bits.length := by
  induction bits generalizing base stride with
  | nil => rfl
  | cons bit bits ih =>
    simp only [tableAddressTree, UnaryActionTree.leaves, ih, List.length_cons, pow_succ]
    omega



/-- The generic row reference is exactly the physical little-endian address. -/
theorem splitAddress_value (low : Fin 7 → Wire) (high : List Wire) (s : BasisState) :
    128 * (tableAddressTree high 0 1).routeLabel s + hotAddress low s =
      tableAddressValue ([lowN low 0, lowN low 1, lowN low 2, lowN low 3, lowN low 4, lowN low 5,
        lowN low 6] ++ high) s := by
  simp only [tableAddressTree_route, zero_add, one_mul, List.cons_append, List.nil_append,
    tableAddressValue, hotAddress, addrN]
  ring


end
end ShorECDLP.Entrant.MeasuredClear


namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
/-- The measured data bank is available to the phase fixup after reset. -/
theorem fixupFactor_recycled {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (s : BasisState) (hs : Clean paths s ∧ LoadedClear data read low tree root s) :
    fixupFactor data outcomes read low hot tree root (clearRegister (data.map ClearPort.target) s) =
      registerXPhase (data.map ClearPort.target) outcomes s := by
  let cleared := clearRegister (data.map ClearPort.target) s
  let prepared := Classical.run (hotPrepare low hot) cleared
  have hhot : HotClean hot cleared := by
    intro i
    change clearRegister (data.map ClearPort.target) s (hot i) = false
    exact clearRegister_clean _ s _ (hh i)
  have hlow : ∀ i, cleared (low i) = s (low i) := by
    intro i
    have hw : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact clearRegister_frame _ _ _ (ha _ (by simp only [List.mem_cons, List.mem_append, hw, or_true, true_or]))
  have haddr : hotAddress low cleared = hotAddress low s :=
    addrN_congr _ _ _ 7 (fun j hj => by simp only [lowN, hj, dite_true]; exact hlow _)
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = s w := by
    change Classical.run (hotPrepare low hot) cleared w = s w
    rw [hotPrepare_frame low hot cleared w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)]
    apply clearRegister_frame
    apply ha
    simp only [List.mem_cons, List.mem_append] at hw ⊢
    tauto
  have hroute : tree.routeLabel prepared = tree.routeLabel s := by
    apply tree.routeLabel_congr prepared s
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 128 := ⟨hotAddress low s, hotAddress_bound low s⟩
  apply phaseFactor_loaded data outcomes read hot tree root s prepared selected
  · intro i
    simpa only [Fin.ext_iff, haddr] using hotPrepare_marker low hot hi hdlow cleared hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hs.2 p hp

theorem measuredClear_recycled_coherent {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank hot)
    (hn : (data.map ClearPort.target).Nodup)
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((measuredClear data low hot tree root scratch paths start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (data.map ClearPort.target)))
      (fun s => Clean paths s ∧ LoadedClear data read low tree root s) := by
  unfold CoherentlyImplementsOn
  rw [measuredClear_run]
  apply measureResetThen_coherent (data.map ClearPort.target)
    (fun outcomes => fixupSource data outcomes read low hot tree root scratch paths)
    (fun outcomes => basisIdeal id (fixupFactor data outcomes read low hot tree root))
    (fun _ s => HotClean hot s ∧ Clean paths s)
    (fun s => Clean paths s ∧ LoadedClear data read low tree root s)
    (clearRegister (data.map ClearPort.target)) hn (witness := zeroBasisState)
  · intro outcomes hout
    exact fixupSource_wellFormed data outcomes read low hot tree root scratch paths hl hi hdlow hs hshot
  · intro outcomes
    exact fixupSource_coherent data outcomes read low hot tree root scratch paths hl hi hdlow hbank hs hshot
  · intro outcomes hout s hvalid
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact clearRegister_clean _ s _ (hh i)
    · intro w hw
      rw [clearRegister_frame _ _ _ (ha w (by simp [hw]))]
      exact hvalid.1 w hw
    · rw [basisIdeal_ket, fixupFactor_recycled data outcomes read low hot tree root paths hi hdlow hbank ha hh s hvalid]
      rfl
  · simp [Clean, LoadedClear, zeroBasisState]


end
end ShorECDLP.Entrant.MeasuredClear

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- The compiler sees a source word and the segment between its load and clear. -/
structure MaskedSite (n : Nat) where
  guard : Wire
  ports : List (LookupPort n)
  arithmetic : ECDSAAdd.Program

def MaskedSite.prefix {n} (s : MaskedSite n) : WCode n :=
  [.lookup (some s.guard) s.ports, .literal s.arithmetic]
def MaskedSite.code {n} (s : MaskedSite n) : WCode n :=
  s.prefix ++ [.lookup (some s.guard) s.ports]

inductive Block (n : Nat) where
  | plain (code : WCode n)
  | masked (site : MaskedSite n)
abbrev Code (n : Nat) := List (Block n)

def Block.code {n} : Block n → WCode n
  | .plain code => code
  | .masked site => site.code

def erase {n} (code : Code n) : WCode n := code.flatMap Block.code
@[simp] theorem erase_append {n} (a b : Code n) : erase (a++b) = erase a ++ erase b := by
  simp [erase,List.flatMap_append]

@[simp] theorem erase_plain {n} (code : WCode n) : erase ([.plain code] : Code n) = code := by
  simp [erase,Block.code]

def reference {n} (read : ConstantBit n → Bool) (address : Nat) (code : Code n) : ECDSAAdd.Program :=
  (specialize (erase code) address).instantiate read
@[simp] theorem reference_append {n} (read : ConstantBit n → Bool) (address : Nat)
    (a b : Code n) : reference read address (a++b) = reference read address a ++ reference read address b := by
  simp [reference]

def blockReference {n} (read : ConstantBit n → Bool) (address : Nat) (b : Block n) : ECDSAAdd.Program :=
  (specialize b.code address).instantiate read

def BlockSafe {n} (read : ConstantBit n → Bool) (address : Nat) : Block n → ECDSAAdd.State → Prop
  | .plain _, _ => True
  | .masked site, st => ∀ m, Clean (portTargets site.ports)
      (ECDSAAdd.run ((specialize site.code address).instantiate read) m st).basis

/-- The annotation is checked on every reference record at every block boundary. -/
def Safe {n} (read : ConstantBit n → Bool) (address : Nat) : Code n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => BlockSafe read address b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference read address b) →
        Safe read address code (ECDSAAdd.run (blockReference read address b) m st)

@[simp] theorem reference_cons {n} (read : ConstantBit n → Bool) (address : Nat)
    (b : Block n) (code : Code n) : reference read address (b::code) =
      blockReference read address b ++ reference read address code := by
  simp [reference,erase,blockReference,specialize]

@[simp] theorem reference_nil {n} (read : ConstantBit n → Bool) (address : Nat) :
    reference read address ([] : Code n) = [] := rfl

theorem safe_append {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code n)
    (st : ECDSAAdd.State) (ha : Safe read address a st)
    (hb : ∀ m, m.length = ECDSAAdd.measurementCount (reference read address a) →
      Safe read address b (ECDSAAdd.run (reference read address a) m st)) :
    Safe read address (a++b) st := by
  induction a generalizing st with
  | nil => simpa [Safe,ECDSAAdd.run] using hb [] rfl
  | cons x xs ih =>
    refine ⟨ha.1,?_⟩
    intro m hm
    apply ih _ (ha.2 m hm)
    intro tail ht
    have hc := hb (m++tail) (by simp [ECDSAAdd.measurementCount_append,hm,ht])
    rw [reference_cons,run_append_records _ _ m tail st hm] at hc
    exact hc

/-- Arithmetic proofs supply this contract; the lookup compiler uses no arithmetic internals. -/
structure Checked {n} (read : ConstantBit n → Bool) (address : Nat)
    (P : BasisState → Prop) (code : Code n) (Q : BasisState → Prop) : Prop where
  correct : ECDSAAdd.Triple P (reference read address code) Q
  safe : ∀ st, P st.basis → Safe read address code st

namespace Checked
variable {n : Nat} {read : ConstantBit n → Bool} {address : Nat}
variable {P Q R : BasisState → Prop} {a b : Code n}

theorem seq (ha : Checked read address P a Q) (hb : Checked read address Q b R) :
    Checked read address P (a++b) R := by
  refine ⟨?_,?_⟩
  · rw [reference_append]; exact ha.correct.seq hb.correct
  · intro st hs
    apply safe_append _ _ _ _ st (ha.safe st hs)
    intro m _
    exact hb.safe _ (ha.correct st m hs).2

theorem plain (code : WCode n) (h : ECDSAAdd.Triple P ((specialize code address).instantiate read) Q) :
    Checked read address P ([.plain code] : Code n) Q := by
  refine ⟨?_,fun _ _ => ⟨True.intro,fun _ _ => True.intro⟩⟩
  simpa [reference,erase,Block.code,specialize] using h

theorem masked (site : MaskedSite n)
    (h : ECDSAAdd.Triple P ((specialize site.code address).instantiate read) Q)
    (hc : ∀ s, Q s → Clean (portTargets site.ports) s) :
    Checked read address P ([.masked site] : Code n) Q := by
  refine ⟨?_,?_⟩
  · simpa [reference,erase,Block.code,specialize] using h
  · intro st hs
    exact ⟨fun m => hc _ (h st m hs).2,fun _ _ => True.intro⟩

end Checked

def constSite {n} (L : ECDSAAdd.Arithmetic.ControlledPointLayout) (r : List Wire)
    (refs : Nat → Nat → ConstantBit n) : MaskedSite n :=
  ⟨L.core.generic,indexedPorts (L.recoveryConstant r).src refs true,
    (L.recoveryConstant r).program SquareReduction.c ECDSAAdd.p⟩

def constAdd {n} (L : ECDSAAdd.Arithmetic.ControlledPointLayout) (r : List Wire)
    (refs : Nat → Nat → ConstantBit n) : Code n := [.masked (constSite L r refs)]
@[simp] theorem erase_constAdd {n} (L : ECDSAAdd.Arithmetic.ControlledPointLayout) (r : List Wire)
    (refs : Nat → Nat → ConstantBit n) : erase (constAdd L r refs) = wConstAdd L r refs := rfl

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open ECDSAAdd
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Arithmetic.CompressedPointDialog ECDSAAdd.Arithmetic.MappedCompressed
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

@[simp] theorem indexed_targets {n} (ws : List Wire) (refs : Nat → Nat → ConstantBit n) (v : Bool) :
    portTargets (indexedPorts ws refs v) = ws := by
  induction ws generalizing refs with
  | nil => rfl
  | cons w ws ih => simpa [indexedPorts,portTargets] using congrArg (List.cons w) (ih (fun a i => refs a (i+1)))

theorem value_source_clean {n} (L : ControlledPointLayout) (r : List Wire)
    (refs : Nat → Nat → ConstantBit n) {X Y : ECDSAAdd.Fp} {G : Bool} {base s : BasisState}
    (h : PointDialogValues L X Y G base s) : Clean (portTargets (constSite L r refs).ports) s := by
  rw [constSite,indexed_targets]
  intro q hq
  exact (regValue_zero _ _).mp h.clean q (List.mem_of_mem_take hq)

theorem const_checked {n} (read : ConstantBit n → Bool) (address : Nat)
    (L : ControlledPointLayout) (r : List Wire) (refs : Nat → Nat → ConstantBit n)
    (P Q : BasisState → Prop)
    (h : ECDSAAdd.Triple P ((specialize (wConstAdd L r refs) address).instantiate read) Q)
    (hc : ∀ s, Q s → Clean (portTargets (constSite L r refs).ports) s) :
    Checked read address P (constAdd L r refs) Q := by
  apply Checked.masked _ _ hc
  exact h

theorem literal_checked {n} (read : ConstantBit n → Bool) (address : Nat)
    (p : ECDSAAdd.Program) (P Q : BasisState → Prop) (h : ECDSAAdd.Triple P p Q) :
    Checked read address P ([.plain (wLiteral p)] : Code n) Q := by
  apply Checked.plain
  simpa using h

theorem addX_checked {n} (read : ConstantBit n → Bool) (address : Nat)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) (k : ECDSAAdd.Fp)
    (refs : Nat → Nat → ConstantBit n) (hr : ∀ i < 256, read (refs address i) = k.val.testBit i) :
    Checked read address (PointDialogValues L X Y G base) (constAdd L L.point.x refs)
      (PointDialogValues L (X+(if G then k else 0)) Y G base) := by
  apply const_checked _ _ _ _ _ _ _
  · rw [specialize_constAdd,constAddT_inst read L L.point.x _ k hr]
    exact dialogStep_addX L hw hn X Y G base k
  · intro s hs
    exact value_source_clean L L.point.x refs hs

theorem addY_checked {n} (read : ConstantBit n → Bool) (address : Nat)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) (k : ECDSAAdd.Fp)
    (refs : Nat → Nat → ConstantBit n) (hr : ∀ i < 256, read (refs address i) = k.val.testBit i) :
    Checked read address (PointDialogValues L X Y G base) (constAdd L L.point.y refs)
      (PointDialogValues L X (Y+(if G then k else 0)) G base) := by
  apply const_checked _ _ _ _ _ _ _
  · rw [specialize_constAdd,constAddT_inst read L L.point.y _ k hr]
    exact dialogStep_addY L hw hn X Y G base k
  · intro s hs
    exact value_source_clean L L.point.y refs hs

def recovery {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : Code n :=
  [.plain (wLiteral (pointRecoveryReflection L))] ++ constAdd L L.point.x (wFields rows .x) ++
    [.plain (wLiteral (pointDialogConstantAdd L L.point.x 1))] ++ constAdd L L.point.y (wFields rows .negY)

def core {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : Code n :=
  constAdd L L.point.x (wFields rows .negX) ++ constAdd L L.point.y (wFields rows .negY) ++
    [.plain (wLiteral (ECDSAAdd.Frontier.arithS L false)),
     .plain (wLiteral (ECDSAAdd.Frontier.SquareOB5.program L))] ++
    constAdd L L.point.x (wFields rows .tripleX) ++
    [.plain (wLiteral (ECDSAAdd.Frontier.arithS L true))] ++ recovery L rows

def generic {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : Code n :=
  [.plain (wLiteral (ECDSAAdd.Frontier.zrep L))] ++ core L rows ++
    [.plain (wLiteral (ECDSAAdd.Frontier.zrep L))]

@[simp] theorem erase_recovery {n} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    erase (recovery L rows) = wRecovery L rows := rfl

@[simp] theorem erase_generic {n} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    erase (generic L rows) = wGeneric L rows := rfl

theorem row_bits {n} {read : ConstantBit n → Bool} {rows : Nat → Fin n} {address : Nat}
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc)) (f : PointField) (k : ECDSAAdd.Fp)
    (hk : fieldValue (toA (.some hc)) f = k.val) :
    ∀ i < 256, read (wFields rows f address i) = k.val.testBit i := by
  intro i hi
  rw [wFields,fieldBits,hr.bit f i hi,hk]

theorem recovery_checked {n} (read : ConstantBit n → Bool) (address : Nat)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) :
    Checked read address (PointDialogValues L X Y G base) (recovery L rows)
      (PointDialogValues L (if G then cx-X else X) (if G then Y-cy else Y) G base) := by
  have a := literal_checked read address _ _ _ (pointRecoveryReflection_step L hw hn X Y G base)
  have b := addX_checked read address L hw hn (if G then -1-X else X) Y G base cx
    (wFields rows .x) (row_bits hc hr .x cx (field_some_x hc))
  have c := literal_checked read address _ _ _
    (dialogStep_addX L hw hn ((if G then -1-X else X)+(if G then cx else 0)) Y G base 1)
  have d := addY_checked read address L hw hn
    (((if G then -1-X else X)+(if G then cx else 0))+(if G then 1 else 0)) Y G base (-cy)
    (wFields rows .negY) (row_bits hc hr .negY (-cy) (field_some_negY hc))
  have all := ((a.seq b).seq c).seq d
  have hx : ((if G then -1-X else X)+(if G then cx else 0))+(if G then 1 else 0)=
      (if G then cx-X else X) := by cases G <;> simp; ring
  have hy : Y+(if G then -cy else 0)=(if G then Y-cy else Y) := by cases G <;> simp [sub_eq_add_neg]
  rw [hx,hy] at all
  exact all

theorem core_checked_true {n} (read : ConstantBit n → Bool) (address : Nat)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Checked read address (PointDialogValues L X Y true base) (core L rows)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := addX_checked read address L hw hn X Y true base (-cx)
    (wFields rows .negX) (row_bits hc hr .negX (-cx) (field_some_negX hc))
  have h2 := addY_checked read address L hw hn (X-cx) Y true base (-cy)
    (wFields rows .negY) (row_bits hc hr .negY (-cy) (field_some_negY hc))
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := literal_checked read address _ _ _
    (ECDSAAdd.Frontier.arith3F_step L hw hn (X-cx) (Y-cy) true base false (sub_ne_zero.mpr hX))
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [Bool.false_eq_true,if_false,ha] at h3
  have h4 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.GenericOB5.square_step L hw hn (X-cx) a true base)
  simp only [if_true] at h4
  have h5 := addX_checked read address L hw hn ((X-cx)-a*a) a true base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc))
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.arith3F_step L hw hn d a true base true hd)
  simp only [if_true] at h6
  have r := recovery_checked read address L hw hn rows hc hr d (a*d) true base
  simp only [if_true] at r
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at r
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at r
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq r
  simpa only [core,List.append_assoc,List.cons_append,List.nil_append] using h

theorem core_checked_false {n} (read : ConstantBit n → Bool) (address : Nat)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState) (hX0 : X ≠ 0) :
    Checked read address (PointDialogValues L X Y false base) (core L rows)
      (PointDialogValues L X Y false base) := by
  have h1 := addX_checked read address L hw hn X Y false base (-cx)
    (wFields rows .negX) (row_bits hc hr .negX (-cx) (field_some_negX hc))
  have h2 := addY_checked read address L hw hn X Y false base (-cy)
    (wFields rows .negY) (row_bits hc hr .negY (-cy) (field_some_negY hc))
  have h3 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.arith3F_step L hw hn X Y false base false hX0)
  have h4 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.GenericOB5.square_step L hw hn X (Y/X) false base)
  have h5 := addX_checked read address L hw hn X (Y/X) false base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc))
  have h6 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.arith3F_step L hw hn X (Y/X) false base true hX0)
  have r := recovery_checked read address L hw hn rows hc hr X Y false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 r
  rw [div_mul_cancel₀ Y hX0] at h6
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq r
  simpa only [core,List.append_assoc,List.cons_append,List.nil_append] using h

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open ECDSAAdd Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000

theorem generic_safe_boundary {n} (read : ConstantBit n → Bool) (address : Nat)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (rows : Nat → Fin n) (R : Point) (b : Bool) (f : BasisState)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc))
    (st : ECDSAAdd.State) (hs : PointDialogBoundary L R b f st.basis) :
    Safe read address (generic L rows) st := by
  have hp := (point_holds _ _ _).mp hs.point
  have hgen : st.basis L.core.generic = f L.core.generic := hs.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false st.basis st.basis :=
      ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
    have hfin : st.basis L.point.finite = false := hp.1
    have z1 := literal_checked read address _ _ _ (Frontier.zrep_step L hw hn 0 5 0 false st.basis
      (by rw [hfin,Frontier.finFive_val]; rfl))
    have mid := core_checked_false read address L hw hn rows hc hr 5 0 st.basis Frontier.finFive_ne_zero
    have z2 := literal_checked read address _ _ _ (Frontier.zrep_step L hw hn 5 0 0 false st.basis
      (by rw [hfin,Frontier.finFive_val]; rfl))
    have all := (z1.seq mid).seq z2
    simpa only [generic,List.append_assoc] using all.safe st values
  | @some x y hrp =>
    have hfin : st.basis L.point.finite = true := hp.1
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false st.basis st.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
      have z1 := literal_checked read address _ _ _ (Frontier.zrep_step L hw hn x x y false st.basis (by rw [hfin]; simp))
      have mid := core_checked_false read address L hw hn rows hc hr x y st.basis (Frontier.curve_x_ne_zero hrp)
      have z2 := literal_checked read address _ _ _ (Frontier.zrep_step L hw hn x x y false st.basis (by rw [hfin]; simp))
      have all := (z1.seq mid).seq z2
      simpa only [generic,List.append_assoc] using all.safe st values
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hrp hc he.2.1 he.2.2.1 he.2.2.2
      have values : PointDialogValues L x y true st.basis st.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
      have z1 := literal_checked read address _ _ _ (Frontier.zrep_step L hw hn x x y true st.basis (by rw [hfin]; simp))
      have mid := core_checked_true read address L hw hn rows hc hr x y st.basis den.1 den.2
      have z2 := literal_checked read address _ _ _ (Frontier.zrep_step L hw hn (genericX x y cx cy)
        (genericX x y cx cy) (genericY x y cx cy) true st.basis (by rw [hfin]; simp))
      have all := (z1.seq mid).seq z2
      simpa only [generic,List.append_assoc] using all.safe st values

end
end ShorECDLP.Entrant.WEXUnlookup
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] ECDSAAdd.run
local instance : DecidableEq Point := Classical.typeDecidableEq _

def referencePrefixCode {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral ([.CX L.control L.core.double]) ++ wLiteral ([.CX L.control L.core.equalX]) ++
  wLiteral (zeroFlag L.point.finite L.control L.infinitySelect) ++
  wPairEqual L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) ++
  wShortNegEqual L L.core.equalX L.core.equalNegY rows ++ wLiteral (pointDialogGenericFlag L)

def prefixCode {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral ([.CX L.control L.core.double]) ++ wLiteral ([.CX L.control L.core.equalX]) ++
  wLiteral (zeroFlag L.point.finite L.control L.infinitySelect) ++
  wPairEqualTight L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) ++
  wShortNegEqual L L.core.equalX L.core.equalNegY rows ++ wLiteral (pointDialogGenericFlag L)

def suffixCode {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wCornersOne L rows ++ wLiteral (pointDialogGenericFlag L) ++
  wPairEqualTight L L.infinitySelect L.core.equalNegY (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) ++
  wShortEqual L L.core.double L.doubleSelect (wBit rows .doubleInfinity)
    (wFields rows .doubleX) (wBit rows .doubleY) ++
  wLiteral (zeroFlag L.point.finite L.control L.genericSelect) ++
  wLiteral ([.CX L.control L.core.equalX]) ++ wLiteral ([.CX L.control L.core.double]) ++
  wLiteral (Arith.padding (L.core.poolWire 0) 49864)

def fusedPrefixCode {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : WCode n :=
  wLiteral ([.CX L.control L.core.double]) ++ wLiteral ([.CX L.control L.core.equalX]) ++
  wLiteral (zeroFlag L.point.finite L.control L.infinitySelect) ++
  wPairShortFused L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
    (wBit rows .y) (wBit rows .negY) (shortNegPorts L rows)
    (zeroControlled L.core.equalX L.core.equalNegY (zeroPorts (shortSrc L) (L.dialogPool.take 258))) ++
  wLiteral (pointDialogGenericFlag L)

theorem specialize_fusedPrefix {n} (L : ControlledPointLayout) (rows : Nat → Fin n) (a : Nat) :
    specialize (fusedPrefixCode L rows) a = specialize (prefixCode L rows) a := by
  rw [fusedPrefixCode,prefixCode,shortNegEqual_expanded]
  simp only [specialize_append,specialize_pairShortFused,List.append_assoc]

def finite {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : Code n :=
  [.plain (prefixCode L rows)] ++ generic L rows ++ [.plain (suffixCode L rows)]

def fusedFinite {n} (L : ControlledPointLayout) (rows : Nat → Fin n) : Code n :=
  [.plain (fusedPrefixCode L rows)] ++ generic L rows ++ [.plain (suffixCode L rows)]

@[simp] theorem erase_fusedFinite {n} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    erase (fusedFinite L rows) = wFinite23 L rows := by
  unfold fusedFinite
  rw [erase_append,erase_append,erase_generic,erase_plain,erase_plain]
  simp only [fusedPrefixCode,suffixCode,wFinite23,List.append_assoc]

@[simp] theorem erase_finite {n} (L : ControlledPointLayout) (rows : Nat → Fin n) :
    erase (finite L rows) = wFiniteTight L rows := by
  unfold finite
  rw [erase_append,erase_append,erase_generic,erase_plain,erase_plain]
  simp only [prefixCode,suffixCode,wFiniteTight,List.append_assoc]

def prefixS (L : ControlledPointLayout) (C : Point) (cy : ECDSAAdd.Fp) : ECDSAAdd.Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  zeroFlag L.point.finite L.control L.infinitySelect ++
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  shortEqual L L.core.equalX L.core.equalNegY (dialogExceptionPoint C) ++ pointDialogGenericFlag L

def flags (L : ControlledPointLayout) (R C : Point) (b : Bool) (cy : ECDSAAdd.Fp) : BasisState := by
  classical
  exact dialogFlagState L (dialogInfinity b R) (dialogDouble b R C) (dialogInversePoint b R C)
    (dialogOrdinary b R C) (b && decide (dialogExceptionEnabled C)) (dialogException b R C)
    (b && decide (cy≠-cy))

-- The prefix is shared with the finite-addend specification, Apache-2.0.
theorem prefixS_checked (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    ECDSAAdd.Triple (PointDialogBoundary L R b (fun _=>false)) (prefixS L (.some hc) cy)
      (PointDialogBoundary L R b (flags L R (.some hc) b cy)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C))=decide (dialogExceptionEnabled C) := by
    simp [pointEqual_decide,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,pointEqual_decide]
  have hD : (K && pointEqual R C)=D := by rw [hK]; simp only [D,dialogDouble,pointEqual_decide]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,pointEqual_decide]
  have hH : (E && pointEqual R (dialogExceptionPoint C))=H := by
    simp [E,H,dialogException,dialogExceptionEnabled,pointEqual_decide]
  have h0 := dialogFlag_doubleEnable L hn R b false false false false false false false cy
  simp only [Bool.false_xor] at h0
  have h1 := dialogFlag_exceptionEnable L hn R b false false false false false false K C
  rw [hE,Bool.false_xor] at h1
  have h2 := zeroFlag_equalO L hn R b false false false false E false K
  rw [hO,Bool.false_xor] at h2
  have h3 := pairFlag_input L hw hn R C cy b O false false false E false K rfl
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := shortFlag_equalH L hw hn R (dialogExceptionPoint C) b O D I false E false K
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false E H K
  simp only [Bool.false_xor] at h6
  have h := ((((h0.seq h1).seq h2).seq h3).seq h5).seq h6
  simpa only [prefixS,List.append_assoc,dialogFlagState_zero,flags,O,D,I,H,G,E,K] using h

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] ECDSAAdd.run

theorem referencePrefix_inst {n} (read : CBit n → Bool) (L : ControlledPointLayout)
    (hw : L.Widths) (rows : Nat → Fin n) (address : Nat) {cx cy : ECDSAAdd.Fp}
    (hc : curve.toAffine.Nonsingular cx cy) (h : RowReads read (rows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point) + .some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point) + .some hc) = 0) :
    (specialize (referencePrefixCode L rows) address).instantiate read = prefixS L (.some hc) cy := by
  set C : Point := .some hc
  have hxl : L.point.x.length = 256 := hw.inputX
  have fC : read (bitRef (rows address) .infinity 0) = !pointFinite C := by
    rw [h.bit _ 0 (by decide), infinity_bit]
  have fD : read (bitRef (rows address) .doubleInfinity 0) = !pointFinite (C+C) := by
    rw [h.bit _ 0 (by decide), ECDSAAdd.ShorPort.doubleInfinity_bit]
  have fH : read (bitRef (rows address) .doubleInfinity 0) = !pointFinite (dialogExceptionPoint C) := by
    rw [fD, dialogExceptionPoint, ECDSAAdd.ShorPort.pointFinite_neg]
  have xC := fieldBits_reads h .x _ (field_x C)
  have xD := fieldBits_reads h .doubleX _ (field_doubleX C)
  have xH : ∀ i < 256, read (fieldBits (rows address) .doubleX i) =
      (pointX (dialogExceptionPoint C)).testBit i := by
    rw [dialogExceptionPoint, ECDSAAdd.ShorPort.pointX_neg]
    exact xD
  rw [← hxl] at xC xH
  have yC : read (bitRef (rows address) .y 0) = yBit C := by
    rw [h.bit _ 0 (by decide), field_y, yBit_eq]
  have yN : read (bitRef (rows address) .negY 0) = yBit (-C) := by
    rw [h.bit _ 0 (by decide), ECDSAAdd.ShorPort.field_negY, yBit_eq]
  have parity := finite_point_parity (C+C) hD hDo
  rw [yBit_eq,yBit_eq] at parity
  have yH : (!read (bitRef (rows address) .doubleY 0)) =
      (pointY (dialogExceptionPoint C)).testBit 0 := by
    rw [h.bit _ 0 (by decide),field_doubleY,dialogExceptionPoint]
    exact parity.symm
  have e1 : pointInPlaceDoubleEnable L cy = [.CX L.control L.core.double] := by
    unfold pointInPlaceDoubleEnable; exact if_pos h₁
  have e2 : pointDialogExceptionEnable L C = [.CX L.control L.core.equalX] := by
    unfold pointDialogExceptionEnable; exact if_pos h₂
  have d1 : decide (cy≠-cy) = true := decide_eq_true h₁
  simp only [referencePrefixCode,specialize_append,specialize_literal,specialize_pairEqual,
    specialize_shortNegEqual,Tmpl.instantiate_append,Tmpl.instantiate_lit,wBit,wFields,
    prefixS,e1,e2,d1,
    pairEqualT_inst read L _ _ _ _ _ _ C (-C) fC xC yC yN,
    shortNegEqualT_inst read L hw _ _ _ _ _ (dialogExceptionPoint C) fH xH yH]

theorem row_opposite {n} (read : CBit n → Bool) (rows : Nat → Fin n) (address : Nat)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (h : RowReads read (rows address) (.some hc)) (h₁ : cy ≠ -cy) :
    read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address)) := by
  have yC : read (bitRef (rows address) .y 0) = yBit (.some hc) := by
    rw [h.bit _ 0 (by decide),field_y,yBit_eq]
  have yN : read (bitRef (rows address) .negY 0) = yBit (-(.some hc : Point)) := by
    rw [h.bit _ 0 (by decide),ECDSAAdd.ShorPort.field_negY,yBit_eq]
  have hy0 : cy ≠ 0 := by intro hy; apply h₁; simp [hy]
  change read (bitRef (rows address) .negY 0) = !(read (bitRef (rows address) .y 0))
  rw [yN,yC,yBit_eq,yBit_eq,pointY_neg]
  exact neg_y_low_bit cy hy0

theorem prefixCode_equiv {n} (read : CBit n → Bool) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (rows : Nat → Fin n) (address : Nat)
    (hop : read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address))) :
    CodeEquivalent read address (referencePrefixCode L rows) (prefixCode L rows) := by
  have hd : L.doubleSelect ≠ L.genericSelect := by
    have h := dialogFlag_separation L hn
    simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at h
    tauto
  have hp : CodeEquivalent read address
      (wPairEqual L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY))
      (wPairEqualTight L L.doubleSelect L.genericSelect (wBit rows .infinity) (wFields rows .x)
        (wBit rows .y) (wBit rows .negY)) := by
    exact ⟨tight_pair_measurements read L _ _ _ _ _ _ address hop,
      tight_pair_run read L hw hn _ _ (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) hd _ _ _ _ address hop⟩
  unfold referencePrefixCode prefixCode
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ (codeEquivalent_refl _ _ _)
  refine codeEquivalent_append read address ?_ hp
  exact codeEquivalent_refl _ _ _

theorem safe_plain {n} (read : ConstantBit n → Bool) (address : Nat) (code : WCode n)
    (st : ECDSAAdd.State) : Safe read address ([.plain code] : Code n) st := ⟨True.intro,fun _ _ => True.intro⟩

theorem finite_safe {n} (read : CBit n → Bool) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (rows : Nat → Fin n) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp}
    (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (rows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (b : Bool) (st : ECDSAAdd.State) (hs : PointDialogBoundary L R b (fun _=>false) st.basis) :
    Safe read address (finite L rows) st := by
  classical
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro m _
  let next := ECDSAAdd.run (blockReference read address (.plain (prefixCode L rows))) m st
  have hv : PointDialogBoundary L R b (flags L R (.some hc) b cy) next.basis := by
    have hp := (prefixS_checked L hw hn R hc b st m hs).2
    have he := prefixCode_equiv read L hw hn rows address (row_opposite read rows address hc hr h₁)
    change PointDialogBoundary L R b (flags L R (.some hc) b cy)
      (ECDSAAdd.run ((specialize (prefixCode L rows) address).instantiate read) m st).basis
    rw [← he.2 m st,referencePrefix_inst read L hw rows address hc hr h₁ h₂ hD hDo]
    exact hp
  apply safe_append _ _ _ _ next
  · apply generic_safe_boundary read address L hw hn rows R b (flags L R (.some hc) b cy) hc hr _ next hv
    intro hg
    have read := dialogFlagState_read L hn (dialogInfinity b R) (dialogDouble b R (.some hc))
      (dialogInversePoint b R (.some hc)) (dialogOrdinary b R (.some hc))
      (b && decide (dialogExceptionEnabled (.some hc))) (dialogException b R (.some hc))
      (b && decide (cy≠-cy))
    have he : dialogOrdinary b R (.some hc) = true := read.2.2.2.1.symm.trans hg
    exact ((dialogOrdinary_true b R (.some hc) (WeierstrassCurve.Affine.Point.some_ne_zero hc)).mp he).2
  · intro m hm
    exact safe_plain _ _ _ _

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.ShorPort
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem delta_getD_mem_take (xs : List Wire) (d : Wire) (i n : Nat)
    (hi : i < n) (hn : n ≤ xs.length) : xs.getD i d ∈ xs.take n := by
  have ht : i < (xs.take n).length := by simp [List.length_take]; omega
  have hp : i < xs.length := by omega
  have heq : (xs.take n)[i] = xs.getD i d := by
    rw [List.getElem_take, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    rfl
  rw [← heq]
  exact List.getElem_mem ht

theorem deltaPool_eq : streamLayout.dialogPool = streamLayout.core.pool.take 2613 := rfl

theorem deltaPoolWire_eq (i : Nat) : streamLayout.core.poolWire i = streamLayout.core.pool.getD i 0 := rfl

theorem deltaPool_length : streamLayout.core.pool.length = 5699 := by
  change ((List.range' 4115 5699).map streamWire).length = 5699
  simp

theorem deltaPool_mem_dialog (i : Nat) (hi : i < 2613) :
    streamLayout.core.poolWire i ∈ streamLayout.dialogPool := by
  rw [deltaPool_eq, deltaPoolWire_eq]
  apply delta_getD_mem_take _ _ i 2613 hi
  rw [deltaPool_length]
  omega

theorem deltaZeroWith_support (T : Wire → Program) (used : List Wire)
    (hT : ∀ c, ECDSAAdd.wires (T c) ⊆ (c::used).toFinset) (c : Wire) (bs : List ZeroBit) :
    ECDSAAdd.wires (zeroWith T c bs) ⊆ (c::used ++ bs.flatMap ZeroBit.wires).toFinset := by
  induction bs generalizing c with
  | nil => simpa [zeroWith] using hT c
  | cons b bs ih =>
    intro q hq
    have child := @ih b.work q
    simp only [zeroWith,ECDSAAdd.wires_append,Finset.mem_union] at hq
    simp [chainAnd,chainErase,ECDSAAdd.wires,Instr.wires,correctionWires,ZeroBit.wires,
      List.mem_cons,List.mem_toFinset] at hq child ⊢
    aesop

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.ShorPort ECDSAAdd.RecordedQuantum
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Conditional X gates: the instantiated form of an uncontrolled lookup. -/
def xBits : List Wire → List Bool → Program
  | w :: ws, b :: bs => (if b then [.X w] else []) ++ xBits ws bs
  | _, _ => []

/-- Copies a loaded scratch word onto its targets. -/
def cxList : List Wire → List Wire → Program
  | a :: as, t :: ts => .CX a t :: cxList as ts
  | _, _ => []

def xMask : List Wire → List Bool → Wire → Bool
  | w :: ws, b :: bs, q => (decide (q = w) && b) ^^ xMask ws bs q
  | _, _, _ => false

theorem xBits_records (S : List Wire) (k : List Bool) : measurementCount (xBits S k) = 0 := by
  induction S generalizing k with
  | nil => rfl
  | cons w S ih =>
    cases k with
    | nil => rfl
    | cons b k => cases b <;> simp [xBits, measurementCount, ih]


theorem cxList_records (S T : List Wire) : measurementCount (cxList S T) = 0 := by
  induction S generalizing T with
  | nil => rfl
  | cons a S ih => cases T <;> simp [cxList, measurementCount, ih]

theorem cxList_toffoli (S T : List Wire) : ECDSAAdd.toffoliCount (cxList S T) = 0 := by
  induction S generalizing T with
  | nil => rfl
  | cons a S ih => cases T <;> simp [cxList, ECDSAAdd.toffoliCount, ih]

theorem xBits_run (S : List Wire) (k m : List Bool) (s : State) :
    run (xBits S k) m s = ⟨s.phase, fun q => s.basis q ^^ xMask S k q⟩ := by
  induction S generalizing k s with
  | nil => simp [xBits, xMask, run]
  | cons w S ih =>
    cases k with
    | nil => simp [xBits, xMask, run]
    | cons b k =>
      cases b
      · simpa [xBits, xMask] using ih k s
      · change run (.X w :: xBits S k) m s = _
        simp only [run]
        rw [ih]
        apply congrArg (State.mk s.phase)
        funext q
        by_cases hq : q = w
        · subst hq
          simp [writeBit, xMask]
        · simp [writeBit, xMask, hq]

theorem xMask_outside (T : List Wire) (k : List Bool) (a : Wire) (h : a ∉ T) : xMask T k a = false := by
  induction T generalizing k with
  | nil => rfl
  | cons w T ih =>
    cases k with
    | nil => rfl
    | cons b k =>
      have ha : a ≠ w := fun e => h (e ▸ List.mem_cons_self)
      have ht : a ∉ T := fun e => h (List.mem_cons_of_mem _ e)
      simp [xMask, ha, ih k ht]

theorem cxList_run (S T : List Wire) (m : List Bool) (u : State) (hd : ∀ a ∈ S, a ∉ T) :
    run (cxList S T) m u = ⟨u.phase, fun q => u.basis q ^^ xMask T (S.map u.basis) q⟩ := by
  induction S generalizing T u with
  | nil => simp [cxList, xMask, run]
  | cons a S ih =>
    cases T with
    | nil => simp [cxList, xMask, run]
    | cons t T =>
      have hat : a ≠ t := fun e => hd a List.mem_cons_self (e ▸ List.mem_cons_self)
      have hS : ∀ x ∈ S, x ≠ t := fun x hx e =>
        hd x (List.mem_cons_of_mem _ hx) (e ▸ List.mem_cons_self)
      have hT : ∀ x ∈ S, x ∉ T := fun x hx e =>
        hd x (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ e)
      simp only [cxList, run]
      rw [ih T _ hT]
      have hmap : S.map (writeBit u.basis t (u.basis t ^^ u.basis a)) = S.map u.basis := by
        apply List.map_congr_left
        intro x hx
        simp [writeBit, Function.update_of_ne (hS x hx)]
      simp only [hmap]
      apply congrArg (State.mk u.phase)
      funext q
      by_cases hq : q = t
      · subst hq
        simp [writeBit, xMask]
      · simp [writeBit, xMask, hq]

theorem xBits_wires (S : List Wire) (k : List Bool) (q : Wire) (h : q ∈ wires (xBits S k)) : q ∈ S := by
  induction S generalizing k with
  | nil => simp [xBits, wires] at h
  | cons w S ih =>
    cases k with
    | nil => simp [xBits, wires] at h
    | cons b k =>
      cases b
      · exact List.mem_cons_of_mem _ (ih k (by simpa [xBits] using h))
      · have h' : q ∈ wires (.X w :: xBits S k) := by simpa [xBits] using h
        simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton] at h'
        rcases h' with rfl | h'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih k h')

theorem cxList_wires (S T : List Wire) (q : Wire) (h : q ∈ wires (cxList S T)) : q ∈ S ∨ q ∈ T := by
  induction S generalizing T with
  | nil => simp [cxList, wires] at h
  | cons a S ih =>
    cases T with
    | nil => simp [cxList, wires] at h
    | cons t T =>
      simp only [cxList, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h
      rcases h with (rfl | rfl) | h
      · exact Or.inl List.mem_cons_self
      · exact Or.inr List.mem_cons_self
      · rcases ih T h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem cxList_physical (S T : List Wire) (hd : ∀ a ∈ S, a ∉ T) : GatePhysical (cxList S T) := by
  induction S generalizing T with
  | nil => simp [cxList, GatePhysical]
  | cons a S ih =>
    cases T with
    | nil => simp [cxList, GatePhysical]
    | cons t T =>
      have hat : a ≠ t := fun e => hd a List.mem_cons_self (e ▸ List.mem_cons_self)
      have hT : ∀ x ∈ S, x ∉ T := fun x hx e =>
        hd x (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ e)
      have hp := ih T hT
      intro i hi
      simp only [cxList, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simpa [PhysicalInstr, ProperGate] using hat
      · exact hp i hi

theorem cxList_slots (S T : List Wire) : ECDSAAdd.Challenge.gateSlots (cxList S T) = min S.length T.length := by
  induction S generalizing T with
  | nil => simp [cxList, ECDSAAdd.Challenge.gateSlots]
  | cons a S ih =>
    cases T with
    | nil => simp [cxList, ECDSAAdd.Challenge.gateSlots]
    | cons t T =>
      have h := ih T
      simp only [ECDSAAdd.Challenge.gateSlots] at h
      simp [cxList, ECDSAAdd.Challenge.gateSlots, ECDSAAdd.Challenge.instructionSlots, h]
      omega

/-- The state with the scratch word loaded. -/
def scrLoad (S : List Wire) (k : List Bool) (x : State) : State :=
  ⟨x.phase, fun q => x.basis q ^^ xMask S k q⟩

/-- `P`, run with the scratch word loaded, simulates `P'` run with it clean. -/
structure ScrSim (S : List Wire) (k : List Bool) (P P' : Program) : Prop where
  records : measurementCount P = measurementCount P'
  step : ∀ (m : List Bool) (x : State), (∀ a ∈ S, x.basis a = false) →
    run P m (scrLoad S k x) = scrLoad S k (run P' m x) ∧ ∀ a ∈ S, (run P' m x).basis a = false

theorem ScrSim.append {S : List Wire} {k : List Bool} {P P' R R' : Program}
    (h : ScrSim S k P P') (g : ScrSim S k R R') : ScrSim S k (P ++ R) (P' ++ R') where
  records := by simp only [measurementCount_append, h.records, g.records]
  step m x hx := by
    rw [run_append, run_append, ← h.records]
    have h1 := h.step (m.take (measurementCount P)) x hx
    rw [h1.1]
    exact g.step (m.drop (measurementCount P)) _ h1.2

theorem ScrSim.disjoint (S : List Wire) (k : List Bool) (p : Program) (hd : ∀ a ∈ S, a ∉ wires p) :
    ScrSim S k p p where
  records := rfl
  step m x hx := by
    constructor
    · have hw : Disjoint (wires p) (wires (xBits S k)) :=
        Finset.disjoint_left.mpr fun q hq hs => hd q (xBits_wires S k q hs) hq
      have hc := run_disjoint_commute p (xBits S k) hw m ([] : List Bool) x
      simpa only [xBits_run, scrLoad] using hc
    · exact fun a ha => (run_preserves_outside p m x a (hd a ha)).trans (hx a ha)

private theorem scr_xor_swap (a b c : Bool) : ((a ^^ b) ^^ c) = ((a ^^ c) ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem ScrSim.cx (S S' T : List Wire) (k k' : List Bool) (hmap : S'.map (xMask S k) = k')
    (hS : ∀ a ∈ S', a ∈ S) (hd : ∀ a ∈ S, a ∉ T) : ScrSim S k (cxList S' T) (xBits T k') where
  records := by rw [cxList_records, xBits_records]
  step m x hx := by
    constructor
    · rw [cxList_run S' T m _ (fun a ha => hd a (hS a ha)), xBits_run]
      have hm : S'.map (scrLoad S k x).basis = k' := by
        rw [← hmap]
        apply List.map_congr_left
        intro a ha
        simp [scrLoad, hx a (hS a ha)]
      rw [hm]
      simp only [scrLoad]
      apply congrArg (State.mk x.phase)
      funext q
      exact scr_xor_swap _ _ _
    · intro a ha
      rw [xBits_run]
      simp [hx a ha, xMask_outside T k' a (hd a ha)]

theorem scr_sandwich (S : List Wire) (k : List Bool) (P P' : Program) (h : ScrSim S k P P')
    (m : List Bool) (s : State) (hs : ∀ a ∈ S, s.basis a = false) :
    run (xBits S k ++ P ++ xBits S k) m s = run P' m s := by
  rw [List.append_assoc, run_append, xBits_records, List.take_zero, List.drop_zero, xBits_run,
    run_append]
  change run (xBits S k) _ (run P _ (scrLoad S k s)) = _
  rw [(h.step _ s hs).1, xBits_run, h.records, run_take]
  apply State.extensionality
  · rfl
  · funext q
    simp [scrLoad]

theorem xMask_append (A B : List Wire) (kA kB : List Bool) (hl : A.length = kA.length) (q : Wire) :
    xMask (A ++ B) (kA ++ kB) q = (xMask A kA q ^^ xMask B kB q) := by
  induction A generalizing kA with
  | nil =>
    cases kA with
    | nil => simp [xMask]
    | cons _ _ => simp at hl
  | cons w A ih =>
    cases kA with
    | nil => simp at hl
    | cons b kA =>
      have h := ih kA (by simpa using hl)
      simp only [List.cons_append, xMask, h, Bool.xor_assoc]

theorem xMask_map (S : List Wire) (k : List Bool) (hn : S.Nodup) (hl : S.length = k.length) :
    S.map (xMask S k) = k := by
  induction S generalizing k with
  | nil =>
    cases k with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons w S ih =>
    cases k with
    | nil => simp at hl
    | cons b k =>
      have hw := (List.nodup_cons.mp hn).1
      have ht := ih k (List.nodup_cons.mp hn).2 (by simpa using hl)
      simp only [List.map_cons, xMask, decide_true, Bool.true_and, xMask_outside S k w hw, Bool.xor_false]
      congr 1
      rw [← ht]
      apply List.map_congr_left
      intro a ha
      have hne : a ≠ w := fun e => hw (e ▸ ha)
      simp [hne, ht]

theorem xMask_map_left (A B : List Wire) (kA kB : List Bool) (hn : (A ++ B).Nodup)
    (hA : A.length = kA.length) : A.map (xMask (A ++ B) (kA ++ kB)) = kA := by
  have hd : ∀ a ∈ A, a ∉ B := fun a ha hb => (List.nodup_append'.mp hn).2.2 ha hb
  rw [← xMask_map A kA (List.nodup_append'.mp hn).1 hA]
  rw [xMask_map A kA (List.nodup_append'.mp hn).1 hA]
  have h : A.map (xMask (A ++ B) (kA ++ kB)) = A.map (xMask A kA) := by
    apply List.map_congr_left
    intro a ha
    rw [xMask_append A B kA kB hA, xMask_outside B kB a (hd a ha), Bool.xor_false]
  rw [h, xMask_map A kA (List.nodup_append'.mp hn).1 hA]

theorem xMask_map_right (A B : List Wire) (kA kB : List Bool) (hn : (A ++ B).Nodup)
    (hA : A.length = kA.length) (hB : B.length = kB.length) : B.map (xMask (A ++ B) (kA ++ kB)) = kB := by
  have hd : ∀ b ∈ B, b ∉ A := fun b hb ha => (List.nodup_append'.mp hn).2.2 ha hb
  have h : B.map (xMask (A ++ B) (kA ++ kB)) = B.map (xMask B kB) := by
    apply List.map_congr_left
    intro b hb
    rw [xMask_append A B kA kB hA, xMask_outside A kA b (hd b hb), Bool.false_xor]
  rw [h, xMask_map B kB (List.nodup_append'.mp hn).2.1 hB]

theorem xBits_snoc (T : List Wire) (y : Wire) (k : List Bool) (b : Bool) (hl : T.length = k.length) :
    xBits (T ++ [y]) (k ++ [b]) = xBits T k ++ (if b then [.X y] else []) := by
  induction T generalizing k with
  | nil =>
    cases k with
    | nil => cases b <;> simp [xBits]
    | cons _ _ => simp at hl
  | cons w T ih =>
    cases k with
    | nil => simp at hl
    | cons c k =>
      simp [xBits, ih k (by simpa using hl), List.append_assoc]

/-- The bits of an uncontrolled lookup at one address. -/
def portBits {n : Nat} (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (a : Nat) : List Bool :=
  ports.map fun p => decide (read (p.ref a) = p.value)

theorem portTemplate_none_inst {n : Nat} (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (a : Nat) :
    (portTemplate none ports a).instantiate read = xBits (portTargets ports) (portBits read ports a) := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    have h : portTargets (p :: ports) = p.target :: portTargets ports := rfl
    have h' : portBits read (p :: ports) a = decide (read (p.ref a) = p.value) :: portBits read ports a := rfl
    rw [h, h', portTemplate_cons, Tmpl.instantiate_cons, ih]
    by_cases hb : read (p.ref a) = p.value <;> simp [xBits, TInstr.instantiate, hb]

/-- The same constant bits, redirected to scratch wires. -/
def retarget {n : Nat} (ports : List (LookupPort n)) (S : List Wire) : List (LookupPort n) :=
  List.zipWith (fun p w => ⟨p.ref, p.value, w⟩) ports S

theorem retarget_targets {n : Nat} (ports : List (LookupPort n)) (S : List Wire)
    (h : ports.length = S.length) : portTargets (retarget ports S) = S := by
  induction ports generalizing S with
  | nil =>
    cases S with
    | nil => rfl
    | cons _ _ => simp at h
  | cons p ports ih =>
    cases S with
    | nil => simp at h
    | cons w S =>
      have := ih S (by simpa using h)
      simp only [retarget, List.zipWith_cons_cons, portTargets, List.map_cons] at this ⊢
      rw [this]

theorem retarget_bits {n : Nat} (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (S : List Wire)
    (h : ports.length = S.length) (a : Nat) : portBits read (retarget ports S) a = portBits read ports a := by
  induction ports generalizing S with
  | nil =>
    cases S with
    | nil => rfl
    | cons _ _ => simp at h
  | cons p ports ih =>
    cases S with
    | nil => simp at h
    | cons w S =>
      have := ih S (by simpa using h)
      simp only [retarget, List.zipWith_cons_cons, portBits, List.map_cons] at this ⊢
      rw [this]

theorem retarget_length {n : Nat} (ports : List (LookupPort n)) (S : List Wire)
    (h : ports.length = S.length) : (retarget ports S).length = S.length := by
  simp [retarget, h]

end
end ShorECDLP.Entrant.WEX
namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.ShorPort
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Clean scratch wires for the output comparison words. -/
def scrPairWires : List Wire :=
  streamLayout.core.poolWire 258 :: (List.range' 259 256).map streamLayout.core.poolWire ++
    [streamLayout.core.poolWire 768]

def scrShortWires : List Wire :=
  streamLayout.core.poolWire 769 :: (List.range' 770 256).map streamLayout.core.poolWire ++
    [streamLayout.core.poolWire 1026]

def scrWires : List Wire := scrPairWires ++ scrShortWires

def scrPairTargets : List Wire := streamLayout.point.finite :: streamLayout.point.x ++ [yLow streamLayout]

def scrShortTargets : List Wire :=
  streamLayout.point.finite :: streamLayout.point.x ++ streamLayout.point.y.take 1

def scrPairBits (rows : Nat → Fin 32768) (r : Nat → ConstantBit 32768) : List (LookupPort 32768) :=
  pairParityPorts streamLayout (wBit rows .infinity) (wFields rows .x) r

def scrShortBits (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  ⟨wBit rows .doubleInfinity, false, streamLayout.point.finite⟩ ::
    indexedPorts streamLayout.point.x (wFields rows .doubleX) true ++
    indexedPorts (streamLayout.point.y.take 1) (fun a _ => wBit rows .doubleY 0 a) true

def scrPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  retarget (scrPairBits rows (wBit rows .y)) scrPairWires ++ retarget (scrShortBits rows) scrShortWires

def scrP1 : Program :=
  zeroWith (fun w => [.CCX w (yLow streamLayout) streamLayout.infinitySelect, .X (yLow streamLayout),
    .CCX w (yLow streamLayout) streamLayout.core.equalNegY]) streamLayout.control (pairPorts streamLayout)

def scrP2 : Program :=
  zeroControlled streamLayout.core.double streamLayout.doubleSelect
    (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258))

/-- One load, Clifford copies for both exception comparisons, one clear. -/
def scrOutCompare (rows : Nat → Fin 32768) : WCode 32768 :=
  [.lookup none (scrPorts rows)] ++
  wLiteral (cxList scrPairWires scrPairTargets) ++
  wZeroWith (wPairTailBare (yLow streamLayout) streamLayout.infinitySelect streamLayout.core.equalNegY)
    streamLayout.control (pairPorts streamLayout) ++
  wLiteral (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
  wLiteral (cxList scrShortWires scrShortTargets) ++
  wLiteral scrP2 ++
  wLiteral (cxList scrShortWires scrShortTargets) ++
  [.lookup none (scrPorts rows)]

def scrOldCompare (rows : Nat → Fin 32768) : WCode 32768 :=
  wPairEqualTight streamLayout streamLayout.infinitySelect streamLayout.core.equalNegY
    (wBit rows .infinity) (wFields rows .x) (wBit rows .y) (wBit rows .negY) ++
  wShortEqual streamLayout streamLayout.core.double streamLayout.doubleSelect (wBit rows .doubleInfinity)
    (wFields rows .doubleX) (wBit rows .doubleY)

theorem scrPairWires_length : scrPairWires.length = 258 := by simp [scrPairWires]
theorem scrShortWires_length : scrShortWires.length = 258 := by simp [scrShortWires]

theorem scr_all_not (S L : List Wire) (h : (S.all fun a => !L.contains a) = true) : ∀ a ∈ S, a ∉ L := by
  intro a ha hl
  have := List.all_eq_true.mp h a ha
  simp [hl] at this

theorem scrWires_nodup : scrWires.Nodup := by decide +kernel
theorem scrWires_pair_targets : ∀ a ∈ scrWires, a ∉ scrPairTargets :=
  scr_all_not _ _ (by decide +kernel)
theorem scrWires_short_targets : ∀ a ∈ scrWires, a ∉ scrShortTargets :=
  scr_all_not _ _ (by decide +kernel)
theorem scrWires_y : ∀ a ∈ scrWires, a ∉ [yLow streamLayout] :=
  scr_all_not _ _ (by decide +kernel)
theorem scrWires_p1 : ∀ a ∈ scrWires, a ∉ (streamLayout.control :: [yLow streamLayout,
    streamLayout.infinitySelect, streamLayout.core.equalNegY] ++ (pairPorts streamLayout).flatMap ZeroBit.wires) :=
  scr_all_not _ _ (by decide +kernel)
theorem scrWires_p2 : ∀ a ∈ scrWires, a ∉ (streamLayout.core.double :: streamLayout.doubleSelect ::
    (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).flatMap ZeroBit.wires) :=
  scr_all_not _ _ (by decide +kernel)

attribute [local irreducible] streamLayout

theorem scrWires_pool (a : Wire) (ha : a ∈ scrWires) : a ∈ streamLayout.dialogPool := by
  simp only [scrWires, scrPairWires, scrShortWires, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_range'_1, List.not_mem_nil, or_false] at ha
  rcases ha with ((rfl | ⟨i, hi, rfl⟩) | rfl) | ((rfl | ⟨i, hi, rfl⟩) | rfl) <;>
    exact deltaPool_mem_dialog _ (by omega)

theorem scrP1_wires (a : Wire) (ha : a ∈ scrWires) : a ∉ wires scrP1 := by
  have htail (c : Wire) : wires
      ([.CCX c (yLow streamLayout) streamLayout.infinitySelect, .X (yLow streamLayout),
        .CCX c (yLow streamLayout) streamLayout.core.equalNegY] : Program) ⊆
      (c :: [yLow streamLayout, streamLayout.infinitySelect, streamLayout.core.equalNegY]).toFinset := by
    intro q hq
    simp [wires, Instr.wires] at hq ⊢
    tauto
  have hz := deltaZeroWith_support
    (fun c : Wire => ([.CCX c (yLow streamLayout) streamLayout.infinitySelect, .X (yLow streamLayout),
      .CCX c (yLow streamLayout) streamLayout.core.equalNegY] : Program))
    ([yLow streamLayout, streamLayout.infinitySelect, streamLayout.core.equalNegY] : List Wire) htail
    streamLayout.control (pairPorts streamLayout)
  intro hq
  exact scrWires_p1 a ha (List.mem_toFinset.mp (hz hq))

theorem scrP2_wires (a : Wire) (ha : a ∈ scrWires) : a ∉ wires scrP2 := by
  intro hq
  rw [scrP2, zeroControlled_wires] at hq
  exact scrWires_p2 a ha (List.mem_toFinset.mp hq)

theorem scrPairBits_length (rows : Nat → Fin 32768) (r : Nat → ConstantBit 32768) :
    (scrPairBits rows r).length = 258 := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  simp [scrPairBits, pairParityPorts, hx]

theorem scrShortBits_length (rows : Nat → Fin 32768) : (scrShortBits rows).length = 258 := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  simp [scrShortBits, hx, hy]

theorem scrPairBits_targets (rows : Nat → Fin 32768) (r : Nat → ConstantBit 32768) :
    portTargets (scrPairBits rows r) = scrPairTargets := by
  have h := indexedPorts_targets streamLayout.point.x (wFields rows .x) true
  simp only [portTargets] at h
  simp only [scrPairBits, pairParityPorts, scrPairTargets, portTargets, List.map_append, List.map_cons,
    List.map_nil, h, List.cons_append]

theorem scrShortBits_targets (rows : Nat → Fin 32768) :
    portTargets (scrShortBits rows) = scrShortTargets := by
  have h := indexedPorts_targets streamLayout.point.x (wFields rows .doubleX) true
  have h' := indexedPorts_targets (streamLayout.point.y.take 1) (fun a _ => wBit rows .doubleY 0 a) true
  simp only [portTargets] at h h'
  simp only [scrShortBits, scrShortTargets, portTargets, List.map_append, List.map_cons, h, h',
    List.cons_append]

theorem scrPorts_targets (rows : Nat → Fin 32768) : portTargets (scrPorts rows) = scrWires := by
  have h1 := retarget_targets (scrPairBits rows (wBit rows .y)) scrPairWires
    ((scrPairBits_length _ _).trans scrPairWires_length.symm)
  have h2 := retarget_targets (scrShortBits rows) scrShortWires
    ((scrShortBits_length _).trans scrShortWires_length.symm)
  simp only [portTargets] at h1 h2
  simp only [scrPorts, scrWires, portTargets, List.map_append, h1, h2]

theorem scrPorts_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (scrPorts rows) a =
      portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a := by
  have h1 := retarget_bits read (scrPairBits rows (wBit rows .y)) scrPairWires
    ((scrPairBits_length _ _).trans scrPairWires_length.symm) a
  have h2 := retarget_bits read (scrShortBits rows) scrShortWires
    ((scrShortBits_length _).trans scrShortWires_length.symm) a
  simp only [portBits] at h1 h2
  simp only [scrPorts, portBits, List.map_append, h1, h2]

theorem scr_lookup_inst (read : ConstantBit 32768 → Bool) (ports : List (LookupPort 32768)) (a : Nat) :
    (specialize ([.lookup none ports] : WCode 32768) a).instantiate read =
      xBits (portTargets ports) (portBits read ports a) := by
  rw [← portTemplate_none_inst]
  simp [specialize, WInstr.specialize]

theorem scr_chain_inst (read : ConstantBit 32768 → Bool) (a : Nat) :
    (specialize (wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.infinitySelect
      streamLayout.core.equalNegY) streamLayout.control (pairPorts streamLayout)) a).instantiate read = scrP1 := by
  rw [specialize_zeroWith _ (fun w => Tmpl.lit [.CCX w (yLow streamLayout) streamLayout.infinitySelect,
    .X (yLow streamLayout), .CCX w (yLow streamLayout) streamLayout.core.equalNegY]) a
    (fun w => by simp [wPairTailBare])]
  apply zeroWithT_inst
  intro w
  simp

theorem scrOut_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (scrOutCompare rows) a).instantiate read =
      xBits scrWires (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
      (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets))))) ++
      xBits scrWires (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) := by
  simp only [scrOutCompare, specialize_append, Tmpl.instantiate_append, scr_lookup_inst, specialize_literal,
    Tmpl.instantiate_lit, scr_chain_inst, scrPorts_targets, scrPorts_bits, List.append_assoc]

theorem scrOld_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (scrOldCompare rows) a).instantiate read =
      xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++
      (scrP1 ++ (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .negY)) a) ++
      (xBits scrShortTargets (portBits read (scrShortBits rows) a) ++
      (scrP2 ++ xBits scrShortTargets (portBits read (scrShortBits rows) a))))) := by
  have h1 (r : Nat → ConstantBit 32768) : wPairXorParity streamLayout (wBit rows .infinity) (wFields rows .x) r =
      [.lookup none (scrPairBits rows r)] := rfl
  have h2 : wShortXor streamLayout (wBit rows .doubleInfinity) (wFields rows .doubleX) (wBit rows .doubleY) =
      [.lookup none (scrShortBits rows)] := rfl
  have h3 : ∀ a, specialize (wLiteral (n := 32768) scrP2) a = Tmpl.lit scrP2 := fun a => specialize_literal _ _
  have h4 : wLiteral (n := 32768) (zeroControlled streamLayout.core.double streamLayout.doubleSelect
      (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258))) = wLiteral scrP2 := rfl
  simp only [scrOldCompare, wPairEqualTight, wShortEqual, h1, h2, h4, specialize_append, Tmpl.instantiate_append,
    scr_lookup_inst, h3, Tmpl.instantiate_lit, scr_chain_inst, scrPairBits_targets, scrShortBits_targets,
    List.append_assoc]

theorem scr_parity_fix (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat)
    (hop : read (wBit rows .negY 0 a) = !(read (wBit rows .y 0 a))) (m : List Bool) (s : State) :
    run (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ [.X (yLow streamLayout)]) m s =
      run (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .negY)) a)) m s := by
  let P0 : List (LookupPort 32768) := ⟨wBit rows .infinity, false, streamLayout.point.finite⟩ ::
    indexedPorts streamLayout.point.x (wFields rows .x) true
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hl : (streamLayout.point.finite :: streamLayout.point.x).length = (portBits read P0 a).length := by
    simp [portBits, P0, hx]
  have hb (r : Nat → ConstantBit 32768) : portBits read (scrPairBits rows r) a =
      portBits read P0 a ++ [decide (read (r a) = false)] := by
    simp [portBits, scrPairBits, pairParityPorts, P0]
  have hT : scrPairTargets = (streamLayout.point.finite :: streamLayout.point.x) ++ [yLow streamLayout] := rfl
  rw [hb, hb, hT, xBits_snoc _ _ _ _ hl, xBits_snoc _ _ _ _ hl]
  rw [hop]
  cases hr : read (wBit rows .y 0 a)
  · simp only [Bool.not_false, decide_true, reduceIte, Bool.true_eq_false, decide_false, Bool.false_eq_true]
    rw [List.append_assoc, run_append, List.append_nil]
    have hxx : ∀ (n : List Bool) (u : State),
        run ([.X (yLow streamLayout)] ++ [.X (yLow streamLayout)]) n u = u := by
      intro n u
      apply State.extensionality
      · rfl
      · funext q
        by_cases hq : q = yLow streamLayout
        · subst hq
          simp [run, writeBit]
        · simp [run, writeBit, Function.update_of_ne hq]
    rw [hxx, run_take]
  · simp only [Bool.not_true, decide_true, reduceIte, Bool.true_eq_false, decide_false, Bool.false_eq_true,
      List.append_nil]

theorem scrCompare_sim (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    ScrSim scrWires (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a)
      (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets)))))
      (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++
        (scrP1 ++ ((xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ [.X (yLow streamLayout)]) ++
        (xBits scrShortTargets (portBits read (scrShortBits rows) a) ++
        (scrP2 ++ xBits scrShortTargets (portBits read (scrShortBits rows) a)))))) := by
  have hlA : scrPairWires.length = (portBits read (scrPairBits rows (wBit rows .y)) a).length := by
    simp [portBits, scrPairBits_length, scrPairWires_length]
  have hlB : scrShortWires.length = (portBits read (scrShortBits rows) a).length := by
    simp [portBits, scrShortBits_length, scrShortWires_length]
  have h1 := ScrSim.cx scrWires scrPairWires scrPairTargets
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) _
    (xMask_map_left _ _ _ _ scrWires_nodup hlA)
    (fun w hw => List.mem_append_left _ hw) scrWires_pair_targets
  have h2 := ScrSim.cx scrWires scrShortWires scrShortTargets
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) _
    (xMask_map_right _ _ _ _ scrWires_nodup hlA hlB)
    (fun w hw => List.mem_append_right _ hw) scrWires_short_targets
  have hp1 := ScrSim.disjoint scrWires
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) scrP1 scrP1_wires
  have hp2 := ScrSim.disjoint scrWires
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) scrP2 scrP2_wires
  have hx := ScrSim.disjoint scrWires
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a)
    ([.X (yLow streamLayout)] : Program) (by
      intro w hw hq
      apply scrWires_y w hw
      simpa [wires, Instr.wires] using hq)
  exact h1.append (hp1.append ((h1.append hx).append (h2.append (hp2.append h2))))

theorem scrCompare_records (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    measurementCount ((specialize (scrOutCompare rows) a).instantiate read) =
      measurementCount ((specialize (scrOldCompare rows) a).instantiate read) := by
  rw [scrOut_inst, scrOld_inst]
  simp only [measurementCount_append, xBits_records, cxList_records, measurementCount]
  omega

theorem scrCompare_run (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat)
    (hop : read (wBit rows .negY 0 a) = !(read (wBit rows .y 0 a))) (m : List Bool) (s : State)
    (hs : ∀ w ∈ scrWires, s.basis w = false) :
    run ((specialize (scrOutCompare rows) a).instantiate read) m s =
      run ((specialize (scrOldCompare rows) a).instantiate read) m s := by
  rw [scrOut_inst, scr_sandwich _ _ _ _ (scrCompare_sim read rows a) m s hs, scrOld_inst]
  have h := run_replace_inside
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ scrP1)
    (xBits scrShortTargets (portBits read (scrShortBits rows) a) ++
      (scrP2 ++ xBits scrShortTargets (portBits read (scrShortBits rows) a)))
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ [.X (yLow streamLayout)])
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .negY)) a))
    (by simp [xBits_records, measurementCount])
    (fun m st => scr_parity_fix read rows a hop m st) m s
  simpa only [List.append_assoc] using h

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The corner writes share one traversal per point value. -/
def thirdCorners (L : ControlledPointLayout) (C : Point) : Program :=
  (negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c ++
  ([.CX L.doubleSelect L.core.equalNegY] ++ maskedPointConstant L.core.equalNegY L.point (C+C) ++
    [.CX L.doubleSelect L.core.equalNegY]) ++
  ([.CX L.infinitySelect L.doubleSelect] ++ maskedPointConstant L.doubleSelect L.point C ++
    [.CX L.infinitySelect L.doubleSelect]) ++
  ([.CX L.genericSelect L.core.equalNegY] ++ maskedPointConstant L.core.equalNegY L.point (-C) ++
    [.CX L.genericSelect L.core.equalNegY])

theorem thirdCorners_records (L : ControlledPointLayout) (C : Point) :
    measurementCount (thirdCorners L C) = measurementCount (secondCorners L C) := by
  simp [thirdCorners, secondCorners, measurementCount_append, maskedPointConstant_counts, measurementCount]

theorem thirdCorners_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (m : List Bool) (st : State) :
    run (thirdCorners L C) m st = run (secondCorners L C) m st := by
  have hpoint : (PointAddLayout.pointWires L.point).Nodup :=
    (L.dialogUsed_nodup hn).of_append_left.of_append_left.of_append_left
  have away (q : Wire) (hq : q ∈ L.inPlaceFlags) : q ∉ PointAddLayout.pointWires L.point := by
    intro bad
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have hb := List.count_pos_iff.mpr bad
    have hf := List.count_pos_iff.mpr hq
    simp only [dialogUsedWires, List.count_append] at h
    omega
  have hO := away L.infinitySelect (by simp [inPlaceFlags])
  have hD := away L.doubleSelect (by simp [inPlaceFlags])
  have hH := away L.core.equalNegY (by simp [inPlaceFlags])
  have hxl : L.point.x.length = 256 := hw.inputX
  have hyl : L.point.y.length = 256 := hw.inputY
  have hDH : L.doubleSelect ≠ L.core.equalNegY := by
    have sep := dialogFlag_separation (L := L) hn
    simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
    tauto
  have hOD : L.infinitySelect ≠ L.doubleSelect := by
    have sep := dialogFlag_separation (L := L) hn
    simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
    tauto
  let mH2 := maskedPointConstant L.core.equalNegY L.point (C+C)
  let mD2 := maskedPointConstant L.doubleSelect L.point (C+C)
  let mO := maskedPointConstant L.infinitySelect L.point C
  let mD := maskedPointConstant L.doubleSelect L.point C
  let X : Program := [.CX L.infinitySelect L.doubleSelect] ++ mD ++ [.CX L.infinitySelect L.doubleSelect]
  let Z : Program := [.CX L.doubleSelect L.core.equalNegY] ++ mH2 ++ [.CX L.doubleSelect L.core.equalNegY]
  have hrec (p : Program) (h : measurementCount p = 0) (n : List Bool) (u : State) : run p n u = run p ([]) u :=
    run_no_records p h n u
  have hX0 : measurementCount X = 0 := by
    simp [X, mD, measurementCount_append, maskedPointConstant_counts, measurementCount]
  have hZ0 : measurementCount Z = 0 := by
    simp [Z, mH2, measurementCount_append, maskedPointConstant_counts, measurementCount]
  have hH20 : measurementCount mH2 = 0 := (maskedPointConstant_counts _ _ _).2
  have hD20 : measurementCount mD2 = 0 := (maskedPointConstant_counts _ _ _).2
  have hmXD (u : State) : run (X ++ mD2) ([]) u = run (mD2 ++ X) ([]) u := by
    have hmerge (v : State) : run X ([]) v = run (mO ++ mD) ([]) v :=
      (merged_point_masks L.point L.infinitySelect L.doubleSelect C hpoint hO hD hOD v ([])).symm
    have hc := maskChain_commute L.point ([(L.infinitySelect, C), (L.doubleSelect, C)] : List (Wire × Point)) L.doubleSelect (C+C) hpoint hD
      (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact hO
        · exact hD)
      hxl hyl u
    have hchain : maskChain L.point ([(L.infinitySelect, C), (L.doubleSelect, C)] : List (Wire × Point)) = mO ++ mD := by
      simp [maskChain, mO, mD]
    rw [hchain] at hc
    rw [run_append_nil, hmerge, ← run_append_nil, hc, run_append_nil, run_append_nil mD2, hmerge]
  have hZrun (u : State) : run (mH2 ++ mD2) ([]) u = run Z ([]) u := by
    have hc := masked_points_commute L.point L.core.equalNegY L.doubleSelect (C+C) (C+C) hpoint hH hD hxl hyl u
    exact hc.trans (merged_point_masks L.point L.doubleSelect L.core.equalNegY (C+C) hpoint hD hH hDH u ([]))
  have hmid (n : List Bool) (u : State) : run (mH2 ++ X ++ mD2) n u = run (Z ++ X) n u := by
    have h1 : measurementCount (mH2 ++ X ++ mD2) = 0 := by
      simp only [measurementCount_append, hH20, hX0, hD20]
    have h2 : measurementCount (Z ++ X) = 0 := by simp only [measurementCount_append, hZ0, hX0]
    rw [hrec _ h1, hrec _ h2, List.append_assoc, run_append_nil, hmXD, ← run_append_nil, ← List.append_assoc,
      run_append_nil, hZrun, ← run_append_nil]
  have h := run_replace_inside
    ((negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c)
    ([.CX L.genericSelect L.core.equalNegY] ++ maskedPointConstant L.core.equalNegY L.point (-C) ++
      [.CX L.genericSelect L.core.equalNegY])
    (Z ++ X) (mH2 ++ X ++ mD2)
    (by simp only [measurementCount_append, hH20, hX0, hD20, hZ0])
    (fun n u => (hmid n u).symm) m st
  simpa only [thirdCorners, secondCorners, Z, X, mH2, mD2, mD, List.append_assoc] using h

/-- The corner code matching `thirdCorners`. -/
def scrCorners (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ((negateYLayout streamLayout).program streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c) ++
  wLiteral ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ++
  wPoint streamLayout.core.equalNegY streamLayout.point (wBit rows .doubleInfinity) (wFields rows .doubleX)
    (wFields rows .doubleY) ++
  wLiteral ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ++
  wLiteral ([.CX streamLayout.infinitySelect streamLayout.doubleSelect]) ++
  wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) ++
  wLiteral ([.CX streamLayout.infinitySelect streamLayout.doubleSelect]) ++
  wLiteral ([.CX streamLayout.genericSelect streamLayout.core.equalNegY]) ++
  wPoint streamLayout.core.equalNegY streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .negY) ++
  wLiteral ([.CX streamLayout.genericSelect streamLayout.core.equalNegY])

theorem scrCorners_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) (C : Point)
    (h : RowReads read (rows address) C) :
    (specialize (scrCorners rows) address).instantiate read = thirdCorners streamLayout C := by
  have hxl : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hyl : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  have fC : read (bitRef (rows address) .infinity 0) = !pointFinite C := by
    rw [h.bit _ 0 (by decide), infinity_bit]
  have fN : read (bitRef (rows address) .infinity 0) = !pointFinite (-C) := by
    rw [fC, ECDSAAdd.ShorPort.pointFinite_neg]
  have fD : read (bitRef (rows address) .doubleInfinity 0) = !pointFinite (C+C) := by
    rw [h.bit _ 0 (by decide), doubleInfinity_bit]
  have xC := fieldBits_reads h .x _ (field_x C)
  have yC := fieldBits_reads h .y _ (field_y C)
  have xN : ∀ i < 256, read (fieldBits (rows address) .x i) = (pointX (-C)).testBit i := by
    rw [ECDSAAdd.ShorPort.pointX_neg]
    exact xC
  have yN := fieldBits_reads h .negY _ (field_negY C)
  have xD := fieldBits_reads h .doubleX _ (field_doubleX C)
  have yD := fieldBits_reads h .doubleY _ (field_doubleY C)
  rw [← hxl] at xC xN xD
  rw [← hyl] at yC yN yD
  simp only [scrCorners, specialize_append, specialize_point, specialize_literal,
    wBit, wFields, Tmpl.instantiate_append, Tmpl.instantiate_lit,
    maskedPointT_inst read _ streamLayout.point _ _ _ C fC xC yC,
    maskedPointT_inst read _ streamLayout.point _ _ _ (C+C) fD xD yD,
    maskedPointT_inst read _ streamLayout.point _ _ _ (-C) fN xN yN,
    thirdCorners]
  simp only [List.append_assoc]


theorem scrCheck_pair : (scrPairWires ++ scrPairTargets).all
    (fun w => decide (fixedPort w ∨ oldWork w) && streamLayout.dialogUsedWires.contains w) = true := by decide +kernel
theorem scrCheck_short : (scrShortWires ++ scrShortTargets).all
    (fun w => decide (fixedPort w ∨ oldWork w) && streamLayout.dialogUsedWires.contains w) = true := by decide +kernel

theorem scrCx_facts (S T : List Wire)
    (hc : (S ++ T).all (fun w => decide (fixedPort w ∨ oldWork w) && streamLayout.dialogUsedWires.contains w) = true)
    (hd : ∀ a ∈ S, a ∉ T) :
    ECDSAAdd.wires (cxList S T) ⊆ streamLayout.dialogUsedWires.toFinset ∧ GatePhysical (cxList S T) ∧
      ECDSAAdd.wires (cxList S T) ⊆ sourceSupport.toFinset := by
  have key (q : Wire) (hq : q ∈ ECDSAAdd.wires (cxList S T)) :
      (fixedPort q ∨ oldWork q) ∧ q ∈ streamLayout.dialogUsedWires := by
    have hm : q ∈ S ++ T := List.mem_append.mpr (cxList_wires S T q hq)
    have := List.all_eq_true.mp hc q hm
    simpa using this
  refine ⟨?_, cxList_physical S T hd, ?_⟩
  · intro q hq
    exact List.mem_toFinset.mpr (key q hq).2
  · intro q hq
    exact List.mem_toFinset.mpr ((sourceSupport_mem q).mpr (key q hq).1)

theorem scrCorner_shape {n : Nat} (neg sw s1 s2 : Program) (ca cb cc cd : Option Wire)
    (pa pb pc pd : List (LookupPort n)) (ht : ECDSAAdd.toffoliCount sw = 0) (hm : ECDSAAdd.measurementCount sw = 0)
    (hs : ECDSAAdd.Challenge.gateSlots sw = 1) :
    let new : WCode n := wLiteral neg ++ wLiteral sw ++ [.lookup ca pa] ++ wLiteral sw ++ wLiteral s1 ++
      [.lookup cb pb] ++ wLiteral s1 ++ wLiteral s2 ++ [.lookup cc pc] ++ wLiteral s2
    let old : WCode n := wLiteral neg ++ [.lookup ca pa] ++ wLiteral s1 ++ [.lookup cb pb] ++ wLiteral s1 ++
      [.lookup cd pd] ++ wLiteral s2 ++ [.lookup cc pc] ++ wLiteral s2
    literalToffolis new = literalToffolis old ∧ literalRecords new = literalRecords old ∧
      traversals new + 1 = traversals old ∧ literalSlotSum new = literalSlotSum old + 2 ∧
      portTotal new ≤ portTotal old := by
  dsimp only
  simp only [wLiteral, literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', literalToffolis, literalRecords, traversals, literalSlotSum, portTotal, ht, hm, hs]
  exact ⟨by omega, by omega, trivial, by omega, by omega⟩

theorem scrCorners_counts (rows : Nat → Fin 32768) :
    literalToffolis (scrCorners rows) = literalToffolis (wCornersOne streamLayout rows) ∧
    literalRecords (scrCorners rows) = literalRecords (wCornersOne streamLayout rows) ∧
    traversals (scrCorners rows) + 1 = traversals (wCornersOne streamLayout rows) ∧
    literalSlotSum (scrCorners rows) = literalSlotSum (wCornersOne streamLayout rows) + 2 ∧
    portTotal (scrCorners rows) ≤ portTotal (wCornersOne streamLayout rows) :=
  scrCorner_shape _ ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY] : Program)
    ([.CX streamLayout.infinitySelect streamLayout.doubleSelect] : Program)
    ([.CX streamLayout.genericSelect streamLayout.core.equalNegY] : Program) _ _ _ _ _ _ _ _ rfl rfl rfl

theorem scrCorners_cases (rows : Nat → Fin 32768) (i : WInstr 32768) (h : i ∈ scrCorners rows) :
    i = WInstr.literal ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ∨ i ∈ wCornersOne streamLayout rows := by
  simp only [scrCorners, wCornersOne, wPoint, wLiteral, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  tauto

theorem scrFlagSwap_facts :
    ECDSAAdd.wires ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY] : Program) ⊆ streamLayout.dialogUsedWires.toFinset ∧
      GatePhysical ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY] : Program) ∧
      ECDSAAdd.wires ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY] : Program) ⊆ sourceSupport.toFinset := by
  have hc : ([streamLayout.doubleSelect, streamLayout.core.equalNegY] : List Wire).all
      (fun w => decide (fixedPort w ∨ oldWork w) && streamLayout.dialogUsedWires.contains w) = true := by decide +kernel
  have hne : streamLayout.doubleSelect ≠ streamLayout.core.equalNegY := by decide +kernel
  have hk := scrCx_facts ([streamLayout.doubleSelect] : List Wire) ([streamLayout.core.equalNegY] : List Wire) hc
    (by intro a ha; simp only [List.mem_singleton] at ha ⊢; rw [ha]; exact hne)
  exact hk

theorem scrCompare_counts (rows : Nat → Fin 32768) :
    literalToffolis (scrOutCompare rows) = literalToffolis (scrOldCompare rows) ∧
    literalRecords (scrOutCompare rows) = literalRecords (scrOldCompare rows) ∧
    traversals (scrOutCompare rows) + 2 = traversals (scrOldCompare rows) := by
  have ht := tight_traversals streamLayout streamLayout.infinitySelect streamLayout.core.equalNegY
    (wBit rows .infinity) (wFields rows .x) (wBit rows .y) (wBit rows .negY)
  have hz : traversals (wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.infinitySelect
      streamLayout.core.equalNegY) streamLayout.control (pairPorts streamLayout)) = 0 :=
    traversals_zeroWith _ 0 (fun _ => rfl) _ _
  have hs : traversals (wShortEqual streamLayout streamLayout.core.double streamLayout.doubleSelect
      (wBit rows .doubleInfinity) (wFields rows .doubleX) (wBit rows .doubleY)) = 2 := by
    simp [wShortEqual, wShortXor, wLiteral, traversals_append, traversals]
  refine ⟨?_, ?_, ?_⟩
  · simp [scrOutCompare, scrOldCompare, wPairEqualTight, wPairXorParity, wShortEqual, wShortXor, wLiteral,
      literalToffolis_append, literalToffolis, cxList_toffoli, ECDSAAdd.toffoliCount, scrP2]
  · simp [scrOutCompare, scrOldCompare, wPairEqualTight, wPairXorParity, wShortEqual, wShortXor, wLiteral,
      literalRecords_append, literalRecords, cxList_records, ECDSAAdd.measurementCount, scrP2]
  · simp only [scrOutCompare, scrOldCompare, traversals_append, ht, hs, hz]
    rfl

theorem scrCompare_slots_ports (rows : Nat → Fin 32768) :
    literalSlotSum (scrOutCompare rows) = literalSlotSum (scrOldCompare rows) + 1033 ∧
    portTotal (scrOutCompare rows) = portTotal (scrOldCompare rows) := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  have hpt : scrPairTargets.length = 258 := by simp [scrPairTargets, hx]
  have hst : scrShortTargets.length = 258 := by simp [scrShortTargets, hx, hy]
  have hzp : portTotal (wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.infinitySelect
      streamLayout.core.equalNegY) streamLayout.control (pairPorts streamLayout)) = 0 :=
    portTotal_zeroWith _ 0 (fun _ => rfl) _ _
  have hpl : (scrPorts (rows)).length = 516 := by
    simp only [scrPorts, List.length_append, retarget_length _ _ ((scrPairBits_length _ _).trans scrPairWires_length.symm),
      retarget_length _ _ ((scrShortBits_length _).trans scrShortWires_length.symm), scrPairWires_length, scrShortWires_length]
  constructor
  · simp [scrOutCompare, scrOldCompare, wPairEqualTight, wPairXorParity, wShortEqual, wShortXor, wLiteral,
      literalSlotSum_append', literalSlotSum, ECDSAAdd.Challenge.gateSlots_append, cxList_slots, scrPairWires_length,
      scrShortWires_length, hpt, hst, scrP2]
    simp [ECDSAAdd.Challenge.gateSlots, ECDSAAdd.Challenge.instructionSlots]
    omega
  · have ho := tight_pair_ports_exact streamLayout streamLayout.infinitySelect streamLayout.core.equalNegY
      (wBit rows .infinity) (wFields rows .x) (wBit rows .y) (wBit rows .negY)
    simp only [scrOutCompare, scrOldCompare, portTotal_append', ho, hzp]
    simp [wShortEqual, wShortXor, wLiteral, portTotal_append', portTotal, hpl, hx, hy]

theorem scrY_facts :
    ECDSAAdd.wires ([.X (yLow streamLayout)] : Program) ⊆ streamLayout.dialogUsedWires.toFinset ∧
      GatePhysical ([.X (yLow streamLayout)] : Program) ∧
      ECDSAAdd.wires ([.X (yLow streamLayout)] : Program) ⊆ sourceSupport.toFinset := by
  have hc : ([yLow streamLayout] : List Wire).all
      (fun w => decide (fixedPort w ∨ oldWork w) && streamLayout.dialogUsedWires.contains w) = true := by decide +kernel
  have key : (fixedPort (yLow streamLayout) ∨ oldWork (yLow streamLayout)) ∧ yLow streamLayout ∈ streamLayout.dialogUsedWires := by
    simpa using hc
  have hw (q : Wire) (hq : q ∈ ECDSAAdd.wires ([.X (yLow streamLayout)] : Program)) : q = yLow streamLayout := by
    simpa [ECDSAAdd.wires, Instr.wires] using hq
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rw [hw q hq]
    exact List.mem_toFinset.mpr key.2
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    simp [ECDSAAdd.RecordedQuantum.PhysicalInstr, ProperGate]
  · intro q hq
    rw [hw q hq]
    exact List.mem_toFinset.mpr ((sourceSupport_mem _).mpr key.1)

theorem scr_lit_inj {n : Nat} {p q : Program} (h : WInstr.literal p ∈ (wLiteral q : WCode n)) : p = q := by
  simpa [wLiteral] using h

theorem scr_lookup_ne {n : Nat} {p : Program} {c : Option Wire} {P : List (LookupPort n)}
    (h : WInstr.literal p ∈ ([.lookup c P] : WCode n)) : False := by
  simp at h

theorem scrCompare_literal_cases (rows : Nat → Fin 32768) (p : Program)
    (hp : WInstr.literal p ∈ scrOutCompare rows) :
    p = cxList scrPairWires scrPairTargets ∨ p = cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)] ∨
      p = cxList scrShortWires scrShortTargets ∨ WInstr.literal p ∈ scrOldCompare rows := by
  have hold (hm : WInstr.literal p ∈ wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.infinitySelect
      streamLayout.core.equalNegY) streamLayout.control (pairPorts streamLayout)) :
      WInstr.literal p ∈ scrOldCompare rows := by
    simp only [scrOldCompare, wPairEqualTight, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hm))
  have hold2 (he : p = scrP2) : WInstr.literal p ∈ scrOldCompare rows := by
    subst he
    unfold scrOldCompare wShortEqual
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  simp only [scrOutCompare, List.mem_append] at hp
  rcases hp with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact (scr_lookup_ne h).elim
  · exact Or.inl (scr_lit_inj h)
  · exact Or.inr (Or.inr (Or.inr (hold h)))
  · exact Or.inr (Or.inl (scr_lit_inj h))
  · exact Or.inr (Or.inr (Or.inl (scr_lit_inj h)))
  · exact Or.inr (Or.inr (Or.inr (hold2 (scr_lit_inj h))))
  · exact Or.inr (Or.inr (Or.inl (scr_lit_inj h)))
  · exact (scr_lookup_ne h).elim

theorem scrCompare_lookup_cases (rows : Nat → Fin 32768) (c : Option Wire) (ports : List (LookupPort 32768))
    (hp : WInstr.lookup c ports ∈ scrOutCompare rows) :
    (c = none ∧ ports = scrPorts rows) ∨ WInstr.lookup c ports ∈ scrOldCompare rows := by
  simp only [scrOutCompare, wLiteral, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    reduceCtorEq, false_or, WInstr.lookup.injEq] at hp
  have hold (hm : WInstr.lookup c ports ∈ wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.infinitySelect
      streamLayout.core.equalNegY) streamLayout.control (pairPorts streamLayout)) :
      WInstr.lookup c ports ∈ scrOldCompare rows := by
    simp only [scrOldCompare, wPairEqualTight, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hm))
  tauto

theorem scrPorts_geometry (rows : Nat → Fin 32768) :
    lookupPlacedOK windowBits windowPaths windowRoot (.lookup none (scrPorts rows)) = true := by
  change geometryOK windowBits windowPaths windowRoot none (portTargets (scrPorts rows)) = true
  rw [scrPorts_targets]
  decide +kernel

theorem scrPorts_sourceOK (rows : Nat → Fin 32768) :
    sourceLookupOK (.lookup none (scrPorts rows)) = true := by
  simp only [sourceLookupOK, Option.toList_none, List.all_nil, Bool.true_and, scrPorts_targets]
  decide +kernel


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The output half of the addition body: corner writes and both output comparisons share their
loaded words. -/
def portSuffixCode (rows : Nat → Fin 32768) : WCode 32768 :=
  scrCorners rows ++ wLiteral (pointDialogGenericFlag streamLayout) ++
  scrOutCompare rows ++
  wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
  wLiteral (Arith.padding (streamLayout.core.poolWire 0) 49864)

theorem portSuffix_shape (rows : Nat → Fin 32768) :
    let Z : WCode 32768 := wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
      wLiteral (Arith.padding (streamLayout.core.poolWire 0) 49864)
    portSuffixCode rows = (scrCorners rows ++ wLiteral (pointDialogGenericFlag streamLayout)) ++ scrOutCompare rows ++ Z ∧
    WEXUnlookup.suffixCode streamLayout rows =
      (wCornersOne streamLayout rows ++ wLiteral (pointDialogGenericFlag streamLayout)) ++ scrOldCompare rows ++ Z := by
  dsimp only
  constructor
  · simp only [portSuffixCode, List.append_assoc]
  · simp only [WEXUnlookup.suffixCode, scrOldCompare, List.append_assoc]

theorem portSuffix_inst_pre (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) (C : Point)
    (row : RowReads read (rows address) C) :
    (specialize (wCornersOne streamLayout rows ++ wLiteral (pointDialogGenericFlag streamLayout)) address).instantiate read =
      secondCorners streamLayout C ++ pointDialogGenericFlag streamLayout ∧
    (specialize (scrCorners rows ++ wLiteral (pointDialogGenericFlag streamLayout)) address).instantiate read =
      thirdCorners streamLayout C ++ pointDialogGenericFlag streamLayout := by
  constructor
  · simp only [specialize_append, Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit,
      wCornersOne_inst read streamLayout streamLayout_widths rows address C row]
  · simp only [specialize_append, Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit,
      scrCorners_inst read rows address C row]

theorem portSuffix_records (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) (C : Point)
    (row : RowReads read (rows address) C) :
    measurementCount ((specialize (portSuffixCode rows) address).instantiate read) =
      measurementCount ((specialize (WEXUnlookup.suffixCode streamLayout rows) address).instantiate read) := by
  have hs := portSuffix_shape rows
  dsimp only at hs
  rw [hs.1, hs.2]
  have hp := portSuffix_inst_pre read rows address C row
  simp only [specialize_append, Tmpl.instantiate_append, measurementCount_append] at hp ⊢
  have h1 := congrArg measurementCount hp.1
  have h2 := congrArg measurementCount hp.2
  simp only [measurementCount_append, Tmpl.instantiate_append, thirdCorners_records] at h1 h2
  have h3 := scrCompare_records read rows address
  simp only [h1, h2, h3]

theorem portSuffix_run (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) (C : Point)
    (row : RowReads read (rows address) C)
    (hop : read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address)))
    (m : List Bool) (s : State)
    (hclean : ∀ n, ∀ w ∈ scrWires,
      (run (secondCorners streamLayout C ++ pointDialogGenericFlag streamLayout) n s).basis w = false) :
    run ((specialize (portSuffixCode rows) address).instantiate read) m s =
      run ((specialize (WEXUnlookup.suffixCode streamLayout rows) address).instantiate read) m s := by
  have hs := portSuffix_shape rows
  dsimp only at hs
  rw [hs.1, hs.2]
  have hp := portSuffix_inst_pre read rows address C row
  have hrecp : measurementCount (thirdCorners streamLayout C ++ pointDialogGenericFlag streamLayout) =
      measurementCount (secondCorners streamLayout C ++ pointDialogGenericFlag streamLayout) := by
    simp only [measurementCount_append, thirdCorners_records]
  have hrunp (n : List Bool) (u : State) : run (thirdCorners streamLayout C ++ pointDialogGenericFlag streamLayout) n u =
      run (secondCorners streamLayout C ++ pointDialogGenericFlag streamLayout) n u := by
    simp only [run_append, thirdCorners_records, thirdCorners_run streamLayout streamLayout_widths streamLayout_nodup]
  have hsp (A B D : WCode 32768) : (specialize (A ++ B ++ D) address).instantiate read =
      (specialize A address).instantiate read ++ (specialize B address).instantiate read ++
        (specialize D address).instantiate read := by
    simp only [specialize_append, Tmpl.instantiate_append]
  rw [hsp _ (scrOutCompare rows), hsp _ (scrOldCompare rows), hp.1, hp.2]
  generalize thirdCorners streamLayout C ++ pointDialogGenericFlag streamLayout = pre' at hrecp hrunp ⊢
  generalize secondCorners streamLayout C ++ pointDialogGenericFlag streamLayout = pre at hrecp hrunp hclean ⊢
  simp only [run_append, measurementCount_append, hrecp, hrunp, scrCompare_records read rows address]
  rw [scrCompare_run read rows address hop _ _ (hclean _)]

theorem portSuffix_middle (A B B' D : Program) (hmc : measurementCount B = measurementCount B') (s : State)
    (h : ∀ k n, run B n (run A k s) = run B' n (run A k s)) (m : List Bool) :
    run (A ++ B ++ D) m s = run (A ++ B' ++ D) m s := by
  rw [run_append (A ++ B), run_append (A ++ B'), run_append A B, run_append A B']
  simp only [measurementCount_append, hmc, h]

theorem portRun_split (X P G : Program) (st u : State) (hX : ∀ n, run X n st = u) (k : List Bool) :
    ∃ k1 k2, run (X ++ P ++ G) k st = run G k1 (run P k2 u) := by
  rw [run_append (X ++ P), run_append X P, hX]
  exact ⟨_, _, rfl⟩

def portFinite (rows : Nat → Fin 32768) : WCode 32768 :=
  WEXUnlookup.fusedPrefixCode streamLayout rows ++ wGeneric streamLayout rows ++ portSuffixCode rows

def portRowCode (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ portFinite rows ++ wLiteral ([.X 838])

theorem wFinite23_split (rows : Nat → Fin 32768) :
    wFinite23 streamLayout rows = WEXUnlookup.fusedPrefixCode streamLayout rows ++ wGeneric streamLayout rows ++
      WEXUnlookup.suffixCode streamLayout rows := by
  simp only [WEXUnlookup.fusedPrefixCode, WEXUnlookup.suffixCode, wFinite23, List.append_assoc]

attribute [local irreducible] streamLayout ECDSAAdd.regValue ECDSAAdd.run in
theorem portRow_run_eq (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s)) (m : List Bool) :
    run ((specialize (portRowCode rows) address).instantiate read) m ⟨false,s⟩ =
      run ((specialize (rowAddCode rows) address).instantiate read) m ⟨false,s⟩ := by
  classical
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hop := WEXUnlookup.row_opposite read rows address hc hr h₁
  have hpe := WEXUnlookup.prefixCode_equiv read streamLayout hw hn rows address hop
  have hpi := WEXUnlookup.referencePrefix_inst read streamLayout hw rows address hc hr h₁ h₂ hD hDo
  have hG : (specialize (wGeneric streamLayout rows) address).instantiate read = Arith.genericS streamLayout cx cy := by
    rw [specialize_generic]
    exact Arith.genericT_inst streamLayout hc hr
  let P0 := (specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read
  let G0 := (specialize (wGeneric streamLayout rows) address).instantiate read
  let B := (specialize (portSuffixCode rows) address).instantiate read
  let B' := (specialize (WEXUnlookup.suffixCode streamLayout rows) address).instantiate read
  have e1 : (specialize (portRowCode rows) address).instantiate read = (([.X 838] : Program) ++ P0 ++ G0) ++ B ++ ([.X 838] : Program) := by
    simp only [portRowCode, portFinite, specialize_append, specialize_literal, Tmpl.instantiate_append, Tmpl.instantiate_lit,
      WEXUnlookup.specialize_fusedPrefix, P0, G0, B, List.append_assoc]
  have e2 : (specialize (rowAddCode rows) address).instantiate read = (([.X 838] : Program) ++ P0 ++ G0) ++ B' ++ ([.X 838] : Program) := by
    simp only [rowAddCode, wFinite23_split, specialize_append, specialize_literal, Tmpl.instantiate_append, Tmpl.instantiate_lit,
      WEXUnlookup.specialize_fusedPrefix, P0, G0, B', List.append_assoc]
  rw [e1, e2]
  apply portSuffix_middle _ _ _ _ (portSuffix_records read rows address _ hr)
  intro k n
  apply portSuffix_run read rows address _ hr hop
  intro n' w hw'
  let C : Point := .some hc
  let O := dialogInfinity true R
  let D := dialogDouble true R C
  let I := dialogInversePoint true R C
  let H := dialogException true R C
  let Gf := dialogOrdinary true R C
  let E := true && decide (dialogExceptionEnabled C)
  let K := true && decide (cy≠-cy)
  have reads := dialogFlagState_read streamLayout hn O D I Gf E H K
  have h7 := Arith.boundary_genericS streamLayout hw hn R true (dialogFlagState streamLayout O D I Gf E H K) hc
    (fun hg => ((dialogOrdinary_true true R C (WeierstrassCurve.Affine.Point.some_ne_zero hc)).mp (reads.2.2.2.1.symm.trans hg)).2)
  rw [reads.2.2.2.1] at h7
  have h8 := secondCorners_boundary streamLayout hw hn R C (WeierstrassCurve.Affine.Point.some_ne_zero hc) true
    (dialogFlagState streamLayout O D I Gf E H K) reads.1 reads.2.1 reads.2.2.1 reads.2.2.2.2.2.1
  have h9 := dialogFlag_generic streamLayout hw hn (if true then R+C else R) true O D I Gf E H K
  have hP (k' : List Bool) : PointDialogBoundary streamLayout R true (dialogFlagState streamLayout O D I Gf E H K)
      (run P0 k' ⟨false, flipInfinity s⟩).basis := by
    have hb := (WEXUnlookup.prefixS_checked streamLayout hw hn R hc true ⟨false, flipInfinity s⟩ k' hs).2
    have he := hpe.2 k' ⟨false, flipInfinity s⟩
    rw [hpi] at he
    change PointDialogBoundary streamLayout R true (dialogFlagState streamLayout O D I Gf E H K)
      (run ((specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read) k' ⟨false, flipInfinity s⟩).basis
    rw [← he]
    exact hb
  have hA := portRun_split ([.X 838] : Program) P0 G0 ⟨false,s⟩ ⟨false, flipInfinity s⟩ (fun n => flip_run _ n) k
  obtain ⟨k1, k2, hA⟩ := hA
  rw [hA]
  have hG' : G0 = Arith.genericS streamLayout cx cy := hG
  have hu := (h7 (run P0 k2 ⟨false, flipInfinity s⟩) k1 (hP _)).2
  rw [← hG'] at hu
  have hv := ((h8.seq h9) _ n' hu).2
  exact (regValue_zero _ _).mp hv.clean w (scrWires_pool w hw')

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem portRow_shape (rows : Nat → Fin 32768) :
    let F : WCode 32768 := wLiteral (ECDSAAdd.Arithmetic.pointDialogGenericFlag streamLayout)
    let Z : WCode 32768 := wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
      wLiteral (Arith.padding (streamLayout.core.poolWire 0) 49864)
    let X : WCode 32768 := wLiteral ([.X 838])
    let H : WCode 32768 := WEXUnlookup.fusedPrefixCode streamLayout rows ++ wGeneric streamLayout rows
    portFinite rows = H ++ scrCorners rows ++ F ++ scrOutCompare rows ++ Z ∧
    wFinite23 streamLayout rows = H ++ wCornersOne streamLayout rows ++ F ++ scrOldCompare rows ++ Z ∧
    portRowCode rows = X ++ portFinite rows ++ X ∧
    rowAddCode rows = X ++ wFinite23 streamLayout rows ++ X := by
  dsimp only
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [portFinite, portSuffixCode, List.append_assoc]
  · rw [wFinite23_split]
    simp only [WEXUnlookup.suffixCode, scrOldCompare, List.append_assoc]

theorem port_member_shape {n : Nat} (X H c c' F o o' Z : WCode n) (i : WInstr n) (E : Prop)
    (hc : i ∈ c → E ∨ i ∈ c') (ho : i ∈ o → E ∨ i ∈ o')
    (hi : i ∈ X ++ (H ++ c ++ F ++ o ++ Z) ++ X) : E ∨ i ∈ X ++ (H ++ c' ++ F ++ o' ++ Z) ++ X := by
  simp only [List.mem_append] at hi ⊢
  tauto

theorem portRow_member (rows : Nat → Fin 32768) (i : WInstr 32768) (hi : i ∈ portRowCode rows) :
    i = WInstr.literal (cxList scrPairWires scrPairTargets) ∨
    i = WInstr.literal (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ∨
    i = WInstr.literal (cxList scrShortWires scrShortTargets) ∨
    i = WInstr.literal ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ∨
    i = WInstr.lookup none (scrPorts rows) ∨ i ∈ rowAddCode rows := by
  have hcmp : i ∈ scrOutCompare rows → i = WInstr.literal (cxList scrPairWires scrPairTargets) ∨
      i = WInstr.literal (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ∨
      i = WInstr.literal (cxList scrShortWires scrShortTargets) ∨
      i = WInstr.lookup none (scrPorts rows) ∨ i ∈ scrOldCompare rows := by
    intro h
    cases i with
    | literal p =>
      rcases scrCompare_literal_cases rows p h with rfl | rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    | lookup c ports =>
      rcases scrCompare_lookup_cases rows c ports h with ⟨rfl, rfl⟩ | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hs := portRow_shape rows
  dsimp only at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [h3, h1] at hi
  rw [h4, h2]
  have hc' : i ∈ scrCorners rows → (i = WInstr.literal (cxList scrPairWires scrPairTargets) ∨
      i = WInstr.literal (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ∨
      i = WInstr.literal (cxList scrShortWires scrShortTargets) ∨
      i = WInstr.literal ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ∨
      i = WInstr.lookup none (scrPorts rows)) ∨ i ∈ wCornersOne streamLayout rows := by
    intro h
    rcases scrCorners_cases rows i h with he | h
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl he))))
    · exact Or.inr h
  have ho' : i ∈ scrOutCompare rows → (i = WInstr.literal (cxList scrPairWires scrPairTargets) ∨
      i = WInstr.literal (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ∨
      i = WInstr.literal (cxList scrShortWires scrShortTargets) ∨
      i = WInstr.literal ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ∨
      i = WInstr.lookup none (scrPorts rows)) ∨ i ∈ scrOldCompare rows := by
    intro h
    rcases hcmp h with he | he | he | he | h
    · exact Or.inl (Or.inl he)
    · exact Or.inl (Or.inr (Or.inl he))
    · exact Or.inl (Or.inr (Or.inr (Or.inl he)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr he))))
    · exact Or.inr h
  rcases port_member_shape _ _ _ _ _ _ _ _ i _ hc' ho' hi with (h | h | h | h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem portCheck_facts :
    (∀ p, (p = cxList scrPairWires scrPairTargets ∨ p = cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)] ∨
        p = cxList scrShortWires scrShortTargets ∨ p = [.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) →
      ECDSAAdd.wires p ⊆ streamLayout.dialogUsedWires.toFinset ∧ GatePhysical p ∧
      ECDSAAdd.wires p ⊆ sourceSupport.toFinset) := by
  have hP := scrCx_facts scrPairWires scrPairTargets scrCheck_pair
    (fun a ha => scrWires_pair_targets a (List.mem_append_left _ ha))
  have hS := scrCx_facts scrShortWires scrShortTargets scrCheck_short
    (fun a ha => scrWires_short_targets a (List.mem_append_right _ ha))
  have hF := scrFlagSwap_facts
  have hY := scrY_facts
  intro p hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hP
  · refine ⟨?_, ?_, ?_⟩
    · rw [ECDSAAdd.wires_append]
      exact Finset.union_subset hP.1 hY.1
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hP.2.1 i hi
      · exact hY.2.1 i hi
    · rw [ECDSAAdd.wires_append]
      exact Finset.union_subset hP.2.2 hY.2.2
  · exact hS
  · exact hF

theorem portRow_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ portRowCode rows, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  have hlit (p : ECDSAAdd.Program) (h : ECDSAAdd.wires p ⊆ streamLayout.dialogUsedWires.toFinset) :
      PlacedPair windowBits windowPaths windowRoot (WInstr.literal (n := 32768) p) := by
    intro w hw hq
    exact window_reserved_outside_used w hw (List.mem_toFinset.mp (h hq))
  rcases portRow_member rows i hi with rfl | rfl | rfl | rfl | rfl | h
  · exact hlit _ (portCheck_facts _ (Or.inl rfl)).1
  · exact hlit _ (portCheck_facts _ (Or.inr (Or.inl rfl))).1
  · exact hlit _ (portCheck_facts _ (Or.inr (Or.inr (Or.inl rfl)))).1
  · exact hlit _ (portCheck_facts _ (Or.inr (Or.inr (Or.inr rfl)))).1
  · exact placed_implies_pair _ _ _ _ ((lookupPlacedOK_iff _ _ _ _).mp (scrPorts_geometry rows))
  · exact rowAddCode_placed rows i h

theorem portRow_physical (rows : Nat → Fin 32768) :
    ∀ p, WInstr.literal p ∈ portRowCode rows → GatePhysical p := by
  intro p hp
  rcases portRow_member rows _ hp with he | he | he | he | he | h
  · cases he; exact (portCheck_facts _ (Or.inl rfl)).2.1
  · cases he; exact (portCheck_facts _ (Or.inr (Or.inl rfl))).2.1
  · cases he; exact (portCheck_facts _ (Or.inr (Or.inr (Or.inl rfl)))).2.1
  · cases he; exact (portCheck_facts _ (Or.inr (Or.inr (Or.inr rfl)))).2.1
  · cases he
  · exact rowAddCode_physical rows p h

theorem portRow_literal_source (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ portRowCode probeRows) :
    ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  rcases portRow_member probeRows _ hp with he | he | he | he | he | hi
  · cases he; exact (portCheck_facts _ (Or.inl rfl)).2.2
  · cases he; exact (portCheck_facts _ (Or.inr (Or.inl rfl))).2.2
  · cases he; exact (portCheck_facts _ (Or.inr (Or.inr (Or.inl rfl)))).2.2
  · cases he; exact (portCheck_facts _ (Or.inr (Or.inr (Or.inr rfl)))).2.2
  · cases he
  · simp only [rowAddCode,List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hi
      subst p
      intro w hw
      have he : w = 838 := by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw
      subst w
      exact List.mem_toFinset.mpr ((sourceSupport_mem 838).mpr (Or.inl (by decide +kernel)))
    · exact finiteOne_literal_source probeRows p (tight_finite_literal_subset streamLayout probeRows p (finite23_literal_subset streamLayout probeRows p hi))
    · simp only [wLiteral,List.mem_singleton,WInstr.literal.injEq] at hi
      subst p
      intro w hw
      have he : w = 838 := by simpa [ECDSAAdd.wires,ECDSAAdd.Instr.wires] using hw
      subst w
      exact List.mem_toFinset.mpr ((sourceSupport_mem 838).mpr (Or.inl (by decide +kernel)))

theorem port_measures_shape {n : Nat} (X H c c' F o o' Z : WCode n)
    (c1 : literalToffolis c = literalToffolis c') (c2 : literalRecords c = literalRecords c')
    (c3 : traversals c + 1 = traversals c') (c4 : literalSlotSum c = literalSlotSum c' + 2)
    (c5 : portTotal c ≤ portTotal c')
    (d1 : literalToffolis o = literalToffolis o') (d2 : literalRecords o = literalRecords o')
    (d3 : traversals o + 2 = traversals o') (d4 : literalSlotSum o = literalSlotSum o' + 1033)
    (d5 : portTotal o = portTotal o') :
    literalToffolis (X ++ (H ++ c ++ F ++ o ++ Z) ++ X) = literalToffolis (X ++ (H ++ c' ++ F ++ o' ++ Z) ++ X) ∧
    literalRecords (X ++ (H ++ c ++ F ++ o ++ Z) ++ X) = literalRecords (X ++ (H ++ c' ++ F ++ o' ++ Z) ++ X) ∧
    literalRecords (H ++ c ++ F ++ o ++ Z) = literalRecords (H ++ c' ++ F ++ o' ++ Z) ∧
    traversals (X ++ (H ++ c ++ F ++ o ++ Z) ++ X) + 3 = traversals (X ++ (H ++ c' ++ F ++ o' ++ Z) ++ X) ∧
    traversals (H ++ c ++ F ++ o ++ Z) + 3 = traversals (H ++ c' ++ F ++ o' ++ Z) ∧
    literalSlotSum (X ++ (H ++ c ++ F ++ o ++ Z) ++ X) = literalSlotSum (X ++ (H ++ c' ++ F ++ o' ++ Z) ++ X) + 1035 ∧
    portTotal (X ++ (H ++ c ++ F ++ o ++ Z) ++ X) ≤ portTotal (X ++ (H ++ c' ++ F ++ o' ++ Z) ++ X) := by
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append']
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem portRow_measures (rows : Nat → Fin 32768) :
    literalToffolis (portRowCode rows) = literalToffolis (rowAddCode rows) ∧
    literalRecords (portRowCode rows) = literalRecords (rowAddCode rows) ∧
    literalRecords (portFinite rows) = literalRecords (wFinite23 streamLayout rows) ∧
    traversals (portRowCode rows) + 3 = traversals (rowAddCode rows) ∧
    traversals (portFinite rows) + 3 = traversals (wFinite23 streamLayout rows) ∧
    literalSlotSum (portRowCode rows) = literalSlotSum (rowAddCode rows) + 1035 ∧
    portTotal (portRowCode rows) ≤ portTotal (rowAddCode rows) := by
  have hs := portRow_shape rows
  dsimp only at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have c := scrCorners_counts rows
  have d := scrCompare_counts rows
  have e := scrCompare_slots_ports rows
  rw [h3, h4, h1, h2]
  exact port_measures_shape _ _ _ _ _ _ _ _ c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 d.1 d.2.1 d.2.2 e.1 e.2

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
open ShorECDLP.Secp256k1
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem port_nat_sub3 (a b : Nat) (h : a + 3 = b) (hb : b = 21) : a = 18 := by omega
theorem port_nat_slots (a b : Nat) (h : a = b + 1035) (hb : b ≤ 50000002) : a ≤ 50001037 := by omega


theorem portRow_literalRecords (rows : Nat → Fin 32768) : literalRecords (portRowCode rows) = 1556899 := by
  have hm := (portRow_measures rows).2.1
  have counts := ((finite23_literal_counts streamLayout rows).2.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup rows).2)
  rw [hm]
  simp only [rowAddCode,literalRecords_append,wLiteral,literalRecords,ECDSAAdd.measurementCount,
    Nat.zero_add,Nat.add_zero,counts]

theorem portRow_traversals' (rows : Nat → Fin 32768) : traversals (portRowCode rows) = 18 := by
  have hm := (portRow_measures rows).2.2.2.1
  have h : traversals (rowAddCode rows) = 21 := by
    simp only [rowAddCode,traversals_append,wLiteral,traversals_finite23,traversals]
  exact port_nat_sub3 _ _ hm h




theorem portRow_sourceLookupOK : (normalizeW (portRowCode probeRows)).all sourceLookupOK = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  cases i with
  | literal p => rfl
  | lookup c ports =>
    rcases portRow_member probeRows _ hi with he | he | he | he | he | h
    · cases he
    · cases he
    · cases he
    · cases he
    · cases he
      exact scrPorts_sourceOK probeRows
    · exact List.all_eq_true.mp row_sourceLookupOK _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem portRow_literal_slots_bound : literalSlotSum (portRowCode probeRows) ≤ 50001037 := by
  exact port_nat_slots _ _ (portRow_measures probeRows).2.2.2.2.2.1 rowAdd_literal_slots_bound

theorem portRow_portTotal : portTotal (portRowCode probeRows) ≤ 20000 :=
  (portRow_measures probeRows).2.2.2.2.2.2.trans rowAdd_portTotal


end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
open ShorECDLP.Secp256k1
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem portLit_append {n : Nat} (a b : WCode n) :
    literalToffolis (normalizeW (a ++ b)) = literalToffolis (normalizeW a) + literalToffolis (normalizeW b) := by
  simp only [normalizeW, List.map_append, literalToffolis_append]

theorem portLit_lookup {n : Nat} (c : Option Wire) (p : List (LookupPort n)) :
    literalToffolis (normalizeW ([.lookup c p] : WCode n)) = 0 := rfl

theorem portLit_free {n : Nat} (p : ECDSAAdd.Program) (h : ECDSAAdd.toffoliCount p = 0) :
    literalToffolis (normalizeW (wLiteral p : WCode n)) = 0 := by
  have h0 := literalToffolis_normalize (wLiteral (n := n) p)
  have h1 : literalToffolis (wLiteral (n := n) p) = 0 := by simp [wLiteral, literalToffolis, h]
  omega

theorem portLit_corner_shape {n : Nat} (neg sw s1 s2 : ECDSAAdd.Program) (ca cb cc cd : Option Wire)
    (pa pb pc pd : List (LookupPort n)) (ht : ECDSAAdd.toffoliCount sw = 0) :
    let new : WCode n := wLiteral neg ++ wLiteral sw ++ [.lookup ca pa] ++ wLiteral sw ++ wLiteral s1 ++
      [.lookup cb pb] ++ wLiteral s1 ++ wLiteral s2 ++ [.lookup cc pc] ++ wLiteral s2
    let old : WCode n := wLiteral neg ++ [.lookup ca pa] ++ wLiteral s1 ++ [.lookup cb pb] ++ wLiteral s1 ++
      [.lookup cd pd] ++ wLiteral s2 ++ [.lookup cc pc] ++ wLiteral s2
    literalToffolis (normalizeW new) ≤ literalToffolis (normalizeW old) := by
  dsimp only
  simp only [portLit_append, portLit_lookup, portLit_free sw ht]
  omega

theorem portLit_corners (rows : Nat → Fin 32768) :
    literalToffolis (normalizeW (scrCorners rows)) ≤ literalToffolis (normalizeW (wCornersOne streamLayout rows)) :=
  portLit_corner_shape _ ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY] : ECDSAAdd.Program)
    ([.CX streamLayout.infinitySelect streamLayout.doubleSelect] : ECDSAAdd.Program)
    ([.CX streamLayout.genericSelect streamLayout.core.equalNegY] : ECDSAAdd.Program) _ _ _ _ _ _ _ _ rfl

theorem portLit_compare_shape {n : Nat} (l1 l2 l3 l4 l5 : List (LookupPort n)) (cx cx' s : ECDSAAdd.Program)
    (y : ECDSAAdd.Program) (hcx : ECDSAAdd.toffoliCount cx = 0) (hcx' : ECDSAAdd.toffoliCount cx' = 0)
    (hy : ECDSAAdd.toffoliCount y = 0) (chain : WCode n) :
    literalToffolis (normalizeW (([.lookup none l1] : WCode n) ++ wLiteral cx ++ chain ++ wLiteral (cx ++ y) ++
        wLiteral cx' ++ wLiteral s ++ wLiteral cx' ++ [.lookup none l1])) ≤
      literalToffolis (normalizeW (([.lookup none l2] : WCode n) ++ chain ++ [.lookup none l3] ++
        ([.lookup none l4] ++ wLiteral s ++ [.lookup none l5]))) := by
  have hc : ECDSAAdd.toffoliCount (cx ++ y) = 0 := by
    rw [ECDSAAdd.toffoliCount_append, hcx, hy]
  simp only [portLit_append, portLit_lookup, portLit_free cx hcx, portLit_free cx' hcx', portLit_free _ hc]
  omega

theorem portLit_compare (rows : Nat → Fin 32768) :
    literalToffolis (normalizeW (scrOutCompare rows)) ≤ literalToffolis (normalizeW (scrOldCompare rows)) :=
  portLit_compare_shape _ _ _ _ _ (cxList scrPairWires scrPairTargets) (cxList scrShortWires scrShortTargets) scrP2
    ([.X (yLow streamLayout)] : ECDSAAdd.Program) (cxList_toffoli _ _) (cxList_toffoli _ _) rfl _

theorem portLit_row_shape {n : Nat} (X H c c' F o o' Z : WCode n)
    (hc : literalToffolis (normalizeW c) ≤ literalToffolis (normalizeW c'))
    (ho : literalToffolis (normalizeW o) ≤ literalToffolis (normalizeW o')) :
    literalToffolis (normalizeW (X ++ (H ++ c ++ F ++ o ++ Z) ++ X)) ≤
      literalToffolis (normalizeW (X ++ (H ++ c' ++ F ++ o' ++ Z) ++ X)) := by
  simp only [portLit_append]
  omega

theorem portLit_row (rows : Nat → Fin 32768) :
    literalToffolis (normalizeW (portRowCode rows)) ≤ literalToffolis (normalizeW (rowAddCode rows)) := by
  have hs := portRow_shape rows
  dsimp only at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [h3, h4, h1, h2]
  exact portLit_row_shape _ _ _ _ _ _ _ _ (portLit_corners rows) (portLit_compare rows)

theorem port_nat_count (a b b' t : Nat) (h : a + b + 21 * t ≤ 2163901 + 21 * t) (hb : b' ≤ b) :
    a + b' + 18 * t ≤ 2163901 + 18 * t := by omega

theorem portRow_count_upper (k : Nat) :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (portRowCode probeRows)) + 18 * (2^k-1) ≤
      2163901 + 18 * (2^k-1) :=
  port_nat_count _ _ _ _ (generic_count_upper k) (portLit_row probeRows)

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
open ShorECDLP.Secp256k1
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
open ShorECDLP.Secp256k1
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


end
end ShorECDLP.Entrant.WEX


/-! ### Scratch-hosted entry comparisons

The entry (prefix) exception tests load the paired parity word and the negated short word of the
doubled point into the same clean scratch words used by the output tests, copy them onto the
point by Clifford CNOTs, and clear the scratch with one more traversal.  This replaces the three
in-place traversals of `wPairShortFused` by two traversals. -/
namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.ShorPort
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def scrInShortBits (rows : Nat → Fin 32768) : List (LookupPort 32768) := shortNegPorts streamLayout rows

def scrInPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  retarget (scrPairBits rows (wBit rows .y)) scrPairWires ++ retarget (scrInShortBits rows) scrShortWires

def scrInP1 : Program :=
  zeroWith (fun w => [.CCX w (yLow streamLayout) streamLayout.doubleSelect, .X (yLow streamLayout),
    .CCX w (yLow streamLayout) streamLayout.genericSelect]) streamLayout.control (pairPorts streamLayout)

def scrInP2 : Program :=
  zeroControlled streamLayout.core.equalX streamLayout.core.equalNegY
    (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258))

/-- One load, Clifford copies for both entry comparisons, one clear. -/
def scrInCompare (rows : Nat → Fin 32768) : WCode 32768 :=
  [.lookup none (scrInPorts rows)] ++
  wLiteral (cxList scrPairWires scrPairTargets) ++
  wZeroWith (wPairTailBare (yLow streamLayout) streamLayout.doubleSelect streamLayout.genericSelect)
    streamLayout.control (pairPorts streamLayout) ++
  wLiteral (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
  wLiteral (cxList scrShortWires scrShortTargets) ++
  wLiteral scrInP2 ++
  wLiteral (cxList scrShortWires scrShortTargets) ++
  [.lookup none (scrInPorts rows)]

def scrInOld (rows : Nat → Fin 32768) : WCode 32768 :=
  wPairEqualTight streamLayout streamLayout.doubleSelect streamLayout.genericSelect
    (wBit rows .infinity) (wFields rows .x) (wBit rows .y) (wBit rows .negY) ++
  wShortNegEqual streamLayout streamLayout.core.equalX streamLayout.core.equalNegY rows

theorem genericSelect_not_pool : streamLayout.genericSelect ∉ streamLayout.dialogPool := by decide +kernel
theorem equalX_not_pool : streamLayout.core.equalX ∉ streamLayout.dialogPool := by decide +kernel

/-- Derived from the output-comparison facts; avoids re-evaluating the scratch word in the kernel. -/
theorem scrWires_inP1 : ∀ a ∈ scrWires, a ∉ (streamLayout.control :: [yLow streamLayout,
    streamLayout.doubleSelect, streamLayout.genericSelect] ++ (pairPorts streamLayout).flatMap ZeroBit.wires) := by
  intro a ha hm
  rcases List.mem_cons.mp hm with h | hm
  · exact scrWires_p1 a ha (h ▸ List.mem_cons_self)
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_cons.mp hm with h | hm
    · exact scrWires_p1 a ha (h ▸ List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
    rcases List.mem_cons.mp hm with h | hm
    · exact scrWires_p2 a ha (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    rcases List.mem_cons.mp hm with h | hm
    · exact genericSelect_not_pool (h ▸ scrWires_pool a ha)
    · exact absurd hm List.not_mem_nil
  · exact scrWires_p1 a ha (List.mem_cons_of_mem _ (List.mem_append_right _ hm))

theorem scrWires_inP2 : ∀ a ∈ scrWires, a ∉ (streamLayout.core.equalX :: streamLayout.core.equalNegY ::
    (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).flatMap ZeroBit.wires) := by
  intro a ha hm
  rcases List.mem_cons.mp hm with h | hm
  · exact equalX_not_pool (h ▸ scrWires_pool a ha)
  rcases List.mem_cons.mp hm with h | hm
  · exact scrWires_p1 a ha (h ▸ List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  · exact scrWires_p2 a ha (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))

attribute [local irreducible] streamLayout

theorem scrInP1_wires (a : Wire) (ha : a ∈ scrWires) : a ∉ ECDSAAdd.wires scrInP1 := by
  have htail (c : Wire) : wires
      ([.CCX c (yLow streamLayout) streamLayout.doubleSelect, .X (yLow streamLayout),
        .CCX c (yLow streamLayout) streamLayout.genericSelect] : Program) ⊆
      (c :: [yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect]).toFinset := by
    intro q hq
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq ⊢
    tauto
  have hz := deltaZeroWith_support
    (fun c : Wire => ([.CCX c (yLow streamLayout) streamLayout.doubleSelect, .X (yLow streamLayout),
      .CCX c (yLow streamLayout) streamLayout.genericSelect] : Program))
    ([yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect] : List Wire) htail
    streamLayout.control (pairPorts streamLayout)
  intro hq
  exact scrWires_inP1 a ha (List.mem_toFinset.mp (hz hq))

theorem scrInP2_wires (a : Wire) (ha : a ∈ scrWires) : a ∉ ECDSAAdd.wires scrInP2 := by
  intro hq
  rw [scrInP2, zeroControlled_wires] at hq
  exact scrWires_inP2 a ha (List.mem_toFinset.mp hq)

theorem scrInShortBits_length (rows : Nat → Fin 32768) : (scrInShortBits rows).length = 258 := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  simp [scrInShortBits, shortNegPorts, hx, hy]

theorem scrInShortBits_targets (rows : Nat → Fin 32768) :
    portTargets (scrInShortBits rows) = scrShortTargets := by
  have h := indexedPorts_targets streamLayout.point.x (wFields rows .doubleX) true
  have h' := indexedPorts_targets (streamLayout.point.y.take 1) (fun a _ => wBit rows .doubleY 0 a) false
  simp only [portTargets] at h h'
  simp only [scrInShortBits, shortNegPorts, scrShortTargets, portTargets, List.map_append, List.map_cons, h, h',
    List.cons_append]

theorem scrInPorts_targets (rows : Nat → Fin 32768) : portTargets (scrInPorts rows) = scrWires := by
  have h1 := retarget_targets (scrPairBits rows (wBit rows .y)) scrPairWires
    ((scrPairBits_length _ _).trans scrPairWires_length.symm)
  have h2 := retarget_targets (scrInShortBits rows) scrShortWires
    ((scrInShortBits_length _).trans scrShortWires_length.symm)
  simp only [portTargets] at h1 h2
  simp only [scrInPorts, scrWires, portTargets, List.map_append, h1, h2]

theorem scrInPorts_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (scrInPorts rows) a =
      portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a := by
  have h1 := retarget_bits read (scrPairBits rows (wBit rows .y)) scrPairWires
    ((scrPairBits_length _ _).trans scrPairWires_length.symm) a
  have h2 := retarget_bits read (scrInShortBits rows) scrShortWires
    ((scrInShortBits_length _).trans scrShortWires_length.symm) a
  simp only [portBits] at h1 h2
  simp only [scrInPorts, portBits, List.map_append, h1, h2]

theorem scrIn_chain_inst (read : ConstantBit 32768 → Bool) (a : Nat) :
    (specialize (wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.doubleSelect
      streamLayout.genericSelect) streamLayout.control (pairPorts streamLayout)) a).instantiate read = scrInP1 := by
  rw [specialize_zeroWith _ (fun w => Tmpl.lit [.CCX w (yLow streamLayout) streamLayout.doubleSelect,
    .X (yLow streamLayout), .CCX w (yLow streamLayout) streamLayout.genericSelect]) a
    (fun w => by simp [wPairTailBare])]
  apply zeroWithT_inst
  intro w
  simp

theorem scrIn_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (scrInCompare rows) a).instantiate read =
      xBits scrWires (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a) ++
      (cxList scrPairWires scrPairTargets ++ (scrInP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrInP2 ++ cxList scrShortWires scrShortTargets))))) ++
      xBits scrWires (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a) := by
  simp only [scrInCompare, specialize_append, Tmpl.instantiate_append, scr_lookup_inst, specialize_literal,
    Tmpl.instantiate_lit, scrIn_chain_inst, scrInPorts_targets, scrInPorts_bits, List.append_assoc]

theorem scrInOld_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (scrInOld rows) a).instantiate read =
      xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++
      (scrInP1 ++ (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .negY)) a) ++
      (xBits scrShortTargets (portBits read (scrInShortBits rows) a) ++
      (scrInP2 ++ xBits scrShortTargets (portBits read (scrInShortBits rows) a))))) := by
  have h1 (r : Nat → ConstantBit 32768) : wPairXorParity streamLayout (wBit rows .infinity) (wFields rows .x) r =
      [.lookup none (scrPairBits rows r)] := rfl
  have h2 : wShortNegXor streamLayout rows = [.lookup none (scrInShortBits rows)] := rfl
  have h3 : ∀ a, specialize (wLiteral (n := 32768) scrInP2) a = Tmpl.lit scrInP2 := fun a => specialize_literal _ _
  have h4 : wLiteral (n := 32768) (zeroControlled streamLayout.core.equalX streamLayout.core.equalNegY
      (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258))) = wLiteral scrInP2 := rfl
  simp only [scrInOld, wPairEqualTight, wShortNegEqual, h1, h2, h4, specialize_append, Tmpl.instantiate_append,
    scr_lookup_inst, h3, Tmpl.instantiate_lit, scrIn_chain_inst, scrPairBits_targets, scrInShortBits_targets,
    List.append_assoc]

theorem scrInCompare_sim (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    ScrSim scrWires (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a)
      (cxList scrPairWires scrPairTargets ++ (scrInP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrInP2 ++ cxList scrShortWires scrShortTargets)))))
      (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++
        (scrInP1 ++ ((xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ [.X (yLow streamLayout)]) ++
        (xBits scrShortTargets (portBits read (scrInShortBits rows) a) ++
        (scrInP2 ++ xBits scrShortTargets (portBits read (scrInShortBits rows) a)))))) := by
  have hlA : scrPairWires.length = (portBits read (scrPairBits rows (wBit rows .y)) a).length := by
    simp [portBits, scrPairBits_length, scrPairWires_length]
  have hlB : scrShortWires.length = (portBits read (scrInShortBits rows) a).length := by
    simp [portBits, scrInShortBits_length, scrShortWires_length]
  have h1 := ScrSim.cx scrWires scrPairWires scrPairTargets
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a) _
    (xMask_map_left _ _ _ _ scrWires_nodup hlA)
    (fun w hw => List.mem_append_left _ hw) scrWires_pair_targets
  have h2 := ScrSim.cx scrWires scrShortWires scrShortTargets
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a) _
    (xMask_map_right _ _ _ _ scrWires_nodup hlA hlB)
    (fun w hw => List.mem_append_right _ hw) scrWires_short_targets
  have hp1 := ScrSim.disjoint scrWires
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a) scrInP1 scrInP1_wires
  have hp2 := ScrSim.disjoint scrWires
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a) scrInP2 scrInP2_wires
  have hx := ScrSim.disjoint scrWires
    (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrInShortBits rows) a)
    ([.X (yLow streamLayout)] : Program) (by
      intro w hw hq
      apply scrWires_y w hw
      simpa [ECDSAAdd.wires, ECDSAAdd.Instr.wires] using hq)
  exact h1.append (hp1.append ((h1.append hx).append (h2.append (hp2.append h2))))

theorem scrInCompare_records (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    measurementCount ((specialize (scrInCompare rows) a).instantiate read) =
      measurementCount ((specialize (scrInOld rows) a).instantiate read) := by
  rw [scrIn_inst, scrInOld_inst]
  simp only [measurementCount_append, xBits_records, cxList_records, measurementCount]
  omega

theorem scrInCompare_run (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat)
    (hop : read (wBit rows .negY 0 a) = !(read (wBit rows .y 0 a))) (m : List Bool) (s : State)
    (hs : ∀ w ∈ scrWires, s.basis w = false) :
    run ((specialize (scrInCompare rows) a).instantiate read) m s =
      run ((specialize (scrInOld rows) a).instantiate read) m s := by
  rw [scrIn_inst, scr_sandwich _ _ _ _ (scrInCompare_sim read rows a) m s hs, scrInOld_inst]
  have h := run_replace_inside
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ scrInP1)
    (xBits scrShortTargets (portBits read (scrInShortBits rows) a) ++
      (scrInP2 ++ xBits scrShortTargets (portBits read (scrInShortBits rows) a)))
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ [.X (yLow streamLayout)])
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .negY)) a))
    (by simp [xBits_records, measurementCount])
    (fun m st => scr_parity_fix read rows a hop m st) m s
  simpa only [List.append_assoc] using h

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The fused in-place entry comparisons of the parent row. -/
def scrInFused (rows : Nat → Fin 32768) : WCode 32768 :=
  wPairShortFused streamLayout streamLayout.doubleSelect streamLayout.genericSelect (wBit rows .infinity)
    (wFields rows .x) (wBit rows .y) (wBit rows .negY) (shortNegPorts streamLayout rows)
    (zeroControlled streamLayout.core.equalX streamLayout.core.equalNegY
      (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)))

theorem scrIn_counts (rows : Nat → Fin 32768) :
    literalToffolis (scrInCompare rows) = literalToffolis (scrInFused rows) ∧
    literalRecords (scrInCompare rows) = literalRecords (scrInFused rows) ∧
    traversals (scrInCompare rows) + 1 = traversals (scrInFused rows) := by
  have hz : traversals (wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.doubleSelect
      streamLayout.genericSelect) streamLayout.control (pairPorts streamLayout)) = 0 :=
    traversals_zeroWith _ 0 (fun _ => rfl) _ _
  refine ⟨?_, ?_, ?_⟩
  · simp [scrInCompare, scrInFused, wPairShortFused, wPairXorParity, wLiteral,
      literalToffolis_append, literalToffolis, cxList_toffoli, ECDSAAdd.toffoliCount, scrInP2]
  · simp [scrInCompare, scrInFused, wPairShortFused, wPairXorParity, wLiteral,
      literalRecords_append, literalRecords, cxList_records, ECDSAAdd.measurementCount, scrInP2]
  · simp only [scrInCompare, scrInFused, wPairShortFused, wPairXorParity, traversals_append, hz]
    rfl

theorem scrIn_slots_ports (rows : Nat → Fin 32768) :
    literalSlotSum (scrInCompare rows) = literalSlotSum (scrInFused rows) + 1033 ∧
    portTotal (scrInCompare rows) = portTotal (scrInFused rows) := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  have hpt : scrPairTargets.length = 258 := by simp [scrPairTargets, hx]
  have hst : scrShortTargets.length = 258 := by simp [scrShortTargets, hx, hy]
  have hzp : portTotal (wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.doubleSelect
      streamLayout.genericSelect) streamLayout.control (pairPorts streamLayout)) = 0 :=
    portTotal_zeroWith _ 0 (fun _ => rfl) _ _
  have hpl : (scrInPorts rows).length = 516 := by
    simp only [scrInPorts, List.length_append, retarget_length _ _ ((scrPairBits_length _ _).trans scrPairWires_length.symm),
      retarget_length _ _ ((scrInShortBits_length _).trans scrShortWires_length.symm), scrPairWires_length, scrShortWires_length]
  have hsl : (shortNegPorts streamLayout rows).length = 258 := scrInShortBits_length rows
  have hpp : (pairParityPorts streamLayout (wBit rows .infinity) (wFields rows .x) (wBit rows .negY)).length = 258 :=
    scrPairBits_length rows _
  have hpp' : (pairParityPorts streamLayout (wBit rows .infinity) (wFields rows .x) (wBit rows .y)).length = 258 :=
    scrPairBits_length rows _
  constructor
  · simp [scrInCompare, scrInFused, wPairShortFused, wPairXorParity, wLiteral,
      literalSlotSum_append', literalSlotSum, ECDSAAdd.Challenge.gateSlots_append, cxList_slots, scrPairWires_length,
      scrShortWires_length, hpt, hst, scrInP2]
    simp [ECDSAAdd.Challenge.gateSlots, ECDSAAdd.Challenge.instructionSlots]
    omega
  · have e1 : wPairXorParity streamLayout (wBit rows .infinity) (wFields rows .x) (wBit rows .y) =
        [.lookup none (pairParityPorts streamLayout (wBit rows .infinity) (wFields rows .x) (wBit rows .y))] := rfl
    simp only [scrInCompare, scrInFused, wPairShortFused, e1, portTotal_append', hzp]
    simp [wLiteral, portTotal_append', portTotal, hpl, hsl, hpp, hpp']

theorem scrIn_member (rows : Nat → Fin 32768) (i : WInstr 32768) (h : i ∈ scrInCompare rows) :
    i = WInstr.lookup none (scrInPorts rows) ∨ i ∈ scrInFused rows ∨ i ∈ scrOutCompare rows := by
  simp only [scrInCompare, List.mem_append] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact Or.inl (List.mem_singleton.mp h)
  · exact Or.inr (Or.inr (by simp only [scrOutCompare, List.mem_append]; tauto))
  · exact Or.inr (Or.inl (by simp only [scrInFused, wPairShortFused, List.mem_append]; tauto))
  · exact Or.inr (Or.inr (by simp only [scrOutCompare, List.mem_append]; tauto))
  · exact Or.inr (Or.inr (by simp only [scrOutCompare, List.mem_append]; tauto))
  · refine Or.inr (Or.inl ?_)
    simp only [scrInP2] at h
    simp only [scrInFused, wPairShortFused, List.mem_append]
    tauto
  · exact Or.inr (Or.inr (by simp only [scrOutCompare, List.mem_append]; tauto))
  · exact Or.inl (List.mem_singleton.mp h)

theorem scrIn_lit (rows : Nat → Fin 32768) :
    literalToffolis (normalizeW (scrInCompare rows)) = literalToffolis (normalizeW (scrInFused rows)) := by
  have hc : ECDSAAdd.toffoliCount (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) = 0 := by
    rw [ECDSAAdd.toffoliCount_append, cxList_toffoli]
    rfl
  have e1 : wPairXorParity streamLayout (wBit rows .infinity) (wFields rows .x) (wBit rows .y) =
      [.lookup none (pairParityPorts streamLayout (wBit rows .infinity) (wFields rows .x) (wBit rows .y))] := rfl
  simp only [scrInCompare, scrInFused, wPairShortFused, e1, scrInP2, portLit_append, portLit_lookup,
    portLit_free _ (cxList_toffoli scrPairWires scrPairTargets), portLit_free _ (cxList_toffoli scrShortWires scrShortTargets),
    portLit_free _ hc]

theorem scrInPorts_geometry (rows : Nat → Fin 32768) :
    lookupPlacedOK windowBits windowPaths windowRoot (.lookup none (scrInPorts rows)) = true := by
  have h := scrPorts_geometry rows
  change geometryOK windowBits windowPaths windowRoot none (portTargets (scrPorts rows)) = true at h
  change geometryOK windowBits windowPaths windowRoot none (portTargets (scrInPorts rows)) = true
  rw [scrInPorts_targets]
  rwa [scrPorts_targets] at h

theorem scrInPorts_sourceOK (rows : Nat → Fin 32768) :
    sourceLookupOK (.lookup none (scrInPorts rows)) = true := by
  have h := scrPorts_sourceOK rows
  simp only [sourceLookupOK, Option.toList_none, List.all_nil, Bool.true_and, scrPorts_targets] at h
  simp only [sourceLookupOK, Option.toList_none, List.all_nil, Bool.true_and, scrInPorts_targets]
  exact h

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The entry half of the addition body with scratch-hosted comparisons. -/
def portPrefixCode (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
  wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect) ++
  scrInCompare rows ++ wLiteral (pointDialogGenericFlag streamLayout)

def scrInHead : Program :=
  [.CX streamLayout.control streamLayout.core.double] ++ [.CX streamLayout.control streamLayout.core.equalX] ++
  zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect

theorem portPrefix_shape (rows : Nat → Fin 32768) :
    WEXUnlookup.prefixCode streamLayout rows =
      wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
      wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect) ++
      scrInOld rows ++ wLiteral (pointDialogGenericFlag streamLayout) := by
  simp only [WEXUnlookup.prefixCode, scrInOld, List.append_assoc]

theorem scrInHead_avoid (a : Wire) (ha : a ∈ scrWires) : a ∉ ECDSAAdd.wires scrInHead := by
  have h := scr_all_not scrWires ([streamLayout.control, streamLayout.core.double, streamLayout.core.equalX,
    streamLayout.point.finite, streamLayout.infinitySelect] : List Wire) (by decide +kernel) a ha
  intro hq
  apply h
  simp [scrInHead, zeroFlag, ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq ⊢
  tauto

theorem portPrefix_head (read : ConstantBit 32768 → Bool) (address : Nat) :
    (specialize (wLiteral (n := 32768) ([.CX streamLayout.control streamLayout.core.double]) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
      wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect)) address).instantiate read =
      scrInHead := by
  simp only [specialize_append, specialize_literal, Tmpl.instantiate_append, Tmpl.instantiate_lit, scrInHead]

theorem portPrefix_split (read : ConstantBit 32768 → Bool) (address : Nat) (A B D : WCode 32768) :
    (specialize (A ++ B ++ D) address).instantiate read =
      (specialize A address).instantiate read ++ (specialize B address).instantiate read ++
        (specialize D address).instantiate read := by
  simp only [specialize_append, Tmpl.instantiate_append]

theorem portPrefix_records (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) :
    measurementCount ((specialize (portPrefixCode rows) address).instantiate read) =
      measurementCount ((specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read) := by
  rw [portPrefix_shape]
  unfold portPrefixCode
  rw [portPrefix_split read address _ (scrInCompare rows), portPrefix_split read address _ (scrInOld rows)]
  simp only [measurementCount_append, scrInCompare_records read rows address]

theorem portPrefix_run (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (hop : read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address))) (m : List Bool) (s : State)
    (hs : ∀ w ∈ scrWires, s.basis w = false) :
    run ((specialize (portPrefixCode rows) address).instantiate read) m s =
      run ((specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read) m s := by
  rw [portPrefix_shape]
  unfold portPrefixCode
  rw [portPrefix_split read address _ (scrInCompare rows), portPrefix_split read address _ (scrInOld rows),
    portPrefix_head]
  apply portSuffix_middle _ _ _ _ (scrInCompare_records read rows address) s
  intro k n
  apply scrInCompare_run read rows address hop n
  intro w hw
  rw [run_preserves_outside _ _ _ _ (scrInHead_avoid w hw)]
  exact hs w hw

def portFinite2 (rows : Nat → Fin 32768) : WCode 32768 :=
  portPrefixCode rows ++ wGeneric streamLayout rows ++ portSuffixCode rows

def portRowCode2 (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ portFinite2 rows ++ wLiteral ([.X 838])

theorem portRow2_run_eq (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (hop : read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address)))
    (s : BasisState) (hclean : ∀ w ∈ scrWires, flipInfinity s w = false) (m : List Bool) :
    run ((specialize (portRowCode2 rows) address).instantiate read) m ⟨false,s⟩ =
      run ((specialize (portRowCode rows) address).instantiate read) m ⟨false,s⟩ := by
  let P' := (specialize (portPrefixCode rows) address).instantiate read
  let P := (specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read
  let R := (specialize (wGeneric streamLayout rows) address).instantiate read ++
    (specialize (portSuffixCode rows) address).instantiate read ++ ([.X 838] : Program)
  have e1 : (specialize (portRowCode2 rows) address).instantiate read = ([.X 838] : Program) ++ P' ++ R := by
    simp only [portRowCode2, portFinite2, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, P', R, List.append_assoc]
  have e2 : (specialize (portRowCode rows) address).instantiate read = ([.X 838] : Program) ++ P ++ R := by
    simp only [portRowCode, portFinite, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, WEXUnlookup.specialize_fusedPrefix, P, R, List.append_assoc]
  rw [e1, e2]
  apply portSuffix_middle _ _ _ _ (portPrefix_records read rows address) ⟨false,s⟩
  intro k n
  rw [flip_run]
  exact portPrefix_run read rows address hop n _ hclean

theorem portRow2_shape (rows : Nat → Fin 32768) :
    let A : WCode 32768 := wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
      wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect)
    let T : WCode 32768 := wLiteral (pointDialogGenericFlag streamLayout) ++ wGeneric streamLayout rows ++
      portSuffixCode rows
    let X : WCode 32768 := wLiteral ([.X 838])
    portRowCode2 rows = X ++ (A ++ scrInCompare rows ++ T) ++ X ∧
    portRowCode rows = X ++ (A ++ scrInFused rows ++ T) ++ X := by
  dsimp only
  constructor
  · simp only [portRowCode2, portFinite2, portPrefixCode, List.append_assoc]
  · simp only [portRowCode, portFinite, WEXUnlookup.fusedPrefixCode, scrInFused, List.append_assoc]

theorem portRow2_member (rows : Nat → Fin 32768) (i : WInstr 32768) (hi : i ∈ portRowCode2 rows) :
    i = WInstr.lookup none (scrInPorts rows) ∨ i ∈ portRowCode rows := by
  have hs := portRow2_shape rows
  dsimp only at hs
  rw [hs.1] at hi
  rw [hs.2]
  have hsuf : i ∈ scrOutCompare rows → i ∈ portSuffixCode rows := by
    intro h
    simp only [portSuffixCode, List.mem_append]
    tauto
  simp only [List.mem_append] at hi ⊢
  rcases hi with (hi | ((hi | hi) | hi)) | hi
  · tauto
  · tauto
  · rcases scrIn_member rows i hi with h | h | h
    · exact Or.inl h
    · tauto
    · have := hsuf h
      tauto
  · tauto
  · tauto

theorem portRow2_measures (rows : Nat → Fin 32768) :
    literalToffolis (portRowCode2 rows) = literalToffolis (portRowCode rows) ∧
    literalRecords (portRowCode2 rows) = literalRecords (portRowCode rows) ∧
    traversals (portRowCode2 rows) + 1 = traversals (portRowCode rows) ∧
    literalSlotSum (portRowCode2 rows) = literalSlotSum (portRowCode rows) + 1033 ∧
    portTotal (portRowCode2 rows) = portTotal (portRowCode rows) ∧
    literalToffolis (normalizeW (portRowCode2 rows)) = literalToffolis (normalizeW (portRowCode rows)) := by
  have hs := portRow2_shape rows
  dsimp only at hs
  rw [hs.1, hs.2]
  have c := scrIn_counts rows
  have d := scrIn_slots_ports rows
  have e := scrIn_lit rows
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', portLit_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

theorem portRow2_run_same (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (s : BasisState) (hs : liveReady s) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (portRowCode2 probeRows)) a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ =
      ECDSAAdd.run ((specialize (normalizeW (rowAddCode probeRows)) a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ := by
  rw [specialize_normalize_run, specialize_normalize_run]
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P,hP⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P) true (fun _=>false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P) (StreamPoint.of_coordinates s P hs.1.1.1.1 hP),?_,?_,?_⟩
    · simpa [streamLayout_control,flipInfinity,ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  cases he : Bridge.toB C with
  | zero =>
    have hzero : C = 0 := congrArg ECDSAAdd.ShorPort.toA he
    exact (hC hzero).elim
  | @some cx cy hc =>
    have ce : C = toA (.some hc) := congrArg toA he
    have hr : RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
      readConstant_rowReads coeffs Q _ _ ce
    have ho : ShorECDLP.order • (.some hc : Point) = 0 := by rw [← he]; exact hord
    have hp2 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 2
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hp3 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 3
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hd : (.some hc : Point)+.some hc ≠ 0 := by simpa only [two_nsmul] using hp2
    have ht : (.some hc : Point)+.some hc+.some hc ≠ 0 := by
      simpa only [show (3 : Nat) = 2+1 from rfl,succ_nsmul,two_nsmul] using hp3
    have en := enables_true hc hd ht
    have hdo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0 := by rw [nsmul_add,ho,zero_add]
    have hop := WEXUnlookup.row_opposite (readConstant coeffs Q) probeRows a hc hr en.1
    exact (portRow2_run_eq (readConstant coeffs Q) probeRows a hop s
      (fun w hw => clean w (List.mem_append_right _ (scrWires_pool w hw))) m).trans
      (portRow_run_eq (readConstant coeffs Q) probeRows a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial m)

theorem portRow2_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ portRowCode2 rows, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  rcases portRow2_member rows i hi with rfl | h
  · exact placed_implies_pair _ _ _ _ ((lookupPlacedOK_iff _ _ _ _).mp (scrInPorts_geometry rows))
  · exact portRow_placed rows i h

theorem portRow2_physical (rows : Nat → Fin 32768) :
    ∀ p, WInstr.literal p ∈ portRowCode2 rows → GatePhysical p := by
  intro p hp
  rcases portRow2_member rows _ hp with he | h
  · cases he
  · exact portRow_physical rows p h

theorem portRow2_literal_source (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ portRowCode2 probeRows) :
    ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  rcases portRow2_member probeRows _ hp with he | h
  · cases he
  · exact portRow_literal_source p h

theorem port2_nat_sub (a b : Nat) (h : a + 1 = b) (hb : b = 18) : a = 17 := by omega

theorem portRow2_traversals' (rows : Nat → Fin 32768) : traversals (portRowCode2 rows) = 17 :=
  port2_nat_sub _ _ (portRow2_measures rows).2.2.1 (portRow_traversals' rows)

theorem portRow2_traversals : traversals (normalizeW (portRowCode2 probeRows)) = 17 := by
  rw [traversals_normalize]
  exact portRow2_traversals' probeRows

theorem portRow2_literalRecords (rows : Nat → Fin 32768) : literalRecords (portRowCode2 rows) = 1556899 :=
  (portRow2_measures rows).2.1.trans (portRow_literalRecords rows)

theorem port2_records_arith (a b k : Nat) (ha : a = 1556899) (hb : b = 17) (l : Nat) (hl : l = k) :
    a + b * (2 ^ l - 1) = 1556899 + 17 * (2 ^ k - 1) := by
  subst ha hb hl
  rfl

theorem port2_records15 (a b l : Nat) (ha : a = 1556899) (hb : b = 17) (hl : l = 15) :
    a + b * (2 ^ l - 1) = 2113938 := by
  subst ha hb hl
  rfl

theorem portRow2_records : codeRecords windowBits windowPaths windowRoot
    (normalizeW (portRowCode2 probeRows)) = 2113938 := by
  have layouts := pair_layouts_of_placed windowBits windowPaths windowRoot _
    (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ (portRow2_placed probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact port2_records15 _ _ _ (portRow2_literalRecords _) (portRow2_traversals' _) (by simp [windowBits])

theorem portRow2_sourceLookupOK : (normalizeW (portRowCode2 probeRows)).all sourceLookupOK = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  cases i with
  | literal p => rfl
  | lookup c ports =>
    rcases portRow2_member probeRows _ hi with he | h
    · cases he
      exact scrInPorts_sourceOK probeRows
    · exact List.all_eq_true.mp portRow_sourceLookupOK _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem port2_nat_slots (a b : Nat) (h : a = b + 1033) (hb : b ≤ 50001037) : a ≤ 50002070 := by omega

theorem portRow2_literal_slots_bound : literalSlotSum (portRowCode2 probeRows) ≤ 50002070 :=
  port2_nat_slots _ _ (portRow2_measures probeRows).2.2.2.1 portRow_literal_slots_bound

theorem portRow2_portTotal : portTotal (portRowCode2 probeRows) ≤ 20000 := by
  rw [(portRow2_measures probeRows).2.2.2.2.1]
  exact portRow_portTotal

theorem port2_nat_count (a b b' t : Nat) (h : a + b + 18 * t ≤ 2163901 + 18 * t) (hb : b' = b) :
    a + b' + 17 * t ≤ 2163901 + 17 * t := by omega

theorem portRow2_count_upper (k : Nat) :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (portRowCode2 probeRows)) + 17 * (2^k-1) ≤
      2163901 + 17 * (2^k-1) :=
  port2_nat_count _ _ _ _ (portRow_count_upper k) (portRow2_measures probeRows).2.2.2.2.2

theorem portRow2_width_placed (k : Nat) (hk : k ≤ 15) (rows : Nat → Fin 32768) :
    ∀ i ∈ portRowCode2 rows, PlacedPair (widthBits k) windowPaths windowRoot i := by
  intro i hi
  have hp := portRow2_placed rows i hi
  cases i with
  | literal p =>
    intro w hw
    exact hp w ((List.Sublist.cons₂ windowRoot (width_sublist k hk)).subset hw)
  | lookup c ports =>
    refine ⟨(List.Sublist.cons₂ _ (width_sublist k hk)).nodup hp.1, hp.2.1, hp.2.2.1, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw ht
    exact List.disjoint_left.mp hp.2.2.2
      ((List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (width_sublist k hk))).subset hw) ht

theorem portRow2_width_records (k : Nat) (hk : k ≤ 15) :
    codeRecords (widthBits k) windowPaths windowRoot (normalizeW (portRowCode2 probeRows)) =
      1556899 + 17 * (2 ^ k - 1) := by
  have layouts := pair_layouts_of_placed (widthBits k) windowPaths windowRoot _
    (by simpa [widthBits,windowPaths] using hk) (pair_placed_normalize _ _ _ _ (portRow2_width_placed k hk probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact port2_records_arith _ _ _ (portRow2_literalRecords _) (portRow2_traversals' _) _ (by simp [widthBits])

end
end ShorECDLP.Entrant.WEX


/-! ### Doubled-point corner from the output scratch

The output scratch load also carries the 255 high `y` bits of the doubled point.  Together with the
short-comparison word already in scratch this is the whole doubled-point encoding, so the first corner
write becomes 513 scratch-controlled Toffolis instead of a controlled table traversal. -/
namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.ShorPort
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

private theorem scr_xor_swap' (a b c : Bool) : ((a ^^ b) ^^ c) = ((a ^^ c) ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Constant bits applied under a control. -/
def cBits (c : Wire) : List Wire → List Bool → Program
  | w :: ws, b :: bs => (if b then [.CX c w] else []) ++ cBits c ws bs
  | _, _ => []

/-- Controlled copies of a loaded scratch word. -/
def ccxList (c : Wire) : List Wire → List Wire → Program
  | a :: as, t :: ts => .CCX c a t :: ccxList c as ts
  | _, _ => []

theorem cBits_records (c : Wire) (S : List Wire) (k : List Bool) : measurementCount (cBits c S k) = 0 := by
  induction S generalizing k with
  | nil => rfl
  | cons w S ih =>
    cases k with
    | nil => rfl
    | cons b k => cases b <;> simp [cBits, measurementCount, ih]

theorem ccxList_records (c : Wire) (S T : List Wire) : measurementCount (ccxList c S T) = 0 := by
  induction S generalizing T with
  | nil => rfl
  | cons a S ih => cases T <;> simp [ccxList, measurementCount, ih]

theorem ccxList_toffoli (c : Wire) (S T : List Wire) :
    ECDSAAdd.toffoliCount (ccxList c S T) = min S.length T.length := by
  induction S generalizing T with
  | nil => simp [ccxList, ECDSAAdd.toffoliCount]
  | cons a S ih =>
    cases T with
    | nil => simp [ccxList, ECDSAAdd.toffoliCount]
    | cons t T =>
      have h := ih T
      simp only [ECDSAAdd.toffoliCount] at h
      simp [ccxList, ECDSAAdd.toffoliCount, h]
      omega

theorem ccxList_slots (c : Wire) (S T : List Wire) :
    ECDSAAdd.Challenge.gateSlots (ccxList c S T) = min S.length T.length := by
  induction S generalizing T with
  | nil => simp [ccxList, ECDSAAdd.Challenge.gateSlots]
  | cons a S ih =>
    cases T with
    | nil => simp [ccxList, ECDSAAdd.Challenge.gateSlots]
    | cons t T =>
      have h := ih T
      simp only [ECDSAAdd.Challenge.gateSlots] at h
      simp [ccxList, ECDSAAdd.Challenge.gateSlots, ECDSAAdd.Challenge.instructionSlots, h]
      omega

theorem cBits_run (c : Wire) (S : List Wire) (k m : List Bool) (s : State) (hc : c ∉ S) :
    run (cBits c S k) m s = ⟨s.phase, fun q => s.basis q ^^ (s.basis c && xMask S k q)⟩ := by
  induction S generalizing k s with
  | nil => simp [cBits, xMask, run]
  | cons w S ih =>
    have hcw : c ≠ w := fun e => hc (e ▸ List.mem_cons_self)
    have hcS : c ∉ S := fun e => hc (List.mem_cons_of_mem _ e)
    cases k with
    | nil => simp [cBits, xMask, run]
    | cons b k =>
      cases b
      · simpa [cBits, xMask] using ih k s hcS
      · change run (.CX c w :: cBits c S k) m s = _
        simp only [run]
        rw [ih k _ hcS]
        apply congrArg (State.mk s.phase)
        funext q
        have hc' : writeBit s.basis w (s.basis w ^^ s.basis c) c = s.basis c := by
          simp [writeBit, Function.update_of_ne hcw]
        dsimp only
        rw [hc']
        by_cases hq : q = w
        · subst hq
          cases s.basis c <;> simp [writeBit, xMask]
        · simp [writeBit, xMask, hq, Function.update_of_ne hq]

theorem ccxList_run (c : Wire) (S T : List Wire) (m : List Bool) (u : State) (hd : ∀ a ∈ S, a ∉ T)
    (hc : c ∉ T) :
    run (ccxList c S T) m u = ⟨u.phase, fun q => u.basis q ^^ (u.basis c && xMask T (S.map u.basis) q)⟩ := by
  induction S generalizing T u with
  | nil => simp [ccxList, xMask, run]
  | cons a S ih =>
    cases T with
    | nil => simp [ccxList, xMask, run]
    | cons t T =>
      have hS : ∀ x ∈ S, x ≠ t := fun x hx e =>
        hd x (List.mem_cons_of_mem _ hx) (e ▸ List.mem_cons_self)
      have hT : ∀ x ∈ S, x ∉ T := fun x hx e =>
        hd x (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ e)
      have hct : c ≠ t := fun e => hc (e ▸ List.mem_cons_self)
      have hcT : c ∉ T := fun e => hc (List.mem_cons_of_mem _ e)
      have hat : a ≠ t := fun e => hd a List.mem_cons_self (e ▸ List.mem_cons_self)
      simp only [ccxList, run]
      rw [ih T _ hT hcT]
      have hmap : S.map (writeBit u.basis t (u.basis t ^^ (u.basis c && u.basis a))) = S.map u.basis := by
        apply List.map_congr_left
        intro x hx
        simp [writeBit, Function.update_of_ne (hS x hx)]
      have hcv : writeBit u.basis t (u.basis t ^^ (u.basis c && u.basis a)) c = u.basis c := by
        simp [writeBit, Function.update_of_ne hct]
      simp only [hmap, hcv]
      apply congrArg (State.mk u.phase)
      funext q
      by_cases hq : q = t
      · subst hq
        cases u.basis c <;> simp [writeBit, xMask]
      · simp [writeBit, xMask, hq, Function.update_of_ne hq]

theorem cBits_wires (c : Wire) (S : List Wire) (k : List Bool) (q : Wire) (h : q ∈ ECDSAAdd.wires (cBits c S k)) :
    q = c ∨ q ∈ S := by
  induction S generalizing k with
  | nil => simp [cBits, ECDSAAdd.wires] at h
  | cons w S ih =>
    cases k with
    | nil => simp [cBits, ECDSAAdd.wires] at h
    | cons b k =>
      cases b
      · rcases ih k (by simpa [cBits] using h) with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · have h' : q ∈ ECDSAAdd.wires (.CX c w :: cBits c S k) := by simpa [cBits] using h
        simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h'
        rcases h' with (rfl | rfl) | h'
        · exact Or.inl rfl
        · exact Or.inr List.mem_cons_self
        · rcases ih k h' with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem ccxList_wires (c : Wire) (S T : List Wire) (q : Wire) (h : q ∈ ECDSAAdd.wires (ccxList c S T)) :
    q = c ∨ q ∈ S ∨ q ∈ T := by
  induction S generalizing T with
  | nil => simp [ccxList, ECDSAAdd.wires] at h
  | cons a S ih =>
    cases T with
    | nil => simp [ccxList, ECDSAAdd.wires] at h
    | cons t T =>
      simp only [ccxList, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h
      rcases h with (rfl | rfl | rfl) | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl List.mem_cons_self)
      · exact Or.inr (Or.inr List.mem_cons_self)
      · rcases ih T h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

theorem ccxList_physical (c : Wire) (S T : List Wire) (hd : ∀ a ∈ S, a ∉ T) (hcS : c ∉ S) (hcT : c ∉ T) :
    GatePhysical (ccxList c S T) := by
  induction S generalizing T with
  | nil => simp [ccxList, GatePhysical]
  | cons a S ih =>
    cases T with
    | nil => simp [ccxList, GatePhysical]
    | cons t T =>
      have hat : a ≠ t := fun e => hd a List.mem_cons_self (e ▸ List.mem_cons_self)
      have hT : ∀ x ∈ S, x ∉ T := fun x hx e =>
        hd x (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ e)
      have hca : c ≠ a := fun e => hcS (e ▸ List.mem_cons_self)
      have hct : c ≠ t := fun e => hcT (e ▸ List.mem_cons_self)
      have hp := ih T hT (fun e => hcS (List.mem_cons_of_mem _ e)) (fun e => hcT (List.mem_cons_of_mem _ e))
      intro i hi
      simp only [ccxList, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp [ECDSAAdd.RecordedQuantum.PhysicalInstr, ProperGate, hca, hct, hat]
      · exact hp i hi

theorem portTemplate_some_inst {n : Nat} (read : ConstantBit n → Bool) (c : Wire)
    (ports : List (LookupPort n)) (a : Nat) :
    (portTemplate (some c) ports a).instantiate read = cBits c (portTargets ports) (portBits read ports a) := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    have h : portTargets (p :: ports) = p.target :: portTargets ports := rfl
    have h' : portBits read (p :: ports) a = decide (read (p.ref a) = p.value) :: portBits read ports a := rfl
    rw [h, h', portTemplate_cons, Tmpl.instantiate_cons, ih]
    by_cases hb : read (p.ref a) = p.value <;> simp [cBits, TInstr.instantiate, hb]

theorem ScrSim.ccx (S S' T : List Wire) (c : Wire) (k k' : List Bool) (hmap : S'.map (xMask S k) = k')
    (hS : ∀ a ∈ S', a ∈ S) (hd : ∀ a ∈ S, a ∉ T) (hcS : c ∉ S) (hcT : c ∉ T) :
    ScrSim S k (ccxList c S' T) (cBits c T k') where
  records := by rw [ccxList_records, cBits_records]
  step m x hx := by
    constructor
    · rw [ccxList_run c S' T m _ (fun a ha => hd a (hS a ha)) hcT, cBits_run c T k' m x hcT]
      have hm : S'.map (scrLoad S k x).basis = k' := by
        rw [← hmap]
        apply List.map_congr_left
        intro a ha
        simp [scrLoad, hx a (hS a ha)]
      have hcv : (scrLoad S k x).basis c = x.basis c := by
        simp [scrLoad, xMask_outside S k c hcS]
      rw [hm, hcv]
      simp only [scrLoad]
      apply congrArg (State.mk x.phase)
      funext q
      exact scr_xor_swap' _ _ _
    · intro a ha
      rw [cBits_run c T k' m x hcT]
      simp [hx a ha, xMask_outside T k' a (hd a ha)]

theorem xMask_map_sub (A B : List Wire) (kA kB : List Bool) (S' : List Wire) (hS' : ∀ a ∈ S', a ∉ B)
    (hl : A.length = kA.length) : S'.map (xMask (A ++ B) (kA ++ kB)) = S'.map (xMask A kA) := by
  apply List.map_congr_left
  intro q hq
  rw [xMask_append _ _ _ _ hl, xMask_outside B kB q (hS' q hq), Bool.xor_false]

theorem indexed_split {n : Nat} (ws : List Wire) (refs : Nat → Nat → ConstantBit n) (v : Bool) :
    indexedPorts (ws.take 1) (fun a _ => refs a 0) v ++ indexedPorts (ws.drop 1) (fun a i => refs a (i+1)) v =
      indexedPorts ws refs v := by
  cases ws <;> rfl

theorem poolWire_eq (i : Nat) (hi : i < 5699) : streamLayout.core.poolWire i = 14115 + i := by
  rw [deltaPoolWire_eq]
  change ((List.range' 4115 5699).map streamWire).getD i 0 = 14115 + i
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range']
  unfold streamWire
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  omega

theorem map_poolWire (s n : Nat) (h : s + n ≤ 5699) :
    (List.range' s n).map streamLayout.core.poolWire = List.range' (14115 + s) n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    rw [List.getElem_map, List.getElem_range', List.getElem_range', poolWire_eq _ (by omega)]
    exact (Nat.add_assoc _ _ _).symm

/-- The explicit wire numbers of the widened output scratch (pool position `i` is wire `14115 + i`). -/
theorem scrAll_eq_explicit : scrWires ++ (List.range' 1284 255).map streamLayout.core.poolWire =
    (14373 :: List.range' 14374 256 ++ [14883]) ++ (14884 :: List.range' 14885 256 ++ [15141]) ++
      List.range' 15399 255 := by
  simp only [scrWires, scrPairWires, scrShortWires, List.map_cons, List.map_append, List.map_nil,
    map_poolWire _ _ (by norm_num : 259 + 256 ≤ 5699), map_poolWire _ _ (by norm_num : 770 + 256 ≤ 5699),
    map_poolWire _ _ (by norm_num : 1284 + 255 ≤ 5699), poolWire_eq _ (by norm_num : 258 < 5699),
    poolWire_eq _ (by norm_num : 768 < 5699), poolWire_eq _ (by norm_num : 769 < 5699),
    poolWire_eq _ (by norm_num : 1026 < 5699)]

/-- Pool positions 1284 through 1538, clean old work wires that the output half never uses. -/
def scrDExtraWires : List Wire := (List.range' 1284 255).map streamLayout.core.poolWire

def scrDWires : List Wire := scrShortWires ++ scrDExtraWires

def scrAllWires : List Wire := scrWires ++ scrDExtraWires

def scrDTargets : List Wire := streamLayout.point.finite :: streamLayout.point.x ++ streamLayout.point.y

def scrDExtraBits (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  indexedPorts (streamLayout.point.y.drop 1) (fun a i => wFields rows .doubleY a (i+1)) true

/-- The doubled-point corner ports of the parent row. -/
def scrDPointPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  ⟨wBit rows .doubleInfinity, false, streamLayout.point.finite⟩ ::
    indexedPorts streamLayout.point.x (wFields rows .doubleX) true ++
    indexedPorts streamLayout.point.y (wFields rows .doubleY) true

theorem scrDPointPorts_eq (rows : Nat → Fin 32768) :
    scrShortBits rows ++ scrDExtraBits rows = scrDPointPorts rows := by
  have h := indexed_split streamLayout.point.y (wFields rows .doubleY) true
  simp only [scrShortBits, scrDExtraBits, scrDPointPorts]
  rw [← h]
  simp only [List.cons_append, List.append_assoc]
  rfl

def scrDPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  scrPorts rows ++ retarget (scrDExtraBits rows) scrDExtraWires

theorem scrDExtraWires_length : scrDExtraWires.length = 255 := by simp [scrDExtraWires]

theorem scrDExtraBits_length (rows : Nat → Fin 32768) : (scrDExtraBits rows).length = 255 := by
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  simp [scrDExtraBits, hy]

theorem scrAll_eq : scrAllWires = (14373 :: List.range' 14374 256 ++ [14883]) ++
    (14884 :: List.range' 14885 256 ++ [15141]) ++ List.range' 15399 255 := scrAll_eq_explicit

theorem scrDWires_eq : scrDWires = (14884 :: List.range' 14885 256 ++ [15141]) ++ List.range' 15399 255 := by
  simp only [scrDWires, scrShortWires, scrDExtraWires, List.map_cons, List.map_append, List.map_nil,
    map_poolWire _ _ (by norm_num : 770 + 256 ≤ 5699), map_poolWire _ _ (by norm_num : 1284 + 255 ≤ 5699),
    poolWire_eq _ (by norm_num : 769 < 5699), poolWire_eq _ (by norm_num : 1026 < 5699)]

theorem scrAllWires_nodup : scrAllWires.Nodup := by
  rw [scrAll_eq]
  have h : ((14373 :: List.range' 14374 256 ++ [14883]) ++ (14884 :: List.range' 14885 256 ++ [15141]) ++
      List.range' 15399 255).IsChain (· < ·) := by decide +kernel
  exact (List.isChain_iff_pairwise.mp h).imp (fun h => Nat.ne_of_lt h)

theorem scrAll_bounds : ∀ a ∈ scrAllWires, 14373 ≤ a ∧ a < 15654 := by
  rw [scrAll_eq]
  intro a ha
  simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.mem_singleton, List.not_mem_nil,
    or_false] at ha
  dsimp only [Wire] at *
  omega

/-- Disjointness from the scratch by a single pass over the other list. -/
theorem scrAll_not_of (L : List Wire) (hL : (L.all fun b => decide (b < 14373 ∨ 15654 ≤ b)) = true) :
    ∀ a ∈ scrAllWires, a ∉ L := by
  intro a ha hm
  have h1 := List.all_eq_true.mp hL a hm
  have h2 := scrAll_bounds a ha
  simp only [decide_eq_true_eq] at h1
  dsimp only [Wire] at *
  omega

theorem scrAll_pair_targets : ∀ a ∈ scrAllWires, a ∉ scrPairTargets := scrAll_not_of _ (by decide +kernel)
theorem scrAll_short_targets : ∀ a ∈ scrAllWires, a ∉ scrShortTargets := scrAll_not_of _ (by decide +kernel)
theorem scrAll_d_targets : ∀ a ∈ scrAllWires, a ∉ scrDTargets := scrAll_not_of _ (by decide +kernel)
theorem scrAll_y : ∀ a ∈ scrAllWires, a ∉ [yLow streamLayout] := scrAll_not_of _ (by decide +kernel)
theorem scrAll_p1 : ∀ a ∈ scrAllWires, a ∉ (streamLayout.control :: [yLow streamLayout,
    streamLayout.infinitySelect, streamLayout.core.equalNegY] ++ (pairPorts streamLayout).flatMap ZeroBit.wires) :=
  scrAll_not_of _ (by decide +kernel)
theorem scrAll_p2 : ∀ a ∈ scrAllWires, a ∉ (streamLayout.core.double :: streamLayout.doubleSelect ::
    (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).flatMap ZeroBit.wires) :=
  scrAll_not_of _ (by decide +kernel)
theorem scrAll_neg : ∀ a ∈ scrAllWires, a ∉ (negateYLayout streamLayout).wires streamLayout.core.equalNegY :=
  scrAll_not_of _ (by decide +kernel)
theorem scrAll_flags : ∀ a ∈ scrAllWires, a ∉ [streamLayout.control, streamLayout.core.generic,
    streamLayout.infinitySelect, streamLayout.doubleSelect, streamLayout.genericSelect,
    streamLayout.core.equalNegY] := scrAll_not_of _ (by decide +kernel)
theorem scrD_eqNegY : streamLayout.core.equalNegY ∉ scrAllWires ∧ streamLayout.core.equalNegY ∉ scrDTargets := by
  constructor
  · exact fun h => scrAll_not_of [streamLayout.core.equalNegY] (by decide +kernel) _ h List.mem_cons_self
  · decide +kernel

attribute [local irreducible] streamLayout

theorem scrDExtra_pool (a : Wire) (ha : a ∈ scrDExtraWires) : a ∈ streamLayout.dialogPool := by
  simp only [scrDExtraWires, List.mem_map, List.mem_range'_1] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact deltaPool_mem_dialog _ (by omega)

theorem scrAll_pool (a : Wire) (ha : a ∈ scrAllWires) : a ∈ streamLayout.dialogPool := by
  rcases List.mem_append.mp ha with h | h
  · exact scrWires_pool a h
  · exact scrDExtra_pool a h

theorem scrDExtra_targets (rows : Nat → Fin 32768) :
    portTargets (retarget (scrDExtraBits rows) scrDExtraWires) = scrDExtraWires :=
  retarget_targets _ _ ((scrDExtraBits_length _).trans scrDExtraWires_length.symm)

theorem scrDPorts_targets (rows : Nat → Fin 32768) : portTargets (scrDPorts rows) = scrAllWires := by
  have h1 := scrPorts_targets rows
  have h2 := scrDExtra_targets rows
  simp only [portTargets] at h1 h2
  simp only [scrDPorts, scrAllWires, portTargets, List.map_append, h1, h2]

theorem scrDPorts_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (scrDPorts rows) a =
      (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
        portBits read (scrDExtraBits rows) a := by
  have h2 := retarget_bits read (scrDExtraBits rows) scrDExtraWires
    ((scrDExtraBits_length _).trans scrDExtraWires_length.symm) a
  simp only [portBits] at h2
  have h1 := scrPorts_bits read rows a
  simp only [portBits] at h1
  simp only [scrDPorts, portBits, List.map_append, h1, h2]

theorem scrDPointPorts_targets (rows : Nat → Fin 32768) : portTargets (scrDPointPorts rows) = scrDTargets := by
  have h := indexedPorts_targets streamLayout.point.x (wFields rows .doubleX) true
  have h' := indexedPorts_targets streamLayout.point.y (wFields rows .doubleY) true
  simp only [portTargets] at h h'
  simp only [scrDPointPorts, scrDTargets, portTargets, List.map_append, List.map_cons, h, h', List.cons_append]

theorem scrDPointPorts_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (scrDPointPorts rows) a = portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a := by
  rw [← scrDPointPorts_eq]
  simp [portBits]

def scrDCorners (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ((negateYLayout streamLayout).program streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c) ++
  wLiteral ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ++
  wLiteral (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) ++
  wLiteral ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ++
  wLiteral ([.CX streamLayout.infinitySelect streamLayout.doubleSelect]) ++
  wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) ++
  wLiteral ([.CX streamLayout.infinitySelect streamLayout.doubleSelect]) ++
  wLiteral ([.CX streamLayout.genericSelect streamLayout.core.equalNegY]) ++
  wPoint streamLayout.core.equalNegY streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .negY) ++
  wLiteral ([.CX streamLayout.genericSelect streamLayout.core.equalNegY])

def scrDMiddle : WCode 32768 :=
  wLiteral (cxList scrPairWires scrPairTargets) ++
  wZeroWith (wPairTailBare (yLow streamLayout) streamLayout.infinitySelect streamLayout.core.equalNegY)
    streamLayout.control (pairPorts streamLayout) ++
  wLiteral (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
  wLiteral (cxList scrShortWires scrShortTargets) ++
  wLiteral scrP2 ++
  wLiteral (cxList scrShortWires scrShortTargets)

/-- Output half: one load serves the doubled-point corner and both comparisons. -/
def portSuffixCodeD (rows : Nat → Fin 32768) : WCode 32768 :=
  [.lookup none (scrDPorts rows)] ++ scrDCorners rows ++ wLiteral (pointDialogGenericFlag streamLayout) ++
  scrDMiddle ++ [.lookup none (scrDPorts rows)] ++
  wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
  wLiteral (Arith.padding (streamLayout.core.poolWire 0) 49864)



end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def scrNegP : Program := (negateYLayout streamLayout).program streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
def scrSw1 : Program := [.CX streamLayout.doubleSelect streamLayout.core.equalNegY]
def scrSw2 : Program := [.CX streamLayout.infinitySelect streamLayout.doubleSelect]
def scrSw3 : Program := [.CX streamLayout.genericSelect streamLayout.core.equalNegY]

def scrCPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  ⟨wBit rows .infinity, false, streamLayout.point.finite⟩ ::
    indexedPorts streamLayout.point.x (wFields rows .x) true ++ indexedPorts streamLayout.point.y (wFields rows .y) true

def scrNPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  ⟨wBit rows .infinity, false, streamLayout.point.finite⟩ ::
    indexedPorts streamLayout.point.x (wFields rows .x) true ++ indexedPorts streamLayout.point.y (wFields rows .negY) true

theorem scr_point_targets (fin : Nat → ConstantBit 32768) (xr yr : Nat → Nat → ConstantBit 32768) :
    portTargets (⟨fin, false, streamLayout.point.finite⟩ ::
      indexedPorts streamLayout.point.x xr true ++ indexedPorts streamLayout.point.y yr true) = scrDTargets := by
  have h := indexedPorts_targets streamLayout.point.x xr true
  have h' := indexedPorts_targets streamLayout.point.y yr true
  simp only [portTargets] at h h'
  simp only [scrDTargets, portTargets, List.map_append, List.map_cons, h, h', List.cons_append]

theorem scr_lookup_some_inst (read : ConstantBit 32768 → Bool) (c : Wire) (ports : List (LookupPort 32768)) (a : Nat) :
    (specialize ([.lookup (some c) ports] : WCode 32768) a).instantiate read =
      cBits c (portTargets ports) (portBits read ports a) := by
  rw [← portTemplate_some_inst]
  simp [specialize, WInstr.specialize]

theorem scrDCorners_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (scrDCorners rows) a).instantiate read =
      scrNegP ++ (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets (portBits read (scrNPorts rows) a) ++ scrSw3)))))))) := by
  have e1 : wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) =
      [.lookup (some streamLayout.doubleSelect) (scrCPorts rows)] := rfl
  have e2 : wPoint streamLayout.core.equalNegY streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .negY) =
      [.lookup (some streamLayout.core.equalNegY) (scrNPorts rows)] := rfl
  simp only [scrDCorners, e1, e2, specialize_append, Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit,
    scr_lookup_some_inst, scrCPorts, scrNPorts, scr_point_targets, scrNegP, scrSw1, scrSw2, scrSw3, List.append_assoc]

theorem scrCorners_inst2 (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (scrCorners rows) a).instantiate read =
      scrNegP ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a) ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets (portBits read (scrNPorts rows) a) ++ scrSw3)))))))) := by
  have e0 : wPoint streamLayout.core.equalNegY streamLayout.point (wBit rows .doubleInfinity) (wFields rows .doubleX)
      (wFields rows .doubleY) = [.lookup (some streamLayout.core.equalNegY) (scrDPointPorts rows)] := rfl
  have e1 : wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) =
      [.lookup (some streamLayout.doubleSelect) (scrCPorts rows)] := rfl
  have e2 : wPoint streamLayout.core.equalNegY streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .negY) =
      [.lookup (some streamLayout.core.equalNegY) (scrNPorts rows)] := rfl
  have hD := scrDPointPorts_targets rows
  have hB := scrDPointPorts_bits read rows a
  simp only [scrCorners, e0, e1, e2, specialize_append, Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit,
    scr_lookup_some_inst, hD, hB, scrCPorts, scrNPorts, scr_point_targets, scrNegP, scrSw1, scrSw2, scrSw3, List.append_assoc]

theorem scrAllP1_wires (a : Wire) (ha : a ∈ scrAllWires) : a ∉ ECDSAAdd.wires scrP1 := by
  have htail (c : Wire) : wires
      ([.CCX c (yLow streamLayout) streamLayout.infinitySelect, .X (yLow streamLayout),
        .CCX c (yLow streamLayout) streamLayout.core.equalNegY] : Program) ⊆
      (c :: [yLow streamLayout, streamLayout.infinitySelect, streamLayout.core.equalNegY]).toFinset := by
    intro q hq
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq ⊢
    tauto
  have hz := deltaZeroWith_support
    (fun c : Wire => ([.CCX c (yLow streamLayout) streamLayout.infinitySelect, .X (yLow streamLayout),
      .CCX c (yLow streamLayout) streamLayout.core.equalNegY] : Program))
    ([yLow streamLayout, streamLayout.infinitySelect, streamLayout.core.equalNegY] : List Wire) htail
    streamLayout.control (pairPorts streamLayout)
  intro hq
  exact scrAll_p1 a ha (List.mem_toFinset.mp (hz hq))

theorem scrAllP2_wires (a : Wire) (ha : a ∈ scrAllWires) : a ∉ ECDSAAdd.wires scrP2 := by
  intro hq
  rw [scrP2, zeroControlled_wires] at hq
  exact scrAll_p2 a ha (List.mem_toFinset.mp hq)

theorem scrAll_flag_avoid (a : Wire) (ha : a ∈ scrAllWires) (p : Program)
    (hp : ∀ q ∈ ECDSAAdd.wires p, q ∈ [streamLayout.control, streamLayout.core.generic,
      streamLayout.infinitySelect, streamLayout.doubleSelect, streamLayout.genericSelect,
      streamLayout.core.equalNegY]) : a ∉ ECDSAAdd.wires p := fun hq => scrAll_flags a ha (hp a hq)

theorem scrSw_flags :
    (∀ q ∈ ECDSAAdd.wires scrSw1, q ∈ [streamLayout.control, streamLayout.core.generic, streamLayout.infinitySelect,
      streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY]) ∧
    (∀ q ∈ ECDSAAdd.wires scrSw2, q ∈ [streamLayout.control, streamLayout.core.generic, streamLayout.infinitySelect,
      streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY]) ∧
    (∀ q ∈ ECDSAAdd.wires scrSw3, q ∈ [streamLayout.control, streamLayout.core.generic, streamLayout.infinitySelect,
      streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY]) ∧
    (∀ q ∈ ECDSAAdd.wires (pointDialogGenericFlag streamLayout), q ∈ [streamLayout.control, streamLayout.core.generic,
      streamLayout.infinitySelect, streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro q hq <;>
    simp [scrSw1, scrSw2, scrSw3, pointDialogGenericFlag, pointInPlaceGenericFlag, ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq ⊢ <;>
    tauto

theorem scrD_maps (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    scrPairWires.map (xMask scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++
      portBits read (scrShortBits rows) a) ++ portBits read (scrDExtraBits rows) a)) =
        portBits read (scrPairBits rows (wBit rows .y)) a ∧
    scrShortWires.map (xMask scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++
      portBits read (scrShortBits rows) a) ++ portBits read (scrDExtraBits rows) a)) =
        portBits read (scrShortBits rows) a ∧
    scrDWires.map (xMask scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++
      portBits read (scrShortBits rows) a) ++ portBits read (scrDExtraBits rows) a)) =
        portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a := by
  generalize hkP : portBits read (scrPairBits rows (wBit rows .y)) a = kP
  generalize hkS : portBits read (scrShortBits rows) a = kS
  generalize hkE : portBits read (scrDExtraBits rows) a = kE
  have hlP : scrPairWires.length = kP.length := by
    rw [← hkP]; simp [portBits, scrPairBits_length, scrPairWires_length]
  have hlS : scrShortWires.length = kS.length := by
    rw [← hkS]; simp [portBits, scrShortBits_length, scrShortWires_length]
  have hlE : scrDExtraWires.length = kE.length := by
    rw [← hkE]; simp [portBits, scrDExtraBits_length, scrDExtraWires_length]
  have hlW : scrWires.length = (kP ++ kS).length := by
    simp only [scrWires, List.length_append, hlP, hlS]
  have hnW : (scrWires ++ scrDExtraWires).Nodup := scrAllWires_nodup
  have eD : scrAllWires = scrPairWires ++ scrDWires := by
    simp only [scrAllWires, scrWires, scrDWires, List.append_assoc]
  have hnD : (scrPairWires ++ scrDWires).Nodup := eD ▸ scrAllWires_nodup
  have hdisjE : ∀ q ∈ scrWires, q ∉ scrDExtraWires := fun q hq he => (List.nodup_append'.mp hnW).2.2 hq he
  refine ⟨?_, ?_, ?_⟩
  · rw [scrAllWires, xMask_map_sub _ _ _ _ _ (fun q hq => hdisjE q (List.mem_append_left _ hq)) hlW]
    exact xMask_map_left _ _ _ _ scrWires_nodup hlP
  · rw [scrAllWires, xMask_map_sub _ _ _ _ _ (fun q hq => hdisjE q (List.mem_append_right _ hq)) hlW]
    exact xMask_map_right _ _ _ _ scrWires_nodup hlP hlS
  · rw [eD, List.append_assoc]
    exact xMask_map_right _ _ _ _ hnD hlP (by simp only [scrDWires, List.length_append, hlS, hlE])

theorem neg_disjoint (K : NegLayout) (flag p c : Nat) (hw : K.work.length = K.word.length) (S : List Wire)
    (hS : ∀ a ∈ S, a ∉ K.wires flag) : ∀ a ∈ S, a ∉ ECDSAAdd.wires (K.program flag p c) := by
  intro a ha hq
  exact hS a ha (List.mem_toFinset.mp (K.program_support flag p c hw hq))

theorem scrD_negSim (K : List Bool) : ScrSim scrAllWires K scrNegP scrNegP :=
  ScrSim.disjoint scrAllWires K scrNegP
    (neg_disjoint (negateYLayout streamLayout) streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
      (negateYLayout_widths streamLayout streamLayout_widths).2 scrAllWires scrAll_neg)

theorem scrD_swSim (K : List Bool) :
    ScrSim scrAllWires K scrSw1 scrSw1 ∧ ScrSim scrAllWires K scrSw2 scrSw2 ∧ ScrSim scrAllWires K scrSw3 scrSw3 ∧
      ScrSim scrAllWires K (pointDialogGenericFlag streamLayout) (pointDialogGenericFlag streamLayout) := by
  have fl := scrSw_flags
  exact ⟨ScrSim.disjoint scrAllWires K scrSw1 (fun w hw' => scrAll_flag_avoid w hw' _ fl.1),
    ScrSim.disjoint scrAllWires K scrSw2 (fun w hw' => scrAll_flag_avoid w hw' _ fl.2.1),
    ScrSim.disjoint scrAllWires K scrSw3 (fun w hw' => scrAll_flag_avoid w hw' _ fl.2.2.1),
    ScrSim.disjoint scrAllWires K (pointDialogGenericFlag streamLayout) (fun w hw' => scrAll_flag_avoid w hw' _ fl.2.2.2)⟩

theorem scrD_cbitsSim (K k : List Bool) (c : Wire) (hc : c ∈ [streamLayout.control, streamLayout.core.generic,
    streamLayout.infinitySelect, streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY]) :
    ScrSim scrAllWires K (cBits c scrDTargets k) (cBits c scrDTargets k) := by
  apply ScrSim.disjoint
  intro w hw' hq
  rcases cBits_wires c scrDTargets k w hq with h | h
  · subst h
    exact scrAll_flags _ hw' hc
  · exact scrAll_d_targets w hw' h

theorem scrD_ccxSim (K kD : List Bool) (hmapD : scrDWires.map (xMask scrAllWires K) = kD) :
    ScrSim scrAllWires K (ccxList streamLayout.core.equalNegY scrDWires scrDTargets)
      (cBits streamLayout.core.equalNegY scrDTargets kD) := by
  have sub_d : ∀ w ∈ scrDWires, w ∈ scrAllWires := by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h
  exact ScrSim.ccx scrAllWires scrDWires scrDTargets streamLayout.core.equalNegY K kD
    hmapD sub_d scrAll_d_targets scrD_eqNegY.1 scrD_eqNegY.2

theorem scrD_cornerSim (S : List Wire) (K kD kC kN : List Bool) (hS : S = scrAllWires)
    (hmapD : scrDWires.map (xMask S K) = kD) :
    ScrSim S K
      (scrNegP ++ (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets kC ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets kN ++ scrSw3)))))))))
      (scrNegP ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets kD ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets kC ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets kN ++ scrSw3))))))))) := by
  subst hS
  have hneg := scrD_negSim K
  have hs := scrD_swSim K
  have hcc := scrD_ccxSim K kD hmapD
  have hC := scrD_cbitsSim K kC streamLayout.doubleSelect
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hN := scrD_cbitsSim K kN streamLayout.core.equalNegY
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))))
  exact hneg.append (hs.1.append (hcc.append (hs.1.append (hs.2.1.append (hC.append (hs.2.1.append (hs.2.2.1.append
    (hN.append hs.2.2.1))))))))

theorem scrD_midSim (S : List Wire) (K kP kS : List Bool) (hS : S = scrAllWires)
    (hmapP : scrPairWires.map (xMask S K) = kP) (hmapS : scrShortWires.map (xMask S K) = kS) :
    ScrSim S K
      (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets))))))
      (pointDialogGenericFlag streamLayout ++
       (xBits scrPairTargets kP ++ (scrP1 ++ ((xBits scrPairTargets kP ++ [.X (yLow streamLayout)]) ++
        (xBits scrShortTargets kS ++ (scrP2 ++ xBits scrShortTargets kS)))))) := by
  subst hS
  have sub_pair : ∀ w ∈ scrPairWires, w ∈ scrAllWires := fun w hw =>
    List.mem_append_left _ (List.mem_append_left _ hw)
  have sub_short : ∀ w ∈ scrShortWires, w ∈ scrAllWires := fun w hw =>
    List.mem_append_left _ (List.mem_append_right _ hw)
  have hf := (scrD_swSim K).2.2.2
  have hxP := ScrSim.cx scrAllWires scrPairWires scrPairTargets K kP hmapP sub_pair scrAll_pair_targets
  have hxS := ScrSim.cx scrAllWires scrShortWires scrShortTargets K kS hmapS sub_short scrAll_short_targets
  have hp1 := ScrSim.disjoint scrAllWires K scrP1 scrAllP1_wires
  have hp2 := ScrSim.disjoint scrAllWires K scrP2 scrAllP2_wires
  have hx := ScrSim.disjoint scrAllWires K ([.X (yLow streamLayout)] : Program) (by
    intro w hw' hq
    apply scrAll_y w hw'
    simpa [ECDSAAdd.wires, ECDSAAdd.Instr.wires] using hq)
  exact hf.append (hxP.append (hp1.append ((hxP.append hx).append (hxS.append (hp2.append hxS)))))

theorem scrD_sim (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    ScrSim scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
        portBits read (scrDExtraBits rows) a)
      ((scrNegP ++ (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets (portBits read (scrNPorts rows) a) ++ scrSw3))))))))) ++
       (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets)))))))
      ((scrNegP ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a) ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets (portBits read (scrNPorts rows) a) ++ scrSw3))))))))) ++
       (pointDialogGenericFlag streamLayout ++
       (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ (scrP1 ++
        ((xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ [.X (yLow streamLayout)]) ++
        (xBits scrShortTargets (portBits read (scrShortBits rows) a) ++
          (scrP2 ++ xBits scrShortTargets (portBits read (scrShortBits rows) a)))))))) := by
  have hm := scrD_maps read rows a
  exact (scrD_cornerSim _ _ _ _ _ rfl hm.2.2).append (scrD_midSim _ _ _ _ rfl hm.1 hm.2.1)

theorem scr_sandwich_append (S : List Wire) (k : List Bool) (P P' Z : Program) (h : ScrSim S k P P')
    (m : List Bool) (s : State) (hs : ∀ a ∈ S, s.basis a = false) :
    run (xBits S k ++ P ++ xBits S k ++ Z) m s = run (P' ++ Z) m s := by
  rw [run_append (xBits S k ++ P ++ xBits S k), run_append P', scr_sandwich S k P P' h _ s hs]
  simp [measurementCount_append, xBits_records, h.records]

theorem portSuffixD_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (portSuffixCodeD rows) a).instantiate read =
      xBits scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
        portBits read (scrDExtraBits rows) a) ++
      ((specialize (scrDCorners rows) a).instantiate read ++ (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets))))))) ++
      xBits scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
        portBits read (scrDExtraBits rows) a) ++
      (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect ++
        ([.CX streamLayout.control streamLayout.core.equalX] ++ ([.CX streamLayout.control streamLayout.core.double] ++
          Arith.padding (streamLayout.core.poolWire 0) 49864))) := by
  simp only [portSuffixCodeD, scrDMiddle, specialize_append, Tmpl.instantiate_append, scr_lookup_inst, specialize_literal,
    Tmpl.instantiate_lit, scr_chain_inst, scrDPorts_targets, scrDPorts_bits, List.append_assoc]


theorem portSuffixD_run (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) (C : Point)
    (row : RowReads read (rows address) C)
    (hop : read (wBit rows .negY 0 address) = !(read (wBit rows .y 0 address)))
    (m : List Bool) (s : State) (hs : ∀ w ∈ scrAllWires, s.basis w = false) :
    run ((specialize (portSuffixCodeD rows) address).instantiate read) m s =
      run ((specialize (WEXUnlookup.suffixCode streamLayout rows) address).instantiate read) m s := by
  rw [portSuffixD_inst, scrDCorners_inst, scr_sandwich_append _ _ _ _ _ (scrD_sim read rows address) m s hs]
  have eC : scrNegP ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) address ++ portBits read (scrDExtraBits rows) address) ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) address) ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets (portBits read (scrNPorts rows) address) ++ scrSw3)))))))) =
      thirdCorners streamLayout C := by
    rw [← scrCorners_inst2, scrCorners_inst read rows address C row]
  rw [eC]
  have hsh := portSuffix_shape rows
  dsimp only at hsh
  rw [hsh.2]
  have hp := (portSuffix_inst_pre read rows address C row).1
  simp only [specialize_append, Tmpl.instantiate_append] at hp ⊢
  rw [hp, scrOld_inst]
  simp only [specialize_literal, Tmpl.instantiate_lit]
  have r1 := run_replace_inside [] (pointDialogGenericFlag streamLayout ++
       (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) address) ++ (scrP1 ++
        ((xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) address) ++ [.X (yLow streamLayout)]) ++
        (xBits scrShortTargets (portBits read (scrShortBits rows) address) ++
          (scrP2 ++ xBits scrShortTargets (portBits read (scrShortBits rows) address)))))) ++
      (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect ++
        ([.CX streamLayout.control streamLayout.core.equalX] ++ ([.CX streamLayout.control streamLayout.core.double] ++
          Arith.padding (streamLayout.core.poolWire 0) 49864))))
    (thirdCorners streamLayout C) (secondCorners streamLayout C) (thirdCorners_records _ _)
    (thirdCorners_run streamLayout streamLayout_widths streamLayout_nodup C) m s
  have r2 := run_replace_inside (secondCorners streamLayout C ++ (pointDialogGenericFlag streamLayout ++
       (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) address) ++ scrP1)))
      (xBits scrShortTargets (portBits read (scrShortBits rows) address) ++
          (scrP2 ++ xBits scrShortTargets (portBits read (scrShortBits rows) address)) ++
      (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect ++
        ([.CX streamLayout.control streamLayout.core.equalX] ++ ([.CX streamLayout.control streamLayout.core.double] ++
          Arith.padding (streamLayout.core.poolWire 0) 49864))))
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) address) ++ [.X (yLow streamLayout)])
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .negY)) address))
    (by simp [xBits_records, measurementCount])
    (fun m st => scr_parity_fix read rows address hop m st) m s
  simp only [List.nil_append, List.append_assoc] at r1 r2 ⊢
  rw [r1, r2]

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem portSuffixD_records (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) (C : Point)
    (row : RowReads read (rows address) C) :
    measurementCount ((specialize (portSuffixCodeD rows) address).instantiate read) =
      measurementCount ((specialize (WEXUnlookup.suffixCode streamLayout rows) address).instantiate read) := by
  have hsim := (scrD_sim read rows address).records
  rw [portSuffixD_inst, scrDCorners_inst]
  have eC : scrNegP ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) address ++ portBits read (scrDExtraBits rows) address) ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) address) ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets (portBits read (scrNPorts rows) address) ++ scrSw3)))))))) =
      thirdCorners streamLayout C := by
    rw [← scrCorners_inst2, scrCorners_inst read rows address C row]
  rw [eC] at hsim
  have hsh := portSuffix_shape rows
  dsimp only at hsh
  rw [hsh.2]
  have hp := (portSuffix_inst_pre read rows address C row).1
  simp only [specialize_append, Tmpl.instantiate_append] at hp ⊢
  rw [hp, scrOld_inst]
  simp only [specialize_literal, Tmpl.instantiate_lit, measurementCount_append, xBits_records] at hsim ⊢
  simp only [thirdCorners_records] at hsim
  have hX : measurementCount ([.X (yLow streamLayout)] : Program) = 0 := rfl
  omega

def portFinite3 (rows : Nat → Fin 32768) : WCode 32768 :=
  portPrefixCode rows ++ wGeneric streamLayout rows ++ portSuffixCodeD rows

def portRowCode3 (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ portFinite3 rows ++ wLiteral ([.X 838])

attribute [local irreducible] streamLayout ECDSAAdd.regValue ECDSAAdd.run in
theorem portRow3_run_eq (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s)) (m : List Bool) :
    run ((specialize (portRowCode3 rows) address).instantiate read) m ⟨false,s⟩ =
      run ((specialize (rowAddCode rows) address).instantiate read) m ⟨false,s⟩ := by
  classical
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hop := WEXUnlookup.row_opposite read rows address hc hr h₁
  have hpe := WEXUnlookup.prefixCode_equiv read streamLayout hw hn rows address hop
  have hpi := WEXUnlookup.referencePrefix_inst read streamLayout hw rows address hc hr h₁ h₂ hD hDo
  have hG : (specialize (wGeneric streamLayout rows) address).instantiate read = Arith.genericS streamLayout cx cy := by
    rw [specialize_generic]
    exact Arith.genericT_inst streamLayout hc hr
  have hclean0 : ∀ w ∈ scrWires, (⟨false, flipInfinity s⟩ : State).basis w = false :=
    fun w hw' => (regValue_zero _ _).mp hs.clean w (scrWires_pool w hw')
  let P0' := (specialize (portPrefixCode rows) address).instantiate read
  let P0 := (specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read
  let G0 := (specialize (wGeneric streamLayout rows) address).instantiate read
  let BD := (specialize (portSuffixCodeD rows) address).instantiate read
  let B' := (specialize (WEXUnlookup.suffixCode streamLayout rows) address).instantiate read
  have e1 : (specialize (portRowCode3 rows) address).instantiate read = (([.X 838] : Program) ++ P0' ++ G0) ++ BD ++ ([.X 838] : Program) := by
    simp only [portRowCode3, portFinite3, specialize_append, specialize_literal, Tmpl.instantiate_append, Tmpl.instantiate_lit,
      P0', G0, BD, List.append_assoc]
  have e2 : (specialize (rowAddCode rows) address).instantiate read = (([.X 838] : Program) ++ P0 ++ G0) ++ B' ++ ([.X 838] : Program) := by
    simp only [rowAddCode, wFinite23_split, specialize_append, specialize_literal, Tmpl.instantiate_append, Tmpl.instantiate_lit,
      WEXUnlookup.specialize_fusedPrefix, P0, G0, B', List.append_assoc]
  have e3 : (([.X 838] : Program) ++ P0' ++ G0) ++ B' ++ ([.X 838] : Program) =
      ([.X 838] : Program) ++ P0' ++ (G0 ++ B' ++ ([.X 838] : Program)) := by simp only [List.append_assoc]
  have e4 : (([.X 838] : Program) ++ P0 ++ G0) ++ B' ++ ([.X 838] : Program) =
      ([.X 838] : Program) ++ P0 ++ (G0 ++ B' ++ ([.X 838] : Program)) := by simp only [List.append_assoc]
  have hprefix (k n : List Bool) : run P0' n (run ([.X 838] : Program) k ⟨false,s⟩) =
      run P0 n (run ([.X 838] : Program) k ⟨false,s⟩) := by
    rw [flip_run]
    exact portPrefix_run read rows address hop n _ hclean0
  have hsuf : ∀ k n, run BD n (run (([.X 838] : Program) ++ P0' ++ G0) k ⟨false,s⟩) =
      run B' n (run (([.X 838] : Program) ++ P0' ++ G0) k ⟨false,s⟩) := by
    intro k n
    apply portSuffixD_run read rows address _ hr hop
    intro w hw'
    let C : Point := .some hc
    let O := dialogInfinity true R
    let D := dialogDouble true R C
    let I := dialogInversePoint true R C
    let H := dialogException true R C
    let Gf := dialogOrdinary true R C
    let E := true && decide (dialogExceptionEnabled C)
    let K := true && decide (cy≠-cy)
    have reads := dialogFlagState_read streamLayout hn O D I Gf E H K
    have h7 := Arith.boundary_genericS streamLayout hw hn R true (dialogFlagState streamLayout O D I Gf E H K) hc
      (fun hg => ((dialogOrdinary_true true R C (WeierstrassCurve.Affine.Point.some_ne_zero hc)).mp (reads.2.2.2.1.symm.trans hg)).2)
    rw [reads.2.2.2.1] at h7
    have hP (k' : List Bool) : PointDialogBoundary streamLayout R true (dialogFlagState streamLayout O D I Gf E H K)
        (run P0 k' ⟨false, flipInfinity s⟩).basis := by
      have hb := (WEXUnlookup.prefixS_checked streamLayout hw hn R hc true ⟨false, flipInfinity s⟩ k' hs).2
      have he := hpe.2 k' ⟨false, flipInfinity s⟩
      rw [hpi] at he
      change PointDialogBoundary streamLayout R true (dialogFlagState streamLayout O D I Gf E H K)
        (run ((specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read) k' ⟨false, flipInfinity s⟩).basis
      rw [← he]
      exact hb
    have hA := portRun_split ([.X 838] : Program) P0' G0 ⟨false,s⟩ ⟨false, flipInfinity s⟩ (fun n => flip_run _ n) k
    obtain ⟨k1, k2, hA⟩ := hA
    rw [hA]
    have hpp : run P0' k2 ⟨false, flipInfinity s⟩ = run P0 k2 ⟨false, flipInfinity s⟩ :=
      portPrefix_run read rows address hop k2 _ hclean0
    rw [hpp]
    have hG' : G0 = Arith.genericS streamLayout cx cy := hG
    have hu := (h7 (run P0 k2 ⟨false, flipInfinity s⟩) k1 (hP _)).2
    rw [← hG'] at hu
    exact (regValue_zero _ _).mp hu.clean w (scrAll_pool w hw')
  rw [e1, e2, portSuffix_middle _ _ _ _ (portSuffixD_records read rows address _ hr) ⟨false,s⟩ hsuf m, e3, e4]
  exact portSuffix_middle _ _ _ _ (portPrefix_records read rows address) ⟨false,s⟩ hprefix m

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem portRow3_shape (rows : Nat → Fin 32768) :
    let H : WCode 32768 := portPrefixCode rows ++ wGeneric streamLayout rows
    let X : WCode 32768 := wLiteral ([.X 838])
    portRowCode3 rows = X ++ (H ++ portSuffixCodeD rows) ++ X ∧
    portRowCode2 rows = X ++ (H ++ portSuffixCode rows) ++ X := by
  dsimp only
  constructor
  · simp only [portRowCode3, portFinite3]
  · simp only [portRowCode2, portFinite2]

def sfxA : WCode 32768 :=
  wLiteral ((negateYLayout streamLayout).program streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c) ++
  wLiteral ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY])
def sfxB (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.CX streamLayout.doubleSelect streamLayout.core.equalNegY]) ++
  wLiteral ([.CX streamLayout.infinitySelect streamLayout.doubleSelect]) ++
  wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) ++
  wLiteral ([.CX streamLayout.infinitySelect streamLayout.doubleSelect]) ++
  wLiteral ([.CX streamLayout.genericSelect streamLayout.core.equalNegY]) ++
  wPoint streamLayout.core.equalNegY streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .negY) ++
  wLiteral ([.CX streamLayout.genericSelect streamLayout.core.equalNegY])
def sfxZ : WCode 32768 := wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
  wLiteral (Arith.padding (streamLayout.core.poolWire 0) 49864)
def sfxF : WCode 32768 := wLiteral (pointDialogGenericFlag streamLayout)
def sfxL (rows : Nat → Fin 32768) : WCode 32768 := [.lookup none (scrDPorts rows)]
def sfxL' (rows : Nat → Fin 32768) : WCode 32768 := [.lookup none (scrPorts rows)]
def sfxDp (rows : Nat → Fin 32768) : WCode 32768 := wPoint streamLayout.core.equalNegY streamLayout.point
  (wBit rows .doubleInfinity) (wFields rows .doubleX) (wFields rows .doubleY)
def sfxCC : WCode 32768 := wLiteral (ccxList streamLayout.core.equalNegY scrDWires scrDTargets)

theorem suffixD_split (rows : Nat → Fin 32768) :
    portSuffixCodeD rows = sfxL rows ++ ((sfxA ++ sfxCC ++ sfxB rows) ++ (sfxF ++ (scrDMiddle ++ (sfxL rows ++ sfxZ)))) ∧
    portSuffixCode rows = (sfxA ++ sfxDp rows ++ sfxB rows) ++ (sfxF ++
      ((sfxL' rows ++ (scrDMiddle ++ sfxL' rows)) ++ sfxZ)) := by
  constructor
  · simp only [portSuffixCodeD, scrDCorners, sfxL, sfxA, sfxCC, sfxB, sfxF, sfxZ, List.append_assoc]
  · simp only [portSuffixCode, scrCorners, scrOutCompare, scrDMiddle, sfxL', sfxA, sfxDp, sfxB, sfxF, sfxZ,
      List.append_assoc]

theorem suffixD_member (rows : Nat → Fin 32768) (i : WInstr 32768) (h : i ∈ portSuffixCodeD rows) :
    i = WInstr.lookup none (scrDPorts rows) ∨
    i = WInstr.literal (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) ∨ i ∈ portSuffixCode rows := by
  have hs := suffixD_split rows
  rw [hs.1] at h
  rw [hs.2]
  simp only [List.mem_append] at h ⊢
  rcases h with h | (((h | h) | h) | h | h | h | h)
  · exact Or.inl (List.mem_singleton.mp h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl h))))
  · exact Or.inr (Or.inl (List.mem_singleton.mp h))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h))))))
  · exact Or.inl (List.mem_singleton.mp h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem suffixD_counts (rows : Nat → Fin 32768) :
    literalToffolis (portSuffixCodeD rows) = literalToffolis (portSuffixCode rows) + 513 ∧
    literalRecords (portSuffixCodeD rows) = literalRecords (portSuffixCode rows) ∧
    traversals (portSuffixCodeD rows) + 1 = traversals (portSuffixCode rows) ∧
    literalSlotSum (portSuffixCodeD rows) = literalSlotSum (portSuffixCode rows) + 513 ∧
    portTotal (portSuffixCodeD rows) + 3 = portTotal (portSuffixCode rows) ∧
    literalToffolis (normalizeW (portSuffixCodeD rows)) ≤ literalToffolis (normalizeW (portSuffixCode rows)) + 513 := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  have hdw : scrDWires.length = 513 := by simp [scrDWires, scrShortWires_length, scrDExtraWires_length]
  have hdt : scrDTargets.length = 513 := by simp [scrDTargets, hx, hy]
  have hcc : ECDSAAdd.toffoliCount (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) = 513 := by
    rw [ccxList_toffoli, hdw, hdt]; rfl
  have hcs : ECDSAAdd.Challenge.gateSlots (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) = 513 := by
    rw [ccxList_slots, hdw, hdt]; rfl
  have hpl : (scrPorts rows).length = 516 := by
    simp only [scrPorts, List.length_append, retarget_length _ _ ((scrPairBits_length _ _).trans scrPairWires_length.symm),
      retarget_length _ _ ((scrShortBits_length _).trans scrShortWires_length.symm), scrPairWires_length, scrShortWires_length]
  have hdl : (scrDPorts rows).length = 771 := by
    simp only [scrDPorts, List.length_append, hpl,
      retarget_length _ _ ((scrDExtraBits_length _).trans scrDExtraWires_length.symm), scrDExtraWires_length]
  have hdpl : (scrDPointPorts rows).length = 513 := by simp [scrDPointPorts, hx, hy]
  have eDp : sfxDp rows = [.lookup (some streamLayout.core.equalNegY) (scrDPointPorts rows)] := rfl
  have t1 : literalToffolis (sfxCC) = 513 := by simp [sfxCC, wLiteral, literalToffolis, hcc]
  have t2 : literalRecords (sfxCC) = 0 := by simp [sfxCC, wLiteral, literalRecords, ccxList_records]
  have t3 : traversals (sfxCC) = 0 := rfl
  have t4 : literalSlotSum (sfxCC) = 513 := by simp [sfxCC, wLiteral, literalSlotSum, hcs]
  have t5 : portTotal (sfxCC) = 0 := rfl
  have l1 : literalToffolis (sfxL rows) = 0 := rfl
  have l2 : literalRecords (sfxL rows) = 0 := rfl
  have l3 : traversals (sfxL rows) = 1 := rfl
  have l4 : literalSlotSum (sfxL rows) = 0 := rfl
  have l5 : portTotal (sfxL rows) = 771 := by simp [sfxL, portTotal, hdl]
  have m1 : literalToffolis (sfxL' rows) = 0 := rfl
  have m2 : literalRecords (sfxL' rows) = 0 := rfl
  have m3 : traversals (sfxL' rows) = 1 := rfl
  have m4 : literalSlotSum (sfxL' rows) = 0 := rfl
  have m5 : portTotal (sfxL' rows) = 516 := by simp [sfxL', portTotal, hpl]
  have d1 : literalToffolis (sfxDp rows) = 0 := by rw [eDp]; rfl
  have d2 : literalRecords (sfxDp rows) = 0 := by rw [eDp]; rfl
  have d3 : traversals (sfxDp rows) = 1 := by rw [eDp]; rfl
  have d4 : literalSlotSum (sfxDp rows) = 0 := by rw [eDp]; rfl
  have d5 : portTotal (sfxDp rows) = 513 := by rw [eDp]; simp [portTotal, hdpl]
  have n1 : literalToffolis (normalizeW (sfxL rows)) = 0 := rfl
  have n2 : literalToffolis (normalizeW (sfxL' rows)) = 0 := rfl
  have n3 : literalToffolis (normalizeW (sfxDp rows)) = 0 := by rw [eDp]; rfl
  have n4 := literalToffolis_normalize sfxCC
  have hs := suffixD_split rows
  rw [hs.1, hs.2]
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', portLit_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem portRow3_member (rows : Nat → Fin 32768) (i : WInstr 32768) (hi : i ∈ portRowCode3 rows) :
    i = WInstr.lookup none (scrDPorts rows) ∨
    i = WInstr.literal (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) ∨ i ∈ portRowCode2 rows := by
  have hs := portRow3_shape rows
  dsimp only at hs
  rw [hs.1] at hi
  rw [hs.2]
  simp only [List.mem_append] at hi ⊢
  rcases hi with (hi | (hi | hi)) | hi
  · tauto
  · tauto
  · rcases suffixD_member rows i hi with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · tauto
  · tauto

theorem portRow3_measures (rows : Nat → Fin 32768) :
    literalToffolis (portRowCode3 rows) = literalToffolis (portRowCode2 rows) + 513 ∧
    literalRecords (portRowCode3 rows) = literalRecords (portRowCode2 rows) ∧
    traversals (portRowCode3 rows) + 1 = traversals (portRowCode2 rows) ∧
    literalSlotSum (portRowCode3 rows) = literalSlotSum (portRowCode2 rows) + 513 ∧
    portTotal (portRowCode3 rows) + 3 = portTotal (portRowCode2 rows) ∧
    literalToffolis (normalizeW (portRowCode3 rows)) ≤ literalToffolis (normalizeW (portRowCode2 rows)) + 513 := by
  have hs := portRow3_shape rows
  dsimp only at hs
  rw [hs.1, hs.2]
  have c := suffixD_counts rows
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', portLit_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem scrDWires_pool (a : Wire) (ha : a ∈ scrDWires) : a ∈ streamLayout.dialogPool :=
  scrAll_pool a (by
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h)

theorem scrCcx_facts :
    ECDSAAdd.wires (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) ⊆ streamLayout.dialogUsedWires.toFinset ∧
      GatePhysical (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) ∧
      ECDSAAdd.wires (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) ⊆ sourceSupport.toFinset := by
  have hd : ∀ a ∈ scrDWires, a ∉ scrDTargets := fun a ha => scrAll_d_targets a (by
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h)
  have hcS : streamLayout.core.equalNegY ∉ scrDWires := fun h => scrD_eqNegY.1 (by
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h)
  have hTf : scrDTargets.all (fun w => decide (fixedPort w ∨ oldWork w)) = true := by decide +kernel
  have hE : (fixedPort streamLayout.core.equalNegY ∨ oldWork streamLayout.core.equalNegY) ∧
      streamLayout.core.equalNegY ∈ streamLayout.dialogUsedWires := by decide +kernel
  have hTu (q : Wire) (h : q ∈ scrDTargets) : q ∈ streamLayout.dialogUsedWires :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  have hW : scrDWires.all (fun w => decide (fixedPort w ∨ oldWork w)) = true := by
    rw [scrDWires_eq]; decide +kernel
  have key (q : Wire) (hq : q ∈ ECDSAAdd.wires (ccxList streamLayout.core.equalNegY scrDWires scrDTargets)) :
      (fixedPort q ∨ oldWork q) ∧ q ∈ streamLayout.dialogUsedWires := by
    rcases ccxList_wires _ _ _ q hq with h | h | h
    · subst h; exact hE
    · refine ⟨by simpa using List.all_eq_true.mp hW q h, ?_⟩
      exact List.mem_append_right _ (scrDWires_pool q h)
    · exact ⟨by simpa using List.all_eq_true.mp hTf q h, hTu q h⟩
  refine ⟨?_, ccxList_physical _ _ _ hd hcS scrD_eqNegY.2, ?_⟩
  · intro q hq
    exact List.mem_toFinset.mpr (key q hq).2
  · intro q hq
    exact List.mem_toFinset.mpr ((sourceSupport_mem q).mpr (key q hq).1)

theorem scrDPorts_geometry (rows : Nat → Fin 32768) :
    lookupPlacedOK windowBits windowPaths windowRoot (.lookup none (scrDPorts rows)) = true := by
  change geometryOK windowBits windowPaths windowRoot none (portTargets (scrDPorts rows)) = true
  rw [scrDPorts_targets]
  unfold geometryOK
  have h1 : decide (lookupRoot windowRoot none :: windowBits ++ windowPaths).Nodup = true := by decide +kernel
  have h2 : decide scrAllWires.Nodup = true := decide_eq_true scrAllWires_nodup
  have hlow : ((windowRoot :: lookupRoot windowRoot none :: windowBits ++ windowPaths).all
      fun w => decide (w < 14373)) = true := by decide +kernel
  have h3 : ((windowRoot :: lookupRoot windowRoot none :: windowBits ++ windowPaths).all
      fun w => !scrAllWires.contains w) = true := by
    apply List.all_eq_true.mpr
    intro w hw
    have hb : w < 14373 := of_decide_eq_true (List.all_eq_true.mp hlow w hw)
    have hn : w ∉ scrAllWires := fun hm => by have := (scrAll_bounds w hm).1; dsimp only [Wire] at *; omega
    simp [hn]
  rw [h1, h2, h3]
  rfl

theorem scrDPorts_sourceOK (rows : Nat → Fin 32768) :
    sourceLookupOK (.lookup none (scrDPorts rows)) = true := by
  simp only [sourceLookupOK, Option.toList_none, List.all_nil, Bool.true_and, scrDPorts_targets, scrAll_eq]
  decide +kernel

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

theorem portRow3_run_same (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (s : BasisState) (hs : liveReady s) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (portRowCode3 probeRows)) a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ =
      ECDSAAdd.run ((specialize (normalizeW (rowAddCode probeRows)) a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ := by
  rw [specialize_normalize_run, specialize_normalize_run]
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P,hP⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P) true (fun _=>false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P) (StreamPoint.of_coordinates s P hs.1.1.1.1 hP),?_,?_,?_⟩
    · simpa [streamLayout_control,flipInfinity,ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  cases he : Bridge.toB C with
  | zero =>
    have hzero : C = 0 := congrArg ECDSAAdd.ShorPort.toA he
    exact (hC hzero).elim
  | @some cx cy hc =>
    have ce : C = toA (.some hc) := congrArg toA he
    have hr : RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
      readConstant_rowReads coeffs Q _ _ ce
    have ho : ShorECDLP.order • (.some hc : Point) = 0 := by rw [← he]; exact hord
    have hp2 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 2
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hp3 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 3
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hd : (.some hc : Point)+.some hc ≠ 0 := by simpa only [two_nsmul] using hp2
    have ht : (.some hc : Point)+.some hc+.some hc ≠ 0 := by
      simpa only [show (3 : Nat) = 2+1 from rfl,succ_nsmul,two_nsmul] using hp3
    have en := enables_true hc hd ht
    have hdo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0 := by rw [nsmul_add,ho,zero_add]
    exact portRow3_run_eq (readConstant coeffs Q) probeRows a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial m

theorem portRow3_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ portRowCode3 rows, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  rcases portRow3_member rows i hi with rfl | rfl | h
  · exact placed_implies_pair _ _ _ _ ((lookupPlacedOK_iff _ _ _ _).mp (scrDPorts_geometry rows))
  · intro w hw hq
    exact window_reserved_outside_used w hw (List.mem_toFinset.mp (scrCcx_facts.1 hq))
  · exact portRow2_placed rows i h

theorem portRow3_physical (rows : Nat → Fin 32768) :
    ∀ p, WInstr.literal p ∈ portRowCode3 rows → GatePhysical p := by
  intro p hp
  rcases portRow3_member rows _ hp with he | he | h
  · cases he
  · cases he; exact scrCcx_facts.2.1
  · exact portRow2_physical rows p h

theorem portRow3_literal_source (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ portRowCode3 probeRows) :
    ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  rcases portRow3_member probeRows _ hp with he | he | h
  · cases he
  · cases he; exact scrCcx_facts.2.2
  · exact portRow2_literal_source p h

theorem port3_nat_sub (a b : Nat) (h : a + 1 = b) (hb : b = 17) : a = 16 := by omega

theorem portRow3_traversals' (rows : Nat → Fin 32768) : traversals (portRowCode3 rows) = 16 :=
  port3_nat_sub _ _ (portRow3_measures rows).2.2.1 (portRow2_traversals' rows)

theorem portRow3_traversals : traversals (normalizeW (portRowCode3 probeRows)) = 16 := by
  rw [traversals_normalize]
  exact portRow3_traversals' probeRows

theorem portRow3_literalRecords (rows : Nat → Fin 32768) : literalRecords (portRowCode3 rows) = 1556899 :=
  (portRow3_measures rows).2.1.trans (portRow2_literalRecords rows)

theorem port3_records_arith (a b k : Nat) (ha : a = 1556899) (hb : b = 16) (l : Nat) (hl : l = k) :
    a + b * (2 ^ l - 1) = 1556899 + 16 * (2 ^ k - 1) := by
  subst ha hb hl
  rfl

theorem port3_records15 (a b l : Nat) (ha : a = 1556899) (hb : b = 16) (hl : l = 15) :
    a + b * (2 ^ l - 1) = 2081171 := by
  subst ha hb hl
  rfl

theorem portRow3_records : codeRecords windowBits windowPaths windowRoot
    (normalizeW (portRowCode3 probeRows)) = 2081171 := by
  have layouts := pair_layouts_of_placed windowBits windowPaths windowRoot _
    (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ (portRow3_placed probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact port3_records15 _ _ _ (portRow3_literalRecords _) (portRow3_traversals' _) (by simp [windowBits])

theorem portRow3_sourceLookupOK : (normalizeW (portRowCode3 probeRows)).all sourceLookupOK = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  cases i with
  | literal p => rfl
  | lookup c ports =>
    rcases portRow3_member probeRows _ hi with he | he | h
    · cases he
      exact scrDPorts_sourceOK probeRows
    · cases he
    · exact List.all_eq_true.mp portRow2_sourceLookupOK _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem port3_nat_slots (a b : Nat) (h : a = b + 513) (hb : b ≤ 50002070) : a ≤ 50002583 := by omega

theorem portRow3_literal_slots_bound : literalSlotSum (portRowCode3 probeRows) ≤ 50002583 :=
  port3_nat_slots _ _ (portRow3_measures probeRows).2.2.2.1 portRow2_literal_slots_bound

theorem portRow3_portTotal : portTotal (portRowCode3 probeRows) ≤ 20000 := by
  have h := (portRow3_measures probeRows).2.2.2.2.1
  have h2 := portRow2_portTotal
  omega

theorem port3_nat_count (a b b' t : Nat) (h : a + b + 17 * t ≤ 2163901 + 17 * t) (hb : b' ≤ b + 513) :
    a + b' + 16 * t ≤ 2164414 + 16 * t := by omega

theorem portRow3_count_upper (k : Nat) :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (portRowCode3 probeRows)) + 16 * (2^k-1) ≤
      2164414 + 16 * (2^k-1) :=
  port3_nat_count _ _ _ _ (portRow2_count_upper k) (portRow3_measures probeRows).2.2.2.2.2

theorem portRow3_width_placed (k : Nat) (hk : k ≤ 15) (rows : Nat → Fin 32768) :
    ∀ i ∈ portRowCode3 rows, PlacedPair (widthBits k) windowPaths windowRoot i := by
  intro i hi
  have hp := portRow3_placed rows i hi
  cases i with
  | literal p =>
    intro w hw
    exact hp w ((List.Sublist.cons₂ windowRoot (width_sublist k hk)).subset hw)
  | lookup c ports =>
    refine ⟨(List.Sublist.cons₂ _ (width_sublist k hk)).nodup hp.1, hp.2.1, hp.2.2.1, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw ht
    exact List.disjoint_left.mp hp.2.2.2
      ((List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (width_sublist k hk))).subset hw) ht

theorem portRow3_width_records (k : Nat) (hk : k ≤ 15) :
    codeRecords (widthBits k) windowPaths windowRoot (normalizeW (portRowCode3 probeRows)) =
      1556899 + 16 * (2 ^ k - 1) := by
  have layouts := pair_layouts_of_placed (widthBits k) windowPaths windowRoot _
    (by simpa [widthBits,windowPaths] using hk) (pair_placed_normalize _ _ _ _ (portRow3_width_placed k hk probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact port3_records_arith _ _ _ (portRow3_literalRecords _) (portRow3_traversals' _) _ (by simp [widthBits])

end
end ShorECDLP.Entrant.WEX


/-! ### Measured clears of the entry/output scratch words

The scratch words hold loaded table bits at their unload, exactly like the constant source register at
the end of a masked constant addition, so the unload can be replaced by the same measured clear.  The
clear is rooted at the window root (true throughout a row) and recycles 128 scratch wires (pool positions
259..386) as its one-hot bank. -/
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def scrSiteHot (i : Fin 128) : Wire := 14374 + i.val

theorem scrWires_eq : WEX.scrWires =
    (14373 :: List.range' 14374 256 ++ [14883]) ++ (14884 :: List.range' 14885 256 ++ [15141]) := by
  simp only [WEX.scrWires, WEX.scrPairWires, WEX.scrShortWires,
    WEX.map_poolWire _ _ (by norm_num : 259 + 256 ≤ 5699), WEX.map_poolWire _ _ (by norm_num : 770 + 256 ≤ 5699),
    WEX.poolWire_eq _ (by norm_num : 258 < 5699), WEX.poolWire_eq _ (by norm_num : 768 < 5699),
    WEX.poolWire_eq _ (by norm_num : 769 < 5699), WEX.poolWire_eq _ (by norm_num : 1026 < 5699)]

theorem scrWires_bounds : ∀ a ∈ WEX.scrWires, 14373 ≤ a ∧ a < 15142 := by
  rw [scrWires_eq]
  intro a ha
  simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.not_mem_nil,
    or_false] at ha
  dsimp only [Wire] at *
  omega

theorem scrSiteHot_mem (i : Fin 128) : scrSiteHot i ∈ WEX.scrWires := by
  rw [scrWires_eq]
  have hi := i.isLt
  apply List.mem_append_left
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  simp only [scrSiteHot, List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem scrWires_head : (WEX.scrWires).headD 0 = 14373 := by
  rw [scrWires_eq]
  rfl

end
end ShorECDLP.Entrant.WEXUnlookup

/-! ### Entry comparisons as a measured-clear site

The scratch-hosted entry comparisons are re-expressed as a masked site: load the scratch words under
the window root, run the comparison literals as one program, and unload under the window root.  The
row-level block compiler then replaces the unload by a measured clear. -/
namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The literal programs of a code, concatenated. -/
def litConcat {n : Nat} : WCode n → Program
  | [] => []
  | .literal p :: code => p ++ litConcat code
  | .lookup _ _ :: code => litConcat code

def LitOnly {n : Nat} (code : WCode n) : Prop := ∀ i ∈ code, ∃ p, i = .literal p

theorem litOnly_append {n : Nat} {a b : WCode n} (ha : LitOnly a) (hb : LitOnly b) : LitOnly (a ++ b) := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact ha i h
  · exact hb i h

theorem litOnly_wLiteral {n : Nat} (p : Program) : LitOnly (wLiteral (n := n) p) := by
  intro i hi
  exact ⟨p, List.mem_singleton.mp hi⟩

theorem litOnly_zeroWith {n : Nat} (tail : Wire → WCode n) (htail : ∀ w, LitOnly (tail w)) :
    ∀ (c : Wire) (bs : List ZeroBit), LitOnly (wZeroWith tail c bs) := by
  intro c bs
  induction bs generalizing c with
  | nil => exact htail c
  | cons b bs ih =>
    exact litOnly_append (litOnly_append (litOnly_wLiteral _) (ih _)) (litOnly_wLiteral _)

theorem litOnly_inst {n : Nat} (code : WCode n) (h : LitOnly code) (a : Nat) (read : ConstantBit n → Bool) :
    (specialize code a).instantiate read = litConcat code := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    obtain ⟨p, rfl⟩ := h i List.mem_cons_self
    have e : specialize (WInstr.literal p :: code) a = Tmpl.lit p ++ specialize code a := by
      simp [specialize, WInstr.specialize]
    rw [e, Tmpl.instantiate_append, Tmpl.instantiate_lit, ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    rfl

theorem litConcat_toffoli {n : Nat} (code : WCode n) :
    ECDSAAdd.toffoliCount (litConcat code) = literalToffolis code := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    cases i with
    | literal p => simp [litConcat, literalToffolis, ECDSAAdd.toffoliCount_append, ih]
    | lookup c ps => simpa [litConcat, literalToffolis] using ih

theorem litConcat_records {n : Nat} (code : WCode n) :
    ECDSAAdd.measurementCount (litConcat code) = literalRecords code := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    cases i with
    | literal p => simp [litConcat, literalRecords, ECDSAAdd.measurementCount_append, ih]
    | lookup c ps => simpa [litConcat, literalRecords] using ih

theorem litConcat_slots {n : Nat} (code : WCode n) :
    ECDSAAdd.Challenge.gateSlots (litConcat code) = literalSlotSum code := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    cases i with
    | literal p => simp [litConcat, literalSlotSum, ECDSAAdd.Challenge.gateSlots_append, ih]
    | lookup c ps => simpa [litConcat, literalSlotSum] using ih

theorem litConcat_wires {n : Nat} (code : WCode n) (q : Wire) (h : q ∈ ECDSAAdd.wires (litConcat code)) :
    ∃ p, WInstr.literal p ∈ code ∧ q ∈ ECDSAAdd.wires p := by
  induction code with
  | nil => simp [litConcat, ECDSAAdd.wires] at h
  | cons i code ih =>
    cases i with
    | literal p =>
      simp only [litConcat, ECDSAAdd.wires_append, Finset.mem_union] at h
      rcases h with h | h
      · exact ⟨p, List.mem_cons_self, h⟩
      · obtain ⟨p', hp', hq⟩ := ih h
        exact ⟨p', List.mem_cons_of_mem _ hp', hq⟩
    | lookup c ps =>
      obtain ⟨p', hp', hq⟩ := ih (by simpa [litConcat] using h)
      exact ⟨p', List.mem_cons_of_mem _ hp', hq⟩

theorem litConcat_physical {n : Nat} (code : WCode n) (h : ∀ p, WInstr.literal p ∈ code → GatePhysical p) :
    GatePhysical (litConcat code) := by
  induction code with
  | nil => intro i hi; simp [litConcat] at hi
  | cons i code ih =>
    have ih' := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    cases i with
    | literal p =>
      simp only [litConcat, gatePhysical_append]
      exact ⟨h p List.mem_cons_self, ih'⟩
    | lookup c ps => simpa [litConcat] using ih'

/-- The literal middle of the scratch-hosted entry comparisons. -/
def scrInMid : WCode 32768 :=
  wLiteral (cxList scrPairWires scrPairTargets) ++
  wZeroWith (wPairTailBare (yLow streamLayout) streamLayout.doubleSelect streamLayout.genericSelect)
    streamLayout.control (pairPorts streamLayout) ++
  wLiteral (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
  wLiteral (cxList scrShortWires scrShortTargets) ++
  wLiteral scrInP2 ++
  wLiteral (cxList scrShortWires scrShortTargets)

theorem scrInMid_litOnly : LitOnly scrInMid := by
  have hz := litOnly_zeroWith (n := 32768)
    (wPairTailBare (yLow streamLayout) streamLayout.doubleSelect streamLayout.genericSelect)
    (fun w => litOnly_wLiteral _) streamLayout.control (pairPorts streamLayout)
  unfold scrInMid
  exact litOnly_append (litOnly_append (litOnly_append (litOnly_append (litOnly_append (litOnly_wLiteral _) hz)
    (litOnly_wLiteral _)) (litOnly_wLiteral _)) (litOnly_wLiteral _)) (litOnly_wLiteral _)

theorem scrInCompare_split (rows : Nat → Fin 32768) :
    scrInCompare rows = [.lookup none (scrInPorts rows)] ++ scrInMid ++ [.lookup none (scrInPorts rows)] := by
  simp only [scrInCompare, scrInMid, List.append_assoc]

def scrInArith : Program := litConcat scrInMid

def scrInSite (rows : Nat → Fin 32768) : WEXUnlookup.MaskedSite 32768 := ⟨windowRoot, scrInPorts rows, scrInArith⟩

def portPrefixCode4 (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
  wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect) ++
  (scrInSite rows).code ++ wLiteral (pointDialogGenericFlag streamLayout)

def portFinite4 (rows : Nat → Fin 32768) : WCode 32768 :=
  portPrefixCode4 rows ++ wGeneric streamLayout rows ++ portSuffixCodeD rows

def portRowCode4 (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ portFinite4 rows ++ wLiteral ([.X 838])

theorem scrInSite_code (rows : Nat → Fin 32768) :
    (scrInSite rows).code = [.lookup (some windowRoot) (scrInPorts rows)] ++ wLiteral scrInArith ++
      [.lookup (some windowRoot) (scrInPorts rows)] := rfl

theorem cBits_eq_xBits_run (c : Wire) (T : List Wire) (k m : List Bool) (s : State) (hc : c ∉ T)
    (hs : s.basis c = true) : run (cBits c T k) m s = run (xBits T k) m s := by
  rw [cBits_run c T k m s hc, xBits_run]
  simp [hs]

theorem cBits_keeps (c : Wire) (T : List Wire) (k m : List Bool) (s : State) (hc : c ∉ T) :
    (run (cBits c T k) m s).basis c = s.basis c := by
  rw [cBits_run c T k m s hc]
  simp [xMask_outside T k c hc]

theorem windowRoot_not_scr : windowRoot ∉ scrWires := by
  intro h
  have := (WEXUnlookup.scrWires_bounds windowRoot h).1
  revert this
  decide

/-- Every literal of the parent row avoids the window root. -/
theorem portRow3_literal_root (p : Program) (hp : WInstr.literal p ∈ portRowCode3 probeRows) :
    windowRoot ∉ ECDSAAdd.wires p := by
  have h := portRow3_placed probeRows _ hp
  exact h windowRoot List.mem_cons_self

theorem scrInMid_sub (p : Program) (hp : WInstr.literal p ∈ scrInMid) :
    WInstr.literal p ∈ portRowCode3 probeRows := by
  have e : portRowCode3 probeRows = wLiteral ([.X 838]) ++ (wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
      wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect) ++
      ([.lookup none (scrInPorts probeRows)] ++ scrInMid ++ [.lookup none (scrInPorts probeRows)]) ++
      wLiteral (pointDialogGenericFlag streamLayout) ++ wGeneric streamLayout probeRows ++ portSuffixCodeD probeRows) ++
      wLiteral ([.X 838]) := by
    simp only [portRowCode3, portFinite3, portPrefixCode, scrInCompare_split, List.append_assoc]
  rw [e]
  simp only [List.mem_append]
  tauto

theorem litConcat_avoid {n : Nat} (code : WCode n) (q : Wire)
    (h : ∀ p, WInstr.literal p ∈ code → q ∉ ECDSAAdd.wires p) : q ∉ ECDSAAdd.wires (litConcat code) := by
  intro hq
  obtain ⟨p, hp, hq'⟩ := litConcat_wires code q hq
  exact h p hp hq'

theorem scrInArith_root : windowRoot ∉ ECDSAAdd.wires scrInArith :=
  litConcat_avoid scrInMid windowRoot (fun p hp => portRow3_literal_root p (scrInMid_sub p hp))

theorem scrInHead_root : windowRoot ∉ ECDSAAdd.wires scrInHead := by
  intro h
  simp [scrInHead, zeroFlag, ECDSAAdd.wires, ECDSAAdd.Instr.wires, windowRoot] at h
  rcases h with h | h | h | h | h <;> revert h <;> decide

theorem cBits_sandwich_run (c : Wire) (S : List Wire) (k : List Bool) (M : Program) (m : List Bool) (t : State)
    (hc : c ∉ S) (hM : c ∉ ECDSAAdd.wires M) (ht : t.basis c = true) :
    run (cBits c S k ++ (M ++ cBits c S k)) m t = run (xBits S k ++ (M ++ xBits S k)) m t := by
  rw [run_append (cBits c S k), run_append (xBits S k), cBits_records, xBits_records,
    cBits_eq_xBits_run c S k _ t hc ht]
  have h1 : (run (xBits S k) (m.take 0) t).basis c = true := by
    rw [xBits_run]; simp [xMask_outside S k c hc, ht]
  generalize run (xBits S k) (m.take 0) t = t1 at h1
  rw [run_append M, run_append M]
  have h2 : (run M ((m.drop 0).take (measurementCount M)) t1).basis c = true := by
    rw [run_preserves_outside _ _ _ _ hM]; exact h1
  rw [cBits_eq_xBits_run c S k _ _ hc h2]

theorem portPrefix4_records (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) :
    measurementCount ((specialize (portPrefixCode4 rows) address).instantiate read) =
      measurementCount ((specialize (portPrefixCode rows) address).instantiate read) := by
  have hm := litOnly_inst scrInMid scrInMid_litOnly address read
  simp only [portPrefixCode4, portPrefixCode, scrInSite_code, scrInCompare_split, specialize_append,
    Tmpl.instantiate_append, scr_lookup_some_inst, scr_lookup_inst, specialize_literal, Tmpl.instantiate_lit,
    measurementCount_append, cBits_records, xBits_records, hm, scrInArith]

theorem portPrefix4_eq3 (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (m : List Bool) (s : State) (hr : s.basis windowRoot = true) :
    run ((specialize (portPrefixCode4 rows) address).instantiate read) m s =
      run ((specialize (portPrefixCode rows) address).instantiate read) m s := by
  have hm := litOnly_inst scrInMid scrInMid_litOnly address read
  let K := portBits read (scrInPorts rows) address
  have e4 : (specialize (portPrefixCode4 rows) address).instantiate read =
      scrInHead ++ (cBits windowRoot scrWires K ++ (scrInArith ++ cBits windowRoot scrWires K)) ++
        pointDialogGenericFlag streamLayout := by
    simp only [portPrefixCode4, scrInSite_code, specialize_append, Tmpl.instantiate_append, scr_lookup_some_inst,
      specialize_literal, Tmpl.instantiate_lit, scrInPorts_targets, scrInHead, K, List.append_assoc]
  have e3 : (specialize (portPrefixCode rows) address).instantiate read =
      scrInHead ++ (xBits scrWires K ++ (scrInArith ++ xBits scrWires K)) ++
        pointDialogGenericFlag streamLayout := by
    simp only [portPrefixCode, scrInCompare_split, specialize_append, Tmpl.instantiate_append, scr_lookup_inst,
      specialize_literal, Tmpl.instantiate_lit, scrInPorts_targets, scrInHead, K, hm, scrInArith, List.append_assoc]
  rw [e4, e3]
  apply portSuffix_middle _ _ _ _ (by simp [measurementCount_append, cBits_records, xBits_records]) s
  intro k n
  have ht : (run scrInHead k s).basis windowRoot = true := by
    rw [run_preserves_outside _ _ _ _ scrInHead_root]; exact hr
  exact cBits_sandwich_run windowRoot scrWires K scrInArith n _ windowRoot_not_scr scrInArith_root ht

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem litConcat_normalize {n : Nat} (code : WCode n) :
    litConcat (normalizeW code) = ECDSAAdd.Baselines.normalizeProgram (litConcat code) := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    cases i with
    | literal p =>
      simp only [normalizeW, List.map_cons, normalizeWInstr, litConcat] at ih ⊢
      rw [ih]
      simp [ECDSAAdd.Baselines.normalizeProgram, List.map_append]
    | lookup c ps => simpa [normalizeW, normalizeWInstr, litConcat] using ih

theorem portRow4_shape (rows : Nat → Fin 32768) :
    let A : WCode 32768 := wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
      wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
      wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect)
    let T : WCode 32768 := wLiteral (pointDialogGenericFlag streamLayout) ++ wGeneric streamLayout rows ++
      portSuffixCodeD rows
    let X : WCode 32768 := wLiteral ([.X 838])
    portRowCode4 rows = X ++ (A ++ ([.lookup (some windowRoot) (scrInPorts rows)] ++ wLiteral scrInArith ++
      [.lookup (some windowRoot) (scrInPorts rows)]) ++ T) ++ X ∧
    portRowCode3 rows = X ++ (A ++ ([.lookup none (scrInPorts rows)] ++ scrInMid ++
      [.lookup none (scrInPorts rows)]) ++ T) ++ X := by
  dsimp only
  constructor
  · simp only [portRowCode4, portFinite4, portPrefixCode4, scrInSite_code, List.append_assoc]
  · simp only [portRowCode3, portFinite3, portPrefixCode, scrInCompare_split, List.append_assoc]

theorem portRow4_member (rows : Nat → Fin 32768) (i : WInstr 32768) (hi : i ∈ portRowCode4 rows) :
    i = WInstr.lookup (some windowRoot) (scrInPorts rows) ∨ i = WInstr.literal scrInArith ∨
      i ∈ portRowCode3 rows := by
  have hs := portRow4_shape rows
  dsimp only at hs
  rw [hs.1] at hi
  rw [hs.2]
  simp only [List.mem_append] at hi ⊢
  rcases hi with (hi | ((hi | ((hi | hi) | hi)) | hi)) | hi
  · tauto
  · tauto
  · exact Or.inl (List.mem_singleton.mp hi)
  · exact Or.inr (Or.inl (List.mem_singleton.mp hi))
  · exact Or.inl (List.mem_singleton.mp hi)
  · tauto
  · tauto

theorem portRow4_measures (rows : Nat → Fin 32768) :
    literalToffolis (portRowCode4 rows) = literalToffolis (portRowCode3 rows) ∧
    literalRecords (portRowCode4 rows) = literalRecords (portRowCode3 rows) ∧
    traversals (portRowCode4 rows) = traversals (portRowCode3 rows) ∧
    literalSlotSum (portRowCode4 rows) = literalSlotSum (portRowCode3 rows) ∧
    portTotal (portRowCode4 rows) = portTotal (portRowCode3 rows) ∧
    literalToffolis (normalizeW (portRowCode4 rows)) = literalToffolis (normalizeW (portRowCode3 rows)) := by
  have hs := portRow4_shape rows
  dsimp only at hs
  rw [hs.1, hs.2]
  have t1 : literalToffolis (wLiteral (n := 32768) scrInArith) = literalToffolis scrInMid := by
    simp [wLiteral, literalToffolis, scrInArith, litConcat_toffoli]
  have t2 : literalRecords (wLiteral (n := 32768) scrInArith) = literalRecords scrInMid := by
    simp [wLiteral, literalRecords, scrInArith, litConcat_records]
  have t3 : literalSlotSum (wLiteral (n := 32768) scrInArith) = literalSlotSum scrInMid := by
    simp [wLiteral, literalSlotSum, scrInArith, litConcat_slots]
  have t4 : traversals (wLiteral (n := 32768) scrInArith) = traversals scrInMid := by
    have h0 : ∀ (code : WCode 32768), LitOnly code → traversals code = 0 := by
      intro code hc
      induction code with
      | nil => rfl
      | cons i code ih =>
        obtain ⟨p, rfl⟩ := hc i List.mem_cons_self
        simpa [traversals] using ih (fun j hj => hc j (List.mem_cons_of_mem _ hj))
    rw [h0 _ (litOnly_wLiteral _), h0 _ scrInMid_litOnly]
  have t5 : portTotal (wLiteral (n := 32768) scrInArith) = portTotal scrInMid := by
    have h0 : ∀ (code : WCode 32768), LitOnly code → portTotal code = 0 := by
      intro code hc
      induction code with
      | nil => rfl
      | cons i code ih =>
        obtain ⟨p, rfl⟩ := hc i List.mem_cons_self
        simpa [portTotal] using ih (fun j hj => hc j (List.mem_cons_of_mem _ hj))
    rw [h0 _ (litOnly_wLiteral _), h0 _ scrInMid_litOnly]
  have t6 : literalToffolis (normalizeW (wLiteral (n := 32768) scrInArith)) = literalToffolis (normalizeW scrInMid) := by
    have e : normalizeW (wLiteral (n := 32768) scrInArith) =
        wLiteral (ECDSAAdd.Baselines.normalizeProgram scrInArith) := rfl
    rw [e, scrInArith, ← litConcat_normalize]
    simp [wLiteral, literalToffolis, litConcat_toffoli]
  have l1 : literalToffolis ([.lookup (some windowRoot) (scrInPorts rows)] : WCode 32768) =
      literalToffolis ([.lookup none (scrInPorts rows)] : WCode 32768) := rfl
  have l2 : portTotal ([.lookup (some windowRoot) (scrInPorts rows)] : WCode 32768) =
      portTotal ([.lookup none (scrInPorts rows)] : WCode 32768) := rfl
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', portLit_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [t1]; rfl
  · rw [t2]; rfl
  · rw [t4]; rfl
  · rw [t3]; rfl
  · rw [t5]; rfl
  · rw [t6]; rfl

theorem portRow4_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ portRowCode4 probeRows, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  rcases portRow4_member probeRows i hi with rfl | rfl | h
  · exact placed_implies_pair _ _ _ _ ((lookupPlacedOK_iff _ _ _ _).mp (scrInPorts_geometry probeRows))
  · intro w hw
    exact litConcat_avoid scrInMid w (fun p hp => portRow3_placed probeRows _ (scrInMid_sub p hp) w hw)
  · exact portRow3_placed probeRows i h

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem litConcat_subset {n : Nat} (code : WCode n) (S : Finset ECDSAAdd.Wire)
    (h : ∀ p, WInstr.literal p ∈ code → ECDSAAdd.wires p ⊆ S) : ECDSAAdd.wires (litConcat code) ⊆ S := by
  intro q hq
  obtain ⟨p, hp, hq'⟩ := litConcat_wires code q hq
  exact h p hp hq'

theorem scrInArith_physical : GatePhysical scrInArith :=
  litConcat_physical scrInMid (fun p hp => portRow3_physical probeRows p (scrInMid_sub p hp))

theorem scrInArith_source : ECDSAAdd.wires scrInArith ⊆ sourceSupport.toFinset :=
  litConcat_subset scrInMid _ (fun p hp => portRow3_literal_source p (scrInMid_sub p hp))

theorem portRow4_physical : ∀ p, WInstr.literal p ∈ portRowCode4 probeRows → GatePhysical p := by
  intro p hp
  rcases portRow4_member probeRows _ hp with he | he | h
  · cases he
  · cases he; exact scrInArith_physical
  · exact portRow3_physical probeRows p h

theorem portRow4_literal_source (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ portRowCode4 probeRows) :
    ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  rcases portRow4_member probeRows _ hp with he | he | h
  · cases he
  · cases he; exact scrInArith_source
  · exact portRow3_literal_source p h

theorem portRow4_traversals' : traversals (portRowCode4 probeRows) = 16 :=
  (portRow4_measures probeRows).2.2.1.trans (portRow3_traversals' probeRows)

theorem portRow4_traversals : traversals (normalizeW (portRowCode4 probeRows)) = 16 := by
  rw [traversals_normalize]; exact portRow4_traversals'

theorem portRow4_literalRecords : literalRecords (portRowCode4 probeRows) = 1556899 :=
  (portRow4_measures probeRows).2.1.trans (portRow3_literalRecords probeRows)

theorem portRow4_records : codeRecords windowBits windowPaths windowRoot
    (normalizeW (portRowCode4 probeRows)) = 2081171 := by
  have layouts := pair_layouts_of_placed windowBits windowPaths windowRoot _
    (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ (portRow4_placed probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact port3_records15 _ _ _ portRow4_literalRecords portRow4_traversals' (by simp [windowBits])

theorem portRow4_sourceLookupOK : (normalizeW (portRowCode4 probeRows)).all sourceLookupOK = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  cases i with
  | literal p => rfl
  | lookup c ports =>
    rcases portRow4_member probeRows _ hi with he | he | h
    · cases he
      have h1 := scrInPorts_sourceOK probeRows
      simp only [sourceLookupOK, Option.toList_none, List.all_nil, Bool.true_and] at h1
      simp only [normalizeWInstr, sourceLookupOK, Option.toList_some, List.all_cons, List.all_nil, Bool.and_true, h1]
      decide
    · cases he
    · exact List.all_eq_true.mp portRow3_sourceLookupOK _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem portRow4_literal_slots_bound : literalSlotSum (portRowCode4 probeRows) ≤ 50002583 := by
  rw [(portRow4_measures probeRows).2.2.2.1]; exact portRow3_literal_slots_bound

theorem portRow4_portTotal : portTotal (portRowCode4 probeRows) ≤ 20000 := by
  rw [(portRow4_measures probeRows).2.2.2.2.1]; exact portRow3_portTotal

theorem portRow4_count_upper (k : Nat) :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (portRowCode4 probeRows)) + 16 * (2^k-1) ≤
      2164414 + 16 * (2^k-1) := by
  rw [(portRow4_measures probeRows).2.2.2.2.2]; exact portRow3_count_upper k

theorem portRow4_width_placed (k : Nat) (hk : k ≤ 15) :
    ∀ i ∈ portRowCode4 probeRows, PlacedPair (widthBits k) windowPaths windowRoot i := by
  intro i hi
  have hp := portRow4_placed probeRows i hi
  cases i with
  | literal p =>
    intro w hw
    exact hp w ((List.Sublist.cons₂ windowRoot (width_sublist k hk)).subset hw)
  | lookup c ports =>
    refine ⟨(List.Sublist.cons₂ _ (width_sublist k hk)).nodup hp.1, hp.2.1, hp.2.2.1, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw ht
    exact List.disjoint_left.mp hp.2.2.2
      ((List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (width_sublist k hk))).subset hw) ht

theorem portRow4_width_records (k : Nat) (hk : k ≤ 15) :
    codeRecords (widthBits k) windowPaths windowRoot (normalizeW (portRowCode4 probeRows)) =
      1556899 + 16 * (2 ^ k - 1) := by
  have layouts := pair_layouts_of_placed (widthBits k) windowPaths windowRoot _
    (by simpa [widthBits,windowPaths] using hk) (pair_placed_normalize _ _ _ _ (portRow4_width_placed k hk))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact port3_records_arith _ _ _ portRow4_literalRecords portRow4_traversals' _ (by simp [widthBits])

theorem portRow4_run_eq (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (s : BasisState) (hr : s windowRoot = true) (m : List Bool) :
    ECDSAAdd.run ((specialize (portRowCode4 rows) address).instantiate read) m ⟨false,s⟩ =
      ECDSAAdd.run ((specialize (portRowCode3 rows) address).instantiate read) m ⟨false,s⟩ := by
  let P' := (specialize (portPrefixCode4 rows) address).instantiate read
  let P := (specialize (portPrefixCode rows) address).instantiate read
  let R := (specialize (wGeneric streamLayout rows) address).instantiate read ++
    (specialize (portSuffixCodeD rows) address).instantiate read ++ ([.X 838] : ECDSAAdd.Program)
  have e1 : (specialize (portRowCode4 rows) address).instantiate read = ([.X 838] : ECDSAAdd.Program) ++ P' ++ R := by
    simp only [portRowCode4, portFinite4, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, P', R, List.append_assoc]
  have e2 : (specialize (portRowCode3 rows) address).instantiate read = ([.X 838] : ECDSAAdd.Program) ++ P ++ R := by
    simp only [portRowCode3, portFinite3, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, P, R, List.append_assoc]
  rw [e1, e2]
  apply portSuffix_middle _ _ _ _ (portPrefix4_records read rows address) ⟨false,s⟩
  intro k n
  rw [flip_run]
  apply portPrefix4_eq3 read rows address n
  change flipInfinity s windowRoot = true
  simpa [flipInfinity, ECDSAAdd.writeBit, Function.update, windowRoot] using hr

theorem portRow4_run_same (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (s : BasisState) (hs : liveReady s) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (portRowCode4 probeRows)) a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ =
      ECDSAAdd.run ((specialize (normalizeW (rowAddCode probeRows)) a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ := by
  have h3 := portRow3_run_same a coeffs Q hQ hn s hs m
  rw [specialize_normalize_run, specialize_normalize_run] at h3 ⊢
  exact (portRow4_run_eq (readConstant coeffs Q) probeRows a s hs.2.2 m).trans h3

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-- With the window root set and clean scratch, the scratch site returns its words clean. -/
theorem scrInSite_clean (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) (m : List Bool)
    (t : State) (hr : t.basis windowRoot = true) (hs : ∀ w ∈ scrWires, t.basis w = false) :
    ∀ w ∈ scrWires, (run ((specialize (scrInSite rows).code a).instantiate read) m t).basis w = false := by
  have hm := litOnly_inst scrInMid scrInMid_litOnly a read
  let K := portBits read (scrInPorts rows) a
  have e4 : (specialize (scrInSite rows).code a).instantiate read =
      cBits windowRoot scrWires K ++ (scrInArith ++ cBits windowRoot scrWires K) := by
    simp only [scrInSite_code, specialize_append, Tmpl.instantiate_append, scr_lookup_some_inst,
      specialize_literal, Tmpl.instantiate_lit, scrInPorts_targets, K, List.append_assoc]
  have e3 : xBits scrWires K ++ (scrInArith ++ xBits scrWires K) =
      (specialize (scrInCompare rows) a).instantiate read := by
    simp only [scrInCompare_split, specialize_append, Tmpl.instantiate_append, scr_lookup_inst,
      scrInPorts_targets, K, hm, scrInArith, List.append_assoc]
  rw [e4, cBits_sandwich_run windowRoot scrWires K scrInArith m t windowRoot_not_scr scrInArith_root hr, e3,
    scrIn_inst, scr_sandwich _ _ _ _ (scrInCompare_sim read rows a) m t hs]
  exact ((scrInCompare_sim read rows a).step m t hs).2

end
end ShorECDLP.Entrant.WEX


end
