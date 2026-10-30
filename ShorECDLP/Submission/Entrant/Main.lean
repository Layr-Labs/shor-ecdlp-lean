import ShorECDLP.Submission.Entrant.Compiler
import ShorECDLP.Submission.«2607_13816».Challenge.Support
import ShorECDLP.Submission.Entrant.Single.Physical
import ShorECDLP.Submission.Entrant.Single.Fourier
import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift


/-! EDITABLE. Single-trial entrant: protected certificate assembly.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Certificate ====

section
/-! Single-trial certificate for the 263/263-bit protected nearest-pair decoder.
The fixed-table packaging follows the Apache-2.0 VerifiedQC Streaming certificate
(PR #551), for the construction of arXiv:2607.13816v2. See LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Generic packaging avoids unfolding a large coefficient table to transport its length. -/
def fixedEntry {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) : StraightEntry where
  coefficients := List.ofFn f
  finalCursor := e
  program := reindexStraight (Fin.cast List.length_ofFn.symm) p

private theorem ofFn_read {n : Nat} (f : Fin n → PointCoeff) (Q : Point) :
    (fun r : ConstantBit n => readConstant (List.ofFn f).get Q
      ⟨Fin.cast (List.length_ofFn).symm r.point, r.field, r.bit⟩) =
      readConstant f Q := by
  funext r
  simp only [readConstant,List.get_eq_getElem,List.getElem_ofFn,Fin.val_cast,Fin.eta]

theorem fixedEntry_instantiate {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (fixedEntry f p).instantiate Q = p.instantiate (readConstant f Q) Fin.elim0 := by
  dsimp only [fixedEntry,StraightEntry.instantiate]
  rw [reindexStraight_instantiate]
  simp only [Function.comp_def,reindexBit]
  rw [ofFn_read]

theorem fixedEntry_slots {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).program.gateSlots = p.gateSlots :=
  reindexStraight_gateSlots _ _

theorem fixedEntry_wellFormed {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).program.WellFormed ↔ p.WellFormed :=
  reindexStraight_wellFormed _ _

theorem fixedEntry_cursor {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).finalCursor = e := rfl

theorem fixedEntry_rows {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).coefficients.length = n := List.length_ofFn


end ShorECDLP.Entrant.Single
end

namespace ShorECDLP.Entrant.Rounded
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open RoundedReadout
noncomputable section
set_option maxRecDepth 4096

def finePositions : List (Fin 921241146) :=
  Single.trialPositions.right.toList.attach.map fun i =>
    ⟨i.val, (Single.right_position_bound i.val i.property).2.trans (by decide)⟩

theorem finePositions_length : finePositions.length = 224 := by
  simp [finePositions, Single.params]

theorem finePositions_vals : finePositions.map Fin.val = Single.trialPositions.right.toList := by
  simp [finePositions, List.map_map]

def carryPosition : Fin 921241146 := finePositions[20]'(by rw [finePositions_length]; decide)
def inputPositions : List (Fin 921241146) := finePositions.drop 21

theorem inputPositions_length : inputPositions.length = 203 := by
  simp [inputPositions, finePositions_length]

def readout : Straight 901120 921241146 921241552 :=
  castFinish (by rw [inputPositions_length]) (addWord 921241146 carryPosition inputPositions)

def program : Straight 901120 0 921241552 := Single.program.append readout

def positions : TrialPositions decoderParams where
  left := Single.trialPositions.left
  right := Vector.ofFn fun i : Fin 203 => 921241146 + 2*i.val+1

def layout : DecodeLayout := ⟨.wrappedShift, decoderParams, [positions], by simp⟩

theorem readout_wellFormed : readout.WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact addWord_wellFormed _ _ _

theorem readout_t (read : ConstantBit 901120 → Bool) (history : Fin 921241146 → Bool) :
    (readout.instantiate read history).tCount = 0 := by
  unfold readout
  rw [castFinish_instantiate]
  exact addWord_t _ _ _ _ _

theorem readout_support (read : ConstantBit 901120 → Bool) (history : Fin 921241146 → Bool) :
    (readout.instantiate read history).wires ⊆ resetWires := by
  unfold readout
  rw [castFinish_instantiate]
  apply (addWord_support _ _ _ _ _).trans
  simp [List.subset_def, resetWires]

theorem program_clean (read : ConstantBit 901120 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (Single.program.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [Single.Distribution.program_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  simp only [Single.Distribution.terminalInstrument, AdaptiveCircuit.run] at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean resetWires resetWires_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 (by simp [resetWires]), h s hs 1 (by simp [resetWires])⟩

theorem word_eq (bits : List Bool) : fourierWordLSB bits = boolWordToNat bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [fourierWordLSB, boolWordToNat_cons, ih]

theorem fine_read (history : Fin 921241146 → Bool) :
    readWord (List.ofFn history) Single.trialPositions.right.toList =
      some (boolWordToNat (finePositions.map history)) := by
  rw [← finePositions_vals]
  have h := readWord_of_actual_bits (List.ofFn history) (finePositions.map Fin.val)
    (finePositions.map history) (by simp only [List.map_map, List.getElem?_ofFn, Fin.isLt, ↓reduceDIte, Fin.eta, Function.comp_def])
  simpa only [word_eq] using h

theorem rounded_read (history : Fin 921241146 → Bool) :
    readWord (List.ofFn history ++ carryBits (history carryPosition) (inputPositions.map history))
      positions.right.toList = some (coarseRound (boolWordToNat (finePositions.map history))) := by
  let bits := finePositions.map history
  have hl : bits.length = 224 := by simp [bits, finePositions_length]
  have hc : history carryPosition = bits[20]'(by omega) := by
    simp [bits, carryPosition]
  have hi : inputPositions.map history = bits.drop 21 := by
    simp [bits, inputPositions, List.map_drop]
  rw [hc, hi]
  have hactual : positions.right.toList.map
      (fun i => (List.ofFn history ++ carryBits bits[20] (bits.drop 21))[i]?) =
      (sumBits bits[20] (bits.drop 21)).map some := by
    apply List.ext_getElem
    · simp only [List.length_map, positions, Vector.toList_ofFn, List.length_ofFn, sumBits_length, List.length_drop, hl]
      rfl
    · intro i hi hj
      simp only [List.length_map, positions, Vector.toList_ofFn, List.length_ofFn] at hi
      simp only [List.getElem_map, positions, Vector.toList_ofFn, List.getElem_ofFn]
      rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega)]
      simp only [List.length_ofFn]
      rw [show 921241146 + 2*i+1-921241146=2*i+1 by omega]
      rw [carryBits_odd, List.getElem?_eq_getElem (by simpa [sumBits_length, hl] using hi)]
  rw [readWord_of_actual_bits _ _ _ hactual, word_eq, rounded_word_value bits 20 (by omega)]
  simp only [hl, coarseRound]
  rfl


theorem readWord_append_left (before after : List Bool) (ps : List Nat)
    (h : ∀ i ∈ ps, i < before.length) : readWord (before ++ after) ps = readWord before ps := by
  induction ps with
  | nil => rfl
  | cons i ps ih =>
    simp only [readWord, List.getElem?_append_left (h i (by simp)),
      ih (fun j hj => h j (by simp [hj]))]

theorem readout_branch (read : ConstantBit 901120 → Bool) (history : Fin 921241146 → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ (readout.instantiate read history).run) (hn : b.kraus ψ ≠ 0) :
    b.history = carryBits (history carryPosition) (inputPositions.map history) := by
  unfold readout at hb
  rw [castFinish_instantiate] at hb
  exact (addWord_branch _ _ _ _ _ _ hψ b hb hn).2

theorem verified_of_reads (ps : TrialPositions decoderParams) (Q : Point) (d : Nat)
    (hd : Q = d • G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist ps.left.toList = some a)
    (hr : readWord hist ps.right.toList = some b)
    (hm : (d : ZMod order) ∈ fixedCandidates decoderParams a b) :
    (verifiedCandidate ⟨.wrappedShift, decoderParams, [ps], by simp⟩ Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order), ?_, ?_⟩
  · simpa only [candidates, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      decodeTrial, trialCandidates, hl, hr, fixedCandidates_take, Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq, ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order]; exact Nat.mod_mod _ _)

theorem pairAccept_value (left right : List Nat) (accept : Nat → Nat → Bool)
    (before : List Bool) (v : Nat) (hr : readWord before right = some v)
    (hf : Single.Distribution.pairAccept left right accept before = true) :
    ∃ a, readWord before left = some a ∧ accept a v = true := by
  unfold Single.Distribution.pairAccept at hf
  rw [hr] at hf
  cases ha : readWord before left with
  | none => simp only [ha, Option.bind_none, Option.getD_none, Bool.false_eq_true] at hf
  | some a =>
    exact ⟨a, rfl, by simpa only [ha, Option.bind_some, Option.map_some, Option.getD_some] using hf⟩

theorem pairRecovered_mem (d a b : Nat) (h : pairRecovered d a b = true) :
    (d : ZMod order) ∈ fixedCandidates decoderParams a (coarseRound b) :=
  of_decide_eq_true h

theorem history_verified (ps : TrialPositions decoderParams) (left right : List Nat) (Q : Point) (d : Nat) (hd : Q = d • G)
    (before after : List Bool) (v : Nat)
    (hl : readWord (before ++ after) ps.left.toList = readWord before left)
    (hr : readWord (before ++ after) ps.right.toList = some (coarseRound v))
    (hfine : readWord before right = some v)
    (hf : Single.Distribution.pairAccept left right (pairRecovered d) before = true) :
    (verifiedCandidate ⟨.wrappedShift, decoderParams, [ps], by simp⟩ Q (before ++ after)).isSome := by
  obtain ⟨a, ha, hp⟩ := pairAccept_value left right (pairRecovered d) before v hfine hf
  exact verified_of_reads ps Q d hd _ a _ (hl.trans ha) hr (pairRecovered_mem d a v hp)

theorem verified_append_congr (Q : Point) (before a b : List Bool) (h : a = b)
    (ha : (verifiedCandidate layout Q (before ++ a)).isSome) :
    (verifiedCandidate layout Q (before ++ b)).isSome := by
  subst b
  exact ha

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q = d • G)
    (read : ConstantBit 901120 → Bool) (history : Fin 921241146 → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : Single.Distribution.fineEvent (pairRecovered d) (List.ofFn history) = true)
    (b : InstrumentBranch) (hb : b ∈ (readout.instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    (verifiedCandidate layout Q (List.ofFn history ++ b.history)).isSome := by
  classical
  have hhist := readout_branch read history ψ hψ b hb hn
  apply verified_append_congr Q (List.ofFn history) _ b.history hhist.symm
  have hr := rounded_read history
  have hl : readWord (List.ofFn history ++ carryBits (history carryPosition) (inputPositions.map history))
      positions.left.toList = readWord (List.ofFn history) Single.trialPositions.left.toList := by
    apply readWord_append_left
    intro i hi
    have h := Single.left_position_bound i hi
    simpa only [List.length_ofFn] using h.trans (by decide : 491358742 < 921241146)
  exact history_verified positions Single.trialPositions.left.toList Single.trialPositions.right.toList Q d hd _ _ _ hl hr (fine_read history) hf

theorem normSq_ge_zero (ψ : State) : 0 ≤ normSq ψ := by
  have h := normSq_interference (0 : State) ψ
  have hz : normSq (0 : State) = 0 := by simp [normSq]
  simp only [zero_add, hz, mul_zero, zero_add] at h
  linarith [h.2]

theorem mass_ge_zero (I : Instrument) (ψ : State) : 0 ≤ I.bornMass ψ :=
  List.sum_nonneg (fun x hx => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact normSq_ge_zero _)

theorem mass_filter_eq (I : Instrument) (p : InstrumentBranch → Bool) (ψ : State)
    (h : ∀ b ∈ I, b.kraus ψ ≠ 0 → p b = true) :
    Instrument.bornMass (I.filter p) ψ = I.bornMass ψ := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    have ht := ih (fun c hc => h c (by simp [hc]))
    by_cases hb : p b = true
    · simpa [Instrument.bornMass, hb] using congrArg (normSq (b.kraus ψ) + ·) ht
    · have hz : b.kraus ψ = 0 := by
        by_contra hn
        exact hb (h b (by simp) hn)
      simpa [Instrument.bornMass, hb, hz, normSq] using ht

theorem appended_mass_lower (I : Instrument) (J : InstrumentBranch → Instrument)
    (p : InstrumentBranch → Bool) (q : InstrumentBranch → Bool) (ψ : State)
    (hn : ∀ a ∈ I, (J a).bornMass (a.kraus ψ) = normSq (a.kraus ψ))
    (hq : ∀ a ∈ I, p a = true → ∀ b ∈ J a,
      b.kraus (a.kraus ψ) ≠ 0 → q (a.seq b) = true) :
    Instrument.bornMass (I.filter p) ψ ≤
      Instrument.bornMass ((I.flatMap fun a => (J a).map a.seq).filter q) ψ := by
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons a I ih =>
    have ht := ih (fun c hc => hn c (by simp [hc]))
      (fun c hc => hq c (by simp [hc]))
    have he : Instrument.bornMass (((J a).map a.seq).filter q) ψ =
        Instrument.bornMass ((J a).filter (fun b => q (a.seq b))) (a.kraus ψ) := by
      simp only [List.filter_map, Instrument.bornMass, List.map_map,
        InstrumentBranch.seq, LinearMap.comp_apply, Function.comp_def]
    simp only [List.flatMap_cons, List.filter_append, Instrument.bornMass,
      List.map_append, List.sum_append] at ht ⊢
    by_cases hp : p a = true
    · have heq := mass_filter_eq (J a) (fun b => q (a.seq b)) (a.kraus ψ)
        (hq a (by simp) hp)
      simp only [Instrument.bornMass] at he heq
      rw [he, heq]
      have hna := hn a (by simp)
      simp only [Instrument.bornMass] at hna
      rw [hna]
      simpa [Instrument.bornMass, hp] using add_le_add_left ht (normSq (a.kraus ψ))
    · have hpos := mass_ge_zero (((J a).map a.seq).filter q) ψ
      simp only [Instrument.bornMass] at hpos
      simpa [hp] using ht.trans (le_add_of_nonneg_left hpos)

theorem program_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99/100 : ℝ) ≤ Instrument.bornMass ((program.instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) := by
  apply (Single.Distribution.program_rounded_success Q d hn hd).trans
  unfold program
  rw [Single.append_run_history]
  apply appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout.instantiate_wellFormed _ _ readout_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = 921241146 := by
      have h := straight_history_length Single.program (readConstant Single.mixedCoefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter 921241146 Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant Single.mixedCoefficientAt Q)
      (Single.historyAfter 921241146 Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

def entry : StraightEntry := Single.fixedEntry Single.mixedCoefficientAt program

def bounds : Bounds := ⟨854, 15397154744, 921241552⟩

theorem program_wellFormed : program.WellFormed :=
  straight_append_wellFormed _ _ Single.program_wellFormed readout_wellFormed

theorem program_support (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ resetWires :=
  outer_append_support _ _ read Fin.elim0 resetWires (Single.program_support read)
    (readout_support read)

theorem program_qubits (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).qubitCount ≤ 854 := by
  have hs : (program.instantiate read Fin.elim0).wires.dedup.toFinset ⊆
      resetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (program_support read (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount, resetWires_length] using hc

attribute [local irreducible] readout

theorem program_t (Q : Point) :
    (program.instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤ 15397154744 := by
  have h := outer_append_t_le Single.program readout (readConstant Single.mixedCoefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  rw [Nat.add_zero] at h
  change ((Single.program.append readout).instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤ 15397154744
  exact h.trans (Single.program_t Q)

theorem program_slots : program.gateSlots ≤ 93000061339 := by
  unfold program readout
  rw [Straight.gateSlots_append, castFinish_gateSlots, addWord_slots, inputPositions_length]
  have h := Single.program_slots
  omega

theorem certificate : Certificate officialLimits layout entry bounds where
  gateBudget := by
    rw [entry, Single.fixedEntry_slots]
    exact program_slots.trans (by decide)
  recordBudget := by
    change 921241552 ≤ officialLimits.measurements
    decide
  tableBudget := by
    rw [entry, Single.fixedEntry_rows]
    decide
  candidateBudget := by
    change 1 * (2*(order/2^203+2)) ≤ 56*(2^49+2)
    simpa using one_trial_budget
  wellFormed := by
    rw [entry, Single.fixedEntry_wellFormed]
    exact program_wellFormed
  resources := by
    intro Q
    rw [entry, Single.fixedEntry_instantiate]
    exact ⟨program_qubits _, program_t Q, (program.measurementCount _ _).le⟩
  success := by
    intro Q d hn hd
    rw [entry, Single.fixedEntry_instantiate]
    exact program_success Q d hn hd

end
end ShorECDLP.Entrant.Rounded


section


/-! Exact cancellation of reversible gates across commuting classical operations.
The rewrite preserves the full quantum operator, including on nonzero workspace. -/
namespace ShorECDLP.Entrant.Cancellation
open Quantum
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

def controls : Gate → List Wire
  | .CX a _ => [a]
  | .CCX a b _ => [a,b]
  | _ => []

def target : Gate → Wire
  | .X t | .H t | .CX _ t | .CCX _ _ t | .P _ _ t => t

def classicalGate : Gate → Bool
  | .X _ | .CX _ _ | .CCX _ _ _ => true
  | _ => false

def commutes (a b : Gate) : Bool :=
  classicalGate a && classicalGate b &&
    !(controls a).contains (target b) && !(controls b).contains (target a)

private theorem classical_commute (a b : Gate) (hc : commutes a b = true)
    (s : BasisState) :
    Classical.applyGate a (Classical.applyGate b s) =
      Classical.applyGate b (Classical.applyGate a s) := by
  cases a <;> cases b <;>
    simp_all [commutes, classicalGate, controls, target]
  all_goals
    funext w
    simp only [Classical.applyGate, upd]
    split_ifs <;> subst_vars <;> try contradiction
  all_goals simp only [eq_self, not_true_eq_false, false_and, and_false] at *
  all_goals try simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_not]

private theorem quantum_commute (a b : Gate) (hc : commutes a b = true)
    (ψ : State) :
    Quantum.applyGate a (Quantum.applyGate b ψ) =
      Quantum.applyGate b (Quantum.applyGate a ψ) := by
  have ha : Classical.IsClassicalGate a := by
    cases a <;> simp_all [commutes, classicalGate, Classical.IsClassicalGate]
  have hb : Classical.IsClassicalGate b := by
    cases b <;> simp_all [commutes, classicalGate, Classical.IsClassicalGate]
  have hk (s : BasisState) :
      Quantum.applyGate a (Quantum.applyGate b (ket s)) =
        Quantum.applyGate b (Quantum.applyGate a (ket s)) := by
    simp only [applyGate_ket_agrees_classical _ _ ha,
      applyGate_ket_agrees_classical _ _ hb, classical_commute a b hc]
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s c ψ hs hc ih =>
    have he : Finsupp.single s c = c • ket s := by simp [ket]
    simp only [map_add, he, map_smul, ih, hk]

/-- Search only through commuting gates. Failure leaves the input untouched. -/
def erase (g : Gate) : Circuit → Option Circuit
  | [] => none
  | h :: hs =>
    if g = h ∧ g.adjoint = g then some hs
    else if commutes g h then (erase g hs).map (List.cons h)
    else none

/-- Append one gate to a reverse-order accumulation, cancelling when possible. -/
def push (g : Gate) (gs : Circuit) : Circuit :=
  match erase g gs with
  | some rest => rest
  | none => g :: gs

/-- The list is processed from right to left. -/
def optimize : Circuit → Circuit
  | [] => []
  | g :: gs => push g (optimize gs)

theorem erase_sublist (g : Gate) (xs ys : Circuit) (h : erase g xs = some ys) :
    ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · cases h
      exact List.Sublist.cons _ (List.Sublist.refl _)
    · split at h
      · cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          exact List.Sublist.cons₂ _ (ih zs he)
      · simp at h

theorem push_sublist (g : Gate) (xs : Circuit) : (push g xs).Sublist (g :: xs) := by
  unfold push
  cases h : erase g xs with
  | none => exact List.Sublist.refl _
  | some ys => exact List.Sublist.cons _ (erase_sublist g xs ys h)

theorem optimize_sublist (xs : Circuit) : (optimize xs).Sublist xs := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons g xs ih =>
    exact (push_sublist g (optimize xs)).trans (List.Sublist.cons₂ g ih)

private theorem erase_mem (g : Gate) (xs ys : Circuit) (h : erase g xs = some ys) :
    ∀ a ∈ ys, a ∈ xs := by
  induction xs generalizing ys with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · cases h
      exact fun b hb => List.mem_cons_of_mem _ hb
    · split at h
      · cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih zs he b hb)
      · simp at h

theorem push_mem (g : Gate) (xs : Circuit) :
    ∀ a ∈ push g xs, a ∈ g :: xs := by
  unfold push
  cases h : erase g xs with
  | none => exact fun _ ha => ha
  | some ys => exact fun a ha => List.mem_cons_of_mem _ (erase_mem g xs ys h a ha)

theorem optimize_mem (xs : Circuit) : ∀ a ∈ optimize xs, a ∈ xs := by
  induction xs with
  | nil => simp [optimize]
  | cons g xs ih =>
    intro a ha
    rcases List.mem_cons.mp (push_mem g (optimize xs) a ha) with rfl | hh
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih a hh)

theorem optimize_wellFormed (xs : Circuit) (h : CircuitWellFormed xs) :
    CircuitWellFormed (optimize xs) :=
  fun a ha => h a (optimize_mem xs a ha)

private theorem erase_run (g : Gate) (xs ys : Circuit)
    (hg : g.WellFormed) (h : erase g xs = some ys) (ψ : State) :
    Quantum.run (g :: xs) ψ = Quantum.run ys ψ := by
  induction xs generalizing ys ψ with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · rename_i he
      rcases he with ⟨rfl, hadj⟩
      cases h
      simp only [Quantum.run_cons]
      have hi := applyGate_adjoint_applyGate g hg ψ
      rw [hadj] at hi
      rw [hi]
    · split at h
      · rename_i hc
        cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          simp only [Quantum.run_cons]
          rw [← quantum_commute g a hc]
          exact ih zs he (Quantum.applyGate a ψ)
      · simp at h

theorem push_run (g : Gate) (xs : Circuit) (hg : g.WellFormed) (ψ : State) :
    Quantum.run (push g xs) ψ = Quantum.run (g :: xs) ψ := by
  unfold push
  cases h : erase g xs with
  | none => rfl
  | some ys => exact (erase_run g xs ys hg h ψ).symm

theorem optimize_run (xs : Circuit) (h : CircuitWellFormed xs) :
    Quantum.run (optimize xs) = Quantum.run xs := by
  induction xs with
  | nil => rfl
  | cons g xs ih =>
    have hg := h g (by simp)
    have ht : CircuitWellFormed xs := fun a ha => h a (by simp [ha])
    apply LinearMap.ext
    intro ψ
    rw [optimize, push_run _ _ hg, Quantum.run_cons, ih ht, Quantum.run_cons]

end ShorECDLP.Entrant.Cancellation

namespace ShorECDLP.Entrant.Cancellation
open Paper2607_13816

/-- The terminal-epoch restore has two redundant traversals of its predicate v-chain. -/
def epochSource : Circuit := blockCForward indexedStepProductionRegisters

def reducedEpoch : Circuit := optimize epochSource

private instance gateWellFormedDecidable (g : Gate) : Decidable g.WellFormed := by
  cases g <;> unfold Gate.WellFormed <;> infer_instance

theorem epochSource_wellFormed : CircuitWellFormed epochSource := by
  unfold CircuitWellFormed
  decide +kernel

theorem reducedEpoch_run : Quantum.run reducedEpoch = Quantum.run epochSource :=
  optimize_run epochSource epochSource_wellFormed

theorem reducedEpoch_sublist : reducedEpoch.Sublist epochSource := optimize_sublist epochSource

theorem reducedEpoch_counts : ShorECDLP.tCount epochSource = 245 ∧
    ShorECDLP.tCount reducedEpoch = 133 ∧ reducedEpoch.length = 24 := by
  decide +kernel

end ShorECDLP.Entrant.Cancellation


namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration

/-- A syntactic subsequence retaining every measurement and classical control. -/
inductive Drops {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Nat → Prop
  | refl {s e} (p : Straight n s e) : Drops p p 0
  | skip {s e} (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate (.literal g) p) q (tCost g + d)
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate g p) (.gate g q) d
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.recordGate i v g p) (.recordGate i v g q) d
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} {d : Nat} :
      Drops p q d → Drops (.measure w p) (.measure w q) d

theorem Drops.wellFormed {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (hp : p.WellFormed) : q.WellFormed := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ih hp

theorem Drops.slots {n s e d} {p q : Straight n s e}
    (h : Drops p q d) : q.gateSlots ≤ p.gateSlots := by
  induction h <;> simp_all [Straight.gateSlots]; omega

theorem Drops.tCount {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (q.instantiate read history).tCount + d = (p.instantiate read history).tCount := by
  induction h with
  | refl => omega
  | skip g h ih =>
    simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have hh := ih history
    omega
  | gate g h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hh := ih history
    omega
  | record i v g h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hh := ih history
    omega
  | measure w h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hf := ih (Fin.lastCases false history)
    have ht := ih (Fin.lastCases true history)
    omega

theorem Drops.wires {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ∀ w ∈ (q.instantiate read history).wires, w ∈ (p.instantiate read history).wires := by
  induction h with
  | refl => exact fun _ hw => hw
  | skip g h ih =>
    intro w hw
    exact List.mem_append_right _ (ih history w hw)
  | gate g h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_append] at hw ⊢
    exact hw.imp id (ih history w)
  | record i v g h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_append] at hw ⊢
    exact hw.imp id (ih history w)
  | measure v h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_cons, List.mem_append] at hw ⊢
    rcases hw with he | hf | ht
    · exact Or.inl he
    · exact Or.inr (Or.inl (ih (Fin.lastCases false history) w hf))
    · exact Or.inr (Or.inr (ih (Fin.lastCases true history) w ht))

private theorem Drops.append_right {n a b c d} (p : Straight n a b)
    {q q' : Straight n b c} (h : Drops q q' d) : Drops (p.append q) (p.append q') d := by
  induction p with
  | done => exact h
  | gate g p ih => exact Drops.gate g (ih h)
  | recordGate i v g p ih => exact Drops.record i v g (ih h)
  | measure w p ih => exact Drops.measure w (ih h)

theorem Drops.append {n a b c d f} {p p' : Straight n a b} {q q' : Straight n b c}
    (hp : Drops p p' d) (hq : Drops q q' f) :
    Drops (p.append q) (p'.append q') (d+f) := by
  induction hp with
  | refl p => simpa using Drops.append_right p hq
  | skip g h ih => simpa [Nat.add_assoc] using Drops.skip g (ih hq)
  | gate g h ih => exact Drops.gate g (ih hq)
  | record i v g h ih => exact Drops.record i v g (ih hq)
  | measure w h ih => exact Drops.measure w (ih hq)

private theorem tCount_le_of_sublist {xs ys : Circuit} (h : xs.Sublist ys) :
    ShorECDLP.tCount xs ≤ ShorECDLP.tCount ys := by
  induction h <;> simp_all [ShorECDLP.tCount]; omega

theorem Drops.literal {n s} {xs ys : Circuit} (h : ys.Sublist xs) :
    Drops (literalProgram xs : Straight n s s) (literalProgram ys)
      (ShorECDLP.tCount xs - ShorECDLP.tCount ys) := by
  induction h with
  | slnil => exact Drops.refl _
  | cons a h ih =>
    have ht := tCount_le_of_sublist h
    simpa [literalProgram, gateProgram, ShorECDLP.tCount_cons, Nat.add_sub_assoc ht]
      using Drops.skip a ih
  | cons₂ a h ih =>
    simpa [literalProgram, gateProgram, ShorECDLP.tCount_cons, Nat.add_sub_add_left] using Drops.gate (.literal a) ih

/-- Structural circuit rewrites, with exact operator equality at unitary leaves. -/
inductive Rewrites {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Prop
  | refl {s e} (p : Straight n s e) : Rewrites p p
  | literal {s} (xs ys : Circuit) : Quantum.run xs = Quantum.run ys →
      Rewrites (literalProgram xs : Straight n s s) (literalProgram ys)
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} :
      Rewrites p q → Rewrites (.gate g p) (.gate g q)
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} :
      Rewrites p q → Rewrites (.recordGate i v g p) (.recordGate i v g q)
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} :
      Rewrites p q → Rewrites (.measure w p) (.measure w q)
  | append {a b c} {p p' : Straight n a b} {q q' : Straight n b c} :
      Rewrites p p' → Rewrites q q' → Rewrites (p.append q) (p'.append q')

private noncomputable def branchPrefix (history : List Bool) (u : State →ₗ[ℂ] State)
    (branches : Instrument) : Instrument :=
  branches.map fun b => ⟨history ++ b.history, b.kraus.comp u⟩

private theorem prefix_prefix (a b : List Bool) (u v : State →ₗ[ℂ] State) (bs : Instrument) :
    branchPrefix a u (branchPrefix b v bs) = branchPrefix (a++b) (v.comp u) bs := by
  simp only [branchPrefix, List.map_map]
  congr 1
  funext branch
  simp only [Function.comp_apply, List.append_assoc, LinearMap.comp_assoc]

/-- Continuation evaluator used only to prove context closure, never as submitted data. -/
private noncomputable def evaluate {n s e} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : Instrument :=
  match p with
  | .done => tail history
  | .gate g p => branchPrefix [] (Quantum.run (g.instantiate read)) (evaluate p read history tail)
  | .recordGate i v g p => branchPrefix [] (Quantum.run (if history i=v then [g] else []))
      (evaluate p read history tail)
  | .measure w p =>
      branchPrefix [false] (xResetKraus w false) (evaluate p read (Fin.lastCases false history) tail) ++
      branchPrefix [true] (xResetKraus w true) (evaluate p read (Fin.lastCases true history) tail)

private theorem evaluate_append {n a b c} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n → Bool) (history : Fin a → Bool)
    (tail : (Fin c → Bool) → Instrument) :
    evaluate (p.append q) read history tail =
      evaluate p read history (fun h => evaluate q read h tail) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [Straight.append, evaluate, ih]
  | recordGate i v g p ih => simp only [Straight.append, evaluate, ih]
  | measure w p ih => simp only [Straight.append, evaluate, ih]

private theorem evaluate_literal {n s} (xs : Circuit) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (tail : (Fin s → Bool) → Instrument) :
    evaluate (literalProgram xs) read history tail = branchPrefix [] (Quantum.run xs) (tail history) := by
  induction xs with
  | nil => simp [literalProgram, gateProgram, evaluate, branchPrefix, Quantum.run]
  | cons g xs ih =>
    simp only [literalProgram, List.map_cons, gateProgram, evaluate, TemplateGate.instantiate] at ⊢
    change branchPrefix [] (Quantum.run [g]) (evaluate (literalProgram xs) read history tail) = _
    rw [ih, prefix_prefix]
    simp [Quantum.run]

private theorem Rewrites.eval_eq {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : evaluate p read history tail = evaluate q read history tail := by
  induction h with
  | refl => rfl
  | literal xs ys he => simp only [evaluate_literal, he]
  | gate g h ih =>
    simp only [evaluate, ih]
  | record i v g h ih =>
    simp only [evaluate, ih]
  | measure w h ih =>
    simp only [evaluate, ih]
  | append hp hq ip iq =>
    simp only [evaluate_append]
    rw [ip]
    congr 1
    funext hist
    exact iq hist tail

private theorem evaluate_run {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    evaluate p read history (fun _ => [{history := [], kraus := LinearMap.id}]) =
      (p.instantiate read history).run := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl
  | recordGate i v g p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl
  | measure w p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl

theorem Rewrites.run {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).run = (q.instantiate read history).run := by
  rw [← evaluate_run, ← evaluate_run]
  exact h.eval_eq read history _

private theorem reindex_append {n m a b c} (f : Fin n → Fin m)
    (p : Straight n a b) (q : Straight n b c) :
    reindexStraight f (p.append q) = (reindexStraight f p).append (reindexStraight f q) := by
  induction p <;> simp_all [reindexStraight, Straight.append]

private theorem reindex_literal {n m s} (f : Fin n → Fin m) (xs : Circuit) :
    reindexStraight f (literalProgram xs : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalProgram, gateProgram, reindexStraight, reindexGate]

theorem Rewrites.reindex {n m s e} {p q : Straight n s e} (h : Rewrites p q)
    (f : Fin n → Fin m) : Rewrites (reindexStraight f p) (reindexStraight f q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he => simpa only [reindex_literal] using Rewrites.literal (n := m) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [reindex_append] using Rewrites.append ip iq

theorem Drops.reindex {n m s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Fin n → Fin m) : Drops (reindexStraight f p) (reindexStraight f q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih => exact Drops.skip _ ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

private theorem relabel_append {n a b c} (f : Wire ≃ Wire)
    (p : Straight n a b) (q : Straight n b c) :
    relabelStraight f (p.append q) = (relabelStraight f p).append (relabelStraight f q) := by
  induction p <;> simp_all [relabelStraight, Straight.append]

private theorem relabel_literal {n s} (f : Wire ≃ Wire) (xs : Circuit) :
    relabelStraight f (literalProgram xs : Straight n s s) = literalProgram (xs.map (Gate.relabel f)) := by
  induction xs <;> simp_all [literalProgram, gateProgram, relabelStraight, relabelTemplateGate]

private theorem relabel_run_eq (f : Wire ≃ Wire) (xs ys : Circuit)
    (h : Quantum.run xs = Quantum.run ys) :
    Quantum.run (xs.map (Gate.relabel f)) = Quantum.run (ys.map (Gate.relabel f)) := by
  apply LinearMap.ext
  intro ψ
  have hx := Quantum.run_relabel f xs (relabelState f.symm ψ)
  have hy := Quantum.run_relabel f ys (relabelState f.symm ψ)
  simp only [relabelState_symm_right] at hx hy
  rw [hx, hy, h]

theorem Rewrites.relabel {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (f : Wire ≃ Wire) : Rewrites (relabelStraight f p) (relabelStraight f q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he =>
    simpa only [relabel_literal] using Rewrites.literal (n := n)
      (xs.map (Gate.relabel f)) (ys.map (Gate.relabel f)) (relabel_run_eq f xs ys he)
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [relabel_append] using Rewrites.append ip iq

theorem Drops.relabel {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Wire ≃ Wire) : Drops (relabelStraight f p) (relabelStraight f q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih =>
    have he : tCost (g.relabel f) = tCost g := by cases g <;> rfl
    simpa only [he] using Drops.skip (g.relabel f) ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

private theorem shift_append {n a b c} (offset : Nat)
    (p : Straight n a b) (q : Straight n b c) :
    shiftStraight offset (p.append q) = (shiftStraight offset p).append (shiftStraight offset q) := by
  induction p <;> simp_all [shiftStraight, Straight.append]

private theorem shift_literal {n s} (offset : Nat) (xs : Circuit) :
    shiftStraight offset (literalProgram xs : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalProgram, gateProgram, shiftStraight]

theorem Rewrites.shift {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (offset : Nat) : Rewrites (shiftStraight offset p) (shiftStraight offset q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he => simpa only [shift_literal] using Rewrites.literal (n := n) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [shift_append] using Rewrites.append ip iq

theorem Drops.shift {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (offset : Nat) : Drops (shiftStraight offset p) (shiftStraight offset q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih => exact Drops.skip _ ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

theorem Rewrites.castFinish {n s e f} {p q : Straight n s e} (h : Rewrites p q)
    (he : e=f) : Rewrites (castFinish he p) (castFinish he q) := by
  subst f
  exact h

theorem Drops.castFinish {n s e f d} {p q : Straight n s e} (h : Drops p q d)
    (he : e=f) : Drops (castFinish he p) (castFinish he q) d := by
  subst f
  exact h

private theorem qubitCount_mono (a b : AdaptiveCircuit)
    (h : ∀ w ∈ a.wires, w ∈ b.wires) : a.qubitCount ≤ b.qubitCount := by
  have hh : a.wires.toFinset ⊆ b.wires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h w (List.mem_toFinset.mp hw))
  simpa only [AdaptiveCircuit.qubitCount, List.card_toFinset] using Finset.card_le_card hh

/-- Retain the exact table and decoder cursor while substituting an equivalent program. -/
def replaceEntry (e : StraightEntry) (p : Straight e.coefficients.length 0 e.finalCursor) : StraightEntry :=
  ⟨e.coefficients,e.finalCursor,p⟩

/-- Transport the protected certificate along a verified gate deletion with exact T savings. -/
theorem replacement_certificate {limits : Limits} {layout : DecodeLayout}
    {entry : StraightEntry} {bounds : Bounds} (original : Certificate limits layout entry bounds)
    {p : Straight entry.coefficients.length 0 entry.finalCursor} {saving : Nat}
    (hd : Drops entry.program p saving) (he : Rewrites entry.program p) :
    Certificate limits layout (replaceEntry entry p)
      ⟨bounds.qubits,bounds.tModel-saving,bounds.measurements⟩ := by
  refine ⟨hd.slots.trans original.gateBudget, original.recordBudget, original.tableBudget,
    original.candidateBudget, hd.wellFormed original.wellFormed, ?_, ?_⟩
  · intro Q
    have ho := original.resources Q
    have hq := qubitCount_mono (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0)
      (entry.instantiate Q) (hd.wires _ _)
    have ht := hd.tCount (readConstant entry.coefficients.get Q) Fin.elim0
    have hm := Straight.measurementCount p (readConstant entry.coefficients.get Q) Fin.elim0
    have hm' := Straight.measurementCount entry.program (readConstant entry.coefficients.get Q) Fin.elim0
    change (entry.instantiate Q).qubitCount ≤ bounds.qubits ∧
      (entry.instantiate Q).tCount ≤ bounds.tModel ∧
      (entry.instantiate Q).measurementCount ≤ bounds.measurements at ho
    change (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).qubitCount ≤ bounds.qubits ∧
      (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel-saving ∧
      (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ bounds.measurements
    exact ⟨hq.trans ho.1, by dsimp only [StraightEntry.instantiate] at ho; omega,
      by dsimp only [StraightEntry.instantiate] at ho; omega⟩
  · intro Q d hQ hdQ
    have hh := he.run (readConstant entry.coefficients.get Q) Fin.elim0
    change (99 : ℝ)/100 ≤ Instrument.bornMass
      (((p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run).filter _) (ket zeroBasisState)
    rw [← hh]
    exact original.success Q d hQ hdQ

/-- A program together with the exact proof needed to replace a fixed source context. -/
structure Patch {n s e : Nat} (source : Straight n s e) (saving : Nat) where
  program : Straight n s e
  drops : Drops source program saving
  rewrites : Rewrites source program

namespace Patch
noncomputable section

def refl {n s e} (p : Straight n s e) : Patch p 0 := ⟨p, Drops.refl p, Rewrites.refl p⟩

def castSaving {n s e a b} {p : Straight n s e} (h : Patch p a) (he : a=b) : Patch p b := he ▸ h

def literal {n s d} (xs ys : Circuit) (hs : ys.Sublist xs)
    (hr : Quantum.run xs = Quantum.run ys)
    (ht : ShorECDLP.tCount ys + d = ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n s s) d := by
  refine ⟨literalProgram ys, ?_, Rewrites.literal xs ys hr⟩
  have hd : ShorECDLP.tCount xs - ShorECDLP.tCount ys = d := by omega
  simpa only [hd] using Drops.literal (n := n) (s := s) hs

def append {n a b c d f} {p : Straight n a b} {q : Straight n b c}
    (hp : Patch p d) (hq : Patch q f) : Patch (p.append q) (d+f) :=
  ⟨hp.program.append hq.program, hp.drops.append hq.drops, hp.rewrites.append hq.rewrites⟩

def castFinish {n s e f d} {p : Straight n s e} (hp : Patch p d) (he : e=f) :
    Patch (Paper2607_13816.ChallengeMigration.castFinish he p) d :=
  ⟨Paper2607_13816.ChallengeMigration.castFinish he hp.program, hp.drops.castFinish he, hp.rewrites.castFinish he⟩

def appendCompiled {n start d f}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : Patch p.2 d) (hq : Patch q.2 f) :
    Patch (Paper2607_13816.ChallengeMigration.appendCompiled p q).2 (d+f) :=
  (hp.append hq).castFinish (Nat.add_assoc start p.1 q.1)

def sequenceCons {n start d f} (head : FixedSegment n) (tail : List (FixedSegment n))
    (hp : Patch (head start).2 d)
    (hq : Patch (sequenceProgram n tail (start+(head start).1)).2 f) :
    Patch (sequenceProgram n (head::tail) start).2 (d+f) :=
  appendCompiled (head start) (sequenceProgram n tail (start+(head start).1)) hp hq

def gate {n s e d} (g : TemplateGate n) {p : Straight n s e} (hp : Patch p d) :
    Patch (.gate g p) d := ⟨.gate g hp.program, Drops.gate g hp.drops, Rewrites.gate g hp.rewrites⟩

def record {n s e d} (i : Fin s) (v : Bool) (g : Gate) {p : Straight n s e}
    (hp : Patch p d) : Patch (.recordGate i v g p) d :=
  ⟨.recordGate i v g hp.program, Drops.record i v g hp.drops, Rewrites.record i v g hp.rewrites⟩

def measure {n s e d} (w : Wire) {p : Straight n (s+1) e} (hp : Patch p d) :
    Patch (.measure w p) d :=
  ⟨.measure w hp.program, Drops.measure w hp.drops, Rewrites.measure w hp.rewrites⟩

def reindex {n m s e d} {p : Straight n s e} (hp : Patch p d) (f : Fin n → Fin m) :
    Patch (reindexStraight f p) d :=
  ⟨reindexStraight f hp.program, hp.drops.reindex f, hp.rewrites.reindex f⟩

def relabel {n s e d} {p : Straight n s e} (hp : Patch p d) (f : Wire ≃ Wire) :
    Patch (relabelStraight f p) d :=
  ⟨relabelStraight f hp.program, hp.drops.relabel f, hp.rewrites.relabel f⟩

def shift {n s e d} {p : Straight n s e} (hp : Patch p d) (offset : Nat) :
    Patch (shiftStraight offset p) d :=
  ⟨shiftStraight offset hp.program, hp.drops.shift offset, hp.rewrites.shift offset⟩

end
end Patch

end ShorECDLP.Entrant.Optimization


namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration
open Paper2607_13816
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
set_option Elab.async false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
  remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
  preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
  measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
  measuredInverseStepProgram measuredEEAReverseProgram measuredReverseWrapperProgram
  hInverseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram
  measuredForwardDataBankProgram measuredReverseDataBankProgram multiplicationProgram
  multiplicationAfterResetProgram multiplicationCorrectionProgram multiplicationCleanupProgram
  multiplyDataProgram unmultiplyDataProgram divisionCorrectionProgram collectProgram
  divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
  zeroMultiplicationProgram xNegateProgram coordinateProgram


def Patch.prependCompiled {n start d} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.prependCompiled gs p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram gs)).append hp).castSaving (Nat.zero_add d)

def Patch.surroundCompiled {n start d} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.surroundCompiled before after p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.surroundCompiled Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram before)).append
    ((Patch.appendCompiled p ⟨0, literalProgram after⟩ hp (Patch.refl _)).castSaving (Nat.add_zero d))).castSaving (Nat.zero_add d)

/-- Rewrite one terminal-epoch restore inside an otherwise untouched literal segment. -/
def epochPatch (n s : Nat) (tail : Circuit) :
    Patch (literalProgram (Cancellation.epochSource ++ tail) : Straight n s s) 112 := by
  apply Patch.literal _ (Cancellation.reducedEpoch ++ tail)
  · exact Cancellation.reducedEpoch_sublist.append (List.Sublist.refl _)
  · simp only [Quantum.run_append_map, Cancellation.reducedEpoch_run]
  · have h := Cancellation.reducedEpoch_counts
    simp only [ShorECDLP.tCount_append, h.1, h.2.1]
    omega



set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def aSource : Circuit := blockAForward indexedStepProductionRegisters
def aMiddle : Circuit := (aSource.drop 837).take 33
def aReduced : Circuit := aSource.take 837 ++ Cancellation.optimize aMiddle ++ aSource.drop 870

private theorem split_three (xs : Circuit) (a b : Nat) :
    xs = xs.take a ++ (xs.drop a).take b ++ xs.drop (a+b) := by
  rw [List.append_assoc, ← List.drop_drop]
  rw [List.take_append_drop, List.take_append_drop]

private theorem aSplit : aSource = aSource.take 837 ++ aMiddle ++ aSource.drop 870 :=
  split_three aSource 837 33

private theorem aMiddle_wellFormed : CircuitWellFormed aMiddle := by
  unfold CircuitWellFormed
  decide +kernel

private theorem aMiddle_counts : ShorECDLP.tCount aMiddle = 105 ∧
    ShorECDLP.tCount (Cancellation.optimize aMiddle) = 7 := by
  decide +kernel

def aPatch (n start : Nat) : Patch (literalProgram aSource : Straight n start start) 98 := by
  apply Patch.literal _ aReduced
  · conv_rhs => rw [aSplit]
    exact ((List.Sublist.refl _).append (Cancellation.optimize_sublist aMiddle)).append (List.Sublist.refl _)
  · have h := Cancellation.optimize_run aMiddle aMiddle_wellFormed
    conv_lhs => rw [aSplit]
    simp only [aReduced, Quantum.run_append_map, h]
  · conv_rhs => rw [aSplit]
    have h := aMiddle_counts
    simp only [aReduced, ShorECDLP.tCount_append, h.1, h.2]
    omega


set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b2Source : Circuit := blockB2 indexedStepProductionRegisters
private theorem b2_wellFormed : CircuitWellFormed b2Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b2_counts : ShorECDLP.tCount b2Source = 462 ∧
    ShorECDLP.tCount (Cancellation.optimize b2Source) = 238 := by
  decide +kernel

def b2Patch (n start : Nat) : Patch (literalProgram b2Source : Straight n start start) 224 := by
  apply Patch.literal _ (Cancellation.optimize b2Source)
  · exact Cancellation.optimize_sublist b2Source
  · exact (Cancellation.optimize_run b2Source b2_wellFormed).symm
  · have h := b2_counts
    omega

def remainderPatch (n start width : Nat) (w : ActiveWindow) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters width w).2 224 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 224) (f := 0) _ _ (b2Patch n _) (Patch.refl _)).castSaving (by omega)

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b1Source : Circuit :=
  let r := indexedStepProductionRegisters
  rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
private theorem b1_wellFormed : CircuitWellFormed b1Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b1_counts : ShorECDLP.tCount b1Source = 217 ∧
    ShorECDLP.tCount (Cancellation.optimize b1Source) = 119 := by decide +kernel

def b1Patch (n start : Nat) : Patch (literalProgram b1Source : Straight n start start) 98 := by
  apply Patch.literal _ (Cancellation.optimize b1Source)
  · exact Cancellation.optimize_sublist b1Source
  · exact (Cancellation.optimize_run b1Source b1_wellFormed).symm
  · have h := b1_counts; omega

def remainderPatchAll (n start width : Nat) (w : ActiveWindow) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters width w).2 420 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 98) (f := 322) _ _ (b1Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 322) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 98) (f := 224) _ _ (b1Patch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 224) (f := 0) _ _ (b2Patch n _) (Patch.refl _)).castSaving (by omega)

def ePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  ((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ prepareLatestPaperTBoundary r.tBoundary 256

def eCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase1] 1 r.control r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

private theorem ePrep_wellFormed : CircuitWellFormed ePrepSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem eClean_wellFormed : CircuitWellFormed eCleanSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem ePrep_counts : ShorECDLP.tCount ePrepSource = 560 ∧
    ShorECDLP.tCount (Cancellation.optimize ePrepSource) = 518 := by decide +kernel
private theorem eClean_counts : ShorECDLP.tCount eCleanSource = 539 ∧
    ShorECDLP.tCount (Cancellation.optimize eCleanSource) = 497 := by decide +kernel

def ePrepPatch (n start : Nat) : Patch (literalProgram ePrepSource : Straight n start start) 42 := by
  apply Patch.literal _ (Cancellation.optimize ePrepSource)
  · exact Cancellation.optimize_sublist ePrepSource
  · exact (Cancellation.optimize_run ePrepSource ePrep_wellFormed).symm
  · have h := ePrep_counts; omega

def eCleanPatch (n start : Nat) : Patch (literalProgram eCleanSource : Straight n start start) 42 := by
  apply Patch.literal _ (Cancellation.optimize eCleanSource)
  · exact Cancellation.optimize_sublist eCleanSource
  · exact (Cancellation.optimize_run eCleanSource eClean_wellFormed).symm
  · have h := eClean_counts; omega

def coefficientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (coefficientBlockProgram n start indexedStepProductionRegisters 256 w).2 84 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  refine (Patch.sequenceCons (d := 42) (f := 42) _ _ (ePrepPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 42) (f := 0) _ _ (eCleanPatch n _) (Patch.refl _)).castSaving (by omega)

def candidateStepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 714 := by
  unfold measuredStepProgram measuredStepSegments
  refine (Patch.sequenceCons (d := 98) (f := 616) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 420) (f := 196) _ _ (remainderPatchAll n _ 256 _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 112) (f := 84) _ _ (epochPatch n _ _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 84) (f := 0) _ _ (coefficientPatch n _ _) (Patch.refl _)).castSaving (by omega)

/-- Optimize the fixed A, remainder-control, epoch and coefficient-boundary literals. -/
def stepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 714 :=
  candidateStepPatch n start T

/-- Exact per-step savings accumulate through the fixed 1,620-step schedule. -/

def schedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 (count*714)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredScheduleProgram]
    exact (Patch.appendCompiled _ _ (stepPatch n start first)
      (schedulePatch n count (first+1) _)).castSaving (by omega)


def eeaForwardPatch (n start : Nat) :
    Patch (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 1156680 := by
  unfold measuredEEAForwardProgram
  exact schedulePatch n 1620 1 start


def wrapperPatch (n start : Nat) :
    Patch (measuredForwardWrapperProgram n start).2 1156680 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 1156680) (f := 0) _ _ (eeaForwardPatch n _) (Patch.refl _)).castSaving (by omega)


/-- Literal concatenation supports mirrored segments without changing their context. -/
private theorem literal_append {n s : Nat} (xs ys : Circuit) :
    (literalProgram (xs ++ ys) : Straight n s s) =
      (literalProgram xs).append (literalProgram ys) := by
  induction xs with
  | nil => simp only [List.nil_append, literalProgram, List.map_nil, gateProgram, Straight.append]
  | cons g xs ih => simpa only [literalProgram, List.map_cons, gateProgram, Straight.append] using congrArg (Straight.gate (.literal g)) ih

def Patch.joinLiteral {n s d f} {xs ys : Circuit}
    (hp : Patch (literalProgram xs : Straight n s s) d)
    (hq : Patch (literalProgram ys : Straight n s s) f) :
    Patch (literalProgram (xs ++ ys) : Straight n s s) (d+f) := by
  rw [literal_append]
  exact hp.append hq

def optimizedLiteralPatch (n s d : Nat) (xs : Circuit)
    (hw : CircuitWellFormed xs)
    (ht : ShorECDLP.tCount (Cancellation.optimize xs) + d = ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n s s) d :=
  Patch.literal xs (Cancellation.optimize xs) (Cancellation.optimize_sublist xs)
    (Cancellation.optimize_run xs hw).symm ht

def reverseCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch

def reversePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

def reverseCleanPatch (n s : Nat) : Patch (literalProgram reverseCleanSource : Straight n s s) 42 :=
  optimizedLiteralPatch n s 42 reverseCleanSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reversePrepPatch (n s : Nat) : Patch (literalProgram reversePrepSource : Straight n s s) 42 :=
  optimizedLiteralPatch n s 42 reversePrepSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reverseEpochPatch (n s : Nat) :
    Patch (literalProgram (blockCInverse indexedStepProductionRegisters) : Straight n s s) 112 :=
  optimizedLiteralPatch n s 112 _ (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

/-- The reverse A literal is split around the terminal-padding epoch test.
Source arithmetic: VerifiedQC/ShorECDLP PR #551, Apache-2.0. -/
def aTerminalSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl (r.phase1 :: r.lengthRPrime) (2 ^ (r.lengthRPrime.length + 1) - 2) r.terminal r.blockScratch

def aInverseBefore : Circuit :=
  let r := indexedStepProductionRegisters
  aTerminalSource ++ terminalEpochRestore r.terminal r.shiftEpoch r.quotientLow ++
    [.CX r.terminal r.phase1] ++ (preShiftUnitary r.preShift).adjoint ++ [.CX r.terminal r.phase1]

def aInverseEpoch : Circuit := terminalPaddingEpochUpdate indexedStepProductionRegisters.terminalPadding

def aInverseAfter : Circuit :=
  let r := indexedStepProductionRegisters.terminalPadding
  controlledDecrement r.terminal r.lengthS r.carries ++ controlledRotateRightOne r.terminal r.work2 ++ aTerminalSource

private theorem aInverseEpoch_wellFormed : CircuitWellFormed aInverseEpoch := by
  unfold CircuitWellFormed
  decide +kernel
private theorem aInverseEpoch_saving :
    ShorECDLP.tCount (Cancellation.optimize aInverseEpoch) + 98 = ShorECDLP.tCount aInverseEpoch := by
  decide +kernel

def aInversePatch (n s : Nat) :
    Patch (literalProgram (blockAInverse indexedStepProductionRegisters) : Straight n s s) 98 := by
  have hp := (((Patch.refl (literalProgram aInverseBefore : Straight n s s)).joinLiteral
    (optimizedLiteralPatch n s 98 aInverseEpoch aInverseEpoch_wellFormed aInverseEpoch_saving)).joinLiteral
    (Patch.refl (literalProgram aInverseAfter : Straight n s s))).castSaving (show 0+98+0=98 by omega)
  simpa only [aInverseBefore, aInverseAfter, aInverseEpoch, aTerminalSource,
    blockAInverse, terminalPaddingInverse, List.append_assoc] using hp

def b3Source : Circuit :=
  let r := indexedStepProductionRegisters
  ([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]

def reverseFrontPatch (n s : Nat) :
    Patch (literalProgram ((blockFForward indexedStepProductionRegisters).adjoint ++
      prepareLatestPaperTBoundary indexedStepProductionRegisters.tBoundary 256 ++
      computeControl [indexedStepProductionRegisters.phase1] 1 indexedStepProductionRegisters.control indexedStepProductionRegisters.blockScratch) : Straight n s s) 42 := by
  have hp := ((Patch.refl (literalProgram (blockFForward indexedStepProductionRegisters).adjoint : Straight n s s)).joinLiteral
    (reverseCleanPatch n s)).castSaving (show 0+42=42 by omega)
  simpa only [reverseCleanSource, List.append_assoc] using hp

def reverseCombinedPatch (n s : Nat) (w : ActiveWindow) :
    Patch (literalProgram (let r := indexedStepProductionRegisters;
      computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
      computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
      computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++
      blockDInverse r w ++ blockCInverse r ++
      (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])) : Straight n s s) 154 := by
  have hp := ((((reversePrepPatch n s).joinLiteral
    (Patch.refl (literalProgram (blockDInverse indexedStepProductionRegisters w) : Straight n s s))).joinLiteral
    (reverseEpochPatch n s)).joinLiteral (Patch.refl (literalProgram b3Source : Straight n s s))).castSaving
    (show 42+0+112+0=154 by omega)
  simpa only [reversePrepSource, b3Source, List.append_assoc] using hp

def reverseRemainderPatch (n s : Nat) :
    Patch (literalProgram (b3Source ++ b2Source ++ b1Source) : Straight n s s) 322 := by
  have hp := (((Patch.refl (literalProgram b3Source : Straight n s s)).joinLiteral
    (b2Patch n s)).joinLiteral (b1Patch n s)).castSaving (show 0+224+98=322 by omega)
  simpa only [List.append_assoc] using hp

def reverseStepPatch (n start T : Nat) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 714 := by
  unfold measuredInverseStepProgram measuredInverseStepSegments
  refine (Patch.sequenceCons (d := 0) (f := 714) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 714) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 42) (f := 672) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 672) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 672) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 672) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 154) (f := 518) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseCombinedPatch n _ (certifiedActiveWindows 256 T).quotientSwap
  refine (Patch.sequenceCons (d := 0) (f := 518) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 322) (f := 196) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseRemainderPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 196) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 196) (f := 0) _ _
    (((b1Patch n _).joinLiteral (aInversePatch n _)).castSaving (by omega)) (Patch.refl _)).castSaving (by omega)

def reverseSchedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredInverseScheduleProgram n indexedStepProductionRegisters count first start).2 (count*714)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredInverseScheduleProgram]
    exact (Patch.appendCompiled _ _ (reverseSchedulePatch n count (first+1) start)
      (reverseStepPatch n _ first)).castSaving (by omega)

def eeaReversePatch (n start : Nat) :
    Patch (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 1156680 := by
  unfold measuredEEAReverseProgram
  exact reverseSchedulePatch n 1620 1 start

def reverseWrapperPatch (n start : Nat) :
    Patch (measuredReverseWrapperProgram n start).2 1156680 := by
  unfold measuredReverseWrapperProgram measuredReverseWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 1156680) (f := 0) _ _ (eeaReversePatch n _) (Patch.refl _)).castSaving (by omega)

def Patch.relabelCompiled {n start d} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.relabelCompiled e p).2 d :=
  hp.relabel e

def forwardDataPatch (n start : Nat) : Patch (measuredForwardDataBankProgram n start).2 1156680 := by
  unfold measuredForwardDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (wrapperPatch n start)

def reverseDataPatch (n start : Nat) : Patch (measuredReverseDataBankProgram n start).2 1156680 := by
  unfold measuredReverseDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (reverseWrapperPatch n start)

def collectPatch {n d}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hp : ∀ cursor prior, Patch (next cursor prior).2 d) :
    (ws : List Wire) → (start : Nat) → (prior : List (Fin start)) →
      Patch (collectProgram n next ws start prior).2 d
  | [], start, prior => by simpa only [collectProgram] using hp start prior
  | w::ws, start, prior => by
    simp only [collectProgram]
    exact (Patch.measure w (collectPatch next hp ws (start+1) _)).castFinish _

def divisionAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (divisionAfterResetProgram n start prior).2 1156680 := by
  unfold divisionAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 1156680) (f := 0) _ _
    ((Patch.appendCompiled (d := 1156680) (f := 0) _ _ (reverseDataPatch n start) (Patch.refl _)).castSaving (by omega))
    (Patch.refl _)).castSaving (by omega)

def divisionPatch (n start : Nat) : Patch (divisionProgram n start).2 2313360 := by
  unfold divisionProgram
  exact (Patch.appendCompiled (d := 1156680) (f := 1156680) _ _
    ((Patch.appendCompiled (d := 1156680) (f := 0) _ _ (wrapperPatch n start) (Patch.refl _)).castSaving (by omega))
    (collectPatch _ (divisionAfterResetPatch n) _ _ _)).castSaving (by omega)

def multiplicationCleanupPatch (n start : Nat) :
    Patch (multiplicationCleanupProgram n start).2 1156680 := by
  unfold multiplicationCleanupProgram appendLiteral
  exact (Patch.appendCompiled (d := 0) (f := 1156680) _ _ (Patch.refl _)
    ((Patch.appendCompiled (d := 1156680) (f := 0) _ _ (reverseDataPatch n _) (Patch.refl _)).castSaving (by omega))).castSaving (by omega)

def multiplicationCorrectionPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationCorrectionProgram n start prior).2 1156680 := by
  unfold multiplicationCorrectionProgram
  exact (Patch.appendCompiled (d := 0) (f := 1156680)
    (correctionCompiled n start (List.range' 580 256) prior) (multiplicationCleanupProgram n start)
    (Patch.refl _) (multiplicationCleanupPatch n start)).castSaving (show 0+1156680=1156680 by omega)

def multiplicationAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationAfterResetProgram n start prior).2 2313360 := by
  unfold multiplicationAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 1156680) (f := 1156680) _ _
    ((Patch.appendCompiled (d := 1156680) (f := 0) _ _ (forwardDataPatch n _) (Patch.refl _)).castSaving (by omega))
    (multiplicationCorrectionPatch n _ _)).castSaving (by omega)

def multiplicationPatch (n start : Nat) : Patch (multiplicationProgram n start).2 2313360 := by
  unfold multiplicationProgram
  exact (Patch.appendCompiled (d := 0) (f := 2313360) _ _ (Patch.refl _)
    (collectPatch _ (multiplicationAfterResetPatch n) _ _ _)).castSaving (by omega)




end
end ShorECDLP.Entrant.Optimization
namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] sequenceProgram appendCompiled literalProgram ShorECDLP.Paper2607_13816.ChallengeMigration.tailCoordinateProgram ShorECDLP.Entrant.BorrowFlag.divisionProgram ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  Single.axis Rounded.entry

def borrowedFieldPatch {saving : Nat} (n start : Nat) (arithmetic : FixedSegment n)
    (hp : ∀ cursor, Patch (arithmetic cursor).2 saving) :
    Patch (ShorECDLP.Entrant.BorrowFlag.fieldProgram n start arithmetic).2 saving := by
  unfold ShorECDLP.Entrant.BorrowFlag.fieldProgram
  apply Patch.surroundCompiled
  unfold ShorECDLP.Entrant.BorrowFlag.coreSegments
  refine (Patch.sequenceCons (d := 0) (f := saving) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := saving) (f := 0) _ _ (hp _) (Patch.refl _)).castSaving (by omega)

def zeroDivisionPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.BorrowFlag.divisionProgram n start).2 2313360 := by
  unfold ShorECDLP.Entrant.BorrowFlag.divisionProgram
  exact borrowedFieldPatch n start (divisionProgram n) (divisionPatch n)

def zeroMultiplicationPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.BorrowFlag.multiplicationProgram n start).2 2313360 := by
  unfold ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  exact borrowedFieldPatch n start (multiplicationProgram n) (multiplicationPatch n)

def coordinatePatch (start : Nat) : Patch (ShorECDLP.Paper2607_13816.ChallengeMigration.tailCoordinateProgram start).2 4626720 := by
  unfold ShorECDLP.Paper2607_13816.ChallengeMigration.tailCoordinateProgram ShorECDLP.Paper2607_13816.ChallengeMigration.tailCoordinateSegments
  refine (Patch.sequenceCons (d := 0) (f := 4626720) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 4626720) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 2313360) (f := 2313360) _ _ (zeroDivisionPatch 32768 _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2313360) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2313360) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 2313360) (f := 0) _ _ (zeroMultiplicationPatch 32768 _) (Patch.refl _)).castSaving (by omega)

def corePatch (start : Nat) : Patch (Single.Physical.core start).2 4626720 := by
  unfold Single.Physical.core Single.Physical.segments
  exact (Patch.sequenceCons (d := 4626720) (f := 0) _ _ (coordinatePatch start) (Patch.refl _)).castSaving (by omega)

def preparedPatch (start : Nat) : Patch (Single.Physical.prepared start).2 4626720 := by
  unfold Single.Physical.prepared
  exact Patch.surroundCompiled _ _ _ (corePatch start)

def actualPatch (start : Nat) : Patch (Single.Physical.actual.program start) 4626720 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedPatch 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def signedPatch (w : Single.SignedWindow) (start : Nat) :
    Patch ((Single.signedWindow w).program start) 4626720 := by
  unfold Single.signedWindow
  exact (actualPatch start).reindex (Single.signedRow w)

def preparePatch {n s e d} (ws : List Wire) {p : Straight n s e} (hp : Patch p d) :
    Patch (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact Patch.gate (.literal (.H w)) ih

structure PatchedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  patch : ∀ start, Patch (source.program start) saving

def leftPatches : List (PatchedWindow 901120) :=
  ⟨Single.firstWindow,0,fun _ => Patch.refl _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,4626720,signedPatch w⟩)
def rightPatches : List (PatchedWindow 901120) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,4626720,signedPatch w⟩)
private theorem leftPatches_source : leftPatches.map PatchedWindow.source = Single.leftWindows := by
  simp [leftPatches, Single.leftWindows]
private theorem rightPatches_source : rightPatches.map PatchedWindow.source = Single.rightWindows := by
  simp [rightPatches, Single.rightWindows]
private theorem leftPatches_saving : (leftPatches.map PatchedWindow.saving).sum = 74027520 := by
  simp [leftPatches, Single.leftSigned]
private theorem rightPatches_saving : (rightPatches.map PatchedWindow.saving).sum = 64774080 := by
  simp [rightPatches, Single.rightSigned]

def axisPatch {n} : (ps : List (PatchedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    Patch (Single.axis (ps.map PatchedWindow.source) start prior) ((ps.map PatchedWindow.saving).sum)
  | [], _, _ => Patch.refl _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine Patch.castFinish ?_ _
    refine Patch.castSaving (Patch.append (f := (ps.map PatchedWindow.saving).sum) (preparePatch _ (p.patch start)) ?_) (by omega)
    exact (Patch.append (Patch.refl _) (axisPatch ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castSaving (by omega)

def axisPatchFor {n} (ps : List (PatchedWindow n)) (ws : List (Single.Window n))
    (he : ps.map PatchedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    Patch (Single.axis ws start prior) ((ps.map PatchedWindow.saving).sum) := by
  subst ws
  exact axisPatch ps start prior

def Patch.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : Patch p dl) (hq : Patch q dr) :
    Patch (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact Patch.gate _ ((Patch.append hp ((Patch.append hq (Patch.gate _ (Patch.refl _))).castSaving (Nat.add_zero dr))).castFinish h)

def trialPatch (start : Nat) : Patch (Single.trial start) 138801600 := by
  have hl := (axisPatchFor leftPatches Single.leftWindows leftPatches_source start List.nil).castSaving leftPatches_saving
  have hr := (axisPatchFor rightPatches Single.rightWindows rightPatches_source
    (start+Single.axisCount Single.leftWindows) List.nil).castSaving rightPatches_saving
  unfold Single.trial
  exact (Patch.framed _ _ _ _ hl hr).castSaving (by decide)

def programPatch : Patch Single.program 138801600 := by
  unfold Single.program
  exact (trialPatch 0).castFinish _

def Patch.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : Patch p d) :
    Patch (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

def entryPatch : Patch Rounded.entry.program 138801600 := by
  unfold Rounded.entry Rounded.program
  exact Patch.fixedEntry Single.mixedCoefficientAt _
    ((Patch.append programPatch (Patch.refl Rounded.readout)).castSaving (by omega))
end
end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.Parent
open Challenge
noncomputable def entry : StraightEntry := Optimization.replaceEntry Rounded.entry Optimization.entryPatch.program
def layout : DecodeLayout := Rounded.layout
def bounds : Bounds := ⟨Rounded.bounds.qubits, Rounded.bounds.tModel - 138801600, Rounded.bounds.measurements⟩
theorem certificate : Certificate officialLimits layout entry bounds :=
  Optimization.replacement_certificate Rounded.certificate Optimization.entryPatch.drops Optimization.entryPatch.rewrites
end ShorECDLP.Entrant.Parent
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option Elab.async false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram tailCoordinateProgram
  ShorECDLP.Entrant.BorrowFlag.fieldProgram ShorECDLP.Entrant.BorrowFlag.divisionProgram
  ShorECDLP.Entrant.BorrowFlag.multiplicationProgram Single.axis Rounded.entry

theorem AtLeast.gate {n s e d} (g : TemplateGate n) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (.gate g p) d := by
  cases g with
  | literal g => cases g <;> simp_all [AtLeast, added] <;> omega
  | whenBit => exact hp

def templateCCX {n} : List (TemplateGate n) → Nat
  | [] => 0
  | .literal (.CCX _ _ _) :: gs => 1 + templateCCX gs
  | _ :: gs => templateCCX gs

def lookupCCX {n} : List (LookupOp n) → Nat
  | [] => 0
  | .gates gs :: ops => templateCCX gs + lookupCCX ops
  | .erase _ _ _ :: ops => lookupCCX ops

theorem added_gateProgram {n s} (gs : List (TemplateGate n)) :
    added (gateProgram gs : Straight n s s) = templateCCX gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g with
    | literal g => cases g <;> simp_all [gateProgram,added,templateCCX]
    | whenBit => simp_all [gateProgram,added,templateCCX]

theorem added_andErase (n s a b t : Nat) : added (andEraseProgram n s a b t) = 0 := by
  simp [andEraseProgram,recordGates,controlledZ,added]

theorem added_lookupProgram {n} (ops : List (LookupOp n)) (start : Nat) :
    added (lookupProgram n ops start) = lookupCCX ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih => cases op <;>
      simp [lookupProgram,lookupCCX,added_append,added_cast,added_gateProgram,added_andErase,ih]

theorem lookupCCX_append {n} (a b : List (LookupOp n)) :
    lookupCCX (a++b) = lookupCCX a + lookupCCX b := by
  induction a with
  | nil => simp [lookupCCX]
  | cons op ops ih => cases op <;> simp [lookupCCX,ih,Nat.add_assoc]

theorem templateCCX_literal {n} (gs : Circuit) :
    @templateCCX n (gs.map TemplateGate.literal) = ccxCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [templateCCX,ccxCount,ih,Nat.add_comm]

theorem lookupCCX_unary_ge {n} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) (hl : tree.Layout q anc) :
    tree.internalNodes ≤ lookupCCX (unaryLookupOps leaf tree q anc) := by
  induction hl with
  | leaf l q anc hn => simp [unaryLookupOps,UnaryActionTree.internalNodes,lookupCCX]
  | node bit q path zero one rest hn hz ho ihz iho =>
    simp only [unaryLookupOps,lookupCCX_append,lookupCCX,ordinaryOp,templateCCX_literal,
      computeZeroAnd,ccxCount,UnaryActionTree.internalNodes] at *
    omega

theorem lookup_count {n} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) (hl : tree.Layout q anc) (start : Nat) :
    AtLeast (lookupProgram n (unaryLookupOps leaf tree q anc) start) tree.internalNodes := by
  unfold AtLeast
  rw [added_lookupProgram]
  exact lookupCCX_unary_ge leaf tree q anc hl


section
-- Append inside AndGadget after Core.lean.
attribute [local irreducible] added fieldLookupAddProgram signedFieldProgram fieldLoadProgram modularAddProgram yNegateProgram

theorem fieldLoadCount (field : PointField) (start : Nat) :
    AtLeast (fieldLoadProgram field start) 32767 := by
  unfold fieldLoadProgram AtLeast
  rw [added_cast]
  unfold fieldLoadOps
  rw [added_lookupProgram]
  have h := lookupCCX_unary_ge
    (fun l q => fieldLeaf ⟨l%32768,Nat.mod_lt _ (by decide)⟩ field q)
    (tableAddressTree pointLookupAddress 0 1) 836 pointLookupPath
    (tableAddressTree_layout _ _ _ _ _ (by decide) (by decide))
  have hn := batchWindowTree_nodes
  unfold batchWindowTree at hn
  omega

theorem fieldAddCount (field : PointField) (acc : List Wire) (start : Nat) :
    AtLeast (fieldLookupAddProgram field acc start).2 65534 := by
  unfold fieldLookupAddProgram
  dsimp only
  refine (AtLeast.appendCompiled (d := 32767) (f := 32767) _ _ (fieldLoadCount field _) ?_).castCount (by omega)
  exact (AtLeast.appendCompiled (d := 0) (f := 32767) _ _ (AtLeast.zero _) (fieldLoadCount field _)).castCount (by omega)

theorem signedFieldCount (field : PointField) (start : Nat) :
    AtLeast (signedFieldProgram field start).2 65534 := by
  unfold signedFieldProgram
  dsimp only
  refine (AtLeast.appendCompiled (d := 0) (f := 65534) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.appendCompiled (d := 65534) (f := 0) _ _ (fieldAddCount field _ _) (AtLeast.zero _)).castCount (by omega)

theorem ipxLookupCount_ge {n} (rows : Nat → Fin n) (tree : UnaryActionTree)
    (paths : List Wire) (hl : ∀ c, tree.Layout (ipxControl c) paths) (ops : List IpxOp) :
    ipxQueries ops * tree.internalNodes ≤ lookupCCX (ipxOps rows tree paths ops) := by
  induction ops with
  | nil => simp [ipxQueries,ipxOps,lookupCCX]
  | cons op ops ih => cases op with
    | query c u v =>
      have h := lookupCCX_unary_ge (fun l q => ipxLeaf (rows l) q u v) tree (ipxControl c) paths (hl c)
      simp only [ipxOps,lookupCCX_append,ipxQueries,Nat.add_mul,Nat.one_mul]
      omega
    | test k =>
      simp only [ipxOps,lookupCCX_append,ipxQueries]
      omega

theorem correctionQueryCount (start : Nat) :
    AtLeast (Single.Physical.placedProgram start).2 425971 := by
  unfold Single.Physical.placedProgram ipxProgramOf AtLeast
  rw [added_lookupProgram]
  have h := ipxLookupCount_ge Single.Physical.tableRows batchWindowTree pointLookupPath ipxTree_layout ipxSchedule
  rw [ipxSchedule_queries,batchWindowTree_nodes] at h
  exact h

end
attribute [local irreducible] fieldLookupAddProgram signedFieldProgram fieldLoadProgram modularAddProgram yNegateProgram
theorem borrowedFieldCount (n start d : Nat) (arithmetic : FixedSegment n)
    (hc : ∀ cursor, AtLeast (arithmetic cursor).2 d) :
    AtLeast (ShorECDLP.Entrant.BorrowFlag.fieldProgram n start arithmetic).2 d := by
  unfold ShorECDLP.Entrant.BorrowFlag.fieldProgram
  apply AtLeast.surroundCompiled
  unfold ShorECDLP.Entrant.BorrowFlag.coreSegments
  refine (AtLeast.sequenceCons (d := 0) (f := d) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := d) (f := 0) _ _ (hc _) (AtLeast.zero _)).castCount (by omega)

theorem borrowedDivisionCount (n start : Nat) :
    AtLeast (ShorECDLP.Entrant.BorrowFlag.divisionProgram n start).2 31544978 := by
  unfold ShorECDLP.Entrant.BorrowFlag.divisionProgram
  exact borrowedFieldCount n start 31544978 _ (divisionBothCount n)

theorem borrowedMultiplicationCount (n start : Nat) :
    AtLeast (ShorECDLP.Entrant.BorrowFlag.multiplicationProgram n start).2 31544978 := by
  unfold ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  exact borrowedFieldCount n start 31544978 _ (multiplicationBothCount n)

theorem tailAllCount (start : Nat) : AtLeast (tailCoordinateProgram start).2 63417626 := by
  unfold tailCoordinateProgram tailCoordinateSegments
  refine (AtLeast.sequenceCons (d := 65534) (f := 63352092) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 63286558) _ _ (signedFieldCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 31544978) (f := 31741580) _ _ (borrowedDivisionCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 31741580) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 31676046) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 31544978) (f := 131068) _ _ (borrowedMultiplicationCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 131068) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 65534) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 65534) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 0) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  exact AtLeast.zero _

theorem coreCount (start : Nat) : AtLeast (Single.Physical.core start).2 63843597 := by
  unfold Single.Physical.core Single.Physical.segments
  refine (AtLeast.sequenceCons (d := 63417626) (f := 425971) _ _ (tailAllCount start) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 425971) (f := 0) _ _ (correctionQueryCount _) (AtLeast.zero _)).castCount (by omega)

theorem preparedCount (start : Nat) : AtLeast (Single.Physical.prepared start).2 63843597 := by
  unfold Single.Physical.prepared
  exact AtLeast.surroundCompiled _ _ _ (coreCount start)

theorem actualCount (start : Nat) : AtLeast (Single.Physical.actual.program start) 63843597 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedCount 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

theorem signedCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) 63843597 := by
  unfold Single.signedWindow
  exact (actualCount start).reindex (Single.signedRow w)

theorem prepareCount {n s e d} (ws : List Wire) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact AtLeast.gate (.literal (.H w)) ih

structure CountedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  countProof : ∀ start, AtLeast (source.program start) saving

def leftCountes : List (CountedWindow 901120) :=
  ⟨Single.firstWindow,0,fun _ => AtLeast.zero _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,63843597,signedCount w⟩)
def rightCountes : List (CountedWindow 901120) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,63843597,signedCount w⟩)
private theorem leftCountes_source : leftCountes.map CountedWindow.source = Single.leftWindows := by
  simp [leftCountes, Single.leftWindows]
private theorem rightCountes_source : rightCountes.map CountedWindow.source = Single.rightWindows := by
  simp [rightCountes, Single.rightWindows]
private theorem leftCountes_saving : (leftCountes.map CountedWindow.saving).sum = 1021497552 := by
  simp [leftCountes, Single.leftSigned]
private theorem rightCountes_saving : (rightCountes.map CountedWindow.saving).sum = 893810358 := by
  simp [rightCountes, Single.rightSigned]

theorem axisCountProof {n} : (ps : List (CountedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    AtLeast (Single.axis (ps.map CountedWindow.source) start prior) ((ps.map CountedWindow.saving).sum)
  | [], _, _ => AtLeast.zero _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine AtLeast.castFinish ?_ _
    refine AtLeast.castCount (AtLeast.append (f := (ps.map CountedWindow.saving).sum) (prepareCount _ (p.countProof start)) ?_) (by omega)
    exact (AtLeast.append (AtLeast.zero _) (axisCountProof ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castCount (by omega)

theorem axisCountFor {n} (ps : List (CountedWindow n)) (ws : List (Single.Window n))
    (he : ps.map CountedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    AtLeast (Single.axis ws start prior) ((ps.map CountedWindow.saving).sum) := by
  subst ws
  exact axisCountProof ps start prior

theorem AtLeast.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : AtLeast p dl) (hq : AtLeast q dr) :
    AtLeast (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact AtLeast.gate _ ((AtLeast.append hp ((AtLeast.append hq (AtLeast.gate _ (AtLeast.zero _))).castCount (Nat.add_zero dr))).castFinish h)

theorem trialCount (start : Nat) : AtLeast (Single.trial start) 1915307910 := by
  have hl := (axisCountFor leftCountes Single.leftWindows leftCountes_source start List.nil).castCount leftCountes_saving
  have hr := (axisCountFor rightCountes Single.rightWindows rightCountes_source
    (start+Single.axisCount Single.leftWindows) List.nil).castCount rightCountes_saving
  unfold Single.trial
  exact (AtLeast.framed _ _ _ _ hl hr).castCount (by decide)

theorem programCount : AtLeast Single.program 1915307910 := by
  unfold Single.program
  exact (trialCount 0).castFinish _

theorem AtLeast.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : AtLeast p d) :
    AtLeast (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

theorem entryCount : AtLeast Rounded.entry.program 1915307910 := by
  unfold Rounded.entry Rounded.program
  apply AtLeast.fixedEntry
  exact ((AtLeast.append programCount (AtLeast.zero Rounded.readout)).castCount (by omega))

theorem dropped_added {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d) :
    7 * added p ≤ 7 * added q + d := by
  induction h with
  | refl => omega
  | skip g h ih => cases g <;> simp_all [added, tCost] <;> omega
  | gate g h ih =>
    cases g with
    | literal g => cases g <;> simp_all [added] <;> omega
    | whenBit => exact ih
  | record => assumption
  | measure => assumption

attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch



theorem parent_added_lower : 1895479110 ≤ added Parent.entry.program := by
  have h := dropped_added Optimization.entryPatch.drops
  have hc := entryCount
  change 1915307910 ≤ added Rounded.entry.program at hc
  unfold Parent.entry Optimization.replaceEntry
  change 1895479110 ≤ added Optimization.entryPatch.program
  omega
theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) (ws : List Wire)
    (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hp.2⟩
  | measure => exact ⟨hp.1, by apply_assumption; exact hp.2⟩


theorem within_drops {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d)
    (ws : List Wire) (hp : Within ws p) : Within ws q := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ⟨hp.1, ih hp.2⟩


theorem fixedEntry_within {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (ws : List Wire) (hp : Within ws p) : Within ws (Single.fixedEntry f p).program :=
  within_reindex p _ ws hp


attribute [local irreducible] Within

theorem parent_within : Within resetWires Parent.entry.program := by
  unfold Parent.entry Optimization.replaceEntry
  apply within_drops Optimization.entryPatch.drops
  unfold Rounded.entry
  apply fixedEntry_within
  apply within_of_instantiate
  intro read history
  have he : history = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst history
  exact Rounded.program_support read


set_option maxRecDepth 2000

theorem parent_added_upper : added Parent.entry.program ≤ 7629176572 := by
  have h := lower_t 1024 Parent.entry.program 0 Fin.elim0
    (readConstant Parent.entry.coefficients.get 0) Fin.elim0 Fin.elim0
    (by funext i; exact Fin.elim0 i)
  have ht := (Parent.certificate.resources 0).2.1
  change (Parent.entry.program.instantiate (readConstant Parent.entry.coefficients.get 0) Fin.elim0).tCount ≤ 15258353144 at ht
  omega


theorem parent_slots : Parent.entry.program.gateSlots ≤ 93000061339 := by
  have hs := Optimization.entryPatch.drops.slots
  have ho : Rounded.entry.program.gateSlots ≤ 93000061339 := by
    rw [Rounded.entry, Single.fixedEntry_slots]
    exact Rounded.program_slots
  unfold Parent.entry Optimization.replaceEntry
  exact hs.trans ho

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant
open Challenge AndGadget Paper2607_13816.ChallengeMigration
attribute [local irreducible] Within
set_option maxRecDepth 10000
attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch
noncomputable def entry : StraightEntry := lowerEntry 1024 Parent.entry
noncomputable def layout : DecodeLayout := lowerLayout 1024 Parent.entry Parent.layout
def bounds : Bounds := ⟨855, 11467394924, 8550418124⟩

private theorem resourceArithmetic (a slots cursor oldT newT maxSlots maxRecords newRecords : Nat)
    (ha : a ≤ 7629176572) (hl : 1895479110 ≤ a) (hs : slots ≤ 93000061339)
    (hc : cursor ≤ 921241552) (ho : oldT ≤ 15258353144) (hn : 11467394924 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hlm : 47471340504 ≤ maxRecords)
    (hnm : 8550418124 ≤ newRecords) :
    slots + 18*a ≤ maxSlots ∧ cursor+a ≤ maxRecords ∧ oldT ≤ newT + 2*a ∧
    cursor+a ≤ newRecords := by omega

theorem certificate : Certificate officialLimits layout entry bounds := by
  have h := resourceArithmetic (added Parent.entry.program) Parent.entry.program.gateSlots
    Parent.entry.finalCursor Parent.bounds.tModel bounds.tModel officialLimits.gateSlots
    officialLimits.measurements bounds.measurements
    parent_added_upper parent_added_lower parent_slots (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  apply lower_certificate officialLimits Parent.layout Parent.entry Parent.bounds bounds
    1024 resetWires Parent.certificate parent_within
  · simp [resetWires]
  · exact h.1
  · exact h.2.1
  · change resetWires.length + 1 ≤ 855
    rw [resetWires_length]
  · exact h.2.2.1
  · exact h.2.2.2
end ShorECDLP.Entrant
end
