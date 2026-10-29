import ShorECDLP.Submission.Entrant.Streaming.Resources
import ShorECDLP.Submission.Entrant.Streaming.Semantics
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
import ShorECDLP.Submission.«2607_13816».Window.PhysicalRepetition

/-! EDITABLE. Streaming entrant, module `Certificate`: the round-count instantiation, retry event and final certificate.

This module concatenates the former per-file modules `Rounds`, `ResourceCertificate`,
`RoundReset`, `RepeatEvent`, `FinalCertificate` (in this order). Each former file is one
`namespace` block below, marked `-- ==== part: <Name> ====`, with its provenance note. Only the
import lines changed.

Why few modules: the kernel replay loads the complete import closure (about 4.3 GB) once per
Entrant module, in parallel across its worker threads, so its peak memory grows with the number
of Entrant modules. -/

-- ==== part: Rounds ====

/-! EDITABLE. Decoder layout for an entry with fewer outer rounds.

The protected `OuterPlan.layout` reads 56 rounds. The entrant runs only the first `k ≤ 56`
rounds of the same outer plan, so its layout keeps exactly the first `k` protected trial
position vectors, unchanged. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The protected wrappedShift layout restricted to its first `k` trials. -/
def OuterPlan.roundsLayout {n : Nat} (p : OuterPlan n) (k : Nat) (hk : k ≤ 56) : DecodeLayout :=
  ⟨.wrappedShift, legacyDecoderParams,
    List.ofFn (fun r : Fin k => p.positions (Fin.castLE hk r)), by simpa using hk⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: ResourceCertificate ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ResourceCertificate.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] ipxOuterPlan coefficientTable OuterPlan.repeat

/-- Generic packaging avoids unfolding a large coefficient table to transport its length. -/
def fixedTableEntry {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) : StraightEntry where
  coefficients := List.ofFn f
  finalCursor := e
  program := reindexStraight (Fin.cast List.length_ofFn.symm) p

private theorem ofFn_read {n : Nat} (f : Fin n → PointCoeff) (Q : Point) :
    (fun r : ConstantBit n => readConstant (List.ofFn f).get Q
      ⟨Fin.cast (List.length_ofFn).symm r.point, r.field, r.bit⟩) =
      readConstant f Q := by
  funext r
  simp only [readConstant,List.get_eq_getElem,List.getElem_ofFn,Fin.val_cast,Fin.eta]

theorem fixedTableEntry_instantiate {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (fixedTableEntry f p).instantiate Q = p.instantiate (readConstant f Q) Fin.elim0 := by
  dsimp only [fixedTableEntry,StraightEntry.instantiate]
  rw [reindexStraight_instantiate]
  simp only [Function.comp_def,reindexBit]
  rw [ofFn_read]

theorem fixedTableEntry_slots {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).program.gateSlots = p.gateSlots :=
  reindexStraight_gateSlots _ _

theorem fixedTableEntry_wellFormed {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).program.WellFormed ↔ p.WellFormed :=
  reindexStraight_wellFormed _ _

theorem fixedTableEntry_cursor {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).finalCursor = e := rfl

theorem fixedTableEntry_rows {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).coefficients.length = n := List.length_ofFn

private theorem resource_t (c : AdaptiveCircuit) : (resources c).tModel = c.tCount := rfl
private theorem resource_m (c : AdaptiveCircuit) : (resources c).measurements = c.measurementCount := rfl
private theorem resource_q (c : AdaptiveCircuit) : (resources c).qubits = c.qubitCount := rfl

theorem fixedTableEntry_measurements {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (resources ((fixedTableEntry f p).instantiate Q)).measurements = e := by
  rw [resource_m,fixedTableEntry_instantiate,Straight.measurementCount,Nat.sub_zero]

/-- The entrant's fixed producer: the first 6 rounds of the 56-round outer plan,
using the public coefficient table. -/
def streamingEntry : StraightEntry := fixedTableEntry coefficientAt (ipxOuterPlan.repeat 6 0)

/-- The protected wrappedShift layout restricted to the 6 actual rounds. -/
def streamingLayout : DecodeLayout := ipxOuterPlan.roundsLayout 6 (by decide)

theorem streamingEntry_instantiate (Q : Point) :
    streamingEntry.instantiate Q =
      (ipxOuterPlan.repeat 6 0).instantiate (readConstant coefficientAt Q) Fin.elim0 :=
  fixedTableEntry_instantiate _ _ Q

attribute [local irreducible] streamingEntry fixedTableEntry

/-- Upper bounds; the qubit bound is not an exact cardinality claim. -/
def streamingBounds : Bounds := ⟨855,86231444094,5159320422⟩

theorem streamingEntry_qubitCount (Q : Point) :
    (streamingEntry.instantiate Q).qubitCount ≤ 855 := by
  rw [streamingEntry_instantiate]
  simpa only [AdaptiveCircuit.qubitCount,List.card_toFinset] using
    ipxOuter_qubits_le_855 6 0 (readConstant coefficientAt Q) Fin.elim0

theorem streamingEntry_tModel (Q : Point) :
    (resources (streamingEntry.instantiate Q)).tModel ≤ 86231444094 := by
  rw [resource_t,streamingEntry_instantiate]
  exact ipxOuterPlan_rounds_t_uniform Q

theorem streamingEntry_measurements (Q : Point) :
    (resources (streamingEntry.instantiate Q)).measurements = 5159320422 := by
  rw [streamingEntry,fixedTableEntry_measurements,Nat.zero_add]
  exact ipxOuterPlan_finalCursor6

theorem streamingEntry_resources (Q : Point) :
    (resources (streamingEntry.instantiate Q)).qubits ≤ streamingBounds.qubits ∧
    (resources (streamingEntry.instantiate Q)).tModel ≤ streamingBounds.tModel ∧
    (resources (streamingEntry.instantiate Q)).measurements ≤ streamingBounds.measurements := by
  rw [resource_q]
  exact ⟨streamingEntry_qubitCount Q,streamingEntry_tModel Q,(streamingEntry_measurements Q).le⟩

theorem streamingEntry_gateSlots : streamingEntry.program.gateSlots ≤ 5000000000000 := by
  simpa only [streamingEntry,fixedTableEntry_slots] using ipxOuterPlan_rounds_slots 0

theorem streamingEntry_gateBudget : streamingEntry.program.gateSlots ≤ officialLimits.gateSlots :=
  streamingEntry_gateSlots.trans (by decide)

theorem streamingEntry_finalCursor : streamingEntry.finalCursor = 5159320422 := by
  unfold streamingEntry
  exact (fixedTableEntry_cursor coefficientAt (ipxOuterPlan.repeat 6 0)).trans
    ((Nat.zero_add _).trans ipxOuterPlan_finalCursor6)

theorem streamingEntry_recordBudget : streamingEntry.finalCursor ≤ officialLimits.measurements :=
  streamingEntry_finalCursor.le.trans (by decide)

theorem streamingEntry_tableBudget : streamingEntry.coefficients.length ≤ officialLimits.coefficientRows := by
  rw [streamingEntry,fixedTableEntry_rows]
  exact Nat.le_refl _

theorem streamingEntry_candidateBudget :
    streamingLayout.trials.length *
      decoderCandidateLimit streamingLayout.kind streamingLayout.params ≤
      officialLimits.candidateChecks := by
  exact streaming_candidate_budget streamingLayout rfl rfl

theorem streamingEntry_wellFormed : streamingEntry.program.WellFormed := by
  rw [streamingEntry]
  exact (fixedTableEntry_wellFormed _ _).mpr (ipxOuterPlan_repeat_wellFormed 6 0)

/-- Only success remains an input: all physical, syntactic and resource fields
refer to this actual fixed entry. This conditional shell is not an accepted submission. -/
theorem streamingEntry_certificate
    (success : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q = d • G →
      (99 : ℝ)/100 ≤ Instrument.bornMass
        ((streamingEntry.instantiate Q).run.filter
          (fun b => (verifiedCandidate streamingLayout Q b.history).isSome))
        (ket zeroBasisState)) :
    Certificate officialLimits streamingLayout streamingEntry streamingBounds where
  gateBudget := streamingEntry_gateBudget
  recordBudget := streamingEntry_recordBudget
  tableBudget := streamingEntry_tableBudget
  candidateBudget := streamingEntry_candidateBudget
  wellFormed := streamingEntry_wellFormed
  resources := streamingEntry_resources
  success := success
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: RoundReset ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/RoundReset.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] actualFirstSource actualOddSource streamAddress fourierOutcomes Quantum.run ipxOuterPlan actualFirstWindow actualIpxWindow

theorem ipxResetWires_nodup : resetWires.Nodup := by
  simp only [resetWires,List.nodup_append,List.nodup_range,
    List.nodup_range' 1, List.nodup_singleton,true_and]
  simp only [List.mem_append,List.mem_range,List.mem_range'_1,List.mem_singleton]
  repeat' constructor
  all_goals intros; dsimp only [Wire] at *; omega

theorem actualRound_support (start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((ipxOuterPlan.round start).instantiate read history).wires ⊆ completeBatchedSupport := by
  apply OuterPlan.round_support
  · intro w hw
    simp only [ipxOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact List.mem_cons_of_mem 837 (List.mem_append_right _ hw)
  · simpa only [ipxOuterPlan,standardOuterPlan] using
      (List.subset_cons_of_subset 837 (List.Subset.refl resetWires))
  · simp [completeBatchedSupport,resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_static window _ cursor
    simpa only [ipxOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

theorem actualRoundTail_clean (b : InstrumentBranch)
    (hb : b ∈ (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection resetWires (fun _ => []))).run) (ψ : State) :
    SupportedOn (Clean resetWires) (b.kraus ψ) := by
  rw [AdaptiveCircuit.run] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  exact resetRegister_clean _ ipxResetWires_nodup c hc _

theorem actualRoundSource_clean (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    SupportedOn (Clean resetWires) (b.kraus (ket zeroBasisState)) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,actualLeftSources_indices,actualRightSources_indices] at hb
  rw [AdaptiveCircuit.run, ← selectedSourceTwoAxes_constant] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  change SupportedOn (Clean resetWires) (c.kraus (Quantum.run [.X 836] (ket zeroBasisState)))
  rw [hx]
  exact actualSourceTwoAxes_supported Q hQ hn leftOddIndices rightOddIndices _ _
    (fun _ _ b hb ψ _ => actualRoundTail_clean b hb ψ) _
    (supportedOn_ket _ _ firstWindowInput_start) c hc

theorem actualCompiledRound_zero_support (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((ipxOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    SupportedOn (fun s => s=zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  intro s hs
  funext w
  by_cases hw : w ∈ resetWires
  · have hb' := hb
    rw [ipxOuterPlan_round_run Q hQ start history] at hb'
    exact actualRoundSource_clean Q hQ hn b hb' s hs w hw
  · by_cases he : w=837
    · subst w
      exact actualCompiledRound_zeroFlag Q hQ hn start history b hb s hs
    · exact AdaptiveCircuit.branch_frame _ w false
        (fun h => (List.mem_cons.mp (actualRound_support start _ history h)).elim he hw)
        b hb (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs

theorem actualCompiledRound_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((ipxOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  supportedZero_scalar _ (actualCompiledRound_zero_support Q hQ hn start history b hb)

theorem actualRoundSource_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  apply actualCompiledRound_zero_branch Q hQ hn 0 Fin.elim0 b
  rwa [ipxOuterPlan_round_run Q hQ]

theorem actualRoundSource_total (Q : Point) (hQ : order • Q=0) :
    (actualRoundSource Q).run.bornMass (ket zeroBasisState)=1 := by
  rw [← ipxOuterPlan_round_run Q hQ 0 Fin.elim0]
  exact AdaptiveCircuit.run_bornMass_eq_one _
    (Straight.instantiate_wellFormed _ _ _ (ipxOuterPlan_round_wellFormed 0)) _ (normSq_ket _)

theorem actualCompiledRepeat_retry_mass (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (count start : Nat) (history : Fin start → Bool) (accept : List Bool → Bool) :
    Instrument.bornMass
      ((((ipxOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run).filter
        (fun b => !repeatWindowFailed (actualRoundSource Q) accept count b.history)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (Instrument.bornMass ((actualRoundSource Q).run.filter (fun b => accept b.history)) (ket zeroBasisState)) count := by
  rw [ipxOuterPlan_repeat_run Q hQ count start history]
  exact repeatWindowSuccess_mass _ accept (actualRoundSource_zero_branch Q hQ hn) (actualRoundSource_total Q hQ) count

theorem actualCompiledRepeat_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (count start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((ipxOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  rw [ipxOuterPlan_repeat_run Q hQ count start history] at hb
  exact repeatWindowProgram_zero _ (actualRoundSource_zero_branch Q hQ hn) count b hb
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: RepeatEvent ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/RepeatEvent.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] ipxOuterPlan actualRoundSource

theorem readWord_append_shift (before history : List Bool) (positions : List Nat) :
    readWord (before ++ history) (positions.map (before.length + ·)) = readWord history positions := by
  induction positions with
  | nil => rfl
  | cons i ps ih =>
    simp only [List.map_cons,readWord,List.getElem?_append_right (show before.length ≤ before.length+i by omega),Nat.add_sub_cancel_left,ih]

theorem readWord_suffix (history suffix : List Bool) (positions : List Nat)
    (h : ∀ i ∈ positions, i < history.length) :
    readWord (history ++ suffix) positions = readWord history positions := by
  induction positions with
  | nil => rfl
  | cons i ps ih =>
    simp only [readWord,List.getElem?_append_left (h i (by simp)),ih (fun j hj => h j (by simp [hj]))]

theorem axisPositions_shift {n : Nat} (ws : List (OuterWindow n)) (start offset : Nat) :
    axisPositions ws (offset+start) = (axisPositions ws start).map (offset+·) := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [axisPositions,List.map_append,Nat.add_assoc,ih]
    congr 1


def planRoundAccept {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (start : Nat) (history : List Bool) : Bool :=
  fixedPairAccept (axisPositions p.left.toList start)
    (axisPositions p.right.toList (start+axisCount p.left.toList)) accept history

theorem planRoundAccept_shift {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (start : Nat) (before history : List Bool) :
    planRoundAccept p accept (before.length+start) (before++history) =
      planRoundAccept p accept start history := by
  simp only [planRoundAccept,fixedPairAccept,Nat.add_assoc,
    axisPositions_shift,readWord_append_shift]

theorem planRoundAccept_suffix {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (history suffix : List Bool) (h : history.length = p.stride) :
    planRoundAccept p accept 0 (history++suffix) = planRoundAccept p accept 0 history := by
  have hl : ∀ i ∈ axisPositions p.left.toList 0, i < history.length := by
    intro i hi
    have := (axisPositions_bounds _ _ _ hi).2
    rw [h]; simp only [OuterPlan.stride]; omega
  have hr : ∀ i ∈ axisPositions p.right.toList (0+axisCount p.left.toList), i < history.length := by
    intro i hi
    have := (axisPositions_bounds _ _ _ hi).2
    rw [h]; simp only [OuterPlan.stride]; omega
  simp only [planRoundAccept,fixedPairAccept,readWord_suffix history suffix _ hl,
    readWord_suffix history suffix _ hr]

def planRepeatAccept {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (count : Nat) (history : List Bool) : Bool :=
  (List.range count).any (fun r => planRoundAccept p accept (r*p.stride) history)

theorem planRepeatAccept_cons {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (count : Nat) (before history : List Bool) (h : before.length=p.stride) :
    planRepeatAccept p accept (count+1) (before++history) =
      (planRoundAccept p accept 0 before || planRepeatAccept p accept count history) := by
  simp only [planRepeatAccept,List.range_succ_eq_map,List.any_cons,List.any_map,
    Nat.zero_mul,planRoundAccept_suffix p accept before history h]
  congr 1
  apply congrArg (List.any (List.range count))
  funext r
  dsimp only [Function.comp_def]
  rw [Nat.succ_mul,← h,Nat.add_comm,planRoundAccept_shift]

private theorem round_records_length {n : Nat} (p : OuterPlan n)
    (read : ConstantBit n → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.round 0).instantiate read Fin.elim0).run) :
    b.history.length = p.stride := by
  have h := straight_history_length _ read Fin.elim0 b hb
  simpa only [Nat.zero_add,Nat.sub_zero] using h

theorem actualRoundSource_records (Q : Point) (hQ : order • Q=0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    b.history.length = ipxOuterPlan.stride := by
  rw [← ipxOuterPlan_round_run Q hQ 0 Fin.elim0] at hb
  exact round_records_length _ _ b hb

theorem planRepeatAccept_retry (Q : Point) (hQ : order • Q=0)
    (accept : Nat → Nat → Bool) (count : Nat) (b : InstrumentBranch)
    (hb : b ∈ (repeatWindowProgram (actualRoundSource Q) count).run) :
    planRepeatAccept ipxOuterPlan accept count b.history =
      !repeatWindowFailed (actualRoundSource Q) (planRoundAccept ipxOuterPlan accept 0) count b.history := by
  induction count generalizing b with
  | zero => rfl
  | succ count ih =>
    rw [repeatWindowProgram,AdaptiveCircuit.run_seq] at hb
    obtain ⟨a,ha,hc⟩ := List.mem_flatMap.mp hb
    obtain ⟨c,hcRun,rfl⟩ := List.mem_map.mp hc
    rw [show (a.seq c).history = a.history++c.history from rfl,
      planRepeatAccept_cons _ _ count _ _ (actualRoundSource_records Q hQ a ha),ih c hcRun]
    simp only [repeatWindowFailed,consumeAdaptiveHistory_run _ a ha,
      List.length_append,Nat.add_sub_cancel_right,List.take_left,Bool.not_and,Bool.not_not]

private theorem find_isSome_any {α : Type} (p : α → Bool) (xs : List α) :
    (xs.find? p).isSome = xs.any p := by
  apply Bool.eq_iff_iff.mpr
  exact List.find?_isSome.trans List.any_eq_true.symm

theorem wrappedLayout_verified_any (params : DecoderParams) (Q : Point)
    (positions : List (TrialPositions params)) (h : positions.length ≤ 56) (history : List Bool) :
    (verifiedCandidate ⟨.wrappedShift,params,positions,h⟩ Q history).isSome =
      positions.any (fun pos => fixedPairAccept pos.left.toList pos.right.toList
        (wrappedPairAccept params Q) history) := by
  classical
  simp only [verifiedCandidate,candidates,find_isSome_any,List.any_flatMap]
  apply List.any_congr rfl
  intro pos
  have hh := wrappedTrial_verified_isSome params Q pos history
  simpa only [verifiedCandidate,candidates,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,find_isSome_any] using hh

theorem OuterPlan.verified_repeat_event {n : Nat} (p : OuterPlan n) (Q : Point) (history : List Bool) :
    (verifiedCandidate p.layout Q history).isSome =
      planRepeatAccept p (wrappedPairAccept legacyDecoderParams Q) 56 history := by
  rw [OuterPlan.layout,wrappedLayout_verified_any]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_ofFn,planRepeatAccept,List.mem_range]
  constructor
  · rintro ⟨pos,⟨r,rfl⟩,hr⟩
    exact ⟨r.val,r.isLt,by simpa only [OuterPlan.positions,Vector.toList,List.toList_toArray,planRoundAccept] using hr⟩
  · rintro ⟨r,hr,haccept⟩
    exact ⟨p.positions ⟨r,hr⟩,⟨⟨r,hr⟩,rfl⟩,by
      simpa only [OuterPlan.positions,Vector.toList,List.toList_toArray,planRoundAccept] using haccept⟩

theorem OuterPlan.verified_rounds_event {n : Nat} (p : OuterPlan n) (k : Nat) (hk : k ≤ 56)
    (Q : Point) (history : List Bool) :
    (verifiedCandidate (p.roundsLayout k hk) Q history).isSome =
      planRepeatAccept p (wrappedPairAccept legacyDecoderParams Q) k history := by
  rw [OuterPlan.roundsLayout,wrappedLayout_verified_any]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_ofFn,planRepeatAccept,List.mem_range]
  constructor
  · rintro ⟨pos,⟨r,rfl⟩,hr⟩
    exact ⟨r.val,r.isLt,by
      simpa only [OuterPlan.positions,Vector.toList,List.toList_toArray,planRoundAccept,
        Fin.val_castLE] using hr⟩
  · rintro ⟨r,hr,haccept⟩
    exact ⟨p.positions (Fin.castLE hk ⟨r,hr⟩),⟨⟨r,hr⟩,rfl⟩,by
      simpa only [OuterPlan.positions,Vector.toList,List.toList_toArray,planRoundAccept,
        Fin.val_castLE] using haccept⟩

private theorem roundAccept_zero {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (history : List Bool) :
    fixedPairAccept (p.positions ⟨0,by decide⟩).left.toList
      (p.positions ⟨0,by decide⟩).right.toList accept history = planRoundAccept p accept 0 history := by
  simp only [OuterPlan.positions,Vector.toList,List.toList_toArray,Nat.zero_mul,planRoundAccept]

theorem actualRoundFixedAccept_eq (accept : Nat → Nat → Bool) (history : List Bool) :
    actualRoundFixedAccept accept history = planRoundAccept ipxOuterPlan accept 0 history :=
  roundAccept_zero _ accept history

theorem actualCompiledRepeat_verified_event (Q : Point) (hQ : order • Q=0)
    (b : InstrumentBranch)
    (hb : b ∈ ((ipxOuterPlan.repeat 56 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run) :
    (verifiedCandidate ipxOuterPlan.layout Q b.history).isSome =
      !repeatWindowFailed (actualRoundSource Q)
        (actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q)) 56 b.history := by
  rw [OuterPlan.verified_repeat_event]
  have hh := planRepeatAccept_retry Q hQ (wrappedPairAccept legacyDecoderParams Q) 56 b
    (by rwa [ipxOuterPlan_repeat_run Q hQ] at hb)
  have he : actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) =
      planRoundAccept ipxOuterPlan (wrappedPairAccept legacyDecoderParams Q) 0 :=
    funext (actualRoundFixedAccept_eq _)
  rw [he]
  exact hh


/-- The protected final decoder tests exactly the independent retry event of the actual 56 rounds. -/
theorem actualCompiledRepeat_verified_mass (Q : Point) (hQ : order • Q=0) (hn : Q≠0) :
    Instrument.bornMass
      ((((ipxOuterPlan.repeat 56 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate ipxOuterPlan.layout Q b.history).isSome)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (Instrument.bornMass ((actualRoundSource Q).run.filter
          (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history)) (ket zeroBasisState)) 56 := by
  have he := List.filter_congr (actualCompiledRepeat_verified_event Q hQ)
  rw [he]
  exact actualCompiledRepeat_retry_mass Q hQ hn 56 0 Fin.elim0 _
/-- The protected final decoder, restricted to the first `k` rounds, tests exactly the
independent retry event of the actual `k`-round program. -/
theorem actualCompiledRounds_verified_event (Q : Point) (hQ : order • Q=0) (k : Nat) (hk : k ≤ 56)
    (b : InstrumentBranch)
    (hb : b ∈ ((ipxOuterPlan.repeat k 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run) :
    (verifiedCandidate (ipxOuterPlan.roundsLayout k hk) Q b.history).isSome =
      !repeatWindowFailed (actualRoundSource Q)
        (actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q)) k b.history := by
  rw [OuterPlan.verified_rounds_event]
  have hh := planRepeatAccept_retry Q hQ (wrappedPairAccept legacyDecoderParams Q) k b
    (by rwa [ipxOuterPlan_repeat_run Q hQ] at hb)
  have he : actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) =
      planRoundAccept ipxOuterPlan (wrappedPairAccept legacyDecoderParams Q) 0 :=
    funext (actualRoundFixedAccept_eq _)
  rw [he]
  exact hh

theorem actualCompiledRounds_verified_mass (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (k : Nat) (hk : k ≤ 56) :
    Instrument.bornMass
      ((((ipxOuterPlan.repeat k 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate (ipxOuterPlan.roundsLayout k hk) Q b.history).isSome))
        (ket zeroBasisState) =
      independentRetrySuccessProbability
        (Instrument.bornMass ((actualRoundSource Q).run.filter
          (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
          (ket zeroBasisState)) k := by
  have he := List.filter_congr (actualCompiledRounds_verified_event Q hQ k hk)
  rw [he]
  exact actualCompiledRepeat_retry_mass Q hQ hn k 0 Fin.elim0 _
end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: FinalCertificate ====

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/FinalCertificate.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] ipxOuterPlan actualRoundSource streamingEntry

theorem publicPoint_order (Q : Point) (d : Nat) (h : Q=d • G) : order • Q=0 := by
  rw [h,smul_comm,generator_nsmul_eq_zero,nsmul_zero]

theorem actualRoundAcceptedMass_le_one (Q : Point) (hQ : order • Q=0) :
    Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState) ≤ 1 := by
  exact (Instrument.bornMass_filter_le _ _ _).trans_eq (actualRoundSource_total Q hQ)

/-- 6 independent rounds suffice: `1 - (23/50)^6 ≥ 99/100` (5 rounds would not). -/
theorem retry6_success :
    (99:ℝ)/100 ≤ independentRetrySuccessProbability ((27:ℝ)/50) 6 := by
  norm_num [independentRetrySuccessProbability]

theorem actualCompiledRounds_success_of_round (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (h : (27:ℝ)/50 ≤ Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState)) :
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((((ipxOuterPlan.repeat 6 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate streamingLayout Q b.history).isSome)) (ket zeroBasisState) := by
  rw [streamingLayout,actualCompiledRounds_verified_mass Q hQ hn 6 (by decide)]
  have hm := independentRetrySuccessProbability_mono 6 (actualRoundAcceptedMass_le_one Q hQ) h
  exact retry6_success.trans hm

/-- Actual single-round accepted mass, with the protected decoder and no loss term. -/
theorem streamingRound_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d • G) :
    (27:ℝ)/50 ≤ Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState) := by
  have hQ := publicPoint_order Q d hd
  rw [actualRoundSource_fixedPair_mass Q hQ hn,selectedIdealTwoAxes_event_eq Q hQ hn]
  exact wrappedIdeal_mass_lower Q G_ne_zero hn hQ d hd

/-- Success of the actual fixed 6-round entry, measured by the protected final decoder. -/
theorem streamingEntry_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((streamingEntry.instantiate Q).run.filter
        (fun b => (verifiedCandidate streamingLayout Q b.history).isSome))
      (ket zeroBasisState) := by
  rw [streamingEntry_instantiate]
  exact actualCompiledRounds_success_of_round Q (publicPoint_order Q d hd) hn
    (streamingRound_success Q d hn hd)

/-- Unconditional protected certificate for the entrant's fixed 6-round streaming program. -/
theorem streamingEntry_certificate_unconditional :
    Certificate officialLimits streamingLayout streamingEntry streamingBounds :=
  streamingEntry_certificate streamingEntry_success
end ShorECDLP.Paper2607_13816.ChallengeMigration
