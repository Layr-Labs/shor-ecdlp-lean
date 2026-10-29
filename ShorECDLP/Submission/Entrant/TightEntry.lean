import ShorECDLP.Submission.Entrant.TightSupport
import ShorECDLP.Challenge.Official

/-! EDITABLE. The Naive round with a tight reset list.

Each round runs the unchanged Naive trial template, observes the two phase
registers and then resets only `tightResetWires` instead of the dense
`List.range 206624` envelope. The protected decoder, the constant table, the
trial template and the success argument are those of the Naive baseline; only
the reset suffix (and hence the record stride) changes. The instantiated
program touches at most 205,856 distinct wires. -/

namespace ShorECDLP.Entrant
open Quantum Secp256k1 Challenge ShorECDLP.NaiveChallenge
noncomputable section

attribute [local irreducible] tightResetWires

/-! ## Straight-line program -/

def tightRoundRaw (cursor : Nat) :
    Straight 512 cursor
      ((cursor + (bitcoinAReg ++ bitcoinBReg).length) + tightResetWires.length) :=
  (observedTrialProgram cursor).append
    (resetWireProgram tightResetWires (cursor + (bitcoinAReg ++ bitcoinBReg).length))

theorem tightRoundEnd (cursor : Nat) :
    ((cursor + (bitcoinAReg ++ bitcoinBReg).length) + tightResetWires.length) =
      cursor + 206368 := by
  have hl : (bitcoinAReg ++ bitcoinBReg).length = 512 := by
    simp only [List.length_append, bitcoinAReg, bitcoinBReg, List.length_range']
  have hf := tightResetWires_length
  omega

def tightRound (cursor : Nat) : Straight 512 cursor (cursor + 206368) :=
  castFinish (tightRoundEnd cursor) (tightRoundRaw cursor)

def tightNative (read : ConstantBit 512 → Bool) : AdaptiveCircuit :=
  (observedNative read).seq (resetNative tightResetWires)

theorem tightRound_instantiate (cursor : Nat) (read : ConstantBit 512 → Bool)
    (history : Fin cursor → Bool) :
    (tightRound cursor).instantiate read history = tightNative read := by
  rw [tightRound, instantiate_castFinish, tightRoundRaw, straight_append_constant _ _ read
    (resetNative tightResetWires) (fun h => resetWireProgram_instantiate _ _ read h),
    observedTrialProgram_instantiate]
  rfl

def tightRepeated : (count cursor : Nat) → Straight 512 cursor (cursor + count * 206368)
  | 0, cursor => castFinish (by omega) .done
  | count + 1, cursor => castFinish (by omega)
      ((tightRound cursor).append (tightRepeated count (cursor + 206368)))

theorem tightRepeated_instantiate (count cursor : Nat) (read : ConstantBit 512 → Bool)
    (history : Fin cursor → Bool) :
    (tightRepeated count cursor).instantiate read history =
      repeatFixed (tightNative read) count := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
    rw [tightRepeated, instantiate_castFinish, straight_append_constant _ _ read
      (repeatFixed (tightNative read) count) (fun h => ih _ h), tightRound_instantiate]
    rfl

def tightEntry : StraightEntry where
  coefficients := naivePowerTable
  finalCursor := 0 + 26 * 206368
  program := castTable naivePowerTable_length.symm (tightRepeated 26 0)

theorem tightEntry_instantiate (Q : Point) :
    tightEntry.instantiate Q =
      repeatFixed (tightNative (readConstant naivePowerCoefficient Q)) 26 := by
  dsimp only [StraightEntry.instantiate, tightEntry]
  rw [castTable_instantiate, naivePowerTable_read, tightRepeated_instantiate]

/-! ## T model and gate slots -/

attribute [local irreducible] trialGates fixedResetWires naivePowerTable

theorem straightT_tightRound (cursor : Nat) : straightT (tightRound cursor) = 343001514760448 := by
  simp only [tightRound, straightT_castFinish, tightRoundRaw, straightT_append,
    observedTrialProgram, trialProgram, straightT_constant, straightT_observe, straightT_reset,
    templateT_trial, Nat.add_zero]

theorem straightT_tightRepeated (count cursor : Nat) :
    straightT (tightRepeated count cursor) = count * 343001514760448 := by
  induction count generalizing cursor with
  | zero => simp only [tightRepeated, straightT_castFinish, straightT, Nat.zero_mul]
  | succ count ih =>
    simp only [tightRepeated, straightT_castFinish, straightT_append, straightT_tightRound, ih]
    omega

theorem tightRound_gateSlots_le (cursor : Nat) :
    (tightRound cursor).gateSlots ≤ 139264031904768 := by
  unfold tightRound
  rw [gateSlots_castFinish]
  unfold tightRoundRaw
  rw [append_reset_gateSlots, observedTrialProgram_slots]
  exact Nat.add_le_add_right trialGates_length_le 1024

theorem tightRepeated_gateSlots_le (count cursor : Nat) :
    (tightRepeated count cursor).gateSlots ≤ count * 139264031904768 := by
  induction count generalizing cursor with
  | zero =>
    simp only [tightRepeated, gateSlots_castFinish, Straight.gateSlots, Nat.zero_mul, le_refl]
  | succ count ih =>
    have h1 := tightRound_gateSlots_le cursor
    have h2 := ih (cursor + 206368)
    simp only [tightRepeated, gateSlots_castFinish, Straight.gateSlots_append]
    omega

/-! ## Well-formedness -/

attribute [local irreducible] Straight.WellFormed

theorem tightRound_wellFormed (cursor : Nat) : (tightRound cursor).WellFormed := by
  have hr := resetWireProgram_wellFormed (n := 512) tightResetWires
    (cursor + (bitcoinAReg ++ bitcoinBReg).length)
  have ha := straight_append_wellFormed (observedTrialProgram cursor)
    (resetWireProgram tightResetWires (cursor + (bitcoinAReg ++ bitcoinBReg).length))
    (observedTrialProgram_wellFormed cursor) hr
  exact castFinish_WF (tightRoundEnd cursor) (tightRoundRaw cursor) ha

theorem tightRepeated_wellFormed (count cursor : Nat) :
    (tightRepeated count cursor).WellFormed := by
  induction count generalizing cursor with
  | zero =>
    exact castFinish_WF (by omega) (.done : Straight 512 cursor cursor)
      (by unfold Straight.WellFormed; trivial)
  | succ count ih =>
    have ha := straight_append_wellFormed (tightRound cursor)
      (tightRepeated count (cursor + 206368)) (tightRound_wellFormed cursor)
      (ih (cursor + 206368))
    exact castFinish_WF
      (by omega : cursor + 206368 + count * 206368 = cursor + (count + 1) * 206368)
      ((tightRound cursor).append (tightRepeated count (cursor + 206368))) ha

attribute [local irreducible] tightRepeated

theorem tightEntry_wellFormed : tightEntry.program.WellFormed := by
  have h := Eq.mpr (castTable_wellFormed naivePowerTable_length.symm (tightRepeated 26 0))
    (tightRepeated_wellFormed 26 0)
  exact h

/-! ## Resources -/

theorem tightEntry_gateSlots_le : tightEntry.program.gateSlots ≤ 3620864829523968 := by
  simp only [tightEntry, gateSlots_castTable]
  exact (tightRepeated_gateSlots_le 26 0).trans (by decide)

theorem tightEntry_tModel_bound (Q : Point) :
    (resources (tightEntry.instantiate Q)).tModel ≤ 8918039383771648 := by
  have h := straight_t_bound tightEntry.program
    (readConstant tightEntry.coefficients.get Q) Fin.elim0
  have ht : straightT tightEntry.program = 8918039383771648 := by
    dsimp only [tightEntry]
    rw [straightT_castTable, straightT_tightRepeated]
  rw [ht] at h
  exact h

theorem tightEntry_measurements (Q : Point) :
    (resources (tightEntry.instantiate Q)).measurements = 5365568 := by
  dsimp only [resources, StraightEntry.instantiate]
  rw [Straight.measurementCount]
  rfl

theorem tightNative_support (Q : Point) :
    (tightNative (readConstant naivePowerCoefficient Q)).wires ⊆ tightResetWires := by
  intro w hw
  rw [tightNative, wires_seq] at hw
  rcases hw with hw | hw
  · rw [observedNative, wires_seq] at hw
    rcases hw with hw | hw
    · rw [gateNative_wires] at hw
      exact trialGates_tight_support Q hw
    · have h := zObserve_support _ hw
      apply declaredWires_tight
      simp only [List.mem_append] at h ⊢
      tauto
  · exact resetNative_support _ hw

theorem tightEntry_support (Q : Point) :
    (tightEntry.instantiate Q).wires ⊆ tightResetWires := by
  rw [tightEntry_instantiate]
  exact repeatFixed_support _ _ (tightNative_support Q) 26

theorem tightEntry_qubit_bound (Q : Point) :
    (resources (tightEntry.instantiate Q)).qubits ≤ 205856 := by
  have hs : (tightEntry.instantiate Q).wires.toFinset ⊆ tightResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (tightEntry_support Q (List.mem_toFinset.mp hw))
  have hc := Finset.card_le_card hs
  simpa only [resources, AdaptiveCircuit.qubitCount, List.card_toFinset,
    List.dedup_eq_self.mpr tightResetWires_nodup, tightResetWires_length] using hc

/-! ## Success through the protected decoder -/

theorem observedNative_run (Q : Point) (ho : order • Q = 0) :
    (observedNative (readConstant naivePowerCoefficient Q)).run = (naiveObserved Q).run := by
  have h := observedTrialProgram_run Q ho 0 Fin.elim0
  rw [observedTrialProgram_instantiate] at h
  exact h

theorem tightNative_zero (Q : Point) (b : InstrumentBranch)
    (hb : b ∈ (tightNative (readConstant naivePowerCoefficient Q)).run) :
    b.kraus (ket zeroBasisState) =
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  have hc : SupportedOn (Clean tightResetWires) (b.kraus (ket zeroBasisState)) := by
    rw [tightNative, AdaptiveCircuit.run_seq, resetNative_run] at hb
    obtain ⟨before, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨after, ha, rfl⟩ := List.mem_map.mp hb
    exact resetAll_clean _ tightResetWires_nodup after ha (before.kraus (ket zeroBasisState))
  have hs : SupportedOn (fun s => s = zeroBasisState) (b.kraus (ket zeroBasisState)) := by
    intro s hs
    funext w
    by_cases hw : w ∈ tightResetWires
    · exact hc s hs w hw
    · exact AdaptiveCircuit.branch_frame (tightNative (readConstant naivePowerCoefficient Q))
        w false (fun h => hw (tightNative_support Q h)) b hb (ket zeroBasisState)
        (supportedOn_ket _ _ rfl) s hs
  ext s
  by_cases he : s = zeroBasisState
  · subst s; simp [ket]
  · have hz : (b.kraus (ket zeroBasisState)) s = 0 := by
      by_contra h
      exact he (hs s h)
    simp only [ket] at hz
    simp [ket, he, hz]

theorem tightNative_length (Q : Point) (ho : order • Q = 0) (b : InstrumentBranch)
    (hb : b ∈ (tightNative (readConstant naivePowerCoefficient Q)).run) :
    b.history.length = 206368 := by
  rw [tightNative, AdaptiveCircuit.run_seq, resetNative_run, observedNative_run Q ho] at hb
  obtain ⟨before, hbefore, hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨after, hafter, rfl⟩ := List.mem_map.mp hb
  simp only [InstrumentBranch.seq, List.length_append,
    naiveObserved_length Q before hbefore, resetAll_history_length _ after hafter,
    tightResetWires_length]

theorem tightNative_total (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (tightNative (readConstant naivePowerCoefficient Q)).run.bornMass (ket zeroBasisState) = 1 := by
  have ho : order • Q = 0 := by rw [hQ]; exact dlogPoint_order d
  rw [tightNative, AdaptiveCircuit.run_seq, resetNative_run,
    instrumentMass_seq_preserving _ _ _ (resetAll_mass _), observedNative_run Q ho,
    naiveObserved_total Q d hQ hn]

theorem tightNative_eventMass (Q : Point) (ho : order • Q = 0) (event : List Bool → Bool)
    (ψ : State) :
    Instrument.bornMass ((tightNative (readConstant naivePowerCoefficient Q)).run.filter
      (fun b => event (b.history.take 512))) ψ =
    Instrument.bornMass ((naiveObserved Q).run.filter (fun b => event b.history)) ψ := by
  rw [tightNative, AdaptiveCircuit.run_seq, resetNative_run, observedNative_run Q ho]
  rw [instrumentFilter_seq_first _ _ (fun b => event b.history) _ (by
    intro b hb c _
    simp [InstrumentBranch.seq, ← naiveObserved_length Q b hb])]
  exact instrumentMass_seq_preserving _ _ _ (resetAll_mass _)

/-- Success of at least one of the 26 rounds, read at the tight stride. -/
def tightSuccess (d : Nat) (history : List Bool) : Bool :=
  !repeatFailed 206368 (fun bits => naiveEvent d (bits.take 512)) 26 history

theorem tightRepeated_probability (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    Instrument.bornMass
      ((repeatFixed (tightNative (readConstant naivePowerCoefficient Q)) 26).run.filter
        (fun b => tightSuccess d b.history)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (recordMass (naiveObserved Q).run (naiveEvent d) (ket zeroBasisState)) 26 := by
  have ho : order • Q = 0 := by rw [hQ]; exact dlogPoint_order d
  unfold tightSuccess
  rw [repeatFixedSuccess_mass _ _ _ (tightNative_length Q ho)
    (tightNative_zero Q) (tightNative_total Q d hQ hn)]
  rw [tightNative_eventMass Q ho, recordMass_filter]

theorem tightRepeated_success (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (99 / 100 : ℝ) ≤ Instrument.bornMass
      ((repeatFixed (tightNative (readConstant naivePowerCoefficient Q)) 26).run.filter
        (fun b => tightSuccess d b.history)) (ket zeroBasisState) := by
  rw [tightRepeated_probability Q d hQ hn]
  have hp := naiveObserved_success Q d hQ hn
  calc
    (99 / 100 : ℝ) ≤ independentRetrySuccessProbability (41 / 250) 26 :=
      by simpa [independentRetrySuccessProbability, naive_bound_value, naive_trialCount_value] using
        bitcoinECDLPSubmission.trialCount_correct
    _ ≤ _ := independentRetrySuccessProbability_mono 26 hp.2 hp.1

theorem tightEntry_success (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (99 / 100 : ℝ) ≤ Instrument.bornMass ((tightEntry.instantiate Q).run.filter
      (fun b => tightSuccess d b.history)) (ket zeroBasisState) := by
  rw [tightEntry_instantiate]
  exact tightRepeated_success Q d hQ hn

theorem tightEntry_history_length (Q : Point) (ho : order • Q = 0) (b : InstrumentBranch)
    (hb : b ∈ (tightEntry.instantiate Q).run) : b.history.length = 5365568 := by
  rw [tightEntry_instantiate] at hb
  exact repeatFixed_history_length _ _ (tightNative_length Q ho) 26 b hb

/-! ## Decoder layout at the tight stride -/

def tightSampleStart (t : Fin 26) : Nat := t.val * 206368

def tightTrialPositions (t : Fin 26) : TrialPositions repeatedDecoderParams where
  left := ⟨(List.range' (tightSampleStart t) 256).toArray, by simp [repeatedDecoderParams]⟩
  right := ⟨(List.range' (tightSampleStart t + 256) 256).toArray,
    by simp [repeatedDecoderParams]⟩

def tightLayout : DecodeLayout where
  kind := .nearestPair
  params := repeatedDecoderParams
  trials := List.ofFn tightTrialPositions
  trials_le := by simp

theorem tightTrialPositions_read (history : List Bool) (hl : history.length = 5365568)
    (t : Fin 26) :
    readWord history (tightTrialPositions t).left.toList =
      some (bitsValue ((history.drop (tightSampleStart t)).take 256)) ∧
    readWord history (tightTrialPositions t).right.toList =
      some (bitsValue ((history.drop (tightSampleStart t + 256)).take 256)) := by
  have ht := t.isLt
  have hs : tightSampleStart t + 512 ≤ history.length := by
    dsimp only [tightSampleStart]
    omega
  simp only [tightTrialPositions, Vector.toList, List.toList_toArray]
  exact ⟨readWord_range history _ _ (by omega), readWord_range history _ _ (by omega)⟩

theorem tightSuccess_iff (d : Nat) (history : List Bool) :
    tightSuccess d history = true ↔
      ∃ t : Fin 26, naiveEvent d ((history.drop (tightSampleStart t)).take 512) = true := by
  rw [tightSuccess, repeatFailed_success_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨⟨t, ht⟩, by simpa [tightSampleStart, List.take_take] using h⟩
  · rintro ⟨t, h⟩
    exact ⟨t.val, t.isLt, by simpa [tightSampleStart, List.take_take] using h⟩

theorem tightSuccess_actualWords (d : Nat) (history : List Bool)
    (hl : history.length = 5365568) (hs : tightSuccess d history = true) :
    ∃ t : Fin 26, ∃ left right : Nat,
      readWord history (tightTrialPositions t).left.toList = some left ∧
      readWord history (tightTrialPositions t).right.toList = some right ∧
      recoveredPair d left right = true := by
  obtain ⟨t, ht⟩ := (tightSuccess_iff d history).mp hs
  obtain ⟨ha, hb⟩ := tightTrialPositions_read history hl t
  refine ⟨t, _, _, ha, hb, ?_⟩
  simpa only [naiveEvent, pairEvent, List.take_take, List.drop_take, List.drop_drop,
    Nat.min_eq_left (by omega : 256 ≤ 512), show 512 - 256 = 256 from rfl] using ht

theorem tight_success_candidate (d : Nat) (history : List Bool)
    (hl : history.length = 5365568) (hs : tightSuccess d history = true) :
    (d : ZMod order) ∈ candidates tightLayout history := by
  obtain ⟨t, a, b, ha, hb, hp⟩ := tightSuccess_actualWords d history hl hs
  apply List.mem_flatMap.mpr
  refine ⟨tightTrialPositions t, List.mem_ofFn.mpr ⟨t, rfl⟩, ?_⟩
  change (d : ZMod order) ∈
    decodeTrial .nearestPair repeatedDecoderParams history (tightTrialPositions t)
  simp only [decodeTrial, ha, hb]
  have hp' := of_decide_eq_true hp
  simp only [nearestPairCandidates, repeatedDecoderParams, ↓reduceIte]
  rw [hp']
  simp

theorem tight_success_verified (Q : Point) (d : Nat) (hd : Q = d • G)
    (history : List Bool) (hl : history.length = 5365568)
    (hs : tightSuccess d history = true) :
    (verifiedCandidate tightLayout Q history).isSome = true := by
  classical
  have hm := tight_success_candidate d history hl hs
  have he : (d : ZMod order).val • G = Q := by
    rw [hd, ZMod.val_natCast]
    exact nsmul_mod_order G (by simpa using dlogPoint_order 1) d
  unfold verifiedCandidate
  exact List.find?_isSome.mpr ⟨_, hm, by simpa using he⟩

theorem tightEntry_verified_success (Q : Point) (d : Nat) (hd : Q = d • G) (hn : Q ≠ 0) :
    (99 / 100 : ℝ) ≤ Instrument.bornMass
      ((tightEntry.instantiate Q).run.filter
        (fun b => (verifiedCandidate tightLayout Q b.history).isSome))
      (ket zeroBasisState) := by
  apply (tightEntry_success Q d hd hn).trans
  apply bornMass_filter_mono
  intro b hb hs
  have ho : order • Q = 0 := by rw [hd]; exact dlogPoint_order d
  exact tight_success_verified Q d hd b.history (tightEntry_history_length Q ho b hb) hs

/-! ## Certificate -/

/-- Declared bounds: the tight qubit count, the unchanged Naive T model, and the
26-round record length at the tight stride. -/
def tightBounds : Bounds where
  qubits := 205856
  tModel := 8918039383771648
  measurements := 5365568

theorem tightEntry_certificate :
    Certificate officialLimits tightLayout tightEntry tightBounds where
  gateBudget := tightEntry_gateSlots_le.trans (by decide)
  recordBudget := by decide
  tableBudget := by
    simpa only [tightEntry, naivePowerTable_length] using
      (by decide : 512 ≤ officialLimits.coefficientRows)
  candidateBudget := by
    have hc : 26 ≤ officialLimits.candidateChecks := by simp [officialLimits, budget55]
    simpa [tightLayout, decoderCandidateLimit] using hc
  wellFormed := tightEntry_wellFormed
  resources := fun Q =>
    ⟨tightEntry_qubit_bound Q, tightEntry_tModel_bound Q, (tightEntry_measurements Q).le⟩
  success := fun Q d hn hd => tightEntry_verified_success Q d hd hn

end
end ShorECDLP.Entrant
