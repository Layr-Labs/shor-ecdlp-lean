import ShorECDLP.Submission.Entrant.Trial
import ShorECDLP.Submission.Entrant.Success
import ShorECDLP.Submission.Entrant.WindowMass
import ShorECDLP.Challenge.Official

/-! EDITABLE. Entrant: one observed trial at 265-bit phase precision.

The circuit reuses the Naive field arithmetic and dense workspace, with nine extra
high-order qubits per phase register.  The extra precision makes the canonical
nearest-numerator decoder succeed with probability at least 99 % in a single trial.
Each controlled point addition is the single-pass `fastCPA` construction. -/

namespace ShorECDLP.Entrant
open Quantum Secp256k1 Challenge NaiveChallenge Arithmetic
open ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
noncomputable section

/-! ## Decoder layout -/

def paramsE : DecoderParams := ⟨265, 265, by omega, by omega, by omega, by omega⟩

def positionsE : TrialPositions paramsE where
  left := ⟨(List.range' 0 265).toArray, by simp [paramsE]⟩
  right := ⟨(List.range' 265 265).toArray, by simp [paramsE]⟩

def layoutE' : DecodeLayout where
  kind := .nearestPair
  params := paramsE
  trials := [positionsE]
  trials_le := by simp

def recoveredE (d a b : Nat) : Bool :=
  decide (orderFindingPostprocess order 265 order_prime
    (Fin.ofNat (2 ^ 265) a, Fin.ofNat (2 ^ 265) b) = some (d : ZMod order))

theorem successE_candidate (d : Nat) (history : List Bool) (hl : history.length = 530)
    (hs : pairEvent 265 (recoveredE d) history = true) :
    (d : ZMod order) ∈ candidates layoutE' history := by
  have hleft : readWord history positionsE.left.toList =
      some (bitsValue (history.take 265)) := by
    simp only [positionsE, Vector.toList, List.toList_toArray]
    simpa using readWord_range history 0 265 (by omega)
  have hright : readWord history positionsE.right.toList =
      some (bitsValue (history.drop 265)) := by
    simp only [positionsE, Vector.toList, List.toList_toArray]
    have h := readWord_range history 265 265 (by omega)
    rwa [List.take_of_length_le (by simp only [List.length_drop]; omega)] at h
  simp only [pairEvent, recoveredE, decide_eq_true_eq] at hs
  change (d : ZMod order) ∈ decodeTrial .nearestPair paramsE history positionsE ++ []
  simp only [decodeTrial, hleft, hright, nearestPairCandidates, paramsE, if_true, hs,
    Option.toList_some, List.append_nil, List.mem_singleton]

theorem successE_verified (Q : Point) (d : Nat) (hd : Q = d • G)
    (history : List Bool) (hl : history.length = 530)
    (hs : pairEvent 265 (recoveredE d) history = true) :
    (verifiedCandidate layoutE' Q history).isSome = true := by
  classical
  have hm := successE_candidate d history hl hs
  have he : (d : ZMod order).val • G = Q := by
    rw [hd, ZMod.val_natCast]
    exact nsmul_mod_order G (by simpa using dlogPoint_order 1) d
  unfold verifiedCandidate
  exact List.find?_isSome.mpr ⟨_, hm, by simpa using he⟩

/-! ## Probability -/

set_option exponentiation.threshold 300 in
theorem hwinE (n : ℕ) (hn0 : 0 < n) (hnr : n < order) :
    (199 : ℝ) / 200 ≤ ∑ a : Fin (2 ^ 265),
      if Quantum.OrderFinding.nearestNumerator order 265 a.val = n then
        Complex.normSq (qpeAmplitude 265 ((n : ℝ) / (order : ℝ)) a.val) else 0 := by
  have h := window_mass order 265 n hn0 hnr (by decide)
  rw [Fin.sum_univ_eq_sum_range (fun a => if Quantum.OrderFinding.nearestNumerator order 265 a = n then
    Complex.normSq (qpeAmplitude 265 ((n : ℝ) / (order : ℝ)) a) else 0)]
  simpa only [Quantum.OrderFinding.nearestNumerator, qpeAmplitude, eigenvalue] using h

theorem secret_mod_ne_zero (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    d % order ≠ 0 := by
  intro h
  apply hn
  rw [hd, ← Nat.mod_add_div d order, h, Nat.zero_add, mul_nsmul, generator_nsmul_eq_zero,
    nsmul_zero]

/-- The oracle specification, for whichever proof of primality of `p` the circuit carries. -/
theorem spec_any (inst : Fact (Nat.Prime p)) (Q : Point) (hn : Q ≠ 0) (ho : order • Q = 0) :
    ECDLPOracleSpec pointEncoding
      (Quantum.run (@fastOracle inst regA regB bitcoinPointReg bitcoinWorkStart G Q))
      G Q regA regB bitcoinPointReg (scalarMulWork bitcoinWorkStart) :=
  @fastOracle_spec inst regA regB bitcoinPointReg bitcoinWorkStart G Q
    (doublingTable_ne_zero _ G G_ne_zero generator_nsmul_eq_zero)
    (doublingTable_ne_zero _ Q hn ho)
    bitcoinWireLayout.2.2.1 layoutE.1

theorem trialE_probability (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ) / 100 ≤ recordMass
      (observedTrial (fastTrial regA regB bitcoinPointReg bitcoinWorkStart
        bitcoinQFTAncilla Q) regA regB).run
      (pairEvent 265 (recoveredE d)) (ket zeroBasisState) := by
  have hfresh := layoutE.2
  let hsetting : ECDLPSetting G Q order d :=
    { prime_order := order_prime
      order_P := generator_order
      Q_eq := hd }
  have hsetup : OrderFindingSetup pointEncoding regA regB bitcoinPointReg
      (scalarMulWork bitcoinWorkStart) bitcoinQFTAncilla 265 zeroBasisState :=
    { a_width := regA_length
      b_width := regB_length
      a_zero := regValue_zeroBasisState regA
      b_zero := regValue_zeroBasisState regB
      point_zero := by
        simp only [regValue_zeroBasisState, pointEncoding_encode_val, encodeNat_zero]
      oracleWork_zero := by simp [Clean]
      ancilla_zero := zeroBasisState_apply bitcoinQFTAncilla
      ancilla_fresh := hfresh }
  rw [observedTrial_recordMass]
  have h := zObserve_eventProbability regA regB 265 regA_length regB_length (recoveredE d)
    (Quantum.run (fastTrial regA regB bitcoinPointReg bitcoinWorkStart
      bitcoinQFTAncilla Q) (ket zeroBasisState))
  rw [regA_length] at h
  rw [h]
  have heq : (∑ a : Fin (2 ^ 265), ∑ b : Fin (2 ^ 265),
      if recoveredE d a.val b.val then
        jointRegisterProbability regA regB a.val b.val
          (Quantum.run (fastTrial regA regB bitcoinPointReg bitcoinWorkStart
            bitcoinQFTAncilla Q) (ket zeroBasisState)) else 0) =
      orderFindingSuccessProbability order 265 d order_prime regA regB
        (Quantum.run (fastTrial regA regB bitcoinPointReg bitcoinWorkStart
          bitcoinQFTAncilla Q) (ket zeroBasisState)) := by
    unfold orderFindingSuccessProbability
    simp only [recoveredE, Fin.ofNat_eq_cast, Fin.cast_val_eq_self, decide_eq_true_eq]
  rw [heq, fastTrial_run]
  refine le_trans ?_ (success_of_window_mass pointEncoding _ G Q regA regB bitcoinPointReg
    (scalarMulWork bitcoinWorkStart) bitcoinQFTAncilla zeroBasisState hsetting
    (spec_any _ Q hn (by rw [hd]; exact dlogPoint_order d))
    hsetup (secret_mod_ne_zero Q d hn hd) (199 / 200) (by norm_num) hwinE)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num [order])]
  norm_num [order]

set_option maxRecDepth 100000 in
theorem entryE_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ) / 100 ≤ Instrument.bornMass ((entryE.instantiate Q).run.filter
      (fun b => (verifiedCandidate layoutE' Q b.history).isSome)) (ket zeroBasisState) := by
  have ho : order • Q = 0 := by rw [hd]; exact dlogPoint_order d
  rw [entryE_run Q ho]
  have hlen : ∀ b ∈ (observedTrial (fastTrial regA regB bitcoinPointReg bitcoinWorkStart
      bitcoinQFTAncilla Q) regA regB).run, b.history.length = 530 := by
    intro b hb
    have h := observedTrial_history_length _ regA regB b hb
    rw [regA_length, regB_length] at h
    exact h
  calc
    (99 : ℝ) / 100 ≤ recordMass
        (observedTrial (fastTrial regA regB bitcoinPointReg bitcoinWorkStart
          bitcoinQFTAncilla Q) regA regB).run
        (pairEvent 265 (recoveredE d)) (ket zeroBasisState) :=
      trialE_probability Q d hn hd
    _ = Instrument.bornMass ((observedTrial (fastTrial regA regB bitcoinPointReg
          bitcoinWorkStart bitcoinQFTAncilla Q) regA regB).run.filter
          (fun b => pairEvent 265 (recoveredE d) b.history)) (ket zeroBasisState) :=
      recordMass_filter _ _ _
    _ ≤ _ := bornMass_filter_mono _ _ _
      (fun b hb hs => successE_verified Q d hd b.history (hlen b hb) hs) _

/-! ## Submission -/

def entry : StraightEntry := entryE
def layout : DecodeLayout := layoutE'

def bounds : Bounds where
  qubits := 206642
  -- Declared T-model bound: the next multiple of 10^4 above the proved count
  -- 88678607248520 (see `entryE_tModel`), so that qubits × tModel = 18324724759354500000
  -- has fifteen significant digits.
  tModel := 88678607250000
  measurements := 530

attribute [local irreducible] tableE progE Straight.WellFormed

theorem certificate : Certificate officialLimits layout entry bounds where
  gateBudget := entryE_gateSlots.trans (by simp [officialLimits])
  recordBudget := by
    change (530 : ℕ) ≤ officialLimits.measurements
    simp [officialLimits]
  tableBudget := by
    change tableE.length ≤ officialLimits.coefficientRows
    rw [tableE_length]
    simp [officialLimits]
  candidateBudget := by
    simp [layout, layoutE', decoderCandidateLimit, officialLimits, budget55]
  wellFormed := entryE_wellFormed
  resources := fun Q =>
    ⟨entryE_qubits Q,
      Nat.le_trans (entryE_tModel Q) (show (88678607248520 : ℕ) ≤ 88678607250000 by norm_num),
      (entryE_measurements Q).le⟩
  success := fun Q d hn hd => entryE_success Q d hn hd

end
end ShorECDLP.Entrant
