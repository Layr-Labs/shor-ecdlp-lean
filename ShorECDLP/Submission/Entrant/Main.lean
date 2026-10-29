import ShorECDLP.Submission.Entrant.Trial
import ShorECDLP.Submission.Entrant.Success
import ShorECDLP.Submission.Entrant.WindowMassSharp
import ShorECDLP.Submission.Entrant.Shift.Success2
import ShorECDLP.Challenge.Official

/-! EDITABLE. Entrant: one observed trial, `wrappedShift` decoder, narrow right register.

The circuit uses the V2 field arithmetic and the Naive dense workspace; each controlled point
addition is the single-pass `fastCPA` construction.  The left phase register has 263 qubits and
is rounded to the nearest numerator `k`.  The right register has only 214 qubits: a diagonal
half-bin shift precedes its inverse QFT and the protected `wrappedShift` decoder reads its top
203 bits, enumerating at most `2 (order / 2^203 + 2)` candidates.  Averaged over the numerators
`k d mod order` (a permutation of the nonzero residues), one trial succeeds with probability
at least 99 %, with 49 fewer controlled point additions than the 263 + 263 layout. -/

namespace ShorECDLP.Entrant
open Quantum Secp256k1 Challenge NaiveChallenge Arithmetic
open ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
noncomputable section

/-! ## Decoder layout -/

def paramsE : DecoderParams := ⟨263, 203, by omega, by omega, by omega, by omega⟩

def positionsE : TrialPositions paramsE where
  left := ⟨(List.range' 0 263).toArray, by simp [paramsE]⟩
  right := ⟨(List.range' 274 203).toArray, by simp [paramsE]⟩

def layoutE' : DecodeLayout where
  kind := .wrappedShift
  params := paramsE
  trials := [positionsE]
  trials_le := by simp

def eventS (d a b : Nat) : Bool :=
  decide ((d : ZMod order) ∈ fixedCandidates paramsE a (b / 2 ^ 11))

theorem bitsValue_div_two (L : List Bool) : bitsValue L / 2 = bitsValue (L.drop 1) := by
  cases L with
  | nil => rfl
  | cons b bs =>
    simp only [bitsValue, List.drop_succ_cons, List.drop_zero]
    cases b <;> simp
    all_goals omega

theorem bitsValue_div_pow (L : List Bool) (k : Nat) :
    bitsValue L / 2 ^ k = bitsValue (L.drop k) := by
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih, bitsValue_div_two, List.drop_drop]

theorem successE_candidate (d : Nat) (history : List Bool) (hl : history.length = 477)
    (hs : pairEvent 263 (eventS d) history = true) :
    (d : ZMod order) ∈ candidates layoutE' history := by
  have hleft : readWord history positionsE.left.toList =
      some (bitsValue (history.take 263)) := by
    simp only [positionsE, Vector.toList, List.toList_toArray]
    simpa using readWord_range history 0 263 (by omega)
  have hright : readWord history positionsE.right.toList =
      some (bitsValue (history.drop 263) / 2 ^ 11) := by
    simp only [positionsE, Vector.toList, List.toList_toArray]
    have h := readWord_range history 274 203 (by omega)
    rw [List.take_of_length_le (by simp only [List.length_drop]; omega)] at h
    rw [h, bitsValue_div_pow, List.drop_drop]
  simp only [pairEvent, eventS, decide_eq_true_eq] at hs
  change (d : ZMod order) ∈ decodeTrial .wrappedShift paramsE history positionsE ++ []
  simp only [decodeTrial, trialCandidates, hleft, hright, fixedCandidates_take, List.append_nil,
    Finset.mem_toList]
  exact hs

theorem successE_verified (Q : Point) (d : Nat) (hd : Q = d • G)
    (history : List Bool) (hl : history.length = 477)
    (hs : pairEvent 263 (eventS d) history = true) :
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
theorem hwinS (n : ℕ) (hn0 : 0 < n) (hnr : n < order) :
    (200 : ℝ) / 201 ≤ ∑ a : Fin (2 ^ 263),
      if Challenge.nearestNumerator order 263 a.val = n then
        Complex.normSq (qpeAmplitude 263 ((n : ℝ) / (order : ℝ)) a.val) else 0 := by
  have h := window_mass_sharp order 263 n hn0 hnr (by decide)
  rw [Fin.sum_univ_eq_sum_range (fun a => if Challenge.nearestNumerator order 263 a = n then
    Complex.normSq (qpeAmplitude 263 ((n : ℝ) / (order : ℝ)) a) else 0)]
  simpa only [Challenge.nearestNumerator, qpeAmplitude, eigenvalue] using h

theorem secret_mod_ne_zero (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    d % order ≠ 0 := by
  intro h
  apply hn
  rw [hd, ← Nat.mod_add_div d order, h, Nat.zero_add, mul_nsmul, generator_nsmul_eq_zero,
    nsmul_zero]

/-- The oracle specification, for whichever proof of primality of `p` the circuit carries. -/
theorem spec_any (inst : Fact (Nat.Prime p)) (Q : Point) (hn : Q ≠ 0) (ho : order • Q = 0) :
    ECDLPOracleSpec pointEncoding
      (Quantum.run (V2.fastOracle regA regB bitcoinPointReg bitcoinWorkStart G Q))
      G Q regA regB bitcoinPointReg (V2.scalarMulWork bitcoinWorkStart) :=
  @V2.fastOracle_spec inst regA regB bitcoinPointReg bitcoinWorkStart G Q
    (V2.doublingTable_ne_zero _ G G_ne_zero generator_nsmul_eq_zero)
    (V2.doublingTable_ne_zero _ Q hn ho)
    V2.v2WireLayout.2.2.1 layoutE.1

theorem hnum_general (r : ℝ) (hr : (10 : ℝ) ^ 6 ≤ r) :
    (99 : ℝ) / 100 ≤ 200 / 201 * ((r - 1) - ((r - 1) / 2 ^ 11 + 1) *
      (3 + 406 / 1000 * (1 + (11 : ℕ) * 0.6931471808) + 2 ^ 11 * (2 / 2 ^ (203 + 11)))) / r := by
  have hA : (3 + 406 / 1000 * (1 + (11 : ℕ) * 0.6931471808) + 2 ^ 11 * (2 / 2 ^ (203 + 11)) : ℝ)
      ≤ 6502 / 1000 := by norm_num
  have hr0 : (0 : ℝ) < r := by linarith
  have hc : (0 : ℝ) ≤ (r - 1) / 2 ^ 11 + 1 := by
    have : (0 : ℝ) ≤ r - 1 := by linarith
    positivity
  have hX := mul_le_mul_of_nonneg_left hA hc
  rw [le_div_iff₀ hr0]
  nlinarith

set_option exponentiation.threshold 300 in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem trialE_probability (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ) / 100 ≤ recordMass
      (observedTrial (trialS regA regB bitcoinPointReg bitcoinWorkStart
        bitcoinQFTAncilla Q) regA regB).run
      (pairEvent 263 (eventS d)) (ket zeroBasisState) := by
  have hfresh := layoutE.2
  let hsetting : ECDLPSetting G Q order d :=
    { prime_order := order_prime
      order_P := generator_order
      Q_eq := hd }
  have hsetup : Quantum.OrderFinding.Two.Setup2 pointEncoding regA regB bitcoinPointReg
      (V2.scalarMulWork bitcoinWorkStart) bitcoinQFTAncilla 263 214 zeroBasisState :=
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
  have h := zObserve_eventProbability2 regA regB 263 214 regA_length regB_length (eventS d)
    (Quantum.run (trialS regA regB bitcoinPointReg bitcoinWorkStart
      bitcoinQFTAncilla Q) (ket zeroBasisState))
  rw [regA_length] at h
  rw [h, trialS_run_ket]
  have hspec : ECDLPOracleSpec pointEncoding (oracleS Q) G Q regA regB bitcoinPointReg
      (V2.scalarMulWork bitcoinWorkStart) :=
    spec_any ⟨p_prime⟩ Q hn (by rw [hd]; exact dlogPoint_order d)
  have hs := shift_success (R := 203) (e := 11) (pb := 214) rfl pointEncoding (oracleS Q) G Q regA regB
    bitcoinPointReg (V2.scalarMulWork bitcoinWorkStart) bitcoinQFTAncilla zeroBasisState paramsE
    rfl rfl hsetting hspec
    hsetup (secret_mod_ne_zero Q d hn hd) (by norm_num) (200 / 201) (by norm_num) hwinS
  have hnum : (99 : ℝ) / 100 ≤ 200 / 201 * (((order : ℝ) - 1) - (((order : ℝ) - 1) / 2 ^ 11 + 1) *
      (3 + 406 / 1000 * (1 + (11 : ℕ) * 0.6931471808) + 2 ^ 11 * (2 / 2 ^ (203 + 11)))) /
        order := hnum_general _ (by norm_num [order])
  refine hnum.trans (hs.trans (le_of_eq ?_))
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [eventS, decide_eq_true_eq]

set_option maxRecDepth 100000 in
theorem entryE_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ) / 100 ≤ Instrument.bornMass ((entryE.instantiate Q).run.filter
      (fun b => (verifiedCandidate layoutE' Q b.history).isSome)) (ket zeroBasisState) := by
  have ho : order • Q = 0 := by rw [hd]; exact dlogPoint_order d
  rw [entryE_run Q ho]
  have hlen : ∀ b ∈ (observedTrial (trialS regA regB bitcoinPointReg bitcoinWorkStart
      bitcoinQFTAncilla Q) regA regB).run, b.history.length = 477 := by
    intro b hb
    have h := observedTrial_history_length _ regA regB b hb
    rw [regA_length, regB_length] at h
    exact h
  calc
    (99 : ℝ) / 100 ≤ recordMass
        (observedTrial (trialS regA regB bitcoinPointReg bitcoinWorkStart
          bitcoinQFTAncilla Q) regA regB).run
        (pairEvent 263 (eventS d)) (ket zeroBasisState) :=
      trialE_probability Q d hn hd
    _ = Instrument.bornMass ((observedTrial (trialS regA regB bitcoinPointReg
          bitcoinWorkStart bitcoinQFTAncilla Q) regA regB).run.filter
          (fun b => pairEvent 263 (eventS d) b.history)) (ket zeroBasisState) :=
      recordMass_filter _ _ _
    _ ≤ _ := bornMass_filter_mono _ _ _
      (fun b hb hs => successE_verified Q d hd b.history (hlen b hb) hs) _

/-! ## Submission -/

def entry : StraightEntry := entryE
def layout : DecodeLayout := layoutE'

def bounds : Bounds where
  qubits := 77575
  tModel := 10616629911600
  measurements := 477

attribute [local irreducible] tableE progE Straight.WellFormed

theorem certificate : Certificate officialLimits layout entry bounds where
  gateBudget := entryE_gateSlots.trans (by simp [officialLimits])
  recordBudget := by
    change (477 : ℕ) ≤ officialLimits.measurements
    simp [officialLimits]
  tableBudget := by
    change tableE.length ≤ officialLimits.coefficientRows
    rw [tableE_length]
    simp [officialLimits]
  candidateBudget := by
    simp only [layout, layoutE', decoderCandidateLimit, trialCandidateLimit, paramsE,
      officialLimits, budget55, List.length_singleton, one_mul]
    norm_num [order]
  wellFormed := entryE_wellFormed
  resources := fun Q =>
    ⟨entryE_qubits Q, (entryE_tModel Q).trans (by simp [bounds]), (entryE_measurements Q).le⟩
  success := fun Q d hn hd => entryE_success Q d hn hd

end
end ShorECDLP.Entrant
