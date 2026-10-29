import ShorECDLP.Submission.Entrant.Single.Fourier
import ShorECDLP.Submission.Entrant.Single.Physical

/-! EDITABLE. Single-trial entrant: concrete single-trial success.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Distribution ====

section
/-! Distribution proof entry point for the mixed-width single-trial construction. -/

end

-- ==== part: Single/Scalar ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

/-- The fixed mixed-width offset cancels the centered odd-digit bias. -/
theorem increment_offset (Q : Point) (hQ : order • Q = 0) (w : SignedWindow) (v : Nat) :
    increment Q w v + offsetScalar w.width w.exponent • w.base Q =
      (v * 2^w.exponent) • w.base Q := by
  let P := w.base Q
  have hr : order • P = 0 := by
    cases w with
    | left16 _ | left15 _ => exact generator_nsmul_eq_zero
    | right16 _ | right15 _ => exact hQ
  have hh : halfOrder ≤ 2^(w.width-1) + order := by
    have hl : halfOrder ≤ order := by norm_num [halfOrder, order]
    exact hl.trans (Nat.le_add_left _ _)
  have he : (2^(w.width-1) + order - halfOrder) • P + halfOrder • P =
      2^(w.width-1) • P := by
    rw [← add_nsmul, Nat.sub_add_cancel hh, add_nsmul, hr, add_zero]
  have hoff : offsetScalar w.width w.exponent • P =
      2^(w.width-1) • (2^w.exponent • P) - (halfOrder * 2^w.exponent) • P := by
    unfold offsetScalar
    rw [mul_smul, smul_comm (2^(w.width-1) + order - halfOrder) (2^w.exponent),
      eq_sub_iff_add_eq.mpr he, nsmul_sub]
    simp only [mul_smul]
    rw [smul_comm (2^w.exponent) (2^(w.width-1)), smul_comm (2^w.exponent) halfOrder]
  let H := (halfOrder * 2^w.exponent) • P
  have hd : H + H = 2^w.exponent • P := by
    change (halfOrder * 2^w.exponent) • P + (halfOrder * 2^w.exponent) • P = _
    rw [mul_smul, smul_comm halfOrder (2^w.exponent), ← nsmul_add]
    exact congrArg (fun R : Point => 2^w.exponent • R)
      (signedWindowHalfPoint_double P order (by decide +kernel) hr)
  have hp : (2 : Int)^w.width = 2 * (2^(w.width-1) : Nat) := by
    cases w <;> norm_num [SignedWindow.width]
  have hcalc : ((2*(v:Int)-(2:Int)^w.width+1) • H) +
      (2^(w.width-1) • (H+H) - H) = v • (H+H) := by
    rw [hp]
    module
  change ((2*(v:Int)-(2:Int)^w.width+1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2^w.exponent) P).symm

/-- Scalar reconstruction expressed without division or modular representatives. -/
theorem increment_eq_unsigned_sub_offset (Q : Point) (hQ : order • Q = 0)
    (w : SignedWindow) (v : Nat) :
    increment Q w v = (v * 2^w.exponent) • w.base Q -
      offsetScalar w.width w.exponent • w.base Q :=
  eq_sub_iff_add_eq.mpr (increment_offset Q hQ w v)

theorem left_offsets :
    (leftSigned.map (fun w => offsetScalar w.width w.exponent)).sum = leftOffset := by
  simp [leftSigned, leftOffset, widths, exponents, List.ofFn_succ,
    SignedWindow.width, SignedWindow.exponent]

theorem right_offsets :
    (rightSigned.map (fun w => offsetScalar w.width w.exponent)).sum = rightOffset := by
  simp [rightSigned, rightOffset, widths, exponents, List.ofFn_succ,
    SignedWindow.width, SignedWindow.exponent]

theorem left_base (Q : Point) (w : SignedWindow) (hw : w ∈ leftSigned) : w.base Q = G := by
  simp only [leftSigned, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem right_base (Q : Point) (w : SignedWindow) (hw : w ∈ rightSigned) : w.base Q = Q := by
  simp only [rightSigned, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem increments_sum (Q : Point) (hQ : order • Q = 0) (ws : List SignedWindow)
    (P : Point) (hbase : ∀ w ∈ ws, w.base Q = P) (values : SignedWindow → Nat) :
    (ws.map (fun w => increment Q w (values w))).sum =
      (ws.map (fun w => values w * 2^w.exponent)).sum • P -
        (ws.map (fun w => offsetScalar w.width w.exponent)).sum • P := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [increment_eq_unsigned_sub_offset Q hQ w, hbase w (by simp),
      ih (fun v hv => hbase v (List.mem_cons_of_mem w hv))]
    simp only [add_nsmul]
    abel

/-- The direct-load offsets cancel all 33 signed biases exactly. -/
theorem unsigned_reconstruction (Q : Point) (hQ : order • Q = 0)
    (first : Nat) (values : SignedWindow → Nat) :
    initialPoint Q first + (leftSigned.map (fun w => increment Q w (values w))).sum +
      (rightSigned.map (fun w => increment Q w (values w))).sum =
    (first * 2^247 + (leftSigned.map (fun w => values w * 2^w.exponent)).sum) • G +
      (rightSigned.map (fun w => values w * 2^w.exponent)).sum • Q := by
  rw [increments_sum Q hQ leftSigned G (left_base Q) values,
    increments_sum Q hQ rightSigned Q (right_base Q) values, left_offsets, right_offsets]
  unfold initialPoint
  simp only [add_nsmul]
  abel

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Setup ====

section
/-! The complete distribution theorem is parameterized by coherent physical
windows. Counts and Fourier order are explicit interface obligations. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option pp.maxSteps 60

structure Setup {n : Nat} (coeffs : Fin n → PointCoeff) where
  first : Window n
  signed : SignedWindow → Window n
  firstLaw : WindowLaw coeffs first firstUpdate FirstWindowInput
  signedLaw : SignedWindowLaw coeffs signed
  firstWires : first.wires = (bank 16).reverse
  signedWires : ∀ w, (signed w).wires = (bank w.width).reverse
  firstCount : first.count = 65535
  signedCount : ∀ w, (signed w).count = 30707853

def Setup.firstModel {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : WindowModel (readConstant coeffs Q) :=
  Distribution.firstModel s.first s.firstLaw s.firstWires Q hQ hn

def Setup.signedModel {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow) :
    WindowModel (readConstant coeffs Q) := ShorECDLP.Entrant.Single.Distribution.signedModel s.signedLaw s.signedWires Q hQ hn w

@[irreducible] def Setup.leftModels {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : List (WindowModel (readConstant coeffs Q)) :=
  s.firstModel Q hQ hn :: leftSigned.map (s.signedModel Q hQ hn)

@[irreducible] def Setup.rightModels {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : List (WindowModel (readConstant coeffs Q)) :=
  rightSigned.map (s.signedModel Q hQ hn)

def SignedWeights (Q P : Point) : List SignedWindow → Prop
  | List.nil => True
  | w :: ws => w.base Q = P ∧ w.exponent = (ws.map SignedWindow.width).sum ∧ SignedWeights Q P ws

theorem left_signed_weights (Q : Point) : SignedWeights Q G leftSigned := by
  norm_num [leftSigned, List.ofFn_succ, SignedWeights, SignedWindow.width,
    SignedWindow.exponent, SignedWindow.base]

theorem right_signed_weights (Q : Point) : SignedWeights Q Q rightSigned := by
  norm_num [rightSigned, List.ofFn_succ, SignedWeights, SignedWindow.width,
    SignedWindow.exponent, SignedWindow.base]

theorem Setup.signed_length {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : SignedWindow) :
    (s.signedModel Q hQ hn w).physical.wires.length = w.width := by
  simp only [Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel, s.signedWires, List.length_reverse, bank_width]

theorem Setup.modelWeights {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q P : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (ws : List SignedWindow) (hw : SignedWeights Q P ws) :
    ModelWeights P (ws.map (s.signedModel Q hQ hn)) := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · intro v
      change increment Q w v + offsetScalar w.width w.exponent • w.base Q = _
      have hwidths : ((ws.map (s.signedModel Q hQ hn)).map
          (fun w => w.physical.wires.length)).sum = (ws.map SignedWindow.width).sum := by
        simp only [List.map_map, Function.comp_def, s.signed_length]
      rw [hwidths, ← hw.2.1, ← hw.1]
      exact increment_offset Q hQ w v
    · exact ih hw.2.2

theorem left_signed_width : (leftSigned.map SignedWindow.width).sum = 247 := by
  norm_num [leftSigned, List.ofFn_succ, SignedWindow.width]

theorem right_signed_width : (rightSigned.map SignedWindow.width).sum = 263 := by
  norm_num [rightSigned, List.ofFn_succ, SignedWindow.width]

theorem Setup.left_weights {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ModelWeights G (s.leftModels Q hQ hn) := by
  rw [Setup.leftModels]
  constructor
  · intro v
    change initialPoint Q v + -(leftOffset • G + rightOffset • Q) = _
    have hwidths : ((leftSigned.map (s.signedModel Q hQ hn)).map
        (fun w => w.physical.wires.length)).sum = 247 := by
      simp only [List.map_map, Function.comp_def, s.signed_length, left_signed_width]
    rw [hwidths]
    unfold initialPoint
    simp only [add_nsmul]
    abel
  · exact s.modelWeights Q G hQ hn leftSigned (left_signed_weights Q)

theorem Setup.right_weights {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ModelWeights Q (s.rightModels Q hQ hn) := by
  rw [Setup.rightModels]
  exact s.modelWeights Q Q hQ hn rightSigned (right_signed_weights Q)

theorem sum_nat_smul (xs : List Nat) (P : Point) : (xs.map (fun k => k • P)).sum = xs.sum • P := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, add_nsmul]

theorem Setup.signed_bias_sum {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q P : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List SignedWindow)
    (hbase : ∀ w ∈ ws, w.base Q = P) :
    ((ws.map (s.signedModel Q hQ hn)).map WindowModel.bias).sum =
      (ws.map (fun w => offsetScalar w.width w.exponent)).sum • P := by
  rw [← sum_nat_smul]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  change offsetScalar w.width w.exponent • w.base Q = _
  rw [hbase w hw]

theorem Setup.bias_cancels {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ((s.leftModels Q hQ hn).map WindowModel.bias).sum +
      ((s.rightModels Q hQ hn).map WindowModel.bias).sum = 0 := by
  rw [Setup.leftModels, Setup.rightModels, List.map_cons, List.sum_cons,
    s.signed_bias_sum Q G hQ hn leftSigned (left_base Q),
    s.signed_bias_sum Q Q hQ hn rightSigned (right_base Q), left_offsets, right_offsets]
  change -(leftOffset • G + rightOffset • Q) + leftOffset • G + rightOffset • Q = 0
  abel

def initialRoot : BasisState := zeroBasisState[836 ↦ true]

theorem initialRoot_input : FirstWindowInput initialRoot := firstWindowInput_start

theorem initialRoot_clean : Clean streamAddress initialRoot := by
  intro v hv
  have he := (show ∀ v ∈ streamAddress, v ≠ 836 by decide +kernel) v hv
  simp only [initialRoot, upd, if_neg he, zeroBasisState]

theorem Setup.ready {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    Ready (s.leftModels Q hQ hn ++ s.rightModels Q hQ hn) (ket initialRoot) := by
  rw [Setup.leftModels, Setup.rightModels, List.cons_append, ← List.map_append]
  exact ready_first_signed s.signedLaw s.signedWires s.first s.firstLaw s.firstWires
    Q hQ hn (leftSigned ++ rightSigned) initialRoot initialRoot_input initialRoot_clean

theorem Setup.kernel {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    KernelLaw Q initialRoot (s.leftModels Q hQ hn) (s.rightModels Q hQ hn) (ket initialRoot) := by
  rw [Setup.leftModels, Setup.rightModels]
  apply kernelLaw_of_windows Q initialRoot (ket initialRoot) (s.firstModel Q hQ hn)
    (leftSigned.map (s.signedModel Q hQ hn)) (rightSigned.map (s.signedModel Q hQ hn))
  · exact firstModel_firstRule s.first s.firstLaw s.firstWires Q hQ hn initialRoot initialRoot_clean
  · intro w hw
    rw [← List.map_append] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact signedModel_pointRule s.signedLaw s.signedWires Q hQ hn v
      initialRoot initialRoot_input initialRoot_clean
  · simpa only [Setup.leftModels] using s.left_weights Q hQ hn
  · simpa only [Setup.rightModels] using s.right_weights Q hQ hn
  · simpa only [Setup.leftModels, Setup.rightModels] using s.bias_cancels Q hQ hn

theorem Setup.left_precision {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : precision (s.leftModels Q hQ hn) = 263 := by
  rw [precision, Setup.leftModels, List.map_cons, List.sum_cons]
  have hlen : (bank 16).length = 16 := by decide +kernel
  simp only [Setup.firstModel, ShorECDLP.Entrant.Single.Distribution.firstModel, s.firstWires, List.length_reverse, hlen,
    List.map_map, Function.comp_def, s.signed_length, left_signed_width]

theorem Setup.right_precision {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : precision (s.rightModels Q hQ hn) = 263 := by
  rw [precision, Setup.rightModels]
  simp only [List.map_map, Function.comp_def, s.signed_length, right_signed_width]

theorem Setup.left_metadata {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ((s.leftModels Q hQ hn).map WindowModel.physical).map
      (fun w => (w.count, w.wires.length)) = leftMetadata := by
  have hlen : (bank 16).length = 16 := by decide +kernel
  simp only [Setup.leftModels, List.map_cons, List.map_map, Function.comp_def,
    Setup.firstModel, ShorECDLP.Entrant.Single.Distribution.firstModel, Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel, s.firstCount, s.signedCount,
    s.firstWires, s.signedWires, List.length_reverse, hlen, bank_width]
  simp [leftSigned, leftMetadata, List.ofFn_succ, SignedWindow.width]

theorem Setup.right_metadata {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ((s.rightModels Q hQ hn).map WindowModel.physical).map
      (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp only [Setup.rightModels, List.map_map, Function.comp_def,
    Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel, s.signedCount, s.signedWires, List.length_reverse, bank_width]
  simp [rightSigned, rightMetadata, List.ofFn_succ, SignedWindow.width]

theorem Setup.left_count {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    axisCount ((s.leftModels Q hQ hn).map WindowModel.physical) = 491391446 := by
  rw [← recordCount_eq_axisCount, s.left_metadata, left_record_count]

theorem Setup.left_positions {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (start : Nat) :
    axisPositions ((s.leftModels Q hQ hn).map WindowModel.physical) start = positions leftMetadata start := by
  rw [axisPositions, s.left_metadata]

theorem Setup.right_positions {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (start : Nat) :
    axisPositions ((s.rightModels Q hQ hn).map WindowModel.physical) start = positions rightMetadata start := by
  rw [axisPositions, s.right_metadata]

/-- One 263/263 Streaming trial reaches the protected verifier with probability
at least 99/100, assuming only the per-window coherent contracts and metadata. -/
theorem Setup.success {n : Nat} {coeffs : Fin n → PointCoeff} (s : Setup coeffs)
    (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) (hQ : order • Q = 0)
    (J : Instrument) (hJ : ∀ ψ, J.bornMass ψ = normSq ψ) :
    (99 : ℝ) / 100 ≤ Instrument.bornMass
      (((physicalAxes (s.leftModels Q hQ hn) (s.rightModels Q hQ hn) 0 Fin.elim0).seq J).filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket initialRoot) := by
  apply success_of_event_distribution Q d hn hd _ (ket initialRoot) initialRoot
  have hm := physicalTwoAxes_event_mass Q initialRoot (s.leftModels Q hQ hn)
    (s.rightModels Q hQ hn) 0 Fin.elim0 (ket initialRoot) (s.ready Q hQ hn)
    (s.kernel Q hQ hn) J hJ (boundedRecovered d)
  rw [selectedTwoAxes_fixed_filter, s.left_count, s.left_positions, s.right_positions,
    s.left_precision, s.right_precision, idealEventMass_bounded_eq Q d hd] at hm
  simpa only [pairAccept, historyRecovered, trialPositions, Vector.toList_mk,
    List.toList_toArray] using hm

end
end ShorECDLP.Entrant.Single.Distribution

end

-- ==== part: Single/ConcreteDistribution ====

section
/-! Connect the distribution theorem to the real coherent bodies. Fourier
metadata is most-significant-first; lookup addresses remain little-endian. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option pp.maxSteps 60

theorem firstInputLaw : WindowLaw mixedCoefficientAt firstWindow firstUpdate FirstWindowInput := by
  intro Q hQ _hn start history
  obtain ⟨cs, hc, hm⟩ := firstWindow_coherent Q hQ start history
  exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (firstWindowInput_lookup s hs)), hm⟩

/-- All premises of the abstract distribution theorem are supplied by real bodies. -/
def concreteSetup : Setup mixedCoefficientAt where
  first := firstWindow
  signed := signedWindow
  firstLaw := firstInputLaw
  signedLaw := concreteSignedWindowLaw
  firstWires := by unfold firstWindow; rfl
  signedWires := signedWindow_wires
  firstCount := by unfold firstWindow; rfl
  signedCount := fun w => signedWindow_count w

def terminalInstrument : Instrument :=
  (AdaptiveCircuit.unitary [.X 836]
    (measureResetWithCorrection resetWires (fun _ => List.nil))).run

theorem terminalInstrument_mass (ψ : State) : terminalInstrument.bornMass ψ = normSq ψ := by
  calc
    _ = (measureResetWithCorrection resetWires (fun _ => List.nil)).run.bornMass
        (Quantum.run [.X 836] ψ) := by
      simp only [terminalInstrument, AdaptiveCircuit.run, Instrument.bornMass,
        List.map_map, Function.comp_def]
      rfl
    _ = normSq (Quantum.run [.X 836] ψ) := resetRegister_mass _ _
    _ = normSq ψ := normSq_run _ (by simp [CircuitWellFormed, Gate.WellFormed]) ψ

/-- Concrete 263/263 Streaming recovery, including exceptional arithmetic branches. -/
theorem concrete_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G)
    (hQ : order • Q = 0) :
    (99 : ℝ) / 100 ≤ Instrument.bornMass
      (((physicalAxes (concreteSetup.leftModels Q hQ hn) (concreteSetup.rightModels Q hQ hn)
        0 Fin.elim0).seq terminalInstrument).filter
          (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket initialRoot) :=
  concreteSetup.success Q d hn hd hQ terminalInstrument terminalInstrument_mass

theorem concrete_model_left (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (concreteSetup.leftModels Q hQ hn).map WindowModel.physical = ShorECDLP.Entrant.Single.leftWindows := by
  simp only [Setup.leftModels, Setup.firstModel, ShorECDLP.Entrant.Single.Distribution.firstModel, Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel,
    concreteSetup, ShorECDLP.Entrant.Single.leftWindows, List.map_cons, List.map_map, Function.comp_def]

theorem concrete_model_right (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (concreteSetup.rightModels Q hQ hn).map WindowModel.physical = ShorECDLP.Entrant.Single.rightWindows := by
  simp only [Setup.rightModels, Setup.signedModel, ShorECDLP.Entrant.Single.Distribution.signedModel,
    concreteSetup, ShorECDLP.Entrant.Single.rightWindows, List.map_map, Function.comp_def]

def physicalAxesData {n : Nat} (left right : List (Window n)) (read : ConstantBit n → Bool)
    (start : Nat) (history : Fin start → Bool) : Instrument :=
  (((axis left start List.nil).append (axis right (start + axisCount left) List.nil)).instantiate read history).run

theorem physicalAxes_asData {n : Nat} {read : ConstantBit n → Bool}
    (left right : List (WindowModel read)) (start : Nat) (history : Fin start → Bool) :
    physicalAxes left right start history = physicalAxesData (left.map WindowModel.physical)
      (right.map WindowModel.physical) read start history := rfl

theorem prefix_filter_mass (I : Instrument) (gs : Circuit) (accept : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((I.map (fun b =>
      ({history := List.nil, kraus := Quantum.run gs} : InstrumentBranch).seq b)).filter
        (fun b => accept b.history)) ψ =
      Instrument.bornMass (I.filter (fun b => accept b.history)) (Quantum.run gs ψ) := by
  rw [List.filter_map]
  simp only [Function.comp_def, InstrumentBranch.seq, List.nil_append, Instrument.bornMass,
    List.map_map, LinearMap.comp_apply]

theorem append_run_fixed_right {n start a b finish : Nat}
    (p : Straight n start a) (q : Straight n a b) (r : Straight n b finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hr : ∀ h, (r.instantiate read h).run = target.run) :
    ((p.append (q.append r)).instantiate read history).run =
      ((p.append q).instantiate read history).run.seq target.run := by
  rw [append_run_history]
  simp_rw [append_run_fixed q r read _ target hr, AdaptiveCircuit.run_seq]
  rw [append_run_history]
  simp only [Instrument.seq, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro x hx
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro z hz
  rcases x with ⟨xh, xk⟩
  rcases y with ⟨yh, yk⟩
  rcases z with ⟨zh, zk⟩
  simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem straight_gate_run {n start finish : Nat} (g : TemplateGate n) (p : Straight n start finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((Straight.gate g p).instantiate read history).run =
      ((p.instantiate read history).run).map (fun b =>
        ({history := List.nil, kraus := Quantum.run (g.instantiate read)} : InstrumentBranch).seq b) := rfl

attribute [local irreducible] axis resetProgram

theorem unitary_run_map (gs : Circuit) (tail : AdaptiveCircuit) :
    (AdaptiveCircuit.unitary gs tail).run = tail.run.map (fun b =>
      ({history := List.nil, kraus := Quantum.run gs} : InstrumentBranch).seq b) := rfl

theorem framed_reset_run {n start a b finish out : Nat}
    (p : Straight n start a) (q : Straight n a b) (r : Straight n b finish) (h : finish = out)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hr : ∀ history, (r.instantiate read history).run = target.run) :
    ((framed p q r h).instantiate read history).run =
      (((p.append q).instantiate read history).run.seq (AdaptiveCircuit.unitary [.X 836] target).run).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  have ht : ∀ history, ((Straight.gate (.literal (.X 836)) r).instantiate read history).run =
      (AdaptiveCircuit.unitary [.X 836] target).run := by
    intro history
    rw [straight_gate_run, hr history, unitary_run_map]
    rfl
  rw [framed_run, unitary_run_map, append_run_fixed_right _ _ _ _ _ _ ht]

theorem program_run_data (read : ConstantBit 851968 → Bool) :
    (ShorECDLP.Entrant.Single.program.instantiate read Fin.elim0).run =
      ((physicalAxesData leftWindows rightWindows read 0 Fin.elim0).seq terminalInstrument).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  calc
    _ = ((ShorECDLP.Entrant.Single.trial 0).instantiate read Fin.elim0).run := by
      unfold ShorECDLP.Entrant.Single.program
      rw [castFinish_instantiate]
    _ = _ := by
      have hf : 0 + axisCount leftWindows + axisCount rightWindows + 854 = 0 + trialCount := by
        unfold trialCount
        omega
      simpa only [ShorECDLP.Entrant.Single.trial, physicalAxesData, terminalInstrument] using
        framed_reset_run (axis leftWindows 0 List.nil)
          (axis rightWindows (0 + axisCount leftWindows) List.nil)
          (resetBody (0 + axisCount leftWindows + axisCount rightWindows)) hf read Fin.elim0
          (measureResetWithCorrection resetWires (fun _ => List.nil))
          (resetBody_run _ read)

theorem concrete_axes_data (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    physicalAxes (concreteSetup.leftModels Q hQ hn) (concreteSetup.rightModels Q hQ hn) 0 Fin.elim0 =
      physicalAxesData leftWindows rightWindows (readConstant mixedCoefficientAt Q) 0 Fin.elim0 := by
  change physicalAxesData _ _ _ _ _ = _
  rw [concrete_model_left Q hQ hn, concrete_model_right Q hQ hn]

/-- Bind the distribution proof to the shared assembled program, including its reset. -/
theorem assembled_program_run (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (ShorECDLP.Entrant.Single.program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).run =
      ((physicalAxes (concreteSetup.leftModels Q hQ hn) (concreteSetup.rightModels Q hQ hn)
        0 Fin.elim0).seq terminalInstrument).map
          (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  exact (program_run_data (readConstant mixedCoefficientAt Q)).trans
    (congrArg (fun I : Instrument => (I.seq terminalInstrument).map
      (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b))
        (concrete_axes_data Q hQ hn).symm)

/-- Success for the exact shared single-trial straight program, with the protected
sparse 263/263 nearest-pair decoder, from the all-zero input state. -/
theorem program_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ) / 100 ≤ Instrument.bornMass
      (((ShorECDLP.Entrant.Single.program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by
    rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [assembled_program_run Q hQ hn,
    prefix_filter_mass _ ([Gate.X 836]) (fun history => (verifiedCandidate layout Q history).isSome) (ket zeroBasisState)]
  have hs : Quantum.run [.X 836] (ket zeroBasisState) = ket initialRoot := by
    simp [Quantum.run, applyGate_ket, onKet, initialRoot, zeroBasisState]
  rw [hs]
  exact concrete_success Q d hn hd hQ

end
end ShorECDLP.Entrant.Single.Distribution

end
