import ShorECDLP.Submission.Entrant.RootPass
import ShorECDLP.Submission.Entrant.KnownRoot
import ShorECDLP.Submission.Entrant.Prefix
import ShorECDLP.Submission.Entrant.TightSupport
import ShorECDLP.Submission.Entrant.WideBank8
import ShorECDLP.Submission.Entrant.First18Loader
import ShorECDLP.Submission.Entrant.MixedBridge
import ShorECDLP.Submission.Entrant.NarrowFused

/-! Mixed-first-load schedule. Physical implementations remain explicit parameters.
    The 17-wire first load is one joint table over the 12 top bits of the left axis and the 5 top
    bits of the right axis, followed by 9 logical17 + 6 logical16 left digits and
    11 logical17 + 1 logical16 right digits (27 body windows). -/
namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] List.ofFn
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

inductive Digit where
  | left17 (index : Fin 11)
  | left16 (index : Fin 4)
  | right17 (index : Fin 8)
  | right16 (index : Fin 4)

def Digit.width : Digit → Nat
  | .left17 _ | .right17 _ => 17
  | .left16 _ | .right16 _ => 16

def Digit.exponent : Digit → Nat
  | .left17 j => 234 - 17*j.val
  | .left16 j => 48 - 16*j.val
  | .right17 j => 183 - 17*j.val
  | .right16 j => 48 - 16*j.val

def Digit.base (Q : Point) : Digit → Point
  | .left17 _ | .left16 _ => G
  | .right17 _ | .right16 _ => Q

def leftDigits : List Digit := List.ofFn (fun j : Fin 11 => .left17 j) ++
  List.ofFn (fun j : Fin 4 => .left16 j)
def rightDigits : List Digit := List.ofFn (fun j : Fin 8 => .right17 j) ++
  List.ofFn (fun j : Fin 4 => .right16 j)
/-- Axis bank widths in chronological order; the heads (10 and 8) come from the joint first load. -/
def leftWidths : List Nat := 10 :: List.replicate 11 17 ++ List.replicate 4 16
def rightWidths : List Nat := 8 :: List.replicate 8 17 ++ List.replicate 4 16

theorem width_cases (w : Digit) : w.width = 16 ∨ w.width = 17 := by
  cases w <;> simp [Digit.width]
theorem left_widths : leftDigits.map Digit.width = List.replicate 11 17 ++ List.replicate 4 16 := by
  simp [leftDigits, List.ofFn_succ, Digit.width, List.replicate]
theorem right_widths : rightDigits.map Digit.width = List.replicate 8 17 ++ List.replicate 4 16 := by
  simp [rightDigits, List.ofFn_succ, Digit.width, List.replicate]
theorem precisions : leftWidths.sum = 261 ∧ rightWidths.sum = 208 ∧
    leftDigits.length = 15 ∧ rightDigits.length = 12 := by
  norm_num [leftWidths, rightWidths, leftDigits, rightDigits, List.replicate]

def leftOffset : Nat := (leftDigits.map (fun w => offsetScalar w.width w.exponent)).sum
def rightOffset : Nat := (rightDigits.map (fun w => offsetScalar w.width w.exponent)).sum

/-- The joint first table: the low eight address bits are the right-axis head digit and the high
    ten are the left-axis head digit. -/
def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients ((v / 256) * 2^251 + leftOffset) ((v % 256) * 2^200 + rightOffset)

def signedCoefficients (w : Digit) (a : Nat) : PointCoeff :=
  match w with
  | .left17 _ | .left16 _ => coefficients (oddScalar w.exponent a) 0
  | .right17 _ | .right16 _ => coefficients 0 (oddScalar w.exponent a)

/-- Raw rows are intentionally over the official limit. Specialize the generator
    block before certifying against officialLimits. -/
def coefficientAt (i : Fin 1769472) : PointCoeff :=
  if i.val < 262144 then initialCoefficients i.val
  else if i.val < 983040 then
    coefficients (oddScalar (234 - 17*((i.val-262144)/65536)) ((i.val-262144)%65536)) 0
  else if i.val < 1114112 then
    coefficients (oddScalar (48 - 16*((i.val-983040)/32768)) ((i.val-983040)%32768)) 0
  else if i.val < 1638400 then
    coefficients 0 (oddScalar (183 - 17*((i.val-1114112)/65536)) ((i.val-1114112)%65536))
  else coefficients 0 (oddScalar (48 - 16*((i.val-1638400)/32768)) ((i.val-1638400)%32768))

def firstRow (a : Fin 262144) : Fin 1769472 := ⟨a.val, by omega⟩
def row : (w : Digit) → Fin (2^(w.width-1)) → Fin 1769472
  | .left17 j, a => ⟨262144 + j.val*65536 + a.val, by
      have : a.val < 65536 := by simpa only [Digit.width] using a.isLt
      omega⟩
  | .left16 j, a => ⟨983040 + j.val*32768 + a.val, by
      have : a.val < 32768 := by simpa only [Digit.width] using a.isLt
      omega⟩
  | .right17 j, a => ⟨1114112 + j.val*65536 + a.val, by
      have : a.val < 65536 := by simpa only [Digit.width] using a.isLt
      omega⟩
  | .right16 j, a => ⟨1638400 + j.val*32768 + a.val, by
      have : a.val < 32768 := by simpa only [Digit.width] using a.isLt
      omega⟩

theorem coefficientAt_first (a : Fin 262144) :
    ShorECDLP.Entrant.Width16Schedule.coefficientAt (firstRow a) = initialCoefficients a.val := by
  simp [ShorECDLP.Entrant.Width16Schedule.coefficientAt, firstRow, a.isLt]

theorem coefficientAt_row (w : Digit) (a : Fin (2^(w.width-1))) :
    ShorECDLP.Entrant.Width16Schedule.coefficientAt (row w a) = signedCoefficients w a.val := by
  cases w with
  | left17 j =>
    have ha : a.val < 65536 := by simpa only [Digit.width] using a.isLt
    have h0 : ¬ (row (.left17 j) a).val < 262144 := by simp only [row]; omega
    have h1 : (row (.left17 j) a).val < 983040 := by simp only [row]; omega
    have hj : ((row (.left17 j) a).val-262144)/65536 = j.val := by simp only [row]; omega
    have hh : ((row (.left17 j) a).val-262144)%65536 = a.val := by simp only [row]; omega
    simp [ShorECDLP.Entrant.Width16Schedule.coefficientAt, h0, h1, hj, hh, signedCoefficients, Digit.exponent]
  | left16 j =>
    have ha : a.val < 32768 := by simpa only [Digit.width] using a.isLt
    have h0 : ¬ (row (.left16 j) a).val < 262144 := by simp only [row]; omega
    have h1 : ¬ (row (.left16 j) a).val < 983040 := by simp only [row]; omega
    have h2 : (row (.left16 j) a).val < 1114112 := by simp only [row]; omega
    have hj : ((row (.left16 j) a).val-983040)/32768 = j.val := by simp only [row]; omega
    have hh : ((row (.left16 j) a).val-983040)%32768 = a.val := by simp only [row]; omega
    simp [ShorECDLP.Entrant.Width16Schedule.coefficientAt, h0, h1, h2, hj, hh, signedCoefficients, Digit.exponent]
  | right17 j =>
    have ha : a.val < 65536 := by simpa only [Digit.width] using a.isLt
    have h0 : ¬ (row (.right17 j) a).val < 262144 := by simp only [row]; omega
    have h1 : ¬ (row (.right17 j) a).val < 983040 := by simp only [row]; omega
    have h2 : ¬ (row (.right17 j) a).val < 1114112 := by simp only [row]; omega
    have h3 : (row (.right17 j) a).val < 1638400 := by simp only [row]; omega
    have hj : ((row (.right17 j) a).val-1114112)/65536 = j.val := by simp only [row]; omega
    have hh : ((row (.right17 j) a).val-1114112)%65536 = a.val := by simp only [row]; omega
    simp [ShorECDLP.Entrant.Width16Schedule.coefficientAt, h0, h1, h2, h3, hj, hh, signedCoefficients, Digit.exponent]
  | right16 j =>
    have ha : a.val < 32768 := by simpa only [Digit.width] using a.isLt
    have h0 : ¬ (row (.right16 j) a).val < 262144 := by simp only [row]; omega
    have h1 : ¬ (row (.right16 j) a).val < 983040 := by simp only [row]; omega
    have h2 : ¬ (row (.right16 j) a).val < 1114112 := by simp only [row]; omega
    have h3 : ¬ (row (.right16 j) a).val < 1638400 := by simp only [row]; omega
    have hj : ((row (.right16 j) a).val-1638400)/32768 = j.val := by simp only [row]; omega
    have hh : ((row (.right16 j) a).val-1638400)%32768 = a.val := by simp only [row]; omega
    simp [ShorECDLP.Entrant.Width16Schedule.coefficientAt, h0, h1, h2, h3, hj, hh, signedCoefficients, Digit.exponent]

def initialPoint (Q : Point) (v : Nat) : Point :=
  ((v/256)*2^251 + leftOffset) • G + ((v%256)*2^200 + rightOffset) • Q

def positivePoint (Q : Point) (w : Digit) (a : Nat) : Point :=
  oddScalar w.exponent a • w.base Q

theorem initialCoefficients_point (Q : Point) (hQ : order • Q = 0) (v : Nat) :
    constantPoint Q (initialCoefficients v) = initialPoint Q v := by
  unfold initialCoefficients initialPoint
  exact coefficients_point _ _ Q hQ

theorem signedCoefficients_point (Q : Point) (hQ : order • Q = 0) (w : Digit) (a : Nat) :
    constantPoint Q (signedCoefficients w a) = positivePoint Q w a := by
  cases w <;> simp [signedCoefficients, coefficients_point _ _ Q hQ, positivePoint, Digit.base]

theorem odd_scalar_ne_zero (P : Point) (hr : order • P = 0) (hp : P ≠ 0)
    (exponent a : Nat) (ha : 2*a+1 < order) : oddScalar exponent a • P ≠ 0 := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf P = order := addOrderOf_eq_prime hr hp
  have hs : 0 < 2*a+1 := by omega
  have horder : 2 < order := by norm_num [order]
  have hh : 0 < halfOrder ∧ halfOrder < order := by dsimp [Single.halfOrder]; omega
  have hodd : ¬ order ∣ 2*a+1 := fun h => (Nat.le_of_dvd hs h).not_gt ha
  have hhalf : ¬ order ∣ halfOrder := fun h => (Nat.le_of_dvd hh.1 h).not_gt hh.2
  have htwo : ¬ order ∣ 2 := by
    intro h
    have hl : 2 < order := by norm_num [order]
    exact (Nat.le_of_dvd (by decide +kernel : 0 < 2) h).not_gt hl
  intro hz
  have he : ((2*a+1)*2^exponent*halfOrder) • P = 0 := by simpa only [oddScalar] using hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  rw [ho] at hd
  rcases order_prime.dvd_mul.mp hd with hd | hd
  · rcases order_prime.dvd_mul.mp hd with hd | hd
    · exact hodd hd
    · exact htwo (order_prime.dvd_of_dvd_pow hd)
  · exact hhalf hd

theorem positivePoint_ne_zero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (a : Nat) (ha : a < 2^(w.width-1)) : positivePoint Q w a ≠ 0 := by
  have hp : w.base Q ≠ 0 := by
    cases w with
    | left17 _ | left16 _ => exact G_ne_zero
    | right17 _ | right16 _ => exact hn
  have hr : order • w.base Q = 0 := by
    cases w with
    | left17 _ | left16 _ => exact generator_nsmul_eq_zero
    | right17 _ | right16 _ => exact hQ
  have hw : 2^(w.width-1) ≤ 65536 := by cases w <;> norm_num [Digit.width]
  have hl : 131071 < order := by norm_num [order]
  exact odd_scalar_ne_zero (w.base Q) hr hp w.exponent a (by omega)

theorem row_nonzero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (a : Fin (2^(w.width-1))) : constantPoint Q (ShorECDLP.Entrant.Width16Schedule.coefficientAt (row w a)) ≠ 0 := by
  rw [coefficientAt_row, signedCoefficients_point Q hQ]
  exact positivePoint_ne_zero Q hQ hn w a.val a.isLt

/-- Reuse the existing width-independent group calculation. Its only width
    identity, 2^width = 2*2^(width-1), is proved here at widths16/17. -/
def increment (P : Point) (width exponent v : Nat) : Point :=
  ((2*(v:Int)-(2:Int)^width+1):Int) • ((halfOrder*2^exponent) • P)

theorem increment_offset (P : Point) (hr : order • P = 0)
    (width exponent v : Nat) (hw : width = 16 ∨ width = 17) :
    increment P width exponent v + offsetScalar width exponent • P = (v*2^exponent) • P := by
  have hh : halfOrder ≤ 2^(width-1)+order := by
    have hl : halfOrder ≤ order := by
      have horder : 0 < order := by norm_num [order]
      dsimp [Single.halfOrder]
      omega
    exact hl.trans (Nat.le_add_left _ _)
  have he : (2^(width-1)+order-halfOrder) • P + halfOrder • P = 2^(width-1) • P := by
    rw [← add_nsmul, Nat.sub_add_cancel hh, add_nsmul, hr, add_zero]
  have hoff : offsetScalar width exponent • P =
      2^(width-1) • (2^exponent • P) - (halfOrder*2^exponent) • P := by
    unfold offsetScalar
    rw [mul_smul, smul_comm (2^(width-1)+order-halfOrder) (2^exponent),
      eq_sub_iff_add_eq.mpr he, nsmul_sub]
    simp only [mul_smul]
    rw [smul_comm (2^exponent) (2^(width-1)), smul_comm (2^exponent) halfOrder]
  let H := (halfOrder*2^exponent) • P
  have hd : H+H = 2^exponent • P := by
    change (halfOrder*2^exponent) • P + (halfOrder*2^exponent) • P = _
    rw [mul_smul, smul_comm halfOrder (2^exponent), ← nsmul_add]
    exact congrArg (fun R : Point => 2^exponent • R)
      (signedWindowHalfPoint_double P order (by decide +kernel) hr)
  have hp : (2:Int)^width = 2*(2^(width-1):Nat) := by rcases hw with rfl | rfl <;> norm_num
  have hcalc : ((2*(v:Int)-(2:Int)^width+1) • H) +
      (2^(width-1) • (H+H)-H) = v • (H+H) := by rw [hp]; module
  change ((2*(v:Int)-(2:Int)^width+1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2^exponent) P).symm

def SignedWeights (Q P : Point) : List Digit → Prop
  | List.nil => True
  | w::ws => w.base Q = P ∧ w.exponent = (ws.map Digit.width).sum ∧ SignedWeights Q P ws

theorem left_signed_weights (Q : Point) : SignedWeights Q G leftDigits := by
  norm_num [leftDigits, List.ofFn_succ, SignedWeights, Digit.width, Digit.exponent, Digit.base]
theorem right_signed_weights (Q : Point) : SignedWeights Q Q rightDigits := by
  norm_num [rightDigits, List.ofFn_succ, SignedWeights, Digit.width, Digit.exponent, Digit.base]

theorem modelWeights {n : Nat} {read : ConstantBit n → Bool}
    (Q P : Point) (hr : order • P = 0) (f : Digit → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = w.width)
    (hpoint : ∀ w v, (f w).point v = increment (w.base Q) w.width w.exponent v)
    (hbias : ∀ w, (f w).bias = offsetScalar w.width w.exponent • w.base Q)
    (ws : List Digit) (hw : SignedWeights Q P ws) : ModelWeights P (ws.map f) := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · intro v
      have hwidths : ((ws.map f).map (fun w => w.physical.wires.length)).sum =
          (ws.map Digit.width).sum := by simp only [List.map_map, Function.comp_def, hwidth]
      rw [hwidths, ← hw.2.1, hpoint, hbias, hw.1]
      exact increment_offset P hr w.width w.exponent v (width_cases w)
    · exact ih hw.2.2

theorem left_base (Q : Point) (w : Digit) (hw : w ∈ leftDigits) : w.base Q = G := by
  simp only [leftDigits, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem right_base (Q : Point) (w : Digit) (hw : w ∈ rightDigits) : w.base Q = Q := by
  simp only [rightDigits, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
-- TODO(mixed): `mixed_kernel` replaces the old `model_kernel` (see MixedAlgebra.mixed_branch_state).

end
end ShorECDLP.Entrant.Width16Schedule


/-! Generic specialization transport, attributed to resume-astra/Specialize.lean
    and generator-wide/FixedSchedule.lean. No selected baseline is embedded. -/
namespace ShorECDLP.Entrant.Width16Schedule.Specialization
open ShorECDLP.Challenge ShorECDLP.Quantum ShorECDLP.Secp256k1

def specializeGate {n m : Nat} (classify : ConstantBit n → Bool ⊕ ConstantBit m)
    (zero : ConstantBit m) : TemplateGate n → TemplateGate m
  | .literal g => .literal g
  | .whenBit r v g =>
      match classify r with
      | .inl b => if b = v then .literal g else .whenBit zero true g
      | .inr r' => .whenBit r' v g

def specialize {n m s e : Nat} (classify : ConstantBit n → Bool ⊕ ConstantBit m)
    (zero : ConstantBit m) : Straight n s e → Straight m s e
  | .done => .done
  | .gate g p => .gate (specializeGate classify zero g) (specialize classify zero p)
  | .recordGate i v g p => .recordGate i v g (specialize classify zero p)
  | .measure w p => .measure w (specialize classify zero p)

theorem specializeGate_instantiate {n m : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (old : ConstantBit n → Bool) (fresh : ConstantBit m → Bool)
    (hz : fresh zero = false)
    (agree : ∀ r, old r = (classify r).elim id fresh) (g : TemplateGate n) :
    (specializeGate classify zero g).instantiate fresh = g.instantiate old := by
  cases g with
  | literal g => rfl
  | whenBit r v g =>
    have hr := agree r
    cases hc : classify r with
    | inl b =>
      simp only [hc, Sum.elim_inl, id_eq] at hr
      by_cases h : b = v <;> simp [specializeGate, hc, TemplateGate.instantiate, hr, hz, h]
    | inr r' =>
      simp only [hc, Sum.elim_inr] at hr
      simp [specializeGate, hc, TemplateGate.instantiate, hr]

theorem specialize_instantiate {n m s e : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (old : ConstantBit n → Bool) (fresh : ConstantBit m → Bool)
    (hz : fresh zero = false)
    (agree : ∀ r, old r = (classify r).elim id fresh)
    (p : Straight n s e) (history : Fin s → Bool) :
    (specialize classify zero p).instantiate fresh history = p.instantiate old history := by
  induction p with
  | done => rfl
  | gate g p ih =>
    simp only [specialize, Straight.instantiate,
      specializeGate_instantiate classify zero old fresh hz agree, ih]
  | recordGate i v g p ih => simp only [specialize, Straight.instantiate, ih]
  | measure w p ih => simp only [specialize, Straight.instantiate, ih]

theorem specializeGate_wellFormed {n m : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (g : TemplateGate n) :
    (specializeGate classify zero g).WellFormed = g.WellFormed := by
  cases g with
  | literal g => rfl
  | whenBit r v g =>
    cases hc : classify r with
    | inl b => simp only [specializeGate, hc]; split <;> rfl
    | inr r' => simp only [specializeGate, hc, TemplateGate.WellFormed]

theorem specialize_wellFormed {n m s e : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (p : Straight n s e) :
    (specialize classify zero p).WellFormed = p.WellFormed := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [specialize, Straight.WellFormed, specializeGate_wellFormed, ih]
  | recordGate i v g p ih => simp only [specialize, Straight.WellFormed, ih]
  | measure w p ih => exact ih

theorem specialize_slots {n m s e : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (p : Straight n s e) : (specialize classify zero p).gateSlots = p.gateSlots := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [specialize, Straight.gateSlots, ih]
  | recordGate i v g p ih => simp only [specialize, Straight.gateSlots, ih]
  | measure w p ih => exact ih

theorem generator_only_constantPoint (c : PointCoeff) (hb : c.b.val = 0) (Q R : Point) :
    constantPoint Q c = constantPoint R c := by
  simp [constantPoint, hb]

theorem generator_only_readConstant {n : Nat} (coeffs : Fin n → PointCoeff)
    (r : ConstantBit n) (hb : (coeffs r.point).b.val = 0) (Q R : Point) :
    readConstant coeffs Q r = readConstant coeffs R r := by
  unfold readConstant
  rw [generator_only_constantPoint (coeffs r.point) hb Q R]

def specializeEntry (e : StraightEntry) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length) : StraightEntry where
  coefficients := coeffs
  finalCursor := e.finalCursor
  program := specialize classify zero e.program

theorem specializeEntry_instantiate (e : StraightEntry) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length) (Q : Point)
    (hz : readConstant coeffs.get Q zero = false)
    (agree : ∀ r, readConstant e.coefficients.get Q r =
      (classify r).elim id (readConstant coeffs.get Q)) :
    (specializeEntry e coeffs classify zero).instantiate Q = e.instantiate Q :=
  specialize_instantiate classify zero _ _ hz agree e.program Fin.elim0

theorem specialize_certificate (limits : Limits) (layout : DecodeLayout)
    (e : StraightEntry) (bounds : Bounds) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length)
    (hz : ∀ Q, readConstant coeffs.get Q zero = false)
    (agree : ∀ Q r, readConstant e.coefficients.get Q r =
      (classify r).elim id (readConstant coeffs.get Q))
    (h : Certificate { limits with coefficientRows := e.coefficients.length } layout e bounds)
    (ht : coeffs.length ≤ limits.coefficientRows) :
    Certificate limits layout (specializeEntry e coeffs classify zero) bounds := by
  have he (Q : Point) := specializeEntry_instantiate e coeffs classify zero Q (hz Q) (agree Q)
  refine ⟨?_, h.recordBudget, ht, h.candidateBudget, ?_, ?_, ?_⟩
  · simpa only [specializeEntry, specialize_slots] using h.gateBudget
  · exact (specialize_wellFormed classify zero e.program).mpr h.wellFormed
  · intro Q
    rw [he Q]
    exact h.resources Q
  · intro Q d hn hd
    rw [he Q]
    exact h.success Q d hn hd

-- Entry-level statements keep the very large program abstract during elaboration.
theorem specializeEntry_properties (e : StraightEntry) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length) :
    (specializeEntry e coeffs classify zero).program.gateSlots = e.program.gateSlots ∧
    (specializeEntry e coeffs classify zero).program.WellFormed = e.program.WellFormed ∧
    (specializeEntry e coeffs classify zero).finalCursor = e.finalCursor ∧
    (specializeEntry e coeffs classify zero).coefficients.length = coeffs.length :=
  ⟨specialize_slots classify zero e.program, specialize_wellFormed classify zero e.program, rfl, rfl⟩

theorem specialize_certificate_same_limits (limits : Limits) (layout : DecodeLayout)
    (e : StraightEntry) (bounds : Bounds) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length)
    (hz : ∀ Q, readConstant coeffs.get Q zero = false)
    (agree : ∀ Q r, readConstant e.coefficients.get Q r =
      (classify r).elim id (readConstant coeffs.get Q))
    (h : Certificate limits layout e bounds)
    (ht : coeffs.length ≤ limits.coefficientRows) :
    Certificate limits layout (specializeEntry e coeffs classify zero) bounds := by
  apply specialize_certificate limits layout e bounds coeffs classify zero hz agree
  · exact ⟨h.gateBudget, h.recordBudget, le_rfl, h.candidateBudget,
      h.wellFormed, h.resources, h.success⟩
  · exact ht

end ShorECDLP.Entrant.Width16Schedule.Specialization


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Specialization
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] List.ofFn

/-- The new map preserves First17 and every right row. Only generator body rows
    [262144,1114112) are frozen. Sentinel is the final, all-zero coefficient. -/
@[irreducible] def retainedAt (i : Fin 917505) : PointCoeff :=
  if h : i.val < 262144 then ShorECDLP.Entrant.Width16Schedule.coefficientAt ⟨i.val, by omega⟩
  else if h : i.val < 917504 then ShorECDLP.Entrant.Width16Schedule.coefficientAt ⟨851968+i.val, by omega⟩
  else coefficients 0 0

def sentinel : ConstantBit 917505 := ⟨⟨917504, by decide +kernel⟩, .x, 0⟩

def classify (r : ConstantBit 1769472) : Bool ⊕ ConstantBit 917505 :=
  if h : r.point.val < 262144 then .inr ⟨⟨r.point.val, by omega⟩, r.field, r.bit⟩
  else if r.point.val < 1114112 then .inl (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt (0 : Point) r)
  else .inr ⟨⟨r.point.val-851968, by have := r.point.isLt; omega⟩, r.field, r.bit⟩

theorem fixed_b_zero (i : Fin 1769472) (hlo : 262144 ≤ i.val) (hhi : i.val < 1114112) :
    (ShorECDLP.Entrant.Width16Schedule.coefficientAt i).b.val = 0 := by
  unfold ShorECDLP.Entrant.Width16Schedule.coefficientAt
  rw [if_neg (by omega)]
  split <;> simp [coefficients]

theorem sentinel_false (Q : Point) : readConstant retainedAt Q sentinel = false := by
  simp [sentinel, retainedAt, readConstant, coefficients, constantPoint, fieldValue, pointCoordinates]

theorem retained_agree (Q : Point) (r : ConstantBit 1769472) :
    readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q r = (classify r).elim id (readConstant retainedAt Q) := by
  unfold classify
  split
  next h => simp only [Sum.elim_inr, readConstant, retainedAt, h, ↓reduceDIte]
  next h0 =>
    split
    next h1 =>
      simp only [Sum.elim_inl, id_eq]
      exact generator_only_readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt r (fixed_b_zero _ (by omega) h1) Q 0
    next h1 =>
      simp only [Sum.elim_inr, readConstant]
      have hl : ¬ r.point.val-851968 < 262144 := by omega
      have hh : r.point.val-851968 < 917504 := by have := r.point.isLt; omega
      have he : 851968+(r.point.val-851968) = r.point.val := by omega
      simp only [retainedAt, hl, hh, ↓reduceDIte, he]

def specializeProgram {s e : Nat} (p : Straight 1769472 s e) : Straight 917505 s e :=
  specialize classify sentinel p

theorem program_equality {s e : Nat} (p : Straight 1769472 s e) (Q : Point) (history : Fin s → Bool) :
    (specializeProgram p).instantiate (readConstant retainedAt Q) history =
      p.instantiate (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q) history :=
  specialize_instantiate classify sentinel _ _ (sentinel_false Q) (retained_agree Q) p history

attribute [local irreducible] Straight.instantiate StraightEntry.instantiate
  Straight.gateSlots Straight.WellFormed AdaptiveCircuit.run ShorECDLP.Challenge.resources

def rawLimits : Limits := { officialLimits with coefficientRows := 1769472 }

/-- Keep both lists abstract in every list/index proof. The actual retained
    entry is built directly by fixedEntry from a specialized Fin-indexed program. -/
theorem tableLength {n : Nat} (f : Fin n → PointCoeff) (l : List PointCoeff)
    (h : l=List.ofFn f) : l.length=n := by
  subst l
  exact List.length_ofFn

theorem table_get {n : Nat} (f : Fin n → PointCoeff) (l : List PointCoeff)
    (h : l=List.ofFn f) (hl : l.length=n) (i : Fin l.length) : l.get i=f (Fin.cast hl i) := by
  subst l
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl

variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
set_option linter.unusedSectionVars false

def canonicalProgram {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) : Straight n 0 e.finalCursor :=
  reindexStraight (Fin.cast (tableLength f e.coefficients he)) e.program

def canonicalEntry {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) : StraightEntry := Single.fixedEntry f (canonicalProgram f e he)

theorem canonical_read {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) (Q : Point) :
    readConstant f Q ∘ reindexBit (Fin.cast (tableLength f e.coefficients he)) =
      readConstant e.coefficients.get Q := by
  funext r
  simp only [Function.comp_def,reindexBit,readConstant]
  rw [table_get f e.coefficients he (tableLength f e.coefficients he) r.point]

theorem canonical_instantiate {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) (Q : Point) :
    (canonicalEntry f e he).instantiate Q=e.instantiate Q := by
  rw [canonicalEntry,Single.fixedEntry_instantiate,canonicalProgram,reindexStraight_instantiate,
    canonical_read f e he Q]
  unfold StraightEntry.instantiate
  rfl

theorem canonical_certificate {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) (limits : Limits) (layout : DecodeLayout) (bounds : Bounds)
    (h : Certificate limits layout e bounds) : Certificate limits layout (canonicalEntry f e he) bounds := by
  refine ⟨?_,h.recordBudget,?_,h.candidateBudget,?_,?_,?_⟩
  · simpa only [canonicalEntry,Single.fixedEntry_slots,canonicalProgram,reindexStraight_gateSlots] using h.gateBudget
  · rw [canonicalEntry,Single.fixedEntry_rows]
    have ht := h.tableBudget
    rw [tableLength f e.coefficients he] at ht
    exact ht
  · rw [canonicalEntry,Single.fixedEntry_wellFormed,canonicalProgram,reindexStraight_wellFormed]
    exact h.wellFormed
  · intro Q
    rw [canonical_instantiate]
    exact h.resources Q
  · intro Q d hn hd
    rw [canonical_instantiate]
    exact h.success Q d hn hd

theorem fixed_specialize_certificate {n m e : Nat} (f : Fin n → PointCoeff) (fresh : Fin m → PointCoeff)
    (classifier : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (hz : ∀ Q,readConstant fresh Q zero=false)
    (agree : ∀ Q r,readConstant f Q r=(classifier r).elim id (readConstant fresh Q))
    (p : Straight n 0 e) (limits : Limits) (layout : DecodeLayout) (bounds : Bounds)
    (h : Certificate { limits with coefficientRows:=n } layout (Single.fixedEntry f p) bounds)
    (ht : m ≤ limits.coefficientRows) :
    Certificate limits layout (Single.fixedEntry fresh (specialize classifier zero p)) bounds := by
  have hi (Q : Point) :
      (Single.fixedEntry fresh (specialize classifier zero p)).instantiate Q=(Single.fixedEntry f p).instantiate Q := by
    rw [Single.fixedEntry_instantiate,Single.fixedEntry_instantiate]
    exact specialize_instantiate classifier zero _ _ (hz Q) (agree Q) p Fin.elim0
  refine ⟨?_,h.recordBudget,?_,h.candidateBudget,?_,?_,?_⟩
  · rw [Single.fixedEntry_slots,specialize_slots]
    simpa only [Single.fixedEntry_slots] using h.gateBudget
  · rw [Single.fixedEntry_rows]
    exact ht
  · rw [Single.fixedEntry_wellFormed,specialize_wellFormed]
    exact (Single.fixedEntry_wellFormed f p).mp h.wellFormed
  · intro Q
    rw [hi Q]
    exact h.resources Q
  · intro Q d hn hd
    rw [hi Q]
    exact h.success Q d hn hd

def specializeEntry (e : StraightEntry)
    (he : e.coefficients=List.ofFn ShorECDLP.Entrant.Width16Schedule.coefficientAt) : StraightEntry :=
  Single.fixedEntry retainedAt
    (specializeProgram (canonicalProgram ShorECDLP.Entrant.Width16Schedule.coefficientAt e he))

theorem specializeEntry_equality (e : StraightEntry)
    (he : e.coefficients=List.ofFn ShorECDLP.Entrant.Width16Schedule.coefficientAt) (Q : Point) :
    (specializeEntry e he).instantiate Q=e.instantiate Q := by
  have hc := canonical_instantiate ShorECDLP.Entrant.Width16Schedule.coefficientAt e he Q
  rw [canonicalEntry,Single.fixedEntry_instantiate] at hc
  rw [specializeEntry,Single.fixedEntry_instantiate,program_equality]
  exact hc

theorem specializeEntry_certificate (e : StraightEntry)
    (he : e.coefficients=List.ofFn ShorECDLP.Entrant.Width16Schedule.coefficientAt)
    (layout : DecodeLayout) (bounds : Bounds) (h : Certificate rawLimits layout e bounds) :
    Certificate officialLimits layout (specializeEntry e he) bounds := by
  have hc := canonical_certificate ShorECDLP.Entrant.Width16Schedule.coefficientAt e he rawLimits layout bounds h
  exact fixed_specialize_certificate ShorECDLP.Entrant.Width16Schedule.coefficientAt retainedAt classify sentinel
    sentinel_false retained_agree (canonicalProgram ShorECDLP.Entrant.Width16Schedule.coefficientAt e he)
    officialLimits layout bounds hc (by change 917505 ≤ 983040; omega)

theorem exact_map_accounting :
    262144+11*65536+4*32768+8*65536+4*32768=1769472 ∧
    11*65536+4*32768=851968 ∧
    262144+8*65536+4*32768+1=917505 ∧ 917505 ≤ 983040 := by norm_num

end
end ShorECDLP.Entrant.Width16Schedule


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution ConditionalCatalyst WeightedPhase28
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] List.ofFn
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]

def count (wide normal : Nat) : Digit → Nat
  | .left17 _ | .right17 _ => wide
  | .left16 _ | .right16 _ => normal

/-- The contract of the physical windows. `headA` is the left head bank (12 wires) with the joint
    17-bit first load inside its program; `headB` is the right head bank (5 wires), a Hadamard
    palindrome that only measures. The 27 body windows are the signed windows. -/
structure Implementation where
  records17 : Nat
  records16 : Nat
  credit17 : Nat
  credit16 : Nat
  headA : Window 1769472
  headB : Window 1769472
  signed : Digit → Window 1769472
  headA_width : headA.wires.length = 10
  headB_width : headB.wires.length = 8
  headA_count : headA.count = 132606
  headB_count : headB.count = 0
  signed_width : ∀ w, (signed w).wires.length = w.width
  signed_count : ∀ w, (signed w).count = count records17 records16 w
  headA_zero : ∀ start, residue (headA.program start) = 0
  headB_zero : ∀ start, residue (headB.program start) = 0
  signed_zero : ∀ w start, residue ((signed w).program start) = 0
  headA_credit : ∀ start, added (headA.program start) = 132595
  headB_credit : ∀ start, added (headB.program start) = 0
  signed_credit : ∀ w start, added ((signed w).program start) = count credit17 credit16 w

def leftBodies (impl : Implementation) : List (Window 1769472) := leftDigits.map impl.signed
def rightBodies (impl : Implementation) : List (Window 1769472) := rightDigits.map impl.signed

def leftMetadata (r17 r16 : Nat) : List (Nat × Nat) :=
  List.replicate 11 (r17,17) ++ List.replicate 4 (r16,16)
def rightMetadata (r17 r16 : Nat) : List (Nat × Nat) :=
  List.replicate 8 (r17,17) ++ List.replicate 4 (r16,16)

theorem left_metadata (impl : Implementation) :
    (leftBodies impl).map (fun w => (w.count,w.wires.length)) =
      leftMetadata impl.records17 impl.records16 := by
  simp only [leftBodies, List.map_map, Function.comp_def, impl.signed_count, impl.signed_width]
  simp [leftDigits, List.ofFn_succ, Digit.width, count, leftMetadata, List.replicate]

theorem right_metadata (impl : Implementation) :
    (rightBodies impl).map (fun w => (w.count,w.wires.length)) =
      rightMetadata impl.records17 impl.records16 := by
  simp only [rightBodies, List.map_map, Function.comp_def, impl.signed_count, impl.signed_width]
  simp [rightDigits, List.ofFn_succ, Digit.width, count, rightMetadata, List.replicate]

theorem headA_axisCount (impl : Implementation) : axisCount [impl.headA] = 132616 := by
  simp [Single.axisCount, impl.headA_count, impl.headA_width]

theorem headB_axisCount (impl : Implementation) : axisCount [impl.headB] = 8 := by
  simp [Single.axisCount, impl.headB_count, impl.headB_width]

theorem left_count (impl : Implementation) :
    axisCount (leftBodies impl) = 11*impl.records17 + 4*impl.records16 + 251 := by
  rw [← recordCount_eq_axisCount, left_metadata]
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_count (impl : Implementation) :
    axisCount (rightBodies impl) = 8*impl.records17 + 4*impl.records16 + 200 := by
  rw [← recordCount_eq_axisCount, right_metadata]
  simp [rightMetadata, recordCount, List.replicate]
  omega

theorem mixS4_value (impl : Implementation) :
    mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0 =
      132606 + 19*impl.records17 + 8*impl.records16 + 469 := by
  simp only [mixS4, mixS3, mixS2, mixS1, headA_axisCount, headB_axisCount, left_count, right_count]
  omega

/-- Static positions of the left word: the left head bank, then the left bodies. -/
def leftPositions (r17 r16 : Nat) : List Nat :=
  positions [(132606,10)] 0 ++ positions (leftMetadata r17 r16) 132624

/-- Static positions of the right word: the right head bank, then the right bodies. -/
def rightPositions (r17 r16 : Nat) : List Nat :=
  positions [(0,8)] 132616 ++ positions (rightMetadata r17 r16) (132624 + (11*r17 + 4*r16 + 251))

theorem left_positions_length (r17 r16 : Nat) : (leftPositions r17 r16).length = 261 := by
  simp only [leftPositions, List.length_append, positions_length]
  norm_num [leftMetadata, List.replicate]

theorem right_positions_length (r17 r16 : Nat) : (rightPositions r17 r16).length = 208 := by
  simp only [rightPositions, List.length_append, positions_length]
  norm_num [rightMetadata, List.replicate]

def trialPositions (r17 r16 : Nat) : TrialPositions SinAverage261.params261 where
  left := ⟨(leftPositions r17 r16).toArray, by
    simpa only [List.size_toArray, SinAverage261.params261] using left_positions_length r17 r16⟩
  right := ⟨(rightPositions r17 r16).toArray, by
    simpa only [List.size_toArray, SinAverage261.params261] using right_positions_length r17 r16⟩

theorem left_position_bound (r17 r16 i : Nat) (hi : i ∈ (trialPositions r17 r16).left.toList) :
    i < 132875+11*r17+4*r16 := by
  have hi' : i ∈ leftPositions r17 r16 := by simpa [trialPositions] using hi
  simp only [leftPositions, List.mem_append] at hi'
  rcases hi' with h | h
  · have := positions_bounds _ _ i h
    simp [recordCount] at this
    omega
  · have := positions_bounds _ _ i h
    simp [leftMetadata, recordCount, List.replicate] at this
    omega

theorem right_position_bound (r17 r16 i : Nat) (hi : i ∈ (trialPositions r17 r16).right.toList) :
    i < 132606+19*r17+8*r16+469 := by
  have hi' : i ∈ rightPositions r17 r16 := by simpa [trialPositions] using hi
  simp only [rightPositions, List.mem_append] at hi'
  rcases hi' with h | h
  · have := positions_bounds _ _ i h
    simp [recordCount] at this
    omega
  · have := positions_bounds _ _ i h
    simp [rightMetadata, recordCount, List.replicate] at this
    omega

def cursor (impl : Implementation) (reset : List Wire) : Nat :=
  132606+19*impl.records17+8*impl.records16+469+reset.length

def finePositions (impl : Implementation) (reset : List Wire) : List (Fin (cursor impl reset)) :=
  (trialPositions impl.records17 impl.records16).right.toList.attach.map fun i =>
    ⟨i.val,(right_position_bound impl.records17 impl.records16 i.val i.property).trans_le
      (by unfold cursor; omega)⟩

theorem finePositions_length (impl : Implementation) (reset : List Wire) :
    (finePositions impl reset).length = 208 := by
  simp [finePositions, SinAverage261.params261]

def fineBits (impl : Implementation) (reset : List Wire) : Vector (Fin (cursor impl reset)) 208 :=
  Vector.ofFn fun i => (finePositions impl reset)[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout (impl : Implementation) (reset : List Wire) :
    Straight 1769472 (cursor impl reset) (cursor impl reset+34946) :=
  castFinish (by omega) (Readout56.suffix56 1769472 (cursor impl reset) 208 (fineBits impl reset))

def program (impl : Implementation) (reset : List Wire) : Straight 1769472 0 (cursor impl reset) :=
  Single.framed (mixHead impl.headA 0)
    (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0)
    (resetProgram 1769472 (mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0) reset)
    (by rw [mixS4_value]; unfold cursor; omega)

def fullProgram (impl : Implementation) (reset : List Wire) :
    Straight 1769472 0 (cursor impl reset+34946) :=
  (program impl reset).append (readout impl reset)

def positionsFor (r17 r16 : Nat) (ps : Vector Nat 208) : TrialPositions SinAverage261.params261 :=
  { left := (trialPositions r17 r16).left, right := ps }

def layout (impl : Implementation) (reset : List Wire) : DecodeLayout :=
  ⟨.wrappedShift, SinAverage261.params261,
    (Readout56.rightWords56 (fineBits impl reset)).map (positionsFor impl.records17 impl.records16), by
      simp only [List.length_map, Readout56.rightWords56_length]; decide⟩

theorem fineBits_vals (impl : Implementation) (reset : List Wire) :
    (fineBits impl reset).map Fin.val = (trialPositions impl.records17 impl.records16).right := by
  apply Vector.ext
  intro i hi
  simp [fineBits, finePositions]
  rfl

theorem readout_wellFormed (impl : Implementation) (reset : List Wire) : (readout impl reset).WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact Readout56.suffix56_wellFormed _ _ _ _

end
end ShorECDLP.Entrant.Width16Schedule


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution ConditionalCatalyst WeightedPhase28
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] List.ofFn
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]

def leftWidthsBody : List Nat := List.replicate 11 17 ++ List.replicate 4 16
def rightWidthsBody : List Nat := List.replicate 8 17 ++ List.replicate 4 16
def leftCostMeta (c17 c16 : Nat) : List (Nat × Nat) :=
  List.replicate 11 (4*c17,17) ++ List.replicate 4 (4*c16,16)
def rightCostMeta (c17 c16 : Nat) : List (Nat × Nat) :=
  List.replicate 8 (4*c17,17) ++ List.replicate 4 (4*c16,16)

theorem exact_phase_metadata (c17 c16 : Nat) :
    metadataWeight [(4*132595,10)] 0 + metadataWeight [(0,8)] 0 +
      metadataWeight (leftCostMeta c17 c16) 10 + metadataWeight (rightCostMeta c17 c16) 8 =
      4*(132595+19*c17+8*c16)+54991 ∧
    WeightedPhase28.metadataDropped [10] 0 + WeightedPhase28.metadataDropped [8] 0 +
      WeightedPhase28.metadataDropped leftWidthsBody 10 +
      WeightedPhase28.metadataDropped rightWidthsBody 8 = 43966 := by
  constructor
  · simp [leftCostMeta, rightCostMeta, List.replicate, metadataWeight, fourierWeight]
    omega
  · decide +kernel

theorem signed_width_relation (impl : Implementation) (ws : List Digit) :
    List.Forall₂ (fun w k => w.wires.length = k) (ws.map impl.signed) (ws.map Digit.width) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih => exact .cons (impl.signed_width w) ih

theorem headA_width_relation (impl : Implementation) :
    List.Forall₂ (fun w k => w.wires.length = k) ([impl.headA]) ([10]) :=
  .cons impl.headA_width .nil

theorem headB_width_relation (impl : Implementation) :
    List.Forall₂ (fun w k => w.wires.length = k) ([impl.headB]) ([8]) :=
  .cons impl.headB_width .nil

theorem left_width_relation (impl : Implementation) :
    List.Forall₂ (fun w k => w.wires.length = k) (leftBodies impl) leftWidthsBody := by
  simpa only [leftBodies, leftWidthsBody, left_widths] using signed_width_relation impl leftDigits

theorem right_width_relation (impl : Implementation) :
    List.Forall₂ (fun w k => w.wires.length = k) (rightBodies impl) rightWidthsBody := by
  simpa only [rightBodies, rightWidthsBody, right_widths] using signed_width_relation impl rightDigits

theorem signed_cost_relation (impl : Implementation) (ws : List Digit) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start, weight4 (w.program start) ≤ k.1)
      (ws.map impl.signed) (ws.map (fun w => (4*count impl.credit17 impl.credit16 w,w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨impl.signed_width w, fun start => ?_⟩ ih
    rw [weight4_zero _ (impl.signed_zero w start), impl.signed_credit]

theorem headA_cost_relation (impl : Implementation) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start, weight4 (w.program start) ≤ k.1)
      ([impl.headA]) ([(4*132595,10)]) :=
  .cons ⟨impl.headA_width, fun start => by
    rw [weight4_zero _ (impl.headA_zero start), impl.headA_credit]⟩ .nil

theorem headB_cost_relation (impl : Implementation) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start, weight4 (w.program start) ≤ k.1)
      ([impl.headB]) ([(0,8)]) :=
  .cons ⟨impl.headB_width, fun start => by
    simp [weight4_zero _ (impl.headB_zero start), impl.headB_credit]⟩ .nil

theorem left_cost_relation (impl : Implementation) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start, weight4 (w.program start) ≤ k.1)
      (leftBodies impl) (leftCostMeta impl.credit17 impl.credit16) := by
  have he : leftCostMeta impl.credit17 impl.credit16 =
      leftDigits.map (fun w => (4*count impl.credit17 impl.credit16 w,w.width)) := by
    simp [leftCostMeta, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  exact signed_cost_relation impl leftDigits

theorem right_cost_relation (impl : Implementation) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start, weight4 (w.program start) ≤ k.1)
      (rightBodies impl) (rightCostMeta impl.credit17 impl.credit16) := by
  have he : rightCostMeta impl.credit17 impl.credit16 =
      rightDigits.map (fun w => (4*count impl.credit17 impl.credit16 w,w.width)) := by
    simp [rightCostMeta, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  exact signed_cost_relation impl rightDigits

theorem mixPriorL_length (impl : Implementation) (start : Nat) :
    (mixPriorL impl.headA impl.headB start).length = 10 := by
  simp [mixPriorL, nextPrior_length, impl.headA_width]

theorem mixPriorR_length (impl : Implementation) (start : Nat) :
    (mixPriorR impl.headA impl.headB (leftBodies impl) start).length = 8 := by
  simp [mixPriorR, nextPrior_length, impl.headB_width]

theorem axes_weight (impl : Implementation) (start : Nat) :
    weight4 (mixHead impl.headA start) +
      weight4 (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) start) ≤
      4*(132595+19*impl.credit17+8*impl.credit16)+54991 := by
  have hA := weight4_axis ([impl.headA]) _ (headA_cost_relation impl) start List.nil
  have hB := weight4_axis ([impl.headB]) _ (headB_cost_relation impl) (mixS1 impl.headA start) List.nil
  have hL := weight4_axis (leftBodies impl) _ (left_cost_relation impl)
    (mixS2 impl.headA impl.headB start) (mixPriorL impl.headA impl.headB start)
  have hR := weight4_axis (rightBodies impl) _ (right_cost_relation impl)
    (mixS3 impl.headA impl.headB (leftBodies impl) start)
    (mixPriorR impl.headA impl.headB (leftBodies impl) start)
  rw [mixPriorL_length] at hL
  rw [mixPriorR_length] at hR
  simp only [List.length_nil] at hA hB
  have he := (exact_phase_metadata impl.credit17 impl.credit16).1
  simp only [mixHead, mixTail, weight4_append]
  omega

theorem axes_removed (impl : Implementation) (start : Nat) :
    43966 ≤ ApproximatePhase34.removed 27 (mixHead impl.headA start) +
      ApproximatePhase34.removed 27
        (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) start) := by
  have hA := WeightedPhase28.removed_axis ([impl.headA]) ([10]) (headA_width_relation impl) start List.nil
  have hB := WeightedPhase28.removed_axis ([impl.headB]) ([8]) (headB_width_relation impl)
    (mixS1 impl.headA start) List.nil
  have hL := WeightedPhase28.removed_axis (leftBodies impl) leftWidthsBody (left_width_relation impl)
    (mixS2 impl.headA impl.headB start) (mixPriorL impl.headA impl.headB start)
  have hR := WeightedPhase28.removed_axis (rightBodies impl) rightWidthsBody (right_width_relation impl)
    (mixS3 impl.headA impl.headB (leftBodies impl) start)
    (mixPriorR impl.headA impl.headB (leftBodies impl) start)
  rw [mixPriorL_length] at hL
  rw [mixPriorR_length] at hR
  simp only [List.length_nil] at hA hB
  have he := (exact_phase_metadata impl.credit17 impl.credit16).2
  simp only [mixHead, mixTail, WeightedPhase28.removed_append]
  omega

theorem fullProgram_weight (impl : Implementation) (reset : List Wire) :
    weight4 (fullProgram impl reset) ≤ 4*(132595+19*impl.credit17+8*impl.credit16)+54991 := by
  have h := axes_weight impl 0
  simp only [fullProgram, weight4_append, program, weight4_framed, weight4_reset,
    readout, weight4_cast, weight4_suffix56]
  omega

theorem removed27_framed {n s m k e f} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) :
    ApproximatePhase34.removed 27 (Single.framed p q r h) =
      ApproximatePhase34.removed 27 p+ApproximatePhase34.removed 27 q+ApproximatePhase34.removed 27 r := by
  simp [Single.framed, ApproximatePhase34.removed, WeightedPhase28.removed_cast,
    WeightedPhase28.removed_append, ApproximatePhase34.largePhase, Nat.add_assoc]

theorem fullProgram_removed (impl : Implementation) (reset : List Wire) :
    43966 ≤ ApproximatePhase34.removed 27 (fullProgram impl reset) := by
  have h := axes_removed impl 0
  simp only [fullProgram, WeightedPhase28.removed_append, program, removed27_framed]
  omega

theorem fullProgram_trim27_weight (impl : Implementation) (reset : List Wire) :
    weight4 (ApproximatePhase34.trim 27 (fullProgram impl reset)) ≤
      4*(132595+19*impl.credit17+8*impl.credit16)+11025 := by
  have hw := fullProgram_weight impl reset
  have hr := fullProgram_removed impl reset
  have h := weight4_trim (fullProgram impl reset)
  omega

theorem fullProgram_error (impl : Implementation) (reset : List Wire) :
    errorCost (fullProgram impl reset) ≤ 469*unit := by
  have hA := error_axis ([impl.headA]) ([10]) (headA_width_relation impl)
    (by intro w hw start; rcases List.mem_singleton.mp hw with rfl; exact impl.headA_zero start)
    0 List.nil
  have hB := error_axis ([impl.headB]) ([8]) (headB_width_relation impl)
    (by intro w hw start; rcases List.mem_singleton.mp hw with rfl; exact impl.headB_zero start)
    (mixS1 impl.headA 0) List.nil
  have hL := error_axis (leftBodies impl) leftWidthsBody (left_width_relation impl)
    (by
      intro w hw start
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
      exact impl.signed_zero d start)
    (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0)
  have hR := error_axis (rightBodies impl) rightWidthsBody (right_width_relation impl)
    (by
      intro w hw start
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
      exact impl.signed_zero d start)
    (mixS3 impl.headA impl.headB (leftBodies impl) 0) (mixPriorR impl.headA impl.headB (leftBodies impl) 0)
  have hz (n start : Nat) (ws : List Wire) : residue (resetProgram n start ws) = 0 := by
    induction ws generalizing start with
    | nil => simp [resetProgram, residue]
    | cons w ws ih => simpa [resetProgram, residue_cast, residue] using ih (start+1)
  have hreset : errorCost (resetProgram 1769472
      (mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0) reset) = 0 :=
    error_zero _ (hz _ _ _)
  have hro : errorCost (readout impl reset) = 0 := by
    apply error_zero
    simp only [readout, residue_cast, ApproximatePhase34.residue_suffix56]
  simp only [leftWidthsBody, rightWidthsBody, List.sum_append, List.sum_replicate, List.sum_cons,
    List.sum_nil] at hA hB hL hR
  norm_num [smul_eq_mul] at hA hB hL hR
  simp only [fullProgram, error_append, program, Single.framed, error_cast,
    error_append, errorCost, charge, zero_add, hreset, hro, mixHead, mixTail]
  linarith

def sourceEntry (impl : Implementation) (reset : List Wire) : StraightEntry :=
  Single.fixedEntry ShorECDLP.Entrant.Width16Schedule.coefficientAt (fullProgram impl reset)

theorem source_error (impl : Implementation) (reset : List Wire) :
    errorCost (sourceEntry impl reset).program ≤ 469*unit := by
  unfold sourceEntry Single.fixedEntry
  rw [error_reindex]
  exact fullProgram_error impl reset

end
end ShorECDLP.Entrant.Width16Schedule


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

def reindexWindow {n m : Nat} (rows : Fin n → Fin m) (w : Window n) : Window m :=
  ⟨w.wires,w.count,fun start => reindexStraight rows (w.program start)⟩

/-- Lift an already proved physical model, preserving its full bank, cursor,
    ideal map and validity predicate. No point evaluation is used in construction. -/
def reindexModel {n m : Nat} (old : Fin n → PointCoeff) (fresh : Fin m → PointCoeff)
    (rows : Fin n → Fin m) (hcoeff : ∀ a, old a = fresh (rows a)) (Q : Point)
    (model : WindowModel (readConstant old Q)) : WindowModel (readConstant fresh Q) where
  physical := reindexWindow rows model.physical
  point := model.point
  bias := model.bias
  ideal := model.ideal
  valid := model.valid
  nodup := model.nodup
  coherent := by
    intro start history
    change CoherentlyImplementsOn
      ((reindexStraight rows (model.physical.program start)).instantiate (readConstant fresh Q) history)
      model.ideal model.valid
    rw [reindexStraight_instantiate]
    rw [readConstant_reindex rows old fresh Q (fun a => (hcoeff a).symm)]
    exact model.coherent start history

theorem reindexModel_step {n m : Nat} (old : Fin n → PointCoeff) (fresh : Fin m → PointCoeff)
    (rows : Fin n → Fin m) (hcoeff : ∀ a, old a = fresh (rows a)) (Q : Point)
    (model : WindowModel (readConstant old Q)) (prior bits : List Bool) :
    (reindexModel old fresh rows hcoeff Q model).step prior bits = model.step prior bits := rfl

theorem reindexModel_pointRule {n m : Nat} (old : Fin n → PointCoeff) (fresh : Fin m → PointCoeff)
    (rows : Fin n → Fin m) (hcoeff : ∀ a, old a = fresh (rows a)) (Q : Point)
    (model : WindowModel (readConstant old Q)) (root : BasisState)
    (h : PointRule root model) : PointRule root (reindexModel old fresh rows hcoeff Q model) := h

def familyWindows (wide : Window 65536) (normal : Window 32768) : Digit → Window 1769472
  | .left17 j => reindexWindow (row (.left17 j)) wide
  | .right17 j => reindexWindow (row (.right17 j)) wide
  | .left16 j => reindexWindow (row (.left16 j)) normal
  | .right16 j => reindexWindow (row (.right16 j)) normal

theorem family_widths (wide : Window 65536) (normal : Window 32768)
    (hw : wide.wires.length = 17) (hn : normal.wires.length = 16) (w : Digit) :
    (familyWindows wide normal w).wires.length = w.width := by
  cases w <;> first | exact hw | exact hn

theorem family_counts (wide : Window 65536) (normal : Window 32768) (w : Digit) :
    (familyWindows wide normal w).count = count wide.count normal.count w := by cases w <;> rfl

end
end ShorECDLP.Entrant.Width16Schedule


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] fourierOutcomes

def firstWindow : Window 1769472 := RootPass.windowGeneric firstRow

theorem firstWindow_law : WindowLaw ShorECDLP.Entrant.Width16Schedule.coefficientAt firstWindow
    (SelectSchedule18.update initialPoint) SelectSchedule18.Input := by
  apply RootPass.window_law_generic
  intro Q hQ a
  rw [coefficientAt_first]
  exact initialCoefficients_point Q hQ a.val

/-- The five low address bits (right-axis head) and the twelve high ones (left-axis head). -/
def headRWires : List Wire := SelectSchedule18.bits.take 8
def headLWires : List Wire := SelectSchedule18.bits.drop 8

/-- Left head bank: measured wires are the twelve high address bits; its program first puts the
    five low address bits in superposition, then runs the one joint 17-wire first load. -/
def headAG (L R : List Wire) : Window 1769472 :=
  ⟨L.reverse, 132606, fun start => prepareOuterBank R (firstWindow.program start)⟩

/-- Right head bank: measured wires are the five low address bits; its program undoes the
    axis preparation, so the bank only measures the Fourier outcome of the loaded register. -/
def headBG (R : List Wire) : Window 1769472 :=
  ⟨R.reverse, 0,
    fun start => prepareOuterBank R.reverse (Straight.done : Straight 1769472 start start)⟩

def headA : Window 1769472 := headAG headLWires headRWires
def headB : Window 1769472 := headBG headRWires

theorem head_bits : headRWires ++ headLWires = SelectSchedule18.bits := by
  unfold headRWires headLWires
  exact List.take_append_drop 8 SelectSchedule18.bits

theorem headR_nodup : headRWires.Nodup :=
  Single.select18_nodup.sublist (by rw [← head_bits]; exact List.sublist_append_left _ _)

theorem headL_nodup : headLWires.Nodup :=
  Single.select18_nodup.sublist (by rw [← head_bits]; exact List.sublist_append_right _ _)

theorem headRL_disjoint : ∀ w ∈ headLWires, w ∉ headRWires := by
  intro w hw hr
  have hnd : (headRWires ++ headLWires).Nodup := by rw [head_bits]; exact Single.select18_nodup
  exact (List.nodup_append.mp hnd).2.2 w hr w hw rfl

theorem added_prepare {n s e} (ws : List Wire) (p : Straight n s e) :
    added (prepareOuterBank ws p) = added p := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [prepareOuterBank, added] using ih

theorem headA_width' : headA.wires.length = 10 := by
  change headLWires.reverse.length = 10
  decide +kernel

theorem headB_width' : headB.wires.length = 8 := by
  change headRWires.reverse.length = 8
  decide +kernel

theorem headA_zero' (start : Nat) : residue (headA.program start) = 0 := by
  change residue (prepareOuterBank headRWires (firstWindow.program start)) = 0
  rw [ApproximatePhase34.residue_prepare]
  unfold firstWindow RootPass.windowGeneric
  rw [residue_reindex, RootPass.first18_rootProgram_residue]

theorem headB_zero' (start : Nat) : residue (headB.program start) = 0 := by
  change residue (prepareOuterBank headRWires.reverse (Straight.done : Straight 1769472 start start)) = 0
  rw [ApproximatePhase34.residue_prepare]
  rfl

theorem headA_credit' (start : Nat) : added (headA.program start) = 132595 := by
  change added (prepareOuterBank headRWires (firstWindow.program start)) = 132595
  rw [added_prepare]
  unfold firstWindow RootPass.windowGeneric
  rw [added_reindex, RootPass.first18_rootProgram_added]

theorem headB_credit' (start : Nat) : added (headB.program start) = 0 := by
  change added (prepareOuterBank headRWires.reverse (Straight.done : Straight 1769472 start start)) = 0
  rw [added_prepare]
  rfl

/-- Ordinary constructor for the complete schedule contract. The actual physical
    signed windows and all their metadata/credit proofs remain arguments. -/
def withHeads (records17 records16 credit17 credit16 : Nat)
    (signed : Digit → Window 1769472)
    (widths : ∀ w, (signed w).wires.length = w.width)
    (counts : ∀ w, (signed w).count = count records17 records16 w)
    (zeros : ∀ w start, residue ((signed w).program start) = 0)
    (credits : ∀ w start, added ((signed w).program start) = count credit17 credit16 w) :
    Implementation where
  records17 := records17
  records16 := records16
  credit17 := credit17
  credit16 := credit16
  headA := headA
  headB := headB
  signed := signed
  headA_width := headA_width'
  headB_width := headB_width'
  headA_count := rfl
  headB_count := rfl
  signed_width := widths
  signed_count := counts
  headA_zero := headA_zero'
  headB_zero := headB_zero'
  headA_credit := headA_credit'
  headB_credit := headB_credit'
  signed_zero := zeros
  signed_credit := credits

end
end ShorECDLP.Entrant.Width16Schedule


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution ConditionalCatalyst WeightedPhase28 ApproximatePhase34
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
attribute [local irreducible] sourceEntry program fullProgram readout Single.fixedEntry

theorem exact_band_metadata :
    (metadataDropped26 [10] 0 - WeightedPhase28.metadataDropped [10] 0) +
    (metadataDropped26 [8] 0 - WeightedPhase28.metadataDropped [8] 0) +
    (metadataDropped26 leftWidthsBody 10 - WeightedPhase28.metadataDropped leftWidthsBody 10) +
    (metadataDropped26 rightWidthsBody 8 - WeightedPhase28.metadataDropped rightWidthsBody 8) = 417 := by
  decide +kernel

theorem axes_band_count (impl : Implementation) (start : Nat) :
    417 ≤ (removed 26 (mixHead impl.headA start) +
      removed 26 (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) start)) -
      (removed 27 (mixHead impl.headA start) +
      removed 27 (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) start)) := by
  have hA := removed_axis_diff ([impl.headA]) ([10]) (headA_width_relation impl) start List.nil
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
  have m1 := removed27_le_removed26 (Single.axis ([impl.headA]) start List.nil)
  have m2 := removed27_le_removed26 (Single.axis ([impl.headB]) (mixS1 impl.headA start) List.nil)
  have m3 := removed27_le_removed26 (Single.axis (leftBodies impl)
    (mixS2 impl.headA impl.headB start) (mixPriorL impl.headA impl.headB start))
  have m4 := removed27_le_removed26 (Single.axis (rightBodies impl)
    (mixS3 impl.headA impl.headB (leftBodies impl) start)
    (mixPriorR impl.headA impl.headB (leftBodies impl) start))
  simp only [mixHead, mixTail, removed26_append, WeightedPhase28.removed_append]
  omega

theorem fullProgram_band_count (impl : Implementation) (reset : List Wire) :
    417 ≤ removed 26 (fullProgram impl reset) - removed 27 (fullProgram impl reset) := by
  have h := axes_band_count impl 0
  have hz := removed27_le_removed26
    (resetProgram 1769472 (mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0) reset)
  have hro := removed27_le_removed26 (readout impl reset)
  simp only [fullProgram, removed26_append, WeightedPhase28.removed_append,
    program, weighted26_removed_framed, removed27_framed]
  omega

theorem fullProgram_trim259_weight (impl : Implementation) (reset : List Wire) :
    weight4 (trimN 259 (fullProgram impl reset)) ≤
      4*(132595+19*impl.credit17+8*impl.credit16)+10766 := by
  have hw := fullProgram_weight impl reset
  have hr := fullProgram_removed impl reset
  have hc := fullProgram_band_count impl reset
  have h := weight4_trimN 259 (fullProgram impl reset)
  have hs : trimSpent 259 (fullProgram impl reset) = 259 := by
    rw [trimSpent_eq]
    omega
  omega

theorem removed27_fixedEntry {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) :
    removed 27 (Single.fixedEntry f p).program=removed 27 p := by
  unfold Single.fixedEntry
  exact WeightedPhase28.removed_reindex p _

theorem source_trim259_weight (impl : Implementation) (reset : List Wire) :
    weight4 (trimN 259 (sourceEntry impl reset).program) ≤
      4*(132595+19*impl.credit17+8*impl.credit16)+10766 := by
  have hw := fullProgram_weight impl reset
  have hr := fullProgram_removed impl reset
  have hc := fullProgram_band_count impl reset
  have hew : weight4 (sourceEntry impl reset).program = weight4 (fullProgram impl reset) := by
    unfold sourceEntry
    exact weight4_fixedEntry _ _
  have her (k : Nat) (hk : k=26 ∨ k=27) :
      removed k (sourceEntry impl reset).program = removed k (fullProgram impl reset) := by
    unfold sourceEntry
    rcases hk with rfl | rfl
    · exact weighted26_removed_fixedEntry _ _
    · exact removed27_fixedEntry _ _
  have h := weight4_trimN 259 (sourceEntry impl reset).program
  have hs : trimSpent 259 (sourceEntry impl reset).program = 259 := by
    rw [trimSpent_eq, her 26 (Or.inl rfl), her 27 (Or.inr rfl)]
    omega
  rw [hew,hs,her 27 (Or.inr rfl)] at h
  omega

theorem four_coefficients (q y : Wire) (e : StraightEntry) :
    (ConditionalCatalyst.fourEntry q y e).coefficients = e.coefficients := rfl

theorem trim_coefficients (e : StraightEntry) : (trimNEntry e).coefficients=e.coefficients := rfl

theorem fixed_coefficients {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) :
    (Single.fixedEntry f p).coefficients=List.ofFn f := by
  unfold Single.fixedEntry
  rfl

theorem source_coefficients (impl : Implementation) (reset : List Wire) :
    (sourceEntry impl reset).coefficients=List.ofFn ShorECDLP.Entrant.Width16Schedule.coefficientAt := by
  unfold sourceEntry
  exact fixed_coefficients _ _

theorem compiled_source_coefficients (impl : Implementation) (reset : List Wire) :
    (ConditionalCatalyst.fourEntry 1938 1939 (trimNEntry (sourceEntry impl reset))).coefficients=
      List.ofFn ShorECDLP.Entrant.Width16Schedule.coefficientAt :=
  (four_coefficients 1938 1939 (trimNEntry (sourceEntry impl reset))).trans
    ((trim_coefficients (sourceEntry impl reset)).trans (source_coefficients impl reset))

/-- The ordinary entry keeps the exact fresh map after phase and compiler
    transformations. This is a constructor, not a discharged certificate. -/
def finalEntry (impl : Implementation) (reset : List Wire) : StraightEntry :=
  specializeEntry (ConditionalCatalyst.fourEntry 1938 1939 (trimNEntry (sourceEntry impl reset)))
    (compiled_source_coefficients impl reset)

/-- CONDITIONAL: rawCertificate, support, strong readout success and physical
    resource premises remain explicit. No complete signed-body proof is assumed
    by a new axiom or hidden in a classical point callback. -/
theorem conditional_certificate (impl : Implementation) (reset ws : List Wire)
    (baseBounds : Bounds) (qBound : Nat)
    (rawCertificate : Certificate rawLimits (layout impl reset) (sourceEntry impl reset) baseBounds)
    (support : Within ws (sourceEntry impl reset).program)
    (strongSuccess : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q=d•G →
      (990038025/1000000000 : ℝ) ≤ Instrument.bornMass (((sourceEntry impl reset).instantiate Q).run.filter
        (fun b => (verifiedCandidate (layout impl reset) Q b.history).isSome)) (ket zeroBasisState))
    (hq : (1938 : Wire) ∉ ws) (hy : (1939 : Wire) ∉ 1938::ws)
    (slotBudget : 4*((sourceEntry impl reset).program.gateSlots+
      18*added (sourceEntry impl reset).program)+2 ≤ officialLimits.gateSlots)
    (recordBudget : (sourceEntry impl reset).finalCursor+added (sourceEntry impl reset).program ≤ officialLimits.measurements)
    (qubitBudget : ws.length+2 ≤ qBound)
    (measurementBound : (sourceEntry impl reset).finalCursor+added (sourceEntry impl reset).program ≤ 544000000) :
    Certificate officialLimits
      (lowerLayout 1938 (trimNEntry (sourceEntry impl reset)) (layout impl reset))
      (finalEntry impl reset) ⟨qBound,4*(132595+19*impl.credit17+8*impl.credit16)+10767,544000000⟩ := by
  have trimmed := trimN_certificate rawLimits (layout impl reset) (sourceEntry impl reset) baseBounds ws
    rawCertificate support (source_error impl reset) strongSuccess
  have hslots := trimN_slots 259 (sourceEntry impl reset).program
  have hw := source_trim259_weight impl reset
  unfold finalEntry
  apply specializeEntry_certificate _ (compiled_source_coefficients impl reset)
  apply ConditionalCatalyst.four_certificate rawLimits (layout impl reset)
    (trimNEntry (sourceEntry impl reset)) _ _ 1938 1939 ws
    trimmed (trimN_within 259 (sourceEntry impl reset).program ws support) hq hy
  · change 4*((trimN 259 (sourceEntry impl reset).program).gateSlots+
      18*added (trimN 259 (sourceEntry impl reset).program))+2 ≤ officialLimits.gateSlots
    rw [trimN_added]
    omega
  · change (sourceEntry impl reset).finalCursor+added (trimN 259 (sourceEntry impl reset).program) ≤ officialLimits.measurements
    rw [trimN_added]
    exact recordBudget
  · exact qubitBudget
  · change weight4 (trimN 259 (sourceEntry impl reset).program)+1 ≤
      4*(132595+19*impl.credit17+8*impl.credit16)+10767
    omega
  · change (sourceEntry impl reset).finalCursor+added (trimN 259 (sourceEntry impl reset).program) ≤ 544000000
    rw [trimN_added]
    exact measurementBound

/-- Exact strict-score test after all body, support, semantic and certificate
    premises have been discharged. No Q or cost number is assumed by the proof. -/
theorem strict_score (Q c17 c16 : Nat)
    (hQ : Q ≤ 1652) (h17 : c17 ≤ 2345143) (h16 : c16 ≤ 2253190) :
    Q * (4*(132595+19*c17+8*c16)+10767) < 420149980414 := by
  have ht : 4*(132595+19*c17+8*c16)+10767 ≤ 250907747 := by omega
  exact (Nat.mul_le_mul hQ ht).trans_lt (by norm_num)

end
end ShorECDLP.Entrant.Width16Schedule


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] fourierOutcomes
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]

/-! Everything below is proved for abstract wire lists `L` (measured first, the left head) and `R`
(the right head) with `R ++ L` equal to the first-load address bits; the concrete heads are an
instance at the very end. -/
section Generic
variable (L R : List Wire)

theorem split_facts (hLR : R ++ L = SelectSchedule18.bits) :
    L.Nodup ∧ R.Nodup ∧ (∀ w ∈ L, w ∉ R) ∧ (∀ w ∈ L, w ∈ SelectSchedule18.bits) ∧
      (∀ w ∈ R, w ∈ SelectSchedule18.bits) := by
  have hnd : (R ++ L).Nodup := by rw [hLR]; exact Single.select18_nodup
  obtain ⟨hR, hL, hd⟩ := List.nodup_append.mp hnd
  refine ⟨hL, hR, fun w hw hr => hd w hr w hw rfl, ?_, ?_⟩
  · intro w hw
    rw [← hLR]
    exact List.mem_append_right _ hw
  · intro w hw
    rw [← hLR]
    exact List.mem_append_left _ hw

def headAModelG (hLR : R ++ L = SelectSchedule18.bits) (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowModel (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q) where
  physical := headAG L R
  point := fun v => (v * 2^251 + leftOffset) • G
  bias := -(leftOffset • G)
  ideal := (Finsupp.lmapDomain ℂ ℂ (SelectSchedule18.update initialPoint Q)).comp
    (Quantum.run (R.map Gate.H))
  valid := SelectSchedule18.Input
  nodup := by
    change L.reverse.Nodup
    exact List.nodup_reverse.mpr (split_facts L R hLR).1
  coherent := by
    intro start history
    change CoherentlyImplementsOn
      ((prepareOuterBank R (firstWindow.program start)).instantiate
        (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q) history) _ _
    exact coherent_prepare R (firstWindow.program start) _ history _ _
      (firstWindow_law Q hQ hn start history)
      (fun s hs => SelectSchedule18.input_prepare R (split_facts L R hLR).2.2.2.2 _
        (supportedOn_ket _ _ hs))

def headBModelG (hLR : R ++ L = SelectSchedule18.bits) (Q : Point) :
    WindowModel (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q) where
  physical := headBG R
  point := fun v => (v * 2^200 + rightOffset) • Q
  bias := -(rightOffset • Q)
  ideal := Quantum.run (R.reverse.map Gate.H)
  valid := fun _ => True
  nodup := by
    change R.reverse.Nodup
    exact List.nodup_reverse.mpr (split_facts L R hLR).2.1
  coherent := by
    intro start history
    exact coherent_prepare_done R.reverse _ history

theorem headAG_step (hLR : R ++ L = SelectSchedule18.bits) (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (prior bits : List Bool) (ψ : State) :
    (headAModelG L R hLR Q hQ hn).step prior bits ψ =
      fourierBranch .inverse L.reverse prior bits
        (Finsupp.lmapDomain ℂ ℂ (SelectSchedule18.update initialPoint Q)
          (Quantum.run (R.map Gate.H) (Quantum.run (L.map Gate.H) ψ))) := by
  have h : (headAModelG L R hLR Q hQ hn).step prior bits ψ =
      fourierBranch .inverse L.reverse prior bits
        (Finsupp.lmapDomain ℂ ℂ (SelectSchedule18.update initialPoint Q)
          (Quantum.run (R.map Gate.H) (Quantum.run (L.reverse.reverse.map Gate.H) ψ))) := rfl
  rw [h, List.reverse_reverse]

theorem headBG_step (hLR : R ++ L = SelectSchedule18.bits) (Q : Point) (prior bits : List Bool)
    (ψ : State) :
    (headBModelG L R hLR Q).step prior bits ψ =
      fourierBranch .inverse R.reverse prior bits
        (Quantum.run (R.reverse.map Gate.H) (Quantum.run (R.map Gate.H) ψ)) := by
  have h : (headBModelG L R hLR Q).step prior bits ψ =
      fourierBranch .inverse R.reverse prior bits
        (Quantum.run (R.reverse.map Gate.H) (Quantum.run (R.reverse.reverse.map Gate.H) ψ)) := rfl
  rw [h, List.reverse_reverse]

theorem tableAddressValue_append (xs ys : List Wire) (s : BasisState) :
    tableAddressValue (xs ++ ys) s = tableAddressValue xs s + 2^xs.length * tableAddressValue ys s := by
  induction xs with
  | nil => simp [tableAddressValue]
  | cons x xs ih =>
    simp only [List.cons_append, tableAddressValue, ih, List.length_cons, pow_succ]
    ring

theorem assigned_address_value (ws : List Wire) (hnd : ws.Nodup) (input : List Bool)
    (hi : input.length = ws.length) (s : BasisState) :
    tableAddressValue ws (phaseWordState ws input s) = boolWordToNat input := by
  have he (ws : List Wire) (t : BasisState) :
      tableAddressValue ws t = boolWordToNat (wireValues ws t) := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      change (t w).toNat + 2 * tableAddressValue ws t =
        (t w).toNat + 2 * boolWordToNat (wireValues ws t)
      rw [ih]
  rw [he, phaseWordState_word _ hnd input hi s]

theorem fourierClear_comm (xs ys : List Wire) (s : BasisState) :
    fourierClear xs (fourierClear ys s) = fourierClear ys (fourierClear xs s) := by
  funext w
  simp only [fourierClear_apply]
  by_cases h1 : w ∈ xs <;> by_cases h2 : w ∈ ys <;> simp [h1, h2]

theorem fourierClear_append (xs ys : List Wire) (s : BasisState) :
    fourierClear (xs ++ ys) s = fourierClear ys (fourierClear xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, fourierClear, ih]

/-- Loading both head banks at once leaves exactly the point written by the joint table. -/
theorem joint_load_clear (hLR : R ++ L = SelectSchedule18.bits)
    (init : Point → Nat → Point) (Q : Point) (root : BasisState)
    (hz : Clean SelectSchedule18.bits root) (inL inR : List Bool)
    (hL : inL.length = L.length) (hR : inR.length = R.length) :
    fourierClear R.reverse (fourierClear L.reverse
      (SelectSchedule18.update init Q (phaseWordState R inR (phaseWordState L inL root)))) =
      pointWrite (init Q (boolWordToNat inR + 2^R.length * boolWordToNat inL)) root := by
  obtain ⟨hnL, hnR, hdisj, hsubL, hsubR⟩ := split_facts L R hLR
  have hcl : Clean (L ++ R) root := by
    intro w hw
    apply hz
    rcases List.mem_append.mp hw with h | h
    · exact hsubL w h
    · exact hsubR w h
  have hsplit : phaseWordState R inR (phaseWordState L inL root) =
      phaseWordState (L ++ R) (inL ++ inR) root :=
    (phaseWordState_append L R inL inR hL root).symm
  have hval : tableAddressValue SelectSchedule18.bits
      (phaseWordState R inR (phaseWordState L inL root)) =
      boolWordToNat inR + 2^R.length * boolWordToNat inL := by
    have h1 : tableAddressValue R (phaseWordState R inR (phaseWordState L inL root)) =
        boolWordToNat inR := assigned_address_value R hnR inR hR _
    have h2 : tableAddressValue L (phaseWordState R inR (phaseWordState L inL root)) =
        boolWordToNat inL := by
      rw [tableAddressValue_congr L _ (phaseWordState L inL root)
        (fun w hw => phaseWordState_frame R inR _ w (fun h => hdisj w hw h))]
      exact assigned_address_value L hnL inL hL root
    rw [← hLR, tableAddressValue_append, h1, h2]
  unfold SelectSchedule18.update
  rw [hval, fourierClear_comm, ← fourierClear_append, ← List.reverse_append, hsplit]
  have hnp : ∀ v ∈ L ++ R, v ∉ pointLogicalWires := by
    intro v hv
    apply Single.select18_not_point
    rcases List.mem_append.mp hv with h | h
    · exact hsubL v h
    · exact hsubR v h
  exact clear_assigned_point (L ++ R) (inL ++ inR) root hcl hnp _

/-- Both head banks together: the closed form of the joint first section, for every pair of
    feedback histories and outcomes. -/
theorem joint_first_step_generic (hLR : R ++ L = SelectSchedule18.bits)
    (hLlen : L.length = 10) (hRlen : R.length = 8)
    (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (prior1 bits1 prior2 bits2 : List Bool) (root : BasisState)
    (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (headBModelG L R hLR Q).step prior2 bits2 ((headAModelG L R hLR Q hQ hn).step prior1 bits1 (ket root)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (10 + 8)) •
        ((fourierOutcomes 10).map (fun inL =>
          ((fourierOutcomes 8).map (fun inR =>
            (fourierBitAmplitude .inverse inL.reverse prior1 bits1 *
              fourierBitAmplitude .inverse inR.reverse prior2 bits2) •
              ket (pointWrite (initialPoint Q (boolWordToNat inR + 256 * boolWordToNat inL)) root))).sum)).sum := by
  obtain ⟨hnL, hnR, hdisj, hsubL, hsubR⟩ := split_facts L R hLR
  have hzb : Clean SelectSchedule18.bits root := Single.select18_clean root hs hz
  have hcl : Clean (L ++ R) root := by
    intro w hw
    apply hzb
    rcases List.mem_append.mp hw with h | h
    · exact hsubL w h
    · exact hsubR w h
  have hfL : ∀ inL ∈ fourierOutcomes L.length, ∀ inR ∈ fourierOutcomes R.length,
      L.map (SelectSchedule18.update initialPoint Q (phaseWordState R inR (phaseWordState L inL root))) = inL := by
    intro inL hinL inR hinR
    have hL' := (fourierOutcomes_mem _ _).mp hinL
    have he : L.map (SelectSchedule18.update initialPoint Q
        (phaseWordState R inR (phaseWordState L inL root))) =
        L.map (phaseWordState R inR (phaseWordState L inL root)) := by
      apply List.map_congr_left
      intro v hv
      exact pointWrite_frame _ _ v (Single.select18_not_point v (hsubL v hv))
    have hf : L.map (phaseWordState R inR (phaseWordState L inL root)) =
        L.map (phaseWordState L inL root) := by
      apply List.map_congr_left
      intro v hv
      exact phaseWordState_frame R inR _ v (hdisj v hv)
    rw [he, hf]
    exact phaseWordState_word L hnL inL hL' root
  have hfR : ∀ inL ∈ fourierOutcomes L.length, ∀ inR ∈ fourierOutcomes R.length,
      R.map (SelectSchedule18.update initialPoint Q (phaseWordState R inR (phaseWordState L inL root))) = inR := by
    intro inL hinL inR hinR
    have hR' := (fourierOutcomes_mem _ _).mp hinR
    have he : R.map (SelectSchedule18.update initialPoint Q
        (phaseWordState R inR (phaseWordState L inL root))) =
        R.map (phaseWordState R inR (phaseWordState L inL root)) := by
      apply List.map_congr_left
      intro v hv
      exact pointWrite_frame _ _ v (Single.select18_not_point v (hsubR v hv))
    rw [he]
    exact phaseWordState_word R hnR inR hR' _
  have key := ShorECDLP.Entrant.Mixed.joint_steps .inverse L R hnL hnR hdisj
    (SelectSchedule18.update initialPoint Q) prior1 prior2 bits1 bits2 root hcl hfL hfR
  rw [headBG_step, headAG_step, ← Quantum.run_append, key, hLlen, hRlen]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (10 + 8)) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro inL hinL
  apply congrArg List.sum
  apply List.map_congr_left
  intro inR hinR
  have hL' := (fourierOutcomes_mem _ _).mp hinL
  have hR' := (fourierOutcomes_mem _ _).mp hinR
  rw [joint_load_clear L R hLR initialPoint Q root hzb inL inR (by rw [hL', hLlen])
    (by rw [hR', hRlen]), hRlen]
  rfl

end Generic

end
end ShorECDLP.Entrant.Width16Schedule


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] fourierOutcomes
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]

theorem headL_length : headLWires.length = 10 := by
  unfold headLWires
  decide +kernel

theorem headR_length : headRWires.length = 8 := by
  unfold headRWires
  decide +kernel

theorem headL_sub : ∀ w ∈ headLWires, w ∈ SelectSchedule18.bits :=
  (split_facts headLWires headRWires head_bits).2.2.2.1

theorem headR_sub' : ∀ w ∈ headRWires, w ∈ SelectSchedule18.bits :=
  (split_facts headLWires headRWires head_bits).2.2.2.2

def headAModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowModel (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q) :=
  headAModelG headLWires headRWires head_bits Q hQ hn

def headBModel (Q : Point) : WindowModel (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q) :=
  headBModelG headLWires headRWires head_bits Q

theorem headAModel_physical (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (headAModel Q hQ hn).physical = headA := rfl

theorem headBModel_physical (Q : Point) : (headBModel Q).physical = headB := rfl

theorem headAModel_width (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (headAModel Q hQ hn).physical.wires.length = 10 := headA_width'

theorem headBModel_width (Q : Point) : (headBModel Q).physical.wires.length = 8 := headB_width'

theorem joint_first_step (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (prior1 bits1 prior2 bits2 : List Bool) (root : BasisState)
    (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (headBModel Q).step prior2 bits2 ((headAModel Q hQ hn).step prior1 bits1 (ket root)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (10 + 8)) •
        ((fourierOutcomes 10).map (fun inL =>
          ((fourierOutcomes 8).map (fun inR =>
            (fourierBitAmplitude .inverse inL.reverse prior1 bits1 *
              fourierBitAmplitude .inverse inR.reverse prior2 bits2) •
              ket (pointWrite (initialPoint Q (boolWordToNat inR + 256 * boolWordToNat inL)) root))).sum)).sum :=
  joint_first_step_generic headLWires headRWires head_bits headL_length headR_length Q hQ hn
    prior1 bits1 prior2 bits2 root hs hz

/-- The joint table splits into the two head points. -/
theorem initialPoint_split (Q : Point) (l r : Nat) (hr : r < 256) :
    initialPoint Q (r + 256 * l) =
      (l * 2^251 + leftOffset) • G + (r * 2^200 + rightOffset) • Q := by
  unfold initialPoint
  have h1 : (r + 256 * l) / 256 = l := by omega
  have h2 : (r + 256 * l) % 256 = r := by omega
  rw [h1, h2]

/-- Hypothesis `hfirst` of the mixed kernel for the actual head models. -/
theorem hfirst_concrete (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (root : BasisState)
    (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    ∀ bA ∈ fourierOutcomes (modelDigit (headAModel Q hQ hn)).width,
      ∀ bB ∈ fourierOutcomes (modelDigit (headBModel Q)).width,
        (headBModel Q).step List.nil bB ((headAModel Q hQ hn).step List.nil bA (ket root)) =
          jointClosedForm (modelDigit (headAModel Q hQ hn)) (modelDigit (headBModel Q)) bA bB root := by
  have hwA : (modelDigit (headAModel Q hQ hn)).width = 10 := headAModel_width Q hQ hn
  have hwB : (modelDigit (headBModel Q)).width = 8 := headBModel_width Q
  intro bA _ bB _
  rw [joint_first_step Q hQ hn List.nil bA List.nil bB root hs hz]
  unfold jointClosedForm
  rw [hwA, hwB]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (10 + 8)) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro inL hinL
  apply congrArg List.sum
  apply List.map_congr_left
  intro inR hinR
  have hr : boolWordToNat inR < 256 := by
    have h := boolWordToNat_lt_pow_two inR
    rw [(fourierOutcomes_mem _ _).mp hinR] at h
    simpa using h
  rw [initialPoint_split Q _ _ hr]
  rfl

/-- A model for the actual static windows; no Q-dependent program constructor. -/
structure ModelFrame (impl : Implementation) (Q : Point) where
  headA : WindowModel (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q)
  headB : WindowModel (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q)
  signed : Digit → WindowModel (readConstant ShorECDLP.Entrant.Width16Schedule.coefficientAt Q)
  headA_physical : headA.physical = impl.headA
  headB_physical : headB.physical = impl.headB
  signed_physical : ∀ w, (signed w).physical = impl.signed w
  headA_point : ∀ v, headA.point v = (v * 2^251 + leftOffset) • G
  headA_bias : headA.bias = -(leftOffset • G)
  headB_point : ∀ v, headB.point v = (v * 2^200 + rightOffset) • Q
  headB_bias : headB.bias = -(rightOffset • Q)
  signed_point : ∀ w v, (signed w).point v = increment (w.base Q) w.width w.exponent v
  signed_bias : ∀ w, (signed w).bias = offsetScalar w.width w.exponent • w.base Q

theorem model_precisions (impl : Implementation) (Q : Point) (m : ModelFrame impl Q) :
    precision (leftDigits.map m.signed) = 251 ∧ precision (rightDigits.map m.signed) = 200 := by
  have hw (w : Digit) : (m.signed w).physical.wires.length = w.width := by
    rw [m.signed_physical, impl.signed_width]
  constructor
  · simp only [precision, List.map_map, Function.comp_def, hw, left_widths]
    norm_num [List.replicate]
  · simp only [precision, List.map_map, Function.comp_def, hw, right_widths]
    norm_num [List.replicate]

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

theorem bias_cancels (impl : Implementation) (Q : Point) (m : ModelFrame impl Q) :
    (modelDigit m.headA).bias + ((leftDigits.map m.signed).map WindowModel.bias).sum +
      ((modelDigit m.headB).bias + ((rightDigits.map m.signed).map WindowModel.bias).sum) = 0 := by
  have h1 : ((leftDigits.map m.signed).map WindowModel.bias).sum = leftOffset • G :=
    signed_bias_sum Q G m.signed m.signed_bias leftDigits (left_base Q)
  have h2 : ((rightDigits.map m.signed).map WindowModel.bias).sum = rightOffset • Q :=
    signed_bias_sum Q Q m.signed m.signed_bias rightDigits (right_base Q)
  have h3 : (modelDigit m.headA).bias = m.headA.bias := rfl
  have h4 : (modelDigit m.headB).bias = m.headB.bias := rfl
  rw [h1, h2, h3, h4, m.headA_bias, m.headB_bias]
  abel

theorem conditional_event_mass (impl : Implementation) (Q : Point) (hQ : order • Q = 0)
    (m : ModelFrame impl Q) (root : BasisState) (ψ : State)
    (hfirst : ∀ bA ∈ fourierOutcomes (modelDigit m.headA).width,
      ∀ bB ∈ fourierOutcomes (modelDigit m.headB).width,
        m.headB.step List.nil bB (m.headA.step List.nil bA ψ) =
          jointClosedForm (modelDigit m.headA) (modelDigit m.headB) bA bB root)
    (pointRules : ∀ w ∈ leftDigits++rightDigits, PointRule root (m.signed w))
    (ready : Ready (m.headA :: m.headB :: ((leftDigits.map m.signed) ++ (rightDigits.map m.signed))) ψ)
    (start : Nat) (history : Fin start → Bool) (J : Instrument)
    (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedMixed m.headA m.headB (leftDigits.map m.signed) (rightDigits.map m.signed)
      start history (fun lhs rhs =>
        if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass ψ =
      idealEventMass Q root 261 208 accept := by
  have hp := model_precisions impl Q m
  have hwid (w : Digit) : (m.signed w).physical.wires.length = w.width := by
    rw [m.signed_physical, impl.signed_width]
  have hwA : m.headA.physical.wires.length = 10 := by rw [m.headA_physical, impl.headA_width]
  have hwB : m.headB.physical.wires.length = 8 := by rw [m.headB_physical, impl.headB_width]
  have hLB : ModelWeights G (leftDigits.map m.signed) :=
    modelWeights Q G generator_nsmul_eq_zero m.signed hwid m.signed_point m.signed_bias leftDigits
      (left_signed_weights Q)
  have hRB : ModelWeights Q (rightDigits.map m.signed) :=
    modelWeights Q Q hQ m.signed hwid m.signed_point m.signed_bias rightDigits (right_signed_weights Q)
  have hmass := physicalMixed_event_mass Q root ψ m.headA m.headB (leftDigits.map m.signed)
    (rightDigits.map m.signed) (modelDigit m.headA) (modelDigit m.headB) rfl rfl hfirst
    (by
      intro w hw
      rw [← List.map_append] at hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact pointRules v hv)
    (by
      intro v
      have h : (modelDigit m.headA).point v + (modelDigit m.headA).bias =
          m.headA.point v + m.headA.bias := rfl
      rw [h, m.headA_point, m.headA_bias, hp.1]
      simp only [add_nsmul, add_assoc, add_neg_cancel, add_zero])
    (by
      intro v
      have h : (modelDigit m.headB).point v + (modelDigit m.headB).bias =
          m.headB.point v + m.headB.bias := rfl
      rw [h, m.headB_point, m.headB_bias, hp.2]
      simp only [add_nsmul, add_assoc, add_neg_cancel, add_zero])
    hLB hRB (bias_cancels impl Q m) ready start history J hJ accept
  have e1 : (modelDigit m.headA).width + precision (leftDigits.map m.signed) = 261 := by
    have h : (modelDigit m.headA).width = m.headA.physical.wires.length := rfl
    rw [h, hwA, hp.1]
  have e2 : (modelDigit m.headB).width + precision (rightDigits.map m.signed) = 208 := by
    have h : (modelDigit m.headB).width = m.headB.physical.wires.length := rfl
    rw [h, hwB, hp.2]
  rw [hmass, e1, e2]

end
end ShorECDLP.Entrant.Width16Schedule

namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] fourierOutcomes

theorem clear_relabel (e : Wire ≃ Wire) (ws : List Wire) (s : BasisState) :
    fourierClear (ws.map e) (relabelBasis e s) = relabelBasis e (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, fourierClear, ← relabelBasis_upd, ih]

theorem coefficient_relabel (e : Wire ≃ Wire) (dir : PhaseDir) (ws : List Wire)
    (prior bits : List Bool) (s : BasisState) :
    fourierBranchCoeff dir (ws.map e) prior bits (relabelBasis e s) =
      fourierBranchCoeff dir ws prior bits s := by
  induction ws generalizing prior bits s with
  | nil => cases bits <;> rfl
  | cons w ws ih =>
    cases bits with
    | nil => rfl
    | cons b bs =>
      simp only [List.map_cons, fourierBranchCoeff, relabelBasis_at, ← relabelBasis_upd, ih]

theorem fourier_relabel (e : Wire ≃ Wire) (dir : PhaseDir) (ws : List Wire)
    (prior bits : List Bool) (ψ : State) :
    fourierBranch dir (ws.map e) prior bits (relabelState e ψ) =
      relabelState e (fourierBranch dir ws prior bits ψ) := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single s c =>
    have hs : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [hs]
    simp only [map_smul, relabelState_ket, fourierBranch_ket, coefficient_relabel,
      clear_relabel]

def relabelModel {n : Nat} {read : ConstantBit n → Bool} (e : Wire ≃ Wire)
    (m : WindowModel read) : WindowModel read where
  physical := ⟨m.physical.wires.map e,m.physical.count,
    fun start => relabelStraight e (m.physical.program start)⟩
  point := m.point
  bias := m.bias
  ideal := (relabelState e).comp (m.ideal.comp (relabelState e.symm))
  valid := fun s => m.valid (relabelBasis e.symm s)
  nodup := m.nodup.map e.injective
  coherent := by
    intro start history
    rw [relabelStraight_instantiate]
    exact (m.coherent start history).relabel e

theorem hadamards_relabel (e : Wire ≃ Wire) (ws : List Wire) (ψ : State) :
    Quantum.run ((ws.map e).map Gate.H) (relabelState e ψ) =
      relabelState e (Quantum.run (ws.map Gate.H) ψ) := by
  have he : (ws.map e).map Gate.H = (ws.map Gate.H).map (Gate.relabel e) := by
    simp only [List.map_map, Function.comp_def, Gate.relabel]
  rw [he]
  exact Quantum.run_relabel e _ ψ

theorem relabelModel_step {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read) (prior bits : List Bool) (ψ : State) :
    (relabelModel e m).step prior bits (relabelState e ψ) =
      relabelState e (m.step prior bits ψ) := by
  simp only [WindowModel.step, relabelModel, LinearMap.comp_apply, ← List.map_reverse,
    hadamards_relabel, relabelState_symm, fourier_relabel]

theorem root_relabel (e : Wire ≃ Wire) (he : e 836 = 836) :
    relabelBasis e initialRoot = initialRoot := by
  have hz : relabelBasis e zeroBasisState = zeroBasisState := rfl
  simp only [initialRoot, relabelBasis_upd, hz, he]

theorem relabelModel_pointRule {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read)
    (pointFrame : ∀ P s, relabelBasis e (pointWrite P s) = pointWrite P (relabelBasis e s))
    (he : e 836 = 836) (h : PointRule initialRoot m) :
    PointRule initialRoot (relabelModel e m) := by
  intro prior bits P
  have hk : ket (pointWrite P initialRoot) = relabelState e (ket (pointWrite P initialRoot)) := by
    rw [relabelState_ket, pointFrame, root_relabel e he]
  rw [hk, relabelModel_step, h]
  simp only [map_smul, map_list_sum, relabelState_ket, pointFrame, root_relabel e he,
    List.map_map, Function.comp_def, relabelModel, List.length_map]

theorem supported_relabel (e : Wire ≃ Wire) (V : BasisState → Prop) (ψ : State)
    (hψ : SupportedOn V ψ) :
    SupportedOn (fun s => V (relabelBasis e.symm s)) (relabelState e ψ) := by
  refine Support.linear V (fun s => V (relabelBasis e.symm s)) (relabelState e) ?_ ψ hψ
  intro s hs
  rw [relabelState_ket]
  exact supportedOn_ket _ _ (by simpa only [relabelBasis_symm] using hs)

theorem relabelModel_prepared {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read)
    (pointFrame : ∀ P s, relabelBasis e.symm (pointWrite P s) = pointWrite P (relabelBasis e.symm s))
    (he : e 836 = 836)
    (hp : ∀ ψ, SupportedOn (pointFamily initialRoot) ψ →
      SupportedOn m.valid (Quantum.run (m.physical.wires.reverse.map Gate.H) ψ))
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (relabelModel e m).valid
      (Quantum.run ((relabelModel e m).physical.wires.reverse.map Gate.H) ψ) := by
  have hes : e.symm 836 = 836 := (Equiv.symm_apply_eq e).mpr he.symm
  have hs : SupportedOn (pointFamily initialRoot) (relabelState e.symm ψ) := by
    refine Support.linear (pointFamily initialRoot) (pointFamily initialRoot) (relabelState e.symm) ?_ ψ hψ
    intro s hs
    obtain ⟨P,rfl⟩ := hs
    rw [relabelState_ket, pointFrame, root_relabel e.symm hes]
    exact supportedOn_ket _ _ ⟨P,rfl⟩
  have hc := supported_relabel e m.valid _ (hp _ hs)
  have hh := hadamards_relabel e m.physical.wires.reverse (relabelState e.symm ψ)
  rw [relabelState_symm_right] at hh
  simpa only [relabelModel, ← List.map_reverse, hh] using hc

end
end ShorECDLP.Entrant.Width16Actual


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule
noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

attribute [local irreducible] WideBank8.Signed16.program WEXFast.W15G.fastBodyProgram
  WEXFast.W15G.compactProgram WideBank8.Row16.program PathShare.narrowCF15

local notation "wideCredit" =>
  (2 * WideSigned.Body.signCredit + WideBank8.Fast16.fcodeTP WideBank8.Row16.code)
local notation "normalCredit" =>
  (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    WEXFast.gcodeTP WEXFast.rowCF)

def wide : Window 65536 :=
  ⟨(WideSigned.Body.logicalBank .w16).reverse.map TightSupport.compact,
    1744024, fun start => relabelStraight TightSupport.compact (WideBank8.Signed16.program start)⟩

def normal : Window 32768 :=
  ⟨streamAddress.reverse,1653272,WEXFast.W15G.compactProgram⟩

def signed : Digit → Window 1769472 := familyWindows wide normal


theorem signed_width (w : Digit) : (signed w).wires.length = w.width :=
  family_widths wide normal (by simp only [wide,List.length_map,List.length_reverse]; decide) (by decide) w

theorem signed_count (w : Digit) : (signed w).count = count 1744024 1653272 w :=
  family_counts wide normal w

theorem signed_credit (w : Digit) (start : Nat) :
    ProgramCredit ((signed w).program start) (count wideCredit normalCredit w) := by
  cases w with
  | left17 j | right17 j =>
    rw [count]
    change ProgramCredit (reindexStraight _ (relabelStraight _ (WideBank8.Signed16.program start))) wideCredit
    constructor
    · rw [WEXCredit.residue_reindex, WEXUnlookup.residue_relabel]
      exact (WideBank8.Signed16.program_credit start).1
    · rw [added_reindex, added_relabel]
      exact (WideBank8.Signed16.program_credit start).2
  | left16 j =>
    rw [count]
    constructor
    · rw [show ((signed (.left16 j)).program start) = reindexStraight (row (.left16 j)) (WEXFast.W15G.compactProgram start) from rfl,
        WEXCredit.residue_reindex]
      exact by rw [WEXFast.W15G.compactProgram,WEXUnlookup.residue_relabel]; exact (WEXFast.W15G.fastBodyProgram_credit start).1
    · rw [show ((signed (.left16 j)).program start) = reindexStraight (row (.left16 j)) (WEXFast.W15G.compactProgram start) from rfl,
        added_reindex]
      exact by rw [WEXFast.W15G.compactProgram,added_relabel]; exact (WEXFast.W15G.fastBodyProgram_credit start).2
  | right16 j =>
    rw [count]
    constructor
    · rw [show ((signed (.right16 j)).program start) = reindexStraight (row (.right16 j)) (WEXFast.W15G.compactProgram start) from rfl,
        WEXCredit.residue_reindex]
      exact by rw [WEXFast.W15G.compactProgram,WEXUnlookup.residue_relabel]; exact (WEXFast.W15G.fastBodyProgram_credit start).1
    · rw [show ((signed (.right16 j)).program start) = reindexStraight (row (.right16 j)) (WEXFast.W15G.compactProgram start) from rfl,
        added_reindex]
      exact by rw [WEXFast.W15G.compactProgram,added_relabel]; exact (WEXFast.W15G.fastBodyProgram_credit start).2

def implementation : Implementation :=
  withHeads 1744024 1653272 wideCredit normalCredit signed signed_width signed_count
    (fun w start => (signed_credit w start).1) (fun w start => (signed_credit w start).2)


theorem withHeads_credits {r17 r16 c17 c16 : Nat} {s : Digit → Window 1769472} {hw hc hz ha} :
    (withHeads r17 r16 c17 c16 s hw hc hz ha).credit17 = c17 ∧
      (withHeads r17 r16 c17 c16 s hw hc hz ha).credit16 = c16 := ⟨rfl, rfl⟩

theorem credits : implementation.credit17 ≤ 2343187 ∧ implementation.credit16 ≤ 2252440 := by
  rw [implementation, withHeads_credits.1, withHeads_credits.2]
  exact ⟨WideBank8.Signed16.credit_bound, WEXFast.W15G.fastCount_upper⟩

theorem signed_support (w : Digit) (start : Nat) :
    straightWires ((signed w).program start) ⊆ List.range 1618 := by
  cases w with
  | left17 j | right17 j =>
    change straightWires (reindexStraight _ (relabelStraight _ (WideBank8.Signed16.program start))) ⊆ _
    rw [straightWires_reindex]
    exact WideBank8.Fast16.Tight.packed_support start
  | left16 j =>
    change straightWires (reindexStraight _ (WEXFast.W15G.compactProgram start)) ⊆ _
    rw [straightWires_reindex, WEXFast.W15G.compactProgram]
    exact (PathShare.relabelH_support _ (WEXFast.W15G.fastBodyProgram_support start)).trans (List.range_subset.mpr (by decide : 1616 ≤ 1618))
  | right16 j =>
    change straightWires (reindexStraight _ (WEXFast.W15G.compactProgram start)) ⊆ _
    rw [straightWires_reindex, WEXFast.W15G.compactProgram]
    exact (PathShare.relabelH_support _ (WEXFast.W15G.fastBodyProgram_support start)).trans (List.range_subset.mpr (by decide : 1616 ≤ 1618))


theorem signed_wellFormed (w : Digit) (start : Nat) : ((signed w).program start).WellFormed := by
  cases w with
  | left17 j | right17 j =>
    apply (reindexStraight_wellFormed _ _).mpr
    exact (relabelStraight_wellFormed _ _).mpr (WideBank8.Signed16.wellFormed start)
  | left16 j | right16 j =>
    apply (reindexStraight_wellFormed _ _).mpr
    change (WEXFast.W15G.compactProgram start).WellFormed
    rw [WEXFast.W15G.compactProgram]
    exact (relabelStraight_wellFormed _ _).mpr (WEXFast.W15G.fastBodyProgram_wellFormed start)

end
end ShorECDLP.Entrant.Width16Actual


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] fourierOutcomes WEXFast.W15G.fastBodyProgram WEXFast.W15G.compactProgram

def normalPoint (coeffs : Fin 32768 → PointCoeff) (Q : Point) (v : Nat) : Point :=
  if v < 32768 then -constantPoint Q (coeffs ⟨(32767-v)%32768,Nat.mod_lt _ (by decide)⟩)
  else constantPoint Q (coeffs ⟨(v-32768)%32768,Nat.mod_lt _ (by decide)⟩)

def normalModel (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) : WindowModel (readConstant coeffs Q) where
  physical := normal
  point := normalPoint coeffs Q
  bias := 0
  ideal := Finsupp.lmapDomain ℂ ℂ (PathShare.stateH coeffs Q)
  valid := fun s => PathShare.readyH s ∧ ∃ P, pointStateCoordinates s=fig14PointEncoding P
  nodup := by decide
  coherent := by
    intro start history
    simpa only [normal,WEXFast.W15G.compactProgram] using
      PathShare.relabelH_coherent _ coeffs Q history
        (WEXFast.W15G.fastBodyProgram_coherent coeffs Q hQ hn start history)

theorem normal_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : PathShare.readyH s) (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    PathShare.stateH coeffs Q s = pointWrite (P+normalPoint coeffs Q (windowRawDigit 0 s)) s := by
  have hl : tableAddressValue WEX.windowBits s < 32768 := by
    simpa only [WEX.windowBits,List.length_range'] using tableAddressValue_lt WEX.windowBits s
  have hv : windowRawDigit 0 s = tableAddressValue WEX.windowBits s + Bool.toNat (s 870) * 32768 := by
    rw [WEX.tableAddress_word]
    change boolWordToNat (wireValues (List.range' 855 15) s)+32768*(s 870).toNat =
      boolWordToNat (wireValues (List.range' 855 15) s)+(s 870).toNat*32768
    omega
  have hsel : (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
      signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
    else -constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
      signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)) =
      normalPoint coeffs Q (windowRawDigit 0 s) := by
    cases hb : s 870
    · have hlow : windowRawDigit 0 s < 32768 := by
        simp only [hb,Bool.toNat_false,Nat.zero_mul,Nat.add_zero] at hv
        omega
      simp only [hb,Bool.false_eq_true,if_false,normalPoint,if_pos hlow]
      apply congrArg (fun a : Fin 32768 => -constantPoint Q (coeffs a))
      apply Fin.ext
      simp only [signedTableAddress,if_pos hlow,Fin.val_mk]
      rw [Nat.mod_eq_of_lt (by omega)]
    · have hhigh : ¬windowRawDigit 0 s < 32768 := by
        simp only [hb,Bool.toNat_true,Nat.one_mul] at hv
        omega
      have hval : windowRawDigit 0 s - 32768 < 32768 := by
        have := windowRawDigit_bound 0 s
        omega
      simp only [hb,if_true,normalPoint,if_neg hhigh]
      apply congrArg (fun a : Fin 32768 => constantPoint Q (coeffs a))
      apply Fin.ext
      simp only [signedTableAddress,if_neg hhigh,Fin.val_mk]
      rw [Nat.mod_eq_of_lt hval]
  rw [PathShare.stateH_correct coeffs Q s hs P hP,PathShare.readyH_active s hs]
  rw [if_pos (show true=true from rfl)]
  exact congrArg (fun R : Point => pointWrite (P+R) s) hsel

theorem normal_assigned_valid (root : BasisState) (hs : FirstWindowInput root)
    (P : Point) (input : List Bool) :
    PathShare.readyH (phaseWordState streamAddress input (pointWrite P root)) ∧
      ∃ A,pointStateCoordinates (phaseWordState streamAddress input (pointWrite P root))=fig14PointEncoding A := by
  refine ⟨phaseWordState_preserves PathShare.readyH streamAddress PathShare.readyH_address
    input _ (PathShare.readyH_first root hs P),P,?_⟩
  rw [phaseWordState_pointWrite _ (by decide),pointWrite_coordinates]

theorem normal_pointRule (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q=0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (normalModel coeffs Q hQ hn) := by
  intro prior output P
  have hc : Clean streamAddress (pointWrite P root) := by
    intro v hv
    rw [pointWrite_frame _ _ _ ((show ∀ v ∈ streamAddress,v ∉ pointLogicalWires by decide) v hv)]
    exact hz v hv
  have hcoords (input : List Bool) :
      pointStateCoordinates (phaseWordState streamAddress input (pointWrite P root)) = fig14PointEncoding P := by
    rw [phaseWordState_pointWrite _ (by decide),pointWrite_coordinates]
  have hword (input : List Bool) (hi : input.length=streamAddress.length) :
      streamAddress.map (PathShare.stateH coeffs Q (phaseWordState streamAddress input (pointWrite P root))) = input := by
    rw [normal_correct coeffs Q _ (normal_assigned_valid root hs P input).1 P (hcoords input)]
    have hf : streamAddress.map (pointWrite
        (P+normalPoint coeffs Q (windowRawDigit 0 (phaseWordState streamAddress input (pointWrite P root))))
        (phaseWordState streamAddress input (pointWrite P root))) =
        streamAddress.map (phaseWordState streamAddress input (pointWrite P root)) := by
      apply List.map_congr_left
      intro v hv
      exact pointWrite_frame _ _ _ ((show ∀ v ∈ streamAddress,v ∉ pointLogicalWires by decide) v hv)
    rw [hf]
    exact phaseWordState_word _ (by decide) input hi _
  simp only [WindowModel.step,normalModel,normal,List.reverse_reverse,LinearMap.comp_apply,List.length_reverse]
  rw [window_branch_uniform .inverse streamAddress (by decide) (PathShare.stateH coeffs Q)
    prior output _ hc (fun input hi => hword input ((fourierOutcomes_mem _ _).mp hi))]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ))^streamAddress.length) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  have hr : windowRawDigit 0 (phaseWordState streamAddress input (pointWrite P root)) = boolWordToNat input := by
    exact assigned_window_digit input ((fourierOutcomes_mem _ _).mp hi) _
  rw [normal_correct coeffs Q _ (normal_assigned_valid root hs P input).1 P (hcoords input),hr,
    clear_assigned_point _ input (pointWrite P root) hc (by decide),pointWrite_overwrite]

theorem normal_prepared (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q=0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (normalModel coeffs Q hQ hn).valid
      (Quantum.run ((normalModel coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ) := by
  simp only [normalModel,normal,List.reverse_reverse]
  refine Support.linear (pointFamily root) (normalModel coeffs Q hQ hn).valid
    (Quantum.run (streamAddress.map Gate.H)) ?_ ψ hψ
  intro s hs'
  obtain ⟨P,rfl⟩ := hs'
  have hc : Clean streamAddress (pointWrite P root) := by
    intro v hv
    rw [pointWrite_frame _ _ _ ((show ∀ v ∈ streamAddress,v ∉ pointLogicalWires by decide) v hv)]
    exact hz v hv
  rw [phaseHadamards_uniform _ (by decide) _ hc]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact supportedOn_ket _ _ (normal_assigned_valid root hs P input)

end
end ShorECDLP.Entrant.Width16Actual


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem positivePoint_eq (Q : Point) (w : Digit) (a : Nat) :
    positivePoint Q w a = (2*a+1) • ((halfOrder*2^w.exponent) • w.base Q) := by
  unfold Width16Schedule.positivePoint Single.oddScalar
  rw [Nat.mul_assoc,Nat.mul_comm (2^w.exponent) halfOrder,mul_smul]

theorem signed_magnitude (P : Point) (half v : Nat) (_hh : 0<half) (hv : v<2*half) :
    (if v<half then -((2*((half-1-v)%half)+1) • P)
      else (2*((v-half)%half)+1) • P) =
      (2*(v:Int)-2*(half:Int)+1) • P := by
  rw [← signedTableOdd_value half v]
  unfold signedTableOdd signedTableAddress
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [neg_smul,natCast_zsmul]
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [natCast_zsmul]

theorem selected_point (Q : Point) (w : Digit) (v : Nat) (hv : v<2^w.width) :
    (if v<2^(w.width-1) then -positivePoint Q w ((2^(w.width-1)-1-v)%2^(w.width-1))
      else positivePoint Q w ((v-2^(w.width-1))%2^(w.width-1))) =
      Width16Schedule.increment (w.base Q) w.width w.exponent v := by
  simp only [positivePoint_eq]
  have hp : 2^w.width=2*2^(w.width-1) := by rcases width_cases w with h|h <;> rw [h] <;> decide
  rw [signed_magnitude _ _ _ (by positivity) (by omega)]
  unfold Width16Schedule.increment
  have he : (2:Int)^w.width=2*(2^(w.width-1):Nat) := by
    rcases width_cases w with h|h <;> rw [h] <;> norm_num
  rw [he]

def localCoefficients (w : Digit) : Fin (2^(w.width-1)) → PointCoeff :=
  fun a => signedCoefficients w a.val

theorem local_nonzero (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit)
    (a : Fin (2^(w.width-1))) : constantPoint Q (localCoefficients w a) ≠0 := by
  rw [localCoefficients,signedCoefficients_point Q hQ]
  exact positivePoint_ne_zero Q hQ hn w a.val a.isLt

end
end ShorECDLP.Entrant.Width16Actual


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] fourierOutcomes WideBank8.Signed16.program
local instance bodyInstance : Single.WindowBody := PathShare.bodyCF
local instance resourceInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0:Wire)∈resetWires; decide)
    (by change (1:Wire)∈resetWires; decide)

def interpretModel {n} {read : ConstantBit n→Bool} (m : WindowModel read)
    (point : Nat→Point) (bias : Point) : WindowModel read := {m with point:=point,bias:=bias}

theorem interpret_pointRule {n} {read : ConstantBit n→Bool} (m : WindowModel read)
    (point : Nat→Point) (bias : Point) (root : BasisState)
    (hm : PointRule root m) (hp : ∀ v, v<2^m.physical.wires.length → m.point v=point v) :
    PointRule root (interpretModel m point bias) := by
  intro prior output P
  change m.step prior output (ket (pointWrite P root)) = _
  rw [hm prior output P]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^m.physical.wires.length) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [hp _ (by simpa only [(fourierOutcomes_mem _ _).mp hi] using boolWordToNat_lt_pow_two input)]
  rfl

/-- Coefficients of a 17-wire body window (left or right axis). -/
def wideCoefficients (d : Digit) : Fin 65536 → PointCoeff := fun a => signedCoefficients d a.val

theorem wide_nonzero (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17)
    (a : Fin 65536) : constantPoint Q (wideCoefficients d a) ≠ 0 := by
  rw [wideCoefficients, Width16Schedule.signedCoefficients_point Q hQ]
  exact Width16Schedule.positivePoint_ne_zero Q hQ hn d a.val (by rw [hw]; exact a.isLt)

theorem wide_point (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17)
    (v : Nat) (hv : v<131072) :
    (WideBank8.Signed16.model (wideCoefficients d) Q hQ (wide_nonzero Q hQ hn d hw)).point v =
      Width16Schedule.increment (d.base Q) 17 d.exponent v := by
  change (if v<65536 then -constantPoint Q
      (wideCoefficients d (WideSigned.Geometry.rows .w16 (65535-v)))
    else constantPoint Q (wideCoefficients d (WideSigned.Geometry.rows .w16 (v-65536)))) = _
  simp only [wideCoefficients,WideSigned.Geometry.rows,WideSigned.Geometry.Width.bits,
    Width16Schedule.signedCoefficients_point Q hQ]
  have h := selected_point Q d v (by rw [hw]; exact hv)
  rw [hw] at h
  exact h

theorem normal_point (Q : Point) (hQ : order•Q=0) (w : Digit) (hw : w.width=16)
    (v : Nat) (hv : v<65536) :
    normalPoint (fun a : Fin 32768 => Width16Schedule.signedCoefficients w a.val) Q v =
      Width16Schedule.increment (w.base Q) w.width w.exponent v := by
  simp only [normalPoint,Width16Schedule.signedCoefficients_point Q hQ]
  have h := selected_point Q w v (by simpa only [hw] using hv)
  simpa only [hw] using h

def wideRawModel (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17) :=
  interpretModel
    (WideBank8.Signed16.model (wideCoefficients d) Q hQ (wide_nonzero Q hQ hn d hw))
    (Width16Schedule.increment (d.base Q) 17 d.exponent)
    (offsetScalar 17 d.exponent • d.base Q)

def widePackedModel (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17) :=
  relabelModel TightSupport.compact (wideRawModel Q hQ hn d hw)

theorem normal_nonzero (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit) (hw : w.width=16)
    (a : Fin 32768) : constantPoint Q (Width16Schedule.signedCoefficients w a.val) ≠ 0 := by
  rw [Width16Schedule.signedCoefficients_point Q hQ]
  exact Width16Schedule.positivePoint_ne_zero Q hQ hn w a.val (by simpa only [hw] using a.isLt)

def localNormalModel (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit) (hw : w.width=16) :=
  interpretModel
    (normalModel (fun a : Fin 32768 => Width16Schedule.signedCoefficients w a.val) Q hQ
      (normal_nonzero Q hQ hn w hw))
    (Width16Schedule.increment (w.base Q) w.width w.exponent)
    (offsetScalar w.width w.exponent • w.base Q)

def signedModel (Q : Point) (hQ : order•Q=0) (hn : Q≠0) :
    Digit→WindowModel (readConstant Width16Schedule.coefficientAt Q)
  | .left17 j => reindexModel (wideCoefficients (.left17 j)) Width16Schedule.coefficientAt
      (row (.left17 j)) (fun a => (coefficientAt_row (.left17 j) a).symm) Q
      (widePackedModel Q hQ hn (.left17 j) rfl)
  | .right17 j => reindexModel (wideCoefficients (.right17 j)) Width16Schedule.coefficientAt
      (row (.right17 j)) (fun a => (coefficientAt_row (.right17 j) a).symm) Q
      (widePackedModel Q hQ hn (.right17 j) rfl)
  | .left16 j => reindexModel (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.left16 j) a.val)
      Width16Schedule.coefficientAt (row (.left16 j)) (fun a => (coefficientAt_row (.left16 j) a).symm) Q
      (localNormalModel Q hQ hn (.left16 j) rfl)
  | .right16 j => reindexModel (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.right16 j) a.val)
      Width16Schedule.coefficientAt (row (.right16 j)) (fun a => (coefficientAt_row (.right16 j) a).symm) Q
      (localNormalModel Q hQ hn (.right16 j) rfl)

def models (Q : Point) (hQ : order•Q=0) (hn : Q≠0) : ModelFrame implementation Q where
  headA := Width16Schedule.headAModel Q hQ hn
  headB := Width16Schedule.headBModel Q
  signed := signedModel Q hQ hn
  headA_physical := rfl
  headB_physical := rfl
  signed_physical := by intro w; cases w <;> rfl
  headA_point := fun _ => rfl
  headA_bias := rfl
  headB_point := fun _ => rfl
  headB_bias := rfl
  signed_point := by intro w v; cases w <;> rfl
  signed_bias := by intro w; cases w <;> rfl

theorem wide_raw_rule (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17) :
    PointRule initialRoot (wideRawModel Q hQ hn d hw) := by
  apply interpret_pointRule
  · exact WideBank8.Signed16.pointRule (wideCoefficients d) Q hQ
      (wide_nonzero Q hQ hn d hw) initialRoot initialRoot_input.1 (by
      intro v hv
      have hb := WideSigned.Body.bank_bounds .w16 v hv
      simp only [initialRoot,upd,zeroBasisState]
      split_ifs <;> dsimp only [Wire] at * <;> omega)
  · intro v hv
    exact wide_point Q hQ hn d hw v hv

theorem inverse_pointFrame (P : Point) (s : BasisState) :
    relabelBasis TightSupport.compact.symm (pointWrite P s) =
      pointWrite P (relabelBasis TightSupport.compact.symm s) := by
  have h := congrArg (relabelBasis TightSupport.compact.symm)
    (TightSupport.compact_pointWrite P (relabelBasis TightSupport.compact.symm s))
  have hr : relabelBasis TightSupport.compact (relabelBasis TightSupport.compact.symm s)=s := by
    simpa only [Equiv.symm_symm] using relabelBasis_symm TightSupport.compact.symm s
  simpa only [relabelBasis_symm,hr] using h.symm

theorem signed_rule (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit) :
    PointRule initialRoot (signedModel Q hQ hn w) := by
  cases w with
  | left17 j =>
    change PointRule initialRoot (widePackedModel Q hQ hn (.left17 j) rfl)
    exact relabelModel_pointRule _ _ TightSupport.compact_pointWrite
      TightSupport.compact_active (wide_raw_rule Q hQ hn (.left17 j) rfl)
  | right17 j =>
    change PointRule initialRoot (widePackedModel Q hQ hn (.right17 j) rfl)
    exact relabelModel_pointRule _ _ TightSupport.compact_pointWrite
      TightSupport.compact_active (wide_raw_rule Q hQ hn (.right17 j) rfl)
  | left16 j =>
    change PointRule initialRoot (localNormalModel Q hQ hn (.left16 j) rfl)
    apply interpret_pointRule
    · exact normal_pointRule (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.left16 j) a.val)
        Q hQ (normal_nonzero Q hQ hn (.left16 j) rfl) initialRoot initialRoot_input initialRoot_clean
    · intro v hv
      exact normal_point Q hQ (.left16 j) rfl v hv
  | right16 j =>
    change PointRule initialRoot (localNormalModel Q hQ hn (.right16 j) rfl)
    apply interpret_pointRule
    · exact normal_pointRule (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.right16 j) a.val)
        Q hQ (normal_nonzero Q hQ hn (.right16 j) rfl) initialRoot initialRoot_input initialRoot_clean
    · intro v hv
      exact normal_point Q hQ (.right16 j) rfl v hv

theorem wide_raw_prepared (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (wideRawModel Q hQ hn d hw).valid
      (Quantum.run ((wideRawModel Q hQ hn d hw).physical.wires.reverse.map Gate.H) ψ) := by
  have hfamily : SupportedOn (pointFamily (pointWrite 0 initialRoot)) ψ := by
    intro s hs
    obtain ⟨P,hP⟩ := hψ s hs
    exact ⟨P,by rw [pointWrite_overwrite]; exact hP⟩
  exact WideBank8.Signed16.prepared (wideCoefficients d) Q hQ
    (wide_nonzero Q hQ hn d hw) (pointWrite 0 initialRoot)
    (WEX.windowReady_first initialRoot initialRoot_input 0)
    (by
      intro v hv
      rw [pointWrite_frame _ _ _ (WideSigned.Body.bank_not_point .w16 v hv)]
      have hb := WideSigned.Body.bank_bounds .w16 v hv
      simp only [initialRoot,upd,zeroBasisState]
      split_ifs <;> dsimp only [Wire] at * <;> omega)
    ψ hfamily

theorem signed_prepared (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (signedModel Q hQ hn w).valid
      (Quantum.run ((signedModel Q hQ hn w).physical.wires.reverse.map Gate.H) ψ) := by
  cases w with
  | left17 j =>
    exact relabelModel_prepared _ _ inverse_pointFrame TightSupport.compact_active
      (wide_raw_prepared Q hQ hn (.left17 j) rfl) ψ hψ
  | right17 j =>
    exact relabelModel_prepared _ _ inverse_pointFrame TightSupport.compact_active
      (wide_raw_prepared Q hQ hn (.right17 j) rfl) ψ hψ
  | left16 j =>
    exact normal_prepared (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.left16 j) a.val)
      Q hQ (normal_nonzero Q hQ hn (.left16 j) rfl) initialRoot initialRoot_input initialRoot_clean ψ hψ
  | right16 j =>
    exact normal_prepared (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.right16 j) a.val)
      Q hQ (normal_nonzero Q hQ hn (.right16 j) rfl) initialRoot initialRoot_input initialRoot_clean ψ hψ

theorem signed_preserves (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit)
    (prior bits : List Bool) (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (pointFamily initialRoot) ((signedModel Q hQ hn w).step prior bits ψ) := by
  refine Support.linear (pointFamily initialRoot) (pointFamily initialRoot)
    ((signedModel Q hQ hn w).step prior bits) ?_ ψ hψ
  intro s hs
  obtain ⟨P,rfl⟩ := hs
  rw [signed_rule Q hQ hn w prior bits P]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact Support.smul _ (supportedOn_ket _ _ ⟨_,rfl⟩)

theorem ready_signed (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (ws : List Digit)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    Ready (ws.map (signedModel Q hQ hn)) ψ := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨signed_prepared Q hQ hn w ψ hψ,fun prior bits=>
      ih _ (signed_preserves Q hQ hn w prior bits ψ hψ)⟩

theorem ready_models (Q : Point) (hQ : order•Q=0) (hn : Q≠0) :
    Ready ((models Q hQ hn).headA :: (models Q hQ hn).headB ::
      (leftDigits.map (models Q hQ hn).signed ++ rightDigits.map (models Q hQ hn).signed))
      (ket initialRoot) := by
  rw [← List.map_append]
  constructor
  · change SupportedOn SelectSchedule18.Input
      (Quantum.run (headLWires.reverse.reverse.map Gate.H) (ket initialRoot))
    rw [List.reverse_reverse]
    exact SelectSchedule18.input_prepare _ headL_sub _
      (supportedOn_ket _ _ (SelectSchedule18.input_of_strong initialRoot initialRoot_input))
  · intro prior bits
    constructor
    · intro s _
      trivial
    · intro prior' bits'
      apply ready_signed Q hQ hn (leftDigits++rightDigits)
      change SupportedOn (pointFamily initialRoot)
        ((Width16Schedule.headBModel Q).step prior' bits'
          ((Width16Schedule.headAModel Q hQ hn).step prior bits (ket initialRoot)))
      rw [Width16Schedule.joint_first_step Q hQ hn prior bits prior' bits' initialRoot
        initialRoot_input initialRoot_clean]
      apply Support.smul
      apply Support.list_sum
      intro inL hinL
      apply Support.list_sum
      intro inR hinR
      exact Support.smul _ (supportedOn_ket _ _ ⟨_,rfl⟩)

end
end ShorECDLP.Entrant.Width16Actual

namespace ShorECDLP.Entrant.Width16Readout
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule RoundedReadout
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
local instance bodyInstance : Single.WindowBody := PathShare.bodyCF
local instance ledgerInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0:Wire)∈resetWires; decide)
    (by change (1:Wire)∈resetWires; decide)
variable (impl : Implementation)

abbrev reset := resetWires
abbrev startCursor := cursor impl reset

def fineEvent (accept : Nat→Nat→Bool) (history : List Bool) : Bool :=
  pairAccept (trialPositions impl.records17 impl.records16).left.toList
    (trialPositions impl.records17 impl.records16).right.toList accept history

theorem model_left (Q : Point) (m : ModelFrame impl Q) :
    (leftDigits.map m.signed).map WindowModel.physical = Width16Schedule.leftBodies impl := by
  simp only [List.map_map,Function.comp_def,m.signed_physical,Width16Schedule.leftBodies]

theorem model_right (Q : Point) (m : ModelFrame impl Q) :
    (rightDigits.map m.signed).map WindowModel.physical = Width16Schedule.rightBodies impl := by
  simp only [List.map_map,Function.comp_def,m.signed_physical,Width16Schedule.rightBodies]

theorem event_mass (Q : Point) (hQ : order•Q=0) (m : ModelFrame impl Q)
    (hfirst : ∀ bA ∈ fourierOutcomes (modelDigit m.headA).width,
      ∀ bB ∈ fourierOutcomes (modelDigit m.headB).width,
        m.headB.step List.nil bB (m.headA.step List.nil bA (ket initialRoot)) =
          jointClosedForm (modelDigit m.headA) (modelDigit m.headB) bA bB initialRoot)
    (pointRules : ∀ w∈leftDigits++rightDigits,PointRule initialRoot (m.signed w))
    (ready : Ready (m.headA :: m.headB :: ((leftDigits.map m.signed) ++ (rightDigits.map m.signed)))
      (ket initialRoot))
    (J : Instrument) (hJ : ∀ ψ,J.bornMass ψ=normSq ψ) (accept : Nat→Nat→Bool) :
    Instrument.bornMass
      (((mixedData impl.headA impl.headB (Width16Schedule.leftBodies impl)
        (Width16Schedule.rightBodies impl) (readConstant Width16Schedule.coefficientAt Q)
        0 Fin.elim0).seq J).filter (fun b => fineEvent impl accept b.history)) (ket initialRoot) =
      idealEventMass Q initialRoot 261 208 accept := by
  have hm := conditional_event_mass impl Q hQ m initialRoot (ket initialRoot) hfirst
    pointRules ready 0 Fin.elim0 J hJ accept
  rw [selectedMixed_fixed_filter] at hm
  rw [m.headA_physical, m.headB_physical, model_left impl Q m, model_right impl Q m] at hm
  have hA : axisPositions [impl.headA] 0 = positions [(132606,10)] 0 := by
    simp [Single.axisPositions, impl.headA_count, impl.headA_width]
  have hB : axisPositions [impl.headB] (mixS1 impl.headA 0) = positions [(0,8)] 132616 := by
    simp [Single.axisPositions, impl.headB_count, impl.headB_width, mixS1, Width16Schedule.headA_axisCount]
  have hL : axisPositions (Width16Schedule.leftBodies impl) (mixS2 impl.headA impl.headB 0) =
      positions (Width16Schedule.leftMetadata impl.records17 impl.records16) 132624 := by
    rw [Single.axisPositions, Width16Schedule.left_metadata]
    simp [mixS2, mixS1, Width16Schedule.headA_axisCount, Width16Schedule.headB_axisCount]
  have hR : axisPositions (Width16Schedule.rightBodies impl)
      (mixS3 impl.headA impl.headB (Width16Schedule.leftBodies impl) 0) =
      positions (Width16Schedule.rightMetadata impl.records17 impl.records16)
        (132624 + (11*impl.records17 + 4*impl.records16 + 251)) := by
    rw [Single.axisPositions, Width16Schedule.right_metadata]
    simp only [mixS3, mixS2, mixS1, Width16Schedule.headA_axisCount, Width16Schedule.headB_axisCount,
      Width16Schedule.left_count, Nat.zero_add]
  rw [hA, hB, hL, hR] at hm
  simpa only [fineEvent,Width16Schedule.trialPositions,Width16Schedule.leftPositions,
    Width16Schedule.rightPositions,Vector.toList_mk,List.toList_toArray] using hm

theorem program_run_data (read : ConstantBit 1769472→Bool) :
    ((Width16Schedule.program impl reset).instantiate read Fin.elim0).run =
      ((mixedData impl.headA impl.headB (Width16Schedule.leftBodies impl)
        (Width16Schedule.rightBodies impl) read 0 Fin.elim0).seq terminalInstrument).map
        (fun b => ({history := List.nil,kraus := Quantum.run [.X 836]}:InstrumentBranch).seq b) := by
  unfold Width16Schedule.program
  have hh : mixS4 impl.headA impl.headB (Width16Schedule.leftBodies impl)
      (Width16Schedule.rightBodies impl) 0 + reset.length = cursor impl reset := by
    rw [Width16Schedule.mixS4_value]
    unfold cursor
    omega
  simpa only [mixedData,mixProgram,terminalInstrument,bodyInstance,PathShare.bodyCF,reset] using
    framed_reset_run (mixHead impl.headA 0)
      (mixTail impl.headA impl.headB (Width16Schedule.leftBodies impl) (Width16Schedule.rightBodies impl) 0)
      (resetProgram 1769472 (mixS4 impl.headA impl.headB (Width16Schedule.leftBodies impl)
        (Width16Schedule.rightBodies impl) 0) reset)
      hh read Fin.elim0 (measureResetWithCorrection reset (fun _=>List.nil))
      (fun h => resetProgram_run _ _ _ read h)

theorem program_event_mass (Q : Point) (hQ : order•Q=0) (m : ModelFrame impl Q)
    (hfirst : ∀ bA ∈ fourierOutcomes (modelDigit m.headA).width,
      ∀ bB ∈ fourierOutcomes (modelDigit m.headB).width,
        m.headB.step List.nil bB (m.headA.step List.nil bA (ket initialRoot)) =
          jointClosedForm (modelDigit m.headA) (modelDigit m.headB) bA bB initialRoot)
    (pointRules : ∀ w∈leftDigits++rightDigits,PointRule initialRoot (m.signed w))
    (ready : Ready (m.headA :: m.headB :: ((leftDigits.map m.signed) ++ (rightDigits.map m.signed)))
      (ket initialRoot))
    (accept : Nat→Nat→Bool) :
    Instrument.bornMass (((Width16Schedule.program impl reset).instantiate
      (readConstant Width16Schedule.coefficientAt Q) Fin.elim0).run.filter
      (fun b => fineEvent impl accept b.history)) (ket zeroBasisState) =
      idealEventMass Q initialRoot 261 208 accept := by
  rw [program_run_data,prefix_filter_mass _ ([Gate.X 836]) (fineEvent impl accept) (ket zeroBasisState)]
  have hs : Quantum.run [.X 836] (ket zeroBasisState)=ket initialRoot := by
    simp [Quantum.run,applyGate_ket,onKet,initialRoot,zeroBasisState]
  rw [hs]
  exact event_mass impl Q hQ m hfirst pointRules ready terminalInstrument terminalInstrument_mass accept

theorem program_clean (read : ConstantBit 1769472→Bool) (b : InstrumentBranch)
    (hb : b∈((Width16Schedule.program impl reset).instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [program_run_data] at hb
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hb
  obtain ⟨a,_,hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
  simp only [terminalInstrument,AdaptiveCircuit.run] at hc
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean bodyInstance.reset ledgerInstance.reset_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 ledgerInstance.reset_zero,h s hs 1 ledgerInstance.reset_one⟩

theorem verified_of_reads (ps : Vector Nat 208) (hps : ps∈Readout56.rightWords56 (fineBits impl reset))
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist (trialPositions impl.records17 impl.records16).left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d:ZMod order)∈fixedCandidates SinAverage261.params261 a b) :
    (verifiedCandidate (Width16Schedule.layout impl reset) Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d:ZMod order),?_,?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨positionsFor impl.records17 impl.records16 ps,List.mem_map.mpr ⟨ps,hps,rfl⟩,?_⟩
    simpa only [decodeTrial,trialCandidates,positionsFor,Width16Schedule.layout,hl,hr,
      fixedCandidates_take,Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq,ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order]; exact Nat.mod_mod _ _)

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q=d•G)
    (read : ConstantBit 1769472→Bool) (history : Fin (startCursor impl)→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : fineEvent impl (SinAverage261.pairRecovered261 d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈((readout impl reset).instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate (Width16Schedule.layout impl reset) Q (List.ofFn history++b.history)).isSome := by
  have hr := NeighborReadout.input_read (fineBits impl reset) history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩ := Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩ := of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩ := Readout56.suffix56_reads 1769472 (startCursor impl) (fineBits impl reset)
    read history ψ hψ b (by simpa only [readout,castFinish_instantiate] using hb) hn
    ((i.val:ℤ)-28) (by have h:=i.isLt;omega)
  apply verified_of_reads impl ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h := left_position_bound impl.records17 impl.records16 j hj
    have hh : 132875+11*impl.records17+4*impl.records16 ≤ startCursor impl := by
      unfold startCursor cursor
      omega
    simpa only [List.length_ofFn] using h.trans_le hh

theorem strong_success (Q : Point) (d : Nat) (hd : Q=d•G)
    (hQ : order•Q=0) (m : ModelFrame impl Q)
    (hfirst : ∀ bA ∈ fourierOutcomes (modelDigit m.headA).width,
      ∀ bB ∈ fourierOutcomes (modelDigit m.headB).width,
        m.headB.step List.nil bB (m.headA.step List.nil bA (ket initialRoot)) =
          jointClosedForm (modelDigit m.headA) (modelDigit m.headB) bA bB initialRoot)
    (pointRules : ∀ w∈leftDigits++rightDigits,PointRule initialRoot (m.signed w))
    (ready : Ready (m.headA :: m.headB :: ((leftDigits.map m.signed) ++ (rightDigits.map m.signed)))
      (ket initialRoot)) :
    (990038025/1000000000:ℝ) ≤ Instrument.bornMass
      (((fullProgram impl reset).instantiate (readConstant Width16Schedule.coefficientAt Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate (Width16Schedule.layout impl reset) Q b.history).isSome)) (ket zeroBasisState) := by
  have hneighbor : (990038025/1000000000:ℝ) ≤ Instrument.bornMass
      (((Width16Schedule.program impl reset).instantiate (readConstant Width16Schedule.coefficientAt Q) Fin.elim0).run.filter
        (fun b => fineEvent impl (SinAverage261.pairRecovered261 d) b.history)) (ket zeroBasisState) := by
    rw [program_event_mass impl Q hQ m hfirst pointRules ready,idealEventMass_distribution Q d hd]
    exact PhaseTrimHeadroom.improved_pair_success d
  apply hneighbor.trans
  unfold fullProgram
  rw [Single.append_run_history]
  apply Rounded.appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      ((readout impl reset).instantiate_wellFormed _ _ (readout_wellFormed impl reset)) _
  · intro a ha hf b hb hne
    have hlen : a.history.length=startCursor impl := by
      have h := straight_history_length (Width16Schedule.program impl reset)
        (readConstant Width16Schedule.coefficientAt Q) Fin.elim0 a ha
      simpa only [startCursor,Nat.zero_add,Nat.sub_zero] using h
    have hh : List.ofFn (Single.historyAfter (startCursor impl) Fin.elim0 a.history)=a.history := by
      simpa only [List.ofFn_zero,List.nil_append] using Single.historyAfter_list Fin.elim0 a.history
        (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept impl Q d hd (readConstant Width16Schedule.coefficientAt Q)
      (Single.historyAfter (startCursor impl) Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean impl _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh,InstrumentBranch.seq] using h

end
end ShorECDLP.Entrant.Width16Readout


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule ConditionalCatalyst
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] PathShare.narrowCF15 WideBank8.Signed16.program
  WideBank8.Row16.program Single.axis resetProgram
attribute [local instance] bodyInstance resourceInstance

def reset : List Wire := resetWires
abbrev impl := implementation
abbrev rawProgram := Width16Schedule.fullProgram impl reset
abbrev rawEntry := Width16Schedule.sourceEntry impl reset
abbrev rawLayout := Width16Schedule.layout impl reset

/-- Every window of the program is one of the two head banks or a signed body window. -/
def IsWin (w : Window 1769472) : Prop :=
  w = Width16Schedule.headA ∨ w = Width16Schedule.headB ∨ ∃ d, w = signed d

theorem isWin_headA : IsWin impl.headA := Or.inl rfl
theorem isWin_headB : IsWin impl.headB := Or.inr (Or.inl rfl)
theorem isWin_left (w : Window 1769472) (hw : w ∈ (Width16Schedule.leftBodies impl)) : IsWin w := by
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hw
  exact Or.inr (Or.inr ⟨d,rfl⟩)
theorem isWin_right (w : Window 1769472) (hw : w ∈ (Width16Schedule.rightBodies impl)) : IsWin w := by
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hw
  exact Or.inr (Or.inr ⟨d,rfl⟩)

theorem signed_slots (w : Digit) (start : Nat) : ((signed w).program start).gateSlots ≤ 3000000000 := by
  cases w with
  | left17 j | right17 j =>
    change (reindexStraight _ (relabelStraight _ (WideBank8.Signed16.program start))).gateSlots ≤ _
    rw [reindexStraight_gateSlots,relabelStraight_slots]
    exact (WideBank8.Signed16.slots start).trans (by decide)
  | left16 j | right16 j =>
    change (reindexStraight _ (WEXFast.W15G.compactProgram start)).gateSlots ≤ _
    rw [reindexStraight_gateSlots, WEXFast.W15G.compactProgram, relabelStraight_slots]
    exact (WEXFast.W15G.fastBodyProgram_slots_upper start).trans (by decide)

theorem win_wellFormed (w : Window 1769472) (hw : IsWin w) (start : Nat) :
    (w.program start).WellFormed := by
  rcases hw with rfl|rfl|⟨d,rfl⟩
  · exact prepareOuterBank_wellFormed _ _ (RootPass.window_wellFormed Width16Schedule.firstRow start)
  · exact prepareOuterBank_wellFormed _ _ trivial
  · exact signed_wellFormed d start

theorem win_slots (w : Window 1769472) (hw : IsWin w) (start : Nat) :
    (w.program start).gateSlots ≤ 3000000000 := by
  rcases hw with rfl|rfl|⟨d,rfl⟩
  · change (prepareOuterBank Width16Schedule.headRWires
      (Width16Schedule.firstWindow.program start)).gateSlots ≤ _
    rw [prepareOuterBank_slots]
    have h : (Width16Schedule.firstWindow.program start).gateSlots ≤ 1000000000 :=
      RootPass.window_slots Width16Schedule.firstRow start
    have hl : Width16Schedule.headRWires.length = 8 := Width16Schedule.headR_length
    omega
  · change (prepareOuterBank Width16Schedule.headRWires.reverse
      (Straight.done : Straight 1769472 start start)).gateSlots ≤ _
    rw [prepareOuterBank_slots]
    have hl : Width16Schedule.headRWires.length = 8 := Width16Schedule.headR_length
    simp only [List.length_reverse, hl]
    change 8 + 0 ≤ _
    omega
  · exact signed_slots d start

theorem bits_range : ∀ v ∈ SelectSchedule18.bits, v ∈ List.range 1618 := by decide

theorem win_bank_support (w : Window 1769472) (hw : IsWin w) : w.wires ⊆ List.range 1618 := by
  rcases hw with rfl|rfl|⟨d,rfl⟩
  · intro v hv
    exact bits_range v (Width16Schedule.headL_sub v (List.mem_reverse.mp hv))
  · intro v hv
    exact bits_range v (by
      rw [← Width16Schedule.head_bits]
      exact List.mem_append_left _ (List.mem_reverse.mp hv))
  · cases d with
    | left17 j | right17 j =>
      change (WideSigned.Body.logicalBank .w16).reverse.map TightSupport.compact ⊆ _
      decide
    | left16 j | right16 j => change streamAddress.reverse ⊆ _; decide

theorem win_support (w : Window 1769472) (hw : IsWin w) (start : Nat)
    (read : ConstantBit 1769472→Bool) (history : Fin start→Bool) :
    ((w.program start).instantiate read history).wires ⊆ List.range 1618 := by
  rcases hw with rfl|rfl|⟨d,rfl⟩
  · change ((prepareOuterBank Width16Schedule.headRWires
      (Width16Schedule.firstWindow.program start)).instantiate read history).wires ⊆ _
    apply prepareOuterBank_support
    · intro v hv
      exact bits_range v (Width16Schedule.headR_sub' v hv)
    · exact (straight_instantiate_support _ read history).trans
        ((RootPass.window_support Width16Schedule.firstRow start).trans
          (First18.support_range.trans (List.range_subset.mpr (by decide))))
  · change ((prepareOuterBank Width16Schedule.headRWires.reverse
      (Straight.done : Straight 1769472 start start)).instantiate read history).wires ⊆ _
    apply prepareOuterBank_support
    · intro v hv
      exact bits_range v (Width16Schedule.headR_sub' v (List.mem_reverse.mp hv))
    · intro v hv
      simp [Straight.instantiate, AdaptiveCircuit.wires] at hv
  · apply (straight_instantiate_support _ read history).trans
    exact signed_support d start

theorem program_wellFormed : (Width16Schedule.program impl reset).WellFormed := by
  unfold Width16Schedule.program
  apply framed_wellFormed
  · exact axis_wellFormed ([impl.headA]) (fun w hw start => by
      rcases List.mem_singleton.mp hw with rfl; exact win_wellFormed _ isWin_headA start) _ _
  · unfold mixTail
    apply straight_append_wellFormed
    · exact axis_wellFormed ([impl.headB]) (fun w hw start => by
        rcases List.mem_singleton.mp hw with rfl; exact win_wellFormed _ isWin_headB start) _ _
    · apply straight_append_wellFormed
      · exact axis_wellFormed (Width16Schedule.leftBodies impl) (fun w hw start => win_wellFormed w (isWin_left w hw) start) _ _
      · exact axis_wellFormed (Width16Schedule.rightBodies impl) (fun w hw start => win_wellFormed w (isWin_right w hw) start) _ _
  · exact resetProgram_wellFormed _ _ _

theorem full_wellFormed : rawProgram.WellFormed :=
  straight_append_wellFormed _ _ program_wellFormed (Width16Schedule.readout_wellFormed impl reset)

theorem mix_slots_bound :
    (mixHead impl.headA 0).gateSlots +
      (mixTail impl.headA impl.headB (Width16Schedule.leftBodies impl)
        (Width16Schedule.rightBodies impl) 0).gateSlots ≤ 99998999998 := by
  have hA := axis_slots ([impl.headA]) 3000000000
    (fun w hw start => by rcases List.mem_singleton.mp hw with rfl; exact win_slots _ isWin_headA start)
    0 List.nil
  have hB := axis_slots ([impl.headB]) 3000000000
    (fun w hw start => by rcases List.mem_singleton.mp hw with rfl; exact win_slots _ isWin_headB start)
    (mixS1 impl.headA 0) List.nil
  have hL := axis_slots (Width16Schedule.leftBodies impl) 3000000000
    (fun w hw start => win_slots w (isWin_left w hw) start)
    (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0)
  have hR := axis_slots (Width16Schedule.rightBodies impl) 3000000000
    (fun w hw start => win_slots w (isWin_right w hw) start)
    (mixS3 impl.headA impl.headB (Width16Schedule.leftBodies impl) 0)
    (mixPriorR impl.headA impl.headB (Width16Schedule.leftBodies impl) 0)
  rw [Width16Schedule.mixPriorL_length] at hL
  rw [Width16Schedule.mixPriorR_length] at hR
  simp only [List.length_nil, List.map_cons, List.map_nil, impl.headA_count, impl.headA_width,
    impl.headB_count, impl.headB_width] at hA hB
  rw [Width16Schedule.left_metadata] at hL
  rw [Width16Schedule.right_metadata] at hR
  have hb : metadataSlots 3000000000 ([(132606,10)]) 0 + metadataSlots 3000000000 ([(0,8)]) 0 +
      metadataSlots 3000000000 (Width16Schedule.leftMetadata impl.records17 impl.records16) 10 +
      metadataSlots 3000000000 (Width16Schedule.rightMetadata impl.records17 impl.records16) 8 ≤
      99998999998 := by
    norm_num [Width16Schedule.leftMetadata, Width16Schedule.rightMetadata, metadataSlots, fourierSlots,
      List.replicate]
  rw [mixHead_slots, mixTail_slots]
  omega

theorem full_slots : rawProgram.gateSlots ≤ 100000000000 := by
  have hm := mix_slots_bound
  have hro : (Width16Schedule.readout impl reset).gateSlots = 122311 := by
    unfold Width16Schedule.readout
    rw [castFinish_gateSlots]
    exact Readout56.suffix56_slots _ _ _ _
  unfold rawProgram Width16Schedule.fullProgram Width16Schedule.program
  rw [Straight.gateSlots_append,framed_slots,resetProgram_gateSlots,hro]
  omega

theorem reset_range : reset ⊆ List.range 1618 := by
  intro w hw
  simp only [reset, resetWires, List.mem_append, List.mem_range, List.mem_singleton,
    List.mem_range'_1] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem full_support (read : ConstantBit 1769472→Bool) (history : Fin 0→Bool) :
    (rawProgram.instantiate read history).wires ⊆ List.range 1618 := by
  have hA := axis_support ([impl.headA]) (List.range 1618)
    (fun w hw => by rcases List.mem_singleton.mp hw with rfl; exact win_bank_support _ isWin_headA)
    (fun w hw start r h => by
      rcases List.mem_singleton.mp hw with rfl; exact win_support _ isWin_headA start r h)
    0 List.nil read history
  have hB (h : Fin (mixS1 impl.headA 0)→Bool) := axis_support ([impl.headB]) (List.range 1618)
    (fun w hw => by rcases List.mem_singleton.mp hw with rfl; exact win_bank_support _ isWin_headB)
    (fun w hw start r h' => by
      rcases List.mem_singleton.mp hw with rfl; exact win_support _ isWin_headB start r h')
    (mixS1 impl.headA 0) List.nil read h
  have hL (h : Fin (mixS2 impl.headA impl.headB 0)→Bool) := axis_support (Width16Schedule.leftBodies impl) (List.range 1618)
    (fun w hw => win_bank_support w (isWin_left w hw))
    (fun w hw start r h' => win_support w (isWin_left w hw) start r h')
    (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0) read h
  have hR (h : Fin (mixS3 impl.headA impl.headB (Width16Schedule.leftBodies impl) 0)→Bool) := axis_support (Width16Schedule.rightBodies impl) (List.range 1618)
    (fun w hw => win_bank_support w (isWin_right w hw))
    (fun w hw start r h' => win_support w (isWin_right w hw) start r h')
    (mixS3 impl.headA impl.headB (Width16Schedule.leftBodies impl) 0) (mixPriorR impl.headA impl.headB (Width16Schedule.leftBodies impl) 0) read h
  apply outer_append_support _ _ read history (List.range 1618) ?_ ?_
  · unfold Width16Schedule.program
    refine framed_support _ _ _ _ read history _ (by decide) hA ?_
      (fun h => resetProgram_support _ _ _ _ read h reset_range)
    intro h
    unfold mixTail
    exact outer_append_support _ _ read h (List.range 1618) (hB h)
      (fun h' => outer_append_support _ _ read h' (List.range 1618) (hL h') (fun h'' => hR h''))
  · intro h
    unfold Width16Schedule.readout
    rw [castFinish_instantiate]
    exact (Readout56.suffix56_support _ _ _ _ read h).trans (by decide)

theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n→Fin m)
    (ws : List Wire) (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1,ih hp.2⟩
  | recordGate i v g p ih => exact ⟨hp.1,ih hp.2⟩
  | measure w p ih => exact ⟨hp.1,ih hp.2⟩

theorem source_within : Within (List.range 1618) rawEntry.program := by
  unfold rawEntry Width16Schedule.sourceEntry Single.fixedEntry
  dsimp only
  exact within_reindex rawProgram _ (List.range 1618)
    (within_of_instantiate rawProgram (List.range 1618) full_support)

theorem added_le_weight {n s e} (p : Straight n s e) : 4*added p ≤ weight4 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp only [added,weight4,weightedLiteral] <;> omega
    | whenBit r b g => simp only [added,weight4]; omega
  | recordGate i b g p ih => simp only [added,weight4]; omega
  | measure w p ih => exact ih

theorem source_credit_bound : added rawEntry.program ≤ 62737992 := by
  have h := added_le_weight rawEntry.program
  have hw := Width16Schedule.fullProgram_weight impl reset
  have hc := credits
  have he : weight4 rawEntry.program = weight4 (Width16Schedule.fullProgram impl reset) := by
    unfold rawEntry Width16Schedule.sourceEntry Single.fixedEntry
    dsimp only
    exact weight4_reindex _ _
  rw [he] at h
  change impl.credit17 ≤ _ ∧ impl.credit16 ≤ _ at hc
  omega

theorem source_counts : rawEntry.finalCursor ≤ 50000000 ∧
    rawEntry.finalCursor+added rawEntry.program ≤ 544000000 ∧
    4*(rawEntry.program.gateSlots+18*added rawEntry.program)+2 ≤ officialLimits.gateSlots := by
  have hc := source_credit_bound
  have hs : rawEntry.program.gateSlots ≤ 100000000000 := by
    rw [rawEntry,Width16Schedule.sourceEntry,Single.fixedEntry_slots]
    exact full_slots
  have hm : rawEntry.finalCursor = 46531507 := by
    change 132606+19*1744024+8*1653272+469+resetWires.length+34946=46531507
    decide
  change _ ∧ _ ∧ _ ≤ 4000000000000000
  omega

end
end ShorECDLP.Entrant.Width16Actual

namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule ConditionalCatalyst
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] Single.axis WideBank8.Signed16.program WEXFast.W15G.compactProgram
  ConditionalCatalyst.fourEntry ConditionalCatalyst.compileEntry ConditionalCatalyst.compile
  AndGadget.lowerEntry AndGadget.lowerLayout
attribute [local instance] bodyInstance resourceInstance

theorem primitive_t_bound (g : Gate) : tCost g ≤ 7 := by cases g <;> simp only [tCost] <;> norm_num

theorem straight_t_bound {n s e} (p : Straight n s e) (read : ConstantBit n→Bool) (history : Fin s→Bool) :
    (p.instantiate read history).tCount ≤ 7*p.gateSlots := by
  induction p with
  | done => simp [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
  | gate g p ih =>
    cases g with
    | literal g =>
      have hg := primitive_t_bound g
      simpa only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
        ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
        Straight.gateSlots,Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
    | whenBit r v g =>
      have hg := primitive_t_bound g
      simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
        Straight.gateSlots]
      split
      · simpa only [ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
          Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
      · simpa only [ShorECDLP.tCount,List.map_nil,List.sum_nil,Nat.zero_add] using
          (ih history).trans (by omega)
  | recordGate i v g p ih =>
    have hg := primitive_t_bound g
    simp only [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
    split
    · simpa only [ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
        Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
    · simpa only [ShorECDLP.tCount,List.map_nil,List.sum_nil,Nat.zero_add] using
        (ih history).trans (by omega)
  | measure w p ih =>
    simp only [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
    exact max_le (ih _) (ih _)

theorem strong_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d•G) :
    (990038025/1000000000:ℝ) ≤ Instrument.bornMass
      ((rawEntry.instantiate Q).run.filter (fun b => (verifiedCandidate rawLayout Q b.history).isSome))
      (ket zeroBasisState) := by
  have hQ : order•Q=0 := by rw [hd,smul_comm order d,generator_nsmul_eq_zero,nsmul_zero]
  rw [rawEntry,sourceEntry,Single.fixedEntry_instantiate]
  exact Width16Readout.strong_success implementation Q d hd hQ (models Q hQ hn)
    (Width16Schedule.hfirst_concrete Q hQ hn initialRoot initialRoot_input initialRoot_clean)
    (fun w _ => signed_rule Q hQ hn w) (ready_models Q hQ hn)

def rawBounds : Bounds := ⟨1618,700000000000,50000000⟩

theorem raw_certificate : Certificate rawLimits rawLayout rawEntry rawBounds where
  gateBudget := by
    rw [rawEntry,sourceEntry,Single.fixedEntry_slots]
    exact full_slots.trans (by decide)
  recordBudget := source_counts.1.trans (by decide)
  tableBudget := by
    rw [rawEntry,sourceEntry,Single.fixedEntry_rows]
    decide
  candidateBudget := by
    change 56*(2*(order/2^208+2))≤56*(2^49+2)
    exact SinAverage261.decoder_budget261
  wellFormed := by
    rw [rawEntry,sourceEntry,Single.fixedEntry_wellFormed]
    exact full_wellFormed
  resources := by
    intro Q
    have hs := source_within.instantiate (readConstant rawEntry.coefficients.get Q) Fin.elim0
    have hq : (rawEntry.instantiate Q).qubitCount ≤ 1618 := by
      have ht : (rawEntry.instantiate Q).wires.dedup.toFinset ⊆ (List.range 1618).toFinset := by
        intro v hv
        exact List.mem_toFinset.mpr (hs (by simpa only [List.mem_toFinset,List.mem_dedup] using hv))
      have hc := (Finset.card_le_card ht).trans (List.toFinset_card_le _)
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc
    refine ⟨hq,?_,?_⟩
    · have ht := straight_t_bound rawEntry.program (readConstant rawEntry.coefficients.get Q) Fin.elim0
      have hb : rawEntry.program.gateSlots≤100000000000 := by
        rw [rawEntry,sourceEntry,Single.fixedEntry_slots]
        exact full_slots
      exact ht.trans (by change _≤700000000000;omega)
    · have hm := source_counts.1
      change (rawEntry.program.instantiate _ _).measurementCount≤50000000
      rw [Straight.measurementCount]
      omega
  success := by
    intro Q d hn hd
    exact (by norm_num : (99/100:ℝ)≤990038025/1000000000).trans (strong_success Q d hn hd)

def entry : StraightEntry := Width16Schedule.finalEntry implementation reset

def layout : DecodeLayout :=
  lowerLayout 1938 (trimNEntry rawEntry) rawLayout

def bounds : Bounds := ⟨1620,250907747,544000000⟩

theorem hcert : Certificate officialLimits
      (lowerLayout 1938 (trimNEntry (Width16Schedule.sourceEntry implementation reset))
        (Width16Schedule.layout implementation reset))
      (Width16Schedule.finalEntry implementation reset)
      ⟨1620,4*(132595+19*implementation.credit17+8*implementation.credit16)+10767,544000000⟩ :=
  Width16Schedule.conditional_certificate implementation reset (List.range 1618)
    rawBounds 1620 raw_certificate source_within strong_success (by decide) (by decide)
    source_counts.2.2 (source_counts.2.1.trans (by decide)) (by decide) source_counts.2.1

theorem tmodel_key : ∀ a b : Nat, a ≤ 2343187 → b ≤ 2252440 → 4*(132595+19*a+8*b)+10767 ≤ 250907747 := by
  intro a b ha hb
  omega

theorem tmodel_of {lim : Limits} {lay : DecodeLayout} {e : StraightEntry} {q t m : Nat}
    (h : Certificate lim lay e ⟨q,t,m⟩) (Q : Point) : (resources (e.instantiate Q)).tModel ≤ t :=
  (h.resources Q).2.1

theorem hres (Q : Point) : (resources (entry.instantiate Q)).qubits ≤ bounds.qubits ∧
    (resources (entry.instantiate Q)).tModel ≤ bounds.tModel ∧
    (resources (entry.instantiate Q)).measurements ≤ bounds.measurements :=
  ⟨(hcert.resources Q).1, (tmodel_of hcert Q).trans (tmodel_key _ _ credits.1 credits.2),
    (hcert.resources Q).2.2⟩

theorem certificate : Certificate officialLimits layout entry bounds :=
  Certificate.mk hcert.gateBudget hcert.recordBudget hcert.tableBudget hcert.candidateBudget
    hcert.wellFormed hres hcert.success

#print axioms certificate
end
end ShorECDLP.Entrant.Width16Actual
