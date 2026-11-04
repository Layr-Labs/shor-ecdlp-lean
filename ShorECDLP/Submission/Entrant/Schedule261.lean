import ShorECDLP.Submission.Entrant.PathBody
import ShorECDLP.Submission.Entrant.SinAverage261
import ShorECDLP.Submission.Entrant.Readout56

/-! The 17-bit first load followed by four physical-15 and twelve physical-14 left digits
(261 left bits) and thirteen physical-15 right digits (208 right bits), read with 56
neighbouring right words (`Readout56.suffix56`). The success argument is the averaged bound
`SinAverage261.pair_success261`. -/

section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
namespace ShorECDLP.Entrant.Schedule29Seventeen244
open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-! Twenty-nine corrected additions after a 17-bit first load: seven physical-15 and nine
physical-14 left digits, then thirteen physical-15 right digits. -/
inductive Digit where
  | left16 (index : Fin 4)
  | left15 (index : Fin 12)
  | right16 (index : Fin 13)

def Digit.width : Digit → Nat
  | .left16 _ | .right16 _ => 16
  | .left15 _ => 15

def Digit.exponent : Digit → Nat
  | .left16 j => 228 - 16 * j.val
  | .left15 j => 165 - 15 * j.val
  | .right16 j => 192 - 16 * j.val

def firstRow (a : Fin 131072) : Fin 884736 := ⟨a.val, by omega⟩

def row : (w : Digit) → Fin (2^(w.width-1)) → Fin 884736
  | .left16 j, a => ⟨131072 + j.val*32768 + a.val, by
    have h : a.val < 32768 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .left15 j, a => ⟨262144 + j.val*16384 + a.val, by
    have h : a.val < 16384 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .right16 j, a => ⟨458752 + j.val*32768 + a.val, by
    have h : a.val < 32768 := by simpa only [Digit.width] using a.isLt
    omega⟩

theorem width_cases (w : Digit) : w.width = 14 ∨ w.width = 15 ∨ w.width = 16 := by
  cases w <;> simp [Digit.width]

def leftDigits : List Digit := List.ofFn (fun j : Fin 4 => .left16 j) ++
  List.ofFn (fun j : Fin 12 => .left15 j)
def rightDigits : List Digit := List.ofFn (fun j : Fin 13 => .right16 j)

theorem left_widths : leftDigits.map Digit.width =
    List.replicate 4 16 ++ List.replicate 12 15 := by
  simp [leftDigits, List.ofFn_succ, Digit.width, List.replicate]
theorem right_widths : rightDigits.map Digit.width = List.replicate 13 16 := by
  simp [rightDigits, List.ofFn_succ, Digit.width, List.replicate]

def leftOffset : Nat := (leftDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum
def rightOffset : Nat := (rightDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum

def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients (v * 2^244 + leftOffset) rightOffset

def signedCoefficients (w : Digit) (a : Nat) : PointCoeff :=
  match w with
  | .left16 _ | .left15 _ => coefficients (Single.oddScalar w.exponent a) 0
  | .right16 _ => coefficients 0 (Single.oddScalar w.exponent a)

def coefficientAt (i : Fin 884736) : PointCoeff :=
  if i.val < 131072 then initialCoefficients i.val
  else if i.val < 262144 then
    coefficients (Single.oddScalar (228 - 16 * ((i.val - 131072) / 32768)) ((i.val - 131072) % 32768)) 0
  else if i.val < 458752 then
    coefficients (Single.oddScalar (165 - 15 * ((i.val - 262144) / 16384)) ((i.val - 262144) % 16384)) 0
  else coefficients 0 (Single.oddScalar (192 - 16 * ((i.val - 458752) / 32768)) ((i.val - 458752) % 32768))

theorem coefficientAt_first (a : Fin 131072) :
    coefficientAt (firstRow a) = initialCoefficients a.val := by
  simp [coefficientAt, firstRow, a.isLt]

theorem coefficientAt_row (w : Digit) (a : Fin (2^(w.width-1))) :
    coefficientAt (row w a) = signedCoefficients w a.val := by
  cases w with
  | left16 j =>
    have ha : a.val < 32768 := by
      simpa only [Digit.width] using a.isLt
    have he : (row (.left16 j) a).val < 262144 := by simp only [row]; omega
    have hbase : ¬ (row (.left16 j) a).val < 131072 := by simp only [row]; omega
    have hj : ((row (.left16 j) a).val - 131072) / 32768 = j.val := by simp only [row]; omega
    have hh : ((row (.left16 j) a).val - 131072) % 32768 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, he, hj, hh, signedCoefficients, Digit.exponent]
  | left15 j =>
    have ha : a.val < 16384 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.left15 j) a).val < 131072 := by simp only [row]; omega
    have he : (row (.left15 j) a).val < 458752 := by simp only [row]; omega
    have hbase : ¬ (row (.left15 j) a).val < 262144 := by simp only [row]; omega
    have hj : ((row (.left15 j) a).val - 262144) / 16384 = j.val := by simp only [row]; omega
    have hh : ((row (.left15 j) a).val - 262144) % 16384 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, he, hj, hh, signedCoefficients, Digit.exponent]
  | right16 j =>
    have ha : a.val < 32768 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.right16 j) a).val < 131072 := by simp only [row]; omega
    have hn1 : ¬ (row (.right16 j) a).val < 262144 := by simp only [row]; omega
    have hbase : ¬ (row (.right16 j) a).val < 458752 := by simp only [row]; omega
    have hj : ((row (.right16 j) a).val - 458752) / 32768 = j.val := by simp only [row]; omega
    have hh : ((row (.right16 j) a).val - 458752) % 32768 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, hn1, hj, hh, signedCoefficients, Digit.exponent]

end ShorECDLP.Entrant.Schedule29Seventeen244




namespace ShorECDLP.Entrant.Schedule29Seventeen244
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def initialPoint (Q : Point) (v : Nat) : Point :=
  (v * 2^244 + leftOffset) • G + rightOffset • Q

theorem initialCoefficients_point (Q : Point) (hQ : order • Q = 0) (v : Nat) :
    constantPoint Q (initialCoefficients v) = initialPoint Q v := by
  unfold initialCoefficients initialPoint
  exact coefficients_point _ _ Q hQ

def firstWindow : Single.Window 884736 := ScheduleFirst17.windowGeneric firstRow

theorem firstWindow_law : WindowLaw coefficientAt firstWindow
    (ScheduleFirst17.update initialPoint) ScheduleFirst17.Input := by
  apply ScheduleFirst17.window_law_generic
  intro Q hQ a
  rw [coefficientAt_first]
  exact initialCoefficients_point Q hQ a.val

end
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def Digit.base (Q : Point) : Digit → Point
  | .left16 _ | .left15 _ => G
  | .right16 _ => Q

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
    | left16 _ | left15 _ => exact G_ne_zero
    | right16 _ => exact hn
  have hr : order • P = 0 := by
    cases w with
    | left16 _ | left15 _ => exact generator_nsmul_eq_zero
    | right16 _ => exact hQ
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


noncomputable def increment (P : Point) (width exponent v : Nat) : Point :=
  ((2 * (v : Int) - (2 : Int)^width + 1) : Int) •
    ((Single.halfOrder * 2^exponent) • P)

theorem increment_offset (P : Point) (hr : order • P = 0)
    (width exponent v : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) :
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
    rcases hw with rfl | rfl | rfl <;> norm_num
  have hcalc : ((2*(v:Int)-(2:Int)^width+1) • H) +
      (2^(width-1) • (H+H) - H) = v • (H+H) := by
    rw [hp]
    module
  change ((2*(v:Int)-(2:Int)^width+1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2^exponent) P).symm


open Quantum ShorECDLP.Paper2607_13816

def logicalValue14 (low : Nat) (sign : Bool) : Nat := low + 8192 * sign.toNat
def logicalValue15 (low : Nat) (sign : Bool) : Nat := low + 16384 * sign.toNat
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



theorem padded_address15 (low : Nat) (sign : Bool) (hlow : low < 16384) :
    signedTableAddress 32768 (Single.paddedValue low sign) % 16384 =
      signedTableAddress 16384 (logicalValue15 low sign) := by
  cases sign with
  | false =>
    have hbig : low < 32768 := by omega
    have hsub : 32767 - low = 16384 + (16383 - low) := by omega
    have hrem : 16383 - low < 16384 := by omega
    simp only [Single.paddedValue, logicalValue15, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      signedTableAddress, if_pos hbig, if_pos hlow]
    rw [hsub, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hrem]
  | true =>
    have hbig : ¬ low + 32768 < 32768 := by omega
    have hsmall : ¬ low + 16384 < 16384 := by omega
    simp only [Single.paddedValue, logicalValue15, Bool.toNat_true, Nat.mul_one,
      signedTableAddress, if_neg hbig, if_neg hsmall]
    have h1 : low + 32768 - 32768 = low := by omega
    have h2 : low + 16384 - 16384 = low := by omega
    rw [h1, h2, Nat.mod_eq_of_lt hlow]

def logicalValue16 (low : Nat) (sign : Bool) : Nat := low + 32768 * sign.toNat

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

theorem bank_length (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) :
    (bank width).length = width := by
  rcases hw with rfl | rfl | rfl <;> simp [bank]

theorem digit14_low (s : BasisState) :
    digit 14 s = logicalValue14 (tableAddressValue (List.range' 855 13) s) (s 870) := by
  change tableAddressValue (List.range' 855 13 ++ [870]) s =
    tableAddressValue (List.range' 855 13) s + 8192 * (s 870).toNat
  rw [address_append]
  simp [tableAddressValue]

theorem digit15_low (s : BasisState) :
    digit 15 s = logicalValue15 (tableAddressValue (List.range' 855 14) s) (s 870) := by
  change tableAddressValue (List.range' 855 14 ++ [870]) s =
    tableAddressValue (List.range' 855 14) s + 16384 * (s 870).toNat
  rw [address_append]
  simp [tableAddressValue]

theorem digit16_low (s : BasisState) :
    digit 16 s = logicalValue16 (tableAddressValue (List.range' 855 15) s) (s 870) := by
  change tableAddressValue (List.range' 855 15 ++ [870]) s =
    tableAddressValue (List.range' 855 15) s + 32768 * (s 870).toNat
  rw [address_append]
  simp [tableAddressValue]

theorem physical_padding14 (s : BasisState) (h868 : s 868 = false) (h869 : s 869 = false) :
    windowRawDigit 0 s = Single.paddedValue (tableAddressValue (List.range' 855 13) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, Single.paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat, h868, h869]

theorem physical_padding15 (s : BasisState) (h869 : s 869 = false) :
    windowRawDigit 0 s = Single.paddedValue (tableAddressValue (List.range' 855 14) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, Single.paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat, h869]

theorem physical_padding16 (s : BasisState) :
    windowRawDigit 0 s = Single.paddedValue (tableAddressValue (List.range' 855 15) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, Single.paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat]

theorem digit16_raw (s : BasisState) : digit 16 s = windowRawDigit 0 s := by
  rw [digit16_low, physical_padding16]
  rfl

theorem bank_nodup (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) : (bank width).Nodup := by
  rcases hw with rfl | rfl | rfl <;> decide +kernel

theorem bank_subset (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) :
    ∀ v ∈ bank width, v ∈ streamAddress := by
  rcases hw with rfl | rfl | rfl <;> decide +kernel

theorem bank_not_point (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) :
    ∀ v ∈ bank width, v ∉ pointLogicalWires := by
  intro v hv
  exact (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v
    (bank_subset width hw v hv)

theorem digit_low_sign (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) (s : BasisState) :
    digit width s < 2^(width-1) ↔ s 870 = false := by
  rcases hw with rfl | rfl | rfl
  · rw [digit14_low]
    have hb := tableAddressValue_lt (List.range' 855 13) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue14]
  · rw [digit15_low]
    have hb := tableAddressValue_lt (List.range' 855 14) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue15]
  · rw [digit16_low]
    have hb := tableAddressValue_lt (List.range' 855 15) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue16]

theorem selected_address_alias (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) (s : BasisState)
    (h869 : width ≠ 16 → s 869 = false) (h868 : width = 14 → s 868 = false) :
    signedTableAddress 32768 (windowRawDigit 0 s) % 2^(width-1) =
      signedTableAddress (2^(width-1)) (digit width s) := by
  rcases hw with rfl | rfl | rfl
  · rw [physical_padding14 s (h868 rfl) (h869 (by decide)), digit14_low]
    exact padded_address14 _ _ (by simpa using tableAddressValue_lt (List.range' 855 13) s)
  · rw [physical_padding15 s (h869 (by decide)), digit15_low]
    exact padded_address15 _ _ (by simpa using tableAddressValue_lt (List.range' 855 14) s)
  · rw [digit16_raw, show (2 : Nat)^(16-1) = 32768 by norm_num]
    exact Nat.mod_eq_of_lt (signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s))

theorem selected_increment (Q : Point) (w : Digit) (s : BasisState)
    (h869 : w.width ≠ 16 → s 869 = false) (h868 : w.width = 14 → s 868 = false) :
    (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))) =
      increment (w.base Q) w.width w.exponent (digit w.width s) := by
  have hpow : (2 : Int)^w.width = 2 * (2^(w.width-1) : Nat) := by
    rcases width_cases w with hw | hw | hw <;> rw [hw] <;> norm_num
  have hs : (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))) =
      signedTableOdd (2^(w.width-1)) (digit w.width s) •
        ((Single.halfOrder * 2^w.exponent) • w.base Q) := by
    simp only [positivePoint, selected_address_alias w.width (width_cases w) s h869 h868,
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

def paddedRow (w : Digit) (a : Fin 32768) : Fin 884736 :=
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
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
variable [b : Single.WindowBody]

def WindowValid (w : Digit) (s : BasisState) : Prop :=
  Single.BodyValid b s ∧ (w.width ≠ 16 → s 869 = false) ∧ (w.width = 14 → s 868 = false)

def signedWindow (w : Digit) : Single.Window 884736 :=
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
  rw [he, selected_increment Q w s hs.2.1 hs.2.2]

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


theorem signedWindow_wellFormed (w : Digit) (start : Nat) :
    ((signedWindow w).program start).WellFormed := by
  unfold signedWindow
  exact (reindexStraight_wellFormed (paddedRow w) (b.program start)).mpr (b.wellFormed start)

theorem signedWindow_slots (w : Digit) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ b.slotBound := by
  unfold signedWindow
  rw [reindexStraight_gateSlots]
  exact b.slots start


end

end
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

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


theorem left_base (Q : Point) (w : Digit) (hw : w ∈ leftDigits) : w.base Q = G := by
  simp only [leftDigits, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem right_base (Q : Point) (w : Digit) (hw : w ∈ rightDigits) : w.base Q = Q := by
  simp only [rightDigits, List.mem_ofFn] at hw
  obtain ⟨i, rfl⟩ := hw
  rfl

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
    have hwidths : ((leftDigits.map f).map (fun w => w.physical.wires.length)).sum = 244 := by
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


section
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

end

end
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
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
omit b in
theorem bank_padding869 (w : Digit) (hw : w.width ≠ 16) : 869 ∉ bank w.width := by
  rcases width_cases w with h | h | h
  · rw [h]; decide +kernel
  · rw [h]; decide +kernel
  · exact absurd h hw

omit b in
theorem bank_padding868 (w : Digit) (hw : w.width = 14) : 868 ∉ bank w.width := by
  rw [hw]
  decide +kernel

omit b in
theorem bank_clean (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16)
    (s : BasisState) (hz : Clean streamAddress s) : Clean (bank width) s :=
  fun v hv => hz v (bank_subset width hw v hv)

omit b in
theorem point_bank_clean (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16)
    (P : Point) (s : BasisState) (hz : Clean streamAddress s) :
    Clean (bank width) (pointWrite P s) := by
  intro v hv
  simpa only [pointWrite_frame P s v (bank_not_point width hw v hv)] using
    bank_clean width hw s hz v hv

theorem assigned_valid (w : Digit) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) (input : List Bool) :
    WindowValid w (phaseWordState (bank w.width) input (pointWrite P s)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact phaseWordState_preserves (Single.BodyValid b) (bank w.width)
      (fun t ht v hv bit => Single.bodyValid_address t ht v
        (bank_subset w.width (width_cases w) v hv) bit) input _ (Single.bodyValid_first s hs P)
  · intro hw16
    rw [phaseWordState_frame _ _ _ 869 (bank_padding869 w hw16),
      pointWrite_frame P s 869 (by decide +kernel)]
    exact hz 869 (by decide +kernel)
  · intro hw
    rw [phaseWordState_frame _ _ _ 868 (bank_padding868 w hw),
      pointWrite_frame P s 868 (by decide +kernel)]
    exact hz 868 (by decide +kernel)

omit b in
theorem assigned_coordinates (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16)
    (P : Point) (s : BasisState) (input : List Bool) :
    pointStateCoordinates (phaseWordState (bank width) input (pointWrite P s)) =
      fig14PointEncoding P := by
  rw [phaseWordState_pointWrite _ (bank_not_point width hw), pointWrite_coordinates]

omit b in
theorem assigned_digit (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16)
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
end

end
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
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

def firstModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : WindowModel (readConstant coefficientAt Q) where
  physical := firstWindow
  point := initialPoint Q
  bias := -(leftOffset • G + rightOffset • Q)
  ideal := Finsupp.lmapDomain ℂ ℂ (ScheduleFirst17.update initialPoint Q)
  valid := ScheduleFirst17.Input
  nodup := by change ScheduleFirst17.bits.reverse.Nodup; exact List.nodup_reverse.mpr Single.first17_nodup
  coherent := by
    intro start history
    exact firstWindow_law Q hQ hn start history

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

omit b ledger in
theorem firstModel_step (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (prior bits : List Bool) (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (firstModel Q hQ hn).step prior bits (ket root) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 17) •
        ((fourierOutcomes 17).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (initialPoint Q (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.reverse_reverse, LinearMap.comp_apply]
  exact Single.first17_window_point_sum_generic initialPoint Q prior bits root hs hz

omit ledger in
theorem signedModel_pointRule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (signedModel Q hQ hn w) := by
  intro prior bits P
  simpa only [signedModel, signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)] using
    signedModel_step Q hQ hn w prior bits P root hs hz

omit b ledger in
theorem firstModel_firstRule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    FirstRule root (ket root) (firstModel Q hQ hn) := by
  intro prior bits
  have hlen : ScheduleFirst17.bits.length = 17 := by decide +kernel
  simpa only [firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.length_reverse, hlen] using
    firstModel_step Q hQ hn prior bits root hs hz


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

omit ledger in
theorem ready_first_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready (firstModel Q hQ hn :: ws.map (signedModel Q hQ hn)) (ket root) := by
  constructor
  · simp only [firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.reverse_reverse]
    exact ScheduleFirst17.input_prepare _ (fun _ h => h) _
      (supportedOn_ket _ _ (ScheduleFirst17.input_of_strong root hs))
  · intro prior bits
    apply ready_signed Q hQ hn ws root hs hz
    rw [firstModel_step Q hQ hn prior bits root hs hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

end
end ShorECDLP.Entrant.Schedule29Seventeen244

namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes

def count (c14 c15 c16 : Nat) (w : Digit) : Nat :=
  if w.width = 14 then c14 else if w.width = 15 then c15 else c16

class Programs (body : Single.WindowBody) where
  records14 : Nat
  records15 : Nat
  records16 : Nat
  cost14 : Nat
  cost15 : Nat
  cost16 : Nat
  program : (w : Digit) → (start : Nat) → Straight 884736 start
    (start + count records14 records15 records16 w)
  coherent : ∀ Q, order • Q = 0 → Q ≠ 0 → ∀ w start history,
    CoherentlyImplementsOn ((program w start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w)
  wellFormed : ∀ w start, (program w start).WellFormed
  slots : ∀ w start, (program w start).gateSlots ≤ body.slotBound
  wires : ∀ w start, straightWires (program w start) ⊆ body.support
  tCount : ∀ Q w start history,
    ((program w start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count cost14 cost15 cost16 w

variable [impl : Programs b]

def signedWindow (w : Digit) : Single.Window 884736 :=
  ⟨(bank w.width).reverse, count impl.records14 impl.records15 impl.records16 w, impl.program w⟩

def signedModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit) :
    WindowModel (readConstant coefficientAt Q) where
  physical := signedWindow w
  point := increment (w.base Q) w.width w.exponent
  bias := Single.offsetScalar w.width w.exponent • w.base Q
  ideal := Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)
  valid := WindowValid w
  nodup := by rw [signedWindow]; exact List.nodup_reverse.mpr (bank_nodup w.width (width_cases w))
  coherent := impl.coherent Q hQ hn w

omit ledger in
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

omit ledger in
theorem signedModel_pointRule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (signedModel Q hQ hn w) := by
  intro prior bits P
  simpa only [signedModel, signedWindow, List.length_reverse, bank_length _ (width_cases w)] using
    signedModel_step Q hQ hn w prior bits P root hs hz

omit ledger in
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

omit ledger in
theorem ready_first_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready (firstModel Q hQ hn :: ws.map (signedModel Q hQ hn)) (ket root) := by
  constructor
  · simp only [firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.reverse_reverse]
    exact ScheduleFirst17.input_prepare _ (fun _ h => h) _
      (supportedOn_ket _ _ (ScheduleFirst17.input_of_strong root hs))
  · intro prior bits
    apply ready_signed Q hQ hn ws root hs hz
    rw [firstModel_step Q hQ hn prior bits root hs hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit ledger in
theorem concrete_ready (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready ((firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)) ++
      rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  rw [List.cons_append, ← List.map_append]
  exact ready_first_signed Q hQ hn (leftDigits ++ rightDigits) root hs hz

theorem concrete_kernel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    KernelLaw Q root (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  apply model_kernel Q hQ root (ket root) (firstModel Q hQ hn) (signedModel Q hQ hn)
  · intro w
    simp only [signedModel, signedWindow, List.length_reverse, bank_length _ (width_cases w)]
  · intro w v
    rfl
  · intro w
    rfl
  · intro v
    rfl
  · rfl
  · exact firstModel_firstRule Q hQ hn root hs hz
  · intro w _
    exact signedModel_pointRule Q hQ hn w root hs hz

omit ledger in
theorem left_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)) = 261 := by
  rw [precision, List.map_cons, List.sum_cons]
  have hlen : ScheduleFirst17.bits.length = 17 := by decide +kernel
  simp only [firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.length_reverse, hlen,
    List.map_map, Function.comp_def, signedModel, signedWindow,
    bank_length _ (width_cases _), left_widths]
  norm_num [List.replicate]

omit ledger in
theorem right_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (rightDigits.map (signedModel Q hQ hn)) = 208 := by
  rw [precision]
  simp only [List.map_map, Function.comp_def, signedModel, signedWindow,
    List.length_reverse, bank_length _ (width_cases _), right_widths]
  norm_num [List.replicate]
end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem concrete_event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (start : Nat) (history : Fin start → Bool) (J : Instrument)
    (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedTwoAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) start history (fun lhs rhs =>
        if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass (ket root) =
      idealEventMass Q root 261 208 accept := by
  rw [physicalTwoAxes_event_mass Q root _ _ start history _
    (concrete_ready Q hQ hn root hs hz) (concrete_kernel Q hQ hn root hs hz) J hJ accept,
    left_precision Q hQ hn, right_precision Q hQ hn]

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible



namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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

def leftWindows : List (Single.Window 884736) := firstWindow :: leftDigits.map signedWindow

def rightWindows : List (Single.Window 884736) := rightDigits.map signedWindow

def leftMetadata : List (Nat × Nat) :=
  (131071, 17) :: List.replicate 4 (impl.records16, 16) ++ List.replicate 12 (impl.records15, 15)

def rightMetadata : List (Nat × Nat) :=
  List.replicate 13 (impl.records16, 16)

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftDigits, signedWindow,
    Digit.width, count, bank, firstWindow, ScheduleFirst17.windowGeneric, ScheduleFirst17.bits, leftMetadata, List.ofFn_succ, List.replicate]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightDigits, signedWindow,
    Digit.width, count, bank, rightMetadata, List.ofFn_succ, List.replicate]

theorem left_record_count : recordCount leftMetadata = 131071 + 4 * impl.records16 + 12 * impl.records15 + 261 := by
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_record_count : recordCount rightMetadata = 13 * impl.records16 + 208 := by
  simp [rightMetadata, recordCount, List.replicate]
  omega

variable [ledger : Single.ProducerResources body]

theorem left_count : axisCount leftWindows = 131071 + 4 * impl.records16 + 12 * impl.records15 + 261 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 13 * impl.records16 + 208 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

def resetBody (start : Nat) : Straight 884736 start (start + body.reset.length) :=
  resetProgram 884736 start body.reset

omit ledger impl in
theorem resetBody_run (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).run =
      (measureResetWithCorrection body.reset (fun _ => [])).run := by
  unfold resetBody
  rw [resetProgram_run]

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + body.reset.length

theorem trialCount_eq : trialCount = 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length := by
  rw [trialCount, left_count, right_count]
  omega

def trial (start : Nat) : Straight 884736 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

def program : Straight 884736 0 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end
end


section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 261 := by
  rw [positions_length]
  simp [leftMetadata, List.replicate]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length]
  simp [rightMetadata, List.replicate]

def trialPositions : TrialPositions SinAverage261.params261 where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, SinAverage261.params261] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (131071 + 4 * impl.records16 + 12 * impl.records15 + 261)).toArray, by
    simpa only [List.size_toArray, SinAverage261.params261] using right_positions_length (131071 + 4 * impl.records16 + 12 * impl.records15 + 261)⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 131071 + 4 * impl.records16 + 12 * impl.records15 + 261 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (131071 + 4 * impl.records16 + 12 * impl.records15 + 261) ≤ i ∧ i < 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 := by
  have h := positions_bounds rightMetadata (131071 + 4 * impl.records16 + 12 * impl.records15 + 261) i
    (show i ∈ positions rightMetadata (131071 + 4 * impl.records16 + 12 * impl.records15 + 261) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

def finePositions : List (Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length)) :=
  trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(right_position_bound i.val i.property).2.trans_le (by omega)⟩

theorem finePositions_length : finePositions.length = 208 := by
  simp [finePositions, SinAverage261.params261]

def fineBits : Vector (Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length)) 208 :=
  Vector.ofFn fun i=> finePositions[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout : Straight 884736 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length)
    (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946) :=
  castFinish (by omega) (Readout56.suffix56 884736
    (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits)

def fullProgram : Straight 884736 0 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946) :=
  program.append readout

def positionsFor (ps : Vector Nat 208) : TrialPositions SinAverage261.params261 where
  left := trialPositions.left
  right := ps

def layout : DecodeLayout := ⟨.wrappedShift, SinAverage261.params261,
  (Readout56.rightWords56 fineBits).map positionsFor, by
    simp only [List.length_map, Readout56.rightWords56_length]; decide⟩

theorem readout_wellFormed : readout.WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact Readout56.suffix56_wellFormed 884736 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits

theorem readout_t (read : ConstantBit 884736 → Bool)
    (h : Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) → Bool) :
    (readout.instantiate read h).tCount = 0 := by
  unfold readout
  rw [castFinish_instantiate]
  exact Readout56.suffix56_t 884736 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits read h

end
end

end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] Single.axis resetProgram

omit ledger in
theorem concrete_model_left (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)).map WindowModel.physical = leftWindows := by
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
      (((physicalAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq J).filter
        (fun b => fineEvent accept b.history)) (ket root) =
      idealEventMass Q root 261 208 accept := by
  have hm := concrete_event_mass Q hQ hn root hs hz 0 Fin.elim0 J hJ accept
  rw [selectedTwoAxes_fixed_filter, concrete_model_left Q hQ hn, concrete_model_right Q hQ hn,
    left_count, left_positions, right_positions] at hm
  simpa only [fineEvent, trialPositions, Vector.toList_mk, List.toList_toArray] using hm

theorem program_run_data (read : ConstantBit 884736 → Bool) :
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
      ((physicalAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
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
      idealEventMass Q initialRoot 261 208 accept := by
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
        (fun b => fineEvent (SinAverage261.pairRecovered261 d) b.history)) (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by
    rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [program_event_mass Q hn hQ, idealEventMass_distribution Q d hd]
  exact SinAverage261.pair_success261 Q d hn hd

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution RoundedReadout
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem fineBits_vals : fineBits.map Fin.val=trialPositions.right := by
  apply Vector.ext
  intro i hi
  simp [fineBits,finePositions]
  rfl

theorem program_clean (read : ConstantBit 884736 → Bool) (b : InstrumentBranch)
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

theorem verified_of_reads (ps : Vector Nat 208) (hps : ps∈Readout56.rightWords56 fineBits)
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist trialPositions.left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d : ZMod order)∈fixedCandidates SinAverage261.params261 a b) :
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
    (read : ConstantBit 884736→Bool) (history : Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length)→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : fineEvent (SinAverage261.pairRecovered261 d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈(readout.instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate layout Q (List.ofFn history++b.history)).isSome := by
  have hr:=NeighborReadout.input_read fineBits history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩:=Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩:=of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩:=Readout56.suffix56_reads 884736 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) fineBits
    read history ψ hψ b (by simpa only [readout, castFinish_instantiate] using hb) hn ((i.val : ℤ)-28) (by have h:=i.isLt;omega)
  apply verified_of_reads ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h:=left_position_bound j hj
    simpa only [List.length_ofFn] using h.trans (by omega : (131071 + 4 * impl.records16 + 12 * impl.records15 + 261)<(131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length))

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
    have hlen : a.history.length = (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) := by
      have h := straight_history_length program (readConstant coefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant coefficientAt Q)
      (Single.historyAfter (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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

def triPrograms (n14 : ModNarrow body 13) (n15 : ModNarrow body 14) (n16 : ModNarrow body 15) :
    Programs body where
  records14 := n14.records
  records15 := n15.records
  records16 := n16.records
  cost14 := n14.tBound
  cost15 := n15.tBound
  cost16 := n16.tBound
  program := fun w start =>
    if h14 : w.width = 14 then
      castFinish (by simp [count,h14]) (reindexStraight (paddedRow w) (n14.program start))
    else if h15 : w.width = 15 then
      castFinish (by simp [count,h15]) (reindexStraight (paddedRow w) (n15.program start))
    else castFinish (by simp [count,h14,h15]) (reindexStraight (paddedRow w) (n16.program start))
  coherent := by
    intro Q hQ hn w start history
    have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
      intro a
      have he := window_table_point Q hQ w a.val
      simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
      rw [he]
      exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
    by_cases h14 : w.width = 14
    · have ha : ModAliased 13 (windowCoefficients w) := by
        simpa only [h14, Nat.reduceSub] using coefficients_aliased w
      have h := n14.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_pos h14, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
    by_cases h15 : w.width = 15
    · have ha : ModAliased 14 (windowCoefficients w) := by
        simpa only [h15, Nat.reduceSub] using coefficients_aliased w
      have h := n15.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_neg h14, dif_pos h15, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
    have h16 : w.width = 16 := ((width_cases w).resolve_left h14).resolve_left h15
    have ha : ModAliased 15 (windowCoefficients w) := by
      simpa only [h16, Nat.reduceSub] using coefficients_aliased w
    have h := n16.coherent (windowCoefficients w) Q hQ htable ha start history
    rw [dif_neg h14, dif_neg h15, castFinish_instantiate, reindexStraight_instantiate,
      readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
    obtain ⟨cs, hc, hm⟩ := h
    exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
  wellFormed := by
    intro w start
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n14.wellFormed start)
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n15.wellFormed start)
    rw [dif_neg h14, dif_neg h15, castFinish_wellFormed]
    exact (reindexStraight_wellFormed _ _).mpr (n16.wellFormed start)
  slots := by
    intro w start
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n14.slots start
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n15.slots start
    rw [dif_neg h14, dif_neg h15, castFinish_gateSlots, reindexStraight_gateSlots]
    exact n16.slots start
  wires := by
    intro w start
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, straightWires_castFinish, straightWires_reindex]
      exact n14.wires start
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, straightWires_castFinish, straightWires_reindex]
      exact n15.wires start
    rw [dif_neg h14, dif_neg h15, straightWires_castFinish, straightWires_reindex]
    exact n16.wires start
  tCount := by
    intro Q w start history
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h14, if_true] using n14.tCount start _ history
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h14, h15, if_true, if_false] using n15.tCount start _ history
    rw [dif_neg h14, dif_neg h15, castFinish_instantiate, reindexStraight_instantiate]
    simpa only [count, h14, h15, if_false] using n16.tCount start _ history

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ScheduleFirst17.program resetProgram leftWindows rightWindows resetBody

def leftCosts (cost16 cost15 : Nat) : List (Nat × Nat) :=
  (917497, 17) :: List.replicate 4 (cost16, 16) ++ List.replicate 12 (cost15, 15)
def rightCosts (cost16 : Nat) : List (Nat × Nat) :=
  List.replicate 13 (cost16, 16)

omit body impl ledger in
theorem left_t_budget (cost16 cost15 : Nat) :
    Single.metadataT (leftCosts cost16 cost15) 0 =
      917497 + 4 * cost16 + 12 * cost15 + 33930 := by
  simp [leftCosts, List.replicate, Single.metadataT, fourierSlots]
  omega

omit body impl ledger in
theorem right_t_budget (cost16 : Nat) :
    Single.metadataT (rightCosts cost16) 0 = 13 * cost16 + 21528 := by
  simp [rightCosts, List.replicate, Single.metadataT, fourierSlots]
  omega

omit body impl ledger in
theorem firstWindow_wellFormed (start : Nat) : (firstWindow.program start).WellFormed := by
  exact ScheduleFirst17.window_wellFormed firstRow start

omit body impl ledger in
theorem firstWindow_slots (start : Nat) : (firstWindow.program start).gateSlots ≤ 3000000000 := by
  exact (ScheduleFirst17.window_slots firstRow start).trans (by norm_num)

omit body impl ledger in
theorem firstWindow_t_uniform (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 917497 := by
  exact ScheduleFirst17.window_t coefficientAt firstRow Q start history

omit impl ledger in
theorem resetBody_wellFormed (start : Nat) : (resetBody start).WellFormed := by
  unfold resetBody
  exact resetProgram_wellFormed _ _ _
omit impl ledger in
theorem resetBody_slots (start : Nat) : (resetBody start).gateSlots = 0 := by
  unfold resetBody
  rw [resetProgram_gateSlots]
omit impl ledger in
theorem resetBody_t (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).tCount = 0 := by
  unfold resetBody
  rw [resetProgram_t]

omit ledger in
theorem signedWindow_wires (w : Digit) : (signedWindow w).wires = (bank w.width).reverse := rfl

omit ledger in
theorem signedWindow_t (Q : Point) (w : Digit) (start : Nat) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count impl.cost14 impl.cost15 impl.cost16 w := impl.tCount Q w start history

omit ledger in
theorem signedWindow_wellFormed (w : Digit) (start : Nat) :
    ((signedWindow w).program start).WellFormed := impl.wellFormed w start

omit ledger in
theorem signedWindow_slots (w : Digit) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ body.slotBound := impl.slots w start

omit ledger in
theorem windows_cases (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows) :
    w = firstWindow ∨ ∃ s, w = signedWindow s := by
  simp only [leftWindows, rightWindows, List.mem_append, List.mem_cons, List.mem_map] at hw
  rcases hw with (h | ⟨s, _, h⟩) | ⟨s, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h.symm⟩
  · exact Or.inr ⟨s, h.symm⟩

omit ledger in
theorem windows_wellFormed (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).WellFormed := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_wellFormed start
  · exact signedWindow_wellFormed s start

def windowSlots : Nat := max 3000000000 body.slotBound

omit ledger in
theorem windows_slots (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
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
    metadataSlots windowSlots rightMetadata 0 + 2 = 30 * windowSlots + 55929 := by
  simp [leftMetadata, rightMetadata, metadataSlots, List.replicate, fourierSlots]
  omega

theorem trial_slots (start : Nat) : (trial start).gateSlots ≤ 32 * windowSlots + 55929 := by
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

theorem program_slots : program.gateSlots ≤ 32 * windowSlots + 55929 := by
  unfold program
  rw [castFinish_gateSlots]
  exact trial_slots 0


omit ledger in
theorem signed_costs (Q : Point) (ws : List Digit) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      (ws.map signedWindow) (ws.map (fun w => (count impl.cost14 impl.cost15 impl.cost16 w, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => signedWindow_t Q w start h⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

omit ledger in
theorem left_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      leftWindows (leftCosts impl.cost16 impl.cost15) := by
  have he : leftCosts impl.cost16 impl.cost15 =
      (917497, 17) :: leftDigits.map (fun w => (count impl.cost14 impl.cost15 impl.cost16 w, w.width)) := by
    simp [leftCosts, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  unfold leftWindows
  refine .cons ⟨?_, fun start h => (firstWindow_t_uniform Q start h).le⟩ (signed_costs Q leftDigits)
  simp only [firstWindow, ScheduleFirst17.windowGeneric, List.length_reverse]
  decide

omit ledger in
theorem right_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      rightWindows (rightCosts impl.cost16) := by
  have he : rightCosts impl.cost16 =
      rightDigits.map (fun w => (count impl.cost14 impl.cost15 impl.cost16 w, w.width)) := by
    simp [rightCosts, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  simpa only [rightWindows] using signed_costs Q rightDigits

theorem left_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      917497 + 4 * impl.cost16 + 12 * impl.cost15 + 33930 := by
  have h := axis_t leftWindows (readConstant coefficientAt Q) (leftCosts impl.cost16 impl.cost15)
    (left_costs Q) start List.nil history
  have hm := left_t_budget impl.cost16 impl.cost15
  simp only [List.length_nil, hm] at h
  omega

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      13 * impl.cost16 + 21528 := by
  have h := axis_t rightWindows (readConstant coefficientAt Q) (rightCosts impl.cost16)
    (right_costs Q) start List.nil history
  have hm := right_t_budget impl.cost16
  simp only [List.length_nil, hm] at h
  omega

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 := by
  unfold trial
  apply (framed_t_le _ _ _ _ _ history (917497 + 4 * impl.cost16 + 12 * impl.cost15 + 33930)
    (13 * impl.cost16 + 21528) (left_axis_t Q start history)
    (fun h => right_axis_t Q _ h) (fun h => resetBody_t _ _ h)).trans
  omega

theorem program_t (Q : Point) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ScheduleFirst17.program resetProgram leftWindows rightWindows resetBody

class SupportCover (body : Single.WindowBody) (ledger : Single.ProducerResources body) : Prop where
  covers : body.support ⊆ ledger.support

variable [cover : SupportCover body ledger]

omit impl cover in
theorem stream_support : streamAddress ⊆ ledger.support := by
  intro v hv
  exact ledger.initial_support (List.mem_append_right _ hv)

omit cover in
theorem windows_bank_support (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows) :
    w.wires ⊆ ledger.support := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · intro v hv
    apply ledger.initial_support
    have hbits : ScheduleFirst17.bits ⊆ resetWires := by decide +kernel
    exact hbits (List.mem_reverse.mp hv)
  · rw [signedWindow_wires]
    intro v hv
    exact stream_support (bank_subset s.width (width_cases s) v (List.mem_reverse.mp hv))

theorem windows_support (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows)
    (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ ledger.support := by
  apply (straight_instantiate_support _ read history).trans
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact (ScheduleFirst17.window_support firstRow start).trans ledger.initial_support
  · exact (impl.wires s start).trans cover.covers

omit impl cover in
private theorem flag_support : (836 : Wire) ∈ ledger.support := by
  apply ledger.initial_support
  simp [resetWires]

omit impl cover in
theorem resetBody_support (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).wires ⊆ ledger.support := by
  unfold resetBody
  exact resetProgram_support _ _ _ _ read history ledger.reset_support

theorem left_axis_support (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support leftWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_left _ hw))
    (fun w hw => windows_support w (List.mem_append_left _ hw)) start List.nil read history

theorem right_axis_support (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support rightWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_right _ hw))
    (fun w hw => windows_support w (List.mem_append_right _ hw)) start List.nil read history

theorem trial_support (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((trial start).instantiate read history).wires ⊆ ledger.support := by
  unfold trial
  exact framed_support _ _ _ _ read history ledger.support flag_support
    (left_axis_support start read history) (fun h => right_axis_support _ read h)
    (fun h => resetBody_support _ read h)

theorem program_support (read : ConstantBit 884736 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ ledger.support := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_support 0 read Fin.elim0

omit cover in
theorem readout_support (read : ConstantBit 884736 → Bool)
    (h : Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) → Bool) :
    (readout.instantiate read h).wires ⊆ ledger.support := by
  unfold readout
  rw [castFinish_instantiate]
  apply (Readout56.suffix56_support 884736
    (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits read h).trans
  have hs : [0,1] ⊆ resetWires := by simp [List.subset_def, resetWires]
  exact hs.trans ledger.initial_support

theorem fullProgram_support (read : ConstantBit 884736 → Bool) :
    (fullProgram.instantiate read Fin.elim0).wires ⊆ ledger.support :=
  outer_append_support _ _ read Fin.elim0 ledger.support (program_support read) (readout_support read)

theorem fullProgram_qubits (read : ConstantBit 884736 → Bool) :
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
      917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 := by
  have h := outer_append_t_le program readout (readConstant coefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  change ((program.append readout).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤ _
  exact h.trans (by simpa only [Nat.add_zero] using program_t Q)

omit cover in
theorem fullProgram_wellFormed : fullProgram.WellFormed :=
  straight_append_wellFormed _ _ program_wellFormed readout_wellFormed

omit cover in
theorem fullProgram_slots : fullProgram.gateSlots ≤ 32 * windowSlots + 178240 := by
  unfold fullProgram
  rw [Straight.gateSlots_append]
  have hr : readout.gateSlots = 122311 := by
    unfold readout
    rw [castFinish_gateSlots]
    exact Readout56.suffix56_slots 884736
      (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits
  rw [hr]
  have h := program_slots
  omega


def entry : StraightEntry := Single.fixedEntry coefficientAt fullProgram

def bounds : Bounds := ⟨ledger.support.length, 917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458,
  131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946⟩

theorem certificate
    (hSlots : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots)
    (hRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946 ≤ officialLimits.measurements) :
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
    change 56 * (2*(order/2^208+2)) ≤ 56*(2^49+2)
    exact SinAverage261.decoder_budget261
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
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] leftWindows rightWindows program fullProgram readout entry Single.axis ScheduleFirst17.program

omit body impl ledger in
theorem first_count (start : Nat) : AtLeast (firstWindow.program start) 131071 := by
  have h := ScheduleFirst17.window_credit coefficientAt firstRow 0 start (fun _ => false)
  exact h.ge

structure ProgramCredit (c14 c15 c16 : Nat) : Prop where
  zero : ∀ w start, residue (impl.program w start) = 0
  count_eq : ∀ w start, added (impl.program w start) = count c14 c15 c16 w

variable {c14 c15 c16 : Nat} (hc : ProgramCredit c14 c15 c16)
include hc

omit ledger in
theorem signed_credit (w : Digit) (start : Nat) :
    AtLeast ((signedWindow w).program start) (count c14 c15 c16 w) := by
  simpa only [signedWindow, AtLeast] using (hc.count_eq w start).ge

def leftCounted : List (CountedWindow 884736) :=
  ⟨firstWindow, 131071, first_count⟩ :: leftDigits.map
    (fun w => ⟨signedWindow w, count c14 c15 c16 w, signed_credit hc w⟩)

def rightCounted : List (CountedWindow 884736) :=
  rightDigits.map (fun w => ⟨signedWindow w, count c14 c15 c16 w, signed_credit hc w⟩)

theorem parent_credit : AtLeast entry.program (131071 + 17 * c16 + 12 * c15) := by
  have hl := counted_axis (leftCounted hc) 0 List.nil
  have hr := counted_axis (rightCounted hc) (0 + Single.axisCount leftWindows) List.nil
  have hls : (leftCounted hc).map CountedWindow.source = leftWindows := by
    simp [leftCounted, leftWindows]
  have hrs : (rightCounted hc).map CountedWindow.source = rightWindows := by
    simp [rightCounted, rightWindows]
  have hln : ((leftCounted hc).map CountedWindow.saving).sum = 131071 + 4 * c16 + 12 * c15 := by
    simp [leftCounted, leftDigits, List.ofFn_succ, Digit.width, count]
    omega
  have hrn : ((rightCounted hc).map CountedWindow.saving).sum = 13 * c16 := by
    simp [rightCounted, rightDigits, List.ofFn_succ, Digit.width, count]
    omega
  rw [hls, hln] at hl
  rw [hrs, hrn] at hr
  have ht : AtLeast (trial 0) (131071 + 17 * c16 + 12 * c15) := by
    unfold trial
    exact (framed_credit _ _ _ _ hl hr).castCount (by omega)
  have hp : AtLeast program (131071 + 17 * c16 + 12 * c15) := by
    unfold program
    exact ht.castFinish _
  unfold entry fullProgram
  apply fixedEntry_credit
  exact (hp.append (AtLeast.zero _)).castCount (by omega)

omit ledger in
theorem signed_t (w : Digit) (start : Nat)
    (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate read history).tCount =
      7 * count c14 c15 c16 w := by
  unfold signedWindow
  rw [exact_t _ (hc.zero w start), hc.count_eq w start]

def creditLeftCosts : List (Nat × Nat) := leftCosts (7*c16) (7*c15)
def creditRightCosts : List (Nat × Nat) := rightCosts (7*c16)

omit ledger in
theorem signed_costs_credit (ws : List Digit) (read : ConstantBit 884736 → Bool) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1)
      (ws.map signedWindow) (ws.map (fun w => (7 * count c14 c15 c16 w, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => (signed_t hc w start read h).le⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

theorem producer_t (Q : Point) :
    (fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      7 * (131071 + 17 * c16 + 12 * c15) + 55458 := by
  let read := readConstant coefficientAt Q
  have lc : List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1) leftWindows
      (creditLeftCosts (c15 := c15) (c16 := c16)) := by
    have he : creditLeftCosts (c15 := c15) (c16 := c16) =
        (917497,17) :: leftDigits.map (fun w => (7 * count c14 c15 c16 w, w.width)) := by
      simp [creditLeftCosts, leftCosts, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
    rw [he]
    unfold leftWindows
    refine .cons ⟨?_, fun start h => (firstWindow_t_uniform Q start h).le⟩
      (signed_costs_credit hc leftDigits read)
    simp only [firstWindow, ScheduleFirst17.windowGeneric, List.length_reverse]
    decide
  have hl := Single.axis_t leftWindows read _ lc 0 List.nil Fin.elim0
  have hr : ∀ h, ((Single.axis rightWindows
      (0 + Single.axisCount leftWindows) List.nil).instantiate read h).tCount ≤
      Single.metadataT (creditRightCosts (c16 := c16)) 0 := by
    intro h
    apply Single.axis_t rightWindows read _ _ _ List.nil h
    have he : creditRightCosts (c16 := c16) =
        rightDigits.map (fun w => (7 * count c14 c15 c16 w, w.width)) := by
      simp [creditRightCosts, rightCosts, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
    rw [he]
    simpa only [rightWindows] using signed_costs_credit hc rightDigits read
  have hln : Single.metadataT (creditLeftCosts (c15 := c15) (c16 := c16)) 0 =
      917497 + 4 * (7*c16) + 12 * (7*c15) + 33930 := left_t_budget _ _
  have hrn : Single.metadataT (creditRightCosts (c16 := c16)) 0 =
      13 * (7*c16) + 21528 := right_t_budget _
  have ht := Single.framed_t_le (Single.axis leftWindows 0 List.nil)
    (Single.axis rightWindows (0 + Single.axisCount leftWindows) List.nil)
    (resetBody (0 + Single.axisCount leftWindows + Single.axisCount rightWindows))
    (show 0 + Single.axisCount leftWindows + Single.axisCount rightWindows +
      body.reset.length = 0 + trialCount from by unfold trialCount; omega)
    read Fin.elim0 _ _ hl hr (resetBody_t _ read)
  have hp : (program.instantiate read Fin.elim0).tCount ≤
      Single.metadataT (creditLeftCosts (c15 := c15) (c16 := c16)) 0 +
        Single.metadataT (creditRightCosts (c16 := c16)) 0 := by
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
    (hBaseSlots : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots)
    (hBaseRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 +
      body.reset.length + 34946 ≤ officialLimits.measurements)
    (hq : q ∉ ledger.support) (hy : y ∉ q :: ledger.support)
    (hslots : entry.program.gateSlots + 21 * added entry.program +
      3 * Catalyst.saved entry.program + 2 ≤ officialLimits.gateSlots)
    (hrecords : entry.finalCursor + added entry.program ≤ officialLimits.measurements) :
    Certificate officialLimits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ledger.support (131071 + 17 * c16 + 12 * c15) 55458) := by
  have base := certificate hBaseSlots hBaseRecords
  have source : Certificate officialLimits layout entry
      ⟨ledger.support.length, 7 * (131071 + 17 * c16 + 12 * c15) + 55458, entry.finalCursor⟩ :=
    { base with
      resources := by
        intro Q
        refine ⟨(base.resources Q).1, ?_, ?_⟩
        change (entry.instantiate Q).tCount ≤ _
        rw [entry, Single.fixedEntry_instantiate]
        · exact producer_t hc Q
        · simpa only [bounds, entry, Single.fixedEntry] using (base.resources Q).2.2 }
  exact WEXCredit.four_certificate officialLimits layout entry ledger.support
    (131071 + 17 * c16 + 12 * c15) 55458 q y source compiler_within hq hy
    (parent_credit hc) hslots hrecords

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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

omit cover in
theorem source_cursor : entry.finalCursor =
    131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946 := by
  unfold entry
  rw [Single.fixedEntry_cursor]

omit cover in
theorem source_slots : entry.program.gateSlots ≤ 32 * windowSlots + 178240 := by
  unfold entry
  rw [Single.fixedEntry_slots]
  exact fullProgram_slots

theorem source_counts (q y : Wire) (sourceBound : Nat)
    (hBaseSlots : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots)
    (hBaseRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 +
      body.reset.length + 34946 ≤ officialLimits.measurements)
    (hSource : 917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 ≤ sourceBound) :
    added entry.program ≤ sourceBound ∧ Catalyst.saved entry.program ≤ sourceBound := by
  have h := four_identity q y entry.program (readConstant entry.coefficients.get 0) Fin.elim0
  have ht := ((certificate hBaseSlots hBaseRecords).resources 0).2.1
  change (entry.program.instantiate (readConstant entry.coefficients.get 0) Fin.elim0).tCount ≤
    917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 at ht
  omega

theorem bounded_four_certificate {c14 c15 c16 : Nat} (hc : ProgramCredit c14 c15 c16)
    (q y : Wire) (sourceBound : Nat)
    (hBaseSlots : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots)
    (hBaseRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 +
      body.reset.length + 34946 ≤ officialLimits.measurements)
    (hSource : 917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 ≤ sourceBound)
    (hSlots : 32 * windowSlots + 178240 + 24 * sourceBound + 2 ≤ officialLimits.gateSlots)
    (hRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length +
      34946 + sourceBound ≤ officialLimits.measurements)
    (hq : q ∉ ledger.support) (hy : y ∉ q :: ledger.support) :
    Certificate officialLimits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ledger.support (131071 + 17 * c16 + 12 * c15) 55458) := by
  have hc' := source_counts q y sourceBound hBaseSlots hBaseRecords hSource
  have hs := source_slots
  have hm := source_cursor
  apply four_certificate hc q y hBaseSlots hBaseRecords hq hy
  · omega
  · omega

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem triProgramCredit (n14 : ModNarrow body 13) (n15 : ModNarrow body 14)
    (n16 : ModNarrow body 15) :
    @ProgramCredit body (triPrograms n14 n15 n16) n14.credit n15.credit n16.credit := by
  refine @ProgramCredit.mk body (triPrograms n14 n15 n16) n14.credit n15.credit n16.credit ?_ ?_
  · intro w start
    change residue (if h14 : w.width = 14 then castFinish _ (reindexStraight (paddedRow w) (n14.program start))
      else if h15 : w.width = 15 then castFinish _ (reindexStraight (paddedRow w) (n15.program start))
      else castFinish _ (reindexStraight (paddedRow w) (n16.program start))) = 0
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, residue_cast, residue_reindex]
      exact n14.zero start
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, residue_cast, residue_reindex]
      exact n15.zero start
    rw [dif_neg h14, dif_neg h15, residue_cast, residue_reindex]
    exact n16.zero start
  · intro w start
    change added (if h14 : w.width = 14 then castFinish _ (reindexStraight (paddedRow w) (n14.program start))
      else if h15 : w.width = 15 then castFinish _ (reindexStraight (paddedRow w) (n15.program start))
      else castFinish _ (reindexStraight (paddedRow w) (n16.program start))) =
        count n14.credit n15.credit n16.credit w
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, added_cast, added_reindex, n14.count_eq start]
      simp [count,h14]
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, added_cast, added_reindex, n15.count_eq start]
      simp [count,h15]
    rw [dif_neg h14, dif_neg h15, added_cast, added_reindex, n16.count_eq start]
    simp [count,h14,h15]

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
end


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit body ledger cover in
private theorem fusedClearWiden {limits : Limits} {layout : DecodeLayout} {entry : StraightEntry}
    {old new : Bounds} (cert : Certificate limits layout entry old)
    (hq : old.qubits ≤ new.qubits) (ht : old.tModel ≤ new.tModel)
    (hm : old.measurements ≤ new.measurements) : Certificate limits layout entry new :=
  { cert with resources := fun Q =>
      ⟨(cert.resources Q).1.trans hq, (cert.resources Q).2.1.trans ht, (cert.resources Q).2.2.trans hm⟩ }

theorem matched_fused_certificate (n14 : ModNarrow body 13) (n15 : ModNarrow body 14)
    (n16 : ModNarrow body 15)
    (hSupport : ledger.support.length ≤ 1619) (hSlot : body.slotBound ≤ 3000000000)
    (hR15 : n15.records ≤ 1659546) (hR16 : n16.records ≤ 1758490)
    (hReset : body.reset.length ≤ 854)
    (hT15 : n15.tBound ≤ 15844248) (hT16 : n16.tBound ≤ 16536856)
    (hC15 : n15.credit ≤ 2263464) (hC16 : n16.credit ≤ 2362408)
    (hq : (1938 : Wire) ∉ ledger.support) (hy : (1939 : Wire) ∉ 1938 :: ledger.support) :
    letI : Programs body := triPrograms n14 n15 n16
    Certificate officialLimits (lowerLayout 1938 entry layout) (fourEntry 1938 1939 entry)
      ⟨1621, 269869759, 543906879⟩ := by
  letI : Programs body := triPrograms n14 n15 n16
  have hwin : windowSlots ≤ 3000000000 := max_le le_rfl hSlot
  have hbaseS : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots := by
    change 32 * windowSlots + 178240 ≤ 4000000000000000
    omega
  have hbaseR : 131071 + 17 * (triPrograms n14 n15 n16).records16 + 12 * (triPrograms n14 n15 n16).records15 +
      469 + body.reset.length + 34946 ≤ officialLimits.measurements := by
    change 131071 + 17 * n16.records + 12 * n15.records + 469 + body.reset.length + 34946 ≤ 47471340504
    omega
  have hsrc : 917497 + 17 * (triPrograms n14 n15 n16).cost16 + 12 * (triPrograms n14 n15 n16).cost15 +
      55458 ≤ 491238726 := by
    change 917497 + 17 * n16.tBound + 12 * n15.tBound + 55458 ≤ 491238726
    omega
  have hslots : 32 * windowSlots + 178240 + 24 * 491238726 + 2 ≤ officialLimits.gateSlots := by
    change 32 * windowSlots + 178240 + 24 * 491238726 + 2 ≤ 4000000000000000
    omega
  have hrecords : 131071 + 17 * (triPrograms n14 n15 n16).records16 + 12 * (triPrograms n14 n15 n16).records15 +
      469 + body.reset.length + 34946 + 491238726 ≤ officialLimits.measurements := by
    change 131071 + 17 * n16.records + 12 * n15.records + 469 + body.reset.length + 34946 +
      491238726 ≤ 47471340504
    omega
  have raw := bounded_four_certificate (triProgramCredit n14 n15 n16) 1938 1939 491238726
    hbaseS hbaseR hsrc hslots hrecords hq hy
  have hcounts := (source_counts 1938 1939 491238726 hbaseS hbaseR hsrc).1
  have hcursor : entry.finalCursor ≤ 52668153 := by
    rw [source_cursor]
    change 131071 + 17 * n16.records + 12 * n15.records + 469 + body.reset.length + 34946 ≤ 52668153
    omega
  apply fusedClearWiden raw
  · change ledger.support.length + 2 ≤ 1621
    omega
  · change 4 * (131071 + 17 * n16.credit + 12 * n15.credit) + 55458 + 1 ≤ 269869759
    omega
  · change entry.finalCursor + added entry.program ≤ 543906879
    omega
end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible

namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible.FusedFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] WEXUnlookupWidth13.compactProgram WEXUnlookupWidth14.compactProgram WEXUnlookup.Width15Fused.fastCompactProgram WEXUnlookupWidth14.Fused.fastCompactProgram
  WEXUnlookupWidth13.bodyProgram WEXUnlookupWidth14.bodyProgram
  WEXUnlookupWidth13.ccx WEXUnlookupWidth14.ccx
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount
  WEX.literalToffolis WEX.normalizeW Nat.add Nat.mul AndGadget.added

def narrow13 : ModNarrow PathShare.body2 13 := PathShare.narrow13
def narrow14 : ModNarrow PathShare.body2 14 := PathShare.narrow14
def narrow15 : ModNarrow PathShare.body2 15 := PathShare.narrow15

theorem n14_records : narrow14.records ≤ 1659546 := by
  exact le_rfl
theorem n15_records : narrow15.records ≤ 1758490 := by
  exact le_rfl
theorem n14_cost : narrow14.tBound ≤ 15844248 := by
  exact le_rfl
theorem n15_cost : narrow15.tBound ≤ 16536856 := by
  exact le_rfl

attribute [local irreducible] narrow13 narrow14 narrow15
local instance bodyInstance : Single.WindowBody := PathShare.body2
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody PathShare.body2
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
local instance programInstance : Programs bodyInstance := triPrograms narrow13 narrow14 narrow15

private theorem count14_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 15844248) :
    c ≤ 2263464 := by omega
private theorem count15_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 16536856) :
    c ≤ 2362408 := by omega

theorem n14_credit : narrow14.credit ≤ 2263464 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow14.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow14.program 0) (narrow14.zero 0) read Fin.elim0
  have hc := narrow14.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count14_bound _ _ he' (ht.trans n14_cost)
theorem n15_credit : narrow15.credit ≤ 2362408 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow15.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow15.program 0) (narrow15.zero 0) read Fin.elim0
  have hc := narrow15.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count15_bound _ _ he' (ht.trans n15_cost)

def entry : StraightEntry := fourEntry 1938 1939 Flexible.entry
def layout : DecodeLayout := lowerLayout 1938 Flexible.entry Flexible.layout
def bounds : Bounds := ⟨1621, 269869759, 543906879⟩

theorem certificate : Certificate officialLimits layout entry bounds := by
  apply @matched_fused_certificate bodyInstance resourcesInstance coverInstance narrow13 narrow14 narrow15
  · change PathShare.body2.support.length ≤ 1619
    exact PathShare.body2_ledger.1.le
  · change PathShare.body2.slotBound ≤ 3000000000
    exact (by decide : (2000000000 : Nat) ≤ 3000000000)
  · exact n14_records.trans (by norm_num)
  · exact n15_records.trans (by norm_num)
  · change PathShare.body2.reset.length ≤ 854
    exact PathShare.body2_ledger.2.le
  · exact n14_cost.trans (by norm_num)
  · exact n15_cost.trans (by norm_num)
  · exact n14_credit
  · exact n15_credit
  · change (1938 : Wire) ∉ List.range 1619
    simp
  · change (1939 : Wire) ∉ 1938 :: List.range 1619
    simp
end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible.FusedFinal

