-- Vendored from ECDSAAdd (ecdsa.fail Lean challenge), Apache-2.0, Copyright 2026 Runzhou Tao, Anirudh and ECDSAAdd contributors; 207 source modules at c3f340a (listed in MODULES.txt), concatenated. Changes: module paths, expanded notation, private-name renames; declarations unreachable from the ShorECDLP judge roots (no kernel or elaborator reference) removed in the 2026-11-11 dead-code compaction, `-- source:` markers kept.
import Mathlib.Data.List.Basic
import Lean
import Mathlib.Data.Finset.Card
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Int.DivMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators

-- source: ECDSAAdd/Framework/Syntax.lean
noncomputable section

namespace ECDSAAdd
open Lean

abbrev Wire := Nat
abbrev BasisState := Wire → Bool

structure State where
  phase : Bool
  basis : BasisState

inductive Correction where
  | Z (target : Wire)
  | CZ (left right : Wire)
  deriving DecidableEq, Repr

/-- 测量只选择即时 Z/CZ 修正；后续算术与测量顺序固定。 -/
inductive Instr where
  | X (target : Wire)
  | CX (control target : Wire)
  | CCX (left right target : Wire)
  | measureX (target : Wire) (onZero onOne : List Correction)
  deriving DecidableEq, Repr

abbrev Program := List Instr

def measurementCount : Program → Nat
  | [] => 0
  | .measureX _ _ _ :: p => 1 + measurementCount p
  | _ :: p => measurementCount p

instance : Coe Correction (List Correction) := ⟨fun c => [c]⟩
end ECDSAAdd
end

-- source: ECDSAAdd/Framework/Semantics.lean
noncomputable section

namespace ECDSAAdd

def writeBit (bits : BasisState) (w : Wire) (v : Bool) : BasisState :=
  Function.update bits w v

def correct : List Correction → State → State
  | [], s => s
  | .Z t :: cs, s => correct cs ⟨s.phase ^^ s.basis t, s.basis⟩
  | .CZ a b :: cs, s => correct cs ⟨s.phase ^^ (s.basis a && s.basis b), s.basis⟩

/-- 先用清零前的位更新相位，再清零，最后按测量结果立即修正。 -/
def measureAndCorrect (t : Wire) (c₀ c₁ : List Correction) (m : Bool) (s : State) : State :=
  correct (if m then c₁ else c₀)
    ⟨s.phase ^^ (m && s.basis t), writeBit s.basis t false⟩

/-- 按表头消费测量结果；不足时补 0，多余结果忽略。全称量化仍覆盖所有分支。 -/
def run : Program → List Bool → State → State
  | [], _, s => s
  | .X t :: p, m, s => run p m ⟨s.phase, writeBit s.basis t (!s.basis t)⟩
  | .CX c t :: p, m, s => run p m ⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis c)⟩
  | .CCX a b t :: p, m, s =>
      run p m ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩
  | .measureX t c₀ c₁ :: p, m, s =>
      run p m.tail (measureAndCorrect t c₀ c₁ (m.headD false) s)

/-- 相位修正不改变任何 basis 位。 -/
@[simp] theorem correct_basis (cs : List Correction) (s : State) :
    (correct cs s).basis = s.basis := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [correct, ih]

/-- 执行只读取本程序需要的测量结果。 -/
theorem run_take (p : Program) (m : List Bool) (s : State) :
    run p (m.take (measurementCount p)) s = run p m s := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [measurementCount, run]
    all_goals try exact ih m _
    cases m <;> simp [ih, Nat.add_comm]

/-- 顺序执行两个程序，记录用 take/drop 按第一段的测量次数拆分。 -/
theorem run_append (p q : Program) (m : List Bool) (s : State) :
    run (p ++ q) m s =
      run q (m.drop (measurementCount p)) (run p (m.take (measurementCount p)) s) := by
  rw [run_take]
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [List.cons_append, run, measurementCount]
    all_goals try exact ih m _
    cases m <;> simp [ih, Nat.add_comm]

end ECDSAAdd
end

-- source: ECDSAAdd/Framework/Cost.lean
noncomputable section

namespace ECDSAAdd

def toffoliCount : Program → Nat
  | [] => 0
  | .CCX _ _ _ :: p => 1 + toffoliCount p
  | _ :: p => toffoliCount p

def correctionWires : List Correction → Finset Wire
  | [] => ∅
  | .Z t :: cs => {t} ∪ correctionWires cs
  | .CZ a b :: cs => {a, b} ∪ correctionWires cs

def Instr.wires : Instr → Finset Wire
  | .X t => {t}
  | .CX c t => {c, t}
  | .CCX a b t => {a, b, t}
  | .measureX t c₀ c₁ => {t} ∪ correctionWires c₀ ∪ correctionWires c₁

/-- 静态线路并集包含两条修正列表，不是每条指令的线路数之和。 -/
def wires : Program → Finset Wire
  | [] => ∅
  | i :: p => i.wires ∪ wires p

/-- 不同物理线路数，不声称最大同时存活数。 -/
def qubitCount (p : Program) : Nat := (wires p).card

@[simp] theorem measurementCount_append (p q : Program) :
    measurementCount (p ++ q) = measurementCount p + measurementCount q := by
  induction p with
  | nil => simp [measurementCount]
  | cons i p ih => cases i <;> simp [measurementCount, ih, Nat.add_assoc]

@[simp] theorem toffoliCount_append (p q : Program) :
    toffoliCount (p ++ q) = toffoliCount p + toffoliCount q := by
  induction p with
  | nil => simp [toffoliCount]
  | cons i p ih => cases i <;> simp [toffoliCount, ih, Nat.add_assoc]

@[simp] theorem wires_append (p q : Program) : wires (p ++ q) = wires p ∪ wires q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih => simp [wires, ih, Finset.union_assoc]

/-- 对所有测量结果，程序不会修改声明线路集合以外的位。 -/
theorem run_preserves_outside (p : Program) (m : List Bool) (s : State) (w : Wire)
    (hw : w ∉ wires p) : (run p m s).basis w = s.basis w := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    have hi : w ∉ i.wires := fun h => hw (Finset.mem_union_left _ h)
    have hp : w ∉ wires p := fun h => hw (Finset.mem_union_right _ h)
    cases i <;> simp only [run] <;> rw [ih _ _ hp] <;>
      simp_all [Instr.wires, measureAndCorrect, writeBit, Function.update]

end ECDSAAdd
end

-- source: ECDSAAdd/Math/BitcoinCurve.lean
noncomputable section

/-!
# Bitcoin's secp256k1 mathematical problem

This module fixes only the mathematical objects needed to state the Bitcoin
ECDLP problem: the base field, curve, standard generator, and group order.  It
contains no point encoding, oracle circuit, arithmetic implementation, or
resource claim; those remain choices made by a submission.
-/

namespace ECDSAAdd

/-- The secp256k1 base-field prime `p = 2^256 − 2^32 − 977`. -/
def p : ℕ := 2 ^ 256 - 2 ^ 32 - 977

/-- secp256k1 short-Weierstrass coefficient `a = 0` (curve `y² = x³ + 7`). -/
def curveA : ℕ := 0

/-- secp256k1 short-Weierstrass coefficient `b = 7`. -/
def curveB : ℕ := 7

/-- The secp256k1 base field `F_p`. -/
abbrev Fp := ZMod p

namespace Secp256k1

/-- The standard generator's `x` coordinate, represented canonically in `[0, p)`. -/
def generatorX : Nat :=
  55066263022277343669578718895168534326250603453777594175500187360389116729240

/-- The standard generator's `y` coordinate, represented canonically in `[0, p)`. -/
def generatorY : Nat :=
  32670510020758816978083085130507043184471273380659243275938904335757337482424

/-- The short-Weierstrass secp256k1 curve `y² = x³ + 7` over `Fp`. -/
def curve : WeierstrassCurve Fp where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := curveA
  a₆ := curveB

/-- The canonical mathematical type of secp256k1 points. -/
abbrev Point := curve.toAffine.Point

/-- The secp256k1 discriminant is nonzero in `Fp`. -/
theorem curve_discriminant_ne_zero : curve.Δ ≠ 0 := by
  have hΔ : curve.Δ = (-21168 : Fp) := by
    simp [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, curveA, curveB]
    norm_num
  rw [hΔ]
  intro h
  have hdvd : (p : Int) ∣ (-21168 : Int) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (-21168) p).mp h
  norm_num [p] at hdvd

/-- Under the published primality hypothesis for `p`, `curve` is an elliptic curve in Mathlib's
sense: its discriminant is a unit. -/
instance [Fact (Nat.Prime p)] : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr curve_discriminant_ne_zero⟩

/-- The standard generator coordinates satisfy the secp256k1 curve equation. -/
theorem generator_equation :
    curve.toAffine.Equation (generatorX : Fp) (generatorY : Fp) := by
  rw [curve.toAffine.equation_iff]
  change ((generatorY : Fp) ^ 2 = (generatorX : Fp) ^ 3 + 7)
  simp only [generatorX, generatorY]
  unfold Fp p
  reduce_mod_char

/-- The standard generator is a nonsingular affine point. -/
theorem generator_nonsingular :
    curve.toAffine.Nonsingular (generatorX : Fp) (generatorY : Fp) :=
  (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
    generator_equation

/-- The standard secp256k1 generator as a value of the canonical point type. -/
def G : Point :=
  .some generator_nonsingular

/-- Reveal affine coordinates while representing the point at infinity by `none`. -/
def coordinates : Point → Option (Fp × Fp)
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => some (x, y)

@[simp]
theorem coordinates_zero : coordinates (0 : Point) = none :=
  rfl

@[simp]
theorem coordinates_some {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    coordinates (.some h) = some (x, y) :=
  rfl

/-- The standard generator exposes exactly the published affine coordinates. -/
@[simp]
theorem coordinates_G :
    coordinates G = some ((generatorX : Fp), (generatorY : Fp)) :=
  rfl

end Secp256k1
end ECDSAAdd
end

-- source: ECDSAAdd/Framework/Hoare.lean
noncomputable section

namespace ECDSAAdd
open Lean

/-- 按寄存器类型读取逻辑值；断言里的 r=v 就展开为此谓词。 -/
class Holds (α : Type) (β : Type) where
  holds : BasisState → α → β → Prop

instance : Holds Wire Bool := ⟨fun st w v => st w = v⟩

def regValue (r : List Wire) (st : BasisState) : Nat :=
  r.foldr (fun w acc => (if st w then 1 else 0) + 2 * acc) 0

instance : Holds (List Wire) Nat := ⟨fun st r n => regValue r st = n⟩

/-- 有限点标志和两个小端坐标寄存器；无穷远点采用全零表示。 -/
structure PointReg where
  finite : Wire
  x : List Wire
  y : List Wire

instance : Holds PointReg Secp256k1.Point where
  holds st r p := match Secp256k1.coordinates p with
    | none => st r.finite = false ∧ regValue r.x st = 0 ∧ regValue r.y st = 0
    | some (x, y) => st r.finite = true ∧ regValue r.x st = x.val ∧ regValue r.y st = y.val

/-- 对所有初始相位和所有测量结果：满足前置条件时，相位恢复且后置条件成立。
这是 monomial 判断；相位恢复必须证明，不由语法保证。 -/
def Triple (P : BasisState → Prop) (c : Program) (Q : BasisState → Prop) : Prop :=
  ∀ (s : State) (m : List Bool), P s.basis →
    (run c m s).phase = s.phase ∧ Q (run c m s).basis

/-! The `{{ P,.. }} c {{ Q,.. }}` notation of the original file is expanded at every
use site to `Triple (fun st => ..) c (fun st => ..)`, where each `x = v` conjunct is
`Holds.holds st x v` and conjuncts nest to the left. -/

namespace Triple
variable {P P' Q Q' R : BasisState → Prop} {c d : Program}

/-- 顺序组合：前一段的后置条件是后一段的前置条件。 -/
theorem seq (hc : Triple P c Q) (hd : Triple Q d R) : Triple P (c ++ d) R := by
  intro s m hP
  rw [run_append]
  obtain ⟨hphase, hQ⟩ := hc s (m.take (measurementCount c)) hP
  obtain ⟨hphase', hR⟩ := hd _ (m.drop (measurementCount c)) hQ
  exact ⟨hphase'.trans hphase, hR⟩

/-- 加强前置条件、削弱后置条件。 -/
theorem conseq (hP : ∀ s, P' s → P s) (hc : Triple P c Q)
    (hQ : ∀ s, Q s → Q' s) : Triple P' c Q' := by
  intro s m h
  obtain ⟨hp, hq⟩ := hc s m (hP _ h)
  exact ⟨hp, hQ _ hq⟩

end Triple
end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/Registers.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 小端读值相等恰好表示寄存器中的每一位相等。 -/
theorem regValue_eq_iff (r : List Wire) (s t : BasisState) :
    regValue r s = regValue r t ↔ ∀ w ∈ r, s w = t w := by
  constructor
  · intro h
    induction r with
    | nil => simp
    | cons a r ih =>
      have hb : s a = t a := by
        change (if s a then 1 else 0) + 2 * regValue r s =
          (if t a then 1 else 0) + 2 * regValue r t at h
        cases hs : s a <;> cases ht : t a <;>
          simp only [hs, ht, Bool.false_eq_true, if_false, if_true] at h ⊢ <;> omega
      have hr : regValue r s = regValue r t := by
        change (if s a then 1 else 0) + 2 * regValue r s =
          (if t a then 1 else 0) + 2 * regValue r t at h
        rw [hb] at h
        omega
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hb
      · exact ih hr w hw
  · intro h
    induction r with
    | nil => rfl
    | cons a r ih =>
      change (if s a then 1 else 0) + 2 * regValue r s =
        (if t a then 1 else 0) + 2 * regValue r t
      rw [h a (by simp), ih (fun w hw => h w (by simp [hw]))]

/-- XOR 按小端的最低位与高位分解。 -/
theorem xor_value_step (a b : Bool) (x y : Nat) :
    (a ^^ b).toNat + 2 * (x ^^^ y) = (a.toNat + 2 * x) ^^^ (b.toNat + 2 * y) := by
  have h := (Nat.xor_bit a x b y).symm
  cases a <;> cases b <;> simpa [Nat.bit, Bool.toNat, Nat.add_comm] using h

/-- 小端寄存器读取只依赖其自身线路。 -/
theorem regValue_congr (r : List Wire) (s t : BasisState)
    (h : ∀ w ∈ r, s w = t w) : regValue r s = regValue r t := by
  induction r with
  | nil => rfl
  | cons w ws ih =>
    change (if s w then 1 else 0) + 2 * regValue ws s =
      (if t w then 1 else 0) + 2 * regValue ws t
    rw [h w (by simp), ih (fun w hw => h w (by simp [hw]))]

/-- 零值恰好表示每一位均为 false。 -/
theorem regValue_zero (r : List Wire) (s : BasisState) :
    regValue r s = 0 ↔ ∀ w ∈ r, s w = false := by
  induction r with
  | nil => simp [regValue]
  | cons w ws ih =>
    change (if s w then 1 else 0) + 2 * regValue ws s = 0 ↔ _
    cases h : s w <;> simp [h, ih]

/-- n 位寄存器总是表示小于 2^n 的自然数。 -/
theorem regValue_lt (r : List Wire) (s : BasisState) : regValue r s < 2^r.length := by
  induction r with
  | nil => simp [regValue]
  | cons w ws ih =>
    change (if s w then 1 else 0) + 2 * regValue ws s < 2^(ws.length+1)
    rw [Nat.pow_succ]
    split <;> omega

/-- 对寄存器每根线路执行 X。 -/
def notRegister (r : List Wire) : Program := r.map Instr.X

/-- 寄存器内每一位取反，其他线路与相位保持。 -/
theorem notRegister_correct (r : List Wire) (hnd : r.Nodup) (s : State) (m : List Bool) :
    run (notRegister r) m s =
      ⟨s.phase, fun w => if w ∈ r then !s.basis w else s.basis w⟩ := by
  induction r generalizing s with
  | nil => simp [notRegister, run]
  | cons a r ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.mp hnd
    simp only [notRegister, List.map_cons, run]
    rw [show List.map Instr.X r = notRegister r from rfl, ih hr]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases hw : w = a
    · subst w; simp [writeBit, ha]
    · simp [writeBit, hw]

/-- 全位取反的读值为 2^n-1-X。 -/
theorem regValue_complement (r : List Wire) (s : BasisState) :
    regValue r (fun w => !s w) = 2^r.length - 1 - regValue r s := by
  have hsum : regValue r (fun w => !s w) + regValue r s + 1 = 2^r.length := by
    induction r with
    | nil => simp [regValue]
    | cons w ws ih =>
      change ((if !s w then 1 else 0) + 2 * regValue ws (fun w => !s w)) +
        ((if s w then 1 else 0) + 2 * regValue ws s) + 1 = 2^(ws.length+1)
      rw [Nat.pow_succ]
      cases s w <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_true, if_false] <;> omega
  omega

/-- 全位取反只含 X 门，没有 Toffoli 或测量。 -/
theorem notRegister_counts (r : List Wire) :
    toffoliCount (notRegister r) = 0 ∧ measurementCount (notRegister r) = 0 := by
  induction r with
  | nil => exact ⟨rfl, rfl⟩
  | cons w ws ih => simpa [notRegister, toffoliCount, measurementCount] using ih

theorem notRegister_wires (r : List Wire) : wires (notRegister r) = r.toFinset := by
  induction r with
  | nil => rfl
  | cons w ws ih => simpa [notRegister, wires, Instr.wires] using congrArg (insert w) ih

/-- 小端寄存器第 i 位与自然数除法表示一致。 -/
theorem regValue_bit (r : List Wire) (i : Nat) (fallback : Wire) (s : BasisState) (hi : i<r.length) :
    (s (r.getD i fallback)).toNat=(regValue r s/2^i)%2 := by
  induction r generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => simp [regValue,Bool.toNat]; cases s a <;> simp
    | succ i =>
      simp only [List.getD_cons_succ]
      rw [ih i (by simpa using hi)]
      have hd : regValue (a::as) s/2=regValue as s := by
        change ((if s a then 1 else 0)+2*regValue as s)/2=regValue as s
        cases s a <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
      rw [Nat.pow_succ,Nat.mul_comm (2^i) 2,← Nat.div_div_eq_div_mul,hd]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Constant.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 经典常量按小端展开，只有常量位为 1 的线路才执行 X。 -/
def xorConstant : List Wire → Nat → Program
  | [], _ => []
  | w :: ws, k => (if k % 2 = 1 then [Instr.X w] else []) ++ xorConstant ws (k / 2)

/-- 异或经典常量，保持相位和寄存器外全部线路。 -/
theorem xorConstant_correct (r : List Wire) (hnd : r.Nodup) (k : Nat)
    (hk : k < 2^r.length) (s : State) (m : List Bool) :
    (run (xorConstant r k) m s).phase = s.phase ∧
    (∀ w, w ∉ r → (run (xorConstant r k) m s).basis w = s.basis w) ∧
    regValue r (run (xorConstant r k) m s).basis = regValue r s.basis ^^^ k := by
  induction r generalizing k s with
  | nil =>
    have hk0 : k = 0 := by simpa using hk
    simp [xorConstant, run, regValue, hk0]
  | cons w ws ih =>
    obtain ⟨hw, hn⟩ := List.nodup_cons.mp hnd
    have htail : k / 2 < 2^ws.length := by
      simp only [List.length_cons, Nat.pow_succ] at hk
      omega
    let s1 : State := if k % 2 = 1 then ⟨s.phase, writeBit s.basis w (!s.basis w)⟩ else s
    have hfirst : run (if k % 2 = 1 then [Instr.X w] else []) m s = s1 := by
      by_cases h : k % 2 = 1 <;> simp [h, run, s1]
    have hs1 : ∀ v, v ≠ w → s1.basis v = s.basis v := by
      intro v hv
      by_cases h : k % 2 = 1 <;> simp [s1, h, writeBit, hv]
    have hp1 : s1.phase = s.phase := by by_cases h : k % 2 = 1 <;> simp [s1, h]
    have hm : measurementCount (if k % 2 = 1 then [Instr.X w] else []) = 0 := by
      by_cases h : k % 2 = 1 <;> simp [h, measurementCount]
    let t := run (xorConstant ws (k/2)) m s1
    obtain ⟨hp, he, hv⟩ := ih hn (k/2) htail s1
    change t.phase = s1.phase at hp
    change ∀ v, v ∉ ws → t.basis v = s1.basis v at he
    change regValue ws t.basis = regValue ws s1.basis ^^^ (k/2) at hv
    rw [xorConstant, run_append, run_take, hm, List.drop_zero, hfirst]
    refine ⟨hp.trans hp1, ?_, ?_⟩
    · intro v hv
      have hv' : v ≠ w ∧ v ∉ ws := by simpa only [List.mem_cons, not_or] using hv
      exact (he v hv'.2).trans (hs1 v hv'.1)
    · have hreg : regValue ws s1.basis = regValue ws s.basis :=
        regValue_congr _ _ _ (fun v hv => hs1 v (by intro h; apply hw; simpa [h] using hv))
      have hbit : t.basis w = (s.basis w ^^ decide (k % 2 = 1)) := by
        rw [he w hw]
        by_cases h : k % 2 = 1 <;> simp [s1, h, writeBit]
      have hkbit : (decide (k % 2 = 1)).toNat + 2 * (k / 2) = k := by
        have hdiv := Nat.mod_add_div k 2
        have hmod := Nat.mod_lt k (by decide : 0 < 2)
        by_cases h : k % 2 = 1
        · simp only [h, decide_true, Bool.toNat_true]; omega
        · have hz : k % 2 = 0 := by omega
          simp only [h, decide_false, Bool.toNat_false]; omega
      change (if t.basis w then 1 else 0) + 2 * regValue ws t.basis = _
      rw [hbit, hv, hreg]
      have hxor := xor_value_step (s.basis w) (decide (k % 2 = 1))
        (regValue ws s.basis) (k/2)
      rw [hkbit] at hxor
      simpa only [regValue, List.foldr_cons, Bool.toNat, Bool.cond_eq_ite] using hxor

/-- 常量 XOR 不使用 Toffoli 或测量。 -/
theorem xorConstant_counts (r : List Wire) (k : Nat) :
    toffoliCount (xorConstant r k) = 0 ∧ measurementCount (xorConstant r k) = 0 := by
  induction r generalizing k with
  | nil => exact ⟨rfl, rfl⟩
  | cons w ws ih =>
    by_cases h : k % 2 = 1 <;>
      simp [xorConstant, h,
        toffoliCount, measurementCount, (ih (k/2)).1, (ih (k/2)).2]

/-- 常量 XOR 只触碰常量寄存器；实际支持集可能更小，因为 0 位不施门。 -/
theorem xorConstant_wires_subset (r : List Wire) (k : Nat) :
    wires (xorConstant r k) ⊆ r.toFinset := by
  induction r generalizing k with
  | nil => simp [xorConstant, wires]
  | cons w ws ih =>
    intro v hv
    by_cases h : k % 2 = 1
    · simp only [xorConstant, h, if_true, wires_append, wires, Instr.wires] at hv
      simp only [Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with rfl | hv
      · simp
      · simpa only [List.toFinset_cons, Finset.mem_insert] using Or.inr (a := v = w) (ih (k/2) hv)
    · simp only [xorConstant, h, if_false, List.nil_append] at hv
      simpa only [List.toFinset_cons, Finset.mem_insert] using Or.inr (a := v = w) (ih (k/2) hv)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FullAdder.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Instr Correction

def sumBit (a b c : Bool) : Bool := (a ^^ b) ^^ c

def carryBit (a b c : Bool) : Bool := ((a && b) ^^ (a && c)) ^^ (b && c)

/-- 先临时异或输入，用一个 Toffoli 计算 majority，再恢复输入并异或输出和位。 -/
def fullAdder (a b cin out carry : Wire) : Program := ([
  CX a b, CX a cin, CCX b cin carry,
  CX a carry, CX a cin, CX a b,
  CX a out, CX b out, CX cin out
] : Program)

/-- 进位是三项 AND 的异或；测量后立即执行对应的三个 CZ 修正。 -/
def eraseCarry (a b cin carry : Wire) : Program :=
  ([ Instr.measureX carry ([] : List Correction) ([CZ a b, CZ a cin, CZ b cin]) ] : Program)

/-- 任意输出和进位初值均可：在两处 XOR 写入和位与进位，其余状态保持。 -/
theorem fullAdder_correct (a b cin out carry : Wire)
    (hdisjoint : [a, b, cin, out, carry].Nodup)
    (s : State) (m : List Bool) :
    run (fullAdder a b cin out carry) m s =
      ⟨s.phase,
        writeBit (writeBit s.basis carry
          (s.basis carry ^^ carryBit (s.basis a) (s.basis b) (s.basis cin)))
          out (s.basis out ^^ sumBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hdisjoint
  obtain ⟨⟨hab, hac, hao, hak⟩, ⟨hbc, hbo, hbk⟩, ⟨hco, hck⟩, hok⟩ := hdisjoint
  have hcb := Ne.symm hbc
  simp only [fullAdder, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwa : w = a <;> by_cases hwb : w = b <;>
    by_cases hwc : w = cin <;> by_cases hwo : w = out <;>
    by_cases hwk : w = carry <;>
    simp_all [writeBit, Function.update, sumBit, carryBit]
  cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;>
    cases s.basis out <;> cases s.basis carry <;> simp_all

/-- 只要 carry 保存正确的进位，就能对任意测量结果清零它，且恢复原相位。 -/
theorem eraseCarry_correct (a b cin carry : Wire)
    (ha : a ≠ carry) (hb : b ≠ carry) (hc : cin ≠ carry)
    (s : State)
    (hcarry : s.basis carry = carryBit (s.basis a) (s.basis b) (s.basis cin))
    (m : List Bool) :
    run (eraseCarry a b cin carry) m s =
      ⟨s.phase, writeBit s.basis carry false⟩ := by
  simp only [eraseCarry, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, ha, hb, hc,
      hcarry, carryBit]
  cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;> simp

/-- 保持三个输入，在输出与进位线上异或写入和位与进位。 -/
theorem fullAdder_spec (a b cin out carry : Wire)
    (hnd : [a, b, cin, out, carry].Nodup) (A B C O K : Bool) :
    (Triple (fun st => (((Holds.holds st a A ∧ Holds.holds st b B) ∧ Holds.holds st cin C) ∧ Holds.holds st out O) ∧ Holds.holds st carry K) (fullAdder a b cin out carry)
      (fun st => (((Holds.holds st a A ∧ Holds.holds st b B) ∧ Holds.holds st cin C) ∧ Holds.holds st out (O ^^ sumBit A B C)) ∧ Holds.holds st carry (K ^^ carryBit A B C))) := by
  intro s m hP
  rw [fullAdder_correct a b cin out carry hnd]
  simp only [Holds.holds] at hP ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨hab, hac, hao, hak⟩, ⟨hbc, hbo, hbk⟩, ⟨hco, hck⟩, hok⟩ := hnd
  simp_all [writeBit, Function.update, Ne.symm hok]

theorem fullAdder_wires (a b cin out carry : Wire) :
    wires (fullAdder a b cin out carry) = {a, b, cin, out, carry} := by
  ext w
  simp [fullAdder, wires, Instr.wires]
  tauto

theorem eraseCarry_wires (a b cin carry : Wire) :
    wires (eraseCarry a b cin carry) = {a, b, cin, carry} := by
  ext w
  simp [eraseCarry, wires, Instr.wires, correctionWires]
  tauto

/-- 和位加上二倍进位，恰好等于三个输入位的自然数之和。 -/
theorem fullAdder_bit_value (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat =
      a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RippleAdder.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 每一位的两根输入线、输出线和进位工作线；列表按小端排列。 -/
structure AddBit where
  x : Wire
  y : Wire
  out : Wire
  carry : Wire

def addWires : List AddBit → List Wire
  | [] => []
  | b :: bs => b.x :: b.y :: b.out :: b.carry :: addWires bs

/-- 正向计算各位，递归返回时按逆序测量清理进位。 -/
def rippleAdder : List AddBit → Wire → Program
  | [], _ => []
  | b :: bs, cin =>
      fullAdder b.x b.y cin b.out b.carry ++ rippleAdder bs b.carry ++
        eraseCarry b.x b.y cin b.carry

theorem sum_value_step (A B C : Bool) (X Y n : Nat) :
    (sumBit A B C).toNat + 2 * ((X + Y + (carryBit A B C).toNat) % 2^n) =
      ((A.toNat + 2 * X) + (B.toNat + 2 * Y) + C.toNat) % 2^(n+1) := by
  have hv := fullAdder_bit_value A B C
  have hs : (sumBit A B C).toNat < 2 := by cases sumBit A B C <;> decide
  have hn : 0 < 2^n := by positivity
  have hr := Nat.mod_lt (X + Y + (carryBit A B C).toNat) hn
  have he : (A.toNat + 2 * X) + (B.toNat + 2 * Y) + C.toNat =
      (sumBit A B C).toNat + 2 * (X + Y + (carryBit A B C).toNat) := by omega
  rw [he, Nat.pow_succ, Nat.mul_comm (2^n) 2]
  have hsmod : (sumBit A B C).toNat < 2 * 2^n := by omega
  have hsmall : (sumBit A B C).toNat +
      2 * ((X + Y + (carryBit A B C).toNat) % 2^n) < 2 * 2^n := by omega
  conv_rhs => rw [Nat.add_mod, Nat.mul_mod_mul_left,
    Nat.mod_eq_of_lt hsmod, Nat.mod_eq_of_lt hsmall]

/-- 非空进位链恰好访问输入进位线和每位的四根线路。 -/
theorem rippleAdder_wires (b : AddBit) (bs : List AddBit) (cin : Wire) :
    wires (rippleAdder (b :: bs) cin) = (cin :: addWires (b :: bs)).toFinset := by
  induction bs generalizing b cin with
  | nil =>
    ext w
    simp [rippleAdder, wires_append, fullAdder_wires, eraseCarry_wires, addWires]
    tauto
  | cons d ds ih =>
    rw [rippleAdder, wires_append, wires_append, fullAdder_wires, ih, eraseCarry_wires]
    ext w
    simp [addWires]
    tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Subtractor.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Layout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 每位的四根线路只存一份，寄存器访问由此派生，长度天然一致。 -/
structure AdderLayout where
  bits : List AddBit
  cin : Wire

namespace AdderLayout

def width (L : AdderLayout) : Nat := L.bits.length
def x (L : AdderLayout) : List Wire := L.bits.map AddBit.x
def y (L : AdderLayout) : List Wire := L.bits.map AddBit.y
def out (L : AdderLayout) : List Wire := L.bits.map AddBit.out
def carry (L : AdderLayout) : List Wire := L.bits.map AddBit.carry
def wires (L : AdderLayout) : List Wire := L.cin :: addWires L.bits

end AdderLayout

def add (L : AdderLayout) : Program := rippleAdder L.bits L.cin

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Select.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 两个候选值与输出位，均按小端排列。 -/
structure SelectBit where
  no : Wire
  yes : Wire
  out : Wire

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModularLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 两个输入、和、模数、候选差、输出，以及两组进位工作线。 -/
inductive ModField where
  | x | y | total | modulus | diff | out | carrySum | carryDiff
  deriving DecidableEq

structure ModBit where
  x : Wire
  y : Wire
  total : Wire
  modulus : Wire
  diff : Wire
  out : Wire
  carrySum : Wire
  carryDiff : Wire

def ModBit.all (b : ModBit) : List Wire :=
  [b.x, b.y, b.total, b.modulus, b.diff, b.out, b.carrySum, b.carryDiff]

/-- high 是额外的最高位，候选差的这个位直接用于选择，不另存 flag。 -/
structure ModLayout where
  low : List ModBit
  high : ModBit
  cinSum : Wire
  cinDiff : Wire

namespace ModLayout

def bits (L : ModLayout) : List ModBit := L.low ++ [L.high]
def wires (L : ModLayout) : List Wire := L.cinSum :: L.cinDiff :: L.bits.flatMap ModBit.all

end ModLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Reduction.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 小端拼接：高段的权重是低段位宽对应的 2 的幂。 -/
theorem regValue_append (lo hi : List Wire) (s : BasisState) :
    regValue (lo ++ hi) s = regValue lo s + 2^lo.length * regValue hi s := by
  induction lo with
  | nil => simp [regValue]
  | cons w lo ih =>
    change (if s w then 1 else 0) + 2 * regValue (lo ++ hi) s =
      ((if s w then 1 else 0) + 2 * regValue lo s) + 2^(lo.length+1) * regValue hi s
    rw [ih, Nat.pow_succ]
    ring

/-- 最高位为 1 恰好表示整个寄存器读值不小于该位的权重。 -/
theorem regValue_highBit (lo : List Wire) (high : Wire) (s : BasisState) :
    s high = true ↔ 2^lo.length ≤ regValue (lo ++ [high]) s := by
  rw [regValue_append]
  have h := regValue_lt lo s
  change s high = true ↔ 2^lo.length ≤ regValue lo s + 2^lo.length * (if s high then 1 else 0)
  cases s high <;> simp [Nat.not_le.mpr h]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModularSteps.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Modular.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModularResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Accumulate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Copy.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

def copyGate (control : Option Wire) (a b : Wire) : Instr :=
  match control with | none => Instr.CX a b | some c => Instr.CCX c a b

/-- 普通复制用 CX；受控复制逐位用 CCX。两者都按 XOR 更新目标。 -/
def copyRegister (control : Option Wire) : List Wire → List Wire → Program
  | a :: src, b :: dst =>
      [copyGate control a b] ++
        copyRegister control src dst
  | _, _ => []

def copyValue (control : Option Wire) (st : BasisState) (X : Nat) : Nat :=
  match control with | none => X | some c => if st c then X else 0

theorem copyRegister_correct (control : Option Wire) (src dst : List Wire)
    (hlen : src.length = dst.length) (hnd : (src ++ dst).Nodup)
    (hc : ∀ c ∈ control, c ∉ dst) (s : State) (m : List Bool) :
    (run (copyRegister control src dst) m s).phase = s.phase ∧
    (∀ w, w ∉ dst → (run (copyRegister control src dst) m s).basis w = s.basis w) ∧
    regValue dst (run (copyRegister control src dst) m s).basis =
      regValue dst s.basis ^^^ copyValue control s.basis (regValue src s.basis) := by
  induction src generalizing dst s with
  | nil =>
    have hd : dst = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst dst
    cases control <;> simp [copyRegister, copyValue, run, regValue]
  | cons a src ih =>
    cases dst with
    | nil => simp at hlen
    | cons b dst =>
      have hlen' : src.length = dst.length := by simpa using hlen
      obtain ⟨hs, hd, hsd⟩ := List.nodup_append'.mp hnd
      have hbs : b ∉ src := by
        intro h; exact List.disjoint_left.mp hsd (List.mem_cons_of_mem a h) (List.mem_cons_self)
      have hbd : b ∉ dst := (List.nodup_cons.mp hd).1
      have ht : (src ++ dst).Nodup :=
        List.nodup_append'.mpr ⟨(List.nodup_cons.mp hs).2, (List.nodup_cons.mp hd).2,
          List.disjoint_left.mpr (fun _ h₁ h₂ => List.disjoint_left.mp hsd (List.mem_cons_of_mem a h₁) (List.mem_cons_of_mem b h₂))⟩
      have hc' : ∀ c ∈ control, c ∉ dst := by
        intro c hm hd; exact hc c hm (by simp [hd])
      have hcb : ∀ c ∈ control, c ≠ b := by
        intro c hm he; exact hc c hm (by simp [he])
      let bit := match control with | none => s.basis a | some c => s.basis c && s.basis a
      let s1 : State := ⟨s.phase, writeBit s.basis b (s.basis b ^^ bit)⟩
      have hfirst : run [copyGate control a b] m s = s1 := by
        cases control <;> rfl
      have hm0 : measurementCount [copyGate control a b] = 0 := by
        cases control <;> rfl
      have hs1 (w : Wire) (hw : w ≠ b) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
      obtain ⟨hp, he, hv⟩ := ih dst hlen' ht hc' s1
      simp only [copyRegister]
      rw [run_append, run_take, hm0, List.drop_zero, hfirst]
      refine ⟨hp, ?_, ?_⟩
      · intro w hw
        have hw' : w ≠ b ∧ w ∉ dst := by simpa only [List.mem_cons, not_or] using hw
        exact (he w hw'.2).trans (hs1 w hw'.1)
      · have hb := he b hbd
        have hsrc : regValue src s1.basis = regValue src s.basis :=
          regValue_congr _ _ _ (fun w hw => hs1 w (by intro h; exact hbs (h ▸ hw)))
        have hdst : regValue dst s1.basis = regValue dst s.basis :=
          regValue_congr _ _ _ (fun w hw => hs1 w (by intro h; exact hbd (h ▸ hw)))
        have hval : copyValue control s1.basis (regValue src s1.basis) =
            copyValue control s.basis (regValue src s.basis) := by
          rw [hsrc]
          cases control with
          | none => rfl
          | some c => simp only [copyValue, hs1 c (hcb c (by simp))]
        change (if (run (copyRegister control src dst) m s1).basis b then 1 else 0) +
          2 * regValue dst (run (copyRegister control src dst) m s1).basis = _
        rw [hb, hv, hdst, hval]
        have hx := xor_value_step (s.basis b) bit (regValue dst s.basis)
          (copyValue control s.basis (regValue src s.basis))
        have hvbit : bit.toNat + 2 * copyValue control s.basis (regValue src s.basis) =
            copyValue control s.basis (regValue (a :: src) s.basis) := by
          cases control with
          | none => simp [bit, copyValue, regValue, Bool.toNat]
          | some c => cases h : s.basis c <;> simp [bit, copyValue, regValue, Bool.toNat, Bool.cond_eq_ite, h]
        rw [hvbit] at hx
        simpa only [s1, writeBit, Function.update_self, regValue, List.foldr_cons,
          Bool.toNat, Bool.cond_eq_ite] using hx

theorem maskedCopy_spec (c : Wire) (src dst : List Wire) (hlen : src.length = dst.length)
    (hnd : (c :: (src ++ dst)).Nodup) (C : Bool) (X O : Nat) :
    (Triple (fun st => (Holds.holds st c C ∧ Holds.holds st src X) ∧ Holds.holds st dst O) (copyRegister (some c) src dst)
      (fun st => (Holds.holds st c C ∧ Holds.holds st src X) ∧ Holds.holds st dst (O ^^^ (if C then X else 0)))) := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hc : c ∉ dst := fun hw => (List.nodup_cons.mp hnd).1 (List.mem_append_right _ hw)
  obtain ⟨hp, he, hv⟩ := copyRegister_correct (some c) src dst hlen (List.nodup_cons.mp hnd).2
    (by simpa using hc) s m
  have hr := regValue_congr src (run (copyRegister (some c) src dst) m s).basis s.basis
    (fun w hw => he w (List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.2 hw))
  exact ⟨hp, ⟨(he c hc).trans h.1.1, hr.trans h.1.2⟩,
    by simpa only [copyValue, h.1.1, h.1.2, h.2] using hv⟩

theorem copyRegister_counts (control : Option Wire) (src dst : List Wire)
    (hlen : src.length = dst.length) :
    toffoliCount (copyRegister control src dst) = (if control.isSome then src.length else 0) ∧
    measurementCount (copyRegister control src dst) = 0 := by
  induction src generalizing dst with
  | nil => cases dst <;> simp_all [copyRegister, toffoliCount, measurementCount]
  | cons a src ih =>
    cases dst with
    | nil => simp at hlen
    | cons b dst =>
      have ht := ih dst (by simpa using hlen)
      cases control <;> simp_all [copyRegister, copyGate, toffoliCount, measurementCount, Nat.add_comm]

theorem copyRegister_wires (control : Option Wire) (src dst : List Wire)
    (hlen : src.length = dst.length) :
    wires (copyRegister control src dst) =
      if src.isEmpty then ∅ else (control.toList ++ src ++ dst).toFinset := by
  induction src generalizing dst with
  | nil => cases dst <;> simp_all [copyRegister, wires]
  | cons a src ih =>
    cases dst with
    | nil => simp at hlen
    | cons b dst =>
      have ht := ih dst (by simpa using hlen)
      simp only [copyRegister, wires_append, ht, List.isEmpty_cons, Bool.false_eq_true, if_false]
      cases src with
      | nil =>
        have hd : dst = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
        subst dst
        cases control <;> ext w <;> simp [copyGate, wires, Instr.wires]
      | cons a' src =>
        cases control <;> ext w <;> simp [copyGate, wires, Instr.wires] <;> tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MaskedConstant.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 经典位为 1 时执行 CX；控制位不属于目标寄存器。 -/
def maskedConstant (c : Wire) : List Wire → Nat → Program
  | [],_ => []
  | w::ws,k => (if k%2=1 then [.CX c w] else [])++maskedConstant c ws (k/2)

theorem maskedConstant_run (c : Wire) (r : List Wire) (k : Nat) (hc : c∉r)
    (s : State) (m : List Bool) :
    run (maskedConstant c r k) m s = if s.basis c then run (xorConstant r k) m s else s := by
  induction r generalizing s k with
  | nil => cases s.basis c <;> simp [maskedConstant,xorConstant,run]
  | cons w ws ih =>
    have hcw : c≠w := fun h => hc (by simp [h])
    have hcs : c∉ws := fun h => hc (by simp [h])
    by_cases hk : k%2=1
    · simp only [maskedConstant,xorConstant,hk,if_true,List.singleton_append,run]
      rw [ih (k/2) hcs]
      cases hs : s.basis c <;> simp [hs,writeBit,hcw]
    · simp only [maskedConstant,xorConstant,hk,if_false,List.nil_append]
      exact ih (k/2) hcs s

theorem maskedConstant_correct (c : Wire) (r : List Wire) (k : Nat)
    (hn : r.Nodup) (hc : c∉r) (hk : k<2^r.length) (s : State) (m : List Bool) :
    (run (maskedConstant c r k) m s).phase=s.phase ∧
    (∀ w∉r,(run (maskedConstant c r k) m s).basis w=s.basis w) ∧
    regValue r (run (maskedConstant c r k) m s).basis=
      regValue r s.basis ^^^ (if s.basis c then k else 0) := by
  rw [maskedConstant_run c r k hc]
  cases hs : s.basis c
  · simp
  · exact xorConstant_correct r hn k hk s m

theorem maskedConstant_counts (c : Wire) (r : List Wire) (k : Nat) :
    toffoliCount (maskedConstant c r k)=0 ∧ measurementCount (maskedConstant c r k)=0 := by
  induction r generalizing k with
  | nil => simp [maskedConstant,toffoliCount,measurementCount]
  | cons w ws ih =>
    by_cases hk : k%2=1 <;> simp [maskedConstant,hk,toffoliCount,measurementCount,ih]

theorem maskedConstant_wires_subset (c : Wire) (r : List Wire) (k : Nat) :
    wires (maskedConstant c r k) ⊆ (c::r).toFinset := by
  induction r generalizing k with
  | nil => simp [maskedConstant,wires]
  | cons w ws ih =>
    intro v hv
    by_cases hk : k%2=1
    · simp only [maskedConstant,hk,if_true,wires_append,wires,Instr.wires,
        Finset.union_empty,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with (rfl|rfl)|hv
      · simp
      · simp
      · have hh := ih (k/2) hv
        simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
        tauto
    · simp only [maskedConstant,hk,if_false,List.nil_append] at hv
      have hh := ih (k/2) hv
      simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
      tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InPlaceAdder.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Instr

/-- fullAdder 的前六门：carry ^= MAJ(a,b,cin)，三个输入恢复，不写和位。 -/
def majority (a b cin carry : Wire) : Program := ([
  CX a b, CX a cin, CCX b cin carry, CX a carry, CX a cin, CX a b
] : Program)

/-- 原地加法 y ← (x + y + cin) mod 2^n：每位先算进位、递归处理高位，
再用现有 eraseCarry 擦除本位进位（此时 x、y、cin 仍是原值），最后把和位写回 y。
最高位只写和位，不算进位，进位链比位宽少一根。 -/
def addInPlace : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      majority a b cin c ++ addInPlace (a' :: as) (b' :: bs) cs c ++
        eraseCarry a b cin c ++ [CX a b, CX cin b]
  | [a], [b], _, cin => [CX a b, CX cin b]
  | _, _, _, _ => []

/-- 进位异或写入 carry，其余状态保持。 -/
theorem majority_correct (a b cin carry : Wire) (hnd : [a, b, cin, carry].Nodup)
    (s : State) (m : List Bool) :
    run (majority a b cin carry) m s =
      ⟨s.phase, writeBit s.basis carry
        (s.basis carry ^^ carryBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨hab, hac, hak⟩, ⟨hbc, hbk⟩, hck⟩ := hnd
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hcb := Ne.symm hbc
  simp only [majority, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwa : w = a <;> by_cases hwb : w = b <;>
    by_cases hwc : w = cin <;> by_cases hwk : w = carry <;>
    simp_all [writeBit, Function.update, carryBit]
  all_goals cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;>
    cases s.basis carry <;> simp_all

/-- 进位链初始为零时：x、cin 保持，y 原地得到低 n 位的和，进位链归零，相位对所有测量记录恢复。 -/
theorem addInPlace_correct (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (s : State) (m : List Bool)
    (hclean : ∀ w ∈ carry, s.basis w = false) :
    (run (addInPlace x y carry cin) m s).phase = s.phase ∧
    (∀ w, w ∉ y → (run (addInPlace x y carry cin) m s).basis w = s.basis w) ∧
    regValue y (run (addInPlace x y carry cin) m s).basis =
      (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^y.length := by
  induction y generalizing x carry cin s m with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    have hcin : cin ∉ a :: as ++ b :: bs ++ carry := (List.nodup_cons.mp hnd).1
    have hrest : ((a :: as) ++ ((b :: bs) ++ carry)).Nodup := by
      simpa only [List.append_assoc] using (List.nodup_cons.mp hnd).2
    obtain ⟨has, hbk, hdisA⟩ := List.nodup_append'.mp hrest
    obtain ⟨hbs, hk, hdisB⟩ := List.nodup_append'.mp hbk
    have hca : cin ≠ a := fun h => hcin (by simp [h])
    have hcb : cin ≠ b := fun h => hcin (by simp [h])
    have hcbs : cin ∉ bs := fun h => hcin (by simp [h])
    have hab : a ≠ b := fun h => List.disjoint_left.mp hdisA List.mem_cons_self (by simp [h])
    have habs : a ∉ bs := fun h => List.disjoint_left.mp hdisA List.mem_cons_self (by simp [h])
    have hbbs : b ∉ bs := (List.nodup_cons.mp hbs).1
    let A := s.basis a
    let B := s.basis b
    let C := s.basis cin
    cases bs with
    | nil =>
      have hx0 : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hx)
      have hc0 : carry = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst hx0 hc0
      simp only [addInPlace, run]
      refine ⟨trivial, ?_, ?_⟩
      · intro w hw
        have hwb : w ≠ b := by simpa using hw
        simp [writeBit, hwb]
      · simp only [regValue, List.foldr_cons, List.foldr_nil, List.length_cons, List.length_nil,
          writeBit, Function.update_self, Function.update_of_ne hcb]
        cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;> simp
    | cons b' bs' =>
      cases as with
      | nil => simp at hx
      | cons a' as' =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
      have hx' : (a' :: as').length = (b' :: bs').length := by simpa using hx
      have hc' : cs.length + 1 = (b' :: bs').length := by simpa using hc
      have hbc : b ≠ c := fun h => List.disjoint_left.mp hdisB List.mem_cons_self (by simp [h])
      have hcbs' : c ∉ b' :: bs' := fun h =>
        List.disjoint_left.mp hdisB (List.mem_cons_of_mem _ h) List.mem_cons_self
      have hccs : c ∉ cs := (List.nodup_cons.mp hk).1
      have hac : a ≠ c := fun h => List.disjoint_left.mp hdisA List.mem_cons_self (by simp [h])
      have hcas : c ∉ a' :: as' := fun h =>
        List.disjoint_left.mp hdisA (List.mem_cons_of_mem _ h) (by simp)
      have hcc : cin ≠ c := fun h => hcin (by simp [h])
      have h4 : [a, b, cin, c].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          not_or, not_false_eq_true, and_true]
        exact ⟨⟨hab, Ne.symm hca, hac⟩, ⟨Ne.symm hcb, hbc⟩, hcc⟩
      have hnd' : (c :: ((a' :: as') ++ (b' :: bs') ++ cs)).Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_, ?_⟩
        · simp only [List.mem_append, not_or]
          exact ⟨⟨hcas, hcbs'⟩, hccs⟩
        · apply List.nodup_append'.mpr
          refine ⟨List.nodup_append'.mpr ⟨(List.nodup_cons.mp has).2, (List.nodup_cons.mp hbs).2, ?_⟩,
            (List.nodup_cons.mp hk).2, ?_⟩
          · exact List.disjoint_left.mpr (fun w hw hw' =>
              List.disjoint_left.mp hdisA (List.mem_cons_of_mem _ hw)
                (List.mem_cons_of_mem _ (List.mem_append_left _ hw')))
          · exact List.disjoint_left.mpr (fun w hw hw' => by
              rcases List.mem_append.mp hw with hw | hw
              · exact List.disjoint_left.mp hdisA (List.mem_cons_of_mem _ hw)
                  (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hw')))
              · exact List.disjoint_left.mp hdisB (List.mem_cons_of_mem _ hw) (List.mem_cons_of_mem _ hw'))
      have hzero : s.basis c = false := hclean c (by simp)
      -- 第一步：进位写入 c
      let s1 : State := ⟨s.phase, writeBit s.basis c (carryBit A B C)⟩
      have hfirst (record : List Bool) : run (majority a b cin c) record s = s1 := by
        rw [majority_correct _ _ _ _ h4]
        simp [s1, hzero, A, B, C]
      have hs1 (w : Wire) (hw : w ≠ c) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
      have hclean' : ∀ d ∈ cs, s1.basis d = false := by
        intro d hd
        rw [hs1 d (fun h => hccs (h ▸ hd))]
        exact hclean d (by simp [hd])
      -- 第二步：高位递归
      obtain ⟨hphase, hsame, hsum⟩ := ih (a' :: as') cs c hnd' hx' hc' s1 m hclean'
      set t := run (addInPlace (a' :: as') (b' :: bs') cs c) m s1 with ht
      have heq (w : Wire) (hw : w ∉ b' :: bs') : t.basis w = s1.basis w := hsame w hw
      have htA : t.basis a = A := by rw [heq a habs, hs1 a hac]
      have htB : t.basis b = B := by rw [heq b hbbs, hs1 b hbc]
      have htC : t.basis cin = C := by rw [heq cin hcbs, hs1 cin hcc]
      have htK : t.basis c = carryBit A B C := by rw [heq c hcbs']; simp [s1, writeBit]
      -- 第三步：擦除本位进位（x、y、cin 仍是原值）
      have herase (record : List Bool) : run (eraseCarry a b cin c) record t =
          ⟨t.phase, writeBit t.basis c false⟩ :=
        eraseCarry_correct _ _ _ _ hac hbc hcc t (by rw [htA, htB, htC, htK]) record
      -- 第四步：写和位
      have hlast (record : List Bool) :
          run [CX a b, CX cin b] record ⟨t.phase, writeBit t.basis c false⟩ =
            ⟨t.phase, writeBit (writeBit t.basis c false) b (sumBit A B C)⟩ := by
        simp only [run]
        apply congrArg (State.mk t.phase)
        funext w
        by_cases hwb : w = b
        · subst hwb
          simp only [writeBit, Function.update_self, Function.update_of_ne hcb,
            Function.update_of_ne hac, Function.update_of_ne hbc, Function.update_of_ne hcc,
            htA, htB, htC, sumBit]
          cases A <;> cases B <;> cases C <;> rfl
        · simp [writeBit, Function.update, hwb]
      -- 组合：按右结合展开，各段记录由 run_take 收回
      have hm0 : measurementCount (majority a b cin c) = 0 := rfl
      simp only [addInPlace, List.append_assoc, run_append, run_take, hm0, List.take_zero,
        List.drop_zero]
      rw [hfirst, ← ht, herase, hlast]
      refine ⟨hphase, ?_, ?_⟩
      · intro w hw
        have hw' : w ≠ b ∧ w ∉ b' :: bs' := by simpa only [List.mem_cons, not_or] using hw
        change (writeBit (writeBit t.basis c false) b (sumBit A B C)) w = s.basis w
        rw [writeBit, Function.update_of_ne hw'.1]
        by_cases hwc : w = c
        · subst hwc; simp [writeBit, hzero]
        · rw [writeBit, Function.update_of_ne hwc, heq w hw'.2, hs1 w hwc]
      · have hbs_t : regValue (b' :: bs') (writeBit (writeBit t.basis c false) b (sumBit A B C)) =
            regValue (b' :: bs') t.basis := by
          apply regValue_congr
          intro w hw
          have hwb : w ≠ b := fun h => hbbs (h ▸ hw)
          have hwc : w ≠ c := fun h => hcbs' (h ▸ hw)
          simp [writeBit, hwb, hwc]
        have hx1 : regValue (a' :: as') s1.basis = regValue (a' :: as') s.basis :=
          regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcas (h ▸ hw)))
        have hy1 : regValue (b' :: bs') s1.basis = regValue (b' :: bs') s.basis :=
          regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcbs' (h ▸ hw)))
        have hc1 : s1.basis c = carryBit A B C := by simp [s1, writeBit]
        change (if (writeBit (writeBit t.basis c false) b (sumBit A B C)) b then 1 else 0) +
            2 * regValue (b' :: bs') (writeBit (writeBit t.basis c false) b (sumBit A B C)) = _
        rw [hbs_t, hsum, hx1, hy1, hc1]
        simp only [writeBit, Function.update_self, List.length_cons]
        have hnum := sum_value_step A B C (regValue (a' :: as') s.basis)
          (regValue (b' :: bs') s.basis) (b' :: bs').length
        simp only [List.length_cons] at hnum
        simpa only [regValue, List.foldr_cons, Bool.toNat, Bool.cond_eq_ite, A, B, C] using hnum


/-- x、cin 保持，y 原地得到低 n 位的和，进位链归零。 -/
theorem addInPlace_spec (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (X Y : Nat) (C : Bool) :
    (Triple (fun st => ((Holds.holds st x X ∧ Holds.holds st y Y) ∧ Holds.holds st cin C) ∧ Holds.holds st carry 0) (addInPlace x y carry cin)
      (fun st => ((Holds.holds st x X ∧ Holds.holds st y ((X + Y + C.toNat) % 2^y.length)) ∧ Holds.holds st cin C) ∧ Holds.holds st carry 0)) := by
  intro s m hP
  simp only [Holds.holds] at hP ⊢
  obtain ⟨⟨⟨hxv, hyv⟩, hcv⟩, hkv⟩ := hP
  have hclean : ∀ w ∈ carry, s.basis w = false := fun w hw => (regValue_zero _ _).mp hkv w hw
  obtain ⟨hp, hsame, hsum⟩ := addInPlace_correct x y carry cin hnd hx hc s m hclean
  have hn := List.nodup_cons.mp hnd
  have hn2 := List.nodup_append'.mp (by simpa only [List.append_assoc] using hn.2 : (x ++ (y ++ carry)).Nodup)
  have hyc := List.nodup_append'.mp hn2.2.1
  have hxy : ∀ w ∈ x, w ∉ y := fun w hw hy => List.disjoint_left.mp hn2.2.2 hw (List.mem_append_left _ hy)
  have hky : ∀ w ∈ carry, w ∉ y := fun w hw hy => List.disjoint_left.mp hyc.2.2 hy hw
  have hciny : cin ∉ y := fun h => hn.1 (by simp [h])
  refine ⟨hp, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => hsame w (hxy w hw))).trans hxv
  · rw [hsum, hxv, hyv, hcv]
  · exact (hsame cin hciny).trans hcv
  · exact (regValue_congr _ _ _ (fun w hw => hsame w (hky w hw))).trans hkv

/-- y ← (y − x) mod 2^n：按位取反、加 x、再取反，¬(¬y + x) = y − x；两层 X 门不计资源。 -/
def subInPlace (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addInPlace x y carry cin ++ notRegister y

private theorem flip_y (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (X Y K : Nat) (C : Bool) :
    (Triple (fun st => ((Holds.holds st x X ∧ Holds.holds st y Y) ∧ Holds.holds st cin C) ∧ Holds.holds st carry K) (notRegister y)
      (fun st => ((Holds.holds st x X ∧ Holds.holds st y (2^y.length - 1 - Y)) ∧ Holds.holds st cin C) ∧ Holds.holds st carry K)) := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hn := List.nodup_cons.mp hnd
  have hn2 := List.nodup_append'.mp (by simpa only [List.append_assoc] using hn.2 : (x ++ (y ++ carry)).Nodup)
  have hyc := List.nodup_append'.mp hn2.2.1
  have hxy : ∀ w ∈ x, w ∉ y := fun w hw hy => List.disjoint_left.mp hn2.2.2 hw (List.mem_append_left _ hy)
  have hky : ∀ w ∈ carry, w ∉ y := fun w hw hy => List.disjoint_left.mp hyc.2.2 hy hw
  have hciny : cin ∉ y := fun hh => hn.1 (by simp [hh])
  rw [notRegister_correct y hyc.1]
  refine ⟨rfl, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => by simp [hxy w hw])).trans h.1.1.1
  · change regValue y (fun w => if w ∈ y then !s.basis w else s.basis w) = _
    rw [regValue_congr y _ (fun w => !s.basis w) (by intro w hw; simp [hw]), regValue_complement, h.1.1.2]
  · simpa [hciny] using h.1.2
  · exact (regValue_congr _ _ _ (fun w hw => by simp [hky w hw])).trans h.2

private theorem complement_sub (X Y N : Nat) (hN : 0 < N) (hX : X < N) (hY : Y < N) :
    N - 1 - ((X + (N - 1 - Y)) % N) = (Y + N - X) % N := by
  by_cases h : X ≤ Y
  · rw [Nat.mod_eq_of_lt (show X + (N - 1 - Y) < N by omega),
      show Y + N - X = (Y - X) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X + (N - 1 - Y) = (X - 1 - Y) + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X - 1 - Y < N by omega), Nat.mod_eq_of_lt (show Y + N - X < N by omega)]
    omega

/-- x 保持，y 原地得到模 2^n 的差，进位链归零。 -/
theorem subInPlace_spec (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (X Y : Nat) :
    (Triple (fun st => ((Holds.holds st x X ∧ Holds.holds st y Y) ∧ Holds.holds st cin false) ∧ Holds.holds st carry 0) (subInPlace x y carry cin)
      (fun st => ((Holds.holds st x X ∧ Holds.holds st y ((Y + 2^y.length - X) % 2^y.length)) ∧ Holds.holds st cin false) ∧ Holds.holds st carry 0)) := by
  intro s m h
  have hX : X < 2^y.length := by
    have hh := regValue_lt x s.basis
    rw [show regValue x s.basis = X from h.1.1.1, hx] at hh
    exact hh
  have hY : Y < 2^y.length := by
    have hh := regValue_lt y s.basis
    rwa [show regValue y s.basis = Y from h.1.1.2] at hh
  have h1 := flip_y x y carry cin hnd X Y 0 false
  have h2 := addInPlace_spec x y carry cin hnd hx hc X (2^y.length - 1 - Y) false
  have h3 := flip_y x y carry cin hnd X ((X + (2^y.length - 1 - Y) + false.toNat) % 2^y.length) 0 false
  simp only [Bool.toNat_false, Nat.add_zero] at h2 h3
  rw [complement_sub X Y (2^y.length) (Nat.two_pow_pos _) hX hY] at h3
  have hall := h1.seq (h2.seq h3)
  rw [subInPlace, List.append_assoc]
  exact hall s m h

theorem addInPlace_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    toffoliCount (addInPlace x y carry cin) = y.length - 1 ∧
    measurementCount (addInPlace x y carry cin) = y.length - 1 := by
  induction y generalizing x carry cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    cases bs with
    | nil =>
      have hx0 : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hx)
      subst hx0
      simp [addInPlace, toffoliCount, measurementCount]
    | cons b' bs' =>
      cases as with
      | nil => simp at hx
      | cons a' as' =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
      have := ih (a' :: as') cs c (by simpa using hx) (by simpa using hc)
      simp only [addInPlace, toffoliCount_append, measurementCount_append, this.1, this.2,
        eraseCarry, majority, toffoliCount, measurementCount, List.length_cons]
      omega

theorem subInPlace_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    toffoliCount (subInPlace x y carry cin) = y.length - 1 ∧
    measurementCount (subInPlace x y carry cin) = y.length - 1 := by
  have h := addInPlace_counts x y carry cin hx hc
  simp only [subInPlace, toffoliCount_append, measurementCount_append,
    (notRegister_counts y).1, (notRegister_counts y).2, h.1, h.2, Nat.zero_add, Nat.add_zero, and_self]

/-- 非空寄存器时，程序恰好触及 cin、x、y 与进位链。 -/
theorem addInPlace_wires (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    wires (addInPlace x y carry cin) = (cin :: (x ++ y ++ carry)).toFinset := by
  induction y generalizing x carry cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    cases bs with
    | nil =>
      have hx0 : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hx)
      have hc0 : carry = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst hx0 hc0
      ext w
      simp [addInPlace, wires, Instr.wires]
    | cons b' bs' =>
      cases as with
      | nil => simp at hx
      | cons a' as' =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
      have := ih (a' :: as') cs c (by simpa using hx) (by simpa using hc)
      have hm : wires (majority a b cin c) = {a, b, cin, c} := by
        ext w; simp [majority, wires, Instr.wires]; tauto
      simp only [addInPlace, wires_append, this, hm, eraseCarry_wires]
      ext w
      simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        List.mem_toFinset, List.mem_cons, List.mem_append, Finset.notMem_empty, or_false]
      tauto

theorem subInPlace_wires (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    wires (subInPlace x y carry cin) = (cin :: (x ++ y ++ carry)).toFinset := by
  rw [subInPlace, wires_append, wires_append, addInPlace_wires x y carry cin hx hc, notRegister_wires]
  ext w
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
  tauto

/-- 受控常数加：T 是零寄存器，受 c 控制装入 K，原地加到 y，再同样受控清 T；不增加 Toffoli。 -/
def maskedAddConst (c : Wire) (T y carry : List Wire) (cin : Wire) (K : Nat) : Program :=
  maskedConstant c T K ++ addInPlace T y carry cin ++ maskedConstant c T K

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedWord.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Clifford source complement controlled by a live sign/control bit. -/
def signComplement (q : Wire) (x : List Wire) : Program := x.map (Instr.CX q)

private theorem signComplement_run (q : Wire) (x : List Wire) (hq : q∉x)
    (s : State) (m : List Bool) :
    run (signComplement q x) m s = if s.basis q then run (notRegister x) m s else s := by
  induction x generalizing s with
  | nil => cases s.basis q <;> rfl
  | cons a x ih =>
    have hqa : q≠a := fun h => hq (by simp [h])
    have hqt : q∉x := fun h => hq (List.mem_cons_of_mem _ h)
    simp only [signComplement,List.map_cons,run]
    change run (signComplement q x) m
      ⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis q)⟩ = _
    rw [ih hqt]
    cases hs : s.basis q <;> simp [hs,writeBit,hqa,notRegister,run]

/-- Exact source complement, with every outside bit and sign restored. -/
theorem signComplement_correct (q : Wire) (x : List Wire) (hn : x.Nodup)
    (hq : q∉x) (s : State) (m : List Bool) :
    (run (signComplement q x) m s).phase=s.phase ∧
      (∀ a,a∉x → (run (signComplement q x) m s).basis a=s.basis a) ∧
      regValue x (run (signComplement q x) m s).basis=
        if s.basis q then 2^x.length-1-regValue x s.basis else regValue x s.basis := by
  rw [signComplement_run q x hq]
  cases hs : s.basis q with
  | false => simp
  | true =>
    rw [notRegister_correct x hn]
    refine ⟨rfl,?_,?_⟩
    · intro a ha
      simp [ha]
    · change regValue x (fun a => if a∈x then !s.basis a else s.basis a)=_
      rw [regValue_congr x _ (fun a => !s.basis a) (by intro a ha; simp [ha]),
        regValue_complement]
      simp

theorem signComplement_counts (q : Wire) (x : List Wire) :
    toffoliCount (signComplement q x)=0 ∧ measurementCount (signComplement q x)=0 := by
  induction x with
  | nil => exact ⟨rfl,rfl⟩
  | cons a x ih => simpa [signComplement,toffoliCount,measurementCount] using ih

theorem signComplement_wires_subset (q : Wire) (x : List Wire) :
    wires (signComplement q x)⊆(q::x).toFinset := by
  induction x with
  | nil => simp [signComplement,wires]
  | cons a x ih =>
    intro b hb
    simp only [signComplement,List.map_cons,wires,Instr.wires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with (rfl|rfl)|hb
    · simp
    · simp
    · have hh := ih hb
      simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
      tauto

def signSourceValue (w : Nat) (Q : Bool) (X : Nat) : Nat :=
  if Q then 2^w-1-X else X

def signedWordValue (w : Nat) (Q : Bool) (X Y : Nat) : Nat :=
  if Q then (Y+2^w-X)%2^w else (Y+X)%2^w

private theorem signSource_twice (w : Nat) (Q : Bool) (X : Nat) (hX : X<2^w) :
    signSourceValue w Q (signSourceValue w Q X)=X := by
  cases Q with
  | false => rfl
  | true =>
    change 2^w-1-(2^w-1-X)=X
    omega

private theorem signSource_add (w : Nat) (Q : Bool) (X Y : Nat) (hX : X<2^w) :
    (signSourceValue w Q X+Y+Q.toNat)%2^w=signedWordValue w Q X Y := by
  cases Q with
  | false => simp [signSourceValue,signedWordValue,Nat.add_comm]
  | true =>
    change (2^w-1-X+Y+1)%2^w=(Y+2^w-X)%2^w
    congr 1
    omega

private theorem complementSource_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (Q : Bool) (X Y : Nat) :
    (Triple (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y Y) ∧ Holds.holds st carry 0) (signComplement q x)
      (fun st => ((Holds.holds st q Q ∧ Holds.holds st x (signSourceValue x.length Q X)) ∧ Holds.holds st y Y) ∧ Holds.holds st carry 0)) := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hl := List.nodup_cons.mp hn
  have hx := (List.nodup_append'.mp (List.nodup_append'.mp hl.2).1).1
  have hq : q∉x := fun hm => hl.1 (by simp [hm])
  have hy : ∀ a∈y,a∉x := by
    intro a ha hm
    exact List.disjoint_left.mp (List.nodup_append'.mp
      (List.nodup_append'.mp hl.2).1).2.2 hm ha
  have hc : ∀ a∈carry,a∉x := by
    intro a ha hm
    exact List.disjoint_left.mp (List.nodup_append'.mp hl.2).2.2
      (List.mem_append_left _ hm) ha
  obtain ⟨hp,he,hv⟩ := signComplement_correct q x hx hq s m
  refine ⟨hp,⟨⟨⟨(he q hq).trans h.1.1.1,?_⟩,?_⟩,?_⟩⟩
  · simpa only [h.1.1.1,h.1.1.2,signSourceValue] using hv
  · exact (regValue_congr _ _ _ (fun a ha => he a (hy a ha))).trans h.1.2
  · exact (regValue_congr _ _ _ (fun a ha => he a (hc a ha))).trans h.2

private theorem signCore_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (X Y : Nat) :
    (Triple (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y Y) ∧ Holds.holds st carry 0) (addInPlace x y carry q)
      (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y ((X+Y+Q.toNat)%2^y.length)) ∧ Holds.holds st carry 0)) := by
  intro s m h
  obtain ⟨hp,ho⟩ := addInPlace_spec x y carry q hn hx hc X Y Q s m
    ⟨⟨⟨h.1.1.2,h.1.2⟩,h.1.1.1⟩,h.2⟩
  exact ⟨hp,⟨⟨⟨ho.1.2,ho.1.1.1⟩,ho.1.1.2⟩,ho.2⟩⟩

/-- q=false adds source x; q=true subtracts x. Control q doubles as carry-in.
The source mask is never materialized. -/
def signedAdd (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ addInPlace x y carry q ++ signComplement q x

/-- All-value modular signed add/sub with source/control/work and sign restored
for every measurement record. Bounds follow from the physical words. -/
theorem signedAdd_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (X Y : Nat) :
    (Triple (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y Y) ∧ Holds.holds st carry 0) (signedAdd q x y carry)
      (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y (signedWordValue y.length Q X Y)) ∧ Holds.holds st carry 0)) := by
  intro s m h
  have hX : X<2^y.length := by
    have hh := regValue_lt x s.basis
    rw [show regValue x s.basis=X from h.1.1.2,hx] at hh
    exact hh
  let V := signSourceValue y.length Q X
  have h1 := complementSource_spec q x y carry hn Q X Y
  rw [hx] at h1
  have h2 := signCore_spec q x y carry hn hx hc Q V Y
  have h3 := complementSource_spec q x y carry hn Q V ((V+Y+Q.toNat)%2^y.length)
  dsimp only [V] at h3
  rw [hx,signSource_twice y.length Q X hX] at h3
  have hall := (h1.seq h2).seq h3
  rw [signSource_add y.length Q X Y hX] at hall
  simpa only [signedAdd,List.append_assoc] using hall s m h

private theorem complementTarget_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (Q : Bool) (X Y : Nat) :
    (Triple (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y Y) ∧ Holds.holds st carry 0) (notRegister y)
      (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y (2^y.length-1-Y)) ∧ Holds.holds st carry 0)) := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hl := List.nodup_cons.mp hn
  have hxy := List.nodup_append'.mp (List.nodup_append'.mp hl.2).1
  have hyc := List.nodup_append'.mp hl.2
  have hqy : q∉y := fun hm => hl.1 (by simp [hm])
  have hcx : ∀ a∈x,a∉y := fun a ha hm => List.disjoint_left.mp hxy.2.2 ha hm
  have hcy : ∀ a∈carry,a∉y := fun a ha hm =>
    List.disjoint_left.mp hyc.2.2 (List.mem_append_right _ hm) ha
  rw [notRegister_correct y hxy.2.1]
  refine ⟨rfl,⟨⟨⟨?_,?_⟩,?_⟩,?_⟩⟩
  · simp [hqy,h.1.1.1]
  · exact (regValue_congr _ _ _ (fun a ha => by simp [hcx a ha])).trans h.1.1.2
  · rw [regValue_congr y _ (fun a => !s.basis a) (by intro a ha; simp [ha]),
      regValue_complement,h.1.2]
  · exact (regValue_congr _ _ _ (fun a ha => by simp [hcy a ha])).trans h.2

private theorem complement_add_sub (N X Y : Nat) (hN : 0<N) (hX : X<N) (hY : Y<N) :
    N-1-((X+(N-1-Y))%N)=(Y+N-X)%N := by
  by_cases h : X≤Y
  · rw [Nat.mod_eq_of_lt (show X+(N-1-Y)<N by omega),
      show Y+N-X=(Y-X)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X+(N-1-Y)=(X-1-Y)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X-1-Y<N by omega),
      Nat.mod_eq_of_lt (show Y+N-X<N by omega)]
    omega

private theorem complement_sub_add (N X Y : Nat) (hN : 0<N) (hX : X<N) (hY : Y<N) :
    N-1-((N-1-Y+N-X)%N)=(Y+X)%N := by
  by_cases hs : Y+X<N
  · rw [show N-1-Y+N-X=(N-1-(Y+X))+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show N-1-(Y+X)<N by omega),Nat.mod_eq_of_lt hs]
    omega
  · rw [Nat.mod_eq_of_lt (show N-1-Y+N-X<N by omega),
      show Y+X=(Y+X-N)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show Y+X-N<N by omega)]
    omega

private theorem signed_complement_inverse (w : Nat) (Q : Bool) (X Y : Nat)
    (hX : X<2^w) (hY : Y<2^w) :
    2^w-1-signedWordValue w Q X (2^w-1-Y)=signedWordValue w (!Q) X Y := by
  cases Q with
  | false =>
    simpa [signedWordValue,Nat.add_comm] using complement_add_sub (2^w) X Y
      (by positivity) hX hY
  | true =>
    simpa [signedWordValue] using complement_sub_add (2^w) X Y (by positivity) hX hY

/-- The inverse uses the identical signed core conjugated by target X gates.
This avoids assuming an unavailable arbitrary-cin subInPlace specification. -/
def signedSub (q : Wire) (x y carry : List Wire) : Program :=
  notRegister y ++ signedAdd q x y carry ++ notRegister y

theorem signedSub_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (X Y : Nat) :
    (Triple (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y Y) ∧ Holds.holds st carry 0) (signedSub q x y carry)
      (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y (signedWordValue y.length (!Q) X Y)) ∧ Holds.holds st carry 0)) := by
  intro s m h
  have hX : X<2^y.length := by
    have hh := regValue_lt x s.basis
    rw [show regValue x s.basis=X from h.1.1.2,hx] at hh
    exact hh
  have hY : Y<2^y.length := by
    have hh := regValue_lt y s.basis
    rw [show regValue y s.basis=Y from h.1.2] at hh
    exact hh
  have h1 := complementTarget_spec q x y carry hn Q X Y
  have h2 := signedAdd_spec q x y carry hn hx hc Q X (2^y.length-1-Y)
  have h3 := complementTarget_spec q x y carry hn Q X
    (signedWordValue y.length Q X (2^y.length-1-Y))
  rw [signed_complement_inverse y.length Q X Y hX hY] at h3
  have hall := (h1.seq h2).seq h3
  simpa only [signedSub,List.append_assoc] using hall s m h

/-- Full-support identities include all measurement correction wires. -/
theorem signedWord_wires (q : Wire) (x y carry : List Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    wires (signedAdd q x y carry)=(q::(x++y++carry)).toFinset ∧
      wires (signedSub q x y carry)=(q::(x++y++carry)).toFinset := by
  have ha := addInPlace_wires x y carry q hx hc
  have hs := signComplement_wires_subset q x
  have hfull : wires (signedAdd q x y carry)=(q::(x++y++carry)).toFinset := by
    simp only [signedAdd,wires_append,ha]
    ext a
    have ht : a∈wires (signComplement q x) → a∈(q::(x++y++carry)).toFinset := by
      intro hm
      have hh := hs hm
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
      tauto
    simp only [Finset.mem_union]
    tauto
  refine ⟨hfull,?_⟩
  simp only [signedSub,wires_append,hfull,notRegister_wires]
  ext a
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

theorem signedWord_counts (q : Wire) (x y carry : List Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    toffoliCount (signedAdd q x y carry)=y.length-1 ∧
      measurementCount (signedAdd q x y carry)=y.length-1 ∧
      toffoliCount (signedSub q x y carry)=y.length-1 ∧
      measurementCount (signedSub q x y carry)=y.length-1 := by
  have hs := signComplement_counts q x
  have ha := addInPlace_counts x y carry q hx hc
  have hn := notRegister_counts y
  simp [signedAdd,signedSub,toffoliCount_append,measurementCount_append,
    hs.1,hs.2,ha.1,ha.2,hn.1,hn.2]

private theorem signedWord_frame_from_spec (q : Wire) (x y carry : List Wire)
    (p : Program) (_hn : (q::(x++y++carry)).Nodup)
    (hp : wires p=(q::(x++y++carry)).toFinset)
    (Q : Bool) (X Y Z : Nat) (hspec :
      (Triple (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y Y) ∧ Holds.holds st carry 0) p
      (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y Z) ∧ Holds.holds st carry 0)))
    (s : State) (m : List Bool) (hq : s.basis q=Q)
    (hx : regValue x s.basis=X) (hy : regValue y s.basis=Y)
    (hc : regValue carry s.basis=0) (a : Wire) (ha : a∉y) :
    (run p m s).basis a=s.basis a := by
  obtain ⟨_,ho⟩ := hspec s m ⟨⟨⟨hq,hx⟩,hy⟩,hc⟩
  by_cases he : a=q
  · subst a
    exact ho.1.1.1.trans hq.symm
  by_cases hex : a∈x
  · exact (regValue_eq_iff _ _ _).mp (ho.1.1.2.trans hx.symm) a hex
  by_cases hec : a∈carry
  · exact (regValue_eq_iff _ _ _).mp (ho.2.trans hc.symm) a hec
  apply run_preserves_outside
  rw [hp]
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

theorem signedWord_frame (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hxy : x.length=y.length)
    (hcarry : carry.length+1=y.length) (Q : Bool) (X Y : Nat)
    (s : State) (m : List Bool) (hq : s.basis q=Q)
    (hx : regValue x s.basis=X) (hy : regValue y s.basis=Y)
    (hc : regValue carry s.basis=0) (a : Wire) (ha : a∉y) :
    (run (signedAdd q x y carry) m s).basis a=s.basis a ∧
      (run (signedSub q x y carry) m s).basis a=s.basis a := by
  have hw := signedWord_wires q x y carry hxy hcarry
  exact ⟨signedWord_frame_from_spec q x y carry _ hn hw.1 Q X Y _
      (signedAdd_spec q x y carry hn hxy hcarry Q X Y) s m hq hx hy hc a ha,
    signedWord_frame_from_spec q x y carry _ hn hw.2 Q X Y _
      (signedSub_spec q x y carry hn hxy hcarry Q X Y) s m hq hx hy hc a ha⟩


/-- Standard two's-complement interpretation of a canonical unsigned word. -/
def signedDecode (w X : Nat) : Int :=
  if X<2^(w-1) then (X:Int) else (X:Int)-(2^w:Nat)

/-- Integer operation implemented by the same live control q. -/
def signedIntegerValue (Q : Bool) (A B : Int) : Int := if Q then B-A else B+A

private theorem word_modulus_double (w : Nat) (hw : 0<w) :
    2^w=2*2^(w-1) := by
  calc
    2^w = 2^((w-1)+1) := by congr 1; omega
    _ = 2^(w-1)*2 := pow_succ _ _
    _ = 2*2^(w-1) := Nat.mul_comm _ _

/-- Decode is a different representative of exactly the same modular word. -/
theorem signedDecode_emod (w X : Nat) :
    signedDecode w X % (2^w:Nat)=(X:Int)%(2^w:Nat) := by
  unfold signedDecode
  split_ifs with h
  · rfl
  · rw [Int.sub_emod]
    simp

/-- The decode interval is half-open, including the most negative value. -/
theorem signedDecode_range (w X : Nat) (hw : 0<w) (hX : X<2^w) :
    -((2^(w-1):Nat):Int)≤signedDecode w X ∧
      signedDecode w X<((2^(w-1):Nat):Int) := by
  have hp := word_modulus_double w hw
  unfold signedDecode
  split_ifs with h
  · omega
  · omega

/-- All canonical words satisfy the integer modular relation, without a
no-overflow hypothesis. Overflow is handled by the full physical word. -/
theorem signedWordValue_emod (w : Nat) (Q : Bool) (X Y : Nat) (hX : X<2^w) :
    (signedWordValue w Q X Y : Int)%(2^w:Nat)=
      signedIntegerValue Q (X:Int) (Y:Int)%(2^w:Nat) := by
  cases Q with
  | false =>
    simp only [signedWordValue,signedIntegerValue,Bool.false_eq_true,if_false]
    rw [Int.natCast_emod]
    simp only [Nat.cast_add,Int.emod_emod]
  | true =>
    simp only [signedWordValue,signedIntegerValue,if_true]
    rw [Int.natCast_emod,Int.emod_emod,
      Nat.cast_sub (show X≤Y+2^w by omega),Nat.cast_add]
    rw [show (Y:Int)+(2^w:Nat)-(X:Int)=((Y:Int)-(X:Int))+(2^w:Nat) by ring]
    rw [Int.add_emod]
    simp

/-- The same modular relation for signed source and target representatives. -/
theorem signedWordValue_decode_emod (w : Nat) (Q : Bool) (X Y : Nat)
    (hX : X<2^w) :
    signedDecode w (signedWordValue w Q X Y)%(2^w:Nat)=
      signedIntegerValue Q (signedDecode w X) (signedDecode w Y)%(2^w:Nat) := by
  rw [signedDecode_emod,signedWordValue_emod w Q X Y hX]
  cases Q with
  | false =>
    simp only [signedIntegerValue,Bool.false_eq_true,if_false]
    calc
      ((Y:Int)+(X:Int))%(2^w:Nat) =
          ((Y:Int)%(2^w:Nat)+(X:Int)%(2^w:Nat))%(2^w:Nat) := Int.add_emod _ _ _
      _ = (signedDecode w Y%(2^w:Nat)+signedDecode w X%(2^w:Nat))%(2^w:Nat) := by
        rw [signedDecode_emod,signedDecode_emod]
      _ = (signedDecode w Y+signedDecode w X)%(2^w:Nat) := (Int.add_emod _ _ _).symm
  | true =>
    simp only [signedIntegerValue,if_true]
    calc
      ((Y:Int)-(X:Int))%(2^w:Nat) =
          ((Y:Int)%(2^w:Nat)-(X:Int)%(2^w:Nat))%(2^w:Nat) := Int.sub_emod _ _ _
      _ = (signedDecode w Y%(2^w:Nat)-signedDecode w X%(2^w:Nat))%(2^w:Nat) := by
        rw [signedDecode_emod,signedDecode_emod]
      _ = (signedDecode w Y-signedDecode w X)%(2^w:Nat) := (Int.sub_emod _ _ _).symm

/-- A proved integer range converts modular gate correctness into exact signed
arithmetic. This internal range is to be discharged by the rail invariant. -/
theorem signedWordValue_lift (w : Nat) (Q : Bool) (X Y : Nat)
    (hw : 0<w) (hX : X<2^w)
    (hlo : -((2^(w-1):Nat):Int)≤
      signedIntegerValue Q (signedDecode w X) (signedDecode w Y))
    (hhi : signedIntegerValue Q (signedDecode w X) (signedDecode w Y)<
      ((2^(w-1):Nat):Int)) :
    signedDecode w (signedWordValue w Q X Y)=
      signedIntegerValue Q (signedDecode w X) (signedDecode w Y) := by
  let H : Int := (2^(w-1):Nat)
  let M : Int := (2^w:Nat)
  let D := signedDecode w (signedWordValue w Q X Y)
  let R := signedIntegerValue Q (signedDecode w X) (signedDecode w Y)
  have hZ : signedWordValue w Q X Y<2^w := by
    unfold signedWordValue
    split <;> exact Nat.mod_lt _ (by positivity)
  have hd := signedDecode_range w (signedWordValue w Q X Y) hw hZ
  have hm : D%M=R%M := signedWordValue_decode_emod w Q X Y hX
  have hpow := congrArg (fun a : Nat => (a:Int)) (word_modulus_double w hw)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hpow
  change -H≤D ∧ D<H at hd
  change -H≤R at hlo
  change R<H at hhi
  change M=2*H at hpow
  have hshift : (D+H)%M=(R+H)%M := by
    calc
      (D+H)%M = (D%M+H%M)%M := Int.add_emod _ _ _
      _ = (R%M+H%M)%M := congrArg (fun a => (a+H%M)%M) hm
      _ = (R+H)%M := (Int.add_emod _ _ _).symm
  have hd0 : 0≤D+H := by omega
  have hdlt : D+H<M := by omega
  have hr0 : 0≤R+H := by omega
  have hrlt : R+H<M := by omega
  rw [Int.emod_eq_of_lt hd0 hdlt,Int.emod_eq_of_lt hr0 hrlt] at hshift
  change D=R
  omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/BitcoinPrimes.lean
noncomputable section

namespace ECDSAAdd
namespace Secp256k1

private theorem lucasFromFactors (n a : Nat) (factors : List Nat)
    (ha : (a : ZMod n) ^ (n - 1) = 1)
    (hn1 : n - 1 ≠ 0)
    (hprod : factors.prod = n - 1)
    (hprime : ∀ q ∈ factors, Nat.Prime q)
    (hpow : ∀ q ∈ factors, (a : ZMod n) ^ ((n - 1) / q) ≠ 1) :
    Nat.Prime n := by
  apply lucas_primality n (a : ZMod n) ha
  intro q hq hqdiv
  have hmemPF : q ∈ Nat.primeFactorsList (n - 1) :=
    (Nat.mem_primeFactorsList_iff_dvd hn1 hq).mpr hqdiv
  have hperm : List.Perm factors (Nat.primeFactorsList (n - 1)) :=
    Nat.primeFactorsList_unique hprod hprime
  exact hpow q (hperm.symm.mem_iff.mp hmemPF)

private theorem prime_cert_01 : Nat.Prime 13 := by
  apply lucasFromFactors 13 2 [2, 2, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_02 : Nat.Prime 17 := by
  apply lucasFromFactors 17 3 [2, 2, 2, 2]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 := by simpa using hq
    rcases hcases with rfl
    · exact Nat.prime_two
  · intro q hq
    have hcases : q = 2 := by simpa using hq
    rcases hcases with rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_03 : Nat.Prime 19 := by
  apply lucasFromFactors 19 2 [2, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_05 : Nat.Prime 29 := by
  apply lucasFromFactors 29 2 [2, 2, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_06 : Nat.Prime 31 := by
  apply lucasFromFactors 31 3 [2, 3, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_08 : Nat.Prime 41 := by
  apply lucasFromFactors 41 6 [2, 2, 2, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_09 : Nat.Prime 53 := by
  apply lucasFromFactors 53 2 [2, 2, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_11 : Nat.Prime 67 := by
  apply lucasFromFactors 67 2 [2, 3, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_13 : Nat.Prime 83 := by
  apply lucasFromFactors 83 2 [2, 41]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_08
  · intro q hq
    have hcases : q = 2 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_14 : Nat.Prime 97 := by
  apply lucasFromFactors 97 5 [2, 2, 2, 2, 2, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_15 : Nat.Prime 101 := by
  apply lucasFromFactors 101 2 [2, 2, 5, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_16 : Nat.Prime 103 := by
  apply lucasFromFactors 103 5 [2, 3, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_19 : Nat.Prime 131 := by
  apply lucasFromFactors 131 2 [2, 5, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_22 : Nat.Prime 239 := by
  apply lucasFromFactors 239 7 [2, 7, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_23 : Nat.Prime 271 := by
  apply lucasFromFactors 271 6 [2, 3, 3, 3, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_25 : Nat.Prime 419 := by
  apply lucasFromFactors 419 2 [2, 11, 19]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 11 ∨ q = 19 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_eleven
    · exact prime_cert_03
  · intro q hq
    have hcases : q = 2 ∨ q = 11 ∨ q = 19 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_26 : Nat.Prime 443 := by
  apply lucasFromFactors 443 2 [2, 13, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 13 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_01
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 13 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_30 : Nat.Prime 887 := by
  apply lucasFromFactors 887 5 [2, 443]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_26
  · intro q hq
    have hcases : q = 2 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_31 : Nat.Prime 971 := by
  apply lucasFromFactors 971 6 [2, 5, 97]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 97 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_14
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 97 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_32 : Nat.Prime 1373 := by
  apply lucasFromFactors 1373 2 [2, 2, 7, 7, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_34 : Nat.Prime 1627 := by
  apply lucasFromFactors 1627 3 [2, 3, 271]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 271 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_23
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 271 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_37 : Nat.Prime 2621 := by
  apply lucasFromFactors 2621 2 [2, 2, 5, 131]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 131 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_19
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 131 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_38 : Nat.Prime 2657 := by
  apply lucasFromFactors 2657 3 [2, 2, 2, 2, 2, 83]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 83 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_13
  · intro q hq
    have hcases : q = 2 ∨ q = 83 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_42 : Nat.Prime 4423 := by
  apply lucasFromFactors 4423 3 [2, 3, 11, 67]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_11
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_43 : Nat.Prime 5323 := by
  apply lucasFromFactors 5323 5 [2, 3, 887]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 887 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_30
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 887 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_44 : Nat.Prime 7723 := by
  apply lucasFromFactors 7723 3 [2, 3, 3, 3, 11, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_46 : Nat.Prime 13441 := by
  apply lucasFromFactors 13441 11 [2, 2, 2, 2, 2, 2, 2, 3, 5, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_48 : Nat.Prime 20113 := by
  apply lucasFromFactors 20113 10 [2, 2, 2, 2, 3, 419]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 419 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_25
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 419 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_49 : Nat.Prime 24809 := by
  apply lucasFromFactors 24809 6 [2, 2, 2, 7, 443]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_26
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_51 : Nat.Prime 41201 := by
  apply lucasFromFactors 41201 3 [2, 2, 2, 2, 5, 5, 103]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 103 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_16
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 103 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_53 : Nat.Prime 96557 := by
  apply lucasFromFactors 96557 2 [2, 2, 101, 239]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 101 ∨ q = 239 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_15
    · exact prime_cert_22
  · intro q hq
    have hcases : q = 2 ∨ q = 101 ∨ q = 239 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_56 : Nat.Prime 1206781 := by
  apply lucasFromFactors 1206781 10 [2, 2, 3, 5, 20113]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 20113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_48
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 20113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_59 : Nat.Prime 7240687 := by
  apply lucasFromFactors 7240687 3 [2, 3, 1206781]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 1206781 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_56
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 1206781 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_60 : Nat.Prime 13331831 := by
  apply lucasFromFactors 13331831 13 [2, 5, 971, 1373]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 971 ∨ q = 1373 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_31
    · exact prime_cert_32
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 971 ∨ q = 1373 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_62 : Nat.Prime 107590001 := by
  apply lucasFromFactors 107590001 3 [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 7 ∨ q = 29 ∨ q = 53 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact Nat.prime_seven
    · exact prime_cert_05
    · exact prime_cert_09
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 7 ∨ q = 29 ∨ q = 53 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_66 : Nat.Prime 173378833005251801 := by
  apply lucasFromFactors 173378833005251801 6 [2, 2, 2, 5, 5, 2621, 24809, 13331831]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 2621 ∨ q = 24809 ∨ q = 13331831 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_37
    · exact prime_cert_49
    · exact prime_cert_60
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 2621 ∨ q = 24809 ∨ q = 13331831 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_68 : Nat.Prime 22149492674086928081353 := by
  apply lucasFromFactors 22149492674086928081353 5 [2, 2, 2, 3, 5323, 173378833005251801]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5323 ∨ q = 173378833005251801 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_43
    · exact prime_cert_66
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5323 ∨ q = 173378833005251801 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_69 : Nat.Prime 132896956044521568488119 := by
  apply lucasFromFactors 132896956044521568488119 6 [2, 3, 22149492674086928081353]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 22149492674086928081353 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_68
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 22149492674086928081353 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_72 : Nat.Prime 255515944373312847190720520512484175977 := by
  apply lucasFromFactors 255515944373312847190720520512484175977 3 [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 11 ∨ q = 1627 ∨ q = 2657 ∨ q = 4423 ∨ q = 41201 ∨ q = 96557 ∨ q = 7240687 ∨ q = 107590001 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact Nat.prime_eleven
    · exact prime_cert_34
    · exact prime_cert_38
    · exact prime_cert_42
    · exact prime_cert_51
    · exact prime_cert_53
    · exact prime_cert_59
    · exact prime_cert_62
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 11 ∨ q = 1627 ∨ q = 2657 ∨ q = 4423 ∨ q = 41201 ∨ q = 96557 ∨ q = 7240687 ∨ q = 107590001 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_73 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  apply lucasFromFactors 205115282021455665897114700593932402728804164701536103180137503955397371 10 [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 31 ∨ q = 7723 ∨ q = 132896956044521568488119 ∨ q = 255515944373312847190720520512484175977 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_05
    · exact prime_cert_06
    · exact prime_cert_44
    · exact prime_cert_69
    · exact prime_cert_72
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 31 ∨ q = 7723 ∨ q = 132896956044521568488119 ∨ q = 255515944373312847190720520512484175977 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


theorem p_prime : Nat.Prime p := by
  apply lucasFromFactors p 3 [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371]
  · unfold p
    reduce_mod_char
  · unfold p
    norm_num
  · unfold p
    norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 13441 ∨ q = 205115282021455665897114700593932402728804164701536103180137503955397371 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_seven
    · exact prime_cert_46
    · exact prime_cert_73
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 13441 ∨ q = 205115282021455665897114700593932402728804164701536103180137503955397371 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold p
      reduce_mod_char
      decide

/-- The fixed secp256k1 base field, derived without exporting the raw primality `Fact`. -/
instance certifiedFpField : Field Fp := by
  letI : Fact (Nat.Prime p) := ⟨p_prime⟩
  infer_instance

/-- The fixed secp256k1 curve is elliptic over the certified base field. -/
instance certifiedCurveIsElliptic : curve.IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr curve_discriminant_ne_zero⟩

end Secp256k1
end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldABI.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.BalancedField
open Secp256k1

/-- Radius of the unique balanced secp256k1 representative. -/
def q : Int := ((p : Int)-1)/2
def h : Int := (q+1)/2
def Centered (z : Int) : Prop := -q≤z ∧ z≤q

def centerFp (x : Fp) : Int :=
  if (x.val : Int)≤q then (x.val : Int) else (x.val : Int)-(p : Int)

def canonicalOfCenter (z : Int) : Nat :=
  (if z<0 then z+(p : Int) else z).toNat

def encodeWord (n : Nat) (z : Int) : Nat := (z % ((2^n : Nat) : Int)).toNat

def centerWord (x : Fp) : Nat := encodeWord 256 (centerFp x)
def ValidCenterWord (w : Nat) : Prop := w<2^256 ∧ Centered (signedDecode 256 w)

 theorem constants : 0<q ∧ (p : Int)=2*q+1 ∧ q%2=1 ∧ q=2*h-1 ∧
    0<h ∧ h<((2^254 : Nat) : Int) ∧ q+1<((2^255 : Nat) : Int) := by
  norm_num [q,h,p]

 theorem centerFp_bounds (x : Fp) : Centered (centerFp x) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hv := ZMod.val_lt x
  have hp := constants
  unfold Centered centerFp
  split_ifs <;> omega

 theorem centerFp_cast (x : Fp) : (centerFp x : Fp)=x := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  unfold centerFp
  split_ifs
  · simp
  · simp [Int.cast_sub]

 theorem centered_cast_unique (A B : Int) (ha : Centered A) (hb : Centered B)
    (he : (A : Fp)=(B : Fp)) : A=B := by
  have hp := constants
  have hm := (ZMod.intCast_eq_intCast_iff' A B p).mp he
  have hs : (A+q)%(p : Int)=(B+q)%(p : Int) := by
    calc
      _ = (A%(p : Int)+q%(p : Int))%(p : Int) := Int.add_emod _ _ _
      _ = (B%(p : Int)+q%(p : Int))%(p : Int) := by rw [hm]
      _ = (B+q)%(p : Int) := (Int.add_emod _ _ _).symm
  unfold Centered at ha hb
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hs
  omega

 theorem centerFp_of_center (z : Int) (hz : Centered z) : centerFp (z : Fp)=z :=
  centered_cast_unique _ _ (centerFp_bounds _) hz (centerFp_cast _)

 theorem centered_residue (z : Int) (hz : Centered z) :
    z%(p : Int)=(if z<0 then z+(p : Int) else z) := by
  have hp := constants
  unfold Centered at hz
  by_cases hn : z<0
  · rw [if_pos hn]
    have he : (z+(p : Int))%(p : Int)=z%(p : Int) := by simp
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at he
    exact he.symm
  · rw [if_neg hn]
    exact Int.emod_eq_of_lt (by omega) (by omega)

 theorem canonicalOfCenter_val (z : Int) (hz : Centered z) :
    canonicalOfCenter z=(z : Fp).val := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hv := ZMod.val_intCast z (n := p)
  rw [centered_residue z hz] at hv
  have hn : 0≤(if z<0 then z+(p : Int) else z) := by
    have hp := constants
    unfold Centered at hz
    split_ifs <;> omega
  have ht := Int.toNat_of_nonneg hn
  unfold canonicalOfCenter
  omega

 theorem canonical_center_inverse (x : Fp) : canonicalOfCenter (centerFp x)=x.val := by
  rw [canonicalOfCenter_val _ (centerFp_bounds x),centerFp_cast]

 theorem center_canonical_inverse (z : Int) (hz : Centered z) :
    centerFp (canonicalOfCenter z : Fp)=z := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  rw [canonicalOfCenter_val z hz,ZMod.natCast_zmod_val,centerFp_of_center z hz]

 theorem encodeWord_bound (n : Nat) (z : Int) : encodeWord n z<2^n := by
  have hm0 : 0<((2^n : Nat) : Int) := by positivity
  have hn := Int.emod_nonneg z (ne_of_gt hm0)
  have hh := Int.emod_lt_of_pos z hm0
  have ht := Int.toNat_of_nonneg hn
  unfold encodeWord
  omega

 theorem encodeWord_cast (n : Nat) (z : Int) :
    (encodeWord n z : Int)=z%((2^n : Nat) : Int) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

/-- The word interface is exact on the full signed interval, for any positive width. -/
 theorem decode_encodeWord (n : Nat) (hn : 0<n) (z : Int)
    (hz : -((2^(n-1) : Nat) : Int)≤z ∧ z<((2^(n-1) : Nat) : Int)) :
    signedDecode n (encodeWord n z)=z := by
  let H : Int := (2^(n-1) : Nat)
  let M : Int := (2^n : Nat)
  let D := signedDecode n (encodeWord n z)
  have hd := signedDecode_range n (encodeWord n z) hn (encodeWord_bound n z)
  have hm : D%M=z%M := by
    rw [signedDecode_emod,encodeWord_cast,Int.emod_emod]
  have hpow : M=2*H := by
    dsimp only [M,H]
    have he : n=(n-1)+1 := by omega
    conv_lhs => rw [he,pow_succ]
    push_cast
    ring
  have hs : (D+H)%M=(z+H)%M := by
    calc
      _ = (D%M+H%M)%M := Int.add_emod _ _ _
      _ = (z%M+H%M)%M := by rw [hm]
      _ = (z+H)%M := (Int.add_emod _ _ _).symm
  change -H≤D ∧ D<H at hd
  change -H≤z ∧ z<H at hz
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hs
  change D=z
  omega

 theorem encode_decodeWord (n w : Nat) (hw : w<2^n) :
    encodeWord n (signedDecode n w)=w := by
  unfold encodeWord
  rw [signedDecode_emod,←Int.natCast_emod,Nat.mod_eq_of_lt hw]
  simp

 theorem centerWord_decode (x : Fp) : signedDecode 256 (centerWord x)=centerFp x := by
  apply decode_encodeWord 256 (by omega)
  have hz := centerFp_bounds x
  have hp := constants
  unfold Centered at hz
  norm_num only [Nat.reduceSub]
  omega

 theorem centerWord_valid (x : Fp) : ValidCenterWord (centerWord x) :=
  ⟨encodeWord_bound _ _,by rw [centerWord_decode]; exact centerFp_bounds x⟩

 theorem validCenterWord_inverse (w : Nat) (hw : ValidCenterWord w) :
    centerWord (signedDecode 256 w : Fp)=w := by
  unfold centerWord
  rw [centerFp_of_center _ hw.2,encode_decodeWord _ _ hw.1]

 theorem validCenterWord_unique (w : Nat) (hw : ValidCenterWord w) (x : Fp)
    (he : (signedDecode 256 w : Fp)=x) : w=centerWord x := by
  rw [←he,validCenterWord_inverse w hw]

 theorem centerWord_sign (x : Fp) :
    2^255≤centerWord x ↔ centerFp x<0 := by
  have hh := centerWord_decode x
  have hb := encodeWord_bound 256 (centerFp x)
  unfold centerWord at hh ⊢
  unfold signedDecode at hh
  norm_num only [Nat.reduceSub] at hh
  split_ifs at hh <;> omega

end ECDSAAdd.Arithmetic.BalancedField
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldHalf.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.BalancedField
open Secp256k1

def signedY (s : Bool) (Y : Int) : Int := if s then -Y else Y
def rawSum (s : Bool) (X Y : Int) : Int := X+signedY s Y
def originalParity (T : Int) : Bool := decide (T%2≠0)

/-- Odd sums are translated by one modulus so their halves are balanced. -/
def evenLift (T : Int) : Int :=
  if T%2=0 then T else if 0≤T then T-(p : Int) else T+(p : Int)
def halfResult (T : Int) : Int := evenLift T/2

 theorem signedY_bounds (s : Bool) (Y : Int) (hy : Centered Y) : Centered (signedY s Y) := by
  cases s <;> simp only [signedY,Bool.false_eq_true,if_false,if_true] <;>
    unfold Centered at hy ⊢ <;> omega

 theorem rawSum_bounds (s : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    -(2*q)≤rawSum s X Y ∧ rawSum s X Y≤2*q := by
  have hs := signedY_bounds s Y hy
  unfold Centered at hx hs
  unfold rawSum
  omega

 theorem evenLift_spec (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    -(2*q)≤evenLift T ∧ evenLift T≤2*q ∧ evenLift T%2=0 := by
  have hp := constants
  unfold evenLift
  split_ifs <;> omega

 theorem halfResult_spec (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    Centered (halfResult T) ∧ 2*halfResult T=evenLift T := by
  have he := evenLift_spec T ht
  unfold halfResult Centered
  omega

 theorem evenLift_cast (T : Int) : (evenLift T : Fp)=(T : Fp) := by
  unfold evenLift
  split_ifs <;> simp [Int.cast_sub,Int.cast_add]

 theorem originalParity_value (T : Int) : T%2=(if originalParity T then 1 else 0) := by
  by_cases he : T%2=0
  · simp [originalParity,he]
  · simp [originalParity,he]
    omega

 theorem halfResult_sign (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    decide (halfResult T<0)=(decide (T<0) ^^ originalParity T) := by
  classical
  have hd := (halfResult_spec T ht).2
  have hp := constants
  by_cases ho : T%2=0
  · rw [evenLift,if_pos ho] at hd
    have he : (halfResult T<0) ↔ T<0 := by omega
    simpa [originalParity,ho] using congrArg (fun P : Prop => decide P) (propext he)
  · rw [evenLift,if_neg ho] at hd
    by_cases hn : T<0
    · rw [if_neg (show ¬0≤T by omega)] at hd
      have hr : ¬halfResult T<0 := by omega
      simp [originalParity,ho,hn,hr]
    · rw [if_pos (show 0≤T by omega)] at hd
      have hr : halfResult T<0 := by omega
      simp [originalParity,ho,hn,hr]

 theorem halfResult_field (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    (halfResult T : Fp)=(T : Fp)/2 := by
  have hd := (halfResult_spec T ht).2
  have hc := congrArg (fun z : Int => (z : Fp)) hd
  change ((2*halfResult T : Int) : Fp)=((evenLift T : Int) : Fp) at hc
  rw [Int.cast_mul,Int.cast_ofNat,evenLift_cast] at hc
  have htwo : (2 : Fp)≠0 := by decide
  apply (eq_div_iff htwo).mpr
  simpa only [mul_comm] using hc

 theorem halfResult_center (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    halfResult T=centerFp ((T : Fp)/2) := by
  rw [←halfResult_field T ht,centerFp_of_center _ (halfResult_spec T ht).1]

/-- Exact signed-half result on every balanced input pair and either sign. -/
 theorem signedHalf_contract (s : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    Centered (halfResult (rawSum s X Y)) ∧
    halfResult (rawSum s X Y)=
      centerFp (((X : Fp)+(if s then -(Y : Fp) else (Y : Fp)))/2) ∧
    2*halfResult (rawSum s X Y)=evenLift (rawSum s X Y) := by
  have hr := halfResult_spec (rawSum s X Y) (rawSum_bounds s X Y hx hy)
  refine ⟨hr.1,?_,hr.2⟩
  have hc := halfResult_center (rawSum s X Y) (rawSum_bounds s X Y hx hy)
  cases s <;> simpa [rawSum,signedY] using hc

/-- The original oddness can be recovered from the updated payload and
unchanged source. No sampling, carry window or convergence assumption appears. -/
 theorem halfResult_parity_interval (s : Bool) (X Y : Int)
    (hx : Centered X) (hy : Centered Y) :
    (rawSum s X Y%2≠0) ↔ q < |2*halfResult (rawSum s X Y)-signedY s Y| := by
  have hd := (halfResult_spec _ (rawSum_bounds s X Y hx hy)).2
  have hp := constants
  have hs : rawSum s X Y=X+signedY s Y := rfl
  unfold Centered at hx
  by_cases ho : rawSum s X Y%2=0
  · rw [evenLift,if_pos ho] at hd
    have hv : 2*halfResult (rawSum s X Y)-signedY s Y=X := by
      omega
    rw [hv]
    have ha : |X|≤q := abs_le.mpr hx
    omega
  · rw [evenLift,if_neg ho] at hd
    by_cases hn : 0≤rawSum s X Y
    · rw [if_pos hn] at hd
      have hv : 2*halfResult (rawSum s X Y)-signedY s Y=X-(p : Int) := by
        omega
      rw [hv,abs_of_neg (show X-(p : Int)<0 by omega)]
      omega
    · rw [if_neg hn] at hd
      have hv : 2*halfResult (rawSum s X Y)-signedY s Y=X+(p : Int) := by
        omega
      rw [hv,abs_of_nonneg (show 0≤X+(p : Int) by omega)]
      omega

 theorem centeredFp_signedHalf (s : Bool) (X Y : Fp) :
    halfResult (rawSum s (centerFp X) (centerFp Y))=
      centerFp ((X+(if s then -Y else Y))/2) := by
  have hh := (signedHalf_contract s (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y)).2.1
  simpa only [centerFp_cast] using hh

end ECDSAAdd.Arithmetic.BalancedField
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldCleanup.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.BalancedField

def negative (R : Int) : Bool := decide (R<0)
def magnitude (R : Int) : Int := if negative R then -R-1 else R
def signBit (R : Int) : Int := if negative R then 1 else 0
def normalizedR (R : Int) : Int := magnitude R-h+signBit R
def viewedY (s : Bool) (R Y : Int) : Int := if s ^^ negative R then -Y-1 else Y
def insertBit (s : Bool) (R : Int) : Int := if !(s ^^ negative R) then 1 else 0
def comparisonLeft (s : Bool) (R : Int) : Int := 2*normalizedR R+insertBit s R

 theorem magnitude_bounds (R : Int) (hr : Centered R) : 0≤magnitude R ∧ magnitude R≤q := by
  unfold Centered at hr
  by_cases hn : R<0 <;> simp [magnitude,negative,hn] <;> omega

 theorem normalizedR_bounds (R : Int) (hr : Centered R) :
    -h≤normalizedR R ∧ normalizedR R<h := by
  have hp := constants
  unfold Centered at hr
  by_cases hn : R<0 <;> simp [normalizedR,magnitude,signBit,negative,hn] <;> omega

 theorem normalizedR_lowword_decode (R : Int) (hr : Centered R) :
    signedDecode 255 (encodeWord 255 (normalizedR R))=normalizedR R := by
  apply decode_encodeWord 255 (by omega)
  have hb := normalizedR_bounds R hr
  have hp := constants
  norm_num only [Nat.reduceSub]
  omega

 theorem comparison_view_bounds (s : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) :
    -(q+1)≤comparisonLeft s R ∧ comparisonLeft s R≤q ∧
    -(q+1)≤viewedY s R Y ∧ viewedY s R Y≤q := by
  have hb := normalizedR_bounds R hr
  have hp := constants
  unfold Centered at hr hy
  cases s <;> by_cases hn : R<0 <;>
    simp [comparisonLeft,normalizedR,magnitude,signBit,insertBit,viewedY,negative,hn] <;> omega

/-- Full-domain direct interval identity, including strict endpoint ties. -/
 theorem cleanup_interval_identity (s : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) :
    q < |2*R-signedY s Y| ↔ viewedY s R Y<comparisonLeft s R := by
  have hp := constants
  have hle : |2*R-signedY s Y|≤q ↔ -q≤2*R-signedY s Y ∧ 2*R-signedY s Y≤q := abs_le
  have hout : q < |2*R-signedY s Y| ↔
      ¬(-q≤2*R-signedY s Y ∧ 2*R-signedY s Y≤q) := by omega
  rw [hout]
  unfold Centered at hr hy
  cases s <;> by_cases hn : R<0 <;>
    simp [comparisonLeft,normalizedR,magnitude,signBit,insertBit,viewedY,negative,signedY,hn] <;> omega

 theorem cleanup_originalParity (s : Bool) (X Y : Int)
    (hx : Centered X) (hy : Centered Y) :
    originalParity (rawSum s X Y)=
      decide (viewedY s (halfResult (rawSum s X Y)) Y<
        comparisonLeft s (halfResult (rawSum s X Y))) := by
  have hr := (halfResult_spec _ (rawSum_bounds s X Y hx hy)).1
  have hi := (halfResult_parity_interval s X Y hx hy).trans
    (cleanup_interval_identity s _ Y hr hy)
  by_cases ht : rawSum s X Y%2≠0
  · have hc := hi.mp ht
    simp [originalParity,ht,hc]
  · have hc : ¬viewedY s (halfResult (rawSum s X Y)) Y<
        comparisonLeft s (halfResult (rawSum s X Y)) := fun hc => ht (hi.mpr hc)
    simp [originalParity,ht,hc]

/-- The low(n−1) adder computes the exact normalized residue; its dividend
is nonnegative and the subtraction cannot underflow. -/
 theorem normalizedR_lowword_arithmetic (R : Int) (hr : Centered R) :
    h.toNat≤(magnitude R).toNat+2^255 ∧
    encodeWord 255 (normalizedR R)=
      (((magnitude R).toNat+2^255-h.toNat+(negative R).toNat)%2^255) := by
  have hb := magnitude_bounds R hr
  have hp := constants
  have hm := Int.toNat_of_nonneg hb.1
  have hh := Int.toNat_of_nonneg (show 0≤h by omega)
  have hsafe : h.toNat≤(magnitude R).toNat+2^255 := by
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hm hh ⊢
    omega
  refine ⟨hsafe,?_⟩
  have hbit : ((negative R).toNat : Int)=signBit R := by
    cases he : negative R <;> simp [signBit,he]
  apply Int.ofNat_inj.mp
  rw [encodeWord_cast,Int.natCast_emod]
  rw [Nat.cast_add,Nat.cast_sub hsafe,Nat.cast_add,hm,hh,hbit]
  have he : magnitude R+((2^255 : Nat) : Int)-h+signBit R=
      normalizedR R+((2^255 : Nat) : Int) := by unfold normalizedR; ring
  rw [he]
  simp

 theorem comparison_words_decode (s : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) :
    signedDecode 256 (encodeWord 256 (comparisonLeft s R))=comparisonLeft s R ∧
    signedDecode 256 (encodeWord 256 (viewedY s R Y))=viewedY s R Y := by
  have hb := comparison_view_bounds s R Y hr hy
  have hp := constants
  constructor <;> apply decode_encodeWord 256 (by omega) <;>
    norm_num only [Nat.reduceSub] <;> omega

end ECDSAAdd.Arithmetic.BalancedField
end

-- source: ECDSAAdd/Arithmetic/Compare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Instr

/-- 读出最高进位：无控制时 target ^= ¬top；有控制时 target ^= control ∧ ¬top。 -/
def flipBelow : Option Wire → Wire → Wire → Program
  | none, top, t => [.X t, .CX top t]
  | some c, top, t => [.CX c t, .CCX c top t]

/-- Gidney 比较链：每位用 majority 算进位、递归到最高位，递归到底时 cin 就是最高进位，
读出后按相反顺序用现有 eraseCarry 擦除。三个输入寄存器全程不变。 -/
def compareChain (control : Option Wire) : List Wire → List Wire → List Wire → Wire → Wire → Program
  | a :: as, b :: bs, c :: cs, cin, target =>
      majority a b cin c ++ compareChain control as bs cs c target ++ eraseCarry a b cin c
  | [], [], [], cin, target => flipBelow control cin target
  | _, _, _, _, _ => []

/-- target ^= [x < y]（有 control 时为 control ∧ [x < y]）：y 按位取反、cin 置 1，
进位链算的是 x + ¬y + 1，最高进位 = [x ≥ y]；读出后擦除并还原 y、cin。 -/
def compareLt (control : Option Wire) (x y carry : List Wire) (cin target : Wire) : Program :=
  notRegister (cin :: y) ++ compareChain control x y carry cin target ++ notRegister (cin :: y)

/-- 与经典常量比较：常量装进零寄存器 T，比较后再卸载。 -/
def compareLtConst (control : Option Wire) (x T carry : List Wire) (cin target : Wire) (K : Nat) : Program :=
  xorConstant T K ++ compareLt control x T carry cin target ++ xorConstant T K

/-- 控制位的值：无控制视为真。 -/
def controlValue : Option Wire → BasisState → Bool
  | none, _ => true
  | some c, st => st c

theorem flipBelow_correct (control : Option Wire) (top t : Wire) (hnt : t ≠ top)
    (hc : ∀ c ∈ control, c ≠ t) (s : State) (m : List Bool) :
    run (flipBelow control top t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (controlValue control s.basis && !s.basis top))⟩ := by
  cases control with
  | none =>
    simp only [flipBelow, run, controlValue]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases hw : w = t
    · subst hw
      simp [writeBit, Ne.symm hnt]
    · simp [writeBit, hw]
  | some c =>
    have hct : c ≠ t := hc c (by simp)
    simp only [flipBelow, run, controlValue]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases hw : w = t
    · subst hw
      simp [writeBit, Ne.symm hnt, hct]
      cases s.basis w <;> cases s.basis c <;> cases s.basis top <;> rfl
    · simp [writeBit, hw]

/-- 进位与和的分解：2^(n+1) ≤ 三输入之和 ⇔ 2^n ≤ 高位之和加进位。 -/
private theorem carry_threshold (A B C : Bool) (X Y n : Nat) :
    (2^(n+1) ≤ (A.toNat + 2*X) + (B.toNat + 2*Y) + C.toNat) ↔
      (2^n ≤ X + Y + (carryBit A B C).toNat) := by
  have hv := fullAdder_bit_value A B C
  have hs : (sumBit A B C).toNat ≤ 1 := by cases sumBit A B C <;> decide
  rw [pow_succ]
  omega

/-- 进位链只改 target：进位辅助位算完又擦回零，x、y、cin 与控制位保持，相位对所有测量记录恢复。 -/
theorem compareChain_correct (control : Option Wire) (x y carry : List Wire) (cin target : Wire)
    (hnd : (target :: cin :: (x ++ y ++ carry)).Nodup)
    (hctl : ∀ c ∈ control, c ∉ target :: cin :: (x ++ y ++ carry))
    (hx : x.length = y.length) (hc : carry.length = y.length) (s : State) (m : List Bool)
    (hclean : ∀ w ∈ carry, s.basis w = false) :
    (run (compareChain control x y carry cin target) m s).phase = s.phase ∧
    (∀ w, w ≠ target → (run (compareChain control x y carry cin target) m s).basis w = s.basis w) ∧
    (run (compareChain control x y carry cin target) m s).basis target =
      (s.basis target ^^ (controlValue control s.basis &&
        !decide (2^y.length ≤ regValue x s.basis + regValue y s.basis + (s.basis cin).toNat))) := by
  induction y generalizing x carry cin s m with
  | nil =>
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero hx
    have hc0 : carry = [] := List.eq_nil_of_length_eq_zero hc
    subst hx0 hc0
    have hnt : target ≠ cin := by
      have := (List.nodup_cons.mp hnd).1; simpa using this
    have hct : ∀ c ∈ control, c ≠ target := fun c hc' hh => hctl c hc' (by simp [hh])
    simp only [compareChain]
    rw [flipBelow_correct control cin target hnt hct]
    refine ⟨rfl, ?_, ?_⟩
    · intro w hw; simp [writeBit, hw]
    · simp only [writeBit, Function.update_self, regValue, List.foldr_nil, Nat.zero_add,
        List.length_nil, pow_zero]
      cases s.basis cin <;> simp
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    cases carry with
    | nil => simp at hc
    | cons c cs =>
    have hx' : as.length = bs.length := by simpa using hx
    have hc' : cs.length = bs.length := by simpa using hc
    -- 互异
    have hcnt := List.nodup_iff_count.mp hnd
    have hnd' : (target :: c :: (as ++ bs ++ cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append] at this ⊢; omega
    have hctl' : ∀ d ∈ control, d ∉ target :: c :: (as ++ bs ++ cs) := by
      intro d hd hm
      apply hctl d hd
      simp only [List.mem_cons, List.mem_append] at hm ⊢
      tauto
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hta : target ≠ a := fun h => by
      have := hcnt a; subst h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
    have htb : target ≠ b := fun h => by
      have := hcnt b; subst h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
    have htcin : target ≠ cin := fun h => by
      have := hcnt cin; subst h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
    have htc : target ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
    have hac : a ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
    have hbc : b ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
    have hcc : cin ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at this; omega
    have hccs : c ∉ cs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1; omega
    let A := s.basis a
    let B := s.basis b
    let C := s.basis cin
    have hzero : s.basis c = false := hclean c (by simp)
    let s1 : State := ⟨s.phase, writeBit s.basis c (carryBit A B C)⟩
    have hfirst (record : List Bool) : run (majority a b cin c) record s = s1 := by
      rw [majority_correct _ _ _ _ h4]; simp [s1, hzero, A, B, C]
    have hs1 (w : Wire) (hw : w ≠ c) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
    have hclean' : ∀ d ∈ cs, s1.basis d = false := by
      intro d hd; rw [hs1 d (fun h => hccs (h ▸ hd))]; exact hclean d (by simp [hd])
    obtain ⟨hp, hsame, hval⟩ := ih as cs c hnd' hctl' hx' hc' s1 m hclean'
    set t := run (compareChain control as bs cs c target) m s1 with ht
    have htA : t.basis a = A := by rw [hsame a hta.symm, hs1 a hac]
    have htB : t.basis b = B := by rw [hsame b htb.symm, hs1 b hbc]
    have htC : t.basis cin = C := by rw [hsame cin htcin.symm, hs1 cin hcc]
    have htK : t.basis c = carryBit A B C := by rw [hsame c htc.symm]; simp [s1, writeBit]
    have herase (record : List Bool) : run (eraseCarry a b cin c) record t =
        ⟨t.phase, writeBit t.basis c false⟩ :=
      eraseCarry_correct _ _ _ _ hac hbc hcc t (by rw [htA, htB, htC, htK]) record
    have hm0 : measurementCount (majority a b cin c) = 0 := rfl
    simp only [compareChain, List.append_assoc, run_append, run_take, hm0, List.take_zero, List.drop_zero]
    rw [hfirst, ← ht, herase]
    refine ⟨hp, ?_, ?_⟩
    · intro w hw
      by_cases hwc : w = c
      · subst hwc; simp [writeBit, hzero]
      · simp only [writeBit, Function.update_of_ne hwc]
        rw [hsame w hw, hs1 w hwc]
    · simp only [writeBit, Function.update_of_ne htc]
      rw [hval]
      have hctlv : controlValue control s1.basis = controlValue control s.basis := by
        cases control with
        | none => rfl
        | some d =>
          have hdc : d ≠ c := fun h => hctl d (by simp) (by simp [h])
          simp [controlValue, s1, writeBit, hdc]
      have hxs : regValue as s1.basis = regValue as s.basis :=
        regValue_congr _ _ _ (fun w hw => hs1 w (fun h => by
          have h1 := hcnt c; have h2 := List.count_pos_iff.mpr (h ▸ hw : c ∈ as)
          simp [List.count_cons] at h1; omega))
      have hys : regValue bs s1.basis = regValue bs s.basis :=
        regValue_congr _ _ _ (fun w hw => hs1 w (fun h => by
          have h1 := hcnt c; have h2 := List.count_pos_iff.mpr (h ▸ hw : c ∈ bs)
          simp [List.count_cons] at h1; omega))
      have hts : s1.basis target = s.basis target := hs1 target htc
      have hc1 : s1.basis c = carryBit A B C := by simp [s1, writeBit]
      rw [hctlv, hxs, hys, hts, hc1]
      have hthr := carry_threshold A B C (regValue as s.basis) (regValue bs s.basis) bs.length
      simp only [regValue, List.foldr_cons, Bool.toNat, Bool.cond_eq_ite, List.length_cons, A, B, C] at hthr ⊢
      simp only [hthr]


/-- 比较器整体：只改 target，x、y、cin、进位链与控制位保持，相位对所有测量记录恢复。 -/
theorem compareLt_correct (control : Option Wire) (x y carry : List Wire) (cin target : Wire)
    (hnd : (target :: cin :: (x ++ y ++ carry)).Nodup)
    (hctl : ∀ c ∈ control, c ∉ target :: cin :: (x ++ y ++ carry))
    (hx : x.length = y.length) (hc : carry.length = y.length) (s : State) (m : List Bool)
    (hcin : s.basis cin = false) (hclean : ∀ w ∈ carry, s.basis w = false) :
    (run (compareLt control x y carry cin target) m s).phase = s.phase ∧
    (∀ w, w ≠ target → (run (compareLt control x y carry cin target) m s).basis w = s.basis w) ∧
    (run (compareLt control x y carry cin target) m s).basis target =
      (s.basis target ^^ (controlValue control s.basis &&
        decide (regValue x s.basis < regValue y s.basis))) := by
  have hcnt := List.nodup_iff_count.mp hnd
  have hny : (cin :: y).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have := hcnt w
    simp only [List.count_cons, List.count_append] at this ⊢; omega
  have htcy : target ∉ cin :: y := fun h => by
    have h1 := hcnt target; have h2 := List.count_pos_iff.mpr h
    simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
  have hxcy : ∀ w ∈ x, w ∉ cin :: y := fun w hw h => by
    have h1 := hcnt w; have h2 := List.count_pos_iff.mpr h; have h3 := List.count_pos_iff.mpr hw
    simp only [List.count_cons, List.count_append] at h1 h2; omega
  have hkcy : ∀ w ∈ carry, w ∉ cin :: y := fun w hw h => by
    have h1 := hcnt w; have h2 := List.count_pos_iff.mpr h; have h3 := List.count_pos_iff.mpr hw
    simp only [List.count_cons, List.count_append] at h1 h2; omega
  have hctlcy : ∀ c ∈ control, c ∉ cin :: y := fun c hc' h => hctl c hc' (by
    simp only [List.mem_cons, List.mem_append] at h ⊢; tauto)
  let s1 : State := ⟨s.phase, fun w => if w ∈ cin :: y then !s.basis w else s.basis w⟩
  have hfirst (record : List Bool) : run (notRegister (cin :: y)) record s = s1 :=
    notRegister_correct _ hny s record
  have hclean1 : ∀ w ∈ carry, s1.basis w = false := fun w hw => by
    simp [s1, hkcy w hw, hclean w hw]
  obtain ⟨hp, hsame, hval⟩ := compareChain_correct control x y carry cin target hnd hctl hx hc s1 m hclean1
  set t := run (compareChain control x y carry cin target) m s1 with ht
  have hX : regValue x s.basis < 2^y.length := by
    have := regValue_lt x s.basis; rwa [hx] at this
  have hY : regValue y s.basis < 2^y.length := regValue_lt y s.basis
  have hx1 : regValue x s1.basis = regValue x s.basis :=
    regValue_congr _ _ _ (fun w hw => by simp [s1, hxcy w hw])
  have hy1 : regValue y s1.basis = 2^y.length - 1 - regValue y s.basis := by
    rw [regValue_congr y _ (fun w => !s.basis w) (by intro w hw; simp [s1, hw]), regValue_complement]
  have hcin1 : s1.basis cin = true := by simp [s1, hcin]
  have htgt1 : s1.basis target = s.basis target := by simp [s1, htcy]
  have hctl1 : controlValue control s1.basis = controlValue control s.basis := by
    cases control with
    | none => rfl
    | some c => simp [controlValue, s1, hctlcy c (by simp)]
  have hm0 : measurementCount (notRegister (cin :: y)) = 0 := (notRegister_counts _).2
  simp only [compareLt, List.append_assoc, run_append, run_take, hm0, List.take_zero, List.drop_zero]
  rw [hfirst, ← ht, notRegister_correct _ hny]
  refine ⟨hp, ?_, ?_⟩
  · intro w hw
    by_cases hm : w ∈ cin :: y
    · simp only [hm, if_true]
      rw [hsame w hw]
      simp [s1, hm]
    · simp only [hm, if_false]
      rw [hsame w hw]
      simp [s1, hm]
  · simp only [htcy, if_false]
    rw [hval, hx1, hy1, hcin1, htgt1, hctl1]
    have hiff : (2^y.length ≤ regValue x s.basis + (2^y.length - 1 - regValue y s.basis) + true.toNat) ↔
        regValue y s.basis ≤ regValue x s.basis := by
      simp only [Bool.toNat_true]; omega
    have hd : (!decide (regValue y s.basis ≤ regValue x s.basis)) =
        decide (regValue x s.basis < regValue y s.basis) := by
      rw [← decide_not]; exact decide_eq_decide.mpr Nat.not_le
    simp only [hiff, hd]

theorem flipBelow_counts (control : Option Wire) (top t : Wire) :
    toffoliCount (flipBelow control top t) = (if control.isSome then 1 else 0) ∧
    measurementCount (flipBelow control top t) = 0 := by
  cases control <;> simp [flipBelow, toffoliCount, measurementCount]

theorem compareChain_counts (control : Option Wire) (x y carry : List Wire) (cin target : Wire)
    (hx : x.length = y.length) (hc : carry.length = y.length) :
    toffoliCount (compareChain control x y carry cin target) = y.length + (if control.isSome then 1 else 0) ∧
    measurementCount (compareChain control x y carry cin target) = y.length := by
  induction y generalizing x carry cin with
  | nil =>
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero hx
    have hc0 : carry = [] := List.eq_nil_of_length_eq_zero hc
    subst hx0 hc0
    simpa [compareChain] using flipBelow_counts control cin target
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    cases carry with
    | nil => simp at hc
    | cons c cs =>
    have := ih as cs c (by simpa using hx) (by simpa using hc)
    simp only [compareChain, toffoliCount_append, measurementCount_append, this.1, this.2,
      majority, eraseCarry, toffoliCount, measurementCount, List.length_cons]
    omega

/-- 比较器 Toffoli = 位宽（受控版 +1），测量 = 位宽。 -/
theorem compareLt_counts (control : Option Wire) (x y carry : List Wire) (cin target : Wire)
    (hx : x.length = y.length) (hc : carry.length = y.length) :
    toffoliCount (compareLt control x y carry cin target) = y.length + (if control.isSome then 1 else 0) ∧
    measurementCount (compareLt control x y carry cin target) = y.length ∧
    ∀ K, toffoliCount (compareLtConst control x y carry cin target K) =
        y.length + (if control.isSome then 1 else 0) ∧
      measurementCount (compareLtConst control x y carry cin target K) = y.length := by
  have h := compareChain_counts control x y carry cin target hx hc
  have hn := notRegister_counts (cin :: y)
  refine ⟨?_, ?_, fun K => ⟨?_, ?_⟩⟩ <;>
    simp only [compareLt, compareLtConst, toffoliCount_append, measurementCount_append,
      h.1, h.2, hn.1, hn.2, (xorConstant_counts _ _).1, (xorConstant_counts _ _).2] <;> omega

theorem flipBelow_wires (control : Option Wire) (top t : Wire) :
    wires (flipBelow control top t) = (control.toList ++ [top, t]).toFinset := by
  cases control with
  | none => ext w; simp [flipBelow, wires, Instr.wires]
  | some c => ext w; simp [flipBelow, wires, Instr.wires]; tauto

theorem compareChain_wires (control : Option Wire) (x y carry : List Wire) (cin target : Wire)
    (hx : x.length = y.length) (hc : carry.length = y.length) :
    wires (compareChain control x y carry cin target) =
      (control.toList ++ target :: cin :: (x ++ y ++ carry)).toFinset := by
  induction y generalizing x carry cin with
  | nil =>
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero hx
    have hc0 : carry = [] := List.eq_nil_of_length_eq_zero hc
    subst hx0 hc0
    rw [compareChain, flipBelow_wires]
    ext w; simp; tauto
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    cases carry with
    | nil => simp at hc
    | cons c cs =>
    have := ih as cs c (by simpa using hx) (by simpa using hc)
    have hm : wires (majority a b cin c) = {a, b, cin, c} := by
      ext w; simp [majority, wires, Instr.wires]; tauto
    simp only [compareChain, wires_append, this, hm, eraseCarry_wires]
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset,
      List.mem_cons, List.mem_append]
    tauto

theorem compareLt_wires (control : Option Wire) (x y carry : List Wire) (cin target : Wire)
    (hx : x.length = y.length) (hc : carry.length = y.length) :
    wires (compareLt control x y carry cin target) =
      (control.toList ++ target :: cin :: (x ++ y ++ carry)).toFinset ∧
    ∀ K, wires (compareLtConst control x y carry cin target K) =
      (control.toList ++ target :: cin :: (x ++ y ++ carry)).toFinset := by
  have hchain := compareChain_wires control x y carry cin target hx hc
  have hsub : (cin :: y).toFinset ⊆ (control.toList ++ target :: cin :: (x ++ y ++ carry)).toFinset := by
    intro w hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hw ⊢
    tauto
  have h1 : wires (compareLt control x y carry cin target) =
      (control.toList ++ target :: cin :: (x ++ y ++ carry)).toFinset := by
    rw [compareLt, wires_append, wires_append, notRegister_wires, hchain,
      Finset.union_eq_right.mpr hsub, Finset.union_eq_left.mpr hsub]
  refine ⟨h1, fun K => ?_⟩
  have hK : wires (xorConstant y K) ⊆ (control.toList ++ target :: cin :: (x ++ y ++ carry)).toFinset := by
    intro w hw
    have := List.mem_toFinset.mp (xorConstant_wires_subset y K hw)
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  rw [compareLtConst, wires_append, wires_append, h1, Finset.union_eq_right.mpr hK,
    Finset.union_eq_left.mpr hK]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ExactBorrowErase.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Borrow-prefix carry without changing either data bit. -/
def borrowMajority (x y cin target : Wire) : Program :=
  [.X x]++majority x y cin target++[.X x]

/-- Immediate Clifford correction for a known borrow. The predicate prefix
is prepared before measuring the target, so no later arithmetic depends on a
saved measurement outcome. -/
def eraseBorrow (x y cin target : Wire) : Program :=
  [.X x]++eraseCarry x y cin target++[.X x]

theorem borrowMajority_correct (x y cin target : Wire)
    (hn : [x,y,cin,target].Nodup) (s : State) (m : List Bool) :
    run (borrowMajority x y cin target) m s=
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ carryBit (!s.basis x) (s.basis y) (s.basis cin))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxy,hxc,hxt⟩,⟨hyc,hyt⟩,hct⟩ := hn
  have hyx := Ne.symm hxy
  have hcx := Ne.symm hxc
  have hcy := Ne.symm hyc
  simp only [borrowMajority,majority,List.cons_append,List.nil_append,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwx : w=x <;> by_cases hwy : w=y <;>
    by_cases hwc : w=cin <;> by_cases hwt : w=target <;>
    simp_all [writeBit,Function.update,carryBit]
  all_goals cases s.basis x <;> cases s.basis y <;> cases s.basis cin <;>
    cases s.basis target <;> simp_all

theorem eraseBorrow_correct (x y cin target : Wire)
    (hx : x≠target) (hy : y≠target) (hc : cin≠target)
    (hxy : x≠y) (hxc : x≠cin)
    (s : State) (m : List Bool)
    (h : s.basis target=carryBit (!s.basis x) (s.basis y) (s.basis cin)) :
    run (eraseBorrow x y cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  let t : State := ⟨s.phase,writeBit s.basis x (!s.basis x)⟩
  have known : t.basis target=carryBit (t.basis x) (t.basis y) (t.basis cin) := by
    simpa [t,writeBit,Ne.symm hx,Ne.symm hxy,Ne.symm hxc] using h
  have clear := eraseCarry_correct x y cin target hx hy hc t known m
  simp only [eraseBorrow,List.cons_append,List.nil_append,run]
  change run (eraseCarry x y cin target++[.X x]) m t=_
  rw [run_append,run_take,clear]
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwt : w=target <;> by_cases hwx : w=x <;>
    simp_all [t,writeBit,Function.update]

/-- Low-to-high borrow preparation, target measurement at the top, then
high-to-low independent measured cleanup. Carries never outlive this block. -/
def eraseLtChain : List Wire → List Wire → List Wire → Wire → Wire → Program
  | a::a'::as,b::b'::bs,c::cs,cin,target =>
      borrowMajority a b cin c++eraseLtChain (a'::as) (b'::bs) cs c target++
        eraseBorrow a b cin c
  | [a],[b],_,cin,target => eraseBorrow a b cin target
  | _,_,_,_,_ => []

theorem borrowMajority_counts (x y cin target : Wire) :
    toffoliCount (borrowMajority x y cin target)=1 ∧
    measurementCount (borrowMajority x y cin target)=0 := by constructor <;> rfl

theorem eraseBorrow_counts (x y cin target : Wire) :
    toffoliCount (eraseBorrow x y cin target)=0 ∧
    measurementCount (eraseBorrow x y cin target)=1 := by constructor <;> rfl

theorem eraseLtChain_counts (x y carry : List Wire) (cin target : Wire)
    (hxy : x.length=y.length) (hc : carry.length+1=y.length) :
    toffoliCount (eraseLtChain x y carry cin target)=y.length-1 ∧
    measurementCount (eraseLtChain x y carry cin target)=y.length := by
  induction y generalizing x carry cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hxy
    | cons a as =>
      cases bs with
      | nil =>
        have ha : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hxy)
        subst ha
        simp [eraseLtChain,eraseBorrow_counts]
      | cons b' bs =>
        cases as with
        | nil => simp at hxy
        | cons a' as =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h := ih (a'::as) cs c (by simpa using hxy) (by simpa using hc)
            rw [eraseLtChain]
            constructor
            · simp only [toffoliCount_append,(borrowMajority_counts _ _ _ _).1,
                (eraseBorrow_counts _ _ _ _).1]
              rw [h.1]
              simp [Nat.add_comm]
            · simp only [measurementCount_append,(borrowMajority_counts _ _ _ _).2,
                (eraseBorrow_counts _ _ _ _).2]
              rw [h.2]
              simp

/-- A borrow out of the low bit is the carry-in for the higher comparison. -/
theorem borrow_threshold (A B C : Bool) (X Y : Nat) :
    (A.toNat+2*X<B.toNat+2*Y+C.toNat) ↔
      X<Y+(carryBit (!A) B C).toNat := by
  cases A <;> cases B <;> cases C <;> simp [carryBit] <;> omega

/-- Exact full-register erasure of a known comparison predicate. The data,
incoming borrow and all other sites are restored; every measurement record
has the same final phase. Only n-1 Toffolis are needed. -/
theorem eraseLtChain_correct (x y carry : List Wire) (cin target : Wire)
    (hnd : (target::cin::(x++y++carry)).Nodup)
    (hxy : x.length=y.length) (hc : carry.length+1=y.length)
    (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (hpred : s.basis target=decide (regValue x s.basis<
      regValue y s.basis+(s.basis cin).toNat)) :
    run (eraseLtChain x y carry cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  induction y generalizing x carry cin s m with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hxy
    | cons a as =>
      have cnt := List.nodup_iff_count.mp hnd
      have hta : target≠a := by
        intro bad; have h := cnt target; subst a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have htb : target≠b := by
        intro bad; have h := cnt target; subst b
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have htcin : target≠cin := by
        intro bad; have h := cnt target; subst cin
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have hab : a≠b := by
        intro bad; have h := cnt b; subst a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have hacin : a≠cin := by
        intro bad; have h := cnt cin; subst a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      cases bs with
      | nil =>
        have ha : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hxy)
        subst ha
        have known : s.basis target=carryBit (!s.basis a) (s.basis b) (s.basis cin) := by
          cases ha : s.basis a <;> cases hb : s.basis b <;> cases hi : s.basis cin <;>
            simpa [regValue,carryBit,ha,hb,hi] using hpred
        exact eraseBorrow_correct a b cin target hta.symm htb.symm htcin.symm
          hab hacin s m known
      | cons b' bs =>
        cases as with
        | nil => simp at hxy
        | cons a' as =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have htc : target≠c := by
              intro bad; have h := cnt target; subst c
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hac : a≠c := by
              intro bad; have h := cnt c; subst a
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hbc : b≠c := by
              intro bad; have h := cnt c; subst b
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcc : cin≠c := by
              intro bad; have h := cnt c; subst cin
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hccs : c∉cs := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcas : c∉a'::as := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hcbs : c∉b'::bs := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have h4 : [a,b,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have hnd' : (target::c::((a'::as)++(b'::bs)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            let K := carryBit (!s.basis a) (s.basis b) (s.basis cin)
            let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
            have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by
              simp [s1,writeBit,hq]
            have hzero := hclean c (by simp)
            have first (record : List Bool) : run (borrowMajority a b cin c) record s=s1 := by
              rw [borrowMajority_correct _ _ _ _ h4]
              simp [s1,K,hzero]
            have clean' : ∀q∈cs,s1.basis q=false := by
              intro q hq
              rw [keep q (fun bad => hccs (bad ▸ hq))]
              exact hclean q (by simp [hq])
            have vx : regValue (a'::as) s1.basis=regValue (a'::as) s.basis :=
              regValue_congr _ _ _ (fun q hq => keep q (fun bad => hcas (bad ▸ hq)))
            have vy : regValue (b'::bs) s1.basis=regValue (b'::bs) s.basis :=
              regValue_congr _ _ _ (fun q hq => keep q (fun bad => hcbs (bad ▸ hq)))
            have pred' : s1.basis target=decide (regValue (a'::as) s1.basis<
                regValue (b'::bs) s1.basis+(s1.basis c).toNat) := by
              rw [keep target htc,vx,vy]
              have hk : s1.basis c=K := by simp [s1,writeBit]
              rw [hk]
              have thr := borrow_threshold (s.basis a) (s.basis b) (s.basis cin)
                (regValue (a'::as) s.basis) (regValue (b'::bs) s.basis)
              have eq : decide (regValue (a::a'::as) s.basis<
                  regValue (b::b'::bs) s.basis+(s.basis cin).toNat)=
                  decide (regValue (a'::as) s.basis<regValue (b'::bs) s.basis+K.toNat) := by
                apply decide_eq_decide.mpr
                simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,K] using thr
              exact hpred.trans eq
            let t : State := ⟨s.phase,writeBit s1.basis target false⟩
            have tail (record : List Bool) :
                run (eraseLtChain (a'::as) (b'::bs) cs c target) record s1=t :=
              ih (a'::as) cs c hnd' (by simpa using hxy) (by simpa using hc)
                s1 record clean' pred'
            have kt (q : Wire) (hqt : q≠target) (hqc : q≠c) : t.basis q=s.basis q := by
              simp [t,writeBit,hqt,keep q hqc]
            have kvalue : t.basis c=K := by simp [t,s1,writeBit,htc.symm]
            have clear (record : List Bool) : run (eraseBorrow a b cin c) record t=
                ⟨s.phase,writeBit t.basis c false⟩ := by
              apply eraseBorrow_correct a b cin c hac hbc hcc hab hacin t record
              rw [kt a hta.symm hac,kt b htb.symm hbc,kt cin htcin.symm hcc,kvalue]
            rw [eraseLtChain]
            simp only [List.append_assoc,run_append,run_take,
              (borrowMajority_counts _ _ _ _).2,List.take_zero,List.drop_zero]
            rw [first,tail,clear]
            apply congrArg (State.mk s.phase)
            funext q
            by_cases hqc : q=c <;> by_cases hqt : q=target <;>
              simp_all [t,s1,writeBit,Function.update]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedAdder.lean
noncomputable section

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- A literal or immutable source bit, optionally complemented. Source wires
may recur in several positions; no source register is materialized. -/
structure MappedBit where
  wire : Option Wire
  flip : Bool

def MappedBit.value (b : MappedBit) (s : BasisState) : Bool :=
  b.flip ^^ (b.wire.map s).getD false

def mappedValue : List MappedBit → BasisState → Nat
  | [],_ => 0
  | b::bs,s => (b.value s).toNat+2*mappedValue bs s

def mappedWires (bits : List MappedBit) : List Wire :=
  bits.flatMap (fun b => b.wire.toList)

/-- One exact carry; inputs return to their entry values before recursion. -/
def mappedMajority (b : MappedBit) (y cin target : Wire) : Program :=
  match b.wire with
  | none => if b.flip then [.CX y target,.CX cin target,.CCX y cin target]
      else [.CCX y cin target]
  | some a => if b.flip then borrowMajority a y cin target
      else majority a y cin target

def mappedEraseCarry (b : MappedBit) (y cin target : Wire) : Program :=
  match b.wire with
  | none => [.measureX target []
      (if b.flip then [.Z y,.Z cin,.CZ y cin] else [.CZ y cin])]
  | some a => if b.flip then eraseBorrow a y cin target
      else eraseCarry a y cin target

def mappedSum (b : MappedBit) (y cin : Wire) : Program :=
  (match b.wire with | none => [] | some a => [.CX a y])++
    (if b.flip then [.X y] else [])++[.CX cin y]

def mappedAdd : List MappedBit → List Wire → List Wire → Wire → Program
  | b::b'::bits,y::y'::ys,c::cs,cin =>
      mappedMajority b y cin c++mappedAdd (b'::bits) (y'::ys) cs c++
        mappedEraseCarry b y cin c++mappedSum b y cin
  | [b],[y],_,cin => mappedSum b y cin
  | _,_,_,_ => []

private theorem mapped_four_nodup (b : MappedBit) (y cin target : Wire)
    (hn : [y,cin,target].Nodup)
    (ha : ∀q∈b.wire,q∉[y,cin,target]) (a : Wire) (hw : b.wire=some a) :
    [a,y,cin,target].Nodup := by
  apply List.nodup_cons.mpr
  exact ⟨ha a (by simp [hw]),hn⟩

theorem mappedMajority_correct (b : MappedBit) (y cin target : Wire)
    (hn : [y,cin,target].Nodup) (ha : ∀q∈b.wire,q∉[y,cin,target])
    (s : State) (m : List Bool) :
    run (mappedMajority b y cin target) m s=
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ carryBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
  cases hw : b.wire with
  | some a =>
    have h4 := mapped_four_nodup b y cin target hn ha a hw
    cases hf : b.flip
    · simpa [mappedMajority,hw,hf,MappedBit.value] using majority_correct a y cin target h4 s m
    · simpa [mappedMajority,hw,hf,MappedBit.value] using borrowMajority_correct a y cin target h4 s m
  | none =>
    have hyt : y≠target := fun bad => (List.nodup_cons.mp hn).1 (by simp [bad])
    have hct : cin≠target := fun bad => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [bad])
    cases hf : b.flip <;>
      simp only [mappedMajority,hw,hf,Bool.false_eq_true,if_false,if_true,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=target <;>
        simp [MappedBit.value,hw,hf,writeBit,Function.update,hq,hyt,hct,carryBit]

theorem mappedEraseCarry_correct (b : MappedBit) (y cin target : Wire)
    (hn : [y,cin,target].Nodup) (ha : ∀q∈b.wire,q∉[y,cin,target])
    (s : State) (m : List Bool)
    (hk : s.basis target=carryBit (b.value s.basis) (s.basis y) (s.basis cin)) :
    run (mappedEraseCarry b y cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  have hyt : y≠target := fun bad => (List.nodup_cons.mp hn).1 (by simp [bad])
  have hct : cin≠target := fun bad => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [bad])
  cases hw : b.wire with
  | some a =>
    have h4 := mapped_four_nodup b y cin target hn ha a hw
    have hx : a≠target := fun bad => (List.nodup_cons.mp h4).1 (by simp [bad])
    have hxy : a≠y := fun bad => (List.nodup_cons.mp h4).1 (by simp [bad])
    have hxc : a≠cin := fun bad => (List.nodup_cons.mp h4).1 (by simp [bad])
    cases hf : b.flip
    · simpa [mappedEraseCarry,hw,hf] using eraseCarry_correct a y cin target hx hyt hct s
        (by simpa [MappedBit.value,hw,hf] using hk) m
    · simpa [mappedEraseCarry,hw,hf] using eraseBorrow_correct a y cin target hx hyt hct
        hxy hxc s m (by simpa [MappedBit.value,hw,hf] using hk)
  | none =>
    cases hf : b.flip <;> cases hm : m.head?.getD false <;>
      simp [mappedEraseCarry,hw,hf,run,measureAndCorrect,correct,writeBit,
        hyt,hct,hk,MappedBit.value,carryBit,hm]
    all_goals cases s.basis y <;> cases s.basis cin <;> simp

theorem mappedSum_correct (b : MappedBit) (y cin : Wire)
    (hc : cin≠y) (ha : ∀q∈b.wire,q≠y) (s : State) (m : List Bool) :
    run (mappedSum b y cin) m s=
      ⟨s.phase,writeBit s.basis y (sumBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
  cases hw : b.wire with
  | none =>
    cases hf : b.flip <;> simp only [mappedSum,hw,hf,Bool.false_eq_true,if_false,
      if_true,List.nil_append,List.cons_append,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=y <;> simp [MappedBit.value,hw,hf,writeBit,Function.update,hq,hc,sumBit]
  | some a =>
    have hay : a≠y := ha a (by simp [hw])
    cases hf : b.flip <;> simp only [mappedSum,hw,hf,Bool.false_eq_true,if_false,
      if_true,List.nil_append,List.cons_append,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=y <;> simp [MappedBit.value,hw,hf,writeBit,Function.update,hq,hc,hay,sumBit]
    all_goals cases s.basis a <;> cases s.basis y <;> cases s.basis cin <;> simp

theorem mappedValue_congr (bits : List MappedBit) (s t : BasisState)
    (h : ∀q∈mappedWires bits,s q=t q) : mappedValue bits s=mappedValue bits t := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.value s=b.value t := by
      cases hw : b.wire
      · simp [MappedBit.value,hw]
      · rename_i q
        simp [MappedBit.value,hw,h q (by simp [mappedWires,hw])]
    rw [mappedValue,mappedValue,hb,ih]
    intro q hq
    exact h q (by simp [mappedWires] at hq ⊢; tauto)

theorem mappedBit_counts (b : MappedBit) (y cin target : Wire) :
    toffoliCount (mappedMajority b y cin target)=1 ∧
    measurementCount (mappedMajority b y cin target)=0 ∧
    toffoliCount (mappedEraseCarry b y cin target)=0 ∧
    measurementCount (mappedEraseCarry b y cin target)=1 ∧
    toffoliCount (mappedSum b y cin)=0 ∧ measurementCount (mappedSum b y cin)=0 := by
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp [mappedMajority,mappedEraseCarry,mappedSum,hw,hf,borrowMajority,eraseBorrow,
      majority,eraseCarry,toffoliCount,measurementCount]

theorem mappedBit_value_congr (b : MappedBit) (s t : BasisState)
    (h : ∀q∈b.wire,s q=t q) : b.value s=b.value t := by
  cases hw : b.wire
  · simp [MappedBit.value,hw]
  · rename_i q
    simp [MappedBit.value,hw,h q (by simp [hw])]

private theorem mapped_head_mem (b : MappedBit) (bits : List MappedBit)
    (q : Wire) (h : q∈b.wire) : q∈mappedWires (b::bits) := by
  cases hw : b.wire with
  | none => simp [hw] at h
  | some a =>
    have eq : a=q := by simpa [hw] using h
    subst a
    simp [mappedWires,hw]

private theorem mapped_tail_mem (b : MappedBit) (bits : List MappedBit)
    (q : Wire) (h : q∈mappedWires bits) : q∈mappedWires (b::bits) := by
  exact List.mem_append_right _ h

/-- Complete measured-adder semantics, allowing repeated immutable source
wires. The whole carry bank is cleaned and all measurement phases restored. -/
theorem mappedAdd_correct (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (mappedAdd bits ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (mappedAdd bits ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (mappedAdd bits ys carry cin) m s).basis=
      (mappedValue bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length := by
  induction ys generalizing bits carry cin s m with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bits =>
      have cnt := List.nodup_iff_count.mp hn
      have hcy : cin≠y := by
        intro bad; have h := cnt y; subst cin
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have bitAway (q : Wire) (hq : q∈b.wire) : q∉cin::((y::ys)++carry) :=
        hs q (mapped_head_mem b bits q hq)
      cases ys with
      | nil =>
        have hb : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst hb
        have ha : ∀q∈b.wire,q≠y := by
          intro q hq bad
          exact bitAway q hq (by simp [bad])
        rw [mappedAdd,mappedSum_correct b y cin hcy ha]
        refine ⟨rfl,?_,?_⟩
        · intro q hq
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
          simp [writeBit,hq]
        · simp only [regValue,List.foldr_cons,List.foldr_nil,writeBit,
            Function.update_self,List.length_cons,List.length_nil,mappedValue]
          cases b.value s.basis <;> cases s.basis y <;> cases s.basis cin <;>
            simp [sumBit,Bool.toNat]
      | cons y' ys =>
        cases bits with
        | nil => simp at hl
        | cons b' bits =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have hyc : y≠c := by
              intro bad; have h := cnt c; subst y
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcc : cin≠c := by
              intro bad; have h := cnt c; subst cin
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcytail : c∉y'::ys := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hyytail : y∉y'::ys := by
              intro bad; have h := cnt y
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hcintail : cin∉y'::ys := by
              intro bad; have h := cnt cin
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hccs : c∉cs := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have h3 : [y,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have hbaway : ∀q∈b.wire,q∉[y,cin,c] := by
              intro q hq bad
              exact bitAway q hq (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
            have nd' : (c::((y'::ys)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            have src' : ∀q∈mappedWires (b'::bits),q∉c::((y'::ys)++cs) := by
              intro q hq bad
              exact hs q (mapped_tail_mem b (b'::bits) q hq)
                (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
            have sourceAwayC (q : Wire) (hq : q∈mappedWires (b::b'::bits)) : q≠c := by
              intro bad
              exact hs q hq (by simp [bad])
            let A := b.value s.basis
            let B := s.basis y
            let C := s.basis cin
            let K := carryBit A B C
            let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
            have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by
              simp [s1,writeBit,hq]
            have hzero := hclean c (by simp)
            have first (record : List Bool) : run (mappedMajority b y cin c) record s=s1 := by
              rw [mappedMajority_correct b y cin c h3 hbaway]
              simp [s1,K,A,B,C,hzero]
            have clean' : ∀q∈cs,s1.basis q=false := by
              intro q hq
              rw [keep q (fun bad => hccs (bad ▸ hq))]
              exact hclean q (by simp [hq])
            obtain ⟨hp,he,hv⟩ := ih (b'::bits) cs c nd' src'
              (by simpa using hl) (by simpa using hc) s1 m clean'
            let t := run (mappedAdd (b'::bits) (y'::ys) cs c) m s1
            have ht : t.phase=s.phase := hp
            have ty : t.basis y=B := (he y hyytail).trans (keep y hyc)
            have ti : t.basis cin=C := (he cin hcintail).trans (keep cin hcc)
            have tk : t.basis c=K := by rw [he c hcytail]; simp [s1,writeBit]
            have ta : b.value t.basis=A := by
              apply mappedBit_value_congr b t.basis s.basis
              intro q hq
              have away := bitAway q hq
              have yt : q∉y'::ys := fun bad => away
                (List.mem_cons_of_mem cin (List.mem_append_left _ (List.mem_cons_of_mem y bad)))
              exact (he q yt).trans (keep q (sourceAwayC q (mapped_head_mem b (b'::bits) q hq)))
            have clear (record : List Bool) : run (mappedEraseCarry b y cin c) record t=
                ⟨t.phase,writeBit t.basis c false⟩ := by
              apply mappedEraseCarry_correct b y cin c h3 hbaway t record
              rw [ta,ty,ti,tk]
            let u : State := ⟨t.phase,writeBit t.basis c false⟩
            have uy : u.basis y=B := by simp [u,writeBit,hyc,ty]
            have ui : u.basis cin=C := by simp [u,writeBit,hcc,ti]
            have ua : b.value u.basis=A := by
              apply Eq.trans (mappedBit_value_congr b u.basis t.basis ?_) ta
              intro q hq
              simp [u,writeBit,sourceAwayC q (mapped_head_mem b (b'::bits) q hq)]
            have finish (record : List Bool) : run (mappedSum b y cin) record u=
                ⟨t.phase,writeBit u.basis y (sumBit A B C)⟩ := by
              rw [mappedSum_correct b y cin hcy (by
                intro q hq bad; exact bitAway q hq (by simp [bad])),ua,uy,ui]
            have mh := mappedBit_counts b y cin c
            rw [mappedAdd]
            simp only [List.append_assoc,run_append,run_take,mh.2.1,List.take_zero,List.drop_zero]
            rw [first]
            change (run (mappedSum b y cin) _ (run (mappedEraseCarry b y cin c) _ t)).phase=_ ∧ _
            rw [clear,finish]
            refine ⟨ht,?_,?_⟩
            · intro q hq
              have hq' : q≠y ∧ q∉y'::ys := by simpa using hq
              by_cases hqc : q=c
              · subst q; simp [u,writeBit,hyc.symm,hzero]
              · simp only [u,writeBit,Function.update_of_ne hq'.1,Function.update_of_ne hqc]
                exact (he q hq'.2).trans (keep q hqc)
            · have tailValue : regValue (y'::ys) (writeBit u.basis y (sumBit A B C))=
                  regValue (y'::ys) t.basis := by
                apply regValue_congr
                intro q hq
                have hqy : q≠y := fun bad => hyytail (bad ▸ hq)
                have hqc : q≠c := fun bad => hcytail (bad ▸ hq)
                simp [u,writeBit,hqy,hqc]
              have sourceValue : mappedValue (b'::bits) s1.basis=mappedValue (b'::bits) s.basis := by
                apply mappedValue_congr
                intro q hq
                exact keep q (sourceAwayC q (mapped_tail_mem b (b'::bits) q hq))
              have yValue : regValue (y'::ys) s1.basis=regValue (y'::ys) s.basis :=
                regValue_congr _ _ _ (fun q hq => keep q (fun bad => hcytail (bad ▸ hq)))
              have kc : s1.basis c=K := by simp [s1,writeBit]
              change (if (writeBit u.basis y (sumBit A B C)) y then 1 else 0)+
                  2*regValue (y'::ys) (writeBit u.basis y (sumBit A B C))=_
              rw [show (writeBit u.basis y (sumBit A B C)) y=sumBit A B C by simp [writeBit],
                tailValue,hv,sourceValue,yValue,kc]
              have num := sum_value_step A B C (mappedValue (b'::bits) s.basis)
                (regValue (y'::ys) s.basis) (y'::ys).length
              simpa only [regValue,List.foldr_cons,mappedValue,List.length_cons,
                Bool.toNat,Bool.cond_eq_ite,A,B,C,K] using num

theorem mappedAdd_counts (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (mappedAdd bits ys carry cin)=ys.length-1 ∧
    measurementCount (mappedAdd bits ys carry cin)=ys.length-1 := by
  induction ys generalizing bits carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bits =>
      cases ys with
      | nil =>
        have hb : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst hb
        simpa [mappedAdd] using
          And.intro (mappedBit_counts b y cin cin).2.2.2.2.1
            (mappedBit_counts b y cin cin).2.2.2.2.2
      | cons y' ys =>
        cases bits with
        | nil => simp at hl
        | cons b' bits =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h := ih (b'::bits) cs c (by simpa using hl) (by simpa using hc)
            have head := mappedBit_counts b y cin c
            rw [mappedAdd]
            constructor
            · simp only [toffoliCount_append,head.1,head.2.2.1,head.2.2.2.2.1]
              rw [h.1]
              simp [Nat.add_comm]
            · simp only [measurementCount_append,head.2.1,head.2.2.2.1,head.2.2.2.2.2]
              rw [h.2]
              simp

theorem mappedBit_wires (b : MappedBit) (y cin target : Wire) :
    wires (mappedMajority b y cin target)⊆(b.wire.toList++[y,cin,target]).toFinset ∧
    wires (mappedEraseCarry b y cin target)⊆(b.wire.toList++[y,cin,target]).toFinset ∧
    wires (mappedSum b y cin)⊆(b.wire.toList++[y,cin]).toFinset := by
  cases hw : b.wire <;> cases hf : b.flip
  all_goals
    constructor
    · intro q hq
      simp [mappedMajority,hw,hf,borrowMajority,majority,wires,Instr.wires] at hq ⊢
      tauto
    · constructor
      · intro q hq
        simp [mappedEraseCarry,hw,hf,eraseBorrow,eraseCarry,wires,Instr.wires,correctionWires] at hq ⊢
        tauto
      · intro q hq
        simp [mappedSum,hw,hf,wires,Instr.wires] at hq ⊢
        tauto

theorem mappedAdd_wires_subset (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (mappedAdd bits ys carry cin)⊆(mappedWires bits++ys++carry++[cin]).toFinset := by
  induction ys generalizing bits carry cin with
  | nil => cases bits <;> simp [mappedAdd,wires]
  | cons y ys ih =>
    cases bits with
    | nil => simp [mappedAdd,wires]
    | cons b bits =>
      cases ys with
      | nil =>
        cases bits with
        | nil =>
          rw [mappedAdd]
          apply Finset.Subset.trans (mappedBit_wires b y cin cin).2.2
          intro q hq
          simp [mappedWires] at hq ⊢
          tauto
        | cons b' bits => simp [mappedAdd,wires]
      | cons y' ys =>
        cases bits with
        | nil => simp [mappedAdd,wires]
        | cons b' bits =>
          cases carry with
          | nil => simp [mappedAdd,wires]
          | cons c cs =>
            let pool := (mappedWires (b::b'::bits)++(y::y'::ys)++(c::cs)++[cin]).toFinset
            have localPool : (b.wire.toList++[y,cin,c]).toFinset⊆pool := by
              intro q hq
              simp [pool,mappedWires] at hq ⊢
              tauto
            have tail : (mappedWires (b'::bits)++(y'::ys)++cs++[c]).toFinset⊆pool := by
              intro q hq
              simp [pool,mappedWires] at hq ⊢
              aesop
            have sum : (b.wire.toList++[y,cin]).toFinset⊆pool := by
              intro q hq
              simp [pool,mappedWires] at hq ⊢
              tauto
            have bit := mappedBit_wires b y cin c
            have headSupport := Finset.Subset.trans bit.1 localPool
            have tailSupport := Finset.Subset.trans (ih (b'::bits) cs c) tail
            have eraseSupport := Finset.Subset.trans bit.2.1 localPool
            have sumSupport := Finset.Subset.trans bit.2.2 sum
            rw [mappedAdd]
            intro q hq
            simp only [wires_append,Finset.mem_union] at hq
            exact by tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Framework/WireRename.lean
noncomputable section

namespace ECDSAAdd

/-- Relabel every gate and every measurement correction together. -/
def renameCorrection (f : Wire → Wire) : Correction → Correction
  | .Z q => .Z (f q)
  | .CZ a b => .CZ (f a) (f b)

def renameInstr (f : Wire → Wire) : Instr → Instr
  | .X q => .X (f q)
  | .CX a q => .CX (f a) (f q)
  | .CCX a b q => .CCX (f a) (f b) (f q)
  | .measureX q c0 c1 =>
      .measureX (f q) (c0.map (renameCorrection f)) (c1.map (renameCorrection f))

def renameProgram (f : Wire → Wire) (p : Program) : Program := p.map (renameInstr f)

def pullState (f : Wire → Wire) (s : State) : State :=
  ⟨s.phase,fun q => s.basis (f q)⟩

theorem State.extensionality (s t : State) (hp : s.phase=t.phase)
    (hb : s.basis=t.basis) : s=t := by
  cases s
  cases t
  simp_all

theorem pullState_write (f : Wire → Wire) (hf : Function.Injective f)
    (ph : Bool) (bits : BasisState) (q : Wire) (v : Bool) :
    pullState f ⟨ph,writeBit bits (f q) v⟩ =
      ⟨ph,writeBit (fun j => bits (f j)) q v⟩ := by
  unfold pullState
  congr 1
  funext j
  simp [writeBit,Function.update,hf.eq_iff]

theorem pullState_correct (f : Wire → Wire) (cs : List Correction) (s : State) :
    pullState f (correct (cs.map (renameCorrection f)) s) =
      correct cs (pullState f s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp only [List.map_cons,renameCorrection,correct] <;>
      rw [ih] <;> rfl

theorem pullState_measure (f : Wire → Wire) (hf : Function.Injective f)
    (q : Wire) (c0 c1 : List Correction) (m : Bool) (s : State) :
    pullState f (measureAndCorrect (f q)
      (c0.map (renameCorrection f)) (c1.map (renameCorrection f)) m s) =
      measureAndCorrect q c0 c1 m (pullState f s) := by
  cases m <;> simp only [measureAndCorrect,Bool.false_eq_true,if_false,if_true]
  all_goals
    rw [pullState_correct,pullState_write f hf]
    rfl

/-- Renaming preserves basis behavior and phase on all measurement records.
The injectivity premise forbids aliasing distinct circuit wires. -/
theorem run_rename (f : Wire → Wire) (hf : Function.Injective f)
    (p : Program) (m : List Bool) (s : State) :
    pullState f (run (renameProgram f p) m s) = run p m (pullState f s) := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [renameProgram,List.map_cons,renameInstr,run]
    all_goals change pullState f (run (renameProgram f p) _ _) = _
    all_goals rw [ih]
    all_goals first
      | rw [pullState_write f hf]; rfl
      | rw [pullState_measure f hf]

theorem renameProgram_counts (f : Wire → Wire) (p : Program) :
    toffoliCount (renameProgram f p) = toffoliCount p ∧
      measurementCount (renameProgram f p) = measurementCount p := by
  induction p with
  | nil => exact ⟨rfl,rfl⟩
  | cons i p ih =>
    simp only [renameProgram] at ih
    cases i <;> simp [renameProgram,renameInstr,toffoliCount,measurementCount,ih]

theorem renameCorrection_support (f : Wire → Wire) (cs : List Correction) :
    correctionWires (cs.map (renameCorrection f)) = (correctionWires cs).image f := by
  induction cs with
  | nil => simp [correctionWires]
  | cons c cs ih =>
    cases c <;> simp [renameCorrection,correctionWires,ih]

theorem renameInstr_support (f : Wire → Wire) (i : Instr) :
    (renameInstr f i).wires=i.wires.image f := by
  cases i <;> simp [renameInstr,Instr.wires,renameCorrection_support,Finset.image_union]

theorem renameProgram_support (f : Wire → Wire) (p : Program) :
    wires (renameProgram f p)=(wires p).image f := by
  induction p with
  | nil => simp [renameProgram,wires]
  | cons i p ih =>
    simp only [renameProgram] at ih
    simp [renameProgram,wires,renameInstr_support,ih,Finset.image_union]

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/LiteralConstAddCells.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def literalConstSum (bit : Bool) (x cin : Wire) : Program :=
  (if bit then [.X x] else [])++[.CX cin x]

/-- Updated-X carry predicates, exactly matching the direct interval adder. -/
def literalConstCarry (bit : Bool) (x cin cout : Wire) : Program :=
  if bit then [.X cout,.X cin,.CCX cin x cout,.X cin]
  else [.X x,.CCX cin x cout,.X x]

def literalConstStep (bit : Bool) (x cin cout : Wire) : Program :=
  literalConstSum bit x cin++literalConstCarry bit x cin cout

def literalConstErase (bit : Bool) (x cin cout one : Wire) : Program :=
  if bit then [.X one,.measureX cout [] [.Z one,.Z x,.CZ x cin],.X one]
  else [.measureX cout [] [.Z cin,.CZ x cin]]

def literalCarryPredicate (bit x cin : Bool) : Bool :=
  if bit then !x || cin else !x && cin

theorem literalConstSum_correct (bit : Bool) (x cin : Wire) (hn : x≠cin)
    (s : State) (m : List Bool) :
    run (literalConstSum bit x cin) m s=
      ⟨s.phase,writeBit s.basis x (sumBit (s.basis x) bit (s.basis cin))⟩ := by
  cases bit <;> simp only [literalConstSum,Bool.false_eq_true,if_false,if_true,
    List.nil_append,List.singleton_append,run]
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=x <;> simp [writeBit,Function.update,hq,Ne.symm hn,sumBit]

theorem literalConstStep_correct (bit : Bool) (x cin cout : Wire)
    (hn : [x,cin,cout].Nodup) (s : State) (m : List Bool) (hc : s.basis cout=false) :
    run (literalConstStep bit x cin cout) m s=
      ⟨s.phase,writeBit (writeBit s.basis x (sumBit (s.basis x) bit (s.basis cin)))
        cout (carryBit (s.basis x) bit (s.basis cin))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxi,hxc⟩,hic⟩ := hn
  have hix := Ne.symm hxi
  have hcx := Ne.symm hxc
  have hci := Ne.symm hic
  cases bit <;> cases hx : s.basis x <;> cases hi : s.basis cin
  all_goals
    simp only [literalConstStep,literalConstSum,literalConstCarry,
      Bool.false_eq_true,if_false,if_true,List.cons_append,List.nil_append,run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqx : q=x <;> by_cases hqi : q=cin <;> by_cases hqc : q=cout <;>
      simp_all [writeBit,Function.update,sumBit,carryBit]

theorem literalCarryPredicate_sum (A B C : Bool) :
    literalCarryPredicate B (sumBit A B C) C=carryBit A B C := by
  cases A <;> cases B <;> cases C <;> rfl

/-- One supplies the literal phase correction only during the measurement.
Every record, including outcome one, restores phase and the clean One wire. -/
theorem literalConstErase_correct (bit : Bool) (x cin cout one : Wire)
    (hn : [one,x,cin,cout].Nodup) (s : State) (m : List Bool)
    (ho : s.basis one=false)
    (hc : s.basis cout=literalCarryPredicate bit (s.basis x) (s.basis cin)) :
    run (literalConstErase bit x cin cout one) m s=
      ⟨s.phase,writeBit s.basis cout false⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hox,hoi,hoc⟩,⟨hxi,hxc⟩,hic⟩ := hn
  have hxo := Ne.symm hox
  have hio := Ne.symm hoi
  have hco := Ne.symm hoc
  cases bit <;> cases hm : m.headD false <;> cases hx : s.basis x <;> cases hi : s.basis cin
  all_goals
    simp only [literalCarryPredicate,Bool.false_eq_true,if_false,if_true,
      Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_or,Bool.true_or] at hc
    apply State.extensionality
    · simp_all [literalConstErase,run,measureAndCorrect,correct,writeBit,Function.update]
    · funext q
      by_cases hqo : q=one <;> by_cases hqc : q=cout <;>
        simp_all [literalConstErase,run,measureAndCorrect,correct,writeBit,Function.update]

theorem literalConstCell_counts (bit : Bool) (x cin cout one : Wire) :
    toffoliCount (literalConstStep bit x cin cout)=1 ∧
    measurementCount (literalConstStep bit x cin cout)=0 ∧
    toffoliCount (literalConstErase bit x cin cout one)=0 ∧
    measurementCount (literalConstErase bit x cin cout one)=1 ∧
    toffoliCount (literalConstSum bit x cin)=0 ∧
    measurementCount (literalConstSum bit x cin)=0 := by
  cases bit <;> simp [literalConstStep,literalConstSum,literalConstCarry,literalConstErase,
    toffoliCount,measurementCount]

theorem literalConstCell_wires (bit : Bool) (x cin cout one : Wire) :
    wires (literalConstStep bit x cin cout)⊆[one,cin,x,cout].toFinset ∧
    wires (literalConstErase bit x cin cout one)⊆[one,cin,x,cout].toFinset ∧
    wires (literalConstSum bit x cin)⊆[one,cin,x,cout].toFinset := by
  cases bit <;> simp [literalConstStep,literalConstSum,literalConstCarry,literalConstErase,
    wires,Instr.wires,correctionWires,Finset.subset_iff]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/LiteralConstAdd.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- In-place literal addition with arbitrary quantum carry-in. Carries are
computed from updated low bits, then independently measured in reverse order.
One is a single clean flag, not a materialized constant register. -/
def literalConstAdd : List Wire → List Wire → Wire → Wire → Nat → Program
  | x::x'::xs,c::cs,cin,one,k =>
      literalConstStep (decide (k%2=1)) x cin c ++
        literalConstAdd (x'::xs) cs c one (k/2) ++
        literalConstErase (decide (k%2=1)) x cin c one
  | [x],_,cin,_,k => literalConstSum (decide (k%2=1)) x cin
  | _,_,_,_,_ => []

theorem literalConstAdd_counts (xs carry : List Wire) (cin one : Wire) (k : Nat)
    (hc : carry.length+1=xs.length) :
    toffoliCount (literalConstAdd xs carry cin one k)=xs.length-1 ∧
    measurementCount (literalConstAdd xs carry cin one k)=xs.length-1 := by
  induction xs generalizing carry cin k with
  | nil => simp at hc
  | cons x xs ih =>
    cases xs with
    | nil =>
      have h := literalConstCell_counts (decide (k%2=1)) x cin cin one
      simpa [literalConstAdd] using And.intro h.2.2.2.2.1 h.2.2.2.2.2
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have h := literalConstCell_counts (decide (k%2=1)) x cin c one
        have hh := ih cs c (k/2) (by simpa using hc)
        simp [literalConstAdd,toffoliCount_append,measurementCount_append,
          h.1,h.2.1,h.2.2.1,h.2.2.2.1,hh.1,hh.2,Nat.add_comm]

theorem literalConstAdd_wires (xs carry : List Wire) (cin one : Wire) (k : Nat) :
    wires (literalConstAdd xs carry cin one k)⊆(one::cin::(xs++carry)).toFinset := by
  induction xs generalizing carry cin k with
  | nil => simp [literalConstAdd,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      intro q hq
      have h := (literalConstCell_wires (decide (k%2=1)) x cin cin one).2.2 hq
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
      tauto
    | cons x' xs =>
      cases carry with
      | nil => simp [literalConstAdd,wires]
      | cons c cs =>
        intro q hq
        simp only [literalConstAdd,wires_append,Finset.mem_union] at hq
        have hh := literalConstCell_wires (decide (k%2=1)) x cin c one
        rcases hq with (hq|hq)|hq
        · have h := hh.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append]; tauto
        · have h := ih cs c (k/2) hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
        · have h := hh.2.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append]; tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/LiteralConstAddProof.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

private theorem literal_split (k : Nat) : (decide (k%2=1)).toNat+2*(k/2)=k := by
  have h := Nat.mod_add_div k 2
  have hm := Nat.mod_lt k (by decide : 0<2)
  by_cases ho : k%2=1 <;> simp [ho] <;> omega

/-- Exact arbitrary-word addition for every literal k, with unrestricted
incoming phase and carry-in, and independent arbitrary measurement records.
No canonical-input bound or literal-size restriction is imposed. -/
theorem literalConstAdd_correct (xs carry : List Wire) (cin one : Wire) (k : Nat)
    (hn : (one::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length)
    (s : State) (m : List Bool) (ho : s.basis one=false)
    (hclean : ∀ q∈carry,s.basis q=false) :
    (run (literalConstAdd xs carry cin one k) m s).phase=s.phase ∧
    (∀ q,q∉xs → (run (literalConstAdd xs carry cin one k) m s).basis q=s.basis q) ∧
    regValue xs (run (literalConstAdd xs carry cin one k) m s).basis=
      (regValue xs s.basis+k+(s.basis cin).toNat)%2^xs.length := by
  induction xs generalizing carry cin k s m with
  | nil => simp at hc
  | cons x xs ih =>
    have hd := List.nodup_cons.mp hn
    have hi := List.nodup_cons.mp hd.2
    have words := List.nodup_append'.mp hi.2
    have hxi : x≠cin := by intro h; exact hi.1 (by simp [h])
    cases xs with
    | nil =>
      rw [literalConstAdd,literalConstSum_correct _ _ _ hxi]
      refine ⟨rfl,?_,?_⟩
      · intro q hq
        have hqx : q≠x := by simpa using hq
        simp [writeBit,hqx]
      · have hcol := sum_value_step (s.basis x) (decide (k%2=1)) (s.basis cin) 0 (k/2) 0
        rw [literal_split] at hcol
        simpa [regValue,writeBit,Bool.toNat,Bool.cond_eq_ite,Nat.mod_one] using hcol
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have count := List.nodup_iff_count.mp hn
        have nd : [one,x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q; have hh := count q
          simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
          omega
        have tailND : (one::c::((x'::xs)++cs)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q; have hh := count q
          simp only [List.count_cons,List.count_append] at hh ⊢
          omega
        have stepND : [x,cin,c].Nodup := (List.nodup_cons.mp nd).2
        have nd' := nd
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
          not_or,not_false_eq_true,and_true] at nd'
        obtain ⟨⟨hox,hoi,hoc⟩,⟨hxi,hxc⟩,hic⟩ := nd'
        have xTail : x∉x'::xs := (List.nodup_cons.mp words.1).1
        have cTail : c∉x'::xs := by
          intro h; exact List.disjoint_left.mp words.2.2 (List.mem_cons_of_mem x h) List.mem_cons_self
        have iTail : cin∉x'::xs := fun h => hi.1
          (List.mem_append_left _ (List.mem_cons_of_mem x h))
        have oTail : one∉x'::xs := fun h => hd.1
          (List.mem_cons_of_mem cin (List.mem_append_left _ (List.mem_cons_of_mem x h)))
        have cScratch : c∉cs := (List.nodup_cons.mp words.2.1).1
        have xScratch : x∉cs := by
          intro h; exact List.disjoint_left.mp words.2.2
            (show x∈x::x'::xs from List.mem_cons_self) (List.mem_cons_of_mem c h)
        let bit := decide (k%2=1)
        let S := sumBit (s.basis x) bit (s.basis cin)
        let K := carryBit (s.basis x) bit (s.basis cin)
        let s1 : State := ⟨s.phase,writeBit (writeBit s.basis x S) c K⟩
        have keep (q : Wire) (hqx : q≠x) (hqc : q≠c) : s1.basis q=s.basis q := by
          simp [s1,writeBit,hqx,hqc]
        have first (record : List Bool) : run (literalConstStep bit x cin c) record s=s1 := by
          exact literalConstStep_correct bit x cin c stepND s record (hclean c (by simp))
        have one1 : s1.basis one=false := (keep one hox hoc).trans ho
        have clean1 : ∀ q∈cs,s1.basis q=false := by
          intro q hq
          exact (keep q (fun h => xScratch (h ▸ hq))
            (fun h => cScratch (h ▸ hq))).trans (hclean q (by simp [hq]))
        have high := ih cs c (k/2) tailND (by simpa using hc) s1 m one1 clean1
        let t := run (literalConstAdd (x'::xs) cs c one (k/2)) m s1
        have tx : t.basis x=S := by rw [high.2.1 x xTail]; simp [s1,writeBit,hxc]
        have ti : t.basis cin=s.basis cin :=
          (high.2.1 cin iTail).trans (keep cin (Ne.symm hxi) hic)
        have tc : t.basis c=K := by rw [high.2.1 c cTail]; simp [s1,writeBit]
        have ton : t.basis one=false := (high.2.1 one oTail).trans one1
        have erase (record : List Bool) : run (literalConstErase bit x cin c one) record t=
            ⟨t.phase,writeBit t.basis c false⟩ := by
          apply literalConstErase_correct bit x cin c one nd t record ton
          rw [tx,ti,tc]
          exact (literalCarryPredicate_sum (s.basis x) bit (s.basis cin)).symm
        have counts := literalConstCell_counts (decide (k%2=1)) x cin c one
        rw [literalConstAdd]
        simp only [List.append_assoc,run_append,run_take,counts.2.1,List.drop_zero]
        rw [first]
        change (run (literalConstErase bit x cin c one) _ t).phase=s.phase ∧ _
        rw [erase]
        refine ⟨high.1,?_,?_⟩
        · intro q hq
          have hxq : q≠x := fun h => hq (by simp [h])
          have htq : q∉x'::xs := fun h => hq (by simp [h])
          by_cases hqc : q=c
          · subst q; simp [writeBit,hclean c (by simp)]
          · simp only [writeBit,Function.update_of_ne hqc]
            exact (high.2.1 q htq).trans (keep q hxq hqc)
        · have tailKeep : regValue (x'::xs) (writeBit t.basis c false)=regValue (x'::xs) t.basis :=
            regValue_congr _ _ _ (fun q hq => by
              simp [writeBit,show q≠c from fun h => cTail (h ▸ hq)])
          have tailIn : regValue (x'::xs) s1.basis=regValue (x'::xs) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q
              (fun h => xTail (h ▸ hq)) (fun h => cTail (h ▸ hq)))
          have kc : s1.basis c=K := by simp [s1,writeBit]
          change (if (writeBit t.basis c false) x then 1 else 0)+
            2*regValue (x'::xs) (writeBit t.basis c false)=_
          rw [tailKeep,high.2.2,tailIn,kc]
          simp only [writeBit,Function.update_of_ne hxc,tx]
          have col := sum_value_step (s.basis x) bit (s.basis cin)
            (regValue (x'::xs) s.basis) (k/2) (x'::xs).length
          have split : bit.toNat+2*(k/2)=k := literal_split k
          rw [split] at col
          simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,List.length_cons,S,K] using col

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Rotate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 无控制物理交换：三个 CX，不消耗 Toffoli 或测量。 -/
def swapBits (a b : Wire) : Program := [.CX b a,.CX a b,.CX b a]

private theorem swapBits_correct (a b : Wire) (hab : a≠b) (s : State) (m : List Bool) :
    (run (swapBits a b) m s).phase=s.phase ∧
    (∀ q, q≠a → q≠b → (run (swapBits a b) m s).basis q=s.basis q) ∧
    (run (swapBits a b) m s).basis a=s.basis b ∧
    (run (swapBits a b) m s).basis b=s.basis a := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro q ha hb; simp [swapBits,run,writeBit,ha,hb]
  all_goals cases ha : s.basis a <;> cases hb : s.basis b <;>
    simp [swapBits,run,writeBit,hab,Ne.symm hab,ha,hb]

private theorem swapBits_twice (a b : Wire) (hab : a≠b) (s : State) (m : List Bool) :
    run (swapBits a b) m (run (swapBits a b) m s)=s := by
  obtain ⟨p1,e1,a1,b1⟩ := swapBits_correct a b hab s m
  obtain ⟨p2,e2,a2,b2⟩ := swapBits_correct a b hab (run (swapBits a b) m s) m
  apply congrArg₂ State.mk
  · exact p2.trans p1
  · funext q
    by_cases ha : q=a
    · subst q; exact a2.trans b1
    by_cases hb : q=b
    · subst q; exact b2.trans a1
    exact (e2 q ha hb).trans (e1 q ha hb)

/-- 小端寄存器右旋：原最低位经相邻交换移动到最高位。 -/
def rotateRight : List Wire → Program
  | a::b::bs => swapBits a b ++ rotateRight (b::bs)
  | _ => []

/-- 左旋按逆序执行无测量的相邻交换；固定物理寄存器不换视图。 -/
def rotateLeft : List Wire → Program
  | a::b::bs => rotateLeft (b::bs) ++ swapBits a b
  | _ => []

theorem rotate_counts (r : List Wire) :
    toffoliCount (rotateRight r)=0 ∧ measurementCount (rotateRight r)=0 ∧
    toffoliCount (rotateLeft r)=0 ∧ measurementCount (rotateLeft r)=0 := by
  induction r with
  | nil => simp [rotateRight,rotateLeft,toffoliCount,measurementCount]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,toffoliCount,measurementCount]
    | cons b bs => simp [rotateRight,rotateLeft,toffoliCount_append,measurementCount_append,
        swapBits,toffoliCount,measurementCount,ih]

theorem rotate_frame (r : List Wire) (s : State) (m : List Bool) :
    (run (rotateRight r) m s).phase=s.phase ∧
    (∀ q, q∉r → (run (rotateRight r) m s).basis q=s.basis q) ∧
    (run (rotateLeft r) m s).phase=s.phase ∧
    (∀ q, q∉r → (run (rotateLeft r) m s).basis q=s.basis q) := by
  induction r generalizing s with
  | nil => simp [rotateRight,rotateLeft,run]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,run]
    | cons b bs =>
      simp only [rotateRight,rotateLeft]
      rw [run_append,run_append,run_take,run_take,
        show measurementCount (swapBits a b)=0 from rfl,(rotate_counts (b::bs)).2.2.2,List.drop_zero]
      have hR := ih (run (swapBits a b) m s)
      have hL := ih s
      refine ⟨hR.1,?_,hL.2.2.1,?_⟩
      · intro q hq
        have hn : q≠a ∧ q≠b ∧ q∉bs := by simpa only [List.mem_cons,not_or] using hq
        rw [hR.2.1 q (by simp [hn.2.1,hn.2.2])]
        simp [swapBits,run,writeBit,hn.1,hn.2.1]
      · intro q hq
        have hn : q≠a ∧ q≠b ∧ q∉bs := by simpa only [List.mem_cons,not_or] using hq
        simpa [swapBits,run,writeBit,hn.1,hn.2.1] using hL.2.2.2 q (by simp [hn.2.1,hn.2.2])

private theorem rotateRight_value (a : Wire) (bs : List Wire) (hnd : (a::bs).Nodup)
    (s : State) (m : List Bool) :
    regValue (a::bs) (run (rotateRight (a::bs)) m s).basis=
      regValue bs s.basis+2^bs.length*(s.basis a).toNat := by
  induction bs generalizing a s with
  | nil => simp [rotateRight,run,regValue,Bool.toNat]
  | cons b bs ih =>
    have ha := (List.nodup_cons.mp hnd).1
    have ht := (List.nodup_cons.mp hnd).2
    have hab : a≠b := fun hh => ha (by simp [hh])
    let s1 := run (swapBits a b) m s
    have hv := ih b ht s1
    obtain ⟨_,he,hA,hB⟩ := swapBits_correct a b hab s m
    have hbs : regValue bs s1.basis=regValue bs s.basis := regValue_congr _ _ _ (by
      intro q hq
      apply he q
      · intro hh; subst q; exact ha (List.mem_cons_of_mem _ hq)
      · intro hh; subst q; exact (List.nodup_cons.mp ht).1 hq)
    have hk := (rotate_frame (b::bs) s1 m).2.1 a ha
    change regValue (a::b::bs) (run (swapBits a b ++ rotateRight (b::bs)) m s).basis=_
    rw [run_append,run_take]
    change (if (run (rotateRight (b::bs)) m s1).basis a then 1 else 0)+
      2*regValue (b::bs) (run (rotateRight (b::bs)) m s1).basis=_
    rw [hk,hv,hbs,hA,hB]
    simp only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,List.length_cons,pow_succ]
    ring

/-- 仅无测量的旋转互逆，不用于反转算术测量门列。 -/
theorem rotateRight_left_cancel (r : List Wire) (hnd : r.Nodup) (s : State) (m : List Bool) :
    run (rotateRight r) m (run (rotateLeft r) m s)=s := by
  induction r generalizing s with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b bs =>
      have ht := (List.nodup_cons.mp hnd).2
      have hab : a≠b := fun hh => (List.nodup_cons.mp hnd).1 (by simp [hh])
      change run (swapBits a b ++ rotateRight (b::bs)) m
        (run (rotateLeft (b::bs) ++ swapBits a b) m s)=s
      rw [run_append,run_take,run_append,run_take,(rotate_counts (b::bs)).2.2.2,
        show measurementCount (swapBits a b)=0 from rfl,List.drop_zero,swapBits_twice a b hab]
      exact ih ht s

/-- 输入为偶数时，右旋恰好除以二，移入最高位为零。 -/
theorem rotateRight_spec (r : List Wire) (hnd : r.Nodup) (X : Nat) (heven : X%2=0) :
    (Triple (fun st => Holds.holds st r X) (rotateRight r)
      (fun st => Holds.holds st r (X/2))) := by
  intro s m h
  refine ⟨(rotate_frame r s m).1,?_⟩
  cases r with
  | nil =>
    change 0=X at h
    change 0=X/2
    omega
  | cons a bs =>
    have hv := rotateRight_value a bs hnd s m
    have hx : (s.basis a).toNat+2*regValue bs s.basis=X := by
      simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite] using h
    change regValue (a::bs) _=X/2
    cases ha : s.basis a <;> simp [ha,Bool.toNat] at hx hv <;> omega

/-- 无溢出时，左旋恰好乘二。 -/
theorem rotateLeft_spec (r : List Wire) (hnd : r.Nodup) (X : Nat) (hfit : 2*X<2^r.length) :
    (Triple (fun st => Holds.holds st r X) (rotateLeft r)
      (fun st => Holds.holds st r (2*X))) := by
  intro s m h
  let t := run (rotateLeft r) m s
  have hcancel := rotateRight_left_cancel r hnd s m
  refine ⟨(rotate_frame r s m).2.2.1,?_⟩
  cases r with
  | nil =>
    change 0=X at h
    change 0=2*X
    omega
  | cons a bs =>
    have hv := rotateRight_value a bs hnd t m
    rw [hcancel,h] at hv
    simp only [List.length_cons,pow_succ] at hfit
    change regValue (a::bs) t.basis=_
    change (if t.basis a then 1 else 0)+2*regValue bs t.basis=_
    cases ha : t.basis a <;> simp [ha,Bool.toNat] at hv ⊢ <;> omega

theorem rotate_wires (r : List Wire) :
    wires (rotateRight r)=(if r.length<2 then ∅ else r.toFinset) ∧
    wires (rotateLeft r)=(if r.length<2 then ∅ else r.toFinset) := by
  induction r with
  | nil => simp [rotateRight,rotateLeft,wires]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,wires]
    | cons b bs =>
      simp only [rotateRight,rotateLeft,wires_append,ih.1,ih.2]
      cases bs with
      | nil => simp [swapBits,wires,Instr.wires,Finset.union_comm]
      | cons d ds =>
        simp only [show ¬(b::d::ds).length<2 by simp,show ¬(a::b::d::ds).length<2 by simp,if_false]
        constructor <;> ext q <;> simp [swapBits,wires,Instr.wires] <;> tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Framework/GateInverse.lean
noncomputable section

namespace ECDSAAdd

/-- The instruction is a basis-state permutation whose target is distinct
from every control.  Measurement instructions are deliberately excluded. -/
def ProperGate : Instr → Prop
  | .X _ => True
  | .CX c t => c ≠ t
  | .CCX a b t => a ≠ t ∧ b ≠ t
  | .measureX _ _ _ => False

def ProperProgram (p : Program) : Prop := ∀i∈p,ProperGate i

theorem properProgram_append (p q : Program) :
    ProperProgram (p++q) ↔ ProperProgram p ∧ ProperProgram q := by
  constructor
  · intro h
    constructor
    · intro i hi; exact h i (List.mem_append_left q hi)
    · intro i hi; exact h i (List.mem_append_right p hi)
  · rintro ⟨hp,hq⟩ i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact hp i hi
    · exact hq i hi

theorem properProgram_reverse (p : Program) :
    ProperProgram p → ProperProgram p.reverse := by
  intro h i hi
  exact h i (List.mem_reverse.mp hi)

theorem properGate_involution (i : Instr) (h : ProperGate i)
    (s : State) (m₁ m₂ : List Bool) :
    run [i] m₂ (run [i] m₁ s)=s := by
  cases i with
  | X t =>
      cases s with
      | mk phase basis =>
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t <;> simp [run,writeBit,hq]
  | CX c t =>
      change c≠t at h
      cases s with
      | mk phase basis =>
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t
        · subst q
          cases hc : basis c <;> cases ht : basis t <;>
            simp [run,writeBit,h,hc,ht]
        · simp [run,writeBit,hq]
  | CCX a b t =>
      cases s with
      | mk phase basis =>
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t
        · subst q
          cases ha : basis a <;> cases hb : basis b <;> cases ht : basis t <;>
            simp [ProperGate] at h
          all_goals simp [run,writeBit,h.1,h.2,ha,hb,ht]
        · simp [run,writeBit,hq]
  | measureX t c₀ c₁ => contradiction

theorem properProgram_measurementCount (p : Program)
    (h : ∀i∈p,ProperGate i) : measurementCount p=0 := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      have hi := h i (by simp)
      have hp : ∀j∈p,ProperGate j := by intro j hj; exact h j (by simp [hj])
      cases i <;> simp_all [ProperGate,measurementCount]

theorem measurementCount_reverse (p : Program) :
    measurementCount p.reverse=measurementCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      cases i <;> simp [measurementCount,ih,Nat.add_comm]

theorem toffoliCount_reverse (p : Program) :
    toffoliCount p.reverse=toffoliCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      cases i <;> simp [toffoliCount,ih,Nat.add_comm]

theorem wires_reverse (p : Program) : wires p.reverse=wires p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      simp [wires,ih,Finset.union_comm]

/-- Reversing a proper gate-only stream gives its exact inverse on the whole
state, including phase.  Since the stream has no measurements, the two record
lists are completely independent. -/
theorem run_reverse_proper (p : Program) (h : ∀i∈p,ProperGate i)
    (s : State) (m₁ m₂ : List Bool) :
    run p.reverse m₂ (run p m₁ s)=s := by
  induction p generalizing s m₁ m₂ with
  | nil => rfl
  | cons i p ih =>
      have hi : ProperGate i := h i (by simp)
      have hp : ∀j∈p,ProperGate j := by intro j hj; exact h j (by simp [hj])
      have pm : measurementCount p=0 := properProgram_measurementCount p hp
      have prm : measurementCount p.reverse=0 := by
        rw [measurementCount_reverse]
        exact pm
      have runCons : run (i::p) m₁ s=run p m₁ (run [i] [] s) := by
        cases i <;> simp_all [ProperGate,run]
      simp only [List.reverse_cons,run_append,prm,List.take_zero,List.drop_zero,runCons]
      rw [ih hp]
      exact properGate_involution i hi s [] m₂

/-- A proper gate-only program depends only on its declared wire support.
States agreeing there and in phase still agree there after execution. -/
theorem run_proper_congr (p : Program) (hp : ProperProgram p)
    (s t : State) (m₁ m₂ : List Bool) (hphase : s.phase=t.phase)
    (hbasis : ∀q∈wires p,s.basis q=t.basis q) :
    (run p m₁ s).phase=(run p m₂ t).phase ∧
      ∀q∈wires p,(run p m₁ s).basis q=(run p m₂ t).basis q := by
  induction p generalizing s t m₁ m₂ with
  | nil => exact ⟨hphase,by simp [wires]⟩
  | cons i p ih =>
    have hi := hp i (by simp)
    have hpt : ProperProgram p := by intro j hj; exact hp j (by simp [hj])
    have tailMem (q : Wire) (hq : q∈wires p) : s.basis q=t.basis q :=
      hbasis q (Finset.mem_union_right _ hq)
    cases i with
    | X x =>
      let s' : State := ⟨s.phase,writeBit s.basis x (!s.basis x)⟩
      let t' : State := ⟨t.phase,writeBit t.basis x (!t.basis x)⟩
      have hx : s.basis x=t.basis x := hbasis x (by simp [wires,Instr.wires])
      have htail (q : Wire) (hq : q∈wires p) : s'.basis q=t'.basis q := by
        by_cases e : q=x
        · subst q; simp [s',t',writeBit,hx]
        · simp [s',t',writeBit,e,tailMem q hq]
      have hrec := ih hpt s' t' m₁ m₂ hphase htail
      refine ⟨hrec.1,?_⟩
      intro q hq
      simp only [wires,Finset.mem_union] at hq
      rcases hq with hq|hq
      · by_cases hqp : q∈wires p
        · exact hrec.2 q hqp
        · have hqeq : s'.basis q=t'.basis q := by
            simp only [Instr.wires,Finset.mem_singleton] at hq
            subst q
            simp [s',t',writeBit,hx]
          exact (run_preserves_outside p m₁ s' q hqp).trans
            (hqeq.trans (run_preserves_outside p m₂ t' q hqp).symm)
      · exact hrec.2 q hq
    | CX c x =>
      have hcx : c≠x := hi
      let s' : State := ⟨s.phase,writeBit s.basis x (s.basis x^^s.basis c)⟩
      let t' : State := ⟨t.phase,writeBit t.basis x (t.basis x^^t.basis c)⟩
      have hc : s.basis c=t.basis c := hbasis c (by simp [wires,Instr.wires])
      have hx : s.basis x=t.basis x := hbasis x (by simp [wires,Instr.wires])
      have htail (q : Wire) (hq : q∈wires p) : s'.basis q=t'.basis q := by
        by_cases e : q=x
        · subst q; simp [s',t',writeBit,hx,hc]
        · simp [s',t',writeBit,e,tailMem q hq]
      have hrec := ih hpt s' t' m₁ m₂ hphase htail
      refine ⟨hrec.1,?_⟩
      intro q hq
      simp only [wires,Finset.mem_union] at hq
      rcases hq with hq|hq
      · by_cases hqp : q∈wires p
        · exact hrec.2 q hqp
        · have hqeq : s'.basis q=t'.basis q := by
            simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl|rfl
            · simp [s',t',writeBit,hcx,hc]
            · simp [s',t',writeBit,hx,hc]
          exact (run_preserves_outside p m₁ s' q hqp).trans
            (hqeq.trans (run_preserves_outside p m₂ t' q hqp).symm)
      · exact hrec.2 q hq
    | CCX a b x =>
      have hax : a≠x := hi.1
      have hbx : b≠x := hi.2
      let s' : State := ⟨s.phase,writeBit s.basis x (s.basis x^^(s.basis a&&s.basis b))⟩
      let t' : State := ⟨t.phase,writeBit t.basis x (t.basis x^^(t.basis a&&t.basis b))⟩
      have ha : s.basis a=t.basis a := hbasis a (by simp [wires,Instr.wires])
      have hb : s.basis b=t.basis b := hbasis b (by simp [wires,Instr.wires])
      have hx : s.basis x=t.basis x := hbasis x (by simp [wires,Instr.wires])
      have htail (q : Wire) (hq : q∈wires p) : s'.basis q=t'.basis q := by
        by_cases e : q=x
        · subst q; simp [s',t',writeBit,hx,ha,hb]
        · simp [s',t',writeBit,e,tailMem q hq]
      have hrec := ih hpt s' t' m₁ m₂ hphase htail
      refine ⟨hrec.1,?_⟩
      intro q hq
      simp only [wires,Finset.mem_union] at hq
      rcases hq with hq|hq
      · by_cases hqp : q∈wires p
        · exact hrec.2 q hqp
        · have hqeq : s'.basis q=t'.basis q := by
            simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl|rfl|rfl
            · simp [s',t',writeBit,hax,ha,hb]
            · simp [s',t',writeBit,hbx,ha,hb]
            · simp [s',t',writeBit,hx,ha,hb]
          exact (run_preserves_outside p m₁ s' q hqp).trans
            (hqeq.trans (run_preserves_outside p m₂ t' q hqp).symm)
      · exact hrec.2 q hq
    | measureX x c₀ c₁ => contradiction

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupCircuitProgram.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.BalancedCleanup
open BalancedField

structure Layout where
  r0 : Wire
  rtail : List Wire
  rmsb : Wire
  ylow : List Wire
  ymsb : Wire
  carry : List Wire
  sign : Wire
  parity : Wire
  lower : Wire
  one : Wire

def Layout.low (L : Layout) := L.r0::L.rtail
def Layout.r (L : Layout) := L.low++[L.rmsb]
def Layout.y (L : Layout) := L.ylow++[L.ymsb]
def Layout.wires (L : Layout) :=
  [L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0]++L.rtail++L.ylow++L.carry

def Layout.Widths (L : Layout) : Prop :=
  L.rtail.length=254 ∧ L.ylow.length=255 ∧ L.carry.length=256

def negativeLiteral : Nat := encodeWord 255 (-h)
def positiveLiteral : Nat := (h-1).toNat

/-- Copy the live result sign, then complement the signed result to magnitude. -/
def prepareSign (L : Layout) : Program :=
  [.CX L.rmsb L.lower]++signComplement L.lower L.r

/-- Rotate the normalized low word, insert the exact low bit, complement
source under S XOR L, and bias both signed words for the existing comparator. -/
def prepareCompare (L : Layout) : Program :=
  rotateLeft L.r++[.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]++
  signComplement L.sign L.y++signComplement L.lower L.y++[.X L.rmsb,.X L.ymsb]

def normalize (L : Layout) : Program :=
  literalConstAdd L.low (L.carry.take 254) L.lower L.one negativeLiteral

def unnormalize (L : Layout) : Program :=
  [.X L.lower]++literalConstAdd L.low (L.carry.take 254) L.lower L.one positiveLiteral++[.X L.lower]

/-- Only the two Clifford views are reversed. Both measured literal adders
and the comparator are independently emitted forward programs. -/
def program (L : Layout) : Program :=
  prepareSign L++(normalize L++(prepareCompare L++
    (compareLt none L.y L.r L.carry L.one L.parity++
      ((prepareCompare L).reverse++(unnormalize L++(prepareSign L).reverse)))))

 theorem widths (L : Layout) (hw : L.Widths) :
    L.low.length=255 ∧ L.r.length=256 ∧ L.y.length=256 ∧ (L.carry.take 254).length=254 := by
  simp [Layout.low,Layout.r,Layout.y,List.length_take,hw.1,hw.2.1,hw.2.2]

 theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=764 ∧ measurementCount (program L)=764 := by
  have w := widths L hw
  have a := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one negativeLiteral
    (by omega)
  have b := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one positiveLiteral
    (by omega)
  have c := compareLt_counts none L.y L.r L.carry L.one L.parity
    (by omega) (by unfold Layout.Widths at hw; omega)
  have rot := rotate_counts L.r
  have r := signComplement_counts L.lower L.r
  have ys := signComplement_counts L.sign L.y
  have yl := signComplement_counts L.lower L.y
  simp only [program,prepareSign,normalize,prepareCompare,unnormalize,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    rot.2.2.1,rot.2.2.2,r.1,r.2,ys.1,ys.2,yl.1,yl.2,a.1,a.2,b.1,b.2,c.1,c.2]
  simp [toffoliCount,measurementCount,w.1,w.2.1]

end ECDSAAdd.Arithmetic.BalancedCleanup


namespace ECDSAAdd.Arithmetic.BalancedCleanup

 theorem Layout.allND (L : Layout) (hn : L.wires.Nodup) :
    ([L.parity,L.sign,L.lower,L.one]++(L.r++(L.y++L.carry))).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w; have h := List.nodup_iff_count.mp hn w
  simp only [Layout.wires,Layout.r,Layout.low,Layout.y,List.count_append,
    List.count_cons,List.count_nil] at h ⊢
  omega

 theorem Layout.flagsND (L : Layout) (hn : L.wires.Nodup) :
    [L.parity,L.sign,L.lower,L.one].Nodup :=
  (List.nodup_append'.mp (L.allND hn)).1

 theorem Layout.dataND (L : Layout) (hn : L.wires.Nodup) : (L.r++(L.y++L.carry)).Nodup :=
  (List.nodup_append'.mp (L.allND hn)).2.1

 theorem Layout.flagAway (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.parity,L.sign,L.lower,L.one]) : q∉(L.r++(L.y++L.carry)) :=
  fun h => List.disjoint_left.mp (List.nodup_append'.mp (L.allND hn)).2.2 hq h

 theorem Layout.normND (L : Layout) (hn : L.wires.Nodup) :
    (L.one::L.lower::(L.low++L.carry.take 254)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w; have h := List.nodup_iff_count.mp hn w
  have c := (List.take_sublist 254 L.carry).count_le w
  simp only [Layout.wires,Layout.low,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

 theorem Layout.compareND (L : Layout) (hn : L.wires.Nodup) :
    (L.parity::L.one::(L.y++L.r++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w; have h := List.nodup_iff_count.mp (L.allND hn) w
  simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

 theorem complement_proper (c : Wire) (r : List Wire) (hc : c∉r) :
    ProperProgram (signComplement c r) := by
  intro i hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
  exact fun he => hc (he ▸ hq)

 theorem rotateLeft_proper (r : List Wire) (hn : r.Nodup) : ProperProgram (rotateLeft r) := by
  induction r with
  | nil => simp [rotateLeft,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateLeft,ProperProgram]
    | cons b r =>
      have ht := List.nodup_cons.mp hn
      have hab : a≠b := fun he => ht.1 (by simp [he])
      apply (properProgram_append _ _).mpr
      exact ⟨ih ht.2,by simpa [ProperProgram,ProperGate,swapBits] using
        (And.intro (Ne.symm hab) (And.intro hab (Ne.symm hab)))⟩

 theorem prepareSign_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (prepareSign L) := by
  have away : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  apply (properProgram_append _ _).mpr
  exact ⟨by simp [ProperProgram,ProperGate,show L.rmsb≠L.lower from
    fun he => away (by simp [Layout.r,he])],complement_proper _ _ away⟩

 theorem prepareCompare_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (prepareCompare L) := by
  have ndR := (List.nodup_append'.mp (L.dataND hn)).1
  have sR : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lR : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have sY : L.sign∉L.y := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lY : L.lower∉L.y := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  simp only [prepareCompare,properProgram_append]
  refine ⟨⟨⟨⟨rotateLeft_proper _ ndR,?_⟩,complement_proper _ _ sY⟩,
    complement_proper _ _ lY⟩,by simp [ProperProgram,ProperGate]⟩
  simp only [ProperProgram,ProperGate,List.mem_cons,List.not_mem_nil,or_false]
  have hs : L.sign≠L.r0 := fun he => sR (by simp [Layout.r,Layout.low,he])
  have hl : L.lower≠L.r0 := fun he => lR (by simp [Layout.r,Layout.low,he])
  intro i hi
  rcases hi with rfl|rfl|rfl
  · trivial
  · exact hs
  · exact hl

end ECDSAAdd.Arithmetic.BalancedCleanup
end

-- source: ECDSAAdd/Arithmetic/SignedHalf.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Once the even low bit is zero, its wire becomes the new sign extension
bit. The new little-endian view is the old high tail followed by that wire. -/
def skywalkHalfView (low : Wire) (tail : List Wire) : List Wire := tail ++ [low]

def skywalkSignedHalf (sign low : Wire) : Program := [.CX sign low]

theorem skywalkSignedHalf_correct (sign low : Wire) (_hsl : sign ≠ low)
    (s : State) (m : List Bool) (he : s.basis low = false) :
    run (skywalkSignedHalf sign low) m s =
      ⟨s.phase, writeBit s.basis low (s.basis sign)⟩ := by
  simp [skywalkSignedHalf, run, he]

theorem skywalkSignedHalf_value (sign low : Wire) (tail : List Wire)
    (hsl : sign ≠ low) (hlo : low ∉ tail)
    (s : State) (m : List Bool) (he : s.basis low = false) :
    regValue (skywalkHalfView low tail) (run (skywalkSignedHalf sign low) m s).basis =
      regValue tail s.basis + 2 ^ tail.length * (s.basis sign).toNat := by
  rw [skywalkSignedHalf_correct sign low hsl s m he]
  have ht : regValue tail (writeBit s.basis low (s.basis sign)) = regValue tail s.basis := by
    apply regValue_congr
    intro q hq
    have hn : q ≠ low := fun h => hlo (h ▸ hq)
    simp [writeBit, hn]
  change regValue (tail ++ [low]) (writeBit s.basis low (s.basis sign)) = _
  rw [regValue_append, ht]
  cases s.basis sign <;> simp [regValue, writeBit, Bool.toNat]

theorem skywalkSignedHalf_frame (sign low : Wire) (s : State) (m : List Bool) :
    (run (skywalkSignedHalf sign low) m s).phase = s.phase ∧
    (∀ q, q ≠ low → (run (skywalkSignedHalf sign low) m s).basis q = s.basis q) := by
  constructor
  · rfl
  · intro q hq
    simp [skywalkSignedHalf, run, writeBit, hq]

/-- Clearing the sign extension is the same CX before restoring the old view.
This is a genuine gate inverse, valid for every initial basis state. -/
theorem skywalkSignedHalf_twice (sign low : Wire) (hsl : sign ≠ low)
    (s : State) (m : List Bool) :
    run (skywalkSignedHalf sign low) m (run (skywalkSignedHalf sign low) m s) = s := by
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = low
  · subst q
    cases hs : s.basis sign <;> cases hl : s.basis low <;>
      simp [skywalkSignedHalf, run, writeBit, hsl, hs, hl]
  · simp [skywalkSignedHalf, run, writeBit, hq]

theorem skywalkSignedHalf_counts (sign low : Wire) :
    toffoliCount (skywalkSignedHalf sign low) = 0 ∧
    measurementCount (skywalkSignedHalf sign low) = 0 := by
  simp [skywalkSignedHalf, toffoliCount, measurementCount]

theorem skywalkSignedHalf_wires (sign low : Wire) :
    wires (skywalkSignedHalf sign low) = [sign, low].toFinset := by
  ext q
  simp [skywalkSignedHalf, wires, Instr.wires]

/-- Explicit sign-bit interpretation; connecting the actual most significant
bit to the canonical signed-word decoder is a separate layout obligation. -/
def signedHalfDecode (n : Nat) (sign : Bool) (raw : Nat) : Int :=
  (raw : Int) - if sign then (2 : Int) ^ n else 0

theorem signedHalfDecode_half (n X : Nat) (S : Bool) :
    signedHalfDecode (n + 1) S (X + 2 ^ n * S.toNat) =
      signedHalfDecode (n + 1) S (2 * X) / 2 := by
  cases S
  · simp [signedHalfDecode, Bool.toNat]
  · simp [signedHalfDecode, pow_succ]
    omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/SkywalkRails.lean
noncomputable section

namespace ECDSAAdd.SkywalkRails

/-- Arithmetic sign, including the unique nonnegative encoding of zero. -/
def neg (x : Int) : Bool := decide (x<0)

def odd (x : Int) : Bool := decide (x%2≠0)

def sameSign (x y : Int) : Bool := decide (neg x=neg y)

@[ext] structure State where
  a : Int
  b : Int
  g : Bool
  deriving DecidableEq

@[ext] structure Tick where
  h : Int
  k : Int
  g : Bool
  s : Bool
  deriving DecidableEq

/-- Exactly one rail is even. The parity of the first rail chooses it. -/
def route (a b : Int) : Int×Int := if odd a then (b,a) else (a,b)

/-- Signed Skywalk tick. Arithmetic remains over unbounded exact integers;
word-width bounds are separate obligations for the circuit implementation. -/
def step (z : State) : Tick :=
  let eo := route z.a z.b
  let h := eo.1/2
  let k := if sameSign eo.1 eo.2 then eo.2-h else eo.2+h
  ⟨h,k,z.g ^^ odd z.a,neg eo.2 ^^ neg k⟩

theorem route_even (a b : Int) (hp : (a+b)%2=1) : (route a b).1%2=0 := by
  by_cases ha : a%2=0
  · simp [route,odd,ha]
  · have hb : b%2=0 := by omega
    simp [route,odd,ha,hb]

/-- Arithmetic right shift preserves sign on even integers, including zero. -/
theorem neg_half (e : Int) (he : e%2=0) : neg (e/2)=neg e := by
  by_cases hn : e<0
  · have hh : e/2<0 := by omega
    simp [neg,hn,hh]
  · have hh : ¬e/2<0 := by omega
    simp [neg,hn,hh]

def signed (s : Bool) (u : Int) : Int := if s then -u else u

/-- g=true means that the first rail is the smaller one. The larger rail
is positive; a zero smaller rail has the unique value zero for either s. -/
def encode (g s : Bool) (u v : Int) : State :=
  if g then ⟨signed s u,u+v,g⟩ else ⟨u+v,signed s u,g⟩

theorem encode_odd_sum (g s : Bool) (u v : Int) (hv : v%2=1) :
    ((encode g s u v).a+(encode g s u v).b)%2=1 := by
  cases g <;> cases s <;> simp only [encode,signed,if_true,if_false,
    Bool.false_eq_true]
  all_goals omega

/-- Terminal states are retained exactly: one tick changes (v,0) to (0,v),
and all following ticks keep (0,v), without a fabricated negative zero. -/
theorem terminal_step (g s : Bool) (v : Int) (hv : 0<v) (hodd : v%2=1) :
    step (encode g s 0 v)=⟨0,v,true,false⟩ := by
  have hvn : ¬v<0 := by omega
  have hvodd : v%2≠0 := by omega
  cases g <;> cases s <;>
    simp [step,encode,signed,route,odd,sameSign,neg,hvn,hvodd]

theorem zero_sign (s : Bool) : signed s 0=0 := by cases s <;> simp [signed]

/-- The new orientation identifies the even-u branch, independently of the
old orientation and the smaller rail's sign. -/
theorem step_orientation (g s : Bool) (u v : Int) (hv : v%2=1) :
    (step (encode g s u v)).g=decide (u%2=0) := by
  by_cases hu : u%2=0
  · have hl : (u+v)%2≠0 := by omega
    have hs : (-u)%2=0 := by omega
    cases g <;> cases s <;> simp [step,encode,signed,odd,hu,hl,hs]
  · have hl : (u+v)%2=0 := by omega
    cases g <;> cases s <;> simp [step,encode,signed,odd,hu,hl]

theorem step_encode_even (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) (hue : u%2=0) :
    step (encode g s u v)=⟨signed s (u/2),u/2+v,true,false⟩ := by
  by_cases hz : u=0
  · subst u
    simpa [signed] using terminal_step g s v hv hvo
  · have hup : 0<u := by omega
    have hLodd : (u+v)%2≠0 := by omega
    have hnue : (-u)%2=0 := by omega
    have hLp : ¬u+v<0 := by omega
    have hun : ¬u<0 := by omega
    have hdiv : (-u)/2=-(u/2) := by omega
    have hdiff : u+v-u/2=u/2+v := by omega
    have hsum : u+v+-(u/2)=u/2+v := by omega
    have hkn : ¬u/2+v<0 := by omega
    cases g <;> cases s <;>
      simp [step,encode,signed,route,odd,sameSign,neg,hue,hLodd,hnue,
        hLp,hun,hup,hdiv,hdiff,hsum,hkn]

/-- At equality the positive small rail records no flip, and the negative
small rail records a flip. Both produce the identical zero-valued rail. -/
theorem step_encode_odd (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) (huo : u%2≠0) :
    step (encode g s u v)=
      ⟨(u+v)/2,if s then (v-u)/2 else (u-v)/2,false,
        decide (if s then u≤v else u<v)⟩ := by
  have hup : 0<u := by omega
  have hLe : (u+v)%2=0 := by omega
  have hLp : ¬u+v<0 := by omega
  have hun : ¬u<0 := by omega
  have hdiff : u-(u+v)/2=(u-v)/2 := by omega
  have hsum : -u+(u+v)/2=(v-u)/2 := by omega
  have hsmall : ((u-v)/2<0) ↔ u<v := by omega
  have hflip : (!decide ((v-u)/2<0))=decide (u≤v) := by
    by_cases hle : u≤v
    · have hn : ¬(v-u)/2<0 := by omega
      simp [hle,hn]
    · have hn : (v-u)/2<0 := by omega
      simp [hle,hn]
  cases g <;> cases s <;>
    simp [step,encode,signed,route,odd,sameSign,neg,huo,hLe,
      hLp,hun,hup,hdiff,hsum,hsmall,hflip]

theorem odd_flip_order (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) (huo : u%2≠0) :
    ((step (encode g s u v)).s=false → v≤u) ∧
    ((step (encode g s u v)).s=true → u≤v) := by
  rw [step_encode_odd g s u v hu hv hvo huo]
  cases s <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    constructor <;> intro h <;> simp_all; omega

/-- The orientation points to a strictly smaller magnitude, and the other
rail is positive. This includes a zero small rail after an equality step. -/
def Frame (t : Tick) : Prop :=
  if t.g then 0<t.k ∧ |t.h|<t.k else 0<t.h ∧ |t.k|<t.h

theorem step_frame (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) :
    Frame (step (encode g s u v)) := by
  by_cases he : u%2=0
  · rw [step_encode_even g s u v hu hv hvo he]
    simp only [Frame,if_true]
    constructor
    · omega
    · cases s <;> simp only [signed,Bool.false_eq_true,if_false,if_true]
      all_goals apply abs_lt.mpr; constructor <;> omega
  · rw [step_encode_odd g s u v hu hv hvo he]
    simp only [Frame,Bool.false_eq_true,if_false]
    constructor
    · omega
    · cases s <;> simp only [Bool.false_eq_true,if_false,if_true]
      all_goals apply abs_lt.mpr; constructor <;> omega

end ECDSAAdd.SkywalkRails
end

-- source: ECDSAAdd/Arithmetic/SignedWordBits.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Signed interpretation of a physical little-endian word. -/
def signedRegValue (r : List Wire) (s : BasisState) : Int :=
  signedDecode r.length (regValue r s)

/-- The physical MSB supplies the exact two's-complement sign correction. -/
theorem signedRegValue_msb (lo : List Wire) (sign : Wire) (s : BasisState) :
    signedRegValue (lo++[sign]) s=(regValue (lo++[sign]) s:Int)-
      if s sign then ((2^(lo.length+1):Nat):Int) else 0 := by
  have hh := regValue_highBit lo sign s
  unfold signedRegValue signedDecode
  simp only [List.length_append,List.length_singleton,Nat.add_sub_cancel]
  cases hs : s sign with
  | false =>
    have hb : regValue (lo++[sign]) s<2^lo.length := by
      have hn : ¬2^lo.length≤regValue (lo++[sign]) s := by
        intro h
        have ht := hh.mpr h
        rw [hs] at ht
        contradiction
      omega
    simp [hb]
  | true =>
    have hb : 2^lo.length≤regValue (lo++[sign]) s := hh.mp hs
    simp [Nat.not_lt.mpr hb]

/-- Negative signed value is equivalent to an asserted physical most significant bit. -/
theorem signedRegValue_neg_iff (lo : List Wire) (sign : Wire) (s : BasisState) :
    signedRegValue (lo++[sign]) s<0 ↔ s sign=true := by
  have hh := regValue_highBit lo sign s
  have hb := regValue_lt (lo++[sign]) s
  simp only [List.length_append,List.length_singleton] at hb
  unfold signedRegValue signedDecode
  simp only [List.length_append,List.length_singleton,Nat.add_sub_cancel]
  cases hs : s sign with
  | false =>
    have hlow : regValue (lo++[sign]) s<2^lo.length := by
      have hn : ¬2^lo.length≤regValue (lo++[sign]) s := by
        intro h
        have ht := hh.mpr h
        rw [hs] at ht
        contradiction
      omega
    rw [if_pos hlow]
    simp
  | true =>
    have hhigh : 2^lo.length≤regValue (lo++[sign]) s := hh.mp hs
    rw [if_neg (Nat.not_lt.mpr hhigh)]
    have hi : (regValue (lo++[sign]) s:Int)<((2^(lo.length+1):Nat):Int) :=
      Int.ofNat_lt.mpr hb
    have hneg : (regValue (lo++[sign]) s:Int)-((2^(lo.length+1):Nat):Int)<0 := by
      omega
    simpa using hneg

/-- Boolean arithmetic sign used by SkywalkRails is exactly the physical MSB. -/
theorem signedRegValue_sign (lo : List Wire) (sign : Wire) (s : BasisState) :
    s sign=SkywalkRails.neg (signedRegValue (lo++[sign]) s) := by
  have hh := signedRegValue_neg_iff lo sign s
  cases hs : s sign with
  | false =>
    have hn : ¬signedRegValue (lo++[sign]) s<0 := by
      intro h
      have ht := hh.mp h
      rw [hs] at ht
      contradiction
    simp [SkywalkRails.neg,hn]
  | true =>
    have hn : signedRegValue (lo++[sign]) s<0 := hh.mpr hs
    simp [SkywalkRails.neg,hn]

/-- Connect the same register convention to the independent Clifford half helper. -/
theorem signedRegValue_halfDecode (lo : List Wire) (sign : Wire) (s : BasisState) :
    signedRegValue (lo++[sign]) s=
      signedHalfDecode (lo.length+1) (s sign) (regValue (lo++[sign]) s) := by
  rw [signedRegValue_msb]
  simp only [signedHalfDecode,Nat.cast_pow,Nat.cast_ofNat]

/-- Subtracting a whole even word modulus cannot change parity. -/
theorem signedDecode_mod_two (w X : Nat) (hw : 0<w) :
    signedDecode w X%2=(X:Int)%2 := by
  have hp : 2^w=2*2^(w-1) := by
    calc
      2^w = 2^((w-1)+1) := by congr 1; omega
      _ = 2^(w-1)*2 := pow_succ _ _
      _ = 2*2^(w-1) := Nat.mul_comm _ _
  have hc := congrArg (fun a : Nat => (a:Int)) hp
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hc
  have hm : ((2^w:Nat):Int)%2=0 := by rw [hc]; omega
  unfold signedDecode
  split_ifs with h
  · rfl
  · rw [Int.sub_emod,hm]
    simp

/-- Exact logical evenness forces the physical low bit to zero before relabelled half. -/
theorem signedRegValue_even_iff (low : Wire) (tail : List Wire) (s : BasisState) :
    signedRegValue (low::tail) s%2=0 ↔ s low=false := by
  unfold signedRegValue
  rw [signedDecode_mod_two (low::tail).length (regValue (low::tail) s) (by simp)]
  cases hs : s low <;> simp [regValue,hs]

private theorem signed_int_spec_of_raw (q : Wire) (x y carry : List Wire) (p : Program)
    (hx : x.length=y.length) (hc : carry.length+1=y.length)
    (Q D : Bool) (A B : Int)
    (hlo : -((2^(y.length-1):Nat):Int)≤signedIntegerValue D A B)
    (hhi : signedIntegerValue D A B<((2^(y.length-1):Nat):Int))
    (hraw : ∀ X Y : Nat,
      (Triple (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y Y) ∧ Holds.holds st carry 0) p
      (fun st => ((Holds.holds st q Q ∧ Holds.holds st x X) ∧ Holds.holds st y (signedWordValue y.length D X Y)) ∧ Holds.holds st carry 0))) :
    Triple (fun s => s q=Q ∧ signedRegValue x s=A ∧ signedRegValue y s=B ∧ regValue carry s=0)
      p (fun s => s q=Q ∧ signedRegValue x s=A ∧
        signedRegValue y s=signedIntegerValue D A B ∧ regValue carry s=0) := by
  intro s m hin
  let X := regValue x s.basis
  let Y := regValue y s.basis
  have hX : X<2^y.length := by simpa only [X,hx] using regValue_lt x s.basis
  have hA : signedDecode y.length X=A := by
    have hh := hin.2.1
    change signedDecode x.length X=A at hh
    rw [hx] at hh
    exact hh
  have hB : signedDecode y.length Y=B := hin.2.2.1
  obtain ⟨hp,ho⟩ := hraw X Y s m ⟨⟨⟨hin.1,rfl⟩,rfl⟩,hin.2.2.2⟩
  have hw : 0<y.length := by omega
  have hv := signedWordValue_lift y.length D X Y hw hX
    (by rw [hA,hB]; exact hlo) (by rw [hA,hB]; exact hhi)
  rw [hA,hB] at hv
  refine ⟨hp,ho.1.1.1,?_,?_,ho.2⟩
  · unfold signedRegValue
    rw [ho.1.1.2]
    exact hin.2.1
  · unfold signedRegValue
    rw [ho.1.2]
    exact hv

/-- Native signed-add gate lifts to the exact unbounded integer rail operation,
provided the separately proved output bound fits the chosen signed word. -/
theorem signedAdd_int_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (A B : Int)
    (hlo : -((2^(y.length-1):Nat):Int)≤signedIntegerValue Q A B)
    (hhi : signedIntegerValue Q A B<((2^(y.length-1):Nat):Int)) :
    Triple (fun s => s q=Q ∧ signedRegValue x s=A ∧ signedRegValue y s=B ∧ regValue carry s=0)
      (signedAdd q x y carry) (fun s => s q=Q ∧ signedRegValue x s=A ∧
        signedRegValue y s=signedIntegerValue Q A B ∧ regValue carry s=0) :=
  signed_int_spec_of_raw q x y carry _ hx hc Q Q A B hlo hhi
    (fun X Y => signedAdd_spec q x y carry hn hx hc Q X Y)

/-- The inverse gate preserves the same physical control and reverses its signed direction. -/
theorem signedSub_int_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (A B : Int)
    (hlo : -((2^(y.length-1):Nat):Int)≤signedIntegerValue (!Q) A B)
    (hhi : signedIntegerValue (!Q) A B<((2^(y.length-1):Nat):Int)) :
    Triple (fun s => s q=Q ∧ signedRegValue x s=A ∧ signedRegValue y s=B ∧ regValue carry s=0)
      (signedSub q x y carry) (fun s => s q=Q ∧ signedRegValue x s=A ∧
        signedRegValue y s=signedIntegerValue (!Q) A B ∧ regValue carry s=0) :=
  signed_int_spec_of_raw q x y carry _ hx hc Q (!Q) A B hlo hhi
    (fun X Y => signedSub_spec q x y carry hn hx hc Q X Y)

/-- Physical Clifford half and its relabelled view implement the exact signed
integer half. The physical low-bit premise follows from logical evenness. -/
theorem skywalkSignedHalf_int (low sign : Wire) (mid : List Wire)
    (hsl : sign≠low) (hlo : low∉mid++[sign]) (s : State) (m : List Bool)
    (he : signedRegValue (low::(mid++[sign])) s.basis%2=0) :
    signedRegValue (skywalkHalfView low (mid++[sign]))
      (run (skywalkSignedHalf sign low) m s).basis =
      signedRegValue (low::(mid++[sign])) s.basis/2 := by
  let tail := mid++[sign]
  let t := run (skywalkSignedHalf sign low) m s
  have hbit : s.basis low=false := (signedRegValue_even_iff low tail s.basis).mp he
  have hsign : t.basis low=s.basis sign := by
    change (run (skywalkSignedHalf sign low) m s).basis low=s.basis sign
    rw [skywalkSignedHalf_correct sign low hsl s m hbit]
    simp [writeBit]
  have hraw : regValue (low::tail) s.basis=2*regValue tail s.basis := by
    simp [regValue,hbit]
  have hwidth : (low::mid).length+1=tail.length+1 := by simp [tail]
  have hin := signedRegValue_halfDecode (low::mid) sign s.basis
  change signedRegValue (low::tail) s.basis=
    signedHalfDecode ((low::mid).length+1) (s.basis sign) (regValue (low::tail) s.basis) at hin
  rw [hwidth,hraw] at hin
  have hout := signedRegValue_halfDecode tail low t.basis
  have hv := skywalkSignedHalf_value sign low tail hsl hlo s m hbit
  change regValue (tail++[low]) t.basis=
    regValue tail s.basis+2^tail.length*(s.basis sign).toNat at hv
  rw [hsign,hv,signedHalfDecode_half] at hout
  change signedRegValue (tail++[low]) t.basis=signedRegValue (low::tail) s.basis/2
  rw [hout,hin]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupCircuitViews.lean
noncomputable section

set_option maxHeartbeats 600000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic.BalancedCleanup
open BalancedField

 theorem complement_encoded (z : Int) : 2^256-1-encodeWord 256 z=encodeWord 256 (-z-1) := by
  have a := encodeWord_cast 256 z
  have b := encodeWord_cast 256 (-z-1)
  have ha := encodeWord_bound 256 z
  have hb := encodeWord_bound 256 (-z-1)
  norm_num only [Nat.reducePow] at a b ha hb ⊢
  omega

 theorem doubled_encoded (z : Int) (b : Bool) :
    encodeWord 256 (2*z+(b.toNat : Int))=2*encodeWord 255 z+b.toNat := by
  have a := encodeWord_cast 255 z
  have c := encodeWord_cast 256 (2*z+(b.toNat : Int))
  have ha := encodeWord_bound 255 z
  have hc := encodeWord_bound 256 (2*z+(b.toNat : Int))
  cases b <;> norm_num only [Bool.toNat_false,Bool.toNat_true,Nat.reducePow] at a c ha hc ⊢ <;> omega

 theorem encoded_nonnegative (n : Nat) (z : Int) (h0 : 0≤z)
    (h1 : z<((2^n : Nat) : Int)) : encodeWord n z=z.toNat := by
  unfold encodeWord
  rw [Int.emod_eq_of_lt h0 h1]

 theorem magnitude_encoded (R : Int) (hr : Centered R) :
    (if negative R then 2^256-1-encodeWord 256 R else encodeWord 256 R)=(magnitude R).toNat := by
  have hp := constants
  have hb := magnitude_bounds R hr
  have hr0 := hr
  unfold Centered at hr0
  by_cases hneg : R<0
  · simp only [magnitude,negative,hneg,decide_true,if_true]
    rw [complement_encoded]
    exact encoded_nonnegative _ _ (by omega) (by norm_num; omega)
  · simp only [magnitude,negative,hneg,decide_false]
    exact encoded_nonnegative _ _ (by omega) (by norm_num; omega)

 theorem result_msb (L : Layout) (hw : L.Widths) (R : Int) (hr : Centered R)
    (s : BasisState) (hs : regValue L.r s=encodeWord 256 R) : s L.rmsb=negative R := by
  have w := widths L hw
  have bit := regValue_highBit L.low L.rmsb s
  have sign := centerWord_sign (R : ECDSAAdd.Fp)
  simp only [centerWord,centerFp_of_center R hr] at sign
  rw [w.1] at bit
  change s L.rmsb=true ↔ 2^255≤regValue L.r s at bit
  rw [hs] at bit
  cases hb : s L.rmsb <;> by_cases hn : R<0 <;> simp [negative,hn] <;>
    simp [hb] at bit <;> omega

 theorem negativeLiteral_value : negativeLiteral=2^255-h.toNat := by
  have hp := constants
  have hi : (-h)%((2^255 : Nat) : Int)=((2^255 : Nat) : Int)-h := by
    have he : (((2^255 : Nat) : Int)-h)%((2^255 : Nat) : Int)=(-h)%((2^255 : Nat) : Int) := by
      rw [show ((2^255 : Nat) : Int)-h=(-h)+((2^255 : Nat) : Int) by ring]
      simp
    rw [Int.emod_eq_of_lt (by norm_num; omega) (by norm_num; omega)] at he
    exact he.symm
  have hc := encodeWord_cast 255 (-h)
  have ht := Int.toNat_of_nonneg (show 0≤h by omega)
  have hb : h.toNat≤2^255 := by norm_num at ⊢; omega
  unfold negativeLiteral
  rw [hi] at hc
  omega

 theorem prepareSign_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hs : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false) :
    let t := run (prepareSign L) m s
    regValue L.r t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀ q,q∉L.r → q≠L.lower → t.basis q=s.basis q) := by
  let c : State := ⟨s.phase,writeBit s.basis L.lower (s.basis L.lower ^^ s.basis L.rmsb)⟩
  have la : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have nd := (List.nodup_append'.mp (L.dataND hn)).1
  have before : regValue L.r c.basis=regValue L.r s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [c,writeBit,show q≠L.lower from fun he => la (he ▸ hq)])
  have lc : c.basis L.lower=negative R := by simp [c,writeBit,hz,result_msb L hw R hr s.basis hs]
  have body := signComplement_correct L.lower L.r nd la c m
  have w := widths L hw
  have hc : ∀ ms,run [.CX L.rmsb L.lower] ms s=c := by intro ms; rfl
  simp only [prepareSign,run_append,measurementCount,List.take_zero,List.drop_zero,hc]
  change regValue L.r (run (signComplement L.lower L.r) m c).basis=_ ∧ _
  refine ⟨?_,(body.2.1 L.lower la).trans lc,?_⟩
  · rw [body.2.2,before,hs,lc,w.2.1,magnitude_encoded R hr]
  · intro q hq hne
    exact (body.2.1 q hq).trans (by simp [c,writeBit,hne])

 theorem normalize_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hv : regValue L.low s.basis=(magnitude R).toNat)
    (hl : s.basis L.lower=negative R) (ho : s.basis L.one=false)
    (hc : ∀ q∈L.carry,s.basis q=false) :
    let t := run (normalize L) m s
    t.phase=s.phase ∧ regValue L.low t.basis=encodeWord 255 (normalizedR R) ∧
    ∀ q,q∉L.low → t.basis q=s.basis q := by
  have w := widths L hw
  have hAdd := literalConstAdd_correct L.low (L.carry.take 254) L.lower L.one negativeLiteral
    (L.normND hn) (by omega) s m ho (fun q hq => hc q (List.mem_of_mem_take hq))
  refine ⟨hAdd.1,?_,hAdd.2.1⟩
  rw [normalize,hAdd.2.2,hv,hl,negativeLiteral_value,w.1]
  have ar := normalizedR_lowword_arithmetic R hr
  have hp := constants
  have ht := Int.toNat_of_nonneg (show 0≤h by omega)
  have hb : h.toNat≤2^255 := by norm_num at ⊢; omega
  rw [ar.2]
  have he : (magnitude R).toNat+(2^255-h.toNat)+(negative R).toNat=
      (magnitude R).toNat+2^255-h.toNat+(negative R).toNat := by omega
  rw [he]

 theorem bias_value (lo : List Wire) (msb : Wire) (nd : (lo++[msb]).Nodup)
    (s : State) (m : List Bool) :
    (regValue (lo++[msb]) (run [.X msb] m s).basis : Int)=
      signedDecode (lo.length+1) (regValue (lo++[msb]) s.basis)+((2^lo.length : Nat) : Int) := by
  have away : msb∉lo := by
    have dis := (List.nodup_append'.mp nd).2.2
    exact fun hm => List.disjoint_left.mp dis hm (by simp)
  have high := signedRegValue_msb lo msb s.basis
  have keep : regValue lo (writeBit s.basis msb (!s.basis msb))=regValue lo s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [writeBit,show q≠msb from fun he => away (he ▸ hq)])
  simp only [signedRegValue,List.length_append,List.length_singleton] at high
  rw [regValue_append] at ⊢
  change ((regValue lo (writeBit s.basis msb (!s.basis msb))+
    2^lo.length*regValue [msb] (writeBit s.basis msb (!s.basis msb)) : Nat) : Int)=_
  rw [keep]
  have hv := regValue_append lo [msb] s.basis
  have sv : regValue [msb] (writeBit s.basis msb (!s.basis msb))=(!s.basis msb).toNat := by
    simp only [regValue,List.foldr_cons,List.foldr_nil,writeBit,Function.update_self]
    cases !s.basis msb <;> rfl
  have oldsv : regValue [msb] s.basis=(s.basis msb).toNat := by
    change (if s.basis msb then 1 else 0)=(s.basis msb).toNat
    cases s.basis msb <;> rfl
  rw [sv]
  rw [oldsv] at hv
  have hp : ((2^(lo.length+1) : Nat) : Int)=2*((2^lo.length : Nat) : Int) := by rw [pow_succ]; push_cast; ring
  rw [hp] at high
  have hvI : (regValue (lo++[msb]) s.basis : Int)=
      (regValue lo s.basis : Int)+((2^lo.length : Nat) : Int)*((s.basis msb).toNat : Int) := by exact_mod_cast hv
  simp only [Nat.cast_add,Nat.cast_mul] at ⊢
  cases hb : s.basis msb <;> simp only [hb,Bool.not_false,Bool.not_true,
    Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,if_false,if_true,
    Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,add_zero,sub_zero] at high hvI ⊢ <;> omega

 theorem prepareCompare_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 255 (normalizedR R))
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hL : s.basis L.lower=negative R) :
    let t := run (prepareCompare L) m s
    (regValue L.r t.basis : Int)=comparisonLeft B R+((2^255 : Nat) : Int) ∧
    (regValue L.y t.basis : Int)=viewedY B R Y+((2^255 : Nat) : Int) ∧
    (∀ q,q∉L.r → q∉L.y → t.basis q=s.basis q) := by
  let U := encodeWord 255 (normalizedR R)
  let v1 := run (rotateLeft L.r) m s
  let ins : Program := [.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]
  let v2 := run ins m v1
  let v3 := run (signComplement L.sign L.y) m v2
  let v4 := run (signComplement L.lower L.y) m v3
  let v5 := run [.X L.rmsb] m v4
  let v6 := run [.X L.ymsb] m v5
  have w := widths L hw
  have d := List.nodup_append'.mp (L.dataND hn)
  have dr := d.1
  have dy := (List.nodup_append'.mp d.2.1).1
  have dis := d.2.2
  have away (q : Wire) (hq : q∈[L.sign,L.lower]) : q∉L.r ∧ q∉L.y := by
    have a := L.flagAway hn q (by simp only [List.mem_cons] at hq ⊢; tauto)
    exact ⟨fun h => a (by simp [h]),fun h => a (by simp [h])⟩
  have r0R : L.r0∈L.r := by simp [Layout.r,Layout.low]
  have rmR : L.rmsb∈L.r := by simp [Layout.r]
  have ymY : L.ymsb∈L.y := by simp [Layout.y]
  have r0Y : L.r0∉L.y := fun h => List.disjoint_left.mp dis r0R (by simp [h])
  have rmY : L.rmsb∉L.y := fun h => List.disjoint_left.mp dis rmR (by simp [h])
  have ymR : L.ymsb∉L.r := fun h => List.disjoint_left.mp dis h (by simp [ymY])
  have sr : L.sign≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have lr : L.lower≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have rot0 := rotateLeft_spec L.r dr U (by have hu := encodeWord_bound 255 (normalizedR R); rw [w.2.1]; norm_num at ⊢; omega) s m hR
  have rot := rot0.2
  have rotfr := (rotate_frame L.r s m).2.2.2
  have S1 : v1.basis L.sign=B := (rotfr _ (away _ (by simp)).1).trans hS
  have L1 : v1.basis L.lower=negative R := (rotfr _ (away _ (by simp)).1).trans hL
  have low0 : v1.basis L.r0=false := by
    change regValue (L.r0::(L.rtail++[L.rmsb])) v1.basis=2*U at rot
    change (if v1.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v1.basis=2*U at rot
    cases e : v1.basis L.r0
    · rfl
    · simp [e] at rot
      omega
  have tail1 : regValue (L.rtail++[L.rmsb]) v1.basis=U := by
    change (if v1.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v1.basis=2*U at rot
    rw [low0] at rot; simp only [Bool.false_eq_true,if_false,zero_add] at rot; omega
  have I2 : v2.basis L.r0=!(B ^^ negative R) := by
    cases b : B <;> cases l : negative R <;> simp [v2,ins,run,writeBit,sr,lr,S1,L1,low0,b,l]
  have out2 (q : Wire) (hq : q≠L.r0) : v2.basis q=v1.basis q := by simp [v2,ins,run,writeBit,hq]
  have S2 : v2.basis L.sign=B := (out2 _ sr).trans S1
  have L2 : v2.basis L.lower=negative R := (out2 _ lr).trans L1
  have tailAway : L.r0∉L.rtail++[L.rmsb] := (List.nodup_cons.mp dr).1
  have R2 : regValue L.r v2.basis=encodeWord 256 (comparisonLeft B R) := by
    change (if v2.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v2.basis=_
    rw [regValue_congr _ _ _ (fun q hq => out2 q (fun e => tailAway (e ▸ hq))),tail1,I2]
    have ib : insertBit B R=((!(B ^^ negative R)).toNat : Int) := by
      cases e : !(B ^^ negative R) <;> simp [insertBit,e]
    rw [comparisonLeft,ib,doubled_encoded]
    cases e : !(B ^^ negative R) <;> simp [U,Bool.toNat,Nat.add_comm]
  have Y2 : regValue L.y v2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => (out2 q (fun e => r0Y (e ▸ hq))).trans
      (rotfr q (fun hrq => List.disjoint_left.mp dis hrq (by simp [hq]))))).trans hY
  have cS := signComplement_correct L.sign L.y dy (away _ (by simp)).2 v2 m
  have cL := signComplement_correct L.lower L.y dy (away _ (by simp)).2 v3 m
  have L3 : v3.basis L.lower=negative R := (cS.2.1 _ (away _ (by simp)).2).trans L2
  have R4 : regValue L.r v4.basis=encodeWord 256 (comparisonLeft B R) := by
    exact (regValue_congr _ _ _ (fun q hq => (cL.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))).trans (cS.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))))).trans R2
  have Y4 : regValue L.y v4.basis=encodeWord 256 (viewedY B R Y) := by
    rw [cL.2.2,cS.2.2,L3,S2,Y2,w.2.2.1]
    have hb := encodeWord_bound 256 Y
    have comp := complement_encoded Y
    cases B <;> cases l : negative R <;> simp [viewedY,l] <;> omega
  have decoded := comparison_words_decode B R Y hr hy
  have bvR := bias_value L.low L.rmsb dr v4 m
  have bvY := bias_value L.ylow L.ymsb dy v5 m
  have Y5 : regValue L.y v5.basis=regValue L.y v4.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [v5,run,writeBit,show q≠L.rmsb from fun e => rmY (e ▸ hq)])
  have R6 : regValue L.r v6.basis=regValue L.r v5.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [v6,run,writeBit,show q≠L.ymsb from fun e => ymR (e ▸ hq)])
  rw [w.1] at bvR
  change (regValue L.r v5.basis : Int)=signedDecode 256 (regValue L.r v4.basis)+((2^255 : Nat) : Int) at bvR
  rw [R4,decoded.1] at bvR
  rw [hw.2.1] at bvY
  change (regValue L.y v6.basis : Int)=signedDecode 256 (regValue L.y v5.basis)+((2^255 : Nat) : Int) at bvY
  rw [Y5,Y4,decoded.2] at bvY
  have emptyRot (t : State) : run (rotateLeft L.r) (m.take 0) t=run (rotateLeft L.r) m t := by
    simpa only [(rotate_counts L.r).2.2.2] using run_take (rotateLeft L.r) m t
  have emptyS (t : State) : run (signComplement L.sign L.y) (m.take 0) t=run (signComplement L.sign L.y) m t := by
    simpa only [(signComplement_counts L.sign L.y).2] using run_take (signComplement L.sign L.y) m t
  have emptyL (t : State) : run (signComplement L.lower L.y) (m.take 0) t=run (signComplement L.lower L.y) m t := by
    simpa only [(signComplement_counts L.lower L.y).2] using run_take (signComplement L.lower L.y) m t
  have execute : run (prepareCompare L) m s=v6 := by
    simp only [prepareCompare,List.append_assoc,run_append,
      (rotate_counts L.r).2.2.2,(signComplement_counts L.sign L.y).2,
      (signComplement_counts L.lower L.y).2,measurementCount,List.drop_zero,emptyRot,emptyS,emptyL]
    rfl
  rw [execute]
  refine ⟨by rw [R6]; exact bvR,bvY,?_⟩
  intro q qr qy
  have nr : q≠L.r0 := fun e => qr (e ▸ r0R)
  have nm : q≠L.rmsb := fun e => qr (e ▸ rmR)
  have ny : q≠L.ymsb := fun e => qy (e ▸ ymY)
  have v56 : v6.basis q=v4.basis q := by simp [v6,v5,run,writeBit,nm,ny]
  exact v56.trans ((cL.2.1 q qy).trans ((cS.2.1 q qy).trans ((out2 q nr).trans (rotfr q qr))))

end ECDSAAdd.Arithmetic.BalancedCleanup
end

-- source: ECDSAAdd/Arithmetic/ConditionalXor.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 两个可变寄存器以外逐线保持初始状态。 -/
def PairFrame (temp dst : List Wire) (base : BasisState) (T O : Nat) (st : BasisState) : Prop :=
  regValue temp st = T ∧ regValue dst st = O ∧
    ∀ w, w ∉ temp → w ∉ dst → st w = base w

namespace PairFrame

theorem update_temp (temp dst : List Wire) (base s t : BasisState) (T O Z : Nat)
    (hd : temp.Disjoint dst) (h : PairFrame temp dst base T O s)
    (he : ∀ w, w ∉ temp → t w = s w) (hz : regValue temp t = Z) :
    PairFrame temp dst base Z O t :=
  ⟨hz, (regValue_congr _ _ _ (fun w hw => he w
    (fun hh => List.disjoint_left.mp hd hh hw))).trans h.2.1,
    fun w ht hd => (he w ht).trans (h.2.2 w ht hd)⟩

theorem update_dst (temp dst : List Wire) (base s t : BasisState) (T O Z : Nat)
    (hd : temp.Disjoint dst) (h : PairFrame temp dst base T O s)
    (he : ∀ w, w ∉ dst → t w = s w) (hz : regValue dst t = Z) :
    PairFrame temp dst base T Z t :=
  ⟨(regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp hd hw))).trans h.1,
    hz, fun w ht hd => (he w hd).trans (h.2.2 w ht hd)⟩

end PairFrame

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredMaskedAdder.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 清除已知等于控制与来源逐位AND的掩码；每位只依赖本次测量记录。 -/
def eraseMask (c : Wire) : List Wire → List Wire → Program
  | a::src, b::dst => .measureX b [] [.CZ c a] :: eraseMask c src dst
  | _, _ => []

private theorem eraseMask_bit (c a b : Wire) (hc : c≠b) (ha : a≠b)
    (s : State) (h : s.basis b = (s.basis c && s.basis a)) (v : Bool) :
    measureAndCorrect b [] [.CZ c a] v s = ⟨s.phase,writeBit s.basis b false⟩ := by
  cases v <;> simp [measureAndCorrect,correct,writeBit,h,hc,ha]

/-- 掩码关系是清理前提；来源、控制和掩码以外的位保持。 -/
theorem eraseMask_correct (c : Wire) (src dst : List Wire)
    (hlen : src.length=dst.length) (hnd : (c::(src++dst)).Nodup)
    (s : State) (m : List Bool)
    (hmask : regValue dst s.basis = if s.basis c then regValue src s.basis else 0) :
    (run (eraseMask c src dst) m s).phase=s.phase ∧
    (∀ w, w∉dst → (run (eraseMask c src dst) m s).basis w=s.basis w) ∧
    regValue dst (run (eraseMask c src dst) m s).basis=0 := by
  induction src generalizing dst s m with
  | nil =>
    have hd : dst=[] := List.eq_nil_of_length_eq_zero hlen.symm
    subst dst
    simp [eraseMask,run,regValue]
  | cons a src ih =>
    cases dst with
    | nil => simp at hlen
    | cons b dst =>
      have hn := List.nodup_cons.mp hnd
      obtain ⟨hs,hd,hsd⟩ := List.nodup_append'.mp hn.2
      have hcb : c≠b := fun h => hn.1 (by simp [h])
      have hab : a≠b := fun h => List.disjoint_left.mp hsd (List.mem_cons_self : a∈a::src) (by simp [h])
      have hbs : b∉src := fun h => List.disjoint_left.mp hsd (List.mem_cons_of_mem a h) (List.mem_cons_self)
      have hbd : b∉dst := (List.nodup_cons.mp hd).1
      have ht : (c::(src++dst)).Nodup := List.nodup_cons.mpr ⟨
        (fun h => hn.1 (by simp only [List.mem_append,List.mem_cons] at h ⊢; tauto)),
        List.nodup_append'.mpr ⟨(List.nodup_cons.mp hs).2,(List.nodup_cons.mp hd).2,
          List.disjoint_left.mpr (fun _ hx hy => List.disjoint_left.mp hsd (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem b hy))⟩⟩
      have hb : s.basis b = (s.basis c && s.basis a) := by
        change (if s.basis b then 1 else 0)+2*regValue dst s.basis =
          (if s.basis c then (if s.basis a then 1 else 0)+2*regValue src s.basis else 0) at hmask
        cases hc : s.basis c <;> cases ha : s.basis a <;> cases hb : s.basis b <;> simp_all <;> omega
      have hv : regValue dst s.basis = if s.basis c then regValue src s.basis else 0 := by
        change (if s.basis b then 1 else 0)+2*regValue dst s.basis =
          (if s.basis c then (if s.basis a then 1 else 0)+2*regValue src s.basis else 0) at hmask
        cases hc : s.basis c <;> cases ha : s.basis a <;> cases hb : s.basis b <;> simp_all
      let t : State := ⟨s.phase,writeBit s.basis b false⟩
      have keep (w : Wire) (hw : w≠b) : t.basis w=s.basis w := by simp [t,writeBit,hw]
      have vs : regValue src t.basis=regValue src s.basis := regValue_congr _ _ _
        (fun w hw => keep w (fun h => hbs (h ▸ hw)))
      have vd : regValue dst t.basis=regValue dst s.basis := regValue_congr _ _ _
        (fun w hw => keep w (fun h => hbd (h ▸ hw)))
      have hm : regValue dst t.basis = if t.basis c then regValue src t.basis else 0 := by
        rw [vs,vd,keep c hcb]; exact hv
      obtain ⟨hp,he,hz⟩ := ih dst (by simpa using hlen) ht t m.tail hm
      simp only [eraseMask,run,eraseMask_bit c a b hcb hab s hb]
      change (run (eraseMask c src dst) m.tail t).phase=s.phase ∧ _
      refine ⟨hp,?_,?_⟩
      · intro w hw
        have hw' : w≠b ∧ w∉dst := by simpa using hw
        exact (he w hw'.2).trans (keep w hw'.1)
      · change (if (run (eraseMask c src dst) m.tail t).basis b then 1 else 0)+2*regValue dst _=0
        rw [he b hbd,hz]
        simp [t,writeBit]


/-- 在确定掩码输入上，测量清理与旧CCX清理恢复完全相同的状态。 -/
theorem eraseMask_eq_copy (c : Wire) (src dst : List Wire)
    (hlen : src.length=dst.length) (hnd : (c::(src++dst)).Nodup)
    (s : State) (m : List Bool)
    (hm : regValue dst s.basis = if s.basis c then regValue src s.basis else 0) :
    run (eraseMask c src dst) m s = run (copyRegister (some c) src dst) m s := by
  obtain ⟨hp,he,hz⟩ := eraseMask_correct c src dst hlen hnd s m hm
  have hn := List.nodup_cons.mp hnd
  have hc : c∉dst := fun h => hn.1 (by simp [h])
  obtain ⟨cp,ce,cv⟩ := copyRegister_correct (some c) src dst hlen hn.2 (by simpa using hc) s m
  have cz : regValue dst (run (copyRegister (some c) src dst) m s).basis=0 := by
    rw [cv,hm]; simp [copyValue]
  have hb : (run (eraseMask c src dst) m s).basis=(run (copyRegister (some c) src dst) m s).basis := by
    funext w
    by_cases hw : w∈dst
    · exact ((regValue_zero _ _).mp hz w hw).trans ((regValue_zero _ _).mp cz w hw).symm
    · exact (he w hw).trans (ce w hw).symm
  cases hx : run (eraseMask c src dst) m s
  cases hy : run (copyRegister (some c) src dst) m s
  simp_all

/-- 受控加法中段保持掩码关系，末段用测量和CZ归零。 -/
def measuredMaskedAddInPlace (c : Wire) (src t y carry : List Wire) (cin : Wire) : Program :=
  copyRegister (some c) src t ++ addInPlace t y carry cin ++ eraseMask c src t

def measuredMaskedSubInPlace (c : Wire) (src t y carry : List Wire) (cin : Wire) : Program :=
  copyRegister (some c) src t ++ subInPlace t y carry cin ++ eraseMask c src t

theorem eraseMask_counts (c : Wire) (src dst : List Wire) (hlen : src.length=dst.length) :
    toffoliCount (eraseMask c src dst)=0 ∧ measurementCount (eraseMask c src dst)=dst.length := by
  induction src generalizing dst with
  | nil => have hd : dst=[] := List.eq_nil_of_length_eq_zero hlen.symm; subst dst; simp [eraseMask,toffoliCount,measurementCount]
  | cons a src ih =>
    cases dst with
    | nil => simp at hlen
    | cons b dst =>
      have h := ih dst (by simpa using hlen)
      simp [eraseMask,toffoliCount,measurementCount,h.1,h.2,Nat.add_comm]

theorem eraseMask_wires_subset (c : Wire) (src dst : List Wire) :
    wires (eraseMask c src dst) ⊆ (c::(src++dst)).toFinset := by
  induction src generalizing dst with
  | nil => simp [eraseMask,wires]
  | cons a src ih =>
    cases dst with
    | nil => simp [eraseMask,wires]
    | cons b dst =>
      intro w hw
      have ht := ih dst
      simp only [eraseMask,wires,Instr.wires,correctionWires] at hw
      have ha : w∈wires (eraseMask c src dst) → w∈(c::(src++dst)).toFinset := fun h => ht h
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
        List.mem_toFinset,List.mem_cons,List.mem_append] at hw ha ⊢
      tauto

theorem measuredMaskedInPlace_wires (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hs : src.length=t.length) (ht : t.length=y.length) (hc : carry.length+1=y.length) :
    wires (measuredMaskedAddInPlace c src t y carry cin)=(c::cin::(src++t++y++carry)).toFinset ∧
    wires (measuredMaskedSubInPlace c src t y carry cin)=(c::cin::(src++t++y++carry)).toFinset := by
  have hn : src≠[] := by intro h; simp [h] at hs; omega
  have cp := copyRegister_wires (some c) src t hs
  simp only [List.isEmpty_iff,hn,if_false,Option.toList_some,List.cons_append,List.nil_append] at cp
  have ep := eraseMask_wires_subset c src t
  constructor
  · rw [measuredMaskedAddInPlace,wires_append,wires_append,cp,addInPlace_wires t y carry cin ht hc]
    ext w
    have he := @ep w
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append] at he ⊢
    tauto
  · rw [measuredMaskedSubInPlace,wires_append,wires_append,cp,subInPlace_wires t y carry cin ht hc]
    ext w
    have he := @ep w
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append] at he ⊢
    tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/ModularHalving.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Math/HalvingBijection.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Math/ModInPlace.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 扩展源范围允许 A=p；一次约减后与源比较，恰好恢复减 p 时的借位。 -/
theorem modAddCore_cleanup (A Z p : Nat) (hA : A ≤ p) (hZ : Z < p) :
    (A + Z < p ↔ A ≤ (A + Z) % p) := by
  by_cases h : A + Z < p
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have hr : A + Z - p < p := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hr]
    omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModInPlace.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 模加核的固定线路：最高位借作约减标志；mask/flag 属于外层，不放入核工作区。 -/
structure ModAddCoreLayout where
  a : List Wire
  low : List Wire
  high : Wire
  constant : List Wire
  carry : List Wire
  cin : Wire

namespace ModAddCoreLayout

def z (L : ModAddCoreLayout) : List Wire := L.low ++ [L.high]
def work (L : ModAddCoreLayout) : List Wire := L.constant ++ L.carry ++ [L.cin]

end ModAddCoreLayout

/-- 四个可辨认阶段：计算扩宽和、试减 p、借位时低位加回 p、由结果与源比较清借位。
constant/carry/cin 初末零；核源可以是外层已装载的 mask，不能提前清该源。 -/
def modAddCore (L : ModAddCoreLayout) (p : Nat) : Program :=
  -- 1. 高位初始零；扩宽寄存器容纳完整 A+Z。
  addInPlace L.a L.z L.carry L.cin ++
  -- 2. 试减 p；结果最高位记录 A+Z<p。装卸常数不影响该标志。
  xorConstant L.constant p ++ subInPlace L.constant L.z L.carry L.cin ++
  xorConstant L.constant p ++
  -- 3. 借位为真时只向低位加回 p，最高位保持直到最后比较。
  maskedAddConst L.high (L.constant.take L.low.length) L.low
    (L.carry.take (L.low.length-1)) L.cin p ++
  -- 4. 规范结果小于源当且仅当曾约减；比较后 X 清原借位。
  compareLt none L.low (L.a.take L.low.length) L.carry L.cin L.high ++ [.X L.high]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModInPlaceCopy.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModInPlaceWrappers.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 外层模算术布局：核工作区之外的 mask 用于受控源，flag 留给单目半倍。
子视图只借用线路，不把 mask 重复加入核工作区。 -/
structure ModInPlaceLayout extends ModAddCoreLayout where
  mask : List Wire
  flag : Wire

namespace ModInPlaceLayout

def z (L : ModInPlaceLayout) : List Wire := L.toModAddCoreLayout.z
def work (L : ModInPlaceLayout) : List Wire := L.toModAddCoreLayout.work ++ L.mask ++ [L.flag]
def wires (L : ModInPlaceLayout) : List Wire := L.a ++ L.z ++ L.work

end ModInPlaceLayout

/-- 普通模加直接调用核，未使用的 mask/flag 保持零。 -/
def modAddInPlace (L : ModInPlaceLayout) (p : Nat) : Program := modAddCore L.toModAddCoreLayout p

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModularFrame.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModularPorts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PoolLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 工作池的连续切片。w 把池内偏移映射到调用方线路。 -/
def wireBlock (w : Nat → Wire) (start count : Nat) : List Wire :=
  (List.range' start count).map w

theorem wireBlock_append (w : Nat → Wire) (start a b : Nat) :
    wireBlock w start a++wireBlock w (start+a) b=wireBlock w start (a+b) := by
  simp only [wireBlock,← List.map_append,← List.range'_append,Nat.one_mul]

theorem wireBlock_length (w : Nat → Wire) (start count : Nat) :
    (wireBlock w start count).length=count := by simp [wireBlock]

theorem wireBlock_flatMap (w : Nat → Wire) (start width count : Nat) :
    ((List.range count).flatMap (fun i => wireBlock w (start+width*i) width))=
      wireBlock w start (width*count) := by
  induction count with
  | zero => simp [wireBlock]
  | succ count ih =>
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,ih]
    rw [wireBlock_append,Nat.mul_succ]

def poolModBit (w : Nat → Wire) (start : Nat) : ModBit :=
  ⟨w start,w (start+1),w (start+2),w (start+3),w (start+4),
    w (start+5),w (start+6),w (start+7)⟩

def poolMod (w : Nat → Wire) (start width : Nat) : ModLayout :=
  ⟨(List.range width).map (fun i => poolModBit w (start+2+8*i)),
    poolModBit w (start+2+8*width),w start,w (start+1)⟩

theorem poolMod_bits (w : Nat → Wire) (start width : Nat) :
    (poolMod w start width).bits=
      (List.range (width+1)).map (fun i => poolModBit w (start+2+8*i)) := by
  simp [poolMod,ModLayout.bits,List.range_succ]

theorem poolModBit_wires (w : Nat → Wire) (start : Nat) :
    (poolModBit w start).all=wireBlock w start 8 := by
  simp [poolModBit,ModBit.all,wireBlock,List.range',Nat.add_assoc]

theorem poolMod_wires (w : Nat → Wire) (start width : Nat) :
    (poolMod w start width).wires=wireBlock w start (2+8*(width+1)) := by
  simp only [ModLayout.wires,poolMod_bits,List.flatMap_map,poolModBit_wires]
  rw [wireBlock_flatMap]
  change w start::w (start+1)::wireBlock w (start+2) (8*(width+1))=_
  rw [← wireBlock_append]
  rfl

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SwapRegisters.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 向量形式 Fredkin 分解；每对位使用两次 CX 和一次 CCX。 -/
def swapRegisters (c : Wire) (a b : List Wire) : Program :=
  copyRegister none b a ++ copyRegister (some c) a b ++ copyRegister none b a

private theorem copy_back (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (c::(a++b)).Nodup) (C : Bool) (A B : Nat) :
    (Triple (fun st => (Holds.holds st c C ∧ Holds.holds st a A) ∧ Holds.holds st b B) (copyRegister none b a)
      (fun st => (Holds.holds st c C ∧ Holds.holds st a (A ^^^ B)) ∧ Holds.holds st b B)) := by
  intro s m h
  have hh := List.nodup_cons.mp hnd
  have hc : c ∉ a := fun h => hh.1 (List.mem_append_left _ h)
  have hba : (b++a).Nodup := by simpa only [List.nodup_append_comm] using hh.2
  have hb := (List.nodup_append'.mp hba).2.2
  obtain ⟨hp, he, hv⟩ := copyRegister_correct none b a hlen.symm hba (by simp) s m
  refine ⟨hp, ⟨(he c hc).trans h.1.1, ?_⟩, ?_⟩
  · simpa only [copyValue, show regValue a s.basis=A from h.1.2,
      show regValue b s.basis=B from h.2] using hv
  · exact (regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp hb hw))).trans h.2

/-- 寄存器长度相同且全部互异；控制为真时交换，否则保持两者。 -/
theorem swapRegisters_spec (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (c::(a++b)).Nodup) (C : Bool) (A B : Nat) :
    (Triple (fun st => (Holds.holds st c C ∧ Holds.holds st a A) ∧ Holds.holds st b B) (swapRegisters c a b)
      (fun st => (Holds.holds st c C ∧ Holds.holds st a (if C then B else A)) ∧ Holds.holds st b (if C then A else B))) := by
  have h1 := copy_back c a b hlen hnd C A B
  have h2 := maskedCopy_spec c a b hlen hnd C (A ^^^ B) B
  have h3 := copy_back c a b hlen hnd C (A ^^^ B) (B ^^^ (if C then A ^^^ B else 0))
  have h := h1.seq (h2.seq h3)
  have he : B ^^^ (if C then A ^^^ B else 0) = if C then A else B := by
    cases C <;> simp [Nat.xor_left_comm]
  have hf : (A ^^^ B) ^^^ (B ^^^ (if C then A ^^^ B else 0)) = if C then B else A := by
    rw [he]
    cases C <;> simp [Nat.xor_right_comm]
  rw [hf] at h
  simpa only [swapRegisters, List.append_assoc, he] using h

theorem swapRegisters_resources (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (c::(a++b)).Nodup) :
    toffoliCount (swapRegisters c a b) = a.length ∧
    measurementCount (swapRegisters c a b) = 0 ∧
    qubitCount (swapRegisters c a b) = (if a.isEmpty then 0 else 2*a.length+1) := by
  have h1 := copyRegister_counts none b a hlen.symm
  have h2 := copyRegister_counts (some c) a b hlen
  have hwa := copyRegister_wires (some c) a b hlen
  have hwb := copyRegister_wires none b a hlen.symm
  have he : b.isEmpty = a.isEmpty := by
    cases a <;> cases b <;> simp_all
  refine ⟨by simp [swapRegisters, toffoliCount_append, h1.1, h2.1],
    by simp [swapRegisters, measurementCount_append, h1.2, h2.2], ?_⟩
  rw [qubitCount, swapRegisters, wires_append, wires_append, hwa, hwb, he]
  split_ifs
  · simp
  · have hw : (none.toList ++ b ++ a).toFinset ∪ ((some c).toList ++ a ++ b).toFinset ∪
        (none.toList ++ b ++ a).toFinset = (c::(a++b)).toFinset := by
      ext w; simp; tauto
    rw [hw, List.toFinset_card_of_nodup hnd]
    simp [← hlen]; omega

/-- 无控制交换不需要 Toffoli，用于把新值移回固定的寄存器位置。 -/
def exchangeRegisters (a b : List Wire) : Program :=
  copyRegister none b a ++ copyRegister none a b ++ copyRegister none b a

theorem swapRegisters_wires (c : Wire) (a b : List Wire) (hlen : a.length=b.length) :
    wires (swapRegisters c a b) ⊆ (c::(a++b)).toFinset := by
  have wa := copyRegister_wires (some c) a b hlen
  have wb := copyRegister_wires none b a hlen.symm
  intro w hw
  simp only [swapRegisters, wires_append, Finset.mem_union] at hw
  have ha : w∈wires (copyRegister (some c) a b) → w∈(c::(a++b)).toFinset := by
    rw [wa]; split_ifs <;> simp_all
  have hb : w∈wires (copyRegister none b a) → w∈(c::(a++b)).toFinset := by
    rw [wb]; split_ifs <;> simp_all [or_comm]
  tauto

/-- 两个目标寄存器以外逐线保持，包括控制线。 -/
theorem swapRegisters_correct (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (c::(a++b)).Nodup) (s : State) (m : List Bool) :
    (run (swapRegisters c a b) m s).phase=s.phase ∧
    (∀ w, w∉a → w∉b → (run (swapRegisters c a b) m s).basis w=s.basis w) ∧
    regValue a (run (swapRegisters c a b) m s).basis =
      (if s.basis c then regValue b s.basis else regValue a s.basis) ∧
    regValue b (run (swapRegisters c a b) m s).basis =
      (if s.basis c then regValue a s.basis else regValue b s.basis) := by
  obtain ⟨hp,hv⟩ := swapRegisters_spec c a b hlen hnd (s.basis c)
    (regValue a s.basis) (regValue b s.basis) s m ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨hp,?_,hv.1.2,hv.2⟩
  intro w ha hb
  by_cases hc : w=c
  · subst w; exact hv.1.1
  · apply run_preserves_outside
    intro hm
    have ht := swapRegisters_wires c a b hlen hm
    simp [ha,hb,hc] at ht

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkRoute.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Extract first-rail parity as history, swap only high rail bits, and make
the retained odd rail's low bit one. The even low bit is represented by zero
in the mathematical source word rather than physically swapping the history. -/
def skywalkRoute (a0 b0 : Wire) (ah bh : List Wire) : Program :=
  swapRegisters a0 ah bh ++ [.CX a0 b0]

theorem skywalkRoute_correct (a0 b0 : Wire) (ah bh : List Wire)
    (hlen : ah.length=bh.length) (hnd : (a0::b0::(ah++bh)).Nodup)
    (s : State) (m : List Bool) (hp : s.basis b0=(!s.basis a0)) :
    (run (skywalkRoute a0 b0 ah bh) m s).phase=s.phase ∧
    (∀ q, q∉ah → q∉bh → q≠b0 →
      (run (skywalkRoute a0 b0 ah bh) m s).basis q=s.basis q) ∧
    (run (skywalkRoute a0 b0 ah bh) m s).basis a0=s.basis a0 ∧
    (run (skywalkRoute a0 b0 ah bh) m s).basis b0=true ∧
    regValue ah (run (skywalkRoute a0 b0 ah bh) m s).basis=
      (if s.basis a0 then regValue bh s.basis else regValue ah s.basis) ∧
    regValue bh (run (skywalkRoute a0 b0 ah bh) m s).basis=
      (if s.basis a0 then regValue ah s.basis else regValue bh s.basis) := by
  have hn : (a0::(ah++bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons] at hh ⊢
    omega
  have hab0 : a0≠b0 := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have haa : a0∉ah := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have hab : a0∉bh := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have hba : b0∉ah := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [h])
  have hbb : b0∉bh := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [h])
  let t := run (swapRegisters a0 ah bh) m s
  let out : State := ⟨t.phase,writeBit t.basis b0 (t.basis b0 ^^ t.basis a0)⟩
  have hm := (swapRegisters_resources a0 ah bh hlen hn).2.1
  have hr := run_take (swapRegisters a0 ah bh) m s
  rw [hm,List.take_zero] at hr
  have hout : run (skywalkRoute a0 b0 ah bh) m s=out := by
    rw [skywalkRoute,run_append,hm,List.take_zero,List.drop_zero,hr]
    rfl
  obtain ⟨ht,he,ha,hb⟩ := swapRegisters_correct a0 ah bh hlen hn s m
  have hc : t.basis a0=s.basis a0 := he a0 haa hab
  have hlo : t.basis b0=(!s.basis a0) := (he b0 hba hbb).trans hp
  have hav : regValue ah out.basis=regValue ah t.basis := by
    apply regValue_congr
    intro q hq
    have hqb : q≠b0 := fun h => hba (h ▸ hq)
    simp [out,writeBit,hqb]
  have hbv : regValue bh out.basis=regValue bh t.basis := by
    apply regValue_congr
    intro q hq
    have hqb : q≠b0 := fun h => hbb (h ▸ hq)
    simp [out,writeBit,hqb]
  rw [hout]
  refine ⟨ht,?_,?_,?_,hav.trans ha,hbv.trans hb⟩
  · intro q hqa hqb hq0
    simpa [out,writeBit,hq0] using he q hqa hqb
  · simpa [out,writeBit,hab0] using hc
  · simp [out,writeBit,hlo,hc]

theorem skywalkRoute_counts (a0 b0 : Wire) (ah bh : List Wire)
    (hlen : ah.length=bh.length) (hnd : (a0::b0::(ah++bh)).Nodup) :
    toffoliCount (skywalkRoute a0 b0 ah bh)=ah.length ∧
    measurementCount (skywalkRoute a0 b0 ah bh)=0 := by
  have hn : (a0::(ah++bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons] at hh ⊢
    omega
  have h := swapRegisters_resources a0 ah bh hlen hn
  simp [skywalkRoute,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,h.1,h.2.1]

theorem skywalkRoute_wires_subset (a0 b0 : Wire) (ah bh : List Wire)
    (hlen : ah.length=bh.length) :
    wires (skywalkRoute a0 b0 ah bh)⊆(a0::b0::(ah++bh)).toFinset := by
  have hs := swapRegisters_wires a0 ah bh hlen
  intro q hq
  have h : q∈wires (swapRegisters a0 ah bh) → q∈a0::(ah++bh) :=
    fun hh => List.mem_toFinset.mp (hs hh)
  simp only [skywalkRoute,wires_append,wires,Instr.wires,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
  simp only [List.mem_cons,List.mem_append] at h
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkIntegerLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- The retired first low bit stores orientation history. A distinct clean
extension avoids duplicating the old MSB in the full-width source view. -/
structure SkywalkIntegerLayout where
  a0 : Wire
  b0 : Wire
  ext : Wire
  history : Wire
  previous : Wire
  aSign : Wire
  bSign : Wire
  aMid : List Wire
  bMid : List Wire
  carry : List Wire

namespace SkywalkIntegerLayout

def ah (L : SkywalkIntegerLayout) : List Wire := L.aMid++[L.aSign]
def bh (L : SkywalkIntegerLayout) : List Wire := L.bMid++[L.bSign]
def a (L : SkywalkIntegerLayout) : List Wire := L.a0::L.ah
def b (L : SkywalkIntegerLayout) : List Wire := L.b0::L.bh
def half (L : SkywalkIntegerLayout) : List Wire := L.ah++[L.ext]
def wires (L : SkywalkIntegerLayout) : List Wire :=
  L.previous::L.history::L.ext::L.a0::L.b0::(L.ah++L.bh++L.carry)

structure Valid (L : SkywalkIntegerLayout) : Prop where
  mids : L.aMid.length=L.bMid.length
  carry : L.carry.length=L.ah.length
  nodup : L.wires.Nodup

theorem route_nodup (L : SkywalkIntegerLayout) (hv : L.Valid) :
    (L.a0::L.b0::(L.ah++L.bh)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,List.count_cons,List.count_append] at hh ⊢
  omega

theorem record_nodup (L : SkywalkIntegerLayout) (hv : L.Valid) :
    (L.history::(L.half++L.b++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,half,b,List.count_cons,List.count_append,List.count_nil] at hh ⊢
  omega

theorem high_lengths (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.ah.length=L.bh.length := by simp [ah,bh,hv.mids]

theorem record_lengths (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.half.length=L.b.length ∧ L.carry.length+1=L.b.length := by
  have hh := L.high_lengths hv
  simp only [half,b,List.length_append,List.length_cons,List.length_nil,hv.carry]
  omega

end SkywalkIntegerLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkPool.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Fixed exact campaign: 258-bit signed words and all 512 logical rounds. -/
def skywalkPoolWires (w : Nat → Wire) : List Wire := wireBlock w 0 1798

def skywalkPoolPreviousId (i : Nat) : Nat := if i=0 then 1797 else i-1

def skywalkPoolTick (w : Nat → Wire) (i : Nat) : SkywalkIntegerLayout :=
  { a0:=w i,b0:=w 770,ext:=w (i+258),history:=w (1028+i),
    previous:=w (skywalkPoolPreviousId i),aSign:=w (i+257),bSign:=w 1027,
    aMid:=wireBlock w (i+1) 256,bMid:=wireBlock w 771 256,
    carry:=wireBlock w 1540 257 }

def skywalkPoolTickIds (i : Nat) : List Nat :=
  skywalkPoolPreviousId i::(1028+i)::(i+258)::i::770::
    (List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)

def skywalkPoolA (w : Nat → Wire) (i : Nat) : List Wire := wireBlock w i 258
def skywalkPoolB (w : Nat → Wire) : List Wire := wireBlock w 770 258

private theorem block_one (w : Nat → Wire) (s : Nat) : wireBlock w s 1=[w s] := by
  simp [wireBlock,List.range']

theorem skywalkPool_ah (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).ah=wireBlock w (i+1) 257 := by
  change wireBlock w (i+1) 256++[w (i+257)]=_
  have he := wireBlock_append w (i+1) 256 1
  simp only [block_one,Nat.add_assoc,Nat.reduceAdd] at he
  exact he

theorem skywalkPool_bh (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).bh=wireBlock w 771 257 := by
  change wireBlock w 771 256++[w 1027]=_
  have he := wireBlock_append w 771 256 1
  simp only [block_one,Nat.reduceAdd] at he
  exact he

theorem skywalkPool_a (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).a=skywalkPoolA w i := by
  change w i::(skywalkPoolTick w i).ah=wireBlock w i 258
  rw [skywalkPool_ah]
  have he := wireBlock_append w i 1 257
  simp only [block_one,Nat.reduceAdd] at he
  exact he

theorem skywalkPool_b (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).b=skywalkPoolB w := by
  change w 770::(skywalkPoolTick w i).bh=wireBlock w 770 258
  rw [skywalkPool_bh]
  have he := wireBlock_append w 770 1 257
  simp only [block_one,Nat.reduceAdd] at he
  exact he

theorem skywalkPool_half (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).half=skywalkPoolA w (i+1) := by
  change (skywalkPoolTick w i).ah++[w (i+258)]=wireBlock w (i+1) 258
  rw [skywalkPool_ah]
  have he := wireBlock_append w (i+1) 257 1
  simp only [block_one,Nat.add_assoc,Nat.reduceAdd] at he
  exact he

/-- Every successor uses precisely the previous relabelled half-word. -/
theorem skywalkPool_chain (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).half=(skywalkPoolTick w (i+1)).a ∧
    (skywalkPoolTick w i).b=(skywalkPoolTick w (i+1)).b ∧
    (skywalkPoolTick w (i+1)).previous=(skywalkPoolTick w i).a0 := by
  refine ⟨by rw [skywalkPool_half,skywalkPool_a],by rw [skywalkPool_b,skywalkPool_b],?_⟩
  change w (skywalkPoolPreviousId (i+1))=w i
  simp only [skywalkPoolPreviousId,if_neg (show i+1≠0 by omega),Nat.add_sub_cancel]

theorem skywalkPool_wires_map (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).wires=(skywalkPoolTickIds i).map w := by
  change w (skywalkPoolPreviousId i)::w (1028+i)::w (i+258)::w i::w 770::
    ((skywalkPoolTick w i).ah++(skywalkPoolTick w i).bh++wireBlock w 1540 257)=_
  rw [skywalkPool_ah,skywalkPool_bh]
  simp only [skywalkPoolTickIds,List.map_cons,List.map_append,wireBlock]

private theorem pool_tickIds_nodup (i : Nat) (hi : i<512) : (skywalkPoolTickIds i).Nodup := by
  have hab : (List.range' (i+1) 257++List.range' 771 257).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_range'_1] at hj hk
    omega
  have hbase : (List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨hab,List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_append,List.mem_range'_1] at hj hk
    omega
  have h770 : (770::(List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hbase⟩
    intro hm
    simp only [List.mem_append,List.mem_range'_1] at hm
    omega
  have ha0 : (i::770::(List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,h770⟩
    intro hm
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega
  have hext : ((i+258)::i::770::(List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,ha0⟩
    intro hm
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega
  have hhist : ((1028+i)::(i+258)::i::770::
      (List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hext⟩
    intro hm
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega
  apply List.nodup_cons.mpr
  refine ⟨?_,hhist⟩
  intro hm
  by_cases hz : i=0
  · subst i
    rw [show skywalkPoolPreviousId 0=1797 from rfl] at hm
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega
  · simp only [skywalkPoolPreviousId,if_neg hz,List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega

theorem skywalkPool_id_bound (i j : Nat) (hi : i<512) (hj : j∈skywalkPoolTickIds i) : j<1798 := by
  by_cases hz : i=0
  · subst i
    simp only [skywalkPoolTickIds,show skywalkPoolPreviousId 0=1797 from rfl,
      List.mem_cons,List.mem_append,List.mem_range'_1] at hj
    omega
  · simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
      List.mem_append,List.mem_range'_1] at hj
    omega

/-- Pool Nodup supplies precisely the needed local injectivity; the caller's
wire map need not be globally injective outside these 1798 indices. -/
theorem skywalkPool_index_inj (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<1798) (hj : j<1798) (he : w i=w j) : i=j := by
  change ((List.range' 0 1798).map w).Nodup at hn
  exact List.inj_on_of_nodup_map hn
    (by simp only [List.mem_range'_1]; omega)
    (by simp only [List.mem_range'_1]; omega) he

theorem skywalkPool_valid (w : Nat → Wire) (i : Nat) (hi : i<512)
    (hn : (skywalkPoolWires w).Nodup) : (skywalkPoolTick w i).Valid := by
  constructor
  · simp [skywalkPoolTick,wireBlock_length]
  · rw [skywalkPool_ah]
    simp [skywalkPoolTick,wireBlock_length]
  · rw [skywalkPool_wires_map]
    apply List.Nodup.map_on
    · intro j hj k hk he
      exact skywalkPool_index_inj w hn j k (skywalkPool_id_bound i j hi hj)
        (skywalkPool_id_bound i k hi hk) he
    · exact pool_tickIds_nodup i hi

theorem skywalkPool_layout_support (w : Nat → Wire) (i : Nat) (hi : i<512) :
    (skywalkPoolTick w i).wires.toFinset⊆(skywalkPoolWires w).toFinset := by
  rw [skywalkPool_wires_map]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨j,?_,rfl⟩
  simp only [List.mem_range'_1]
  have hb := skywalkPool_id_bound i j hi hj
  omega

/-- Instantiating the native tick's proved support theorem closes support for
any actual program with this concrete tick interface. -/
theorem skywalkPool_program_support (w : Nat → Wire) (i : Nat) (hi : i<512)
    (p : Program) (hp : wires p⊆(skywalkPoolTick w i).wires.toFinset) :
    wires p⊆(skywalkPoolWires w).toFinset := hp.trans (skywalkPool_layout_support w i hi)

private theorem pool_fresh_index (i j : Nat) (hi : i<512) (hj : j < i) :
    i+258∉skywalkPoolTickIds j ∧ 1028+i∉skywalkPoolTickIds j := by
  by_cases hz : j=0
  · subst j
    simp only [skywalkPoolTickIds,show skywalkPoolPreviousId 0=1797 from rfl,
      List.mem_cons,List.mem_append,List.mem_range'_1]
    omega
  · simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
      List.mem_append,List.mem_range'_1]
    omega

private theorem pool_not_mem_map (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a : Nat) (ha : a<1798) (ls : List Nat) (hl : ∀ j∈ls,j<1798) (he : a∉ls) : w a∉ls.map w := by
  intro hm
  obtain ⟨j,hj,hwa⟩ := List.mem_map.mp hm
  have hij : j=a := skywalkPool_index_inj w hn j a (hl j hj) ha hwa
  subst j
  exact he hj

/-- Fresh extension/history wires cannot have been touched by any previous tick.
This includes all past orientation and sign records as well as reused carries. -/
theorem skywalkPool_fresh_previous (w : Nat → Wire) (i j : Nat) (hi : i<512) (hj : j < i)
    (hn : (skywalkPoolWires w).Nodup) :
    (skywalkPoolTick w i).ext∉(skywalkPoolTick w j).wires ∧
      (skywalkPoolTick w i).history∉(skywalkPoolTick w j).wires := by
  simp only [skywalkPool_wires_map]
  have hji : j<512 := by omega
  have hf := pool_fresh_index i j hi hj
  exact ⟨pool_not_mem_map w hn (i+258) (by omega) _
      (skywalkPool_id_bound j · hji) hf.1,
    pool_not_mem_map w hn (1028+i) (by omega) _
      (skywalkPool_id_bound j · hji) hf.2⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkSign.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Clifford-only sign workspace update, used both to seed the signed
arithmetic control and to turn it into the reversible sign-flip history. -/
def skywalkSignToggle (a b t : Wire) : Program := [.X t,.CX a t,.CX b t]

theorem skywalkSignToggle_correct (a b t : Wire) (ha : a≠t) (hb : b≠t)
    (s : State) (m : List Bool) :
    run (skywalkSignToggle a b t) m s=
      ⟨s.phase,writeBit s.basis t ((!s.basis t) ^^ s.basis a ^^ s.basis b)⟩ := by
  simp only [skywalkSignToggle,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=t
  · subst w
    simp only [writeBit,Function.update_self,Function.update_of_ne ha,
      Function.update_of_ne hb]
  · simp [writeBit,Function.update,hw]

theorem skywalkSignToggle_counts (a b t : Wire) :
    toffoliCount (skywalkSignToggle a b t)=0 ∧
    measurementCount (skywalkSignToggle a b t)=0 := by
  simp [skywalkSignToggle,toffoliCount,measurementCount]

theorem skywalkSignToggle_wires (a b t : Wire) :
    wires (skywalkSignToggle a b t)=[a,b,t].toFinset := by
  ext q
  simp [skywalkSignToggle,wires,Instr.wires]
  tauto

/-- Equality/zero signs require no exceptional correction: these identities
hold for every Boolean combination of source, old target and new target signs. -/
theorem skywalkSignToggle_seed (H O : Bool) :
    ((!false) ^^ H ^^ O)=(!(H ^^ O)) := by cases H <;> cases O <;> rfl

theorem skywalkSignToggle_finish (H O N : Bool) :
    ((!(!(H ^^ O))) ^^ H ^^ N)=(O ^^ N) := by
  cases H <;> cases O <;> cases N <;> rfl

theorem skywalkSignToggle_recover (H O N : Bool) :
    ((!(O ^^ N)) ^^ H ^^ N)=(!(H ^^ O)) := by
  cases H <;> cases O <;> cases N <;> rfl

theorem skywalkSignToggle_clear (H O : Bool) :
    ((!(!(H ^^ O))) ^^ H ^^ O)=false := by cases H <;> cases O <;> rfl

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedRecordProgram.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Source, target and sign-history interface. The history flag is the temporary
arithmetic control between seed/finish; all carries are restored. -/
def SignedRecordValues (q : Wire) (x y carry : List Wire) (A B : Int) (T : Bool)
    (s : BasisState) : Prop :=
  s q=T ∧ signedRegValue x s=A ∧ signedRegValue y s=B ∧ regValue carry s=0

def signedRecordControl (A B : Int) : Bool := !(SkywalkRails.neg A ^^ SkywalkRails.neg B)
def signedRecordValue (A B : Int) : Int := signedIntegerValue (signedRecordControl A B) A B

/-- Executable record: seed same-sign control, update the target, then retain
only its actual old/new sign flip. No orientation bit is used or modified. -/
def signedRecord (sx sy q : Wire) (x y carry : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAdd q x y carry ++ skywalkSignToggle sx sy q

/-- Executable forward cleanup: recover the old arithmetic control from history,
undo the signed target update, and clear the history flag. -/
def signedUnrecord (sx sy q : Wire) (x y carry : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedSub q x y carry ++ skywalkSignToggle sx sy q

private theorem signToggle_record_spec (xlo ylo : List Wire) (sx sy q : Wire)
    (carry : List Wire) (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (A B : Int) (T : Bool) :
    Triple (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A B T)
      (skywalkSignToggle sx sy q)
      (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A B
        ((!T) ^^ SkywalkRails.neg A ^^ SkywalkRails.neg B)) := by
  intro s m hin
  have hq := (List.nodup_cons.mp hn).1
  have hqx : q∉xlo++[sx] := fun hm => hq
    (List.mem_append_left carry (List.mem_append_left (ylo++[sy]) hm))
  have hqy : q∉ylo++[sy] := fun hm => hq
    (List.mem_append_left carry (List.mem_append_right (xlo++[sx]) hm))
  have hqc : q∉carry := fun hm => hq
    (List.mem_append_right ((xlo++[sx])++(ylo++[sy])) hm)
  have hsx : sx≠q := by
    intro h
    exact hqx (by simp [← h])
  have hsy : sy≠q := by
    intro h
    exact hqy (by simp [← h])
  have hA : s.basis sx=SkywalkRails.neg A := by
    have hh := signedRegValue_sign xlo sx s.basis
    rw [hin.2.1] at hh
    exact hh
  have hB : s.basis sy=SkywalkRails.neg B := by
    have hh := signedRegValue_sign ylo sy s.basis
    rw [hin.2.2.1] at hh
    exact hh
  rw [skywalkSignToggle_correct sx sy q hsx hsy s m]
  have keep (r : List Wire) (hr : q∉r) :
      regValue r (writeBit s.basis q ((!s.basis q) ^^ s.basis sx ^^ s.basis sy))=
        regValue r s.basis := by
    apply regValue_congr
    intro a ha
    have he : a≠q := fun h => hr (h ▸ ha)
    simp [writeBit,he]
  have keepSigned (r : List Wire) (hr : q∉r) :
      signedRegValue r (writeBit s.basis q ((!s.basis q) ^^ s.basis sx ^^ s.basis sy))=
        signedRegValue r s.basis := by
    unfold signedRegValue
    rw [keep r hr]
  refine ⟨rfl,?_,(keepSigned _ hqx).trans hin.2.1,
    (keepSigned _ hqy).trans hin.2.2.1,(keep _ hqc).trans hin.2.2.2⟩
  simp [writeBit,hin.1,hA,hB]

/-- Same-sign subtraction and opposite-sign addition cancel magnitudes and
cannot overflow when both input signed representatives fit the word. -/
private theorem signedRecord_range (H : Int) (A B : Int)
    (ha0 : -H≤A) (ha1 : A<H) (hb0 : -H≤B) (hb1 : B<H) :
    -H≤signedRecordValue A B ∧ signedRecordValue A B<H := by
  by_cases ha : A<0
  · by_cases hb : B<0
    · simp [signedRecordValue,signedRecordControl,SkywalkRails.neg,
        signedIntegerValue,ha,hb]
      omega
    · simp [signedRecordValue,signedRecordControl,SkywalkRails.neg,
        signedIntegerValue,ha,hb]
      omega
  · by_cases hb : B<0
    · simp [signedRecordValue,signedRecordControl,SkywalkRails.neg,
        signedIntegerValue,ha,hb]
      omega
    · simp [signedRecordValue,signedRecordControl,SkywalkRails.neg,
        signedIntegerValue,ha,hb]
      omega

private theorem signedIntegerValue_undo (Q : Bool) (A B : Int) :
    signedIntegerValue (!Q) A (signedIntegerValue Q A B)=B := by
  cases Q <;> simp [signedIntegerValue]

/-- Native forward record works for every physically representable input pair.
No additional range assumption or sampled history support is required. -/
theorem signedRecord_spec (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (A B : Int) :
    Triple (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A B false)
      (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry)
      (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A (signedRecordValue A B)
        (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B))) := by
  intro s m hin
  let x := xlo++[sx]
  let y := ylo++[sy]
  let Q := signedRecordControl A B
  let R := signedRecordValue A B
  have hw : 0<y.length := by simp [y]
  have hA := signedDecode_range x.length (regValue x s.basis)
    (by simp [x]) (regValue_lt x s.basis)
  change -((2^(x.length-1):Nat):Int)≤signedRegValue x s.basis ∧
    signedRegValue x s.basis<((2^(x.length-1):Nat):Int) at hA
  rw [hin.2.1,hx] at hA
  have hB := signedDecode_range y.length (regValue y s.basis) hw (regValue_lt y s.basis)
  change -((2^(y.length-1):Nat):Int)≤signedRegValue y s.basis ∧
    signedRegValue y s.basis<((2^(y.length-1):Nat):Int) at hB
  rw [hin.2.2.1] at hB
  have hR := signedRecord_range ((2^(y.length-1):Nat):Int) A B
    hA.1 hA.2 hB.1 hB.2
  have h1 := signToggle_record_spec xlo ylo sx sy q carry hn A B false
  rw [skywalkSignToggle_seed] at h1
  have h2 := signedAdd_int_spec q x y carry hn hx hc Q A B hR.1 hR.2
  have h3 := signToggle_record_spec xlo ylo sx sy q carry hn A R Q
  dsimp only [Q,signedRecordControl] at h3
  rw [skywalkSignToggle_finish] at h3
  have hall := (h1.seq h2).seq h3
  simpa only [signedRecord,List.append_assoc] using hall s m hin

/-- Inverse expects a valid recorded image and the original target's signed
range. The latter is automatic for every forward physical input word. -/
theorem signedUnrecord_spec (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (A B : Int)
    (hb0 : -((2^((ylo++[sy]).length-1):Nat):Int)≤B)
    (hb1 : B<((2^((ylo++[sy]).length-1):Nat):Int)) :
    Triple (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A (signedRecordValue A B)
        (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B)))
      (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry)
      (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A B false) := by
  let x := xlo++[sx]
  let y := ylo++[sy]
  let Q := signedRecordControl A B
  let R := signedRecordValue A B
  have h1 := signToggle_record_spec xlo ylo sx sy q carry hn A R
    (SkywalkRails.neg B ^^ SkywalkRails.neg R)
  rw [skywalkSignToggle_recover] at h1
  have hundo : signedIntegerValue (!Q) A R=B := signedIntegerValue_undo Q A B
  have h2 := signedSub_int_spec q x y carry hn hx hc Q A R
    (by rw [hundo]; exact hb0) (by rw [hundo]; exact hb1)
  rw [hundo] at h2
  have h3 := signToggle_record_spec xlo ylo sx sy q carry hn A B Q
  dsimp only [Q,signedRecordControl] at h3
  rw [skywalkSignToggle_clear] at h3
  simpa only [signedUnrecord,List.append_assoc] using (h1.seq h2).seq h3

/-- The retained history is literally the XOR of old and new physical target MSBs. -/
theorem signedRecord_history (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (s : State) (m : List Bool)
    (hq : s.basis q=false) (hcarry : regValue carry s.basis=0) :
    (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis q=
      (s.basis sy ^^ (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis sy) := by
  let A := signedRegValue (xlo++[sx]) s.basis
  let B := signedRegValue (ylo++[sy]) s.basis
  obtain ⟨_,ho⟩ := signedRecord_spec xlo ylo sx sy q carry hn hx hc A B s m
    ⟨hq,rfl,rfl,hcarry⟩
  have hi := signedRegValue_sign ylo sy s.basis
  have hout := signedRegValue_sign ylo sy
    (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis
  rw [ho.2.2.1] at hout
  rw [ho.1,hi,hout]

/-- Signed representatives are injective on the physical word encodings.
Thus preserving a signed source value preserves every source bit. -/
theorem signedRegValue_eq_iff (r : List Wire) (s t : BasisState) :
    signedRegValue r s=signedRegValue r t ↔ ∀ a∈r,s a=t a := by
  constructor
  · intro h
    let w := r.length
    let X := regValue r s
    let Y := regValue r t
    let M : Int := (2^w:Nat)
    change signedDecode w X=signedDecode w Y at h
    have hm : (X:Int)%M=(Y:Int)%M := by
      calc
        (X:Int)%M = signedDecode w X%M := (signedDecode_emod w X).symm
        _ = signedDecode w Y%M := congrArg (fun a : Int => a%M) h
        _ = (Y:Int)%M := signedDecode_emod w Y
    have hx : (X:Int)<M := Int.ofNat_lt.mpr (regValue_lt r s)
    have hy : (Y:Int)<M := Int.ofNat_lt.mpr (regValue_lt r t)
    rw [Int.emod_eq_of_lt (by omega) hx,Int.emod_eq_of_lt (by omega) hy] at hm
    have he : X=Y := by omega
    exact (regValue_eq_iff r s t).mp he
  · intro h
    unfold signedRegValue
    rw [(regValue_eq_iff r s t).mpr h]

theorem signedRecord_source_restored (xlo ylo : List Wire) (sx sy q : Wire)
    (carry : List Wire) (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (s : State) (m : List Bool)
    (hq : s.basis q=false) (hcarry : regValue carry s.basis=0) :
    ∀ a∈xlo++[sx],
      (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis a=s.basis a := by
  obtain ⟨_,ho⟩ := signedRecord_spec xlo ylo sx sy q carry hn hx hc
    (signedRegValue (xlo++[sx]) s.basis) (signedRegValue (ylo++[sy]) s.basis)
    s m ⟨hq,rfl,rfl,hcarry⟩
  exact (signedRegValue_eq_iff _ _ _).mp ho.2.1

private theorem signedDecode_bit (n V : Nat) (b : Bool) (hn : 0<n) :
    signedDecode (n+1) (b.toNat+2*V)=2*signedDecode n V+(b.toNat:Nat) := by
  have hp : 2^n=2*2^(n-1) := by
    calc
      2^n = 2^((n-1)+1) := by congr 1; omega
      _ = 2^(n-1)*2 := pow_succ _ _
      _ = 2*2^(n-1) := Nat.mul_comm _ _
  have hb : b.toNat≤1 := by cases b <;> decide
  have hm : ((2^(n+1):Nat):Int)=2*((2^n:Nat):Int) := by
    have hh := congrArg (fun k : Nat => (k:Int)) (pow_succ (2:Nat) n)
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hh
    omega
  by_cases hv : V<2^(n-1)
  · have hf : b.toNat+2*V<2^n := by omega
    unfold signedDecode
    simp only [Nat.add_sub_cancel,if_pos hf,if_pos hv,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  · have hf : ¬b.toNat+2*V<2^n := by omega
    unfold signedDecode
    simp only [Nat.add_sub_cancel,if_neg hf,if_neg hv,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat]
    omega

/-- Exact low-bit/high-word signed decomposition used by high-only Skywalk routing. -/
theorem signedRegValue_cons (low : Wire) (tail : List Wire) (s : BasisState)
    (ht : tail≠[]) :
    signedRegValue (low::tail) s=2*signedRegValue tail s+((s low).toNat:Nat) := by
  have hn : 0<tail.length := by cases tail <;> simp_all
  have hr : regValue (low::tail) s=(s low).toNat+2*regValue tail s := by
    cases hs : s low <;> simp [regValue,Bool.toNat,hs]
  unfold signedRegValue
  rw [List.length_cons,hr]
  exact signedDecode_bit tail.length (regValue tail s) (s low) hn

/-- The integer operation is exactly the post-half signed Skywalk rail update. -/
theorem signedRecordValue_rails (A B : Int) :
    signedRecordValue A B=(if SkywalkRails.sameSign A B then B-A else B+A) := by
  have he : signedRecordControl A B=SkywalkRails.sameSign A B := by
    unfold signedRecordControl SkywalkRails.sameSign
    cases SkywalkRails.neg A <;> cases SkywalkRails.neg B <;> rfl
  rw [signedRecordValue,he]
  rfl

theorem signedRecord_counts (sx sy q : Wire) (x y carry : List Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    toffoliCount (signedRecord sx sy q x y carry)=y.length-1 ∧
      measurementCount (signedRecord sx sy q x y carry)=y.length-1 ∧
      toffoliCount (signedUnrecord sx sy q x y carry)=y.length-1 ∧
      measurementCount (signedUnrecord sx sy q x y carry)=y.length-1 := by
  have ht := skywalkSignToggle_counts sx sy q
  have hw := signedWord_counts q x y carry hx hc
  simp [signedRecord,signedUnrecord,toffoliCount_append,measurementCount_append,
    ht.1,ht.2,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2]

/-- Sign rails are part of their words; the wrapper introduces no new support
beyond the record flag, source, target and carry workspace. -/
theorem signedRecord_wires (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) :
    wires (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry)=
      (q::((xlo++[sx])++(ylo++[sy])++carry)).toFinset ∧
    wires (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry)=
      (q::((xlo++[sx])++(ylo++[sy])++carry)).toFinset := by
  have ht := skywalkSignToggle_wires sx sy q
  have hw := signedWord_wires q (xlo++[sx]) (ylo++[sy]) carry hx hc
  constructor
  · simp only [signedRecord,wires_append,ht,hw.1]
    ext a
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false]
    tauto
  · simp only [signedUnrecord,wires_append,ht,hw.2]
    ext a
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false]
    tauto

/-- Previous orientation and any other caller wire outside the actual support
remain unchanged in both directions, for every record. -/
theorem signedRecord_frame (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (s : State) (m : List Bool)
    (a : Wire) (ha : a∉q::((xlo++[sx])++(ylo++[sy])++carry)) :
    (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis a=s.basis a ∧
      (run (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis a=s.basis a := by
  have hw := signedRecord_wires xlo ylo sx sy q carry hx hc
  constructor
  · apply run_preserves_outside
    rw [hw.1]
    simpa only [List.mem_toFinset] using ha
  · apply run_preserves_outside
    rw [hw.2]
    simpa only [List.mem_toFinset] using ha

/-- Strong gate inverse on the valid clean-history image. Measurement records
of the two directions are independent; phase and every physical bit restore. -/
theorem signedRecord_roundtrip (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (s : State) (m1 m2 : List Bool)
    (hq : s.basis q=false) (hcarry : regValue carry s.basis=0) :
    run (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m2
      (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m1 s)=s := by
  let x := xlo++[sx]
  let y := ylo++[sy]
  let A := signedRegValue x s.basis
  let B := signedRegValue y s.basis
  let t := run (signedRecord sx sy q x y carry) m1 s
  let u := run (signedUnrecord sx sy q x y carry) m2 t
  obtain ⟨hp,ht⟩ := signedRecord_spec xlo ylo sx sy q carry hn hx hc A B s m1
    ⟨hq,rfl,rfl,hcarry⟩
  have hb := signedDecode_range y.length (regValue y s.basis)
    (by simp [y]) (regValue_lt y s.basis)
  change -((2^(y.length-1):Nat):Int)≤B ∧ B<((2^(y.length-1):Nat):Int) at hb
  obtain ⟨hp',hu⟩ := signedUnrecord_spec xlo ylo sx sy q carry hn hx hc A B
    hb.1 hb.2 t m2 ht
  have hxs : ∀ a∈x,u.basis a=s.basis a := (signedRegValue_eq_iff _ _ _).mp hu.2.1
  have hys : ∀ a∈y,u.basis a=s.basis a := (signedRegValue_eq_iff _ _ _).mp hu.2.2.1
  have hcs : ∀ a∈carry,u.basis a=s.basis a :=
    (regValue_eq_iff _ _ _).mp (hu.2.2.2.trans hcarry.symm)
  change u=s
  apply congrArg₂ State.mk
  · exact hp'.trans hp
  · funext a
    by_cases haq : a=q
    · subst a
      exact hu.1.trans hq.symm
    by_cases hax : a∈x
    · exact hxs a hax
    by_cases hay : a∈y
    · exact hys a hay
    by_cases hac : a∈carry
    · exact hcs a hac
    have hout : a∉q::(x++y++carry) := by
      simp only [List.mem_cons,List.mem_append]
      tauto
    have hbefore := (signedRecord_frame xlo ylo sx sy q carry hx hc s m1 a hout).1
    have hafter := (signedRecord_frame xlo ylo sx sy q carry hx hc t m2 a hout).2
    exact hafter.trans hbefore

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/Kaliski.lean
noncomputable section

namespace ECDSAAdd

/-- Kaliski 第一阶段的自然数状态；k 只计入尚未终止的轮。 -/
structure KState where
  u : Nat
  v : Nat
  r : Nat
  s : Nat
  k : Nat

def kaliskiInit (p a : Nat) : KState := ⟨p, a, 0, 1, 0⟩

end ECDSAAdd
end

-- source: ECDSAAdd/Math/SkywalkNat.lean
noncomputable section

namespace ECDSAAdd.SkywalkNat

/-- Logical unsigned Stein state. The second rail remains odd and positive. -/
@[ext] structure State where
  u : Nat
  v : Nat
  deriving DecidableEq

def init (x p : Nat) : State := ⟨x,p⟩

/-- Min-source Stein recurrence. The order split expresses absolute difference
without any signed overflow or truncated arithmetic. -/
def step (z : State) : State :=
  if z.u=0 then z
  else if z.u%2=0 then ⟨z.u/2,z.v⟩
  else if z.v≤z.u then ⟨(z.u-z.v)/2,z.v⟩
  else ⟨(z.v-z.u)/2,z.u⟩

theorem step_v_odd_pos (z : State) (hv0 : 0<z.v) (hvodd : z.v%2=1) :
    0<(step z).v ∧ (step z).v%2=1 := by
  unfold step
  split_ifs with hz he hle <;> (try dsimp) <;> omega

private theorem gcd_half_of_odd (a b : Nat) (ha : a%2=0) (hb : b%2=1) :
    (a/2).gcd b=a.gcd b := by
  have hh : 2*(a/2)=a := by omega
  have htwo : (2:Nat).Coprime b :=
    Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hb)
  have h := Nat.Coprime.gcd_mul_left_cancel (a/2) htwo
  rw [hh] at h
  exact h.symm

/-- General gcd preservation, without assuming the gcd is one. -/
theorem step_gcd (z : State) (hvodd : z.v%2=1) :
    (step z).u.gcd (step z).v=z.u.gcd z.v := by
  unfold step
  split_ifs with hz he hle
  · rfl
  · exact gcd_half_of_odd z.u z.v he hvodd
  · have hdiff : (z.u-z.v)%2=0 := by omega
    change ((z.u-z.v)/2).gcd z.v=z.u.gcd z.v
    rw [gcd_half_of_odd _ _ hdiff hvodd,Nat.gcd_sub_self_left hle]
  · have huodd : z.u%2=1 := by omega
    have hdiff : (z.v-z.u)%2=0 := by omega
    change ((z.v-z.u)/2).gcd z.u=z.u.gcd z.v
    rw [gcd_half_of_odd _ _ hdiff huodd,
      Nat.gcd_sub_self_left (show z.u≤z.v by omega),Nat.gcd_comm z.v z.u]

theorem step_coprime (z : State) (hvodd : z.v%2=1) (hc : z.u.Coprime z.v) :
    (step z).u.Coprime (step z).v := by
  change (step z).u.gcd (step z).v=1
  rw [step_gcd z hvodd]
  exact hc

/-- The nonnegative product contracts even across the identity terminal suffix. -/
theorem step_product_halves (z : State) :
    2*((step z).u*(step z).v)≤z.u*z.v := by
  unfold step
  split_ifs with hz he hle
  · simp [hz]
  · dsimp
    have hh : 2*(z.u/2)≤z.u := by omega
    nlinarith
  · dsimp
    have hh : 2*((z.u-z.v)/2)≤z.u := by omega
    nlinarith
  · dsimp
    have hh : 2*((z.v-z.u)/2)≤z.v := by omega
    nlinarith

theorem iter_product_bound (i : Nat) (z : State) :
    2^i*((step^[i] z).u*(step^[i] z).v)≤z.u*z.v := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply',pow_succ]
    have hh := Nat.mul_le_mul_left (2^i) (step_product_halves (step^[i] z))
    nlinarith

/-- Validity and gcd propagate through any number of rounds. -/
theorem iter_valid (i : Nat) (z : State) (hv0 : 0<z.v) (hvodd : z.v%2=1) :
    0<(step^[i] z).v ∧ (step^[i] z).v%2=1 ∧
      (step^[i] z).u.gcd (step^[i] z).v=z.u.gcd z.v := by
  induction i with
  | zero => exact ⟨hv0,hvodd,rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_v_odd_pos (step^[i] z) ih.1 ih.2.1
    exact ⟨hh.1,hh.2,(step_gcd _ ih.2.1).trans ih.2.2⟩

/-- Universal conservative termination: no sampled 393-round envelope. -/
theorem terminates_2n (p x n : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<2^n) (hc : x.Coprime p) :
    (step^[2*n] (init x p)).u=0 ∧ (step^[2*n] (init x p)).v=1 := by
  let z := step^[2*n] (init x p)
  have hi := iter_valid (2*n) (init x p) hp0 hpodd
  have hb := iter_product_bound (2*n) (init x p)
  change 2^(2*n)*(z.u*z.v)≤x*p at hb
  have hxp : x*p<2^(2*n) := by
    rw [two_mul,pow_add]
    calc
      x*p < x*2^n := Nat.mul_lt_mul_of_pos_left hp hx0
      _ < 2^n*2^n := Nat.mul_lt_mul_of_pos_right hx (by positivity)
  have hu : z.u=0 := by
    by_contra h
    have hprod : 1≤z.u*z.v := Nat.mul_pos (Nat.pos_of_ne_zero h) hi.1
    have hm := Nat.mul_le_mul_left (2^(2*n)) hprod
    omega
  have hg : z.u.gcd z.v=1 := hi.2.2.trans hc
  rw [hu,Nat.gcd_zero_left] at hg
  exact ⟨hu,hg⟩

theorem step_sum_nonincrease (z : State) : (step z).u+(step z).v≤z.u+z.v := by
  unfold step
  split_ifs <;> (try dsimp) <;> omega

theorem iter_sum_nonincrease (i : Nat) (z : State) :
    (step^[i] z).u+(step^[i] z).v≤z.u+z.v := by
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (step_sum_nonincrease _).trans ih

end ECDSAAdd.SkywalkNat
end

-- source: ECDSAAdd/Arithmetic/SkywalkSeed.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

structure SkywalkSeedLayout where
  a : List Wire
  b : List Wire
  constant : List Wire
  carry : List Wire
  cin : Wire
  orientation : Wire

namespace SkywalkSeedLayout

def wires (L : SkywalkSeedLayout) : List Wire :=
  L.cin::L.orientation::(L.a++L.b++L.constant++L.carry)

def usedWires (L : SkywalkSeedLayout) : List Wire := L.cin::(L.a++L.b++L.constant++L.carry)

structure Widths (L : SkywalkSeedLayout) (w : Nat) : Prop where
  a : L.a.length=w
  b : L.b.length=w
  constant : L.constant.length=w
  carry : L.carry.length+1=w

theorem core_nodup (L : SkywalkSeedLayout) (hn : L.wires.Nodup) :
    (L.cin::(L.constant++L.a++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hn q
  simp only [wires,List.count_cons,List.count_append] at hh ⊢
  omega

private theorem constant_nodup (L : SkywalkSeedLayout) (hn : L.wires.Nodup) :
    L.constant.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hn q
  simp only [wires,List.count_cons,List.count_append] at hh
  omega

private theorem copy_nodup (L : SkywalkSeedLayout) (hn : L.wires.Nodup) :
    (L.b++L.a).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hn q
  simp only [wires,List.count_cons,List.count_append] at hh ⊢
  omega

private theorem outside_constant (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈[L.cin,L.orientation]++L.a++L.b++L.carry) : q∉L.constant := by
  intro hc
  have hh := List.nodup_iff_count.mp hn q
  have ho := List.count_pos_iff.mpr hq
  have hd := List.count_pos_iff.mpr hc
  simp only [wires,List.count_cons,List.count_append,List.count_nil] at hh ho
  omega

private theorem outside_a (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈[L.cin,L.orientation]++L.b++L.constant++L.carry) : q∉L.a := by
  intro ha
  have hh := List.nodup_iff_count.mp hn q
  have ho := List.count_pos_iff.mpr hq
  have hd := List.count_pos_iff.mpr ha
  simp only [wires,List.count_cons,List.count_append,List.count_nil] at hh ho
  omega

end SkywalkSeedLayout

structure SkywalkSeedValues (L : SkywalkSeedLayout) (A B C : Nat) (s : BasisState) : Prop where
  a : regValue L.a s=A
  b : regValue L.b s=B
  constant : regValue L.constant s=C
  carry : regValue L.carry s=0
  cin : s L.cin=false
  orientation : s L.orientation=false

def skywalkSeed (L : SkywalkSeedLayout) (p : Nat) : Program :=
  copyRegister none L.b L.a ++ xorConstant L.constant p ++
    addInPlace L.constant L.a L.carry L.cin ++ xorConstant L.constant p

def skywalkUnseed (L : SkywalkSeedLayout) (p : Nat) : Program :=
  xorConstant L.constant p ++ subInPlace L.constant L.a L.carry L.cin ++
    xorConstant L.constant p ++ copyRegister none L.b L.a

private theorem seed_constant_stage (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (p A B C : Nat) (hp : p<2^L.constant.length) :
    Triple (SkywalkSeedValues L A B C) (xorConstant L.constant p)
      (SkywalkSeedValues L A B (C ^^^ p)) := by
  intro s m hin
  obtain ⟨hphase,he,hv⟩ := xorConstant_correct L.constant (L.constant_nodup hn) p hp s m
  have keep (r : List Wire) (hr : r⊆[L.cin,L.orientation]++L.a++L.b++L.carry) :
      regValue r (run (xorConstant L.constant p) m s).basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact he q (L.outside_constant hn q (hr hq))
  refine ⟨hphase,(keep _ (by intro q hq; simp [hq])).trans hin.a,
    (keep _ (by intro q hq; simp [hq])).trans hin.b,?_,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (he _ (L.outside_constant hn _ (by simp))).trans hin.cin,
    (he _ (L.outside_constant hn _ (by simp))).trans hin.orientation⟩
  simpa only [hin.constant] using hv

private theorem seed_copy_stage (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (hw : L.b.length=L.a.length) (A B C : Nat) :
    Triple (SkywalkSeedValues L A B C) (copyRegister none L.b L.a)
      (SkywalkSeedValues L (A ^^^ B) B C) := by
  intro s m hin
  obtain ⟨hphase,he,hv⟩ := copyRegister_correct none L.b L.a hw (L.copy_nodup hn)
    (by simp) s m
  have keep (r : List Wire) (hr : r⊆[L.cin,L.orientation]++L.b++L.constant++L.carry) :
      regValue r (run (copyRegister none L.b L.a) m s).basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact he q (L.outside_a hn q (hr hq))
  refine ⟨hphase,?_,(keep _ (by intro q hq; simp [hq])).trans hin.b,
    (keep _ (by intro q hq; simp [hq])).trans hin.constant,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (he _ (L.outside_a hn _ (by simp))).trans hin.cin,
    (he _ (L.outside_a hn _ (by simp))).trans hin.orientation⟩
  simpa only [hin.a,hin.b,copyValue] using hv

private theorem seed_add_stage (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (hx : L.constant.length=L.a.length) (hc : L.carry.length+1=L.a.length)
    (A B C : Nat) :
    Triple (SkywalkSeedValues L A B C) (addInPlace L.constant L.a L.carry L.cin)
      (SkywalkSeedValues L ((C+A)%2^L.a.length) B C) := by
  intro s m hin
  obtain ⟨hp,he,hv⟩ := addInPlace_correct L.constant L.a L.carry L.cin
    (L.core_nodup hn) hx hc s m ((regValue_zero _ _).mp hin.carry)
  have keep (r : List Wire) (hr : r⊆[L.cin,L.orientation]++L.b++L.constant++L.carry) :
      regValue r (run (addInPlace L.constant L.a L.carry L.cin) m s).basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact he q (L.outside_a hn q (hr hq))
  refine ⟨hp,?_,(keep _ (by intro q hq; simp [hq])).trans hin.b,
    (keep _ (by intro q hq; simp [hq])).trans hin.constant,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (he _ (L.outside_a hn _ (by simp))).trans hin.cin,
    (he _ (L.outside_a hn _ (by simp))).trans hin.orientation⟩
  simpa only [hin.constant,hin.a,hin.cin,Bool.toNat_false,Nat.add_zero] using hv

private theorem seed_small_bounds (w p x : Nat) (hw : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    p<2^w ∧ x<2^w ∧ p+x<2^(w-1) ∧ p+x<2^w := by
  have hpow : 2^(w-1)=2^(w-2)*2 := by
    rw [show w-1=(w-2)+1 by omega,pow_succ]
  have hmono : 2^(w-1)≤2^w := Nat.pow_le_pow_right (by decide) (by omega)
  have hs : p+x<2^(w-1) := by rw [hpow]; omega
  exact ⟨by omega,by omega,hs,hs.trans_le hmono⟩

/-- Exact positive seed, including all work/control restoration and arbitrary records. -/
theorem skywalkSeed_spec (L : SkywalkSeedLayout) (w p x : Nat) (h : L.Widths w)
    (hn : L.wires.Nodup) (hw : 2≤w) (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    Triple (SkywalkSeedValues L 0 x 0) (skywalkSeed L p)
      (SkywalkSeedValues L (p+x) x 0) := by
  have hb := seed_small_bounds w p x hw hp hx
  have h1 := seed_copy_stage L hn (h.b.trans h.a.symm) 0 x 0
  simp only [Nat.zero_xor] at h1
  have h2 := seed_constant_stage L hn p x x 0 (by rw [h.constant]; exact hb.1)
  simp only [Nat.zero_xor] at h2
  have h3 := seed_add_stage L hn (h.constant.trans h.a.symm)
    (h.carry.trans h.a.symm) x x p
  rw [h.a,Nat.mod_eq_of_lt hb.2.2.2] at h3
  have h4 := seed_constant_stage L hn p (p+x) x p (by rw [h.constant]; exact hb.1)
  simp only [Nat.xor_self] at h4
  simpa only [skywalkSeed,List.append_assoc] using ((h1.seq h2).seq h3).seq h4

theorem skywalkSeed_wires (L : SkywalkSeedLayout) (w p : Nat) (h : L.Widths w) :
    wires (skywalkSeed L p)=L.usedWires.toFinset ∧
      wires (skywalkUnseed L p)=L.usedWires.toFinset := by
  have hpos : 0<w := by have hh := h.carry; omega
  have hne : L.b.isEmpty=false := by
    cases hb : L.b with
    | nil => have hh := h.b; rw [hb] at hh; simp at hh; omega
    | cons b bs => rfl
  have hcopy := copyRegister_wires none L.b L.a (h.b.trans h.a.symm)
  rw [hne] at hcopy
  simp only [Bool.false_eq_true,if_false,Option.toList_none,List.nil_append] at hcopy
  have ha := addInPlace_wires L.constant L.a L.carry L.cin
    (h.constant.trans h.a.symm) (h.carry.trans h.a.symm)
  have hs := subInPlace_wires L.constant L.a L.carry L.cin
    (h.constant.trans h.a.symm) (h.carry.trans h.a.symm)
  have hc := xorConstant_wires_subset L.constant p
  constructor
  · simp only [skywalkSeed,wires_append,hcopy,ha]
    ext q
    have hq : q∈wires (xorConstant L.constant p) → q∈L.constant :=
      fun hh => List.mem_toFinset.mp (hc hh)
    simp only [SkywalkSeedLayout.usedWires,Finset.mem_union,List.mem_toFinset,
      List.mem_cons,List.mem_append]
    tauto
  · simp only [skywalkUnseed,wires_append,hcopy,hs]
    ext q
    have hq : q∈wires (xorConstant L.constant p) → q∈L.constant :=
      fun hh => List.mem_toFinset.mp (hc hh)
    simp only [SkywalkSeedLayout.usedWires,Finset.mem_union,List.mem_toFinset,
      List.mem_cons,List.mem_append]
    tauto

theorem skywalkSeed_frame (L : SkywalkSeedLayout) (w p : Nat) (h : L.Widths w)
    (s : State) (m : List Bool) (q : Wire) (hq : q∉L.usedWires) :
    (run (skywalkSeed L p) m s).basis q=s.basis q ∧
      (run (skywalkUnseed L p) m s).basis q=s.basis q := by
  have hs := skywalkSeed_wires L w p h
  constructor
  · apply run_preserves_outside
    rw [hs.1]
    simpa only [List.mem_toFinset] using hq
  · apply run_preserves_outside
    rw [hs.2]
    simpa only [List.mem_toFinset] using hq

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkShared.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Integer memory plus a 258-bit seed constant, 257-bit numerator and auxiliary flag. -/
def skywalkSharedWires (w : Nat → Wire) : List Wire := wireBlock w 0 2314

def skywalkSharedSeed (w : Nat → Wire) : SkywalkSeedLayout :=
  { a:=wireBlock w 0 258,b:=wireBlock w 770 258,constant:=wireBlock w 1798 258,
    carry:=wireBlock w 1540 257,cin:=w 2313,orientation:=w 1797 }

/-- Field arithmetic borrows cleared terminal rails and restored integer/seed scratch. -/
def skywalkSharedField (w : Nat → Wire) : ModInPlaceLayout :=
  { a:=wireBlock w 770 257,low:=wireBlock w 2056 256,high:=w 2312,
    constant:=wireBlock w 1540 257,carry:=wireBlock w 1798 256,cin:=w 1797,
    mask:=wireBlock w 512 257,flag:=w 2313 }

def skywalkSharedTape (w : Nat → Wire) : List (Wire × Wire) :=
  (List.range 512).map (fun i => (w i,w (1028+i)))

def skywalkSharedUnused (w : Nat → Wire) : List Wire := [w 769,w 1027,w 2054,w 2055]

private def sharedSeedIds : List Nat :=
  2313::1797::(List.range' 0 258++List.range' 770 258++
    List.range' 1798 258++List.range' 1540 257)

private def sharedFieldIds : List Nat :=
  List.range' 770 257++List.range' 2056 257++List.range' 1540 257++
    List.range' 1798 256++[1797]++List.range' 512 257++[2313]

private theorem shared_block_one (w : Nat → Wire) (s : Nat) : wireBlock w s 1=[w s] := by
  simp [wireBlock,List.range']

private theorem shared_append_region (ls : List Nat) (hd : ls.Nodup) (s n : Nat)
    (hsep : ∀ j∈ls,j<s ∨ s+n≤j) : (ls++List.range' s n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨hd,List.nodup_range',?_⟩
  apply List.disjoint_left.mpr
  intro j hj hk
  have hh := hsep j hj
  simp only [List.mem_range'_1] at hk
  omega

private theorem shared_seedIds_nodup : sharedSeedIds.Nodup := by
  have h1 := shared_append_region (List.range' 0 258) List.nodup_range' 770 258 (by
    intro j hj; simp only [List.mem_range'_1] at hj; omega)
  have h2 := shared_append_region _ h1 1798 258 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h3 := shared_append_region _ h2 1540 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h4 : (1797::(List.range' 0 258++List.range' 770 258++
      List.range' 1798 258++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,h3⟩
    intro hm
    simp only [List.mem_append,List.mem_range'_1] at hm
    omega
  apply List.nodup_cons.mpr
  refine ⟨?_,h4⟩
  intro hm
  simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
  omega

private theorem shared_fieldIds_nodup : sharedFieldIds.Nodup := by
  have h1 := shared_append_region (List.range' 770 257) List.nodup_range' 2056 257 (by
    intro j hj; simp only [List.mem_range'_1] at hj; omega)
  have h2 := shared_append_region _ h1 1540 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h3 := shared_append_region _ h2 1798 256 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h4 := shared_append_region _ h3 1797 1 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h5 := shared_append_region _ h4 512 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h6 := shared_append_region _ h5 2313 1 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  simpa only [show List.range' 1797 1=[1797] from rfl,
    show List.range' 2313 1=[2313] from rfl] using h6

private theorem shared_seedIds_bound (j : Nat) (hj : j∈sharedSeedIds) : j<2314 := by
  simp only [sharedSeedIds,List.mem_cons,List.mem_append,List.mem_range'_1] at hj
  omega

private theorem shared_fieldIds_bound (j : Nat) (hj : j∈sharedFieldIds) : j<2314 := by
  simp only [sharedFieldIds,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at hj
  omega

theorem skywalkShared_index_inj (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i j : Nat) (hi : i<2314) (hj : j<2314) (he : w i=w j) : i=j := by
  change ((List.range' 0 2314).map w).Nodup at hn
  exact List.inj_on_of_nodup_map hn
    (by simp only [List.mem_range'_1]; omega)
    (by simp only [List.mem_range'_1]; omega) he

private theorem shared_map_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (ls : List Nat) (hd : ls.Nodup) (hb : ∀ j∈ls,j<2314) : (ls.map w).Nodup := by
  apply List.Nodup.map_on
  · intro j hj k hk he
    exact skywalkShared_index_inj w hn j k (hb j hj) (hb k hk) he
  · exact hd

private theorem shared_not_mem_map (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i : Nat) (hi : i<2314) (ls : List Nat) (hb : ∀ j∈ls,j<2314) (he : i∉ls) : w i∉ls.map w := by
  intro hm
  obtain ⟨j,hj,hji⟩ := List.mem_map.mp hm
  have hh := skywalkShared_index_inj w hn j i (hb j hj) hi hji
  subst j
  exact he hj

theorem skywalkShared_integer_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    (skywalkPoolWires w).Nodup := by
  have he := wireBlock_append w 0 1798 516
  change (wireBlock w 0 1798).Nodup
  apply (List.sublist_append_left (wireBlock w 0 1798) (wireBlock w 1798 516)).nodup
  simpa only [he,Nat.zero_add,Nat.reduceAdd,skywalkSharedWires] using hn

theorem skywalkShared_seed_widths (w : Nat → Wire) : (skywalkSharedSeed w).Widths 258 := by
  constructor <;> simp [skywalkSharedSeed,wireBlock_length]

theorem skywalkShared_seed_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    (skywalkSharedSeed w).wires.Nodup := by
  have he : (skywalkSharedSeed w).wires=sharedSeedIds.map w := by
    simp only [skywalkSharedSeed,SkywalkSeedLayout.wires,sharedSeedIds,
      wireBlock,List.map_cons,List.map_append]
  rw [he]
  exact shared_map_nodup w hn _ shared_seedIds_nodup shared_seedIds_bound

theorem skywalkShared_field_z (w : Nat → Wire) :
    (skywalkSharedField w).z=wireBlock w 2056 257 := by
  change wireBlock w 2056 256++[w 2312]=_
  have he := wireBlock_append w 2056 256 1
  simp only [shared_block_one,Nat.reduceAdd] at he
  exact he

private theorem shared_field_wires (w : Nat → Wire) :
    (skywalkSharedField w).wires=sharedFieldIds.map w := by
  unfold ModInPlaceLayout.wires
  rw [skywalkShared_field_z]
  simp only [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,
    sharedFieldIds,wireBlock,List.map_append,List.map_cons,List.map_nil]
  simp only [List.append_assoc]

theorem skywalkShared_field_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    (skywalkSharedField w).wires.Nodup := by
  rw [shared_field_wires]
  exact shared_map_nodup w hn _ shared_fieldIds_nodup shared_fieldIds_bound

theorem skywalkShared_tape_length (w : Nat → Wire) : (skywalkSharedTape w).length=512 := by
  simp [skywalkSharedTape]

/-- Every real record pair is disjoint from all field data/scratch. An existing
caller control outside the universe may serve as the proof-only active wire. -/
theorem skywalkShared_tape_layout (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (active : Wire) (ha : active∉skywalkSharedWires w) :
    ∀ r∈skywalkSharedTape w,(active::r.2::r.1::(skywalkSharedField w).wires).Nodup := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  have hib : i<512 := List.mem_range.mp hi
  have hfield := skywalkShared_field_nodup w hn
  have hgi : w i∉(skywalkSharedField w).wires := by
    rw [shared_field_wires]
    apply shared_not_mem_map w hn i (by omega) _ shared_fieldIds_bound
    simp only [sharedFieldIds,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false]
    omega
  have hsi : w (1028+i)∉(skywalkSharedField w).wires := by
    rw [shared_field_wires]
    apply shared_not_mem_map w hn (1028+i) (by omega) _ shared_fieldIds_bound
    simp only [sharedFieldIds,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false]
    omega
  have hsg : w (1028+i)≠w i := by
    intro he
    have hh := skywalkShared_index_inj w hn (1028+i) i (by omega) (by omega) he
    omega
  have hbase : (w i::(skywalkSharedField w).wires).Nodup := List.nodup_cons.mpr ⟨hgi,hfield⟩
  have hpair : (w (1028+i)::w i::(skywalkSharedField w).wires).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hbase⟩
    intro hm
    rcases List.mem_cons.mp hm with hm|hm
    · exact hsg hm
    · exact hsi hm
  apply List.nodup_cons.mpr
  refine ⟨?_,hpair⟩
  intro hm
  have hpool : ∀ j<2314,w j∈skywalkSharedWires w := by
    intro j hj
    apply List.mem_map.mpr
    refine ⟨j,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  simp only [List.mem_cons] at hm
  rcases hm with rfl|rfl|hm
  · exact ha (hpool _ (by omega))
  · exact ha (hpool _ (by omega))
  · rw [shared_field_wires] at hm
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
    exact ha (hpool _ (shared_fieldIds_bound j hj))

/-- Full integer/seed scratch after terminal clear, before any field borrowing. -/
def SkywalkSharedClean (w : Nat → Wire) (s : BasisState) : Prop :=
  regValue (wireBlock w 512 258) s=0 ∧ regValue (wireBlock w 770 258) s=0 ∧
  regValue (wireBlock w 1540 257) s=0 ∧ regValue (wireBlock w 1798 258) s=0 ∧
  s (w 1797)=false ∧ s (w 2313)=false

private theorem shared_block_prefix (w : Nat → Wire) (start n m : Nat) (h : n≤m) :
    (wireBlock w start n).Sublist (wireBlock w start m) := by
  have he := wireBlock_append w start n (m-n)
  rw [Nat.add_sub_of_le h] at he
  rw [← he]
  exact List.sublist_append_left _ _

private theorem shared_zero_sublist (a b : List Wire) (s : BasisState)
    (hab : a.Sublist b) (h : regValue b s=0) : regValue a s=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  exact (regValue_zero _ _).mp h q (hab.subset hq)

/-- Exact transfer of clean integer rails/seed constant to source and all field work.
The four omitted padding sites are retained explicitly, rather than discarded. -/
theorem skywalkShared_clean_to_field (w : Nat → Wire) (s : BasisState)
    (h : SkywalkSharedClean w s) :
    regValue (skywalkSharedField w).a s=0 ∧ regValue (skywalkSharedField w).work s=0 ∧
      regValue (skywalkSharedUnused w) s=0 := by
  have ha := shared_zero_sublist _ _ s (shared_block_prefix w 770 257 258 (by decide)) h.2.1
  have hm := shared_zero_sublist _ _ s (shared_block_prefix w 512 257 258 (by decide)) h.1
  have hc := shared_zero_sublist _ _ s (shared_block_prefix w 1798 256 258 (by decide)) h.2.2.2.1
  refine ⟨ha,?_,?_⟩
  · change regValue (wireBlock w 1540 257++wireBlock w 1798 256++[w 1797]++
      wireBlock w 512 257++[w 2313]) s=0
    rw [regValue_append,regValue_append,regValue_append,regValue_append,
      h.2.2.1,hc,hm]
    simp [regValue,h.2.2.2.2.1,h.2.2.2.2.2]
  · apply (regValue_zero _ _).mpr
    intro q hq
    have memA : w 769∈wireBlock w 512 258 := by
      apply List.mem_map.mpr; refine ⟨769,?_,rfl⟩; simp only [List.mem_range'_1]; omega
    have memB : w 1027∈wireBlock w 770 258 := by
      apply List.mem_map.mpr; refine ⟨1027,?_,rfl⟩; simp only [List.mem_range'_1]; omega
    have memC (j : Nat) (hj : j=2054 ∨ j=2055) : w j∈wireBlock w 1798 258 := by
      apply List.mem_map.mpr; refine ⟨j,?_,rfl⟩; simp only [List.mem_range'_1]; omega
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact (regValue_zero _ _).mp h.1 _ memA
    · exact (regValue_zero _ _).mp h.2.1 _ memB
    · exact (regValue_zero _ _).mp h.2.2.2.1 _ (memC 2054 (Or.inl rfl))
    · exact (regValue_zero _ _).mp h.2.2.2.1 _ (memC 2055 (Or.inr rfl))

theorem skywalkShared_unused_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (q : Wire) (hq : q∈skywalkSharedUnused w) : q∉(skywalkSharedField w).wires := by
  rw [shared_field_wires]
  have notField (i : Nat) (hi : i=769 ∨ i=1027 ∨ i=2054 ∨ i=2055) : w i∉sharedFieldIds.map w := by
    apply shared_not_mem_map w hn i (by omega) _ shared_fieldIds_bound
    simp only [sharedFieldIds,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false]
    omega
  simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  · exact notField 769 (Or.inl rfl)
  · exact notField 1027 (Or.inr (Or.inl rfl))
  · exact notField 2054 (Or.inr (Or.inr (Or.inl rfl)))
  · exact notField 2055 (Or.inr (Or.inr (Or.inr rfl)))

/-- The numerator's used high padding bit is also zero for every canonical
256-bit field result; unlike the four unused sites it is part of the target. -/
theorem skywalkShared_numerator_high_zero (w : Nat → Wire) (s : BasisState) (Z : Nat)
    (hz : regValue (skywalkSharedField w).z s=Z) (hZ : Z<2^256) : s (w 2312)=false := by
  have hp := regValue_highBit (wireBlock w 2056 256) (w 2312) s
  have hl : (wireBlock w 2056 256).length=256 := wireBlock_length _ _ _
  rw [hl] at hp
  change regValue (wireBlock w 2056 256++[w 2312]) s=Z at hz
  rw [hz] at hp
  cases hs : s (w 2312) with
  | false => rfl
  | true => have hh := hp.mp hs; omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedIds.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Full signed words, shared carry frame and threshold workspace for the
exact fused kernel. The retired integer transcript is excluded. -/
def fusedSharedIds : List Nat :=
  1797::(List.range' 770 258++(List.range' 2056 257++[769])++
    (List.range' 1540 257++[2055])++(List.range' 1798 257++[2313])++List.range' 512 256)

theorem fusedSharedIds_bound (i : Nat) (hi : i∈fusedSharedIds) : i < 2314 := by
  simp only [fusedSharedIds,List.mem_cons,List.mem_append,List.mem_range'_1,
    List.not_mem_nil,or_false] at hi
  omega

theorem fusedSharedSites_subset (w : Nat → Wire) :
    fusedSharedIds.map w ⊆ skywalkSharedWires w := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  apply List.mem_map.mpr
  exact ⟨i,by simp only [List.mem_range'_1]; exact ⟨Nat.zero_le i,fusedSharedIds_bound i hi⟩,rfl⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/TrailingZeroCompare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Exact strict comparison with a threshold divisible by eight.
All high bits are compared; low bits cannot affect this predicate. -/
def compareLtMultipleEight (x T carry : List Wire) (cin target : Wire) (K : Nat) : Program :=
  compareLtConst none (x.drop 3) (T.take (x.length-3)) (carry.take (x.length-3)) cin target (K/8)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/FusedSignedHalf.lean
noncomputable section

/-!
Exact fused signed half blueprint, derived from the incumbent's signed-sum/fold
architecture (public snapshot 1c185d) and the verified local SignedWord and
SkywalkSignedModAdd interfaces. No finite carry/compare windows are assumed.
-/
namespace ECDSAAdd.FusedSignedHalf
open Secp256k1

def bit (b : Bool) : Int := if b then 1 else 0

def signedSum (b : Bool) (X Y : Nat) : Int := (X : Int)+(if b then -(Y : Int) else (Y : Int))
def parity (s : Int) : Bool := decide (s%2=1)
def reduction (p : Nat) (s : Int) : Bool := decide (¬(0≤s ∧ s<(p : Int)))
def normalizedParity (p : Nat) (s : Int) : Bool := parity s ^^ reduction p s

def correction (p : Nat) (b : Bool) (s : Int) : Int :=
  bit (normalizedParity p s)+(if b then bit (reduction p s) else -bit (reduction p s))
def canonicalSum (p : Nat) (b : Bool) (s : Int) : Int :=
  s+(if b then bit (reduction p s)*(p : Int) else -bit (reduction p s)*(p : Int))
def evenLift (p : Nat) (b : Bool) (s : Int) : Int := s+correction p b s*(p : Int)
def result (p : Nat) (b : Bool) (X Y : Nat) : Nat := (evenLift p b (signedSum b X Y)/2).toNat

def RawDomain (p : Nat) (b : Bool) (s : Int) : Prop :=
  if b then -(p : Int)<s ∧ s<(p : Int) else 0≤s ∧ s<2*(p : Int)

theorem signedSum_domain (p X Y : Nat) (b : Bool) (hX : X<p) (hY : Y<p) :
    RawDomain p b (signedSum b X Y) := by
  cases b <;> simp only [RawDomain,signedSum,Bool.false_eq_true,if_false,if_true] <;> omega

theorem parity_value (s : Int) : s%2=bit (parity s) := by
  by_cases hs : s%2=1
  · simp [parity,bit,hs]
  · have hz : s%2=0 := by omega
    simp [parity,bit,hz]

theorem canonicalSum_bounds (p : Nat) (b : Bool) (s : Int) (hd : RawDomain p b s) :
    0≤canonicalSum p b s ∧ canonicalSum p b s<(p : Int) := by
  cases b
  · simp only [RawDomain,Bool.false_eq_true,if_false] at hd
    by_cases hs : s<(p : Int)
    · simp [canonicalSum,reduction,bit,hd.1,hs]
    · simp [canonicalSum,reduction,bit,hd.1,hs]
      omega
  · simp only [RawDomain,if_true] at hd
    by_cases hs : 0≤s
    · simp [canonicalSum,reduction,bit,hs,hd.2]
    · simp [canonicalSum,reduction,bit,hs]
      omega

theorem evenLift_eq_canonicalSum (p : Nat) (b : Bool) (s : Int) :
    evenLift p b s=canonicalSum p b s+bit (normalizedParity p s)*(p : Int) := by
  cases b <;> simp [evenLift,canonicalSum,correction] <;> ring

/-- The normalized parity is exact even at raw sum zero and modulus boundaries. -/
theorem normalizedParity_value (p : Nat) (b : Bool) (s : Int) (hp : p%2=1) :
    canonicalSum p b s%2=bit (normalizedParity p s) := by
  have hs := parity_value s
  have hpi : (p : Int)%2=1 := by omega
  cases b <;> cases ha : parity s <;> cases hh : reduction p s <;>
    simp only [canonicalSum,normalizedParity,bit,ha,hh,Bool.false_eq_true,if_false,if_true,
      Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] at hs ⊢ <;> omega

/-- The one correction produces an even positive lift below 2p, without wrap assumptions. -/
theorem evenLift_spec (p : Nat) (b : Bool) (s : Int) (hp : p%2=1) (hd : RawDomain p b s) :
    0≤evenLift p b s ∧ evenLift p b s<2*(p : Int) ∧ evenLift p b s%2=0 := by
  have hz := canonicalSum_bounds p b s hd
  have hq := normalizedParity_value p b s hp
  have hpi : (p : Int)%2=1 := by omega
  rw [evenLift_eq_canonicalSum]
  cases he : normalizedParity p s <;> simp only [bit,he,Bool.false_eq_true,if_false,if_true] at hq ⊢ <;> omega

/-- Exact natural representative and doubled-value equation. -/
theorem result_spec (p X Y : Nat) (b : Bool) (hp : p%2=1) (hX : X<p) (hY : Y<p) :
    result p b X Y<p ∧ 2*(result p b X Y : Int)=evenLift p b (signedSum b X Y) := by
  have he := evenLift_spec p b (signedSum b X Y) hp (signedSum_domain p X Y b hX hY)
  have hn : 0≤evenLift p b (signedSum b X Y)/2 := by omega
  have ht := Int.toNat_of_nonneg hn
  simp only [result]
  omega

def halfThreshold (p : Nat) : Nat := (p+1)/2

end ECDSAAdd.FusedSignedHalf
end

-- source: ECDSAAdd/Arithmetic/FusedSignedHalf.lean
noncomputable section

/-!
Actual gate capsules for the exact fused signed half. The mathematical blueprint
is attributed to the incumbent's signed-sum/fold architecture and local verified
SignedWord kernels. Complete kernel assembly is not yet asserted by this module.
-/
namespace ECDSAAdd.Arithmetic

/-- Exact output-side parity erasure. The low three bits are irrelevant because
the fixed half-threshold is divisible by eight. -/
def fusedHalfParityClear (x T carry : List Wire) (cin q : Wire) : Program :=
  compareLtMultipleEight x T carry cin q (FusedSignedHalf.halfThreshold p) ++ [.X q]

/-- Reset selector flags in dependency order, with exact immediate phase correction.
The guard need not still exist in the changed target word: j=b AND h. -/
def fusedCorrectionFlagsErase (b a h j l m : Wire) : Program :=
  eraseMask a [j] [m] ++ eraseMask a [h] [l] ++ eraseMask b [h] [j]

/-- Clifford load of the correction word. The sign/selector XORs are distributed
through the three fixed words; no nonlinear word mask is computed. -/
def fusedCorrectionWordLoad (a j l m : Wire) (C : List Wire) (P D N : Nat) : Program :=
  maskedConstant a C P ++ maskedConstant l C P ++ maskedConstant m C P ++
  maskedConstant j C D ++ maskedConstant m C D ++ maskedConstant l C N ++ maskedConstant m C N

/-- One full-width correction addition, with its source word Clifford-cleared afterwards. -/
def fusedCorrectionApply (a j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P D N : Nat) : Program :=
  fusedCorrectionWordLoad a j l m C P D N ++ addInPlace C R carry cin ++
    fusedCorrectionWordLoad a j l m C P D N

/-- Full signed raw addition and full-width normalization comparison.
The sign control doubles as the raw addition's carry input. -/
def fusedRawNormalize (b h : Wire) (Y R C addCarry compareCarry : List Wire)
    (cin : Wire) (P : Nat) : Program :=
  signedAdd b Y R addCarry ++ compareLtConst none R C compareCarry cin h P ++ [.X h]

/-- Temporary Clifford change of the threshold AND inputs. The same capsule
restores both q and the source parity bit after the AND is computed/erased. -/
def fusedThresholdToggle (b q e : Wire) : Program := [.CX b e,.X q]

/-- Exact two-AND threshold selectors: t=b AND q and d=NOT q AND(e XOR b).
Source parity and sign/parity controls are restored immediately. -/
def fusedThresholdFlagsSeed (b q e t d : Wire) : Program :=
  [.CCX b q t] ++ fusedThresholdToggle b q e ++ [.CCX q e d] ++ fusedThresholdToggle b q e

/-- The cleanup computes the same exact AND inputs, measures the flags and
applies immediate phase corrections before restoring those inputs. -/
def fusedThresholdFlagsErase (b q e t d : Wire) : Program :=
  eraseMask b [q] [t] ++ fusedThresholdToggle b q e ++
    eraseMask q [e] [d] ++ fusedThresholdToggle b q e

/-- The threshold source constant is loaded by Clifford XORs. The low-bit
selector is separate from the two even constants. -/
def fusedThresholdWordLoad (b q t d : Wire) (C : List Wire) (K P : Nat) : Program :=
  maskedConstant b C K ++ maskedConstant q C K ++ maskedConstant t C P ++ maskedConstant d C 1

/-- Apply the selected full-word correction, erase every nonlinear correction
flag with phase correction, and physically rotate the proved even lift. -/
def fusedEvenHalf (b a h j l m : Wire) (C R carry : List Wire) (cin : Wire) (P : Nat) : Program :=
  fusedCorrectionApply a j l m C R carry cin P (2*P) (2^R.length-P) ++
    fusedCorrectionFlagsErase b a h j l m ++ rotateRight R

/-- Move the two retained classical flags into cleared target guards. The early
scratch bits are cleared by physical Clifford swaps. -/
def fusedFlagsMove (a h qOut hOut : Wire) : Program :=
  [.CX h a] ++ swapBits a qOut ++ swapBits h hOut

/-- Threshold input preparation uses only Clifford copy and conditional NOT. -/
def fusedThresholdPrepare (b : Wire) (sourceHalf A : List Wire) : Program :=
  copyRegister none sourceHalf A ++ signComplement b A

/-- Restore the threshold input by a fresh forward Clifford stream. -/
def fusedThresholdUnprepare (b : Wire) (sourceHalf A : List Wire) : Program :=
  signComplement b A ++ copyRegister none sourceHalf A

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSignedHalfPacked.lean
noncomputable section

/-! Exact staged composition and storage packing for the signed field half. -/
namespace ECDSAAdd.Arithmetic

/-- Packed fused-half ports: five early flags are borrowed from A, target guards
hold two retained flags later, and constant guards hold two threshold selectors.
All arithmetic chains use prefixes of a single full carry array. -/
structure FusedHalfPorts where
  b : Wire
  cin : Wire
  low : Wire
  e : Wire
  a : Wire
  h : Wire
  j : Wire
  l : Wire
  m : Wire
  qOut : Wire
  hOut : Wire
  t : Wire
  d : Wire
  yg0 : Wire
  yg1 : Wire
  rTail : List Wire
  yTail : List Wire
  C : List Wire
  A : List Wire
  carry : List Wire

namespace FusedHalfPorts

def targetLow (L : FusedHalfPorts) : List Wire := L.low::L.rTail
def sourceHalf (L : FusedHalfPorts) : List Wire := L.yTail++[L.yg0]

end FusedHalfPorts


end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedShared.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Packed forward kernel overlay. Guards and temporaries are borrowed from
the already cleared terminal rails and restored seed/integer workspace. -/
def fusedSharedPorts (w : Nat → Wire) (g : Wire) : FusedHalfPorts :=
  { b:=g,cin:=w 1797,low:=w 2056,e:=w 770,
    a:=w 512,h:=w 513,j:=w 514,l:=w 515,m:=w 516,
    qOut:=w 2312,hOut:=w 769,t:=w 1796,d:=w 2055,
    yg0:=w 1026,yg1:=w 1027,rTail:=wireBlock w 2057 255,
    yTail:=wireBlock w 771 255,C:=wireBlock w 1540 256,
    A:=wireBlock w 512 256,carry:=wireBlock w 1798 257++[w 2313] }

attribute [local irreducible] wireBlock

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedInput.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] wireBlock

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModInPlaceNegate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModInPlaceSubtract.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModUnary.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 单目模算术借用同一目标与 scratch；mask 在半倍期间保持零。 -/
structure ModUnaryLayout where
  low : List Wire
  high : Wire
  constant : List Wire
  carry : List Wire
  cin : Wire
  mask : List Wire
  flag : Wire

namespace ModUnaryLayout

def z (U : ModUnaryLayout) : List Wire := U.low++[U.high]
/-- 合法位宽下 low 非空；回退值仅使构造对所有布局有定义。 -/
def bit (U : ModUnaryLayout) : Wire := U.low.headD U.high

end ModUnaryLayout

/-- 左旋得到 2Z，试减 p、借位低位加回，最后由结果奇偶清借位。 -/
def dblInPlace (U : ModUnaryLayout) (p : Nat) : Program :=
  rotateLeft U.z ++ xorConstant U.constant p ++ subInPlace U.constant U.z U.carry U.cin ++
  xorConstant U.constant p ++
  maskedAddConst U.high (U.constant.take U.low.length) U.low
    (U.carry.take (U.low.length-1)) U.cin p ++ [.X U.high,.CX U.bit U.high]

/-- 保存奇偶，奇数加 p 后右旋，由减半结果与 (p+1)/2 比较清奇偶位。 -/
def halfInPlace (U : ModUnaryLayout) (p : Nat) : Program :=
  [.CX U.bit U.flag] ++ maskedAddConst U.flag U.constant U.z U.carry U.cin p ++
  rotateRight U.z ++
  compareLtConst none U.low (U.constant.take U.low.length) U.carry U.cin U.flag ((p+1)/2) ++
  [.X U.flag]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModDouble.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModHalf.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ModUnaryResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Shift.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Fredkin 门分解为两次 CX 与一次 CCX；控制与两个目标必须互异。 -/
def cswap (c a b : Wire) : Program := [.CX b a, .CCX c a b, .CX b a]

theorem cswap_correct (c a b : Wire) (hnd : [c,a,b].Nodup) (s : State) (m : List Bool) :
    (run (cswap c a b) m s).phase = s.phase ∧
    (∀ w, w ≠ a → w ≠ b → (run (cswap c a b) m s).basis w = s.basis w) ∧
    (run (cswap c a b) m s).basis a = (if s.basis c then s.basis b else s.basis a) ∧
    (run (cswap c a b) m s).basis b = (if s.basis c then s.basis a else s.basis b) := by
  have hn : c ≠ a ∧ c ≠ b ∧ a ≠ b := by simpa [and_assoc] using hnd
  obtain ⟨hca, hcb, hab⟩ := hn
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro w ha hb
    simp [cswap, run, writeBit, ha, hb]
  all_goals cases hc : s.basis c <;> cases ha : s.basis a <;> cases hb : s.basis b <;>
    simp [cswap, run, writeBit, hca, hab, Ne.symm hab, hc, ha, hb]

/-- 右移网络实际是循环移位；规格中的偶数前提保证移出的最低位为零。 -/
def shiftRight (c : Wire) : List Wire → Program
  | a::b::bs => cswap c a b ++ shiftRight c (b::bs)
  | _ => []

/-- 左移按相反顺序执行同一组 CSWAP；只重排无测量交换门。 -/
def shiftLeft (c : Wire) : List Wire → Program
  | a::b::bs => shiftLeft c (b::bs) ++ cswap c a b
  | _ => []

theorem shift_wires (c : Wire) (r : List Wire) :
    wires (shiftRight c r) = (if r.length<2 then ∅ else (c::r).toFinset) ∧
    wires (shiftLeft c r) = (if r.length<2 then ∅ else (c::r).toFinset) := by
  induction r with
  | nil => simp [shiftRight, shiftLeft, wires]
  | cons a r ih =>
    cases r with
    | nil => simp [shiftRight, shiftLeft, wires]
    | cons b bs =>
      change wires (cswap c a b ++ shiftRight c (b::bs)) = _ ∧
        wires (shiftLeft c (b::bs) ++ cswap c a b) = _
      simp only [wires_append, ih.1, ih.2]
      cases bs with
      | nil => simp [cswap, wires, Instr.wires, Finset.union_comm]
      | cons d ds =>
        simp only [show ¬(b::d::ds).length<2 by simp,
          show ¬(a::b::d::ds).length<2 by simp, if_false]
        constructor <;> ext w <;> simp [cswap, wires, Instr.wires] <;> tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledModUnary.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledUnaryState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace UnaryValues

end UnaryValues
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledDoubleSteps.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace DoubleValues

end DoubleValues
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledDouble.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledHalf.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledUnaryResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SwapLow.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 规范值的未用高位为零。 -/
theorem regValue_take_drop_of_lt (r : List Wire) (n N : Nat) (s : BasisState)
    (hr : n≤r.length) (hv : regValue r s=N) (hb : N<2^n) :
    regValue (r.take n) s=N ∧ regValue (r.drop n) s=0 := by
  have hh := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hr, hv] at hh
  have hn : 0<2^n := by positivity
  have ht := regValue_lt (r.take n) s
  rw [List.length_take, Nat.min_eq_left hr] at ht
  have hz : regValue (r.drop n) s=0 := by
    by_contra h
    have : 1≤regValue (r.drop n) s := by omega
    nlinarith
  exact ⟨by simpa [hz] using hh.symm,hz⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ReplayCell.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace ModInPlaceLayout
/-- 回放的单目阶段借同一目标和零工作区。 -/
def unary (L : ModInPlaceLayout) : ModUnaryLayout :=
  ⟨L.low,L.high,L.constant,L.carry,L.cin,L.mask,L.flag⟩

end ModInPlaceLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ReplayCellState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace ReplayValues

end ReplayValues
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ReplayCellProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ReplayCellResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledNegRaw.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkSignedModAdd.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace ModInPlaceLayout

end ModInPlaceLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/SkywalkPayload.lean
noncomputable section

namespace ECDSAAdd
open Secp256k1

/-- The butterfly payload corresponding to logical Stein rails (u,v).
The common scale κ is unchanged by every exact replay cell. -/
def skywalkPayloadFor (u v : Nat) (κ : Fp) : Fp × Fp :=
  ((2*(u : Fp)+(v : Fp))*κ,(v : Fp)*κ)

/-- Forward division replay: signed half-add, then the recorded swap.
The payload never participates in selecting g or s. -/
def skywalkPayloadCell (g s : Bool) (q : Fp × Fp) : Fp × Fp :=
  let t := (q.1+(if g then q.2 else -q.2))/2
  if s then (q.2,t) else (t,q.2)

/-- Multiplication replay: undo the recorded swap, then double and signed add. -/
def skywalkPayloadUncell (g s : Bool) (q : Fp × Fp) : Fp × Fp :=
  let t := if s then (q.2,q.1) else q
  (2*t.1+(if g then -t.2 else t.2),t.2)

private theorem skywalk_two_ne_zero : (2 : Fp)≠0 := by
  change (2 : ZMod p)≠0
  decide

/-- Exact inverse on every field pair and every Boolean record. -/
theorem skywalkPayloadUncell_cell (g s : Bool) (q : Fp × Fp) :
    skywalkPayloadUncell g s (skywalkPayloadCell g s q)=q := by
  cases g <;> cases s <;> apply Prod.ext <;>
    simp [skywalkPayloadCell,skywalkPayloadUncell] <;>
    field_simp [skywalk_two_ne_zero] <;> ring

private theorem skywalk_cast_half (n : Nat) (he : n%2=0) :
    ((n/2 : Nat) : Fp)=(n : Fp)/2 := by
  apply (eq_div_iff skywalk_two_ne_zero).2
  norm_cast
  exact congrArg (fun k : Nat => (k : Fp))
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero he))

/-- The even-rail branch; zero is included, so terminal padding is exact. -/
theorem skywalkPayload_even (u v : Nat) (κ : Fp) (he : u%2=0) :
    skywalkPayloadCell true false (skywalkPayloadFor u v κ)=skywalkPayloadFor (u/2) v κ := by
  apply Prod.ext
  · change ((2*(u : Fp)+(v : Fp))*κ+(v : Fp)*κ)/2=
      (2*((u/2 : Nat) : Fp)+(v : Fp))*κ
    rw [skywalk_cast_half u he]
    field_simp [skywalk_two_ne_zero]
    ring
  · rfl

/-- Odd rails with u≤v: use the recorded swap, including the equality case. -/
theorem skywalkPayload_odd_le (u v : Nat) (κ : Fp)
    (hu : u%2=1) (hv : v%2=1) (hle : u≤v) :
    skywalkPayloadCell false true (skywalkPayloadFor u v κ)=skywalkPayloadFor ((v-u)/2) u κ := by
  have he : (v-u)%2=0 := by omega
  apply Prod.ext
  · change (v : Fp)*κ=(2*(((v-u)/2 : Nat) : Fp)+(u : Fp))*κ
    rw [skywalk_cast_half (v-u) he,Nat.cast_sub hle]
    field_simp [skywalk_two_ne_zero]
    ring
  · change ((2*(u : Fp)+(v : Fp))*κ+(-((v : Fp)*κ)))/2=(u : Fp)*κ
    field_simp [skywalk_two_ne_zero]
    ring

/-- Odd rails with v≤u: retain order, also including equality. -/
theorem skywalkPayload_odd_ge (u v : Nat) (κ : Fp)
    (hu : u%2=1) (hv : v%2=1) (hle : v≤u) :
    skywalkPayloadCell false false (skywalkPayloadFor u v κ)=skywalkPayloadFor ((u-v)/2) v κ := by
  have he : (u-v)%2=0 := by omega
  apply Prod.ext
  · change ((2*(u : Fp)+(v : Fp))*κ+(-((v : Fp)*κ)))/2=
      (2*(((u-v)/2 : Nat) : Fp)+(v : Fp))*κ
    rw [skywalk_cast_half (u-v) he,Nat.cast_sub hle]
    field_simp [skywalk_two_ne_zero]
    ring
  · rfl

/-- Equality accepts either sign record, and both logical updates are (0,u). -/
theorem skywalkPayload_equal (u : Nat) (κ : Fp) (s : Bool) (hu : u%2=1) :
    skywalkPayloadCell false s (skywalkPayloadFor u u κ)=skywalkPayloadFor 0 u κ := by
  cases s
  · simpa using skywalkPayload_odd_ge u u κ hu hu (Nat.le_refl u)
  · simpa using skywalkPayload_odd_le u u κ hu hu (Nat.le_refl u)

/-- secp256k1 initialization represents arbitrary Y, including Y=0. -/
theorem skywalkPayload_init (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) :
    skywalkPayloadFor x p (Y/(x : Fp))=(2*Y,0) := by
  have hnx : (x : Fp)≠0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hx] at hv
    simp only [ZMod.val_zero] at hv
    omega
  apply Prod.ext
  · change (2*(x : Fp)+(p : Fp))*(Y/(x : Fp))=2*Y
    rw [ZMod.natCast_self]
    field_simp [hnx]
    ring
  · change (p : Fp)*(Y/(x : Fp))=0
    rw [ZMod.natCast_self]
    simp

/-- At the exact coprime terminal rails, both payload registers contain κ. -/
theorem skywalkPayload_terminal (κ : Fp) : skywalkPayloadFor 0 1 κ=(κ,κ) := by
  simp [skywalkPayloadFor]

/-- Any correctly classified physical record preserves the logical invariant.
Only odd rails use sign/order constraints; equality may choose either record. -/
theorem skywalkPayload_step_record (z : SkywalkNat.State) (κ : Fp) (g s : Bool)
    (hv : z.v%2=1) (hg : g=decide (z.u%2=0))
    (hsEven : z.u%2=0 → s=false)
    (hsLe : z.u%2≠0 → s=true → z.u≤z.v)
    (hsGe : z.u%2≠0 → s=false → z.v≤z.u) :
    skywalkPayloadCell g s (skywalkPayloadFor z.u z.v κ)=
      skywalkPayloadFor (SkywalkNat.step z).u (SkywalkNat.step z).v κ := by
  by_cases he : z.u%2=0
  · have hgt : g=true := by simpa [he] using hg
    have hsf : s=false := hsEven he
    have hstep : SkywalkNat.step z=⟨z.u/2,z.v⟩ := by
      by_cases hz : z.u=0
      · apply SkywalkNat.State.ext <;> simp [SkywalkNat.step,hz]
      · simp [SkywalkNat.step,hz,he]
    rw [hgt,hsf,hstep]
    exact skywalkPayload_even z.u z.v κ he
  · have hgf : g=false := by simpa [he] using hg
    have hu : z.u%2=1 := by omega
    have hz : z.u≠0 := by omega
    rw [hgf]
    cases hs : s
    · have hle := hsGe he hs
      simpa [SkywalkNat.step,hz,he,hle] using skywalkPayload_odd_ge z.u z.v κ hu hv hle
    · have hle := hsLe he hs
      by_cases hge : z.v≤z.u
      · have heq : z.u=z.v := by omega
        have hv0 : z.v≠0 := by omega
        have heV : z.v%2≠0 := by omega
        simpa [SkywalkNat.step,heq,hv0,heV] using skywalkPayload_equal z.v κ true hv
      · simpa [SkywalkNat.step,hz,he,hge] using skywalkPayload_odd_le z.u z.v κ hu hv hle

/-- Canonical logical records; equality uses the unswapped form.
The equality lemma above also permits the physical sign convention's swapped form. -/
def skywalkPayloadCode (z : SkywalkNat.State) : Bool × Bool :=
  (decide (z.u%2=0),decide (z.u%2≠0 ∧ z.u<z.v))

/-- All records are replayed in time order; they are produced independently by the integer walk. -/
def skywalkPayloadReplay : List (Bool × Bool) → Fp × Fp → Fp × Fp
  | [], q => q
  | (g,s)::cs, q => skywalkPayloadReplay cs (skywalkPayloadCell g s q)

/-- Replay inversion is a separately specified forward formula, in reverse record order. -/
def skywalkPayloadReplayInverse : List (Bool × Bool) → Fp × Fp → Fp × Fp
  | [], q => q
  | (g,s)::cs, q => skywalkPayloadUncell g s (skywalkPayloadReplayInverse cs q)

theorem skywalkPayloadReplayInverse_replay (cs : List (Bool × Bool)) (q : Fp × Fp) :
    skywalkPayloadReplayInverse cs (skywalkPayloadReplay cs q)=q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨g,s⟩
    simp only [skywalkPayloadReplay,skywalkPayloadReplayInverse,ih,skywalkPayloadUncell_cell]

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/SkywalkPayloadProgram.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedFieldBridge.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Toggle the recorded sign convention around an independently verified
kernel. The generic Program boundary keeps gate streams sealed to proofs. -/
def fusedFieldSignedHalf (g : Wire) (kernel : Program) : Program :=
  [.X g]++kernel++[.X g]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/SkywalkRailsBridge.lean
noncomputable section

namespace ECDSAAdd.SkywalkRails

/-- Decode the unsigned smaller magnitude and the gap to the positive larger
rail. The orientation determines which physical rail is smaller. -/
def decode (t : Tick) : SkywalkNat.State :=
  let small := if t.g then t.h.natAbs else t.k.natAbs
  let large := if t.g then t.k else t.h
  ⟨small,(large-(small : Int)).toNat⟩

def railsOf (t : Tick) : State := ⟨t.h,t.k,t.g⟩

def smallerSign (t : Tick) : Bool := if t.g then neg t.h else neg t.k

private theorem signed_neg_abs (x : Int) : signed (neg x) |x|=x := by
  by_cases hn : x<0
  · simp [signed,neg,hn,abs_of_neg hn]
  · have hp : 0≤x := by omega
    simp [signed,neg,hn,abs_of_nonneg hp]

/-- Decoding loses no rail information when the smaller sign is retained.
The retained sign is the actual smaller-rail sign, not the sign-flip tape. -/
theorem frame_reencode (t : Tick) (hf : Frame t) :
    railsOf t=encode t.g (smallerSign t) ((decode t).u : Int) ((decode t).v : Int) := by
  cases hg : t.g
  · have hs : signed (neg t.k) (t.k.natAbs : Int)=t.k := by
      rw [Int.natCast_natAbs]
      exact signed_neg_abs t.k
    have hnonneg : 0≤t.h-(t.k.natAbs : Int) := by
      rw [Int.natCast_natAbs]
      simp only [Frame,hg,Bool.false_eq_true,if_false] at hf
      omega
    have hgap := Int.toNat_of_nonneg hnonneg
    have hsum : (t.k.natAbs : Int)+(t.h-(t.k.natAbs : Int)).toNat=t.h := by
      rw [hgap]
      omega
    simp only [railsOf,encode,smallerSign,decode,hg,Bool.false_eq_true,if_false]
    apply State.ext
    · exact hsum.symm
    · exact hs.symm
    · rfl
  · have hs : signed (neg t.h) (t.h.natAbs : Int)=t.h := by
      rw [Int.natCast_natAbs]
      exact signed_neg_abs t.h
    have hnonneg : 0≤t.k-(t.h.natAbs : Int) := by
      rw [Int.natCast_natAbs]
      simp only [Frame,hg,if_true] at hf
      omega
    have hgap := Int.toNat_of_nonneg hnonneg
    have hsum : (t.h.natAbs : Int)+(t.k-(t.h.natAbs : Int)).toNat=t.k := by
      rw [hgap]
      omega
    simp only [railsOf,encode,smallerSign,decode,hg,if_true]
    apply State.ext
    · exact hs.symm
    · exact hsum.symm
    · rfl

/-- Exact representation bridge to the all-input min-source Stein recurrence.
Signs are retained by the signed tick and only projected out by this theorem. -/
theorem decode_step_encode (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    decode (step (encode g s (z.u : Int) (z.v : Int)))=SkywalkNat.step z := by
  have hun : (0:Int)≤z.u := by omega
  have hvp : (0:Int)<z.v := by omega
  have hvi : (z.v : Int)%2=1 := by omega
  by_cases he : z.u%2=0
  · have hei : (z.u : Int)%2=0 := by omega
    have hhalf : ((z.u/2 : Nat) : Int)=(z.u : Int)/2 := by omega
    have hs : (signed s ((z.u : Int)/2)).natAbs=z.u/2 := by
      have hbase : (((z.u/2 : Nat) : Int)).natAbs=z.u/2 := rfl
      rw [←hhalf]
      cases s with
      | false => exact hbase
      | true => exact (Int.natAbs_neg _).trans hbase
    have hgap : (z.u : Int)/2+(z.v : Int)-((z.u/2 : Nat) : Int)=(z.v : Int) := by
      rw [←hhalf]
      omega
    rw [step_encode_even g s _ _ hun hvp hvi hei]
    simp only [decode,if_true,hs,hgap]
    by_cases hz : z.u=0
    · simp only [SkywalkNat.step,hz,if_true]
      cases z
      simp_all
    · simp [SkywalkNat.step,hz,he]
  · have hei : (z.u : Int)%2≠0 := by omega
    have hzero : z.u≠0 := by omega
    rw [step_encode_odd g s _ _ hun hvp hvi hei]
    by_cases hle : z.v≤z.u
    · let d := (z.u-z.v)/2
      have hd : ((z.u : Int)-(z.v : Int))/2=(d : Int) := by dsimp [d]; omega
      have hn : ((z.v : Int)-(z.u : Int))/2=-(d : Int) := by dsimp [d]; omega
      have hk : (if s then ((z.v : Int)-(z.u : Int))/2 else
          ((z.u : Int)-(z.v : Int))/2).natAbs=d := by
        cases s <;> simp [hd,hn]
      have hgap : ((z.u : Int)+(z.v : Int))/2-(d : Int)=(z.v : Int) := by
        dsimp [d]
        omega
      simp only [decode,Bool.false_eq_true,if_false,hk,hgap]
      simp [SkywalkNat.step,hzero,he,hle,d]
    · let d := (z.v-z.u)/2
      have hd : ((z.v : Int)-(z.u : Int))/2=(d : Int) := by dsimp [d]; omega
      have hn : ((z.u : Int)-(z.v : Int))/2=-(d : Int) := by dsimp [d]; omega
      have hk : (if s then ((z.v : Int)-(z.u : Int))/2 else
          ((z.u : Int)-(z.v : Int))/2).natAbs=d := by
        cases s <;> simp [hd,hn]
      have hgap : ((z.u : Int)+(z.v : Int))/2-(d : Int)=(z.u : Int) := by
        dsimp [d]
        omega
      simp only [decode,Bool.false_eq_true,if_false,hk,hgap]
      simp [SkywalkNat.step,hzero,he,hle,d]

/-- A complete one-step reachability statement, sufficient to reapply the
encoded-rail invariants at every later step. -/
theorem step_reencode (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    let t := step (encode g s (z.u : Int) (z.v : Int))
    railsOf t=encode t.g (smallerSign t)
      ((SkywalkNat.step z).u : Int) ((SkywalkNat.step z).v : Int) := by
  dsimp only
  have hf := step_frame g s (z.u : Int) (z.v : Int)
    (by omega) (by omega) (by omega)
  simpa only [decode_step_encode g s z hv hvo] using frame_reencode _ hf

end ECDSAAdd.SkywalkRails
end

-- source: ECDSAAdd/Math/SkywalkTrace.lean
noncomputable section

namespace ECDSAAdd.SkywalkTrace
open SkywalkRails Secp256k1

def next (r : SkywalkRails.State) : SkywalkRails.State := railsOf (SkywalkRails.step r)

/-- The transcript records the actual signed tick, including its zero/tie sign. -/
def code (r : SkywalkRails.State) : Bool×Bool :=
  let t := SkywalkRails.step r
  (t.g,t.s)

def trace : Nat → SkywalkRails.State → List (Bool×Bool)
  | 0, _ => []
  | n+1, r => code r::trace n (next r)

theorem trace_length (n : Nat) (r : SkywalkRails.State) : (trace n r).length=n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp [trace,ih]

/-- Full physical signed representation is preserved at every iteration.
Orientation and the actual smaller sign are retained rather than projected away. -/
theorem iter_encoded (i : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    ∃ G S : Bool, (next^[i] (encode g s (z.u : Int) (z.v : Int)))=
      encode G S ((SkywalkNat.step^[i] z).u : Int) ((SkywalkNat.step^[i] z).v : Int) := by
  induction i with
  | zero => exact ⟨g,s,rfl⟩
  | succ i ih =>
    obtain ⟨G,S,henc⟩ := ih
    let zi := SkywalkNat.step^[i] z
    have hvalid := SkywalkNat.iter_valid i z hv hvo
    let t := SkywalkRails.step (encode G S (zi.u : Int) (zi.v : Int))
    refine ⟨t.g,smallerSign t,?_⟩
    rw [Function.iterate_succ_apply',henc]
    have hr := step_reencode G S zi hvalid.1 hvalid.2.1
    simpa only [next,zi,Function.iterate_succ_apply'] using hr

/-- All premises of the field trajectory are supplied by the actual integer
record. Weak order is intentional: either sign is valid at u=v. -/
theorem code_classified (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    let c := code (encode g s (z.u : Int) (z.v : Int))
    c.1=decide (z.u%2=0) ∧
    (z.u%2=0 → c.2=false) ∧
    (z.u%2≠0 → c.2=true → z.u≤z.v) ∧
    (z.u%2≠0 → c.2=false → z.v≤z.u) := by
  dsimp only
  have hvi : (z.v : Int)%2=1 := by omega
  have hpar : ((z.u : Int)%2=0) ↔ z.u%2=0 := by omega
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [code,hpar] using step_orientation g s (z.u : Int) (z.v : Int) hvi
  · intro he
    change (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).s=false
    rw [step_encode_even g s _ _ (by omega) (by omega) hvi (by omega)]
  · intro he hs
    change (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).s=true at hs
    have horder := odd_flip_order g s (z.u : Int) (z.v : Int)
      (by omega) (by omega) hvi (by omega)
    have hle := horder.2 hs
    omega
  · intro he hs
    change (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).s=false at hs
    have horder := odd_flip_order g s (z.u : Int) (z.v : Int)
      (by omega) (by omega) hvi (by omega)
    have hle := horder.1 hs
    omega

theorem iter_code_classified (i : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    let zi := SkywalkNat.step^[i] z
    let c := code (next^[i] (encode g s (z.u : Int) (z.v : Int)))
    c.1=decide (zi.u%2=0) ∧
    (zi.u%2=0 → c.2=false) ∧
    (zi.u%2≠0 → c.2=true → zi.u≤zi.v) ∧
    (zi.u%2≠0 → c.2=false → zi.v≤zi.u) := by
  dsimp only
  obtain ⟨G,S,henc⟩ := iter_encoded i g s z hv hvo
  rw [henc]
  have hvalid := SkywalkNat.iter_valid i z hv hvo
  exact code_classified G S _ hvalid.1 hvalid.2.1

/-- A single actual integer letter drives the exact butterfly field invariant.
The scale κ may be zero; payloads do not classify the integer record. -/
theorem payload_step (g s : Bool) (z : SkywalkNat.State) (κ : Fp)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    let c := code (encode g s (z.u : Int) (z.v : Int))
    skywalkPayloadCell c.1 c.2 (skywalkPayloadFor z.u z.v κ)=
      skywalkPayloadFor (SkywalkNat.step z).u (SkywalkNat.step z).v κ := by
  have hc := code_classified g s z hv hvo
  exact skywalkPayload_step_record z κ _ _ hvo hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- Replay is coupled to the actual signed transcript, not a tie convention
chosen separately from the integer implementation. -/
theorem payload_trace (n : Nat) (g s : Bool) (z : SkywalkNat.State) (κ : Fp)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    skywalkPayloadReplay (trace n (encode g s (z.u : Int) (z.v : Int)))
      (skywalkPayloadFor z.u z.v κ)=
      skywalkPayloadFor (SkywalkNat.step^[n] z).u (SkywalkNat.step^[n] z).v κ := by
  induction n generalizing g s z with
  | zero => rfl
  | succ n ih =>
    let r := encode g s (z.u : Int) (z.v : Int)
    let t := SkywalkRails.step r
    have hcell := payload_step g s z κ hv hvo
    have heq := step_reencode g s z hv hvo
    change next r=encode t.g (smallerSign t) ((SkywalkNat.step z).u : Int)
      ((SkywalkNat.step z).v : Int) at heq
    change skywalkPayloadReplay (trace n (next r))
      (skywalkPayloadCell (code r).1 (code r).2 (skywalkPayloadFor z.u z.v κ))=_
    rw [hcell,heq]
    have hvalid := SkywalkNat.step_v_odd_pos z hv hvo
    simpa only [Function.iterate_succ_apply] using
      ih t.g (smallerSign t) (SkywalkNat.step z) hvalid.1 hvalid.2

/-- Universal secp256k1 quotient trajectory for all canonical nonzero x and
all Y, driven by the actual512 signed-rail records. -/
theorem quotient512 (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) :
    skywalkPayloadReplay (trace 512 (encode false false (x : Int) (p : Int)))
      (2*Y,0)=(Y/(x : Fp),Y/(x : Fp)) := by
  have hp0 : 0<p := by norm_num [p]
  have hpodd : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have hc : x.Coprime p := by
    apply Nat.Coprime.symm
    apply Secp256k1.p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have ht := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpodd hp (hx.trans hp) hc
  have hr := payload_trace 512 false false (SkywalkNat.init x p)
    (Y/(x : Fp)) hp0 hpodd
  change skywalkPayloadReplay _ (skywalkPayloadFor x p (Y/(x : Fp)))=_ at hr
  rw [skywalkPayload_init x Y hx0 hx] at hr
  have hu : ((SkywalkNat.step^[512]) (SkywalkNat.init x p)).u=0 := ht.1
  have hv : ((SkywalkNat.step^[512]) (SkywalkNat.init x p)).v=1 := ht.2
  rw [hu,hv,skywalkPayload_terminal] at hr
  exact hr

/-- The same actual transcript gives exact multiplication in reverse. -/
theorem product512 (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) :
    skywalkPayloadReplayInverse (trace 512 (encode false false (x : Int) (p : Int)))
      (Y,Y)=(2*(Y*(x : Fp)),0) := by
  have hnx : (x : Fp)≠0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hx] at hv
    simp only [ZMod.val_zero] at hv
    omega
  have hq := quotient512 x (Y*(x : Fp)) hx0 hx
  rw [mul_div_cancel_right₀ Y hnx] at hq
  rw [←hq,skywalkPayloadReplayInverse_replay]

end ECDSAAdd.SkywalkTrace
end

-- source: ECDSAAdd/Arithmetic/SkywalkIntegerTick.lean
noncomputable section

namespace ECDSAAdd.Arithmetic



/-- Executable exact parity-route, signed relabelled half, native signed
record, and orientation history update. The two history bits remain coherent. -/
def skywalkIntegerTick (L : SkywalkIntegerLayout) : Program :=
  skywalkRoute L.a0 L.b0 L.ah L.bh ++
  skywalkSignedHalf L.aSign L.ext ++
  signedRecord L.ext L.bSign L.history L.half L.b L.carry ++
  [.CX L.previous L.a0]

/-- Forward inverse arithmetic, with fresh measurement records. Original low
parity is recovered before undoing the high-word routing. -/
def skywalkIntegerUntick (L : SkywalkIntegerLayout) : Program :=
  [.CX L.previous L.a0] ++
  signedUnrecord L.ext L.bSign L.history L.half L.b L.carry ++
  skywalkSignedHalf L.aSign L.ext ++ [.CX L.a0 L.b0] ++
  swapRegisters L.a0 L.ah L.bh

def SkywalkIntegerInput (L : SkywalkIntegerLayout) (A B : Int) (G : Bool)
    (s : BasisState) : Prop :=
  signedRegValue L.a s=A ∧ signedRegValue L.b s=B ∧ s L.previous=G ∧
  s L.ext=false ∧ s L.history=false ∧ regValue L.carry s=0

def SkywalkIntegerOutput (L : SkywalkIntegerLayout) (A B : Int) (G : Bool)
    (s : BasisState) : Prop :=
  let t := SkywalkRails.step ⟨A,B,G⟩
  signedRegValue L.half s=t.h ∧ signedRegValue L.b s=t.k ∧
  s L.a0=t.g ∧ s L.history=t.s ∧ s L.previous=G ∧ regValue L.carry s=0

private theorem prefix_no_measure (p q : Program) (hp : measurementCount p=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  have hr := run_take p m s
  rw [hp,List.take_zero] at hr
  rw [run_append,hp,List.take_zero,List.drop_zero,hr]

private theorem suffix_no_measure (p q : Program) (hq : measurementCount q=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  rw [run_append,run_take]
  have h1 := run_take q (m.drop (measurementCount p)) (run p m s)
  have h2 := run_take q m (run p m s)
  rw [hq,List.take_zero] at h1 h2
  exact h1.symm.trans h2

private theorem tick_run (L : SkywalkIntegerLayout) (hv : L.Valid) (s : State) (m : List Bool) :
    run (skywalkIntegerTick L) m s=
      run [.CX L.previous L.a0] m
        (run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m
          (run (skywalkSignedHalf L.aSign L.ext) m
            (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s))) := by
  have hr := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv)).2
  have hh := (skywalkSignedHalf_counts L.aSign L.ext).2
  simp only [skywalkIntegerTick,List.append_assoc]
  rw [prefix_no_measure _ _ hr,prefix_no_measure _ _ hh,
    suffix_no_measure _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0)]

private theorem route_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.ext::L.carry) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis q=s.basis q := by
  have hn : ((L.previous::L.history::L.ext::L.carry)++
      (L.a0::L.b0::(L.ah++L.bh))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  apply run_preserves_outside
  intro hm
  have hh := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) hm
  exact List.disjoint_left.mp hd hq (List.mem_toFinset.mp hh)

private theorem half_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.a0::(L.b++L.carry)) :
    (run (skywalkSignedHalf L.aSign L.ext) m s).basis q=s.basis q := by
  have hne : q≠L.ext := by
    intro he
    subst q
    have hh := List.nodup_iff_count.mp hv.nodup L.ext
    have hp := List.count_pos_iff.mpr hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.b,
      List.count_cons,List.count_append] at hh hp
    simp only [beq_self_eq_true,if_true] at hh
    omega
  exact (skywalkSignedHalf_frame L.aSign L.ext s m).2 q hne

private theorem record_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire) (hq : q∈[L.previous,L.a0]) :
    (run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m s).basis q=s.basis q := by
  have hn : ([L.previous,L.a0]++(L.history::(L.half++L.b++L.carry))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
      List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  have hc := L.record_lengths hv
  exact (signedRecord_frame L.ah (L.b0::L.bMid) L.ext L.bSign L.history L.carry
    hc.1 hc.2 s m q (fun hm => List.disjoint_left.mp hd hq hm)).1

private theorem ext_outside_high (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.ext∉L.ah := by
  intro hm
  have hh := List.nodup_iff_count.mp hv.nodup L.ext
  have hp := List.count_pos_iff.mpr hm
  simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh
  simp only [beq_self_eq_true,if_true] at hh
  omega

private theorem ext_sign_ne (L : SkywalkIntegerLayout) (hv : L.Valid) : L.aSign≠L.ext := by
  intro he
  exact ext_outside_high L hv (by simp [SkywalkIntegerLayout.ah,←he])

private theorem previous_low_ne (L : SkywalkIntegerLayout) (hv : L.Valid) : L.previous≠L.a0 := by
  intro he
  have hh := List.nodup_iff_count.mp hv.nodup L.previous
  simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh
  simp [he] at hh

private theorem route_int_values (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (hp : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (hext : s.basis L.ext=false) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).phase=s.phase ∧
    signedRegValue (L.ext::L.ah) (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).1 ∧
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).2 ∧
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis L.a0=SkywalkRails.odd A := by
  have hna : L.ah≠[] := by simp [SkywalkIntegerLayout.ah]
  have hnb : L.bh≠[] := by simp [SkywalkIntegerLayout.bh]
  have hA := ha.symm.trans (signedRegValue_cons L.a0 L.ah s.basis hna)
  have hB := hb.symm.trans (signedRegValue_cons L.b0 L.bh s.basis hnb)
  have hpar : s.basis L.b0=(!s.basis L.a0) := by
    cases hca : s.basis L.a0 with
    | false =>
      cases hcb : s.basis L.b0 with
      | false =>
        simp [hca,hcb] at hA hB
        omega
      | true => rfl
    | true =>
      cases hcb : s.basis L.b0 with
      | false => rfl
      | true =>
        simp [hca,hcb] at hA hB
        omega
  have hctrl : s.basis L.a0=SkywalkRails.odd A := by
    cases hc : s.basis L.a0 with
    | false =>
      have he : A%2=0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
    | true =>
      have he : A%2≠0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  obtain ⟨hf,_,hctl,hlo,hrawA,hrawB⟩ := skywalkRoute_correct L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv) s m hpar
  have he0 : t.basis L.ext=false :=
    (route_aux_frame L hv s m L.ext (by simp)).trans hext
  have hsa : signedRegValue L.ah t.basis=
      if s.basis L.a0 then signedRegValue L.bh s.basis else signedRegValue L.ah s.basis := by
    have hh := congrArg (signedDecode L.ah.length) hrawA
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  have hsb : signedRegValue L.bh t.basis=
      if s.basis L.a0 then signedRegValue L.ah s.basis else signedRegValue L.bh s.basis := by
    have hh := congrArg (signedDecode L.bh.length) hrawB
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  refine ⟨hf,?_,?_,hctl.trans hctrl⟩
  · rw [signedRegValue_cons L.ext L.ah t.basis hna,he0,hsa]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

  · change signedRegValue (L.b0::L.bh) t.basis=_
    rw [signedRegValue_cons L.b0 L.bh t.basis hnb,hlo,hsb]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

private theorem low_outside_record (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.a0∉L.history::(L.half++L.b++L.carry) := by
  intro hm
  have hh := List.nodup_iff_count.mp hv.nodup L.a0
  have hp := List.count_pos_iff.mpr hm
  simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
    List.count_cons,List.count_append,List.count_nil] at hh hp
  simp only [beq_self_eq_true,if_true] at hh
  omega

/-- Actual routed, sign-extended and recorded bits implement the unbounded
signed tick exactly, including zero rails and both equality sign histories. -/
theorem skywalkIntegerTick_spec (L : SkywalkIntegerLayout) (hv : L.Valid)
    (A B : Int) (G : Bool) (hp : (A+B)%2=1) :
    Triple (SkywalkIntegerInput L A B G) (skywalkIntegerTick L)
      (SkywalkIntegerOutput L A B G) := by
  intro s m hin
  let E := (SkywalkRails.route A B).1
  let O := (SkywalkRails.route A B).2
  let H := E/2
  let K := signedRecordValue H O
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  let u := run (skywalkSignedHalf L.aSign L.ext) m t
  let v := run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m u
  have he : E%2=0 := SkywalkRails.route_even A B hp
  obtain ⟨htp,hE,hO,hC⟩ := route_int_values L hv A B hp s m hin.1 hin.2.1 hin.2.2.2.1
  change signedRegValue (L.ext::(L.aMid++[L.aSign])) t.basis=E at hE
  have tq : t.basis L.history=false :=
    (route_aux_frame L hv s m L.history (by simp)).trans hin.2.2.2.2.1
  have tp : t.basis L.previous=G :=
    (route_aux_frame L hv s m L.previous (by simp)).trans hin.2.2.1
  have tk : regValue L.carry t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hin.2.2.2.2.2
    intro q hq
    exact route_aux_frame L hv s m q (by simp [hq])
  have uH : signedRegValue L.half u.basis=H := by
    have hh := skywalkSignedHalf_int L.ext L.aSign L.aMid (ext_sign_ne L hv)
      (ext_outside_high L hv) t m (by rw [hE]; exact he)
    change signedRegValue L.half u.basis=
      signedRegValue (L.ext::(L.aMid++[L.aSign])) t.basis/2 at hh
    rw [hE] at hh
    exact hh
  have uO : signedRegValue L.b u.basis=O := by
    apply Eq.trans ((signedRegValue_eq_iff _ _ _).mpr ?_) hO
    intro q hq
    exact half_aux_frame L hv t m q (by simp [hq])
  have uq : u.basis L.history=false :=
    (half_aux_frame L hv t m L.history (by simp)).trans tq
  have up : u.basis L.previous=G :=
    (half_aux_frame L hv t m L.previous (by simp)).trans tp
  have uc : u.basis L.a0=SkywalkRails.odd A :=
    (half_aux_frame L hv t m L.a0 (by simp)).trans hC
  have uk : regValue L.carry u.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) tk
    intro q hq
    exact half_aux_frame L hv t m q (by simp [hq])
  have hl := L.record_lengths hv
  obtain ⟨hvp,hval⟩ := signedRecord_spec L.ah (L.b0::L.bMid) L.ext L.bSign L.history
    L.carry (L.record_nodup hv) hl.1 hl.2 H O u m ⟨uq,uH,uO,uk⟩
  have vp : v.basis L.previous=G :=
    (record_aux_frame L hv u m L.previous (by simp)).trans up
  have vc : v.basis L.a0=SkywalkRails.odd A :=
    (record_aux_frame L hv u m L.a0 (by simp)).trans uc
  have hsame : SkywalkRails.sameSign H O=SkywalkRails.sameSign E O := by
    unfold SkywalkRails.sameSign
    rw [SkywalkRails.neg_half E he]
  have hK : K=(if SkywalkRails.sameSign E O then O-H else O+H) := by
    change signedRecordValue H O=_
    rw [signedRecordValue_rails,hsame]
  rw [tick_run L hv s m]
  have keep (q : Wire) (hq : q∈L.history::(L.half++L.b++L.carry)) :
      (run [.CX L.previous L.a0] m v).basis q=v.basis q := by
    have hne : q≠L.a0 := fun he => low_outside_record L hv (he ▸ hq)
    simp [run,writeBit,hne]
  have hHfinal : signedRegValue L.half (run [.CX L.previous L.a0] m v).basis=H := by
    apply Eq.trans ((signedRegValue_eq_iff _ _ _).mpr ?_) hval.2.1
    intro q hq
    change q∈L.half at hq
    exact keep q (by simp [hq])
  have hOfinal : signedRegValue L.b (run [.CX L.previous L.a0] m v).basis=K := by
    apply Eq.trans ((signedRegValue_eq_iff _ _ _).mpr ?_) hval.2.2.1
    intro q hq
    change q∈L.b at hq
    exact keep q (by simp [hq])
  have hqfinal : (run [.CX L.previous L.a0] m v).basis L.history=
      (SkywalkRails.neg O ^^ SkywalkRails.neg K) :=
    (keep L.history (by simp)).trans hval.1
  have hpfinal : (run [.CX L.previous L.a0] m v).basis L.previous=G := by
    simpa [run,writeBit,previous_low_ne L hv] using vp
  have hkfinal : regValue L.carry (run [.CX L.previous L.a0] m v).basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hval.2.2.2
    intro q hq
    exact keep q (by simp [hq])
  have hcfinal : (run [.CX L.previous L.a0] m v).basis L.a0=
      (G ^^ SkywalkRails.odd A) := by
    simp only [run,writeBit,Function.update_self,vc,vp]
    exact Bool.xor_comm _ _
  refine ⟨hvp.trans ((skywalkSignedHalf_frame L.aSign L.ext t m).1.trans htp),?_⟩
  dsimp only [SkywalkIntegerOutput,SkywalkRails.step]
  simpa only [E,O,H,←hK] using
    (show signedRegValue L.half (run [.CX L.previous L.a0] m v).basis=H ∧
      signedRegValue L.b (run [.CX L.previous L.a0] m v).basis=K ∧
      (run [.CX L.previous L.a0] m v).basis L.a0=(G ^^ SkywalkRails.odd A) ∧
      (run [.CX L.previous L.a0] m v).basis L.history=(SkywalkRails.neg O ^^ SkywalkRails.neg K) ∧
      (run [.CX L.previous L.a0] m v).basis L.previous=G ∧
      regValue L.carry (run [.CX L.previous L.a0] m v).basis=0 from
      ⟨hHfinal,hOfinal,hcfinal,hqfinal,hpfinal,hkfinal⟩)

/-- Actual support is confined to the explicit rail/carry/history interface. -/
theorem skywalkIntegerTick_wires_subset (L : SkywalkIntegerLayout) (hv : L.Valid) :
    wires (skywalkIntegerTick L)⊆L.wires.toFinset ∧
    wires (skywalkIntegerUntick L)⊆L.wires.toFinset := by
  have hl := L.high_lengths hv
  have hc := L.record_lengths hv
  have hroute : wires (skywalkRoute L.a0 L.b0 L.ah L.bh)⊆L.wires.toFinset := by
    intro q hq
    have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh hl hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have hswap : wires (swapRegisters L.a0 L.ah L.bh)⊆L.wires.toFinset := by
    intro q hq
    have h := swapRegisters_wires L.a0 L.ah L.bh hl hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have hhalf : wires (skywalkSignedHalf L.aSign L.ext)⊆L.wires.toFinset := by
    rw [skywalkSignedHalf_wires]
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · simp [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah]
    · simp [SkywalkIntegerLayout.wires]
  have hword := signedRecord_wires L.ah (L.b0::L.bMid) L.ext L.bSign L.history L.carry hc.1 hc.2
  have hsigned :
      wires (signedRecord L.ext L.bSign L.history L.half L.b L.carry)=
        (L.history::(L.half++L.b++L.carry)).toFinset ∧
      wires (signedUnrecord L.ext L.bSign L.history L.half L.b L.carry)=
        (L.history::(L.half++L.b++L.carry)).toFinset := hword
  have hown : (L.history::(L.half++L.b++L.carry)).toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hrecord : wires (signedRecord L.ext L.bSign L.history L.half L.b L.carry)⊆L.wires.toFinset := by
    rw [hsigned.1]
    exact hown
  have hunrecord : wires (signedUnrecord L.ext L.bSign L.history L.half L.b L.carry)⊆L.wires.toFinset := by
    rw [hsigned.2]
    exact hown
  have hprevious : wires [.CX L.previous L.a0]⊆L.wires.toFinset := by
    simp [SkywalkIntegerLayout.wires,wires,Instr.wires]
  have hlow : wires [.CX L.a0 L.b0]⊆L.wires.toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [skywalkIntegerTick,skywalkIntegerUntick,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨hroute,hhalf⟩,hrecord⟩,hprevious⟩,
    ⟨⟨⟨⟨hprevious,hunrecord⟩,hhalf⟩,hlow⟩,hswap⟩⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkIntegerLoopCore.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] skywalkIntegerTick skywalkIntegerUntick
attribute [local irreducible] run

/-- Complete concrete-pool stage: current rails and orientation, actual past
records, all future fresh sites, reused carry, and the seed orientation. -/
def SkywalkIntegerStage (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (s : BasisState) : Prop :=
  let ri := SkywalkTrace.next^[i] r
  signedRegValue (skywalkPoolA w i) s=ri.a ∧
  signedRegValue (skywalkPoolB w) s=ri.b ∧
  s (w (skywalkPoolPreviousId i))=ri.g ∧
  (∀ j,j < i → s (w j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 ∧
    s (w (1028+j))=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).2) ∧
  (∀ j,i≤j → j<512 → s (w (j+258))=false ∧ s (w (1028+j))=false) ∧
  regValue (wireBlock w 1540 257) s=0 ∧ s (w 1797)=false

private theorem pool_index_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<512) (hj : j<1798) (hm : j∉skywalkPoolTickIds i) :
    w j∉(skywalkPoolTick w i).wires := by
  rw [skywalkPool_wires_map]
  intro h
  obtain ⟨k,hk,he⟩ := List.mem_map.mp h
  have hkj := skywalkPool_index_inj w hn k j (skywalkPool_id_bound i k hi hk) hj he
  subst k
  exact hm hk

private theorem past_orientation_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<512) (hj : j+1< i) :
    w j∉(skywalkPoolTick w i).wires := by
  apply pool_index_outside w hn i j hi (by omega)
  have hz : i≠0 := by omega
  simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
    List.mem_append,List.mem_range'_1]
  omega

private theorem past_sign_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<512) (hj : j < i) :
    w (1028+j)∉(skywalkPoolTick w i).wires := by
  apply pool_index_outside w hn i (1028+j) hi (by omega)
  by_cases hz : i=0
  · omega
  · simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
      List.mem_append,List.mem_range'_1]
    omega

private theorem initial_orientation_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) (hz : i≠0) :
    w 1797∉(skywalkPoolTick w i).wires := by
  apply pool_index_outside w hn i 1797 hi (by omega)
  simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
    List.mem_append,List.mem_range'_1]
  omega

private theorem tick_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉(skywalkPoolTick w i).wires) :
    (run (skywalkIntegerTick (skywalkPoolTick w i)) m s).basis q=s.basis q := by
  have hs := skywalkIntegerTick_wires_subset (skywalkPoolTick w i) (skywalkPool_valid w i hi hn)
  exact run_preserves_outside (skywalkIntegerTick (skywalkPoolTick w i)) m s q
    (fun hm => hq (List.mem_toFinset.mp (hs.1 hm)))

/-- One concrete tick advances the complete pool partition and extends the
actual transcript while preserving every earlier record and future zero site. -/
theorem skywalkIntegerStage_step (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (r : SkywalkRails.State) (i : Nat) (hi : i<512)
    (hodd : ((SkywalkTrace.next^[i] r).a+(SkywalkTrace.next^[i] r).b)%2=1) :
    Triple (SkywalkIntegerStage w r i) (skywalkIntegerTick (skywalkPoolTick w i))
      (SkywalkIntegerStage w r (i+1)) := by
  intro s m hin
  let L := skywalkPoolTick w i
  let ri := SkywalkTrace.next^[i] r
  let t := SkywalkRails.step ri
  generalize hout : run (skywalkIntegerTick L) m s = out
  have hv := skywalkPool_valid w i hi hn
  have fresh := hin.2.2.2.2.1 i (Nat.le_refl i) hi
  have hnative : SkywalkIntegerInput L ri.a ri.b ri.g s.basis := by
    refine ⟨?_,?_,hin.2.2.1,fresh.1,fresh.2,hin.2.2.2.2.2.1⟩
    · rw [skywalkPool_a]
      exact hin.1
    · rw [skywalkPool_b]
      exact hin.2.1
  obtain ⟨hf,ho⟩ := skywalkIntegerTick_spec L hv ri.a ri.b ri.g hodd s m hnative
  rw [hout] at hf ho
  have hframe : ∀ q, q∉L.wires → out.basis q=s.basis q := by
    intro q hq
    have hh := tick_outside w hn i hi s m q hq
    change (run (skywalkIntegerTick L) m s).basis q=s.basis q at hh
    rw [hout] at hh
    exact hh
  change signedRegValue L.half out.basis=t.h ∧ signedRegValue L.b out.basis=t.k ∧
    out.basis L.a0=t.g ∧ out.basis L.history=t.s ∧ out.basis L.previous=ri.g ∧
    regValue L.carry out.basis=0 at ho
  have hnext : SkywalkTrace.next^[i+1] r=SkywalkRails.railsOf t := by
    rw [Function.iterate_succ_apply']
    rfl
  refine ⟨hf,?_⟩
  dsimp only [SkywalkIntegerStage]
  rw [hnext]
  refine ⟨?_,?_,?_,?_,?_,ho.2.2.2.2.2,?_⟩
  · have hh := ho.1
    rw [skywalkPool_half] at hh
    exact hh
  · have hh := ho.2.1
    rw [skywalkPool_b] at hh
    exact hh
  · change out.basis (skywalkPoolTick w (i+1)).previous=t.g
    rw [(skywalkPool_chain w i).2.2]
    exact ho.2.2.1
  · intro j hj
    by_cases heq : j=i
    · subst j
      exact ⟨ho.2.2.1,ho.2.2.2.1⟩
    · have hji : j < i := by omega
      have priorValues := hin.2.2.2.1 j hji
      have kg : out.basis (w j)=s.basis (w j) := by
        by_cases hlast : j+1=i
        · have hiz : i≠0 := by omega
          have hpidx : skywalkPoolPreviousId i=j := by
            rw [skywalkPoolPreviousId,if_neg hiz]
            omega
          have hh := ho.2.2.2.2.1.trans hin.2.2.1.symm
          simpa only [L,skywalkPoolTick,hpidx] using hh
        · exact hframe (w j)
            (past_orientation_outside w hn i j hi (by omega))
      have ks := hframe (w (1028+j))
        (past_sign_outside w hn i j hi hji)
      exact ⟨kg.trans priorValues.1,ks.trans priorValues.2⟩
  · intro j hj hjmax
    have priorValues := hin.2.2.2.2.1 j (by omega) hjmax
    have hnew := skywalkPool_fresh_previous w j i hjmax (by omega) hn
    have ke := hframe (w (j+258)) hnew.1
    have ks := hframe (w (1028+j)) hnew.2
    exact ⟨ke.trans priorValues.1,ks.trans priorValues.2⟩
  · by_cases hz : i=0
    · subst i
      exact (ho.2.2.2.2.1.trans hin.2.2.1.symm).trans hin.2.2.2.2.2.2
    · exact (hframe (w 1797)
        (initial_orientation_outside w hn i hi hz)).trans hin.2.2.2.2.2.2

attribute [local irreducible] SkywalkTrace.next Nat.iterate

section LoopSpec
attribute [local irreducible] SkywalkIntegerStage

end LoopSpec

private theorem block_member (w : Nat → Wire) (start len j : Nat)
    (hlo : start≤j) (hhi : j<start+len) : w j∈wireBlock w start len := by
  apply List.mem_map.mpr
  exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩

/-- The stage assertion uniquely determines every one of the1798 pool bits.
External registers and the global input phase are intentionally unrestricted. -/
theorem skywalkIntegerStage_agrees (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (hi : i≤512) (s t : BasisState) (hs : SkywalkIntegerStage w r i s)
    (ht : SkywalkIntegerStage w r i t) : ∀ q∈skywalkPoolWires w,s q=t q := by
  have hA := (signedRegValue_eq_iff (skywalkPoolA w i) s t).mp (hs.1.trans ht.1.symm)
  have hB := (signedRegValue_eq_iff (skywalkPoolB w) s t).mp (hs.2.1.trans ht.2.1.symm)
  intro q hq
  change q∈(List.range' 0 1798).map w at hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hj
  by_cases hpast : j < i
  · exact (hs.2.2.2.1 j hpast).1.trans (ht.2.2.2.1 j hpast).1.symm
  by_cases ha : j < i+258
  · exact hA (w j) (block_member w i 258 j (by omega) ha)
  by_cases hf : j<770
  · have hk0 : i≤j-258 := by omega
    have hk1 : j-258<512 := by omega
    have he : j-258+258=j := by omega
    have h1 := (hs.2.2.2.2.1 (j-258) hk0 hk1).1
    have h2 := (ht.2.2.2.2.1 (j-258) hk0 hk1).1
    rw [he] at h1 h2
    exact h1.trans h2.symm
  by_cases hb : j<1028
  · exact hB (w j) (block_member w 770 258 j (by omega) hb)
  by_cases hps : j<1028+i
  · have hk : j-1028< i := by omega
    have he : 1028+(j-1028)=j := by omega
    have h1 := (hs.2.2.2.1 (j-1028) hk).2
    have h2 := (ht.2.2.2.1 (j-1028) hk).2
    rw [he] at h1 h2
    exact h1.trans h2.symm
  by_cases hfs : j<1540
  · have hk0 : i≤j-1028 := by omega
    have hk1 : j-1028<512 := by omega
    have he : 1028+(j-1028)=j := by omega
    have h1 := (hs.2.2.2.2.1 (j-1028) hk0 hk1).2
    have h2 := (ht.2.2.2.2.1 (j-1028) hk0 hk1).2
    rw [he] at h1 h2
    exact h1.trans h2.symm
  by_cases hc : j<1797
  · have hm := block_member w 1540 257 j (by omega) hc
    have h1 := (regValue_zero _ _).mp hs.2.2.2.2.2.1 (w j) hm
    have h2 := (regValue_zero _ _).mp ht.2.2.2.2.2.1 (w j) hm
    exact h1.trans h2.symm
  have he : j=1797 := by omega
  subst j
  exact hs.2.2.2.2.2.2.trans ht.2.2.2.2.2.2.symm

private theorem pool_write_agrees (W : Finset Wire) (s t : BasisState) (q : Wire) (v : Bool)
    (h : ∀ w∈W, s w=t w) :
    ∀ w∈W, writeBit s q v w=writeBit t q v w := by
  intro w hw
  by_cases he : w=q
  · subst w; simp [writeBit]
  · simp [writeBit,Function.update,he,h w hw]

private theorem pool_correct_agrees (cs : List Correction) (W : Finset Wire)
    (hc : correctionWires cs ⊆ W) (s t : State) (hp : s.phase=t.phase)
    (hb : ∀ w∈W, s.basis w=t.basis w) :
    (correct cs s).phase=(correct cs t).phase ∧
    ∀ w∈W, (correct cs s).basis w=(correct cs t).basis w := by
  induction cs generalizing s t with
  | nil => exact ⟨hp,hb⟩
  | cons c cs ih =>
    have ht : correctionWires cs ⊆ W := by
      intro w h
      apply hc
      cases c <;> exact Finset.mem_union_right _ h
    cases c with
    | Z q =>
      apply ih ht
      · simp only [hp,hb q (hc (by simp [correctionWires]))]
      · exact hb
    | CZ a b =>
      apply ih ht
      · simp only [hp,hb a (hc (by simp [correctionWires])),hb b (hc (by simp [correctionWires]))]
      · exact hb

theorem pool_run_agrees (p : Program) (W : Finset Wire) (hw : wires p ⊆ W)
    (m : List Bool) (s t : State) (hp : s.phase=t.phase)
    (hb : ∀ w∈W, s.basis w=t.basis w) :
    (run p m s).phase=(run p m t).phase ∧
    ∀ w∈W, (run p m s).basis w=(run p m t).basis w := by
  induction p generalizing m s t with
  | nil => simpa only [run] using (And.intro hp hb)
  | cons c p ih =>
    have ht : wires p ⊆ W := fun _ h => hw (Finset.mem_union_right _ h)
    have hi : c.wires ⊆ W := fun _ h => hw (Finset.mem_union_left _ h)
    cases c with
    | X q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires]))]
        exact pool_write_agrees W s.basis t.basis q _ hb
    | CX a q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires])),hb a (hi (by simp [Instr.wires]))]
        exact pool_write_agrees W s.basis t.basis q _ hb
    | CCX a b q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires])),hb a (hi (by simp [Instr.wires])),
          hb b (hi (by simp [Instr.wires]))]
        exact pool_write_agrees W s.basis t.basis q _ hb
    | measureX q c0 c1 =>
      simp only [run]
      have hc : correctionWires (if m.headD false then c1 else c0) ⊆ W := by
        split <;> intro w hw <;> apply hi <;> simp_all [Instr.wires]
      have he := pool_correct_agrees _ W hc
        ⟨s.phase ^^ (m.headD false && s.basis q),writeBit s.basis q false⟩
        ⟨t.phase ^^ (m.headD false && t.basis q),writeBit t.basis q false⟩
        (by simp only [hp,hb q (hi (by simp [Instr.wires]))])
        (pool_write_agrees W s.basis t.basis q false hb)
      exact ih ht _ _ _ he.1 he.2

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RetainedThreshold.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ECDSAAdd.Arithmetic
open Instr

/-- Exact addition with every low carry retained. The top bit needs no carry:
its omitted overflow is precisely the fixed-width modular wrap. -/
def retainedAddStart : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
    majority a b cin c ++ (retainedAddStart (a'::as) (b'::bs) cs c ++ [CX a b,CX cin b])
  | [a], [b], _, cin => [CX a b,CX cin b]
  | _, _, _, _ => []

/-- Unsum low-to-high before erasing any retained carry, then erase high-to-low.
Both full original operands are restored before the first carry measurement. -/
def retainedAddFinish : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
    [CX cin b,CX a b] ++ (retainedAddFinish (a'::as) (b'::bs) cs c ++ eraseCarry a b cin c)
  | [a], [b], _, cin => [CX cin b,CX a b]
  | _, _, _, _ => []

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedRetainedThreshold.lean
noncomputable section

/-! Exact retained-carry threshold alternative. The accepted canonical endpoint
remains unchanged; this alternative must pass full composition before use. -/
namespace ECDSAAdd.Arithmetic

/-- Load a selected constant, retain the full addition carry frame, and borrow
its unloaded constant word as the full comparison carry. Both original operands
return before any retained carry is measured. -/
def fusedRetainedThresholdCore (load : Program) (R A C retained : List Wire)
    (cin h : Wire) : Program :=
  load ++ retainedAddStart C A retained cin ++ load ++
    compareLt none R A C cin h ++ load ++ retainedAddFinish C A retained cin ++ load

/-- Actual selected-threshold stream, with old reduction-bit convention unchanged. -/
def fusedRetainedThresholdRecover (b q t d h : Wire) (R A C retained : List Wire)
    (cin : Wire) (K P : Nat) : Program :=
  fusedRetainedThresholdCore (fusedThresholdWordLoad b q t d C K P) R A C retained cin h ++ [.CX b h]

/-- Complete paid cleanup after flag transfer into target guards. All word
views here have n bits; the guard flags and constant selectors are outside them. -/
def fusedSignedHalfRetainedBack (b cin q h t d e : Wire) (sourceHalf R A C carry : List Wire) : Program :=
  let ac := carry.take (R.length-1)
  fusedThresholdFlagsSeed b q e t d ++ fusedThresholdPrepare b sourceHalf A ++
    fusedRetainedThresholdRecover b q t d h R A C ac cin (FusedSignedHalf.halfThreshold p) (p+1) ++
    fusedThresholdUnprepare b sourceHalf A ++ fusedThresholdFlagsErase b q e t d ++
    fusedHalfParityClear R C carry cin q


namespace FusedHalfPorts

end FusedHalfPorts

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/FusedSignedHalfInverse.lean
noncomputable section

namespace ECDSAAdd.FusedSignedHalf
open Secp256k1

end ECDSAAdd.FusedSignedHalf
end

-- source: ECDSAAdd/Arithmetic/FusedInverseSeed.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedInverseFlags.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] run fusedRetainedThresholdRecover

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedInverseCorrection.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedInverseFront.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic

/-- The inverse front must reconstruct the signed-guard AND explicitly:
its old input-side guard no longer exists in the canonical output. -/
def fusedInverseCorrectionFlagsSeed (b a h j l m : Wire) : Program :=
  [.CCX b h j,.CCX a h l,.CCX a j m]

attribute [local irreducible] run signedSub

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactGuardFront.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace ECDSAAdd.Arithmetic

/-- One raw guard is sufficient with explicit signed-guard AND reconstruction. -/
def compactSignedHalfFront (b cin low a h j l m : Wire) (Y R C carry : List Wire)
    (P : Nat) : Program :=
  let ac := carry.take (R.length-1)
  fusedRawNormalize b h Y R C ac carry cin P ++ [.CX low a] ++
    fusedInverseCorrectionFlagsSeed b a h j l m ++ fusedEvenHalf b a h j l m C R ac cin P

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedInversePacked.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace FusedHalfPorts

end FusedHalfPorts

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactGuardPorts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

/-- One overflow guard, with the second target/constant guards retained as
separate late flag ports. The public payload still has all 256 field bits. -/
def compactSource (L : FusedHalfPorts) := (L.e::L.yTail)++[L.yg0]
def compactTarget (L : FusedHalfPorts) := L.targetLow++[L.qOut]
def compactConstant (L : FusedHalfPorts) := L.C++[L.t]
def compactCarry (L : FusedHalfPorts) := L.carry.take (L.A.length+1)

def compactForwardProgram (L : FusedHalfPorts) : Program :=
  compactSignedHalfFront L.b L.cin L.low L.a L.h L.j L.l L.m
    L.compactSource L.compactTarget L.compactConstant L.compactCarry p ++
    fusedFlagsMove L.a L.h L.qOut L.hOut ++
    fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e
      L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)

end FusedHalfPorts

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactGuardLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

end FusedHalfPorts
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactGuardPackedInverse.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

attribute [local irreducible] run

end FusedHalfPorts
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedInverse.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedFieldInverseBridge.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactGuardPackedForward.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

attribute [local irreducible] run compactSignedHalfFront

end FusedHalfPorts
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedRetained.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedRetainedCell.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

def fusedSharedRetainedSignedHalf (w : Nat → Wire) (g : Wire) : Program :=
  fusedFieldSignedHalf g (fusedSharedPorts w g).compactForwardProgram

def fusedSharedRetainedCell (w : Nat → Wire) (g swap : Wire) : Program :=
  fusedSharedRetainedSignedHalf w g ++
  swapRegisters swap ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkDialog.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Physical record pairs are (parity g, swap s), and are read without modification. -/
def skywalkTapeControls (base : BasisState) (rs : List (Wire × Wire)) : List (Bool × Bool) :=
  rs.map (fun r => (base r.1,base r.2))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedRetainedReplay.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedInverseCell.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedInverseReplay.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedRetainedDivision.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedInverseMultiplication.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedHalfSupportCommon.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic

namespace FusedHalfPorts

end FusedHalfPorts

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactGuardSupport.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

end FusedHalfPorts
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedRetainedSupport.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic



attribute [local irreducible] wireBlock swapRegisters dblInPlace copyRegister
attribute [local irreducible] fusedSharedRetainedCell

private theorem retained_block_subset_shared (w : Nat → Wire) (s n : Nat)
    (hb : s+n≤2314) : wireBlock w s n ⊆ skywalkSharedWires w := by
  intro q hq
  rw [wireBlock] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  rw [skywalkSharedWires,wireBlock]
  apply List.mem_map.mpr
  have hi' := List.mem_range'_1.mp hi
  exact ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem retained_field_subset_shared (w : Nat → Wire) :
    (skywalkSharedField w).wires⊆skywalkSharedWires w := by
  intro q hq
  unfold ModInPlaceLayout.wires at hq
  rw [skywalkShared_field_z] at hq
  change q∈wireBlock w 770 257++wireBlock w 2056 257++
    (wireBlock w 1540 257++wireBlock w 1798 256++[w 1797]++
      wireBlock w 512 257++[w 2313]) at hq
  simp only [List.mem_append,List.mem_singleton,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq
  · exact retained_block_subset_shared w 770 257 (by omega) hq
  · exact retained_block_subset_shared w 2056 257 (by omega) hq
  · exact retained_block_subset_shared w 1540 257 (by omega) hq
  · exact retained_block_subset_shared w 1798 256 (by omega) hq
  · subst q
    exact retained_block_subset_shared w 1797 1 (by omega) (by simp [wireBlock])
  · exact retained_block_subset_shared w 512 257 (by omega) hq
  · subst q
    exact retained_block_subset_shared w 2313 1 (by omega) (by simp [wireBlock])

theorem retained_tape_subset_shared (w : Nat → Wire) :
    ∀ r∈skywalkSharedTape w,r.1∈skywalkSharedWires w ∧
      r.2∈skywalkSharedWires w := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  have hib : i<512 := List.mem_range.mp hi
  constructor
  · exact retained_block_subset_shared w i 1 (by omega) (by simp [wireBlock])
  · exact retained_block_subset_shared w (1028+i) 1 (by omega) (by simp [wireBlock])

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FusedSharedInverseSupport.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

attribute [local irreducible] fusedThresholdFlagsSeed fusedThresholdPrepare
attribute [local irreducible] fusedRetainedThresholdRecover fusedThresholdUnprepare
attribute [local irreducible] fusedThresholdFlagsErase fusedHalfParityClear swapBits

end FusedHalfPorts

attribute [local irreducible] wireBlock swapRegisters copyRegister halfInPlace

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NarrowSignedRecord.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- A full word with an explicit retained MSB and discarded sign-padding tail.
The executable streams below still use take/drop of the full words. -/
structure NarrowSignedRecordLayout where
  xlo : List Wire
  ylo : List Wire
  sx : Wire
  sy : Wire
  q : Wire
  xhigh : List Wire
  yhigh : List Wire
  carryLow : List Wire
  carryHigh : List Wire

namespace NarrowSignedRecordLayout

def xp (L : NarrowSignedRecordLayout) := L.xlo++[L.sx]
def yp (L : NarrowSignedRecordLayout) := L.ylo++[L.sy]
def x (L : NarrowSignedRecordLayout) := L.xp++L.xhigh
def y (L : NarrowSignedRecordLayout) := L.yp++L.yhigh
def carry (L : NarrowSignedRecordLayout) := L.carryLow++L.carryHigh
def wires (L : NarrowSignedRecordLayout) := L.q::(L.x++L.y++L.carry)

structure Widths (L : NarrowSignedRecordLayout) (n : Nat) : Prop where
  x : L.xp.length=n
  y : L.yp.length=n
  carry : L.carryLow.length+1=n

theorem views (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) :
    L.x.take n=L.xp ∧ L.y.take n=L.yp ∧
    L.carry.take (n-1)=L.carryLow ∧ L.y.drop n=L.yhigh := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [←hw.x,x,List.take_left]
  · rw [←hw.y,y,List.take_left]
  · rw [←hw.carry,Nat.add_sub_cancel,carry,List.take_left]
  · rw [←hw.y,y,List.drop_left]

theorem short_nodup (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup) :
    (L.q::(L.xp++L.yp++L.carryLow)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro a
  have h := List.nodup_iff_count.mp hn a
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h ⊢
  omega

theorem high_nodup (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup) : L.yhigh.Nodup := by
  apply List.nodup_iff_count.mpr
  intro a
  have h := List.nodup_iff_count.mp hn a
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h
  omega

theorem q_high (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup) : L.q∉L.yhigh := by
  intro hm
  have h := List.nodup_iff_count.mp hn L.q
  have hp := List.count_pos_iff.mpr hm
  simp only [wires,x,y,carry,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
  omega

theorem rest_away_short (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.xhigh++L.yhigh++L.carryHigh) :
    a∉L.q::(L.xp++L.yp++L.carryLow) := by
  intro hm
  have h := List.nodup_iff_count.mp hn a
  have hp := List.count_pos_iff.mpr ha
  have hs := List.count_pos_iff.mpr hm
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h hs hp
  omega

theorem other_away_high (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.x++L.yp++L.carry) : a∉L.yhigh := by
  intro hm
  have h := List.nodup_iff_count.mp hn a
  have hp := List.count_pos_iff.mpr ha
  have hs := List.count_pos_iff.mpr hm
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h hp
  omega

end NarrowSignedRecordLayout

/-- Prefix arithmetic followed by Clifford extension of the retained sign flip. -/
def narrowSignedRecord (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  signedRecord L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

/-- A new forward inverse stream, with its own measurement list. -/
def narrowSignedUnrecord (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  signComplement L.q (L.y.drop n) ++
    signedUnrecord L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1))

attribute [local irreducible] signedRecord signedUnrecord run

private theorem narrow_fanout_run (q : Wire) (r : List Wire) (hq : q∉r)
    (s : State) (m : List Bool) :
    run (signComplement q r) m s=if s.basis q then run (notRegister r) m s else s := by
  induction r generalizing s with
  | nil => cases s.basis q <;> simp [signComplement,run,notRegister]
  | cons a r ih =>
    have hqa : q≠a := fun h => hq (by simp [h])
    have hqr : q∉r := fun h => hq (List.mem_cons_of_mem _ h)
    simp only [signComplement,List.map_cons,run]
    change run (signComplement q r) m
      ⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis q)⟩=_
    rw [ih hqr]
    cases hs : s.basis q <;> simp [hs,writeBit,hqa,notRegister,run]

/-- Literal bit-level fanout, including its live control, outside frame and phase. -/
theorem narrow_fanout_correct (q : Wire) (r : List Wire) (hn : r.Nodup) (hq : q∉r)
    (s : State) (m : List Bool) :
    run (signComplement q r) m s=
      ⟨s.phase,fun a => if a∈r then s.basis a ^^ s.basis q else s.basis a⟩ := by
  rw [narrow_fanout_run q r hq]
  cases hs : s.basis q
  · apply congrArg (State.mk s.phase)
    funext a
    simp
  · rw [notRegister_correct r hn]
    simp

/-- Fanout reversal is Clifford and independent of both record lists. -/
theorem narrow_fanout_twice (q : Wire) (r : List Wire) (hn : r.Nodup) (hq : q∉r)
    (s : State) (m1 m2 : List Bool) :
    run (signComplement q r) m2 (run (signComplement q r) m1 s)=s := by
  rw [narrow_fanout_correct q r hn hq,narrow_fanout_correct q r hn hq]
  apply congrArg (State.mk s.phase)
  funext a
  by_cases ha : a∈r
  · simp only [ha,if_true,hq,if_false]
    cases s.basis a <;> cases s.basis q <;> rfl
  · simp [ha]

/-- Signed value of an appended nonempty high word. -/
theorem narrow_signed_append (lo hi : List Wire) (s : BasisState) (hh : hi≠[]) :
    signedRegValue (lo++hi) s=(regValue lo s:Int)+
      ((2^lo.length:Nat):Int)*signedRegValue hi s := by
  induction lo with
  | nil => simp [regValue]
  | cons a lo ih =>
    have ht : lo++hi≠[] := by simp [hh]
    rw [List.cons_append,signedRegValue_cons a (lo++hi) s ht,ih]
    cases ha : s a <;>
      simp [regValue,ha,List.length_cons,pow_succ,Nat.cast_add,Nat.cast_mul] <;> ring

private theorem narrow_false_value (r : List Wire) : signedRegValue r (fun _ => false)=0 := by
  have hz : regValue r (fun _ => false)=0 := (regValue_zero _ _).mpr (fun _ _ => rfl)
  unfold signedRegValue signedDecode
  rw [hz,if_pos (by positivity)]
  rfl

private theorem narrow_true_value (r : List Wire) (hr : r≠[]) :
    signedRegValue r (fun _ => true)= -1 := by
  induction r with
  | nil => contradiction
  | cons a r ih =>
    cases r with
    | nil => norm_num [signedRegValue,signedDecode,regValue]
    | cons b r =>
      rw [signedRegValue_cons a (b::r) _ (by simp),ih (by simp)]
      norm_num

/-- Exact prefix read and every discarded high bit, for a value that fits the
retained signed interval. The positive endpoint is deliberately strict. -/
theorem narrow_signed_prefix (lo hi : List Wire) (s : BasisState) (A : Int)
    (hn : 0 < lo.length) (hv : signedRegValue (lo++hi) s=A)
    (ha0 : -((2^(lo.length-1):Nat):Int) ≤ A)
    (ha1 : A < ((2^(lo.length-1):Nat):Int)) :
    signedRegValue lo s=A ∧ ∀ a∈hi,s a=SkywalkRails.neg A := by
  by_cases he : hi=[]
  · subst hi
    simp only [List.append_nil] at hv
    exact ⟨hv,by simp⟩
  let R : Int := regValue lo s
  let M : Int := (2^lo.length:Nat)
  let H : Int := (2^(lo.length-1):Nat)
  let T := signedRegValue hi s
  have hm : M=2*H := by
    have hp : 2^lo.length=2^(lo.length-1)*2 := by
      calc
        2^lo.length = 2^((lo.length-1)+1) := by congr 1; omega
        _ = 2^(lo.length-1)*2 := pow_succ _ _
    change ((2^lo.length:Nat):Int)=2*((2^(lo.length-1):Nat):Int)
    rw [hp,Nat.cast_mul]
    ring
  have hH : 0 < H := by dsimp [H]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < M := Int.ofNat_lt.mpr (regValue_lt lo s)
  have hA0 : -H ≤ A := ha0
  have hA1 : A < H := ha1
  have hs := narrow_signed_append lo hi s he
  rw [hv] at hs
  change A=R+M*T at hs
  have hT0 : T ≤ 0 := by
    by_contra hnot
    have hp : 1 ≤ T := by omega
    nlinarith
  have hT1 : -1 ≤ T := by
    by_contra hnot
    have hp : T ≤ -2 := by omega
    nlinarith
  have hcases : T=0 ∨ T= -1 := by omega
  rcases hcases with ht|ht
  · have hA : A=R := by rw [ht] at hs; omega
    have hraw : regValue lo s < 2^(lo.length-1) := by
      have hh : (regValue lo s:Int) < ((2^(lo.length-1):Nat):Int) := by change R < H; omega
      exact_mod_cast hh
    have hsg : SkywalkRails.neg A=false := by simp [SkywalkRails.neg]; omega
    refine ⟨?_,?_⟩
    · unfold signedRegValue signedDecode
      rw [if_pos hraw]
      exact hA.symm
    · have ht' : signedRegValue hi s=signedRegValue hi (fun _ => false) := by
        rw [narrow_false_value]
        exact ht
      intro a ha
      rw [hsg]
      exact (signedRegValue_eq_iff hi _ _).mp ht' a ha
  · have hA : A=R-M := by rw [ht] at hs; nlinarith
    have hraw : ¬regValue lo s < 2^(lo.length-1) := by
      have hh : ¬(regValue lo s:Int) < ((2^(lo.length-1):Nat):Int) := by change ¬R < H; omega
      exact_mod_cast hh
    have hsg : SkywalkRails.neg A=true := by simp [SkywalkRails.neg]; omega
    refine ⟨?_,?_⟩
    · unfold signedRegValue signedDecode
      rw [if_neg hraw]
      exact hA.symm
    · have ht' : signedRegValue hi s=signedRegValue hi (fun _ => true) := by
        rw [narrow_true_value hi he]
        exact ht
      intro a ha
      rw [hsg]
      exact (signedRegValue_eq_iff hi _ _).mp ht' a ha

/-- Uniform high sign padding preserves the signed value of the prefix. -/
theorem narrow_signed_extend (lo hi : List Wire) (s : BasisState) (A : Int)
    (hn : 0 < lo.length) (hv : signedRegValue lo s=A)
    (hh : ∀ a∈hi,s a=SkywalkRails.neg A) : signedRegValue (lo++hi) s=A := by
  by_cases he : hi=[]
  · subst hi; simpa using hv
  have hp := signedDecode_range lo.length (regValue lo s) hn (regValue_lt lo s)
  change -((2^(lo.length-1):Nat):Int) ≤ signedRegValue lo s ∧
    signedRegValue lo s < ((2^(lo.length-1):Nat):Int) at hp
  have ha := narrow_signed_append lo hi s he
  by_cases hs : A < 0
  · have hb : signedRegValue hi s= -1 := by
      apply Eq.trans ((signedRegValue_eq_iff hi s (fun _ => true)).mpr ?_)
        (narrow_true_value hi he)
      intro a hmem
      rw [hh a hmem]
      simp [SkywalkRails.neg,hs]
    have hsig : ¬regValue lo s < 2^(lo.length-1) := by
      intro ht
      have hv' := hv
      unfold signedRegValue signedDecode at hv'
      rw [if_pos ht] at hv'
      omega
    rw [hb] at ha
    unfold signedRegValue signedDecode at hv
    rw [if_neg hsig] at hv
    nlinarith
  · have hb : signedRegValue hi s=0 := by
      apply Eq.trans ((signedRegValue_eq_iff hi s (fun _ => false)).mpr ?_)
        (narrow_false_value hi)
      intro a hmem
      rw [hh a hmem]
      simp [SkywalkRails.neg,hs]
    have hsig : regValue lo s < 2^(lo.length-1) := by
      by_contra ht
      have hv' := hv
      unfold signedRegValue signedDecode at hv'
      rw [if_neg ht] at hv'
      have hraw := regValue_lt lo s
      omega
    rw [hb] at ha
    unfold signedRegValue signedDecode at hv
    rw [if_pos hsig] at hv
    nlinarith

private theorem narrow_short_full (L : NarrowSignedRecordLayout) (A B : Int) (T : Bool)
    (s : BasisState) (h : SignedRecordValues L.q L.xp L.yp L.carryLow A B T s)
    (hx : ∀ a∈L.xhigh,s a=SkywalkRails.neg A)
    (hy : ∀ a∈L.yhigh,s a=SkywalkRails.neg B) (hc : regValue L.carryHigh s=0) :
    SignedRecordValues L.q L.x L.y L.carry A B T s := by
  refine ⟨h.1,?_,?_,?_⟩
  · exact narrow_signed_extend L.xp L.xhigh s A (by simp [NarrowSignedRecordLayout.xp]) h.2.1 hx
  · exact narrow_signed_extend L.yp L.yhigh s B (by simp [NarrowSignedRecordLayout.yp]) h.2.2.1 hy
  · simp only [NarrowSignedRecordLayout.carry,regValue_append,h.2.2.2,hc,Nat.mul_zero,Nat.add_zero]

private theorem narrow_full_to_short (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n)
    (A B : Int) (T : Bool) (s : BasisState)
    (h : SignedRecordValues L.q L.x L.y L.carry A B T s)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int)) :
    SignedRecordValues L.q L.xp L.yp L.carryLow A B T s ∧
      (∀ a∈L.xhigh,s a=SkywalkRails.neg A) ∧
      (∀ a∈L.yhigh,s a=SkywalkRails.neg B) ∧ regValue L.carryHigh s=0 := by
  have hx := narrow_signed_prefix L.xp L.xhigh s A (by simp [NarrowSignedRecordLayout.xp])
    h.2.1 (by rw [hw.x]; exact ha0) (by rw [hw.x]; exact ha1)
  have hy := narrow_signed_prefix L.yp L.yhigh s B (by simp [NarrowSignedRecordLayout.yp])
    h.2.2.1 (by rw [hw.y]; exact hb0) (by rw [hw.y]; exact hb1)
  have hcl : regValue L.carryLow s=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    exact (regValue_zero _ _).mp h.2.2.2 a (List.mem_append_left _ ha)
  have hch : regValue L.carryHigh s=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    exact (regValue_zero _ _).mp h.2.2.2 a (List.mem_append_right _ ha)
  exact ⟨⟨h.1,hx.1,hy.1,hcl⟩,hx.2,hy.2,hch⟩

/-- Full-value semantics: both original inputs fit the retained signed interval;
all discarded bits are repaired to the new sign, not assumed zero. -/
theorem narrowSignedRecord_spec (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) (A B : Int)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int)) :
    Triple (SignedRecordValues L.q L.x L.y L.carry A B false) (narrowSignedRecord L n)
      (SignedRecordValues L.q L.x L.y L.carry A (signedRecordValue A B)
        (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B))) := by
  intro s m hin
  let R := signedRecordValue A B
  let T := SkywalkRails.neg B ^^ SkywalkRails.neg R
  have hv := L.views n hw
  simp only [narrowSignedRecord,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2]
  rw [run_append]
  generalize hr : run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow)
    (m.take (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow))) s=mid
  generalize hf : run (signComplement L.q L.yhigh)
    (m.drop (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow))) mid=out
  have hi := narrow_full_to_short L n hw A B false s.basis hin ha0 ha1 hb0 hb1
  have hh := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm) A B s
    (m.take (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow))) hi.1
  change (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) _ s).phase=s.phase ∧
    SignedRecordValues L.q L.xp L.yp L.carryLow A R T
      (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) _ s).basis at hh
  rw [hr] at hh
  have hfan := narrow_fanout_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) mid
    (m.drop (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow)))
  rw [hf] at hfan
  have fanbit (a : Wire) : out.basis a=(if a∈L.yhigh then mid.basis a ^^ mid.basis L.q else mid.basis a) :=
    congrArg (fun t : State => t.basis a) hfan
  have keep (a : Wire) (ha : a∈L.x++L.yp++L.carry) : out.basis a=mid.basis a := by
    rw [fanbit,if_neg (L.other_away_high hn a ha)]
  have keepRead (r : List Wire) (hsub : r⊆L.x++L.yp++L.carry) :
      regValue r out.basis=regValue r mid.basis :=
    regValue_congr _ _ _ (fun a ha => keep a (hsub ha))
  have keepSigned (r : List Wire) (hsub : r⊆L.x++L.yp++L.carry) :
      signedRegValue r out.basis=signedRegValue r mid.basis := by
    unfold signedRegValue
    rw [keepRead r hsub]
  have tailOld (a : Wire) (ha : a∈L.xhigh++L.yhigh++L.carryHigh) : mid.basis a=s.basis a := by
    have hb := (signedRecord_frame L.xlo L.ylo L.sx L.sy L.q L.carryLow
      (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm) s
      (m.take (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow))) a
      (L.rest_away_short hn a ha)).1
    change (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) _ s).basis a=s.basis a at hb
    rw [hr] at hb
    exact hb
  have hqOut : out.basis L.q=T := by
    rw [fanbit,if_neg (L.q_high hn)]
    exact hh.2.1
  have hxOut : signedRegValue L.xp out.basis=A := by
    rw [keepSigned L.xp (by intro a ha; simp [NarrowSignedRecordLayout.x,ha])]
    exact hh.2.2.1
  have hyOut : signedRegValue L.yp out.basis=R := by
    rw [keepSigned L.yp (by intro a ha; simp [ha])]
    exact hh.2.2.2.1
  have hcOut : regValue L.carryLow out.basis=0 := by
    rw [keepRead L.carryLow (by intro a ha; simp [NarrowSignedRecordLayout.carry,ha])]
    exact hh.2.2.2.2
  refine ⟨(congrArg State.phase hfan).trans hh.1,narrow_short_full L A R T out.basis
    ⟨hqOut,hxOut,hyOut,hcOut⟩ ?_ ?_ ?_⟩
  · intro a ha
    rw [keep a (by simp [NarrowSignedRecordLayout.x,ha]),tailOld a (by simp [ha])]
    exact hi.2.1 a ha
  · intro a ha
    rw [fanbit,if_pos ha,hh.2.1,tailOld a (by simp [ha]),hi.2.2.1 a ha]
    dsimp only [T]
    cases SkywalkRails.neg B <;> cases SkywalkRails.neg R <;> rfl
  · apply Eq.trans (keepRead L.carryHigh (by intro a ha; simp [NarrowSignedRecordLayout.carry,ha]))
    apply Eq.trans (regValue_congr _ _ _ (fun a ha => tailOld a (by simp [ha]))) hi.2.2.2

/-- Actual gate counts: discarded high-bit repair uses only CX. -/
theorem narrowSignedRecord_counts (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) :
    toffoliCount (narrowSignedRecord L n)=n-1 ∧ measurementCount (narrowSignedRecord L n)=n-1 ∧
    toffoliCount (narrowSignedUnrecord L n)=n-1 ∧ measurementCount (narrowSignedUnrecord L n)=n-1 := by
  have h := L.views n hw
  have hs := signedRecord_counts L.sx L.sy L.q L.xp L.yp L.carryLow
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  have hf := signComplement_counts L.q L.yhigh
  simp only [narrowSignedRecord,narrowSignedUnrecord,h.1,h.2.1,h.2.2.1,h.2.2.2,
    toffoliCount_append,measurementCount_append,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hf.1,hf.2,hw.y,
    Nat.add_zero,Nat.zero_add]
  simp

/-- Complete actual support, including every repaired high target bit. -/
theorem narrowSignedRecord_support (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) :
    wires (narrowSignedRecord L n)⊆L.wires.toFinset ∧
    wires (narrowSignedUnrecord L n)⊆L.wires.toFinset := by
  have hv := L.views n hw
  have hs := signedRecord_wires L.xlo L.ylo L.sx L.sy L.q L.carryLow
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  change wires (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow)=
      (L.q::(L.xp++L.yp++L.carryLow)).toFinset ∧
    wires (signedUnrecord L.sx L.sy L.q L.xp L.yp L.carryLow)=
      (L.q::(L.xp++L.yp++L.carryLow)).toFinset at hs
  have hf := signComplement_wires_subset L.q L.yhigh
  have small : (L.q::(L.xp++L.yp++L.carryLow)).toFinset⊆L.wires.toFinset := by
    intro a ha
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,NarrowSignedRecordLayout.wires,
      NarrowSignedRecordLayout.x,NarrowSignedRecordLayout.y,NarrowSignedRecordLayout.carry] at ha ⊢
    tauto
  have high : (L.q::L.yhigh).toFinset⊆L.wires.toFinset := by
    intro a ha
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,NarrowSignedRecordLayout.wires,
      NarrowSignedRecordLayout.x,NarrowSignedRecordLayout.y,NarrowSignedRecordLayout.carry] at ha ⊢
    tauto
  simp only [narrowSignedRecord,narrowSignedUnrecord,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2,
    wires_append,Finset.union_subset_iff,hs.1,hs.2]
  exact ⟨⟨small,hf.trans high⟩,⟨hf.trans high,small⟩⟩

/-- Previous orientation and every external control/caller site frame in both
forward and independently measured inverse streams. -/
theorem narrowSignedRecord_frame (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n)
    (s : State) (m : List Bool) (a : Wire) (ha : a∉L.wires) :
    (run (narrowSignedRecord L n) m s).basis a=s.basis a ∧
    (run (narrowSignedUnrecord L n) m s).basis a=s.basis a := by
  have hp := narrowSignedRecord_support L n hw
  constructor
  · exact run_preserves_outside _ m s a (fun h => ha (List.mem_toFinset.mp (hp.1 h)))
  · exact run_preserves_outside _ m s a (fun h => ha (List.mem_toFinset.mp (hp.2 h)))

/-- Strong full-State inverse, without reversing any measurement instruction.
The two record lists are independent. The signed fit assumptions needed for
full-value lifting are unnecessary for this stronger bit-level roundtrip. -/
theorem narrowSignedRecord_roundtrip (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) (s : State) (m1 m2 : List Bool)
    (hq : s.basis L.q=false) (hc : regValue L.carry s.basis=0) :
    run (narrowSignedUnrecord L n) m2 (run (narrowSignedRecord L n) m1 s)=s := by
  have hv := L.views n hw
  have hcarry : regValue L.carryLow s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    exact (regValue_zero _ _).mp hc a (List.mem_append_left _ ha)
  have hm := signComplement_counts L.q L.yhigh
  simp only [narrowSignedRecord,narrowSignedUnrecord,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2]
  rw [run_append,run_append,hm.2]
  simp only [List.take_zero,List.drop_zero]
  rw [narrow_fanout_twice L.q L.yhigh (L.high_nodup hn) (L.q_high hn)]
  exact signedRecord_roundtrip L.xlo L.ylo L.sx L.sy L.q L.carryLow
    (L.short_nodup hn) (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm) s _ m2 hq hcarry

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/SkywalkSumWidth.lean
noncomputable section

namespace ECDSAAdd.SkywalkNat

/-- The product controls the sum on the complete coprime trajectory, including
terminal(0,1). The terminal case cannot be inferred from positivity alone. -/
theorem coprime_sum_le_product_succ (z : State) (hv : 0 < z.v) (hg : z.u.gcd z.v=1) :
    z.u+z.v ≤ z.u*z.v+1 := by
  by_cases hu : z.u=0
  · rw [hu,Nat.gcd_zero_left] at hg
    rw [hu,hg]
  · have hu0 : 0 < z.u := Nat.pos_of_ne_zero hu
    have hp : 1 ≤ (z.u-1)*(z.v-1)+1 := by omega
    have he : z.u*z.v+1=z.u+z.v+(z.u-1)*(z.v-1) := by
      have hu' : z.u=(z.u-1)+1 := by omega
      have hv' : z.v=(z.v-1)+1 := by omega
      nth_rw 1 [hu',hv']
      ring_nf
      omega
    omega

/-- Inclusive sum envelope from the exact product bound. No sampled width
profile or early-termination schedule is used. -/
theorem iter_sum_product_width (p x n i : Nat) (hp0 : 0 < p) (hx0 : 0 < x)
    (hpo : p%2=1) (hp : p < 2^n) (hx : x < p) (hc : x.Coprime p)
    (hi : i ≤ 2*n) :
    let z := step^[i] (init x p)
    z.u+z.v ≤ 2^(2*n-i) := by
  let z := step^[i] (init x p)
  have hvalid := iter_valid i (init x p) hp0 hpo
  have hg : z.u.gcd z.v=1 := hvalid.2.2.trans hc
  have hsum := coprime_sum_le_product_succ z hvalid.1 hg
  have hb := iter_product_bound i (init x p)
  change 2^i*(z.u*z.v) ≤ x*p at hb
  have hxp : x*p < 2^(2*n) := by
    rw [two_mul,pow_add]
    calc
      x*p < x*2^n := Nat.mul_lt_mul_of_pos_left hp hx0
      _ < 2^n*2^n := Nat.mul_lt_mul_of_pos_right (hx.trans hp) (by positivity)
  have he : 2^(2*n)=2^i*2^(2*n-i) := by
    rw [←pow_add]
    congr 1
    omega
  rw [he] at hxp
  have hprod : z.u*z.v < 2^(2*n-i) := by
    by_contra hnot
    have hm := Nat.mul_le_mul_left (2^i) (Nat.le_of_not_gt hnot)
    omega
  change z.u+z.v ≤ 2^(2*n-i)
  omega

/-- Initial common cap from monotone sum, independent of the product cap. -/
theorem iter_sum_initial_width (p x n i : Nat) (hp : p < 2^n) (hx : x < p) :
    let z := step^[i] (init x p)
    z.u+z.v < 2^(n+1) := by
  have hsum := iter_sum_nonincrease i (init x p)
  change (step^[i] (init x p)).u+(step^[i] (init x p)).v ≤ x+p at hsum
  have hx' : x < 2^n := hx.trans hp
  dsimp only
  rw [pow_succ]
  omega

end ECDSAAdd.SkywalkNat

namespace ECDSAAdd.SkywalkRails

private theorem sumwidth_signed_abs (s : Bool) (u : Nat) : |signed s (u:Int)|=(u:Int) := by
  cases s with
  | false => exact Int.abs_natCast u
  | true =>
    change |-(u:Int)|=(u:Int)
    rw [abs_neg]
    exact Int.abs_natCast u

/-- Whole input rails have an inclusive envelope. Equality at the positive
upper endpoint must not be mistaken for a narrower signed decoding theorem. -/
theorem encode_abs_sum_bound (g s : Bool) (u v B : Nat) (hs : u+v ≤ B) :
    |(encode g s (u:Int) (v:Int)).a| ≤ (B:Int) ∧
    |(encode g s (u:Int) (v:Int)).b| ≤ (B:Int) := by
  have hu : (u:Int) ≤ B := by omega
  have hlarge : |(u:Int)+(v:Int)| ≤ (B:Int) := by
    rw [abs_of_nonneg (show 0 ≤ (u:Int)+(v:Int) by omega)]
    omega
  have hsmall : |signed s (u:Int)| ≤ (B:Int) := by
    rw [sumwidth_signed_abs]
    exact hu
  cases g
  · exact ⟨hlarge,hsmall⟩
  · exact ⟨hsmall,hlarge⟩

private theorem even_power (k : Nat) (hk : 0 < k) :
    ((2^k:Nat):Int)=2*((2^(k-1):Nat):Int) := by
  have he : (2^k:Nat)=2^(k-1)*2 := by
    calc
      2^k = 2^((k-1)+1) := by congr 1; omega
      _ = 2^(k-1)*2 := pow_succ 2 (k-1)
  rw [he,Nat.cast_mul]
  ring

/-- An odd rail cannot attain an even power-of-two endpoint. -/
private theorem odd_abs_strict (o : Int) (k : Nat) (hk : 0 < k)
    (ho : o%2=1) (hb : |o| ≤ ((2^k:Nat):Int)) : |o| < ((2^k:Nat):Int) := by
  have he := even_power k hk
  have hm : ((2^k:Nat):Int)%2=0 := by omega
  by_contra hnot
  have hx : |o|=((2^k:Nat):Int) := le_antisymm hb (le_of_not_gt hnot)
  by_cases hz : 0 ≤ o
  · rw [abs_of_nonneg hz] at hx
    omega
  · rw [abs_of_neg (by omega)] at hx
    omega

/-- The routed arithmetic operands allow one fewer sign-padding bit than a
naive sum-of-individual-widths bound: oddO is strictly below2^k, while evenE
is below2^k after halving. Keep the original full sign for the half operation.
This theorem does not change any circuit or the complete512-round schedule. -/
theorem route_half_width (a b : Int) (k : Nat) (hk : 0 < k)
    (hp : (a+b)%2=1) (ha : |a| ≤ ((2^k:Nat):Int)) (hb : |b| ≤ ((2^k:Nat):Int)) :
    |(route a b).2| < ((2^k:Nat):Int) ∧
    |(route a b).1/2| ≤ ((2^(k-1):Nat):Int) := by
  have hroute : |(route a b).1| ≤ ((2^k:Nat):Int) ∧
      |(route a b).2| ≤ ((2^k:Nat):Int) ∧ (route a b).2%2=1 := by
    by_cases he : a%2=0
    · have ho : odd a=false := by simp [odd,he]
      rw [route,ho]
      refine ⟨ha,hb,?_⟩
      change b%2=1
      omega
    · have ho : odd a=true := by simp [odd,he]
      rw [route,ho]
      refine ⟨hb,ha,?_⟩
      change a%2=1
      omega
  refine ⟨odd_abs_strict _ k hk hroute.2.2 hroute.2.1,?_⟩
  have he := even_power k hk
  have hr := abs_le.mp hroute.1
  apply abs_le.mpr
  omega

end ECDSAAdd.SkywalkRails
end

-- source: ECDSAAdd/Arithmetic/NarrowSkywalkTick.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

private theorem narrow_take_msb (r : List Wire) (n : Nat) (hn : 0 < n) (hle : n ≤ r.length) :
    r.take (n-1)++[r.getD (n-1) 0]=r.take n := by
  have hidx : n-1 < r.length := by omega
  have he : n=(n-1)+1 := by omega
  conv_rhs => rw [he]
  rw [List.getD_eq_getElem _ _ hidx,List.take_add_one,List.getElem?_eq_getElem hidx]
  rfl

/-- The full258-bit route and half remain unchanged. Only post-half arithmetic
uses the retained signed prefix and Clifford high-sign restoration. -/
def narrowSkywalkRecordLayout (L : SkywalkIntegerLayout) (n : Nat) : NarrowSignedRecordLayout :=
  { xlo:=L.half.take (n-1),ylo:=L.b.take (n-1),
    sx:=L.half.getD (n-1) 0,sy:=L.b.getD (n-1) 0,q:=L.history,
    xhigh:=L.half.drop n,yhigh:=L.b.drop n,
    carryLow:=L.carry.take (n-1),carryHigh:=L.carry.drop (n-1) }

theorem narrowSkywalkRecord_views (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) :
    (narrowSkywalkRecordLayout L n).x=L.half ∧
    (narrowSkywalkRecordLayout L n).y=L.b ∧
    (narrowSkywalkRecordLayout L n).carry=L.carry := by
  have hl := L.record_lengths hv
  have hx := narrow_take_msb L.half n hn hle
  have hy := narrow_take_msb L.b n hn (by omega)
  simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.x,NarrowSignedRecordLayout.y,
    NarrowSignedRecordLayout.carry,NarrowSignedRecordLayout.xp,NarrowSignedRecordLayout.yp]
  rw [hx,hy,List.take_append_drop,List.take_append_drop,List.take_append_drop]
  exact ⟨rfl,rfl,rfl⟩

theorem narrowSkywalkRecord_widths (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) : (narrowSkywalkRecordLayout L n).Widths n := by
  have hl := L.record_lengths hv
  constructor
  · simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.xp,List.length_append,
      List.length_singleton,List.length_take]
    omega
  · simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.yp,List.length_append,
      List.length_singleton,List.length_take]
    omega
  · simp only [narrowSkywalkRecordLayout,List.length_take]
    omega

theorem narrowSkywalkRecord_nodup (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) : (narrowSkywalkRecordLayout L n).wires.Nodup := by
  have hf := narrowSkywalkRecord_views L hv n hn hle
  simp only [NarrowSignedRecordLayout.wires,hf.1,hf.2.1,hf.2.2]
  exact L.record_nodup hv

def narrowSkywalkTick (L : SkywalkIntegerLayout) (n : Nat) : Program :=
  skywalkRoute L.a0 L.b0 L.ah L.bh ++ skywalkSignedHalf L.aSign L.ext ++
    narrowSignedRecord (narrowSkywalkRecordLayout L n) n ++ [.CX L.previous L.a0]

def narrowSkywalkUntick (L : SkywalkIntegerLayout) (n : Nat) : Program :=
  [.CX L.previous L.a0] ++ narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n ++
    skywalkSignedHalf L.aSign L.ext ++ [.CX L.a0 L.b0] ++ swapRegisters L.a0 L.ah L.bh

private theorem prefix_no_measure_NarrowSkywalkTick (p q : Program) (hp : measurementCount p=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  have hr := run_take p m s
  rw [hp,List.take_zero] at hr
  rw [run_append,hp,List.take_zero,List.drop_zero,hr]

private theorem suffix_no_measure_NarrowSkywalkTick (p q : Program) (hq : measurementCount q=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  rw [run_append,run_take]
  have h1 := run_take q (m.drop (measurementCount p)) (run p m s)
  have h2 := run_take q m (run p m s)
  rw [hq,List.take_zero] at h1 h2
  exact h1.symm.trans h2

private theorem route_aux_frame_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.ext::L.carry) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis q=s.basis q := by
  have hn : ((L.previous::L.history::L.ext::L.carry)++
      (L.a0::L.b0::(L.ah++L.bh))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  apply run_preserves_outside
  intro hm
  have hh := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) hm
  exact List.disjoint_left.mp hd hq (List.mem_toFinset.mp hh)

private theorem half_aux_frame_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.a0::(L.b++L.carry)) :
    (run (skywalkSignedHalf L.aSign L.ext) m s).basis q=s.basis q := by
  have hne : q≠L.ext := by
    intro he
    subst q
    have hh := List.nodup_iff_count.mp hv.nodup L.ext
    have hp := List.count_pos_iff.mpr hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.b,
      List.count_cons,List.count_append] at hh hp
    simp only [beq_self_eq_true,if_true] at hh
    omega
  exact (skywalkSignedHalf_frame L.aSign L.ext s m).2 q hne

private theorem ext_outside_high_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.ext∉L.ah := by
  intro hm
  have hh := List.nodup_iff_count.mp hv.nodup L.ext
  have hp := List.count_pos_iff.mpr hm
  simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh
  simp only [beq_self_eq_true,if_true] at hh
  omega

private theorem ext_sign_ne_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid) : L.aSign≠L.ext := by
  intro he
  exact ext_outside_high_NarrowSkywalkTick L hv (by simp [SkywalkIntegerLayout.ah,←he])

private theorem previous_low_ne_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid) : L.previous≠L.a0 := by
  intro he
  have hh := List.nodup_iff_count.mp hv.nodup L.previous
  simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh
  simp [he] at hh

private theorem route_int_values_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (hp : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (hext : s.basis L.ext=false) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).phase=s.phase ∧
    signedRegValue (L.ext::L.ah) (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).1 ∧
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).2 ∧
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis L.a0=SkywalkRails.odd A := by
  have hna : L.ah≠[] := by simp [SkywalkIntegerLayout.ah]
  have hnb : L.bh≠[] := by simp [SkywalkIntegerLayout.bh]
  have hA := ha.symm.trans (signedRegValue_cons L.a0 L.ah s.basis hna)
  have hB := hb.symm.trans (signedRegValue_cons L.b0 L.bh s.basis hnb)
  have hpar : s.basis L.b0=(!s.basis L.a0) := by
    cases hca : s.basis L.a0 with
    | false =>
      cases hcb : s.basis L.b0 with
      | false =>
        simp [hca,hcb] at hA hB
        omega
      | true => rfl
    | true =>
      cases hcb : s.basis L.b0 with
      | false => rfl
      | true =>
        simp [hca,hcb] at hA hB
        omega
  have hctrl : s.basis L.a0=SkywalkRails.odd A := by
    cases hc : s.basis L.a0 with
    | false =>
      have he : A%2=0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
    | true =>
      have he : A%2≠0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  obtain ⟨hf,_,hctl,hlo,hrawA,hrawB⟩ := skywalkRoute_correct L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv) s m hpar
  have he0 : t.basis L.ext=false :=
    (route_aux_frame_NarrowSkywalkTick L hv s m L.ext (by simp)).trans hext
  have hsa : signedRegValue L.ah t.basis=
      if s.basis L.a0 then signedRegValue L.bh s.basis else signedRegValue L.ah s.basis := by
    have hh := congrArg (signedDecode L.ah.length) hrawA
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  have hsb : signedRegValue L.bh t.basis=
      if s.basis L.a0 then signedRegValue L.ah s.basis else signedRegValue L.bh s.basis := by
    have hh := congrArg (signedDecode L.bh.length) hrawB
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  refine ⟨hf,?_,?_,hctl.trans hctrl⟩
  · rw [signedRegValue_cons L.ext L.ah t.basis hna,he0,hsa]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

  · change signedRegValue (L.b0::L.bh) t.basis=_
    rw [signedRegValue_cons L.b0 L.bh t.basis hnb,hlo,hsb]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

private theorem tick_run_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat) (s : State) (m : List Bool) :
    run (narrowSkywalkTick L n) m s=
      run [.CX L.previous L.a0] m
        (run (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) m
          (run (skywalkSignedHalf L.aSign L.ext) m
            (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s))) := by
  have hr := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv)).2
  have hh := (skywalkSignedHalf_counts L.aSign L.ext).2
  simp only [narrowSkywalkTick,List.append_assoc]
  rw [prefix_no_measure_NarrowSkywalkTick _ _ hr,prefix_no_measure_NarrowSkywalkTick _ _ hh,
    suffix_no_measure_NarrowSkywalkTick _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0)]


/-- Full-State equality of independently measured wide and retained-prefix
records. High target sign extension is an actual Clifford fanout. -/
theorem narrowSkywalkRecord_eq (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) (A B : Int)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int))
    (s : State) (m₁ m₂ : List Bool)
    (hi : SignedRecordValues L.history L.half L.b L.carry A B false s.basis) :
    run (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) m₁ s=
      run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m₂ s := by
  have hw := narrowSkywalkRecord_widths L hv n hn hle
  have hd := narrowSkywalkRecord_nodup L hv n hn hle
  have vv := narrowSkywalkRecord_views L hv n hn hle
  have hl := L.record_lengths hv
  have hs := narrowSignedRecord_spec (narrowSkywalkRecordLayout L n) n hw hd A B
    ha0 ha1 hb0 hb1 s m₁
  simp only [vv.1,vv.2.1,vv.2.2] at hs
  obtain ⟨ps,vs⟩ := hs hi
  obtain ⟨pw,vw⟩ := signedRecord_spec L.ah (L.b0::L.bMid) L.ext L.bSign L.history
    L.carry (L.record_nodup hv) hl.1 hl.2 A B s m₂ hi
  apply congrArg₂ State.mk
  · exact ps.trans pw.symm
  · funext a
    by_cases hq : a=L.history
    · subst a
      exact vs.1.trans vw.1.symm
    by_cases hx : a∈L.half
    · exact (signedRegValue_eq_iff _ _ _).mp (vs.2.1.trans vw.2.1.symm) a hx
    by_cases hy : a∈L.b
    · exact (signedRegValue_eq_iff _ _ _).mp (vs.2.2.1.trans vw.2.2.1.symm) a hy
    by_cases hc : a∈L.carry
    · exact (regValue_eq_iff _ _ _).mp (vs.2.2.2.trans vw.2.2.2.symm) a hc
    have hsframe := (narrowSignedRecord_frame (narrowSkywalkRecordLayout L n) n hw s m₁ a)
    have hnot : a∉(narrowSkywalkRecordLayout L n).wires := by
      simp only [NarrowSignedRecordLayout.wires,vv.1,vv.2.1,vv.2.2,
        List.mem_cons,List.mem_append]
      tauto
    have hwframe := signedRecord_frame L.ah (L.b0::L.bMid) L.ext L.bSign L.history
      L.carry hl.1 hl.2 s m₂ a
    exact (hsframe hnot).1.trans ((hwframe (by
      change a∉L.history::(L.half++L.b++L.carry)
      simp only [List.mem_cons,List.mem_append]
      tauto)).1.symm)

/-- The unchanged route/half prefix presents bounded H/O to the narrow adder. -/
theorem narrowSkywalkTick_eq (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) (A B : Int) (G : Bool)
    (hp : (A+B)%2=1)
    (ha0 : -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(n-1):Nat):Int))
    (s : State) (m : List Bool) (hin : SkywalkIntegerInput L A B G s.basis) :
    run (narrowSkywalkTick L n) m s=run (skywalkIntegerTick L) m s := by
  let E := (SkywalkRails.route A B).1
  let O := (SkywalkRails.route A B).2
  let H := E/2
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  let u := run (skywalkSignedHalf L.aSign L.ext) m t
  have he : E%2=0 := SkywalkRails.route_even A B hp
  obtain ⟨_,hE,hO,_⟩ := route_int_values_NarrowSkywalkTick L hv A B hp s m hin.1 hin.2.1 hin.2.2.2.1
  change signedRegValue (L.ext::(L.aMid++[L.aSign])) t.basis=E at hE
  have tq : t.basis L.history=false :=
    (route_aux_frame_NarrowSkywalkTick L hv s m L.history (by simp)).trans hin.2.2.2.2.1
  have tk : regValue L.carry t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hin.2.2.2.2.2
    intro q hq
    exact route_aux_frame_NarrowSkywalkTick L hv s m q (by simp [hq])
  have uH : signedRegValue L.half u.basis=H := by
    have hh := skywalkSignedHalf_int L.ext L.aSign L.aMid (ext_sign_ne_NarrowSkywalkTick L hv)
      (ext_outside_high_NarrowSkywalkTick L hv) t m (by rw [hE]; exact he)
    change signedRegValue L.half u.basis=
      signedRegValue (L.ext::(L.aMid++[L.aSign])) t.basis/2 at hh
    rw [hE] at hh
    exact hh
  have uO : signedRegValue L.b u.basis=O := by
    apply Eq.trans ((signedRegValue_eq_iff _ _ _).mpr ?_) hO
    intro q hq
    exact half_aux_frame_NarrowSkywalkTick L hv t m q (by simp [hq])
  have uq : u.basis L.history=false :=
    (half_aux_frame_NarrowSkywalkTick L hv t m L.history (by simp)).trans tq
  have uk : regValue L.carry u.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) tk
    intro q hq
    exact half_aux_frame_NarrowSkywalkTick L hv t m q (by simp [hq])
  have hr := narrowSkywalkRecord_eq L hv n hn hle H O ha0 ha1 hb0 hb1 u m m ⟨uq,uH,uO,uk⟩
  rw [tick_run_NarrowSkywalkTick L hv n s m,hr]
  have hmR := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv)).2
  have hmH := (skywalkSignedHalf_counts L.aSign L.ext).2
  simp only [skywalkIntegerTick,List.append_assoc]
  rw [prefix_no_measure_NarrowSkywalkTick _ _ hmR,prefix_no_measure_NarrowSkywalkTick _ _ hmH,
    suffix_no_measure_NarrowSkywalkTick _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0)]

/-- Same public mathematical output and arbitrary-record phase as the accepted
wide tick, with explicit post-half signed fit assumptions. -/
theorem narrowSkywalkTick_spec (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) (A B : Int) (G : Bool)
    (hp : (A+B)%2=1)
    (ha0 : -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(n-1):Nat):Int)) :
    Triple (SkywalkIntegerInput L A B G) (narrowSkywalkTick L n)
      (SkywalkIntegerOutput L A B G) := by
  intro s m hin
  rw [narrowSkywalkTick_eq L hv n hn hle A B G hp ha0 ha1 hb0 hb1 s m hin]
  exact skywalkIntegerTick_spec L hv A B G hp s m hin

private theorem swap_twice_NarrowSkywalkTick (c : Wire) (a b : List Wire) (hl : a.length=b.length)
    (hn : (c::(a++b)).Nodup) (s : State) (m₁ m₂ : List Bool) :
    run (swapRegisters c a b) m₂ (run (swapRegisters c a b) m₁ s)=s := by
  let t := run (swapRegisters c a b) m₁ s
  let v := run (swapRegisters c a b) m₂ t
  obtain ⟨p1,e1,a1,b1⟩ := swapRegisters_correct c a b hl hn s m₁
  obtain ⟨p2,e2,a2,b2⟩ := swapRegisters_correct c a b hl hn t m₂
  have hc : t.basis c=s.basis c := e1 c
    (fun h => (List.nodup_cons.mp hn).1 (by simp [h]))
    (fun h => (List.nodup_cons.mp hn).1 (by simp [h]))
  have ha : regValue a v.basis=regValue a s.basis := by
    rw [a2,hc,a1,b1]
    cases s.basis c <;> rfl
  have hb : regValue b v.basis=regValue b s.basis := by
    rw [b2,hc,a1,b1]
    cases s.basis c <;> rfl
  apply congrArg₂ State.mk
  · exact p2.trans p1
  · funext q
    by_cases hqa : q∈a
    · exact (regValue_eq_iff _ _ _).mp ha q hqa
    by_cases hqb : q∈b
    · exact (regValue_eq_iff _ _ _).mp hb q hqb
    exact (e2 q hqa hqb).trans (e1 q hqa hqb)

private theorem cx_twice_NarrowSkywalkTick (c t : Wire) (hct : c≠t) (s : State) (m₁ m₂ : List Bool) :
    run [.CX c t] m₂ (run [.CX c t] m₁ s)=s := by
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=t
  · subst q
    cases hc : s.basis c <;> cases ht : s.basis t <;>
      simp [run,writeBit,hct,hc,ht]
  · simp [run,writeBit,hq]

private theorem route_roundtrip_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m₁ m₂ : List Bool) :
    run ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh) m₂
      (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m₁ s)=s := by
  have hl := L.high_lengths hv
  have hn : (L.a0::(L.ah++L.bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp (L.route_nodup hv) q
    simp only [List.count_cons] at hh ⊢
    omega
  have hne : L.a0≠L.b0 := fun h => (List.nodup_cons.mp (L.route_nodup hv)).1 (by simp [h])
  have hm := (swapRegisters_resources L.a0 L.ah L.bh hl hn).2.1
  rw [skywalkRoute,prefix_no_measure_NarrowSkywalkTick _ _ hm,
    prefix_no_measure_NarrowSkywalkTick _ _ (by rfl : measurementCount [.CX L.a0 L.b0]=0)]
  rw [cx_twice_NarrowSkywalkTick L.a0 L.b0 hne]
  exact swap_twice_NarrowSkywalkTick L.a0 L.ah L.bh hl hn s m₁ m₂

private theorem untick_run_NarrowSkywalkTick (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat) (s : State) (m : List Bool) :
    run (narrowSkywalkUntick L n) m s=
      run ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh) m
        (run (skywalkSignedHalf L.aSign L.ext) m
          (run (narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n) m
            (run [.CX L.previous L.a0] m s))) := by
  have hl := L.high_lengths hv
  have hn : (L.a0::(L.ah++L.bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp (L.route_nodup hv) q
    simp only [List.count_cons] at hh ⊢
    omega
  have hs := (swapRegisters_resources L.a0 L.ah L.bh hl hn).2.1
  have hh := (skywalkSignedHalf_counts L.aSign L.ext).2
  have ht : measurementCount (skywalkSignedHalf L.aSign L.ext++
      ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh))=0 := by
    simp [measurementCount_append,hh,hs,measurementCount]
  simp only [narrowSkywalkUntick,List.append_assoc]
  rw [prefix_no_measure_NarrowSkywalkTick _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0),
    suffix_no_measure_NarrowSkywalkTick _ _ ht,prefix_no_measure_NarrowSkywalkTick _ _ hh]

/-- The separately emitted inverse restores the entire physical State with
independent measurement streams. Only the history/carry clean premises are
needed for reversal; signed parity/extension premises are for interpretation. -/
theorem narrowSkywalkTick_roundtrip (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) (s : State) (m₁ m₂ : List Bool) (hq : s.basis L.history=false)
    (hk : regValue L.carry s.basis=0) :
    run (narrowSkywalkUntick L n) m₂ (run (narrowSkywalkTick L n) m₁ s)=s := by
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m₁ s
  let u := run (skywalkSignedHalf L.aSign L.ext) m₁ t
  have tq : t.basis L.history=false :=
    (route_aux_frame_NarrowSkywalkTick L hv s m₁ L.history (by simp)).trans hq
  have tk : regValue L.carry t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hk
    intro q hq
    exact route_aux_frame_NarrowSkywalkTick L hv s m₁ q (by simp [hq])
  have uq : u.basis L.history=false :=
    (half_aux_frame_NarrowSkywalkTick L hv t m₁ L.history (by simp)).trans tq
  have uk : regValue L.carry u.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) tk
    intro q hq
    exact half_aux_frame_NarrowSkywalkTick L hv t m₁ q (by simp [hq])
  have hvv := narrowSkywalkRecord_views L hv n hn hle
  have hr := narrowSignedRecord_roundtrip (narrowSkywalkRecordLayout L n) n
    (narrowSkywalkRecord_widths L hv n hn hle)
    (narrowSkywalkRecord_nodup L hv n hn hle) u m₁ m₂
    (by simpa only [narrowSkywalkRecordLayout] using uq)
    (by simpa only [hvv.2.2] using uk)
  have hh : run (skywalkSignedHalf L.aSign L.ext) m₂ u=t := by
    simpa only [skywalkSignedHalf,run] using
      skywalkSignedHalf_twice L.aSign L.ext (ext_sign_ne_NarrowSkywalkTick L hv) t m₁
  rw [tick_run_NarrowSkywalkTick L hv n s m₁,untick_run_NarrowSkywalkTick L hv n _ m₂,
    cx_twice_NarrowSkywalkTick L.previous L.a0 (previous_low_ne_NarrowSkywalkTick L hv)]
  change run ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh) m₂
    (run (skywalkSignedHalf L.aSign L.ext) m₂
      (run (narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n) m₂
        (run (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) m₁ u)))=s
  rw [hr,hh]
  exact route_roundtrip_NarrowSkywalkTick L hv s m₁ m₂


/-- The actual narrow adder stream has n-1 T/M; the route remains full width. -/
theorem narrowSkywalkTick_counts (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) :
    toffoliCount (narrowSkywalkTick L n)=L.ah.length+(n-1) ∧
    measurementCount (narrowSkywalkTick L n)=n-1 ∧
    toffoliCount (narrowSkywalkUntick L n)=L.ah.length+(n-1) ∧
    measurementCount (narrowSkywalkUntick L n)=n-1 := by
  have hl := L.high_lengths hv
  have hr := skywalkRoute_counts L.a0 L.b0 L.ah L.bh hl (L.route_nodup hv)
  have hnd : (L.a0::(L.ah++L.bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp (L.route_nodup hv) q
    simp only [List.count_cons] at hh ⊢
    omega
  have hs := swapRegisters_resources L.a0 L.ah L.bh hl hnd
  have ha := narrowSignedRecord_counts (narrowSkywalkRecordLayout L n) n
    (narrowSkywalkRecord_widths L hv n hn hle)
  have hh := skywalkSignedHalf_counts L.aSign L.ext
  simp only [narrowSkywalkTick,narrowSkywalkUntick,toffoliCount_append,measurementCount_append,
    hr.1,hr.2,hs.1,hs.2.1,ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hh.1,hh.2,
    toffoliCount,measurementCount]
  omega
theorem narrowSkywalkTick_wires_subset (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) :
    wires (narrowSkywalkTick L n)⊆L.wires.toFinset ∧
    wires (narrowSkywalkUntick L n)⊆L.wires.toFinset := by
  have hl := L.high_lengths hv
  have hroute : wires (skywalkRoute L.a0 L.b0 L.ah L.bh)⊆L.wires.toFinset := by
    intro q hq
    have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh hl hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have hswap : wires (swapRegisters L.a0 L.ah L.bh)⊆L.wires.toFinset := by
    intro q hq
    have h := swapRegisters_wires L.a0 L.ah L.bh hl hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have hhalf : wires (skywalkSignedHalf L.aSign L.ext)⊆L.wires.toFinset := by
    rw [skywalkSignedHalf_wires]
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · simp [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah]
    · simp [SkywalkIntegerLayout.wires]
  have hword := narrowSignedRecord_support (narrowSkywalkRecordLayout L n) n
    (narrowSkywalkRecord_widths L hv n hn hle)
  have vv := narrowSkywalkRecord_views L hv n hn hle
  have hsigned :
      wires (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) ⊆
        (L.history::(L.half++L.b++L.carry)).toFinset ∧
      wires (narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n) ⊆
        (L.history::(L.half++L.b++L.carry)).toFinset := by
    simpa only [NarrowSignedRecordLayout.wires,vv.1,vv.2.1,vv.2.2,
      ] using hword
  have hown : (L.history::(L.half++L.b++L.carry)).toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hrecord : wires (narrowSignedRecord (narrowSkywalkRecordLayout L n) n)⊆L.wires.toFinset := by
    exact hsigned.1.trans hown
  have hunrecord : wires (narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n)⊆L.wires.toFinset := by
    exact hsigned.2.trans hown
  have hprevious : wires [.CX L.previous L.a0]⊆L.wires.toFinset := by
    simp [SkywalkIntegerLayout.wires,wires,Instr.wires]
  have hlow : wires [.CX L.a0 L.b0]⊆L.wires.toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [narrowSkywalkTick,narrowSkywalkUntick,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨hroute,hhalf⟩,hrecord⟩,hprevious⟩,
    ⟨⟨⟨⟨hprevious,hunrecord⟩,hhalf⟩,hlow⟩,hswap⟩⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NarrowSkywalkLoopCore.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic

/-- Exact universal retained arithmetic width; all512 ticks remain present. -/
def narrowSkywalkWidth (i : Nat) : Nat := min 258 (513-i)

theorem narrowSkywalkWidth_bounds (i : Nat) (hi : i<512) :
    2≤narrowSkywalkWidth i ∧ narrowSkywalkWidth i≤258 ∧
    narrowSkywalkWidth i-1=min 257 (512-i) := by
  unfold narrowSkywalkWidth
  omega

/-- Derived from the complete coprime logical trajectory, not a sampled
profile. The strict signed operands are O and E/2 after the full-width route. -/
theorem narrowSkywalk_iter_fit (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpo : p%2=1) (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    let n := narrowSkywalkWidth i
    (r.a+r.b)%2=1 ∧
    -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route r.a r.b).1/2 ∧
    (SkywalkRails.route r.a r.b).1/2 < ((2^(n-1):Nat):Int) ∧
    -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route r.a r.b).2 ∧
    (SkywalkRails.route r.a r.b).2 < ((2^(n-1):Nat):Int) := by
  dsimp only
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  let k := min 257 (512-i)
  have hk : 0<k := by dsimp only [k]; omega
  have hn := (narrowSkywalkWidth_bounds i hi).2.2
  have hsum : z.u+z.v≤2^k := by
    by_cases he : 257≤512-i
    · have hk' : k=257 := by dsimp only [k]; omega
      rw [hk']
      exact Nat.le_of_lt (SkywalkNat.iter_sum_initial_width p x 256 i hp hx)
    · have hk' : k=512-i := by dsimp only [k]; omega
      rw [hk']
      exact SkywalkNat.iter_sum_product_width p x 256 i hp0 hx0 hpo hp hx hc (by omega)
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at he
  rw [he]
  have hvalid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  have hpar := SkywalkRails.encode_odd_sum G S (z.u:Int) (z.v:Int) (by
    have hodd := hvalid.2.1
    exact_mod_cast hodd)
  have hb := SkywalkRails.encode_abs_sum_bound G S z.u z.v (2^k) hsum
  have hr := SkywalkRails.route_half_width _ _ k hk hpar hb.1 hb.2
  have hpw : (2^k:Nat)=2^(k-1)*2 := by
    calc
      2^k=2^((k-1)+1) := by congr 1; omega
      _=2^(k-1)*2 := pow_succ 2 (k-1)
  have hpw' : ((2^k:Nat):Int)=((2^(k-1):Nat):Int)*2 := by
    exact_mod_cast hpw
  have hpositive : 0<((2^(k-1):Nat):Int) := by positivity
  have hH := abs_le.mp hr.2
  have hO := abs_lt.mp hr.1
  rw [hn]
  change ((SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a+
    (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b)%2=1 ∧
    -((2^k:Nat):Int)≤(SkywalkRails.route (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a
      (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b).1/2 ∧
    (SkywalkRails.route (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a
      (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b).1/2<((2^k:Nat):Int) ∧
    -((2^k:Nat):Int)≤(SkywalkRails.route (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a
      (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b).2 ∧
    (SkywalkRails.route (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a
      (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b).2<((2^k:Nat):Int)
  exact ⟨hpar,by omega,by omega,by omega,hO.2⟩


attribute [local irreducible] narrowSkywalkTick narrowSkywalkUntick
attribute [local irreducible] run
attribute [local irreducible] SkywalkTrace.next Nat.iterate

/-- Narrow ticks advance the identical complete physical pool and actual
history as the accepted wide path, under the canonical nonzero input contract. -/
theorem narrowSkywalkStage_step (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    let r := SkywalkRails.encode false false (x:Int) (p:Int)
    Triple (SkywalkIntegerStage w r i)
      (narrowSkywalkTick (skywalkPoolTick w i) (narrowSkywalkWidth i))
      (SkywalkIntegerStage w r (i+1)) := by
  dsimp only
  intro s m hin
  let r := SkywalkRails.encode false false (x:Int) (p:Int)
  let ri := SkywalkTrace.next^[i] r
  let L := skywalkPoolTick w i
  have hv := skywalkPool_valid w i hi hn
  have hf := narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp hx hc hi
  have hw := narrowSkywalkWidth_bounds i hi
  have hlength : L.half.length=258 := by
    rw [skywalkPool_half,skywalkPoolA,wireBlock_length]
  have fresh := hin.2.2.2.2.1 i (Nat.le_refl i) hi
  have hnative : SkywalkIntegerInput L ri.a ri.b ri.g s.basis := by
    refine ⟨?_,?_,hin.2.2.1,fresh.1,fresh.2,hin.2.2.2.2.2.1⟩
    · rw [skywalkPool_a]
      exact hin.1
    · rw [skywalkPool_b]
      exact hin.2.1
  have heq := narrowSkywalkTick_eq L hv (narrowSkywalkWidth i) (by omega)
    (by omega) ri.a ri.b ri.g hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 s m hnative
  rw [heq]
  exact skywalkIntegerStage_step w hn r i hi hf.1 s m hin

section LoopSpec
attribute [local irreducible] SkywalkIntegerStage

end LoopSpec

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NarrowSkywalkRoute.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- Sign-difference AND, computing one coherent fanout control. The sign
reference is temporarily XORed and immediately restored. -/
def skywalkSignDelta (g a b d : Wire) : Program :=
  [.CX b a,.CCX g a d,.CX b a]

/-- The XOR of both sign references is invariant when both sign banks flip.
This permits exact measured AND cleanup with the current references. -/
def skywalkSignDeltaErase (g a b d : Wire) : Program :=
  [.CX b a,.measureX d [] [.CZ g a],.CX b a]

theorem skywalkSignDelta_correct (g a b d : Wire)
    (hga : g≠a) (_hgd : g≠d) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (s : State) (m : List Bool) (hd : s.basis d=false) :
    run (skywalkSignDelta g a b d) m s=
      ⟨s.phase,writeBit s.basis d (s.basis g && (s.basis a ^^ s.basis b))⟩ := by
  have hda := had.symm
  have hba := hab.symm
  simp only [skywalkSignDelta,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=d
  · subst q
    simp_all [writeBit]
  by_cases hqa : q=a
  · subst q
    cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp_all [writeBit]
  · simp [writeBit,hq,hqa]

theorem skywalkSignDeltaErase_correct (g a b d : Wire)
    (hga : g≠a) (hgd : g≠d) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (s : State) (m : List Bool)
    (hd : s.basis d=(s.basis g && (s.basis a ^^ s.basis b))) :
    run (skywalkSignDeltaErase g a b d) m s=⟨s.phase,writeBit s.basis d false⟩ := by
  have hda := had.symm
  have hba := hab.symm
  simp only [skywalkSignDeltaErase,run]
  cases hm : m.headD false <;>
    simp_all [measureAndCorrect,correct,writeBit]
  all_goals
    funext q
    by_cases hq : q=a
    · subst q
      simp_all
    · simp_all [Function.update_apply]

theorem skywalkSignDelta_counts (g a b d : Wire) :
    toffoliCount (skywalkSignDelta g a b d)=1 ∧
    measurementCount (skywalkSignDelta g a b d)=0 ∧
    toffoliCount (skywalkSignDeltaErase g a b d)=0 ∧
    measurementCount (skywalkSignDeltaErase g a b d)=1 := by
  simp [skywalkSignDelta,skywalkSignDeltaErase,toffoliCount,measurementCount]

structure NarrowSkywalkSwapLayout where
  g : Wire
  delta : Wire
  sx : Wire
  sy : Wire
  xlow : List Wire
  ylow : List Wire
  xhigh : List Wire
  yhigh : List Wire

namespace NarrowSkywalkSwapLayout

def xbank (L : NarrowSkywalkSwapLayout) : List Wire := L.sx::L.xhigh
def ybank (L : NarrowSkywalkSwapLayout) : List Wire := L.sy::L.yhigh
def x (L : NarrowSkywalkSwapLayout) : List Wire := L.xlow++L.xbank
def y (L : NarrowSkywalkSwapLayout) : List Wire := L.ylow++L.ybank
def bank (L : NarrowSkywalkSwapLayout) : List Wire := L.xbank++L.ybank
def wires (L : NarrowSkywalkSwapLayout) : List Wire := L.g::L.delta::(L.x++L.y)

structure Valid (L : NarrowSkywalkSwapLayout) : Prop where
  low_lengths : L.xlow.length=L.ylow.length
  high_lengths : L.xhigh.length=L.yhigh.length
  nodup : L.wires.Nodup

/-- Current high rails are sign copies, including the chosen reference signs.
Positive powers-of-two endpoints are handled by the caller's extra route bit. -/
def Copies (L : NarrowSkywalkSwapLayout) (s : BasisState) : Prop :=
  (∀ q∈L.xbank,s q=s L.sx) ∧ (∀ q∈L.ybank,s q=s L.sy)

theorem lengths (L : NarrowSkywalkSwapLayout) (hv : L.Valid) : L.x.length=L.y.length := by
  simp only [x,y,xbank,ybank,List.length_append,List.length_cons,hv.low_lengths,hv.high_lengths]

theorem full_nodup (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    (L.g::(L.x++L.y)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,List.count_cons] at hh ⊢
  omega

theorem low_nodup (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    (L.g::(L.xlow++L.ylow)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh ⊢
  omega

theorem bank_nodup (L : NarrowSkywalkSwapLayout) (hv : L.Valid) : L.bank.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,x,y,xbank,ybank,bank,List.count_cons,List.count_append] at hh ⊢
  omega

theorem delta_bank (L : NarrowSkywalkSwapLayout) (hv : L.Valid) : L.delta∉L.bank := by
  intro hm
  have hh := List.nodup_iff_count.mp hv.nodup L.delta
  have hp := List.count_pos_iff.mpr hm
  simp only [wires,x,y,xbank,ybank,bank,List.count_cons,List.count_append] at hh hp
  simp only [beq_self_eq_true,if_true] at hh
  omega

theorem distinct (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    L.g≠L.sx ∧ L.g≠L.delta ∧ L.sx≠L.sy ∧ L.sx≠L.delta ∧ L.sy≠L.delta := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.g
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.g
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.sx
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
    omega
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.sx
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
    omega
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.sy
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
    omega

theorem outside_low (L : NarrowSkywalkSwapLayout) (hv : L.Valid) (q : Wire)
    (hq : q∈L.g::L.delta::L.bank) : q∉L.xlow ∧ q∉L.ylow := by
  constructor <;> intro hm
  all_goals
    have hh := List.nodup_iff_count.mp hv.nodup q
    have hp := List.count_pos_iff.mpr hm
    have hb := List.count_pos_iff.mpr hq
    simp only [wires,x,y,xbank,ybank,bank,List.count_cons,List.count_append] at hh hb
    omega

end NarrowSkywalkSwapLayout

/-- Only low non-sign bits use Fredkins. Both retained signs and all omitted
high sign copies use the one coherent delta fanout, then measured cleanup. -/
def narrowSkywalkSwap (L : NarrowSkywalkSwapLayout) : Program :=
  skywalkSignDelta L.g L.sx L.sy L.delta ++ swapRegisters L.g L.xlow L.ylow ++
    signComplement L.delta L.bank ++ skywalkSignDeltaErase L.g L.sx L.sy L.delta

private theorem narrow_route_const_read (r : List Wire) (s : BasisState) (c : Bool)
    (hc : ∀ q∈r,s q=c) : regValue r s=(if c then 2^r.length-1 else 0) := by
  induction r with
  | nil => cases c <;> simp [regValue]
  | cons q r ih =>
    have hq := hc q (by simp)
    have hr := ih (by intro a ha; exact hc a (by simp [ha]))
    change (if s q then 1 else 0)+2*regValue r s=(if c then 2^(r.length+1)-1 else 0)
    rw [hq,hr]
    cases c <;> simp [pow_succ]
    all_goals have hp : 0<2^r.length := by positivity
    all_goals omega

private theorem route_prefix_no_measure (p q : Program) (hp : measurementCount p=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  have hr := run_take p m s
  rw [hp,List.take_zero] at hr
  rw [run_append,hp,List.take_zero,List.drop_zero,hr]


/-- Exact swap projection, including full source/control/work frames and
arbitrary-record phase restoration. Only redundant sign-bank premises narrow. -/
theorem narrowSkywalkSwap_correct (L : NarrowSkywalkSwapLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hd : s.basis L.delta=false) (hc : L.Copies s.basis) :
    (run (narrowSkywalkSwap L) m s).phase=s.phase ∧
    (∀ q,q∉L.x → q∉L.y → (run (narrowSkywalkSwap L) m s).basis q=s.basis q) ∧
    regValue L.x (run (narrowSkywalkSwap L) m s).basis=
      (if s.basis L.g then regValue L.y s.basis else regValue L.x s.basis) ∧
    regValue L.y (run (narrowSkywalkSwap L) m s).basis=
      (if s.basis L.g then regValue L.x s.basis else regValue L.y s.basis) ∧
    L.Copies (run (narrowSkywalkSwap L) m s).basis := by
  let D := s.basis L.g && (s.basis L.sx ^^ s.basis L.sy)
  let u := run (skywalkSignDelta L.g L.sx L.sy L.delta) m s
  let t := run (swapRegisters L.g L.xlow L.ylow) m u
  let v := run (signComplement L.delta L.bank) m t
  let out := run (skywalkSignDeltaErase L.g L.sx L.sy L.delta) m v
  have hn := L.distinct hv
  have hu : u=⟨s.phase,writeBit s.basis L.delta D⟩ :=
    skywalkSignDelta_correct _ _ _ _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2 s m hd
  have ulow (q : Wire) (hq : q∈L.xlow ∨ q∈L.ylow) : u.basis q=s.basis q := by
    have he : q≠L.delta := by
      intro he
      subst q
      have hh := L.outside_low hv L.delta (by simp)
      tauto
    rw [hu]
    simp [writeBit,he]
  have ux : regValue L.xlow u.basis=regValue L.xlow s.basis :=
    regValue_congr _ _ _ (by intro q hq; exact ulow q (Or.inl hq))
  have uy : regValue L.ylow u.basis=regValue L.ylow s.basis :=
    regValue_congr _ _ _ (by intro q hq; exact ulow q (Or.inr hq))
  have uother (q : Wire) (hq : q≠L.delta) : u.basis q=s.basis q := by
    rw [hu]
    simp [writeBit,hq]
  obtain ⟨tp,tf,tx,ty⟩ := swapRegisters_correct L.g L.xlow L.ylow hv.low_lengths
    (L.low_nodup hv) u m
  change regValue L.xlow t.basis=(if u.basis L.g then regValue L.ylow u.basis else regValue L.xlow u.basis) at tx
  change regValue L.ylow t.basis=(if u.basis L.g then regValue L.xlow u.basis else regValue L.ylow u.basis) at ty
  have keep (q : Wire) (hq : q∈L.g::L.delta::L.bank) : t.basis q=u.basis q := by
    have hh := L.outside_low hv q hq
    exact tf q hh.1 hh.2
  have tg : t.basis L.g=s.basis L.g :=
    (keep L.g (by simp)).trans (uother L.g hn.2.1)
  have td : t.basis L.delta=D := by
    rw [keep L.delta (by simp),hu]
    simp [writeBit]
  have tb (q : Wire) (hq : q∈L.bank) : t.basis q=s.basis q := by
    have he : q≠L.delta := fun he => L.delta_bank hv (he ▸ hq)
    exact (keep q (by simp [hq])).trans (uother q he)
  have hvf : v=⟨t.phase,fun q => if q∈L.bank then t.basis q ^^ t.basis L.delta else t.basis q⟩ :=
    narrow_fanout_correct L.delta L.bank (L.bank_nodup hv) (L.delta_bank hv) t m
  have gb : L.g∉L.bank := by
    intro hm
    have hh := List.nodup_iff_count.mp hv.nodup L.g
    have hp := List.count_pos_iff.mpr hm
    simp only [NarrowSkywalkSwapLayout.wires,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
      NarrowSkywalkSwapLayout.xbank,NarrowSkywalkSwapLayout.ybank,NarrowSkywalkSwapLayout.bank,
      List.count_cons,List.count_append] at hh hp
    simp only [beq_self_eq_true,if_true] at hh
    omega
  have vg : v.basis L.g=s.basis L.g := by
    rw [hvf]
    simp only [if_neg gb]
    exact tg
  have vd : v.basis L.delta=D := by
    rw [hvf]
    simp only [if_neg (L.delta_bank hv)]
    exact td
  have vbank (q : Wire) (hq : q∈L.bank) : v.basis q=(s.basis q ^^ D) := by
    rw [hvf]
    simp only [if_pos hq,td,tb q hq]
  have vsx : v.basis L.sx=(s.basis L.sx ^^ D) := vbank L.sx (by
    simp [NarrowSkywalkSwapLayout.bank,NarrowSkywalkSwapLayout.xbank])
  have vsy : v.basis L.sy=(s.basis L.sy ^^ D) := vbank L.sy (by
    simp [NarrowSkywalkSwapLayout.bank,NarrowSkywalkSwapLayout.ybank])
  have hD : v.basis L.delta=(v.basis L.g && (v.basis L.sx ^^ v.basis L.sy)) := by
    rw [vd,vg,vsx,vsy]
    dsimp only [D]
    cases s.basis L.g <;> cases s.basis L.sx <;> cases s.basis L.sy <;> rfl
  have ho : out=⟨v.phase,writeBit v.basis L.delta false⟩ :=
    skywalkSignDeltaErase_correct _ _ _ _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2 v m hD
  have ot (q : Wire) (hq : q∈L.xlow ∨ q∈L.ylow) : out.basis q=t.basis q := by
    have hb : q∉L.bank := by
      intro hqb
      have hh := L.outside_low hv q (by simp [hqb])
      tauto
    have he : q≠L.delta := by
      intro he
      subst q
      have hh := L.outside_low hv L.delta (by simp)
      tauto
    rw [ho,hvf]
    simp [writeBit,he,hb]
  have ox : regValue L.xlow out.basis=regValue L.xlow t.basis :=
    regValue_congr _ _ _ (by intro q hq; exact ot q (Or.inl hq))
  have oy : regValue L.ylow out.basis=regValue L.ylow t.basis :=
    regValue_congr _ _ _ (by intro q hq; exact ot q (Or.inr hq))
  have ogx (q : Wire) (hq : q∈L.xbank) :
      out.basis q=(if s.basis L.g then s.basis L.sy else s.basis L.sx) := by
    have hb : q∈L.bank := List.mem_append_left _ hq
    have he : q≠L.delta := fun he => L.delta_bank hv (he ▸ hb)
    rw [ho]
    simp only [writeBit,Function.update_of_ne he,vbank q hb,hc.1 q hq]
    dsimp only [D]
    cases s.basis L.g <;> cases s.basis L.sx <;> cases s.basis L.sy <;> rfl
  have ogy (q : Wire) (hq : q∈L.ybank) :
      out.basis q=(if s.basis L.g then s.basis L.sx else s.basis L.sy) := by
    have hb : q∈L.bank := List.mem_append_right _ hq
    have he : q≠L.delta := fun he => L.delta_bank hv (he ▸ hb)
    rw [ho]
    simp only [writeBit,Function.update_of_ne he,vbank q hb,hc.2 q hq]
    dsimp only [D]
    cases s.basis L.g <;> cases s.basis L.sx <;> cases s.basis L.sy <;> rfl
  have obx := narrow_route_const_read L.xbank out.basis _ ogx
  have oby := narrow_route_const_read L.ybank out.basis _ ogy
  have sbx := narrow_route_const_read L.xbank s.basis _ hc.1
  have sby := narrow_route_const_read L.ybank s.basis _ hc.2
  have hbanklen : L.xbank.length=L.ybank.length := by
    simp [NarrowSkywalkSwapLayout.xbank,NarrowSkywalkSwapLayout.ybank,hv.high_lengths]
  have ug : u.basis L.g=s.basis L.g := uother L.g hn.2.1
  have hr : run (narrowSkywalkSwap L) m s=out := by
    have hsd := (skywalkSignDelta_counts L.g L.sx L.sy L.delta).2.1
    have hsw := (swapRegisters_resources L.g L.xlow L.ylow hv.low_lengths (L.low_nodup hv)).2.1
    have hsf := (signComplement_counts L.delta L.bank).2
    simp only [narrowSkywalkSwap,List.append_assoc]
    rw [route_prefix_no_measure _ _ hsd,route_prefix_no_measure _ _ hsw,
      route_prefix_no_measure _ _ hsf]
  rw [hr]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [ho,hvf]
    have hup : u.phase=s.phase := by
      have hh := congrArg State.phase hu
      exact hh
    exact tp.trans hup
  · intro q hqx hqy
    by_cases hqd : q=L.delta
    · subst q
      rw [ho]
      simp [writeBit,hd]
    have hxl : q∉L.xlow := fun h => hqx (List.mem_append_left _ h)
    have hyl : q∉L.ylow := fun h => hqy (List.mem_append_left _ h)
    have hb : q∉L.bank := by
      intro hm
      rcases List.mem_append.mp hm with hx|hy
      · exact hqx (List.mem_append_right _ hx)
      · exact hqy (List.mem_append_right _ hy)
    rw [ho,hvf]
    simp only [writeBit,Function.update_of_ne hqd,if_neg hb]
    exact (tf q hxl hyl).trans (uother q hqd)
  · simp only [NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,regValue_append,
      ox,tx,ug,ux,uy,obx,sbx,sby]
    cases s.basis L.g <;> simp [hv.low_lengths,hbanklen]
  · simp only [NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,regValue_append,
      oy,ty,ug,ux,uy,oby,sbx,sby]
    cases s.basis L.g <;> simp [hv.low_lengths,hbanklen]
  · constructor
    · intro q hq
      exact (ogx q hq).trans (ogx L.sx (by simp [NarrowSkywalkSwapLayout.xbank])).symm
    · intro q hq
      exact (ogy q hq).trans (ogy L.sy (by simp [NarrowSkywalkSwapLayout.ybank])).symm

/-- Scoped full-State equivalence with the actual wide Fredkin program.
The two record lists are independent; the temporary carry site returns to0. -/
theorem narrowSkywalkSwap_eq (L : NarrowSkywalkSwapLayout) (hv : L.Valid)
    (s : State) (m₁ m₂ : List Bool) (hd : s.basis L.delta=false) (hc : L.Copies s.basis) :
    run (narrowSkywalkSwap L) m₁ s=run (swapRegisters L.g L.x L.y) m₂ s := by
  obtain ⟨np,nf,nx,ny,_⟩ := narrowSkywalkSwap_correct L hv s m₁ hd hc
  obtain ⟨wp,wf,wx,wy⟩ := swapRegisters_correct L.g L.x L.y (L.lengths hv)
    (L.full_nodup hv) s m₂
  apply congrArg₂ State.mk
  · exact np.trans wp.symm
  · funext q
    by_cases hx : q∈L.x
    · exact (regValue_eq_iff _ _ _).mp (nx.trans wx.symm) q hx
    by_cases hy : q∈L.y
    · exact (regValue_eq_iff _ _ _).mp (ny.trans wy.symm) q hy
    exact (nf q hx hy).trans (wf q hx hy).symm

/-- One sign-delta Toffoli replaces the retained sign and every high Fredkin.
Measured cleanup costs one M, with no additional Toffoli. -/
theorem narrowSkywalkSwap_counts (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    toffoliCount (narrowSkywalkSwap L)=L.xlow.length+1 ∧
    measurementCount (narrowSkywalkSwap L)=1 := by
  have hd := skywalkSignDelta_counts L.g L.sx L.sy L.delta
  have hs := swapRegisters_resources L.g L.xlow L.ylow hv.low_lengths (L.low_nodup hv)
  have hf := signComplement_counts L.delta L.bank
  simp only [narrowSkywalkSwap,toffoliCount_append,measurementCount_append,
    hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,hs.1,hs.2.1,hf.1,hf.2]
  constructor
  · omega
  · trivial


private theorem route_suffix_no_measure (p q : Program) (hq : measurementCount q=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  rw [run_append,run_take]
  have h1 := run_take q (m.drop (measurementCount p)) (run p m s)
  have h2 := run_take q m (run p m s)
  rw [hq,List.take_zero] at h1 h2
  exact h1.symm.trans h2

/-- Actual Skywalk route with the original parity-history/odd-low operation. -/
def narrowSkywalkRoute (L : NarrowSkywalkSwapLayout) (b0 : Wire) : Program :=
  narrowSkywalkSwap L ++ [.CX L.g b0]

theorem narrowSkywalkRoute_eq (L : NarrowSkywalkSwapLayout) (hv : L.Valid) (b0 : Wire)
    (s : State) (m₁ m₂ : List Bool) (hd : s.basis L.delta=false) (hc : L.Copies s.basis) :
    run (narrowSkywalkRoute L b0) m₁ s=run (skywalkRoute L.g b0 L.x L.y) m₂ s := by
  rw [narrowSkywalkRoute,skywalkRoute,
    route_suffix_no_measure _ _ (by rfl : measurementCount [.CX L.g b0]=0),
    route_suffix_no_measure _ _ (by rfl : measurementCount [.CX L.g b0]=0)]
  rw [narrowSkywalkSwap_eq L hv s m₁ m₂ hd hc]
  rfl

theorem narrowSkywalkRoute_counts (L : NarrowSkywalkSwapLayout) (hv : L.Valid) (b0 : Wire) :
    toffoliCount (narrowSkywalkRoute L b0)=L.xlow.length+1 ∧
    measurementCount (narrowSkywalkRoute L b0)=1 := by
  have h := narrowSkywalkSwap_counts L hv
  simp [narrowSkywalkRoute,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,h.1,h.2]

private theorem route_delta_support (g a b d : Wire) :
    wires (skywalkSignDelta g a b d)⊆[g,a,b,d].toFinset ∧
    wires (skywalkSignDeltaErase g a b d)⊆[g,a,b,d].toFinset := by
  constructor <;> intro q hq
  all_goals
    simp only [skywalkSignDelta,skywalkSignDeltaErase,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
      List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto

theorem narrowSkywalkSwap_support (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    wires (narrowSkywalkSwap L)⊆L.wires.toFinset := by
  have hd := route_delta_support L.g L.sx L.sy L.delta
  have ha : [L.g,L.sx,L.sy,L.delta].toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [NarrowSkywalkSwapLayout.wires,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
      NarrowSkywalkSwapLayout.xbank,NarrowSkywalkSwapLayout.ybank,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hs : wires (swapRegisters L.g L.xlow L.ylow)⊆L.wires.toFinset := by
    intro q hq
    have hh := swapRegisters_wires L.g L.xlow L.ylow hv.low_lengths hq
    simp only [NarrowSkywalkSwapLayout.wires,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
      List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
    tauto
  have hf : wires (signComplement L.delta L.bank)⊆L.wires.toFinset := by
    intro q hq
    have hh := signComplement_wires_subset L.delta L.bank hq
    simp only [NarrowSkywalkSwapLayout.wires,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
      NarrowSkywalkSwapLayout.bank,List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
    tauto
  simp only [narrowSkywalkSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨hd.1.trans ha,hs⟩,hf⟩,hd.2.trans ha⟩

theorem narrowSkywalkRoute_support (L : NarrowSkywalkSwapLayout) (hv : L.Valid) (b0 : Wire) :
    wires (narrowSkywalkRoute L b0)⊆(b0::L.wires).toFinset := by
  have hs := narrowSkywalkSwap_support L hv
  intro q hq
  simp only [narrowSkywalkRoute,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · exact List.mem_toFinset.mpr (List.mem_cons_of_mem b0 (List.mem_toFinset.mp (hs hq)))
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,NarrowSkywalkSwapLayout.wires]
    tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NarrowSkywalkRouteTick.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic

private theorem route_take_msb (r : List Wire) (n : Nat) (hn : 0<n) (hle : n≤r.length) :
    r.take (n-1)++[r.getD (n-1) 0]=r.take n := by
  have hidx : n-1<r.length := by omega
  have he : n=(n-1)+1 := by omega
  conv_rhs => rw [he]
  rw [List.getD_eq_getElem _ _ hidx,List.take_add_one,List.getElem?_eq_getElem hidx]
  rfl

/-- A reused carry bit supplies delta; the reference signs are retained bits,
so all omitted high bits and the signs themselves use the Clifford fanout. -/
def narrowSkywalkRouteLayout (L : SkywalkIntegerLayout) (n : Nat) : NarrowSkywalkSwapLayout :=
  {g:=L.a0,delta:=L.carry.headD 0,
   sx:=L.ah.getD (n-2) 0,sy:=L.bh.getD (n-2) 0,
   xlow:=L.ah.take (n-2),ylow:=L.bh.take (n-2),
   xhigh:=L.ah.drop (n-1),yhigh:=L.bh.drop (n-1)}

theorem narrowSkywalkRoute_views (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 2≤n) (hle : n≤L.a.length) :
    (narrowSkywalkRouteLayout L n).x=L.ah ∧ (narrowSkywalkRouteLayout L n).y=L.bh := by
  have hl := L.high_lengths hv
  have hal : L.a.length=L.ah.length+1 := by simp [SkywalkIntegerLayout.a]
  have he : (n-1)-1=n-2 := by omega
  have hx := route_take_msb L.ah (n-1) (by omega) (by omega)
  have hy := route_take_msb L.bh (n-1) (by omega) (by omega)
  rw [he] at hx hy
  simp only [narrowSkywalkRouteLayout,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
    NarrowSkywalkSwapLayout.xbank,NarrowSkywalkSwapLayout.ybank]
  constructor
  · calc
      _ = (L.ah.take (n-2)++[L.ah.getD (n-2) 0])++L.ah.drop (n-1) := by rw [List.append_assoc,List.singleton_append]
      _ = L.ah := by rw [hx,List.take_append_drop]
  · calc
      _ = (L.bh.take (n-2)++[L.bh.getD (n-2) 0])++L.bh.drop (n-1) := by rw [List.append_assoc,List.singleton_append]
      _ = L.bh := by rw [hy,List.take_append_drop]

theorem narrowSkywalkRoute_delta_mem (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.carry.headD 0∈L.carry := by
  have hl := L.record_lengths hv
  have hpos : 0<L.ah.length := by simp [SkywalkIntegerLayout.ah]
  have hc : L.carry.length=L.ah.length := by
    simp only [SkywalkIntegerLayout.half,List.length_append,List.length_singleton] at hl
    omega
  cases he : L.carry with
  | nil => simp only [he,List.length_nil] at hc; omega
  | cons a r => simp

theorem narrowSkywalkRoute_valid (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 2≤n) (hle : n≤L.a.length) : (narrowSkywalkRouteLayout L n).Valid := by
  have hl := L.high_lengths hv
  have vv := narrowSkywalkRoute_views L hv n hn hle
  constructor
  · simp [narrowSkywalkRouteLayout,List.length_take,hl]
  · simp [narrowSkywalkRouteLayout,List.length_drop,hl]
  · simp only [NarrowSkywalkSwapLayout.wires,vv.1,vv.2]
    change (L.a0::L.carry.headD 0::(L.ah++L.bh)).Nodup
    apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp hv.nodup q
    have hhead : (if L.carry.headD 0==q then 1 else 0)≤L.carry.count q := by
      by_cases he : L.carry.headD 0=q
      · have hp := List.count_pos_iff.mpr (he ▸ narrowSkywalkRoute_delta_mem L hv)
        simp only [he,beq_self_eq_true,if_true]
        omega
      · simp only [beq_iff_eq,if_neg he,Nat.zero_le]
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hc ⊢
    omega

/-- A signed full rail fitting the retained width has its exact prefix value
and every omitted bit equal to the retained sign reference. -/
theorem narrowSkywalkRoute_copies (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 2≤n) (hle : n≤L.a.length) (A B : Int) (s : BasisState)
    (ha : signedRegValue L.a s=A) (hb : signedRegValue L.b s=B)
    (ha0 : -((2^(n-1):Nat):Int)≤A) (ha1 : A<((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int)≤B) (hb1 : B<((2^(n-1):Nat):Int)) :
    (narrowSkywalkRouteLayout L n).Copies s := by
  let R := narrowSkywalkRouteLayout L n
  have vv := narrowSkywalkRoute_views L hv n hn hle
  have hal : L.a.length=L.ah.length+1 := by simp [SkywalkIntegerLayout.a]
  have hxlen : (L.a0::R.xlow++[R.sx]).length=n := by
    simp only [R,narrowSkywalkRouteLayout,List.length_append,List.length_cons,
      List.length_nil,List.length_take]
    omega
  have hylen : (L.b0::R.ylow++[R.sy]).length=n := by
    have hl := L.high_lengths hv
    simp only [R,narrowSkywalkRouteLayout,List.length_append,List.length_cons,
      List.length_nil,List.length_take]
    omega
  have hax : signedRegValue ((L.a0::R.xlow++[R.sx])++R.xhigh) s=A := by
    simp only [List.append_assoc]
    change signedRegValue (L.a0::R.x) s=A
    rw [vv.1]
    exact ha
  have hby : signedRegValue ((L.b0::R.ylow++[R.sy])++R.yhigh) s=B := by
    simp only [List.append_assoc]
    change signedRegValue (L.b0::R.y) s=B
    rw [vv.2]
    exact hb
  have hxa := narrow_signed_prefix (L.a0::R.xlow++[R.sx]) R.xhigh s A (by omega)
    hax (by simpa only [hxlen] using ha0) (by simpa only [hxlen] using ha1)
  have hyb := narrow_signed_prefix (L.b0::R.ylow++[R.sy]) R.yhigh s B (by omega)
    hby (by simpa only [hylen] using hb0) (by simpa only [hylen] using hb1)
  have hsx := signedRegValue_sign (L.a0::R.xlow) R.sx s
  have hsy := signedRegValue_sign (L.b0::R.ylow) R.sy s
  rw [hxa.1] at hsx
  rw [hyb.1] at hsy
  constructor
  · intro q hq
    rcases List.mem_cons.mp hq with he|hq
    · subst q; rfl
    · exact (hxa.2 q hq).trans hsx.symm
  · intro q hq
    rcases List.mem_cons.mp hq with he|hq
    · subst q; rfl
    · exact (hyb.2 q hq).trans hsy.symm

/-- One extra signed input bit protects the inclusive pre-half product cap. -/
def narrowSkywalkRouteWidth (i : Nat) : Nat := min 258 (514-i)

theorem narrowSkywalkRouteWidth_bounds (i : Nat) (hi : i<512) :
    3≤narrowSkywalkRouteWidth i ∧ narrowSkywalkRouteWidth i≤258 ∧
    narrowSkywalkRouteWidth i-1=min 257 (513-i) := by
  unfold narrowSkywalkRouteWidth
  omega

/-- Complete universal input fit for the route. Early states use the strict
initial sum; late states double the inclusive product/sum cap. -/
theorem narrowSkywalkRoute_iter_fit (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpo : p%2=1) (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    let n := narrowSkywalkRouteWidth i;
    -((2^(n-1):Nat):Int)≤r.a ∧ r.a<((2^(n-1):Nat):Int) ∧
    -((2^(n-1):Nat):Int)≤r.b ∧ r.b<((2^(n-1):Nat):Int) := by
  dsimp only
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at he
  rw [he]
  have hb := SkywalkRails.encode_abs_sum_bound G S z.u z.v (z.u+z.v) (Nat.le_refl _)
  have hsum : z.u+z.v<2^(narrowSkywalkRouteWidth i-1) := by
    by_cases hi0 : i≤256
    · have hn : narrowSkywalkRouteWidth i=258 := by unfold narrowSkywalkRouteWidth; omega
      rw [hn]
      exact SkywalkNat.iter_sum_initial_width p x 256 i hp hx
    · have hn : narrowSkywalkRouteWidth i-1=(512-i)+1 := by unfold narrowSkywalkRouteWidth; omega
      rw [hn,pow_succ]
      have hc := SkywalkNat.iter_sum_product_width p x 256 i hp0 hx0 hpo hp hx hc (by omega)
      change z.u+z.v≤2^(512-i) at hc
      have hpos : 0<2^(512-i) := by positivity
      omega
  have hsum' : ((z.u+z.v:Nat):Int)<((2^(narrowSkywalkRouteWidth i-1):Nat):Int) := by
    exact_mod_cast hsum
  have ha := abs_le.mp hb.1
  have hb' := abs_le.mp hb.2
  change -((2^(narrowSkywalkRouteWidth i-1):Nat):Int)≤(SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a ∧
    (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a<((2^(narrowSkywalkRouteWidth i-1):Nat):Int) ∧
    -((2^(narrowSkywalkRouteWidth i-1):Nat):Int)≤(SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b ∧
    (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b<((2^(narrowSkywalkRouteWidth i-1):Nat):Int)
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- Replacing a zero-M prefix by an exactly equal one-M prefix shifts only the
remaining stream. The reference record list is never falsely aligned. -/
private theorem route_measured_prefix (p q tail : Program) (hp : measurementCount p=1)
    (hq : measurementCount q=0) (s : State) (m : List Bool)
    (he : ∀ rec,run p rec s=run q [] s) :
    run (p++tail) m s=run (q++tail) (m.drop 1) s := by
  rw [run_append,run_append,hp,hq,List.take_zero,List.drop_zero,he]

/-- The complete full-half/narrow-adder suffix is untouched. -/
def narrowSkywalkRoutedTick (L : SkywalkIntegerLayout) (nr na : Nat) : Program :=
  narrowSkywalkRoute (narrowSkywalkRouteLayout L nr) L.b0 ++
    (skywalkSignedHalf L.aSign L.ext ++
      narrowSignedRecord (narrowSkywalkRecordLayout L na) na ++ [.CX L.previous L.a0])

/-- Whole-State tick equality with the accepted narrow-adder path; exactly
one prefix measurement is consumed before its independent arithmetic stream. -/
theorem narrowSkywalkRoutedTick_eq (L : SkywalkIntegerLayout) (hv : L.Valid) (nr na : Nat)
    (hn : 2≤nr) (hle : nr≤L.a.length) (s : State) (m : List Bool)
    (hd : s.basis (L.carry.headD 0)=false)
    (hc : (narrowSkywalkRouteLayout L nr).Copies s.basis) :
    run (narrowSkywalkRoutedTick L nr na) m s=run (narrowSkywalkTick L na) (m.drop 1) s := by
  have vv := narrowSkywalkRoute_views L hv nr hn hle
  have hvR := narrowSkywalkRoute_valid L hv nr hn hle
  have hh := narrowSkywalkRoute_counts _ hvR L.b0
  have hm := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh (L.high_lengths hv) (L.route_nodup hv)).2
  have he : ∀ rec,run (narrowSkywalkRoute (narrowSkywalkRouteLayout L nr) L.b0) rec s=
      run (skywalkRoute L.a0 L.b0 L.ah L.bh) [] s := by
    intro rec
    have ho := narrowSkywalkRoute_eq _ hvR L.b0 s rec [] hd hc
    simpa only [vv.1,vv.2] using ho
  simp only [narrowSkywalkRoutedTick,narrowSkywalkTick,List.append_assoc]
  exact route_measured_prefix _ _ _ hh.2 hm s m he

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NarrowSkywalkRouteInverse.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- Independent measured inverse route: recover the original low parity
before performing the same exact sign-bank swap with a fresh record. -/
def narrowSkywalkUnroute (L : NarrowSkywalkSwapLayout) (b0 : Wire) : Program :=
  [.CX L.g b0] ++ narrowSkywalkSwap L

private def routedBody (L : SkywalkIntegerLayout) (na : Nat) : Program :=
  skywalkSignedHalf L.aSign L.ext ++
    narrowSignedRecord (narrowSkywalkRecordLayout L na) na ++ [.CX L.previous L.a0]

private def routedBodyInverse (L : SkywalkIntegerLayout) (na : Nat) : Program :=
  [.CX L.previous L.a0] ++ narrowSignedUnrecord (narrowSkywalkRecordLayout L na) na ++
    skywalkSignedHalf L.aSign L.ext

/-- The independently emitted full untick keeps full signed half and reverses
only the actual retained-prefix arithmetic and sign-bank route streams. -/
def narrowSkywalkRoutedUntick (L : SkywalkIntegerLayout) (nr na : Nat) : Program :=
  routedBodyInverse L na ++ narrowSkywalkUnroute (narrowSkywalkRouteLayout L nr) L.b0

private theorem routed_route_support (L : SkywalkIntegerLayout) (hv : L.Valid) (nr : Nat)
    (hnr : 2≤nr) (hrlen : nr≤L.a.length) :
    wires (narrowSkywalkRoute (narrowSkywalkRouteLayout L nr) L.b0)⊆L.wires.toFinset ∧
    wires (narrowSkywalkUnroute (narrowSkywalkRouteLayout L nr) L.b0)⊆L.wires.toFinset := by
  let R := narrowSkywalkRouteLayout L nr
  have hvR := narrowSkywalkRoute_valid L hv nr hnr hrlen
  have vv := narrowSkywalkRoute_views L hv nr hnr hrlen
  have hs := narrowSkywalkRoute_support R hvR L.b0
  have ha : (L.b0::R.wires).toFinset⊆L.wires.toFinset := by
    intro q hq
    have hm := narrowSkywalkRoute_delta_mem L hv
    dsimp only [R] at hq
    simp only [NarrowSkywalkSwapLayout.wires,vv.1,vv.2] at hq
    change q∈(L.b0::L.a0::L.carry.headD 0::(L.ah++L.bh)).toFinset at hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    rcases hq with he|he|he|he
    · subst q; simp
    · subst q; simp
    · subst q; tauto
    · tauto
  have hswap := narrowSkywalkSwap_support R hvR
  constructor
  · exact hs.trans ha
  · intro q hq
    simp only [narrowSkywalkUnroute,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · apply ha
      simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.notMem_empty,or_false] at hq
      simp only [List.mem_toFinset,List.mem_cons,NarrowSkywalkSwapLayout.wires]
      tauto
    · exact ha (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hswap hq))))

/-- Both actual new directions remain inside the existing rail/history/carry
layout. Borrowing the already-zero carry head adds no physical site. -/
theorem narrowSkywalkRoutedTick_support (L : SkywalkIntegerLayout) (hv : L.Valid) (nr na : Nat)
    (hnr : 2≤nr) (hrlen : nr≤L.a.length) (hna : 0<na) (halen : na≤L.half.length) :
    wires (narrowSkywalkRoutedTick L nr na)⊆L.wires.toFinset ∧
    wires (narrowSkywalkRoutedUntick L nr na)⊆L.wires.toFinset := by
  have hroute := routed_route_support L hv nr hnr hrlen
  have hold := narrowSkywalkTick_wires_subset L hv na hna halen
  have hbody : wires (routedBody L na)⊆L.wires.toFinset := by
    intro q hq
    apply hold.1
    simp only [narrowSkywalkTick,routedBody,wires_append,Finset.mem_union] at hq ⊢
    tauto
  have hbodyInverse : wires (routedBodyInverse L na)⊆L.wires.toFinset := by
    intro q hq
    apply hold.2
    simp only [narrowSkywalkUntick,routedBodyInverse,wires_append,Finset.mem_union] at hq ⊢
    tauto
  change wires (_++routedBody L na)⊆_ ∧ wires (routedBodyInverse L na++_)⊆_
  simp only [wires_append,Finset.union_subset_iff]
  exact ⟨⟨hroute.1,hbody⟩,hbodyInverse,hroute.2⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NarrowSkywalkRoutedLoopCore.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- Keep the original zero-M route at full width; only profitable late routes
use the exact sign-bank helper. All512 actual ticks are still emitted. -/
def narrowSkywalkScheduledTick (w : Nat → Wire) (i : Nat) : Program :=
  if narrowSkywalkRouteWidth i=258 then
    narrowSkywalkTick (skywalkPoolTick w i) (narrowSkywalkWidth i)
  else narrowSkywalkRoutedTick (skywalkPoolTick w i)
    (narrowSkywalkRouteWidth i) (narrowSkywalkWidth i)

def narrowSkywalkScheduledUntick (w : Nat → Wire) (i : Nat) : Program :=
  if narrowSkywalkRouteWidth i=258 then
    narrowSkywalkUntick (skywalkPoolTick w i) (narrowSkywalkWidth i)
  else narrowSkywalkRoutedUntick (skywalkPoolTick w i)
    (narrowSkywalkRouteWidth i) (narrowSkywalkWidth i)

def narrowSkywalkRoutedLoop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => narrowSkywalkScheduledTick w i ++ narrowSkywalkRoutedLoop w (i+1) n

def narrowSkywalkRoutedUnloop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => narrowSkywalkRoutedUnloop w (i+1) n ++ narrowSkywalkScheduledUntick w i

attribute [local irreducible] narrowSkywalkTick narrowSkywalkUntick
attribute [local irreducible] narrowSkywalkRoutedTick narrowSkywalkRoutedUntick
attribute [local irreducible] narrowSkywalkScheduledTick narrowSkywalkScheduledUntick
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run
attribute [local irreducible] SkywalkTrace.next Nat.iterate

private theorem routed_index_lengths (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).a.length=258 ∧ (skywalkPoolTick w i).half.length=258 := by
  constructor
  · rw [skywalkPool_a,skywalkPoolA,wireBlock_length]
  · rw [skywalkPool_half,skywalkPoolA,wireBlock_length]

private theorem routed_index_copies (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i<512) (s : BasisState)
    (hs : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s) :
    (narrowSkywalkRouteLayout (skywalkPoolTick w i) (narrowSkywalkRouteWidth i)).Copies s := by
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  have hv := skywalkPool_valid w i hi hn
  have hr := narrowSkywalkRouteWidth_bounds i hi
  have hl := routed_index_lengths w i
  have hf := narrowSkywalkRoute_iter_fit x p i hp0 hx0 hpo hp hx hc hi
  apply narrowSkywalkRoute_copies _ hv _ (by omega) (by omega) r.a r.b s
  · rw [skywalkPool_a]
    exact hs.1
  · rw [skywalkPool_b]
    exact hs.2.1
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2

/-- Exact complete Stage advancement for the actual full-route/late-route
schedule; every parity/sign history and clean future site is retained. -/
theorem narrowSkywalkRoutedStage_step (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    let r := SkywalkRails.encode false false (x:Int) (p:Int)
    Triple (SkywalkIntegerStage w r i) (narrowSkywalkScheduledTick w i)
      (SkywalkIntegerStage w r (i+1)) := by
  dsimp only
  by_cases he : narrowSkywalkRouteWidth i=258
  · rw [narrowSkywalkScheduledTick,if_pos he]
    exact narrowSkywalkStage_step w hn x p i hp0 hx0 hpo hp hx hc hi
  · intro s m hs
    rw [narrowSkywalkScheduledTick,if_neg he]
    have hv := skywalkPool_valid w i hi hn
    have hr := narrowSkywalkRouteWidth_bounds i hi
    have hl := routed_index_lengths w i
    have hcopy := routed_index_copies w hn x p i hp0 hx0 hpo hp hx hc hi s.basis hs
    have hd : s.basis ((skywalkPoolTick w i).carry.headD 0)=false :=
      (regValue_zero _ _).mp hs.2.2.2.2.2.1 _ (narrowSkywalkRoute_delta_mem _ hv)
    rw [narrowSkywalkRoutedTick_eq _ hv _ _ (by omega) (by omega) s m hd hcopy]
    exact narrowSkywalkStage_step w hn x p i hp0 hx0 hpo hp hx hc hi s (m.drop 1) hs

section LoopSpec
attribute [local irreducible] SkywalkIntegerStage

theorem narrowSkywalkRoutedLoop_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i+n≤512) :
    let r := SkywalkRails.encode false false (x:Int) (p:Int)
    Triple (SkywalkIntegerStage w r i) (narrowSkywalkRoutedLoop w i n)
      (SkywalkIntegerStage w r (i+n)) := by
  dsimp only
  induction n generalizing i with
  | zero =>
    rw [narrowSkywalkRoutedLoop,Nat.add_zero]
    intro s m h
    simpa only [run] using (And.intro (rfl : s.phase=s.phase) h)
  | succ n ih =>
    have hstep := narrowSkywalkRoutedStage_step w hn x p i hp0 hx0 hpo hp hx hc (by omega)
    have htail := ih (i+1) (by omega)
    have hall := hstep.seq htail
    have hindex : i+(n+1)=(i+1)+n := by omega
    rw [narrowSkywalkRoutedLoop,hindex]
    exact hall

end LoopSpec

theorem narrowSkywalkScheduledTick_support (w : Nat → Wire) (i : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i<512) :
    wires (narrowSkywalkScheduledTick w i)⊆(skywalkPoolTick w i).wires.toFinset ∧
    wires (narrowSkywalkScheduledUntick w i)⊆(skywalkPoolTick w i).wires.toFinset := by
  have hv := skywalkPool_valid w i hi hn
  have hr := narrowSkywalkRouteWidth_bounds i hi
  have ha := narrowSkywalkWidth_bounds i hi
  have hl := routed_index_lengths w i
  by_cases he : narrowSkywalkRouteWidth i=258
  · simp only [narrowSkywalkScheduledTick,narrowSkywalkScheduledUntick,if_pos he]
    exact narrowSkywalkTick_wires_subset (skywalkPoolTick w i) hv (narrowSkywalkWidth i) (by omega) (by omega)
  · simp only [narrowSkywalkScheduledTick,narrowSkywalkScheduledUntick,if_neg he]
    exact narrowSkywalkRoutedTick_support (skywalkPoolTick w i) hv (narrowSkywalkRouteWidth i) (narrowSkywalkWidth i) (by omega) (by omega) (by omega) (by omega)

theorem narrowSkywalkRoutedLoop_support (w : Nat → Wire) (i n : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i+n≤512) :
    wires (narrowSkywalkRoutedLoop w i n)⊆(skywalkPoolWires w).toFinset ∧
    wires (narrowSkywalkRoutedUnloop w i n)⊆(skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,wires]
  | succ n ih =>
    have hbound : i<512 := by omega
    have hc := narrowSkywalkScheduledTick_support w i hn hbound
    have h1 := skywalkPool_program_support w i hbound _ hc.1
    have h2 := skywalkPool_program_support w i hbound _ hc.2
    have ht := ih (i+1) (by omega)
    simp only [narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,wires_append,Finset.union_subset_iff]
    exact ⟨⟨h1,ht.1⟩,ht.2,h2⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NarrowSkywalkRoutedLoop.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] narrowSkywalkScheduledTick narrowSkywalkScheduledUntick
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] SkywalkTrace.next Nat.iterate run SkywalkIntegerStage

theorem narrowSkywalkRouted512_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) :
    let r := SkywalkRails.encode false false (x : Int) (p : Int)
    Triple (SkywalkIntegerStage w r 0) (narrowSkywalkRoutedLoop w 0 512)
      (SkywalkIntegerStage w r 512) :=
  narrowSkywalkRoutedLoop_spec w hn x p 0 512 hp0 hx0 hpo hp hx hc (by omega)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkTerminal.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- A terminal signed trajectory has rails (0,1) or (1,0), with orientation
stored separately. Clear both low bits so the entire rail workspace can be
borrowed during field replay. The same Clifford program restores the rails. -/
def skywalkTerminalClear (g a b : Wire) : Program := [.CX g a,.X a,.CX g b]

theorem skywalkTerminalClear_correct (g a b : Wire) (hn : [g,a,b].Nodup)
    (s : State) (m : List Bool) :
    (run (skywalkTerminalClear g a b) m s).phase=s.phase ∧
    (∀ q, q≠a → q≠b → (run (skywalkTerminalClear g a b) m s).basis q=s.basis q) ∧
    (run (skywalkTerminalClear g a b) m s).basis a=(!(s.basis a ^^ s.basis g)) ∧
    (run (skywalkTerminalClear g a b) m s).basis b=(s.basis b ^^ s.basis g) := by
  have hd : g≠a ∧ g≠b ∧ a≠b := by simpa [and_assoc] using hn
  refine ⟨rfl,?_,?_,?_⟩
  · intro q hqa hqb
    simp [skywalkTerminalClear,run,writeBit,hqa,hqb]
  · simp [skywalkTerminalClear,run,writeBit,hd.1,hd.2.2]
  · simp [skywalkTerminalClear,run,writeBit,hd.1,Ne.symm hd.2.2]

theorem skywalkTerminalClear_spec (g a b : Wire) (hn : [g,a,b].Nodup) (G : Bool) :
    (Triple (fun st => (Holds.holds st g G ∧ Holds.holds st a (!G)) ∧ Holds.holds st b G) (skywalkTerminalClear g a b)
      (fun st => (Holds.holds st g G ∧ Holds.holds st a false) ∧ Holds.holds st b false)) := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hd : g≠a ∧ g≠b ∧ a≠b := by simpa [and_assoc] using hn
  obtain ⟨hp,he,ha,hb⟩ := skywalkTerminalClear_correct g a b hn s m
  refine ⟨hp,⟨(he g hd.1 hd.2.1).trans h.1.1,?_⟩,?_⟩
  · rw [ha,h.1.2,h.1.1]
    cases G <;> rfl
  · rw [hb,h.2,h.1.1]
    cases G <;> rfl

theorem skywalkTerminalClear_twice (g a b : Wire) (hn : [g,a,b].Nodup)
    (s : State) (m1 m2 : List Bool) :
    run (skywalkTerminalClear g a b) m2 (run (skywalkTerminalClear g a b) m1 s)=s := by
  have hd : g≠a ∧ g≠b ∧ a≠b := by simpa [and_assoc] using hn
  obtain ⟨p1,e1,a1,b1⟩ := skywalkTerminalClear_correct g a b hn s m1
  obtain ⟨p2,e2,a2,b2⟩ := skywalkTerminalClear_correct g a b hn
    (run (skywalkTerminalClear g a b) m1 s) m2
  have hg := e1 g hd.1 hd.2.1
  apply congrArg₂ State.mk
  · exact p2.trans p1
  · funext q
    change (run (skywalkTerminalClear g a b) m2
      (run (skywalkTerminalClear g a b) m1 s)).basis q=s.basis q
    by_cases hqa : q=a
    · subst q
      rw [a2,a1,hg]
      cases s.basis a <;> cases s.basis g <;> rfl
    by_cases hqb : q=b
    · subst q
      rw [b2,b1,hg]
      cases s.basis b <;> cases s.basis g <;> rfl
    exact (e2 q hqa hqb).trans (e1 q hqa hqb)

/-- Whole-word interface: all high bits are already zero because each rail
has value zero or one. No high-word conditional swap is required. -/
theorem skywalkTerminalClear_words (g a b : Wire) (aTail bTail : List Wire)
    (hn : (g::a::b::(aTail++bTail)).Nodup) (G : Bool) :
    (Triple (fun st => (Holds.holds st g G ∧ Holds.holds st (a::aTail) (if G then 0 else 1)) ∧ Holds.holds st (b::bTail) (if G then 1 else 0)) (skywalkTerminalClear g a b)
      (fun st => (Holds.holds st g G ∧ Holds.holds st (a::aTail) 0) ∧ Holds.holds st (b::bTail) 0)) := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hgates : [g,a,b].Nodup := by
    have hh := hn
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or] at hh
    simp [hh.1.1,hh.1.2.1,hh.2.1.1]
  have hav := h.1.2
  have hbv := h.2
  change (if s.basis a then 1 else 0)+2*regValue aTail s.basis=(if G then 0 else 1) at hav
  change (if s.basis b then 1 else 0)+2*regValue bTail s.basis=(if G then 1 else 0) at hbv
  have ha0 : s.basis a=(!G) ∧ regValue aTail s.basis=0 := by
    cases G <;> cases ha : s.basis a <;> simp [ha] at hav ⊢ <;> omega
  have hb0 : s.basis b=G ∧ regValue bTail s.basis=0 := by
    cases G <;> cases hb : s.basis b <;> simp [hb] at hbv ⊢ <;> omega
  obtain ⟨hp,hpost⟩ := skywalkTerminalClear_spec g a b hgates G s m ⟨⟨h.1.1,ha0.1⟩,hb0.1⟩
  have keep (q : Wire) (hq : q∈aTail++bTail) :
      (run (skywalkTerminalClear g a b) m s).basis q=s.basis q := by
    have hq0 : q≠a ∧ q≠b := by
      have hd := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      have hb := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1
      constructor
      · intro he
        subst q
        exact hd (List.mem_cons_of_mem _ hq)
      · intro he
        subst q
        exact hb hq
    exact (skywalkTerminalClear_correct g a b hgates s m).2.1 q hq0.1 hq0.2
  have hat := (regValue_congr aTail _ _ (fun q hq => keep q (List.mem_append_left _ hq))).trans ha0.2
  have hbt := (regValue_congr bTail _ _ (fun q hq => keep q (List.mem_append_right _ hq))).trans hb0.2
  simp only [Holds.holds] at hpost
  refine ⟨hp,⟨hpost.1.1,?_⟩,?_⟩
  · change (if (run (skywalkTerminalClear g a b) m s).basis a then 1 else 0)+
      2*regValue aTail (run (skywalkTerminalClear g a b) m s).basis=0
    rw [hpost.1.2,hat]
    rfl
  · change (if (run (skywalkTerminalClear g a b) m s).basis b then 1 else 0)+
      2*regValue bTail (run (skywalkTerminalClear g a b) m s).basis=0
    rw [hpost.2,hbt]
    rfl

theorem skywalkTerminalClear_counts (g a b : Wire) :
    toffoliCount (skywalkTerminalClear g a b)=0 ∧
    measurementCount (skywalkTerminalClear g a b)=0 := by
  simp [skywalkTerminalClear,toffoliCount,measurementCount]

theorem skywalkTerminalClear_wires (g a b : Wire) :
    wires (skywalkTerminalClear g a b)=[g,a,b].toFinset := by
  ext q
  simp [skywalkTerminalClear,wires,Instr.wires]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkArithmeticCore.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- The original public divisor and numerator ports, each exactly 256 bits. -/
def skywalkArithmeticDivisor (w : Nat → Wire) := wireBlock w 770 256
def skywalkArithmeticNumerator (w : Nat → Wire) := wireBlock w 2056 256

def SkywalkArithmeticInput (w : Nat → Wire) (x y : Nat) (s : BasisState) : Prop :=
  regValue (skywalkArithmeticDivisor w) s=x ∧
  regValue (skywalkArithmeticNumerator w) s=y ∧
  ∀ q∈skywalkSharedWires w,q∉skywalkArithmeticDivisor w →
    q∉skywalkArithmeticNumerator w → s q=false

def skywalkArithmeticClear (w : Nat → Wire) : Program :=
  skywalkTerminalClear (w 511) (w 512) (w 770)

attribute [local irreducible] skywalkSeed skywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] run

def skywalkArithmeticResult (divide : Bool) (x : Nat) (Y : Fp) : Fp :=
  if divide then Y/(x : Fp) else Y*(x : Fp)

attribute [local irreducible] SkywalkTrace.next Nat.iterate

/-- Pure interpreter composition. The callback is discharged by the concrete
state theorem; this lemma introduces no circuit oracle or input assumption. -/
theorem skywalkRunSeven (p1 p2 p3 p4 p5 p6 p7 : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 s5 s6 s7 : State) (m1 m2 m3 m4 m5 m6 m7 : List Bool),
      run p1 m1 s=s1 → run p2 m2 s1=s2 → run p3 m3 s2=s3 →
      run p4 m4 s3=s4 → run p5 m5 s4=s5 → run p6 m6 s5=s6 →
      run p7 m7 s6=s7 → P s s7) (s : State) (m : List Bool) :
    P s (run (p1++(p2++(p3++(p4++(p5++(p6++p7)))))) m s) := by
  simp only [run_append]
  apply h s _ _ _ _ _ _ _ _ _ _ _ _ _ _ <;> rfl

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupCircuitProof.lean
noncomputable section

set_option maxHeartbeats 900000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic.BalancedCleanup
open BalancedField

def Except (a : Wire) (s t : State) : Prop :=
  s.phase=t.phase ∧ ∀q,q≠a → s.basis q=t.basis q

 theorem inverse_except (p : Program) (hp : ProperProgram p) (a : Wire)
    (ha : a∉wires p) (s t : State) (m n : List Bool)
    (he : Except a t (run p m s)) : Except a (run p.reverse n t) s := by
  have hr := run_reverse_proper p hp s m n
  have hc := run_proper_congr p.reverse (properProgram_reverse p hp)
    t (run p m s) n n he.1 (by
      intro q hq
      rw [wires_reverse] at hq
      exact he.2 q (fun e => ha (e ▸ hq)))
  refine ⟨hc.1.trans (congrArg State.phase hr),?_⟩
  intro q hqa
  by_cases hq : q∈wires p.reverse
  · exact (hc.2 q hq).trans (congrArg (fun u : State => u.basis q) hr)
  · have a1 := run_preserves_outside p.reverse n t q hq
    have a2 := run_preserves_outside p.reverse n (run p m s) q hq
    exact a1.trans ((he.2 q hqa).trans (a2.symm.trans (congrArg (fun u : State => u.basis q) hr)))

 theorem clifford_parity_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.parity∉wires (prepareSign L) ∧ L.parity∉wires (prepareCompare L) := by
  have a := L.flagAway hn L.parity (by simp)
  have af := (List.nodup_cons.mp (L.flagsND hn)).1
  have ar : L.parity∉L.r := fun h => a (by simp [h])
  have ay : L.parity∉L.y := fun h => a (by simp [h])
  have acL : L.parity∉wires (signComplement L.lower L.r) := by
    intro h; have hh := signComplement_wires_subset L.lower L.r h
    simp only [List.mem_toFinset,List.mem_cons] at hh
    rcases hh with h|h
    · exact af (by simp [h])
    · exact ar h
  have acS : L.parity∉wires (signComplement L.sign L.y) := by
    intro h; have hh := signComplement_wires_subset L.sign L.y h
    simp only [List.mem_toFinset,List.mem_cons] at hh
    rcases hh with h|h
    · exact af (by simp [h])
    · exact ay h
  have acY : L.parity∉wires (signComplement L.lower L.y) := by
    intro h; have hh := signComplement_wires_subset L.lower L.y h
    simp only [List.mem_toFinset,List.mem_cons] at hh
    rcases hh with h|h
    · exact af (by simp [h])
    · exact ay h
  have rot : L.parity∉wires (rotateLeft L.r) := by
    rw [(rotate_wires L.r).2,(widths L hw).2.1]
    simpa using ar
  have ar0 : L.parity≠L.r0 := fun e => ar (by simp [Layout.r,Layout.low,e])
  have arm : L.parity≠L.rmsb := fun e => ar (by simp [Layout.r,e])
  have aym : L.parity≠L.ymsb := fun e => ay (by simp [Layout.y,e])
  have asl : L.parity≠L.sign ∧ L.parity≠L.lower := by
    simp only [List.mem_cons,not_or] at af
    tauto
  simp [prepareSign,prepareCompare,wires_append,wires,Instr.wires,
    acL,acS,acY,rot,ar0,arm,aym,asl.1,asl.2]

 theorem unnormalize_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    let t := run (unnormalize L) m s
    t.phase=s.phase ∧
    regValue L.low t.basis=(regValue L.low s.basis+positiveLiteral+(!s.basis L.lower).toNat)%2^255 ∧
    ∀q,q∉L.low → t.basis q=s.basis q := by
  let u : State := ⟨s.phase,writeBit s.basis L.lower (!s.basis L.lower)⟩
  have nd := L.normND hn
  have la : L.lower∉L.low := fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])
  have ol : L.one≠L.lower := by
    intro e; exact (List.nodup_cons.mp nd).1 (by simp [e])
  have cl (q : Wire) (hq : q∈L.carry) : q≠L.lower := by
    intro e; exact L.flagAway hn L.lower (by simp) (by simp [←e,hq])
  have clean : ∀q∈L.carry.take 254,u.basis q=false := by
    intro q hq; simp [u,writeBit,cl q (List.mem_of_mem_take hq),hc q (List.mem_of_mem_take hq)]
  have hu : regValue L.low u.basis=regValue L.low s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [u,writeBit,show q≠L.lower from fun e => la (e ▸ hq)])
  have w := widths L hw
  have add := literalConstAdd_correct L.low (L.carry.take 254) L.lower L.one positiveLiteral
    nd (by omega) u m (by simp [u,writeBit,ol,ho]) clean
  let v := run (literalConstAdd L.low (L.carry.take 254) L.lower L.one positiveLiteral) m u
  have vl : v.basis L.lower=!s.basis L.lower := by rw [add.2.1 L.lower la]; simp [u,writeBit]
  have execute : run (unnormalize L) m s=run [.X L.lower]
      (m.drop (measurementCount (literalConstAdd L.low (L.carry.take 254) L.lower L.one positiveLiteral))) v := by
    simp only [unnormalize,List.append_assoc,run_append,run_take,measurementCount,List.drop_zero]
    rfl
  rw [execute]
  refine ⟨add.1,?_,?_⟩
  · have last (ms : List Bool) : regValue L.low (run [.X L.lower] ms v).basis=regValue L.low v.basis :=
      regValue_congr _ _ _ (fun q hq => by simp [run,writeBit,show q≠L.lower from fun e => la (e ▸ hq)])
    rw [last,add.2.2,hu,w.1]
    simp [u,writeBit]
  · intro q hq
    by_cases e : q=L.lower
    · subst q
      have hx (ms : List Bool) : (run [.X L.lower] ms v).basis L.lower=!v.basis L.lower := by
        simp only [run,writeBit,Function.update_self]
      rw [hx,vl]
      simp
    · simp only [run,writeBit,Function.update_of_ne e]
      exact (add.2.1 q hq).trans (by simp [u,writeBit,e])

 theorem literals_sum : negativeLiteral+positiveLiteral+1=2^255 := by
  have hp := constants
  have hh := Int.toNat_of_nonneg (show 0≤h by omega)
  have hl := Int.toNat_of_nonneg (show 0≤h-1 by omega)
  have hb : h.toNat≤2^255 := by norm_num at ⊢; omega
  rw [negativeLiteral_value]
  unfold positiveLiteral
  omega

 theorem states (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool) (s1 s2 s3 s4 s5 s6 s7 : State)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false)
    (hA : s.basis L.parity=decide (q < |2*R-signedY B Y|))
    (hs1 : run (prepareSign L) m1 s=s1) (hs2 : run (normalize L) m2 s1=s2)
    (hs3 : run (prepareCompare L) m3 s2=s3)
    (hs4 : run (compareLt none L.y L.r L.carry L.one L.parity) m4 s3=s4)
    (hs5 : run (prepareCompare L).reverse m5 s4=s5)
    (hs6 : run (unnormalize L) m6 s5=s6) (hs7 : run (prepareSign L).reverse m7 s6=s7) :
    Except L.parity s7 s ∧ s7.basis L.parity=false := by
  have w := widths L hw
  have nd := L.normND hn
  have flags := L.flagsND hn
  have pa := clifford_parity_away L hw hn
  have ar : L.parity∉L.r := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have ay : L.parity∉L.y := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have al : L.parity≠L.lower := by have hh := (List.nodup_cons.mp flags).1; simp at hh; tauto
  have oa : L.one∉L.r := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have ol : L.one≠L.lower := by have hh := List.nodup_iff_count.mp flags L.one; simp [List.count_cons] at hh; intro e; simp [e] at hh; omega
  have sy : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have sl : L.sign≠L.lower := by have hh := List.nodup_iff_count.mp flags L.sign; simp [List.count_cons] at hh; intro e; simp [←e] at hh; omega
  have ca (q : Wire) (hq : q∈L.carry) : q∉L.r ∧ q≠L.lower := by
    have d := List.nodup_append'.mp (L.dataND hn)
    exact ⟨fun h => List.disjoint_left.mp d.2.2 h (by simp [hq]),
      fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])⟩
  have v1 := prepareSign_value L hw hn R hr s m1 hR hz
  rw [hs1] at v1
  have one1 : s1.basis L.one=false := (v1.2.2 _ oa ol).trans ho
  have clean1 : ∀q∈L.carry,s1.basis q=false := fun q hq => (v1.2.2 q (ca q hq).1 (ca q hq).2).trans (hc q hq)
  have Y1 : regValue L.y s1.basis=encodeWord 256 Y := by
    have d := List.nodup_append'.mp (L.dataND hn)
    exact (regValue_congr _ _ _ (fun q hq => v1.2.2 q
      (fun r => List.disjoint_left.mp d.2.2 r (by simp [hq]))
      (fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])))).trans hY
  have rm0 : s1.basis L.rmsb=false := by
    have hi := regValue_highBit L.low L.rmsb s1.basis
    rw [w.1] at hi
    change s1.basis L.rmsb=true ↔ 2^255≤regValue L.r s1.basis at hi
    rw [v1.1] at hi
    have b := magnitude_bounds R hr; have p := constants
    have cast := Int.toNat_of_nonneg b.1
    cases e : s1.basis L.rmsb
    · rfl
    · simp [e] at hi
      omega
  have low1 : regValue L.low s1.basis=(magnitude R).toNat := by
    have h := v1.1; rw [Layout.r,regValue_append] at h; simpa [regValue,rm0] using h
  have v2 := normalize_value L hw hn R hr s1 m2 low1 v1.2.1 one1 clean1
  rw [hs2] at v2
  have rmAway : L.rmsb∉L.low := by have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).1; exact fun h => List.disjoint_left.mp d.2.2 h (by simp)
  have R2 : regValue L.r s2.basis=encodeWord 255 (normalizedR R) := by
    rw [Layout.r,regValue_append,v2.2.1]; simp [regValue,v2.2.2 _ rmAway,rm0]
  have Y2 : regValue L.y s2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => v2.2.2 q (by
      intro hl; exact List.disjoint_left.mp (List.nodup_append'.mp (L.dataND hn)).2.2
        (show q∈L.r from by simp [Layout.r,hl])
        (show q∈L.y++L.carry from by simp [hq])))).trans Y1
  have S2 : s2.basis L.sign=B := (v2.2.2 _ (fun h => sy (by simp [Layout.r,h]))).trans ((v1.2.2 _ sy sl).trans hS)
  have L2 : s2.basis L.lower=negative R := (v2.2.2 _ (fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h]))).trans v1.2.1
  have v3 := prepareCompare_value L hw hn R Y B hr hy s2 m3 R2 Y2 S2 L2
  rw [hs3] at v3
  have frame2 (q : Wire) (hq : q∉L.r) : s2.basis q=s1.basis q := v2.2.2 q (fun h => hq (by simp [Layout.r,h]))
  have one3 : s3.basis L.one=false := (v3.2.2 _ oa (fun h => L.flagAway hn L.one (by simp) (by simp [h]))).trans ((frame2 _ oa).trans one1)
  have clean3 : ∀q∈L.carry,s3.basis q=false := by
    intro q hq; have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).2.1
    exact (v3.2.2 q (ca q hq).1 (fun hyq => List.disjoint_left.mp d.2.2 hyq hq)).trans ((frame2 q (ca q hq).1).trans (clean1 q hq))
  have cmp := compareLt_correct none L.y L.r L.carry L.one L.parity (L.compareND hn)
    (by simp) (by omega) (by unfold Layout.Widths at hw; omega) s3 m4 one3 clean3
  rw [hs4] at cmp
  have pred : decide (regValue L.y s3.basis<regValue L.r s3.basis)=decide (q < |2*R-signedY B Y|) := by
    apply decide_eq_decide.mpr
    have interval := cleanup_interval_identity B R Y hr hy
    omega
  have A3 : s3.basis L.parity=s.basis L.parity := (v3.2.2 _ ar ay).trans ((frame2 _ ar).trans (v1.2.2 _ ar al))
  have A4 : s4.basis L.parity=false := by rw [cmp.2.2,A3,pred,hA]; simp [controlValue]
  have ex5 := inverse_except (prepareCompare L) (prepareCompare_proper L hn) L.parity pa.2 s2 s4 m3 m5 (by rw [hs3]; exact ⟨cmp.1,cmp.2.1⟩)
  rw [hs5] at ex5
  have one5 : s5.basis L.one=false := (ex5.2 _ (by intro e; have hh := (List.nodup_cons.mp flags).1; exact hh (by simp [←e]))).trans ((frame2 _ oa).trans one1)
  have clean5 : ∀q∈L.carry,s5.basis q=false := by
    intro q hq; exact (ex5.2 q (fun e => L.flagAway hn L.parity (by simp) (by simp [←e,hq]))).trans ((frame2 q (ca q hq).1).trans (clean1 q hq))
  have un := unnormalize_correct L hw hn s5 m6 one5 clean5
  rw [hs6] at un
  have raw := literalConstAdd_correct L.low (L.carry.take 254) L.lower L.one negativeLiteral nd (by omega) s1 m2 one1 (fun q hq => clean1 q (List.mem_of_mem_take hq))
  have read2 : regValue L.low s2.basis=
      (regValue L.low s1.basis+negativeLiteral+(s1.basis L.lower).toNat)%2^L.low.length := by
    rw [←hs2]
    exact raw.2.2
  have low5 : regValue L.low s5.basis=regValue L.low s2.basis := regValue_congr _ _ _ (fun q hq => ex5.2 q (fun e => ar (by simp [Layout.r,←e,hq])))
  have lower5 : s5.basis L.lower=s1.basis L.lower := (ex5.2 _ (Ne.symm al)).trans (v2.2.2 _ (fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])))
  have low6 : regValue L.low s6.basis=regValue L.low s1.basis := by
    rw [un.2.1,low5,read2,lower5,w.1]
    have fit := regValue_lt L.low s1.basis; rw [w.1] at fit
    have sum := literals_sum
    cases b : s1.basis L.lower <;> simp only [Bool.not_false,Bool.not_true,Bool.toNat_false,Bool.toNat_true] <;> omega
  have ex6 : Except L.parity s6 s1 := by
    refine ⟨un.1.trans (ex5.1.trans v2.1),?_⟩
    intro q hq
    by_cases hl : q∈L.low
    · exact (regValue_eq_iff L.low _ _).mp low6 q hl
    · exact (un.2.2 q hl).trans ((ex5.2 q hq).trans (v2.2.2 q hl))
  have ex7 := inverse_except (prepareSign L) (prepareSign_proper L hn) L.parity pa.1 s s6 m1 m7 (by rw [hs1]; exact ex6)
  rw [hs7] at ex7
  have keep5 := run_preserves_outside (prepareCompare L).reverse m5 s4 L.parity (by rw [wires_reverse]; exact pa.2)
  have keep7 := run_preserves_outside (prepareSign L).reverse m7 s6 L.parity (by rw [wires_reverse]; exact pa.1)
  rw [hs5] at keep5; rw [hs7] at keep7
  exact ⟨ex7,keep7.trans ((un.2.2 _ (fun h => ar (by simp [Layout.r,h]))).trans (keep5.trans A4))⟩

 theorem correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false)
    (hA : s.basis L.parity=decide (q < |2*R-signedY B Y|)) :
    run (program L) m s=⟨s.phase,writeBit s.basis L.parity false⟩ := by
  let P : State → State → Prop := fun i o =>
    regValue L.r i.basis=encodeWord 256 R → regValue L.y i.basis=encodeWord 256 Y →
    i.basis L.sign=B → i.basis L.lower=false → i.basis L.one=false →
    (∀q∈L.carry,i.basis q=false) → i.basis L.parity=decide (q < |2*R-signedY B Y|) →
    Except L.parity o i ∧ o.basis L.parity=false
  have h := skywalkRunSeven (prepareSign L) (normalize L) (prepareCompare L)
    (compareLt none L.y L.r L.carry L.one L.parity) (prepareCompare L).reverse
    (unnormalize L) (prepareSign L).reverse P
    (by intro i s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 e1 e2 e3 e4 e5 e6 e7 r y b z o c a
        exact states L hw hn R Y B hr hy i m1 m2 m3 m4 m5 m6 m7 s1 s2 s3 s4 s5 s6 s7 r y b z o c a e1 e2 e3 e4 e5 e6 e7) s m
  have result : Except L.parity (run (program L) m s) s ∧ (run (program L) m s).basis L.parity=false :=
    by simpa only [program] using h hR hY hS hz ho hc hA
  apply State.extensionality
  · exact result.1.1
  · funext q
    by_cases e : q=L.parity
    · subst q; simp [writeBit,result.2]
    · simp [writeBit,e,result.1.2 q e]

end ECDSAAdd.Arithmetic.BalancedCleanup
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldCircuitProgram.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open Secp256k1

/-- Two centered field words, one shared carry ladder, and eight scalar
positions. The sign is an input control; all other scalar work starts clean. -/
structure Layout extends BalancedCleanup.Layout where
  sourceGuard : Wire
  cout : Wire
  minus : Wire
  plus : Wire

def Layout.wires (L : Layout) := [L.sourceGuard,L.cout,L.minus,L.plus]++L.toLayout.wires
def Layout.Widths (L : Layout) := L.toLayout.Widths

def rawSource (L : Layout) := L.toLayout.y++[L.sourceGuard]
def rawTarget (L : Layout) := L.toLayout.r++[L.one]
def foldTarget (L : Layout) := L.rtail++[L.rmsb,L.one]
def sparseF : Nat := 2^32+977

/-- For odd f, the upper bits of f and -f are complementary. Each
position therefore reads one of two immutable selectors, without a bank. -/
def foldBits (L : Layout) : List MappedBit :=
  (List.range 256).map (fun i =>
    {wire:=some (if sparseF.testBit (i+1) then L.plus else L.minus),flip:=false})++
    [{wire:=none,flip:=false}]

def seedViews (L : Layout) : Program :=
  [.CX L.ymsb L.sourceGuard,.CX L.rmsb L.one,
    .CX (L.ylow.getD 0 0) L.parity,.CX L.r0 L.parity]

def rawAdd (L : Layout) : Program :=
  signComplement L.sign (rawSource L)++
  addInPlace (rawSource L) (rawTarget L) L.carry L.sign++
  signComplement L.sign (rawSource L)

def prepareFold (L : Layout) : Program :=
  [.CX L.one L.lower,.CCX L.parity L.lower L.minus,
    .CX L.parity L.plus,.CX L.minus L.plus,
    .CX L.parity L.one,.CX L.parity L.r0]

def fold (L : Layout) : Program :=
  mappedAdd (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity++[.CX L.minus L.cout]

def releaseSelectors (L : Layout) : Program :=
  [.CX L.parity L.lower,.CX L.rmsb L.lower,
    .CX L.parity L.plus,.CX L.minus L.plus,
    .measureX L.minus [] [.Z L.parity,.CZ L.parity L.rmsb]]

/-- The complete candidate emission. Resource theorems do not assert
functional correctness; full gate-level composition is still required. -/
def program (L : Layout) : Program :=
  seedViews L++rawAdd L++prepareFold L++fold L++rotateRight (rawTarget L)++
    releaseSelectors L++BalancedCleanup.program L.toLayout++[.CX L.ymsb L.sourceGuard]

theorem widths (L : Layout) (hw : L.Widths) :
    (rawSource L).length=257 ∧ (rawTarget L).length=257 ∧
    (foldTarget L++[L.cout]).length=257 ∧ (foldBits L).length=257 ∧ L.carry.length=256 := by
  have w := BalancedCleanup.widths L.toLayout hw
  simp [rawSource,rawTarget,foldTarget,foldBits,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,hw.1,hw.2.1,hw.2.2]

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=1277 ∧ measurementCount (program L)=1277 := by
  have w := widths L hw
  have ra := addInPlace_counts (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have fa := mappedAdd_counts (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
    (by omega) (by omega)
  have cm := signComplement_counts L.sign (rawSource L)
  have ro := rotate_counts (rawTarget L)
  have cl := BalancedCleanup.counts L.toLayout hw
  simp only [program,seedViews,rawAdd,prepareFold,fold,releaseSelectors,
    toffoliCount_append,measurementCount_append,ra.1,ra.2,fa.1,fa.2,cm.1,cm.2,ro.1,ro.2.1,cl.1,cl.2]
  simp only [w.2.1,w.2.2.1]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetProgram.lean
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
open BalancedCircuit BalancedField

/-- Rejected cost-screen layout. Its extra full carry bank violates the
776-site field-kernel envelope. This module is not selected by production. -/
structure Layout extends toCircuit : BalancedCircuit.Layout where
  offsetCarry : List Wire

def Layout.wires (L : Layout) := L.toCircuit.wires++L.offsetCarry
def Layout.Widths (L : Layout) := L.toCircuit.Widths ∧ L.offsetCarry.length=256

def offset : Nat := (BalancedCircuit.sparseF-1)/2

/-- J has bit1 clear, so J+2*Lower is read without a constant register. -/
def offsetBits (L : Layout) : List MappedBit := (List.range 256).map fun i =>
  if i=1 then {wire:=some L.lower,flip:=false}
  else {wire:=none,flip:=offset.testBit i}

/-- Temporarily form each sum bit, compare it, and restore it while unwinding.
The offset and comparator prefixes occupy separate full clean carry banks.
Functional correctness, including all measured phase corrections, is pending. -/
def chain : List MappedBit → List Wire → List Wire → List Wire → List Wire →
    Wire → Wire → Wire → Program
  | b::bits,a::as,y::ys,c::cs,d::ds,cinC,cinB,target =>
      mappedMajority b y cinC c++mappedSum b y cinC++[.X y]++
      majority a y cinB d++chain bits as ys cs ds c d target++
      eraseCarry a y cinB d++[.X y]++mappedSum b y cinC++mappedEraseCarry b y cinC c
  | [],[],[],[],[],_,cinB,target => flipBelow none cinB target
  | _,_,_,_,_,_,_,_ => []

/-- Magnitude is doubled by a Clifford rotation. Only the source comparison
word receives the signed-to-unsigned top-bit bias. -/
def view (L : Layout) : Program :=
  rotateLeft L.r++[.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]++
  signComplement L.sign L.y++signComplement L.lower L.y++[.X L.ymsb]

/-- Actual isolated emission. The comparator carry-in is Cout=1 and the
constant carry-in is One=0. No finite comparison window appears. -/
def program (L : Layout) : Program :=
  BalancedCleanup.prepareSign L.toCircuit.toLayout++view L++[.X L.cout]++
  chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity++
  [.X L.cout]++(view L).reverse++(BalancedCleanup.prepareSign L.toCircuit.toLayout).reverse

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetHead.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
attribute [local irreducible] run majority mappedMajority mappedSum mappedEraseCarry eraseCarry

def prepareHead (b : MappedBit) (a y cinC cinB c d : Wire) : Program :=
  mappedMajority b y cinC c++mappedSum b y cinC++[.X y]++majority a y cinB d

def releaseHead (b : MappedBit) (a y cinC cinB c d : Wire) : Program :=
  eraseCarry a y cinB d++[.X y]++mappedSum b y cinC++mappedEraseCarry b y cinC c

theorem bit_write (b : MappedBit) (s : BasisState) (q : Wire) (v : Bool)
    (ha : ∀w∈b.wire,w≠q) : b.value (writeBit s q v)=b.value s := by
  apply mappedBit_value_congr
  intro w hw
  simp only [writeBit,Function.update_of_ne (ha w hw)]

theorem sum_involution (B Y C : Bool) : sumBit B (sumBit B Y C) C=Y := by
  cases B <;> cases Y <;> cases C <;> rfl

theorem write_twice (s : BasisState) (q : Wire) (u v : Bool) :
    writeBit (writeBit s q u) q v=writeBit s q v := by
  funext w
  by_cases h : w=q <;> simp [writeBit,h]

theorem x_run (q : Wire) (s : State) (m : List Bool) :
    run [.X q] m s=⟨s.phase,writeBit s.basis q (!s.basis q)⟩ := by simp only [run]

theorem prepareHead_run (b : MappedBit) (a y cinC cinB c d : Wire)
    (hn : [a,y,cinC,cinB,c,d].Nodup) (ha : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d])
    (s : State) (m : List Bool) (hc : s.basis c=false) (hd : s.basis d=false) :
    run (prepareHead b a y cinC cinB c d) m s=
      let K := carryBit (b.value s.basis) (s.basis y) (s.basis cinC)
      let S := sumBit (b.value s.basis) (s.basis y) (s.basis cinC)
      ⟨s.phase,writeBit (writeBit (writeBit s.basis c K) y (!S)) d
        (carryBit (s.basis a) (!S) (s.basis cinB))⟩ := by
  have nd := hn
  have nr := List.nodup_reverse.mpr hn
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd nr
  have src (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d]) : ∀w∈b.wire,w≠q :=
    fun w hw e => ha w hw (e.symm ▸ hq)
  have nc : [y,cinC,c].Nodup := by simp [List.nodup_cons,nd,nr]
  have nm : [a,y,cinB,d].Nodup := by simp [List.nodup_cons,nd,nr]
  have source : ∀w∈b.wire,w∉[y,cinC,c] := by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨src y (by simp) w hw,src cinC (by simp) w hw,src c (by simp) w hw⟩
  let K := carryBit (b.value s.basis) (s.basis y) (s.basis cinC)
  let S := sumBit (b.value s.basis) (s.basis y) (s.basis cinC)
  generalize eu : run (mappedMajority b y cinC c) m s=u
  generalize ev : run (mappedSum b y cinC) m u=v
  generalize ew : run [.X y] m v=w
  generalize et : run (majority a y cinB d) m w=t
  have us := mappedMajority_correct b y cinC c nc source s m
  rw [eu,hc,Bool.false_xor] at us
  change u=⟨s.phase,writeBit s.basis c K⟩ at us
  have uf (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ub : b.value u.basis=b.value s.basis := by rw [us]; exact bit_write b s.basis c K (src c (by simp))
  have vu := mappedSum_correct b y cinC (by simp [nd,nr]) (src y (by simp)) u m
  rw [ev,ub,uf y (by simp [nd,nr]),uf cinC (by simp [nd,nr])] at vu
  change v=⟨u.phase,writeBit u.basis y S⟩ at vu
  have vf (q : Wire) (hq : q≠y) : v.basis q=u.basis q := by
    rw [vu]
    simp only [writeBit,Function.update_of_ne hq]
  have vy : v.basis y=S := by rw [vu]; simp only [writeBit,Function.update_self]
  have wv := x_run y v m
  rw [ew,vy] at wv
  have wf (q : Wire) (hq : q≠y) : w.basis q=v.basis q := by
    rw [wv]
    simp only [writeBit,Function.update_of_ne hq]
  have wa : w.basis a=s.basis a := (wf a (by simp [nd,nr])).trans
    ((vf a (by simp [nd,nr])).trans (uf a (by simp [nd,nr])))
  have wi : w.basis cinB=s.basis cinB := (wf cinB (by simp [nd,nr])).trans
    ((vf cinB (by simp [nd,nr])).trans (uf cinB (by simp [nd,nr])))
  have wy : w.basis y= !S := by rw [wv]; simp only [writeBit,Function.update_self]
  have wd : w.basis d=false := (wf d (by simp [nd,nr])).trans
    ((vf d (by simp [nd,nr])).trans ((uf d (by simp [nd,nr])).trans hd))
  have tw := majority_correct a y cinB d nm w m
  rw [et,wa,wi,wy,wd,Bool.false_xor] at tw
  have actual : run (prepareHead b a y cinC cinB c d) m s=t := by
    simp only [prepareHead,List.append_assoc,run_append]
    simp only [run_take]
    simp only [(mappedBit_counts b y cinC c).2.1,(mappedBit_counts b y cinC c).2.2.2.2.2,
      show measurementCount [.X y]=0 from rfl,List.drop_zero]
    rw [eu,ev,ew,et]
  rw [actual,tw,wv,vu,us]
  simp only [write_twice,K,S]

theorem releaseHead_run (b : MappedBit) (a y cinC cinB c d : Wire)
    (hn : [a,y,cinC,cinB,c,d].Nodup) (ha : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d])
    (B A Y C D : Bool) (s : State) (m : List Bool)
    (hb : b.value s.basis=B) (hA : s.basis a=A) (hC : s.basis cinC=C)
    (hD : s.basis cinB=D) (hy : s.basis y= !(sumBit B Y C))
    (hc : s.basis c=carryBit B Y C) (hd : s.basis d=carryBit A (!(sumBit B Y C)) D) :
    run (releaseHead b a y cinC cinB c d) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis d false) y Y) c false⟩ := by
  have nd := hn
  have nr := List.nodup_reverse.mpr hn
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd nr
  have src (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d]) : ∀w∈b.wire,w≠q :=
    fun w hw e => ha w hw (e.symm ▸ hq)
  have nc : [y,cinC,c].Nodup := by simp [List.nodup_cons,nd,nr]
  have source : ∀w∈b.wire,w∉[y,cinC,c] := by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨src y (by simp) w hw,src cinC (by simp) w hw,src c (by simp) w hw⟩
  let tail := m.drop 1
  generalize eu : run (eraseCarry a y cinB d) m s=u
  generalize ev : run [.X y] tail u=v
  generalize ew : run (mappedSum b y cinC) tail v=w
  generalize et : run (mappedEraseCarry b y cinC c) tail w=t
  have us := eraseCarry_correct a y cinB d (by simp [nd,nr]) (by simp [nd,nr])
    (by simp [nd,nr]) s (by rw [hA,hy,hD]; exact hd) m
  rw [eu] at us
  have uf (q : Wire) (hq : q≠d) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ub : b.value u.basis=B := by
    rw [us,bit_write b s.basis d false (src d (by simp))]
    exact hb
  have uy : u.basis y= !(sumBit B Y C) := (uf y (by simp [nd,nr])).trans hy
  have ucin : u.basis cinC=C := (uf cinC (by simp [nd,nr])).trans hC
  have vu := x_run y u tail
  rw [ev,uy,Bool.not_not] at vu
  have vf (q : Wire) (hq : q≠y) : v.basis q=u.basis q := by
    rw [vu]
    simp only [writeBit,Function.update_of_ne hq]
  have vb : b.value v.basis=B := by
    rw [vu,bit_write b u.basis y (sumBit B Y C) (src y (by simp))]
    exact ub
  have vy : v.basis y=sumBit B Y C := by rw [vu]; simp only [writeBit,Function.update_self]
  have vcin : v.basis cinC=C := (vf cinC (by simp [nd,nr])).trans ucin
  have vc : v.basis c=carryBit B Y C := (vf c (by simp [nd,nr])).trans
    ((uf c (by simp [nd,nr])).trans hc)
  have wv := mappedSum_correct b y cinC (by simp [nd,nr]) (src y (by simp)) v tail
  rw [ew,vb,vy,vcin,sum_involution] at wv
  have wf (q : Wire) (hq : q≠y) : w.basis q=v.basis q := by
    rw [wv]
    simp only [writeBit,Function.update_of_ne hq]
  have wb : b.value w.basis=B := by
    rw [wv,bit_write b v.basis y Y (src y (by simp))]
    exact vb
  have wy : w.basis y=Y := by rw [wv]; simp only [writeBit,Function.update_self]
  have wcin : w.basis cinC=C := (wf cinC (by simp [nd,nr])).trans vcin
  have wc : w.basis c=carryBit B Y C := (wf c (by simp [nd,nr])).trans vc
  have tw := mappedEraseCarry_correct b y cinC c nc source w tail
    (by rw [wb,wy,wcin]; exact wc)
  rw [et] at tw
  have actual : run (releaseHead b a y cinC cinB c d) m s=t := by
    simp only [releaseHead,List.append_assoc,run_append]
    simp only [run_take]
    simp only [show measurementCount (eraseCarry a y cinB d)=1 from by unfold eraseCarry; rfl,
      show measurementCount [.X y]=0 from rfl,(mappedBit_counts b y cinC c).2.2.2.2.2,List.drop_zero]
    simp only [tail] at ev ew et
    rw [eu,ev,ew,et]
  rw [actual,tw,wv,vu,us]
  simp only [write_twice]

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetLogic.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

def decision : List Bool → List Bool → List Bool → Bool → Bool → Bool
  | b::bs,a::as,y::ys,cinC,cinB =>
      decision bs as ys (carryBit b y cinC) (carryBit a (!(sumBit b y cinC)) cinB)
  | [],[],[],_,cinB => !cinB
  | _,_,_,_,_ => false

theorem mapped_member (b : MappedBit) (bits : List MappedBit) (w : Wire) (hw : w∈b.wire) :
    w∈mappedWires (b::bits) := by
  cases hb : b.wire with
  | none => simp [hb] at hw
  | some a =>
    have e : a=w := by simpa [hb] using hw
    subst w
    simp [mappedWires,hb]

theorem mapped_tail_member (b : MappedBit) (bits : List MappedBit) (w : Wire)
    (hw : w∈mappedWires bits) : w∈mappedWires (b::bits) := by
  change w ∈ b.wire.toList ++ mappedWires bits
  exact List.mem_append.mpr (Or.inr hw)

theorem head_tail_nd (target cinC cinB a y c d : Wire) (as ys cs ds : List Wire)
    (hn : (target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds))).Nodup) :
    ([a,y,cinC,cinB,c,d,target]++(as++ys++cs++ds)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem head_six_nd (a y cinC cinB c d target : Wire)
    (hn : [a,y,cinC,cinB,c,d,target].Nodup) : [a,y,cinC,cinB,c,d].Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_nil] at h ⊢
  omega

theorem recursive_nd (target cinC cinB a y c d : Wire) (as ys cs ds : List Wire)
    (hn : (target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds))).Nodup) :
    (target::c::d::(as++ys++cs++ds)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem head_mem_scope (target cinC cinB a y c d q : Wire) (as ys cs ds : List Wire)
    (hq : q∈[a,y,cinC,cinB,c,d,target]) :
    q∈target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds)) := by
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  tauto

theorem tail_mem_scope (target cinC cinB a y c d q : Wire) (as ys cs ds : List Wire)
    (hq : q∈target::c::d::(as++ys++cs++ds)) :
    q∈target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds)) := by
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  tauto

theorem tail_away_head (target cinC cinB a y c d q h : Wire) (as ys cs ds : List Wire)
    (hn : (target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds))).Nodup)
    (hq : q∈as++ys++cs++ds) (hh : h∈[a,y,cinC,cinB,c,d,target]) : q≠h := by
  have dis := (List.nodup_append'.mp (head_tail_nd target cinC cinB a y c d as ys cs ds hn)).2.2
  exact fun e => List.disjoint_left.mp dis hh (e ▸ hq)

theorem prepareHead_measurements (b : MappedBit) (a y cinC cinB c d : Wire) :
    measurementCount (prepareHead b a y cinC cinB c d)=0 := by
  simp only [prepareHead,measurementCount_append,(mappedBit_counts b y cinC c).2.1,
    (mappedBit_counts b y cinC c).2.2.2.2.2]
  rfl

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetChainProof.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
attribute [local irreducible] run chain prepareHead releaseHead

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetCompareProof.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

def value : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*value bs

def sumWords : List Bool → List Bool → Bool → List Bool
  | b::bs,y::ys,c => sumBit b y c::sumWords bs ys (carryBit b y c)
  | _,_,_ => []

def compareDecision : List Bool → List Bool → Bool → Bool
  | a::as,y::ys,c => compareDecision as ys (carryBit a (!y) c)
  | [],[],c => !c
  | _,_,_ => false

def borrowDecision : List Bool → List Bool → Bool → Bool
  | a::as,y::ys,c => borrowDecision as ys (carryBit (!a) y c)
  | [],[],c => c
  | _,_,_ => false

theorem carry_complement (A Y C : Bool) : carryBit A (!Y) C= !(carryBit (!A) Y (!C)) := by
  cases A <;> cases Y <;> cases C <;> rfl

theorem sumWords_length (ks ys : List Bool) (h : ks.length=ys.length) (C : Bool) :
    (sumWords ks ys C).length=ys.length := by
  induction ys generalizing ks C with
  | nil => have e := List.eq_nil_of_length_eq_zero (by simpa using h); subst ks; rfl
  | cons y ys ih =>
    cases ks with
    | nil => simp at h
    | cons k ks => simpa only [sumWords,List.length_cons] using congrArg Nat.succ (ih ks (by simpa using h) _)

theorem sumWords_value (ks ys : List Bool) (h : ks.length=ys.length) (C : Bool) :
    value (sumWords ks ys C)=(value ks+value ys+C.toNat)%2^ys.length := by
  induction ys generalizing ks C with
  | nil =>
    have e := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst ks
    simp [sumWords,value,Nat.mod_one]
  | cons y ys ih =>
    cases ks with
    | nil => simp at h
    | cons k ks =>
      rw [sumWords,value,ih ks (by simpa using h)]
      exact sum_value_step k y C (value ks) (value ys) ys.length

theorem decision_factor (ks xs ys : List Bool) (hk : ks.length=ys.length)
    (hx : xs.length=ys.length) (C D : Bool) :
    decision ks xs ys C D=compareDecision xs (sumWords ks ys C) D := by
  induction ys generalizing ks xs C D with
  | nil =>
    have e := List.eq_nil_of_length_eq_zero (by simpa using hk)
    have f := List.eq_nil_of_length_eq_zero (by simpa using hx)
    subst ks xs
    rfl
  | cons y ys ih =>
    cases ks with
    | nil => simp at hk
    | cons k ks =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        exact ih ks xs (by simpa using hk) (by simpa using hx) _ _

theorem compare_borrow (xs ys : List Bool) (h : xs.length=ys.length) (C : Bool) :
    compareDecision xs ys C=borrowDecision xs ys (!C) := by
  induction ys generalizing xs C with
  | nil => have e := List.eq_nil_of_length_eq_zero (by simpa using h); subst xs; rfl
  | cons y ys ih =>
    cases xs with
    | nil => simp at h
    | cons a xs =>
      simpa only [compareDecision,borrowDecision,carry_complement,Bool.not_not] using
        ih xs (by simpa using h) (carryBit a (!y) C)

theorem borrow_value (xs ys : List Bool) (h : xs.length=ys.length) (C : Bool) :
    borrowDecision xs ys C=decide (value xs<value ys+C.toNat) := by
  induction ys generalizing xs C with
  | nil =>
    have e := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst xs
    cases C <;> rfl
  | cons y ys ih =>
    cases xs with
    | nil => simp at h
    | cons a xs =>
      rw [borrowDecision,ih xs (by simpa using h)]
      apply decide_eq_decide.mpr
      exact (borrow_threshold a y C (value xs) (value ys)).symm

theorem decision_value (ks xs ys : List Bool) (hk : ks.length=ys.length)
    (hx : xs.length=ys.length) (C : Bool) :
    decision ks xs ys C true=decide (value xs<(value ks+value ys+C.toNat)%2^ys.length) := by
  rw [decision_factor ks xs ys hk hx C true,
    compare_borrow xs (sumWords ks ys C) (by rw [sumWords_length ks ys hk]; exact hx),
    borrow_value xs (sumWords ks ys C) (by rw [sumWords_length ks ys hk]; exact hx)]
  simp only [Bool.not_true,Bool.toNat_false,Nat.add_zero,sumWords_value ks ys hk C]

theorem mapped_value_map (bits : List MappedBit) (s : BasisState) :
    value (bits.map (fun b => b.value s))=mappedValue bits s := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [List.map_cons,value,mappedValue,ih]

theorem word_value_map (xs : List Wire) (s : BasisState) : value (xs.map s)=regValue xs s := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,value,regValue,List.foldr_cons,ih]
    cases s a <;> rfl

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetConstant.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

private def virtualOffset (b : Bool) : Nat :=
  (List.range 256).foldr (fun i n =>
    (if i=1 then b else offset.testBit i).toNat+2*n) 0

private theorem virtualOffset_value (b : Bool) :
    virtualOffset b=offset+2*b.toNat := by cases b <;> decide

private theorem offset_list (is : List Nat) (L : Layout) (s : BasisState) :
    mappedValue (is.map (fun i =>
      if i=1 then ({wire:=some L.lower,flip:=false} : MappedBit)
      else {wire:=none,flip:=offset.testBit i})) s=
    is.foldr (fun i n => (if i=1 then s L.lower else offset.testBit i).toNat+2*n) 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons,ih]
    by_cases hi : i=1 <;> simp [MappedBit.value,hi]

/-- Value of the concrete emitted bits on every layout and basis state.
Only the single selector at bit 1 is read from the state. -/
theorem offsetBits_value (L : Layout) (s : BasisState) :
    mappedValue (offsetBits L) s=offset+2*(s L.lower).toNat := by
  rw [offsetBits,offset_list]
  exact virtualOffset_value _

theorem offsetBits_length (L : Layout) : (offsetBits L).length=256 := by
  simp [offsetBits]

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetLayout.lean
noncomputable section

set_option maxHeartbeats 600000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

theorem Layout.baseND (L : Layout) (hn : L.wires.Nodup) : L.toCircuit.wires.Nodup :=
  (List.nodup_append'.mp hn).1

theorem Layout.cleanupND (L : Layout) (hn : L.wires.Nodup) : L.toCircuit.toLayout.wires.Nodup :=
  (List.nodup_append'.mp (L.baseND hn)).2.1

theorem Layout.allND (L : Layout) (hn : L.wires.Nodup) :
    ([L.parity,L.sign,L.lower,L.one,L.sourceGuard,L.cout,L.minus,L.plus] ++
      (L.r++L.y++L.carry++L.offsetCarry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem Layout.flagsND (L : Layout) (hn : L.wires.Nodup) :
    [L.parity,L.sign,L.lower,L.one,L.sourceGuard,L.cout,L.minus,L.plus].Nodup :=
  (List.nodup_append'.mp (L.allND hn)).1

theorem Layout.flagAway (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.parity,L.sign,L.lower,L.one,L.sourceGuard,L.cout,L.minus,L.plus]) :
    q∉L.r++L.y++L.carry++L.offsetCarry :=
  fun h => List.disjoint_left.mp (List.nodup_append'.mp (L.allND hn)).2.2 hq h

theorem Layout.chainND (L : Layout) (hn : L.wires.Nodup) :
    (L.parity::L.one::L.cout::(L.y++L.r++L.offsetCarry++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.allND hn) q
  simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

/-- The only data-dependent offset bit is the already retained lower sign. -/
theorem offsetSources (L : Layout) (q : Wire) (hq : q∈mappedWires (offsetBits L)) :
    q=L.lower := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  by_cases h : i=1
  · simp only [if_pos h] at hq
    simpa using hq
  · simp only [if_neg h] at hq
    simp at hq

theorem offsetSources_away (L : Layout) (hn : L.wires.Nodup) :
    ∀q∈mappedWires (offsetBits L),q∉L.parity::L.one::L.cout::
      (L.y++L.r++L.offsetCarry++L.carry) := by
  intro q hq
  have eq := offsetSources L q hq
  subst q
  have flags := L.flagsND hn
  have away := L.flagAway hn L.lower (by simp)
  have f := List.nodup_iff_count.mp flags L.lower
  simp only [List.count_cons,List.count_nil] at f
  have np : L.lower≠L.parity := by intro e; simp [e] at f
  have no : L.lower≠L.one := by intro e; simp [e] at f; omega
  have nc : L.lower≠L.cout := by intro e; simp [e] at f; omega
  intro h
  simp only [List.mem_cons,List.mem_append,np,no,nc,false_or] at h
  exact away (by simpa only [List.mem_append,or_assoc,or_left_comm,or_comm] using h)

theorem view_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (view L) := by
  have nd := L.cleanupND hn
  have full := BalancedCleanup.Layout.dataND L.toCircuit.toLayout nd
  have nr := (List.nodup_append'.mp full).1
  have sR : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lR : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have sY : L.sign∉L.y := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lY : L.lower∉L.y := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  simp only [view,properProgram_append]
  refine ⟨⟨⟨⟨BalancedCleanup.rotateLeft_proper _ nr,?_⟩,
    BalancedCleanup.complement_proper _ _ sY⟩,
    BalancedCleanup.complement_proper _ _ lY⟩,by simp [ProperProgram,ProperGate]⟩
  simp only [ProperProgram,ProperGate,List.mem_cons,List.not_mem_nil,or_false]
  have sr : L.sign≠L.r0 := fun e => sR (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  have lr : L.lower≠L.r0 := fun e => lR (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  intro i hi
  rcases hi with rfl|rfl|rfl
  · trivial
  · exact sr
  · exact lr

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetMath.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
open BalancedField BalancedCircuit Secp256k1

/-- The unnormalized R word after prepareSign and the Clifford view. -/
def rawR (B : Bool) (R : Int) : Nat :=
  2*(magnitude R).toNat+(!(B ^^ negative R)).toNat

/-- Only Y receives the signed-to-unsigned top-bit bias. -/
def biasedY (B : Bool) (R Y : Int) : Nat :=
  (viewedY B R Y+((2^255 : Nat) : Int)).toNat

/-- The bias omitted from R is exactly J. In particular h has scale 2^254. -/
theorem offset_relation : (offset : Int)=((2^255 : Nat) : Int)-2*h := by
  norm_num [offset,sparseF,h,q,p]

theorem offset_safety : 0 < offset ∧
    2*q+(offset : Int)+3 < ((2^256 : Nat) : Int) := by
  norm_num [offset,sparseF,q,p]

theorem insertedBit_cast (B : Bool) (R : Int) :
    ((!(B ^^ negative R)).toNat : Int)=insertBit B R := by
  cases hb : !(B ^^ negative R) <;> simp [insertBit,hb]

theorem negativeBit_cast (R : Int) :
    ((negative R).toNat : Int)=signBit R := by
  cases hb : negative R <;> simp [signBit,hb]

theorem insertedBit_bounds (B : Bool) (R : Int) :
    0 ≤ insertBit B R ∧ insertBit B R ≤ 1 := by
  unfold insertBit
  split_ifs <;> omega

theorem negativeBit_bounds (R : Int) :
    0 ≤ ((negative R).toNat : Int) ∧ ((negative R).toNat : Int) ≤ 1 := by
  cases hb : negative R <;> simp

theorem rawR_cast (B : Bool) (R : Int) (hr : Centered R) :
    (rawR B R : Int)=2*magnitude R+insertBit B R := by
  have hm := magnitude_bounds R hr
  simp only [rawR,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    Int.toNat_of_nonneg hm.1,insertedBit_cast]

/-- The offset addition is an ordinary unsigned sum on the entire centered
domain. Its physical modulo never wraps, including all endpoint ties. -/
theorem threshold_no_wrap (B : Bool) (R : Int) (hr : Centered R) :
    rawR B R+offset+2*(negative R).toNat < 2^256 := by
  have hm := magnitude_bounds R hr
  have hi := insertedBit_bounds B R
  have hn := negativeBit_bounds R
  have hs := offset_safety
  have limit : ((rawR B R+offset+2*(negative R).toNat : Nat) : Int) < ((2^256 : Nat) : Int) := by
    push_cast
    rw [rawR_cast B R hr]
    omega
  exact_mod_cast limit

theorem threshold_value (B : Bool) (R : Int) (hr : Centered R) :
    (((rawR B R+offset+2*(negative R).toNat)%2^256 : Nat) : Int)=
      comparisonLeft B R+((2^255 : Nat) : Int) := by
  rw [Nat.mod_eq_of_lt (threshold_no_wrap B R hr)]
  push_cast
  rw [rawR_cast B R hr,offset_relation,negativeBit_cast]
  unfold comparisonLeft normalizedR
  ring

theorem biasedY_bounds (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    0 ≤ viewedY B R Y+((2^255 : Nat) : Int) ∧
    viewedY B R Y+((2^255 : Nat) : Int) < ((2^256 : Nat) : Int) := by
  have bounds := comparison_view_bounds B R Y hr hy
  have hc := BalancedField.constants
  norm_num only [Nat.reducePow] at bounds hc ⊢
  omega

theorem biasedY_cast (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    (biasedY B R Y : Int)=viewedY B R Y+((2^255 : Nat) : Int) :=
  Int.toNat_of_nonneg (biasedY_bounds B R Y hr hy).1

/-- Exact full-domain replacement predicate for the actual offsetCarry
comparator. The proof covers both B values and both signs of R. -/
theorem comparison_predicate (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    biasedY B R Y < (rawR B R+offset+2*(negative R).toNat)%2^256 ↔
      q < |2*R-signedY B Y| := by
  have cast : biasedY B R Y < (rawR B R+offset+2*(negative R).toNat)%2^256 ↔
      (biasedY B R Y : Int) < (((rawR B R+offset+2*(negative R).toNat)%2^256 : Nat) : Int) := by omega
  rw [cast,biasedY_cast B R Y hr hy,threshold_value B R hr]
  have interval := cleanup_interval_identity B R Y hr hy
  constructor
  · intro hcmp
    apply interval.mpr
    omega
  · intro hout
    have hcmp := interval.mp hout
    omega

/-- Chain's mapped constant is J+2*Lower, with One=0. Addition order
agrees exactly with its already proved full-width arithmetic predicate. -/
theorem chain_predicate (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    biasedY B R Y < (offset+2*(negative R).toNat+rawR B R)%2^256 ↔
      q < |2*R-signedY B Y| := by
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    comparison_predicate B R Y hr hy

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetSupport.lean
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

theorem view_support (L : Layout) (hw : L.Widths) :
    wires (view L) ⊆ ([L.sign,L.lower]++L.r++L.y).toFinset := by
  have w := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have rr := (rotate_wires L.r).2
  have cs := signComplement_wires_subset L.sign L.y
  have cl := signComplement_wires_subset L.lower L.y
  intro q hq
  simp only [view,wires_append,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq
  · rw [rr,if_neg (by omega)] at hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · have h := cs hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  · have h := cl hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    simp only [BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false]
    tauto

theorem view_parity_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.parity∉wires (view L) := by
  have flags := List.nodup_cons.mp (L.flagsND hn)
  have away := L.flagAway hn L.parity (by simp)
  intro h
  have m := view_support L hw h
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  have ns : L.parity≠L.sign := fun e => flags.1 (by simp [e])
  have nl : L.parity≠L.lower := fun e => flags.1 (by simp [e])
  have nr : L.parity∉L.r := fun h => away (by simp [h])
  have ny : L.parity∉L.y := fun h => away (by simp [h])
  tauto

/-- Actual offset heads and both measured carry corrections remain in a
declared finite pool. This generic proof imports no caller field program. -/
theorem chain_pool_support (bits : List MappedBit) (xs ys cs ds : List Wire)
    (ci cb t : Wire) (W : Finset Wire)
    (hbits : ∀q∈mappedWires bits,q∈W) (hx : ∀q∈xs,q∈W) (hy : ∀q∈ys,q∈W)
    (hc : ∀q∈cs,q∈W) (hd : ∀q∈ds,q∈W) (hci : ci∈W) (hcb : cb∈W) (ht : t∈W) :
    wires (chain bits xs ys cs ds ci cb t)⊆W := by
  induction bits generalizing xs ys cs ds ci cb with
  | nil =>
    cases xs <;> cases ys <;> cases cs <;> cases ds <;>
      simp [chain,flipBelow_wires,wires,Finset.subset_iff,hcb,ht]
  | cons b bits ih =>
    cases xs with
    | nil => simp [chain,wires]
    | cons a xs =>
      cases ys with
      | nil => simp [chain,wires]
      | cons y ys =>
        cases cs with
        | nil => simp [chain,wires]
        | cons c cs =>
          cases ds with
          | nil => simp [chain,wires]
          | cons d ds =>
            have ha := hx a (by simp)
            have hyy := hy y (by simp)
            have hcc := hc c (by simp)
            have hdd := hd d (by simp)
            have source (q : Wire) (hq : q∈b.wire.toList) : q∈W :=
              hbits q (List.mem_append_left _ hq)
            have headPool : (b.wire.toList++[y,ci,c]).toFinset⊆W := by
              intro q hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
              rcases hq with hq|rfl|rfl|rfl
              · exact source q hq
              · exact hyy
              · exact hci
              · exact hcc
            have sum : (b.wire.toList++[y,ci]).toFinset⊆W := by
              intro q hq
              apply headPool
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
              tauto
            have recurse := ih xs ys cs ds c d
              (fun q hq => hbits q (List.mem_append_right _ hq))
              (fun q hq => hx q (List.mem_cons_of_mem _ hq))
              (fun q hq => hy q (List.mem_cons_of_mem _ hq))
              (fun q hq => hc q (List.mem_cons_of_mem _ hq))
              (fun q hq => hd q (List.mem_cons_of_mem _ hq)) hcc hdd
            have small : wires (majority a y cb d)⊆W ∧ wires (eraseCarry a y cb d)⊆W ∧
                wires [.X y]⊆W := by
              simp [majority,eraseCarry,wires,Instr.wires,correctionWires,Finset.subset_iff,
                ha,hyy,hcb,hdd]
            have bit := mappedBit_wires b y ci c
            simp only [chain,wires_append,Finset.union_subset_iff,and_assoc]
            exact ⟨bit.1.trans headPool,bit.2.2.trans sum,small.2.2,small.1,recurse,
              small.2.1,small.2.2,bit.2.2.trans sum,bit.2.1.trans headPool⟩

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetViews.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
open BalancedField

/-- Actual unnormalized Clifford view. The result remains an unsigned
double magnitude; only the source receives the signed comparison bias. -/
theorem view_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=(magnitude R).toNat)
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hL : s.basis L.lower=negative R) :
    let t := run (view L) m s
    regValue L.r t.basis=rawR B R ∧ regValue L.y t.basis=biasedY B R Y ∧
    (∀q,q∉L.r → q∉L.y → t.basis q=s.basis q) := by
  let U := (magnitude R).toNat
  let v1 := run (rotateLeft L.r) m s
  let ins : Program := [.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]
  let v2 := run ins m v1
  let v3 := run (signComplement L.sign L.y) m v2
  let v4 := run (signComplement L.lower L.y) m v3
  let v5 := run [.X L.ymsb] m v4
  have w := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have d := List.nodup_append'.mp (BalancedCleanup.Layout.dataND _ (L.cleanupND hn))
  have dr := d.1
  have dy := (List.nodup_append'.mp d.2.1).1
  have dis := d.2.2
  have away (q : Wire) (hq : q∈[L.sign,L.lower]) : q∉L.r ∧ q∉L.y := by
    have a := L.flagAway hn q (by simp only [List.mem_cons] at hq ⊢; tauto)
    exact ⟨fun h => a (by simp [h]),fun h => a (by simp [h])⟩
  have r0R : L.r0∈L.r := by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  have ymY : L.ymsb∈L.y := by simp [BalancedCleanup.Layout.y]
  have r0Y : L.r0∉L.y := fun h => List.disjoint_left.mp dis r0R (by simp [h])
  have ymR : L.ymsb∉L.r := fun h => List.disjoint_left.mp dis h (by simp [ymY])
  have sr : L.sign≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have lr : L.lower≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have rot0 := rotateLeft_spec L.r dr U (by
    have b := magnitude_bounds R hr
    have c := BalancedField.constants
    have u := Int.toNat_of_nonneg b.1
    rw [w.2.1]
    norm_num only [Nat.reducePow] at c ⊢
    omega) s m hR
  have rot := rot0.2
  have rotfr := (rotate_frame L.r s m).2.2.2
  have S1 : v1.basis L.sign=B := (rotfr _ (away _ (by simp)).1).trans hS
  have L1 : v1.basis L.lower=negative R := (rotfr _ (away _ (by simp)).1).trans hL
  have low0 : v1.basis L.r0=false := by
    change (if v1.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v1.basis=2*U at rot
    cases e : v1.basis L.r0
    · rfl
    · simp [e] at rot
      omega
  have tail1 : regValue (L.rtail++[L.rmsb]) v1.basis=U := by
    change (if v1.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v1.basis=2*U at rot
    rw [low0] at rot
    simp only [Bool.false_eq_true,if_false,zero_add] at rot
    omega
  have I2 : v2.basis L.r0=!(B ^^ negative R) := by
    cases b : B <;> cases l : negative R <;> simp [v2,ins,run,writeBit,sr,lr,S1,L1,low0,b,l]
  have out2 (q : Wire) (hq : q≠L.r0) : v2.basis q=v1.basis q := by simp [v2,ins,run,writeBit,hq]
  have S2 : v2.basis L.sign=B := (out2 _ sr).trans S1
  have L2 : v2.basis L.lower=negative R := (out2 _ lr).trans L1
  have tailAway : L.r0∉L.rtail++[L.rmsb] := (List.nodup_cons.mp dr).1
  have R2 : regValue L.r v2.basis=rawR B R := by
    change (if v2.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v2.basis=_
    rw [regValue_congr _ _ _ (fun q hq => out2 q (fun e => tailAway (e ▸ hq))),tail1,I2]
    cases e : !(B ^^ negative R) <;> simp [rawR,U,e,Nat.add_comm]
  have Y2 : regValue L.y v2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => (out2 q (fun e => r0Y (e ▸ hq))).trans
      (rotfr q (fun hrq => List.disjoint_left.mp dis hrq (by simp [hq]))))).trans hY
  have cS := signComplement_correct L.sign L.y dy (away _ (by simp)).2 v2 m
  have cL := signComplement_correct L.lower L.y dy (away _ (by simp)).2 v3 m
  have L3 : v3.basis L.lower=negative R := (cS.2.1 _ (away _ (by simp)).2).trans L2
  have R4 : regValue L.r v4.basis=rawR B R := by
    exact (regValue_congr _ _ _ (fun q hq => (cL.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))).trans (cS.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))))).trans R2
  have Y4 : regValue L.y v4.basis=encodeWord 256 (viewedY B R Y) := by
    rw [cL.2.2,cS.2.2,L3,S2,Y2,w.2.2.1]
    have hb := encodeWord_bound 256 Y
    have comp := BalancedCleanup.complement_encoded Y
    cases B <;> cases l : negative R <;> simp [viewedY,l] <;> omega
  have bvY := BalancedCleanup.bias_value L.ylow L.ymsb dy v4 m
  rw [hw.1.2.1] at bvY
  change (regValue L.y v5.basis : Int)=signedDecode 256 (regValue L.y v4.basis)+((2^255 : Nat) : Int) at bvY
  rw [Y4,(comparison_words_decode B R Y hr hy).2] at bvY
  have Y5 : regValue L.y v5.basis=biasedY B R Y := by
    have bv := biasedY_cast B R Y hr hy
    omega
  have R5 : regValue L.r v5.basis=rawR B R :=
    (regValue_congr _ _ _ (fun q hq => by simp [v5,run,writeBit,show q≠L.ymsb from fun e => ymR (e ▸ hq)])).trans R4
  have emptyRot (t : State) : run (rotateLeft L.r) (m.take 0) t=run (rotateLeft L.r) m t := by
    simpa only [(rotate_counts L.r).2.2.2] using run_take (rotateLeft L.r) m t
  have emptyS (t : State) : run (signComplement L.sign L.y) (m.take 0) t=run (signComplement L.sign L.y) m t := by
    simpa only [(signComplement_counts L.sign L.y).2] using run_take (signComplement L.sign L.y) m t
  have emptyL (t : State) : run (signComplement L.lower L.y) (m.take 0) t=run (signComplement L.lower L.y) m t := by
    simpa only [(signComplement_counts L.lower L.y).2] using run_take (signComplement L.lower L.y) m t
  have execute : run (view L) m s=v5 := by
    simp only [view,List.append_assoc,run_append,
      (rotate_counts L.r).2.2.2,(signComplement_counts L.sign L.y).2,
      (signComplement_counts L.lower L.y).2,measurementCount,List.drop_zero,emptyRot,emptyS,emptyL]
    rfl
  rw [execute]
  refine ⟨R5,Y5,?_⟩
  intro q qr qy
  have nr : q≠L.r0 := fun e => qr (e ▸ r0R)
  have ny : q≠L.ymsb := fun e => qy (e ▸ ymY)
  have v5q : v5.basis q=v4.basis q := by simp [v5,run,writeBit,ny]
  exact v5q.trans ((cL.2.1 q qy).trans ((cS.2.1 q qy).trans ((out2 q nr).trans (rotfr q qr))))

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetPrefix.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
open BalancedField

def front (L : Layout) : Program :=
  BalancedCleanup.prepareSign L.toCircuit.toLayout++view L++[.X L.cout]

theorem program_sandwich (L : Layout) : program L=
    front L++chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity++
      (front L).reverse := by
  simp only [program,front,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.append_assoc]

theorem front_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (front L) := by
  simp only [front,properProgram_append]
  exact ⟨⟨BalancedCleanup.prepareSign_proper _ (L.cleanupND hn),view_proper L hn⟩,
    by simp [ProperProgram,ProperGate]⟩

theorem front_parity_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.parity∉wires (front L) := by
  have a := (BalancedCleanup.clifford_parity_away L.toCircuit.toLayout hw.1 (L.cleanupND hn)).1
  have b := view_parity_away L hw hn
  have ne : L.parity≠L.cout := by
    have f := List.nodup_cons.mp (L.flagsND hn)
    exact fun e => f.1 (by simp [e])
  simpa only [front,wires_append,wires,Instr.wires,Finset.mem_union,
    Finset.mem_singleton,Finset.notMem_empty,or_false,not_or] using ⟨⟨a,b⟩,ne⟩

/-- All numeric reads are proved for the actual emitted front circuit.
The frame leaves the second carry bank and all caller metadata intact. -/
theorem front_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R)
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (hc : s.basis L.cout=false) :
    let t := run (front L) m s
    regValue L.r t.basis=rawR B R ∧ regValue L.y t.basis=biasedY B R Y ∧
    t.basis L.lower=negative R ∧ t.basis L.cout=true ∧
    (∀q,q∉L.r → q∉L.y → q≠L.lower → q≠L.cout → t.basis q=s.basis q) := by
  let u := run (BalancedCleanup.prepareSign L.toCircuit.toLayout) m s
  let v := run (view L) m u
  let t := run [.X L.cout] m v
  have sign := BalancedCleanup.prepareSign_value L.toCircuit.toLayout hw.1
    (L.cleanupND hn) R hr s m hR hz
  have all := List.nodup_append'.mp (L.allND hn)
  have d := List.nodup_append'.mp (BalancedCleanup.Layout.dataND _ (L.cleanupND hn))
  have lR : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have lY : L.lower∉L.y := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have cR : L.cout∉L.r := fun h => L.flagAway hn L.cout (by simp) (by simp [h])
  have cY : L.cout∉L.y := fun h => L.flagAway hn L.cout (by simp) (by simp [h])
  have sR : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have sl : L.sign≠L.lower := by
    have f := L.flagsND hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at f
    tauto
  have cl : L.cout≠L.lower := by
    have f := L.flagsND hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at f
    tauto
  have yu : regValue L.y u.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => sign.2.2 q
      (fun h => List.disjoint_left.mp d.2.2 h (by simp [hq]))
      (fun e => lY (e ▸ hq)))).trans hY
  have su : u.basis L.sign=B := (sign.2.2 _ sR sl).trans hS
  have cu : u.basis L.cout=false := (sign.2.2 _ cR cl).trans hc
  have value := view_value L hw hn R Y B hr hy u m sign.1 yu su sign.2.1
  have cv : v.basis L.cout=false := (value.2.2 _ cR cY).trans cu
  have execute : run (front L) m s=t := by
    have ps := properProgram_measurementCount _ (BalancedCleanup.prepareSign_proper _ (L.cleanupND hn))
    have pv := properProgram_measurementCount _ (view_proper L hn)
    have ep (z : State) : run (BalancedCleanup.prepareSign L.toCircuit.toLayout) (m.take 0) z=
        run (BalancedCleanup.prepareSign L.toCircuit.toLayout) m z := by
          simpa only [ps] using run_take (BalancedCleanup.prepareSign L.toCircuit.toLayout) m z
    have ev (z : State) : run (view L) (m.take 0) z=run (view L) m z := by
      simpa only [pv] using run_take (view L) m z
    simp only [front,List.append_assoc,run_append,ps,pv,List.drop_zero,ep,ev]
    rfl
  rw [execute]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => by simp [t,v,run,writeBit,show q≠L.cout from fun e => cR (e ▸ hq)])).trans value.1
  · exact (regValue_congr _ _ _ (fun q hq => by simp [t,v,run,writeBit,show q≠L.cout from fun e => cY (e ▸ hq)])).trans value.2.1
  · have lv := (value.2.2 _ lR lY).trans sign.2.1
    simpa [t,run,writeBit,Ne.symm cl] using lv
  · simp [t,run,writeBit,cv]
  · intro q qr qy ql qc
    have kept := (value.2.2 q qr qy).trans (sign.2.2 q qr ql)
    simpa [t,run,writeBit,qc] using kept

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetSlimLeafProof.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
open BalancedCleanupOffset
attribute [local irreducible] run mappedSum majority eraseCarry

def leaf (b : MappedBit) (a y cinC cinB d target : Wire) : Program :=
  mappedSum b y cinC++[.X y]++compareChain none [a] [y] [d] cinB target++
    [.X y]++mappedSum b y cinC

private theorem zero_records (P : Program) (h : measurementCount P=0)
    (s : State) (m n : List Bool) : run P m s=run P n s := by
  have x := run_take P m s
  have z := run_take P n s
  rw [h,List.take_zero] at x z
  exact x.symm.trans z
private theorem run_zero (P Q : Program) (h : measurementCount P=0) (s : State) (m : List Bool) :
    run (P++Q) m s=run Q m (run P m s) := by
  rw [run_append,h,List.take_zero,List.drop_zero,zero_records P h s [] m]
private theorem threshold (a b c : Bool) :
    decide (2 ≤ (if a then 1 else 0)+(if b then 1 else 0)+c.toNat)=carryBit a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem singleton_run (b : MappedBit) (a y cinC cinB c d target : Wire)
    (hn : [a,y,cinC,cinB,c,d,target].Nodup)
    (ha : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d,target])
    (s : State) (m : List Bool) (hd : s.basis d=false) :
    run (leaf b a y cinC cinB d target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^
        !(carryBit (s.basis a) (!(sumBit (b.value s.basis) (s.basis y) (s.basis cinC))) (s.basis cinB)))⟩ := by
  have nd := hn
  have nr := List.nodup_reverse.mpr hn
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd nr
  have src (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d,target]) : ∀w∈b.wire,w≠q :=
    fun w hw e => ha w hw (e.symm ▸ hq)
  have sm : measurementCount (mappedSum b y cinC)=0 := (mappedBit_counts b y cinC c).2.2.2.2.2
  have xm : measurementCount [.X y]=0 := rfl
  have pm : measurementCount (mappedSum b y cinC++[.X y])=0 := by
    rw [measurementCount_append,sm,xm]
  have cm : measurementCount (compareChain none [a] [y] [d] cinB target)=1 := by
    simp [compareChain,majority,eraseCarry,flipBelow,measurementCount_append,measurementCount]
  let B := b.value s.basis
  let Y := s.basis y
  let C := s.basis cinC
  let S := sumBit B Y C
  let u := run (mappedSum b y cinC++[.X y]) m s
  have pu : u=⟨s.phase,writeBit s.basis y (!S)⟩ := by
    dsimp only [u]
    rw [run_zero _ _ sm,mappedSum_correct b y cinC (by simp [nd,nr]) (src y (by simp)),x_run]
    apply State.extensionality
    · rfl
    · funext q
      by_cases eq : q=y <;> simp [writeBit,Function.update,eq,S,B,Y,C]
  let v := run (compareChain none [a] [y] [d] cinB target) m u
  have comp := compareChain_correct none [a] [y] [d] cinB target
    (by simp [List.nodup_cons,nd,nr]) (by simp) rfl rfl u m (by
      intro q hq
      have eq : q=d := List.mem_singleton.mp hq
      rw [eq]
      simpa [pu,writeBit,show d≠y by simp [nd,nr]] using hd)
  change v.phase=u.phase ∧ (∀q,q≠target → v.basis q=u.basis q) ∧ _ at comp
  have uf (q : Wire) (hq : q≠y) : u.basis q=s.basis q := by
    rw [pu]
    simp [writeBit,hq]
  have uy : u.basis y= !S := by rw [pu]; simp [writeBit]
  have value : v.basis target=(s.basis target ^^ !(carryBit (s.basis a) (!S) (s.basis cinB))) := by
    have raw := comp.2.2
    change v.basis target=(u.basis target ^^ !(decide (2 ≤
      (if u.basis a then 1 else 0)+(if u.basis y then 1 else 0)+(u.basis cinB).toNat))) at raw
    rw [threshold,uf target (by simp [nd,nr]),uf a (by simp [nd,nr]),uy,
      uf cinB (by simp [nd,nr])] at raw
    exact raw
  have vy : v.basis y= !S := (comp.2.1 y (by simp [nd,nr])).trans uy
  have vc : v.basis cinC=C := (comp.2.1 cinC (by simp [nd,nr])).trans (uf cinC (by simp [nd,nr]))
  have vb : b.value v.basis=B := by
    apply mappedBit_value_congr
    intro w hw
    exact (comp.2.1 w (src target (by simp) w hw)).trans (uf w (src y (by simp) w hw))
  have done : run (mappedSum b y cinC) (m.drop 1) (run [.X y] (m.drop 1) v)=
      ⟨v.phase,writeBit v.basis y Y⟩ := by
    rw [x_run,mappedSum_correct b y cinC (by simp [nd,nr]) (src y (by simp))]
    have source := (bit_write b v.basis y (!v.basis y) (src y (by simp))).trans vb
    have restored : sumBit (b.value (writeBit v.basis y (!v.basis y)))
        (!v.basis y) (v.basis cinC)=Y := by
      rw [source,vy,Bool.not_not,vc]
      exact sum_involution B Y C
    apply State.extensionality
    · rfl
    · funext q
      by_cases eq : q=y
      · rw [eq]
        simp only [writeBit,Function.update_self,
          Function.update_of_ne (show cinC≠y by simp [nd,nr])]
        exact restored
      · simp [writeBit,Function.update,eq]
  have shape : leaf b a y cinC cinB d target=(mappedSum b y cinC++[.X y])++
      (compareChain none [a] [y] [d] cinB target++([.X y]++mappedSum b y cinC)) := by
    simp only [leaf,List.append_assoc]
  have actual : run (leaf b a y cinC cinB d target) m s=
      run (mappedSum b y cinC) (m.drop 1) (run [.X y] (m.drop 1) v) := by
    rw [shape,run_zero _ _ pm,run_append]
    have take := run_take (compareChain none [a] [y] [d] cinB target) m u
    rw [cm] at take
    rw [cm,take,run_zero _ _ xm]
  rw [actual,done]
  apply State.extensionality
  · exact comp.1.trans (by rw [pu])
  · funext q
    by_cases qt : q=target
    · subst q
      simp [writeBit,show target≠y by simp [nd,nr],value,B,Y,C,S]
    · by_cases qy : q=y
      · subst q
        simp [writeBit,show y≠target by simp [nd,nr],Y]
      · simp [writeBit,qy,qt,comp.2.1 q qt,uf q qy]

end ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetSlimProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
open BalancedCleanupOffset
attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry wires

/-- The final offset carry is never read. The comparison still emits its
independent measured carry cleanup; no outcome or phase premise is assumed. -/
def chain : List MappedBit → List Wire → List Wire → List Wire → List Wire →
    Wire → Wire → Wire → Program
  | [b],[a],[y],[_c],[d],cinC,cinB,target =>
      mappedSum b y cinC++[.X y]++compareChain none [a] [y] [d] cinB target++
      [.X y]++mappedSum b y cinC
  | b::bits,a::as,y::ys,c::cs,d::ds,cinC,cinB,target =>
      prepareHead b a y cinC cinB c d++chain bits as ys cs ds c d target++
      releaseHead b a y cinC cinB c d
  | [],[],[],[],[],_,cinB,target => flipBelow none cinB target
  | _,_,_,_,_,_,_,_ => []

def program (L : Layout) : Program :=
  front L++chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity++
    (front L).reverse

private theorem chain_facts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 1) ∧
    measurementCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 1) ∧
    wires (chain bits xs ys cs ds cinC cinB target)⊆
      wires (BalancedCleanupOffset.chain bits xs ys cs ds cinC cinB target) := by
  induction ys generalizing bits xs cs ds cinC cinB with
  | nil =>
    have b := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have x := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have c := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have d := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    simp [chain,BalancedCleanupOffset.chain,flipBelow,toffoliCount,measurementCount]
  | cons y ys ih =>
    cases bits with
    | nil => simp at hb
    | cons b bits =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          cases ds with
          | nil => simp at hd
          | cons d ds =>
            cases ys with
            | nil =>
              have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
              have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
              have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
              have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
              subst bits xs cs ds
              have sum := mappedBit_counts b y cinC c
              have comparator := compareChain_counts none [a] [y] [d] cinB target rfl rfl
              refine ⟨?_,?_,?_⟩
              · simp only [chain,toffoliCount_append,sum.2.2.2.2.1,comparator.1]
                norm_num [toffoliCount]
              · simp only [chain,measurementCount_append,sum.2.2.2.2.2,comparator.2]
                norm_num [measurementCount]
              · intro q hq
                simp only [chain,BalancedCleanupOffset.chain,compareChain,wires_append,
                  Finset.mem_union] at hq ⊢
                tauto
            | cons y' ys =>
              cases bits with
              | nil => simp at hb
              | cons b' bits =>
                have emitted : chain (b::b'::bits) (a::xs) (y::y'::ys) (c::cs) (d::ds) cinC cinB target=
                    prepareHead b a y cinC cinB c d++chain (b'::bits) xs (y'::ys) cs ds c d target++
                    releaseHead b a y cinC cinB c d := rfl
                have original : BalancedCleanupOffset.chain (b::b'::bits) (a::xs) (y::y'::ys)
                    (c::cs) (d::ds) cinC cinB target=
                    prepareHead b a y cinC cinB c d++BalancedCleanupOffset.chain (b'::bits)
                      xs (y'::ys) cs ds c d target++releaseHead b a y cinC cinB c d := by
                  rw [BalancedCleanupOffset.chain]
                  simp only [prepareHead,releaseHead,List.append_assoc]
                have tail := ih (b'::bits) xs cs ds c d (by simpa using hb)
                  (by simpa using hx) (by simpa using hc) (by simpa using hd)
                rcases mappedBit_counts b y cinC c with ⟨mt,mm,et,em,st,sm⟩
                have majT : toffoliCount (majority a y cinB d)=1 := by simp [majority,toffoliCount]
                have majM : measurementCount (majority a y cinB d)=0 := by simp [majority,measurementCount]
                have eraseT : toffoliCount (eraseCarry a y cinB d)=0 := rfl
                have eraseM : measurementCount (eraseCarry a y cinB d)=1 := rfl
                refine ⟨?_,?_,?_⟩
                · simp only [emitted,prepareHead,releaseHead,toffoliCount_append,
                    mt,et,st,majT,eraseT,tail.1]
                  simp [toffoliCount,List.length_cons]
                  omega
                · simp only [emitted,prepareHead,releaseHead,measurementCount_append,
                    mm,em,sm,majM,eraseM,tail.2.1]
                  simp [measurementCount,List.length_cons]
                  omega
                · intro q hq
                  have recurse : q∈wires (chain (b'::bits) xs (y'::ys) cs ds c d target) →
                      q∈wires (BalancedCleanupOffset.chain (b'::bits) xs (y'::ys) cs ds c d target) := fun h => tail.2.2 h
                  simp only [emitted,original,prepareHead,releaseHead,
                    wires_append,Finset.mem_union,or_assoc] at hq ⊢
                  tauto

theorem chain_counts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 1) ∧
    measurementCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 1) := by
  have facts := chain_facts bits xs ys cs ds cinC cinB target hb hx hc hd
  exact ⟨facts.1,facts.2.1⟩

theorem chain_support (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    wires (chain bits xs ys cs ds cinC cinB target)⊆
      wires (BalancedCleanupOffset.chain bits xs ys cs ds cinC cinB target) :=
  (chain_facts bits xs ys cs ds cinC cinB target hb hx hc hd).2.2

theorem front_counts (L : Layout) : toffoliCount (front L)=0 ∧ measurementCount (front L)=0 := by
  have rotate := rotate_counts L.r
  have s := signComplement_counts L.sign L.y
  have l := signComplement_counts L.lower L.y
  have r := signComplement_counts L.lower L.r
  simp only [front,view,BalancedCleanup.prepareSign,toffoliCount_append,measurementCount_append,
    rotate.2.2.1,rotate.2.2.2,s.1,s.2,l.1,l.2,r.1,r.2]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetSlimChainProof.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
open BalancedCleanupOffset
attribute [local irreducible] run chain prepareHead releaseHead

/-- Actual two-prefix circuit, with no tail-circuit premise. The explicit
Boolean recurrence is the offset carry followed by the comparison carry.
Every physical bit except target is restored, including both full banks. -/
theorem chain_run (bits : List MappedBit) (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hn : (target::cinC::cinB::(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉target::cinC::cinB::(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (m : List Bool) (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false) :
    run (chain bits xs ys cs ds cinC cinB target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^
        decision (bits.map (fun b => b.value s.basis)) (xs.map s.basis) (ys.map s.basis)
          (s.basis cinC) (s.basis cinB))⟩ := by
  induction ys generalizing bits xs cs ds cinC cinB s m with
  | nil =>
    have eb := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have ex := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have ec := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have ed := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    have ne : target≠cinB := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
        not_or,not_false_eq_true,and_true] at hn
      tauto
    simpa only [chain,decision,List.map_nil,controlValue,Bool.true_and] using
      flipBelow_correct none cinB target ne (by simp) s m
  | cons y ys ih =>
    cases bits with
    | nil => simp at hb
    | cons b bits =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          cases ds with
          | nil => simp at hd
          | cons d ds =>
            by_cases lone : ys=[]
            · subst ys
              have eb := List.eq_nil_of_length_eq_zero (by simpa using hb)
              have ex := List.eq_nil_of_length_eq_zero (by simpa using hx)
              have ec := List.eq_nil_of_length_eq_zero (by simpa using hc)
              have ed := List.eq_nil_of_length_eq_zero (by simpa using hd)
              subst bits xs cs ds
              have full := head_tail_nd target cinC cinB a y c d [] [] [] [] hn
              have head := (List.nodup_append'.mp full).1
              have fresh : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d,target] := by
                intro w hw hq
                apply ha w (mapped_member b [] w hw)
                simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
                tauto
              have one := singleton_run b a y cinC cinB c d target head fresh s m (hdd d (by simp))
              simpa only [chain,leaf,decision,List.map_cons,List.map_nil] using one
            ·
              have full := head_tail_nd target cinC cinB a y c d xs ys cs ds hn
              have hs := (List.nodup_append'.mp full).1
              have six := head_six_nd a y cinC cinB c d target hs
              have nd := hs
              simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
                not_or,not_false_eq_true,and_true] at nd
              rcases nd with ⟨⟨a_y,a_iC,a_iB,a_c,a_d,a_t⟩,
                ⟨y_iC,y_iB,y_c,y_d,y_t⟩,⟨iC_iB,iC_c,iC_d,iC_t⟩,
                ⟨iB_c,iB_d,iB_t⟩,⟨c_d,c_t⟩,d_t⟩
              have sourceHead (w : Wire) (hw : w∈mappedWires (b::bits))
                  (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d,target]) : w≠q :=
                fun e => ha w hw (head_mem_scope target cinC cinB a y c d w xs ys cs ds (e.symm ▸ hq))
              have srcB (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d,target]) : ∀w∈b.wire,w≠q :=
                fun w hw => sourceHead w (mapped_member b bits w hw) q hq
              have headSource : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d] := by
                intro w hw hq
                have hq' : w∈[a,y,cinC,cinB,c,d,target] := by
                  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto
                exact sourceHead w (mapped_member b bits w hw) w hq' rfl
              let B := b.value s.basis
              let A := s.basis a
              let Y := s.basis y
              let C := s.basis cinC
              let E := s.basis cinB
              let K := carryBit B Y C
              let S := sumBit B Y C
              let D := carryBit A (!S) E
              let u : State := ⟨s.phase,writeBit (writeBit (writeBit s.basis c K) y (!S)) d D⟩
              have pre : run (prepareHead b a y cinC cinB c d) m s=u :=
                prepareHead_run b a y cinC cinB c d six headSource s m
                  (hcc c (by simp)) (hdd d (by simp))
              have uf (q : Wire) (n1 : q≠c) (n2 : q≠y) (n3 : q≠d) : u.basis q=s.basis q := by
                simp only [u,writeBit,Function.update_of_ne n1,Function.update_of_ne n2,
                  Function.update_of_ne n3]
              have tailNe (q : Wire) (hq : q∈xs++ys++cs++ds) (t : Wire)
                  (ht : t∈[a,y,cinC,cinB,c,d,target]) : q≠t :=
                tail_away_head target cinC cinB a y c d q t xs ys cs ds hn hq ht
              have tailSame (q : Wire) (hq : q∈xs++ys++cs++ds) : u.basis q=s.basis q :=
                uf q (tailNe q hq c (by simp)) (tailNe q hq y (by simp)) (tailNe q hq d (by simp))
              have mapA : xs.map u.basis=xs.map s.basis := by
                apply List.map_congr_left
                intro q hq
                exact tailSame q (by simp [hq])
              have mapY : ys.map u.basis=ys.map s.basis := by
                apply List.map_congr_left
                intro q hq
                exact tailSame q (by simp [hq])
              have sourceSame (w : Wire) (hw : w∈mappedWires (b::bits)) : u.basis w=s.basis w :=
                uf w (sourceHead w hw c (by simp)) (sourceHead w hw y (by simp))
                  (sourceHead w hw d (by simp))
              have mapBits : bits.map (fun b => b.value u.basis)=bits.map (fun b => b.value s.basis) := by
                apply List.map_congr_left
                intro bit hbit
                apply mappedBit_value_congr
                intro w hw
                have mem : w∈mappedWires bits := by
                  apply List.mem_flatMap.mpr
                  refine ⟨bit,hbit,?_⟩
                  cases he : bit.wire with
                  | none => simp [he] at hw
                  | some wire =>
                    have eq : wire=w := by simpa [he] using hw
                    subst w
                    simp [he]
                exact sourceSame w (mapped_tail_member b bits w mem)
              have uk : u.basis c=K := by simp only [u,writeBit,Function.update_of_ne
                c_d,Function.update_of_ne
                (Ne.symm y_c),Function.update_self]
              have ud : u.basis d=D := by simp only [u,writeBit,Function.update_self]
              have nt := recursive_nd target cinC cinB a y c d xs ys cs ds hn
              have tailSource : ∀w∈mappedWires bits,w∉target::c::d::(xs++ys++cs++ds) := by
                intro w hw hm
                exact ha w (mapped_tail_member b bits w hw)
                  (tail_mem_scope target cinC cinB a y c d w xs ys cs ds hm)
              have cc : ∀q∈cs,u.basis q=false := fun q hq =>
                (tailSame q (by simp [hq])).trans (hcc q (by simp [hq]))
              have dd : ∀q∈ds,u.basis q=false := fun q hq =>
                (tailSame q (by simp [hq])).trans (hdd q (by simp [hq]))
              have tail := ih bits xs cs ds c d nt tailSource (by simpa using hb) (by simpa using hx)
                (by simpa using hc) (by simpa using hd) u m cc dd
              rw [mapBits,mapA,mapY,uk,ud] at tail
              let V := decision (bits.map (fun b => b.value s.basis)) (xs.map s.basis)
                (ys.map s.basis) K D
              let v : State := ⟨u.phase,writeBit u.basis target (u.basis target ^^ V)⟩
              change run (chain bits xs ys cs ds c d target) m u=v at tail
              have vf (q : Wire) (hq : q≠target) : v.basis q=u.basis q := by
                simp only [v,writeBit,Function.update_of_ne hq]
              have bu : b.value u.basis=B := mappedBit_value_congr b u.basis s.basis
                (fun w hw => sourceSame w (mapped_member b bits w hw))
              have bv : b.value v.basis=B := by
                apply Eq.trans _ bu
                apply mappedBit_value_congr
                intro w hw
                exact vf w (srcB target (by simp) w hw)
              have va : v.basis a=A := (vf a a_t).trans (uf a a_c a_y a_d)
              have vc : v.basis cinC=C := (vf cinC iC_t).trans (uf cinC iC_c (Ne.symm y_iC) iC_d)
              have ve : v.basis cinB=E := (vf cinB iB_t).trans (uf cinB iB_c (Ne.symm y_iB) iB_d)
              have vy : v.basis y= !S := by
                rw [vf y y_t]
                simp only [u,writeBit,Function.update_of_ne y_d,Function.update_self]
              have vk : v.basis c=K := (vf c c_t).trans uk
              have vd : v.basis d=D := (vf d d_t).trans ud
              let rest := m.drop (measurementCount (chain bits xs ys cs ds c d target))
              have post := releaseHead_run b a y cinC cinB c d six headSource B A Y C E v rest
                bv va vc ve vy vk vd
              have emitted : chain (b::bits) (a::xs) (y::ys) (c::cs) (d::ds) cinC cinB target=
                  prepareHead b a y cinC cinB c d++(chain bits xs ys cs ds c d target++
                    releaseHead b a y cinC cinB c d) := by
                cases ys with
                | nil => exact (lone rfl).elim
                | cons y' ys =>
                  cases bits with
                  | nil => simp at hb
                  | cons b' bits =>
                    cases xs with
                    | nil => simp at hx
                    | cons a' xs =>
                      cases cs with
                      | nil => simp at hc
                      | cons c' cs =>
                        cases ds with
                        | nil => simp at hd
                        | cons d' ds =>
                          rw [chain,List.append_assoc]
                          all_goals simp
              rw [emitted,run_append,run_take,pre,prepareHead_measurements,List.drop_zero,
                run_append,run_take,tail,post]
              apply State.extensionality
              · rfl
              · funext q
                have cz : s.basis c=false := hcc c (by simp)
                have dz : s.basis d=false := hdd d (by simp)
                by_cases qt : q=target
                · subst q
                  simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                    Function.update_of_ne (Ne.symm c_t),Function.update_of_ne (Ne.symm y_t),
                    Function.update_of_ne (Ne.symm d_t),Function.update_self]
                · by_cases qc : q=c
                  · subst q
                    simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                      Function.update_self,Function.update_of_ne c_t,cz]
                  · by_cases qy : q=y
                    · subst q
                      simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                        Function.update_of_ne y_c,Function.update_of_ne y_t,Function.update_self]
                    · by_cases qd : q=d
                      · subst q
                        simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                          Function.update_of_ne (Ne.symm c_d),Function.update_of_ne (Ne.symm y_d),
                          Function.update_of_ne d_t,Function.update_self,dz]
                      · simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                          Function.update_of_ne qt,Function.update_of_ne qc,
                          Function.update_of_ne qy,Function.update_of_ne qd]


end ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetSlimProof.lean
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
open BalancedCleanupOffset BalancedField
attribute [local irreducible] run chain

theorem program_sandwich (L : Layout) : program L=
    front L++chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity++
      (front L).reverse := rfl

theorem chain_compare (bits : List MappedBit) (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hn : (target::cinC::cinB::(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉target::cinC::cinB::(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (m : List Bool) (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false)
    (hi : s.basis cinB=true) :
    run (chain bits xs ys cs ds cinC cinB target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^
        decide (regValue xs s.basis<(mappedValue bits s.basis+regValue ys s.basis+
          (s.basis cinC).toNat)%2^ys.length))⟩ := by
  have h := chain_run bits xs ys cs ds cinC cinB target hn ha hb hx hc hd s m hcc hdd
  have v := decision_value (bits.map (fun b => b.value s.basis)) (xs.map s.basis)
    (ys.map s.basis) (by simpa using hb) (by simpa using hx) (s.basis cinC)
  rw [mapped_value_map,word_value_map,word_value_map,List.length_map] at v
  rw [hi,v] at h
  exact h


private theorem bank_away (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.carry++L.offsetCarry) :
    q∉L.r ∧ q∉L.y ∧ q≠L.lower ∧ q≠L.cout := by
  have nd : (L.r++(L.y++(L.carry++L.offsetCarry))).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (L.allND hn)).2.1
  have r := List.nodup_append'.mp nd
  have y := List.nodup_append'.mp r.2.1
  refine ⟨fun h => List.disjoint_left.mp r.2.2 h (List.mem_append_right _ hq),
    fun h => List.disjoint_left.mp y.2.2 h hq,?_,?_⟩
  · intro e
    exact L.flagAway hn L.lower (by simp) (by simp [←e,List.mem_append.mp hq])
  · intro e
    exact L.flagAway hn L.cout (by simp) (by simp [←e,List.mem_append.mp hq])

/-- Complete exact measured cleanup, restoring every site except the cleared
parity bit, and preserving phase for every measurement record. Both carry
banks must be supplied clean by the caller's actual allocation invariant. -/
theorem xor_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R)
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false)
    (ho : s.basis L.one=false) (hcout : s.basis L.cout=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hd : ∀q∈L.offsetCarry,s.basis q=false)
    : run (program L) m s=⟨s.phase,writeBit s.basis L.parity
      (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|))⟩ := by
  let u := run (front L) m s
  let cell := chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity
  let v := run cell m u
  let n := m.drop (measurementCount cell)
  have prepared := front_value L hw hn R Y B hr hy s m hR hY hS hz hcout
  have flags := L.flagsND hn
  have flagFacts := flags
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flagFacts
  have pR : L.parity∉L.r := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have pY : L.parity∉L.y := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have oR : L.one∉L.r := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have oY : L.one∉L.y := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have pl : L.parity≠L.lower := by tauto
  have pc : L.parity≠L.cout := by tauto
  have ol : L.one≠L.lower := by tauto
  have oc : L.one≠L.cout := by tauto
  have one : u.basis L.one=false := (prepared.2.2.2.2 _ oR oY ol oc).trans ho
  have parity : u.basis L.parity=s.basis L.parity :=
    prepared.2.2.2.2 _ pR pY pl pc
  have cleanC : ∀q∈L.carry,u.basis q=false := by
    intro q hq
    have away := bank_away L hn q (List.mem_append_left _ hq)
    exact (prepared.2.2.2.2 q away.1 away.2.1 away.2.2.1 away.2.2.2).trans (hc q hq)
  have cleanD : ∀q∈L.offsetCarry,u.basis q=false := by
    intro q hq
    have away := bank_away L hn q (List.mem_append_right _ hq)
    exact (prepared.2.2.2.2 q away.1 away.2.1 away.2.2.1 away.2.2.2).trans (hd q hq)
  have widths := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cmp := chain_compare (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout
    L.parity (L.chainND hn) (offsetSources_away L hn)
    (by rw [offsetBits_length,widths.2.1]) (by omega) (by rw [hw.2,widths.2.1])
    (by rw [hw.1.2.2,widths.2.1]) u m cleanD cleanC prepared.2.2.2.1
  have pred : decide (regValue L.y u.basis <
      (mappedValue (offsetBits L) u.basis+regValue L.r u.basis+(u.basis L.one).toNat)%2^L.r.length)=
      decide (q < |2*R-signedY B Y|) := by
    rw [prepared.1,prepared.2.1,offsetBits_value,prepared.2.2.1,one,widths.2.1]
    simp only [Bool.toNat_false,Nat.add_zero]
    exact decide_eq_decide.mpr (chain_predicate B R Y hr hy)
  have clear : v=⟨u.phase,writeBit u.basis L.parity
      (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|))⟩ := by
    change run cell m u=_
    rw [cmp,pred,parity]
  have except := BalancedCleanup.inverse_except (front L) (front_proper L hn) L.parity
    (front_parity_away L hw hn) s v m n (by
      rw [clear]
      exact ⟨rfl,fun q hq => by simp [writeBit,hq,u]⟩)
  have kept := run_preserves_outside (front L).reverse n v L.parity (by
    rw [wires_reverse]
    exact front_parity_away L hw hn)
  have zero : (run (front L).reverse n v).basis L.parity=
      (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|)) := by
    rw [kept,clear]
    simp [writeBit]
  have execute : run (program L) m s=run (front L).reverse n v := by
    have mc := properProgram_measurementCount _ (front_proper L hn)
    have empty : run (front L) (m.take 0) s=run (front L) m s := by
      simpa only [mc] using run_take (front L) m s
    rw [program_sandwich,List.append_assoc,run_append,mc,List.drop_zero,empty,
      run_append,run_take]
  rw [execute]
  apply State.extensionality
  · exact except.1
  · funext q
    by_cases e : q=L.parity
    · subst q
      simpa [writeBit] using zero
    · simpa [writeBit,e] using except.2 q e

end ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetZeroHead.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroHead
open BalancedCleanupOffset
attribute [local irreducible] run BalancedCleanupOffsetSlim.chain majority eraseCarry

/-- Offset bit0 and its incoming carry are both zero. The comparison carry
is still computed and measured cleanly; the offset carry is never emitted. -/
def program (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire) : Program :=
  ([.X y]++majority a y cinB d)++
    (BalancedCleanupOffsetSlim.chain bits xs ys cs ds cinC d target++
      (eraseCarry a y cinB d++[.X y]))

private theorem zero_records (P : Program) (h : measurementCount P=0)
    (s : State) (m n : List Bool) : run P m s=run P n s := by
  have x := run_take P m s
  have z := run_take P n s
  rw [h,List.take_zero] at x z
  exact x.symm.trans z
private theorem run_zero (P Q : Program) (h : measurementCount P=0) (s : State) (m : List Bool) :
    run (P++Q) m s=run Q m (run P m s) := by
  rw [run_append,h,List.take_zero,List.drop_zero,zero_records P h s [] m]

/-- Exact full-state semantics, including arbitrary incoming phase and all
independent measurement records. Both tail banks and d are restored. -/
theorem run_correct (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire)
    (hn : ([a,y,cinC,cinB,d,target]++(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉[a,y,cinC,cinB,d,target]++(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (m : List Bool) (hz : s.basis cinC=false) (hzD : s.basis d=false)
    (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false) :
    run (program bits xs ys cs ds a y cinC cinB d target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^
        decision (false::bits.map (fun b => b.value s.basis))
          (s.basis a::xs.map s.basis) (s.basis y::ys.map s.basis) false (s.basis cinB))⟩ := by
  have full := List.nodup_append'.mp hn
  have nd := full.1
  have nr := List.nodup_reverse.mpr nd
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd nr
  have majND : [a,y,cinB,d].Nodup := by simp [List.nodup_cons,nd,nr]
  let A := s.basis a
  let Y := s.basis y
  let E := s.basis cinB
  let D := carryBit A (!Y) E
  let u : State := ⟨s.phase,writeBit (writeBit s.basis y (!Y)) d D⟩
  have pm : measurementCount ([.X y]++majority a y cinB d)=0 := by
    simp [measurementCount_append,majority,measurementCount]
  have pre : run ([.X y]++majority a y cinB d) m s=u := by
    rw [run_zero _ _ (show measurementCount [.X y]=0 from rfl),x_run,
      majority_correct a y cinB d majND]
    simp only [writeBit,Function.update_of_ne (show d≠y by simp [nd,nr]),
      Function.update_of_ne (show a≠y by simp [nd,nr]),
      Function.update_of_ne (show cinB≠y by simp [nd,nr]),Function.update_self,
      hzD,Bool.false_xor]
    rfl
  have uf (q : Wire) (qy : q≠y) (qd : q≠d) : u.basis q=s.basis q := by
    simp only [u,writeBit,Function.update_of_ne qy,Function.update_of_ne qd]
  have tailNe (q : Wire) (hq : q∈xs++ys++cs++ds) (h : Wire)
      (hh : h∈[a,y,cinC,cinB,d,target]) : q≠h := by
    intro eq
    exact List.disjoint_left.mp full.2.2 hh (eq ▸ hq)
  have same (q : Wire) (hq : q∈xs++ys++cs++ds) : u.basis q=s.basis q :=
    uf q (tailNe q hq y (by simp)) (tailNe q hq d (by simp))
  have mapA : xs.map u.basis=xs.map s.basis := by
    apply List.map_congr_left
    intro q hq
    exact same q (by simp [hq])
  have mapY : ys.map u.basis=ys.map s.basis := by
    apply List.map_congr_left
    intro q hq
    exact same q (by simp [hq])
  have src (q : Wire) (hq : q∈[a,y,cinC,cinB,d,target])
      (w : Wire) (hw : w∈mappedWires bits) : w≠q := by
    intro eq
    exact ha w hw (List.mem_append_left _ (eq.symm ▸ hq))
  have mapBits : bits.map (fun b => b.value u.basis)=bits.map (fun b => b.value s.basis) := by
    apply List.map_congr_left
    intro bit hbit
    apply mappedBit_value_congr
    intro w hw
    have member : w∈mappedWires bits := by
      apply List.mem_flatMap.mpr
      refine ⟨bit,hbit,?_⟩
      cases he : bit.wire with
      | none => simp [he] at hw
      | some wire =>
        have eq : wire=w := by simpa [he] using hw
        subst w
        simp [he]
    exact uf w (src y (by simp) w member) (src d (by simp) w member)
  have tailND : (target::cinC::d::(xs++ys++cs++ds)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have tailFresh : ∀w∈mappedWires bits,w∉target::cinC::d::(xs++ys++cs++ds) := by
    intro w hw hm
    apply ha w hw
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hm ⊢
    tauto
  have uc : u.basis cinC=false := (uf cinC (by simp [nd,nr]) (by simp [nd,nr])).trans hz
  have ud : u.basis d=D := by simp only [u,writeBit,Function.update_self]
  have cleanC : ∀q∈cs,u.basis q=false := fun q hq => (same q (by simp [hq])).trans (hcc q hq)
  have cleanD : ∀q∈ds,u.basis q=false := fun q hq => (same q (by simp [hq])).trans (hdd q hq)
  have tail := BalancedCleanupOffsetSlim.chain_run bits xs ys cs ds cinC d target tailND
    tailFresh hb hx hc hd u m cleanC cleanD
  rw [mapBits,mapA,mapY,uc,ud] at tail
  let V := decision (bits.map (fun b => b.value s.basis)) (xs.map s.basis) (ys.map s.basis) false D
  let v : State := ⟨u.phase,writeBit u.basis target (u.basis target ^^ V)⟩
  change run (BalancedCleanupOffsetSlim.chain bits xs ys cs ds cinC d target) m u=v at tail
  have vf (q : Wire) (hq : q≠target) : v.basis q=u.basis q := by
    simp only [v,writeBit,Function.update_of_ne hq]
  have va : v.basis a=A := (vf a (by simp [nd,nr])).trans (uf a (by simp [nd,nr]) (by simp [nd,nr]))
  have ve : v.basis cinB=E := (vf cinB (by simp [nd,nr])).trans
    (uf cinB (by simp [nd,nr]) (by simp [nd,nr]))
  have vy : v.basis y= !Y := by
    rw [vf y (by simp [nd,nr])]
    simp only [u,writeBit,Function.update_of_ne (show y≠d by simp [nd,nr]),Function.update_self]
  have vd : v.basis d=D := (vf d (by simp [nd,nr])).trans ud
  have post (n : List Bool) : run (eraseCarry a y cinB d++[.X y]) n v=
      ⟨v.phase,writeBit (writeBit v.basis d false) y Y⟩ := by
    have carry : v.basis d=carryBit (v.basis a) (v.basis y) (v.basis cinB) := by
      rw [vd,va,vy,ve]
    rw [run_append,run_take,eraseCarry_correct a y cinB d
      (by simp [nd,nr]) (by simp [nd,nr]) (by simp [nd,nr]) v carry,x_run]
    simp only [writeBit,Function.update_of_ne (show y≠d by simp [nd,nr]),vy,Bool.not_not]
  rw [program,run_zero _ _ pm,pre,run_append,run_take,tail,post]
  apply State.extensionality
  · rfl
  · funext q
    have boolean : carryBit false Y false=false ∧ sumBit false Y false=Y := by
      cases Y <;> decide
    by_cases qt : q=target
    · subst q
      simp only [u,v,V,D,A,Y,E,decision,boolean.1,boolean.2,writeBit,
        Function.update_of_ne (show target≠y by simp [nd,nr]),
        Function.update_of_ne (show target≠d by simp [nd,nr]),Function.update_self]
    · by_cases qy : q=y
      · subst q
        simp only [u,v,Y,writeBit,Function.update_self,
          Function.update_of_ne (show y≠target by simp [nd,nr])]
      · by_cases qd : q=d
        · subst q
          simp only [u,v,writeBit,Function.update_of_ne qy,Function.update_self,
            Function.update_of_ne (show d≠target by simp [nd,nr]),hzD]
        · simp only [u,v,writeBit,Function.update_of_ne qt,
            Function.update_of_ne qy,Function.update_of_ne qd]

/-- Exact emitted prefix cost. For a255-bit tail this is510 T/M. -/
theorem counts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (program bits xs ys cs ds a y cinC cinB d target)=
      1+(2*ys.length-(if ys.length=0 then 0 else 1)) ∧
    measurementCount (program bits xs ys cs ds a y cinC cinB d target)=
      1+(2*ys.length-(if ys.length=0 then 0 else 1)) := by
  have tail := BalancedCleanupOffsetSlim.chain_counts bits xs ys cs ds cinC d target hb hx hc hd
  simp only [program,toffoliCount_append,measurementCount_append,tail.1,tail.2]
  constructor <;> simp [majority,eraseCarry,toffoliCount,measurementCount,Nat.add_comm]


/-- Independent old/new record lists give the same complete State. The old
unused offset-carry site c0 is supplied clean by the existing bank contract. -/
theorem chain_equiv (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y c0 d cinC cinB target : Wire)
    (hn : (target::cinC::cinB::((a::xs)++(y::ys)++(c0::cs)++(d::ds))).Nodup)
    (ha : ∀w∈mappedWires bits,w∉target::cinC::cinB::((a::xs)++(y::ys)++(c0::cs)++(d::ds)))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (mOld mNew : List Bool) (hz : s.basis cinC=false)
    (hcc : ∀q∈c0::cs,s.basis q=false) (hdd : ∀q∈d::ds,s.basis q=false) :
    run (BalancedCleanupOffsetSlim.chain (⟨none,false⟩::bits) (a::xs) (y::ys)
      (c0::cs) (d::ds) cinC cinB target) mOld s =
    run (program bits xs ys cs ds a y cinC cinB d target) mNew s := by
  have nd : ([a,y,cinC,cinB,d,target]++(xs++ys++cs++ds)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have fresh : ∀w∈mappedWires bits,w∉[a,y,cinC,cinB,d,target]++(xs++ys++cs++ds) := by
    intro w hw hm
    apply ha w hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
    tauto
  have old := BalancedCleanupOffsetSlim.chain_run (⟨none,false⟩::bits) (a::xs) (y::ys)
    (c0::cs) (d::ds) cinC cinB target hn (by
      intro w hw
      apply ha w
      simpa [mappedWires] using hw)
    (by simpa using hb) (by simpa using hx) (by simpa using hc) (by simpa using hd) s mOld hcc hdd
  have freshRun := run_correct bits xs ys cs ds a y cinC cinB d target nd fresh hb hx hc hd
    s mNew hz (hdd d (by simp)) (fun q hq => hcc q (by simp [hq])) (fun q hq => hdd q (by simp [hq]))
  rw [old,freshRun]
  simp [MappedBit.value,hz]
end ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroHead
end

-- source: ECDSAAdd/Arithmetic/BalancedCleanupOffsetZeroProgram.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero
open BalancedCleanupOffset BalancedField
attribute [local irreducible] run BalancedCleanupOffsetSlim.chain

def core (L : Layout) : Program :=
  BalancedCleanupOffsetZeroHead.program (offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail (L.y.headD 0) (L.r.headD 0) L.one L.cout
    (L.carry.headD 0) L.parity

def program (L : Layout) : Program := front L++core L++(front L).reverse
attribute [local irreducible] core

private theorem offset_head (L : Layout) :
    offsetBits L=({wire:=none,flip:=false} : MappedBit)::(offsetBits L).tail := by
  have zero : offset.testBit 0=false := by decide
  have range : List.range 256=0::(List.range 255).map Nat.succ := List.range_succ_eq_map
  simp only [offsetBits,range,List.map_cons]
  simp only [show ¬((0 : Nat)=1) from by decide,if_false,zero,List.tail_cons]

private theorem tails (L : Layout) (hw : L.Widths) :
    (offsetBits L).tail.length=255 ∧ L.y.tail.length=255 ∧ L.r.tail.length=255 ∧
    L.offsetCarry.tail.length=255 ∧ L.carry.tail.length=255 := by
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  simp only [List.length_tail,offsetBits_length,width.2.1,width.2.2.1,hw.2,cy]
  decide

private theorem heads (L : Layout) (hw : L.Widths) :
    ∃ a xs y ys c cs d ds, L.y=a::xs ∧ L.r=y::ys ∧ L.offsetCarry=c::cs ∧ L.carry=d::ds ∧
      xs.length=255 ∧ ys.length=255 ∧ cs.length=255 ∧ ds.length=255 := by
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have ylen : L.y.length=256 := width.2.2.1
  have rlen : L.r.length=256 := width.2.1
  have clen : L.offsetCarry.length=256 := hw.2
  have dlen : L.carry.length=256 := hw.1.2.2
  cases ey : L.y with
  | nil => simp [ey] at ylen
  | cons a xs =>
    cases er : L.r with
    | nil => simp [er] at rlen
    | cons y ys =>
      cases ec : L.offsetCarry with
      | nil => simp [ec] at clen
      | cons c cs =>
        cases ed : L.carry with
        | nil => simp [ed] at dlen
        | cons d ds =>
          refine ⟨a,xs,y,ys,c,cs,d,ds,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
          all_goals
            simp only [ey,er,ec,ed,List.length_cons] at ylen rlen clen dlen
            omega

/-- The skipped carry is replaced by the same known-zero One input in the
actual emitted tail. The two circuits may use completely independent records. -/
theorem core_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (mOld mNew : List Bool) (hz : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hd : ∀q∈L.offsetCarry,s.basis q=false) :
    run (BalancedCleanupOffsetSlim.chain (offsetBits L) L.y L.r L.offsetCarry L.carry
      L.one L.cout L.parity) mOld s=run (core L) mNew s := by
  obtain ⟨a,xs,y,ys,c,cs,d,ds,ey,er,ec,ed,lx,ly,lc,ld⟩ := heads L hw
  have bitlen : (offsetBits L).tail.length=255 := (tails L hw).1
  have nd := L.chainND hn
  rw [ey,er,ec,ed] at nd
  have fresh : ∀w∈mappedWires (offsetBits L).tail,
      w∉L.parity::L.one::L.cout::((a::xs)++(y::ys)++(c::cs)++(d::ds)) := by
    intro w hq
    have mem : w∈mappedWires (offsetBits L) := by
      rw [offset_head]
      exact mapped_tail_member _ _ _ hq
    simpa only [ey,er,ec,ed] using offsetSources_away L hn w mem
  have cleanC : ∀q∈c::cs,s.basis q=false := by simpa only [ec] using hd
  have cleanD : ∀q∈d::ds,s.basis q=false := by simpa only [ed] using hc
  have eq := BalancedCleanupOffsetZeroHead.chain_equiv (offsetBits L).tail xs ys cs ds
    a y c d L.one L.cout L.parity nd fresh (by omega) (by omega) (by omega) (by omega)
    s mOld mNew hz cleanC cleanD
  rw [offset_head,ey,er,ec,ed]
  simpa only [core,ey,er,ec,ed,List.tail_cons,List.headD_cons] using eq

private theorem sandwich_run (P Q : Program) (hz : measurementCount P=0)
    (s : State) (m : List Bool) :
    run (P++Q++P.reverse) m s=run P.reverse [] (run Q m (run P [] s)) := by
  simp only [List.append_assoc]
  rw [run_append,hz,List.take_zero,List.drop_zero,run_append,run_take]
  have zero : measurementCount P.reverse=0 := by rw [measurementCount_reverse,hz]
  have a := run_take P.reverse (m.drop (measurementCount Q)) (run Q m (run P [] s))
  rw [zero,List.take_zero] at a
  exact a.symm

private theorem bank_away (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.carry++L.offsetCarry) : q∉L.r ∧ q∉L.y ∧ q≠L.lower ∧ q≠L.cout := by
  have nd : (L.r++(L.y++(L.carry++L.offsetCarry))).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (L.allND hn)).2.1
  have r := List.nodup_append'.mp nd
  have y := List.nodup_append'.mp r.2.1
  refine ⟨fun h => List.disjoint_left.mp r.2.2 h (List.mem_append_right _ hq),
    fun h => List.disjoint_left.mp y.2.2 h hq,?_,?_⟩
  · intro e
    exact L.flagAway hn L.lower (by simp) (by simp [←e,List.mem_append.mp hq])
  · intro e
    exact L.flagAway hn L.cout (by simp) (by simp [←e,List.mem_append.mp hq])

/-- Complete wrapper equality on the original canonical contract. The actual
front supplies the clean One/banks; the Clifford reverse ignores record shifts. -/
theorem program_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hcout : s.basis L.cout=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hd : ∀q∈L.offsetCarry,s.basis q=false) :
    run (program L) m s=run (BalancedCleanupOffsetSlim.program L) m s := by
  let u := run (front L) [] s
  have prepared := front_value L hw hn R Y B hr hy s [] hR hY hS hz hcout
  have flags := L.flagsND hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have oR : L.one∉L.r := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have oY : L.one∉L.y := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have one : u.basis L.one=false := (prepared.2.2.2.2 _ oR oY (by tauto) (by tauto)).trans ho
  have cleanC : ∀q∈L.carry,u.basis q=false := by
    intro q hq
    have a := bank_away L hn q (List.mem_append_left _ hq)
    exact (prepared.2.2.2.2 q a.1 a.2.1 a.2.2.1 a.2.2.2).trans (hc q hq)
  have cleanD : ∀q∈L.offsetCarry,u.basis q=false := by
    intro q hq
    have a := bank_away L hn q (List.mem_append_right _ hq)
    exact (prepared.2.2.2.2 q a.1 a.2.1 a.2.2.1 a.2.2.2).trans (hd q hq)
  have eq := core_eq L hw hn u m m one cleanC cleanD
  rw [program,BalancedCleanupOffsetSlim.program_sandwich,
    sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2,
    sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2,←eq]

/-- Exact cleanup oracle: phase and every site except parity are restored. -/
theorem xor_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hcout : s.basis L.cout=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hd : ∀q∈L.offsetCarry,s.basis q=false) :
    run (program L) m s=⟨s.phase,writeBit s.basis L.parity
      (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|))⟩ := by
  rw [program_eq L hw hn R Y B hr hy s m hR hY hS hz ho hcout hc hd]
  exact BalancedCleanupOffsetSlim.xor_correct L hw hn R Y B hr hy s m hR hY hS hz ho hcout hc hd

theorem correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hcout : s.basis L.cout=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hd : ∀q∈L.offsetCarry,s.basis q=false)
    (hA : s.basis L.parity=decide (q < |2*R-signedY B Y|)) :
    run (program L) m s=⟨s.phase,writeBit s.basis L.parity false⟩ := by
  simpa only [hA,Bool.xor_self] using xor_correct L hw hn R Y B hr hy s m hR hY hS hz ho hcout hc hd

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=510 ∧ measurementCount (program L)=510 := by
  have t := tails L hw
  have h := BalancedCleanupOffsetZeroHead.counts (offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail (L.y.headD 0) (L.r.headD 0) L.one L.cout
    (L.carry.headD 0) L.parity (by omega) (by omega) (by omega) (by omega)
  simp only [program,core,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,(BalancedCleanupOffsetSlim.front_counts L).1,
    (BalancedCleanupOffsetSlim.front_counts L).2,h.1,h.2,t.2.2.1]
  norm_num

end ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero
end

-- source: ECDSAAdd/Arithmetic/BalancedFoldMath.lean
noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic.BalancedFold
open BalancedField BalancedCircuit

def modulusWord : Nat := 2^256

/-- The upper 256 source bits of the sparse correction, without a bank. -/
def virtualSource (u v : Bool) : Nat :=
  (List.range 256).foldr (fun i acc =>
    (if sparseF.testBit (i+1) then u else v).toNat+2*acc) 0

def selectedSource (u v : Bool) : Nat :=
  if u then (sparseF-1)/2 else if v then modulusWord-(sparseF+1)/2 else 0

/-- Finite fixed-modulus calculation by ordinary kernel reduction. -/
theorem virtualSource_value (u v : Bool) (hn : ¬(u && v)=true) :
    virtualSource u v=selectedSource u v := by
  cases u <;> cases v
  · decide
  · decide
  · decide
  · simp at hn

private theorem mapped_list_value (is : List Nat) (L : BalancedCircuit.Layout) (s : BasisState) :
    mappedValue (is.map (fun i =>
      {wire:=some (if sparseF.testBit (i+1) then L.plus else L.minus),flip:=false})++
      [{wire:=none,flip:=false}]) s=
    is.foldr (fun i acc =>
      (if sparseF.testBit (i+1) then s L.plus else s L.minus).toNat+2*acc) 0 := by
  induction is with
  | nil => simp [mappedValue,MappedBit.value]
  | cons i is ih =>
    simp only [List.map_cons,List.cons_append,mappedValue,List.foldr_cons]
    rw [ih]
    cases hb : sparseF.testBit (i+1) <;> simp [MappedBit.value,hb]

theorem foldBits_value (L : BalancedCircuit.Layout) (s : BasisState)
    (hn : ¬(s L.plus && s L.minus)=true) :
    mappedValue (foldBits L) s=selectedSource (s L.plus) (s L.minus) := by
  rw [foldBits,mapped_list_value]
  exact virtualSource_value _ _ hn

/-- Encoding on one complete positive and negative modulus interval. -/
theorem encode_shift (n : Nat) (z : Int)
    (hz : -((2^n : Nat) : Int)≤z ∧ z<((2^n : Nat) : Int)) :
    (encodeWord n z : Int)=z+(if z<0 then ((2^n : Nat) : Int) else 0) := by
  rw [encodeWord_cast]
  by_cases hn : z<0
  · rw [if_pos hn]
    have he : (z+((2^n : Nat) : Int))%((2^n : Nat) : Int)=
        z%((2^n : Nat) : Int) := by simp
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at he
    exact he.symm
  · rw [if_neg hn,Int.emod_eq_of_lt (by omega) hz.2]
    omega

def minusController (T : Int) : Bool := originalParity T && decide (T<0)
def plusController (T : Int) : Bool := originalParity T && !decide (T<0)

theorem controllers_exclusive (T : Int) :
    ¬(plusController T && minusController T)=true := by
  unfold plusController minusController
  cases originalParity T <;> cases decide (T<0) <;> decide

/-- A physical bit-256 toggle, using the proved raw-word sign. -/
def toggledWord (T : Int) : Nat :=
  if originalParity T then
    if decide (T<0) then encodeWord 257 T-modulusWord else encodeWord 257 T+modulusWord
  else encodeWord 257 T

/-- The cleared low bit is omitted, and a clean extra top bit is appended
before the exact mapped add with the original parity as carry-in. -/
def foldedSum (T : Int) : Nat :=
  toggledWord T/2+selectedSource (plusController T) (minusController T)+
    (originalParity T).toNat

private theorem raw_encoding (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    (encodeWord 257 T : Int)=T+(if T<0 then ((2^257 : Nat) : Int) else 0) := by
  apply encode_shift
  norm_num [q,ECDSAAdd.p] at ht ⊢
  omega

theorem raw_sign (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    encodeWord 257 T/modulusWord=(decide (T<0)).toNat := by
  have hr := raw_encoding T ht
  by_cases hn : T<0 <;> norm_num [hn,modulusWord,q,ECDSAAdd.p] at hr ht ⊢ <;> omega

private theorem fixed_relations :
    modulusWord=2*(2^255) ∧ (2^257 : Nat)=4*(2^255) ∧
    (sparseF+1)/2=(sparseF-1)/2+1 ∧
    (ECDSAAdd.p : Int)=2*((2^255 : Nat) : Int)-2*(((sparseF-1)/2 : Nat) : Int)-1 ∧
    (sparseF-1)/2+1≤2*(2^255) := by decide

private theorem generic_bound (Q T : Int) (H K : Nat)
    (hp : 2*Q+1=2*(H : Int)-2*(K : Int)-1) (ht : -(2*Q)≤T ∧ T≤2*Q) :
    -2*(H : Int)<T ∧ T<2*(H : Int) := by omega

private theorem generic_parity (H U : Nat) (T : Int) (a s : Bool)
    (hu : (U : Int)=T+(if s then 4*(H : Int) else 0))
    (ht : -2*(H : Int)<T ∧ T<2*(H : Int)) (hp : T%2=(a.toNat : Int)) :
    (if a then if s then U-2*H else U+2*H else U)%2=a.toNat := by
  cases a <;> cases s <;> simp at hu hp ⊢ <;> omega

theorem toggled_parity (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T%2=(originalParity T).toNat := by
  obtain ⟨hm,hw,hk,hp,hkb⟩ := fixed_relations
  have raw := raw_encoding T ht
  rw [hw] at raw
  have raw' : (encodeWord 257 T : Int)=T+
      (if decide (T<0) then 4*((2^255 : Nat) : Int) else 0) := by
    by_cases hn : T<0 <;>
      simp only [hn,decide_true,decide_false,if_true,if_false,Nat.cast_mul,Nat.cast_ofNat] at raw ⊢ <;>
      exact raw
  have bound := generic_bound q T (2^255) ((sparseF-1)/2)
    ((constants.2.1).symm.trans hp) ht
  have par : T%2=((originalParity T).toNat : Int) := by
    have h := originalParity_value T
    cases ha : originalParity T <;> simpa [ha] using h
  simpa only [toggledWord,hm] using generic_parity (2^255) (encodeWord 257 T)
    T (originalParity T) (decide (T<0)) raw' bound par

theorem cleared_low_word (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T=2*(toggledWord T/2)+(originalParity T).toNat := by
  have h := Nat.mod_add_div (toggledWord T) 2
  rw [toggled_parity T ht] at h
  omega

private theorem generic_fold (H K U E : Nat) (T R : Int) (a s : Bool)
    (hk : K+1≤2*H) (ht : -2*(H : Int)<T ∧ T<2*(H : Int))
    (hu : (U : Int)=T+(if s then 4*(H : Int) else 0))
    (he : (E : Int)=R+(if s ^^ a then 2*(H : Int) else 0))
    (hr : 2*R=T+(if a then if s then 2*(H : Int)-2*(K : Int)-1
      else -(2*(H : Int)-2*(K : Int)-1) else 0)) :
    (if a then if s then U-2*H else U+2*H else U)/2+
      (if a && !s then K else if a && s then 2*H-K-1 else 0)+a.toNat=
      E+2*H*(a && s).toNat := by
  cases a <;> cases s <;> simp at hu he hr ⊢ <;> omega

/-- Generic arithmetic is proved before fixed constants are instantiated,
so no enormous numerical omega certificate enters the kernel. -/
theorem foldedSum_value (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    foldedSum T=encodeWord 256 (halfResult T)+modulusWord*(minusController T).toNat := by
  obtain ⟨hm,hw,hk,hp,hkb⟩ := fixed_relations
  have raw := raw_encoding T ht
  rw [hw] at raw
  have raw' : (encodeWord 257 T : Int)=T+
      (if decide (T<0) then 4*((2^255 : Nat) : Int) else 0) := by
    by_cases hn : T<0 <;>
      simp only [hn,decide_true,decide_false,if_true,if_false,Nat.cast_mul,Nat.cast_ofNat] at raw ⊢ <;>
      exact raw
  have hs := halfResult_spec T ht
  have result := encode_shift 256 (halfResult T) (by
    have h := hs.1
    norm_num [Centered,q,ECDSAAdd.p] at h ⊢
    omega)
  have hi : (if halfResult T<0 then ((2^256 : Nat) : Int) else 0)=
      (if decide (T<0) ^^ originalParity T then ((2^256 : Nat) : Int) else 0) := by
    rw [←halfResult_sign T ht]
    by_cases hn : halfResult T<0 <;> simp [hn]
  rw [hi,show (2^256 : Nat)=2*(2^255) from hm] at result
  simp only [Nat.cast_mul,Nat.cast_ofNat] at result
  have half : 2*halfResult T=T+(if originalParity T then
      if decide (T<0) then (ECDSAAdd.p : Int) else -(ECDSAAdd.p : Int) else 0) := by
    have h := hs.2
    by_cases ho : T%2=0 <;> by_cases hn : T<0
    all_goals simp [evenLift,originalParity,ho,hn,show (0≤T)↔¬T<0 by omega,
      sub_eq_add_neg] at h ⊢; exact h
  rw [hp] at half
  have bound := generic_bound q T (2^255) ((sparseF-1)/2)
    ((constants.2.1).symm.trans hp) ht
  have g := generic_fold (2^255) ((sparseF-1)/2) (encodeWord 257 T)
    (encodeWord 256 (halfResult T)) T (halfResult T) (originalParity T) (decide (T<0))
    hkb bound raw' result half
  simpa only [foldedSum,toggledWord,selectedSource,plusController,minusController,
    hm,hk,Nat.sub_sub] using g

theorem foldedSum_low (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    foldedSum T%modulusWord=encodeWord 256 (halfResult T) := by
  have hb := encodeWord_bound 256 (halfResult T)
  norm_num at hb
  rw [foldedSum_value T ht]
  simp [Nat.add_mod,Nat.mul_mod,modulusWord,Nat.mod_eq_of_lt hb]

theorem foldedSum_bound (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    foldedSum T<2^257 := by
  have hv := foldedSum_value T ht
  have hb := encodeWord_bound 256 (halfResult T)
  cases hc : minusController T <;> norm_num [hc,modulusWord] at hv hb ⊢ <;> omega

end ECDSAAdd.Arithmetic.BalancedFold
end

-- source: ECDSAAdd/Arithmetic/MappedSources.lean
noncomputable section

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- An optional external control; an absent control enables the literal. -/
def mappedEnabled (c : Option Wire) (s : BasisState) : Bool := (c.map s).getD true

def mappedConstantBit (c : Option Wire) (b : Bool) : MappedBit :=
  if b then {wire:=c,flip:=c.isNone} else {wire:=none,flip:=false}

def mappedConstant : Option Wire → Nat → Nat → List MappedBit
  | _,0,_ => []
  | c,n+1,k => mappedConstantBit c (decide (k%2=1))::mappedConstant c n (k/2)

def mappedRead (xs : List Wire) (flip : Bool := false) : List MappedBit :=
  xs.map (fun q => {wire:=some q,flip:=flip})

theorem mappedConstantBit_value (c : Option Wire) (b : Bool) (s : BasisState) :
    (mappedConstantBit c b).value s=if b then mappedEnabled c s else false := by
  cases c <;> cases b <;> simp [mappedConstantBit,MappedBit.value,mappedEnabled]

theorem mappedConstant_length (c : Option Wire) (n k : Nat) :
    (mappedConstant c n k).length=n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [mappedConstant,ih]

theorem mappedConstant_value (c : Option Wire) (n k : Nat) (s : BasisState)
    (hk : k<2^n) :
    mappedValue (mappedConstant c n k) s=if mappedEnabled c s then k else 0 := by
  induction n generalizing k with
  | zero =>
    have h : k=0 := by simpa using hk
    simp [mappedConstant,mappedValue,h]
  | succ n ih =>
    have hd : k/2<2^n := by rw [Nat.pow_succ] at hk; omega
    rw [mappedConstant,mappedValue,mappedConstantBit_value,ih _ hd]
    have split := Nat.mod_add_div k 2
    have small := Nat.mod_lt k (by decide : 0<2)
    cases he : mappedEnabled c s <;> by_cases odd : k%2=1 <;>
      simp [he,odd] <;> omega

theorem mappedConstant_wires (c : Option Wire) (n k : Nat) :
    ∀q∈mappedWires (mappedConstant c n k),q∈c := by
  induction n generalizing k with
  | zero => simp [mappedConstant,mappedWires]
  | succ n ih =>
    intro q hq
    simp only [mappedConstant,mappedWires,List.flatMap_cons,List.mem_append] at hq
    rcases hq with head|tail
    · by_cases odd : k%2=1
      · simpa [mappedConstantBit,odd] using head
      · simp [mappedConstantBit,odd] at head
    · exact ih _ q tail

theorem mappedRead_value (xs : List Wire) (s : BasisState) :
    mappedValue (mappedRead xs false) s=regValue xs s := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    simp [mappedRead,mappedValue,MappedBit.value,regValue,ih,Bool.toNat,Bool.cond_eq_ite]
    simpa [mappedRead,regValue] using ih

theorem mappedRead_complement (xs : List Wire) (s : BasisState) :
    mappedValue (mappedRead xs true) s=2^xs.length-1-regValue xs s := by
  have eq : mappedValue (mappedRead xs true) s=regValue xs (fun q => !s q) := by
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp [mappedRead,mappedValue,MappedBit.value,regValue,ih,Bool.toNat,Bool.cond_eq_ite]
      simpa [mappedRead,regValue] using ih
  rw [eq,regValue_complement]

theorem mappedRead_wires (xs : List Wire) (flip : Bool) :
    mappedWires (mappedRead xs flip)=xs := by
  induction xs with
  | nil => rfl
  | cons q qs ih => simpa [mappedRead,mappedWires] using congrArg (List.cons q) ih

theorem mappedValue_append (xs ys : List MappedBit) (s : BasisState) :
    mappedValue (xs++ys) s=mappedValue xs s+2^xs.length*mappedValue ys s := by
  induction xs with
  | nil => simp [mappedValue]
  | cons x xs ih => simp [mappedValue,ih,Nat.pow_succ]; ring

/-- Repeated wires are immutable reads, so this diagonal source needs no
128/129-bit mask register in addition to the controlled square input. -/
def mappedDiagonal (xs : List Wire) : List MappedBit :=
  mappedRead xs false++mappedRead (xs.take (xs.length-1)) true++[{wire:=none,flip:=false}]

theorem mappedDiagonal_length (xs : List Wire) (hn : 0<xs.length) :
    (mappedDiagonal xs).length=2*xs.length := by
  simp [mappedDiagonal,mappedRead]
  omega

theorem mappedRead_length (xs : List Wire) (flip : Bool) :
    (mappedRead xs flip).length=xs.length := by simp [mappedRead]

theorem mappedDiagonal_value (xs : List Wire) (s : BasisState) :
    mappedValue (mappedDiagonal xs) s=regValue xs s+
      2^xs.length*(2^(xs.length-1)-1-regValue (xs.take (xs.length-1)) s) := by
  simp only [mappedDiagonal,mappedValue_append,mappedRead_value,mappedRead_complement,
    mappedRead_length,mappedValue,MappedBit.value,Option.map_none,Option.getD_none,
    Bool.xor_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
  rw [List.length_take,Nat.min_eq_left (by omega)]

def mappedConstAdd (c : Option Wire) (ys carry : List Wire) (cin : Wire) (k : Nat) : Program :=
  mappedAdd (mappedConstant c ys.length k) ys carry cin

theorem mappedConstAdd_counts (c : Option Wire) (ys carry : List Wire) (cin : Wire) (k : Nat)
    (hc : carry.length+1=ys.length) :
    toffoliCount (mappedConstAdd c ys carry cin k)=ys.length-1 ∧
    measurementCount (mappedConstAdd c ys carry cin k)=ys.length-1 :=
  mappedAdd_counts _ _ _ _ (mappedConstant_length _ _ _) hc

theorem mappedConstAdd_correct (c : Option Wire) (ys carry : List Wire) (cin : Wire) (k : Nat)
    (hn : (cin::(ys++carry)).Nodup) (ha : ∀q∈c,q∉cin::(ys++carry))
    (hc : carry.length+1=ys.length) (hk : k<2^ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (mappedConstAdd c ys carry cin k) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (mappedConstAdd c ys carry cin k) m s).basis q=s.basis q) ∧
    regValue ys (run (mappedConstAdd c ys carry cin k) m s).basis=
      ((if mappedEnabled c s.basis then k else 0)+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length := by
  obtain ⟨hp,he,hv⟩ := mappedAdd_correct (mappedConstant c ys.length k) ys carry cin hn
    (fun q hq => ha q (mappedConstant_wires _ _ _ q hq)) (mappedConstant_length _ _ _) hc s m hclean
  exact ⟨hp,he,by simpa [mappedConstant_value _ _ _ _ hk] using hv⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedSubtract.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem mappedValue_lt (bits : List MappedBit) (s : BasisState) :
    mappedValue bits s<2^bits.length := by
  induction bits with
  | nil => simp [mappedValue]
  | cons b bits ih =>
    have hb : (b.value s).toNat≤1 := by cases b.value s <;> decide
    simp only [mappedValue,List.length_cons,Nat.pow_succ]
    omega

/-- The source stays implicit, including complemented and repeated reads. -/
def mappedSub (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++mappedAdd bits ys carry cin++notRegister ys

private theorem mapped_complement_sub (X Y N : Nat) (hN : 0<N) (hX : X<N) (hY : Y<N) :
    N-1-((X+(N-1-Y))%N)=(Y+N-X)%N := by
  by_cases less : X≤Y
  · rw [Nat.mod_eq_of_lt (show X+(N-1-Y)<N by omega),
      show Y+N-X=(Y-X)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X+(N-1-Y)=(X-1-Y)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X-1-Y<N by omega),Nat.mod_eq_of_lt (show Y+N-X<N by omega)]
    omega

theorem mappedSub_correct (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hi : s.basis cin=false) :
    (run (mappedSub bits ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (mappedSub bits ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (mappedSub bits ys carry cin) m s).basis=
      (regValue ys s.basis+2^ys.length-mappedValue bits s.basis)%2^ys.length := by
  have nd := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1
  have away (q : Wire) (hq : q∈cin::carry) : q∉ys := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  let s1 : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have first (record : List Bool) : run (notRegister ys) record s=s1 :=
    notRegister_correct ys nd s record
  have keep (q : Wire) (hq : q∉ys) : s1.basis q=s.basis q := by simp [s1,hq]
  have clean : ∀q∈carry,s1.basis q=false := by
    intro q hq
    exact (keep q (away q (by simp [hq]))).trans (hclean q hq)
  have ci : s1.basis cin=false := (keep cin (away cin (by simp))).trans hi
  have src : mappedValue bits s1.basis=mappedValue bits s.basis := by
    apply mappedValue_congr
    intro q hq
    exact keep q (fun bad => hs q hq (by simp [bad]))
  have inverted : regValue ys s1.basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys s1.basis (fun q => !s.basis q) (by intro q hq; simp [s1,hq]),regValue_complement]
  obtain ⟨phase,same,value⟩ := mappedAdd_correct bits ys carry cin hn hs hl hc s1 m clean
  let t := run (mappedAdd bits ys carry cin) m s1
  have flipValue : regValue ys (fun q => if q∈ys then !t.basis q else t.basis q)=
      2^ys.length-1-regValue ys t.basis := by
    rw [regValue_congr ys _ (fun q => !t.basis q) (by intro q hq; simp [hq]),regValue_complement]
  have zeroM := (notRegister_counts ys).2
  simp only [mappedSub,List.append_assoc,run_append,run_take,zeroM,List.take_zero,List.drop_zero]
  rw [first]
  change (run (notRegister ys) _ t).phase=s.phase ∧ _
  rw [notRegister_correct ys nd]
  refine ⟨phase,?_,?_⟩
  · intro q hq
    simp only [hq,if_false]
    exact (same q hq).trans (keep q hq)
  · rw [flipValue,value,src,inverted,ci,Bool.toNat_false,Nat.add_zero]
    apply mapped_complement_sub _ _ _ (Nat.two_pow_pos _)
    · simpa [hl] using mappedValue_lt bits s.basis
    · exact regValue_lt ys s.basis

theorem mappedSub_counts (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (mappedSub bits ys carry cin)=ys.length-1 ∧
    measurementCount (mappedSub bits ys carry cin)=ys.length-1 := by
  have h := mappedAdd_counts bits ys carry cin hl hc
  simp [mappedSub,h.1,h.2,(notRegister_counts ys).1,(notRegister_counts ys).2]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldConvertProgram.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic.BalancedConvert
open BalancedField BalancedCircuit

/-- A single field word and a shared carry ladder. No constant word bank. -/
structure Layout where
  low : List Wire
  msb : Wire
  carry : List Wire
  cin : Wire
  one : Wire
  flag : Wire

def Layout.word (L : Layout) := L.low++[L.msb]
def Layout.wires (L : Layout) := [L.cin,L.one,L.flag,L.msb]++L.low++L.carry
def Layout.Widths (L : Layout) := L.low.length=255 ∧ L.carry.length=255

def bias : Nat := (sparseF-1)/2
def inverseBias : Nat := 2^256-bias

def correction (L : Layout) : List MappedBit :=
  (List.range 256).map fun i =>
    {wire:=if sparseF.testBit i then some L.flag else none,flip:=false}

/-- The exact threshold predicate is copied from a biased word's top bit.
Both adders run forward, with independent measurement cleanup. -/
def predicate (L : Layout) : Program :=
  literalConstAdd L.word L.carry L.cin L.one bias++[.CX L.msb L.flag]++
    literalConstAdd L.word L.carry L.cin L.one inverseBias

/-- Convert canonical x to two's-complement centerFp(x). Functional
composition is a separate proof obligation; these are actual instructions. -/
def center (L : Layout) : Program :=
  predicate L++mappedAdd (correction L) L.word L.carry L.cin++[.CX L.msb L.flag]

/-- Independently emitted inverse: subtract the selected sparse correction
and XOR the exact canonical threshold predicate back into the flag. -/
def canonical (L : Layout) : Program :=
  [.CX L.msb L.flag]++mappedSub (correction L) L.word L.carry L.cin++predicate L

theorem predicate_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (predicate L)=510 ∧ measurementCount (predicate L)=510 := by
  have w : L.word.length=256 := by simp [Layout.word,hw.1]
  have cy : L.carry.length=255 := hw.2
  have a := literalConstAdd_counts L.word L.carry L.cin L.one bias (by omega)
  have b := literalConstAdd_counts L.word L.carry L.cin L.one inverseBias (by omega)
  simp [predicate,a.1,a.2,b.1,b.2,w,toffoliCount,measurementCount]

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (center L)=765 ∧ measurementCount (center L)=765 ∧
    toffoliCount (canonical L)=765 ∧ measurementCount (canonical L)=765 := by
  have w : L.word.length=256 := by simp [Layout.word,hw.1]
  have cy : L.carry.length=255 := hw.2
  have len : (correction L).length=L.word.length := by simp [correction,w]
  have hc : L.carry.length+1=L.word.length := by omega
  have a := mappedAdd_counts (correction L) L.word L.carry L.cin len hc
  have b := mappedSub_counts (correction L) L.word L.carry L.cin len hc
  have p := predicate_counts L hw
  simp [center,canonical,a.1,a.2,b.1,b.2,p.1,p.2,w,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.BalancedConvert
end

-- source: ECDSAAdd/Arithmetic/ConstantBorrow.lean
noncomputable section

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def constantBorrow (bit : Bool) (x cin target : Wire) : Program :=
  [.X x]++mappedMajority {wire:=none,flip:=bit} x cin target++[.X x]

def constantBorrowErase (bit : Bool) (x cin target : Wire) : Program :=
  [.X x]++mappedEraseCarry {wire:=none,flip:=bit} x cin target++[.X x]

theorem carryBit_swap (A B C : Bool) : carryBit A B C=carryBit B A C := by
  cases A <;> cases B <;> cases C <;> rfl

theorem constantBorrow_correct (bit : Bool) (x cin target : Wire)
    (hn : [x,cin,target].Nodup) (s : State) (m : List Bool) :
    run (constantBorrow bit x cin target) m s=
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ carryBit (!s.basis x) bit (s.basis cin))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxc,hxt⟩,hct⟩ := hn
  have hcx := Ne.symm hxc
  cases bit <;>
    simp only [constantBorrow,mappedMajority,Bool.false_eq_true,if_false,if_true,
      List.cons_append,List.nil_append,run]
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqx : q=x <;> by_cases hqc : q=cin <;> by_cases hqt : q=target <;>
      simp_all [writeBit,Function.update,carryBit] <;>
      cases s.basis x <;> cases s.basis cin <;> cases s.basis target <;> simp_all

theorem constantBorrowErase_correct (bit : Bool) (x cin target : Wire)
    (hn : [x,cin,target].Nodup) (s : State) (m : List Bool)
    (hk : s.basis target=carryBit (!s.basis x) bit (s.basis cin)) :
    run (constantBorrowErase bit x cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  have nd := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxc,hxt⟩,hct⟩ := hn
  let t : State := ⟨s.phase,writeBit s.basis x (!s.basis x)⟩
  have known : t.basis target=carryBit
      (({wire:=none,flip:=bit} : MappedBit).value t.basis) (t.basis x) (t.basis cin) := by
    have h := hk.trans (carryBit_swap (!s.basis x) bit (s.basis cin))
    simpa [t,writeBit,Ne.symm hxt,Ne.symm hxc,MappedBit.value] using h
  have clear := mappedEraseCarry_correct {wire:=none,flip:=bit} x cin target nd (by simp) t m known
  simp only [constantBorrowErase,List.cons_append,List.nil_append,run]
  change run (mappedEraseCarry {wire:=none,flip:=bit} x cin target++[.X x]) m t=_
  rw [run_append,run_take,clear]
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hqt : q=target <;> by_cases hqx : q=x <;>
    simp_all [t,writeBit,Function.update]

theorem constantBorrow_counts (bit : Bool) (x cin target : Wire) :
    toffoliCount (constantBorrow bit x cin target)=1 ∧
    measurementCount (constantBorrow bit x cin target)=0 ∧
    toffoliCount (constantBorrowErase bit x cin target)=0 ∧
    measurementCount (constantBorrowErase bit x cin target)=1 := by
  have h := mappedBit_counts {wire:=none,flip:=bit} x cin target
  simp only [constantBorrow,constantBorrowErase,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,h.1,h.2.1,h.2.2.1,h.2.2.2.1]
  simp

/-- Exact comparison with a literal source. Scratch contains n-1 borrow bits;
no constant register, truncated window or sampled envelope is required. -/
def compareConstantLt : List Wire → List Wire → Wire → Wire → Nat → Program
  | x::x'::xs,c::cs,cin,target,k =>
      constantBorrow (decide (k%2=1)) x cin c++
        compareConstantLt (x'::xs) cs c target (k/2)++
        constantBorrowErase (decide (k%2=1)) x cin c
  | [x],_,cin,target,k => constantBorrow (decide (k%2=1)) x cin target
  | _,_,_,_,_ => []

def compareConstantGe (xs carry : List Wire) (cin target : Wire) (k : Nat) : Program :=
  compareConstantLt xs carry cin target k++[.X target]

theorem compareConstantLt_counts (xs carry : List Wire) (cin target : Wire) (k : Nat)
    (hc : carry.length+1=xs.length) :
    toffoliCount (compareConstantLt xs carry cin target k)=xs.length ∧
    measurementCount (compareConstantLt xs carry cin target k)=xs.length-1 := by
  induction xs generalizing carry cin k with
  | nil => simp at hc
  | cons x xs ih =>
    cases xs with
    | nil =>
      have h := constantBorrow_counts (decide (k%2=1)) x cin target
      simpa [compareConstantLt] using And.intro h.1 h.2.1
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have h := ih cs c (k/2) (by simpa using hc)
        have b := constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareConstantLt]
        constructor
        · simp only [toffoliCount_append,b.1,b.2.2.1]
          rw [h.1]
          simp [Nat.add_comm]
        · simp only [measurementCount_append,b.2.1,b.2.2.2]
          rw [h.2]
          simp

theorem compareConstantGe_counts (xs carry : List Wire) (cin target : Wire) (k : Nat)
    (hc : carry.length+1=xs.length) :
    toffoliCount (compareConstantGe xs carry cin target k)=xs.length ∧
    measurementCount (compareConstantGe xs carry cin target k)=xs.length-1 := by
  have h := compareConstantLt_counts xs carry cin target k hc
  simp [compareConstantGe,h.1,h.2,toffoliCount,measurementCount]

/-- A literal comparison toggles only its target and returns all borrow
scratch to zero, for every input word and every measurement record. -/
theorem compareConstantLt_correct (xs carry : List Wire) (cin target : Wire) (k : Nat)
    (hn : (target::cin::(xs++carry)).Nodup)
    (hc : carry.length+1=xs.length) (hk : k<2^xs.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (compareConstantLt xs carry cin target k) m s).phase=s.phase ∧
    (∀q,q≠target → (run (compareConstantLt xs carry cin target k) m s).basis q=s.basis q) ∧
    (run (compareConstantLt xs carry cin target k) m s).basis target=
      (s.basis target ^^ decide (regValue xs s.basis<k+(s.basis cin).toNat)) := by
  induction xs generalizing carry cin k s m with
  | nil => simp at hc
  | cons x xs ih =>
    have cnt := List.nodup_iff_count.mp hn
    have htx : target≠x := by
      intro bad; have h := cnt target; subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have htci : target≠cin := by
      intro bad; have h := cnt target; subst cin
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have hxc : x≠cin := by
      intro bad; have h := cnt cin; subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    cases xs with
    | nil =>
      have nd : [x,cin,target].Nodup := by
        apply List.nodup_iff_count.mpr; intro q; have h := cnt q
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        omega
      rw [compareConstantLt,constantBorrow_correct _ _ _ _ nd]
      refine ⟨rfl,?_,?_⟩
      · intro q hq; simp [writeBit,hq]
      · have small : k<2 := by simpa using hk
        by_cases zero : k=0
        · subst k
          cases hx : s.basis x <;> cases hi : s.basis cin <;>
            simp [writeBit,regValue,carryBit,hx,hi]
        · have one : k=1 := by omega
          subst k
          cases hx : s.basis x <;> cases hi : s.basis cin <;>
            simp [writeBit,regValue,carryBit,hx,hi]
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have htc : target≠c := by
          intro bad; have h := cnt target; subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hxc' : x≠c := by
          intro bad; have h := cnt c; subst x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hcic : cin≠c := by
          intro bad; have h := cnt c; subst cin
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hctail : c∉x'::xs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
          omega
        have hccs : c∉cs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have nd : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have nd' : (target::c::((x'::xs)++cs)).Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        let bit := decide (k%2=1)
        let K := carryBit (!s.basis x) bit (s.basis cin)
        let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
        have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by simp [s1,writeBit,hq]
        have zero := hclean c (by simp)
        have first (record : List Bool) : run (constantBorrow bit x cin c) record s=s1 := by
          rw [constantBorrow_correct _ _ _ _ nd]
          simp [s1,K,zero]
        have clean' : ∀q∈cs,s1.basis q=false := by
          intro q hq
          rw [keep q (fun bad => hccs (bad ▸ hq))]
          exact hclean q (by simp [hq])
        have high : k/2<2^(x'::xs).length := by
          simp only [List.length_cons,Nat.pow_succ] at hk ⊢
          omega
        obtain ⟨hp,he,hv⟩ := ih cs c (k/2) nd' (by simpa using hc) high s1 m clean'
        let t := run (compareConstantLt (x'::xs) cs c target (k/2)) m s1
        have tx : t.basis x=s.basis x := (he x htx.symm).trans (keep x hxc')
        have ti : t.basis cin=s.basis cin := (he cin htci.symm).trans (keep cin hcic)
        have tk : t.basis c=K := by rw [he c htc.symm]; simp [s1,writeBit]
        have clear (record : List Bool) : run (constantBorrowErase bit x cin c) record t=
            ⟨t.phase,writeBit t.basis c false⟩ := by
          apply constantBorrowErase_correct _ _ _ _ nd t record
          rw [tx,ti,tk]
        have counts := constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareConstantLt]
        simp only [List.append_assoc,run_append,run_take,counts.2.1,List.take_zero,List.drop_zero]
        rw [first]
        change (run (constantBorrowErase bit x cin c) _ t).phase=_ ∧ _
        rw [clear]
        refine ⟨hp,?_,?_⟩
        · intro q hq
          by_cases hqc : q=c
          · subst q; simp [writeBit,zero]
          · simp only [writeBit,Function.update_of_ne hqc]
            exact (he q hq).trans (keep q hqc)
        · simp only [writeBit,Function.update_of_ne htc]
          rw [hv,keep target htc]
          have v : regValue (x'::xs) s1.basis=regValue (x'::xs) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q (fun bad => hctail (bad ▸ hq)))
          have carryVal : s1.basis c=K := by simp [s1,writeBit]
          rw [v,carryVal]
          have split : bit.toNat+2*(k/2)=k := by
            have e := Nat.mod_add_div k 2
            have b := Nat.mod_lt k (by decide : 0<2)
            by_cases odd : k%2=1 <;> simp [bit,odd] <;> omega
          have thr := borrow_threshold (s.basis x) bit (s.basis cin)
            (regValue (x'::xs) s.basis) (k/2)
          rw [split] at thr
          have pred : decide (regValue (x::x'::xs) s.basis<k+(s.basis cin).toNat)=
              decide (regValue (x'::xs) s.basis<k/2+K.toNat) := by
            apply decide_eq_decide.mpr
            simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,K] using thr
          rw [pred]

theorem compareConstantGe_correct (xs carry : List Wire) (cin target : Wire) (k : Nat)
    (hn : (target::cin::(xs++carry)).Nodup)
    (hc : carry.length+1=xs.length) (hk : k<2^xs.length)
    (s : State) (m : List Bool) (hcin : s.basis cin=false)
    (hclean : ∀q∈carry,s.basis q=false) :
    (run (compareConstantGe xs carry cin target k) m s).phase=s.phase ∧
    (∀q,q≠target → (run (compareConstantGe xs carry cin target k) m s).basis q=s.basis q) ∧
    (run (compareConstantGe xs carry cin target k) m s).basis target=
      (s.basis target ^^ decide (k≤regValue xs s.basis)) := by
  obtain ⟨hp,he,hv⟩ := compareConstantLt_correct xs carry cin target k hn hc hk s m hclean
  simp only [compareConstantGe,run_append,run_take,run]
  refine ⟨hp,?_,?_⟩
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]
    exact he q hq
  · simp only [writeBit,Function.update_self,hv,hcin,Bool.toNat_false,Nat.add_zero]
    by_cases less : regValue xs s.basis<k
    · have no : ¬k≤regValue xs s.basis := by omega
      simp [less,no]
    · have yes : k≤regValue xs s.basis := by omega
      simp [less,yes]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontRotate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 同一物理寄存器连续右旋 k 位；不改变寄存器视图。 -/
def rotateRightBits (r : List Wire) : Nat → Program
  | 0 => []
  | k+1 => rotateRight r ++ rotateRightBits r k

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Framework/RecordedSyntax.lean
noncomputable section

namespace ECDSAAdd

/-- Deferred corrections refer to a previously consumed measurement ordinal.
They read the classical tape and act only on their declared quantum wires. -/
inductive RecordedInstr where
  | gate (instruction : Instr)
  | phaseFromRecord (measurementOrdinal : Nat) (corrections : List Correction)
  deriving DecidableEq, Repr

abbrev RecordedProgram := List RecordedInstr

def embedRecorded (p : Program) : RecordedProgram := p.map RecordedInstr.gate

def recordedMeasurementCount : RecordedProgram → Nat
  | [] => 0
  | .gate i :: p => measurementCount [i] + recordedMeasurementCount p
  | .phaseFromRecord _ _ :: p => recordedMeasurementCount p

def RecordedInstr.quantumWires : RecordedInstr → Finset Wire
  | .gate i => i.wires
  | .phaseFromRecord _ cs => correctionWires cs

def recordedWires : RecordedProgram → Finset Wire
  | [] => ∅
  | i :: p => i.quantumWires ∪ recordedWires p

/-- The tape is fixed across composition; cursor counts consumed measurements. -/
structure RecordedContext where
  tape : List Bool
  cursor : Nat

/-- A deferred correction may refer only to an earlier measurement, even when
an arbitrary finite tape is shorter than the consumed prefix (then it reads 0). -/
def RecordedWellFormedAt : Nat → RecordedProgram → Prop
  | _, [] => True
  | k, .gate i :: p => RecordedWellFormedAt (k + measurementCount [i]) p
  | k, .phaseFromRecord j _ :: p => j < k ∧ RecordedWellFormedAt k p

end ECDSAAdd
end

-- source: ECDSAAdd/Framework/RecordedSemantics.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd

/-- Absolute ordinals always index the same tape. A deferred correction
consumes no outcome and never replaces the old measurement by an inverse one. -/
def runWithTape : RecordedProgram → List Bool → Nat → State → State
  | [], _, _, s => s
  | .gate i :: p, m, k, s =>
      runWithTape p m (k+measurementCount [i]) (run [i] (m.drop k) s)
  | .phaseFromRecord j cs :: p, m, k, s =>
      runWithTape p m k (if m.getD j false then correct cs s else s)

def runRecorded (p : RecordedProgram) (ctx : RecordedContext) (s : State) : State × RecordedContext :=
  (runWithTape p ctx.tape ctx.cursor s,
    ⟨ctx.tape,ctx.cursor+recordedMeasurementCount p⟩)

@[simp] theorem runRecorded_tape (p : RecordedProgram) (ctx : RecordedContext) (s : State) :
    (runRecorded p ctx s).2.tape=ctx.tape := rfl

@[simp] theorem runRecorded_cursor (p : RecordedProgram) (ctx : RecordedContext) (s : State) :
    (runRecorded p ctx s).2.cursor=ctx.cursor+recordedMeasurementCount p := rfl

@[simp] theorem runWithTape_phaseFromRecord (j : Nat) (cs : List Correction)
    (m : List Bool) (k : Nat) (s : State) :
    runWithTape [.phaseFromRecord j cs] m k s=
      if m.getD j false then correct cs s else s := rfl

end ECDSAAdd
end

-- source: ECDSAAdd/Framework/RecordedRelocation.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd

/-- Relocate classical ordinals when placing a closed recorded segment after
earlier measurements. Quantum wire identities are deliberately unchanged. -/
def relocateRecord (offset : Nat) : RecordedInstr → RecordedInstr
  | .gate i => .gate i
  | .phaseFromRecord j cs => .phaseFromRecord (offset+j) cs

def relocateRecords (offset : Nat) (p : RecordedProgram) : RecordedProgram :=
  p.map (relocateRecord offset)

/-- Closed concatenation owns all its record references. Its second segment
is moved by exactly the first segment's consumed measurement count. -/
def recordedThen (p q : RecordedProgram) : RecordedProgram :=
  p++relocateRecords (recordedMeasurementCount p) q

end ECDSAAdd
end

-- source: ECDSAAdd/Framework/FailureBudget.lean
noncomputable section

namespace ECDSAAdd.FailureBudget

/-- A named finite input law. No uniformity or independence is implicit. -/
structure InputLaw (X : Type*) [Fintype X] where
  weight : X → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

variable {X : Type*} [Fintype X]

/-- Probability of an explicitly supplied input event, not of a measurement tape. -/
def InputLaw.mass (μ : InputLaw X) (event : Finset X) : ℝ :=
  ∑ x ∈ event, μ.weight x

variable [DecidableEq X]

/-- A budget is non-vacuous only together with a specified law and an explicit
bound below one; a downstream application must choose its numerical target. -/
structure CertifiedEvent (μ : InputLaw X) where
  event : Finset X
  epsilon : ℝ
  nonneg : 0 ≤ epsilon
  lt_one : epsilon < 1
  bound : μ.mass event ≤ epsilon

end ECDSAAdd.FailureBudget
end

-- source: ECDSAAdd/Framework/CoherentFailure.lean
noncomputable section

namespace ECDSAAdd.FailureBudget

variable {X : Type*} [Fintype X] [DecidableEq X]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

end ECDSAAdd.FailureBudget
end

-- source: ECDSAAdd/Framework/FiniteUnitary.lean
noncomputable section

/-! Finite, exact quantum semantics for proper X/CX/CCX programs.

Every wire must lie below n. The basis permutation is derived from run, with
its inverse proved using the reversed gate stream. Its linear extension is
a complex linear isometric equivalence, not an arbitrary realization witness.
No measurements, corrections, tape probabilities, or record environments
are interpreted here. Those require a separate semantics.
-/

namespace ECDSAAdd.FiniteUnitary

abbrev Bits (n : Nat) := Fin n → Bool

theorem run_phase (p : Program) (hp : ProperProgram p) (s : State) (m : List Bool) :
    (run p m s).phase = s.phase := by
  induction p generalizing s with
  | nil => rfl
  | cons i p ih =>
    have hi := hp i (by simp)
    have ht : ProperProgram p := fun j hj => hp j (by simp [hj])
    cases i <;> simp_all [ProperGate, run]

end ECDSAAdd.FiniteUnitary
end

-- source: ECDSAAdd/Framework/RecordedMeasurement.lean
noncomputable section

/-! Coherent X-basis measurement with a retained record.

The measured bit is exchanged for its outcome coordinate by a Hadamard map.
The data target is represented by the Cleared subtype, so its zero reset is
explicit. Conditional corrections are diagonal signs obtained from correct.
The output is a purification: reading the record gives the outcome law.
This file does not yet induct over arbitrary RecordedProgram streams.
-/

namespace ECDSAAdd.RecordedMeasurement

variable {X : Type*} [Fintype X]

open FiniteUnitary

def Cleared (n : Nat) (t : Fin n) := {x : Bits n // x t = false}

instance (n : Nat) (t : Fin n) : Fintype (Cleared n t) := inferInstanceAs (Fintype {x : Bits n // x t = false})
instance (n : Nat) (t : Fin n) : DecidableEq (Cleared n t) := inferInstanceAs (DecidableEq {x : Bits n // x t = false})

end ECDSAAdd.RecordedMeasurement
end

-- source: ECDSAAdd/Framework/RecordedQuantum.lean
noncomputable section

/-! Finite coherent semantics with persistent measurement records.
The typed Circuit carries input/output record counts. Its program erasure is
well formed and bounded to n data wires. Every constructor has a concrete
isometry; kernel computes interpreter-derived primitive amplitudes and sums
intermediate configurations for sequencing. Every bounded well-formed stream of physical instructions has such a typing.
A closed full-tape runWithTape formula and a RecordedAgreement-to-budget
corollary are separate obligations.
-/

namespace ECDSAAdd.RecordedQuantum

open FiniteUnitary RecordedMeasurement

/-- Circuit typing records the number of outcomes available at each boundary. -/
inductive Circuit (n : Nat) : Nat → Nat → Type where
  | gates {k : Nat} (p : Program) (hp : ProperProgram p)
      (hw : wires p ⊆ Finset.range n) : Circuit n k k
  | measure {k : Nat} (t : Fin n) (c0 c1 : List Correction)
      (hw0 : correctionWires c0 ⊆ Finset.range n)
      (hw1 : correctionWires c1 ⊆ Finset.range n) : Circuit n k (k+1)
  | saved {k : Nat} (j : Fin k) (cs : List Correction)
      (hw : correctionWires cs ⊆ Finset.range n) : Circuit n k k
  | seq {k l m : Nat} (a : Circuit n k l) (b : Circuit n l m) : Circuit n k m

namespace Circuit

end Circuit
/-- Ordinary gates have no target/control alias. Measurements are admitted. -/
def PhysicalInstr : RecordedInstr → Prop
  | .gate (.measureX _ _ _) => True
  | .gate i => ProperGate i
  | .phaseFromRecord _ _ => True

end ECDSAAdd.RecordedQuantum
end

-- source: ECDSAAdd/Framework/RecordedPhysical.lean
noncomputable section

namespace ECDSAAdd.RecordedQuantum

/-- Local physical validity: every ordinary target differs from its controls.
Measurements and saved-record phase instructions are admitted. -/
def PhysicalProgram (p : RecordedProgram) : Prop := ∀ i ∈ p, PhysicalInstr i

theorem physical_embed (p : Program) :
    PhysicalProgram (embedRecorded p) ↔ ∀ i ∈ p, PhysicalInstr (.gate i) := by
  simp [PhysicalProgram,embedRecorded]

theorem physical_of_proper (p : Program) (hp : ProperProgram p) :
    PhysicalProgram (embedRecorded p) := by
  rw [physical_embed]
  intro i hi
  have h := hp i hi
  cases i <;> simp_all [PhysicalInstr,ProperGate]

end ECDSAAdd.RecordedQuantum
end

-- source: ECDSAAdd/Arithmetic/MeasuredArithmeticPhysical.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

def GatePhysical (p : Program) : Prop := ∀ i ∈ p, PhysicalInstr (.gate i)

@[simp] theorem gatePhysical_append (p q : Program) :
    GatePhysical (p++q) ↔ GatePhysical p ∧ GatePhysical q := by
  simp only [GatePhysical,List.mem_append,or_imp,forall_and]

theorem copyRegister_physical (control : Option Wire) (src dst : List Wire)
    (hnd : (src++dst).Nodup) (hc : ∀ c ∈ control, c ∉ dst) :
    GatePhysical (copyRegister control src dst) := by
  induction src generalizing dst with
  | nil => simp [copyRegister,GatePhysical]
  | cons a src ih =>
    cases dst with
    | nil => simp [copyRegister,GatePhysical]
    | cons b dst =>
      have hab : a ≠ b := by
        intro e; subst b
        have h := List.nodup_iff_count.mp hnd a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have ht : (src++dst).Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hnd q
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      rw [copyRegister,gatePhysical_append]
      constructor
      · cases control with
        | none => simpa [GatePhysical,copyGate,PhysicalInstr,ProperGate] using hab
        | some c =>
          have hcb : c ≠ b := fun e => hc c rfl (by simp [e])
          simpa [GatePhysical,copyGate,PhysicalInstr,ProperGate] using And.intro hcb hab
      · exact ih dst ht (fun c hm hh => hc c hm (List.mem_cons_of_mem _ hh))

theorem majority_physical (a b cin carry : Wire) (hn : [a,b,cin,carry].Nodup) :
    GatePhysical (majority a b cin carry) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  simp_all [GatePhysical,majority,PhysicalInstr,ProperGate]

theorem eraseCarry_physical (a b cin carry : Wire) : GatePhysical (eraseCarry a b cin carry) := by
  simp [GatePhysical,eraseCarry,PhysicalInstr]

theorem eraseMask_physical (c : Wire) (src dst : List Wire) : GatePhysical (eraseMask c src dst) := by
  induction src generalizing dst with
  | nil => simp [eraseMask,GatePhysical]
  | cons a src ih =>
    cases dst with
    | nil => simp [eraseMask,GatePhysical]
    | cons b dst =>
      simpa [eraseMask,GatePhysical,PhysicalInstr] using ih dst

theorem addInPlace_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: x ++ y ++ carry).Nodup) : GatePhysical (addInPlace x y carry cin) := by
  induction x generalizing y carry cin with
  | nil => simp [addInPlace,GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases y with
      | nil => simp [addInPlace,GatePhysical]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [addInPlace,GatePhysical]
        | nil =>
          have hab : a ≠ b := by
            intro e; subst b
            have h := List.nodup_iff_count.mp hn a
            simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
            omega
          have hcb : cin ≠ b := by
            intro e; subst cin
            have h := List.nodup_iff_count.mp hn b
            simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
            omega
          simp [addInPlace,GatePhysical,PhysicalInstr,ProperGate,hab,hcb]
    | cons a' xs =>
      cases y with
      | nil => simp [addInPlace,GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [addInPlace,GatePhysical]
        | cons b' ys =>
          cases carry with
          | nil => simp [addInPlace,GatePhysical]
          | cons k ks =>
            have hs : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
            have ht : (k :: (a'::xs) ++ (b'::ys) ++ ks).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append] at h ⊢; omega
            have htail := ih (b'::ys) ks k ht
            rw [addInPlace]
            simp only [gatePhysical_append]
            refine ⟨⟨⟨majority_physical _ _ _ _ hs,htail⟩,eraseCarry_physical _ _ _ _⟩,?_⟩
            simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
              not_or,not_false_eq_true,and_true] at hs
            have hcb : cin ≠ b := Ne.symm hs.2.1.1
            simp [GatePhysical,PhysicalInstr,ProperGate,hs.1.1,hcb]

theorem notRegister_physical (r : List Wire) : GatePhysical (notRegister r) := by
  simp [GatePhysical,notRegister,PhysicalInstr,ProperGate]

theorem subInPlace_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: x ++ y ++ carry).Nodup) : GatePhysical (subInPlace x y carry cin) := by
  simp only [subInPlace,gatePhysical_append]
  exact ⟨⟨notRegister_physical _,addInPlace_physical _ _ _ _ hn⟩,notRegister_physical _⟩

theorem swapRegisters_physical (c : Wire) (a b : List Wire)
    (hn : (c :: a ++ b).Nodup) : GatePhysical (swapRegisters c a b) := by
  have nd := List.nodup_cons.mp hn
  have ba : (b++a).Nodup := List.nodup_append_comm.mpr nd.2
  have back := copyRegister_physical none b a ba (by simp)
  have mid := copyRegister_physical (some c) a b nd.2
    (by intro q hq h; cases hq; exact nd.1 (List.mem_append_right _ h))
  simp only [swapRegisters,gatePhysical_append]
  exact ⟨⟨back,mid⟩,back⟩

theorem xorConstant_physical (r : List Wire) (k : Nat) : GatePhysical (xorConstant r k) := by
  induction r generalizing k with
  | nil => simp [xorConstant,GatePhysical]
  | cons a r ih =>
    rw [xorConstant,gatePhysical_append]
    refine ⟨?_,ih _⟩
    split <;> simp [GatePhysical,PhysicalInstr,ProperGate]

theorem maskedConstant_physical (c : Wire) (r : List Wire) (k : Nat) (hc : c ∉ r) :
    GatePhysical (maskedConstant c r k) := by
  induction r generalizing k with
  | nil => simp [maskedConstant,GatePhysical]
  | cons a r ih =>
    have ha : c ≠ a := fun e => hc (by simp [e])
    have hr : c ∉ r := fun h => hc (List.mem_cons_of_mem _ h)
    rw [maskedConstant,gatePhysical_append]
    refine ⟨?_,ih _ hr⟩
    split <;> simp [GatePhysical,PhysicalInstr,ProperGate,ha]

theorem swapBits_physical (a b : Wire) (h : a ≠ b) : GatePhysical (swapBits a b) := by
  simp [GatePhysical,swapBits,PhysicalInstr,ProperGate,h,Ne.symm h]

theorem rotate_physical (r : List Wire) (hn : r.Nodup) :
    GatePhysical (rotateRight r) ∧ GatePhysical (rotateLeft r) := by
  induction r with
  | nil => simp [rotateRight,rotateLeft,GatePhysical]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,GatePhysical]
    | cons b r =>
      have ht := ih hn.tail
      have hab : a ≠ b := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
      simp only [rotateRight,rotateLeft,gatePhysical_append]
      exact ⟨⟨swapBits_physical _ _ hab,ht.1⟩,⟨ht.2,swapBits_physical _ _ hab⟩⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredCanonicalMod.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- The exact canonical add core reuses one carry bank. Its source is already
canonical; normalization and source copy/unload are separate streamed steps. -/
structure MeasuredCanonicalModLayout where
  src : List Wire
  out : List Wire
  carry : List Wire
  high : Wire
  cin : Wire
  flag : Wire

namespace MeasuredCanonicalModLayout

def extended (L : MeasuredCanonicalModLayout) : List Wire := L.out++[L.high]
def wires (L : MeasuredCanonicalModLayout) : List Wire :=
  L.src++L.out++L.carry++[L.high,L.cin,L.flag]

structure Widths (L : MeasuredCanonicalModLayout) (n : Nat) : Prop where
  src : L.src.length=n
  out : L.out.length=n
  carry : L.carry.length=n

def sum (L : MeasuredCanonicalModLayout) : Program :=
  mappedAdd (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)])
    L.extended L.carry L.cin

def program (L : MeasuredCanonicalModLayout) (c p : Nat) : Program :=
  L.sum++
    compareConstantGe L.out (L.carry.take (L.out.length-1)) L.cin L.flag p++
    [.CX L.high L.flag]++
    mappedConstAdd (some L.flag) L.extended L.carry L.cin c++
    [.CX L.flag L.high]++
    eraseLtChain L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag

theorem program_counts (L : MeasuredCanonicalModLayout) (n c p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    toffoliCount (L.program c p)=4*n-1 ∧
    measurementCount (L.program c p)=4*n-1 := by
  have extendedLength : L.extended.length=n+1 := by simp [extended,hw.out]
  have sourceLength : (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)]).length=n+1 := by
    simp [mappedRead,hw.src]
  have sumCounts := mappedAdd_counts (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)])
    L.extended L.carry L.cin (sourceLength.trans extendedLength.symm)
    (by rw [hw.carry,extendedLength])
  have geCounts := compareConstantGe_counts L.out (L.carry.take (L.out.length-1))
    L.cin L.flag p (by simp [hw.carry,hw.out]; omega)
  have correction := mappedConstAdd_counts (some L.flag) L.extended L.carry L.cin c
    (by rw [hw.carry,extendedLength])
  have eraseCounts := eraseLtChain_counts L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag
    (hw.out.trans hw.src.symm) (by simp [hw.carry,hw.out,hw.src]; omega)
  constructor
  · simp only [program,sum,toffoliCount_append,toffoliCount]
    rw [sumCounts.1,geCounts.1,correction.1,eraseCounts.1,extendedLength,hw.out,hw.src]
    omega
  · simp only [program,sum,measurementCount_append,measurementCount]
    rw [sumCounts.2,geCounts.2,correction.2,eraseCounts.2,extendedLength,hw.out,hw.src]
    omega

theorem secp_program_counts (L : MeasuredCanonicalModLayout) (hw : L.Widths 256) (c p : Nat) :
    toffoliCount (L.program c p)=1023 ∧ measurementCount (L.program c p)=1023 := by
  simpa using L.program_counts 256 c p hw (by decide)

end MeasuredCanonicalModLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedArithmeticPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem borrowMajority_physical (x y cin target : Wire) (hn : [x,y,cin,target].Nodup) :
    GatePhysical (borrowMajority x y cin target) := by
  simp only [borrowMajority,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate],majority_physical x y cin target hn⟩,
    by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem eraseBorrow_physical (x y cin target : Wire) :
    GatePhysical (eraseBorrow x y cin target) := by
  simp [eraseBorrow,GatePhysical,eraseCarry,PhysicalInstr,ProperGate]

theorem mappedMajority_physical (b : MappedBit) (y cin target : Wire)
    (hn : [y,cin,target].Nodup) (ha : ∀ q ∈ b.wire, q ∉ [y,cin,target]) :
    GatePhysical (mappedMajority b y cin target) := by
  cases hw : b.wire with
  | none =>
    cases hf : b.flip <;>
      simp_all [mappedMajority,GatePhysical,PhysicalInstr,ProperGate,List.nodup_cons]
  | some a =>
    have h4 : [a,y,cin,target].Nodup := List.nodup_cons.mpr ⟨ha a (by simp [hw]),hn⟩
    cases hf : b.flip
    · simpa [mappedMajority,hw,hf] using majority_physical a y cin target h4
    · simpa [mappedMajority,hw,hf] using borrowMajority_physical a y cin target h4

theorem mappedEraseCarry_physical (b : MappedBit) (y cin target : Wire) :
    GatePhysical (mappedEraseCarry b y cin target) := by
  cases hw : b.wire with
  | none => simp [mappedEraseCarry,hw,GatePhysical,PhysicalInstr]
  | some a =>
    cases hf : b.flip
    · simpa [mappedEraseCarry,hw,hf] using eraseCarry_physical a y cin target
    · simpa [mappedEraseCarry,hw,hf] using eraseBorrow_physical a y cin target

theorem mappedSum_physical (b : MappedBit) (y cin : Wire)
    (hn : cin ≠ y) (ha : ∀ q ∈ b.wire, q ≠ y) : GatePhysical (mappedSum b y cin) := by
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp_all [mappedSum,GatePhysical,PhysicalInstr,ProperGate]

theorem mappedAdd_physical (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin :: ys ++ carry).Nodup)
    (ha : ∀ b ∈ bits, ∀ q ∈ b.wire, q ∉ cin :: ys ++ carry) :
    GatePhysical (mappedAdd bits ys carry cin) := by
  induction bits generalizing ys carry cin with
  | nil => simp [mappedAdd,GatePhysical]
  | cons b bs ih =>
    cases bs with
    | nil =>
      cases ys with
      | nil => simp [mappedAdd,GatePhysical]
      | cons y rest =>
        cases rest with
        | cons z zs => simp [mappedAdd,GatePhysical]
        | nil =>
          apply mappedSum_physical
          · intro he; subst cin
            exact (List.nodup_cons.mp hn).1 (by simp)
          · intro q hq he; subst q
            exact ha b (by simp) y hq (by simp)
    | cons b' bs =>
      cases ys with
      | nil => simp [mappedAdd,GatePhysical]
      | cons y rest =>
        cases rest with
        | nil => simp [mappedAdd,GatePhysical]
        | cons y' ys =>
          cases carry with
          | nil => simp [mappedAdd,GatePhysical]
          | cons k ks =>
            have hs : [y,cin,k].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
            have ht : (k :: (y'::ys) ++ ks).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append] at h ⊢; omega
            have hb : ∀ q ∈ b.wire, q ∉ [y,cin,k] := by
              intro q hq hmem
              apply ha b (by simp) q hq
              simp only [List.mem_cons,List.mem_append,List.not_mem_nil] at hmem ⊢
              tauto
            have hat : ∀ z ∈ b'::bs, ∀ q ∈ z.wire, q ∉ k :: (y'::ys) ++ ks := by
              intro z hz q hq hm
              apply ha z (by simp [hz]) q hq
              simp only [List.mem_cons,List.mem_append] at hm ⊢
              tauto
            rw [mappedAdd]
            simp only [gatePhysical_append]
            refine ⟨⟨⟨mappedMajority_physical b y cin k hs hb,ih _ _ _ ht hat⟩,
              mappedEraseCarry_physical b y cin k⟩,?_⟩
            apply mappedSum_physical
            · intro he; subst cin
              exact (List.nodup_cons.mp hs).1 (by simp)
            · intro q hq he; subst q; exact hb y hq (by simp)


private theorem mappedConstant_source (c : Option Wire) (n k : Nat) (b : MappedBit)
    (hb : b ∈ mappedConstant c n k) (q : Wire) (hq : q ∈ b.wire) : q ∈ c := by
  induction n generalizing k with
  | zero => simp [mappedConstant] at hb
  | succ n ih =>
    simp only [mappedConstant,List.mem_cons] at hb
    rcases hb with rfl | hb
    · cases h : decide (k%2=1) <;> simp_all [mappedConstantBit]
    · exact ih (k/2) hb

theorem mappedConstAdd_physical (c : Option Wire) (ys carry : List Wire) (cin k : Nat)
    (hn : (cin :: ys ++ carry).Nodup) (hc : ∀ q ∈ c, q ∉ cin :: ys ++ carry) :
    GatePhysical (mappedConstAdd c ys carry cin k) := by
  apply mappedAdd_physical _ _ _ _ hn
  intro b hb q hq
  exact hc q (mappedConstant_source c _ _ b hb q hq)

theorem constantBorrow_physical (bit : Bool) (x cin target : Wire)
    (hn : [x,cin,target].Nodup) : GatePhysical (constantBorrow bit x cin target) := by
  simp only [constantBorrow,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate],
    mappedMajority_physical _ _ _ _ hn (by simp)⟩,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem constantBorrowErase_physical (bit : Bool) (x cin target : Wire) :
    GatePhysical (constantBorrowErase bit x cin target) := by
  simp only [constantBorrowErase,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate],
    mappedEraseCarry_physical _ _ _ _⟩,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem compareConstantLt_physical (xs carry : List Wire) (cin target k : Nat)
    (hn : ([cin,target] ++ xs ++ carry).Nodup) :
    GatePhysical (compareConstantLt xs carry cin target k) := by
  induction xs generalizing carry cin k with
  | nil => simp [compareConstantLt,GatePhysical]
  | cons x xs ih =>
    cases xs with
    | nil =>
      apply constantBorrow_physical
      apply List.nodup_iff_count.mpr; intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
    | cons x' xs =>
      cases carry with
      | nil => simp [compareConstantLt,GatePhysical]
      | cons c cs =>
        have hs : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
        have ht : ([c,target] ++ (x'::xs) ++ cs).Nodup := by
          apply List.nodup_iff_count.mpr; intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
        rw [compareConstantLt]
        simp only [gatePhysical_append]
        exact ⟨⟨constantBorrow_physical _ _ _ _ hs,ih _ _ _ ht⟩,
          constantBorrowErase_physical _ _ _ _⟩

theorem compareConstantGe_physical (xs carry : List Wire) (cin target k : Nat)
    (hn : ([cin,target] ++ xs ++ carry).Nodup) :
    GatePhysical (compareConstantGe xs carry cin target k) := by
  simp only [compareConstantGe,gatePhysical_append]
  exact ⟨compareConstantLt_physical _ _ _ _ _ hn,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩


theorem eraseLtChain_physical (xs ys carry : List Wire) (cin target : Wire)
    (hn : (cin :: xs ++ ys ++ carry).Nodup) :
    GatePhysical (eraseLtChain xs ys carry cin target) := by
  induction xs generalizing ys carry cin with
  | nil => simp [eraseLtChain,GatePhysical]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [eraseLtChain,GatePhysical]
      | cons y rest =>
        cases rest with
        | nil => exact eraseBorrow_physical _ _ _ _
        | cons y' ys => simp [eraseLtChain,GatePhysical]
    | cons x' xs =>
      cases ys with
      | nil => simp [eraseLtChain,GatePhysical]
      | cons y rest =>
        cases rest with
        | nil => simp [eraseLtChain,GatePhysical]
        | cons y' ys =>
          cases carry with
          | nil => simp [eraseLtChain,GatePhysical]
          | cons c cs =>
            have hs : [x,y,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
            have ht : (c :: (x'::xs) ++ (y'::ys) ++ cs).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append] at h ⊢; omega
            rw [eraseLtChain]
            simp only [gatePhysical_append]
            exact ⟨⟨borrowMajority_physical _ _ _ _ hs,ih _ _ _ ht⟩,
              eraseBorrow_physical _ _ _ _⟩


theorem MeasuredCanonicalModLayout.physical (L : MeasuredCanonicalModLayout)
    (c p : Nat) (hn : L.wires.Nodup) : GatePhysical (L.program c p) := by
  have count := List.nodup_iff_count.mp hn
  have ndsum : (L.cin :: L.extended ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := count q
    simp only [wires,extended,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  have ndcmp : ([L.cin,L.flag] ++ L.out ++ L.carry.take (L.out.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := count q
    have ht := (List.take_sublist (L.out.length-1) L.carry).count_le q
    simp only [wires,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  have hsum : GatePhysical L.sum := by
    apply mappedAdd_physical _ _ _ _ ndsum
    intro b hb q hq hm
    simp only [mappedRead,List.mem_append,List.mem_map,List.mem_singleton] at hb
    rcases hb with ⟨r,hr,rfl⟩ | rfl
    · have eq : q = r := by simpa [eq_comm] using hq
      subst q
      have h := count r
      have hs := List.count_pos_iff.mpr hr
      have hh := List.count_pos_iff.mpr hm
      simp only [wires,extended,List.count_cons,List.count_append,List.count_nil] at h hh
      omega
    · simp at hq
  have hfc : ∀ q ∈ some L.flag, q ∉ L.cin :: L.extended ++ L.carry := by
    intro q hq hm
    have eq : q = L.flag := by simpa [eq_comm] using hq
    subst q
    have h := count L.flag
    have hh := List.count_pos_iff.mpr hm
    simp only [wires,extended,List.count_cons,List.count_append,List.count_nil,
      beq_self_eq_true,ite_true] at h hh
    omega
  have hf : L.high ≠ L.flag := by
    intro he
    have h := count L.high
    simp only [wires,List.count_cons,List.count_append,List.count_nil,he,
      beq_self_eq_true,ite_true] at h
    omega
  have nderase : (L.cin :: L.out ++ L.src ++ L.carry.take (L.out.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := count q
    have ht := (List.take_sublist (L.out.length-1) L.carry).count_le q
    simp only [wires,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  simp only [program,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨hsum,compareConstantGe_physical _ _ _ _ _ ndcmp⟩,
    by simpa [GatePhysical,PhysicalInstr,ProperGate] using hf⟩,
    mappedConstAdd_physical _ _ _ _ _ ndsum hfc⟩,
    by simpa [GatePhysical,PhysicalInstr,ProperGate] using Ne.symm hf⟩,
    eraseLtChain_physical _ _ _ _ _ nderase⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/LiteralConstPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem literalCells_physical (bit : Bool) (x cin cout one : Wire)
    (hn : [x,cin,cout].Nodup) :
    GatePhysical (literalConstStep bit x cin cout) ∧
    GatePhysical (literalConstErase bit x cin cout one) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  cases bit <;> simp_all [literalConstStep,literalConstSum,literalConstCarry,
    literalConstErase,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

theorem literalAdd_physical (xs carry : List Wire) (cin one k : Nat)
    (hn : (cin::xs++carry).Nodup) : GatePhysical (literalConstAdd xs carry cin one k) := by
  induction xs generalizing carry cin k with
  | nil => simp [literalConstAdd,GatePhysical]
  | cons x xs ih =>
    cases xs with
    | nil =>
      have ne : cin≠x := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
      simp only [literalConstAdd]
      unfold literalConstSum
      split <;> simp [GatePhysical,PhysicalInstr,ProperGate,ne]
    | cons y ys =>
      cases carry with
      | nil => simp [literalConstAdd,GatePhysical]
      | cons c cs =>
        have small : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
        have tail : (c::(y::ys)++cs).Nodup := by
          apply List.nodup_iff_count.mpr; intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append] at h ⊢; omega
        have cells := literalCells_physical (decide (k%2=1)) x cin c one small
        have recs := ih cs c (k/2) tail
        simp only [literalConstAdd,gatePhysical_append]
        exact ⟨⟨cells.1,recs⟩,cells.2⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedConvertPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum
theorem balancedConverters_physical (L : BalancedConvert.Layout) (hn : L.wires.Nodup) :
    GatePhysical (BalancedConvert.center L) ∧ GatePhysical (BalancedConvert.canonical L) := by
  have nd : (L.cin::L.word++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    simp only [BalancedConvert.Layout.wires,BalancedConvert.Layout.word,
      List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  have src : ∀ b∈BalancedConvert.correction L,∀q∈b.wire,q∉L.cin::L.word++L.carry := by
    intro b hb q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    dsimp only at hq
    split at hq
    · have eq : q=L.flag := by simpa [eq_comm] using hq
      subst q
      intro hm
      have h := List.nodup_iff_count.mp hn L.flag
      have hp := List.count_pos_iff.mpr hm
      simp only [BalancedConvert.Layout.wires,BalancedConvert.Layout.word,
        List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h hp
      omega
    · simp at hq
  have mf : L.msb≠L.flag := by
    intro eq
    have h := List.nodup_iff_count.mp hn L.flag
    simp only [BalancedConvert.Layout.wires,eq,List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have cx : GatePhysical [.CX L.msb L.flag] := by simp [GatePhysical,PhysicalInstr,ProperGate,mf]
  have a := literalAdd_physical L.word L.carry L.cin L.one BalancedConvert.bias nd
  have b := literalAdd_physical L.word L.carry L.cin L.one BalancedConvert.inverseBias nd
  have ma := mappedAdd_physical _ _ _ _ nd src
  have nt := notRegister_physical L.word
  have ms : GatePhysical (mappedSub (BalancedConvert.correction L) L.word L.carry L.cin) := by
    simpa only [mappedSub,gatePhysical_append] using And.intro (And.intro nt ma) nt
  have pred : GatePhysical (BalancedConvert.predicate L) := by
    simpa only [BalancedConvert.predicate,gatePhysical_append] using And.intro (And.intro a cx) b
  simp only [BalancedConvert.center,BalancedConvert.canonical,gatePhysical_append]
  exact ⟨⟨⟨pred,ma⟩,cx⟩,⟨⟨cx,ms⟩,pred⟩⟩
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedRawCircuitProof.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 300000
namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

/-- The extended raw words and their control/carry sites are physically distinct. -/
theorem rawLayoutND (L : Layout) (hn : L.wires.Nodup) :
    (L.sign::(rawSource L++rawTarget L++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,rawSource,rawTarget,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

/-- The actual 257-bit signed addition, including every measurement's
phase correction, implements the unbounded signed sum on every centered pair. -/
theorem rawAdd_signed (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    Triple (fun s => s L.sign=B ∧ signedRegValue (rawSource L) s=Y ∧
      signedRegValue (rawTarget L) s=X ∧ regValue L.carry s=0)
      (rawAdd L)
      (fun s => s L.sign=B ∧ signedRegValue (rawSource L) s=Y ∧
        signedRegValue (rawTarget L) s=rawSum B X Y ∧ regValue L.carry s=0) := by
  have w := widths L hw
  have hsum := rawSum_bounds B X Y hx hy
  have hp := constants
  have bound : -((2^256 : Nat) : Int)≤rawSum B X Y ∧ rawSum B X Y<((2^256 : Nat) : Int) := by
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at ⊢
    have pow : (2^256 : Int)=2*(2^255 : Int) := by norm_num
    omega
  have arithmetic : signedIntegerValue B Y X=rawSum B X Y := by
    cases B <;> simp [signedIntegerValue,rawSum,signedY,sub_eq_add_neg]
  have result := signedAdd_int_spec L.sign (rawSource L) (rawTarget L) L.carry
    (rawLayoutND L hn) (by omega) (by omega) B Y X
    (by rw [w.2.1,arithmetic]; norm_num only [Nat.reduceSub]; exact bound.1)
    (by rw [w.2.1,arithmetic]; norm_num only [Nat.reduceSub]; exact bound.2)
  simpa only [rawAdd,signedAdd,arithmetic] using result

/-- Every physical bit outside the extended target word is restored,
including source, control, raw parity and the complete carry bank. -/
theorem rawAdd_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hc : regValue L.carry s.basis=0)
    (a : Wire) (ha : a∉rawTarget L) :
    (run (rawAdd L) m s).basis a=s.basis a := by
  have w := widths L hw
  have hf := (signedWord_frame L.sign (rawSource L) (rawTarget L) L.carry
    (rawLayoutND L hn) (by omega) (by omega) (s.basis L.sign)
    (regValue (rawSource L) s.basis) (regValue (rawTarget L) s.basis)
    s m rfl rfl rfl hc a ha).1
  simpa only [rawAdd,signedAdd] using hf

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedCoreLayoutProof.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

def work (L : Layout) := [L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.lower,L.one]++L.carry

theorem scalarND (L : Layout) (hn : L.wires.Nodup) :
    [L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0].Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem seedND (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    [L.sourceGuard,L.one,L.parity,L.ymsb,L.rmsb,L.ylow.getD 0 0,L.r0].Nodup := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as =>
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [Layout.wires,BalancedCleanup.Layout.wires,hy,List.getD_cons_zero,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega

theorem rawTargetND (L : Layout) (hn : L.wires.Nodup) : (rawTarget L).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q; have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,rawTarget,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem allND (L : Layout) (hn : L.wires.Nodup) :
    ([L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]++
      (L.r++L.y++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q; have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem foldND (L : Layout) (hn : L.wires.Nodup) :
    ([L.plus,L.minus,L.parity]++(foldTarget L++[L.cout]++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q; have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,foldTarget,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem flagAway (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
    q∉L.r++L.y++L.carry :=
  fun h => List.disjoint_left.mp (List.nodup_append'.mp (allND L hn)).2.2 hq h

theorem signed_extension (lo : List Wire) (msb guard : Wire) (b : BasisState)
    (hg : b guard=b msb) : signedRegValue ((lo++[msb])++[guard]) b=signedRegValue (lo++[msb]) b := by
  rw [signedRegValue_msb,signedRegValue_msb,regValue_append]
  cases hm : b msb <;>
    simp [hg,hm,regValue,List.length_append,Nat.pow_succ,Nat.cast_add,Nat.cast_mul] <;> ring

theorem word_encoding (r : List Wire) (n : Nat) (hn : r.length=n) (b : BasisState) (X : Int)
    (hx : signedRegValue r b=X) : regValue r b=encodeWord n X := by
  have he := encode_decodeWord n (regValue r b) (by simpa [hn] using regValue_lt r b)
  change encodeWord n (signedDecode n (regValue r b))=regValue r b at he
  change signedDecode r.length (regValue r b)=X at hx
  rw [hn] at hx
  rw [hx] at he
  exact he.symm

theorem word_sign (lo : List Wire) (msb : Wire) (b : BasisState) (X : Int)
    (hx : signedRegValue (lo++[msb]) b=X) : b msb=decide (X<0) := by
  have h := signedRegValue_neg_iff lo msb b
  rw [hx] at h
  cases hb : b msb
  · have hx0 : ¬X<0 := fun hn => by have hh := h.mp hn; simp [hb] at hh
    simp [hx0]
  · have hx0 : X<0 := h.mpr hb
    simp [hx0]

private theorem add_parity (X Y : Int) : originalParity (X+Y)=(originalParity Y ^^ originalParity X) := by
  have px := originalParity_value X
  have py := originalParity_value Y
  have pt := originalParity_value (X+Y)
  cases hx : originalParity X <;> cases hy : originalParity Y <;> cases ht : originalParity (X+Y)
  all_goals simp only [hx,hy,ht,Bool.false_eq_true,if_false,if_true] at px py pt ⊢
  all_goals first | rfl | omega

theorem raw_parity (S : Bool) (X Y : Int) :
    originalParity (rawSum S X Y)=(originalParity Y ^^ originalParity X) := by
  have neg : originalParity (-Y)=originalParity Y := by
    unfold originalParity
    apply decide_eq_decide.mpr
    omega
  cases S <;> simp only [rawSum,signedY,Bool.false_eq_true,if_false,if_true]
  · exact add_parity X Y
  · rw [add_parity,neg]

theorem word_parity (low : Wire) (tail : List Wire) (b : BasisState) (X : Int)
    (hx : signedRegValue (low::tail) b=X) : b low=originalParity X := by
  have h := signedRegValue_even_iff low tail b
  rw [hx] at h
  cases hb : b low
  · have he : X%2=0 := h.mpr hb
    simp [originalParity,he]
  · have he : X%2≠0 := fun he => by have hh := h.mp he; simp [hb] at hh
    simp [originalParity,he]

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedFoldMathViews.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic.BalancedFold
open BalancedField BalancedCircuit

/-- Repeated virtual source positions touch only the two immutable selectors. -/
theorem foldBits_sources (L : BalancedCircuit.Layout) (w : Wire)
    (hw : w∈mappedWires (foldBits L)) : w=L.plus ∨ w=L.minus := by
  obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp hw
  rw [foldBits] at hb
  rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨i,hi,he⟩ := List.mem_map.mp hb
    subst b
    cases ht : sparseF.testBit (i+1)
    · right; simpa [ht] using hm
    · left; simpa [ht] using hm
  · have he : b={wire:=none,flip:=false} := by simpa using hb
    subst b
    simp at hm

private theorem generic_toggle_bound (M U r : Nat) (a s : Bool)
    (hr : r<M) (hd : r+M*s.toNat=U) :
    (if a then if s then U-M else U+M else U)<2*M := by
  cases a <;> cases s <;> simp at hd ⊢ <;> omega

theorem toggledWord_bound (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T<2^257 := by
  have hd := Nat.mod_add_div (encodeWord 257 T) modulusWord
  rw [raw_sign T ht] at hd
  have hr := Nat.mod_lt (encodeWord 257 T) (show 0<modulusWord by norm_num [modulusWord])
  have h := generic_toggle_bound modulusWord (encodeWord 257 T)
    (encodeWord 257 T%modulusWord) (originalParity T) (decide (T<0)) hr hd
  have hm : 2*modulusWord=(2^257 : Nat) := by decide
  simpa only [toggledWord,hm] using h

private theorem generic_half_bound (U M : Nat) (h : U<2*M) : U/2<M := by omega

theorem prepared_upper_bound (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T/2<modulusWord := by
  have h := toggledWord_bound T ht
  have hm : 2*modulusWord=(2^257 : Nat) := by decide
  rw [←hm] at h
  exact generic_half_bound _ _ h

end ECDSAAdd.Arithmetic.BalancedFold
end

-- source: ECDSAAdd/Arithmetic/BalancedCoreFoldProof.lean
noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField BalancedFold

private theorem bit_split (M x E : Nat) (b v : Bool) (hx : x<M) (hE : E<M)
    (he : x+M*b.toNat=E+M*v.toNat) : x=E ∧ b=v := by
  cases b <;> cases v <;> simp at he ⊢ <;> omega

/-- The actual extended mapped adder and final Cout XOR. No arithmetic
oracle is substituted, and all measurement records have restored phase. -/
theorem fold_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hu : s.basis L.plus=plusController T) (hv : s.basis L.minus=minusController T)
    (hc : s.basis L.cout=false) (hcarry : regValue L.carry s.basis=0)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    (run (fold L) m s).phase=s.phase ∧
    regValue (foldTarget L) (run (fold L) m s).basis=encodeWord 256 (halfResult T) ∧
    (run (fold L) m s).basis L.cout=false ∧
    ∀ w,w∉foldTarget L → (run (fold L) m s).basis w=s.basis w := by
  let ys := foldTarget L++[L.cout]
  have nd : (L.plus::L.minus::L.parity::(ys++L.carry)).Nodup := by
    simpa only [ys,List.cons_append,List.nil_append,List.append_assoc] using foldND L hn
  have n1 := List.nodup_cons.mp nd
  have n2 := List.nodup_cons.mp n1.2
  have n3 := List.nodup_cons.mp n2.2
  have yND : ys.Nodup := (List.nodup_append'.mp n3.2).1
  have minusAway : L.minus∉ys := by
    intro h; exact n2.1 (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have coutAway : L.cout∉foldTarget L := by
    intro h
    exact List.disjoint_left.mp (List.nodup_append'.mp yND).2.2 h (by simp)
  have sourceAway : ∀ w∈mappedWires (foldBits L),w∉L.parity::(ys++L.carry) := by
    intro w h
    rcases foldBits_sources L w h with rfl|rfl
    · intro h; exact n1.1 (List.mem_cons_of_mem _ h)
    · exact n2.1
  have widths := BalancedCircuit.widths L hw
  have ylen : ys.length=257 := widths.2.2.1
  have lowlen : (foldTarget L).length=256 := by
    have h := ylen
    simp only [ys,List.length_append,List.length_cons,List.length_nil] at h
    omega
  have init : regValue ys s.basis=toggledWord T/2 := by
    rw [regValue_append,hword]
    simp [regValue,hc]
  have source : mappedValue (foldBits L) s.basis=
      selectedSource (plusController T) (minusController T) := by
    have hex : ¬(s.basis L.plus && s.basis L.minus)=true := by
      rw [hu,hv]; exact controllers_exclusive T
    simpa only [hu,hv] using foldBits_value L s.basis hex
  have hadd := mappedAdd_correct (foldBits L) ys L.carry L.parity n2.2 sourceAway
    (by omega) (by omega) s m ((regValue_zero _ _).mp hcarry)
  generalize hr : run (mappedAdd (foldBits L) ys L.carry L.parity) m s=r at hadd
  have value : regValue ys r.basis=foldedSum T := by
    have h := hadd.2.2
    rw [source,init,hp,ylen,Nat.add_comm (selectedSource _ _) (toggledWord T/2)] at h
    change regValue ys r.basis=foldedSum T%2^257 at h
    rw [Nat.mod_eq_of_lt (foldedSum_bound T ht)] at h
    exact h
  have split := regValue_append (foldTarget L) [L.cout] r.basis
  have one : regValue [L.cout] r.basis=(r.basis L.cout).toNat := by
    cases h : r.basis L.cout <;> simp [regValue,h]
  rw [one,lowlen] at split
  have eqvalue : regValue (foldTarget L) r.basis+
      modulusWord*(r.basis L.cout).toNat=
      encodeWord 256 (halfResult T)+modulusWord*(minusController T).toNat := by
    exact split.symm.trans (value.trans (foldedSum_value T ht))
  have decoded := bit_split modulusWord (regValue (foldTarget L) r.basis)
    (encodeWord 256 (halfResult T)) (r.basis L.cout) (minusController T)
    (by simpa only [lowlen,modulusWord] using regValue_lt (foldTarget L) r.basis)
    (encodeWord_bound 256 (halfResult T)) eqvalue
  have minusR : r.basis L.minus=minusController T := (hadd.2.1 L.minus minusAway).trans hv
  have actual : run (fold L) m s=
      ⟨r.phase,writeBit r.basis L.cout (r.basis L.cout ^^ r.basis L.minus)⟩ := by
    unfold fold
    rw [run_append,run_take,hr]
    rfl
  have lowKeep : regValue (foldTarget L)
      (writeBit r.basis L.cout (r.basis L.cout ^^ r.basis L.minus))=
      regValue (foldTarget L) r.basis := by
    apply regValue_congr
    intro w hw
    simp [writeBit,show w≠L.cout from fun he => coutAway (he ▸ hw)]
  rw [actual]
  refine ⟨hadd.1,lowKeep.trans decoded.1,?_,?_⟩
  · simp [writeBit,decoded.2,minusR]
  · intro w hw
    by_cases he : w=L.cout
    · subst w; simp [writeBit,decoded.2,minusR,hc]
    · simp only [writeBit,Function.update_of_ne he]
      apply hadd.2.1
      simp only [ys,List.mem_append,List.mem_singleton]
      exact not_or.mpr ⟨hw,he⟩

/-- The actual Clifford rotate divides the cleared-low-bit raw word by
two. Its old zero low bit becomes the clean One guard. -/
theorem rotate_folded (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (_ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hzero : s.basis L.r0=false)
    (hword : regValue (foldTarget L) s.basis=encodeWord 256 (halfResult T)) :
    (run (rotateRight (rawTarget L)) m s).phase=s.phase ∧
    regValue L.r (run (rotateRight (rawTarget L)) m s).basis=encodeWord 256 (halfResult T) ∧
    (run (rotateRight (rawTarget L)) m s).basis L.one=false ∧
    ∀ w,w∉rawTarget L → (run (rotateRight (rawTarget L)) m s).basis w=s.basis w := by
  have shape : rawTarget L=L.r0::foldTarget L := by
    simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have init : regValue (rawTarget L) s.basis=2*encodeWord 256 (halfResult T) := by
    rw [shape]
    change (if s.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) s.basis=_
    simp [hzero,hword]
  have rr := rotateRight_spec (rawTarget L) (rawTargetND L hn)
    (2*encodeWord 256 (halfResult T)) (by omega) s m init
  have frame := (rotate_frame (rawTarget L) s m).2.1
  generalize hr : run (rotateRight (rawTarget L)) m s=r at rr frame ⊢
  have value : regValue (rawTarget L) r.basis=encodeWord 256 (halfResult T) := by
    have h := rr.2
    change regValue (rawTarget L) r.basis=(2*encodeWord 256 (halfResult T))/2 at h
    omega
  have rlen : L.r.length=256 := (BalancedCleanup.widths L.toLayout hw).2.1
  have split := regValue_append L.r [L.one] r.basis
  have one : regValue [L.one] r.basis=(r.basis L.one).toNat := by
    cases h : r.basis L.one <;> simp [regValue,h]
  rw [one,rlen] at split
  have eqvalue : regValue L.r r.basis+modulusWord*(r.basis L.one).toNat=
      encodeWord 256 (halfResult T)+modulusWord*false.toNat := by
    simpa only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using split.symm.trans value
  have decoded := bit_split modulusWord (regValue L.r r.basis)
    (encodeWord 256 (halfResult T)) (r.basis L.one) false
    (by simpa only [rlen,modulusWord] using regValue_lt L.r r.basis)
    (encodeWord_bound 256 (halfResult T)) eqvalue
  exact ⟨rr.1,decoded.1,decoded.2,frame⟩

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedCoreFlagsProof.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

theorem seedViews_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hg : s.basis L.sourceGuard=false)
    (ho : s.basis L.one=false) (hp : s.basis L.parity=false) :
    run (seedViews L) m s=⟨s.phase,writeBit (writeBit (writeBit s.basis L.sourceGuard
      (s.basis L.ymsb)) L.one (s.basis L.rmsb)) L.parity
      (s.basis (L.ylow.getD 0 0) ^^ s.basis L.r0)⟩ := by
  have nd := seedND L hw hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6⟩,⟨h2_3,h2_4,h2_5,h2_6⟩,⟨h3_4,h3_5,h3_6⟩,⟨h4_5,h4_6⟩,h5_6⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h0_6r := Ne.symm h0_6
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h1_6r := Ne.symm h1_6
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h2_6r := Ne.symm h2_6
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h3_6r := Ne.symm h3_6
  have h4_5r := Ne.symm h4_5
  have h4_6r := Ne.symm h4_6
  have h5_6r := Ne.symm h5_6
  simp only [seedViews,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hqg : q=L.sourceGuard <;> by_cases hqo : q=L.one <;> by_cases hqp : q=L.parity <;>
    simp_all [writeBit,Function.update]

theorem prepareFold_run (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (ho : s.basis L.one=N)
    (hr : s.basis L.r0=P) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) :
    run (prepareFold L) m s=⟨s.phase,
      writeBit (writeBit (writeBit (writeBit (writeBit s.basis L.lower N)
        L.minus (P && N)) L.plus (P && !N)) L.one (N ^^ P)) L.r0 false⟩ := by
  have nd : [L.one,L.parity,L.r0,L.lower,L.minus,L.plus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5⟩,⟨h1_2,h1_3,h1_4,h1_5⟩,⟨h2_3,h2_4,h2_5⟩,⟨h3_4,h3_5⟩,h4_5⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h4_5r := Ne.symm h4_5
  cases P <;> cases N
  all_goals
    simp only [prepareFold,run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hql : q=L.lower <;> by_cases hqm : q=L.minus <;> by_cases hqu : q=L.plus <;>
      by_cases hqo : q=L.one <;> by_cases hqr : q=L.r0 <;>
      simp_all [writeBit,Function.update]

/-- The remaining minus selector is P AND NOT(result sign). Its immediate
Z/CZ correction supplies the exact measured phase for either outcome. -/
theorem releaseSelectors_run (L : Layout) (hn : L.wires.Nodup) (P H : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (hh : s.basis L.rmsb=H)
    (hl : s.basis L.lower=(H ^^ P)) (hm : s.basis L.minus=(P && !H))
    (hu : s.basis L.plus=(P ^^ (P && !H))) :
    run (releaseSelectors L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.lower false) L.plus false) L.minus false⟩ := by
  have nd : [L.parity,L.rmsb,L.lower,L.plus,L.minus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4⟩,⟨h1_2,h1_3,h1_4⟩,⟨h2_3,h2_4⟩,h3_4⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h3_4r := Ne.symm h3_4
  cases P <;> cases H <;> cases hr : m.headD false
  all_goals
    apply State.extensionality
    · simp_all [releaseSelectors,run,measureAndCorrect,correct,writeBit,Function.update]
    · funext q
      by_cases hql : q=L.lower <;> by_cases hqm : q=L.minus <;> by_cases hqu : q=L.plus <;>
        simp_all [releaseSelectors,run,measureAndCorrect,correct,writeBit,Function.update]

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedCoreSeedProof.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

theorem seed_data_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hc : ∀q∈work L,s.basis q=false) :
    ∀q∈L.r++L.y++L.carry,(run (seedViews L) m s).basis q=s.basis q := by
  have he := seedViews_run L hw hn s m (hc _ (by simp [work]))
    (hc _ (by simp [work])) (hc _ (by simp [work]))
  intro q hq
  have ng : q≠L.sourceGuard := fun e => flagAway L hn _ (by simp) (e ▸ hq)
  have no : q≠L.one := fun e => flagAway L hn _ (by simp) (e ▸ hq)
  have np : q≠L.parity := fun e => flagAway L hn _ (by simp) (e ▸ hq)
  rw [he]
  simp [writeBit,ng,no,np]

theorem seed_signed (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Int) (s : State) (m : List Bool)
    (hr : signedRegValue L.r s.basis=X) (hy : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    signedRegValue (rawTarget L) (run (seedViews L) m s).basis=X ∧
    signedRegValue (rawSource L) (run (seedViews L) m s).basis=Y ∧
    regValue L.carry (run (seedViews L) m s).basis=0 := by
  let t := run (seedViews L) m s
  have frame := seed_data_frame L hw hn s m hc
  have sameR : signedRegValue L.r t.basis=X := by
    unfold signedRegValue
    rw [regValue_congr L.r t.basis s.basis (fun q hq => frame q (by simp [hq]))]
    exact hr
  have sameY : signedRegValue L.y t.basis=Y := by
    unfold signedRegValue
    rw [regValue_congr L.y t.basis s.basis (fun q hq => frame q (by simp [hq]))]
    exact hy
  have eq := seedViews_run L hw hn s m (hc _ (by simp [work]))
    (hc _ (by simp [work])) (hc _ (by simp [work]))
  have flags := seedND L hw hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  rcases flags with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6⟩,⟨h2_3,h2_4,h2_5,h2_6⟩,⟨h3_4,h3_5,h3_6⟩,⟨h4_5,h4_6⟩,h5_6⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h0_6r := Ne.symm h0_6
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h1_6r := Ne.symm h1_6
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h2_6r := Ne.symm h2_6
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h3_6r := Ne.symm h3_6
  have h4_5r := Ne.symm h4_5
  have h4_6r := Ne.symm h4_6
  have h5_6r := Ne.symm h5_6
  have one : t.basis L.one=t.basis L.rmsb := by
    rw [show t=run (seedViews L) m s from rfl,eq]
    simp_all [writeBit,Function.update]
  have guard : t.basis L.sourceGuard=t.basis L.ymsb := by
    rw [show t=run (seedViews L) m s from rfl,eq]
    simp_all [writeBit,Function.update]
  refine ⟨(signed_extension L.low L.rmsb L.one t.basis one).trans sameR,
    (signed_extension L.ylow L.ymsb L.sourceGuard t.basis guard).trans sameY,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  exact (frame q (by simp [hq])).trans (hc q (by simp [work,hq]))

theorem seed_parity (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (s : State) (m : List Bool)
    (hr : signedRegValue L.r s.basis=X) (hy : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    (run (seedViews L) m s).basis L.parity=originalParity (rawSum B X Y) := by
  have rp : s.basis L.r0=originalParity X := word_parity L.r0 (L.rtail++[L.rmsb]) s.basis X hr
  have yp : s.basis (L.ylow.getD 0 0)=originalParity Y := by
    cases hy0 : L.ylow with
    | nil => have hw0 := hw.2.1; simp [hy0] at hw0
    | cons a as =>
      have he : signedRegValue (a::(as++[L.ymsb])) s.basis=Y := by simpa [BalancedCleanup.Layout.y,hy0] using hy
      simpa [hy0] using word_parity a (as++[L.ymsb]) s.basis Y he
  rw [seedViews_run L hw hn s m (hc _ (by simp [work]))
    (hc _ (by simp [work])) (hc _ (by simp [work]))]
  simp only [writeBit,Function.update_self,rp,yp]
  exact (raw_parity B X Y).symm

/-- Actual seed-view and signed-add composition, covering unrestricted
incoming phase and every record. No fold circuit premise is introduced. -/
theorem seed_raw_signed (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) (s : State) (m : List Bool)
    (hs : s.basis L.sign=B) (hr : signedRegValue L.r s.basis=X)
    (hyr : signedRegValue L.y s.basis=Y) (hc : ∀q∈work L,s.basis q=false) :
    let t := run (seedViews L++rawAdd L) m s
    t.phase=s.phase ∧ signedRegValue (rawTarget L) t.basis=rawSum B X Y ∧
    signedRegValue (rawSource L) t.basis=Y ∧ regValue L.carry t.basis=0 := by
  let u := run (seedViews L) m s
  have seed := seed_signed L hw hn X Y s m hr hyr hc
  have data := seed_data_frame L hw hn s m hc
  have si : u.basis L.sign=B := by
    have eq := seedViews_run L hw hn s m (hc _ (by simp [work]))
      (hc _ (by simp [work])) (hc _ (by simp [work]))
    have flags : [L.sign,L.sourceGuard,L.one,L.parity].Nodup := by
      apply List.nodup_iff_count.mpr
      intro q; have h := List.nodup_iff_count.mp (scalarND L hn) q
      simp only [List.count_cons,List.count_nil] at h ⊢
      omega
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at flags
    rcases flags with ⟨⟨h0_1,h0_2,h0_3⟩,⟨h1_2,h1_3⟩,h2_3⟩
    have h0_1r := Ne.symm h0_1
    have h0_2r := Ne.symm h0_2
    have h0_3r := Ne.symm h0_3
    have h1_2r := Ne.symm h1_2
    have h1_3r := Ne.symm h1_3
    have h2_3r := Ne.symm h2_3
    rw [show u=run (seedViews L) m s from rfl,eq]
    simp_all [writeBit,Function.update]
  have raw := rawAdd_signed L hw hn B X Y hx hy u m ⟨si,seed.2.1,seed.1,seed.2.2⟩
  have phase : u.phase=s.phase := by
    rw [show u=run (seedViews L) m s from rfl,
      seedViews_run L hw hn s m (hc _ (by simp [work]))
        (hc _ (by simp [work])) (hc _ (by simp [work]))]
  simp only [run_append,run_take,show measurementCount (seedViews L)=0 from rfl,List.drop_zero]
  exact ⟨raw.1.trans phase,raw.2.2.2.1,raw.2.2.1,raw.2.2.2.2⟩

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedCoreCircuitProof.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField BalancedFold

private theorem toggle_upper_arithmetic (E B H : Nat) (P N : Bool)
    (he : E=P.toNat+2*(B+H*N.toNat)) :
    B+H*(N ^^ P).toNat=(if P then if N then E-2*H else E+2*H else E)/2 := by
  cases P <;> cases N <;> simp only [Bool.toNat_true,Bool.toNat_false,
    Bool.false_eq_true,if_false,if_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero,
    Nat.zero_add,Bool.xor_true,Bool.xor_false,Bool.not_true,Bool.not_false] at he ⊢ <;> omega

/-- Physical preparation computes the sparse selectors, flips bit 256 and
clears the raw parity bit. The remaining 256-bit view is the proved upper word. -/
theorem prepare_upper (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (s : State) (m : List Bool) (hr : signedRegValue (rawTarget L) s.basis=T)
    (hp : s.basis L.parity=originalParity T)
    (hl : s.basis L.lower=false) (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) :
    regValue (foldTarget L) (run (prepareFold L) m s).basis=toggledWord T/2 := by
  let P := originalParity T
  let N := decide (T<0)
  have one : s.basis L.one=N := word_sign L.r L.one s.basis T hr
  have hrs : signedRegValue (L.r0::(L.rtail++[L.rmsb,L.one])) s.basis=T := by
    simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using hr
  have low : s.basis L.r0=P := word_parity L.r0 (L.rtail++[L.rmsb,L.one]) s.basis T hrs
  have he := prepareFold_run L hn P N s m hp one low hl hm hu
  let B := regValue (L.rtail++[L.rmsb]) s.basis
  have enc := word_encoding (rawTarget L) 257 (widths L hw).2.1 s.basis T hr
  have shape : encodeWord 257 T=P.toNat+2*(B+2^255*N.toNat) := by
    symm
    change _=encodeWord 257 T at enc
    change (if s.basis L.r0 then 1 else 0)+
      2*regValue ((L.rtail++[L.rmsb])++[L.one]) s.basis=encodeWord 257 T at enc
    rw [regValue_append,show (L.rtail++[L.rmsb]).length=255 by simp [hw.1]] at enc
    simpa [B,low,one,regValue,Bool.toNat,Bool.cond_eq_ite] using enc
  have rawnd := rawTargetND L hn
  change (L.r0::((L.rtail++[L.rmsb])++[L.one])).Nodup at rawnd
  have rAway := (List.nodup_cons.mp rawnd).1
  have same : regValue (L.rtail++[L.rmsb]) (run (prepareFold L) m s).basis=B := by
    apply regValue_congr
    intro q hq
    have member : q∈L.r++L.y++L.carry := by
      have rq : q∈L.r := by
        change q∈L.r0::(L.rtail++[L.rmsb])
        exact List.mem_cons_of_mem L.r0 hq
      exact List.mem_append_left _ (List.mem_append_left _ rq)
    have away (a : Wire) (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : q≠a :=
      fun e => flagAway L hn a ha (e ▸ member)
    have qr : q≠L.r0 := fun e => rAway (List.mem_append_left _ (e ▸ hq))
    rw [he]
    simp [writeBit,qr,away L.lower (by simp),away L.minus (by simp),
      away L.plus (by simp),away L.one (by simp)]
  have fs := scalarND L hn
  have oo : L.one≠L.r0 := by
    have mem : L.one∈(L.rtail++[L.rmsb])++[L.one] := by simp
    exact fun e => rAway (e ▸ mem)
  have high : (run (prepareFold L) m s).basis L.one=(N ^^ P) := by
    rw [he]
    simp only [writeBit,Function.update_of_ne oo,Function.update_self]
  have value : regValue (foldTarget L) (run (prepareFold L) m s).basis=B+2^255*(N ^^ P).toNat := by
    rw [show foldTarget L=(L.rtail++[L.rmsb])++[L.one] by simp [foldTarget,List.append_assoc]]
    rw [regValue_append,same,show (L.rtail++[L.rmsb]).length=255 by simp [hw.1]]
    simp only [regValue,List.foldr_cons,List.foldr_nil,high,Nat.mul_zero,Nat.add_zero]
    cases N <;> cases P <;> rfl
  rw [value]
  change _=(if P then if N then encodeWord 257 T-modulusWord else encodeWord 257 T+modulusWord
    else encodeWord 257 T)/2
  have pow : modulusWord=2*2^255 := by norm_num [modulusWord]
  rw [pow]
  exact toggle_upper_arithmetic _ _ _ P N shape

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedCoreComposeViews.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField BalancedFold

theorem compose_raw_away (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
    a∉rawTarget L := by
  have nd : (rawTarget L++([L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [Layout.wires,BalancedCleanup.Layout.wires,rawTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  exact fun h => List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h ha

theorem compose_fold_subset (L : Layout) (a : Wire) (ha : a∉rawTarget L) : a∉foldTarget L := by
  have shape : rawTarget L=L.r0::foldTarget L := by
    simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  exact fun h => ha (by rw [shape]; exact List.mem_cons_of_mem _ h)

theorem compose_clean_views (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.cout,L.minus,L.plus,L.lower]++L.carry) :
    q∉rawTarget L ∧ q≠L.sourceGuard ∧ q≠L.parity ∧ q∈work L := by
  have qa := compose_raw_away L hn q (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have ng : q≠L.sourceGuard := by
    rcases List.mem_append.mp hq with hq|hq
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> exact Ne.symm (by tauto)
    · intro e
      have hsg : L.sourceGuard∈L.carry := e ▸ hq
      exact flagAway L hn L.sourceGuard (by simp) (by simp [hsg])
  have np : q≠L.parity := by
    rcases List.mem_append.mp hq with hq|hq
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> tauto
    · intro e
      have hp : L.parity∈L.carry := e ▸ hq
      exact flagAway L hn L.parity (by simp) (by simp [hp])
  exact ⟨qa,ng,np,by
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto⟩

theorem compose_not_raw (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]) :
    a∉rawTarget L := by
  have data := flagAway L hn a (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; tauto)
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have no : a≠L.one := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
  simp only [rawTarget,List.mem_append,List.mem_singleton,not_or]
  exact ⟨fun h => data (by simp [h]),no⟩

theorem compose_not_fold_r0 (L : Layout) (hn : L.wires.Nodup) : L.r0∉foldTarget L := by
  have nd := rawTargetND L hn
  simpa [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
    List.append_assoc] using (List.nodup_cons.mp (show (L.r0::foldTarget L).Nodup by
      simpa [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
        List.append_assoc] using nd)).1

theorem compose_seed_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hc : ∀q∈work L,s.basis q=false) :
    (run (seedViews L) m s).phase=s.phase ∧
    (run (seedViews L) m s).basis L.sourceGuard=s.basis L.ymsb ∧
    ∀a,a≠L.sourceGuard → a≠L.one → a≠L.parity →
      (run (seedViews L) m s).basis a=s.basis a := by
  rw [seedViews_run L hw hn s m (hc _ (by simp [work]))
    (hc _ (by simp [work])) (hc _ (by simp [work]))]
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  refine ⟨rfl,?_,?_⟩
  · simp_all [writeBit,Function.update]
  · intro a h1 h2 h3
    simp only [writeBit,Function.update_of_ne h1,Function.update_of_ne h2,
      Function.update_of_ne h3]

theorem compose_prepare_bits (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (ho : s.basis L.one=N)
    (hr : s.basis L.r0=P) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) :
    let t := run (prepareFold L) m s
    t.phase=s.phase ∧ t.basis L.r0=false ∧ t.basis L.lower=N ∧
    t.basis L.minus=(P && N) ∧ t.basis L.plus=(P && !N) ∧
    ∀a,a≠L.r0 → a≠L.one → a≠L.lower → a≠L.minus → a≠L.plus →
      t.basis a=s.basis a := by
  dsimp only
  rw [prepareFold_run L hn P N s m hp ho hr hl hm hu]
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have lm : L.lower≠L.minus := Ne.symm (by tauto)
  have lp : L.lower≠L.plus := Ne.symm (by tauto)
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · simp only [writeBit,Function.update_self]
  · simp_all [writeBit,Function.update]
  · simp_all [writeBit,Function.update]
  · simp_all [writeBit,Function.update]
  · intro a h1 h2 h3 h4 h5
    simp only [writeBit,Function.update_of_ne h1,Function.update_of_ne h2,
      Function.update_of_ne h3,Function.update_of_ne h4,Function.update_of_ne h5]

theorem compose_prepare_frame (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (ho : s.basis L.one=N)
    (hr : s.basis L.r0=P) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) (a : Wire)
    (ha : a∉rawTarget L) (ha1 : a≠L.lower) (ha2 : a≠L.minus) (ha3 : a≠L.plus) :
    (run (prepareFold L) m s).basis a=s.basis a := by
  have h := compose_prepare_bits L hn P N s m hp ho hr hl hm hu
  exact h.2.2.2.2.2 a (fun e => ha (e ▸ (by simp [rawTarget,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])))
    (fun e => ha (e ▸ (by simp [rawTarget]))) ha1 ha2 ha3

theorem compose_release_frame (L : Layout) (hn : L.wires.Nodup) (P H : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (hh : s.basis L.rmsb=H)
    (hl : s.basis L.lower=(H ^^ P)) (hm : s.basis L.minus=(P && !H))
    (hu : s.basis L.plus=(P ^^ (P && !H))) :
    let t := run (releaseSelectors L) m s
    t.phase=s.phase ∧ t.basis L.lower=false ∧ t.basis L.minus=false ∧
    t.basis L.plus=false ∧ ∀a,a≠L.lower → a≠L.minus → a≠L.plus →
      t.basis a=s.basis a := by
  dsimp only
  rw [releaseSelectors_run L hn P H s m hp hh hl hm hu]
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have lm : L.lower≠L.minus := Ne.symm (by tauto)
  have lp : L.lower≠L.plus := Ne.symm (by tauto)
  have pm : L.plus≠L.minus := Ne.symm (by tauto)
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp_all [writeBit,Function.update]
  · simp only [writeBit,Function.update_self]
  · simp_all [writeBit,Function.update]
  · intro a h1 h2 h3
    simp only [writeBit,Function.update_of_ne h1,Function.update_of_ne h2,
      Function.update_of_ne h3]

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedCoreComposeProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField BalancedFold

def coreProgram (L : Layout) : Program :=
  seedViews L++(rawAdd L++(prepareFold L++(fold L++
    (rotateRight (rawTarget L)++releaseSelectors L))))

def coreClean (L : Layout) : List Wire := [L.cout,L.minus,L.plus,L.lower,L.one]++L.carry

theorem coreClean_sub_work (L : Layout) (q : Wire) (hq : q∈coreClean L) : q∈work L := by
  simp only [coreClean,work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  tauto

theorem program_eq_core (L : Layout) : program L=coreProgram L++
    BalancedCleanup.program L.toLayout++[.CX L.ymsb L.sourceGuard] := by
  simp only [program,coreProgram,List.append_assoc]

/-- Full forward balanced core, for arbitrary incoming phase and every
measurement stream. Its two retained views are exactly the raw parity and
the original source sign. All remaining work is clean. -/
theorem core_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (coreProgram L) m s
    t.phase=s.phase ∧
    regValue L.r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    t.basis L.parity=originalParity (rawSum B X Y) ∧
    t.basis L.sourceGuard=s.basis L.ymsb ∧
    (∀q∈coreClean L,t.basis q=false) ∧
    (∀q,q∉L.r → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q) := by
  let T := rawSum B X Y
  let P := originalParity T
  let N := decide (T<0)
  let H := negative (halfResult T)
  let m₁ := m.drop (measurementCount (rawAdd L))
  let m₂ := m₁.drop (measurementCount (fold L))
  generalize eu : run (seedViews L) m s = u
  generalize ev : run (rawAdd L) m u = v
  generalize ew : run (prepareFold L) m₁ v = w
  generalize ez : run (fold L) m₁ w = z
  generalize ea : run (rotateRight (rawTarget L)) m₂ z = a
  generalize et : run (releaseSelectors L) m₂ a = t
  have ht := rawSum_bounds B X Y hx hy
  have ndR := List.nodup_reverse.mpr (scalarND L hn)
  simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndR
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  rcases ndR with ⟨⟨r0_1,r0_2,r0_3,r0_4,r0_5,r0_6,r0_7,r0_8,r0_9,r0_10⟩,⟨r1_2,r1_3,r1_4,r1_5,r1_6,r1_7,r1_8,r1_9,r1_10⟩,⟨r2_3,r2_4,r2_5,r2_6,r2_7,r2_8,r2_9,r2_10⟩,⟨r3_4,r3_5,r3_6,r3_7,r3_8,r3_9,r3_10⟩,⟨r4_5,r4_6,r4_7,r4_8,r4_9,r4_10⟩,⟨r5_6,r5_7,r5_8,r5_9,r5_10⟩,⟨r6_7,r6_8,r6_9,r6_10⟩,⟨r7_8,r7_9,r7_10⟩,⟨r8_9,r8_10⟩,r9_10⟩
  have su := compose_seed_frame L hw hn s m hc
  rw [eu] at su
  have sv := seed_raw_signed L hw hn B X Y hx hy s m hs hr hyr hc
  simp only [run_append] at sv
  simp only [run_take] at sv
  simp only [show measurementCount (seedViews L)=0 from rfl,List.drop_zero] at sv
  rw [eu,ev] at sv
  have cu := (seed_signed L hw hn X Y s m hr hyr hc).2.2
  rw [eu] at cu
  have rf (q : Wire) (hq : q∉rawTarget L) : v.basis q=u.basis q :=
    by simpa only [ev] using rawAdd_frame L hw hn u m cu q hq
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉rawTarget L := compose_raw_away L hn q hq
  have vp : v.basis L.parity=P :=
    (rf _ (away _ (by simp))).trans (by simpa only [eu] using seed_parity L hw hn B X Y s m hr hyr hc)
  have vo : v.basis L.one=N := word_sign L.r L.one v.basis T sv.2.1
  have vr : v.basis L.r0=P := by
    apply word_parity L.r0 (L.rtail++[L.rmsb,L.one]) v.basis T
    simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using sv.2.1
  have vz (q : Wire) (hq : q∈[L.cout,L.minus,L.plus,L.lower]++L.carry) : v.basis q=false := by
    have cv := compose_clean_views L hn q hq
    have qo : q≠L.one := fun e => cv.1 (e ▸ (by simp [rawTarget]))
    exact (rf q cv.1).trans ((su.2.2 q cv.2.1 qo cv.2.2.1).trans (hc q cv.2.2.2))
  have wp := compose_prepare_bits L hn P N v m₁ vp vo vr
    (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp))
  rw [ew] at wp
  have pf (q : Wire) (hq : q∉rawTarget L) (hl : q≠L.lower)
      (hm : q≠L.minus) (hu : q≠L.plus) : w.basis q=v.basis q :=
    by
      simpa only [ew] using (compose_prepare_frame L hn P N v m₁ vp vo vr
        (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp)) q hq hl hm hu)
  have wpar : w.basis L.parity=P := by
    exact (pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans vp
  have wc : w.basis L.cout=false := by
    exact (pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans (vz _ (by simp))
  have wcarry : regValue L.carry w.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have qne (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
    exact (pf q (away q (by simp [hq])) (qne _ (by simp))
      (qne _ (by simp)) (qne _ (by simp))).trans (vz q (by simp [hq]))
  have prepared := prepare_upper L hw hn T v m₁ sv.2.1 vp
    (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp))
  rw [ew] at prepared
  have zw := fold_correct L hw hn T ht w m₁ wpar
    wp.2.2.2.2.1 wp.2.2.2.1 wc wcarry prepared
  rw [ez] at zw
  have z0 : z.basis L.r0=false :=
    (zw.2.2.2 _ (compose_not_fold_r0 L hn)).trans wp.2.1
  have az := rotate_folded L hw hn T ht z m₂ z0 zw.2.1
  rw [ea] at az
  have af (q : Wire) (hq : q∉rawTarget L) : a.basis q=w.basis q :=
    (az.2.2.2 q hq).trans (zw.2.2.2 q (compose_fold_subset L q hq))
  have ah : a.basis L.rmsb=H :=
    BalancedCleanup.result_msb L.toLayout hw (halfResult T) (halfResult_spec T ht).1 a.basis az.2.1
  have hp : a.basis L.parity=P := (af _ (away _ (by simp))).trans wpar
  have hsign : H=(N ^^ P) := halfResult_sign T ht
  have al : a.basis L.lower=(H ^^ P) := by
    rw [af _ (away _ (by simp)),wp.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have am : a.basis L.minus=(P && !H) := by
    rw [af _ (away _ (by simp)),wp.2.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have au : a.basis L.plus=(P ^^ (P && !H)) := by
    rw [af _ (away _ (by simp)),wp.2.2.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have ta := compose_release_frame L hn P H a m₂ hp ah al am au
  rw [et] at ta
  have tf (q : Wire) (hl : q≠L.lower) (hm : q≠L.minus) (hu : q≠L.plus) :
      t.basis q=a.basis q := ta.2.2.2.2 q hl hm hu
  have tr : regValue L.r t.basis=encodeWord 256 (halfResult T) := by
    apply Eq.trans _ az.2.1
    apply regValue_congr
    intro q hq
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
    exact tf q (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  have tp : t.basis L.parity=P := by
    exact (tf _ (by assumption) (by assumption) (by assumption)).trans hp
  have tg : t.basis L.sourceGuard=s.basis L.ymsb := by
    exact (tf _ (by assumption) (by assumption) (by assumption)).trans
      ((af _ (away _ (by simp))).trans
        ((pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans
          ((rf _ (away _ (by simp))).trans su.2.1)))
  have tz : ∀q∈coreClean L,t.basis q=false := by
    intro q hq
    simp only [coreClean,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|hq
    · exact (tf _ (by assumption) (by assumption) (by assumption)).trans
        ((az.2.2.2 _ (away _ (by simp))).trans zw.2.2.1)
    · exact ta.2.2.1
    · exact ta.2.2.2.1
    · exact ta.2.1
    · exact (tf _ (by assumption) (by assumption) (by assumption)).trans az.2.2.1
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
          q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
      exact (tf q (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((af q (away q (by simp [hq]))).trans
          ((pf q (away q (by simp [hq])) (neq _ (by simp)) (neq _ (by simp))
            (neq _ (by simp))).trans (vz q (by simp [hq]))))
  have frame : ∀q,q∉L.r → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q := by
    intro q hqr hqp hqg
    by_cases hq : q∈coreClean L
    · exact (tz q hq).trans (hc q (coreClean_sub_work L q hq)).symm
    · have qo : q≠L.one := fun e => hq (by simp [coreClean,e])
      have ql : q≠L.lower := fun e => hq (by simp [coreClean,e])
      have qm : q≠L.minus := fun e => hq (by simp [coreClean,e])
      have qu : q≠L.plus := fun e => hq (by simp [coreClean,e])
      have qa : q∉rawTarget L := by simpa only [rawTarget,List.mem_append,
        List.mem_singleton,not_or] using And.intro hqr qo
      exact (tf q ql qm qu).trans ((af q qa).trans ((pf q qa ql qm qu).trans
        ((rf q qa).trans (su.2.2 q hqg qo hqp))))
  have actual : run (coreProgram L) m s=t := by
    simp only [coreProgram,run_append]
    simp only [run_take]
    simp only [
      show measurementCount (seedViews L)=0 from rfl,
      show measurementCount (prepareFold L)=0 from rfl,
      (rotate_counts (rawTarget L)).2.1,List.drop_zero]
    rw [eu,ev,ew,ez,ea,et]
  rw [actual]
  exact ⟨ta.1.trans (az.1.trans (zw.1.trans (wp.1.trans sv.1))),tr,tp,tg,tz,frame⟩

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldCircuitProof.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

/-- Complete actual forward field kernel, including final parity and
source-guard cleanup. Every measurement record restores incoming phase. -/
theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (program L) m s
    t.phase=s.phase ∧
    regValue L.r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    (∀q∈work L,t.basis q=false) ∧
    (∀q,q∉L.r → t.basis q=s.basis q) := by
  let R := halfResult (rawSum B X Y)
  let ms := m.drop (measurementCount (coreProgram L))
  generalize ec : run (coreProgram L) m s=c
  have core := core_correct L hw hn B X Y hx hy s m hs hr hyr hc
  rw [ec] at core
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have sgp : L.sourceGuard≠L.parity := by tauto
  have ysg : L.ymsb≠L.sourceGuard := Ne.symm (by tauto)
  have ypa : L.ymsb≠L.parity := Ne.symm (by tauto)
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have rcenter : Centered R := (halfResult_spec _ (rawSum_bounds B X Y hx hy)).1
  have qflag (q f : Wire) (hq : q∈L.y)
      (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : q≠f := by
    intro e
    have mem : f∈L.y := e ▸ hq
    exact flagAway L hn f hf (by simp [mem])
  have yr (q : Wire) (hq : q∈L.y) : q∉L.r := by
    have a := compose_raw_away L hn q (by simp [hq])
    exact fun h => a (by simp [rawTarget,h])
  have cY : regValue L.y c.basis=encodeWord 256 Y := by
    have same := regValue_congr L.y c.basis s.basis
      (fun q hq => core.2.2.2.2.2 q (yr q hq) (qflag q L.parity hq (by simp))
        (qflag q L.sourceGuard hq (by simp)))
    exact same.trans (word_encoding L.y 256 (BalancedCleanup.widths L.toLayout hw).2.2.1 s.basis Y hyr)
  have signAway : L.sign∉L.r := by
    exact fun h => flagAway L hn L.sign (by simp) (by simp [h])
  have cS : c.basis L.sign=B :=
    (core.2.2.2.2.2 L.sign signAway (Ne.symm (by tauto)) (Ne.symm (by tauto))).trans hs
  have parity : originalParity (rawSum B X Y)=decide (q < |2*R-signedY B Y|) := by
    apply decide_eq_decide.mpr
    exact halfResult_parity_interval B X Y hx hy
  have cl := BalancedCleanup.correct L.toLayout hw n0 R Y B rcenter hy c ms
    core.2.1 cY cS (core.2.2.2.2.1 _ (by simp [coreClean]))
    (core.2.2.2.2.1 _ (by simp [coreClean]))
    (fun q hq => core.2.2.2.2.1 q (by simp [coreClean,hq]))
    (core.2.2.1.trans parity)
  let d : State := ⟨c.phase,writeBit c.basis L.parity false⟩
  have dp : d.basis L.sourceGuard=s.basis L.ymsb := by
    exact (show d.basis L.sourceGuard=c.basis L.sourceGuard from by simp [d,writeBit,sgp]).trans core.2.2.2.1
  have dy : d.basis L.ymsb=s.basis L.ymsb := by
    have hy0 : L.ymsb∈L.y := by simp [BalancedCleanup.Layout.y]
    exact (show d.basis L.ymsb=c.basis L.ymsb from by simp [d,writeBit,ypa]).trans
      (core.2.2.2.2.2 L.ymsb (yr _ hy0) ypa ysg)
  let t : State := ⟨c.phase,writeBit d.basis L.sourceGuard false⟩
  have actual : run (program L) m s=t := by
    rw [program_eq_core,List.append_assoc,run_append,run_take,ec]
    change run (BalancedCleanup.program L.toLayout++[.CX L.ymsb L.sourceGuard]) ms c=t
    rw [run_append,run_take,cl]
    change ⟨c.phase,writeBit d.basis L.sourceGuard
      (d.basis L.sourceGuard ^^ d.basis L.ymsb)⟩=t
    rw [dp,dy,Bool.xor_self]
  have frame (q : Wire) (hq : q∉L.r) : t.basis q=s.basis q := by
    by_cases hp : q=L.parity
    · subst q
      simp only [t,d,writeBit,Function.update_of_ne (Ne.symm sgp),Function.update_self]
      exact (hc _ (by simp [work])).symm
    by_cases hg : q=L.sourceGuard
    · subst q
      simp only [t,writeBit,Function.update_self]
      exact (hc _ (by simp [work])).symm
    simp only [t,d,writeBit,Function.update_of_ne hg,Function.update_of_ne hp]
    exact core.2.2.2.2.2 q hq hp hg
  rw [actual]
  refine ⟨core.1,?_,?_,frame⟩
  · exact (regValue_congr L.r t.basis c.basis (by
      intro q hq
      have np : q≠L.parity := fun e => flagAway L hn L.parity (by simp) (by simp [e ▸ hq])
      have ng : q≠L.sourceGuard := fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ hq])
      simp only [t,d,writeBit,Function.update_of_ne ng,Function.update_of_ne np])).trans core.2.1
  · intro q hq
    have outside : q∉L.r := by
      intro qr
      have h := List.nodup_iff_count.mp hn q
      have a := List.count_pos_iff.mpr hq
      have b := List.count_pos_iff.mpr qr
      simp only [Layout.wires,BalancedCleanup.Layout.wires,work,
        BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
        List.count_append,List.count_cons,List.count_nil] at h a b
      omega
    exact (frame q outside).trans (hc q hq)

end ECDSAAdd.Arithmetic.BalancedCircuit
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldConvertMath.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedConvert
open BalancedField BalancedCircuit BalancedFold Secp256k1

def wordModulus : Nat := 2^256
def wordHalf : Nat := 2^255
def threshold (x : Fp) : Bool := decide (q<(x.val : Int))
theorem convert_constants : wordModulus=2*wordHalf ∧ sparseF=2*bias+1 ∧
    0<bias ∧ bias<wordHalf ∧ p+sparseF=wordModulus ∧ 0≤q ∧
    q=(wordHalf : Int)-(bias : Int)-1 ∧ p≤wordModulus ∧ q<(wordModulus : Int) := by decide

theorem generic_center (H K F P x : Nat) (hm : P+F=2*H)
    (hf : F=2*K+1) (hx : x<P) :
    (if H-K-1<x then x+F else x)<2*H ∧
    (H≤(if H-K-1<x then x+F else x) ↔ H-K-1<x) := by split_ifs <;> omega

theorem generic_center_range (X P Q M : Int) (hx : 0≤X ∧ X<P)
    (hp : P≤M) :
    -M≤(if X≤Q then X else X-P) ∧ (if X≤Q then X else X-P)<M := by
  split_ifs <;> omega

theorem generic_center_encoding (X P Q M F : Int) (hx : 0≤X ∧ X<P)
    (hm : P+F=M) :
    (if X≤Q then X else X-P)+(if (if X≤Q then X else X-P)<0 then M else 0)=
      (if Q<X then X+F else X) := by
  by_cases hc : X≤Q
  · simp only [if_pos hc,if_neg (show ¬Q<X by omega),if_neg (show ¬X<0 by omega),add_zero]
  · simp only [if_neg hc,if_pos (show Q<X by omega),if_pos (show X-P<0 by omega)]
    omega

theorem canonical_bound (x : Fp) : x.val<p := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact ZMod.val_lt x

theorem centerWord_value (x : Fp) : centerWord x=if threshold x then x.val+sparseF else x.val := by
  rcases convert_constants with ⟨hm,hf,hk,hK,hp,hq,hQ,hPM,hQM⟩
  have hx : 0≤(x.val : Int) ∧ (x.val : Int)<(p : Int) :=
    ⟨Nat.cast_nonneg _,by exact_mod_cast canonical_bound x⟩
  have hp' : (p : Int)≤(wordModulus : Int) := by exact_mod_cast hPM
  have hm' : (p : Int)+(sparseF : Int)=(wordModulus : Int) := by exact_mod_cast hp
  have hr := generic_center_range (x.val : Int) p q wordModulus hx hp'
  have he := encode_shift 256 (centerFp x) hr
  have hv := generic_center_encoding (x.val : Int) p q wordModulus sparseF hx hm'
  change (centerWord x : Int)=_ at he
  rw [show centerFp x=(if (x.val : Int)≤q then (x.val : Int) else (x.val : Int)-(p : Int)) from rfl] at he
  have eq : (centerWord x : Int)=(if threshold x then ((x.val+sparseF : Nat) : Int) else (x.val : Int)) := by
    simpa only [threshold,Bool.cond_eq_ite,decide_eq_true_eq,Nat.cast_add] using he.trans hv
  exact_mod_cast eq

theorem center_threshold (x : Fp) : wordHalf≤centerWord x ↔ threshold x=true := by
  rcases convert_constants with ⟨hm,hf,hk,hK,hp,hq,hQ,hPM,hQM⟩
  have g := generic_center wordHalf bias sparseF p x.val (hp.trans hm) hf (canonical_bound x)
  have hi : ((wordHalf-bias-1 : Nat) : Int)=q := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hK)),
      Nat.cast_sub (Nat.le_of_lt hK),Nat.cast_one,hQ]
  rw [centerWord_value]
  simpa only [threshold,Bool.cond_eq_ite,decide_eq_true_eq,←hi,Nat.cast_lt] using g.2

theorem correction_sources (L : Layout) (w : Wire) (hw : w∈mappedWires (correction L)) : w=L.flag := by
  obtain ⟨b,hb,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  cases hf : sparseF.testBit i
  · simp [hf] at hw
  · simpa [hf] using hw
def scratch (L : Layout) : List Wire := [L.cin,L.one]++L.carry
 def work (L : Layout) : List Wire := L.flag::scratch L

theorem word_length (L : Layout) (hw : L.Widths) : L.word.length=256 := by simp [Layout.word,hw.1]

theorem layout_literal (L : Layout) (hn : L.wires.Nodup) : (L.one::L.cin::(L.word++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,Layout.word,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem layout_add (L : Layout) (hn : L.wires.Nodup) : (L.cin::(L.word++L.carry)).Nodup :=
  (List.nodup_cons.mp (layout_literal L hn)).2

theorem layout_away (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.cin,L.one,L.flag]++L.carry) : q∉L.word := by
  have nd : (L.word++([L.cin,L.one,L.flag]++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have h := List.nodup_iff_count.mp hn a
    simp only [Layout.wires,Layout.word,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  exact fun h => List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h hq

theorem flag_away (L : Layout) (hn : L.wires.Nodup) : L.flag∉L.cin::(L.word++L.carry) := by
  have nd : (L.flag::L.cin::(L.word++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have h := List.nodup_iff_count.mp hn a
    simp only [Layout.wires,Layout.word,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  exact (List.nodup_cons.mp nd).1

theorem scratch_away (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈scratch L) :
    q∉L.word ∧ q≠L.flag := by
  have a := layout_away L hn q (by simp only [scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  have nd : (L.flag::scratch L).Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have h := List.nodup_iff_count.mp hn a
    simp only [Layout.wires,scratch,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  exact ⟨a,fun e => (List.nodup_cons.mp nd).1 (e ▸ hq)⟩

theorem word_msb (L : Layout) (hw : L.Widths) (s : BasisState) (v : Nat) (B : Bool)
    (hv : regValue L.word s=v) (hb : wordHalf≤v ↔ B=true) : s L.msb=B := by
  have high := regValue_highBit L.low L.msb s
  rw [hw.1] at high
  change s L.msb=true ↔ wordHalf≤regValue L.word s at high
  rw [hv] at high
  cases hs : s L.msb <;> cases B <;> simp_all

end ECDSAAdd.Arithmetic.BalancedConvert
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldConvertProof.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedConvert
open BalancedField BalancedCircuit Secp256k1
attribute [local irreducible] run literalConstAdd mappedAdd mappedSub

theorem work_of_frame (L : Layout) (hn : L.wires.Nodup) (s t : State)
    (hc : ∀q∈work L,s.basis q=false) (hf : ∀q,q∉L.word → t.basis q=s.basis q) :
    ∀q∈work L,t.basis q=false := by
  intro q hq
  have ha : q∉L.word := layout_away L hn q (by
    simp only [work,scratch,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢; tauto)
  exact (hf q ha).trans (hc q hq)

end ECDSAAdd.Arithmetic.BalancedConvert
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldInverseProgram.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit

/-- Reuse the forward, independently measured XOR oracle to reconstruct
parity. No measurement instruction is reversed. -/
def recoverParity (L : Layout) : Program := BalancedCleanup.program L.toLayout

/-- Dual of the former minus-selector measurement: its quadratic predicate
is A XOR (A AND sign(R)). The remaining operations undo Clifford views. -/
def recoverSelectors (L : Layout) : Program :=
  [.CX L.parity L.minus,.CCX L.parity L.rmsb L.minus,
    .CX L.minus L.plus,.CX L.parity L.plus,
    .CX L.rmsb L.lower,.CX L.parity L.lower]

/-- Arithmetic inverse of the mapped addition, including the original
quantum carry-in. This is a fresh measured subtraction, not reversed MX. -/
def undoFold (L : Layout) : Program :=
  [.CX L.minus L.cout]++mappedSub (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity

/-- The prepared AND has known pre-target zero, so its inverse is one
measurement with the exact CZ correction, rather than a reversed CCX. -/
def undoPreparation (L : Layout) : Program :=
  [.CX L.parity L.r0,.CX L.parity L.one,
    .CX L.minus L.plus,.CX L.parity L.plus,
    .measureX L.minus [] [.CZ L.parity L.lower],.CX L.one L.lower]

def rawSubtract (L : Layout) : Program :=
  signComplement L.sign (rawSource L)++
  subInPlace (rawSource L) (rawTarget L) L.carry L.sign++
  signComplement L.sign (rawSource L)

/-- Actual independently emitted inverse candidate. Only the seed's CX
stream is reversed; every arithmetic and cleanup measurement runs forward. -/
def program (L : Layout) : Program :=
  [.CX L.ymsb L.sourceGuard]++recoverParity L++recoverSelectors L++
  rotateLeft (rawTarget L)++undoFold L++undoPreparation L++rawSubtract L++(seedViews L).reverse

/-- Honest counts of this DSL emission. The prototype's1276 estimate is
not imposed on the current independently measured primitive recipes. -/
theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=1277 ∧ measurementCount (program L)=1277 := by
  have w := BalancedCircuit.widths L hw
  have ra := subInPlace_counts (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have fa := mappedSub_counts (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
    (by omega) (by omega)
  have cm := signComplement_counts L.sign (rawSource L)
  have ro := rotate_counts (rawTarget L)
  have cl := BalancedCleanup.counts L.toLayout hw
  simp only [program,recoverParity,recoverSelectors,undoFold,undoPreparation,rawSubtract,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    ra.1,ra.2,fa.1,fa.2,cm.1,cm.2,ro.2.2.1,ro.2.2.2,cl.1,cl.2]
  simp only [w.2.1,w.2.2.1,seedViews]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldInverseArithmetic.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedField Secp256k1

private theorem complement_sub_cin (X Y N C : Nat) (hN : 0<N)
    (hX : X<N) (hY : Y<N) (hC : C≤1) :
    N-1-((X+(N-1-Y)+C)%N)=(Y+N-X-C)%N := by
  by_cases h : X+C≤Y
  · rw [Nat.mod_eq_of_lt (show X+(N-1-Y)+C<N by omega),
      show Y+N-X-C=(Y-X-C)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X+(N-1-Y)+C=(X+C-1-Y)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X+C-1-Y<N by omega),Nat.mod_eq_of_lt (show Y+N-X-C<N by omega)]
    omega

/-- A measured-adder contract lifts through two fresh, measurement-free
complements. The carry-in may be either quantum basis value. -/
theorem complement_sandwich (ys : List Wire) (hn : ys.Nodup) (body : Program)
    (X C : Nat) (s : State) (m : List Bool) (hX : X<2^ys.length) (hC : C≤1)
    (hbody : let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
      (run body m u).phase=s.phase ∧
      (∀q,q∉ys → (run body m u).basis q=u.basis q) ∧
      regValue ys (run body m u).basis=(X+(2^ys.length-1-regValue ys s.basis)+C)%2^ys.length) :
    (run (notRegister ys++body++notRegister ys) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (notRegister ys++body++notRegister ys) m s).basis q=s.basis q) ∧
    regValue ys (run (notRegister ys++body++notRegister ys) m s).basis=
      (regValue ys s.basis+2^ys.length-X-C)%2^ys.length := by
  let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  let t := run body m u
  have first (ms : List Bool) : run (notRegister ys) ms s=u := notRegister_correct ys hn s ms
  have value : regValue ys (fun q => if q∈ys then !t.basis q else t.basis q)=
      2^ys.length-1-regValue ys t.basis := by
    rw [regValue_congr ys _ (fun q => !t.basis q) (by intro q hq; simp [hq]),regValue_complement]
  simp only [List.append_assoc,run_append,run_take,(notRegister_counts ys).2,List.drop_zero,first]
  rw [notRegister_correct ys hn]
  refine ⟨hbody.1,?_,?_⟩
  · intro q hq; simp only [hq,if_false]; exact (hbody.2.1 q hq).trans (by simp [hq])
  · rw [value,hbody.2.2]
    exact complement_sub_cin X (regValue ys s.basis) (2^ys.length) C
      (Nat.two_pow_pos _) hX (regValue_lt ys s.basis) hC

/-- Actual mapped subtraction, now proved for arbitrary carry-in. All
immutable selectors, cin and every carry restore, with all records allowed. -/
theorem mappedSub_any_correct (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (mappedSub bits ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (mappedSub bits ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (mappedSub bits ys carry cin) m s).basis=
      (regValue ys s.basis+2^ys.length-mappedValue bits s.basis-(s.basis cin).toNat)%2^ys.length := by
  have nd := List.nodup_append'.mp (List.nodup_cons.mp hn).2
  let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have awayCin : cin∉ys := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have clean : ∀q∈carry,u.basis q=false := by
    intro q hq; have away : q∉ys := fun h => List.disjoint_left.mp nd.2.2 h hq
    simp only [show u.basis q=s.basis q from by simp [u,away],hclean q hq]
  have source : mappedValue bits u.basis=mappedValue bits s.basis := by
    apply mappedValue_congr
    intro q hq; simp [u,show q∉ys from fun h => hs q hq (by simp [h])]
  have input : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys _ (fun q => !s.basis q) (by intro q hq; simp [u,hq]),regValue_complement]
  have add := mappedAdd_correct bits ys carry cin hn hs hl hc u m clean
  apply complement_sandwich ys nd.1 (mappedAdd bits ys carry cin)
    (mappedValue bits s.basis) (s.basis cin).toNat s m
    (by simpa only [hl] using mappedValue_lt bits s.basis)
    (by cases s.basis cin <;> decide)
  simpa only [source,input,show u.basis cin=s.basis cin from by simp [u,awayCin]] using add

/-- The raw subtraction likewise supports its original sign carry-in,
without changing any source/control/workspace wire outside the target. -/
theorem subInPlace_any_correct (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::(xs++ys++carry)).Nodup) (hl : xs.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) :
    (run (subInPlace xs ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (subInPlace xs ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (subInPlace xs ys carry cin) m s).basis=
      (regValue ys s.basis+2^ys.length-regValue xs s.basis-(s.basis cin).toNat)%2^ys.length := by
  have words := List.nodup_cons.mp hn
  have split := List.nodup_append'.mp (show (xs++(ys++carry)).Nodup from by simpa only [List.append_assoc] using words.2)
  have nd := List.nodup_append'.mp split.2.1
  let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have ci : cin∉ys := fun h => words.1 (by simp [h])
  have clean : ∀q∈carry,u.basis q=false := by
    intro q hq; have away : q∉ys := fun h => List.disjoint_left.mp nd.2.2 h hq
    simp only [show u.basis q=s.basis q from by simp [u,away],hclean q hq]
  have source : regValue xs u.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [u,show q∉ys from fun h => List.disjoint_left.mp split.2.2 hq (by simp [h])])
  have input : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys _ (fun q => !s.basis q) (by intro q hq; simp [u,hq]),regValue_complement]
  have add := addInPlace_correct xs ys carry cin hn hl hc u m clean
  apply complement_sandwich ys nd.1 (addInPlace xs ys carry cin)
    (regValue xs s.basis) (s.basis cin).toNat s m
    (by simpa only [hl] using regValue_lt xs s.basis) (by cases s.basis cin <;> decide)
  simpa only [source,input,show u.basis cin=s.basis cin from by simp [u,ci]] using add

/-- Exact inverse field value; validity holds on the entire balanced domain. -/
def result (B : Bool) (R Y : Int) : Int := centerFp ((2*R-signedY B Y : Int) : Fp)

theorem result_bounds (B : Bool) (R Y : Int) : Centered (result B R Y) := centerFp_bounds _

theorem result_half (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    halfResult (rawSum B (result B R Y) Y)=R := by
  have hx := result_bounds B R Y
  have half := halfResult_center (rawSum B (result B R Y) Y) (rawSum_bounds B _ Y hx hy)
  have cast : (result B R Y : Fp)=((2*R-signedY B Y : Int) : Fp) := centerFp_cast _
  have eq : ((rawSum B (result B R Y) Y : Int) : Fp)/2=(R : Fp) := by
    simp only [rawSum,Int.cast_add,cast,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
    have two : (2 : Fp)≠0 := by decide
    field_simp [two]
    ring
  rw [half,eq,centerFp_of_center R hr]

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldInverseParity.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000
namespace ECDSAAdd.Arithmetic.BalancedCleanupXor
open BalancedCleanup BalancedField

 theorem xor_states (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool) (s1 s2 s3 s4 s5 s6 s7 : State)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false)
    (hs1 : run (prepareSign L) m1 s=s1) (hs2 : run (normalize L) m2 s1=s2)
    (hs3 : run (prepareCompare L) m3 s2=s3)
    (hs4 : run (compareLt none L.y L.r L.carry L.one L.parity) m4 s3=s4)
    (hs5 : run (prepareCompare L).reverse m5 s4=s5)
    (hs6 : run (unnormalize L) m6 s5=s6) (hs7 : run (prepareSign L).reverse m7 s6=s7) :
    Except L.parity s7 s ∧ s7.basis L.parity=(s.basis L.parity ^^ decide (q < |2*R-signedY B Y|)) := by
  have w := widths L hw
  have nd := L.normND hn
  have flags := L.flagsND hn
  have pa := clifford_parity_away L hw hn
  have ar : L.parity∉L.r := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have ay : L.parity∉L.y := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have al : L.parity≠L.lower := by have hh := (List.nodup_cons.mp flags).1; simp at hh; tauto
  have oa : L.one∉L.r := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have ol : L.one≠L.lower := by have hh := List.nodup_iff_count.mp flags L.one; simp [List.count_cons] at hh; intro e; simp [e] at hh; omega
  have sy : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have sl : L.sign≠L.lower := by have hh := List.nodup_iff_count.mp flags L.sign; simp [List.count_cons] at hh; intro e; simp [←e] at hh; omega
  have ca (q : Wire) (hq : q∈L.carry) : q∉L.r ∧ q≠L.lower := by
    have d := List.nodup_append'.mp (L.dataND hn)
    exact ⟨fun h => List.disjoint_left.mp d.2.2 h (by simp [hq]),
      fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])⟩
  have v1 := prepareSign_value L hw hn R hr s m1 hR hz
  rw [hs1] at v1
  have one1 : s1.basis L.one=false := (v1.2.2 _ oa ol).trans ho
  have clean1 : ∀q∈L.carry,s1.basis q=false := fun q hq => (v1.2.2 q (ca q hq).1 (ca q hq).2).trans (hc q hq)
  have Y1 : regValue L.y s1.basis=encodeWord 256 Y := by
    have d := List.nodup_append'.mp (L.dataND hn)
    exact (regValue_congr _ _ _ (fun q hq => v1.2.2 q
      (fun r => List.disjoint_left.mp d.2.2 r (by simp [hq]))
      (fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])))).trans hY
  have rm0 : s1.basis L.rmsb=false := by
    have hi := regValue_highBit L.low L.rmsb s1.basis
    rw [w.1] at hi
    change s1.basis L.rmsb=true ↔ 2^255≤regValue L.r s1.basis at hi
    rw [v1.1] at hi
    have b := magnitude_bounds R hr; have p := constants
    have cast := Int.toNat_of_nonneg b.1
    cases e : s1.basis L.rmsb
    · rfl
    · simp [e] at hi
      omega
  have low1 : regValue L.low s1.basis=(magnitude R).toNat := by
    have h := v1.1; rw [Layout.r,regValue_append] at h; simpa [regValue,rm0] using h
  have v2 := normalize_value L hw hn R hr s1 m2 low1 v1.2.1 one1 clean1
  rw [hs2] at v2
  have rmAway : L.rmsb∉L.low := by have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).1; exact fun h => List.disjoint_left.mp d.2.2 h (by simp)
  have R2 : regValue L.r s2.basis=encodeWord 255 (normalizedR R) := by
    rw [Layout.r,regValue_append,v2.2.1]; simp [regValue,v2.2.2 _ rmAway,rm0]
  have Y2 : regValue L.y s2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => v2.2.2 q (by
      intro hl; exact List.disjoint_left.mp (List.nodup_append'.mp (L.dataND hn)).2.2
        (show q∈L.r from by simp [Layout.r,hl])
        (show q∈L.y++L.carry from by simp [hq])))).trans Y1
  have S2 : s2.basis L.sign=B := (v2.2.2 _ (fun h => sy (by simp [Layout.r,h]))).trans ((v1.2.2 _ sy sl).trans hS)
  have L2 : s2.basis L.lower=negative R := (v2.2.2 _ (fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h]))).trans v1.2.1
  have v3 := prepareCompare_value L hw hn R Y B hr hy s2 m3 R2 Y2 S2 L2
  rw [hs3] at v3
  have frame2 (q : Wire) (hq : q∉L.r) : s2.basis q=s1.basis q := v2.2.2 q (fun h => hq (by simp [Layout.r,h]))
  have one3 : s3.basis L.one=false := (v3.2.2 _ oa (fun h => L.flagAway hn L.one (by simp) (by simp [h]))).trans ((frame2 _ oa).trans one1)
  have clean3 : ∀q∈L.carry,s3.basis q=false := by
    intro q hq; have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).2.1
    exact (v3.2.2 q (ca q hq).1 (fun hyq => List.disjoint_left.mp d.2.2 hyq hq)).trans ((frame2 q (ca q hq).1).trans (clean1 q hq))
  have cmp := compareLt_correct none L.y L.r L.carry L.one L.parity (L.compareND hn)
    (by simp) (by omega) (by unfold Layout.Widths at hw; omega) s3 m4 one3 clean3
  rw [hs4] at cmp
  have pred : decide (regValue L.y s3.basis<regValue L.r s3.basis)=decide (q < |2*R-signedY B Y|) := by
    apply decide_eq_decide.mpr
    have interval := cleanup_interval_identity B R Y hr hy
    omega
  have A3 : s3.basis L.parity=s.basis L.parity := (v3.2.2 _ ar ay).trans ((frame2 _ ar).trans (v1.2.2 _ ar al))
  have A4 : s4.basis L.parity=(s.basis L.parity ^^ decide (q < |2*R-signedY B Y|)) := by
    rw [cmp.2.2,A3,pred]
    simp [controlValue]
  have ex5 := inverse_except (prepareCompare L) (prepareCompare_proper L hn) L.parity pa.2 s2 s4 m3 m5 (by rw [hs3]; exact ⟨cmp.1,cmp.2.1⟩)
  rw [hs5] at ex5
  have one5 : s5.basis L.one=false := (ex5.2 _ (by intro e; have hh := (List.nodup_cons.mp flags).1; exact hh (by simp [←e]))).trans ((frame2 _ oa).trans one1)
  have clean5 : ∀q∈L.carry,s5.basis q=false := by
    intro q hq; exact (ex5.2 q (fun e => L.flagAway hn L.parity (by simp) (by simp [←e,hq]))).trans ((frame2 q (ca q hq).1).trans (clean1 q hq))
  have un := unnormalize_correct L hw hn s5 m6 one5 clean5
  rw [hs6] at un
  have raw := literalConstAdd_correct L.low (L.carry.take 254) L.lower L.one negativeLiteral nd (by omega) s1 m2 one1 (fun q hq => clean1 q (List.mem_of_mem_take hq))
  have read2 : regValue L.low s2.basis=
      (regValue L.low s1.basis+negativeLiteral+(s1.basis L.lower).toNat)%2^L.low.length := by
    rw [←hs2]
    exact raw.2.2
  have low5 : regValue L.low s5.basis=regValue L.low s2.basis := regValue_congr _ _ _ (fun q hq => ex5.2 q (fun e => ar (by simp [Layout.r,←e,hq])))
  have lower5 : s5.basis L.lower=s1.basis L.lower := (ex5.2 _ (Ne.symm al)).trans (v2.2.2 _ (fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])))
  have low6 : regValue L.low s6.basis=regValue L.low s1.basis := by
    rw [un.2.1,low5,read2,lower5,w.1]
    have fit := regValue_lt L.low s1.basis; rw [w.1] at fit
    have sum := literals_sum
    cases b : s1.basis L.lower <;> simp only [Bool.not_false,Bool.not_true,Bool.toNat_false,Bool.toNat_true] <;> omega
  have ex6 : Except L.parity s6 s1 := by
    refine ⟨un.1.trans (ex5.1.trans v2.1),?_⟩
    intro q hq
    by_cases hl : q∈L.low
    · exact (regValue_eq_iff L.low _ _).mp low6 q hl
    · exact (un.2.2 q hl).trans ((ex5.2 q hq).trans (v2.2.2 q hl))
  have ex7 := inverse_except (prepareSign L) (prepareSign_proper L hn) L.parity pa.1 s s6 m1 m7 (by rw [hs1]; exact ex6)
  rw [hs7] at ex7
  have keep5 := run_preserves_outside (prepareCompare L).reverse m5 s4 L.parity (by rw [wires_reverse]; exact pa.2)
  have keep7 := run_preserves_outside (prepareSign L).reverse m7 s6 L.parity (by rw [wires_reverse]; exact pa.1)
  rw [hs5] at keep5; rw [hs7] at keep7
  exact ⟨ex7,keep7.trans ((un.2.2 _ (fun h => ar (by simp [Layout.r,h]))).trans (keep5.trans A4))⟩

 theorem xor_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false)
    :
    run (program L) m s=⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|))⟩ := by
  let P : State → State → Prop := fun i o =>
    regValue L.r i.basis=encodeWord 256 R → regValue L.y i.basis=encodeWord 256 Y →
    i.basis L.sign=B → i.basis L.lower=false → i.basis L.one=false →
    (∀q∈L.carry,i.basis q=false) →
    Except L.parity o i ∧ o.basis L.parity=(i.basis L.parity ^^ decide (q < |2*R-signedY B Y|))
  have h := skywalkRunSeven (prepareSign L) (normalize L) (prepareCompare L)
    (compareLt none L.y L.r L.carry L.one L.parity) (prepareCompare L).reverse
    (unnormalize L) (prepareSign L).reverse P
    (by intro i s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 e1 e2 e3 e4 e5 e6 e7 r y b z o c
        exact xor_states L hw hn R Y B hr hy i m1 m2 m3 m4 m5 m6 m7 s1 s2 s3 s4 s5 s6 s7 r y b z o c e1 e2 e3 e4 e5 e6 e7) s m
  have result : Except L.parity (run (program L) m s) s ∧ (run (program L) m s).basis L.parity=(s.basis L.parity ^^ decide (q < |2*R-signedY B Y|)) :=
    by simpa only [program] using h hR hY hS hz ho hc
  apply State.extensionality
  · exact result.1.1
  · funext q
    by_cases e : q=L.parity
    · subst q; simp [writeBit,result.2]
    · simp [writeBit,e,result.1.2 q e]

end ECDSAAdd.Arithmetic.BalancedCleanupXor


namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField

/-- Executable parity reconstruction from clean A, with the full caller
phase/data/control/workspace frame for every measurement record. -/
theorem recoverParity_correct (L : Layout) (hw : L.Widths)
    (hn : L.toLayout.wires.Nodup) (R Y : Int) (B : Bool)
    (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.toLayout.r s.basis=encodeWord 256 R)
    (hY : regValue L.toLayout.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (ha : s.basis L.parity=false) :
    run (recoverParity L) m s=
      ⟨s.phase,writeBit s.basis L.parity (decide (q < |2*R-signedY B Y|))⟩ := by
  have hh := BalancedCleanupXor.xor_correct L.toLayout hw hn R Y B hr hy s m hR hY hS hz ho hc
  simpa only [recoverParity,ha,Bool.false_xor] using hh

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedFieldSupport.lean
noncomputable section

set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic

namespace BalancedCleanup

theorem support (L : Layout) (hw : L.Widths) :
    wires (program L) ⊆ L.wires.toFinset := by
  have w := widths L hw
  have ns := literalConstAdd_wires L.low (L.carry.take 254) L.lower L.one negativeLiteral
  have ps := literalConstAdd_wires L.low (L.carry.take 254) L.lower L.one positiveLiteral
  have cmp := (compareLt_wires none L.y L.r L.carry L.one L.parity
    (by omega) (by unfold Layout.Widths at hw; omega)).1
  have rr := (rotate_wires L.r).2
  have cr := signComplement_wires_subset L.lower L.r
  have cy := signComplement_wires_subset L.sign L.y
  have cl := signComplement_wires_subset L.lower L.y
  have sign : wires (prepareSign L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [prepareSign,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq
    · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,Layout.wires,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := cr hq
      simp only [Layout.wires,Layout.r,Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
  have view : wires (prepareCompare L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [prepareCompare,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq|hq|hq
    · rw [rr,if_neg (by omega)] at hq
      simp only [Layout.wires,Layout.r,Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · simp only [wires,Instr.wires,Layout.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := cy hq; simp only [Layout.wires,Layout.y,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · have h := cl hq; simp only [Layout.wires,Layout.y,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · simp only [wires,Instr.wires,Layout.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  have norm : wires (normalize L) ⊆ L.wires.toFinset := by
    intro q hq
    have h := ns hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    have take : q∈L.carry.take 254 → q∈L.carry := List.mem_of_mem_take
    simp only [Layout.wires,Layout.low,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
  have un : wires (unnormalize L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [unnormalize,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq
    · simp only [wires,Instr.wires,Layout.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := ps hq
      have take : q∈L.carry.take 254 → q∈L.carry := List.mem_of_mem_take
      simp only [Layout.wires,Layout.low,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · simp only [wires,Instr.wires,Layout.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  intro q hq
  simp only [program,wires_append,wires_reverse,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq
  · exact sign hq
  · exact norm hq
  · exact view hq
  · rw [cmp] at hq
    simp only [Layout.wires,Layout.r,Layout.low,Layout.y,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,Option.toList_none,List.nil_append] at hq ⊢; tauto
  · exact view hq
  · exact un hq
  · exact sign hq

end BalancedCleanup

namespace BalancedCircuit

theorem foldSources (L : Layout) (q : Wire) (hq : q∈mappedWires (foldBits L)) :
    q=L.plus ∨ q=L.minus := by
  obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp hq
  rw [foldBits] at hb
  rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨i,hi,he⟩ := List.mem_map.mp hb
    subst b
    cases ht : sparseF.testBit (i+1)
    · right; simpa [ht] using hm
    · left; simpa [ht] using hm
  · have he : b={wire:=none,flip:=false} := by simpa using hb
    subst b
    simp at hm

theorem support (L : Layout) (hw : L.Widths) :
    wires (program L) ⊆ L.wires.toFinset := by
  have w := widths L hw
  have cleanup := BalancedCleanup.support L.toLayout hw
  have add := addInPlace_wires (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have comp := signComplement_wires_subset L.sign (rawSource L)
  have mapped := mappedAdd_wires_subset (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
  have rot := (rotate_wires (rawTarget L)).1
  have member (q : Wire) : q∈L.wires.toFinset ↔
      q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry := by
    simp [Layout.wires,BalancedCleanup.Layout.wires,or_assoc]
  have raw : wires (rawAdd L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [rawAdd,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq
    · have h := comp hq
      simp only [member,rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · rw [add] at hq
      simp only [member,rawSource,rawTarget,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := comp hq
      simp only [member,rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
  have foldSupport : wires (fold L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [fold,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · have h := mapped hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
        foldTarget,or_false,or_assoc] at h
      rcases h with h|h|h|h|h|h|h
      · rcases foldSources L q h with e|e
        all_goals exact (member q).mpr (Or.inl (by simp [e]))
      · exact (member q).mpr (Or.inr (Or.inl h))
      · exact (member q).mpr (Or.inl (by simp [h]))
      · exact (member q).mpr (Or.inl (by simp [h]))
      · exact (member q).mpr (Or.inl (by simp [h]))
      · exact (member q).mpr (Or.inr (Or.inr (Or.inr h)))
      · exact (member q).mpr (Or.inl (by simp [h]))
    · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  have seedSmall : wires (seedViews L) ⊆
      [L.ymsb,L.sourceGuard,L.rmsb,L.one,L.ylow.getD 0 0,L.parity,L.r0].toFinset := by
    intro q hq
    simp only [seedViews,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,List.mem_cons,List.not_mem_nil] at hq ⊢
    tauto
  have seed : wires (seedViews L) ⊆ L.wires.toFinset := by
    intro q hq
    have low : L.ylow.getD 0 0∈L.ylow := by
      cases hy : L.ylow with
      | nil => have hh := hw.2.1; simp [hy] at hh
      | cons a as => simp [hy]
    have small := seedSmall hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil] at small
    rcases small with e|e|e|e|e|e|e|e
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inr (Or.inr (Or.inl (by simpa [e] using low))))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact False.elim e
  intro q hq
  simp only [program,wires_append,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq|hq
  · exact seed hq
  · exact raw hq
  · simp only [prepareFold,member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · exact foldSupport hq
  · rw [rot,if_neg (by omega)] at hq
    simp only [member,rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · simp only [releaseSelectors,member,wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · have h := cleanup hq
    simp only [Layout.wires,List.mem_toFinset,List.mem_append] at ⊢
    exact Or.inr (List.mem_toFinset.mp h)
  · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto

end BalancedCircuit
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseComposeFlags.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- Selector reconstruction is the actual six-gate stream. -/
theorem recoverSelectors_run (L : Layout) (hn : L.wires.Nodup) (P H : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P)
    (hh : s.basis L.rmsb=H) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) :
    run (recoverSelectors L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.minus (P && !H))
        L.plus (P && H)) L.lower (H ^^ P)⟩ := by
  have nd : [L.parity,L.rmsb,L.lower,L.minus,L.plus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4⟩,⟨h1_2,h1_3,h1_4⟩,⟨h2_3,h2_4⟩,h3_4⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h3_4r := Ne.symm h3_4
  cases P <;> cases H
  all_goals
    simp only [recoverSelectors,run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqm : q=L.minus <;> by_cases hqu : q=L.plus <;> by_cases hql : q=L.lower <;>
      simp_all [writeBit,Function.update]

/-- The inverse preparation uses a fresh X measurement with its CZ
correction; phase restoration holds for either record value. -/
theorem undoPreparation_run (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P)
    (ho : s.basis L.one=(N ^^ P)) (hr : s.basis L.r0=false)
    (hl : s.basis L.lower=N) (hm : s.basis L.minus=(P && N))
    (hu : s.basis L.plus=(P && !N)) :
    run (undoPreparation L) m s=⟨s.phase,
      writeBit (writeBit (writeBit (writeBit (writeBit s.basis L.r0 P)
        L.one N) L.plus false) L.minus false) L.lower false⟩ := by
  have nd : [L.parity,L.one,L.r0,L.lower,L.minus,L.plus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5⟩,⟨h1_2,h1_3,h1_4,h1_5⟩,⟨h2_3,h2_4,h2_5⟩,⟨h3_4,h3_5⟩,h4_5⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h4_5r := Ne.symm h4_5
  cases P <;> cases N <;> cases hx : m.headD false
  all_goals
    apply State.extensionality
    · simp_all [undoPreparation,run,measureAndCorrect,correct,writeBit,Function.update]
    · funext q
      by_cases hqr : q=L.r0 <;> by_cases hqo : q=L.one <;>
        by_cases hqu : q=L.plus <;> by_cases hqm : q=L.minus <;> by_cases hql : q=L.lower <;>
        simp_all [undoPreparation,run,measureAndCorrect,correct,writeBit,Function.update]

/-- The recovered threshold flag is the exact oddness of the inverse raw sum. -/
theorem result_parity (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    decide (q < |2*R-signedY B Y|)=originalParity (rawSum B (result B R Y) Y) := by
  have h := halfResult_parity_interval B (result B R Y) Y (result_bounds B R Y) hy
  rw [result_half B R Y hr hy] at h
  exact (decide_eq_decide.mpr h).symm

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseComposeFold.lean
noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- The actual left rotation restores the cleared low bit and the upper
word, with phase and every outside wire preserved. -/
theorem rotate_unfold (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (s : State) (m : List Bool) (ho : s.basis L.one=false)
    (hR : regValue L.r s.basis=encodeWord 256 R) :
    (run (rotateLeft (rawTarget L)) m s).phase=s.phase ∧
    (run (rotateLeft (rawTarget L)) m s).basis L.r0=false ∧
    regValue (foldTarget L) (run (rotateLeft (rawTarget L)) m s).basis=encodeWord 256 R ∧
    ∀w,w∉rawTarget L →
      (run (rotateLeft (rawTarget L)) m s).basis w=s.basis w := by
  have w := BalancedCircuit.widths L hw
  have init : regValue (rawTarget L) s.basis=encodeWord 256 R := by
    rw [rawTarget,regValue_append,hR]
    simp [regValue,ho]
  have rot := rotateLeft_spec (rawTarget L) (rawTargetND L hn) (encodeWord 256 R)
    (by have h := encodeWord_bound 256 R; rw [w.2.1]; omega) s m init
  have shape : rawTarget L=L.r0::foldTarget L := by
    simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have value := rot.2
  change regValue (rawTarget L) (run (rotateLeft (rawTarget L)) m s).basis=
    2*encodeWord 256 R at value
  have frame := (rotate_frame (rawTarget L) s m).2.2.2
  generalize runEq : run (rotateLeft (rawTarget L)) m s=t at rot value frame ⊢
  rw [shape] at value
  change (if t.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) t.basis=
      2*encodeWord 256 R at value
  have low : t.basis L.r0=false := by
    cases h : t.basis L.r0 <;> simp [h] at value ⊢
    omega
  refine ⟨rot.1,low,?_,frame⟩
  simp only [low,Bool.false_eq_true,if_false,Nat.zero_add] at value
  omega

/-- Fresh measured mapped subtraction restores the preparation upper word
and cleans Cout by the proved bounded integer split. -/
theorem undoFold_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hu : s.basis L.plus=plusController T) (hv : s.basis L.minus=minusController T)
    (hc : s.basis L.cout=false) (hcarry : regValue L.carry s.basis=0)
    (hword : regValue (foldTarget L) s.basis=encodeWord 256 (halfResult T)) :
    (run (undoFold L) m s).phase=s.phase ∧
    regValue (foldTarget L) (run (undoFold L) m s).basis=toggledWord T/2 ∧
    (run (undoFold L) m s).basis L.cout=false ∧
    ∀w,w∉foldTarget L → (run (undoFold L) m s).basis w=s.basis w := by
  let ys := foldTarget L++[L.cout]
  have nd : (L.plus::L.minus::L.parity::(ys++L.carry)).Nodup := by
    simpa only [ys,List.cons_append,List.nil_append,List.append_assoc] using foldND L hn
  have n1 := List.nodup_cons.mp nd
  have n2 := List.nodup_cons.mp n1.2
  have n3 := List.nodup_cons.mp n2.2
  have yND : ys.Nodup := (List.nodup_append'.mp n3.2).1
  have minusAway : L.minus∉ys := by
    intro h; exact n2.1 (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have coutAway : L.cout∉foldTarget L := by
    intro h
    exact List.disjoint_left.mp (List.nodup_append'.mp yND).2.2 h (by simp)
  have sourceAway : ∀w∈mappedWires (foldBits L),w∉L.parity::(ys++L.carry) := by
    intro w h
    rcases foldBits_sources L w h with rfl|rfl
    · intro h; exact n1.1 (List.mem_cons_of_mem _ h)
    · exact n2.1
  have widths := BalancedCircuit.widths L hw
  have ylen : ys.length=257 := widths.2.2.1
  have lowlen : (foldTarget L).length=256 := by
    have h := ylen
    simp only [ys,List.length_append,List.length_cons,List.length_nil] at h
    omega
  let u : State := ⟨s.phase,writeBit s.basis L.cout (minusController T)⟩
  have step : run [.CX L.minus L.cout] m s=u := by
    simp [run,u,hc,hv]
  have keep (a : Wire) (ha : a≠L.cout) : u.basis a=s.basis a := by
    simp [u,writeBit,ha]
  have pAway : L.parity≠L.cout := by
    intro e; exact n3.1 (List.mem_append_left _ (by simp [ys,←e]))
  have plusAway : L.plus≠L.cout := by
    intro e; exact n1.1 (by simp [ys,←e])
  have vAway : L.minus≠L.cout := fun e => minusAway (by simp [ys,←e])
  have source : mappedValue (foldBits L) u.basis=
      selectedSource (plusController T) (minusController T) := by
    have up : u.basis L.plus=plusController T := (keep _ plusAway).trans hu
    have um : u.basis L.minus=minusController T := (keep _ vAway).trans hv
    have hex : ¬(u.basis L.plus && u.basis L.minus)=true := by
      rw [up,um]; exact controllers_exclusive T
    simpa only [up,um] using foldBits_value L u.basis hex
  have init : regValue ys u.basis=foldedSum T := by
    rw [regValue_append]
    have low : regValue (foldTarget L) u.basis=encodeWord 256 (halfResult T) :=
      (regValue_congr _ _ _ (fun a ha => keep a (fun e => coutAway (e ▸ ha)))).trans hword
    rw [low,lowlen,foldedSum_value T ht]
    simp [u,writeBit,regValue,Bool.toNat,Bool.cond_eq_ite,modulusWord]
  have clean : ∀a∈L.carry,u.basis a=false := by
    intro a ha
    have away : a≠L.cout := by
      intro e
      exact List.disjoint_left.mp (List.nodup_append'.mp n3.2).2.2 (by simp [ys,←e]) ha
    exact (keep a away).trans ((regValue_zero _ _).mp hcarry a ha)
  have sub := mappedSub_any_correct (foldBits L) ys L.carry L.parity n2.2
    sourceAway (by omega) (by omega) u (m.drop 0) clean
  have value : regValue ys (run (mappedSub (foldBits L) ys L.carry L.parity) (m.drop 0) u).basis=
      toggledWord T/2 := by
    have h := sub.2.2
    rw [init,source,keep L.parity pAway,hp,ylen] at h
    have eq := foldedSum_value T ht
    have b := prepared_upper_bound T ht
    have expression : (foldedSum T+2^257-selectedSource (plusController T) (minusController T)-
        (originalParity T).toNat)%2^257=toggledWord T/2 := by
      have fs : foldedSum T=toggledWord T/2+
          selectedSource (plusController T) (minusController T)+(originalParity T).toNat := rfl
      have power : (2^257 : Nat)=2*modulusWord := by decide
      rw [show foldedSum T+2^257-selectedSource (plusController T) (minusController T)-
        (originalParity T).toNat=toggledWord T/2+2^257 by omega,Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    exact h.trans expression
  have actual : run (undoFold L) m s=
      run (mappedSub (foldBits L) ys L.carry L.parity) (m.drop 0) u := by
    unfold undoFold
    rw [run_append,run_take]
    change run (mappedSub (foldBits L) ys L.carry L.parity) (m.drop 0)
      (run [.CX L.minus L.cout] m s)=_
    rw [step]
  rw [actual]
  generalize hr : run (mappedSub (foldBits L) ys L.carry L.parity) (m.drop 0) u=r at sub value ⊢
  have split := regValue_append (foldTarget L) [L.cout] r.basis
  have one : regValue [L.cout] r.basis=(r.basis L.cout).toNat := by
    cases h : r.basis L.cout <;> simp [regValue,h]
  rw [one,lowlen] at split
  have eq : regValue (foldTarget L) r.basis+modulusWord*(r.basis L.cout).toNat=toggledWord T/2 :=
    split.symm.trans value
  have bound := prepared_upper_bound T ht
  have cout : r.basis L.cout=false := by
    cases h : r.basis L.cout <;> simp [h] at eq ⊢
    omega
  refine ⟨sub.1,?_,cout,?_⟩
  · simpa [cout] using eq
  · intro a ha
    by_cases he : a=L.cout
    · subst a; exact cout.trans hc.symm
    · exact (sub.2.1 a (by simp [ys,ha,he])).trans (keep a he)

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseComposeRaw.lean
noncomputable section

set_option maxRecDepth 16384
set_option exponentiation.threshold 512
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- The emitted source-complement/subtraction/source-complement stream
has the opposite signed direction, including arbitrary quantum carry-in. -/
theorem rawSubtract_modular (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hc : regValue L.carry s.basis=0) :
    (run (rawSubtract L) m s).phase=s.phase ∧
    (∀a,a∉rawTarget L → (run (rawSubtract L) m s).basis a=s.basis a) ∧
    regValue (rawTarget L) (run (rawSubtract L) m s).basis=
      signedWordValue 257 (!s.basis L.sign)
        (regValue (rawSource L) s.basis) (regValue (rawTarget L) s.basis) := by
  let xs := rawSource L
  let ys := rawTarget L
  have w := BalancedCircuit.widths L hw
  have xlen : xs.length=257 := by simpa only [xs] using w.1
  have ylen : ys.length=257 := by simpa only [ys] using w.2.1
  have nd := List.nodup_cons.mp (rawLayoutND L hn)
  have xd := List.nodup_append'.mp nd.2
  have xys := List.nodup_append'.mp xd.1
  have xa : L.sign∉xs := fun h => nd.1 (by simp [xs,h])
  have ya : L.sign∉ys := fun h => nd.1 (by simp [ys,h])
  have sourceND : xs.Nodup := xys.1
  have disjoint (a : Wire) (ha : a∈ys) : a∉xs :=
    fun h => List.disjoint_left.mp xys.2.2 h ha
  have carryAway (a : Wire) (ha : a∈L.carry) : a∉xs :=
    fun h => List.disjoint_left.mp xd.2.2 (List.mem_append_left _ h) ha
  let u := run (signComplement L.sign xs) m s
  have first := signComplement_correct L.sign xs sourceND xa s m
  change u.phase=s.phase ∧ (∀a,a∉xs → u.basis a=s.basis a) ∧
    regValue xs u.basis=(if s.basis L.sign then 2^xs.length-1-regValue xs s.basis
      else regValue xs s.basis) at first
  have sign1 : u.basis L.sign=s.basis L.sign := first.2.1 _ xa
  have target1 : regValue ys u.basis=regValue ys s.basis :=
    regValue_congr _ _ _ (fun a ha => first.2.1 a (disjoint a ha))
  have clean1 : ∀a∈L.carry,u.basis a=false :=
    fun a ha => (first.2.1 a (carryAway a ha)).trans ((regValue_zero _ _).mp hc a ha)
  let v := run (subInPlace xs ys L.carry L.sign) m u
  have second := subInPlace_any_correct xs ys L.carry L.sign (rawLayoutND L hn)
    (by omega) (by omega) u m clean1
  change v.phase=u.phase ∧ (∀a,a∉ys → v.basis a=u.basis a) ∧
    regValue ys v.basis=(regValue ys u.basis+2^ys.length-regValue xs u.basis-
      (u.basis L.sign).toNat)%2^ys.length at second
  have sign2 : v.basis L.sign=s.basis L.sign := (second.2.1 _ ya).trans sign1
  have source2 : regValue xs v.basis=regValue xs u.basis :=
    regValue_congr _ _ _ (fun a ha => second.2.1 a
      (fun h => List.disjoint_left.mp xys.2.2 ha h))
  let z := run (signComplement L.sign xs) (m.drop (measurementCount (subInPlace xs ys L.carry L.sign))) v
  have third := signComplement_correct L.sign xs sourceND xa v
    (m.drop (measurementCount (subInPlace xs ys L.carry L.sign)))
  change z.phase=v.phase ∧ (∀a,a∉xs → z.basis a=v.basis a) ∧
    regValue xs z.basis=(if v.basis L.sign then 2^xs.length-1-regValue xs v.basis
      else regValue xs v.basis) at third
  have source3 : regValue xs z.basis=regValue xs s.basis := by
    rw [third.2.2,sign2,source2,first.2.2]
    have h := regValue_lt xs s.basis
    cases s.basis L.sign <;> simp <;> omega
  have target3 : regValue ys z.basis=regValue ys v.basis :=
    regValue_congr _ _ _ (fun a ha => third.2.1 a (disjoint a ha))
  have eu : run (signComplement L.sign xs) m s=u := rfl
  have ev : run (subInPlace xs ys L.carry L.sign) m u=v := rfl
  have ez : run (signComplement L.sign xs)
      (m.drop (measurementCount (subInPlace xs ys L.carry L.sign))) v=z := rfl
  have actual : run (rawSubtract L) m s=z := by
    change run ((signComplement L.sign xs++subInPlace xs ys L.carry L.sign)++
      signComplement L.sign xs) m s=z
    rw [List.append_assoc,run_append,run_take,
      (signComplement_counts L.sign xs).2,List.drop_zero,eu,
      run_append,run_take,ev,ez]
  rw [actual]
  refine ⟨third.1.trans (second.1.trans first.1),?_,?_⟩
  · intro a ha
    by_cases hx : a∈xs
    · exact (regValue_eq_iff xs _ _).mp source3 a hx
    · exact (third.2.1 a hx).trans ((second.2.1 a ha).trans (first.2.1 a hx))
  · rw [target3,second.2.2,target1,first.2.2,sign1]
    have fit : regValue xs s.basis<2^257 := by
      simpa only [xlen] using regValue_lt xs s.basis
    rw [xlen,ylen]
    dsimp only [xs,ys] at fit ⊢
    cases hb : s.basis L.sign
    · simp [signedWordValue,hb]
    · simp only [hb,if_true,Bool.not_true,Bool.toNat_true,signedWordValue,Bool.false_eq_true,if_false]
      congr 1
      omega

/-- Exact inverse signed raw arithmetic on the entire centered domain. -/
theorem rawSubtract_signed (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (s : State) (m : List Bool)
    (hs : s.basis L.sign=B) (hy : signedRegValue (rawSource L) s.basis=Y)
    (ht : signedRegValue (rawTarget L) s.basis=rawSum B X Y)
    (hc : regValue L.carry s.basis=0) :
    (run (rawSubtract L) m s).phase=s.phase ∧
    signedRegValue (rawTarget L) (run (rawSubtract L) m s).basis=X ∧
    ∀a,a∉rawTarget L → (run (rawSubtract L) m s).basis a=s.basis a := by
  have h := rawSubtract_modular L hw hn s m hc
  have w := BalancedCircuit.widths L hw
  have source : signedDecode 257 (regValue (rawSource L) s.basis)=Y := by
    simpa [signedRegValue,w.1] using hy
  have target : signedDecode 257 (regValue (rawTarget L) s.basis)=rawSum B X Y := by
    simpa [signedRegValue,w.2.1] using ht
  have direction : signedIntegerValue (!B) Y (rawSum B X Y)=X := by
    cases B <;> simp [signedIntegerValue,rawSum,signedY]
  have bound : -((2^(257-1) : Nat) : Int)≤X ∧ X<((2^(257-1) : Nat) : Int) := by
    have constants := BalancedField.constants
    unfold Centered at hx
    norm_num at ⊢
    omega
  have lift := signedWordValue_lift 257 (!B)
    (regValue (rawSource L) s.basis) (regValue (rawTarget L) s.basis)
    (by omega) (by simpa only [w.1] using regValue_lt (rawSource L) s.basis)
    (by rw [source,target,direction]; exact bound.1)
    (by rw [source,target,direction]; exact bound.2)
  rw [source,target,direction] at lift
  refine ⟨h.1,?_,h.2.1⟩
  unfold signedRegValue
  rw [w.2.1,h.2.2,hs]
  exact lift

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseComposeWord.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

private theorem top_half (U H : Nat) (P N : Bool)
    (hH : 0<H) (hU : U/(2*H)=N.toNat) :
    (if P then if N then U-2*H else U+2*H else U)/2/H=(N ^^ P).toNat := by
  have div := Nat.mod_add_div U (2*H)
  have rem := Nat.mod_lt U (show 0<2*H by omega)
  rw [hU] at div
  cases P <;> cases N
  · simpa only [Bool.false_eq_true,if_false,Bool.xor_false,Bool.toNat_false,
      Nat.div_div_eq_div_mul,Nat.mul_comm] using hU
  · simpa only [Bool.false_eq_true,if_false,Bool.xor_false,Bool.toNat_true,
      Nat.div_div_eq_div_mul,Nat.mul_comm] using hU
  · simp only [if_true,Bool.false_eq_true,if_false,Bool.false_xor,
      Bool.toNat_true,Nat.div_div_eq_div_mul]
    rw [Nat.add_div_right _ (show 0<2*H by omega)]
    simpa using hU
  · simp only [if_true,Bool.true_xor,Bool.not_true,Bool.toNat_false,
      Nat.div_div_eq_div_mul]
    apply Nat.div_eq_of_lt
    simp only [Bool.toNat_true,Nat.mul_one] at div
    omega

private theorem top_bit_split (M x y : Nat) (b v : Bool)
    (hx : x<M) (hy : y<M) (h : x+M*b.toNat=y+M*v.toNat) : b=v := by
  cases b <;> cases v <;> simp at h ⊢ <;> omega

private theorem restore_word (U B H : Nat) (P N : Bool)
    (hs : U/(2*H)=N.toNat)
    (hw : (if P then if N then U-2*H else U+2*H else U)=
      2*(B+H*(N ^^ P).toNat)+P.toNat) :
    P.toNat+2*(B+H*N.toNat)=U := by
  have div := Nat.mod_add_div U (2*H)
  rw [hs] at div
  cases P <;> cases N <;> simp at div hw ⊢ <;> omega


/-- A prepared upper word determines its physical highest bit. -/
theorem prepared_one (L : Layout) (hw : L.Widths) (T : Int)
    (ht : -(2*q)≤T ∧ T≤2*q) (s : State)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    s.basis L.one=(decide (T<0) ^^ originalParity T) := by
  have shape : foldTarget L=(L.rtail++[L.rmsb])++[L.one] := by
    simp [foldTarget,List.append_assoc]
  have len : (L.rtail++[L.rmsb]).length=255 := by simp [hw.1]
  have split := regValue_append (L.rtail++[L.rmsb]) [L.one] s.basis
  rw [←shape,hword,len] at split
  have low := regValue_lt (L.rtail++[L.rmsb]) s.basis
  rw [len] at low
  have one : regValue [L.one] s.basis=(s.basis L.one).toNat := by
    cases h : s.basis L.one <;> simp [regValue,h]
  rw [one] at split
  have top := top_half (encodeWord 257 T) (2^255)
    (originalParity T) (decide (T<0)) (Nat.two_pow_pos _)
    (by simpa only [show 2*2^255=modulusWord from by norm_num [modulusWord]] using raw_sign T ht)
  change toggledWord T/2/2^255=(decide (T<0) ^^ originalParity T).toNat at top
  have div := Nat.mod_add_div (toggledWord T/2) (2^255)
  rw [top] at div
  have rem := Nat.mod_lt (toggledWord T/2) (Nat.two_pow_pos 255)
  exact top_bit_split (2^255) (regValue (L.rtail++[L.rmsb]) s.basis)
    ((toggledWord T/2)%2^255) (s.basis L.one) (decide (T<0) ^^ originalParity T)
    low rem (split.symm.trans div.symm)


/-- The actual inverse preparation restores the full raw 257-bit encoding. -/
theorem undoPreparation_word (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T) (hr : s.basis L.r0=false)
    (hl : s.basis L.lower=decide (T<0))
    (hm : s.basis L.minus=minusController T) (hu : s.basis L.plus=plusController T)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    regValue (rawTarget L) (run (undoPreparation L) m s).basis=encodeWord 257 T := by
  let P := originalParity T
  let N := decide (T<0)
  have one := prepared_one L hw T ht s hword
  have actual := undoPreparation_run L hn P N s m hp one hr hl hm hu
  let mid := L.rtail++[L.rmsb]
  have shape : rawTarget L=L.r0::(mid++[L.one]) := by
    simp [mid,rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have fshape : foldTarget L=mid++[L.one] := by simp [mid,foldTarget,List.append_assoc]
  have len : mid.length=255 := by simp [mid,hw.1]
  have split := regValue_append mid [L.one] s.basis
  rw [←fshape,hword,len] at split
  have b : regValue [L.one] s.basis=(N ^^ P).toNat := by
    simp only [regValue,List.foldr_cons,List.foldr_nil,Nat.mul_zero,Nat.add_zero,one]
    cases h : N ^^ P <;> rfl
  rw [b] at split
  have raw := raw_sign T ht
  have clear := cleared_low_word T ht
  have nd := rawTargetND L hn
  rw [shape] at nd
  have lowAway := (List.nodup_cons.mp nd).1
  have middle : regValue mid (run (undoPreparation L) m s).basis=regValue mid s.basis := by
    apply regValue_congr
    intro a ha
    have data : a∈L.r++L.y++L.carry := by
      have r : a∈L.r := by
        simp only [mid,List.mem_append,List.mem_singleton] at ha
        simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
          List.mem_append,List.mem_cons,List.mem_singleton]
        tauto
      exact List.mem_append_left _ (List.mem_append_left _ r)
    have away (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (e ▸ data)
    have ar : a≠L.r0 := fun e => lowAway (by simp [←e,ha])
    rw [actual]
    simp [writeBit,ar,away L.one (by simp),away L.plus (by simp),
      away L.minus (by simp),away L.lower (by simp)]
  have sND : [L.r0,L.one,L.plus,L.minus,L.lower].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at sND
  rcases sND with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
  have lout : (run (undoPreparation L) m s).basis L.r0=P := by
    rw [actual]
    simp only [writeBit,Function.update_of_ne h04,Function.update_of_ne h03,
      Function.update_of_ne h02,Function.update_of_ne h01,Function.update_self]
  have hout : (run (undoPreparation L) m s).basis L.one=N := by
    rw [actual]
    simp only [writeBit,Function.update_of_ne h14,Function.update_of_ne h13,
      Function.update_of_ne h12,Function.update_self]
  rw [shape]
  change (if (run (undoPreparation L) m s).basis L.r0 then 1 else 0)+
    2*regValue (mid++[L.one]) (run (undoPreparation L) m s).basis=_
  rw [lout,regValue_append,middle,len]
  have high : regValue [L.one] (run (undoPreparation L) m s).basis=N.toNat := by
    simp only [regValue,List.foldr_cons,List.foldr_nil,Nat.mul_zero,Nat.add_zero,hout]
    cases h : N <;> rfl
  rw [high]
  have pow : modulusWord=2*2^255 := by norm_num [modulusWord]
  change encodeWord 257 T/modulusWord=N.toNat at raw
  change toggledWord T=2*(toggledWord T/2)+P.toNat at clear
  have pv : (if P then 1 else 0)=P.toNat := by cases P <;> rfl
  rw [pv]
  change (if P then if N then encodeWord 257 T-modulusWord else
    encodeWord 257 T+modulusWord else encodeWord 257 T)=_ at clear
  rw [pow] at raw clear
  rw [split] at clear
  exact restore_word (encodeWord 257 T) (regValue mid s.basis) (2^255) P N
    raw clear

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseComposeSeed.lean
noncomputable section

set_option maxRecDepth 4096
set_option exponentiation.threshold 512
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- Only the seed's four CX gates are reversed. Their exact correlations
clear the three seeded scalar sites without measurements. -/
theorem unseed_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hg : s.basis L.sourceGuard=s.basis L.ymsb)
    (ho : s.basis L.one=s.basis L.rmsb)
    (hp : s.basis L.parity=(s.basis (L.ylow.getD 0 0) ^^ s.basis L.r0)) :
    run (seedViews L).reverse m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.parity false) L.one false) L.sourceGuard false⟩ := by
  have nd := seedND L hw hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6⟩,⟨h2_3,h2_4,h2_5,h2_6⟩,⟨h3_4,h3_5,h3_6⟩,⟨h4_5,h4_6⟩,h5_6⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h0_6r := Ne.symm h0_6
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h1_6r := Ne.symm h1_6
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h2_6r := Ne.symm h2_6
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h3_6r := Ne.symm h3_6
  have h4_5r := Ne.symm h4_5
  have h4_6r := Ne.symm h4_6
  have h5_6r := Ne.symm h5_6
  apply State.extensionality
  · simp [seedViews,run]
  · funext q
    by_cases hqg : q=L.sourceGuard <;> by_cases hqo : q=L.one <;> by_cases hqp : q=L.parity <;>
      simp_all [seedViews,run,writeBit,Function.update]

/-- The raw arithmetic postcondition supplies the unseed sign and parity
correlations directly, without a classical circuit oracle. -/
theorem unseed_correlations (L : Layout) (hw : L.Widths)
    (B : Bool) (X Y : Int) (hc : Centered X) (s : State)
    (hx : signedRegValue (rawTarget L) s.basis=X)
    (hy : signedRegValue L.y s.basis=Y)
    (_hg : s.basis L.sourceGuard=s.basis L.ymsb)
    (hp : s.basis L.parity=originalParity (rawSum B X Y)) :
    s.basis L.one=s.basis L.rmsb ∧
    s.basis L.parity=(s.basis (L.ylow.getD 0 0) ^^ s.basis L.r0) := by
  have rlen : L.r.length=256 := (BalancedCleanup.widths L.toLayout hw).2.1
  have lowlen : (L.r0::L.rtail).length=255 := by simp [hw.1]
  have high := regValue_highBit (L.r0::L.rtail) L.rmsb s.basis
  have hraw := hx
  rw [rawTarget,signedRegValue_msb,regValue_append,rlen] at hraw
  have bits : regValue [L.one] s.basis=(s.basis L.one).toNat := by
    cases h : s.basis L.one <;> simp [regValue,h]
  rw [bits] at hraw
  have rshape : (L.r0::L.rtail)++[L.rmsb]=L.r := by
    simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  rw [lowlen,rshape] at high
  have same : s.basis L.one=s.basis L.rmsb := by
    have constant := BalancedField.constants
    unfold Centered at hc
    cases ho : s.basis L.one <;> cases hm : s.basis L.rmsb
    all_goals try rfl
    all_goals simp [ho,hm] at hraw high
    all_goals omega
  constructor
  · exact same
  · have xpar : s.basis L.r0=originalParity X := by
      apply word_parity L.r0 (L.rtail++[L.rmsb,L.one]) s.basis X
      simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using hx
    cases hylo : L.ylow with
    | nil => have h := hw.2.1; simp [hylo] at h
    | cons a as =>
      have ypar : s.basis a=originalParity Y := by
        apply word_parity a (as++[L.ymsb]) s.basis Y
        simpa [BalancedCleanup.Layout.y,hylo] using hy
      rw [hp,raw_parity,xpar]
      simp [hylo,ypar]

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseComposePackets.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- Result-sign selectors reconstruct precisely the original raw controls. -/
theorem recoverSelectors_raw (L : Layout) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hh : s.basis L.rmsb=decide (halfResult T<0))
    (hl : s.basis L.lower=false) (hm : s.basis L.minus=false)
    (hu : s.basis L.plus=false) :
    run (recoverSelectors L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.minus (minusController T))
        L.plus (plusController T)) L.lower (decide (T<0))⟩ := by
  have h := recoverSelectors_run L hn (originalParity T) (decide (halfResult T<0))
    s m hp hh hl hm hu
  rw [halfResult_sign T ht] at h
  have minus : (originalParity T && !(decide (T<0) ^^ originalParity T))=minusController T := by
    unfold minusController
    cases originalParity T <;> cases decide (T<0) <;> rfl
  have plus : (originalParity T && (decide (T<0) ^^ originalParity T))=plusController T := by
    unfold plusController
    cases originalParity T <;> cases decide (T<0) <;> rfl
  have low : ((decide (T<0) ^^ originalParity T) ^^ originalParity T)=decide (T<0) := by
    cases originalParity T <;> cases decide (T<0) <;> rfl
  simpa only [minus,plus,low] using h

/-- A selector packet exposes all physical controls and its full frame. -/
theorem recoverSelectors_packet (L : Layout) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hh : s.basis L.rmsb=decide (halfResult T<0))
    (hl : s.basis L.lower=false) (hm : s.basis L.minus=false)
    (hu : s.basis L.plus=false) :
    let t := run (recoverSelectors L) m s
    t.phase=s.phase ∧ t.basis L.lower=decide (T<0) ∧
    t.basis L.minus=minusController T ∧ t.basis L.plus=plusController T ∧
    ∀a,a≠L.lower → a≠L.minus → a≠L.plus → t.basis a=s.basis a := by
  dsimp only
  rw [recoverSelectors_raw L hn T ht s m hp hh hl hm hu]
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp [writeBit]
  · simp_all [writeBit,Function.update]
  · simp_all [writeBit,Function.update]
  · intro a hl hm hu; simp [writeBit,hl,hm,hu]

/-- Inverse preparation provides all selector zeros, phase restoration and
an outside-target frame in one packet. -/
theorem undoPreparation_packet (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T) (hr : s.basis L.r0=false)
    (hl : s.basis L.lower=decide (T<0))
    (hm : s.basis L.minus=minusController T) (hu : s.basis L.plus=plusController T)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    let t := run (undoPreparation L) m s
    t.phase=s.phase ∧ regValue (rawTarget L) t.basis=encodeWord 257 T ∧
    t.basis L.lower=false ∧ t.basis L.minus=false ∧ t.basis L.plus=false ∧
    ∀a,a∉rawTarget L → a≠L.lower → a≠L.minus → a≠L.plus → t.basis a=s.basis a := by
  dsimp only
  have actual := undoPreparation_run L hn (originalParity T) (decide (T<0)) s m
    hp (prepared_one L hw T ht s hword) hr hl hm hu
  have value := undoPreparation_word L hw hn T ht s m hp hr hl hm hu hword
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  refine ⟨?_,value,?_,?_,?_,?_⟩
  · rw [actual]
  · rw [actual]; simp_all [writeBit,Function.update]
  · rw [actual]; simp_all [writeBit,Function.update]
  · rw [actual]; simp_all [writeBit,Function.update]
  · intro a ha hl hm hu
    have ar : a≠L.r0 := fun e => ha (by simp [rawTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,←e])
    have ao : a≠L.one := fun e => ha (by simp [rawTarget,←e])
    rw [actual]
    simp [writeBit,ar,ao,hl,hm,hu]

/-- Once the restored raw word is centered, the genuine reverse seed
cleans its three sites and preserves every other physical wire. -/
theorem unseed_packet (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (s : State) (m : List Bool)
    (hr : signedRegValue (rawTarget L) s.basis=X)
    (hy : signedRegValue L.y s.basis=Y)
    (hg : s.basis L.sourceGuard=s.basis L.ymsb)
    (hp : s.basis L.parity=originalParity (rawSum B X Y)) :
    let t := run (seedViews L).reverse m s
    t.phase=s.phase ∧ t.basis L.sourceGuard=false ∧ t.basis L.one=false ∧
    t.basis L.parity=false ∧ ∀a,a≠L.sourceGuard → a≠L.one → a≠L.parity → t.basis a=s.basis a := by
  dsimp only
  have corr := unseed_correlations L hw B X Y hx s hr hy hg hp
  have actual := unseed_run L hw hn s m hg corr.1 corr.2
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rw [actual]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp [writeBit]
  · simp_all [writeBit,Function.update]
  · simp_all [writeBit,Function.update]
  · intro a hg ho hp; simp [writeBit,hg,ho,hp]

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseComposeProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

private theorem initialWork (L : Layout) (a : Wire)
    (ha : a∈[L.parity,L.lower,L.one]++L.carry) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem selectorWork (L : Layout) (a : Wire)
    (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem frameWork (L : Layout) (a : Wire)
    (ha : a∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus,L.plus]) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem selectorAway (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) :
    a≠L.sourceGuard ∧ a≠L.parity := by
  have nd : ([L.sourceGuard,L.parity]++([L.cout,L.minus,L.plus,L.lower,L.one]++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (allND L hn) q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have sep := List.disjoint_left.mp (List.nodup_append'.mp nd).2.2
  exact ⟨fun e => sep (by simp [←e]) ha,fun e => sep (by simp [←e]) ha⟩

/-- Complete independently emitted inverse field kernel, including phase,
all measurement records, complete workspace cleanup, and outside-R frame. -/
theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (program L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (result B R Y) ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.r → t.basis q=s.basis q) := by
  let X := result B R Y
  let T := rawSum B X Y
  let P := originalParity T
  let m₁ := m.drop (measurementCount (recoverParity L))
  let m₂ := m₁.drop (measurementCount (undoFold L))
  let m₃ := m₂.drop (measurementCount (undoPreparation L))
  let m₄ := m₃.drop (measurementCount (rawSubtract L))
  generalize e₀ : run [.CX L.ymsb L.sourceGuard] m s=u₀
  generalize e₁ : run (recoverParity L) m u₀=u₁
  generalize e₂ : run (recoverSelectors L) m₁ u₁=u₂
  generalize e₃ : run (rotateLeft (rawTarget L)) m₁ u₂=u₃
  generalize e₄ : run (undoFold L) m₁ u₃=u₄
  generalize e₅ : run (undoPreparation L) m₂ u₄=u₅
  generalize e₆ : run (rawSubtract L) m₃ u₅=u₆
  generalize e₇ : run (seedViews L).reverse m₄ u₆=t
  have hx : Centered X := result_bounds B R Y
  have ht : -(2*q)≤T ∧ T≤2*q := rawSum_bounds B X Y hx hy
  have half : halfResult T=R := result_half B R Y hr hy
  have rawRange : -((2^(257-1) : Nat) : Int)≤T ∧ T<((2^(257-1) : Nat) : Int) := by
    have c := BalancedField.constants
    norm_num at ⊢
    omega
  have w := BalancedCircuit.widths L hw
  have rlen := (BalancedCleanup.widths L.toLayout hw).2.1
  have ylen := (BalancedCleanup.widths L.toLayout hw).2.2.1
  have cnd : L.toLayout.wires.Nodup :=
    (List.nodup_append'.mp (show ([L.sourceGuard,L.cout,L.minus,L.plus]++L.toLayout.wires).Nodup from hn)).2.1
  have ndR := List.nodup_reverse.mpr (scalarND L hn)
  simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndR
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  rcases ndR with ⟨⟨r0_1,r0_2,r0_3,r0_4,r0_5,r0_6,r0_7,r0_8,r0_9,r0_10⟩,⟨r1_2,r1_3,r1_4,r1_5,r1_6,r1_7,r1_8,r1_9,r1_10⟩,⟨r2_3,r2_4,r2_5,r2_6,r2_7,r2_8,r2_9,r2_10⟩,⟨r3_4,r3_5,r3_6,r3_7,r3_8,r3_9,r3_10⟩,⟨r4_5,r4_6,r4_7,r4_8,r4_9,r4_10⟩,⟨r5_6,r5_7,r5_8,r5_9,r5_10⟩,⟨r6_7,r6_8,r6_9,r6_10⟩,⟨r7_8,r7_9,r7_10⟩,⟨r8_9,r8_10⟩,r9_10⟩
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉rawTarget L := compose_raw_away L hn q hq
  have zero (q : Wire) (hq : q∈work L) : s.basis q=false := hc q hq
  have f₀ (a : Wire) (ha : a≠L.sourceGuard) : u₀.basis a=s.basis a := by
    rw [←e₀]; simp only [run,writeBit,Function.update_of_ne ha]
  have guard₀ : u₀.basis L.sourceGuard=s.basis L.ymsb := by
    rw [←e₀]
    simp only [run,writeBit,Function.update_self]
    rw [hc L.sourceGuard (by simp [work])]
    simp only [Bool.false_xor]
  have R₀ : regValue L.r u₀.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 rlen s.basis R hR)
    apply regValue_congr
    intro a ha
    exact f₀ a (fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha]))
  have Y₀ : regValue L.y u₀.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 ylen s.basis Y hY)
    apply regValue_congr
    intro a ha
    exact f₀ a (fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha]))
  have z₀ (a : Wire) (ha : a∈[L.parity,L.lower,L.one]++L.carry) : u₀.basis a=false := by
    have ne : a≠L.sourceGuard := by
      rcases List.mem_append.mp ha with ha|ha
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl <;> assumption
      · exact fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha])
    exact (f₀ a ne).trans (hc a (initialWork L a ha))
  have oneOracle := recoverParity_correct L hw cnd R Y B hr hy u₀ m R₀ Y₀
    ((f₀ _ (by assumption)).trans hs) (z₀ _ (by simp)) (z₀ _ (by simp))
    (fun a ha => z₀ a (by simp [ha])) (z₀ _ (by simp))
  have parity : decide (q < |2*R-signedY B Y|)=P := result_parity B R Y hr hy
  rw [parity,e₁] at oneOracle
  have p₁ : u₁.basis L.parity=P := by rw [oneOracle]; simp only [writeBit,Function.update_self]
  have f₁ (a : Wire) (hg : a≠L.sourceGuard) (hp : a≠L.parity) : u₁.basis a=s.basis a := by
    rw [oneOracle]; simp only [writeBit,Function.update_of_ne hp]; exact f₀ a hg
  have g₁ : u₁.basis L.sourceGuard=s.basis L.ymsb := by
    rw [oneOracle]; simpa only [writeBit,Function.update_of_ne (show L.sourceGuard≠L.parity by assumption)] using guard₀
  have z₁ (a : Wire) (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) : u₁.basis a=false := by
    have ne := selectorAway L hn a ha
    exact (f₁ a ne.1 ne.2).trans (hc a (selectorWork L a ha))
  have R₁ : regValue L.r u₁.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 rlen s.basis R hR)
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₁ a (neq _ (by simp)) (neq _ (by simp))
  have sign₁ : u₁.basis L.rmsb=decide (halfResult T<0) := by
    rw [half]
    exact BalancedCleanup.result_msb L.toLayout hw R hr u₁.basis R₁
  have packet₂ := recoverSelectors_packet L hn T ht u₁ m₁ p₁ sign₁
    (z₁ _ (by simp)) (z₁ _ (by simp)) (z₁ _ (by simp))
  rw [e₂] at packet₂
  have f₂ (a : Wire) (hl : a≠L.lower) (hm : a≠L.minus) (hu : a≠L.plus) : u₂.basis a=u₁.basis a :=
    packet₂.2.2.2.2 a hl hm hu
  have R₂ : regValue L.r u₂.basis=encodeWord 256 R := by
    apply Eq.trans _ R₁
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₂ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  have one₂ : u₂.basis L.one=false :=
    (f₂ _ (by assumption) (by assumption) (by assumption)).trans (z₁ _ (by simp))
  have packet₃ := rotate_unfold L hw hn R u₂ m₁ one₂ R₂
  rw [e₃] at packet₃
  have f₃ (a : Wire) (ha : a∉rawTarget L) : u₃.basis a=u₂.basis a := packet₃.2.2.2 a ha
  have p₃ : u₃.basis L.parity=P := (f₃ _ (away _ (by simp))).trans
    ((f₂ _ (by assumption) (by assumption) (by assumption)).trans p₁)
  have c₃ : u₃.basis L.cout=false := (f₃ _ (away _ (by simp))).trans
    ((f₂ _ (by assumption) (by assumption) (by assumption)).trans (z₁ _ (by simp)))
  have carry₃ : regValue L.carry u₃.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (f₃ a (away a (by simp [ha]))).trans
      ((f₂ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans (z₁ a (by simp [ha])))
  have upper₃ : regValue (foldTarget L) u₃.basis=encodeWord 256 (halfResult T) := by
    rw [half]; exact packet₃.2.2.1
  have packet₄ := undoFold_correct L hw hn T ht u₃ m₁ p₃
    ((f₃ _ (away _ (by simp))).trans packet₂.2.2.2.1)
    ((f₃ _ (away _ (by simp))).trans packet₂.2.2.1) c₃ carry₃ upper₃
  rw [e₄] at packet₄
  have f₄ (a : Wire) (ha : a∉rawTarget L) : u₄.basis a=u₃.basis a :=
    packet₄.2.2.2 a (compose_fold_subset L a ha)
  have zero₄ : u₄.basis L.r0=false :=
    (packet₄.2.2.2 _ (compose_not_fold_r0 L hn)).trans packet₃.2.1
  have packet₅ := undoPreparation_packet L hw hn T ht u₄ m₂
    ((f₄ _ (away _ (by simp))).trans p₃) zero₄
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.1))
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.2.1))
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.2.2.1)) packet₄.2.1
  rw [e₅] at packet₅
  have f₅ (a : Wire) (ha : a∉rawTarget L) (hl : a≠L.lower) (hm : a≠L.minus) (hu : a≠L.plus) :
      u₅.basis a=u₁.basis a := (packet₅.2.2.2.2.2 a ha hl hm hu).trans
    ((f₄ a ha).trans ((f₃ a ha).trans (f₂ a hl hm hu)))
  have raw₅ : signedRegValue (rawTarget L) u₅.basis=T := by
    unfold signedRegValue
    rw [w.2.1,packet₅.2.1]
    exact decode_encodeWord 257 (by norm_num) T rawRange
  have Y₅ : signedRegValue L.y u₅.basis=Y := by
    apply Eq.trans _ hY
    unfold signedRegValue
    congr 1
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (f₅ a (away a (by simp [ha])) (neq _ (by simp))
      (neq _ (by simp)) (neq _ (by simp))).trans (f₁ a (neq _ (by simp)) (neq _ (by simp)))
  have g₅ : u₅.basis L.sourceGuard=u₅.basis L.ymsb := by
    have left := (f₅ _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans g₁
    have right := (f₅ L.ymsb (away L.ymsb (by simp [BalancedCleanup.Layout.y]))
      (by assumption) (by assumption) (by assumption)).trans (f₁ L.ymsb (by assumption) (by assumption))
    exact left.trans right.symm
  have src₅ : signedRegValue (rawSource L) u₅.basis=Y := by
    exact (signed_extension L.ylow L.ymsb L.sourceGuard u₅.basis g₅).trans Y₅
  have carry₅ : regValue L.carry u₅.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (packet₅.2.2.2.2.2 a (away a (by simp [ha])) (neq _ (by simp))
      (neq _ (by simp)) (neq _ (by simp))).trans
      ((regValue_zero _ _).mp carry₃ a ha |> fun h => (f₄ a (away a (by simp [ha]))).trans h)
  have sign₅ : u₅.basis L.sign=B := (f₅ _ (away _ (by simp))
    (by assumption) (by assumption) (by assumption)).trans ((f₁ _ (by assumption) (by assumption)).trans hs)
  have packet₆ := rawSubtract_signed L hw hn B X Y hx u₅ m₃ sign₅ src₅ raw₅ carry₅
  rw [e₆] at packet₆
  have f₆ (a : Wire) (ha : a∉rawTarget L) : u₆.basis a=u₅.basis a := packet₆.2.2 a ha
  have Y₆ : signedRegValue L.y u₆.basis=Y := by
    apply Eq.trans _ Y₅
    unfold signedRegValue
    congr 1
    exact regValue_congr _ _ _ (fun a ha => f₆ a (away a (by simp [ha])))
  have g₆ : u₆.basis L.sourceGuard=u₆.basis L.ymsb := by
    exact (f₆ _ (away _ (by simp))).trans (g₅.trans
      (f₆ _ (away _ (by simp [BalancedCleanup.Layout.y]))).symm)
  have p₆ : u₆.basis L.parity=P := (f₆ _ (away _ (by simp))).trans
    ((f₅ _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans p₁)
  have packet₇ := unseed_packet L hw hn B X Y hx u₆ m₄ packet₆.2.1 Y₆ g₆ p₆
  rw [e₇] at packet₇
  have f₇ (a : Wire) (hg : a≠L.sourceGuard) (ho : a≠L.one) (hp : a≠L.parity) :
      t.basis a=u₆.basis a := packet₇.2.2.2.2 a hg ho hp
  have actual : run (program L) m s=t := by
    simp only [program,List.append_assoc]
    rw [run_append,run_take]
    simp only [show measurementCount [.CX L.ymsb L.sourceGuard]=0 from rfl,List.drop_zero]
    rw [e₀,run_append,run_take,e₁,run_append,run_take]
    simp only [show measurementCount (recoverSelectors L)=0 from rfl,List.drop_zero]
    rw [e₂,run_append,run_take,(rotate_counts (rawTarget L)).2.2.2,List.drop_zero,
      e₃,run_append,run_take,e₄,run_append,run_take,e₅,run_append,run_take,e₆,e₇]

  have clean : ∀a∈work L,t.basis a=false := by
    intro a ha
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|ha
    · exact packet₇.2.1
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans ((packet₅.2.2.2.2.2 _ (away _ (by simp))
          (by assumption) (by assumption) (by assumption)).trans packet₄.2.2.1))
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.2.1)
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.2.2.1)
    · exact packet₇.2.2.2.1
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.1)
    · exact packet₇.2.2.1
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
        fun e => flagAway L hn f hf (by simp [e ▸ ha])
      exact (f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((f₆ a (away a (by simp [ha]))).trans ((regValue_zero _ _).mp carry₅ a ha))
  have frame : ∀a,a∉L.r → t.basis a=s.basis a := by
    intro a ha
    by_cases workA : a∈work L
    · exact (clean a workA).trans (hc a workA).symm
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus,L.plus]) : a≠f :=
        fun e => workA (e.symm ▸ frameWork L f hf)
      have ar : a∉rawTarget L := by
        simp only [rawTarget,List.mem_append,List.mem_singleton,not_or]
        exact ⟨ha,neq _ (by simp)⟩
      exact (f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((f₆ a ar).trans ((f₅ a ar (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
          (f₁ a (neq _ (by simp)) (neq _ (by simp)))))
  have out : regValue L.r t.basis=encodeWord 256 X := by
    have corr := unseed_correlations L hw B X Y hx u₆ packet₆.2.1 Y₆ g₆ p₆
    have narrow : signedRegValue L.r u₆.basis=X :=
      (signed_extension (L.r0::L.rtail) L.rmsb L.one u₆.basis corr.1).symm.trans packet₆.2.1
    apply Eq.trans _ (word_encoding L.r 256 rlen u₆.basis X narrow)
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  rw [actual]
  exact ⟨packet₇.1.trans (packet₆.1.trans (packet₅.1.trans (packet₄.1.trans
    (packet₃.1.trans (packet₂.1.trans (by rw [oneOracle,←e₀]; rfl)))))),out,clean,frame⟩

end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/TranscriptSelectFlag.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Store B AND (source XOR constant). The source returns before the body. -/
def transcriptSelectCompute (b source flag : Wire) (constant : Bool) : Program :=
  (if constant then [.X source] else []) ++ [.CCX b source flag] ++
    (if constant then [.X source] else [])

/-- During the body the flag is the selected actual/constant transcript bit. -/
def transcriptSelectExpose (flag : Wire) (constant : Bool) : Program :=
  if constant then [.X flag] else []

def transcriptSelectErase (b source flag : Wire) (constant : Bool) : Program :=
  [.measureX flag [] (if constant then [.Z b,.CZ b source] else [.CZ b source])]

private theorem select_distinct (b source flag : Wire) (hn : [b,source,flag].Nodup) :
    b≠source ∧ b≠flag ∧ source≠flag := by
  simpa [List.nodup_cons,List.mem_cons,and_assoc] using hn

theorem transcriptSelectCompute_correct (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool) :
    run (transcriptSelectCompute b source flag constant) m s=
      ⟨s.phase,writeBit s.basis flag
        (s.basis flag ^^ (s.basis b && (s.basis source ^^ constant)))⟩ := by
  have h := select_distinct b source flag hn
  cases constant <;> simp only [transcriptSelectCompute,Bool.false_eq_true,if_false,if_true,
    List.nil_append,List.cons_append,List.append_nil,run]
  all_goals apply State.extensionality
  all_goals try rfl
  all_goals
    funext q
    by_cases hq : q=source
    · subst q
      cases hb : s.basis b <;> cases hs : s.basis source <;> cases hf : s.basis flag <;>
        simp_all [writeBit,Function.update]
    · by_cases hqf : q=flag
      · subst q
        cases hb : s.basis b <;> cases hs : s.basis source <;> cases hf : s.basis flag <;>
          simp_all [writeBit,Function.update]
      · simp_all [writeBit,Function.update]

theorem transcriptSelect_counts (b source flag : Wire) (constant : Bool) :
    toffoliCount (transcriptSelectCompute b source flag constant)=1 ∧
    measurementCount (transcriptSelectCompute b source flag constant)=0 ∧
    toffoliCount (transcriptSelectExpose flag constant)=0 ∧
    measurementCount (transcriptSelectExpose flag constant)=0 ∧
    toffoliCount (transcriptSelectErase b source flag constant)=0 ∧
    measurementCount (transcriptSelectErase b source flag constant)=1 := by
  cases constant <;> simp [transcriptSelectCompute,transcriptSelectExpose,transcriptSelectErase,
    toffoliCount,measurementCount]

/-- The second exposure restores the stored product before measurement.
Keeping this inside the emitted window prevents a complemented-control
cleanup from introducing an outcome-dependent global phase. -/
def transcriptSelectWindow (b source flag : Wire) (constant : Bool) (body : Program) : Program :=
  transcriptSelectCompute b source flag constant ++ transcriptSelectExpose flag constant ++
    body ++ transcriptSelectExpose flag constant ++ transcriptSelectErase b source flag constant

/-- Safe cleanup after a body that preserves the effective flag and its
enable/source inputs. The semantic premise is the selected control value. -/
theorem transcriptSelect_finish_correct (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool)
    (hv : s.basis flag=(if s.basis b then s.basis source else constant)) :
    run (transcriptSelectExpose flag constant ++ transcriptSelectErase b source flag constant) m s=
      ⟨s.phase,writeBit s.basis flag false⟩ := by
  have h := select_distinct b source flag hn
  cases constant <;> cases hm : m.headD false <;>
    cases hb : s.basis b <;> cases hs : s.basis source <;>
    simp_all [transcriptSelectExpose,transcriptSelectErase,run,measureAndCorrect,
      correct,writeBit,Function.update]

theorem transcriptSelectWindow_counts (b source flag : Wire) (constant : Bool) (body : Program) :
    toffoliCount (transcriptSelectWindow b source flag constant body)=toffoliCount body+1 ∧
    measurementCount (transcriptSelectWindow b source flag constant body)=measurementCount body+1 := by
  have hc := transcriptSelect_counts b source flag constant
  simp only [transcriptSelectWindow,toffoliCount_append,measurementCount_append,
    hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2]
  constructor <;> omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MixedTranscriptFieldCell.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open Secp256k1
/-- The effective transcript equals the recorded bit in the enabled branch,
and the supplied fixed transcript bit in the inactive branch. -/
def mixedTranscriptBit (base : BasisState) (b source : Wire) (constant : Bool) : Bool :=
  if base b then base source else constant
def mixedTranscriptBase (base : BasisState) (b source flag : Wire)
    (constant : Bool) : BasisState :=
  writeBit base flag (mixedTranscriptBit base b source constant)
private theorem select_start (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool)
    (hf : s.basis flag=false) :
    run (transcriptSelectCompute b source flag constant ++
      transcriptSelectExpose flag constant) m s=
      ⟨s.phase,mixedTranscriptBase s.basis b source flag constant⟩ := by
  rw [run_append,transcriptSelectCompute_correct b source flag constant hn]
  apply State.extensionality
  · cases constant <;> rfl
  · funext q
    by_cases hq : q=flag
    · subst q
      cases hb : s.basis b <;> cases hs : s.basis source <;> cases constant <;>
        simp [transcriptSelectExpose,run,mixedTranscriptBase,mixedTranscriptBit,
          writeBit,Function.update,hf,hb,hs]
    · cases constant <;>
        simp [transcriptSelectExpose,run,mixedTranscriptBase,writeBit,Function.update,hq]

/-- Lift an exact pair-framed body through a complete measured selection
window. The body's frame preserves the selected flag and both inputs. -/
theorem transcriptSelectWindow_pairFrame (b source flag : Wire) (constant : Bool)
    (z a : List Wire) (hn : [b,source,flag].Nodup)
    (hb : b∉z ∧ b∉a) (hs : source∉z ∧ source∉a)
    (hf : flag∉z ∧ flag∉a) (base : BasisState) (hzero : base flag=false)
    (X Y X' Y' : Nat) (body : Program)
    (hbody : Triple (PairFrame z a (mixedTranscriptBase base b source flag constant) X Y)
      body (PairFrame z a (mixedTranscriptBase base b source flag constant) X' Y')) :
    Triple (PairFrame z a base X Y) (transcriptSelectWindow b source flag constant body)
      (PairFrame z a base X' Y') := by
  let selected := mixedTranscriptBase base b source flag constant
  have hstart : Triple (PairFrame z a base X Y)
      (transcriptSelectCompute b source flag constant ++ transcriptSelectExpose flag constant)
      (PairFrame z a selected X Y) := by
    intro s m h
    have hz : s.basis flag=false := (h.2.2 flag hf.1 hf.2).trans hzero
    rw [select_start b source flag constant hn s m hz]
    refine ⟨rfl,?_,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => by
        simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from
          fun he => hf.1 (he ▸ hq)])).trans h.1
    · exact (regValue_congr _ _ _ (fun q hq => by
        simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from
          fun he => hf.2 (he ▸ hq)])).trans h.2.1
    · intro q hqz hqa
      by_cases hq : q=flag
      · subst q
        simp [selected,mixedTranscriptBase,mixedTranscriptBit,writeBit,
          h.2.2 b hb.1 hb.2,h.2.2 source hs.1 hs.2]
      · simpa [selected,mixedTranscriptBase,writeBit,Function.update,hq] using h.2.2 q hqz hqa
  have hfinish : Triple (PairFrame z a selected X' Y')
      (transcriptSelectExpose flag constant ++ transcriptSelectErase b source flag constant)
      (PairFrame z a base X' Y') := by
    intro s m h
    have hd := List.nodup_cons.mp hn
    have hbs : b≠flag := by
      intro he
      exact hd.1 (by simp [he])
    have hsf : source≠flag := by
      simpa using (List.nodup_cons.mp hd.2).1
    have hv : s.basis flag=(if s.basis b then s.basis source else constant) := by
      rw [h.2.2 flag hf.1 hf.2,h.2.2 b hb.1 hb.2,h.2.2 source hs.1 hs.2]
      simp [selected,mixedTranscriptBase,mixedTranscriptBit,writeBit,hbs,hsf]
    rw [transcriptSelect_finish_correct b source flag constant hn s m hv]
    refine ⟨rfl,?_,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => by
        simp [writeBit,Function.update,show q≠flag from fun he => hf.1 (he ▸ hq)])).trans h.1
    · exact (regValue_congr _ _ _ (fun q hq => by
        simp [writeBit,Function.update,show q≠flag from fun he => hf.2 (he ▸ hq)])).trans h.2.1
    · intro q hqz hqa
      by_cases hq : q=flag
      · subst q
        simpa [writeBit] using hzero.symm
      · simpa [selected,mixedTranscriptBase,writeBit,Function.update,hq] using h.2.2 q hqz hqa
  simpa only [transcriptSelectWindow,List.append_assoc] using (hstart.seq hbody).seq hfinish

/-- Two external clean flags surround a forward retained cell. The second
flag is erased first; every measured cleanup is emitted in forward order. -/
def mixedTranscriptFieldCell (w : Nat → Wire) (b g swap effG effS : Wire)
    (inactiveG inactiveS : Bool) : Program :=
  transcriptSelectWindow b g effG inactiveG
    (transcriptSelectWindow b swap effS inactiveS (fusedSharedRetainedCell w effG effS))

/-- All transcript wires are external to the canonical field layout. Only
the two effective flags must also avoid the retained kernel's borrowed sites. -/
structure MixedTranscriptFieldLayout (w : Nat → Wire) (b g swap effG effS : Wire) : Prop where
  shared : (skywalkSharedWires w).Nodup
  controls : (b::g::swap::effG::effS::(skywalkSharedField w).wires).Nodup
  gKernel : effG∉fusedSharedIds.map w
  gUnused : effG∉skywalkSharedUnused w
  sUnused : effS∉skywalkSharedUnused w

namespace MixedTranscriptFieldLayout

theorem outside {w : Nat → Wire} {b g swap effG effS : Wire}
    (h : MixedTranscriptFieldLayout w b g swap effG effS) (q : Wire)
    (hq : q∈[b,g,swap,effG,effS]) : q∉(skywalkSharedField w).wires := by
  intro hm
  have hc := List.nodup_iff_count.mp h.controls q
  have hp := List.count_pos_iff.mpr hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl <;> simp [List.count_cons] at hc <;> omega

end MixedTranscriptFieldLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MixedTranscriptReplay.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- The complete exact divisor-one transcript, computed from the same pure
integer transition as the actual recorded transcript. These are build-time
Boolean gate parameters; there is no approximate or truncated transcript. -/
def mixedTranscriptUnitTrace : List (Bool×Bool) :=
  SkywalkTrace.trace 512 (SkywalkRails.encode false false (1 : Int) (p : Int))

abbrev MixedTranscriptLetter := (Wire×Wire)×(Bool×Bool)

def mixedTranscriptTape (w : Nat → Wire) : List MixedTranscriptLetter :=
  (skywalkSharedTape w).zip mixedTranscriptUnitTrace

def MixedTranscriptReplayLayout (w : Nat → Wire) (b effG effS : Wire)
    (ls : List MixedTranscriptLetter) : Prop :=
  ∀ l∈ls, MixedTranscriptFieldLayout w b l.1.1 l.1.2 effG effS

private theorem mixedTranscript_zip_record (rs : List (Wire×Wire))
    (cs : List (Bool×Bool)) (l : MixedTranscriptLetter) (hl : l∈rs.zip cs) :
    l.1∈rs := by
  induction rs generalizing cs with
  | nil => simp at hl
  | cons r rs ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      simp only [List.zip_cons_cons,List.mem_cons] at hl
      rcases hl with rfl|hl
      · simp
      · exact List.mem_cons_of_mem r (ih cs hl)

theorem mixedTranscriptTape_layout (w : Nat → Wire) (b effG effS : Wire)
    (hl : ∀ r∈skywalkSharedTape w,
      MixedTranscriptFieldLayout w b r.1 r.2 effG effS) :
    MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w) := by
  intro l hm
  exact hl l.1 (mixedTranscript_zip_record _ _ l hm)

def mixedTranscriptControls (base : BasisState) (b : Wire)
    (ls : List MixedTranscriptLetter) : List (Bool×Bool) :=
  ls.map fun l => (mixedTranscriptBit base b l.1.1 l.2.1,
    mixedTranscriptBit base b l.1.2 l.2.2)

theorem mixedTranscriptUnitTrace_length : mixedTranscriptUnitTrace.length=512 :=
  SkywalkTrace.trace_length _ _

theorem mixedTranscriptTape_length (w : Nat → Wire) : (mixedTranscriptTape w).length=512 := by
  simp [mixedTranscriptTape,List.length_zip,skywalkShared_tape_length,
    mixedTranscriptUnitTrace_length]

theorem mixedTranscriptControls_zip (base : BasisState) (b : Wire)
    (rs : List (Wire×Wire)) (cs : List (Bool×Bool)) (hlen : rs.length=cs.length) :
    mixedTranscriptControls base b (rs.zip cs)=
      if base b then skywalkTapeControls base rs else cs := by
  induction rs generalizing cs with
  | nil =>
    cases cs with
    | nil => cases base b <;> rfl
    | cons c cs => simp at hlen
  | cons r rs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have ht : rs.length=cs.length := by simpa using hlen
      change (mixedTranscriptBit base b r.1 c.1,mixedTranscriptBit base b r.2 c.2)::
        mixedTranscriptControls base b (rs.zip cs)=_
      rw [ih cs ht]
      cases hb : base b <;> simp [mixedTranscriptBit,skywalkTapeControls,hb]

theorem mixedTranscriptTape_controls (w : Nat → Wire) (base : BasisState) (b : Wire) :
    mixedTranscriptControls base b (mixedTranscriptTape w)=
      if base b then skywalkTapeControls base (skywalkSharedTape w) else mixedTranscriptUnitTrace := by
  exact mixedTranscriptControls_zip base b _ _
    ((skywalkShared_tape_length w).trans mixedTranscriptUnitTrace_length.symm)

/-- Use the actual denominator when enabled and divisor one otherwise. -/
theorem mixedTranscriptTape_quotient (w : Nat → Wire) (base : BasisState) (b : Wire)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    skywalkPayloadReplay (mixedTranscriptControls base b (mixedTranscriptTape w)) (2*Y,0)=
      (if base b then Y/(x : Fp) else Y,if base b then Y/(x : Fp) else Y) := by
  rw [mixedTranscriptTape_controls]
  cases hb : base b
  · simpa [mixedTranscriptUnitTrace] using
      (SkywalkTrace.quotient512 1 Y (by omega) (by norm_num [p]))
  · simpa only [hb,if_true,hr] using SkywalkTrace.quotient512 x Y hx0 hx

theorem mixedTranscriptTape_product (w : Nat → Wire) (base : BasisState) (b : Wire)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    skywalkPayloadReplayInverse (mixedTranscriptControls base b (mixedTranscriptTape w)) (Y,Y)=
      (2*(if base b then Y*(x : Fp) else Y),0) := by
  rw [mixedTranscriptTape_controls]
  cases hb : base b
  · simpa [mixedTranscriptUnitTrace] using
      (SkywalkTrace.product512 1 Y (by omega) (by norm_num [p]))
  · simpa only [hb,if_true,hr] using SkywalkTrace.product512 x Y hx0 hx

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedTranscriptCell.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField
attribute [local irreducible] centerWord

/-- Balanced words remain in this ABI throughout replay. -/
def balancedTranscriptBody (L : BalancedCircuit.Layout) (swap : Wire) : Program :=
  [.X L.sign] ++ BalancedCircuit.program L ++ [.X L.sign] ++
    swapRegisters swap L.r L.y

structure BalancedTranscriptLayout (L : BalancedCircuit.Layout)
    (b g swap effS : Wire) : Prop where
  widths : L.Widths
  kernel : L.wires.Nodup
  controls : [b,g,swap,L.sign,effS].Nodup
  outside : ∀q∈[b,g,swap,L.sign,effS],q∉L.r ∧ q∉L.y
  scratch : L.sign∉BalancedCircuit.work L ∧ effS∉BalancedCircuit.work L
  swapND : (effS::L.r++L.y).Nodup

private theorem balanced_sign_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sign∉L.r ∧ L.sign∉L.y := by
  have h := BalancedCircuit.flagAway L hn L.sign (by simp)
  exact ⟨fun hm => h (by simp [hm]),fun hm => h (by simp [hm])⟩

private theorem balanced_work_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r ∧ q∉L.y := by
  have nd := BalancedCircuit.allND L hn
  have h := List.nodup_iff_count.mp nd q
  have hw := List.count_pos_iff.mpr hq
  constructor <;> intro hd <;> have hc := List.count_pos_iff.mpr hd
  all_goals
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h hw
    omega

private theorem balanced_sign_work (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sign∉BalancedCircuit.work L := by
  have nd : (L.sign::BalancedCircuit.work L).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
      BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  exact (List.nodup_cons.mp nd).1

private theorem balanced_toggle_view (sign : Wire) (s : State) (m : List Bool) :
    let t := run [.X sign] m s
    t.phase=s.phase ∧ t.basis sign= !s.basis sign ∧
      ∀q,q≠sign → t.basis q=s.basis q := by
  simp only [run]
  refine ⟨True.intro,?_,?_⟩
  · simp only [writeBit,Function.update_self]
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]

/-- The sign-complement wrapper preserves the selected transcript exactly. -/
theorem balancedTranscriptHalf_frame (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (base : BasisState)
    (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      ([.X L.sign]++BalancedCircuit.program L++[.X L.sign])
      (PairFrame L.r L.y base (centerWord ((X+(if base L.sign then Y else -Y))/2))
        (centerWord Y)) := by
  intro s m h
  generalize eu : run [.X L.sign] m s=u
  have first := balanced_toggle_view L.sign s m
  rw [eu] at first
  have sa := balanced_sign_away L hn
  have uv (r : List Wire) (ha : L.sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr r u.basis s.basis (fun q hq =>
      first.2.2 q (fun e => ha (e ▸ hq)))
  have us : u.basis L.sign= !base L.sign := by
    rw [first.2.1,h.2.2 L.sign sa.1 sa.2]
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout hw).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout hw).2.2.1,centerWord_decode]
  have uc : ∀q∈BalancedCircuit.work L,u.basis q=false := by
    intro q hq
    have away := balanced_work_away L hn q hq
    have ns : q≠L.sign := fun e => balanced_sign_work L hn (e ▸ hq)
    exact (first.2.2 q ns).trans ((h.2.2 q away.1 away.2).trans (hc q hq))
  generalize ev : run (BalancedCircuit.program L) m u=v
  have hv := BalancedCircuit.program_correct L hw hn (!base L.sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m us ur uy uc
  rw [ev] at hv
  have vv : regValue L.r v.basis=centerWord ((X+(if base L.sign then Y else -Y))/2) := by
    rw [hv.2.1,centeredFp_signedHalf]
    cases base L.sign <;> simp only [centerWord,Bool.not_false,Bool.not_true,if_true,if_false,Bool.false_eq_true]
  let tail := m.drop (measurementCount (BalancedCircuit.program L))
  generalize et : run [.X L.sign] tail v=t
  have last := balanced_toggle_view L.sign v tail
  rw [et] at last
  have actual : run ([.X L.sign]++BalancedCircuit.program L++[.X L.sign]) m s=t := by
    simp only [List.append_assoc,run_append,run_take]
    simp only [show measurementCount [.X L.sign]=0 from rfl,List.drop_zero,Nat.zero_add,
      measurementCount_append]
    rw [eu,ev]
    exact et
  rw [actual]
  refine ⟨last.1.trans (hv.1.trans first.1),?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq =>
      last.2.2 q (fun e => sa.1 (e ▸ hq)))).trans vv
  · exact (regValue_congr _ _ _ (fun q hq => by
      have qr : q∉L.r := by
        have d := (List.nodup_append'.mp (List.nodup_append'.mp (BalancedCircuit.allND L hn)).2.1).1
        exact fun hr => List.disjoint_left.mp (List.nodup_append'.mp d).2.2 hr hq
      exact (last.2.2 q (fun e => sa.2 (e ▸ hq))).trans (hv.2.2.2 q qr))).trans
      ((uv L.y sa.2).trans h.2.1)
  · intro q qr qy
    by_cases qs : q=L.sign
    · subst q
      rw [last.2.1,hv.2.2.2 L.sign sa.1,us,Bool.not_not]
    · exact (last.2.2 q qs).trans ((hv.2.2.2 q qr).trans
        ((first.2.2 q qs).trans (h.2.2 q qr qy)))

private theorem balancedSwap_frame (r y : List Wire) (c : Wire)
    (hlen : r.length=y.length) (hn : (c::r++y).Nodup)
    (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have hc : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c hc.1 hc.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

theorem balancedTranscriptBody_frame (L : BalancedCircuit.Layout) (effS : Wire)
    (hw : L.Widths) (hn : L.wires.Nodup) (hs : (effS::L.r++L.y).Nodup)
    (base : BasisState) (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      (balancedTranscriptBody L effS)
      (PairFrame L.r L.y base
        (centerWord (skywalkPayloadCell (base L.sign) (base effS) (X,Y)).1)
        (centerWord (skywalkPayloadCell (base L.sign) (base effS) (X,Y)).2)) := by
  have hh := balancedTranscriptHalf_frame L hw hn base hc X Y
  have len := BalancedCleanup.widths L.toLayout hw
  let T := (X+(if base L.sign then Y else -Y))/2
  have sw := balancedSwap_frame L.r L.y effS (len.2.1.trans len.2.2.1.symm) hs
    base (centerWord T) (centerWord Y)
  have view : PairFrame L.r L.y base
      (centerWord (skywalkPayloadCell (base L.sign) (base effS) (X,Y)).1)
      (centerWord (skywalkPayloadCell (base L.sign) (base effS) (X,Y)).2)=
      PairFrame L.r L.y base (if base effS then centerWord Y else centerWord T)
        (if base effS then centerWord T else centerWord Y) := by
    cases e : base effS <;>
      simp only [skywalkPayloadCell,e,Bool.false_eq_true,if_true,if_false,T]
  rw [←view] at sw
  simpa only [balancedTranscriptBody] using hh.seq sw
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedTranscriptReplay.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseTranscriptCell.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField
attribute [local irreducible] centerWord

/-- A fresh measured inverse: undo the recorded swap before the inverse field kernel. -/
def balancedInverseTranscriptBody (L : BalancedCircuit.Layout) (swap : Wire) : Program :=
  swapRegisters swap L.r L.y ++ [.X L.sign] ++ BalancedInverse.program L ++ [.X L.sign]

private theorem inverse_result_word (B : Bool) (X Y : Fp) :
    encodeWord 256 (BalancedInverse.result B (centerFp X) (centerFp Y)) =
      centerWord (2*X-(if B then -Y else Y)) := by
  unfold BalancedInverse.result BalancedField.signedY
  unfold centerWord
  congr 2
  cases B <;>
    simp [Int.cast_sub,Int.cast_mul,Int.cast_neg,centerFp_cast]

private theorem inverse_sign_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sign∉L.r ∧ L.sign∉L.y := by
  have h := BalancedCircuit.flagAway L hn L.sign (by simp)
  exact ⟨fun hm => h (by simp [hm]),fun hm => h (by simp [hm])⟩

private theorem inverse_work_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r ∧ q∉L.y := by
  have nd := BalancedCircuit.allND L hn
  have h := List.nodup_iff_count.mp nd q
  have hw := List.count_pos_iff.mpr hq
  constructor <;> intro hd <;> have hc := List.count_pos_iff.mpr hd
  all_goals
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h hw
    omega

private theorem inverse_sign_work (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sign∉BalancedCircuit.work L := by
  have nd : (L.sign::BalancedCircuit.work L).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
      BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  exact (List.nodup_cons.mp nd).1

private theorem inverse_toggle_view (sign : Wire) (s : State) (m : List Bool) :
    let t := run [.X sign] m s
    t.phase=s.phase ∧ t.basis sign= !s.basis sign ∧
      ∀q,q≠sign → t.basis q=s.basis q := by
  simp only [run]
  refine ⟨True.intro,?_,?_⟩
  · simp only [writeBit,Function.update_self]
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]

/-- The sign-complement wrapper preserves the selected transcript exactly. -/
theorem balancedTranscriptDouble_frame (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (base : BasisState)
    (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      ([.X L.sign]++BalancedInverse.program L++[.X L.sign])
      (PairFrame L.r L.y base (centerWord (2*X+(if base L.sign then -Y else Y)))
        (centerWord Y)) := by
  intro s m h
  generalize eu : run [.X L.sign] m s=u
  have first := inverse_toggle_view L.sign s m
  rw [eu] at first
  have sa := inverse_sign_away L hn
  have uv (r : List Wire) (ha : L.sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr r u.basis s.basis (fun q hq =>
      first.2.2 q (fun e => ha (e ▸ hq)))
  have us : u.basis L.sign= !base L.sign := by
    rw [first.2.1,h.2.2 L.sign sa.1 sa.2]
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout hw).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout hw).2.2.1,centerWord_decode]
  have uc : ∀q∈BalancedCircuit.work L,u.basis q=false := by
    intro q hq
    have away := inverse_work_away L hn q hq
    have ns : q≠L.sign := fun e => inverse_sign_work L hn (e ▸ hq)
    exact (first.2.2 q ns).trans ((h.2.2 q away.1 away.2).trans (hc q hq))
  generalize ev : run (BalancedInverse.program L) m u=v
  have hv := BalancedInverse.program_correct L hw hn (!base L.sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m us ur uy uc
  rw [ev] at hv
  have vv : regValue L.r v.basis=centerWord (2*X+(if base L.sign then -Y else Y)) := by
    rw [hv.2.1,inverse_result_word]
    cases base L.sign <;> simp only [Bool.not_false,Bool.not_true,if_true,if_false,Bool.false_eq_true,sub_eq_add_neg,neg_neg]
  let tail := m.drop (measurementCount (BalancedInverse.program L))
  generalize et : run [.X L.sign] tail v=t
  have last := inverse_toggle_view L.sign v tail
  rw [et] at last
  have actual : run ([.X L.sign]++BalancedInverse.program L++[.X L.sign]) m s=t := by
    simp only [List.append_assoc,run_append,run_take]
    simp only [show measurementCount [.X L.sign]=0 from rfl,List.drop_zero,Nat.zero_add,
      measurementCount_append]
    rw [eu,ev]
    exact et
  rw [actual]
  refine ⟨last.1.trans (hv.1.trans first.1),?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq =>
      last.2.2 q (fun e => sa.1 (e ▸ hq)))).trans vv
  · exact (regValue_congr _ _ _ (fun q hq => by
      have qr : q∉L.r := by
        have d := (List.nodup_append'.mp (List.nodup_append'.mp (BalancedCircuit.allND L hn)).2.1).1
        exact fun hr => List.disjoint_left.mp (List.nodup_append'.mp d).2.2 hr hq
      exact (last.2.2 q (fun e => sa.2 (e ▸ hq))).trans (hv.2.2.2 q qr))).trans
      ((uv L.y sa.2).trans h.2.1)
  · intro q qr qy
    by_cases qs : q=L.sign
    · subst q
      rw [last.2.1,hv.2.2.2 L.sign sa.1,us,Bool.not_not]
    · exact (last.2.2 q qs).trans ((hv.2.2.2 q qr).trans
        ((first.2.2 q qs).trans (h.2.2 q qr qy)))

private theorem inverseSwap_frame (r y : List Wire) (c : Wire)
    (hlen : r.length=y.length) (hn : (c::r++y).Nodup)
    (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have hc : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c hc.1 hc.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

theorem balancedInverseTranscriptBody_frame (L : BalancedCircuit.Layout) (effS : Wire)
    (hw : L.Widths) (hn : L.wires.Nodup) (hs : (effS::L.r++L.y).Nodup)
    (base : BasisState) (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      (balancedInverseTranscriptBody L effS)
      (PairFrame L.r L.y base
        (centerWord (skywalkPayloadUncell (base L.sign) (base effS) (X,Y)).1)
        (centerWord (skywalkPayloadUncell (base L.sign) (base effS) (X,Y)).2)) := by
  have len := BalancedCleanup.widths L.toLayout hw
  have sw := inverseSwap_frame L.r L.y effS (len.2.1.trans len.2.2.1.symm) hs
    base (centerWord X) (centerWord Y)
  let A := if base effS then Y else X
  let B := if base effS then X else Y
  have view : PairFrame L.r L.y base (centerWord A) (centerWord B) =
      PairFrame L.r L.y base (if base effS then centerWord Y else centerWord X)
        (if base effS then centerWord X else centerWord Y) := by
    cases e : base effS <;> simp only [A,B,e,Bool.false_eq_true,if_true,if_false]
  rw [←view] at sw
  have dbl := balancedTranscriptDouble_frame L hw hn base hc A B
  have out : PairFrame L.r L.y base
      (centerWord (skywalkPayloadUncell (base L.sign) (base effS) (X,Y)).1)
      (centerWord (skywalkPayloadUncell (base L.sign) (base effS) (X,Y)).2) =
      PairFrame L.r L.y base (centerWord (2*A+(if base L.sign then -B else B)))
        (centerWord B) := by
    cases e : base effS <;> simp only [skywalkPayloadUncell,A,B,e,Bool.false_eq_true,if_true,if_false]
  rw [out]
  simpa only [balancedInverseTranscriptBody,List.append_assoc] using sw.seq dbl
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseTranscriptReplay.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedTranscriptBoundary.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField

/-- The two boundary conversions reuse scratch, and each restores it. -/
structure BalancedTranscriptBoundary (L : BalancedCircuit.Layout) where
  target : BalancedConvert.Layout
  source : BalancedConvert.Layout
  targetWord : target.word=L.r
  sourceWord : source.word=L.y
  targetWidths : target.Widths
  sourceWidths : source.Widths
  targetND : target.wires.Nodup
  sourceND : source.wires.Nodup
  pairND : (L.r++L.y).Nodup
  targetWorkAway : ∀q∈BalancedConvert.work target,q∉L.r ∧ q∉L.y
  sourceWorkAway : ∀q∈BalancedConvert.work source,q∉L.r ∧ q∉L.y

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseTranscriptBoundary.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedSharedPorts.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The balanced field port borrows terminal-zero mask and padding sites,
and the restored integer carry bank. It does not touch the seed bank. -/
def balancedSharedPorts (w : Nat → Wire) (sign : Wire) : BalancedCircuit.Layout :=
  { r0:=w 2056,rtail:=wireBlock w 2057 254,rmsb:=w 2311,
    ylow:=wireBlock w 770 255,ymsb:=w 1025,carry:=wireBlock w 1540 256,
    sign:=sign,parity:=w 1796,lower:=w 1797,one:=w 1027,
    sourceGuard:=w 765,cout:=w 768,minus:=w 767,plus:=w 766 }

def balancedSharedIds : List Nat :=
  [765,768,767,766,1796,1797,1027,2311,1025,2056]++
    List.range' 2057 254++List.range' 770 255++List.range' 1540 256

theorem balancedSharedIds_nodup : balancedSharedIds.Nodup := by decide

theorem balancedSharedIds_bound (j : Nat) (hj : j∈balancedSharedIds) : j<2314 := by
  simp only [balancedSharedIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj
  omega

theorem balancedSharedPorts_widths (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).Widths := by
  simp [BalancedCircuit.Layout.Widths,BalancedCleanup.Layout.Widths,
    balancedSharedPorts,wireBlock]

theorem balancedSharedPorts_nodup (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hs : sign∉balancedSharedIds.map w) :
    (balancedSharedPorts w sign).wires.Nodup := by
  have mapped : (balancedSharedIds.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkShared_index_inj w hn i j (balancedSharedIds_bound i hi)
        (balancedSharedIds_bound j hj) he
    · exact balancedSharedIds_nodup
  have all : (sign::balancedSharedIds.map w).Nodup := List.nodup_cons.mpr ⟨hs,mapped⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp all q
  simp only [balancedSharedPorts,balancedSharedIds,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,wireBlock,List.map_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem balancedSharedPorts_y (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).y=wireBlock w 770 256 := by
  have a := wireBlock_append w 770 255 1
  have one : wireBlock w 1025 1=[w 1025] := by simp [wireBlock,List.range']
  change wireBlock w 770 255++[w 1025]=wireBlock w 770 256
  simpa only [Nat.reduceAdd,one] using a

theorem balancedSharedPorts_r (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).r=wireBlock w 2056 256 := by
  have a := wireBlock_append w 2056 1 254
  have b := wireBlock_append w 2056 255 1
  have one (s : Nat) : wireBlock w s 1=[w s] := by simp [wireBlock,List.range']
  rw [one] at a b
  have a0 : [w 2056]++wireBlock w 2057 254=wireBlock w 2056 255 := by simpa using a
  change (w 2056::wireBlock w 2057 254)++[w 2311]=_
  rw [show w 2056::wireBlock w 2057 254=[w 2056]++wireBlock w 2057 254 from rfl,a0]
  simpa using b

theorem balancedSharedPorts_support (w : Nat → Wire) (sign : Wire) :
    wires (BalancedCircuit.program (balancedSharedPorts w sign)) ⊆
      (balancedSharedPorts w sign).wires.toFinset :=
  BalancedCircuit.support _ (balancedSharedPorts_widths w sign)

private def balancedWorkIds : List Nat :=
  [765,768,767,766,1796,1797,1027]++List.range' 1540 256

private def availableWorkIds : List Nat :=
  List.range' 1540 257++List.range' 1798 256++[1797]++List.range' 512 257++
    [2313,769,1027,2054,2055]

private theorem balancedWorkIds_subset : balancedWorkIds⊆availableWorkIds := by decide

/-- All temporary balanced sites were proved zero by the existing terminal
clear/field-work interface, including the explicitly borrowed padding bit. -/
theorem balancedSharedPorts_work_subset (w : Nat → Wire) (sign : Wire) :
    BalancedCircuit.work (balancedSharedPorts w sign) ⊆
      (skywalkSharedField w).work++skywalkSharedUnused w := by
  have used : BalancedCircuit.work (balancedSharedPorts w sign)=balancedWorkIds.map w := by
    simp [BalancedCircuit.work,balancedSharedPorts,balancedWorkIds,wireBlock]
  have available : (skywalkSharedField w).work++skywalkSharedUnused w=availableWorkIds.map w := by
    simp [skywalkSharedField,skywalkSharedUnused,ModInPlaceLayout.work,
      ModAddCoreLayout.work,availableWorkIds,wireBlock,List.map_append,List.append_assoc]
  rw [used,available]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨j,balancedWorkIds_subset hj,rfl⟩

theorem balancedSharedPorts_clean (w : Nat → Wire) (sign : Wire) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) :
    ∀q∈BalancedCircuit.work (balancedSharedPorts w sign),base q=false := by
  intro q hq
  have h := balancedSharedPorts_work_subset w sign hq
  rcases List.mem_append.mp h with h|h
  · exact (regValue_zero _ _).mp hw q h
  · exact (regValue_zero _ _).mp hu q h

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedSharedLayoutBoundary.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Boundary conversion borrows the first 255 restored carry sites. -/
def balancedSharedTargetConvert (w : Nat → Wire) : BalancedConvert.Layout :=
  { low:=wireBlock w 2056 255,msb:=w 2311,carry:=wireBlock w 1540 255,
    cin:=w 1797,one:=w 1027,flag:=w 1796 }

def balancedSharedSourceConvert (w : Nat → Wire) : BalancedConvert.Layout :=
  { low:=wireBlock w 770 255,msb:=w 1025,carry:=wireBlock w 1540 255,
    cin:=w 1797,one:=w 1027,flag:=w 1796 }

/-- Map a finite allocation within the original shared bank. -/
theorem balancedSharedLayout_mapND (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (ids : List Nat)
    (hd : ids.Nodup) (hb : ∀j∈ids,j<2314) : (ids.map w).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj he
    exact skywalkShared_index_inj w hn i j (hb i hi) (hb j hj) he
  · exact hd

/-- Every ID allocation in the shared bank is a subset of that bank. -/
theorem balancedSharedLayout_mapSubset (w : Nat → Wire) (ids : List Nat)
    (hb : ∀j∈ids,j<2314) : ids.map w ⊆ skywalkSharedWires w := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
  exact ⟨j,by have h := hb j hj; omega,rfl⟩

private def targetIds : List Nat :=
  [1797,1027,1796,2311]++List.range' 2056 255++List.range' 1540 255
private def sourceIds : List Nat :=
  [1797,1027,1796,1025]++List.range' 770 255++List.range' 1540 255
private def pairIds : List Nat := List.range' 2056 256++List.range' 770 256
private def workIds : List Nat := [1796,1797,1027]++List.range' 1540 255
private def kernelWorkIds : List Nat :=
  [765,768,767,766,1796,1797,1027]++List.range' 1540 256

private theorem targetIdsND : targetIds.Nodup := by decide
private theorem sourceIdsND : sourceIds.Nodup := by decide
private theorem workPairIdsND : (workIds++pairIds).Nodup := by decide
private theorem workIds_kernel : workIds ⊆ kernelWorkIds := by decide
private theorem allIds_bound (j : Nat) :
    j∈targetIds ∨ j∈sourceIds ∨ j∈workIds++pairIds → j<2314 := by
  simp only [targetIds,sourceIds,workIds,pairIds,List.mem_append,List.mem_cons,
    List.not_mem_nil,List.mem_range'_1,or_false]
  omega

private theorem targetWires (w : Nat → Wire) :
    (balancedSharedTargetConvert w).wires=targetIds.map w := by
  simp [balancedSharedTargetConvert,BalancedConvert.Layout.wires,targetIds,wireBlock]
private theorem sourceWires (w : Nat → Wire) :
    (balancedSharedSourceConvert w).wires=sourceIds.map w := by
  simp [balancedSharedSourceConvert,BalancedConvert.Layout.wires,sourceIds,wireBlock]
private theorem convertWork (w : Nat → Wire) :
    BalancedConvert.work (balancedSharedTargetConvert w)=workIds.map w ∧
    BalancedConvert.work (balancedSharedSourceConvert w)=workIds.map w := by
  simp [balancedSharedTargetConvert,balancedSharedSourceConvert,BalancedConvert.work,
    BalancedConvert.scratch,workIds,wireBlock]
private theorem pairWires (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y=pairIds.map w := by
  rw [balancedSharedPorts_r,balancedSharedPorts_y]
  simp [pairIds,wireBlock]

theorem balancedSharedTargetConvert_widths (w : Nat → Wire) :
    (balancedSharedTargetConvert w).Widths := by
  simp [BalancedConvert.Layout.Widths,balancedSharedTargetConvert,wireBlock]
theorem balancedSharedSourceConvert_widths (w : Nat → Wire) :
    (balancedSharedSourceConvert w).Widths := by
  simp [BalancedConvert.Layout.Widths,balancedSharedSourceConvert,wireBlock]

theorem balancedSharedTargetConvert_word (w : Nat → Wire) (sign : Wire) :
    (balancedSharedTargetConvert w).word=(balancedSharedPorts w sign).r := by
  rw [balancedSharedPorts_r]
  have h := wireBlock_append w 2056 255 1
  have one : wireBlock w 2311 1=[w 2311] := by simp [wireBlock,List.range']
  change wireBlock w 2056 255++[w 2311]=wireBlock w 2056 256
  simpa only [Nat.reduceAdd,one] using h

theorem balancedSharedSourceConvert_word (w : Nat → Wire) (sign : Wire) :
    (balancedSharedSourceConvert w).word=(balancedSharedPorts w sign).y := rfl

theorem balancedSharedTargetConvert_nodup (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    (balancedSharedTargetConvert w).wires.Nodup := by
  rw [targetWires]
  exact balancedSharedLayout_mapND w hn targetIds targetIdsND
    (fun j hj => allIds_bound j (Or.inl hj))
theorem balancedSharedSourceConvert_nodup (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    (balancedSharedSourceConvert w).wires.Nodup := by
  rw [sourceWires]
  exact balancedSharedLayout_mapND w hn sourceIds sourceIdsND
    (fun j hj => allIds_bound j (Or.inr (Or.inl hj)))

theorem balancedSharedLayout_pairND (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    ((balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup := by
  have h := balancedSharedLayout_mapND w hn (workIds++pairIds) workPairIdsND
    (fun j hj => allIds_bound j (Or.inr (Or.inr hj)))
  rw [List.map_append] at h
  rw [pairWires]
  exact (List.nodup_append'.mp h).2.1

private theorem workAway (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (q : Wire) (hq : q∈workIds.map w) :
    q∉(balancedSharedPorts w sign).r ∧ q∉(balancedSharedPorts w sign).y := by
  have h := balancedSharedLayout_mapND w hn (workIds++pairIds) workPairIdsND
    (fun j hj => allIds_bound j (Or.inr (Or.inr hj)))
  rw [List.map_append] at h
  have dis := List.disjoint_left.mp (List.nodup_append'.mp h).2.2 hq
  rw [←pairWires w sign] at dis
  exact ⟨fun hr => dis (List.mem_append_left _ hr),
    fun hy => dis (List.mem_append_right _ hy)⟩

/-- Concrete entry and exit converters require no additional physical sites. -/
def balancedSharedBoundary (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    BalancedTranscriptBoundary (balancedSharedPorts w sign) where
  target := balancedSharedTargetConvert w
  source := balancedSharedSourceConvert w
  targetWord := balancedSharedTargetConvert_word w sign
  sourceWord := balancedSharedSourceConvert_word w sign
  targetWidths := balancedSharedTargetConvert_widths w
  sourceWidths := balancedSharedSourceConvert_widths w
  targetND := balancedSharedTargetConvert_nodup w hn
  sourceND := balancedSharedSourceConvert_nodup w hn
  pairND := balancedSharedLayout_pairND w sign hn
  targetWorkAway := by
    intro q hq
    rw [(convertWork w).1] at hq
    exact workAway w sign hn q hq
  sourceWorkAway := by
    intro q hq
    rw [(convertWork w).2] at hq
    exact workAway w sign hn q hq

theorem balancedSharedBoundary_work_subset (w : Nat → Wire) (sign : Wire) :
    BalancedConvert.work (balancedSharedTargetConvert w) ⊆
      BalancedCircuit.work (balancedSharedPorts w sign) ∧
    BalancedConvert.work (balancedSharedSourceConvert w) ⊆
      BalancedCircuit.work (balancedSharedPorts w sign) := by
  have hk : BalancedCircuit.work (balancedSharedPorts w sign)=kernelWorkIds.map w := by
    simp [BalancedCircuit.work,balancedSharedPorts,kernelWorkIds,wireBlock]
  rw [(convertWork w).1,(convertWork w).2,hk]
  have hs : workIds.map w ⊆ kernelWorkIds.map w := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    exact List.mem_map.mpr ⟨j,workIds_kernel hj,rfl⟩
  exact ⟨hs,hs⟩

theorem balancedSharedBoundary_clean (w : Nat → Wire) (sign : Wire) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) :
    (∀q∈BalancedConvert.work (balancedSharedTargetConvert w),base q=false) ∧
    (∀q∈BalancedConvert.work (balancedSharedSourceConvert w),base q=false) := by
  have hc := balancedSharedPorts_clean w sign base hw hu
  have hs := balancedSharedBoundary_work_subset w sign
  exact ⟨fun q hq => hc q (hs.1 hq),fun q hq => hc q (hs.2 hq)⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedSharedLayoutTranscript.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private def fieldAvailableIds : List Nat :=
  List.range' 770 257++List.range' 2056 256++[2312]++List.range' 1540 257++
    List.range' 1798 256++[1797]++List.range' 512 257++[2313]++[769,1027,2054,2055]
private def portWorkIds : List Nat :=
  [765,768,767,766,1796,1797,1027]++List.range' 1540 256

theorem balancedSharedLayout_pair_subset_field (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y ⊆
      (skywalkSharedField w).wires := by
  intro q hq
  rw [balancedSharedPorts_r,balancedSharedPorts_y] at hq
  have ay := wireBlock_append w 770 256 1
  have hy : wireBlock w 770 257=wireBlock w 770 256++wireBlock w 1026 1 := by
    simpa only [Nat.reduceAdd] using ay.symm
  simp only [List.mem_append] at hq
  rcases hq with hq|hq
  · simp only [ModInPlaceLayout.wires,ModInPlaceLayout.z,ModAddCoreLayout.z,
      skywalkSharedField,List.mem_append,List.mem_cons,List.not_mem_nil]
    tauto
  · simp only [ModInPlaceLayout.wires,skywalkSharedField,hy,List.mem_append]
    tauto

theorem balancedSharedLayout_work_subset_shared (w : Nat → Wire) (sign : Wire) :
    BalancedCircuit.work (balancedSharedPorts w sign) ⊆ skywalkSharedWires w := by
  have he : BalancedCircuit.work (balancedSharedPorts w sign)=portWorkIds.map w := by
    simp [BalancedCircuit.work,balancedSharedPorts,portWorkIds,wireBlock]
  rw [he]
  apply balancedSharedLayout_mapSubset
  intro j hj
  simp only [portWorkIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj
  omega

/-- The ordinary mixed layout gives the five distinct controls and keeps
all of them outside the low-word data ports. Only the two selected flags
need the stronger exclusion from the entire original shared bank. -/
theorem balancedSharedTranscriptLayout (w : Nat → Wire) (b g swap effG effS : Wire)
    (hf : MixedTranscriptFieldLayout w b g swap effG effS)
    (hg : effG∉skywalkSharedWires w) (hs : effS∉skywalkSharedWires w) :
    BalancedTranscriptLayout (balancedSharedPorts w effG) b g swap effS := by
  have gIds : effG∉balancedSharedIds.map w := by
    intro hm
    exact hg (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound hm)
  have outside : ∀q∈[b,g,swap,effG,effS],
      q∉(balancedSharedPorts w effG).r ∧ q∉(balancedSharedPorts w effG).y := by
    intro q hq
    have ho := hf.outside q hq
    have hp := balancedSharedLayout_pair_subset_field w effG
    exact ⟨fun hm => ho (hp (List.mem_append_left _ hm)),
      fun hm => ho (hp (List.mem_append_right _ hm))⟩
  refine ⟨balancedSharedPorts_widths w effG,
    balancedSharedPorts_nodup w effG hf.shared gIds,?_,outside,?_,?_⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hf.controls q
    simp only [balancedSharedPorts,List.count_cons,List.count_nil] at h ⊢
    omega
  · exact ⟨fun hm => hg (balancedSharedLayout_work_subset_shared w effG hm),
      fun hm => hs (balancedSharedLayout_work_subset_shared w effG hm)⟩
  · apply List.nodup_cons.mpr
    refine ⟨?_,balancedSharedLayout_pairND w effG hf.shared⟩
    intro hm
    rcases List.mem_append.mp hm with hm|hm
    · exact (outside effS (by simp)).1 hm
    · exact (outside effS (by simp)).2 hm

/-- Direct arithmetic's existing outside-bank condition is sufficient. -/
theorem balancedSharedTranscriptLayout_direct (w : Nat → Wire) (b g swap effG effS : Wire)
    (hf : MixedTranscriptFieldLayout w b g swap effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    BalancedTranscriptLayout (balancedSharedPorts w effG) b g swap effS :=
  balancedSharedTranscriptLayout w b g swap effG effS hf
    (ho effG (by simp)) (ho effS (by simp))

end ECDSAAdd.Arithmetic
end
