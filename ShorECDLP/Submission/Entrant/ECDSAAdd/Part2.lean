-- Vendored from ECDSAAdd (ecdsa.fail Lean challenge), Apache-2.0, Copyright 2026 Runzhou Tao, Anirudh and ECDSAAdd contributors; 346 source modules at c3f340a (listed in MODULES.txt), concatenated. Changes: module paths, expanded notation, private-name renames; declarations unreachable from the ShorECDLP judge roots (no kernel or elaborator reference) removed in the 2026-11-11 dead-code compaction, `-- source:` markers kept.
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part1
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.ZMod.Basic

-- source: ECDSAAdd/Arithmetic/BalancedInverseSharedReplay.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedSharedLayoutReplay.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedSharedEmission.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedSharedFraming.lean
noncomputable section

set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic

private theorem bounded_high (M low value : Nat) (bit : Bool)
    (h : low+M*bit.toNat=value) (hv : value<M) : low=value ∧ bit=false := by
  cases bit <;> simp at h ⊢ <;> omega

/-- A canonical field value in a 257-bit word has a zero extension bit. -/
theorem balancedCanonical_high_zero (low : List Wire) (high : Wire) (base : BasisState)
    (value : Nat) (hv : value<2^low.length) (he : regValue (low++[high]) base=value) :
    regValue low base=value ∧ base high=false := by
  have h := (regValue_append low [high] base).symm.trans he
  have b : regValue [high] base=(base high).toNat := by
    cases hb : base high <;> simp [regValue,hb]
  rw [b] at h
  exact bounded_high _ _ _ _ h hv

/-- Narrow the two data ports while retaining the extension bits in the
caller frame. This is a register identity, independent of input sampling. -/
theorem balancedPair_narrow (r y : List Wire) (rh yh : Wire) (base st : BasisState)
    (X Y : Nat) (hx : X<2^r.length) (hy : Y<2^y.length)
    (h : PairFrame (r++[rh]) (y++[yh]) base X Y st)
    (hbaseR : base rh=false) (hbaseY : base yh=false) : PairFrame r y base X Y st := by
  have vr := balancedCanonical_high_zero r rh st X hx h.1
  have vy := balancedCanonical_high_zero y yh st Y hy h.2.1
  refine ⟨vr.1,vy.1,?_⟩
  intro q hr hy
  by_cases er : q=rh
  · subst q
    exact vr.2.trans hbaseR.symm
  by_cases ey : q=yh
  · subst q
    exact vy.2.trans hbaseY.symm
  exact h.2.2 q (by simp [hr,er]) (by simp [hy,ey])

/-- Extend a verified low-word pair result using the preserved zero high
sites. Both sites must lie outside the two mutable 256-bit words. -/
theorem balancedPair_widen (r y : List Wire) (rh yh : Wire) (base st : BasisState)
    (X Y : Nat) (h : PairFrame r y base X Y st)
    (hr : rh∉r ∧ rh∉y) (hy : yh∉r ∧ yh∉y)
    (hbaseR : base rh=false) (hbaseY : base yh=false) :
    PairFrame (r++[rh]) (y++[yh]) base X Y st := by
  have er : st rh=false := (h.2.2 rh hr.1 hr.2).trans hbaseR
  have ey : st yh=false := (h.2.2 yh hy.1 hy.2).trans hbaseY
  refine ⟨?_,?_,?_⟩
  · rw [regValue_append,h.1]
    simp [regValue,er]
  · rw [regValue_append,h.2.1]
    simp [regValue,ey]
  · intro q hqr hqy
    exact h.2.2 q (fun hq => hqr (List.mem_append_left _ hq))
      (fun hq => hqy (List.mem_append_left _ hq))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedSharedDivisionBridge.lean
noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
open Secp256k1

private theorem index_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i offset count : Nat) (hi : i < 2314) (hb : offset + count ≤ 2314)
    (hs : i < offset ∨ offset + count ≤ i) : w i ∉ wireBlock w offset count := by
  intro hm
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hm
  have hj' : offset ≤ j ∧ j < offset + count := by simpa only [List.mem_range'_1] using hj
  have eq := skywalkShared_index_inj w hn j i (by omega) hi he
  omega

theorem balancedSharedDivision_high_outside (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    (w 2312∉wireBlock w 2056 256 ∧ w 2312∉wireBlock w 770 256) ∧
    (w 1026∉wireBlock w 2056 256 ∧ w 1026∉wireBlock w 770 256) := by
  constructor <;> constructor <;> apply index_outside w hn <;> omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseSharedMultiplicationReplay.lean
noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic

open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BorrowedSkywalkUnaryLayout.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Unary arithmetic borrows the cleared mask and integer carry. The mask
field is a ghost of the old clean bank; actual unary gates never touch it. -/
def borrowedSkywalkUnary (w : Nat → Wire) : ModUnaryLayout :=
  { low:=wireBlock w 2056 256,high:=w 2312,constant:=wireBlock w 512 257,
    carry:=wireBlock w 1540 256,cin:=w 1797,mask:=wireBlock w 1798 257,flag:=w 769 }

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BorrowedSkywalkUnaryClean.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BorrowedSkywalkUnaryFrames.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseSharedMultiplication.lean
noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroAdder.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- The Cuccaro in-place majority.  The carry is written into `a`, so no
per-bit carry register is allocated. -/
def cuccaroMaj (a b cin : Wire) : Program := [.CX a b,.CX a cin,.CCX b cin a]

/-- Unmajority-and-add: restore `a` and `cin`, and write the sum bit to `b`. -/
def cuccaroUma (a b cin : Wire) : Program := [.CCX b cin a,.CX a cin,.CX cin b]

/-- Fixed-width in-place addition `b += a + cin (mod 2^n)` using the input
word itself for the carry ladder and no work register. -/
def cuccaroAdd : List Wire → List Wire → Wire → Program
  | [], [], _ => []
  | [a], [b], cin => [.CX a b,.CX cin b]
  | a::a'::as, b::b'::bs, cin =>
      cuccaroMaj a b cin ++ (cuccaroAdd (a'::as) (b'::bs) a ++ cuccaroUma a b cin)
  | _, _, _ => []

@[simp] theorem cuccaroMaj_measurementCount (a b cin : Wire) :
    measurementCount (cuccaroMaj a b cin)=0 := rfl

@[simp] theorem cuccaroUma_measurementCount (a b cin : Wire) :
    measurementCount (cuccaroUma a b cin)=0 := rfl

@[simp] theorem cuccaroAdd_measurementCount (a b : List Wire) (cin : Wire) :
    measurementCount (cuccaroAdd a b cin)=0 := by
  induction b generalizing a cin with
  | nil =>
    cases a with
    | nil => rfl
    | cons x xs => cases xs <;> rfl
  | cons y ys ih =>
    cases a with
    | nil => rfl
    | cons x xs =>
      cases ys with
      | nil => cases xs <;> rfl
      | cons y' ys' =>
        cases xs with
        | nil => rfl
        | cons x' xs' => simp [cuccaroAdd,ih]

theorem cuccaroAdd_counts (a b : List Wire) (cin : Wire) (hlen : a.length=b.length) :
    toffoliCount (cuccaroAdd a b cin)=2*(b.length-1) ∧
      measurementCount (cuccaroAdd a b cin)=0 := by
  induction b generalizing a cin with
  | nil =>
    have ha : a=[] := List.eq_nil_of_length_eq_zero hlen
    subst a
    simp [cuccaroAdd,toffoliCount,measurementCount]
  | cons y ys ih =>
    cases a with
    | nil => simp at hlen
    | cons x xs =>
      cases ys with
      | nil =>
        have hx : xs=[] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst xs
        simp [cuccaroAdd,toffoliCount,measurementCount]
      | cons y' ys' =>
        cases xs with
        | nil => simp at hlen
        | cons x' xs' =>
          have h := ih (x'::xs') x (by simpa using hlen)
          simp [cuccaroAdd,cuccaroMaj,cuccaroUma,toffoliCount,measurementCount,h]
          omega

theorem cuccaroAdd_wires_subset (a b : List Wire) (cin : Wire) :
    wires (cuccaroAdd a b cin)⊆(cin::a++b).toFinset := by
  induction a generalizing b cin with
  | nil => cases b <;> simp [cuccaroAdd,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases b with
      | nil => simp [cuccaroAdd,wires]
      | cons y ys => cases ys <;> simp [cuccaroAdd,wires,Instr.wires]
    | cons x' xs' =>
      cases b with
      | nil => simp [cuccaroAdd,wires]
      | cons y ys =>
        cases ys with
        | nil => simp [cuccaroAdd,wires]
        | cons y' ys' =>
          intro q hq
          simp only [cuccaroAdd,wires_append,Finset.mem_union] at hq
          have hm : wires (cuccaroMaj x y cin)⊆{x,y,cin} := by
            intro w hw; simp [cuccaroMaj,wires,Instr.wires] at hw ⊢; tauto
          have hu : wires (cuccaroUma x y cin)⊆{x,y,cin} := by
            intro w hw; simp [cuccaroUma,wires,Instr.wires] at hw ⊢; tauto
          rcases hq with hq|(hq|hq)
          · have h := hm hq
            simp only [Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,
              List.mem_cons,List.mem_append] at h ⊢
            tauto
          · have h := ih (y'::ys') x hq
            simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
            tauto
          · have h := hu hq
            simp only [Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,
              List.mem_cons,List.mem_append] at h ⊢
            tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroMod.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- One-work-register modular arithmetic.  The source, target and work words
are widened by one bit; `flag` is used only by subtraction. -/
structure CuccaroModLayout where
  a : List Wire
  low : List Wire
  high : Wire
  work : List Wire
  workHigh : Wire
  cin : Wire
  flag : Wire

namespace CuccaroModLayout

end CuccaroModLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroModProof.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroNormalize.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

structure CuccaroNormalizeLayout where
  src : List Wire
  high : Wire
  work : List Wire
  workHigh : Wire
  cin : Wire
  flag : Wire

namespace CuccaroNormalizeLayout

end CuccaroNormalizeLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/Square.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- An m-bit natural has a square fitting in 2m bits, including the empty word. -/
theorem square_bound (X m : Nat) (hX : X < 2^m) : X^2 < 2^(2*m) := by
  have hh : X * X < 2^m * 2^m := Nat.mul_self_lt_mul_self hX
  simpa [pow_two, ← Nat.pow_add, ← two_mul] using hh

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/TriangularSquare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/TriangularSquareProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 固定来源及工作区，只允许目标寄存器改变。 -/
def SquareFrame (dst : List Wire) (base : BasisState) (V : Nat) (s : BasisState) : Prop :=
  regValue dst s=V ∧ ∀ w,w∉dst → s w=base w

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/TriangularSquareResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/TriangularSquareSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaratsubaSquare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Integer-square layout. All fields denote disjoint physical registers. -/
structure KaratsubaSquareLayout where
  low : List Wire
  high : List Wire
  a : List Wire
  d : List Wire
  c : List Wire
  z : List Wire
  sum : List Wire
  pad : List Wire
  mask : List Wire
  carry : List Wire
  cin : Wire

namespace KaratsubaSquareLayout

end KaratsubaSquareLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaratsubaSquareResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace KaratsubaSquareLayout

end KaratsubaSquareLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaratsubaSquareProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedTriangularSquare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Complement every target exactly when `c` is false, preserving `c`.
The per-target form keeps its all-state semantics easy to expose to Lean. -/
def xorWhenFalse (c : Wire) : List Wire → Program
  | [] => []
  | y::ys => [.X y, .CX c y] ++ xorWhenFalse c ys

/-- One exact signed triangular row.

The ordinary ripple sees `c` as its carry-in.  The Clifford frames turn it
into the signed contribution used by the square identity, avoiding a
controlled copy of the quantum addend. -/
def signedSquareRow (c : Wire) (xs dst pad carry : List Wire) : Program :=
  xorWhenFalse c (dst.take xs.length) ++
    addInPlace (xs ++ pad.take 1) dst (carry.take xs.length) c ++
    xorWhenFalse c dst

/-- Independent measured inverse of `signedSquareRow`; no measurement stream
is ever replayed backwards. -/
def signedSquareRowClear (c : Wire) (xs dst pad carry : List Wire) : Program :=
  xorWhenFalse c dst ++ (notRegister dst ++
    (addInPlace (xs ++ pad.take 1) dst (carry.take xs.length) c ++
      (notRegister dst ++ xorWhenFalse c (dst.take xs.length))))

/-- Low-to-high signed rows.  At recursion depth `i`, `dst` begins at product
bit `2i`; the active row is bits `2i+1 .. i+m`. -/
def signedSquareRows : List Wire → List Wire → List Wire → List Wire → Program
  | [], _, _, _ => []
  | _::[], _, _, _ => []
  | c::d::tail, dst, pad, carry =>
      signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry ++
        signedSquareRows (d::tail) (dst.drop 2) pad carry

/-- High-to-low independent cleanup of the signed rows. -/
def signedSquareRowsClear : List Wire → List Wire → List Wire → List Wire → Program
  | [], _, _, _ => []
  | _::[], _, _, _ => []
  | c::d::tail, dst, pad, carry =>
      signedSquareRowsClear (d::tail) (dst.drop 2) pad carry ++
        signedSquareRowClear c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry

/-- Copy the most significant input bit into the most significant product bit. -/
def signedSquareTop : List Wire → List Wire → Program
  | [], _ => []
  | [x], _::z::_ => [.CX x z]
  | _::x::xs, _::_::dst => signedSquareTop (x::xs) dst
  | _, _ => []

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedTriangularSquareResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

@[simp] theorem xorWhenFalse_toffoliCount (c : Wire) (ys : List Wire) :
    toffoliCount (xorWhenFalse c ys)=0 := by
  induction ys <;> simp_all [xorWhenFalse,toffoliCount]

@[simp] theorem xorWhenFalse_measurementCount (c : Wire) (ys : List Wire) :
    measurementCount (xorWhenFalse c ys)=0 := by
  induction ys <;> simp_all [xorWhenFalse,measurementCount]

theorem signedSquareRow_counts (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    toffoliCount (signedSquareRow c xs dst pad carry)=xs.length ∧
      measurementCount (signedSquareRow c xs dst pad carry)=xs.length := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have hk : (carry.take xs.length).length+1=dst.length := by simp [hd,hc]
  have h := addInPlace_counts (xs++pad.take 1) dst (carry.take xs.length) c hs hk
  simp [signedSquareRow,toffoliCount_append,measurementCount_append,h.1,h.2]
  omega

theorem signedSquareRowClear_counts (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    toffoliCount (signedSquareRowClear c xs dst pad carry)=xs.length ∧
      measurementCount (signedSquareRowClear c xs dst pad carry)=xs.length := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have hk : (carry.take xs.length).length+1=dst.length := by simp [hd,hc]
  have h := addInPlace_counts (xs++pad.take 1) dst (carry.take xs.length) c hs hk
  simp [signedSquareRowClear,toffoliCount_append,measurementCount_append,h.1,h.2,
    (notRegister_counts dst).1,(notRegister_counts dst).2]
  omega

def signedSquareRowsCount : Nat → Nat
  | 0 => 0
  | n+1 => n+signedSquareRowsCount n

theorem signedSquareRows_counts (xs dst pad carry : List Wire)
    (hd : dst.length=2*xs.length) (hp : xs.length≤1 ∨ 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    (toffoliCount (signedSquareRows xs dst pad carry)=signedSquareRowsCount xs.length ∧
      measurementCount (signedSquareRows xs dst pad carry)=signedSquareRowsCount xs.length) ∧
    (toffoliCount (signedSquareRowsClear xs dst pad carry)=signedSquareRowsCount xs.length ∧
      measurementCount (signedSquareRowsClear xs dst pad carry)=signedSquareRowsCount xs.length) := by
  induction xs generalizing dst with
  | nil => simp [signedSquareRows,signedSquareRowsClear,signedSquareRowsCount,toffoliCount,measurementCount]
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedSquareRows,signedSquareRowsClear,signedSquareRowsCount,toffoliCount,measurementCount]
    | cons d tail =>
      simp only [List.length_cons] at hd hp hc
      have hcap : (d::tail).length+1≤(dst.drop 1).length := by
        simp
        omega
      have hrow : ((dst.drop 1).take ((d::tail).length+1)).length=(d::tail).length+1 := by
        exact List.length_take_of_le hcap
      have hnext : (dst.drop 2).length=2*(d::tail).length := by
        simp [List.length_drop]
        omega
      have hpad : 1≤pad.length := by rcases hp with hp|hp <;> omega
      have hcarry : (d::tail).length≤carry.length := by
        change tail.length+1≤carry.length
        omega
      have hr := signedSquareRow_counts c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry hrow hpad hcarry
      have hrc := signedSquareRowClear_counts c (d::tail)
        ((dst.drop 1).take ((d::tail).length+1)) pad carry hrow hpad hcarry
      have hrecCarry : (d::tail).length-1≤carry.length := by omega
      have hi := ih (dst.drop 2) hnext (Or.inr hpad) hrecCarry
      constructor
      · constructor
        · rw [signedSquareRows,toffoliCount_append,hr.1,hi.1.1]
          simp [signedSquareRowsCount]
        · rw [signedSquareRows,measurementCount_append,hr.2,hi.1.2]
          simp [signedSquareRowsCount]
      · constructor
        · rw [signedSquareRowsClear,toffoliCount_append,hi.2.1,hrc.1]
          simp [signedSquareRowsCount]
          omega
        · rw [signedSquareRowsClear,measurementCount_append,hi.2.2,hrc.2]
          simp [signedSquareRowsCount]
          omega

@[simp] theorem signedSquareTop_toffoliCount (xs dst : List Wire) :
    toffoliCount (signedSquareTop xs dst)=0 := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,toffoliCount]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,toffoliCount]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,toffoliCount]
        | cons z zs => simp [signedSquareTop,toffoliCount]
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,toffoliCount]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,toffoliCount]
        | cons b tail => simpa [signedSquareTop] using ih tail

@[simp] theorem signedSquareTop_measurementCount (xs dst : List Wire) :
    measurementCount (signedSquareTop xs dst)=0 := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,measurementCount]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,measurementCount]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,measurementCount]
        | cons z zs => simp [signedSquareTop,measurementCount]
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,measurementCount]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,measurementCount]
        | cons b tail => simpa [signedSquareTop] using ih tail

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/SignedSquare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Arithmetic effect of a false-controlled complement/add/complement row.
`M` is the low-half radix and the row word has modulus `2*M`. -/
theorem signed_false_row_value (A S M : Nat) (hM : 0<M)
    (hA : A<2*M) (hS : S<M) :
    2*M-1-((((M-1-A%M)+M*(A/M))+S)%(2*M))=
      (A+M-S)%(2*M) := by
  have hsplit : A%M+M*(A/M)=A := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div A M)
  have hr : A%M<M := Nat.mod_lt A hM
  have hhi : A/M<2 := (Nat.div_lt_iff_lt_mul hM).2 (by simpa [Nat.mul_comm] using hA)
  have hq : A/M=0 ∨ A/M=1 := by
    cases he : A/M with
    | zero => exact Or.inl rfl
    | succ q => exact Or.inr (by omega)
  rcases hq with hq|hq
  · have hP : (M-1-A%M)+M*(A/M)+S<2*M := by rw [hq]; simp; omega
    have hQ : A+M-S<2*M := by rw [← hsplit,hq]; simp; omega
    rw [Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hQ]
    have ha : A=A%M := by rw [hq] at hsplit; simpa using hsplit.symm
    simp only [hq]
    simp only [Nat.mul_zero,Nat.add_zero]
    omega
  · rw [hq] at hsplit
    simp at hsplit
    have ha : A=A%M+M := by omega
    by_cases hs : S≤A%M
    · have hP : (M-1-A%M)+M*(A/M)+S<2*M := by rw [hq]; simp; omega
      have hQ : 2*M≤A+M-S := by omega
      have hQ2 : A+M-S-2*M<2*M := by omega
      rw [Nat.mod_eq_of_lt hP,Nat.mod_eq_sub_mod hQ,Nat.mod_eq_of_lt hQ2]
      simp only [hq]
      simp only [Nat.mul_one]
      omega
    · have hP : 2*M≤(M-1-A%M)+M*(A/M)+S := by rw [hq]; simp; omega
      have hP2 : (M-1-A%M)+M*(A/M)+S-2*M<2*M := by rw [hq]; simp; omega
      have hQ : A+M-S<2*M := by omega
      rw [Nat.mod_eq_sub_mod hP,Nat.mod_eq_of_lt hP2,Nat.mod_eq_of_lt hQ]
      simp only [hq]
      simp only [Nat.mul_one]
      omega

def signedDeltaValue (c : Wire) (xs : List Wire) (base : BasisState) : Nat :=
  if base c then regValue xs base+1 else 2^xs.length-regValue xs base

def signedRowsValue : List Wire → BasisState → Nat
  | [], _ => 0
  | _::[], _ => 0
  | c::d::tail, base =>
      2*signedDeltaValue c (d::tail) base+4*signedRowsValue (d::tail) base

theorem signedRowsValue_congr (xs : List Wire) (s t : BasisState)
    (h : ∀w∈xs,s w=t w) : signedRowsValue xs s=signedRowsValue xs t := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    cases xs with
    | nil => rfl
    | cons d tail =>
      have hc := h c (by simp)
      have hr : regValue (d::tail) s=regValue (d::tail) t :=
        regValue_congr _ _ _ (fun w hw => h w (by simp [hw]))
      have hi := ih (fun w hw => h w (by simp [hw]))
      simp [signedRowsValue,signedDeltaValue,hc,hr,hi]

theorem signedDeltaValue_bound (c : Wire) (xs : List Wire) (base : BasisState) :
    signedDeltaValue c xs base≤2^xs.length := by
  have h := regValue_lt xs base
  simp only [signedDeltaValue]
  split <;> omega

/-- All signed rows fit below the untouched top product bit.  The stronger
subtracted term is what leaves room for an arbitrary clean low-half prefix. -/
theorem signedRowsValue_bound (xs : List Wire) (base : BasisState) (hn : 1≤xs.length) :
    signedRowsValue xs base≤2^(2*xs.length-1)-2^xs.length := by
  induction xs with
  | nil => simp at hn
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedRowsValue]
    | cons d tail =>
      let rest := d::tail
      have hk : 1≤rest.length := by simp [rest]
      have hi := ih hk
      have hd := signedDeltaValue_bound c rest base
      have hp1 : 2^(rest.length+1)=2*2^rest.length := by rw [Nat.pow_succ]; omega
      have he : 2*(rest.length+1)-1=(2*rest.length-1)+2 := by omega
      have hp2 : 2^(2*(rest.length+1)-1)=4*2^(2*rest.length-1) := by
        rw [he,Nat.pow_add]
        norm_num [Nat.mul_comm]
      have hpow : 2^rest.length≤2^(2*rest.length-1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      simp only [signedRowsValue,List.length_cons]
      change 2*signedDeltaValue c rest base+4*signedRowsValue rest base≤
        2^(2*(rest.length+1)-1)-2^(rest.length+1)
      change signedRowsValue rest base≤2^(2*rest.length-1)-2^rest.length at hi
      rw [hp1,hp2]
      omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedTriangularSquareProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

def xorFalseBasis (c : Wire) (ys : List Wire) (s : BasisState) : BasisState :=
  fun w => if w∈ys then s w ^^ !s c else s w

private theorem xorFalseBit_correct (c y : Wire) (hcy : c≠y) (s : State) (m : List Bool) :
    run [.X y,.CX c y] m s=
      ⟨s.phase,writeBit s.basis y (s.basis y ^^ !s.basis c)⟩ := by
  simp [run,writeBit,hcy]

/-- Exact all-state semantics of the Clifford false-controlled complement. -/
theorem xorWhenFalse_correct (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) :
    run (xorWhenFalse c ys) m s=⟨s.phase,xorFalseBasis c ys s.basis⟩ := by
  induction ys generalizing s with
  | nil =>
    apply congrArg (State.mk s.phase)
    funext w
    simp [xorFalseBasis]
  | cons y ys ih =>
    obtain ⟨hy,hys⟩ := List.nodup_cons.mp hnd
    have hcy : c≠y := fun h => hc (by simp [h])
    have hcs : c∉ys := fun h => hc (by simp [h])
    let s1 : State := ⟨s.phase,writeBit s.basis y (s.basis y ^^ !s.basis c)⟩
    rw [xorWhenFalse,run_append]
    simp only [measurementCount,List.take_zero,List.drop_zero]
    rw [xorFalseBit_correct c y hcy s [],
      show (⟨s.phase,writeBit s.basis y (s.basis y ^^ !s.basis c)⟩ : State)=s1 from rfl,
      ih hys hcs s1]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases hwy : w=y
    · subst w
      simp [xorFalseBasis,hy,s1,writeBit]
    · by_cases hws : w∈ys
      · simp [xorFalseBasis,hws,hwy,s1,writeBit,hcy]
      · simp [xorFalseBasis,hws,hwy,s1,writeBit]

theorem xorWhenFalse_phase (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) :
    (run (xorWhenFalse c ys) m s).phase=s.phase := by
  rw [xorWhenFalse_correct c ys hnd hc]

theorem xorWhenFalse_outside (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) (w : Wire) (hw : w∉ys) :
    (run (xorWhenFalse c ys) m s).basis w=s.basis w := by
  rw [xorWhenFalse_correct c ys hnd hc]
  simp [xorFalseBasis,hw]

theorem xorWhenFalse_value (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) :
    regValue ys (run (xorWhenFalse c ys) m s).basis=
      if s.basis c then regValue ys s.basis else 2^ys.length-1-regValue ys s.basis := by
  rw [xorWhenFalse_correct c ys hnd hc]
  by_cases h : s.basis c
  · simp [h]
    apply regValue_congr
    intro w hw
    simp [xorFalseBasis,hw,h]
  · simp [h]
    rw [regValue_congr ys _ (fun w => !s.basis w) (by intro w hw; simp [xorFalseBasis,hw,h]),
      regValue_complement]

private theorem take_value_mod (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.take n) s=regValue r s%2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  rw [h,Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt ?_).symm
  simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s

private theorem drop_value_div (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.drop n) s=regValue r s/2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  have hl : regValue (r.take n) s<2^n := by
    simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [h,Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),Nat.div_eq_of_lt hl,Nat.zero_add]

/-- Complementing a low prefix preserves the high quotient and complements
only the low residue. -/
theorem xorWhenFalse_prefix_value (c : Wire) (dst : List Wire) (k : Nat)
    (hnd : dst.Nodup) (hc : c∉dst) (hk : k≤dst.length) (s : State) (m : List Bool) :
    regValue dst (run (xorWhenFalse c (dst.take k)) m s).basis=
      if s.basis c then regValue dst s.basis
      else (2^k-1-regValue dst s.basis%2^k)+2^k*(regValue dst s.basis/2^k) := by
  let u := run (xorWhenFalse c (dst.take k)) m s
  have htakeN : (dst.take k).Nodup := (List.take_sublist k dst).nodup hnd
  have hctake : c∉dst.take k := fun h => hc (List.mem_of_mem_take h)
  have hlo := xorWhenFalse_value c (dst.take k) htakeN hctake s m
  have hhigh : regValue (dst.drop k) u.basis=regValue (dst.drop k) s.basis := by
    apply regValue_congr
    intro w hw
    apply xorWhenFalse_outside c (dst.take k) htakeN hctake s m
    intro ht
    exact List.disjoint_left.mp (List.disjoint_take_drop hnd (Nat.le_refl k)) ht hw
  have hsplitU := regValue_append (dst.take k) (dst.drop k) u.basis
  have hsplitS := regValue_append (dst.take k) (dst.drop k) s.basis
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hk] at hsplitU hsplitS
  have hlowS := take_value_mod dst k hk s.basis
  have hhighS := drop_value_div dst k hk s.basis
  rw [List.length_take,Nat.min_eq_left hk] at hlo
  change regValue dst u.basis=_
  rw [hsplitU,hhigh,hlo,hlowS,hhighS]
  split
  · exact Nat.mod_add_div (regValue dst s.basis) (2^k)
  · rfl

theorem xorWhenFalse_frame (c : Wire) (dst : List Wire)
    (hnd : (c::dst).Nodup) (base : BasisState) (C : Bool) (A : Nat)
    (hC : base c=C) :
    Triple (SquareFrame dst base A) (xorWhenFalse c dst)
      (SquareFrame dst base (if C then A else 2^dst.length-1-A)) := by
  have hd : dst.Nodup := (List.nodup_cons.mp hnd).2
  have hc : c∉dst := (List.nodup_cons.mp hnd).1
  intro s m h
  have sc : s.basis c=C := (h.2 c hc).trans hC
  have hv := xorWhenFalse_value c dst hd hc s m
  have hp := xorWhenFalse_phase c dst hd hc s m
  refine ⟨hp,?_,?_⟩
  · simpa [sc,h.1] using hv
  · intro w hw
    exact (xorWhenFalse_outside c dst hd hc s m w hw).trans (h.2 w hw)

theorem xorWhenFalse_prefix_frame (c : Wire) (dst : List Wire) (k : Nat)
    (hnd : (c::dst).Nodup) (hk : k≤dst.length) (base : BasisState)
    (C : Bool) (A : Nat) (hC : base c=C) :
    Triple (SquareFrame dst base A) (xorWhenFalse c (dst.take k))
      (SquareFrame dst base (if C then A
        else (2^k-1-A%2^k)+2^k*(A/2^k))) := by
  have hd : dst.Nodup := (List.nodup_cons.mp hnd).2
  have hc : c∉dst := (List.nodup_cons.mp hnd).1
  intro s m h
  have sc : s.basis c=C := (h.2 c hc).trans hC
  have hv := xorWhenFalse_prefix_value c dst k hd hc hk s m
  have htN : (dst.take k).Nodup := (List.take_sublist k dst).nodup hd
  have hct : c∉dst.take k := fun hh => hc (List.mem_of_mem_take hh)
  have hp := xorWhenFalse_phase c (dst.take k) htN hct s m
  refine ⟨hp,?_,?_⟩
  · simpa [sc,h.1] using hv
  · intro w hw
    exact (xorWhenFalse_outside c (dst.take k) htN hct s m w
      (fun hh => hw (List.mem_of_mem_take hh))).trans (h.2 w hw)

/-- Exact ripple-add frame with a live arbitrary carry-in. -/
theorem addInPlace_cin_frame (cin : Wire) (src dst carry : List Wire)
    (hnd : (cin::src++dst++carry).Nodup) (hs : src.length=dst.length)
    (hc : carry.length+1=dst.length) (base : BasisState) (C : Bool)
    (hC : base cin=C) (hk : regValue carry base=0) (V : Nat) :
    Triple (SquareFrame dst base V) (addInPlace src dst carry cin)
      (SquareFrame dst base ((V+regValue src base+C.toNat)%2^dst.length)) := by
  have dis (w : Wire) (hw : w∈cin::src++carry) : w∉dst := by
    intro hdw
    have hn := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hdw
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  intro s m h
  have sv : regValue src s.basis=regValue src base :=
    regValue_congr _ _ _ (fun w hw => h.2 w (dis w (by simp [hw])))
  have kv : regValue carry s.basis=0 :=
    (regValue_congr _ _ _ (fun w hw => h.2 w (dis w (by simp [hw])))).trans hk
  have cv : s.basis cin=C := (h.2 cin (dis cin (by simp))).trans hC
  have runh := addInPlace_correct src dst carry cin hnd hs hc s m
    ((regValue_zero _ _).mp kv)
  refine ⟨runh.1,?_,?_⟩
  · rw [runh.2.2,sv,h.1,cv]
    congr 2
    omega
  · intro w hw
    exact (runh.2.1 w hw).trans (h.2 w hw)

def signedRowValue (C : Bool) (A S k : Nat) : Nat :=
  if C then (A+S+1)%2^(k+1) else (A+2^k-S)%2^(k+1)

/-- One signed row has exact all-record semantics, preserves every non-target
wire, and restores its measured ripple carries. -/
theorem signedSquareRow_frame (c : Wire) (xs dst pad carry : List Wire)
    (hnd : (c::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (base : BasisState) (C : Bool) (hC : base c=C)
    (hz : regValue (pad++carry) base=0) (A : Nat) (hA : A<2^dst.length) :
    Triple (SquareFrame dst base A) (signedSquareRow c xs dst pad carry)
      (SquareFrame dst base (signedRowValue C A (regValue xs base) xs.length)) := by
  let src := xs++pad.take 1
  let cy := carry.take xs.length
  have ndc : (c::dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndadd : (c::src++dst++cy).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    have hp' := (List.take_sublist 1 pad).count_le w
    have hc' := (List.take_sublist xs.length carry).count_le w
    simp only [src,cy,List.count_cons,List.count_append] at h ⊢
    omega
  have hs : src.length=dst.length := by simp [src,hd,hp]
  have hcy : cy.length+1=dst.length := by simp [cy,hc,hd]
  have srcv : regValue src base=regValue xs base := by
    have p0 : regValue (pad.take 1) base=0 := (regValue_zero _ _).mpr
      (fun w hw => (regValue_zero _ _).mp hz w (by simp [List.mem_of_mem_take hw]))
    simp [src,regValue_append,p0]
  have cy0 : regValue cy base=0 := (regValue_zero _ _).mpr
    (fun w hw => (regValue_zero _ _).mp hz w (by simp [List.mem_of_mem_take hw]))
  let P := if C then A else
    (2^xs.length-1-A%2^xs.length)+2^xs.length*(A/2^xs.length)
  let B := (P+regValue src base+C.toNat)%2^dst.length
  have h1 := xorWhenFalse_prefix_frame c dst xs.length ndc (by omega) base C A hC
  have h2 := addInPlace_cin_frame c src dst cy ndadd hs hcy base C hC cy0 P
  have h3 := xorWhenFalse_frame c dst ndc base C B hC
  have comp := h1.seq (h2.seq h3)
  have heq : (if C then B else 2^dst.length-1-B)=
      signedRowValue C A (regValue xs base) xs.length := by
    simp only [P,B,srcv]
    cases C with
    | true => simp [signedRowValue,hd]
    | false =>
      simp only [Bool.false_eq_true,if_false,Bool.toNat_false,Nat.add_zero]
      rw [hd] at hA
      have hS : regValue xs base<2^xs.length := regValue_lt xs base
      have hm : 0<2^xs.length := Nat.two_pow_pos _
      have hA2 : A<2*(2^xs.length) := by simpa [Nat.pow_succ,Nat.mul_comm] using hA
      rw [hd]
      simp only [signedRowValue,Bool.false_eq_true,if_false]
      rw [show 2^(xs.length+1)=2*(2^xs.length) by rw [Nat.pow_succ]; omega]
      exact signed_false_row_value A (regValue xs base) (2^xs.length) hm hA2 hS
  have final := Triple.conseq (fun _ h => h) comp
    (fun _ hpost => by simpa [heq] using hpost)
  simpa [signedSquareRow,src,cy,List.append_assoc] using final

theorem notRegister_frame (dst : List Wire) (hnd : dst.Nodup)
    (base : BasisState) (A : Nat) :
    Triple (SquareFrame dst base A) (notRegister dst)
      (SquareFrame dst base (2^dst.length-1-A)) := by
  intro s m h
  have nr := notRegister_correct dst hnd s m
  rw [nr]
  refine ⟨rfl,?_,?_⟩
  · change regValue dst _=_
    rw [regValue_congr dst _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.1]
  · intro q hq
    simp [hq,h.2 q hq]

theorem signedSquareRowClear_frame (c : Wire) (xs dst pad carry : List Wire)
    (hnd : (c::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (base : BasisState) (C : Bool) (hC : base c=C)
    (hz : regValue (pad++carry) base=0) (A : Nat) (hA : A<2^xs.length) :
    Triple (SquareFrame dst base (signedRowValue C A (regValue xs base) xs.length))
      (signedSquareRowClear c xs dst pad carry) (SquareFrame dst base A) := by
  let src := xs++pad.take 1
  let cy := carry.take xs.length
  have ndc : (c::dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have dstN : dst.Nodup := (List.nodup_cons.mp ndc).2
  have ndadd : (c::src++dst++cy).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hp' := (List.take_sublist 1 pad).count_le q
    have hc' := (List.take_sublist xs.length carry).count_le q
    simp only [src,cy,List.count_cons,List.count_append] at h ⊢
    omega
  have hs : src.length=dst.length := by simp [src,hd,hp]
  have hcy : cy.length+1=dst.length := by simp [cy,hc,hd]
  have srcv : regValue src base=regValue xs base := by
    have p0 : regValue (pad.take 1) base=0 := (regValue_zero _ _).mpr
      (fun q hq => (regValue_zero _ _).mp hz q (by simp [List.mem_of_mem_take hq]))
    simp [src,regValue_append,p0]
  have cy0 : regValue cy base=0 := (regValue_zero _ _).mpr
    (fun q hq => (regValue_zero _ _).mp hz q (by simp [List.mem_of_mem_take hq]))
  let B := signedRowValue C A (regValue xs base) xs.length
  let V1 := if C then B else 2^dst.length-1-B
  let V2 := 2^dst.length-1-V1
  let V3 := (V2+regValue src base+C.toNat)%2^dst.length
  let V4 := 2^dst.length-1-V3
  have h1 := xorWhenFalse_frame c dst ndc base C B hC
  have h2 := notRegister_frame dst dstN base V1
  have h3 := addInPlace_cin_frame c src dst cy ndadd hs hcy base C hC cy0 V2
  have h4 := notRegister_frame dst dstN base V3
  have h5 := xorWhenFalse_prefix_frame c dst xs.length ndc (by omega) base C V4 hC
  have comp := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  have heq : (if C then V4 else
      (2^xs.length-1-V4%2^xs.length)+2^xs.length*(V4/2^xs.length))=A := by
    have hS := regValue_lt xs base
    have pow : 2^dst.length=2*2^xs.length := by rw [hd,Nat.pow_succ]; omega
    cases C with
    | false =>
      have bfit : A+2^xs.length-regValue xs base<2^dst.length := by rw [pow]; omega
      have bEq : B=A+2^xs.length-regValue xs base := by
        simp only [B,signedRowValue,Bool.false_eq_true,if_false]
        have bf : A+2^xs.length-regValue xs base<2^(xs.length+1) := by simpa [hd] using bfit
        rw [Nat.mod_eq_of_lt bf]
      have v2Eq : V2=B := by
        dsimp [V1,V2]
        rw [bEq]
        omega
      have addfit : A+2^xs.length<2^dst.length := by rw [pow]; omega
      have v3Eq : V3=A+2^xs.length := by
        dsimp [V3]
        rw [v2Eq,srcv]
        simp only [bEq]
        rw [show A+2^xs.length-regValue xs base+regValue xs base=A+2^xs.length by omega,
          Nat.mod_eq_of_lt addfit]
      have v4Eq : V4=2^xs.length-1-A := by
        dsimp [V4]
        rw [v3Eq,pow]
        omega
      simp only [Bool.false_eq_true,if_false]
      rw [v4Eq]
      have lowfit : 2^xs.length-1-A<2^xs.length := by omega
      rw [Nat.mod_eq_of_lt lowfit,Nat.div_eq_of_lt lowfit]
      omega
    | true =>
      have bfit : A+regValue xs base+1<2^dst.length := by rw [pow]; omega
      have bEq : B=A+regValue xs base+1 := by
        simp only [B,signedRowValue,if_true]
        have bf : A+regValue xs base+1<2^(xs.length+1) := by simpa [hd] using bfit
        rw [Nat.mod_eq_of_lt bf]
      have v2Eq : V2=2^dst.length-1-B := by simp [V1,V2]
      have midfit : 2^dst.length-1-(A+regValue xs base+1)+regValue xs base+1<2^dst.length := by omega
      have v3Eq : V3=2^dst.length-1-A := by
        dsimp [V3]
        rw [v2Eq,srcv,bEq]
        rw [Nat.mod_eq_of_lt midfit]
        omega
      have v4Eq : V4=A := by dsimp [V4]; rw [v3Eq]; omega
      simp [v4Eq]
  have final := Triple.conseq (fun _ h => h) comp (fun _ h => by simpa [heq] using h)
  simpa [signedSquareRowClear,src,cy,B,V1,V2,V3,V4,List.append_assoc] using final

theorem signedSquareRow_roundtrip (c : Wire) (xs dst pad carry : List Wire)
    (hnd : (c::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (base : BasisState) (hz : regValue (pad++carry) base=0)
    (A : Nat) (hA : A<2^xs.length) :
    Triple (SquareFrame dst base A)
      (signedSquareRow c xs dst pad carry++signedSquareRowClear c xs dst pad carry)
      (SquareFrame dst base A) := by
  let C := base c
  have f := signedSquareRow_frame c xs dst pad carry hnd hd hp hc base C rfl hz A
    (hA.trans (Nat.pow_lt_pow_right (by decide) (by omega)))
  have r := signedSquareRowClear_frame c xs dst pad carry hnd hd hp hc base C rfl hz A hA
  exact f.seq r

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedSquareRowsProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

private theorem row_tail_identity (dst : List Wire) (n : Nat) :
    (dst.drop 1).take n++dst.drop (n+1)=dst.drop 1 := by
  rw [show dst.drop (n+1)=(dst.drop 1).drop n by
    rw [List.drop_drop]; congr 1; omega]
  exact List.take_append_drop n (dst.drop 1)

private theorem drop_tail_sublist (dst : List Wire) (n : Nat) :
    (dst.drop (n+1)).Sublist (dst.drop n) := by
  have h := List.drop_sublist 1 (dst.drop n)
  simpa [List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

private theorem drop_value_div_local (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.drop n) s=regValue r s/2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  have hl : regValue (r.take n) s<2^n := by
    simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [h,Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),Nat.div_eq_of_lt hl,Nat.zero_add]

/-- If bits `n` and above are clean, the row window at positions `1..n`
contains exactly the full word divided by two. -/
theorem signed_row_slice_value (dst : List Wire) (n A : Nat) (hn : 1≤dst.length)
    (s : BasisState) (hv : regValue dst s=A)
    (hhi : regValue (dst.drop n) s=0) :
    regValue ((dst.drop 1).take n) s=A/2 := by
  have tail0 : regValue (dst.drop (n+1)) s=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero _ _).mp hhi q ((drop_tail_sublist dst n).subset hq)
  have split := regValue_append ((dst.drop 1).take n) (dst.drop (n+1)) s
  rw [row_tail_identity,tail0,Nat.mul_zero,Nat.add_zero] at split
  have dropv := drop_value_div_local dst 1 hn s
  rw [hv] at dropv
  exact split.symm.trans dropv

/-- Updating only the row window by `D` updates the complete word by `2D` and
preserves the clean tail above the row. -/
theorem signed_row_lift_update (dst : List Wire) (n A D : Nat)
    (hn : 1≤dst.length) (hnd : dst.Nodup) (s t : BasisState)
    (hv : regValue dst s=A)
    (hrow : regValue ((dst.drop 1).take n) t=A/2+D)
    (htail : regValue (dst.drop (n+1)) s=0)
    (hkeep : ∀q,q∉(dst.drop 1).take n → t q=s q) :
    regValue dst t=A+2*D ∧ regValue (dst.drop (n+1)) t=0 := by
  let row := (dst.drop 1).take n
  let tail := dst.drop (n+1)
  have dropN : (dst.drop 1).Nodup := (List.drop_sublist 1 dst).nodup hnd
  have dis : row.Disjoint tail := by
    have h := List.disjoint_take_drop dropN (Nat.le_refl n)
    simpa [row,tail,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
  have tailt : regValue tail t=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    rw [hkeep q (fun hr => List.disjoint_left.mp dis hr hq)]
    exact (regValue_zero _ _).mp htail q hq
  have drop1t := regValue_append row tail t
  rw [row_tail_identity,hrow,tailt,Nat.mul_zero,Nat.add_zero] at drop1t
  have take1same : regValue (dst.take 1) t=regValue (dst.take 1) s := by
    apply regValue_congr
    intro q hq
    apply hkeep q
    intro hr
    have dis1 := List.disjoint_take_drop hnd (show 1≤1 from le_rfl)
    exact List.disjoint_left.mp dis1 hq (List.mem_of_mem_take hr)
  have ss := regValue_append (dst.take 1) (dst.drop 1) s
  have tt := regValue_append (dst.take 1) (dst.drop 1) t
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at ss tt
  have drop1s := drop_value_div_local dst 1 hn s
  rw [hv] at drop1s
  constructor
  · rw [tt,take1same,drop1t,← hv,ss,drop1s]
    norm_num
    omega
  · exact tailt

/-- Exact semantics of the complete overlapping signed-row ladder. -/
theorem signedSquareRows_correct (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : xs.length≤1 ∨ 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    let out := run (signedSquareRows xs dst pad carry) m s
    out.phase=s.phase ∧ regValue dst out.basis=A+signedRowsValue xs s.basis ∧
      (∀q,q∉dst → out.basis q=s.basis q) ∧ regValue (pad++carry) out.basis=0 ∧
      regValue (dst.drop (2*xs.length-1)) out.basis=0 := by
  induction xs generalizing dst s m A with
  | nil =>
    have de : dst=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst dst
    have ha : A=0 := by simpa using hv.symm
    subst A
    change s.phase=s.phase ∧ regValue [] s.basis=0+0 ∧
      (∀q,q∉[] → s.basis q=s.basis q) ∧ regValue (pad++carry) s.basis=0 ∧
      regValue [] s.basis=0
    exact ⟨rfl,rfl,fun _ _ => rfl,hw,rfl⟩
  | cons c xs ih =>
    cases xs with
    | nil =>
      simp only [List.length_cons,List.length_nil] at hd hhi ⊢
      refine ⟨rfl,?_,fun _ _ => rfl,hw,?_⟩
      · simpa [signedRowsValue] using hv
      · simpa using hhi
    | cons d tail =>
      simp only [List.length_cons] at hd hp hc hhi
      let rest := d::tail
      let n := rest.length+1
      let row := (dst.drop 1).take n
      let dst2 := dst.drop 2
      have hpad : 1≤pad.length := by
        rcases hp with hp|hp
        · simp at hp
        · exact hp
      have hcarry : rest.length≤carry.length := by
        change tail.length+1≤carry.length
        omega
      have hdst : 2≤dst.length := by omega
      have rowLen : row.length=rest.length+1 := by
        have cap : n≤(dst.drop 1).length := by dsimp [n,rest]; simp; omega
        simpa [row,n] using List.length_take_of_le cap
      have dst2Len : dst2.length=2*rest.length := by
        dsimp [dst2,rest]
        simp
        omega
      have rowSub : row.Sublist dst :=
        (List.take_sublist n (dst.drop 1)).trans (List.drop_sublist 1 dst)
      have dst2Sub : dst2.Sublist dst := List.drop_sublist 2 dst
      have ndrow : (c::rest++row++pad++carry).Nodup := by
        have pre := (List.Sublist.refl (c::rest)).append rowSub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub : (c::rest++row++pad++carry).Sublist
            (c::rest++dst++pad++carry) := by simpa [List.append_assoc] using all
        exact sub.nodup hnd
      have ndrec : (rest++dst2++pad++carry).Nodup := by
        have pre := (List.Sublist.refl rest).append dst2Sub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub0 : (rest++dst2++pad++carry).Sublist (rest++dst++pad++carry) := by
          simpa [List.append_assoc] using all
        have htail : (rest++dst++pad++carry).Nodup := by
          simpa [rest,List.append_assoc] using (List.nodup_cons.mp hnd).2
        exact sub0.nodup htail
      have dstN : dst.Nodup := by
        apply List.nodup_iff_count.mpr
        intro q
        have hh := List.nodup_iff_count.mp hnd q
        simp only [List.count_cons,List.count_append] at hh ⊢
        omega
      have high0 : regValue (dst.drop n) s.basis=0 := by
        simpa [n,rest] using hhi
      have rowv : regValue row s.basis=A/2 := by
        simpa [row,n] using signed_row_slice_value dst n A (by omega) s.basis hv high0
      have work0 : regValue (pad++carry) s.basis=0 := hw
      have rowBound : A/2<2^row.length := by
        rw [← rowv]
        exact regValue_lt row s.basis
      have rf := signedSquareRow_frame c rest row pad carry ndrow rowLen hpad hcarry
        s.basis (s.basis c) rfl work0 (A/2) rowBound
      let mr := m.take (measurementCount (signedSquareRow c rest row pad carry))
      let u := run (signedSquareRow c rest row pad carry) mr s
      have ru := rf s mr ⟨rowv,fun _ _ => rfl⟩
      let D := signedDeltaValue c rest s.basis
      have delta : signedRowValue (s.basis c) (A/2) (regValue rest s.basis) rest.length=A/2+D := by
        have hbA : A/2<2^rest.length := by
          have hnDst : n≤dst.length := by dsimp [n,rest]; omega
          have Ahi : A<2^n := by
            have split := regValue_append (dst.take n) (dst.drop n) s.basis
            rw [List.take_append_drop,List.length_take,Nat.min_eq_left hnDst,
              high0,Nat.mul_zero,Nat.add_zero,hv] at split
            rw [split]
            have b := regValue_lt (dst.take n) s.basis
            simpa [List.length_take,Nat.min_eq_left hnDst] using b
          dsimp [n] at Ahi
          rw [Nat.pow_succ] at Ahi
          omega
        have hbS := regValue_lt rest s.basis
        cases hb : s.basis c
        · simp only [signedRowValue,hb,Bool.false_eq_true,if_false,signedDeltaValue,D]
          have hlt : A/2+2^rest.length-regValue rest s.basis<2^(rest.length+1) := by
            rw [Nat.pow_succ]; omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
        · simp only [signedRowValue,hb,if_true,signedDeltaValue,D]
          have hlt : A/2+regValue rest s.basis+1<2^(rest.length+1) := by
            rw [Nat.pow_succ]; omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
      have rowOut : regValue row u.basis=A/2+D := by
        change regValue row (run (signedSquareRow c rest row pad carry) mr s).basis=_
        rw [ru.2.1,delta]
      have keepRow (q : Wire) (hq : q∉row) : u.basis q=s.basis q := ru.2.2 q hq
      have lift := signed_row_lift_update dst n A D (by omega)
        dstN s.basis u.basis hv rowOut
        (by
          have sub := drop_tail_sublist dst n
          apply (regValue_zero _ _).mpr; intro q hq
          exact (regValue_zero _ _).mp high0 q (sub.subset hq)) keepRow
      have workU : regValue (pad++carry) u.basis=0 := by
        rw [← hw]
        apply regValue_congr
        intro q hq
        apply keepRow q
        intro hr
        have hnq := List.nodup_iff_count.mp ndrow q
        have h1 := List.count_pos_iff.mpr hq
        have h2 := List.count_pos_iff.mpr hr
        simp only [List.count_cons,List.count_append] at hnq h1
        omega
      have high2 : regValue (dst2.drop rest.length) u.basis=0 := by
        simpa [dst2,n,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using lift.2
      let A2 := regValue dst2 u.basis
      have hcrec : rest.length-1≤carry.length := by omega
      have recResult := ih dst2 (by simpa [rest] using ndrec) (by simpa [rest] using dst2Len)
        (Or.inr hpad) (by simpa [rest] using hcrec) u
        (m.drop (measurementCount (signedSquareRow c rest row pad carry))) A2 rfl
        (by simpa [rest] using high2) workU
      let out := run (signedSquareRows rest dst2 pad carry)
        (m.drop (measurementCount (signedSquareRow c rest row pad carry))) u
      have restRows : signedRowsValue rest u.basis=signedRowsValue rest s.basis := by
        apply signedRowsValue_congr
        intro q hq
        apply keepRow q
        intro hr
        have hnq := List.nodup_iff_count.mp ndrow q
        have h1 := List.count_pos_iff.mpr hq
        have h2 := List.count_pos_iff.mpr hr
        simp only [List.count_cons,List.count_append] at hnq h1
        omega
      have low2same : regValue (dst.take 2) out.basis=regValue (dst.take 2) u.basis := by
        apply regValue_congr
        intro q hq
        exact recResult.2.2.1 q (fun hdq => by
          have dis := List.disjoint_take_drop dstN (show 2≤2 from le_rfl)
          exact List.disjoint_left.mp dis hq hdq)
      have finalValue : regValue dst out.basis=A+signedRowsValue (c::rest) s.basis := by
        have su := regValue_append (dst.take 2) dst2 u.basis
        have so := regValue_append (dst.take 2) dst2 out.basis
        rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at su so
        have su' : regValue (dst.take 2) u.basis+4*A2=A+2*D := by
          dsimp [A2]
          norm_num at su ⊢
          rw [← su,lift.1]
        rw [so,low2same,recResult.2.1,restRows]
        norm_num
        have rowsFull : signedRowsValue (c::rest) s.basis=
            2*D+4*signedRowsValue rest s.basis := by
          simp [signedRowsValue,D,rest]
        rw [rowsFull]
        omega
      rw [signedSquareRows,run_append]
      change out.phase=s.phase ∧ _
      refine ⟨recResult.1.trans ru.1,finalValue,?_,recResult.2.2.2.1,?_⟩
      · intro q hq
        exact (recResult.2.2.1 q (fun hdq => hq (dst2Sub.subset hdq))).trans
          (keepRow q (fun hr => hq (rowSub.subset hr)))
      · have top := recResult.2.2.2.2
        change regValue (dst2.drop (2*rest.length-1)) out.basis=0 at top
        have he : 2+(2*rest.length-1)=2*(rest.length+1)-1 := by
          have : 1≤rest.length := by simp [rest]
          omega
        dsimp [dst2] at top
        rw [List.drop_drop,he] at top
        change regValue (dst.drop (2*(rest.length+1)-1)) out.basis=0
        exact top

theorem signedSquareRows_roundtrip (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : xs.length≤1 ∨ 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    let out := run (signedSquareRows xs dst pad carry++
      signedSquareRowsClear xs dst pad carry) m s
    out.phase=s.phase ∧ out.basis=s.basis := by
  induction xs generalizing dst s m A with
  | nil =>
    have de : dst=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst dst
    simp [signedSquareRows,signedSquareRowsClear,run]
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedSquareRows,signedSquareRowsClear,run]
    | cons d tail =>
      simp only [List.length_cons] at hd hp hc hhi
      let rest := d::tail
      let n := rest.length+1
      let row := (dst.drop 1).take n
      let dst2 := dst.drop 2
      let rfwd := signedSquareRow c rest row pad carry
      let rclr := signedSquareRowClear c rest row pad carry
      let middle := signedSquareRows rest dst2 pad carry++signedSquareRowsClear rest dst2 pad carry
      have hpad : 1≤pad.length := by rcases hp with hp|hp <;> omega
      have hcarry : rest.length≤carry.length := by change tail.length+1≤carry.length; omega
      have rowLen : row.length=rest.length+1 := by
        have cap : n≤(dst.drop 1).length := by dsimp [n,rest]; simp; omega
        simpa [row,n] using List.length_take_of_le cap
      have dst2Len : dst2.length=2*rest.length := by dsimp [dst2,rest]; simp; omega
      have rowSub : row.Sublist dst :=
        (List.take_sublist n (dst.drop 1)).trans (List.drop_sublist 1 dst)
      have dst2Sub : dst2.Sublist dst := List.drop_sublist 2 dst
      have ndrow : (c::rest++row++pad++carry).Nodup := by
        have pre := (List.Sublist.refl (c::rest)).append rowSub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub : (c::rest++row++pad++carry).Sublist
            (c::rest++dst++pad++carry) := by simpa [List.append_assoc] using all
        exact sub.nodup hnd
      have ndrec : (rest++dst2++pad++carry).Nodup := by
        have pre := (List.Sublist.refl rest).append dst2Sub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub0 : (rest++dst2++pad++carry).Sublist (rest++dst++pad++carry) := by
          simpa [List.append_assoc] using all
        have ht : (rest++dst++pad++carry).Nodup := by
          simpa [rest,List.append_assoc] using (List.nodup_cons.mp hnd).2
        exact sub0.nodup ht
      have dstN : dst.Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hnd q
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
      have high0 : regValue (dst.drop n) s.basis=0 := by simpa [n,rest] using hhi
      have rowv : regValue row s.basis=A/2 := by
        simpa [row,n] using signed_row_slice_value dst n A (by omega) s.basis hv high0
      have hA : A/2<2^rest.length := by
        have hnDst : n≤dst.length := by dsimp [n,rest]; omega
        have split := regValue_append (dst.take n) (dst.drop n) s.basis
        rw [List.take_append_drop,List.length_take,Nat.min_eq_left hnDst,
          high0,Nat.mul_zero,Nat.add_zero,hv] at split
        have b := regValue_lt (dst.take n) s.basis
        rw [List.length_take,Nat.min_eq_left hnDst] at b
        dsimp [n] at split b
        rw [Nat.pow_succ] at b
        omega
      have work0 : regValue (pad++carry) s.basis=0 := hw
      have ff := signedSquareRow_frame c rest row pad carry ndrow rowLen hpad hcarry
        s.basis (s.basis c) rfl work0 (A/2)
        (hA.trans (Nat.pow_lt_pow_right (by decide) (by omega)))
      let m1 := m.drop (measurementCount rfwd)
      let u := run rfwd (m.take (measurementCount rfwd)) s
      have fu := ff s (m.take (measurementCount rfwd)) ⟨rowv,fun _ _ => rfl⟩
      let D := signedDeltaValue c rest s.basis
      have delta : signedRowValue (s.basis c) (A/2) (regValue rest s.basis) rest.length=A/2+D := by
        have hs := regValue_lt rest s.basis
        cases hb : s.basis c
        · simp only [signedRowValue,hb,Bool.false_eq_true,if_false,signedDeltaValue,D]
          have fit : A/2+2^rest.length-regValue rest s.basis<2^(rest.length+1) := by
            rw [Nat.pow_succ]; omega
          rw [Nat.mod_eq_of_lt fit]; omega
        · simp only [signedRowValue,hb,if_true,signedDeltaValue,D]
          have fit : A/2+regValue rest s.basis+1<2^(rest.length+1) := by
            rw [Nat.pow_succ]; omega
          rw [Nat.mod_eq_of_lt fit]; omega
      have rowU : regValue row u.basis=A/2+D := by
        change regValue row (run rfwd (m.take (measurementCount rfwd)) s).basis=_
        rw [fu.2.1,delta]
      have keepU (q : Wire) (hq : q∉row) : u.basis q=s.basis q := fu.2.2 q hq
      have lift := signed_row_lift_update dst n A D (by omega) dstN s.basis u.basis
        hv rowU (by
          have sub := drop_tail_sublist dst n
          apply (regValue_zero _ _).mpr; intro q hq
          exact (regValue_zero _ _).mp high0 q (sub.subset hq)) keepU
      have workU : regValue (pad++carry) u.basis=0 := by
        rw [← hw]; apply regValue_congr; intro q hq; apply keepU q
        intro hr
        have hn := List.nodup_iff_count.mp ndrow q
        have h1 := List.count_pos_iff.mpr hq
        have h2 := List.count_pos_iff.mpr hr
        simp only [List.count_cons,List.count_append] at hn h1
        omega
      have high2 : regValue (dst2.drop rest.length) u.basis=0 := by
        simpa [dst2,n,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using lift.2
      let A2 := regValue dst2 u.basis
      have hcrec : rest.length-1≤carry.length := by omega
      have mid := ih dst2 (by simpa [rest] using ndrec) (by simpa [rest] using dst2Len)
        (Or.inr hpad) (by simpa [rest] using hcrec) u (m1.take (measurementCount middle)) A2 rfl
        (by simpa [rest] using high2) workU
      let w := run middle (m1.take (measurementCount middle)) u
      have wbasis : w.basis=u.basis := mid.2
      have wphase : w.phase=u.phase := mid.1
      have rr := signedSquareRowClear_frame c rest row pad carry ndrow rowLen hpad hcarry
        s.basis (s.basis c) rfl work0 (A/2) hA
      have preW : SquareFrame row s.basis
          (signedRowValue (s.basis c) (A/2) (regValue rest s.basis) rest.length) w.basis := by
        rw [wbasis]
        exact fu.2
      let out := run rclr (m1.drop (measurementCount middle)) w
      have fin := rr w (m1.drop (measurementCount middle)) preW
      change out.phase=w.phase ∧ SquareFrame row s.basis (A/2) out.basis at fin
      have outbasis : out.basis=s.basis := by
        funext q
        by_cases hq : q∈row
        · exact (regValue_eq_iff row out.basis s.basis).mp (fin.2.1.trans rowv.symm) q hq
        · exact fin.2.2 q hq
      have outphase : out.phase=s.phase := fin.1.trans (wphase.trans fu.1)
      have exec : run (rfwd++(middle++rclr)) m s=out := by
        rw [run_append]
        change run (middle++rclr) m1 u=out
        rw [run_append]
      have result : (run (rfwd++(middle++rclr)) m s).phase=s.phase ∧
          (run (rfwd++(middle++rclr)) m s).basis=s.basis := by
        rw [exec]
        exact ⟨outphase,outbasis⟩
      change (run (signedSquareRows (c::rest) dst pad carry++
        signedSquareRowsClear (c::rest) dst pad carry) m s).phase=s.phase ∧
        (run (signedSquareRows (c::rest) dst pad carry++
          signedSquareRowsClear (c::rest) dst pad carry) m s).basis=s.basis
      rw [show signedSquareRows (c::rest) dst pad carry=
        rfwd++signedSquareRows rest dst2 pad carry by rfl,
        show signedSquareRowsClear (c::rest) dst pad carry=
          signedSquareRowsClear rest dst2 pad carry++rclr by rfl]
      simpa [middle,List.append_assoc] using result

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/SignedSquareIdentity.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

def signedDiagValue (X n : Nat) : Nat :=
  if n=0 then 0 else X+(2^(n-1)-1-X%2^(n-1))*2^n

theorem signedDiagValue_step (b : Bool) (Y k : Nat) (hk : 1≤k) (_hY : Y<2^k) :
    signedDiagValue (b.toNat+2*Y) (k+1)+2*Y=
      4*signedDiagValue Y k+(if b then 1 else 2^(k+1)) := by
  let H := 2^(k-1)
  let M := 2^k
  have hH : 0<H := by positivity
  have hm : M=2*H := by
    have he : (k-1)+1=k := by omega
    calc
      M = 2^k := rfl
      _ = 2^((k-1)+1) := congrArg (2^·) he.symm
      _ = 2^(k-1)*2 := by rw [Nat.pow_succ]
      _ = 2*H := by simp [H,Nat.mul_comm]
  have hr : Y%H<H := Nat.mod_lt Y hH
  have split : Y%H+H*(Y/H)=Y := Nat.mod_add_div Y H
  have hb : b.toNat≤1 := by cases b <;> simp
  have low : b.toNat+2*(Y%H)<M := by rw [hm]; omega
  have decomp : b.toNat+2*Y=(b.toNat+2*(Y%H))+M*(Y/H) := by
    calc
      b.toNat+2*Y = b.toNat+2*(Y%H+H*(Y/H)) :=
        congrArg (fun z => b.toNat+2*z) split.symm
      _ = (b.toNat+2*(Y%H))+M*(Y/H) := by rw [hm]; ring
  have xmod : (b.toNat+2*Y)%M=b.toNat+2*(Y%H) := by
    rw [decomp,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt low]
  have pk : 2^(k+1)=2*M := by rw [Nat.pow_succ]; simp [M,Nat.mul_comm]
  have hkn : k≠0 := by omega
  have hks : k+1≠0 := by omega
  simp only [signedDiagValue,hkn,hks,if_false]
  rw [show k+1-1=k by omega]
  change (b.toNat+2*Y)+(M-1-(b.toNat+2*Y)%M)*2^(k+1)+2*Y=
    4*(Y+(H-1-Y%H)*M)+(if b then 1 else 2^(k+1))
  cases b
  · simp only [Bool.toNat_false,Nat.zero_add,Bool.false_eq_true,if_false] at xmod ⊢
    rw [xmod,pk]
    have hs1 : (M-1-2*(Y%H))+(2*(Y%H)+1)=M := by rw [hm]; omega
    have hs2 : (H-1-Y%H)+(Y%H+1)=H := by omega
    have hab : M-1-2*(Y%H)=2*(H-1-Y%H)+1 := by rw [hm]; omega
    rw [hab]
    ring
  · simp only [Bool.toNat_true,if_true] at xmod ⊢
    rw [xmod,pk]
    have hs1 : (M-1-(1+2*(Y%H)))+(2*(Y%H)+2)=M := by rw [hm]; omega
    have hs2 : (H-1-Y%H)+(Y%H+1)=H := by omega
    nlinarith [congrArg (fun z => z*(2*M)) hs1,
      congrArg (fun z => 4*z*M) hs2]

def signedRawValue : List Wire → BasisState → Nat
  | [], _ => 0
  | c::[], base => 2*(base c).toNat
  | c::d::tail, base =>
      2*signedDeltaValue c (d::tail) base+4*signedRawValue (d::tail) base

def signedTopTerm : List Wire → BasisState → Nat
  | [], _ => 0
  | c::[], base => 2*(base c).toNat
  | _::d::tail, base => 4*signedTopTerm (d::tail) base

theorem signedTopTerm_congr (xs : List Wire) (s t : BasisState)
    (h : ∀q∈xs,s q=t q) : signedTopTerm xs s=signedTopTerm xs t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [signedTopTerm,h x (by simp)]
    | cons y ys =>
      simp only [signedTopTerm]
      rw [ih (fun q hq => h q (by simp [hq]))]

theorem signedRawValue_rows_top (xs : List Wire) (base : BasisState) :
    signedRawValue xs base=signedRowsValue xs base+signedTopTerm xs base := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedRawValue,signedRowsValue,signedTopTerm]
    | cons d tail =>
      simp only [signedRawValue,signedRowsValue,signedTopTerm]
      rw [ih]
      omega

theorem signedTopTerm_bound (xs : List Wire) (base : BasisState) (hn : 1≤xs.length) :
    signedTopTerm xs base≤2^(2*xs.length-1) := by
  induction xs with
  | nil => simp at hn
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases h : base x <;> simp [signedTopTerm,h]
    | cons y ys =>
      let rest := y::ys
      have hi : signedTopTerm rest base≤2^(2*rest.length-1) := by
        simpa [rest] using ih (by simp)
      change 4*signedTopTerm rest base≤2^(2*(rest.length+1)-1)
      have hlen : 1≤rest.length := by simp [rest]
      have he : 2*(rest.length+1)-1=(2*rest.length-1)+2 := by omega
      rw [he,Nat.pow_add]
      norm_num
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left 4 hi

theorem signedRawValue_bound (xs : List Wire) (base : BasisState) (hn : 1≤xs.length) :
    signedRawValue xs base<2^(2*xs.length) := by
  rw [signedRawValue_rows_top]
  have hr := signedRowsValue_bound xs base hn
  have ht := signedTopTerm_bound xs base hn
  have hp : 2^xs.length≤2^(2*xs.length-1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hs : 0<2^xs.length := Nat.two_pow_pos _
  have he : 2*xs.length=(2*xs.length-1)+1 := by omega
  rw [he,Nat.pow_succ]
  omega

theorem signedRawValue_correct (xs : List Wire) (base : BasisState) (hn : xs≠[]) :
    signedRawValue xs base=(regValue xs base)^2+
      signedDiagValue (regValue xs base) xs.length := by
  induction xs with
  | nil => contradiction
  | cons c xs ih =>
    cases xs with
    | nil =>
      cases hc : base c <;> simp [signedRawValue,signedDiagValue,regValue,hc]
    | cons d tail =>
      let rest := d::tail
      have hi := ih (by simp)
      have hk : 1≤rest.length := by simp [rest]
      have hY := regValue_lt rest base
      have step := signedDiagValue_step (base c) (regValue rest base) rest.length hk hY
      have rval : regValue (c::rest) base=(base c).toNat+2*regValue rest base := by
        change (if base c then 1 else 0)+2*regValue rest base=_
        cases base c <;> rfl
      cases hb : base c
      · have st : signedDiagValue (2*regValue rest base) (rest.length+1)+
            2*regValue rest base=
            4*signedDiagValue (regValue rest base) rest.length+2^(rest.length+1) := by
          simpa [hb] using step
        simp only [signedRawValue,signedDeltaValue,hb,Bool.false_eq_true,if_false]
        rw [rval,hb]
        simp only [Bool.toNat_false,Nat.zero_add,List.length_cons]
        change 2*(2^(d::tail).length-regValue (d::tail) base)+4*signedRawValue (d::tail) base=
          (2*regValue (d::tail) base)^2+
            signedDiagValue (2*regValue (d::tail) base) ((d::tail).length+1)
        rw [hi]
        rw [Nat.pow_succ] at st
        have hsub : (2^(d::tail).length-regValue (d::tail) base)+
            regValue (d::tail) base=2^(d::tail).length :=
          Nat.sub_add_cancel (Nat.le_of_lt (regValue_lt (d::tail) base))
        nlinarith
      · have st : signedDiagValue (1+2*regValue rest base) (rest.length+1)+
            2*regValue rest base=
            4*signedDiagValue (regValue rest base) rest.length+1 := by
          simpa [hb] using step
        simp only [signedRawValue,signedDeltaValue,hb,if_true]
        rw [rval,hb]
        simp only [Bool.toNat_true,List.length_cons]
        change 2*(regValue (d::tail) base+1)+4*signedRawValue (d::tail) base=
          (1+2*regValue (d::tail) base)^2+
            signedDiagValue (1+2*regValue (d::tail) base) ((d::tail).length+1)
        rw [hi]
        nlinarith

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedSquareDiagonalProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem xorWhenFalse_wires_subset (c : Wire) (ys : List Wire) :
    wires (xorWhenFalse c ys)⊆(c::ys).toFinset := by
  induction ys with
  | nil => simp [xorWhenFalse,wires]
  | cons y ys ih =>
    simp only [xorWhenFalse,wires_append]
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,List.mem_toFinset,List.mem_cons] at hq ⊢
    have hi := @ih q
    simp only [List.mem_toFinset,List.mem_cons] at hi
    tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedSquareLeafProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem signedSquareTop_correct (xs dst : List Wire)
    (hnd : (xs++dst).Nodup) (hd : dst.length=2*xs.length)
    (s : State) (m : List Bool)
    (htop : regValue (dst.drop (2*xs.length-1)) s.basis=0) :
    let out := run (signedSquareTop xs dst) m s
    out.phase=s.phase ∧
      regValue dst out.basis=regValue dst s.basis+signedTopTerm xs s.basis ∧
      (∀q,q∉dst → out.basis q=s.basis q) ∧
      regValue xs out.basis=regValue xs s.basis := by
  induction xs generalizing dst s with
  | nil =>
    have de : dst=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst dst
    simp [signedSquareTop,signedTopTerm,run]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp at hd
      | cons a ds =>
        cases ds with
        | nil => simp at hd
        | cons z tail =>
          have te : tail=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
          subst tail
          have hxz : x≠z := by
            intro e; subst z; simp at hnd
          have haz : a≠z := by
            intro e; subst z; simp at hnd
          have hzx : z≠x := Ne.symm hxz
          have top0 : s.basis z=false := by
            change regValue [z] s.basis=0 at htop
            simpa [regValue] using htop
          simp only [signedSquareTop,run,signedTopTerm,regValue,List.foldr_cons,List.foldr_nil]
          refine ⟨True.intro,?_,?_,?_⟩
          · simp [writeBit,top0,haz]
            cases s.basis x <;> cases s.basis a <;> rfl
          · intro q hq
            simp [writeBit,show q≠z from fun e => hq (by simp [e])]
          · simp [writeBit,hxz]
    | cons y ys =>
      cases dst with
      | nil => simp at hd
      | cons a ds =>
        cases ds with
        | nil => simp at hd; omega
        | cons b tail =>
          let rest := y::ys
          have htail : tail.length=2*rest.length := by
            dsimp [rest]
            simp only [List.length_cons] at hd
            omega
          have hnTail : (rest++tail).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := List.nodup_iff_count.mp hnd q
            simp only [rest,List.count_cons,List.count_append] at h ⊢
            omega
          have topTail : regValue (tail.drop (2*rest.length-1)) s.basis=0 := by
            simpa [rest,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using htop
          have hi := ih tail hnTail htail s topTail
          let out := run (signedSquareTop rest tail) m s
          have dstN : (a::b::tail).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := List.nodup_iff_count.mp hnd q
            simp only [List.count_cons,List.count_append] at h ⊢
            omega
          have lowSame : regValue [a,b] out.basis=regValue [a,b] s.basis := by
            apply regValue_congr
            intro q hq
            exact hi.2.2.1 q (fun ht =>
              List.disjoint_left.mp (List.disjoint_take_drop dstN (show 2≤2 from le_rfl)) hq ht)
          have splitS := regValue_append [a,b] tail s.basis
          have splitO := regValue_append [a,b] tail out.basis
          change out.phase=s.phase ∧ _
          refine ⟨hi.1,?_,?_,?_⟩
          · change regValue (a::b::tail) out.basis=
              regValue (a::b::tail) s.basis+signedTopTerm (x::rest) s.basis
            rw [← show [a,b]++tail=a::b::tail by rfl,splitO,lowSame,hi.2.1,splitS]
            simp [signedTopTerm,rest]
            omega
          · intro q hq
            exact hi.2.2.1 q (fun ht => hq (by simp [ht]))
          · have srcSame : regValue rest out.basis=regValue rest s.basis := hi.2.2.2
            change (if out.basis x then 1 else 0)+2*regValue rest out.basis=
              (if s.basis x then 1 else 0)+2*regValue rest s.basis
            rw [srcSame,hi.2.2.1 x (by
              intro ht
              have hn := List.nodup_iff_count.mp hnd x
              have h2 := List.count_pos_iff.mpr ht
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at hn
              omega)]

theorem signedSquareTop_roundtrip (xs dst : List Wire) (hnd : (xs++dst).Nodup)
    (s : State) (m : List Bool) :
    run (signedSquareTop xs dst++signedSquareTop xs dst) m s=s := by
  induction xs generalizing dst s with
  | nil => simp [signedSquareTop,run]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,run]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,run]
        | cons z tail =>
          have hxz : x≠z := by
            intro e; subst z; simp at hnd
          simp [signedSquareTop,run,writeBit,hxz]
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,run]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,run]
        | cons b tail =>
          have hn : (y::ys++tail).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := List.nodup_iff_count.mp hnd q
            simp only [List.count_cons,List.count_append] at h ⊢
            omega
          simpa [signedSquareTop] using ih tail hn s

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroSignedSquare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroSignedSquareRowsProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroSignedSquareDiagonalProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroSignedSquareProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedSquareLeafSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem signedSquareRow_wires_subset (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    wires (signedSquareRow c xs dst pad carry)⊆
      (c::xs++dst++pad++carry).toFinset := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have hk : (carry.take xs.length).length+1=dst.length := by simp [hd,hc]
  have ha := addInPlace_wires (xs++pad.take 1) dst (carry.take xs.length) c hs hk
  have hxl := xorWhenFalse_wires_subset c (dst.take xs.length)
  have hxr := xorWhenFalse_wires_subset c dst
  intro q hq
  simp only [signedSquareRow,wires_append,Finset.mem_union] at hq
  rcases hq with (hq|hq)|hq
  · have h := hxl hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    have ht : q∈dst.take xs.length → q∈dst := List.mem_of_mem_take
    grind
  · rw [ha] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp' : q∈pad.take 1 → q∈pad := List.mem_of_mem_take
    have hc' : q∈carry.take xs.length → q∈carry := List.mem_of_mem_take
    grind
  · have h := hxr hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    grind

theorem signedSquareRowClear_wires_subset (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    wires (signedSquareRowClear c xs dst pad carry)⊆
      (c::xs++dst++pad++carry).toFinset := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have hk : (carry.take xs.length).length+1=dst.length := by simp [hd,hc]
  have ha := addInPlace_wires (xs++pad.take 1) dst (carry.take xs.length) c hs hk
  have hxl := xorWhenFalse_wires_subset c (dst.take xs.length)
  have hxr := xorWhenFalse_wires_subset c dst
  intro q hq
  simp only [signedSquareRowClear,wires_append,Finset.mem_union,notRegister_wires] at hq
  rcases hq with hq|hq|hq|hq|hq
  · have h := hxr hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    grind
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    grind
  · rw [ha] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp' : q∈pad.take 1 → q∈pad := List.mem_of_mem_take
    have hc' : q∈carry.take xs.length → q∈carry := List.mem_of_mem_take
    grind
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    grind
  · have h := hxl hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    have ht : q∈dst.take xs.length → q∈dst := List.mem_of_mem_take
    grind

theorem signedSquareTop_wires_subset (xs dst : List Wire) :
    wires (signedSquareTop xs dst)⊆(xs++dst).toFinset := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,wires]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,wires]
        | cons z zs => simp [signedSquareTop,wires,Instr.wires]
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,wires]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,wires]
        | cons b tail =>
          intro q hq
          have h := ih tail hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at h ⊢
          tauto

theorem signedSquareRows_wires_subset (xs dst pad carry : List Wire)
    (hd : dst.length=2*xs.length) (hp : xs.length≤1 ∨ 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    wires (signedSquareRows xs dst pad carry)⊆(xs++dst++pad++carry).toFinset ∧
      wires (signedSquareRowsClear xs dst pad carry)⊆
        (xs++dst++pad++carry).toFinset := by
  induction xs generalizing dst with
  | nil => simp [signedSquareRows,signedSquareRowsClear,wires]
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedSquareRows,signedSquareRowsClear,wires]
    | cons d tail =>
      simp only [List.length_cons] at hd hp hc
      let rest := d::tail
      let row := (dst.drop 1).take (rest.length+1)
      let dst2 := dst.drop 2
      have hpad : 1≤pad.length := by rcases hp with hp|hp <;> omega
      have hcarry : rest.length≤carry.length := by dsimp [rest]; omega
      have rowLen : row.length=rest.length+1 := by
        apply List.length_take_of_le
        dsimp [row,rest]
        simp
        omega
      have dst2Len : dst2.length=2*rest.length := by
        dsimp [dst2,rest]
        simp
        omega
      have hrecCarry : rest.length-1≤carry.length := by omega
      have hr := signedSquareRow_wires_subset c rest row pad carry rowLen hpad hcarry
      have hrc := signedSquareRowClear_wires_subset c rest row pad carry rowLen hpad hcarry
      have hi := ih dst2 dst2Len (Or.inr hpad) hrecCarry
      have rowMem (q : Wire) (hq : q∈row) : q∈dst :=
        List.mem_of_mem_drop (List.mem_of_mem_take hq)
      have dst2Mem (q : Wire) (hq : q∈dst2) : q∈dst := List.mem_of_mem_drop hq
      constructor
      · intro q hq
        simp only [signedSquareRows,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq
        · have h := hr hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hi.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
      · intro q hq
        simp only [signedSquareRowsClear,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq
        · have h := hi.2 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hrc hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroSignedSquareResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroSignedSquareInverse.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem cuccaroMaj_proper (a b cin : Wire) (hnd : [a,b,cin].Nodup) :
    ProperProgram (cuccaroMaj a b cin) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hnd
  obtain ⟨⟨hab,hac⟩,hbc⟩ := hnd
  simp [cuccaroMaj,ProperProgram,ProperGate,hab,hac,
    Ne.symm hab,Ne.symm hac]

theorem cuccaroUma_proper (a b cin : Wire) (hnd : [a,b,cin].Nodup) :
    ProperProgram (cuccaroUma a b cin) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hnd
  obtain ⟨⟨hab,hac⟩,hbc⟩ := hnd
  simp [cuccaroUma,ProperProgram,ProperGate,hac,
    Ne.symm hab,Ne.symm hac,Ne.symm hbc]

theorem cuccaroAdd_proper (a b : List Wire) (cin : Wire)
    (hnd : (cin::a++b).Nodup) : ProperProgram (cuccaroAdd a b cin) := by
  induction a generalizing b cin with
  | nil => cases b <;> simp [cuccaroAdd,ProperProgram]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases b with
      | nil => simp [cuccaroAdd,ProperProgram]
      | cons y ys =>
        cases ys with
        | nil =>
          have hxy : x≠y := by
            intro e; subst y
            have h := List.nodup_iff_count.mp hnd x
            simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
            omega
          have hcy : cin≠y := by
            intro e; subst cin
            have h := List.nodup_iff_count.mp hnd y
            simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
            omega
          simpa [cuccaroAdd,ProperProgram,ProperGate] using And.intro hxy hcy
        | cons y' ys' => simp [cuccaroAdd,ProperProgram]
    | cons x' xs' =>
      cases b with
      | nil => simp [cuccaroAdd,ProperProgram]
      | cons y ys =>
        cases ys with
        | nil => simp [cuccaroAdd,ProperProgram]
        | cons y' ys' =>
          have n0 := List.nodup_cons.mp hnd
          have nap := List.nodup_append'.mp n0.2
          have na := List.nodup_cons.mp nap.1
          have nb := List.nodup_cons.mp nap.2.1
          have dis := nap.2.2
          have hcx : cin≠x := fun e => n0.1 (by simp [e])
          have hcy : cin≠y := fun e => n0.1 (by simp [e])
          have hxy : x≠y := fun e =>
            List.disjoint_left.mp dis (List.mem_cons_self) (by simp [e])
          have h3 : [x,y,cin].Nodup := by
            simp [hxy,Ne.symm hcx,Ne.symm hcy]
          have ht : (x::(x'::xs')++(y'::ys')).Nodup := by
            apply List.nodup_append'.mpr
            refine ⟨nap.1,(List.nodup_cons.mp nap.2.1).2,?_⟩
            apply List.disjoint_left.mpr
            intro q hqa hqb
            exact List.disjoint_left.mp dis hqa (List.mem_cons_of_mem y hqb)
          simp only [cuccaroAdd,properProgram_append]
          exact ⟨cuccaroMaj_proper x y cin h3,⟨ih (y'::ys') x ht,
            cuccaroUma_proper x y cin h3⟩⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroNormalizeProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroNormalizedMod.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Shared physical layout for normalize/use/uncompute.  The 256-bit `work`
word is reused by normalization and modular arithmetic. -/
structure CuccaroNormalizedModLayout where
  src : List Wire
  srcHigh : Wire
  out : List Wire
  outHigh : Wire
  work : List Wire
  workHigh : Wire
  cin : Wire
  normFlag : Wire
  modFlag : Wire

namespace CuccaroNormalizedModLayout

end CuccaroNormalizedModLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroNormalizedModProof.lean
noncomputable section

set_option maxHeartbeats 8000000

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareFold.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 将来源左移 j 位并补零到固定宽度；两段补零互不重叠。 -/
def shiftedSource (src pad : List Wire) (j width : Nat) : List Wire :=
  pad.take j ++ src ++ (pad.drop j).take (width-j-src.length)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/SquareReduction.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.SquareReduction

def B : Nat := 2^256
def c : Nat := 2^32 + 977
def p : Nat := B-c

end ECDSAAdd.Arithmetic.SquareReduction
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquare.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic

/-- Exact low-width workspace for a `with_square` schedule.  `product` holds
only the currently active Karatsuba leaf.  `work` is reused as the signed
square mask while the leaf is built and as modular scratch while it is folded. -/
structure CuccaroStreamedSquareLayout where
  y : List Wire
  out : List Wire
  product : List Wire
  pad : List Wire
  work : List Wire
  productHigh : Wire
  outHigh : Wire
  workHigh : Wire
  cin : Wire
  normFlag : Wire
  modFlag : Wire
  sumCarry : Wire

namespace CuccaroStreamedSquareLayout

def wires (L : CuccaroStreamedSquareLayout) : List Wire :=
  L.y++L.out++L.product++L.pad++L.work++
    [L.productHigh,L.outHigh,L.workHigh,L.cin,L.normFlag,L.modFlag,L.sumCarry]

structure Widths (L : CuccaroStreamedSquareLayout) : Prop where
  y : L.y.length=256
  out : L.out.length=256
  product : L.product.length=258
  pad : L.pad.length=128
  work : L.work.length=256

def low (L : CuccaroStreamedSquareLayout) : List Wire := L.y.take 128
def high (L : CuccaroStreamedSquareLayout) : List Wire := (L.y.drop 128).take 128
def sum (L : CuccaroStreamedSquareLayout) : List Wire := L.high++[L.sumCarry]

def prepareSum (L : CuccaroStreamedSquareLayout) : Program :=
  cuccaroAdd (L.low++[L.pad.getD 0 0]) L.sum L.cin

def clearSum (L : CuccaroStreamedSquareLayout) : Program := L.prepareSum.reverse

theorem low_length (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    L.low.length=128 := by simp [low,hw.y]

theorem high_length (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    L.high.length=128 := by simp [high,hw.y]

theorem sum_length (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    L.sum.length=129 := by simp [sum,L.high_length hw]

theorem sum_counts (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    (toffoliCount L.prepareSum=256 ∧ measurementCount L.prepareSum=0) ∧
    (toffoliCount L.clearSum=256 ∧ measurementCount L.clearSum=0) := by
  have h := cuccaroAdd_counts (L.low++[L.pad.getD 0 0]) L.sum L.cin (by
    simp [L.low_length hw,L.sum_length hw])
  constructor
  · constructor
    · change toffoliCount (cuccaroAdd (L.low++[L.pad.getD 0 0]) L.sum L.cin)=256
      rw [h.1,L.sum_length hw]
    · simpa [prepareSum] using h.2
  · rw [clearSum,toffoliCount_reverse,measurementCount_reverse]
    constructor
    · change toffoliCount (cuccaroAdd (L.low++[L.pad.getD 0 0]) L.sum L.cin)=256
      rw [h.1,L.sum_length hw]
    · simpa [prepareSum] using h.2

end CuccaroStreamedSquareLayout

/-- Provisional exact fold layout.  The extra 126 clean sites make every
short NAF source, including the two-bit cross-term overhang at shift 128,
an explicit 256-bit word.  They are the only sites that must disappear to
move the executable version from 1,296 Q to the 1,170-Q core envelope. -/
structure CuccaroStreamedSquareWideLayout where
  core : CuccaroStreamedSquareLayout
  overflowPad : List Wire

namespace CuccaroStreamedSquareWideLayout

def wires (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.core.wires++L.overflowPad

structure Widths (L : CuccaroStreamedSquareWideLayout) : Prop where
  core : L.core.Widths
  overflowPad : L.overflowPad.length=126

def foldPad (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.core.pad++L.overflowPad

def shifted (L : CuccaroStreamedSquareWideLayout) (src : List Wire) (j : Nat) : List Wire :=
  shiftedSource src L.foldPad j 256

def rotated128 (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  (L.core.product.drop 128).take 128++L.core.product.take 128

def rotateFull (src : List Wire) (j : Nat) : List Wire :=
  src.drop (256-j)++src.take (256-j)

theorem foldPad_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]

end CuccaroStreamedSquareWideLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedDiagonal.lean
noncomputable section

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def mappedDiagSub (xs dst carry : List Wire) (cin : Wire) : Program :=
  mappedSub (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

def mappedDiagAdd (xs dst carry : List Wire) (cin : Wire) : Program :=
  mappedAdd (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

theorem mappedDiagonal_wires (xs : List Wire) :
    mappedWires (mappedDiagonal xs)=xs++xs.take (xs.length-1) := by
  simp only [mappedDiagonal,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    Option.toList_none,List.nil_append,List.append_nil]
  rw [show List.flatMap (fun b : MappedBit => b.wire.toList) (mappedRead xs false)=xs from
    mappedRead_wires xs false]
  rw [show List.flatMap (fun b : MappedBit => b.wire.toList)
      (mappedRead (xs.take (xs.length-1)) true)=xs.take (xs.length-1) from
    mappedRead_wires _ true]

theorem mappedDiagonal_exact (xs : List Wire) (s : BasisState) (hx : 0<xs.length) :
    mappedValue (mappedDiagonal xs) s=signedDiagValue (regValue xs s) xs.length := by
  have takeValue : regValue (xs.take (xs.length-1)) s=regValue xs s%2^(xs.length-1) := by
    have eq := regValue_append (xs.take (xs.length-1)) (xs.drop (xs.length-1)) s
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (Nat.sub_le xs.length 1)] at eq
    rw [eq,Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by
      simpa only [List.length_take,Nat.min_eq_left (Nat.sub_le xs.length 1)] using regValue_lt (xs.take (xs.length-1)) s)).symm
  rw [mappedDiagonal_value,takeValue]
  simp [signedDiagValue,show xs.length≠0 by omega,Nat.mul_comm]

private theorem mapped_diag_views (cin : Wire) (xs dst carry : List Wire)
    (hn : (cin::xs++dst++carry).Nodup) :
    (cin::dst++carry.take (dst.length-1)).Nodup ∧
      (∀q∈mappedWires (mappedDiagonal xs),q∉cin::dst++carry.take (dst.length-1)) := by
  constructor
  · apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (dst.length-1) carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  · intro q hq bad
    rw [mappedDiagonal_wires] at hq
    have src : q∈xs := by
      rcases List.mem_append.mp hq with h|h
      · exact h
      · exact List.mem_of_mem_take h
    have h := List.nodup_iff_count.mp hn q
    have pos := List.count_pos_iff.mpr src
    have b := List.count_pos_iff.mpr bad
    have takeBound := (List.take_sublist (dst.length-1) carry).count_le q
    simp only [List.count_cons,List.count_append] at h b
    omega

theorem mappedDiagSub_correct (cin : Wire) (xs dst carry : List Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (m : List Bool) (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (mappedDiagSub xs dst carry cin) m s).phase=s.phase ∧
    regValue dst (run (mappedDiagSub xs dst carry cin) m s).basis=
      (regValue dst s.basis+2^dst.length-signedDiagValue (regValue xs s.basis) xs.length)%2^dst.length ∧
    ∀q,q∉dst → (run (mappedDiagSub xs dst carry cin) m s).basis q=s.basis q := by
  have views := mapped_diag_views cin xs dst carry hn
  have len : (mappedDiagonal xs).length=dst.length := (mappedDiagonal_length xs hx).trans hd.symm
  have cl : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
  obtain ⟨phase,same,value⟩ := mappedSub_correct (mappedDiagonal xs) dst (carry.take (dst.length-1))
    cin views.1 views.2 len cl s m (fun q hq =>
      (regValue_zero _ _).mp hclean q (List.mem_of_mem_take hq)) hi
  exact ⟨phase,by simpa only [mappedDiagonal_exact xs s.basis hx] using value,same⟩

theorem mappedDiagAdd_correct (cin : Wire) (xs dst carry : List Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (m : List Bool) (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (mappedDiagAdd xs dst carry cin) m s).phase=s.phase ∧
    regValue dst (run (mappedDiagAdd xs dst carry cin) m s).basis=
      (regValue dst s.basis+signedDiagValue (regValue xs s.basis) xs.length)%2^dst.length ∧
    ∀q,q∉dst → (run (mappedDiagAdd xs dst carry cin) m s).basis q=s.basis q := by
  have views := mapped_diag_views cin xs dst carry hn
  have len : (mappedDiagonal xs).length=dst.length := (mappedDiagonal_length xs hx).trans hd.symm
  have cl : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
  obtain ⟨phase,same,value⟩ := mappedAdd_correct (mappedDiagonal xs) dst (carry.take (dst.length-1))
    cin views.1 views.2 len cl s m (fun q hq =>
      (regValue_zero _ _).mp hclean q (List.mem_of_mem_take hq))
  exact ⟨phase,by simpa [hi,mappedDiagonal_exact xs s.basis hx,Nat.add_comm] using value,same⟩

theorem mappedDiag_counts (xs dst carry : List Wire) (cin : Wire)
    (hx : 0<xs.length) (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length) :
    (toffoliCount (mappedDiagSub xs dst carry cin)=dst.length-1 ∧
      measurementCount (mappedDiagSub xs dst carry cin)=dst.length-1) ∧
    (toffoliCount (mappedDiagAdd xs dst carry cin)=dst.length-1 ∧
      measurementCount (mappedDiagAdd xs dst carry cin)=dst.length-1) := by
  have len : (mappedDiagonal xs).length=dst.length := (mappedDiagonal_length xs hx).trans hd.symm
  have cl : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
  exact ⟨mappedSub_counts _ _ _ _ len cl,mappedAdd_counts _ _ _ _ len cl⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedSignedSquare.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- The signed rows are unchanged; the diagonal reads the source directly
and therefore needs no additional mask register while the source mask is live. -/
def mappedSignedSquare (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  signedSquareRows xs dst pad carry++signedSquareTop xs dst++mappedDiagSub xs dst carry cin

def mappedSignedSquareClear (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  mappedDiagAdd xs dst carry cin++signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry

theorem mappedSignedSquare_counts (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    (toffoliCount (mappedSignedSquare xs dst pad carry cin)=
        signedSquareRowsCount xs.length+dst.length-1 ∧
      measurementCount (mappedSignedSquare xs dst pad carry cin)=
        signedSquareRowsCount xs.length+dst.length-1) ∧
    (toffoliCount (mappedSignedSquareClear xs dst pad carry cin)=
        signedSquareRowsCount xs.length+dst.length-1 ∧
      measurementCount (mappedSignedSquareClear xs dst pad carry cin)=
        signedSquareRowsCount xs.length+dst.length-1) := by
  have rows := signedSquareRows_counts xs dst pad carry hd (Or.inr hp) (by omega)
  have diag := mappedDiag_counts xs dst carry cin (by omega) hd hc
  simp only [mappedSignedSquare,mappedSignedSquareClear,toffoliCount_append,measurementCount_append,
    signedSquareTop_toffoliCount,signedSquareTop_measurementCount,rows.1.1,rows.1.2,
    rows.2.1,rows.2.2,diag.1.1,diag.1.2,diag.2.1,diag.2.2]
  constructor <;> constructor <;> omega

theorem mappedSignedSquare_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (mappedSignedSquare xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (mappedSignedSquare xs dst pad carry cin) records s).basis=(regValue xs s.basis)^2 ∧
    ∀q,q∉dst → (run (mappedSignedSquare xs dst pad carry cin) records s).basis q=s.basis q := by
  let rows := signedSquareRows xs dst pad carry
  let top := signedSquareTop xs dst
  let diag := mappedDiagSub xs dst carry cin
  let rest := records.drop (measurementCount rows)
  let u := run rows (records.take (measurementCount rows)) s
  let v := run top (rest.take (measurementCount top)) u
  let out := run diag (rest.drop (measurementCount top)) v
  have ndRows : (xs++dst++pad++carry).Nodup := (List.nodup_cons.mp hn).2
  have ndTop : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndDiag : (cin::xs++dst++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have away (q : Wire) (hq : q∈cin::xs++pad++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  have high0 : regValue (dst.drop xs.length) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp h0 q (List.mem_of_mem_drop hq))
  have work0 : regValue (pad++carry) s.basis=0 := by simp [regValue_append,hp0,hc0]
  have rc := signedSquareRows_correct xs dst pad carry ndRows hd (Or.inr hp)
    (by omega) s (records.take (measurementCount rows)) 0 h0 high0 work0
  have tc := signedSquareTop_correct xs dst ndTop hd u (rest.take (measurementCount top)) rc.2.2.2.2
  have keepRows (q : Wire) (hq : q∉dst) : u.basis q=s.basis q := rc.2.2.1 q hq
  have keepTop (q : Wire) (hq : q∉dst) : v.basis q=u.basis q := tc.2.2.1 q hq
  have source : regValue xs v.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => (keepTop q (away q (by simp [hq]))).trans
      (keepRows q (away q (by simp [hq]))))
  have carryV : regValue carry v.basis=0 := by
    rw [←hc0]
    apply regValue_congr
    intro q hq
    exact (keepTop q (away q (by simp [hq]))).trans (keepRows q (away q (by simp [hq])))
  have cin0 : v.basis cin=false :=
    ((keepTop cin (away cin (by simp))).trans (keepRows cin (away cin (by simp)))).trans hi0
  have topSame : signedTopTerm xs u.basis=signedTopTerm xs s.basis := by
    apply signedTopTerm_congr
    intro q hq
    exact keepRows q (away q (by simp [hq]))
  have raw : regValue dst v.basis=signedRawValue xs s.basis := by
    rw [tc.2.1,rc.2.1,topSame]
    simp only [Nat.zero_add]
    exact (signedRawValue_rows_top xs s.basis).symm
  have dc := mappedDiagSub_correct cin xs dst carry ndDiag (by omega) hd hc v
    (rest.drop (measurementCount top)) carryV cin0
  have final : out.phase=s.phase ∧ regValue dst out.basis=(regValue xs s.basis)^2 ∧
      ∀q,q∉dst → out.basis q=s.basis q := by
    refine ⟨dc.1.trans (tc.1.trans rc.1),?_,?_⟩
    · rw [dc.2.1,raw,source]
      have rawEq := signedRawValue_correct xs s.basis (List.ne_nil_of_length_pos (by omega))
      have bound := square_bound (regValue xs s.basis) xs.length (regValue_lt xs s.basis)
      rw [rawEq,hd]
      have eq : (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length+
          2^(2*xs.length)-signedDiagValue (regValue xs s.basis) xs.length=
          (regValue xs s.basis)^2+2^(2*xs.length) := by omega
      rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt bound]
    · intro q hq
      exact (dc.2.2 q hq).trans ((keepTop q hq).trans (keepRows q hq))
  simpa [mappedSignedSquare,rows,top,diag,rest,u,v,out,run_append] using final

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/ExactStreamedFold.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- A canonical sum's extended carry and trial comparison are disjoint.
Their sum is the single modular-reduction flag. -/
theorem exactFold_reduction_flag (B c p X A : Nat)
    (hB : p+c=B) (hc : 0<c) (hX : X<p) (hA : A<p) :
    (if B≤X+A then 1 else 0)+(if p≤(X+A)%B then 1 else 0)=
      (if p≤X+A then 1 else 0) := by
  by_cases h : X+A<B
  · rw [if_neg (by omega : ¬ B≤X+A),Nat.mod_eq_of_lt h]
    simp
  · have hmod : (X+A)%B=X+A-B := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [hmod,if_pos (by omega : B≤X+A),if_neg (by omega : ¬p≤X+A-B),
      if_pos (by omega : p≤X+A)]

/-- The output/source comparison recovers the reduction flag for all
canonical operands; no truncated comparison or random-input assumption. -/
theorem exactFold_recover_flag (X A p : Nat) (hX : X<p) (hA : A<p) :
    ((X+A)%p<A ↔ p≤X+A) := by
  have h := modAddCore_cleanup A X p (by omega) hX
  rw [Nat.add_comm A X] at h
  omega

/-- No integer square has low three bits 111. -/
theorem exactFold_square_mod8 (Y : Nat) : Y^2%8≠7 := by
  have bound := Nat.mod_lt Y (by decide : 0<8)
  rw [Nat.pow_mod]
  interval_cases h : Y%8 <;> norm_num

/-- The unrotated 128-bit leaf square is already canonical. -/
theorem exactFold_leaf128_canonical (Y : Nat) (hY : Y<2^128) :
    Y^2<SquareReduction.p := by
  have hy : Y≤2^128-1 := by omega
  have hp : (2^128-1)^2<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  nlinarith

/-- Rotating a square's low 256 bits by 128 cannot enter [p,2^256):
that interval would require the square's low 128 bits to be all ones. -/
theorem exactFold_rotate128_canonical (Y : Nat) :
    (Y^2%2^256)/2^128+(Y^2%2^128)*2^128<SquareReduction.p := by
  let H : Nat := 2^128
  let P : Nat := Y^2%2^256
  have hh : 0<H := by norm_num [H]
  have hP : P<H*H := by
    have := Nat.mod_lt (Y^2) (by positivity : 0<2^256)
    norm_num [P,H] at *
    exact this
  have hi : P/H<H := by
    have := Nat.mod_add_div P H
    by_contra! bad
    have b := Nat.mul_le_mul_left H bad
    omega
  have hlo : Y^2%H<H := Nat.mod_lt _ hh
  have h8 : H%8=0 := by norm_num [H]
  have he : (Y^2%H)%8=Y^2%8 := by
    conv_rhs => rw [←Nat.mod_add_div (Y^2) H]
    simp [Nat.add_mod,Nat.mul_mod,h8]
  have hmax : Y^2%H≠H-1 := by
    intro bad
    have hres := exactFold_square_mod8 Y
    rw [←he,bad] at hres
    norm_num [H] at hres
  have hlt : Y^2%H≤H-2 := by omega
  have hp : H*H-H-1<SquareReduction.p := by
    norm_num [H,SquareReduction.p,SquareReduction.B,SquareReduction.c]
  change P/H+(Y^2%H)*H<SquareReduction.p
  have hi' : P/H≤H-1 := by omega
  have prod := Nat.mul_le_mul_right H hlt
  norm_num [H,SquareReduction.p,SquareReduction.B,SquareReduction.c] at *
  omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/MeasuredCanonicalCore.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- The two disjoint reduction conditions combine by XOR, rather than
leaving two independent flags that would need separate predicate recovery. -/
theorem canonical_flag_bool (B c p X A : Nat)
    (hB : p+c=B) (hc : 0<c) (hX : X<p) (hA : A<p) :
    (decide (p≤(X+A)%B) ^^ decide (B≤X+A))=decide (p≤X+A) := by
  have h := exactFold_reduction_flag B c p X A hB hc hX hA
  by_cases q : B≤X+A <;> by_cases d : p≤(X+A)%B <;> by_cases r : p≤X+A <;>
    simp [q,d,r] at h ⊢

/-- The wide correction is exactly the canonical result plus one radix
when reduction was required. This proves both the output and the high flag. -/
theorem canonical_corrected_extended (B c p X A : Nat)
    (hB : p+c=B) (hX : X<p) (hA : A<p) :
    X+A+c*(if p≤X+A then 1 else 0)=
      (X+A)%p+B*(if p≤X+A then 1 else 0) := by
  by_cases small : X+A<p
  · rw [if_neg (by omega : ¬p≤X+A),Nat.mul_zero,Nat.mul_zero,Nat.add_zero,Nat.add_zero,
      Nat.mod_eq_of_lt small]
  · have mod : (X+A)%p=X+A-p := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [if_pos (by omega : p≤X+A),Nat.mul_one,Nat.mul_one,mod]
    omega

theorem canonical_corrected_bound (B c p X A : Nat)
    (hB : p+c=B) (hc : 0<c) (hX : X<p) (hA : A<p) :
    X+A+c*(if p≤X+A then 1 else 0)<2*B := by
  rw [canonical_corrected_extended B c p X A hB hX hA]
  have hp : 0<p := by omega
  have mod := Nat.mod_lt (X+A) hp
  split_ifs <;> omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredCanonicalModProof.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.MeasuredCanonicalModLayout

/-- Only the output and two temporary flags change within the canonical core. -/
def mutable (L : MeasuredCanonicalModLayout) : List Wire := L.out++[L.high,L.flag]
def Frame (L : MeasuredCanonicalModLayout) (base : BasisState) (O : Nat) (H F : Bool)
    (s : BasisState) : Prop :=
  regValue L.out s=O ∧ s L.high=H ∧ s L.flag=F ∧
    ∀q,q∉L.mutable → s q=base q

theorem protected_away (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.src++L.carry++[L.cin]) : q∉L.mutable := by
  intro bad
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [wires,mutable,List.count_append,List.count_cons,List.count_nil] at h a b
  omega

theorem flags_away (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup) :
    L.high∉L.out ∧ L.flag∉L.extended ∧ L.cin∉L.extended ∧ L.high≠L.flag := by
  constructor
  · intro bad; have h := List.nodup_iff_count.mp hn L.high
    have pos := List.count_pos_iff.mpr bad
    simp only [wires,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  constructor
  · intro bad; have h := List.nodup_iff_count.mp hn L.flag
    have pos := List.count_pos_iff.mpr bad
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h pos
    omega
  constructor
  · intro bad; have h := List.nodup_iff_count.mp hn L.cin
    have pos := List.count_pos_iff.mpr bad
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h pos
    omega
  · intro bad; have h := List.nodup_iff_count.mp hn L.flag
    simp only [wires,bad,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega

theorem Frame.source (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (base s : BasisState) (O : Nat) (H F : Bool) (hf : L.Frame base O H F s) :
    regValue L.src s=regValue L.src base :=
  regValue_congr _ _ _ (fun q hq => hf.2.2.2 q (L.protected_away hn q (by simp [hq])))

theorem Frame.clean (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (base s : BasisState) (O : Nat) (H F : Bool) (hf : L.Frame base O H F s)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    (∀q∈L.carry,s q=false) ∧ s L.cin=false := by
  constructor
  · intro q hq
    exact (hf.2.2.2 q (L.protected_away hn q (by simp [hq]))).trans (hc q hq)
  · exact (hf.2.2.2 L.cin (L.protected_away hn L.cin (by simp))).trans hi

theorem extended_value (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (s : BasisState) : regValue L.extended s=regValue L.out s+2^n*(s L.high).toNat := by
  rw [extended,regValue_append,hw.out]
  simp [regValue,Bool.toNat,Bool.cond_eq_ite]

theorem extended_decode (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (s : BasisState) (V : Nat) (hv : regValue L.extended s=V) :
    regValue L.out s=V%2^n ∧ s L.high=decide (2^n≤V) := by
  have bound : regValue L.out s<2^n := by simpa [hw.out] using regValue_lt L.out s
  rw [L.extended_value n hw] at hv
  cases hh : s L.high
  · simp only [hh,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hv
    subst V
    simp [Nat.mod_eq_of_lt bound,show ¬2^n≤regValue L.out s by omega]
  · simp only [hh,Bool.toNat_true,Nat.mul_one] at hv
    rw [←hv,Nat.add_mod_right,Nat.mod_eq_of_lt bound]
    simp

theorem Frame.afterExtended (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (base s t : BasisState) (O V : Nat) (H F : Bool)
    (hf : L.Frame base O H F s) (he : ∀q,q∉L.extended → t q=s q)
    (hv : regValue L.extended t=V) :
    L.Frame base (V%2^n) (decide (2^n≤V)) F t := by
  have flags := L.flags_away hn
  have decoded := L.extended_decode n hw t V hv
  refine ⟨decoded.1,decoded.2,(he L.flag flags.2.1).trans hf.2.2.1,?_⟩
  intro q hq
  have ex : q∉L.extended := by
    intro bad
    apply hq
    simp only [mutable,extended,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at bad ⊢
    tauto
  exact (he q ex).trans (hf.2.2.2 q hq)

theorem sum_frame (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (base : BasisState) (A X : Nat)
    (hs : regValue L.src base=A) (hb : A+X<2^(n+1))
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base X false false) L.sum
      (L.Frame base ((A+X)%2^n) (decide (2^n≤A+X)) false) := by
  have nd : (L.cin::(L.extended++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  let bits := mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)]
  have bw : mappedWires bits=L.src := by
    simp only [bits,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      Option.toList_none,List.nil_append,List.append_nil]
    exact mappedRead_wires L.src false
  have away : ∀q∈mappedWires bits,q∉L.cin::(L.extended++L.carry) := by
    rw [bw]
    intro q hq bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil] at h b
    omega
  have len : bits.length=L.extended.length := by simp [bits,mappedRead,extended,hw.src,hw.out]
  have carryLen : L.carry.length+1=L.extended.length := by simp [hw.carry,extended,hw.out]
  intro s m hf
  have clean := Frame.clean L hn base s.basis X false false hf hc hi
  have val : mappedValue bits s.basis=A := by
    rw [show bits=mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)] from rfl,
      mappedValue_append,mappedRead_value]
    simp only [mappedValue,MappedBit.value,Option.map_none,Option.getD_none,Bool.xor_false,
      Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
    rw [Frame.source L hn base s.basis X false false hf,hs]
  have ext : regValue L.extended s.basis=X := by
    rw [L.extended_value n hw,hf.1,hf.2.1]
    simp
  obtain ⟨hp,he,hv⟩ := mappedAdd_correct bits L.extended L.carry L.cin nd away len carryLen s m clean.1
  have total : regValue L.extended (run (mappedAdd bits L.extended L.carry L.cin) m s).basis=A+X := by
    rw [hv,val,ext,clean.2,Bool.toNat_false,Nat.add_zero]
    simp [extended,hw.out,Nat.mod_eq_of_lt hb]
  exact ⟨hp,Frame.afterExtended L n hw hn base s.basis _ X (A+X) false false hf he total⟩

theorem ge_frame (L : MeasuredCanonicalModLayout) (n p : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (npos : 0<n) (hp : p<2^n)
    (base : BasisState) (O : Nat) (H F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base O H F)
      (compareConstantGe L.out (L.carry.take (L.out.length-1)) L.cin L.flag p)
      (L.Frame base O H (F ^^ decide (p≤O))) := by
  have nd : (L.flag::L.cin::(L.out++L.carry.take (L.out.length-1))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (L.out.length-1) L.carry).count_le q
    simp only [wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have carryLen : (L.carry.take (L.out.length-1)).length+1=L.out.length := by
    simp [hw.carry,hw.out]; omega
  have away := L.flags_away hn
  intro s m hf
  have clean := Frame.clean L hn base s.basis O H F hf hc hi
  obtain ⟨phase,same,value⟩ := compareConstantGe_correct L.out (L.carry.take (L.out.length-1))
    L.cin L.flag p nd carryLen (by simpa [hw.out] using hp) s m clean.2
    (fun q hq => clean.1 q (List.mem_of_mem_take hq))
  refine ⟨phase,?_,(same L.high away.2.2.2).trans hf.2.1,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    exact same q (fun bad => away.2.1 (by simp [extended,←bad,hq]))
  · simpa [hf.1,hf.2.2.1] using value
  · intro q hq
    have ne : q≠L.flag := fun bad => hq (by simp [mutable,bad])
    exact (same q ne).trans (hf.2.2.2 q hq)

theorem cx_flag_frame (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (base : BasisState) (O : Nat) (H F : Bool) :
    Triple (L.Frame base O H F) [.CX L.high L.flag] (L.Frame base O H (F ^^ H)) := by
  have away := L.flags_away hn
  intro s m hf
  simp only [run]
  refine ⟨by trivial,?_,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    have ne : q≠L.flag := fun bad => away.2.1 (by simp [extended,←bad,hq])
    simp [writeBit,ne]
  · simpa [writeBit,away.2.2.2] using hf.2.1
  · simp [writeBit,hf.2.1,hf.2.2.1]
  · intro q hq
    have ne : q≠L.flag := fun bad => hq (by simp [mutable,bad])
    simpa [writeBit,ne] using hf.2.2.2 q hq

theorem cx_high_frame (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (base : BasisState) (O : Nat) (H F : Bool) :
    Triple (L.Frame base O H F) [.CX L.flag L.high] (L.Frame base O (H ^^ F) F) := by
  have away := L.flags_away hn
  intro s m hf
  simp only [run]
  refine ⟨by trivial,?_,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    have ne : q≠L.high := fun bad => away.1 (bad ▸ hq)
    simp [writeBit,ne]
  · simp [writeBit,hf.2.1,hf.2.2.1]
  · simpa [writeBit,Ne.symm away.2.2.2] using hf.2.2.1
  · intro q hq
    have ne : q≠L.high := fun bad => hq (by simp [mutable,bad])
    simpa [writeBit,ne] using hf.2.2.2 q hq

theorem correction_frame (L : MeasuredCanonicalModLayout) (n c : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (hcb : c<2^(n+1)) (base : BasisState)
    (O V : Nat) (H F : Bool) (hv : (if F then c else 0)+O+2^n*H.toNat=V)
    (hvb : V<2^(n+1)) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base O H F) (mappedConstAdd (some L.flag) L.extended L.carry L.cin c)
      (L.Frame base (V%2^n) (decide (2^n≤V)) F) := by
  have nd : (L.cin::(L.extended++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have srcAway : ∀q∈some L.flag,q∉L.cin::(L.extended++L.carry) := by
    intro q hq bad
    have eq : q=L.flag := by simpa [eq_comm] using hq
    subst q
    have h := List.nodup_iff_count.mp hn L.flag
    have pos := List.count_pos_iff.mpr bad
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h pos
    omega
  have carryLen : L.carry.length+1=L.extended.length := by simp [extended,hw.carry,hw.out]
  have cBound : c<2^L.extended.length := by simpa [extended,hw.out] using hcb
  intro s m hf
  have clean := Frame.clean L hn base s.basis O H F hf hc hi
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct (some L.flag) L.extended L.carry L.cin c
    nd srcAway carryLen cBound s m clean.1
  have total : regValue L.extended (run (mappedConstAdd (some L.flag) L.extended L.carry L.cin c) m s).basis=V := by
    rw [value,L.extended_value n hw,hf.1,hf.2.1,clean.2,Bool.toNat_false,Nat.add_zero]
    simp only [mappedEnabled,Option.map_some,Option.getD_some,hf.2.2.1]
    rw [show (if F then c else 0)+(O+2^n*H.toNat)=V by omega]
    simp [extended,hw.out,Nat.mod_eq_of_lt hvb]
  exact ⟨phase,Frame.afterExtended L n hw hn base s.basis _ O V H F hf same total⟩

theorem erase_frame (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (npos : 0<n) (base : BasisState) (A R : Nat) (H : Bool)
    (ha : regValue L.src base=A) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base R H (decide (R<A)))
      (eraseLtChain L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag)
      (L.Frame base R H false) := by
  have nd : (L.flag::L.cin::(L.out++L.src++L.carry.take (L.out.length-1))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (L.out.length-1) L.carry).count_le q
    simp only [wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have carryLen : (L.carry.take (L.out.length-1)).length+1=L.src.length := by
    simp [hw.carry,hw.out,hw.src]; omega
  have away := L.flags_away hn
  intro s m hf
  have clean := Frame.clean L hn base s.basis R H (decide (R<A)) hf hc hi
  have src : regValue L.src s.basis=A := (Frame.source L hn base s.basis R H _ hf).trans ha
  have pred : s.basis L.flag=decide (regValue L.out s.basis<
      regValue L.src s.basis+(s.basis L.cin).toNat) := by
    rw [hf.1,src,clean.2,Bool.toNat_false,Nat.add_zero,hf.2.2.1]
  rw [eraseLtChain_correct L.out L.src _ L.cin L.flag nd (hw.out.trans hw.src.symm)
    carryLen s m (fun q hq => clean.1 q (List.mem_of_mem_take hq)) pred]
  refine ⟨by trivial,?_,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    have ne : q≠L.flag := fun bad => away.2.1 (by simp [extended,←bad,hq])
    simp [writeBit,ne]
  · simpa [writeBit,away.2.2.2] using hf.2.1
  · simp [writeBit]
  · intro q hq
    have ne : q≠L.flag := fun bad => hq (by simp [mutable,bad])
    simpa [writeBit,ne] using hf.2.2.2 q hq

/-- Functional composition of the complete canonical modular-add core.
The single reduction flag and extended high bit both return to zero. -/
theorem program_frame (L : MeasuredCanonicalModLayout) (n c p : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (npos : 0<n) (hpc : p+c=2^n) (hcp : 0<c)
    (base : BasisState) (A X : Nat) (ha : regValue L.src base=A)
    (hA : A<p) (hX : X<p) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base X false false) (L.program c p)
      (L.Frame base ((A+X)%p) false false) := by
  let B := 2^n
  let S := A+X
  let U := S%B
  let Q := decide (B≤S)
  let D := decide (p≤U)
  let r := decide (p≤S)
  let R := S%p
  let V := S+(if r then c else 0)
  have ppos : 0<p := by omega
  have bpos : 0<B := by dsimp [B]; positivity
  have pb : p<B := by dsimp [B]; omega
  have wideBound : S<2^(n+1) := by dsimp [S]; rw [Nat.pow_succ]; omega
  have doubleBound : S<2*B := by
    dsimp [B]
    rw [Nat.pow_succ] at wideBound
    omega
  have cBound : c<2^(n+1) := by rw [Nat.pow_succ]; omega
  have Rb : R<B := lt_trans (Nat.mod_lt S ppos) pb
  have combined : (D ^^ Q)=r := canonical_flag_bool B c p A X hpc hcp hA hX
  have split : U+B*Q.toNat=S := by
    by_cases small : S<B
    · simp [U,Q,Nat.mod_eq_of_lt small,show ¬B≤S by omega]
    · have mod : S%B=S-B := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      simp only [U,Q,mod,show B≤S by omega,decide_true,Bool.toNat_true,Nat.mul_one]
      omega
  have corrected : V=R+B*r.toNat := by
    have eq := canonical_corrected_extended B c p A X hpc hA hX
    by_cases reduce : p≤S <;> simpa [V,R,r,S,reduce] using eq
  have Vb : V<2^(n+1) := by
    have bound := canonical_corrected_bound B c p A X hpc hcp hA hX
    rw [Nat.pow_succ]
    by_cases reduce : p≤S <;> simpa [V,r,S,B,reduce,Nat.mul_comm] using bound
  have low : V%B=R := by
    rw [corrected,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt Rb]
  have high : decide (B≤V)=r := by
    rw [corrected]
    cases hr : r <;> simp [hr,show ¬B≤R by omega]
  have flagPred : r=decide (R<A) := by
    apply decide_eq_decide.mpr
    simpa [R,S,Nat.add_comm] using (exactFold_recover_flag X A p hX hA).symm
  have s1 := L.sum_frame n hw hn base A X ha wideBound hc hi
  have s2 : Triple (L.Frame base U Q false)
      (compareConstantGe L.out (L.carry.take (L.out.length-1)) L.cin L.flag p)
      (L.Frame base U Q D) := by
    simpa [D] using L.ge_frame n p hw hn npos pb base U Q false hc hi
  have s3 : Triple (L.Frame base U Q D) [.CX L.high L.flag] (L.Frame base U Q r) := by
    simpa only [combined] using L.cx_flag_frame hn base U Q D
  have s4 : Triple (L.Frame base U Q r)
      (mappedConstAdd (some L.flag) L.extended L.carry L.cin c) (L.Frame base R r r) := by
    have val : (if r then c else 0)+U+2^n*Q.toNat=V := by
      change (if r then c else 0)+U+B*Q.toNat=V
      dsimp [V]
      omega
    have h := L.correction_frame n c hw hn cBound base U V Q r val Vb hc hi
    change Triple (L.Frame base U Q r)
      (mappedConstAdd (some L.flag) L.extended L.carry L.cin c)
      (L.Frame base (V%B) (decide (B≤V)) r) at h
    simpa only [low,high] using h
  have s5 : Triple (L.Frame base R r r) [.CX L.flag L.high] (L.Frame base R false r) := by
    simpa using L.cx_high_frame hn base R r r
  have s6 : Triple (L.Frame base R false r)
      (eraseLtChain L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag)
      (L.Frame base R false false) := by
    rw [flagPred]
    exact L.erase_frame n hw hn npos base A R false ha hc hi
  have all := (((s1.seq s2).seq s3).seq s4).seq s5 |>.seq s6
  simpa only [program,List.append_assoc] using all

/-- All valid canonical inputs and all measurement outcomes: exact sum
modulo p, phase restoration and full workspace/control/source preservation. -/
theorem program_correct (L : MeasuredCanonicalModLayout) (n c p : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (npos : 0<n) (hpc : p+c=2^n) (hcp : 0<c)
    (A X : Nat) (hA : A<p) (hX : X<p) (s : State) (m : List Bool)
    (ha : regValue L.src s.basis=A) (hx : regValue L.out s.basis=X)
    (hh : s.basis L.high=false) (hf : s.basis L.flag=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hi : s.basis L.cin=false) :
    (run (L.program c p) m s).phase=s.phase ∧
    regValue L.out (run (L.program c p) m s).basis=(A+X)%p ∧
    ∀q,q∉L.out → (run (L.program c p) m s).basis q=s.basis q := by
  have initial : L.Frame s.basis X false false s.basis := ⟨hx,hh,hf,fun _ _ => rfl⟩
  obtain ⟨phase,post⟩ := L.program_frame n c p hw hn npos hpc hcp s.basis A X ha hA hX hc hi s m initial
  refine ⟨phase,post.1,?_⟩
  intro q hq
  by_cases high : q=L.high
  · subst q; exact post.2.1.trans hh.symm
  by_cases flag : q=L.flag
  · subst q; exact post.2.2.1.trans hf.symm
  exact post.2.2.2 q (by simpa only [mutable,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using ⟨hq,high,flag⟩)

end ECDSAAdd.Arithmetic.MeasuredCanonicalModLayout
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedSquare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

structure MeasuredSquareFold where
  negative : Bool
  canonical : Bool
  src : List Wire
  shift : Nat := 0

namespace CuccaroStreamedSquareWideLayout

def inputBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 129
def leafCarry (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.core.work.drop 129++(L.foldPad.drop 1).take 130
def leafPad (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.take 1
def foldCarry (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.foldPad++[L.core.productHigh,L.core.workHigh]
def shortCarry (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldCarry.take 255

def measuredCore (L : CuccaroStreamedSquareWideLayout) : MeasuredCanonicalModLayout :=
  {src:=L.core.work,out:=L.core.out,carry:=L.foldCarry,
    high:=L.core.outHigh,cin:=L.core.cin,flag:=L.core.modFlag}

def normalizeSource (L : CuccaroStreamedSquareWideLayout) : Program :=
  compareConstantGe L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p++
    mappedConstAdd (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.c

def restoreSource (L : CuccaroStreamedSquareWideLayout) : Program :=
  mappedConstAdd (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.p++
    compareConstantGe L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p

def reflectOutput (L : CuccaroStreamedSquareWideLayout) : Program :=
  notRegister L.core.out++mappedConstAdd none L.core.out L.shortCarry L.core.cin SquareReduction.p

def foldDestination (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) : List Wire :=
  (L.core.work.drop f.shift).take f.src.length

def measuredFold (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) : Program :=
  copyRegister none f.src (L.foldDestination f)++
    (if f.canonical then [] else L.normalizeSource)++
    L.measuredCore.program SquareReduction.c SquareReduction.p++
    (if f.canonical then [] else L.restoreSource)++
    copyRegister none f.src (L.foldDestination f)

/-- The physical output is reflected only when the next signed term needs a
new orientation. No blanket quantum-control wrapper is applied to arithmetic. -/
def measuredFolds (L : CuccaroStreamedSquareWideLayout) : Bool → List MeasuredSquareFold → Program
  | _,[] => []
  | orientation,f::fs =>
      (if orientation=f.negative then [] else L.reflectOutput)++
        L.measuredFold f++L.measuredFolds f.negative fs

def nafMinusOneItems (negative : Bool) (src : List Wire) : List MeasuredSquareFold :=
  [{negative:=negative,canonical:=true,src:=src,shift:=4},
   {negative:=!negative,canonical:=true,src:=src,shift:=6},
   {negative:=negative,canonical:=true,src:=src,shift:=10},
   {negative:=negative,canonical:=true,src:=src,shift:=32}]

def measuredAItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=true,canonical:=true,src:=L.core.product.take 256},
   {negative:=false,canonical:=true,src:=L.rotated128}]++
    nafMinusOneItems false (L.core.product.drop 128)

def shiftedProductItems (negative : Bool) (src : List Wire) (j : Nat) : List MeasuredSquareFold :=
  if j=0 then [{negative:=negative,canonical:=true,src:=src}]
  else [{negative:=negative,canonical:=false,src:=rotateFull src j}]++
    nafMinusOneItems negative (src.drop (256-j))

def measuredBItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=false,canonical:=true,src:=L.rotated128}]++
    nafMinusOneItems false (L.core.product.drop 128)++
    shiftedProductItems true (L.core.product.take 256) 0++
    shiftedProductItems true (L.core.product.take 256) 4++
    shiftedProductItems false (L.core.product.take 256) 6++
    shiftedProductItems true (L.core.product.take 256) 10++
    shiftedProductItems true (L.core.product.take 256) 32

def measuredCItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=true,canonical:=true,src:=L.rotated128}]++
    nafMinusOneItems true (L.core.product.drop 128)++
    [{negative:=true,canonical:=true,src:=L.core.product.drop 256,shift:=128}]

/-- The input mask is measured out before folding, freeing the same work
register for source copies. It is recreated for the independent cleanup. -/
def withMeasuredSquare (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (src dst : List Wire) (body : Program) : Program :=
  copyRegister (some control) src (L.inputBank.take src.length)++
    mappedSignedSquare (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin++
    eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)++
    mappedSignedSquareClear (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin++
    eraseMask control src (L.inputBank.take src.length)

def measuredBranchA (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.low (L.core.product.take 256)
    (L.measuredFolds false L.measuredAItems)
def measuredBranchB (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.high (L.core.product.take 256)
    (L.measuredFolds false L.measuredBItems)
def measuredBranchC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.core.prepareSum++L.withMeasuredSquare control L.core.sum L.core.product
    (L.measuredFolds true L.measuredCItems)++L.core.clearSum

/-- Complete gate-level replacement of the controlled square stage. Its
resource and functional theorems are checked separately before promotion. -/
def measuredProgram (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.measuredBranchA control++L.measuredBranchB control++L.measuredBranchC control++L.reflectOutput

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredGateSupport.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

theorem mappedSub_wires_subset (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (mappedSub bits ys carry cin)⊆(mappedWires bits++ys++carry++[cin]).toFinset := by
  have ha := mappedAdd_wires_subset bits ys carry cin
  intro q hq
  simp only [mappedSub,wires_append,Finset.mem_union,notRegister_wires] at hq
  rcases hq with (hq|hq)|hq
  · simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  · exact ha hq
  · simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto

theorem mappedConstAdd_wires_subset (control : Option Wire) (ys carry : List Wire)
    (cin : Wire) (k : Nat) :
    wires (mappedConstAdd control ys carry cin k)⊆(control.toList++ys++carry++[cin]).toFinset := by
  apply (mappedAdd_wires_subset _ _ _ _).trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  have hc : q∈mappedWires (mappedConstant control ys.length k) → q∈control.toList := by
    intro h
    simpa using mappedConstant_wires control ys.length k q h
  tauto

theorem constantBorrow_wires_subset (b : Bool) (x cin target : Wire) :
    wires (constantBorrow b x cin target)⊆[x,cin,target].toFinset ∧
    wires (constantBorrowErase b x cin target)⊆[x,cin,target].toFinset := by
  have h := mappedBit_wires ({wire:=none,flip:=b} : MappedBit) x cin target
  constructor
  · intro q hq
    simp only [constantBorrow,wires_append,Finset.mem_union] at hq
    have hh : q∈wires (mappedMajority {wire:=none,flip:=b} x cin target) →
        q∈[x,cin,target].toFinset := by
      intro hq
      simpa using h.1 hq
    simp [wires,Instr.wires] at hq hh ⊢
    tauto
  · intro q hq
    simp only [constantBorrowErase,wires_append,Finset.mem_union] at hq
    have hh : q∈wires (mappedEraseCarry {wire:=none,flip:=b} x cin target) →
        q∈[x,cin,target].toFinset := by
      intro hq
      simpa using h.2.1 hq
    simp [wires,Instr.wires] at hq hh ⊢
    tauto

theorem compareConstantLt_wires_subset (xs carry : List Wire) (cin target : Wire) (k : Nat) :
    wires (compareConstantLt xs carry cin target k)⊆(xs++carry++[cin,target]).toFinset := by
  induction xs generalizing carry cin k with
  | nil => simp [compareConstantLt,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      apply (constantBorrow_wires_subset _ _ _ _).1.trans
      intro q hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
      tauto
    | cons x' xs =>
      cases carry with
      | nil => simp [compareConstantLt,wires]
      | cons c cs =>
        have head := constantBorrow_wires_subset (decide (k%2=1)) x cin c
        have tail := ih cs c (k/2)
        intro q hq
        rw [compareConstantLt] at hq
        simp only [wires_append,Finset.mem_union] at hq
        have h1 := head.1
        have h2 := head.2
        rcases hq with (hq|hq)|hq
        · have h := h1 hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
          tauto
        · have h := tail hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
          tauto
        · have h := h2 hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
          tauto

theorem compareConstantGe_wires_subset (xs carry : List Wire) (cin target : Wire) (k : Nat) :
    wires (compareConstantGe xs carry cin target k)⊆(xs++carry++[cin,target]).toFinset := by
  have h := compareConstantLt_wires_subset xs carry cin target k
  intro q hq
  simp only [compareConstantGe,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · exact h hq
  · simp [wires,Instr.wires] at hq ⊢
    tauto

theorem borrowPair_wires_subset (x y cin target : Wire) :
    wires (borrowMajority x y cin target)⊆[x,y,cin,target].toFinset ∧
    wires (eraseBorrow x y cin target)⊆[x,y,cin,target].toFinset := by
  constructor <;> intro q hq <;>
    simp [borrowMajority,eraseBorrow,majority,eraseCarry,wires,Instr.wires,correctionWires] at hq ⊢ <;> tauto

theorem eraseLtChain_wires_subset (xs ys carry : List Wire) (cin target : Wire) :
    wires (eraseLtChain xs ys carry cin target)⊆(xs++ys++carry++[cin,target]).toFinset := by
  induction xs generalizing ys carry cin with
  | nil => simp [eraseLtChain,wires]
  | cons x xs ih =>
    cases ys with
    | nil => simp [eraseLtChain,wires]
    | cons y ys =>
      cases xs with
      | nil =>
        cases ys with
        | nil =>
          apply (borrowPair_wires_subset x y cin target).2.trans
          intro q hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
          tauto
        | cons y' ys => simp [eraseLtChain,wires]
      | cons x' xs =>
        cases ys with
        | nil => simp [eraseLtChain,wires]
        | cons y' ys =>
          cases carry with
          | nil => simp [eraseLtChain,wires]
          | cons c cs =>
            have head := borrowPair_wires_subset x y cin c
            have tail := ih (y'::ys) cs c
            intro q hq
            rw [eraseLtChain] at hq
            simp only [wires_append,Finset.mem_union] at hq
            rcases hq with (hq|hq)|hq
            · have h := head.1 hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
              tauto
            · have h := tail hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
              tauto
            · have h := head.2 hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
              tauto

theorem mappedSignedSquare_wires_subset (xs dst pad carry : List Wire) (cin : Wire)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    wires (mappedSignedSquare xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset ∧
    wires (mappedSignedSquareClear xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
  have rows := signedSquareRows_wires_subset xs dst pad carry hd (Or.inr hp) (by omega)
  have top := signedSquareTop_wires_subset xs dst
  have diagSub := mappedSub_wires_subset (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin
  have diagAdd := mappedAdd_wires_subset (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin
  have ds : wires (mappedDiagSub xs dst carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := diagSub hq
    rw [mappedDiagonal_wires] at h
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    have hs : q∈xs.take (xs.length-1) → q∈xs := List.mem_of_mem_take
    have hcarry : q∈carry.take (dst.length-1) → q∈carry := List.mem_of_mem_take
    tauto
  have da : wires (mappedDiagAdd xs dst carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := diagAdd hq
    rw [mappedDiagonal_wires] at h
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    have hs : q∈xs.take (xs.length-1) → q∈xs := List.mem_of_mem_take
    have hcarry : q∈carry.take (dst.length-1) → q∈carry := List.mem_of_mem_take
    tauto
  have r1 : wires (signedSquareRows xs dst pad carry)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := rows.1 hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have r2 : wires (signedSquareRowsClear xs dst pad carry)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := rows.2 hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have t : wires (signedSquareTop xs dst)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := top hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  constructor <;> intro q hq
  · simp only [mappedSignedSquare,wires_append,Finset.mem_union] at hq
    tauto
  · simp only [mappedSignedSquareClear,wires_append,Finset.mem_union] at hq
    tauto

theorem copyRegister_wires_subset (control : Option Wire) (src dst : List Wire) :
    wires (copyRegister control src dst)⊆(control.toList++src++dst).toFinset := by
  induction src generalizing dst with
  | nil => simp [copyRegister,wires]
  | cons x xs ih =>
    cases dst with
    | nil => simp [copyRegister,wires]
    | cons y ys =>
      intro q hq
      simp only [copyRegister,wires_append,Finset.mem_union] at hq
      rcases hq with head|tail
      · cases control <;> simp [copyGate,wires,Instr.wires] at head ⊢ <;> tauto
      · have h := ih ys tail
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at h ⊢
        tauto

theorem MeasuredCanonicalModLayout.program_wires_subset (L : MeasuredCanonicalModLayout) (c p : Nat) :
    ECDSAAdd.wires (L.program c p)⊆L.wires.toFinset := by
  have sum := mappedAdd_wires_subset
    (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)]) L.extended L.carry L.cin
  have read : mappedWires (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)])=L.src := by
    simp only [mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,Option.toList_none,List.nil_append,List.append_nil]
    exact mappedRead_wires L.src false
  rw [read] at sum
  have ge := compareConstantGe_wires_subset L.out (L.carry.take (L.out.length-1)) L.cin L.flag p
  have add := mappedConstAdd_wires_subset (some L.flag) L.extended L.carry L.cin c
  have erase := eraseLtChain_wires_subset L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag
  have embed1 : (L.src++L.extended++L.carry++[L.cin]).toFinset⊆L.wires.toFinset := by
    intro q hq
    simp [MeasuredCanonicalModLayout.wires,MeasuredCanonicalModLayout.extended] at hq ⊢
    tauto
  have embed2 : (L.out++L.carry.take (L.out.length-1)++[L.cin,L.flag]).toFinset⊆L.wires.toFinset := by
    intro q hq
    have ht : q∈L.carry.take (L.out.length-1) → q∈L.carry := List.mem_of_mem_take
    simp [MeasuredCanonicalModLayout.wires] at hq ⊢
    tauto
  have embed3 : ((some L.flag).toList++L.extended++L.carry++[L.cin]).toFinset⊆L.wires.toFinset := by
    intro q hq
    simp [MeasuredCanonicalModLayout.wires,MeasuredCanonicalModLayout.extended] at hq ⊢
    tauto
  have embed4 : (L.out++L.src++L.carry.take (L.out.length-1)++[L.cin,L.flag]).toFinset⊆L.wires.toFinset := by
    intro q hq
    have ht : q∈L.carry.take (L.out.length-1) → q∈L.carry := List.mem_of_mem_take
    simp [MeasuredCanonicalModLayout.wires] at hq ⊢
    tauto
  have s1 := sum.trans embed1
  have s2 := ge.trans embed2
  have s3 := add.trans embed3
  have s4 := erase.trans embed4
  intro q hq
  simp only [MeasuredCanonicalModLayout.program,MeasuredCanonicalModLayout.sum,
    wires_append,Finset.mem_union] at hq
  have cx1 : q∈ECDSAAdd.wires [Instr.CX L.high L.flag] → q∈L.wires.toFinset := by
    simp [ECDSAAdd.wires,Instr.wires,MeasuredCanonicalModLayout.wires]
    tauto
  have cx2 : q∈ECDSAAdd.wires [Instr.CX L.flag L.high] → q∈L.wires.toFinset := by
    simp [ECDSAAdd.wires,Instr.wires,MeasuredCanonicalModLayout.wires]
    tauto
  rcases hq with ((((hq|hq)|hq)|hq)|hq)|hq
  · exact s1 hq
  · exact s2 hq
  · exact cx1 hq
  · exact s3 hq
  · exact cx2 hq
  · exact s4 hq

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedTranscriptSupport.lean
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic

namespace BalancedConvert
/-- Includes phase-correction controls of every measurement instruction. -/
theorem support (L : Layout) :
    wires (center L)⊆L.wires.toFinset ∧ wires (canonical L)⊆L.wires.toFinset := by
  have a := literalConstAdd_wires L.word L.carry L.cin L.one bias
  have b := literalConstAdd_wires L.word L.carry L.cin L.one inverseBias
  have c := mappedAdd_wires_subset (correction L) L.word L.carry L.cin
  have d := mappedSub_wires_subset (correction L) L.word L.carry L.cin
  have lit (q : Wire) (hq : q∈(L.one::L.cin::(L.word++L.carry)).toFinset) :
      q∈L.wires.toFinset := by
    simp only [Layout.wires,Layout.word,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have mapped (q : Wire) (hq : q∈(mappedWires (correction L)++L.word++L.carry++[L.cin]).toFinset) :
      q∈L.wires.toFinset := by
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with hq|hq|hq|hq
    · have e := correction_sources L q hq
      simp [Layout.wires,e]
    · simp only [Layout.wires,Layout.word,List.mem_toFinset,List.mem_cons,
        List.mem_append,List.not_mem_nil,or_false] at hq ⊢
      tauto
    · simp [Layout.wires,hq]
    · simp [Layout.wires,hq]
  have cx : wires [.CX L.msb L.flag]⊆L.wires.toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false,Layout.wires,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.not_mem_nil] at hq ⊢
    tauto
  have pred : wires (predicate L)⊆L.wires.toFinset := by
    intro q hq
    simp only [predicate,wires_append,Finset.mem_union] at hq
    rcases hq with (hq|hq)|hq
    · exact lit q (a hq)
    · exact cx hq
    · exact lit q (b hq)
  constructor <;> intro q hq
  · simp only [center,wires_append,Finset.mem_union] at hq
    rcases hq with (hq|hq)|hq
    · exact pred hq
    · exact mapped q (c hq)
    · exact cx hq
  · simp only [canonical,wires_append,Finset.mem_union] at hq
    rcases hq with (hq|hq)|hq
    · exact cx hq
    · exact mapped q (d hq)
    · exact pred hq
end BalancedConvert

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseTranscriptKernelSupport.lean
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit
theorem support (L : Layout) (hw : L.Widths) :
    wires (program L) ⊆ L.wires.toFinset := by
  have w := widths L hw
  have cleanup : wires (recoverParity L) ⊆ L.toLayout.wires.toFinset := BalancedCleanup.support L.toLayout hw
  have add := subInPlace_wires (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have comp := signComplement_wires_subset L.sign (rawSource L)
  have mapped := mappedSub_wires_subset (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
  have rot := (rotate_wires (rawTarget L)).2
  have member (q : Wire) : q∈L.wires.toFinset ↔
      q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry := by
    simp [Layout.wires,BalancedCleanup.Layout.wires,or_assoc]
  have raw : wires (rawSubtract L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [rawSubtract,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq
    · have h := comp hq
      simp only [member,rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · rw [add] at hq
      simp only [member,rawSource,rawTarget,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := comp hq
      simp only [member,rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
  have foldSupport : wires (undoFold L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [undoFold,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
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
      | cons a as => simp
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
  · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · have h := cleanup hq
    simp only [BalancedCircuit.Layout.wires,List.mem_toFinset,List.mem_append] at ⊢
    exact Or.inr (List.mem_toFinset.mp h)
  · simp only [recoverSelectors,member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · rw [rot,if_neg (by omega)] at hq
    simp only [member,rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · exact foldSupport hq
  · simp only [undoPreparation,member,wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · exact raw hq
  · rw [wires_reverse] at hq
    exact seed hq
end ECDSAAdd.Arithmetic.BalancedInverse
end

-- source: ECDSAAdd/Arithmetic/BalancedInverseTranscriptSupport.lean
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic

def balancedInverseTranscriptSupport (L : BalancedCircuit.Layout) (b effS : Wire)
    (ls : List MixedTranscriptLetter) : List Wire :=
  [b,effS]++L.wires++ls.flatMap (fun l => [l.1.1,l.1.2])

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BalancedSharedDivision.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Counter.lean
noncomputable section

/-!
10 位计数原语复用 AdderLayout。常用接口 counterInc_spec / counterDec_spec 从
`{{ x=K, y=0, cin=C, out=0, carry=0 }}` 出发，清空 x 并把结果写入 out。
结果分别为 (K+C) mod 1024 和 (K+1024−C) mod 1024；即使 C=false 也交换角色。
下层 XOR 接口保留来源，用于第二次前向调用清除旧值；不反转测量程序。
-/

namespace ECDSAAdd.Arithmetic

private theorem counter_perm (L : AdderLayout) :
    ((L.cin::L.y) ++ (L.x ++ L.out ++ L.carry)).Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  rcases L with ⟨bs, cin⟩
  induction bs with
  | nil => simp [AdderLayout.y, AdderLayout.x, AdderLayout.out, AdderLayout.carry, AdderLayout.wires, addWires]
  | cons b bs ih =>
    simp [AdderLayout.y, AdderLayout.x, AdderLayout.out, AdderLayout.carry,
      AdderLayout.wires, addWires, List.count_cons] at ih ⊢
    omega

private def counterFlip (L : AdderLayout) : Program := notRegister (L.cin::L.y)

/-- 10 位计数器的 XOR 写出；cin 是活动控制位，y 和 carry 是零工作寄存器。 -/
def counterIncXor (L : AdderLayout) : Program := add L

/-- 用补码加法写出 K−C，恢复用于控制的 cin 和全一辅助寄存器。 -/
def counterDecXor (L : AdderLayout) : Program := counterFlip L ++ add L ++ counterFlip L

private theorem counter_wires (L : AdderLayout) (hw : L.width=10) :
    wires (counterIncXor L) = L.wires.toFinset ∧ wires (counterDecXor L) = L.wires.toFinset := by
  have ha : wires (add L) = L.wires.toFinset := by
    cases L with
    | mk bs cin =>
      cases bs with
      | nil => simp [AdderLayout.width] at hw
      | cons b bs => exact rippleAdder_wires b bs cin
  have hs : (L.cin::L.y).toFinset ⊆ L.wires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr ((counter_perm L).mem_iff.mp (List.mem_append_left _ (List.mem_toFinset.mp hw)))
  refine ⟨ha, ?_⟩
  rw [counterDecXor, wires_append, wires_append, counterFlip, notRegister_wires, ha]
  rw [Finset.union_eq_right.mpr hs, Finset.union_eq_left.mpr hs]

def AdderLayout.swapCounter (L : AdderLayout) : AdderLayout :=
  { L with bits := L.bits.map (fun b => { b with x := b.out, out := b.x }) }

theorem AdderLayout.swapCounter_fields (L : AdderLayout) :
    L.swapCounter.x = L.out ∧ L.swapCounter.out = L.x ∧ L.swapCounter.y = L.y ∧
    L.swapCounter.carry = L.carry ∧ L.swapCounter.cin = L.cin ∧ L.swapCounter.width = L.width := by
  simp [AdderLayout.swapCounter, AdderLayout.x, AdderLayout.y, AdderLayout.out,
    AdderLayout.carry, AdderLayout.width, List.map_map, Function.comp_def]

theorem AdderLayout.swapCounter_perm (L : AdderLayout) : L.swapCounter.wires.Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  rcases L with ⟨bs, cin⟩
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp [AdderLayout.swapCounter, AdderLayout.wires, addWires, List.count_cons] at ih ⊢
    omega

/-- 把受控增量后的值移入空计数寄存器，并以前向减法清空旧寄存器。 -/
def counterInc (L : AdderLayout) : Program := counterIncXor L ++ counterDecXor L.swapCounter

/-- 受控减量后同样清空旧计数寄存器，供下轮交换角色复用。 -/
def counterDec (L : AdderLayout) : Program := counterDecXor L ++ counterIncXor L.swapCounter

/-- 移动计数器仍只使用同一布局的线路。 -/
theorem counterMove_wires (L : AdderLayout) (hw : L.width=10) :
    wires (counterInc L)=L.wires.toFinset ∧ wires (counterDec L)=L.wires.toFinset := by
  have hc := counter_wires L hw
  have hs := counter_wires L.swapCounter ((AdderLayout.swapCounter_fields L).2.2.2.2.2.trans hw)
  have he : L.swapCounter.wires.toFinset=L.wires.toFinset := by
    ext w
    simpa only [List.mem_toFinset] using (AdderLayout.swapCounter_perm L).mem_iff
  simp only [counterInc,counterDec,wires_append,hc.1,hc.2,hs.1,hs.2,he,Finset.union_self,and_self]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MaskedAdder.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem AdderLayout.interface_perm (L : AdderLayout) :
    (((L.x ++ L.y) ++ L.out) ++ (L.cin::L.carry)).Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  rcases L with ⟨bs, cin⟩
  induction bs with
  | nil => simp [AdderLayout.x, AdderLayout.y, AdderLayout.out, AdderLayout.carry,
      AdderLayout.wires, addWires]
  | cons b bs ih =>
    simp [AdderLayout.x, AdderLayout.y, AdderLayout.out, AdderLayout.carry,
      AdderLayout.wires, addWires, List.count_cons] at ih ⊢
    omega

theorem AdderLayout.reg_subset (L : AdderLayout) :
    L.x ⊆ L.wires ∧ L.y ⊆ L.wires ∧ L.out ⊆ L.wires ∧ L.carry ⊆ L.wires := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro w hw <;> apply (L.interface_perm).mem_iff.mp <;> simp [hw]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Borrow.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 将 [i<k] XOR 到 target：装载阈值 i+1 并比较，清比较工作区后翻转结果。
不访问计数器另一银行 out。 -/
def counterActiveXor (L : AdderLayout) (target : Wire) (i : Nat) : Program :=
  compareLtConst none L.x L.y L.carry L.cin target (i+1) ++ [.X target]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BorrowFrame.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 实际支持集不含未访问的另一计数银行 out。 -/
theorem counterActiveXor_wires (L : AdderLayout) (target : Wire) (i : Nat) :
    wires (counterActiveXor L target i)=(target::L.cin::(L.x++L.y++L.carry)).toFinset := by
  have h := (compareLt_wires none L.x L.y L.carry L.cin target
    (by simp [AdderLayout.x,AdderLayout.y]) (by simp [AdderLayout.carry,AdderLayout.y])).2 (i+1)
  simp [counterActiveXor,wires_append,h,wires,Instr.wires,Finset.insert_comm]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BorrowedSkywalkCompactSupportLayout.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

namespace BorrowedSkywalkCompactSupport

end BorrowedSkywalkCompactSupport
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/LiteralSkywalkSeedLayout.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Bank-free seed allocation. Orientation is a boundary observation and
may coincide with Cin; distinctness applies only to physically touched roles. -/
structure LiteralSkywalkSeedLayout where
  a : List Wire
  b : List Wire
  carry : List Wire
  cin : Wire
  one : Wire
  orientation : Wire

namespace LiteralSkywalkSeedLayout

def usedWires (L : LiteralSkywalkSeedLayout) : List Wire :=
  L.one::L.cin::(L.a++L.b++L.carry)

structure Widths (L : LiteralSkywalkSeedLayout) (w : Nat) : Prop where
  a : L.a.length=w
  b : L.b.length=w
  carry : L.carry.length+1=w

structure Valid (L : LiteralSkywalkSeedLayout) : Prop where
  touched : L.usedWires.Nodup
  orientationAway : L.orientation∉L.a

theorem literalND (L : LiteralSkywalkSeedLayout) (hn : L.Valid) :
    (L.one::L.cin::(L.a++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn.touched q
  simp only [usedWires,List.count_cons,List.count_append] at h ⊢
  omega

theorem copyND (L : LiteralSkywalkSeedLayout) (hn : L.Valid) :
    (L.b++L.a).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn.touched q
  simp only [usedWires,List.count_cons,List.count_append] at h ⊢
  omega

theorem outsideA (L : LiteralSkywalkSeedLayout) (hn : L.Valid) (q : Wire)
    (hq : q∈[L.one,L.cin]++L.b++L.carry) : q∉L.a := by
  intro ha
  have h := List.nodup_iff_count.mp hn.touched q
  have hp := List.count_pos_iff.mpr hq
  have hd := List.count_pos_iff.mpr ha
  simp only [usedWires,List.count_cons,List.count_append,List.count_nil] at h hp
  omega

end LiteralSkywalkSeedLayout

structure LiteralSkywalkSeedValues (L : LiteralSkywalkSeedLayout) (A B : Nat)
    (s : BasisState) : Prop where
  a : regValue L.a s=A
  b : regValue L.b s=B
  carry : regValue L.carry s=0
  cin : s L.cin=false
  one : s L.one=false
  orientation : s L.orientation=false

def literalSkywalkSeed (L : LiteralSkywalkSeedLayout) (p : Nat) : Program :=
  copyRegister none L.b L.a++literalConstAdd L.a L.carry L.cin L.one p

/-- Forward literal subtraction and XOR cleanup use fresh measurement records. -/
def literalSkywalkUnseed (L : LiteralSkywalkSeedLayout) (p : Nat) : Program :=
  literalConstAdd L.a L.carry L.cin L.one (2^L.a.length-p)++copyRegister none L.b L.a

theorem literalSkywalkSeed_counts (L : LiteralSkywalkSeedLayout) (w p : Nat)
    (hw : L.Widths w) :
    toffoliCount (literalSkywalkSeed L p)=w-1 ∧
    measurementCount (literalSkywalkSeed L p)=w-1 ∧
    toffoliCount (literalSkywalkUnseed L p)=w-1 ∧
    measurementCount (literalSkywalkUnseed L p)=w-1 := by
  have c := copyRegister_counts none L.b L.a (hw.b.trans hw.a.symm)
  have a := literalConstAdd_counts L.a L.carry L.cin L.one p (hw.carry.trans hw.a.symm)
  have u := literalConstAdd_counts L.a L.carry L.cin L.one (2^L.a.length-p)
    (hw.carry.trans hw.a.symm)
  simp only [literalSkywalkSeed,literalSkywalkUnseed,toffoliCount_append,measurementCount_append]
  rw [c.1,c.2,a.1,a.2,u.1,u.2]
  simp [hw.a]

/-- Allocation support omits a materialized constant bank and counts Cin once. -/
theorem literalSkywalkSeed_support (L : LiteralSkywalkSeedLayout) (w p : Nat)
    (hw : L.Widths w) :
    wires (literalSkywalkSeed L p) ⊆ L.usedWires.toFinset ∧
    wires (literalSkywalkUnseed L p) ⊆ L.usedWires.toFinset := by
  have c := copyRegister_wires none L.b L.a (hw.b.trans hw.a.symm)
  have a := literalConstAdd_wires L.a L.carry L.cin L.one p
  have u := literalConstAdd_wires L.a L.carry L.cin L.one (2^L.a.length-p)
  have cs : wires (copyRegister none L.b L.a) ⊆ L.usedWires.toFinset := by
    intro q hq
    rw [c] at hq
    split_ifs at hq with he
    · simp at hq
    · simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
      simp only [LiteralSkywalkSeedLayout.usedWires,List.mem_toFinset,
        List.mem_cons,List.mem_append]
      tauto
  have lift : ∀k,wires (literalConstAdd L.a L.carry L.cin L.one k) ⊆ L.usedWires.toFinset := by
    intro k q hq
    have h := literalConstAdd_wires L.a L.carry L.cin L.one k hq
    simp only [LiteralSkywalkSeedLayout.usedWires,List.mem_toFinset,
      List.mem_cons,List.mem_append] at h ⊢
    tauto
  constructor <;> intro q hq
  · simp only [literalSkywalkSeed,wires_append,Finset.mem_union] at hq
    exact hq.elim (fun h => cs h) (fun h => (lift p) h)
  · simp only [literalSkywalkUnseed,wires_append,Finset.mem_union] at hq
    exact hq.elim (fun h => (lift _) h) (fun h => cs h)

theorem literalSkywalkSeed_frame (L : LiteralSkywalkSeedLayout) (w p : Nat)
    (hw : L.Widths w) (s : State) (m : List Bool) (q : Wire) (hq : q∉L.usedWires) :
    (run (literalSkywalkSeed L p) m s).basis q=s.basis q ∧
    (run (literalSkywalkUnseed L p) m s).basis q=s.basis q := by
  have hs := literalSkywalkSeed_support L w p hw
  constructor
  · exact run_preserves_outside _ m s q (fun h => hq (List.mem_toFinset.mp (hs.1 h)))
  · exact run_preserves_outside _ m s q (fun h => hq (List.mem_toFinset.mp (hs.2 h)))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/LiteralSkywalkSeedProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The copy restores every touched role outside its target word. -/
theorem literalSkywalkSeed_copy_stage (L : LiteralSkywalkSeedLayout) (hn : L.Valid)
    (hw : L.b.length=L.a.length) (A B : Nat) :
    Triple (LiteralSkywalkSeedValues L A B) (copyRegister none L.b L.a)
      (LiteralSkywalkSeedValues L (A ^^^ B) B) := by
  intro s m hin
  have h := copyRegister_correct none L.b L.a hw (L.copyND hn) (by simp) s m
  have keep (r : List Wire) (hr : r⊆[L.one,L.cin]++L.b++L.carry) :
      regValue r (run (copyRegister none L.b L.a) m s).basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact h.2.1 q (L.outsideA hn q (hr hq))
  refine ⟨h.1,?_,(keep _ (by intro q hq; simp [hq])).trans hin.b,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (h.2.1 _ (L.outsideA hn _ (by simp))).trans hin.cin,
    (h.2.1 _ (L.outsideA hn _ (by simp))).trans hin.one,
    (h.2.1 _ hn.orientationAway).trans hin.orientation⟩
  simpa only [hin.a,hin.b,copyValue] using h.2.2

/-- Exact forward literal arithmetic for every input word and record stream. -/
theorem literalSkywalkSeed_add_stage (L : LiteralSkywalkSeedLayout) (hn : L.Valid)
    (hc : L.carry.length+1=L.a.length) (A B k : Nat) :
    Triple (LiteralSkywalkSeedValues L A B) (literalConstAdd L.a L.carry L.cin L.one k)
      (LiteralSkywalkSeedValues L ((A+k)%2^L.a.length) B) := by
  intro s m hin
  have h := literalConstAdd_correct L.a L.carry L.cin L.one k (L.literalND hn) hc
    s m hin.one ((regValue_zero _ _).mp hin.carry)
  have keep (r : List Wire) (hr : r⊆[L.one,L.cin]++L.b++L.carry) :
      regValue r (run (literalConstAdd L.a L.carry L.cin L.one k) m s).basis=
        regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact h.2.1 q (L.outsideA hn q (hr hq))
  refine ⟨h.1,?_,(keep _ (by intro q hq; simp [hq])).trans hin.b,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (h.2.1 _ (L.outsideA hn _ (by simp))).trans hin.cin,
    (h.2.1 _ (L.outsideA hn _ (by simp))).trans hin.one,
    (h.2.1 _ hn.orientationAway).trans hin.orientation⟩
  simpa only [hin.a,hin.cin,Bool.toNat_false,Nat.add_zero] using h.2.2

theorem literalSkywalkSeed_small_bounds (w p x : Nat) (hw : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    p<2^w ∧ x<2^w ∧ p+x<2^(w-1) ∧ p+x<2^w := by
  have he : 2^(w-1)=2^(w-2)*2 := by
    rw [show w-1=(w-2)+1 by omega,pow_succ]
  have hm : 2^(w-1)≤2^w := Nat.pow_le_pow_right (by decide) (by omega)
  have hs : p+x<2^(w-1) := by rw [he]; omega
  exact ⟨by omega,by omega,hs,hs.trans_le hm⟩

/-- Positive exact seed, clean One/carry/Cin/orientation, unrestricted phase. -/
theorem literalSkywalkSeed_spec (L : LiteralSkywalkSeedLayout) (w p x : Nat)
    (hw : L.Widths w) (hn : L.Valid) (hw2 : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    Triple (LiteralSkywalkSeedValues L 0 x) (literalSkywalkSeed L p)
      (LiteralSkywalkSeedValues L (p+x) x) := by
  have hb := literalSkywalkSeed_small_bounds w p x hw2 hp hx
  have c := literalSkywalkSeed_copy_stage L hn (hw.b.trans hw.a.symm) 0 x
  simp only [Nat.zero_xor] at c
  have a := literalSkywalkSeed_add_stage L hn (hw.carry.trans hw.a.symm) x x p
  rw [hw.a,Nat.add_comm x p,Nat.mod_eq_of_lt hb.2.2.2] at a
  exact c.seq a

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/LiteralSkywalkSeedState.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The seed restores every site outside A, including all its touched scratch. -/
theorem literalSkywalkSeed_preserves_outsideA (L : LiteralSkywalkSeedLayout) (w p x : Nat)
    (hw : L.Widths w) (hn : L.Valid) (hw2 : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues L 0 x s.basis) (q : Wire) (hqa : q∉L.a) :
    (run (literalSkywalkSeed L p) m s).basis q=s.basis q := by
  obtain ⟨_,hout⟩ := literalSkywalkSeed_spec L w p x hw hn hw2 hp hx s m hin
  by_cases he : q=L.one
  · subst q
    exact hout.one.trans hin.one.symm
  by_cases he : q=L.cin
  · subst q
    exact hout.cin.trans hin.cin.symm
  by_cases hqb : q∈L.b
  · exact (regValue_eq_iff _ _ _).mp (hout.b.trans hin.b.symm) q hqb
  by_cases hqc : q∈L.carry
  · exact (regValue_eq_iff _ _ _).mp (hout.carry.trans hin.carry.symm) q hqc
  have hu : q∉L.usedWires := by
    simp only [LiteralSkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
    tauto
  exact (literalSkywalkSeed_frame L w p hw s m q hu).1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/LiteralSkywalkSeedPool.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Cin loans the initial orientation; One loans the first future history bit. -/
def literalSkywalkPoolSeed (w : Nat → Wire) : LiteralSkywalkSeedLayout :=
  { a:=wireBlock w 0 258,b:=wireBlock w 770 258,carry:=wireBlock w 1540 257,
    cin:=w 1797,one:=w 1028,orientation:=w 1797 }

private def poolSeedIds : List Nat :=
  [1028,1797]++List.range' 0 258++List.range' 770 258++List.range' 1540 257
private theorem poolSeedIdsND : poolSeedIds.Nodup := by
  have ab : (List.range' 0 258++List.range' 770 258).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_range'_1] at hj hk
    omega
  have abc : (List.range' 0 258++List.range' 770 258++List.range' 1540 257).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨ab,List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_append,List.mem_range'_1] at hj hk
    omega
  have all : (1028::1797::(List.range' 0 258++List.range' 770 258++
      List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_cons.mpr ⟨?_,abc⟩⟩
    · simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
    · simp only [List.mem_append,List.mem_range'_1]
      omega
  simpa only [poolSeedIds,List.cons_append,List.nil_append] using all
private theorem poolSeedIdsBound (j : Nat) (hj : j∈poolSeedIds) : j<1798 := by
  simp only [poolSeedIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj
  omega
private theorem poolSeedUsed (w : Nat → Wire) :
    (literalSkywalkPoolSeed w).usedWires=poolSeedIds.map w := by
  simp [literalSkywalkPoolSeed,LiteralSkywalkSeedLayout.usedWires,poolSeedIds,wireBlock]

theorem literalSkywalkPoolSeed_widths (w : Nat → Wire) :
    (literalSkywalkPoolSeed w).Widths 258 := by
  constructor <;> simp [literalSkywalkPoolSeed,wireBlock]

theorem literalSkywalkPoolSeed_valid (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) : (literalSkywalkPoolSeed w).Valid := by
  have mapped : (poolSeedIds.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkPool_index_inj w hn i j (poolSeedIdsBound i hi) (poolSeedIdsBound j hj) he
    · exact poolSeedIdsND
  have touched : (literalSkywalkPoolSeed w).usedWires.Nodup := by
    rw [poolSeedUsed]
    exact mapped
  refine ⟨touched,?_⟩
  have cinAway := (List.nodup_cons.mp (List.nodup_cons.mp touched).2).1
  intro hq
  apply cinAway
  change (literalSkywalkPoolSeed w).cin∈(literalSkywalkPoolSeed w).a at hq
  exact List.mem_append_left _ (List.mem_append_left _ hq)

theorem literalSkywalkPoolSeed_counts (w : Nat → Wire) (p : Nat) :
    toffoliCount (literalSkywalkSeed (literalSkywalkPoolSeed w) p)=257 ∧
    measurementCount (literalSkywalkSeed (literalSkywalkPoolSeed w) p)=257 ∧
    toffoliCount (literalSkywalkUnseed (literalSkywalkPoolSeed w) p)=257 ∧
    measurementCount (literalSkywalkUnseed (literalSkywalkPoolSeed w) p)=257 :=
  literalSkywalkSeed_counts _ 258 p (literalSkywalkPoolSeed_widths w)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/BorrowedSkywalkCompactSupportInteger.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
attribute [local irreducible] wireBlock literalSkywalkSeed literalSkywalkUnseed
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop

end ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
end

-- source: ECDSAAdd/Arithmetic/BorrowedSkywalkCompactSupportReplay.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
attribute [local irreducible] wireBlock copyRegister

end ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
end

-- source: ECDSAAdd/Arithmetic/BorrowedSkywalkCompactSupportUnary.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
open Secp256k1
attribute [local irreducible] wireBlock dblInPlace halfInPlace

end ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
end

-- source: ECDSAAdd/Arithmetic/InverseContract.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ZeroControl.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 每个被检测的输入位配一根可复用的零工作位。 -/
structure ZeroBit where
  input : Wire
  work : Wire

def ZeroBit.wires (b : ZeroBit) : List Wire := [b.input,b.work]

private def negAnd (c a t : Wire) : Program := [.X a, .CCX c a t, .X a]

private def negAndErase (c a t : Wire) : Program :=
  [.X a, .measureX t [] [.CZ c a], .X a]

/-- XOR 写入“控制为真且整段为零”；测量清理AND链并修正相位。 -/
def zeroControlled (c target : Wire) : List ZeroBit → Program
  | [] => [.CX c target]
  | b::bs => negAnd c b.input b.work ++ zeroControlled b.work target bs ++ negAndErase c b.input b.work

private theorem negAnd_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (s : State) (m : List Bool) :
    run (negAnd c a t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis a))⟩ := by
  simp only [negAnd, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=a
  · subst w; simp [writeBit, hca, hat]
  · by_cases ht : w=t
    · subst w; simp [writeBit, hca, Ne.symm hat]
    · simp [writeBit, hw, ht, hca]

private theorem negAndErase_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (hct : c≠t) (s : State) (m : List Bool)
    (hq : s.basis t = (s.basis c && !s.basis a)) :
    run (negAndErase c a t) m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [negAndErase, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, hca, hat, hat.symm, hct, hq]
  all_goals
    funext w
    by_cases hw : w=a
    · subst w; simp [hat]
    · simp [Function.update_apply, hw]

theorem zeroControlled_counts (c target : Wire) (bs : List ZeroBit) :
    toffoliCount (zeroControlled c target bs) = bs.length ∧
    measurementCount (zeroControlled c target bs) = bs.length := by
  induction bs generalizing c with
  | nil => simp [zeroControlled, toffoliCount, measurementCount]
  | cons b bs ih =>
    simp [zeroControlled, negAnd, negAndErase, toffoliCount_append, measurementCount_append,
      toffoliCount, measurementCount, ih]; omega

/-- 完整状态公式：只有目标翻转，包含所有借用工作位和控制位的恢复。 -/
theorem zeroControlled_correct (c target : Wire) (bs : List ZeroBit)
    (hnd : (c::target::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b∈bs, s.basis b.work=false) :
    run (zeroControlled c target bs) m s =
      ⟨s.phase, writeBit s.basis target
        (s.basis target ^^ (s.basis c && bs.all (fun b => !s.basis b.input)))⟩ := by
  induction bs generalizing c s m with
  | nil => simp [zeroControlled, run]
  | cons b bs ih =>
    have hnames : (c::target::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    have hca : c≠b.input := hni.1.2.1
    have hai : b.input≠b.work := hni.2.2.1.1
    have hta : target≠b.input := hni.2.1.1
    have htw : target≠b.work := hni.2.1.2.1
    have hcw : c≠b.work := hni.1.2.2.1
    have hchild : (b.work::target::bs.flatMap ZeroBit.wires).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨htw.symm,hni.2.2.2.1⟩,hni.2.1.2.2,hni.2.2.2.2⟩
    let q := s.basis c && !s.basis b.input
    let t : State := ⟨s.phase, writeBit s.basis b.work q⟩
    have hp : run (negAnd c b.input b.work) m s=t := by
      rw [negAnd_run c b.input b.work hca hai]
      simp [t, q, hz b (by simp), writeBit]
    have htail (d : ZeroBit) (hd : d∈bs) : d.work≠b.work ∧ d.input≠b.work := by
      have hh := hni.2.2.2.1
      constructor <;> intro he <;> apply hh <;>
        apply List.mem_flatMap.mpr <;> refine ⟨d,hd,?_⟩ <;> simp [ZeroBit.wires, he]
    have hz' : ∀ d∈bs, t.basis d.work=false := by
      intro d hd
      simpa [t, writeBit, (htail d hd).1] using hz d (by simp [hd])
    have hall : bs.all (fun d => !t.basis d.input) = bs.all (fun d => !s.basis d.input) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro h d hd <;> simpa [t, writeBit, (htail d hd).2] using h d hd
    change run (negAnd c b.input b.work ++ zeroControlled b.work target bs ++ negAndErase c b.input b.work) m s = _
    rw [run_append, run_take, run_append, run_take]
    simp only [measurementCount_append, (zeroControlled_counts b.work target bs).2,
      show measurementCount (negAnd c b.input b.work)=0 from rfl, Nat.zero_add, List.drop_zero]
    rw [hp, ih b.work hchild t m hz']
    rw [negAndErase_run c b.input b.work hca hai hcw _ _ (by
      simp [t, writeBit, htw.symm, hcw, hai, hni.1.1, hta.symm, q])]
    simp only [hall, t, List.all_cons]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases ht : w=target
    · subst w
      simp [writeBit, htw, q, Bool.and_assoc]
    · by_cases hw : w=b.work
      · subst w
        simp [writeBit, ht, hz b (by simp)]
      · simp [writeBit, ht, hw]

theorem zeroControlled_wires (c target : Wire) (bs : List ZeroBit) :
    wires (zeroControlled c target bs) = (c::target::bs.flatMap ZeroBit.wires).toFinset := by
  induction bs generalizing c with
  | nil => simp [zeroControlled, wires, Instr.wires]
  | cons b bs ih =>
    rw [zeroControlled, wires_append, wires_append, ih]
    ext w
    simp [negAnd, negAndErase, wires, Instr.wires, correctionWires, ZeroBit.wires, or_comm, or_left_comm]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RoundLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 四份 EEA 数据与一份共用算术/零检测工作区。 -/
inductive RoundField where
  | u | v | r | s | y | out | carry | zero
  deriving DecidableEq

structure RoundBit where
  u : Wire
  v : Wire
  r : Wire
  s : Wire
  y : Wire
  out : Wire
  carry : Wire
  zero : Wire

def RoundBit.get (b : RoundBit) : RoundField → Wire
  | .u => b.u | .v => b.v | .r => b.r | .s => b.s
  | .y => b.y | .out => b.out | .carry => b.carry | .zero => b.zero

def RoundBit.wires (b : RoundBit) : List Wire :=
  [b.u,b.v,b.r,b.s,b.y,b.out,b.carry,b.zero]

structure RoundDataLayout where
  bits : List RoundBit
  cin : Wire

namespace RoundDataLayout

def width (L : RoundDataLayout) : Nat := L.bits.length
def reg (L : RoundDataLayout) (f : RoundField) : List Wire := L.bits.map (fun b => b.get f)
def u (L : RoundDataLayout) : List Wire := L.reg .u
def v (L : RoundDataLayout) : List Wire := L.reg .v
def r (L : RoundDataLayout) : List Wire := L.reg .r
def s (L : RoundDataLayout) : List Wire := L.reg .s
def work (L : RoundDataLayout) : List Wire :=
  L.cin :: (L.reg .y ++ L.reg .out ++ L.reg .carry ++ L.reg .zero)
def wires (L : RoundDataLayout) : List Wire := L.cin :: L.bits.flatMap RoundBit.wires

def zeroBits (L : RoundDataLayout) (f : RoundField) : List ZeroBit :=
  L.bits.map (fun b => ⟨b.get f,b.zero⟩)

theorem reg_length (L : RoundDataLayout) (f : RoundField) : (L.reg f).length=L.width := by
  simp [reg, width]

end RoundDataLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RoundFrame.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 复用原地受控加减，y和低位进位链清零，out不再被触及。 -/
def inplaceArithmetic (L : RoundDataLayout) (f g : RoundField) (c : Wire) (negative : Bool) : Program :=
  if negative then
    measuredMaskedSubInPlace c (L.reg g) (L.reg .y) (L.reg f) ((L.reg .carry).take (L.width-1)) L.cin
  else
    measuredMaskedAddInPlace c (L.reg g) (L.reg .y) (L.reg f) ((L.reg .carry).take (L.width-1)) L.cin

namespace RoundFrame

end RoundFrame
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/KaliskiRound.lean
noncomputable section

namespace ECDSAAdd

/-- 完整两位记录：(是否交换 u/v 与 r/s，是否需要减法)。终止后取 00。 -/
def kaliskiCode (z : KState) : Bool × Bool :=
  if z.v = 0 then (false, false)
  else if z.u%2 = 0 then (false, false)
  else if z.v%2 = 0 then (true, false)
  else if z.v < z.u then (false, true)
  else (true, true)

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/RoundBody.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaliskiRound.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 单轮布局：数据、共享工作区、双银行计数器、两位记录与常数个控制工作位。 -/
structure KaliskiRoundLayout where
  low : List RoundBit
  high : RoundBit
  cin : Wire
  counterLow : List AddBit
  counterHigh : AddBit
  active : Wire
  compareCin : Wire
  done : Wire
  swap : Wire
  subtract : Wire
  oddWork : Wire
  bothWork : Wire

namespace KaliskiRoundLayout

def data (L : KaliskiRoundLayout) : RoundDataLayout := ⟨L.low++[L.high],L.cin⟩
def counter (L : KaliskiRoundLayout) : AdderLayout := ⟨L.counterLow++[L.counterHigh],L.active⟩

/-- 更新后的 k 在 counter.out；比较借用旧的空银行，cin 单独保持为零。 -/
def comparator (L : KaliskiRoundLayout) : AdderLayout :=
  { L.counter.swapCounter with cin:=L.compareCin }

def u (L : KaliskiRoundLayout) : List Wire := L.data.u
def v (L : KaliskiRoundLayout) : List Wire := L.data.v
def r (L : KaliskiRoundLayout) : List Wire := L.data.r
def s (L : KaliskiRoundLayout) : List Wire := L.data.s
def k (L : KaliskiRoundLayout) : List Wire := L.counter.x
def kNext (L : KaliskiRoundLayout) : List Wire := L.counter.out

def scratch (L : KaliskiRoundLayout) : List Wire :=
  L.data.work ++ L.counter.y ++ L.counter.carry ++ [L.active,L.compareCin,L.oddWork,L.bothWork]

/-- 下一轮仅交换计数器两份银行的角色；数据及算术工作区保持相同位置。 -/
def swapCounter (L : KaliskiRoundLayout) : KaliskiRoundLayout :=
  { L with
    counterLow := L.counterLow.map (fun b => {b with x:=b.out,out:=b.x})
    counterHigh := {L.counterHigh with x:=L.counterHigh.out,out:=L.counterHigh.x} }

theorem data_reg_length (L : KaliskiRoundLayout) (f : RoundField) :
    (L.data.reg f).length=L.low.length+1 := by
  simp [RoundDataLayout.reg,data]

end KaliskiRoundLayout

/-- 先保存奇偶条件，直接把受控比较 XOR 到记录位，再清条件；不生成差寄存器。 -/
def recordRound (L : KaliskiRoundLayout) : Program :=
  [.CCX L.active L.u.head! L.oddWork, .CCX L.oddWork L.v.head! L.bothWork,
   .CX L.bothWork L.subtract, .CX L.oddWork L.swap] ++
  compareLt (some L.bothWork) L.v L.u (L.data.reg .carry) L.cin L.swap ++
  [.CCX L.oddWork L.v.head! L.bothWork, .CCX L.active L.u.head! L.oddWork]

/-- 只翻转活动辅助位，既用于装入 !done，也用于恢复 done 后的清理。 -/
def loadActive (L : KaliskiRoundLayout) : Program := [.X L.active,.CX L.done L.active]

def roundActiveXor (L : KaliskiRoundLayout) (i : Nat) : Program :=
  counterActiveXor L.comparator L.active i

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/HalveInPlace.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 求逆第二阶段的原地减半/加倍布局：data 上原地操作；常数字、进位链（chain 给加法器，
chain ++ [top] 给比较器）、cin 与标志借自模算术工作区；active 与计数银行沿用第一阶段。 -/
structure HalvingLayout where
  data : List Wire
  constant : List Wire
  chain : List Wire
  top : Wire
  cin : Wire
  flag : Wire
  active : Wire
  counterLow : List AddBit
  counterHigh : AddBit
  compareCin : Wire

namespace HalvingLayout

end HalvingLayout

namespace HalvingLayout

end HalvingLayout


namespace HalvingLayout

end HalvingLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ExternalMod.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.ExternalMod

end ECDSAAdd.Arithmetic.ExternalMod
end

-- source: ECDSAAdd/Arithmetic/ModularXorSteps.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.ExternalMod

end ECDSAAdd.Arithmetic.ExternalMod
end

-- source: ECDSAAdd/Arithmetic/UnaryMod.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ExternalMod

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/UnaryModResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ExternalMod

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NegativeInit.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NegativeInitResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RecordRound.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace KaliskiRoundLayout

theorem head_mem (L : KaliskiRoundLayout) (f : RoundField) :
    (L.data.reg f).head!∈L.data.reg f := by
  have hn : L.data.reg f≠[] := by
    intro he
    have h := L.data_reg_length f
    rw [he] at h
    simp at h
  cases hr : L.data.reg f with
  | nil => exact False.elim (hn hr)
  | cons a r => simp

end KaliskiRoundLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RoundState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace KaliskiRoundLayout

end KaliskiRoundLayout

namespace RoundAuxValues

end RoundAuxValues

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RoundControls.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaliskiRoundProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RoundResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RoundWires.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 记录段只接触两份输入、进位链及六个控制/记录位。 -/
theorem recordRound_wires (L : KaliskiRoundLayout) :
    wires (recordRound L)=([L.active,L.swap,L.subtract,L.oddWork,L.bothWork,L.data.cin]++
      L.u++L.v++L.data.reg .carry).toFinset := by
  have hc := (compareLt_wires (some L.bothWork) L.v L.u (L.data.reg .carry) L.cin L.swap
    (by simp [KaliskiRoundLayout.v,KaliskiRoundLayout.u,RoundDataLayout.v,RoundDataLayout.u,L.data.reg_length])
    (by simp [KaliskiRoundLayout.u,RoundDataLayout.u,L.data.reg_length])).1
  rw [recordRound,wires_append,wires_append,hc]
  ext w
  have hu : w=L.u.head! → w∈L.u := fun he => he ▸ L.head_mem .u
  have hv : w=L.v.head! → w∈L.v := fun he => he ▸ L.head_mem .v
  simp only [wires,Instr.wires,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
    List.mem_nil_iff,Finset.mem_insert,Finset.notMem_empty,
    Option.toList_some,Finset.mem_singleton]
  simp only [KaliskiRoundLayout.data] at *
  tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/RoundSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaliskiLoop.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 每轮独占两根历史线路；数据与计数工作区逐轮复用。 -/
structure RoundRecord where
  swap : Wire
  subtract : Wire

def RoundRecord.wires (r : RoundRecord) : List Wire := [r.swap,r.subtract]

namespace KaliskiRoundLayout

def withRecord (L : KaliskiRoundLayout) (r : RoundRecord) : KaliskiRoundLayout :=
  {L with swap:=r.swap,subtract:=r.subtract}

def sharedWires (L : KaliskiRoundLayout) : List Wire :=
  [L.done,L.oddWork,L.bothWork,L.compareCin]++L.data.wires++L.counter.wires

def tapeWires (L : KaliskiRoundLayout) (rs : List RoundRecord) : List Wire :=
  rs.flatMap RoundRecord.wires++L.sharedWires

theorem swapCounter_data (L : KaliskiRoundLayout) : L.swapCounter.data=L.data := rfl

theorem swapCounter_counter (L : KaliskiRoundLayout) : L.swapCounter.counter=L.counter.swapCounter := by
  simp [swapCounter,counter,AdderLayout.swapCounter]

end KaliskiRoundLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaliskiLoopResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaliskiLoopState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace LoopState

end LoopState

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/EraseSwap.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/KaliskiOneBit.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/OneBitRound.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OneBitRoundProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OneBitRoundSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OneBitRoundResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OneBitLoop.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace KaliskiRoundLayout

end KaliskiRoundLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OneBitLoopResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OneBitRecords.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseLoopLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- I4 使用已初始化的第一阶段寄存器；第二阶段复用其计数比较线路。 -/
structure InverseLoopLayout where
  first : KaliskiRoundLayout
  records : List RoundRecord
  arithmetic : ModLayout
  a : List Wire
  temp : List Wire
  out : List Wire

namespace InverseLoopLayout

def extra (L : InverseLoopLayout) : List Wire := L.a++L.temp++L.arithmetic.wires

def wires (L : InverseLoopLayout) : List Wire := L.first.tapeWires L.records++L.extra++L.out

end InverseLoopLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseLoopState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseMiddle.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace InverseLoopLayout

end InverseLoopLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Lookup.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Instr Correction

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/Montgomery.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/MontPrepare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 一个 Montgomery 段；另一段复用 table/mask/carry/pad/scratch，保留各自 acc/history/flag。 -/
structure MontStageLayout where
  acc : List Wire
  history : List Wire
  flag : Wire
  table : List Wire
  mask : List Wire
  carry : List Wire
  cin : Wire
  pad : List Wire
  scratch : List Wire

namespace MontStageLayout

end MontStageLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontLookup.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 减法也逐线保持目标以外所有位；清零进位仍由同一前向门列证明。 -/
theorem subInPlace_frame (x y carry : List Wire) (cin : Wire)
    (hnd : (cin::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (s : State) (m : List Bool)
    (hcin : s.basis cin=false) (hcarry : regValue carry s.basis=0)
    (w : Wire) (hw : w∉y) : (run (subInPlace x y carry cin) m s).basis w=s.basis w := by
  have h := (subInPlace_spec x y carry cin hnd hx hc
    (regValue x s.basis) (regValue y s.basis) s m ⟨⟨⟨rfl,rfl⟩,hcin⟩,hcarry⟩).2
  by_cases hxw : w∈x
  · exact (regValue_eq_iff x _ _).mp h.1.1.1 w hxw
  by_cases hcw : w∈carry
  · exact (regValue_eq_iff carry _ _).mp (h.2.trans hcarry.symm) w hcw
  by_cases he : w=cin
  · subst w; exact h.1.2.trans hcin.symm
  apply run_preserves_outside
  rw [subInPlace_wires x y carry cin hx hc]
  simpa using (show w∉cin::(x++y++carry) by simp [he,hxw,hw,hcw])

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontConstant.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontNormalize.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontReduce.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontDigit.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontHistory.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontStagePorts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.MontStageLayout

end ECDSAAdd.Arithmetic.MontStageLayout
end

-- source: ECDSAAdd/Arithmetic/MontWindow.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontRounds.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ConstDigit.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ConstWindow.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ConstRounds.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontStageSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ConstStageSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/MontgomeryConversion.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/MontLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 两段只分配一份临时工作区，各自保存累加器、记录带和借位。 -/
structure MontLayout where
  x : List Wire
  y : List Wire
  out : List Wire
  first : MontStageLayout
  z : List Wire
  hZ : List Wire
  fZ : Wire

namespace MontLayout

end MontLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontPQ.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontCounts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontWires.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/KaliskiInverse.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Math/InverseScaleFactor.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/InverseScale.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 一次计数缩放的实际寄存器视图；不拥有额外分配。 -/
structure InverseScaleLayout where
  a : List Wire
  k : List Wire
  factor : List Wire
  stage : MontStageLayout
  extraScratch : List Wire

namespace InverseScaleLayout

end InverseScaleLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseScaleBorrow.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.InverseLoopLayout

end ECDSAAdd.Arithmetic.InverseLoopLayout
end

-- source: ECDSAAdd/Math/KaliskiTerminal.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/NegativeEven.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace ModInPlaceLayout

end ModInPlaceLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseCompactLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace InverseLoopLayout

end InverseLoopLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseCompactViews.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.InverseLoopLayout

end ECDSAAdd.Arithmetic.InverseLoopLayout
end

-- source: ECDSAAdd/Arithmetic/InverseTerminalConstants.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseCompactState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace InverseLoopLayout

end InverseLoopLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseCompactStages.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseScaleState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseCompute.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseCompactSupport.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace InverseScaleLayout

end InverseScaleLayout
namespace InverseLoopLayout

end InverseLoopLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseLoopSupport.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace InverseLoopLayout

end InverseLoopLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseLoopProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseLoopSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

def InverseLoopLayout.work (L : InverseLoopLayout) : List Wire :=
  L.first.kNext++L.first.scratch++L.records.flatMap RoundRecord.wires++L.extra

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseLoopResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 外部输入另占 256 位；内核输出的末位作为工作位，公开输出取其低 256 位。 -/
structure InverseLayout where
  inner : InverseLoopLayout
  x : List Wire

namespace InverseLayout

def out (L : InverseLayout) : List Wire := L.inner.out.take 256
def vLow (L : InverseLayout) : List Wire := L.inner.first.low.map RoundBit.v
def rest (L : InverseLayout) : List Wire :=
  L.inner.first.r ++ L.inner.first.k ++ [L.inner.first.done] ++ L.inner.work ++
    [L.inner.first.high.v] ++ L.inner.out.drop 256
def work (L : InverseLayout) : List Wire :=
  L.inner.first.u ++ L.vLow ++ L.inner.first.s ++ L.rest
def wires (L : InverseLayout) : List Wire := L.x ++ L.out ++ L.work

private theorem data_count (bs : List RoundBit) (w : Wire) :
    (bs.flatMap RoundBit.wires).count w =
    (bs.map RoundBit.u).count w + (bs.map RoundBit.v).count w +
    (bs.map RoundBit.r).count w + (bs.map RoundBit.s).count w +
    (bs.map RoundBit.y).count w + (bs.map RoundBit.out).count w +
    (bs.map RoundBit.carry).count w + (bs.map RoundBit.zero).count w := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons,RoundBit.wires,List.map_cons,List.count_append,
      List.count_cons,List.count_nil,ih]
    omega

private theorem counter_count (bs : List AddBit) (w : Wire) :
    (addWires bs).count w =
    (bs.map AddBit.x).count w + (bs.map AddBit.y).count w +
    (bs.map AddBit.out).count w + (bs.map AddBit.carry).count w := by
  induction bs with
  | nil => simp [addWires]
  | cons b bs ih => simp only [addWires,List.map_cons,List.count_cons,ih]; omega

theorem wires_perm (L : InverseLayout) : L.wires.Perm (L.x++L.inner.wires) := by
  apply List.perm_iff_count.mpr
  intro w
  have ho := congrArg (List.count w) (List.take_append_drop 256 L.inner.out)
  simp only [List.count_append] at ho
  simp only [wires,out,work,rest,vLow,InverseLoopLayout.wires,InverseLoopLayout.work,
    KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,KaliskiRoundLayout.scratch,
    KaliskiRoundLayout.u,KaliskiRoundLayout.r,KaliskiRoundLayout.s,
    KaliskiRoundLayout.k,KaliskiRoundLayout.kNext,KaliskiRoundLayout.data,KaliskiRoundLayout.counter,
    RoundDataLayout.u,RoundDataLayout.r,RoundDataLayout.s,RoundDataLayout.work,
    RoundDataLayout.reg,RoundDataLayout.wires,AdderLayout.wires,AdderLayout.x,AdderLayout.y,
    AdderLayout.out,AdderLayout.carry,List.count_append,List.count_cons,List.count_nil,
    data_count,counter_count,List.map_append,List.map_cons,List.map_nil,RoundBit.get]
  simp only [(show (fun b : RoundBit => b.u) = RoundBit.u from rfl),
    (show (fun b : RoundBit => b.r) = RoundBit.r from rfl),
    (show (fun b : RoundBit => b.s) = RoundBit.s from rfl),
    (show (fun b : RoundBit => b.y) = RoundBit.y from rfl),
    (show (fun b : RoundBit => b.out) = RoundBit.out from rfl),
    (show (fun b : RoundBit => b.carry) = RoundBit.carry from rfl),
    (show (fun b : RoundBit => b.zero) = RoundBit.zero from rfl)]
  omega

end InverseLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseLoad.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 装载证明使用的六个不交寄存器；rest 包括输入与输出的内部高位。 -/
inductive InverseField where
  | x | u | v | s | out | rest
  deriving DecidableEq

namespace InverseLayout

end InverseLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InverseResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/InversePorts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

private def poolRoundBit (w : Nat → Wire) (start : Nat) : RoundBit :=
  ⟨w start,w (start+1),w (start+2),w (start+3),w (start+4),
    w (start+5),w (start+6),w (start+7)⟩

private def poolAddBit (w : Nat → Wire) (start : Nat) : AddBit :=
  ⟨w start,w (start+1),w (start+2),w (start+3)⟩

/-- 基础轮的两根记录占位字段不会执行；每轮由 records 中的独立线路替换。 -/
private def poolFirstRound (w : Nat → Wire) : KaliskiRoundLayout :=
  ⟨(List.range 256).map (fun i => poolRoundBit w (5+8*i)),poolRoundBit w (5+8*256),w 4,
    (List.range 9).map (fun i => poolAddBit w (2062+4*i)),poolAddBit w (2062+4*9),
    w 2061,w 3,w 0,w 2102,w 2103,w 1,w 2⟩

/-- 现有求逆模块的 5699 根工作线映射到同一个模乘工作池的前缀。 -/
def poolInverse (w : Nat → Wire) (x out : List Wire) : InverseLayout :=
  ⟨⟨poolFirstRound w,
     (List.range 512).map (fun i => ⟨w (2102+2*i),w (2102+2*i+1)⟩),
     poolMod w 3126 256,wireBlock w 5184 257,
     wireBlock w 5441 257,out++[w 5698]⟩,x⟩

theorem poolInverse_inputs (w : Nat → Wire) (x out : List Wire) (ho : out.length=256) :
    (poolInverse w x out).x=x ∧ (poolInverse w x out).out=out := by
  refine ⟨rfl,?_⟩
  change (out++[w 5698]).take 256=out
  rw [← ho,List.take_left]

private theorem poolRoundBit_wires (w : Nat → Wire) (start : Nat) :
    (poolRoundBit w start).wires=wireBlock w start 8 := by
  simp [poolRoundBit,RoundBit.wires,wireBlock,List.range',Nat.add_assoc]

private theorem poolAddBit_wires (w : Nat → Wire) (start : Nat) :
    addWires [poolAddBit w start]=wireBlock w start 4 := by
  simp [poolAddBit,addWires,wireBlock,List.range',Nat.add_assoc]

private theorem addWires_flatMap (bs : List AddBit) :
    addWires bs=bs.flatMap (fun b => addWires [b]) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [addWires] using ih

private theorem poolFirstRound_shared (w : Nat → Wire) :
    (poolFirstRound w).sharedWires=wireBlock w 0 2102 := by
  have hd : (poolFirstRound w).data.wires=wireBlock w 4 2057 := by
    have hb : (poolFirstRound w).data.bits=
        (List.range 257).map (fun i => poolRoundBit w (5+8*i)) := by
      rw [show (257:Nat)=256+1 from rfl,List.range_succ]
      simp [poolFirstRound,KaliskiRoundLayout.data]
    rw [RoundDataLayout.wires,hb,List.flatMap_map]
    simp only [poolRoundBit_wires]
    rw [wireBlock_flatMap]
    change w 4::wireBlock w (4+1) 2056=_
    rw [← wireBlock_append w 4 1 2056]
    rfl
  have hc : (poolFirstRound w).counter.wires=wireBlock w 2061 41 := by
    have hb : (poolFirstRound w).counter.bits=
        (List.range 10).map (fun i => poolAddBit w (2062+4*i)) := by
      rw [show (10:Nat)=9+1 from rfl,List.range_succ]
      simp [poolFirstRound,KaliskiRoundLayout.counter]
    rw [AdderLayout.wires,hb,addWires_flatMap,List.flatMap_map]
    simp only [poolAddBit_wires]
    rw [wireBlock_flatMap]
    change w 2061::wireBlock w (2061+1) 40=_
    rw [← wireBlock_append w 2061 1 40]
    rfl
  rw [KaliskiRoundLayout.sharedWires,hd,hc]
  change wireBlock w 0 4++wireBlock w 4 2057++wireBlock w 2061 41=_
  rw [show (4:Nat)=0+4 from rfl,wireBlock_append]
  rw [show (2061:Nat)=0+(4+2057) from rfl,wireBlock_append]

private theorem poolInverse_inner_perm (w : Nat → Wire) (x out : List Wire) :
    (poolInverse w x out).inner.wires.Perm (out++wireBlock w 0 5699) := by
  have hr : ((poolInverse w x out).inner.records.flatMap RoundRecord.wires)=
      wireBlock w 2102 1024 := by
    simp only [poolInverse,List.flatMap_map,RoundRecord.wires]
    change ((List.range 512).flatMap (fun i => wireBlock w (2102+2*i) 2))=_
    exact wireBlock_flatMap _ _ _ _
  have hj : wireBlock w 0 2102++wireBlock w 2102 1024++wireBlock w 3126 2058++
      wireBlock w 5184 257++wireBlock w 5441 257++wireBlock w 5698 1=
        wireBlock w 0 5699 := by
    rw [wireBlock_append w 0 2102 1024,wireBlock_append w 0 3126 2058,
      wireBlock_append w 0 5184 257,wireBlock_append w 0 5441 257,
      wireBlock_append w 0 5698 1]
  rw [InverseLoopLayout.wires,KaliskiRoundLayout.tapeWires,hr]
  change (wireBlock w 2102 1024++(poolFirstRound w).sharedWires++
    (wireBlock w 5184 257++wireBlock w 5441 257++
      (poolMod w 3126 256).wires)++(out++[w 5698])).Perm _
  rw [poolFirstRound_shared,poolMod_wires,← hj]
  change (wireBlock w 2102 1024++wireBlock w 0 2102++
    (wireBlock w 5184 257++wireBlock w 5441 257++wireBlock w 3126 2058)++
    (out++wireBlock w 5698 1)).Perm _
  apply List.perm_iff_count.mpr
  intro v
  simp only [List.count_append]
  ac_rfl

theorem poolInverse_work_perm (w : Nat → Wire) (x out : List Wire) (ho : out.length=256) :
    (poolInverse w x out).work.Perm (wireBlock w 0 5699) := by
  have hh := (poolInverse w x out).wires_perm
  unfold InverseLayout.wires at hh
  rw [(poolInverse_inputs w x out ho).1,(poolInverse_inputs w x out ho).2] at hh
  have ht := hh.trans (List.Perm.append_left x (poolInverse_inner_perm w x out))
  apply List.perm_iff_count.mpr
  intro v
  have hc := ht.count_eq v
  simp only [List.count_append] at hc
  omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CandidatePool.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkSignReleaseProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The retained sign belongs to the physical prefix. Released high sites
are distinct from every retained site and may subsequently be loaned. -/
structure CompactSkywalkSignReleaseLayout where
  low : List Wire
  sign : Wire
  released : List Wire

namespace CompactSkywalkSignReleaseLayout

def retained (L : CompactSkywalkSignReleaseLayout) : List Wire := L.low++[L.sign]
def expanded (L : CompactSkywalkSignReleaseLayout) : List Wire := L.retained++L.released
def Valid (L : CompactSkywalkSignReleaseLayout) : Prop := L.expanded.Nodup
def Copies (L : CompactSkywalkSignReleaseLayout) (s : BasisState) : Prop :=
  ∀q ∈ L.released,s q = s L.sign
def Clean (L : CompactSkywalkSignReleaseLayout) (s : BasisState) : Prop :=
  ∀q ∈ L.released,s q = false

def cleared (L : CompactSkywalkSignReleaseLayout) (s : BasisState) : BasisState :=
  fun q => if q ∈ L.released then false else s q
/-- Virtual sign-extension interface while high sites are physically clean. -/
def reconstructed (L : CompactSkywalkSignReleaseLayout) (s : BasisState) : BasisState :=
  fun q => if q ∈ L.released then s L.sign else s q

theorem releasedND (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid) : L.released.Nodup :=
  (List.nodup_append'.mp hv).2.1

theorem signAway (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid) : L.sign ∉ L.released := by
  have h := (List.nodup_append'.mp hv).2.2
  exact List.disjoint_left.mp h (by simp [retained])

theorem retainedAway (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (q : Wire) (hq : q ∈ L.retained) : q ∉ L.released :=
  List.disjoint_left.mp (List.nodup_append'.mp hv).2.2 hq

end CompactSkywalkSignReleaseLayout

/-- One emitted CX per redundant sign copy; there are no carry instructions. -/
def compactSkywalkSignRelease (L : CompactSkywalkSignReleaseLayout) : Program :=
  signComplement L.sign L.released
/-- The same independently emitted Clifford fanout reconstructs clean high sites. -/
def compactSkywalkSignExpand (L : CompactSkywalkSignReleaseLayout) : Program :=
  signComplement L.sign L.released

theorem compactSkywalkSignRelease_run (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) :
    run (compactSkywalkSignRelease L) m s = 
      ⟨s.phase,fun q => if q ∈ L.released then s.basis q ^^ s.basis L.sign else s.basis q⟩ :=
  narrow_fanout_correct L.sign L.released (L.releasedND hv) (L.signAway hv) s m

theorem compactSkywalkSignRelease_correct (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Copies s.basis) :
    run (compactSkywalkSignRelease L) m s = ⟨s.phase,L.cleared s.basis⟩ := by
  rw [compactSkywalkSignRelease_run L hv s m]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q ∈ L.released
  · simp only [CompactSkywalkSignReleaseLayout.cleared,if_pos hq,hc q hq]
    cases s.basis L.sign <;> rfl
  · simp [CompactSkywalkSignReleaseLayout.cleared,hq]

/-- Arbitrary incoming phase and arbitrary record lists are preserved. -/
theorem compactSkywalkSignRelease_phase_frame (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) :
    (run (compactSkywalkSignRelease L) m s).phase = s.phase ∧
    (∀q,q ∉ L.released → (run (compactSkywalkSignRelease L) m s).basis q = s.basis q) ∧
    (run (compactSkywalkSignExpand L) m s).phase = s.phase ∧
    (∀q,q ∉ L.released → (run (compactSkywalkSignExpand L) m s).basis q = s.basis q) := by
  have h := signComplement_correct L.sign L.released (L.releasedND hv) (L.signAway hv) s m
  exact ⟨h.1,h.2.1,h.1,h.2.1⟩

theorem compactSkywalkSignRelease_clean (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Copies s.basis) :
    L.Clean (run (compactSkywalkSignRelease L) m s).basis := by
  rw [compactSkywalkSignRelease_correct L hv s m hc]
  intro q hq
  simp [CompactSkywalkSignReleaseLayout.cleared,hq]

/-- Both physical direction orders are exact State inverses, even before
restricting to the sign-copy/clean-bank boundary predicates. -/
theorem compactSkywalkSignRelease_roundtrip (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m1 m2 : List Bool) :
    run (compactSkywalkSignExpand L) m2 (run (compactSkywalkSignRelease L) m1 s) = s ∧
    run (compactSkywalkSignRelease L) m2 (run (compactSkywalkSignExpand L) m1 s) = s := by
  have h := narrow_fanout_twice L.sign L.released (L.releasedND hv) (L.signAway hv) s m1 m2
  exact ⟨h,h⟩

theorem compactSkywalkSignRelease_counts (L : CompactSkywalkSignReleaseLayout) :
    toffoliCount (compactSkywalkSignRelease L) = 0 ∧ measurementCount (compactSkywalkSignRelease L) = 0 ∧
    toffoliCount (compactSkywalkSignExpand L) = 0 ∧ measurementCount (compactSkywalkSignExpand L) = 0 := by
  have h := signComplement_counts L.sign L.released
  exact ⟨h.1,h.2,h.1,h.2⟩

theorem compactSkywalkSignRelease_support (L : CompactSkywalkSignReleaseLayout) :
    wires (compactSkywalkSignRelease L) ⊆ (L.sign::L.released).toFinset ∧
    wires (compactSkywalkSignExpand L) ⊆ (L.sign::L.released).toFinset := by
  have h := signComplement_wires_subset L.sign L.released
  exact ⟨h,h⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkSignReleaseMath.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Exact signed padding identity, including the negative endpoint. -/
theorem compactSkywalkSignRelease_expanded_value (L : CompactSkywalkSignReleaseLayout)
    (s : BasisState) (hc : L.Copies s) :
    signedRegValue L.expanded s = signedRegValue L.retained s := by
  apply narrow_signed_extend L.retained L.released s (signedRegValue L.retained s)
    (by simp [CompactSkywalkSignReleaseLayout.retained]) rfl
  intro q hq
  exact (hc q hq).trans (signedRegValue_sign L.low L.sign s)

/-- A proved strict signed fit supplies every physical high sign copy. -/
theorem compactSkywalkSignRelease_copies_of_fit (L : CompactSkywalkSignReleaseLayout)
    (s : BasisState) (A : Int) (ha : signedRegValue L.expanded s = A)
    (ha0 : -((2^(L.retained.length-1):Nat):Int) ≤ A)
    (ha1 : A < ((2^(L.retained.length-1):Nat):Int)) : L.Copies s := by
  have hp := narrow_signed_prefix L.retained L.released s A
    (by simp [CompactSkywalkSignReleaseLayout.retained]) ha ha0 ha1
  have hs := signedRegValue_sign L.low L.sign s
  change s L.sign = SkywalkRails.neg (signedRegValue L.retained s) at hs
  rw [hp.1] at hs
  intro q hq
  exact (hp.2 q hq).trans hs.symm

private theorem retained_congr (L : CompactSkywalkSignReleaseLayout) (s t : BasisState)
    (he : ∀q ∈ L.retained,t q = s q) : signedRegValue L.retained t = signedRegValue L.retained s := by
  unfold signedRegValue
  rw [regValue_congr L.retained t s he]

/-- Clearing the physical tail preserves the retained signed value. The old
expanded word must subsequently be interpreted through reconstruction. -/
theorem compactSkywalkSignRelease_signed (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Copies s.basis) :
    signedRegValue L.retained (run (compactSkywalkSignRelease L) m s).basis = 
      signedRegValue L.expanded s.basis := by
  have h := (compactSkywalkSignRelease_phase_frame L hv s m).2.1
  have hp := retained_congr L s.basis (run (compactSkywalkSignRelease L) m s).basis
    (fun q hq => h q (L.retainedAway hv q hq))
  exact hp.trans (compactSkywalkSignRelease_expanded_value L s.basis hc).symm

/-- Virtual high sign extension depends only on the current retained word,
so released sites may carry other data between certified clean boundaries. -/
theorem compactSkywalkSignRelease_virtual_signed (L : CompactSkywalkSignReleaseLayout)
    (hv : L.Valid) (s : BasisState) :
    signedRegValue L.expanded (L.reconstructed s) = signedRegValue L.retained s := by
  have hc : L.Copies (L.reconstructed s) := by
    intro q hq
    simp [CompactSkywalkSignReleaseLayout.reconstructed,hq,L.signAway hv]
  have hp := retained_congr L s (L.reconstructed s) (by
    intro q hq
    simp [CompactSkywalkSignReleaseLayout.reconstructed,L.retainedAway hv q hq])
  exact (compactSkywalkSignRelease_expanded_value L (L.reconstructed s) hc).trans hp

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkSignReleaseViews.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Physical take/drop allocation: the omitted tail is really cleared by CX. -/
def compactSkywalkSignWord (r : List Wire) (n : Nat) : CompactSkywalkSignReleaseLayout :=
  {low:=r.take (n-1),sign:=r.getD (n-1) 0,released:=r.drop n}

theorem compactSkywalkSignWord_retained (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) : (compactSkywalkSignWord r n).retained = r.take n := by
  have hidx : n-1 < r.length := by omega
  have he : n = (n-1)+1 := by omega
  change r.take (n-1)++[r.getD (n-1) 0] = r.take n
  conv_rhs => rw [he]
  rw [List.getD_eq_getElem _ _ hidx,List.take_add_one,List.getElem?_eq_getElem hidx]
  rfl

theorem compactSkywalkSignWord_expanded (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) : (compactSkywalkSignWord r n).expanded = r := by
  rw [CompactSkywalkSignReleaseLayout.expanded,compactSkywalkSignWord_retained r n hn hle]
  exact List.take_append_drop n r

theorem compactSkywalkSignWord_valid (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) (hr : r.Nodup) : (compactSkywalkSignWord r n).Valid := by
  change (compactSkywalkSignWord r n).expanded.Nodup
  rw [compactSkywalkSignWord_expanded r n hn hle]
  exact hr

theorem compactSkywalkSignWord_lengths (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) :
    (compactSkywalkSignWord r n).retained.length = n ∧
    (compactSkywalkSignWord r n).released.length = r.length-n := by
  rw [compactSkywalkSignWord_retained r n hn hle]
  simp [compactSkywalkSignWord,Nat.min_eq_left hle]

/-- A strict signed fit proves the required redundant copies, without sampling. -/
theorem compactSkywalkSignWord_copies (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) (s : BasisState) (A : Int)
    (ha : signedRegValue r s = A)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int)) :
    (compactSkywalkSignWord r n).Copies s := by
  apply compactSkywalkSignRelease_copies_of_fit (compactSkywalkSignWord r n) s A
  · simpa only [compactSkywalkSignWord_expanded r n hn hle] using ha
  · simpa only [(compactSkywalkSignWord_lengths r n hn hle).1] using ha0
  · simpa only [(compactSkywalkSignWord_lengths r n hn hle).1] using ha1

/-- No carry or any other external allocation occurs in either actual program. -/
theorem compactSkywalkSignWord_support (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) :
    wires (compactSkywalkSignRelease (compactSkywalkSignWord r n)) ⊆ r.toFinset ∧
    wires (compactSkywalkSignExpand (compactSkywalkSignWord r n)) ⊆ r.toFinset := by
  have hs := compactSkywalkSignRelease_support (compactSkywalkSignWord r n)
  have sub : ((compactSkywalkSignWord r n).sign::(compactSkywalkSignWord r n).released).toFinset⊆r.toFinset := by
    intro q hq
    apply List.mem_toFinset.mpr
    rw [←compactSkywalkSignWord_expanded r n hn hle]
    simp only [CompactSkywalkSignReleaseLayout.expanded]
    rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with he|he
    · exact List.mem_append_left _ (by simp [CompactSkywalkSignReleaseLayout.retained,he])
    · exact List.mem_append_right _ he
  exact ⟨hs.1.trans sub,hs.2.trans sub⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkSignReleasePool.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

def compactSkywalkSignPoolA (w : Nat → Wire) (i : Nat) : CompactSkywalkSignReleaseLayout :=
  compactSkywalkSignWord (skywalkPoolA w i) (narrowSkywalkRouteWidth i)
def compactSkywalkSignPoolB (w : Nat → Wire) (i : Nat) : CompactSkywalkSignReleaseLayout :=
  compactSkywalkSignWord (skywalkPoolB w) (narrowSkywalkRouteWidth i)

def compactSkywalkSignPoolRelease (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkSignRelease (compactSkywalkSignPoolA w i)++
    compactSkywalkSignRelease (compactSkywalkSignPoolB w i)

private theorem blockND (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start count : Nat) (hb : start+count ≤ 1798) : (wireBlock w start count).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj he
    simp only [List.mem_range'_1] at hi hj
    exact skywalkPool_index_inj w hn i j (by omega) (by omega) he
  · exact List.nodup_range'

theorem compactSkywalkSignPool_wordsND (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (skywalkPoolA w i).Nodup ∧ (skywalkPoolB w).Nodup :=
  ⟨blockND w hn i 258 (by omega),blockND w hn 770 258 (by decide)⟩

theorem compactSkywalkSignPool_valid (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (compactSkywalkSignPoolA w i).Valid ∧ (compactSkywalkSignPoolB w i).Valid := by
  have hw := narrowSkywalkRouteWidth_bounds i hi
  have nd := compactSkywalkSignPool_wordsND w i hi hn
  exact ⟨compactSkywalkSignWord_valid _ _ (by omega)
    (by simpa [skywalkPoolA,wireBlock] using hw.2.1) nd.1,
    compactSkywalkSignWord_valid _ _ (by omega)
    (by simpa [skywalkPoolB,wireBlock] using hw.2.1) nd.2⟩

theorem compactSkywalkSignPool_wordsDisjoint (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) : (skywalkPoolA w i).Disjoint (skywalkPoolB w) := by
  apply List.disjoint_left.mpr
  intro q ha hb
  simp only [skywalkPoolA,skywalkPoolB,wireBlock,List.mem_map,List.mem_range'_1] at ha hb
  obtain ⟨a,ha,hea⟩ := ha
  obtain ⟨b,hb,heb⟩ := hb
  have he := skywalkPool_index_inj w hn a b (by omega) (by omega) (hea.trans heb.symm)
  omega

/-- The exact universal route bound supplies both physical sign-copy banks
for every complete valid nonzero coprime input and every one of the512 stages. -/
theorem compactSkywalkSignPool_stage_copies (w : Nat → Wire) (x p i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (hi : i < 512) (s : BasisState)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s) :
    (compactSkywalkSignPoolA w i).Copies s ∧ (compactSkywalkSignPoolB w i).Copies s := by
  have fit := narrowSkywalkRoute_iter_fit x p i hp0 hx0 hpo hp hx hc hi
  have hw := narrowSkywalkRouteWidth_bounds i hi
  exact ⟨compactSkywalkSignWord_copies _ _ (by omega)
    (by simpa [skywalkPoolA,wireBlock] using hw.2.1) s _ hin.1 fit.1 fit.2.1,
    compactSkywalkSignWord_copies _ _ (by omega)
    (by simpa [skywalkPoolB,wireBlock] using hw.2.1) s _ hin.2.1 fit.2.2.1 fit.2.2.2⟩

/-- All measurement streams are immaterial to these Clifford prefixes. -/

theorem compactSkywalkSign_no_measure_append (p q : Program) (hp : measurementCount p = 0)
    (s : State) (m : List Bool) : run (p++q) m s = run q m (run p m s) := by
  have h := run_take p m s
  rw [hp,List.take_zero] at h
  rw [run_append,hp,List.take_zero,List.drop_zero,h]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkSignReleasePair.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem word_subviews (r : List Wire) (n : Nat) (hn : 0 < n) (hle : n ≤ r.length) :
    (compactSkywalkSignWord r n).retained⊆r ∧
    (compactSkywalkSignWord r n).released⊆r ∧ (compactSkywalkSignWord r n).sign ∈ r := by
  have he := compactSkywalkSignWord_expanded r n hn hle
  refine ⟨?_,?_,?_⟩
  · intro q hq
    rw [←he]
    exact List.mem_append_left _ hq
  · intro q hq
    rw [←he]
    exact List.mem_append_right _ hq
  · have hs : (compactSkywalkSignWord r n).sign ∈ (compactSkywalkSignWord r n).retained := by
      simp [CompactSkywalkSignReleaseLayout.retained]
    have hx : (compactSkywalkSignWord r n).sign ∈ (compactSkywalkSignWord r n).expanded :=
      List.mem_append_left _ hs
    simpa only [he] using hx

private theorem same_signed (r : List Wire) (s t : BasisState)
    (he : ∀q ∈ r,t q = s q) : signedRegValue r t = signedRegValue r s := by
  unfold signedRegValue
  rw [regValue_congr r t s he]

/-- The emitted two-bank release really frees both physical tails, preserves
both exact signed prefix values and every outsider, and changes no phase. -/
theorem compactSkywalkSignPool_release_correct (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (hcA : (compactSkywalkSignPoolA w i).Copies s.basis)
    (hcB : (compactSkywalkSignPoolB w i).Copies s.basis) :
    (run (compactSkywalkSignPoolRelease w i) m s).phase = s.phase ∧
    (compactSkywalkSignPoolA w i).Clean (run (compactSkywalkSignPoolRelease w i) m s).basis ∧
    (compactSkywalkSignPoolB w i).Clean (run (compactSkywalkSignPoolRelease w i) m s).basis ∧
    signedRegValue (compactSkywalkSignPoolA w i).retained
      (run (compactSkywalkSignPoolRelease w i) m s).basis = signedRegValue (skywalkPoolA w i) s.basis ∧
    signedRegValue (compactSkywalkSignPoolB w i).retained
      (run (compactSkywalkSignPoolRelease w i) m s).basis = signedRegValue (skywalkPoolB w) s.basis ∧
    (∀q,q ∉ skywalkPoolA w i → q ∉ skywalkPoolB w →
      (run (compactSkywalkSignPoolRelease w i) m s).basis q = s.basis q) := by
  let A := compactSkywalkSignPoolA w i
  let B := compactSkywalkSignPoolB w i
  let u := run (compactSkywalkSignRelease A) m s
  let v := run (compactSkywalkSignRelease B) m u
  have hv := compactSkywalkSignPool_valid w i hi hn
  have hw := narrowSkywalkRouteWidth_bounds i hi
  have la : narrowSkywalkRouteWidth i ≤ (skywalkPoolA w i).length := by
    simpa [skywalkPoolA,wireBlock] using hw.2.1
  have lb : narrowSkywalkRouteWidth i ≤ (skywalkPoolB w).length := by
    simpa [skywalkPoolB,wireBlock] using hw.2.1
  have av := word_subviews (skywalkPoolA w i) (narrowSkywalkRouteWidth i) (by omega) la
  have bv := word_subviews (skywalkPoolB w) (narrowSkywalkRouteWidth i) (by omega) lb
  have sa := (compactSkywalkSignWord_support (skywalkPoolA w i)
    (narrowSkywalkRouteWidth i) (by omega) la).1
  have sb := (compactSkywalkSignWord_support (skywalkPoolB w)
    (narrowSkywalkRouteWidth i) (by omega) lb).1
  have hd := compactSkywalkSignPool_wordsDisjoint w i hi hn
  have ub : ∀q ∈ skywalkPoolB w,u.basis q = s.basis q := by
    intro q hq
    exact run_preserves_outside _ m s q (fun hs =>
      List.disjoint_left.mp hd (List.mem_toFinset.mp (sa hs)) hq)
  have va : ∀q ∈ skywalkPoolA w i,v.basis q = u.basis q := by
    intro q hq
    exact run_preserves_outside _ m u q (fun hs =>
      List.disjoint_left.mp hd hq (List.mem_toFinset.mp (sb hs)))
  have uCopiesB : B.Copies u.basis := by
    intro q hq
    rw [ub q (bv.2.1 hq),ub B.sign bv.2.2]
    exact hcB q hq
  have uCleanA := compactSkywalkSignRelease_clean A hv.1 s m hcA
  have vCleanA : A.Clean v.basis := by
    intro q hq
    exact (va q (av.2.1 hq)).trans (uCleanA q hq)
  have vCleanB := compactSkywalkSignRelease_clean B hv.2 u m uCopiesB
  have aValue := (same_signed A.retained u.basis v.basis
    (fun q hq => va q (av.1 hq))).trans
      (compactSkywalkSignRelease_signed A hv.1 s m hcA)
  have bValue := (compactSkywalkSignRelease_signed B hv.2 u m uCopiesB).trans
    (same_signed B.expanded s.basis u.basis (by
      intro q hq
      have he := compactSkywalkSignWord_expanded (skywalkPoolB w)
        (narrowSkywalkRouteWidth i) (by omega) lb
      change q ∈ (compactSkywalkSignWord (skywalkPoolB w) (narrowSkywalkRouteWidth i)).expanded at hq
      rw [he] at hq
      exact ub q hq))
  have ar : A.expanded = skywalkPoolA w i := compactSkywalkSignWord_expanded _ _ (by omega) la
  have br : B.expanded = skywalkPoolB w := compactSkywalkSignWord_expanded _ _ (by omega) lb
  rw [ar] at aValue
  rw [br] at bValue
  have ca := compactSkywalkSignRelease_counts A
  have actual : run (compactSkywalkSignPoolRelease w i) m s = v :=
    compactSkywalkSign_no_measure_append _ _ ca.2.1 s m
  rw [actual]
  have pa := (compactSkywalkSignRelease_phase_frame A hv.1 s m).1
  have pb := (compactSkywalkSignRelease_phase_frame B hv.2 u m).1
  refine ⟨pb.trans pa,vCleanA,vCleanB,aValue,bValue,?_⟩
  intro q hqa hqb
  have ua := run_preserves_outside (compactSkywalkSignRelease A) m s q
    (fun h => hqa (List.mem_toFinset.mp (sa h)))
  exact (run_preserves_outside (compactSkywalkSignRelease B) m u q
    (fun h => hqb (List.mem_toFinset.mp (sb h)))).trans ua

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkTickLayout.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

def compactSkywalkTickPreWidth (i : Nat) : Nat := narrowSkywalkRouteWidth i
def compactSkywalkTickPostWidth (i : Nat) : Nat := narrowSkywalkWidth i

/-- All arithmetic ports are the current physical prefix, with a fresh clean
extension. No omitted 258-bit sign copies are reconstructed for this tick. -/
def compactSkywalkTickLayout (w : Nat → Wire) (i : Nat) : SkywalkIntegerLayout :=
  let n := compactSkywalkTickPreWidth i
  { a0:=w i,b0:=w 770,ext:=w (i+n),history:=w (1028+i),
    previous:=w (skywalkPoolPreviousId i),aSign:=w (i+n-1),bSign:=w (770+n-1),
    aMid:=wireBlock w (i+1) (n-2),bMid:=wireBlock w 771 (n-2),
    carry:=wireBlock w 1540 (n-1) }

theorem compactSkywalkTick_width_bounds (i : Nat) (hi : i < 512) :
    3 ≤ compactSkywalkTickPreWidth i ∧ 2 ≤ compactSkywalkTickPostWidth i ∧
    compactSkywalkTickPostWidth i ≤ compactSkywalkTickPreWidth i ∧
    compactSkywalkTickPreWidth i ≤ 258 ∧
    compactSkywalkTickPreWidth i ≤ 514-i ∧
    compactSkywalkTickPostWidth i = compactSkywalkTickPreWidth (i+1) := by
  have a := narrowSkywalkRouteWidth_bounds i hi
  have b := narrowSkywalkWidth_bounds i hi
  unfold compactSkywalkTickPreWidth compactSkywalkTickPostWidth
    narrowSkywalkRouteWidth narrowSkywalkWidth at *
  omega

private theorem blockLast (w : Nat → Wire) (start count : Nat) (hc : 0 < count) :
    wireBlock w start (count-1)++[w (start+count-1)] = wireBlock w start count := by
  have h := wireBlock_append w start (count-1) 1
  have one : wireBlock w (start+(count-1)) 1 = [w (start+(count-1))] := by
    simp [wireBlock,List.range']
  rw [one] at h
  simpa only [show start+(count-1) = start+count-1 by omega,
    show count-1+1 = count by omega] using h

theorem compactSkywalkTick_ah (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).ah = wireBlock w (i+1) (compactSkywalkTickPreWidth i-1) := by
  have hb := compactSkywalkTick_width_bounds i hi
  have h := blockLast w (i+1) (compactSkywalkTickPreWidth i-1) (by omega)
  change wireBlock w (i+1) (compactSkywalkTickPreWidth i-2)++
    [w (i+compactSkywalkTickPreWidth i-1)] = _
  simpa only [show (compactSkywalkTickPreWidth i-1)-1 = compactSkywalkTickPreWidth i-2 by omega,
    show (i+1)+(compactSkywalkTickPreWidth i-1)-1 = i+compactSkywalkTickPreWidth i-1 by omega] using h

theorem compactSkywalkTick_bh (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).bh = wireBlock w 771 (compactSkywalkTickPreWidth i-1) := by
  have hb := compactSkywalkTick_width_bounds i hi
  have h := blockLast w 771 (compactSkywalkTickPreWidth i-1) (by omega)
  change wireBlock w 771 (compactSkywalkTickPreWidth i-2)++
    [w (770+compactSkywalkTickPreWidth i-1)] = _
  simpa only [show (compactSkywalkTickPreWidth i-1)-1 = compactSkywalkTickPreWidth i-2 by omega,
    show 771+(compactSkywalkTickPreWidth i-1)-1 = 770+compactSkywalkTickPreWidth i-1 by omega] using h

private theorem blockFirst (w : Nat → Wire) (start count : Nat) (hc : 0 < count) :
    w start::wireBlock w (start+1) (count-1) = wireBlock w start count := by
  have h := wireBlock_append w start 1 (count-1)
  have one : wireBlock w start 1 = [w start] := by simp [wireBlock,List.range']
  rw [one] at h
  simpa only [show 1+(count-1) = count by omega,List.singleton_append] using h

theorem compactSkywalkTick_a (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).a = wireBlock w i (compactSkywalkTickPreWidth i) := by
  have hb := compactSkywalkTick_width_bounds i hi
  rw [SkywalkIntegerLayout.a,compactSkywalkTick_ah w i hi]
  exact blockFirst w i _ (by omega)

theorem compactSkywalkTick_b (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).b = wireBlock w 770 (compactSkywalkTickPreWidth i) := by
  have hb := compactSkywalkTick_width_bounds i hi
  rw [SkywalkIntegerLayout.b,compactSkywalkTick_bh w i hi]
  exact blockFirst w 770 _ (by omega)

theorem compactSkywalkTick_half (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).half = wireBlock w (i+1) (compactSkywalkTickPreWidth i) := by
  have hb := compactSkywalkTick_width_bounds i hi
  rw [SkywalkIntegerLayout.half,compactSkywalkTick_ah w i hi]
  change wireBlock w (i+1) (compactSkywalkTickPreWidth i-1)++
    [w (i+compactSkywalkTickPreWidth i)] = _
  have h := blockLast w (i+1) (compactSkywalkTickPreWidth i) (by omega)
  simpa only [show (i+1)+compactSkywalkTickPreWidth i-1 = i+compactSkywalkTickPreWidth i by omega] using h

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkTickValidation.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private def compactTickControls (i : Nat) : List Nat :=
  [skywalkPoolPreviousId i,1028+i,i+compactSkywalkTickPreWidth i,i,770]
private def compactTickBlocks (i : Nat) : List Nat :=
  List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
    List.range' 771 (compactSkywalkTickPreWidth i-1)++
    List.range' 1540 (compactSkywalkTickPreWidth i-1)
private def compactTickIds (i : Nat) : List Nat := compactTickControls i++compactTickBlocks i

private theorem compactTickIdsND (i : Nat) (hi : i < 512) : (compactTickIds i).Nodup := by
  have hn := compactSkywalkTick_width_bounds i hi
  have a : (List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
      List.range' 771 (compactSkywalkTickPreWidth i-1)).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_range'_1] at hj hk
    omega
  have b : (compactTickBlocks i).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨a,List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_append,List.mem_range'_1] at hj hk
    omega
  have c : (compactTickControls i).Nodup := by
    by_cases hz : i = 0
    · subst i
      norm_num [compactTickControls,skywalkPoolPreviousId,compactSkywalkTickPreWidth,
        narrowSkywalkRouteWidth]
    · simp [compactTickControls,skywalkPoolPreviousId,hz]
      omega
  apply List.nodup_append'.mpr
  refine ⟨c,b,?_⟩
  apply List.disjoint_left.mpr
  intro j hj hk
  simp only [compactTickControls,List.mem_cons,List.not_mem_nil,or_false] at hj
  simp only [compactTickBlocks,List.mem_append,List.mem_range'_1] at hk
  by_cases hz : i = 0
  · simp only [skywalkPoolPreviousId,if_pos hz] at hj
    omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at hj
    omega

private theorem compactTickIdsBound (i j : Nat) (hi : i < 512)
    (hj : j ∈ compactTickIds i) : j < 1798 := by
  have hn := compactSkywalkTick_width_bounds i hi
  simp only [compactTickIds,compactTickControls,compactTickBlocks,List.mem_append,
    List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
  by_cases hz : i = 0
  · simp only [skywalkPoolPreviousId,if_pos hz] at hj
    omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at hj
    omega

private theorem compactTickWires (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).wires = (compactTickIds i).map w := by
  change w (skywalkPoolPreviousId i)::w (1028+i)::w (i+compactSkywalkTickPreWidth i)::
    w i::w 770::((compactSkywalkTickLayout w i).ah++(compactSkywalkTickLayout w i).bh++
      wireBlock w 1540 (compactSkywalkTickPreWidth i-1)) = _
  rw [compactSkywalkTick_ah w i hi,compactSkywalkTick_bh w i hi]
  simp [compactTickIds,compactTickControls,compactTickBlocks,wireBlock,List.map_append]

/-- The actual variable-width local tick has no aliases under pool injectivity. -/
theorem compactSkywalkTick_valid (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) : (compactSkywalkTickLayout w i).Valid := by
  constructor
  · simp [compactSkywalkTickLayout,wireBlock]
  · rw [compactSkywalkTick_ah w i hi]
    simp [compactSkywalkTickLayout,wireBlock]
  · rw [compactTickWires w i hi]
    apply List.Nodup.map_on
    · intro a ha b hb he
      exact skywalkPool_index_inj w hn a b (compactTickIdsBound i a hi ha)
        (compactTickIdsBound i b hi hb) he
    · exact compactTickIdsND i hi

theorem compactSkywalkTick_local_support (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).wires ⊆ skywalkPoolWires w := by
  rw [compactTickWires w i hi]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
  exact ⟨j,by have h := compactTickIdsBound i j hi hj; omega,rfl⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkTickProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

def compactSkywalkTickARelease (w : Nat → Wire) (i : Nat) : CompactSkywalkSignReleaseLayout :=
  compactSkywalkSignWord (compactSkywalkTickLayout w i).half (compactSkywalkTickPostWidth i)
def compactSkywalkTickBRelease (w : Nat → Wire) (i : Nat) : CompactSkywalkSignReleaseLayout :=
  compactSkywalkSignWord (compactSkywalkTickLayout w i).b (compactSkywalkTickPostWidth i)
def compactSkywalkTickCleanup (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkSignRelease (compactSkywalkTickARelease w i)++
    compactSkywalkSignRelease (compactSkywalkTickBRelease w i)

/-- Actual compact route/record on local prefixes, followed only by CX release
of the post-boundary sign tails. No full258 reconstruction is emitted. -/
def compactSkywalkTick (w : Nat → Wire) (i : Nat) : Program :=
  narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)++
    compactSkywalkTickCleanup w i

attribute [local irreducible] narrowSkywalkTick compactSkywalkSignRelease

private theorem recordWordsND (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.half.Nodup ∧ L.b.Nodup ∧ L.half.Disjoint L.b := by
  have h := (List.nodup_cons.mp (L.record_nodup hv)).2
  exact List.nodup_append'.mp (List.nodup_append'.mp h).1

theorem compactSkywalkTick_release_valid (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (compactSkywalkTickARelease w i).Valid ∧ (compactSkywalkTickBRelease w i).Valid := by
  have h := compactSkywalkTick_width_bounds i hi
  have nd := recordWordsND _ (compactSkywalkTick_valid w i hi hn)
  refine ⟨compactSkywalkSignWord_valid _ _ (by omega) ?_ nd.1,
    compactSkywalkSignWord_valid _ _ (by omega) ?_ nd.2.1⟩
  · rw [compactSkywalkTick_half w i hi,wireBlock_length]
    exact h.2.2.1
  · rw [compactSkywalkTick_b w i hi,wireBlock_length]
    exact h.2.2.1

theorem compactSkywalkTick_words_disjoint (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (compactSkywalkTickLayout w i).half.Disjoint (compactSkywalkTickLayout w i).b :=
  (recordWordsND _ (compactSkywalkTick_valid w i hi hn)).2.2

theorem compactSkywalkTick_cleanup_counts (w : Nat → Wire) (i : Nat) :
    toffoliCount (compactSkywalkTickCleanup w i) = 0 ∧
    measurementCount (compactSkywalkTickCleanup w i) = 0 := by
  have a := compactSkywalkSignRelease_counts (compactSkywalkTickARelease w i)
  have b := compactSkywalkSignRelease_counts (compactSkywalkTickBRelease w i)
  rw [compactSkywalkTickCleanup,toffoliCount_append,measurementCount_append,a.1,a.2.1,b.1,b.2.1]
  exact ⟨rfl,rfl⟩

theorem compactSkywalkTick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (compactSkywalkTick w i) =
      (compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1) ∧
    measurementCount (compactSkywalkTick w i) = compactSkywalkTickPostWidth i-1 := by
  have h := compactSkywalkTick_width_bounds i hi
  have len : (compactSkywalkTickLayout w i).half.length = compactSkywalkTickPreWidth i := by
    rw [compactSkywalkTick_half w i hi,wireBlock_length]
  have c := narrowSkywalkTick_counts _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by rw [len]; exact h.2.2.1)
  have z := compactSkywalkTick_cleanup_counts w i
  rw [compactSkywalkTick,toffoliCount_append,measurementCount_append,c.1,c.2.1,z.1,z.2]
  rw [compactSkywalkTick_ah w i hi,wireBlock_length]
  exact ⟨by omega,by omega⟩

theorem compactSkywalkTick_cleanup_support (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    wires (compactSkywalkTickCleanup w i) ⊆ (compactSkywalkTickLayout w i).wires.toFinset := by
  have h := compactSkywalkTick_width_bounds i hi
  have a := (compactSkywalkSignWord_support (compactSkywalkTickLayout w i).half
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)).1
  have b := (compactSkywalkSignWord_support (compactSkywalkTickLayout w i).b
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_b w i hi,wireBlock_length]; exact h.2.2.1)).1
  intro q hq
  simp only [compactSkywalkTickCleanup,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have ha := List.mem_toFinset.mp (a hq)
    simp only [SkywalkIntegerLayout.half,SkywalkIntegerLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
    tauto
  · have hb := List.mem_toFinset.mp (b hq)
    simp only [SkywalkIntegerLayout.b,SkywalkIntegerLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons] at hb ⊢
    tauto

theorem compactSkywalkTick_support (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    wires (compactSkywalkTick w i) ⊆ (compactSkywalkTickLayout w i).wires.toFinset := by
  have h := compactSkywalkTick_width_bounds i hi
  have n := (narrowSkywalkTick_wires_subset _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)).1
  have c := compactSkywalkTick_cleanup_support w i hi
  rw [compactSkywalkTick,wires_append,Finset.union_subset_iff]
  exact ⟨n,c⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkTickProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem record_fit (H A B : Int) (ha0 : -H ≤ A) (ha1 : A < H)
    (hb0 : -H ≤ B) (hb1 : B < H) :
    -H ≤ signedRecordValue A B ∧ signedRecordValue A B < H := by
  by_cases ha : A < 0 <;> by_cases hb : B < 0 <;>
    simp [signedRecordValue,signedRecordControl,signedIntegerValue,SkywalkRails.neg,ha,hb] <;> omega

/-- Cancellation keeps both post-tick rails inside the strict record interval. -/
theorem compactSkywalkTick_step_fit (A B : Int) (G : Bool) (H : Int)
    (hp : (A+B)%2 = 1)
    (ha0 : -H ≤ (SkywalkRails.route A B).1/2) (ha1 : (SkywalkRails.route A B).1/2 < H)
    (hb0 : -H ≤ (SkywalkRails.route A B).2) (hb1 : (SkywalkRails.route A B).2 < H) :
    -H ≤ (SkywalkRails.step ⟨A,B,G⟩).h ∧ (SkywalkRails.step ⟨A,B,G⟩).h < H ∧
    -H ≤ (SkywalkRails.step ⟨A,B,G⟩).k ∧ (SkywalkRails.step ⟨A,B,G⟩).k < H := by
  have he := SkywalkRails.route_even A B hp
  have hs : SkywalkRails.sameSign ((SkywalkRails.route A B).1/2) (SkywalkRails.route A B).2 =
      SkywalkRails.sameSign (SkywalkRails.route A B).1 (SkywalkRails.route A B).2 := by
    unfold SkywalkRails.sameSign
    rw [SkywalkRails.neg_half _ he]
  have hk := record_fit H ((SkywalkRails.route A B).1/2) (SkywalkRails.route A B).2 ha0 ha1 hb0 hb1
  rw [signedRecordValue_rails,hs] at hk
  exact ⟨ha0,ha1,hk.1,hk.2⟩

/-- The native tick already uses only the actual local prefixes. Every input
fit obligation is the same universally proved post-route envelope. -/
theorem compactSkywalkTick_native_spec (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (A B : Int) (G : Bool) (hp : (A+B)%2 = 1)
    (ha0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int))
    (hb0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int)) :
    Triple (SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G)
      (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i))
      (SkywalkIntegerOutput (compactSkywalkTickLayout w i) A B G) := by
  have h := compactSkywalkTick_width_bounds i hi
  exact narrowSkywalkTick_spec _ (compactSkywalkTick_valid w i hi hn) _ (by omega)
    (by rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)
    A B G hp ha0 ha1 hb0 hb1

/-- The actual locally emitted native result supplies both sign-release
premises; no post-tick sign-copy oracle is assumed. -/
theorem compactSkywalkTick_native_copies (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (A B : Int) (G : Bool) (hp : (A+B)%2 = 1)
    (ha0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int))
    (hb0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int))
    (s : State) (m : List Bool)
    (hin : SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G s.basis) :
    let t := run (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)) m s
    (compactSkywalkTickARelease w i).Copies t.basis ∧
    (compactSkywalkTickBRelease w i).Copies t.basis := by
  dsimp only
  have h := compactSkywalkTick_width_bounds i hi
  have fit := compactSkywalkTick_step_fit A B G _ hp ha0 ha1 hb0 hb1
  have out := (compactSkywalkTick_native_spec w i hi hn A B G hp ha0 ha1 hb0 hb1 s m hin).2
  exact ⟨compactSkywalkSignWord_copies _ _ (by omega)
    (by rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1) _ _
      out.1 fit.1 fit.2.1,
    compactSkywalkSignWord_copies _ _ (by omega)
    (by rw [compactSkywalkTick_b w i hi,wireBlock_length]; exact h.2.2.1) _ _
      out.2.1 fit.2.2.1 fit.2.2.2⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkTickEntry.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem block_prefix_CompactSkywalkTickEntry (w : Nat → Wire) (start len n : Nat) (hn : n ≤ len) :
    (wireBlock w start len).take n=wireBlock w start n := by
  have h := wireBlock_append w start n (len-n)
  have e : n+(len-n)=len := by omega
  rw [e] at h
  rw [←h]
  have take : (wireBlock w start n ++ wireBlock w (start+n) (len-n)).take
      (wireBlock w start n).length = wireBlock w start n := List.take_left
  simpa only [wireBlock_length] using take

private theorem entry_views (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkSignPoolA w i).retained=(compactSkywalkTickLayout w i).a ∧
    (compactSkywalkSignPoolB w i).retained=(compactSkywalkTickLayout w i).b := by
  have hw := compactSkywalkTick_width_bounds i hi
  have na : narrowSkywalkRouteWidth i ≤ (skywalkPoolA w i).length := by
    simpa only [skywalkPoolA,wireBlock_length] using hw.2.2.2.1
  have nb : narrowSkywalkRouteWidth i ≤ (skywalkPoolB w).length := by
    simpa only [skywalkPoolB,wireBlock_length] using hw.2.2.2.1
  have hpos : 0 < narrowSkywalkRouteWidth i := by
    change 0 < compactSkywalkTickPreWidth i
    omega
  have va := compactSkywalkSignWord_retained (skywalkPoolA w i) (narrowSkywalkRouteWidth i)
    hpos na
  have vb := compactSkywalkSignWord_retained (skywalkPoolB w) (narrowSkywalkRouteWidth i)
    hpos nb
  constructor
  · change (compactSkywalkSignWord (skywalkPoolA w i) (narrowSkywalkRouteWidth i)).retained=_
    rw [va,skywalkPoolA,compactSkywalkTick_a w i hi]
    exact block_prefix_CompactSkywalkTickEntry w i 258 _ hw.2.2.2.1
  · change (compactSkywalkSignWord (skywalkPoolB w) (narrowSkywalkRouteWidth i)).retained=_
    rw [vb,skywalkPoolB,compactSkywalkTick_b w i hi]
    exact block_prefix_CompactSkywalkTickEntry w 770 258 _ hw.2.2.2.1

private theorem index_away (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i < 512) (hj : j < 1798)
    (ha : j < i ∨ i+258 ≤ j) (hb : j < 770 ∨ 1028 ≤ j) :
    w j∉skywalkPoolA w i ∧ w j∉skywalkPoolB w := by
  constructor <;> intro hq
  · obtain ⟨k,hk,he⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hk
    have e := skywalkPool_index_inj w hn k j (by omega) hj he
    omega
  · obtain ⟨k,hk,he⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hk
    have e := skywalkPool_index_inj w hn k j (by omega) hj he
    omega

private theorem extension_in_release (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hsmall : compactSkywalkTickPreWidth i < 258) :
    w (i+compactSkywalkTickPreWidth i)∈(compactSkywalkSignPoolA w i).released := by
  have hw := compactSkywalkTick_width_bounds i hi
  change w (i+compactSkywalkTickPreWidth i)∈
    (wireBlock w i 258).drop (compactSkywalkTickPreWidth i)
  have h := wireBlock_append w i (compactSkywalkTickPreWidth i)
    (258-compactSkywalkTickPreWidth i)
  rw [show compactSkywalkTickPreWidth i+(258-compactSkywalkTickPreWidth i)=258 by omega] at h
  rw [←h]
  have drop : (wireBlock w i (compactSkywalkTickPreWidth i) ++
      wireBlock w (i+compactSkywalkTickPreWidth i) (258-compactSkywalkTickPreWidth i)).drop
      (wireBlock w i (compactSkywalkTickPreWidth i)).length =
      wireBlock w (i+compactSkywalkTickPreWidth i) (258-compactSkywalkTickPreWidth i) := List.drop_left
  simp only [wireBlock_length] at drop
  rw [drop]
  apply List.mem_map.mpr
  exact ⟨i+compactSkywalkTickPreWidth i,by simp only [List.mem_range'_1]; omega,rfl⟩

/-- Every zero required by the local tick comes from actual release or
the old fresh-extension/work frame. There is no new clean-work oracle. -/
theorem compactSkywalkTickEntry_from_stage (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (hi : i < 512) (s : State) (m : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    let t := run (compactSkywalkSignPoolRelease w i) m s
    t.phase=s.phase ∧ SkywalkIntegerInput (compactSkywalkTickLayout w i) r.a r.b r.g t.basis := by
  dsimp only
  generalize ht : run (compactSkywalkSignPoolRelease w i) m s=t
  have copies := compactSkywalkSignPool_stage_copies w x p i hp0 hx0 hpo hp hx hc hi s.basis hin
  have release := compactSkywalkSignPool_release_correct w i hi hn s m copies.1 copies.2
  rw [ht] at release
  obtain ⟨phase,cleanA,cleanB,valA,valB,frame⟩ := release
  have views := entry_views w i hi
  rw [views.1] at valA
  rw [views.2] at valB
  have keep (j : Nat) (hj : j < 1798) (ha : j < i ∨ i+258 ≤ j)
      (hb : j < 770 ∨ 1028 ≤ j) : t.basis (w j)=s.basis (w j) := by
    have away := index_away w hn i j hi hj ha hb
    exact frame _ away.1 away.2
  have prev := keep (skywalkPoolPreviousId i) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega)
  have fresh := hin.2.2.2.2.1 i (Nat.le_refl i) hi
  refine ⟨phase,valA.trans hin.1,valB.trans hin.2.1,?_,?_,?_,?_⟩
  · change t.basis (w (skywalkPoolPreviousId i))=_
    exact prev.trans hin.2.2.1
  · change t.basis (w (i+compactSkywalkTickPreWidth i))=false
    have width := (compactSkywalkTick_width_bounds i hi).2.2.2.1
    by_cases hfull : compactSkywalkTickPreWidth i=258
    · rw [hfull,keep (i+258) (by omega) (by omega) (by omega)]
      exact fresh.1
    · exact cleanA _ (extension_in_release w i hi (by omega))
  · change t.basis (w (1028+i))=false
    exact (keep (1028+i) (by omega) (by omega) (by omega)).trans fresh.2
  · apply (regValue_zero _ _).mpr
    intro q hq
    change q∈wireBlock w 1540 (compactSkywalkTickPreWidth i-1) at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have width := (compactSkywalkTick_width_bounds i hi).2.2.2.1
    have before := (regValue_zero _ _).mp hin.2.2.2.2.2.1 (w j) (by
      apply List.mem_map.mpr
      exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩)
    exact (keep j (by omega) (by omega) (by omega)).trans before

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkTickOutputCleanup.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem subviews (r : List Wire) (n : Nat) (hn : 0 < n) (hle : n ≤ r.length) :
    (compactSkywalkSignWord r n).retained ⊆ r ∧
    (compactSkywalkSignWord r n).released ⊆ r ∧ (compactSkywalkSignWord r n).sign ∈ r := by
  have he := compactSkywalkSignWord_expanded r n hn hle
  refine ⟨?_,?_,?_⟩
  · intro q hq
    rw [←he]
    exact List.mem_append_left _ hq
  · intro q hq
    rw [←he]
    exact List.mem_append_right _ hq
  · have hs : (compactSkywalkSignWord r n).sign ∈ (compactSkywalkSignWord r n).retained := by
      simp [CompactSkywalkSignReleaseLayout.retained]
    have hx : (compactSkywalkSignWord r n).sign ∈ (compactSkywalkSignWord r n).expanded :=
      List.mem_append_left _ hs
    simpa only [he] using hx

private theorem same_signed_CompactSkywalkTickOutputCleanup (r : List Wire) (s t : BasisState)
    (he : ∀q ∈ r,t q = s q) : signedRegValue r t = signedRegValue r s := by
  unfold signedRegValue
  rw [regValue_congr r t s he]

/-- These are actual two-bank CX instructions, with both clean tails and
retained signed values proved from the native result's sign-copy predicates. -/
theorem compactSkywalkTickOutput_cleanup_correct (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (hcA : (compactSkywalkTickARelease w i).Copies s.basis)
    (hcB : (compactSkywalkTickBRelease w i).Copies s.basis) :
    (run (compactSkywalkTickCleanup w i) m s).phase = s.phase ∧
    (compactSkywalkTickARelease w i).Clean (run (compactSkywalkTickCleanup w i) m s).basis ∧
    (compactSkywalkTickBRelease w i).Clean (run (compactSkywalkTickCleanup w i) m s).basis ∧
    signedRegValue (compactSkywalkTickARelease w i).retained
      (run (compactSkywalkTickCleanup w i) m s).basis =
        signedRegValue (compactSkywalkTickLayout w i).half s.basis ∧
    signedRegValue (compactSkywalkTickBRelease w i).retained
      (run (compactSkywalkTickCleanup w i) m s).basis =
        signedRegValue (compactSkywalkTickLayout w i).b s.basis ∧
    (∀q,q ∉ (compactSkywalkTickLayout w i).half → q ∉ (compactSkywalkTickLayout w i).b →
      (run (compactSkywalkTickCleanup w i) m s).basis q = s.basis q) := by
  let L := compactSkywalkTickLayout w i
  let A := compactSkywalkTickARelease w i
  let B := compactSkywalkTickBRelease w i
  let u := run (compactSkywalkSignRelease A) m s
  let v := run (compactSkywalkSignRelease B) m u
  have hv := compactSkywalkTick_release_valid w i hi hn
  have hw := compactSkywalkTick_width_bounds i hi
  have la : compactSkywalkTickPostWidth i ≤ L.half.length := by
    rw [compactSkywalkTick_half w i hi,wireBlock_length]
    exact hw.2.2.1
  have lb : compactSkywalkTickPostWidth i ≤ L.b.length := by
    rw [compactSkywalkTick_b w i hi,wireBlock_length]
    exact hw.2.2.1
  have av := subviews L.half (compactSkywalkTickPostWidth i) (by omega) la
  have bv := subviews L.b (compactSkywalkTickPostWidth i) (by omega) lb
  have sa := (compactSkywalkSignWord_support L.half (compactSkywalkTickPostWidth i) (by omega) la).1
  have sb := (compactSkywalkSignWord_support L.b (compactSkywalkTickPostWidth i) (by omega) lb).1
  have hd := compactSkywalkTick_words_disjoint w i hi hn
  have ub : ∀q ∈ L.b,u.basis q = s.basis q := by
    intro q hq
    exact run_preserves_outside _ m s q (fun h =>
      List.disjoint_left.mp hd (List.mem_toFinset.mp (sa h)) hq)
  have va : ∀q ∈ L.half,v.basis q = u.basis q := by
    intro q hq
    exact run_preserves_outside _ m u q (fun h =>
      List.disjoint_left.mp hd hq (List.mem_toFinset.mp (sb h)))
  have uCopiesB : B.Copies u.basis := by
    intro q hq
    have keepQ : u.basis q = s.basis q := ub q (bv.2.1 hq)
    have keepS : u.basis B.sign = s.basis B.sign := ub B.sign bv.2.2
    rw [keepQ,keepS]
    exact hcB q hq
  have uCleanA := compactSkywalkSignRelease_clean A hv.1 s m hcA
  have vCleanA : A.Clean v.basis := by
    intro q hq
    exact (va q (av.2.1 hq)).trans (uCleanA q hq)
  have vCleanB := compactSkywalkSignRelease_clean B hv.2 u m uCopiesB
  have aValue := (same_signed_CompactSkywalkTickOutputCleanup A.retained u.basis v.basis
    (fun q hq => va q (av.1 hq))).trans (compactSkywalkSignRelease_signed A hv.1 s m hcA)
  have bValue := (compactSkywalkSignRelease_signed B hv.2 u m uCopiesB).trans
    (same_signed_CompactSkywalkTickOutputCleanup B.expanded s.basis u.basis (by
      intro q hq
      have he : B.expanded = L.b := compactSkywalkSignWord_expanded _ _ (by omega) lb
      rw [he] at hq
      exact ub q hq))
  have ar : A.expanded = L.half := compactSkywalkSignWord_expanded _ _ (by omega) la
  have br : B.expanded = L.b := compactSkywalkSignWord_expanded _ _ (by omega) lb
  rw [ar] at aValue
  rw [br] at bValue
  have ca := compactSkywalkSignRelease_counts A
  have actual : run (compactSkywalkTickCleanup w i) m s = v :=
    compactSkywalkSign_no_measure_append _ _ ca.2.1 s m
  rw [actual]
  have pa := (compactSkywalkSignRelease_phase_frame A hv.1 s m).1
  have pb := (compactSkywalkSignRelease_phase_frame B hv.2 u m).1
  refine ⟨pb.trans pa,vCleanA,vCleanB,aValue,bValue,?_⟩
  intro q hqa hqb
  have ua := run_preserves_outside (compactSkywalkSignRelease A) m s q
    (fun h => hqa (List.mem_toFinset.mp (sa h)))
  exact (run_preserves_outside (compactSkywalkSignRelease B) m u q
    (fun h => hqb (List.mem_toFinset.mp (sb h)))).trans ua

/-- Orientation, sign-history, previous control and every local carry are
outside the two mutable words, by the physical local-layout distinctness. -/
theorem compactSkywalkTickOutput_metadataAway (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (q : Wire)
    (hq : q ∈ [(compactSkywalkTickLayout w i).a0,(compactSkywalkTickLayout w i).history,
      (compactSkywalkTickLayout w i).previous]++(compactSkywalkTickLayout w i).carry) :
    q ∉ (compactSkywalkTickLayout w i).half ∧ q ∉ (compactSkywalkTickLayout w i).b := by
  have h := List.nodup_iff_count.mp (compactSkywalkTick_valid w i hi hn).nodup q
  have hp := List.count_pos_iff.mpr hq
  constructor <;> intro hd <;> have hv := List.count_pos_iff.mpr hd
  all_goals
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
      List.count_append,List.count_cons,List.count_nil] at h hp hv
    omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkTickOutputSpec.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The post-boundary integer words are physically retained prefixes.
History is still the actual emitted orientation/sign history, not recomputed data. -/
def CompactSkywalkTickOutput (w : Nat → Wire) (i : Nat) (A B : Int) (G : Bool)
    (s : BasisState) : Prop :=
  let L := compactSkywalkTickLayout w i
  let t := SkywalkRails.step ⟨A,B,G⟩
  signedRegValue (compactSkywalkTickARelease w i).retained s = t.h ∧
  signedRegValue (compactSkywalkTickBRelease w i).retained s = t.k ∧
  s L.a0 = t.g ∧ s L.history = t.s ∧ s L.previous = G ∧ regValue L.carry s = 0 ∧
  (compactSkywalkTickARelease w i).Clean s ∧ (compactSkywalkTickBRelease w i).Clean s

/-- The cleanup suffix has zero measurements, so its stream can be chosen
independently of the native tick's consumed prefix. -/
theorem compactSkywalkTickOutput_run (w : Nat → Wire) (i : Nat) (s : State) (m : List Bool) :
    run (compactSkywalkTick w i) m s =
      run (compactSkywalkTickCleanup w i) m
        (run (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)) m s) := by
  rw [compactSkywalkTick,run_append,run_take]
  have hz := (compactSkywalkTick_cleanup_counts w i).2
  have h1 := run_take (compactSkywalkTickCleanup w i)
    (m.drop (measurementCount
      (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i))))
    (run (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)) m s)
  have h2 := run_take (compactSkywalkTickCleanup w i) m
    (run (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)) m s)
  rw [hz,List.take_zero] at h1 h2
  exact h1.symm.trans h2

/-- Full actual compact-tick semantics. Copies for both cleanup banks are
proved from the native result; no sign-copy premise is added to the input. -/
theorem compactSkywalkTickOutput_spec (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (A B : Int) (G : Bool) (hp : (A+B)%2 = 1)
    (ha0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int))
    (hb0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int)) :
    Triple (SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G)
      (compactSkywalkTick w i) (CompactSkywalkTickOutput w i A B G) := by
  intro s m hin
  let L := compactSkywalkTickLayout w i
  let t := run (narrowSkywalkTick L (compactSkywalkTickPostWidth i)) m s
  let u := run (compactSkywalkTickCleanup w i) m t
  have native := compactSkywalkTick_native_spec w i hi hn A B G hp ha0 ha1 hb0 hb1 s m hin
  have copies := compactSkywalkTick_native_copies w i hi hn A B G hp ha0 ha1 hb0 hb1 s m hin
  have cleanup := compactSkywalkTickOutput_cleanup_correct w i hi hn t m copies.1 copies.2
  have keep : ∀q,q ∈ [L.a0,L.history,L.previous]++L.carry → u.basis q = t.basis q := by
    intro q hq
    have away := compactSkywalkTickOutput_metadataAway w i hi hn q hq
    exact cleanup.2.2.2.2.2 q away.1 away.2
  have carry : regValue L.carry u.basis = 0 := by
    apply Eq.trans (regValue_congr L.carry u.basis t.basis ?_) native.2.2.2.2.2.2
    intro q hq
    exact keep q (by simp [hq])
  have actual : run (compactSkywalkTick w i) m s = u := compactSkywalkTickOutput_run w i s m
  rw [actual]
  refine ⟨cleanup.1.trans native.1,cleanup.2.2.2.1.trans native.2.1,
    cleanup.2.2.2.2.1.trans native.2.2.1,
    (keep L.a0 (by simp)).trans native.2.2.2.1,
    (keep L.history (by simp)).trans native.2.2.2.2.1,
    (keep L.previous (by simp)).trans native.2.2.2.2.2.1,
    carry,cleanup.2.1,cleanup.2.2.1⟩

/-- Complete outsider frame for the actual compact program, independent of
input values and measurement outcomes. -/
theorem compactSkywalkTickOutput_frame (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ (compactSkywalkTickLayout w i).wires) :
    (run (compactSkywalkTick w i) m s).basis q = s.basis q :=
  run_preserves_outside _ m s q (fun h =>
    hq (List.mem_toFinset.mp (compactSkywalkTick_support w i hi hn h)))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageViews.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Mathematical full-word interpretation. This is a basis function, not an
emitted sign-expansion program or an allocated high-copy register. -/
def compactSkywalkStageVirtual (w : Nat → Wire) (i : Nat) (s : BasisState) : BasisState :=
  let A := compactSkywalkSignPoolA w i
  let B := compactSkywalkSignPoolB w i
  fun q => if q ∈ A.released then s A.sign else if q ∈ B.released then s B.sign else s q

def CompactSkywalkStage (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (s : BasisState) : Prop :=
  SkywalkIntegerStage w r i (compactSkywalkStageVirtual w i s) ∧
  (compactSkywalkSignPoolA w i).Clean s ∧ (compactSkywalkSignPoolB w i).Clean s

theorem compactSkywalkStage_width (i : Nat) (hi : i ≤ 512) :
    2 ≤ narrowSkywalkRouteWidth i ∧ narrowSkywalkRouteWidth i ≤ 258 := by
  unfold narrowSkywalkRouteWidth
  omega

private theorem blockND_CompactSkywalkStageViews (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start count : Nat) (hb : start+count ≤ 1798) : (wireBlock w start count).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj he
    simp only [List.mem_range'_1] at hi hj
    exact skywalkPool_index_inj w hn i j (by omega) (by omega) he
  · exact List.nodup_range'

theorem compactSkywalkStage_valid (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (compactSkywalkSignPoolA w i).Valid ∧ (compactSkywalkSignPoolB w i).Valid := by
  have h := compactSkywalkStage_width i hi
  exact ⟨compactSkywalkSignWord_valid _ _ (by omega)
    (by simpa only [skywalkPoolA,wireBlock_length] using h.2)
    (blockND_CompactSkywalkStageViews w hn i 258 (by omega)),
    compactSkywalkSignWord_valid _ _ (by omega)
    (by simpa only [skywalkPoolB,wireBlock_length] using h.2)
    (blockND_CompactSkywalkStageViews w hn 770 258 (by decide))⟩

theorem compactSkywalkStage_expanded (w : Nat → Wire) (i : Nat) (hi : i ≤ 512) :
    (compactSkywalkSignPoolA w i).expanded = skywalkPoolA w i ∧
    (compactSkywalkSignPoolB w i).expanded = skywalkPoolB w := by
  have h := compactSkywalkStage_width i hi
  exact ⟨compactSkywalkSignWord_expanded _ _ (by omega)
    (by simpa only [skywalkPoolA,wireBlock_length] using h.2),
    compactSkywalkSignWord_expanded _ _ (by omega)
    (by simpa only [skywalkPoolB,wireBlock_length] using h.2)⟩

theorem compactSkywalkStage_words_disjoint (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) : (skywalkPoolA w i).Disjoint (skywalkPoolB w) := by
  apply List.disjoint_left.mpr
  intro q ha hb
  simp only [skywalkPoolA,skywalkPoolB,wireBlock,List.mem_map,List.mem_range'_1] at ha hb
  obtain ⟨a,ha,hea⟩ := ha
  obtain ⟨b,hb,heb⟩ := hb
  have he := skywalkPool_index_inj w hn a b (by omega) (by omega) (hea.trans heb.symm)
  omega

/-- Outside the two physically released banks the virtual basis is unchanged. -/
theorem compactSkywalkStage_virtual_outside (w : Nat → Wire) (i : Nat) (s : BasisState)
    (q : Wire) (ha : q ∉ (compactSkywalkSignPoolA w i).released)
    (hb : q ∉ (compactSkywalkSignPoolB w i).released) :
    compactSkywalkStageVirtual w i s q = s q := by
  simp [compactSkywalkStageVirtual,ha,hb]

theorem compactSkywalkStage_zero_tails (w : Nat → Wire) :
    (compactSkywalkSignPoolA w 0).released = [] ∧
    (compactSkywalkSignPoolB w 0).released = [] := by
  constructor
  · change (wireBlock w 0 258).drop 258 = []
    have h : (wireBlock w 0 258).drop (wireBlock w 0 258).length = [] := List.drop_length
    simpa only [wireBlock_length] using h
  · change (wireBlock w 770 258).drop 258 = []
    have h : (wireBlock w 770 258).drop (wireBlock w 770 258).length = [] := List.drop_length
    simpa only [wireBlock_length] using h

theorem compactSkywalkStage_zero_virtual (w : Nat → Wire) (s : BasisState) :
    compactSkywalkStageVirtual w 0 s = s := by
  funext q
  simp [compactSkywalkStageVirtual,(compactSkywalkStage_zero_tails w).1,
    (compactSkywalkStage_zero_tails w).2]

/-- The existing seed-stage predicate is exactly the initial compact stage. -/
theorem compactSkywalkStage_zero_iff (w : Nat → Wire) (r : SkywalkRails.State) (s : BasisState) :
    CompactSkywalkStage w r 0 s ↔ SkywalkIntegerStage w r 0 s := by
  simp [CompactSkywalkStage,compactSkywalkStage_zero_virtual,
    CompactSkywalkSignReleaseLayout.Clean,(compactSkywalkStage_zero_tails w).1,
    (compactSkywalkStage_zero_tails w).2]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageVirtual.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem signed_congr (r : List Wire) (s t : BasisState)
    (he : ∀q∈r,s q=t q) : signedRegValue r s=signedRegValue r t := by
  unfold signedRegValue
  rw [regValue_congr r s t he]

private theorem parts (w : Nat → Wire) (i : Nat) (hi : i ≤ 512) :
    (compactSkywalkSignPoolA w i).released ⊆ skywalkPoolA w i ∧
    (compactSkywalkSignPoolB w i).released ⊆ skywalkPoolB w ∧
    (compactSkywalkSignPoolA w i).sign ∈ skywalkPoolA w i ∧
    (compactSkywalkSignPoolB w i).sign ∈ skywalkPoolB w := by
  have he := compactSkywalkStage_expanded w i hi
  refine ⟨?_,?_,?_,?_⟩
  · intro q hq; rw [←he.1]; exact List.mem_append_right _ hq
  · intro q hq; rw [←he.2]; exact List.mem_append_right _ hq
  · have hs : (compactSkywalkSignPoolA w i).sign ∈ (compactSkywalkSignPoolA w i).expanded :=
      List.mem_append_left _ (by simp [CompactSkywalkSignReleaseLayout.retained])
    simpa only [he.1] using hs
  · have hs : (compactSkywalkSignPoolB w i).sign ∈ (compactSkywalkSignPoolB w i).expanded :=
      List.mem_append_left _ (by simp [CompactSkywalkSignReleaseLayout.retained])
    simpa only [he.2] using hs

theorem compactSkywalkStage_virtual_signs (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    compactSkywalkStageVirtual w i s (compactSkywalkSignPoolA w i).sign =
      s (compactSkywalkSignPoolA w i).sign ∧
    compactSkywalkStageVirtual w i s (compactSkywalkSignPoolB w i).sign =
      s (compactSkywalkSignPoolB w i).sign := by
  have hv := compactSkywalkStage_valid w i hi hn
  have hd := compactSkywalkStage_words_disjoint w i hi hn
  have hp := parts w i hi
  constructor
  · apply compactSkywalkStage_virtual_outside
    · exact (compactSkywalkSignPoolA w i).signAway hv.1
    · intro hq
      exact List.disjoint_left.mp hd hp.2.2.1 (hp.2.1 hq)
  · apply compactSkywalkStage_virtual_outside
    · intro hq
      exact List.disjoint_left.mp hd (hp.1 hq) hp.2.2.2
    · exact (compactSkywalkSignPoolB w i).signAway hv.2

theorem compactSkywalkStage_virtual_copies (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    (compactSkywalkSignPoolA w i).Copies (compactSkywalkStageVirtual w i s) ∧
    (compactSkywalkSignPoolB w i).Copies (compactSkywalkStageVirtual w i s) := by
  have hs := compactSkywalkStage_virtual_signs w i hi hn s
  have hd := compactSkywalkStage_words_disjoint w i hi hn
  have hp := parts w i hi
  constructor
  · intro q hq
    rw [hs.1]
    simp [compactSkywalkStageVirtual,hq]
  · intro q hq
    have ha : q ∉ (compactSkywalkSignPoolA w i).released := by
      intro hm
      exact List.disjoint_left.mp hd (hp.1 hm) (hp.2.1 hq)
    rw [hs.2]
    simp [compactSkywalkStageVirtual,ha,hq]

/-- Virtual full reads are exactly the current physical retained signed reads. -/
theorem compactSkywalkStage_virtual_values (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    signedRegValue (skywalkPoolA w i) (compactSkywalkStageVirtual w i s) =
      signedRegValue (compactSkywalkSignPoolA w i).retained s ∧
    signedRegValue (skywalkPoolB w) (compactSkywalkStageVirtual w i s) =
      signedRegValue (compactSkywalkSignPoolB w i).retained s := by
  have hv := compactSkywalkStage_valid w i hi hn
  have he := compactSkywalkStage_expanded w i hi
  have hd := compactSkywalkStage_words_disjoint w i hi hn
  have hp := parts w i hi
  constructor
  · rw [←he.1]
    apply Eq.trans (signed_congr _ _ _ ?_)
      (compactSkywalkSignRelease_virtual_signed _ hv.1 s)
    intro q hq
    have hb : q ∉ (compactSkywalkSignPoolB w i).released := by
      intro hm
      rw [he.1] at hq
      exact List.disjoint_left.mp hd hq (hp.2.1 hm)
    simp [compactSkywalkStageVirtual,CompactSkywalkSignReleaseLayout.reconstructed,hb]
  · rw [←he.2]
    apply Eq.trans (signed_congr _ _ _ ?_)
      (compactSkywalkSignRelease_virtual_signed _ hv.2 s)
    intro q hq
    have ha : q ∉ (compactSkywalkSignPoolA w i).released := by
      intro hm
      rw [he.2] at hq
      exact List.disjoint_left.mp hd (hp.1 hm) hq
    simp [compactSkywalkStageVirtual,CompactSkywalkSignReleaseLayout.reconstructed,ha]

/-- Mathematical reconstruction followed by ghost release is exactly the
physical state. This equivalence emits no expansion in the compact circuit. -/
theorem compactSkywalkStage_release_virtual (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (hcA : (compactSkywalkSignPoolA w i).Clean s.basis)
    (hcB : (compactSkywalkSignPoolB w i).Clean s.basis) :
    run (compactSkywalkSignPoolRelease w i) m
      ⟨s.phase,compactSkywalkStageVirtual w i s.basis⟩ = s := by
  let v : State := ⟨s.phase,compactSkywalkStageVirtual w i s.basis⟩
  let A := compactSkywalkSignPoolA w i
  let B := compactSkywalkSignPoolB w i
  let u := run (compactSkywalkSignRelease A) m v
  let t := run (compactSkywalkSignRelease B) m u
  have hv := compactSkywalkSignPool_valid w i hi hn
  have copies := compactSkywalkStage_virtual_copies w i (by omega) hn s.basis
  have h := compactSkywalkSignPool_release_correct w i hi hn v m copies.1 copies.2
  have ca := compactSkywalkSignRelease_counts A
  have actual : run (compactSkywalkSignPoolRelease w i) m v = t :=
    compactSkywalkSign_no_measure_append _ _ ca.2.1 v m
  rw [actual] at h
  change run (compactSkywalkSignPoolRelease w i) m v = s
  rw [actual]
  apply congrArg₂ State.mk
  · exact h.1
  · funext q
    by_cases ha : q ∈ A.released
    · exact (h.2.1 q ha).trans (hcA q ha).symm
    by_cases hb : q ∈ B.released
    · exact (h.2.2.1 q hb).trans (hcB q hb).symm
    have a := (compactSkywalkSignRelease_phase_frame A hv.1 v m).2.1 q ha
    have b := (compactSkywalkSignRelease_phase_frame B hv.2 u m).2.1 q hb
    exact (b.trans a).trans (compactSkywalkStage_virtual_outside w i s.basis q ha hb)

/-- Every local tick input is obtained from the compact-stage predicate by
verified ghost release. No extra clean extension or work oracle is introduced. -/
theorem compactSkywalkStage_local_input (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (hi : i < 512) (s : State)
    (hin : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    SkywalkIntegerInput (compactSkywalkTickLayout w i) r.a r.b r.g s.basis := by
  have entry := compactSkywalkTickEntry_from_stage w hn x p i hp0 hx0 hpo hp hx hc hi
    ⟨s.phase,compactSkywalkStageVirtual w i s.basis⟩ [] hin.1
  have eq := compactSkywalkStage_release_virtual w i hi hn s [] hin.2.1 hin.2.2
  rw [eq] at entry
  exact entry.2

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageFrame.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem block_away (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start len j : Nat) (hb : start+len ≤ 1798) (hj : j < 1798)
    (ha : j < start ∨ start+len ≤ j) : w j ∉ wireBlock w start len := by
  intro hm
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hm
  simp only [List.mem_range'_1] at hk
  have e := skywalkPool_index_inj w hn k j (by omega) hj he
  omega

/-- Raw tape, future extension sites and the complete carry bank are not
changed by mathematical sign reconstruction. -/
theorem compactSkywalkStage_virtual_index (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (s : BasisState) (j : Nat) (hj : j < 1798)
    (ha : j < i ∨ i+258 ≤ j) (hb : j < 770 ∨ 1028 ≤ j) :
    compactSkywalkStageVirtual w i s (w j) = s (w j) := by
  have ea := compactSkywalkStage_expanded w i hi
  apply compactSkywalkStage_virtual_outside
  · intro hm
    have hw : w j ∈ skywalkPoolA w i := by rw [←ea.1]; exact List.mem_append_right _ hm
    exact block_away w hn i 258 j (by omega) hj ha hw
  · intro hm
    have hw : w j ∈ skywalkPoolB w := by rw [←ea.2]; exact List.mem_append_right _ hm
    exact block_away w hn 770 258 j (by decide) hj hb hw

/-- An index interval exclusion checks the actual local native/cleanup support. -/
theorem compactSkywalkStage_tick_away (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj : j < 1798)
    (hp : j ≠ skywalkPoolPreviousId i) (hh : j ≠ 1028+i)
    (he : j ≠ i+compactSkywalkTickPreWidth i) (hi0 : j ≠ i) (hb0 : j ≠ 770)
    (ha : j < i+1 ∨ i+compactSkywalkTickPreWidth i ≤ j)
    (hb : j < 771 ∨ 770+compactSkywalkTickPreWidth i ≤ j)
    (hc : j < 1540 ∨ 1540+(compactSkywalkTickPreWidth i-1) ≤ j) :
    w j ∉ (compactSkywalkTickLayout w i).wires := by
  have width := compactSkywalkTick_width_bounds i hi
  have distinct (k : Nat) (hk : k < 1798) (hne : j ≠ k) : w j ≠ w k := by
    intro e
    exact hne (skywalkPool_index_inj w hn j k hj hk e)
  have pa := distinct _ (by unfold skywalkPoolPreviousId; split_ifs <;> omega) hp
  have ph := distinct _ (by omega) hh
  have pe := distinct _ (by omega) he
  have pi := distinct _ (by omega) hi0
  have pb := distinct _ (by decide) hb0
  have aa := block_away w hn (i+1) (compactSkywalkTickPreWidth i-1) j (by omega) hj (by omega)
  have ab := block_away w hn 771 (compactSkywalkTickPreWidth i-1) j (by omega) hj (by omega)
  have ac := block_away w hn 1540 (compactSkywalkTickPreWidth i-1) j (by omega) hj hc
  simp only [SkywalkIntegerLayout.wires,compactSkywalkTick_ah w i hi,
    compactSkywalkTick_bh w i hi,List.mem_cons,List.mem_append]
  simp only [compactSkywalkTickLayout]
  tauto

theorem compactSkywalkStage_tick_keep (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj : j < 1798)
    (hp : j ≠ skywalkPoolPreviousId i) (hh : j ≠ 1028+i)
    (he : j ≠ i+compactSkywalkTickPreWidth i) (hi0 : j ≠ i) (hb0 : j ≠ 770)
    (ha : j < i+1 ∨ i+compactSkywalkTickPreWidth i ≤ j)
    (hb : j < 771 ∨ 770+compactSkywalkTickPreWidth i ≤ j)
    (hc : j < 1540 ∨ 1540+(compactSkywalkTickPreWidth i-1) ≤ j)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) :=
  compactSkywalkTickOutput_frame w i hi hn s m _
    (compactSkywalkStage_tick_away w i hi hn j hj hp hh he hi0 hb0 ha hb hc)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageFields.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Physical form of the compact invariant. Only the current signed reads
are shortened; all stored controls and fresh/work bits remain explicit. -/
def CompactSkywalkStageFields (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (s : BasisState) : Prop :=
  let ri := SkywalkTrace.next^[i] r
  signedRegValue (compactSkywalkSignPoolA w i).retained s=ri.a ∧
  signedRegValue (compactSkywalkSignPoolB w i).retained s=ri.b ∧
  s (w (skywalkPoolPreviousId i))=ri.g ∧
  (∀j,j < i → s (w j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 ∧
    s (w (1028+j))=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).2) ∧
  (∀j,i ≤ j → j < 512 → s (w (j+258))=false ∧ s (w (1028+j))=false) ∧
  regValue (wireBlock w 1540 257) s=0 ∧ s (w 1797)=false ∧
  (compactSkywalkSignPoolA w i).Clean s ∧ (compactSkywalkSignPoolB w i).Clean s

private theorem metadata_reads (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (hi : i ≤ 512) (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    SkywalkIntegerStage w r i (compactSkywalkStageVirtual w i s) ↔
      signedRegValue (compactSkywalkSignPoolA w i).retained s=(SkywalkTrace.next^[i] r).a ∧
      signedRegValue (compactSkywalkSignPoolB w i).retained s=(SkywalkTrace.next^[i] r).b ∧
      s (w (skywalkPoolPreviousId i))=(SkywalkTrace.next^[i] r).g ∧
      (∀j,j < i → s (w j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 ∧
        s (w (1028+j))=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).2) ∧
      (∀j,i ≤ j → j < 512 → s (w (j+258))=false ∧ s (w (1028+j))=false) ∧
      regValue (wireBlock w 1540 257) s=0 ∧ s (w 1797)=false := by
  have values := compactSkywalkStage_virtual_values w i hi hn s
  have keep (j : Nat) (hj : j < 1798) (ha : j < i ∨ i+258 ≤ j)
      (hb : j < 770 ∨ 1028 ≤ j) := compactSkywalkStage_virtual_index w i hi hn s j hj ha hb
  have prev := keep (skywalkPoolPreviousId i) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega)
  have initial := keep 1797 (by omega) (by omega) (by omega)
  have carry : regValue (wireBlock w 1540 257) (compactSkywalkStageVirtual w i s)=
      regValue (wireBlock w 1540 257) s := by
    apply regValue_congr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact keep j (by omega) (by omega) (by omega)
  have oldG (j : Nat) (hj : j < i) := keep j (by omega) (by omega) (by omega)
  have oldS (j : Nat) (hj : j < i) := keep (1028+j) (by omega) (by omega) (by omega)
  have freshE (j : Nat) (hj : i ≤ j) (h512 : j < 512) :=
    keep (j+258) (by omega) (by omega) (by omega)
  have freshS (j : Nat) (hj : i ≤ j) (h512 : j < 512) :=
    keep (1028+j) (by omega) (by omega) (by omega)
  unfold SkywalkIntegerStage
  rw [values.1,values.2,prev,carry,initial]
  constructor
  · intro h
    refine ⟨h.1,h.2.1,h.2.2.1,?_,?_,h.2.2.2.2.2⟩
    · intro j hj
      have t := h.2.2.2.1 j hj
      simpa only [oldG j hj,oldS j hj] using t
    · intro j hj hk
      have t := h.2.2.2.2.1 j hj hk
      simpa only [freshE j hj hk,freshS j hj hk] using t
  · intro h
    refine ⟨h.1,h.2.1,h.2.2.1,?_,?_,h.2.2.2.2.2⟩
    · intro j hj
      rw [oldG j hj,oldS j hj]
      exact h.2.2.2.1 j hj
    · intro j hj hk
      rw [freshE j hj hk,freshS j hj hk]
      exact h.2.2.2.2.1 j hj hk

/-- Equivalence introduces no predicate about unseen high qubits. The
mathematical virtual view is exactly the physical prefix/clean-tail assertion. -/
theorem compactSkywalkStage_fields_iff (w : Nat → Wire) (r : SkywalkRails.State)
    (i : Nat) (hi : i ≤ 512) (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    CompactSkywalkStage w r i s ↔ CompactSkywalkStageFields w r i s := by
  unfold CompactSkywalkStage CompactSkywalkStageFields
  rw [metadata_reads w r i hi hn s]
  constructor
  · rintro ⟨⟨ha,hb,hg,hpast,hfuture,hcarry,horient⟩,hcleanA,hcleanB⟩
    exact ⟨ha,hb,hg,hpast,hfuture,hcarry,horient,hcleanA,hcleanB⟩
  · rintro ⟨ha,hb,hg,hpast,hfuture,hcarry,horient,hcleanA,hcleanB⟩
    exact ⟨⟨ha,hb,hg,hpast,hfuture,hcarry,horient⟩,hcleanA,hcleanB⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageMetadata.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Past G records strictly before the predecessor site lie outside the
actual native and cleanup instruction support. -/
theorem compactSkywalkStageMetadata_pastG (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj : j+1 < i)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : j ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn j (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

theorem compactSkywalkStageMetadata_pastS (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj : j < i)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w (1028+j)) = s.basis (w (1028+j)) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : 1028+j ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn (1028+j) (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

/-- Future extensions of the original full-width words remain untouched;
the compact physical A prefix ends no later than site 514. -/
theorem compactSkywalkStageMetadata_futureExtension (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj0 : i+1 ≤ j) (hj : j < 512)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w (j+258)) = s.basis (w (j+258)) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : j+258 ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn (j+258) (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

theorem compactSkywalkStageMetadata_futureS (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj0 : i+1 ≤ j) (hj : j < 512)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w (1028+j)) = s.basis (w (1028+j)) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : 1028+j ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn (1028+j) (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

/-- The unused suffix of the original carry bank is a frame, with no
cleanliness premise on those untouched bits. -/
theorem compactSkywalkStageMetadata_carryTail (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat)
    (hj0 : 1540+(compactSkywalkTickPreWidth i-1) ≤ j) (hj : j < 1797)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : j ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn j (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

theorem compactSkywalkStageMetadata_orientation (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (hi0 : 0 < i) (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w 1797) = s.basis (w 1797) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : 1797 ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn 1797 (by decide) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

/-- The predecessor is preserved by the native output contract, including
the special initial orientation site. -/
theorem compactSkywalkStageMetadata_previous (w : Nat → Wire) (i : Nat)
    (A B : Int) (G : Bool) (before out : BasisState)
    (hin : SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G before)
    (hout : CompactSkywalkTickOutput w i A B G out) :
    out (w (skywalkPoolPreviousId i)) = before (w (skywalkPoolPreviousId i)) :=
  hout.2.2.2.2.1.trans hin.2.2.1.symm

theorem compactSkywalkStageMetadata_previousG (w : Nat → Wire) (i : Nat) (hi0 : 0 < i)
    (A B : Int) (G : Bool) (before out : BasisState)
    (hin : SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G before)
    (hout : CompactSkywalkTickOutput w i A B G out) :
    out (w (i-1)) = before (w (i-1)) := by
  have h := compactSkywalkStageMetadata_previous w i A B G before out hin hout
  simpa only [skywalkPoolPreviousId,if_neg (by omega : i ≠ 0)] using h

theorem compactSkywalkStageMetadata_orientation_zero (w : Nat → Wire)
    (A B : Int) (G : Bool) (before out : BasisState)
    (hin : SkywalkIntegerInput (compactSkywalkTickLayout w 0) A B G before)
    (hout : CompactSkywalkTickOutput w 0 A B G out) :
    out (w 1797) = before (w 1797) := by
  simpa only [skywalkPoolPreviousId,if_pos rfl] using
    (compactSkywalkStageMetadata_previous w 0 A B G before out hin hout)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageStepGeometry.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem blockPrefix (w : Nat → Wire) (start len n : Nat) (hn : n ≤ len) :
    (wireBlock w start len).take n = wireBlock w start n := by
  have h := wireBlock_append w start n (len-n)
  rw [show n+(len-n) = len by omega] at h
  rw [←h]
  have ht : (wireBlock w start n++wireBlock w (start+n) (len-n)).take
    (wireBlock w start n).length = wireBlock w start n := List.take_left
  simpa only [wireBlock_length] using ht

private theorem blockDrop (w : Nat → Wire) (start len n : Nat) (hn : n ≤ len) :
    (wireBlock w start len).drop n = wireBlock w (start+n) (len-n) := by
  have h := wireBlock_append w start n (len-n)
  rw [show n+(len-n) = len by omega] at h
  rw [←h]
  have ht : (wireBlock w start n++wireBlock w (start+n) (len-n)).drop
    (wireBlock w start n).length = wireBlock w (start+n) (len-n) := List.drop_left
  simpa only [wireBlock_length] using ht

/-- Next retained words are precisely the physically computed output prefixes. -/
theorem compactSkywalkStageStep_retained (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkSignPoolA w (i+1)).retained = (compactSkywalkTickARelease w i).retained ∧
    (compactSkywalkSignPoolB w (i+1)).retained = (compactSkywalkTickBRelease w i).retained := by
  have h := compactSkywalkTick_width_bounds i hi
  have a := compactSkywalkStage_width (i+1) (by omega)
  have e : narrowSkywalkRouteWidth (i+1) = compactSkywalkTickPostWidth i := h.2.2.2.2.2.symm
  have pos : 0 < compactSkywalkTickPostWidth i := by omega
  have nextA := compactSkywalkSignWord_retained (skywalkPoolA w (i+1))
    (narrowSkywalkRouteWidth (i+1)) (by omega) (by simpa only [skywalkPoolA,wireBlock_length] using a.2)
  have nextB := compactSkywalkSignWord_retained (skywalkPoolB w)
    (narrowSkywalkRouteWidth (i+1)) (by omega) (by simpa only [skywalkPoolB,wireBlock_length] using a.2)
  have curA := compactSkywalkSignWord_retained (compactSkywalkTickLayout w i).half
    (compactSkywalkTickPostWidth i) pos (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)
  have curB := compactSkywalkSignWord_retained (compactSkywalkTickLayout w i).b
    (compactSkywalkTickPostWidth i) pos (by
      rw [compactSkywalkTick_b w i hi,wireBlock_length]; exact h.2.2.1)
  constructor
  · change (compactSkywalkSignWord _ _).retained = (compactSkywalkSignWord _ _).retained
    rw [nextA,curA,e,compactSkywalkTick_half w i hi,skywalkPoolA]
    rw [blockPrefix w (i+1) 258 _ (by omega),blockPrefix w (i+1) _ _ h.2.2.1]
  · change (compactSkywalkSignWord _ _).retained = (compactSkywalkSignWord _ _).retained
    rw [nextB,curB,e,compactSkywalkTick_b w i hi,skywalkPoolB]
    rw [blockPrefix w 770 258 _ (by omega),blockPrefix w 770 _ _ h.2.2.1]

/-- Current cleanup tails and next full-word tails are concrete intervals. -/
theorem compactSkywalkStageStep_tail_views (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickARelease w i).released =
      wireBlock w (i+1+compactSkywalkTickPostWidth i)
        (compactSkywalkTickPreWidth i-compactSkywalkTickPostWidth i) ∧
    (compactSkywalkTickBRelease w i).released =
      wireBlock w (770+compactSkywalkTickPostWidth i)
        (compactSkywalkTickPreWidth i-compactSkywalkTickPostWidth i) ∧
    (compactSkywalkSignPoolA w (i+1)).released =
      wireBlock w (i+1+compactSkywalkTickPostWidth i) (258-compactSkywalkTickPostWidth i) ∧
    (compactSkywalkSignPoolB w (i+1)).released =
      wireBlock w (770+compactSkywalkTickPostWidth i) (258-compactSkywalkTickPostWidth i) ∧
    (compactSkywalkSignPoolA w i).released =
      wireBlock w (i+compactSkywalkTickPreWidth i) (258-compactSkywalkTickPreWidth i) ∧
    (compactSkywalkSignPoolB w i).released =
      wireBlock w (770+compactSkywalkTickPreWidth i) (258-compactSkywalkTickPreWidth i) := by
  have h := compactSkywalkTick_width_bounds i hi
  have e : narrowSkywalkRouteWidth (i+1) = compactSkywalkTickPostWidth i := h.2.2.2.2.2.symm
  simp only [compactSkywalkTickARelease,compactSkywalkTickBRelease,compactSkywalkSignPoolA,
    compactSkywalkSignPoolB,compactSkywalkSignWord,compactSkywalkTick_half w i hi,
    compactSkywalkTick_b w i hi,skywalkPoolA,skywalkPoolB,e]
  change (wireBlock w (i+1) (compactSkywalkTickPreWidth i)).drop (compactSkywalkTickPostWidth i) = _ ∧
    (wireBlock w 770 (compactSkywalkTickPreWidth i)).drop (compactSkywalkTickPostWidth i) = _ ∧
    (wireBlock w (i+1) 258).drop (compactSkywalkTickPostWidth i) = _ ∧
    (wireBlock w 770 258).drop (compactSkywalkTickPostWidth i) = _ ∧
    (wireBlock w i 258).drop (compactSkywalkTickPreWidth i) = _ ∧
    (wireBlock w 770 258).drop (compactSkywalkTickPreWidth i) = _
  exact ⟨blockDrop _ _ _ _ h.2.2.1,blockDrop _ _ _ _ h.2.2.1,
    blockDrop _ _ _ _ (by omega),blockDrop _ _ _ _ (by omega),
    blockDrop _ _ _ _ h.2.2.2.1,blockDrop _ _ _ _ h.2.2.2.1⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageStepTails.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Both next full-word tails are clean: the native local tail is cleared by
actual CX, the previously omitted suffix is a frame, and A's new last site is fresh. -/
theorem compactSkywalkStageStep_clean_tails (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (r : SkywalkRails.State) (s : State) (m : List Bool)
    (hin : CompactSkywalkStageFields w r i s.basis) (A B : Int) (G : Bool)
    (hout : CompactSkywalkTickOutput w i A B G (run (compactSkywalkTick w i) m s).basis) :
    (compactSkywalkSignPoolA w (i+1)).Clean (run (compactSkywalkTick w i) m s).basis ∧
    (compactSkywalkSignPoolB w (i+1)).Clean (run (compactSkywalkTick w i) m s).basis := by
  rcases hin with ⟨ha,hb,hprev,hpast,hfuture,hcarry,horient,oldA,oldB⟩
  have width := compactSkywalkTick_width_bounds i hi
  have tv := compactSkywalkStageStep_tail_views w i hi
  have nowA := hout.2.2.2.2.2.2.1
  have nowB := hout.2.2.2.2.2.2.2
  have keepA (j : Nat) (hj0 : i+compactSkywalkTickPreWidth i+1 ≤ j) (hj1 : j ≤ i+258) :
      (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) := by
    have hp : j ≠ skywalkPoolPreviousId i := by
      unfold skywalkPoolPreviousId; split_ifs <;> omega
    exact compactSkywalkStage_tick_keep w i hi hn j (by omega) hp
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) s m
  have keepB (j : Nat) (hj0 : 770+compactSkywalkTickPreWidth i ≤ j) (hj1 : j < 1028) :
      (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) := by
    have hp : j ≠ skywalkPoolPreviousId i := by
      unfold skywalkPoolPreviousId; split_ifs <;> omega
    exact compactSkywalkStage_tick_keep w i hi hn j (by omega) hp
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) s m
  constructor
  · intro q hq
    rw [tv.2.2.1] at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    by_cases current : j < i+1+compactSkywalkTickPreWidth i
    · apply nowA
      rw [tv.1]
      apply List.mem_map.mpr
      exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩
    · rw [keepA j (by omega) (by omega)]
      by_cases last : j = i+258
      · subst j
        exact (hfuture i (Nat.le_refl i) hi).1
      · apply oldA
        rw [tv.2.2.2.2.1]
        apply List.mem_map.mpr
        exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩
  · intro q hq
    rw [tv.2.2.2.1] at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    by_cases current : j < 770+compactSkywalkTickPreWidth i
    · apply nowB
      rw [tv.2.1]
      apply List.mem_map.mpr
      exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩
    · rw [keepB j (by omega) (by omega)]
      apply oldB
      rw [tv.2.2.2.2.2]
      apply List.mem_map.mpr
      exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageStepProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Actual compact physical stage advancement. Every old tape/work/fresh
field is transported, while both next full-word tails are proved clean. -/
theorem compactSkywalkStageStep (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hi : i < 512) :
    Triple (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i)
      (compactSkywalkTick w i)
      (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) (i+1)) := by
  intro s m hin
  let r := SkywalkRails.encode false false (x:Int) (p:Int)
  let ri := SkywalkTrace.next^[i] r
  let t := SkywalkRails.step ri
  let out := run (compactSkywalkTick w i) m s
  have fields := (compactSkywalkStage_fields_iff w r i (by omega) hn s.basis).mp hin
  rcases fields with ⟨readA,readB,prev,past,future,carry,orient,cleanA,cleanB⟩
  have input := compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hx hc hi s hin
  have fit := narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp hx hc hi
  have result := compactSkywalkTickOutput_spec w i hi hn ri.a ri.b ri.g
    fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s m input
  have ho : CompactSkywalkTickOutput w i ri.a ri.b ri.g out.basis := result.2
  have tails := compactSkywalkStageStep_clean_tails w i hi hn r s m
    ⟨readA,readB,prev,past,future,carry,orient,cleanA,cleanB⟩ ri.a ri.b ri.g ho
  have views := compactSkywalkStageStep_retained w i hi
  have hnext : SkywalkTrace.next^[i+1] r = SkywalkRails.railsOf t := by
    rw [Function.iterate_succ_apply']
    rfl
  refine ⟨result.1,(compactSkywalkStage_fields_iff w r (i+1) (by omega) hn out.basis).mpr ?_⟩
  change CompactSkywalkStageFields w r (i+1) out.basis
  unfold CompactSkywalkStageFields
  rw [hnext]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,tails.1,tails.2⟩
  · rw [views.1]
    exact ho.1
  · rw [views.2]
    exact ho.2.1
  · change out.basis (w (skywalkPoolPreviousId (i+1))) = t.g
    rw [skywalkPoolPreviousId,if_neg (by omega : i+1 ≠ 0)]
    simpa only [Nat.add_sub_cancel] using ho.2.2.1
  · intro j hj
    by_cases now : j = i
    · subst j
      exact ⟨ho.2.2.1,ho.2.2.2.1⟩
    · have old : j < i := by omega
      have history := past j old
      have keepG : out.basis (w j) = s.basis (w j) := by
        by_cases last : j+1 = i
        · have hkeep := compactSkywalkStageMetadata_previousG w i (by omega)
            ri.a ri.b ri.g s.basis out.basis input ho
          have he : i-1 = j := by omega
          simpa only [he] using hkeep
        · exact compactSkywalkStageMetadata_pastG w i hi hn j (by omega) s m
      have keepS := compactSkywalkStageMetadata_pastS w i hi hn j old s m
      exact ⟨keepG.trans history.1,keepS.trans history.2⟩
  · intro j hj hj512
    have before := future j (by omega) hj512
    exact ⟨(compactSkywalkStageMetadata_futureExtension w i hi hn j hj hj512 s m).trans before.1,
      (compactSkywalkStageMetadata_futureS w i hi hn j hj hj512 s m).trans before.2⟩
  · apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    by_cases used : j < 1540+(compactSkywalkTickPreWidth i-1)
    · have carryClean := (regValue_zero _ _).mp ho.2.2.2.2.2.1
      apply carryClean
      change w j ∈ wireBlock w 1540 (compactSkywalkTickPreWidth i-1)
      exact List.mem_map.mpr ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩
    · have keep := compactSkywalkStageMetadata_carryTail w i hi hn j (by omega) (by omega) s m
      apply keep.trans
      exact (regValue_zero _ _).mp carry (w j)
        (List.mem_map.mpr ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩)
  · by_cases zero : i = 0
    · subst i
      exact (compactSkywalkStageMetadata_orientation_zero w ri.a ri.b ri.g
        s.basis out.basis input ho).trans orient
    · exact (compactSkywalkStageMetadata_orientation w i hi hn (by omega) s m).trans orient

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkForward.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Actual forward compact ticks only; no high-word reconstruction or reverse
measurement instruction is inserted between physical compact boundaries. -/
def compactSkywalkForward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compactSkywalkTick w i++compactSkywalkForward w (i+1) n

attribute [local irreducible] compactSkywalkTick

/-- Exact stage induction includes phase, raw history, future zero sites,
full clean carry, initial orientation, and both omitted physical tails. -/
theorem compactSkywalkForward_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hsteps : i+n ≤ 512) :
    Triple (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i)
      (compactSkywalkForward w i n)
      (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) (i+n)) := by
  induction n generalizing i with
  | zero =>
    intro s m hin
    exact ⟨rfl,hin⟩
  | succ n ih =>
    have first := compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hx hc (by omega)
    have rest := ih (i+1) (by omega)
    simpa only [compactSkywalkForward,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using first.seq rest

/-- The existing seed-stage input starts the full512 compact campaign directly. -/
theorem compactSkywalkForward_512 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) :
    Triple (SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0)
      (compactSkywalkForward w 0 512)
      (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512) := by
  intro s m hin
  exact compactSkywalkForward_spec w hn x p 0 512 hp0 hx0 hpo hp hx hc (by decide) s m
    ((compactSkywalkStage_zero_iff w _ s.basis).mpr hin)

/-- Pure arithmetic charge recurrences mirror actual per-tick resources. -/
def compactSkywalkForwardT (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1)+
      compactSkywalkForwardT (i+1) n

def compactSkywalkForwardM (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (compactSkywalkTickPostWidth i-1)+compactSkywalkForwardM (i+1) n

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkForwardFrame.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] compactSkywalkTick

/-- Every actual forward tick remains inside the original integer pool.
This support ceiling is not a compact whole-point allocation certificate. -/
theorem compactSkywalkForward_support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    wires (compactSkywalkForward w i n) ⊆ (skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [compactSkywalkForward,wires]
  | succ n ih =>
    have hi : i < 512 := by omega
    have ht := compactSkywalkTick_support w i hi hn
    have hl := compactSkywalkTick_local_support w i hi
    have first : wires (compactSkywalkTick w i) ⊆ (skywalkPoolWires w).toFinset := by
      intro q hq
      exact List.mem_toFinset.mpr (hl (List.mem_toFinset.mp (ht hq)))
    rw [compactSkywalkForward,wires_append,Finset.union_subset_iff]
    exact ⟨first,ih (i+1) (by omega)⟩

/-- All caller wires outside the integer pool are preserved for arbitrary
input basis/phase and arbitrary complete measurement streams. -/
theorem compactSkywalkForward_frame (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ skywalkPoolWires w) :
    (run (compactSkywalkForward w i n) m s).basis q = s.basis q :=
  run_preserves_outside _ m s q (fun h => hq
    (List.mem_toFinset.mp (compactSkywalkForward_support w hn i n hsteps h)))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkReverseProgram.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Expand only the tails removed at the previous local tick. Their lengths
are preN-postN (zero or one), not258-postN. -/
def compactSkywalkReverseExpand (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkSignExpand (compactSkywalkTickBRelease w i)++
    compactSkywalkSignExpand (compactSkywalkTickARelease w i)

/-- Fresh independently measured signed unrecord, then local half/route
reversal. No forward measurement instruction is reversed. -/
def compactSkywalkReverseTick (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkReverseExpand w i++
    narrowSkywalkUntick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)

attribute [local irreducible] narrowSkywalkTick narrowSkywalkUntick
attribute [local irreducible] compactSkywalkSignRelease compactSkywalkSignExpand

theorem compactSkywalkReverseExpand_counts (w : Nat → Wire) (i : Nat) :
    toffoliCount (compactSkywalkReverseExpand w i) = 0 ∧
    measurementCount (compactSkywalkReverseExpand w i) = 0 := by
  have a := compactSkywalkSignRelease_counts (compactSkywalkTickARelease w i)
  have b := compactSkywalkSignRelease_counts (compactSkywalkTickBRelease w i)
  rw [compactSkywalkReverseExpand,toffoliCount_append,measurementCount_append,
    b.2.2.1,b.2.2.2,a.2.2.1,a.2.2.2]
  exact ⟨rfl,rfl⟩

/-- Local-tail expansion exactly cancels actual compact cleanup, with
independent record lists and arbitrary initial data in both local tails. -/
theorem compactSkywalkReverseExpand_cleanup (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m1 m2 : List Bool) :
    run (compactSkywalkReverseExpand w i) m2
      (run (compactSkywalkTickCleanup w i) m1 s) = s := by
  let A := compactSkywalkTickARelease w i
  let B := compactSkywalkTickBRelease w i
  have hv := compactSkywalkTick_release_valid w i hi hn
  have ca := compactSkywalkSignRelease_counts A
  have cb := compactSkywalkSignRelease_counts B
  change run (compactSkywalkSignExpand B++compactSkywalkSignExpand A) m2
    (run (compactSkywalkSignRelease A++compactSkywalkSignRelease B) m1 s) = s
  rw [compactSkywalkSign_no_measure_append _ _ ca.2.1,
    compactSkywalkSign_no_measure_append _ _ cb.2.2.2]
  rw [(compactSkywalkSignRelease_roundtrip B hv.2
    (run (compactSkywalkSignRelease A) m1 s) m1 m2).1]
  exact (compactSkywalkSignRelease_roundtrip A hv.1 s m1 m2).1

/-- Exact complete State inverse of the actual compact tick. Only its fresh
history and clean local carry are needed; measurement lists are independent. -/
theorem compactSkywalkReverseTick_roundtrip (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m1 m2 : List Bool)
    (hh : s.basis (compactSkywalkTickLayout w i).history = false)
    (hc : regValue (compactSkywalkTickLayout w i).carry s.basis = 0) :
    run (compactSkywalkReverseTick w i) m2 (run (compactSkywalkTick w i) m1 s) = s := by
  have hz := (compactSkywalkReverseExpand_counts w i).2
  have hr := compactSkywalkTickOutput_run w i s m1
  rw [hr,compactSkywalkReverseTick,compactSkywalkSign_no_measure_append _ _ hz]
  rw [compactSkywalkReverseExpand_cleanup w i hi hn _ m1 m2]
  have width := compactSkywalkTick_width_bounds i hi
  exact narrowSkywalkTick_roundtrip _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1) s m1 m2 hh hc

theorem compactSkywalkReverseTick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (compactSkywalkReverseTick w i) =
      (compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1) ∧
    measurementCount (compactSkywalkReverseTick w i) = compactSkywalkTickPostWidth i-1 := by
  have width := compactSkywalkTick_width_bounds i hi
  have c := narrowSkywalkTick_counts _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1)
  have z := compactSkywalkReverseExpand_counts w i
  rw [compactSkywalkReverseTick,toffoliCount_append,measurementCount_append,
    z.1,z.2,c.2.2.1,c.2.2.2,compactSkywalkTick_ah w i hi,wireBlock_length]
  exact ⟨by omega,by omega⟩

theorem compactSkywalkReverseExpand_support (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    wires (compactSkywalkReverseExpand w i) ⊆ (compactSkywalkTickLayout w i).wires.toFinset := by
  have h := compactSkywalkTick_width_bounds i hi
  have a := (compactSkywalkSignWord_support (compactSkywalkTickLayout w i).half
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)).2
  have b := (compactSkywalkSignWord_support (compactSkywalkTickLayout w i).b
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_b w i hi,wireBlock_length]; exact h.2.2.1)).2
  intro q hq
  simp only [compactSkywalkReverseExpand,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have hb := List.mem_toFinset.mp (b hq)
    simp only [SkywalkIntegerLayout.b,SkywalkIntegerLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons] at hb ⊢
    tauto
  · have ha := List.mem_toFinset.mp (a hq)
    simp only [SkywalkIntegerLayout.half,SkywalkIntegerLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
    tauto

theorem compactSkywalkReverseTick_support (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    wires (compactSkywalkReverseTick w i) ⊆ (compactSkywalkTickLayout w i).wires.toFinset := by
  have h := compactSkywalkTick_width_bounds i hi
  have n := (narrowSkywalkTick_wires_subset _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)).2
  rw [compactSkywalkReverseTick,wires_append,Finset.union_subset_iff]
  exact ⟨compactSkywalkReverseExpand_support w i hi,n⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkReverseLoop.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Walk back the actual compact ticks, with independent inverse measurements
and local sign expansion only at the immediately preceding width. -/
def compactSkywalkReverse (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compactSkywalkReverse w (i+1) n++compactSkywalkReverseTick w i

attribute [local irreducible] compactSkywalkTick compactSkywalkReverseTick

/-- Complete physical State restoration on every valid compact forward path.
No arbitrary-poststate reachability premise or reused measurement stream is assumed. -/
theorem compactSkywalkReverse_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hsteps : i+n ≤ 512)
    (s : State) (m1 m2 : List Bool)
    (hin : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (compactSkywalkReverse w i n) m2 (run (compactSkywalkForward w i n) m1 s) = s := by
  induction n generalizing i s m1 m2 with
  | zero => rfl
  | succ n ih =>
    have hi : i < 512 := by omega
    let tick := compactSkywalkTick w i
    simp only [compactSkywalkForward,compactSkywalkReverse]
    rw [run_append,run_append]
    generalize htick : run tick (m1.take (measurementCount tick)) s = t
    have hs := compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hx hc hi
      s (m1.take (measurementCount tick)) hin
    rw [htick] at hs
    have htail := ih (i+1) (by omega) t (m1.drop (measurementCount tick))
      (m2.take (measurementCount (compactSkywalkReverse w (i+1) n))) hs.2
    have localInput := compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hx hc hi s hin
    have restore := compactSkywalkReverseTick_roundtrip w i hi hn s
      (m1.take (measurementCount tick))
      (m2.drop (measurementCount (compactSkywalkReverse w (i+1) n)))
      localInput.2.2.2.2.1 localInput.2.2.2.2.2
    rw [htick] at restore
    rw [htail]
    exact restore

theorem compactSkywalkReverse_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    toffoliCount (compactSkywalkReverse w i n) = compactSkywalkForwardT i n ∧
    measurementCount (compactSkywalkReverse w i n) = compactSkywalkForwardM i n := by
  induction n generalizing i with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have first := compactSkywalkReverseTick_counts w i (by omega) hn
    have rest := ih (i+1) (by omega)
    rw [compactSkywalkReverse,toffoliCount_append,measurementCount_append,
      first.1,first.2,rest.1,rest.2]
    change compactSkywalkForwardT (i+1) n+
      ((compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1)) =
        (compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1)+
          compactSkywalkForwardT (i+1) n ∧
      compactSkywalkForwardM (i+1) n+(compactSkywalkTickPostWidth i-1) =
        (compactSkywalkTickPostWidth i-1)+compactSkywalkForwardM (i+1) n
    exact ⟨Nat.add_comm _ _,Nat.add_comm _ _⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkReverseFrame.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] compactSkywalkReverseTick

/-- Independently emitted reverse instructions touch only the integer pool. -/
theorem compactSkywalkReverse_support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    wires (compactSkywalkReverse w i n) ⊆ (skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [compactSkywalkReverse,wires]
  | succ n ih =>
    have hi : i < 512 := by omega
    have hs := compactSkywalkReverseTick_support w i hi hn
    have hl := compactSkywalkTick_local_support w i hi
    have tick : wires (compactSkywalkReverseTick w i) ⊆ (skywalkPoolWires w).toFinset := by
      intro q hq
      exact List.mem_toFinset.mpr (hl (List.mem_toFinset.mp (hs hq)))
    rw [compactSkywalkReverse,wires_append,Finset.union_subset_iff]
    exact ⟨ih (i+1) (by omega),tick⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkStageTerminal.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Clean physical tails and nonnegative retained rails make reconstruction
literally the original physical basis, for either terminal orientation. -/
theorem compactSkywalkStage_nonnegative_identity (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (r : SkywalkRails.State) (s : BasisState)
    (hin : CompactSkywalkStage w r i s)
    (ha : 0 ≤ (SkywalkTrace.next^[i] r).a) (hb : 0 ≤ (SkywalkTrace.next^[i] r).b) :
    compactSkywalkStageVirtual w i s = s := by
  have values := compactSkywalkStage_virtual_values w i hi hn s
  have va := values.1.symm.trans hin.1.1
  have vb := values.2.symm.trans hin.1.2.1
  have sa := signedRegValue_sign (compactSkywalkSignPoolA w i).low
    (compactSkywalkSignPoolA w i).sign s
  have sb := signedRegValue_sign (compactSkywalkSignPoolB w i).low
    (compactSkywalkSignPoolB w i).sign s
  change s (compactSkywalkSignPoolA w i).sign =
    SkywalkRails.neg (signedRegValue (compactSkywalkSignPoolA w i).retained s) at sa
  change s (compactSkywalkSignPoolB w i).sign =
    SkywalkRails.neg (signedRegValue (compactSkywalkSignPoolB w i).retained s) at sb
  rw [va] at sa
  rw [vb] at sb
  have za : s (compactSkywalkSignPoolA w i).sign = false := by
    simpa only [SkywalkRails.neg,not_lt.mpr ha,decide_false] using sa
  have zb : s (compactSkywalkSignPoolB w i).sign = false := by
    simpa only [SkywalkRails.neg,not_lt.mpr hb,decide_false] using sb
  funext q
  by_cases qa : q ∈ (compactSkywalkSignPoolA w i).released
  · simp only [compactSkywalkStageVirtual,if_pos qa,za,hin.2.1 q qa]
  by_cases qb : q ∈ (compactSkywalkSignPoolB w i).released
  · simp only [compactSkywalkStageVirtual,if_neg qa,if_pos qb,zb,hin.2.2 q qb]
  · exact compactSkywalkStage_virtual_outside w i s q qa qb

/-- Exact termination has unsigned magnitudes (0,1); its orientation G is
arbitrary, hence the signed rails may be (1,0) or (0,1). Both are nonnegative. -/
theorem compactSkywalkStage_terminal_nonnegative (x p : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) :
    0 ≤ (SkywalkTrace.next^[512] (SkywalkRails.encode false false (x:Int) (p:Int))).a ∧
    0 ≤ (SkywalkTrace.next^[512] (SkywalkRails.encode false false (x:Int) (p:Int))).b := by
  have ht := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpo hp (hx.trans hp) hc
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded 512 false false (SkywalkNat.init x p) hp0 hpo
  norm_num only at ht
  simp only [SkywalkNat.init] at he ht
  rw [ht.1,ht.2] at he
  rw [he]
  cases G <;> cases S <;> norm_num [SkywalkRails.encode,SkywalkRails.signed]

/-- The unchanged old terminal caller may consume the physical compact state
at512 directly. No actual high-word expansion is needed. -/
theorem compactSkywalkStage_terminal (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (s : BasisState)
    (hin : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s) :
    compactSkywalkStageVirtual w 512 s = s ∧
    SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s := by
  have pos := compactSkywalkStage_terminal_nonnegative x p hp0 hx0 hpo hp hx hc
  have he := compactSkywalkStage_nonnegative_identity w 512 (by decide) hn _ s hin pos.1 pos.2
  exact ⟨he,by simpa only [he] using hin.1⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkArithmetic.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic
open Secp256k1

attribute [local irreducible] run

private theorem arith_mem (w : Nat → Wire) (start len j : Nat)
    (hlo : start ≤ j) (hhi : j < start+len) : w j∈wireBlock w start len := by
  apply List.mem_map.mpr
  exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩

private theorem arith_block_away (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i start len : Nat) (hi : i < 2314) (hb : start+len ≤ 2314)
    (ha : i < start ∨ start+len ≤ i) : w i∉wireBlock w start len := by
  intro hm
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hm
  simp only [List.mem_range'_1] at hj
  have hh := skywalkShared_index_inj w hn j i (by omega) hi he
  omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DirectSkywalkInput.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ECDSAAdd.Arithmetic.DirectSkywalk
open Secp256k1
attribute [local irreducible] skywalkSeed skywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run

theorem arith_coprime (x : Nat) (hx0 : 0 < x) (hx : x < p) : x.Coprime p := by
  apply Nat.Coprime.symm
  apply p_prime.coprime_iff_not_dvd.mpr
  intro hd
  exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)

theorem arith_modulus_bound : p < 2^256 := by norm_num [p]

theorem arith_mem (w : Nat → Wire) (start len j : Nat)
    (hlo : start ≤ j) (hhi : j < start+len) : w j∈wireBlock w start len := by
  apply List.mem_map.mpr
  exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem arith_block_away (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i start len : Nat) (hi : i < 2314) (hb : start+len ≤ 2314)
    (ha : i < start ∨ start+len ≤ i) : w i∉wireBlock w start len := by
  intro hm
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hm
  simp only [List.mem_range'_1] at hj
  have hh := skywalkShared_index_inj w hn j i (by omega) hi he
  omega

theorem arith_input_bit (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s)
    (i : Nat) (hi : i < 2314) (hx : i < 770 ∨ 1026 ≤ i) (hy : i < 2056 ∨ 2312 ≤ i) :
    s (w i)=false :=
  h.2.2 _ (arith_mem w 0 2314 i (by omega) hi)
    (arith_block_away w hn i 770 256 hi (by omega) hx)
    (arith_block_away w hn i 2056 256 hi (by omega) hy)

theorem arith_input_zero (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y start len : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s)
    (hb : start+len ≤ 2314) (hx : start+len ≤ 770 ∨ 1026 ≤ start)
    (hy : start+len ≤ 2056 ∨ 2312 ≤ start) : regValue (wireBlock w start len) s=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact arith_input_bit w hn x y s h i (by omega) (by omega) (by omega)

theorem arith_seed_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i : Nat) (hi : i < 2314) (ha : 258 ≤ i)
    (hb : i < 770 ∨ 1028 ≤ i) (hc : i < 1798 ∨ 2056 ≤ i)
    (hd : i < 1540 ∨ 1797 ≤ i) (hcin : i≠2313) :
    w i∉(skywalkSharedSeed w).usedWires := by
  have hA := arith_block_away w hn i 0 258 hi (by omega) (by omega)
  have hB := arith_block_away w hn i 770 258 hi (by omega) hb
  have hC := arith_block_away w hn i 1798 258 hi (by omega) hc
  have hD := arith_block_away w hn i 1540 257 hi (by omega) hd
  have hI : w i≠w 2313 := by
    intro he
    exact hcin (skywalkShared_index_inj w hn i 2313 hi (by omega) he)
  intro hm
  change w i∈w 2313::(wireBlock w 0 258++wireBlock w 770 258++
    wireBlock w 1798 258++wireBlock w 1540 257) at hm
  rcases List.mem_cons.mp hm with he|hr
  · exact hI he
  · simp only [List.mem_append,or_assoc] at hr
    rcases hr with he|he|he|he
    · exact hA he
    · exact hB he
    · exact hC he
    · exact hD he

theorem arith_seed_input (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s) :
    SkywalkSeedValues (skywalkSharedSeed w) 0 x 0 s := by
  have hpad := arith_input_zero w hn x y 1026 2 s h (by omega) (by omega) (by omega)
  have hp := wireBlock_append w 770 256 2
  have hb : regValue (wireBlock w 770 258) s=x := by
    rw [←hp,regValue_append]
    change regValue (skywalkArithmeticDivisor w) s+2^256*regValue (wireBlock w 1026 2) s=x
    rw [h.1,hpad]
    omega
  refine ⟨arith_input_zero w hn x y 0 258 s h (by omega) (by omega) (by omega),hb,
    arith_input_zero w hn x y 1798 258 s h (by omega) (by omega) (by omega),
    arith_input_zero w hn x y 1540 257 s h (by omega) (by omega) (by omega),
    arith_input_bit w hn x y s h 2313 (by omega) (by omega) (by omega),
    arith_input_bit w hn x y s h 1797 (by omega) (by omega) (by omega)⟩

set_option exponentiation.threshold 258 in
theorem arith_seed_stage0 (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx : x < p) (s : State) (m : List Bool)
    (h : SkywalkArithmeticInput w x y s.basis) :
    SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 0
      (run (skywalkSeed (skywalkSharedSeed w) p) m s).basis := by
  generalize hs : run (skywalkSeed (skywalkSharedSeed w) p) m s=t
  have hp : p < 2^256 := by norm_num [p]
  have hw := skywalkShared_seed_widths w
  have htFull := skywalkSeed_spec _ 258 p x hw (skywalkShared_seed_nodup w hn)
    (by omega) hp (hx.trans hp) s m (arith_seed_input w hn x y s.basis h)
  rw [hs] at htFull
  have ht := htFull.2
  have hsum : p+x < 2^257 := by
    have hxp0 := hx.trans hp
    change _ < 2^(256+1)
    rw [pow_succ]
    omega
  have hxp : x < 2^257 := by
    have hxp0 := hx.trans hp
    change _ < 2^(256+1)
    rw [pow_succ]
    omega
  have ha : signedRegValue (skywalkPoolA w 0) t.basis=(x:Int)+(p:Int) := by
    change signedDecode 258 (regValue (skywalkSharedSeed w).a t.basis)=_
    rw [ht.a]
    simp only [signedDecode,if_pos hsum]
    omega
  have hb : signedRegValue (skywalkPoolB w) t.basis=(x:Int) := by
    change signedDecode 258 (regValue (skywalkSharedSeed w).b t.basis)=_
    rw [ht.b]
    simp only [signedDecode,if_pos hxp]
  unfold SkywalkIntegerStage
  rw [Function.iterate_zero_apply]
  change signedRegValue (skywalkPoolA w 0) t.basis=(x:Int)+(p:Int) ∧
    signedRegValue (skywalkPoolB w) t.basis=(x:Int) ∧ t.basis (w 1797)=false ∧ _
  refine ⟨ha,hb,ht.orientation,?_,?_,ht.carry,ht.orientation⟩
  · intro j hj; omega
  · intro j hj hjmax
    have keep (i : Nat) (hi : i=j+258 ∨ i=1028+j) :
        t.basis (w i)=false := by
      have hout := arith_seed_outside w hn i (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      have hk := (skywalkSeed_frame _ 258 p hw s m _ hout).1
      rw [hs] at hk
      exact hk.trans (arith_input_bit w hn x y s.basis h i (by omega) (by omega) (by omega))
    exact ⟨keep _ (Or.inl rfl),keep _ (Or.inr rfl)⟩

attribute [local irreducible] SkywalkTrace.next Nat.iterate

theorem arith_trace_map (n : Nat) (r : SkywalkRails.State) :
    SkywalkTrace.trace n r=(List.range n).map
      (fun i => SkywalkTrace.code (SkywalkTrace.next^[i] r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [SkywalkTrace.trace,ih,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.iterate_zero_apply]
    congr 1
    apply List.map_congr_left
    intro i hi
    change SkywalkTrace.code (SkywalkTrace.next^[i] (SkywalkTrace.next r))=
      SkywalkTrace.code (SkywalkTrace.next^[i+1] r)
    rw [Function.iterate_succ_apply]

theorem arith_tape (w : Nat → Wire) (x : Nat) (s : BasisState)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s) :
    skywalkTapeControls s (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) := by
  rw [arith_trace_map]
  simp only [skywalkTapeControls,skywalkSharedTape,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hh := h.2.2.2.1 i (List.mem_range.mp hi)
  exact Prod.ext hh.1 hh.2

theorem arith_terminal (x : Nat) (hx0 : 0 < x) (hx : x < p) :
    let r := SkywalkTrace.next^[512] (SkywalkRails.encode false false (x : Int) (p : Int))
    r.a=(if r.g then 0 else 1) ∧ r.b=(if r.g then 1 else 0) := by
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p < 2^256 := by norm_num [p]
  have hc : x.Coprime p := by
    apply Nat.Coprime.symm
    apply p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have ht := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpo hp (hx.trans hp) hc
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded 512 false false (SkywalkNat.init x p) hp0 hpo
  change (SkywalkNat.step^[512] (SkywalkNat.init x p)).u=0 ∧
    (SkywalkNat.step^[512] (SkywalkNat.init x p)).v=1 at ht
  rw [ht.1,ht.2] at he
  change SkywalkTrace.next^[512] (SkywalkRails.encode false false (x:Int) (p:Int))=
    SkywalkRails.encode G S (0:Int) (1:Int) at he
  dsimp only
  rw [he]
  cases G <;> simp [SkywalkRails.encode,SkywalkRails.zero_sign]

theorem arith_signed_read_nat (r : List Wire) (s : BasisState) (N : Nat)
    (hs : signedRegValue r s=(N : Int)) (hn : N < 2^r.length) : regValue r s=N := by
  have hh := congrArg (fun a : Int => a%(2^r.length:Nat)) hs
  change signedDecode r.length (regValue r s)%(2^r.length:Nat)=(N:Int)%(2^r.length:Nat) at hh
  rw [signedDecode_emod] at hh
  have hv := regValue_lt r s
  rw [Int.emod_eq_of_lt (by omega) (Int.ofNat_lt.mpr hv),
    Int.emod_eq_of_lt (by omega) (Int.ofNat_lt.mpr hn)] at hh
  omega

theorem arith_terminal_words (w : Nat → Wire) (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : BasisState)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s) :
    regValue (wireBlock w 512 258) s=(if s (w 511) then 0 else 1) ∧
    regValue (wireBlock w 770 258) s=(if s (w 511) then 1 else 0) := by
  have ht := arith_terminal x hx0 hx
  dsimp only at ht
  have hg : s (w 511)=(SkywalkTrace.next^[512]
      (SkywalkRails.encode false false (x : Int) (p : Int))).g := h.2.2.1
  refine ⟨?_,?_⟩
  · apply arith_signed_read_nat _ s (if s (w 511) then 0 else 1)
    · rw [hg]
      simpa only [skywalkPoolA,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] using h.1.trans ht.1
    · rw [wireBlock_length]; split <;> norm_num
  · apply arith_signed_read_nat _ s (if s (w 511) then 1 else 0)
    · rw [hg]
      simpa only [skywalkPoolB,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] using h.2.1.trans ht.2
    · rw [wireBlock_length]; split <;> norm_num

theorem arith_clear_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    (w 511::w 512::w 770::(wireBlock w 513 257++wireBlock w 771 257)).Nodup := by
  have hsep : (List.range' 513 257).Disjoint (List.range' 771 257) := by
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_range'_1] at hj hk
    omega
  have hd : (511::512::770::(List.range' 513 257++List.range' 771 257)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,List.mem_range'_1]
    refine ⟨by omega,by omega,by omega,List.nodup_append'.mpr
      ⟨List.nodup_range',List.nodup_range',hsep⟩⟩
  change ((511::512::770::(List.range' 513 257++List.range' 771 257)).map w).Nodup
  apply List.Nodup.map_on
  · intro i hi j hj he
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hi hj
    exact skywalkShared_index_inj w hn i j (by omega) (by omega) he
  · exact hd

theorem arith_clear_gates (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    [w 511,w 512,w 770].Nodup := by
  have hd := arith_clear_nodup w hn
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hd q
  simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
  omega

theorem arith_clear_words (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x : Nat) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s.basis) :
    regValue (wireBlock w 512 258) (run (skywalkArithmeticClear w) m s).basis=0 ∧
    regValue (wireBlock w 770 258) (run (skywalkArithmeticClear w) m s).basis=0 := by
  have ht := arith_terminal_words w x hx0 hx s.basis h
  have hA : wireBlock w 512 258=w 512::wireBlock w 513 257 := by
    have he := wireBlock_append w 512 1 257
    simpa only [show wireBlock w 512 1=[w 512] from rfl,List.singleton_append] using he.symm
  have hB : wireBlock w 770 258=w 770::wireBlock w 771 257 := by
    have he := wireBlock_append w 770 1 257
    simpa only [show wireBlock w 770 1=[w 770] from rfl,List.singleton_append] using he.symm
  rw [hA,hB] at ht ⊢
  have ho := skywalkTerminalClear_words _ _ _ _ _ (arith_clear_nodup w hn)
    (s.basis (w 511)) s m ⟨⟨rfl,ht.1⟩,ht.2⟩
  exact ⟨ho.2.1.2,ho.2.2⟩

end ECDSAAdd.Arithmetic.DirectSkywalk
end

-- source: ECDSAAdd/Arithmetic/DirectSkywalkCleanup.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ECDSAAdd.Arithmetic.DirectSkywalk
open Secp256k1
attribute [local irreducible] skywalkSeed skywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run

/-- PairFrame plus a source that starts and ends zero is a numerator-only frame. -/
theorem arith_field_frame (L : ModInPlaceLayout) (base s : BasisState) (Z : Nat)
    (ha : regValue L.a base=0) (hf : PairFrame L.z L.a base Z 0 s) :
    ∀ q,q∉L.z → s q=base q := by
  have he := (regValue_eq_iff L.a s base).mp (hf.2.1.trans ha.symm)
  intro q hq
  by_cases hs : q∈L.a
  · exact he q hs
  · exact hf.2.2 q hq hs

theorem arith_pool_away_z (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (q : Wire) (hq : q∈skywalkPoolWires w) : q∉(skywalkSharedField w).z := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [skywalkShared_field_z]
  exact arith_block_away w hn i 2056 257 (by omega) (by omega) (by omega)

theorem arith_loop_outside (back : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires w) :
    (run (if back then narrowSkywalkRoutedUnloop w 0 512 else narrowSkywalkRoutedLoop w 0 512) m s).basis q=s.basis q := by
  have hp := narrowSkywalkRoutedLoop_support w 0 512 (skywalkShared_integer_nodup w hn) (by omega)
  apply run_preserves_outside
  intro hm
  cases back
  · exact hq (List.mem_toFinset.mp (hp.1 hm))
  · exact hq (List.mem_toFinset.mp (hp.2 hm))

theorem arith_record_outside (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires w) :
    (run (narrowSkywalkRoutedLoop w 0 512) m s).basis q=s.basis q := by
  simpa only [Bool.false_eq_true,if_false] using arith_loop_outside false w hn s m q hq

theorem arith_clear_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire) (hq : q∉skywalkPoolWires w) :
    (run (skywalkArithmeticClear w) m s).basis q=s.basis q := by
  apply (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s m).2.1
  · intro he; subst q; exact hq (arith_mem w 0 1798 512 (by omega) (by omega))
  · intro he; subst q; exact hq (arith_mem w 0 1798 770 (by omega) (by omega))

theorem arith_z_input (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s) :
    regValue (skywalkSharedField w).z s=y := by
  change regValue (wireBlock w 2056 256++[w 2312]) s=y
  rw [regValue_append]
  change regValue (skywalkArithmeticNumerator w) s+_=_
  rw [h.2.1]
  simp [regValue,arith_input_bit w hn x y s h 2312 (by omega) (by omega) (by omega)]

theorem arith_preparation_frame (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (s : State) (m1 m2 m3 : List Bool) (q : Wire) (hq : q∈(skywalkSharedField w).z) :
    (run (skywalkArithmeticClear w) m3
      (run (narrowSkywalkRoutedLoop w 0 512) m2
        (run (skywalkSeed (skywalkSharedSeed w) p) m1 s))).basis q=s.basis q := by
  generalize hs1 : run (skywalkSeed (skywalkSharedSeed w) p) m1 s=s1
  generalize hs2 : run (narrowSkywalkRoutedLoop w 0 512) m2 s1=s2
  generalize hs3 : run (skywalkArithmeticClear w) m3 s2=s3
  rw [skywalkShared_field_z] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have hp := arith_block_away w hn i 0 1798 (by omega) (by omega) (by omega)
  have hs := arith_seed_outside w hn i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc := arith_clear_outside w hn s2 m3 (w i) hp
  rw [hs3] at hc
  have hl := arith_record_outside w hn s1 m2 (w i) hp
  rw [hs2] at hl
  have hf := (skywalkSeed_frame (skywalkSharedSeed w) 258 p
    (skywalkShared_seed_widths w) s m1 (w i) hs).1
  rw [hs1] at hf
  exact hc.trans (hl.trans hf)

theorem arith_clean_preparation (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx0 : 0 < x) (hx : x < p) (s : State) (m1 m2 m3 : List Bool)
    (h : SkywalkArithmeticInput w x y s.basis) :
    SkywalkSharedClean w (run (skywalkArithmeticClear w) m3
      (run (narrowSkywalkRoutedLoop w 0 512) m2
        (run (skywalkSeed (skywalkSharedSeed w) p) m1 s))).basis := by
  generalize hs1 : run (skywalkSeed (skywalkSharedSeed w) p) m1 s=seed
  generalize hs2 : run (narrowSkywalkRoutedLoop w 0 512) m2 seed=recorded
  generalize hs3 : run (skywalkArithmeticClear w) m3 recorded=cleared
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hst0 := arith_seed_stage0 w hn x y hx s m1 h
  rw [hs1] at hst0
  have hstFull := narrowSkywalkRouted512_spec w (skywalkShared_integer_nodup w hn) x p hp0 hx0 hpo arith_modulus_bound hx (arith_coprime x hx0 hx) seed m2 hst0
  rw [hs2] at hstFull
  have hst := hstFull.2
  have hr := arith_clear_words w hn x hx0 hx recorded m3 hst
  rw [hs3] at hr
  have keep (j : Nat) (hj : 1798 ≤ j) (hjmax : j < 2314) : cleared.basis (w j)=seed.basis (w j) := by
    have ho := arith_block_away w hn j 0 1798 hjmax (by omega) (by omega)
    have hc := arith_clear_outside w hn recorded m3 _ ho
    have hl := arith_record_outside w hn seed m2 _ ho
    rw [hs3] at hc
    rw [hs2] at hl
    exact hc.trans hl
  have hp : p < 2^256 := by norm_num [p]
  have hseedFull := skywalkSeed_spec _ 258 p x (skywalkShared_seed_widths w)
    (skywalkShared_seed_nodup w hn) (by omega) hp (hx.trans hp) s m1
      (arith_seed_input w hn x y s.basis h)
  rw [hs1] at hseedFull
  have hseed := hseedFull.2
  have hconst : regValue (wireBlock w 1798 258) cleared.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hseed.constant
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact keep j (by omega) (by omega)
  have hcarry : regValue (wireBlock w 1540 257) cleared.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hst.2.2.2.2.2.1
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have hk := (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) recorded m3).2.1
    change ∀ q,q≠w 512 → q≠w 770 → (run (skywalkArithmeticClear w) m3 recorded).basis q=recorded.basis q at hk
    rw [hs3] at hk
    apply hk
    · intro he; have hi := skywalkShared_index_inj w hn j 512 (by omega) (by omega) he; omega
    · intro he; have hi := skywalkShared_index_inj w hn j 770 (by omega) (by omega) he; omega
  have horient : cleared.basis (w 1797)=false := by
    have hk := (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) recorded m3).2.1
    change ∀ q,q≠w 512 → q≠w 770 → (run (skywalkArithmeticClear w) m3 recorded).basis q=recorded.basis q at hk
    rw [hs3] at hk
    apply Eq.trans (hk _ ?_ ?_) hst.2.2.2.2.2.2
    · intro he; have hi := skywalkShared_index_inj w hn 1797 512 (by omega) (by omega) he; omega
    · intro he; have hi := skywalkShared_index_inj w hn 1797 770 (by omega) (by omega) he; omega
  exact ⟨hr.1,hr.2,hcarry,hconst,horient,(keep 2313 (by omega) (by omega)).trans hseed.cin⟩

theorem arith_tape_clear (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (s : State) (m : List Bool) :
    skywalkTapeControls (run (skywalkArithmeticClear w) m s).basis (skywalkSharedTape w)=
      skywalkTapeControls s.basis (skywalkSharedTape w) := by
  simp only [skywalkTapeControls,skywalkSharedTape,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hib := List.mem_range.mp hi
  have keep (j : Nat) (hj : j=i ∨ j=1028+i) :
      (run (skywalkArithmeticClear w) m s).basis (w j)=s.basis (w j) := by
    apply (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s m).2.1
    · intro he; have hh := skywalkShared_index_inj w hn j 512 (by omega) (by omega) he; omega
    · intro he; have hh := skywalkShared_index_inj w hn j 770 (by omega) (by omega) he; omega
  exact Prod.ext (keep _ (Or.inl rfl)) (keep _ (Or.inr rfl))

theorem arith_block_subset_shared (w : Nat → Wire) (a n : Nat)
    (hb : a+n ≤ 2314) : wireBlock w a n ⊆ skywalkSharedWires w := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hj
  exact arith_mem w 0 2314 j (by omega) (by omega)

theorem arith_seed_subset_shared (w : Nat → Wire) :
    (skywalkSharedSeed w).usedWires ⊆ skywalkSharedWires w := by
  intro q hq
  change q∈w 2313::(wireBlock w 0 258++wireBlock w 770 258++
    wireBlock w 1798 258++wireBlock w 1540 257) at hq
  rcases List.mem_cons.mp hq with rfl|hr
  · exact arith_mem w 0 2314 2313 (by omega) (by omega)
  · simp only [List.mem_append,or_assoc] at hr
    rcases hr with hq|hq|hq|hq
    · exact arith_block_subset_shared w 0 258 (by omega) hq
    · exact arith_block_subset_shared w 770 258 (by omega) hq
    · exact arith_block_subset_shared w 1798 258 (by omega) hq
    · exact arith_block_subset_shared w 1540 257 (by omega) hq

end ECDSAAdd.Arithmetic.DirectSkywalk
end

-- source: ECDSAAdd/Arithmetic/LiteralSkywalkSeedSharedBridgeSupport.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Canonical shared seed values transfer without materializing any constant.
The initial orientation supplies clean Cin and the first history site supplies One. -/
theorem literalSkywalkSeedSharedBridge_values (w : Nat → Wire) (A B C : Nat)
    (s : BasisState) (hin : SkywalkSeedValues (skywalkSharedSeed w) A B C s)
    (hOne : s (w 1028)=false) :
    LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) A B s :=
  ⟨hin.a,hin.b,hin.carry,hin.orientation,hOne,hin.orientation⟩

/-- Register-value restoration plus the checked executable frame gives a
complete outsider-of-A frame, including the old constant bank and Cin. -/
private theorem old_values_outsideA (L : SkywalkSeedLayout) (A A' B C : Nat)
    (s t : BasisState) (hin : SkywalkSeedValues L A B C s)
    (hout : SkywalkSeedValues L A' B C t)
    (hf : ∀q,q∉L.usedWires → t q=s q) : ∀q,q∉L.a → t q=s q := by
  intro q hqa
  by_cases he : q=L.cin
  · subst q
    exact hout.cin.trans hin.cin.symm
  by_cases hqb : q∈L.b
  · exact (regValue_eq_iff _ _ _).mp (hout.b.trans hin.b.symm) q hqb
  by_cases hqc : q∈L.constant
  · exact (regValue_eq_iff _ _ _).mp (hout.constant.trans hin.constant.symm) q hqc
  by_cases hqd : q∈L.carry
  · exact (regValue_eq_iff _ _ _).mp (hout.carry.trans hin.carry.symm) q hqd
  apply hf q
  simp only [SkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
  tauto

/-- Actual old seed instructions preserve all sites outside A on canonical inputs. -/
theorem literalSkywalkSeedSharedBridge_oldSeed_outsideA (w : Nat → Wire) (p x : Nat)
    (hn : (skywalkSharedWires w).Nodup) (hp : p<2^256) (hx : x<2^256)
    (s : State) (m : List Bool) (hin : SkywalkSeedValues (skywalkSharedSeed w) 0 x 0 s.basis) :
    ∀q,q∉(skywalkSharedSeed w).a →
      (run (skywalkSeed (skywalkSharedSeed w) p) m s).basis q=s.basis q := by
  have hw := skywalkShared_seed_widths w
  have hl := skywalkShared_seed_nodup w hn
  have h := (skywalkSeed_spec (skywalkSharedSeed w) 258 p x hw hl
    (by decide) hp hx s m hin).2
  exact old_values_outsideA _ 0 (p+x) x 0 _ _ hin h
    (fun q hq => (skywalkSeed_frame (skywalkSharedSeed w) 258 p hw s m q hq).1)

/-- Equality of the mutable word and the full outsider frame determines State. -/
private theorem same_word_state (a : List Wire) (s t u : State) (V : Nat)
    (htp : t.phase=s.phase) (hup : u.phase=s.phase)
    (htv : regValue a t.basis=V) (huv : regValue a u.basis=V)
    (htf : ∀q,q∉a → t.basis q=s.basis q)
    (huf : ∀q,q∉a → u.basis q=s.basis q) : t=u := by
  apply congrArg₂ State.mk
  · exact htp.trans hup.symm
  · funext q
    by_cases hq : q∈a
    · exact (regValue_eq_iff _ _ _).mp (htv.trans huv.symm) q hq
    · exact (htf q hq).trans (huf q hq).symm

/-- A reusable exact State comparison for the actual seed emissions. -/
theorem literalSkywalkSeedSharedBridge_state_eq (a : List Wire) (s t u : State) (V : Nat)
    (htp : t.phase=s.phase) (hup : u.phase=s.phase)
    (htv : regValue a t.basis=V) (huv : regValue a u.basis=V)
    (htf : ∀q,q∉a → t.basis q=s.basis q)
    (huf : ∀q,q∉a → u.basis q=s.basis q) : t=u :=
  same_word_state a s t u V htp hup htv huv htf huf

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/LiteralSkywalkSeedSharedBridge.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Bank-free and original seed emissions have identical full State outputs.
Their measurement records are arbitrary and need not agree. -/
theorem literalSkywalkSeedSharedBridge_seed_eq (w : Nat → Wire) (p x : Nat)
    (hn : (skywalkSharedWires w).Nodup) (hp : p<2^256) (hx : x<2^256)
    (s : State) (mNew mOld : List Bool)
    (hin : SkywalkSeedValues (skywalkSharedSeed w) 0 x 0 s.basis)
    (hOne : s.basis (w 1028)=false) :
    run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) mNew s=
      run (skywalkSeed (skywalkSharedSeed w) p) mOld s := by
  have nInput := literalSkywalkSeedSharedBridge_values w 0 x 0 s.basis hin hOne
  have nv := literalSkywalkPoolSeed_valid w (skywalkShared_integer_nodup w hn)
  have nw := literalSkywalkPoolSeed_widths w
  have ow := skywalkShared_seed_widths w
  have ov := skywalkShared_seed_nodup w hn
  have n := literalSkywalkSeed_spec (literalSkywalkPoolSeed w) 258 p x nw nv
    (by decide) hp hx s mNew nInput
  have o := skywalkSeed_spec (skywalkSharedSeed w) 258 p x ow ov
    (by decide) hp hx s mOld hin
  exact literalSkywalkSeedSharedBridge_state_eq (skywalkSharedSeed w).a s _ _ (p+x)
    n.1 o.1 n.2.a o.2.a
    (literalSkywalkSeed_preserves_outsideA (literalSkywalkPoolSeed w) 258 p x nw nv
      (by decide) hp hx s mNew nInput)
    (literalSkywalkSeedSharedBridge_oldSeed_outsideA w p x hn hp hx s mOld hin)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DirectSkywalkLiteralSeedBridge.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1 DirectSkywalk

/-- The loaned One is already clean in the original arithmetic input. -/
theorem directSkywalkLiteralSeed_seed_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (x y : Nat) (hx : x<p)
    (s : State) (m : List Bool) (hin : SkywalkArithmeticInput w x y s.basis) :
    run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s=
      run (skywalkSeed (skywalkSharedSeed w) p) m s :=
  literalSkywalkSeedSharedBridge_seed_eq w p x hn arith_modulus_bound
    (hx.trans arith_modulus_bound) s m m (arith_seed_input w hn x y s.basis hin)
    (arith_input_bit w hn x y s.basis hin 1028 (by omega) (by omega) (by omega))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DirectSkywalkArithmetic.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic
open Secp256k1 DirectSkywalk

def directSkywalkResult (divide enabled : Bool) (x : Nat) (Y : Fp) : Fp :=
  if enabled then skywalkArithmeticResult divide x Y else Y

def DirectSkywalkArithmeticStrong (divide : Bool) (w : Nat → Wire) (b : Wire)
    (x : Nat) (Y : Fp) (initial out : State) : Prop :=
  out.phase=initial.phase ∧ regValue (skywalkArithmeticNumerator w) out.basis=
    (directSkywalkResult divide (initial.basis b) x Y).val ∧
    ∀ q,q∉skywalkArithmeticNumerator w → out.basis q=initial.basis q

attribute [local irreducible] skywalkSeed skywalkUnseed literalSkywalkSeed literalSkywalkUnseed
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run
attribute [local irreducible] SkywalkTrace.next Nat.iterate

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactSkywalkCallerInteger.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open DirectSkywalk
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] compactSkywalkForward compactSkywalkReverse
attribute [local irreducible] run measurementCount
attribute [local irreducible] SkywalkTrace.next Nat.iterate SkywalkIntegerStage

/-- Both actual forward emitters reach the same complete terminal physical
State. All integer history and every outsider agree, with independent records. -/
theorem compactSkywalkCaller_forward_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (x p : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (s : State) (mNew mOld : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    run (compactSkywalkForward w 0 512) mNew s = run (narrowSkywalkRoutedLoop w 0 512) mOld s := by
  have pool := skywalkShared_integer_nodup w hn
  have new := compactSkywalkForward_512 w pool x p hp0 hx0 hpo hp hx hc s mNew hin
  have old := narrowSkywalkRouted512_spec w pool x p hp0 hx0 hpo hp hx hc s mOld hin
  generalize eNew : run (compactSkywalkForward w 0 512) mNew s = newState at new ⊢
  generalize eOld : run (narrowSkywalkRoutedLoop w 0 512) mOld s = oldState at old ⊢
  have terminal := (compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc
    newState.basis new.2).2
  apply State.extensionality newState oldState
  · exact new.1.trans old.1.symm
  · funext q
    by_cases hq : q ∈ skywalkPoolWires w
    · exact skywalkIntegerStage_agrees w
        (SkywalkRails.encode false false (x : Int) (p : Int)) 512 (by decide)
        newState.basis oldState.basis terminal old.2 q hq
    · have frameNew := compactSkywalkForward_frame w pool 0 512 (by decide) s mNew q hq
      have frameOld := arith_record_outside w hn s mOld q hq
      rw [eNew] at frameNew
      rw [eOld] at frameOld
      exact frameNew.trans frameOld.symm

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OffsetCleanupBorrowedCallerLayout.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller

/-- The current source guard at 765 remains live. The clean old Cout at
768 replaces that single site in the borrowed mask bank. -/
def carry (w : Nat → Wire) : List Wire := wireBlock w 512 253++[w 766,w 767,w 768]

/-- Cleanup does not emit any instruction on the inherited Minus/Plus
roles. Distinct existing history sites supply those descriptor-only roles.
The active Cout borrows the preserved canonical source extension at 1026. -/
def layout (w : Nat → Wire) (sign : Wire) : BalancedCleanupOffset.Layout :=
  { toCircuit := { balancedSharedPorts w sign with cout:=w 1026,minus:=w 0,plus:=w 1 },
    offsetCarry := carry w }

private def ids : List Nat :=
  [765,1026,0,1,1796,1797,1027,2311,1025,2056]++List.range' 2057 254++
    List.range' 770 255++List.range' 1540 256++List.range' 512 253++[766,767,768]

private theorem idsND : ids.Nodup := by decide

private theorem idsBound (i : Nat) (hi : i∈ids) : i < 2314 := by
  simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
  omega

theorem widths (w : Nat → Wire) (sign : Wire) : (layout w sign).Widths := by
  simp [BalancedCleanupOffset.Layout.Widths,BalancedCircuit.Layout.Widths,
    BalancedCleanup.Layout.Widths,layout,carry,balancedSharedPorts,wireBlock]

theorem nodup (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (hs : sign∉skywalkSharedWires w) : (layout w sign).wires.Nodup := by
  have mapped : (ids.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkShared_index_inj w hn i j (idsBound i hi) (idsBound j hj) he
    · exact idsND
  have outside : sign∉ids.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    apply hs
    simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by have bound := idsBound i hi; omega,rfl⟩
  have all := List.nodup_cons.mpr ⟨outside,mapped⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp all q
  simp only [BalancedCleanupOffset.Layout.wires,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,layout,carry,balancedSharedPorts,ids,wireBlock,
    List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

end ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller
end

-- source: ECDSAAdd/Arithmetic/TerminalParityMeasure.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic.TerminalParityMeasure

def program (a b cin target : Wire) : Program :=
  [.X target]++eraseCarry a b cin target

/-- The input flag already holds the complemented majority. Measure that
flag directly; each fresh outcome receives its actual quadratic correction. -/
theorem correct (a b cin target : Wire)
    (ha : a≠target) (hb : b≠target) (hc : cin≠target)
    (s : State) (m : List Bool)
    (ht : s.basis target= !(carryBit (s.basis a) (s.basis b) (s.basis cin))) :
    run (program a b cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  let u := run [.X target] [] s
  have hu : u=⟨s.phase,writeBit s.basis target (!s.basis target)⟩ := rfl
  have hcarry : u.basis target=carryBit (u.basis a) (u.basis b) (u.basis cin) := by
    simp only [hu,writeBit,Function.update_self,Function.update_of_ne ha,
      Function.update_of_ne hb,Function.update_of_ne hc,ht,Bool.not_not]
  rw [program,run_append]
  simp only [show measurementCount [.X target]=0 from rfl,List.take_zero,List.drop_zero]
  change run (eraseCarry a b cin target) m u=_
  rw [eraseCarry_correct a b cin target ha hb hc u hcarry m,hu]
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq : q=target
    · subst q
      simp [writeBit]
    · simp [writeBit,hq]

theorem counts (a b cin target : Wire) :
    toffoliCount (program a b cin target)=0 ∧
    measurementCount (program a b cin target)=1 := by
  simp [program,eraseCarry,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.TerminalParityMeasure
end

-- source: ECDSAAdd/Arithmetic/TerminalParityLeaf.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityMeasure
open BalancedCleanupOffset
attribute [local irreducible] run mappedSum majority eraseCarry

def leaf (b : MappedBit) (a y cinC cinB d target : Wire) : Program :=
  mappedSum b y cinC++[.X y]++program a y cinB target++
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

theorem leaf_correct (b : MappedBit) (a y cinC cinB c d target : Wire)
    (hn : [a,y,cinC,cinB,c,d,target].Nodup)
    (ha : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d,target])
    (s : State) (m : List Bool) (hd : s.basis d=false)
    (ht : s.basis target= !(carryBit (s.basis a)
      (!(sumBit (b.value s.basis) (s.basis y) (s.basis cinC))) (s.basis cinB))) :
    run (leaf b a y cinC cinB d target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
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
  have cm : measurementCount (program a y cinB target)=1 := (counts a y cinB target).2
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
  let v := run (program a y cinB target) m u
  have uf (q : Wire) (hq : q≠y) : u.basis q=s.basis q := by
    rw [pu]
    simp [writeBit,hq]
  have uy : u.basis y= !S := by rw [pu]; simp [writeBit]
  have input : u.basis target= !(carryBit (u.basis a) (u.basis y) (u.basis cinB)) := by
    rw [uf target (by simp [nd,nr]),uf a (by simp [nd,nr]),uy,
      uf cinB (by simp [nd,nr])]
    exact ht
  have actualMeasure := correct a y cinB target (by simp [nd,nr])
    (by simp [nd,nr]) (by simp [nd,nr]) u m input
  change v=⟨u.phase,writeBit u.basis target false⟩ at actualMeasure
  have comp : v.phase=u.phase ∧ (∀q,q≠target → v.basis q=u.basis q) ∧
      v.basis target=false := by
    rw [actualMeasure]
    exact ⟨rfl,fun q hq => by simp [writeBit,hq],by simp [writeBit]⟩
  have value : v.basis target=false := comp.2.2
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
      (program a y cinB target++([.X y]++mappedSum b y cinC)) := by
    simp only [leaf,List.append_assoc]
  have actual : run (leaf b a y cinC cinB d target) m s=
      run (mappedSum b y cinC) (m.drop 1) (run [.X y] (m.drop 1) v) := by
    rw [shape,run_zero _ _ pm,run_append]
    have take := run_take (program a y cinB target) m u
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

theorem leaf_counts (b : MappedBit) (a y cinC cinB d target : Wire) :
    toffoliCount (leaf b a y cinC cinB d target)=0 ∧
    measurementCount (leaf b a y cinC cinB d target)=1 := by
  have c := mappedBit_counts b y cinC d
  have p := counts a y cinB target
  simp only [leaf,toffoliCount_append,measurementCount_append,
    c.2.2.2.2.1,c.2.2.2.2.2,p.1,p.2]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.TerminalParityMeasure
end

-- source: ECDSAAdd/Arithmetic/TerminalParityChain.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityMeasure
open BalancedCleanupOffset
def chain : List MappedBit → List Wire → List Wire → List Wire → List Wire →
    Wire → Wire → Wire → Program
  | [b],[a],[y],[_c],[d],cinC,cinB,target => leaf b a y cinC cinB d target
  | b::bits,a::as,y::ys,c::cs,d::ds,cinC,cinB,target =>
      prepareHead b a y cinC cinB c d++chain bits as ys cs ds c d target++
        releaseHead b a y cinC cinB c d
  | [],[],[],[],[],_,cinB,target => flipBelow none cinB target
  | _,_,_,_,_,_,_,_ => []

attribute [local irreducible] run chain prepareHead releaseHead

/-- Actual two-prefix circuit, with no tail-circuit premise. The explicit
Boolean recurrence is the offset carry followed by the comparison carry.
Every physical bit except target is restored, including both full banks. -/
theorem chain_correct (bits : List MappedBit) (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hn : (target::cinC::cinB::(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉target::cinC::cinB::(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (m : List Bool) (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false)
    (ht : s.basis target=decision (bits.map (fun b => b.value s.basis))
      (xs.map s.basis) (ys.map s.basis) (s.basis cinC) (s.basis cinB))
    (hnonempty : ys≠[]) :
    run (chain bits xs ys cs ds cinC cinB target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  induction ys generalizing bits xs cs ds cinC cinB s m with
  | nil =>
    exact (hnonempty rfl).elim
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
              have tag : s.basis target= !(carryBit (s.basis a)
                  (!(sumBit (b.value s.basis) (s.basis y) (s.basis cinC))) (s.basis cinB)) := by
                simpa only [decision,List.map_cons,List.map_nil] using ht
              have one := leaf_correct b a y cinC cinB c d target head fresh s m
                (hdd d (by simp)) tag
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
              have tag : u.basis target=decision (bits.map (fun b => b.value u.basis))
                  (xs.map u.basis) (ys.map u.basis) (u.basis c) (u.basis d) := by
                rw [uf target (Ne.symm c_t) (Ne.symm y_t) (Ne.symm d_t),mapBits,mapA,mapY,uk,ud]
                simpa only [decision,List.map_cons] using ht
              have tail := ih bits xs cs ds c d nt tailSource (by simpa using hb) (by simpa using hx)
                (by simpa using hc) (by simpa using hd) u m cc dd tag lone
              let V := decision (bits.map (fun b => b.value s.basis)) (xs.map s.basis)
                (ys.map s.basis) K D
              let v : State := ⟨u.phase,writeBit u.basis target false⟩
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


end ECDSAAdd.Arithmetic.TerminalParityMeasure
end

-- source: ECDSAAdd/Arithmetic/TerminalParityChainResources.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityMeasure
open BalancedCleanupOffset
attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry wires

private theorem chain_facts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 2) ∧
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
              have emittedLeaf := leaf_counts b a y cinC cinB d target
              refine ⟨?_,?_,?_⟩
              · simpa only [chain,List.length_cons,List.length_nil] using emittedLeaf.1
              · simpa only [chain,List.length_cons,List.length_nil] using emittedLeaf.2
              · intro q hq
                simp only [chain,leaf,program,BalancedCleanupOffset.chain,compareChain,
                  wires_append,Finset.mem_union] at hq ⊢
                simp only [majority,eraseCarry,flipBelow,wires,Instr.wires,correctionWires,
                  Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq ⊢
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
      2*ys.length-(if ys.length=0 then 0 else 2) ∧
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

end ECDSAAdd.Arithmetic.TerminalParityMeasure
end

-- source: ECDSAAdd/Arithmetic/TerminalParityZeroHead.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityZeroHead
open BalancedCleanupOffset
attribute [local irreducible] run TerminalParityMeasure.chain majority eraseCarry

/-- Offset bit0 and its incoming carry are both zero. The comparison carry
is still computed and measured cleanly; the offset carry is never emitted. -/
def program (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire) : Program :=
  ([.X y]++majority a y cinB d)++
    (TerminalParityMeasure.chain bits xs ys cs ds cinC d target++
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
    (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false)
    (ht : s.basis target=decision (false::bits.map (fun b => b.value s.basis))
      (s.basis a::xs.map s.basis) (s.basis y::ys.map s.basis) false (s.basis cinB))
    (hnonempty : ys≠[]) :
    run (program bits xs ys cs ds a y cinC cinB d target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
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
  have tag : u.basis target=decision (bits.map (fun b => b.value u.basis))
      (xs.map u.basis) (ys.map u.basis) (u.basis cinC) (u.basis d) := by
    rw [uf target (by simp [nd,nr]) (by simp [nd,nr]),mapBits,mapA,mapY,uc,ud]
    have boolean : carryBit false Y false=false ∧ sumBit false Y false=Y := by
      cases Y <;> decide
    simpa [decision,carryBit,sumBit,A,Y,E,D] using ht
  have tail := TerminalParityMeasure.chain_correct bits xs ys cs ds cinC d target tailND
    tailFresh hb hx hc hd u m cleanC cleanD tag hnonempty
  let V := decision (bits.map (fun b => b.value s.basis)) (xs.map s.basis) (ys.map s.basis) false D
  let v : State := ⟨u.phase,writeBit u.basis target false⟩
  change run (TerminalParityMeasure.chain bits xs ys cs ds cinC d target) m u=v at tail
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
      1+(2*ys.length-(if ys.length=0 then 0 else 2)) ∧
    measurementCount (program bits xs ys cs ds a y cinC cinB d target)=
      1+(2*ys.length-(if ys.length=0 then 0 else 1)) := by
  have tail := TerminalParityMeasure.chain_counts bits xs ys cs ds cinC d target hb hx hc hd
  simp only [program,toffoliCount_append,measurementCount_append,tail.1,tail.2]
  constructor <;> simp [majority,eraseCarry,toffoliCount,measurementCount,Nat.add_comm]



end ECDSAAdd.Arithmetic.TerminalParityZeroHead
end

-- source: ECDSAAdd/Arithmetic/TerminalParityZeroBridge.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace ECDSAAdd.Arithmetic.TerminalParityZeroHead
open BalancedCleanupOffset

/-- The matching flag follows from the old block's guaranteed zero output.
No new arithmetic-domain premise is imposed on the surrounding caller. -/
theorem eq_old_of_clears (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire)
    (hn : ([a,y,cinC,cinB,d,target]++(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉[a,y,cinC,cinB,d,target]++(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (mOld mNew : List Bool) (hz : s.basis cinC=false) (hzD : s.basis d=false)
    (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false)
    (hclear : (run (BalancedCleanupOffsetZeroHead.program bits xs ys cs ds
      a y cinC cinB d target) mOld s).basis target=false)
    (hnonempty : ys≠[]) :
    run (program bits xs ys cs ds a y cinC cinB d target) mNew s=
      run (BalancedCleanupOffsetZeroHead.program bits xs ys cs ds
        a y cinC cinB d target) mOld s := by
  let D := decision (false::bits.map (fun b => b.value s.basis))
    (s.basis a::xs.map s.basis) (s.basis y::ys.map s.basis) false (s.basis cinB)
  have old := BalancedCleanupOffsetZeroHead.run_correct bits xs ys cs ds a y cinC cinB
    d target hn ha hb hx hc hd s mOld hz hzD hcc hdd
  change run (BalancedCleanupOffsetZeroHead.program bits xs ys cs ds a y cinC cinB
    d target) mOld s=⟨s.phase,writeBit s.basis target (s.basis target ^^ D)⟩ at old
  have bit := congrArg (fun t : State => t.basis target) old
  have cleared : (s.basis target ^^ D)=false := by
    simpa only [writeBit,Function.update_self,hclear] using bit.symm
  have tag : s.basis target=D := by
    cases hp : s.basis target <;> cases hD : D <;> simp_all
  have fresh := run_correct bits xs ys cs ds a y cinC cinB d target hn ha hb hx hc hd
    s mNew hz hzD hcc hdd tag hnonempty
  rw [fresh,old,tag,Bool.xor_self]

end ECDSAAdd.Arithmetic.TerminalParityZeroHead
end

-- source: ECDSAAdd/Arithmetic/TerminalParityOffset.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityOffset
open BalancedCleanupOffset BalancedField
attribute [local irreducible] run

def core (L : Layout) : Program :=
  TerminalParityZeroHead.program (offsetBits L).tail L.y.tail L.r.tail
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


theorem core_eq_old_of_clears (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (mOld mNew : List Bool) (hz : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hd : ∀q∈L.offsetCarry,s.basis q=false)
    (hclear : (run (BalancedCleanupOffsetZero.core L) mOld s).basis L.parity=false) :
    run (core L) mNew s=run (BalancedCleanupOffsetZero.core L) mOld s := by
  obtain ⟨a,xs,y,ys,c,cs,d,ds,ey,er,ec,ed,lx,ly,lc,ld⟩ := heads L hw
  have bitlen : (offsetBits L).tail.length=255 := (tails L hw).1
  have nd := L.chainND hn
  rw [ey,er,ec,ed] at nd
  have shortND : ([a,y,L.one,L.cout,d,L.parity]++(xs++ys++cs++ds)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have fresh : ∀w∈mappedWires (offsetBits L).tail,
      w∉[a,y,L.one,L.cout,d,L.parity]++(xs++ys++cs++ds) := by
    intro w hq hm
    have mem : w∈mappedWires (offsetBits L) := by
      rw [offset_head]
      exact mapped_tail_member _ _ _ hq
    have away := offsetSources_away L hn w mem
    rw [ey,er,ec,ed] at away
    apply away
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hm ⊢
    tauto
  have cleanC : ∀q∈c::cs,s.basis q=false := by simpa only [ec] using hd
  have cleanD : ∀q∈d::ds,s.basis q=false := by simpa only [ed] using hc
  have oldClear : (run (BalancedCleanupOffsetZeroHead.program (offsetBits L).tail xs ys cs ds
      a y L.one L.cout d L.parity) mOld s).basis L.parity=false := by
    simpa only [BalancedCleanupOffsetZero.core,ey,er,ec,ed,List.tail_cons,List.headD_cons] using hclear
  have eq := TerminalParityZeroHead.eq_old_of_clears (offsetBits L).tail xs ys cs ds
    a y L.one L.cout d L.parity shortND fresh (by omega) (by omega) (by omega) (by omega)
    s mOld mNew hz (cleanD d (by simp)) (fun q hq => cleanC q (by simp [hq]))
      (fun q hq => cleanD q (by simp [hq])) oldClear (by intro e; simp [e] at ly)
  simpa only [core,BalancedCleanupOffsetZero.core,ey,er,ec,ed,List.tail_cons,List.headD_cons] using eq

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


theorem correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hcout : s.basis L.cout=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hd : ∀q∈L.offsetCarry,s.basis q=false)
    (hP : s.basis L.parity=decide (q < |2*R-signedY B Y|)) :
    run (program L) m s=run (BalancedCleanupOffsetZero.program L) m s := by
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
  have old := BalancedCleanupOffsetZero.correct L hw hn R Y B hr hy s m
    hR hY hS hz ho hcout hc hd hP
  rw [BalancedCleanupOffsetZero.program,sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2] at old
  have oldClear : (run (BalancedCleanupOffsetZero.core L) m u).basis L.parity=false := by
    have bit := congrArg (fun t : State => t.basis L.parity) old
    change (run (front L).reverse [] (run (BalancedCleanupOffsetZero.core L) m u)).basis L.parity=
      (writeBit s.basis L.parity false) L.parity at bit
    have away : L.parity∉wires (front L).reverse := by
      rw [wires_reverse]
      exact front_parity_away L hw hn
    rw [run_preserves_outside (front L).reverse [] (run (BalancedCleanupOffsetZero.core L) m u)
      L.parity away] at bit
    simpa only [writeBit,Function.update_self] using bit
  have eq := core_eq_old_of_clears L hw hn u m m one cleanC cleanD oldClear
  rw [program,BalancedCleanupOffsetZero.program,
    sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2,
    sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2,eq]

end ECDSAAdd.Arithmetic.TerminalParityOffset
end

-- source: ECDSAAdd/Arithmetic/TerminalParityOffsetResources.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityOffset
open BalancedCleanupOffset BalancedField

private theorem offset_head_TerminalParityOffsetResources (L : Layout) :
    offsetBits L=({wire:=none,flip:=false} : MappedBit)::(offsetBits L).tail := by
  have zero : offset.testBit 0=false := by decide
  have range : List.range 256=0::(List.range 255).map Nat.succ := List.range_succ_eq_map
  simp only [offsetBits,range,List.map_cons]
  simp only [show ¬((0 : Nat)=1) from by decide,if_false,zero,List.tail_cons]

private theorem tails_TerminalParityOffsetResources (L : Layout) (hw : L.Widths) :
    (offsetBits L).tail.length=255 ∧ L.y.tail.length=255 ∧ L.r.tail.length=255 ∧
    L.offsetCarry.tail.length=255 ∧ L.carry.tail.length=255 := by
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  simp only [List.length_tail,offsetBits_length,width.2.1,width.2.2.1,hw.2,cy]
  decide

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=509 ∧ measurementCount (program L)=510 := by
  have t := tails_TerminalParityOffsetResources L hw
  have h := TerminalParityZeroHead.counts (offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail (L.y.headD 0) (L.r.headD 0) L.one L.cout
    (L.carry.headD 0) L.parity (by omega) (by omega) (by omega) (by omega)
  simp only [program,core,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,(BalancedCleanupOffsetSlim.front_counts L).1,
    (BalancedCleanupOffsetSlim.front_counts L).2,h.1,h.2,t.2.2.1]
  norm_num

end ECDSAAdd.Arithmetic.TerminalParityOffset
end

-- source: ECDSAAdd/Arithmetic/TerminalParitySlimSupport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityMeasure
open BalancedCleanupOffset
attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry wires
private theorem slim_facts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 2) ∧
    measurementCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 1) ∧
    wires (chain bits xs ys cs ds cinC cinB target)⊆
      wires (BalancedCleanupOffsetSlim.chain bits xs ys cs ds cinC cinB target) := by
  induction ys generalizing bits xs cs ds cinC cinB with
  | nil =>
    have b := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have x := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have c := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have d := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    simp [chain,BalancedCleanupOffsetSlim.chain,flipBelow,toffoliCount,measurementCount]
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
              have emittedLeaf := leaf_counts b a y cinC cinB d target
              refine ⟨?_,?_,?_⟩
              · simpa only [chain,List.length_cons,List.length_nil] using emittedLeaf.1
              · simpa only [chain,List.length_cons,List.length_nil] using emittedLeaf.2
              · intro q hq
                simp only [chain,leaf,program,BalancedCleanupOffsetSlim.chain,compareChain,
                  wires_append,Finset.mem_union] at hq ⊢
                simp only [majority,eraseCarry,flipBelow,wires,Instr.wires,correctionWires,
                  Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq ⊢
                tauto
            | cons y' ys =>
              cases bits with
              | nil => simp at hb
              | cons b' bits =>
                have emitted : chain (b::b'::bits) (a::xs) (y::y'::ys) (c::cs) (d::ds) cinC cinB target=
                    prepareHead b a y cinC cinB c d++chain (b'::bits) xs (y'::ys) cs ds c d target++
                    releaseHead b a y cinC cinB c d := rfl
                have original : BalancedCleanupOffsetSlim.chain (b::b'::bits) (a::xs) (y::y'::ys)
                    (c::cs) (d::ds) cinC cinB target=
                    prepareHead b a y cinC cinB c d++BalancedCleanupOffsetSlim.chain (b'::bits)
                      xs (y'::ys) cs ds c d target++releaseHead b a y cinC cinB c d := rfl
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
                      q∈wires (BalancedCleanupOffsetSlim.chain (b'::bits) xs (y'::ys) cs ds c d target) := fun h => tail.2.2 h
                  simp only [emitted,original,prepareHead,releaseHead,
                    wires_append,Finset.mem_union,or_assoc] at hq ⊢
                  tauto


theorem chain_support_slim (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    wires (chain bits xs ys cs ds cinC cinB target)⊆
      wires (BalancedCleanupOffsetSlim.chain bits xs ys cs ds cinC cinB target) :=
  (slim_facts bits xs ys cs ds cinC cinB target hb hx hc hd).2.2
end ECDSAAdd.Arithmetic.TerminalParityMeasure
end

-- source: ECDSAAdd/Arithmetic/TerminalParityOldSupport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityOffset
open BalancedCleanupOffset BalancedField
private theorem offset_head_TerminalParityOldSupport (L : Layout) :
    offsetBits L=({wire:=none,flip:=false} : MappedBit)::(offsetBits L).tail := by
  have zero : offset.testBit 0=false := by decide
  have range : List.range 256=0::(List.range 255).map Nat.succ := List.range_succ_eq_map
  simp only [offsetBits,range,List.map_cons]
  simp only [show ¬((0 : Nat)=1) from by decide,if_false,zero,List.tail_cons]

private theorem tails_TerminalParityOldSupport (L : Layout) (hw : L.Widths) :
    (offsetBits L).tail.length=255 ∧ L.y.tail.length=255 ∧ L.r.tail.length=255 ∧
    L.offsetCarry.tail.length=255 ∧ L.carry.tail.length=255 := by
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  simp only [List.length_tail,offsetBits_length,width.2.1,width.2.2.1,hw.2,cy]
  decide

private theorem heads_TerminalParityOldSupport (L : Layout) (hw : L.Widths) :
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


theorem support_old (L : Layout) (hw : L.Widths) :
    wires (program L)⊆wires (BalancedCleanupOffsetZero.program L) := by
  obtain ⟨a,xs,y,ys,c,cs,d,ds,ey,er,ec,ed,lx,ly,lc,ld⟩ := heads_TerminalParityOldSupport L hw
  have sub := TerminalParityMeasure.chain_support_slim (offsetBits L).tail xs ys cs ds
    L.one d L.parity (by have h := (tails_TerminalParityOldSupport L hw).1; omega)
      (by omega) (by omega) (by omega)
  have coreSub : wires (core L)⊆wires (BalancedCleanupOffsetZero.core L) := by
    intro q hq
    simp only [core,BalancedCleanupOffsetZero.core,ey,er,ec,ed,List.tail_cons,List.headD_cons,
      TerminalParityZeroHead.program,BalancedCleanupOffsetZeroHead.program,
      wires_append,Finset.mem_union] at hq ⊢
    have step : q∈wires (TerminalParityMeasure.chain (offsetBits L).tail xs ys cs ds
        L.one d L.parity) → q∈wires (BalancedCleanupOffsetSlim.chain (offsetBits L).tail
          xs ys cs ds L.one d L.parity) := fun h => sub h
    tauto
  intro q hq
  simp only [program,BalancedCleanupOffsetZero.program,wires_append,Finset.mem_union] at hq ⊢
  have step : q∈wires (core L) → q∈wires (BalancedCleanupOffsetZero.core L) := fun h => coreSub h
  tauto

end ECDSAAdd.Arithmetic.TerminalParityOffset
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedFieldProgram.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedField

/-- Forward field emission. The second carry bank is supplied by
existing terminal-zero mask sites, deliberately excluding the live guard765. -/
def program (w : Nat → Wire) (sign : Wire) : Program :=
  BalancedCircuit.coreProgram (balancedSharedPorts w sign)++
    (TerminalParityOffset.program (OffsetCleanupBorrowedCaller.layout w sign)++
      [.CX (balancedSharedPorts w sign).ymsb (balancedSharedPorts w sign).sourceGuard])

/-- Every used clean bank/flag, including the canonical high source site
borrowed as the cleanup comparison carry-in. Ghost descriptor roles are absent. -/
def work (w : Nat → Wire) (sign : Wire) : List Wire :=
  BalancedCircuit.work (balancedSharedPorts w sign)++
    OffsetCleanupBorrowedCaller.carry w++[w 1026]

theorem core_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (BalancedCircuit.coreProgram L)=513 ∧
    measurementCount (BalancedCircuit.coreProgram L)=513 := by
  have full := BalancedCircuit.counts L hw
  have cleanup := BalancedCleanup.counts L.toLayout hw
  rw [BalancedCircuit.program_eq_core] at full
  simp only [toffoliCount_append,measurementCount_append,cleanup.1,cleanup.2,
    show toffoliCount [.CX L.ymsb L.sourceGuard]=0 from rfl,
    show measurementCount [.CX L.ymsb L.sourceGuard]=0 from rfl,Nat.add_zero] at full
  omega

theorem counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (program w sign)=1022 ∧ measurementCount (program w sign)=1023 := by
  have c := core_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  have o := TerminalParityOffset.counts (OffsetCleanupBorrowedCaller.layout w sign)
    (OffsetCleanupBorrowedCaller.widths w sign)
  simp only [program,toffoliCount_append,measurementCount_append,c.1,c.2,o.1,o.2]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.OffsetBorrowedField
end

-- source: ECDSAAdd/Arithmetic/OffsetCleanupBorrowedCallerClean.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller
open BalancedField Secp256k1 DirectSkywalk
attribute [local irreducible] run wires

private theorem core_support_sub (L : BalancedCircuit.Layout) :
    wires (BalancedCircuit.coreProgram L) ⊆ wires (BalancedCircuit.program L) := by
  intro q hq
  simp only [BalancedCircuit.program_eq_core,wires_append,Finset.mem_union]
  exact Or.inl (Or.inl hq)

private theorem wireNe (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i j : Nat) (hi : i < 2314) (hj : j < 2314) (hne : i ≠ j) : w i ≠ w j :=
  fun he => hne (skywalkShared_index_inj w hn i j hi hj he)

/-- This is the actual caller's existing field-work invariant. Past G
records occupy 0..511; the terminal-clear mask is 512..768. -/
theorem maskBit_zero (w : Nat → Wire) (s : BasisState)
    (hw : regValue (skywalkSharedField w).work s=0) (i : Nat)
    (hi0 : 512 ≤ i) (hi : i < 769) : s (w i)=false := by
  have hm := arith_mem w 512 257 i hi0 (by omega)
  exact (regValue_zero _ _).mp hw _ (by
    simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,hm])

theorem entryCarry_clean (w : Nat → Wire) (s : BasisState)
    (hw : regValue (skywalkSharedField w).work s=0) : ∀q∈carry w,s q=false := by
  intro q hq
  simp only [carry,List.mem_append] at hq
  rcases hq with hq|hq
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact maskBit_zero w s hw i (by omega) (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    all_goals exact maskBit_zero w s hw _ (by omega) (by omega)

/-- Every canonical original 257-bit source has zero extension; the
existing low-pair caller frame preserves that site throughout the replay. -/
theorem callerCout_clean (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base current : BasisState) (Y : Fp) (X Z : Nat)
    (hy : regValue (skywalkSharedField w).a base=Y.val)
    (hframe : PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base X Z current) :
    current (w 1026)=false := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have a := wireBlock_append w 770 256 1
  have one : wireBlock w 1026 1=[w 1026] := by simp [wireBlock,List.range']
  have av : (skywalkSharedField w).a=wireBlock w 770 256++[w 1026] := by
    change wireBlock w 770 257=_
    simpa only [Nat.reduceAdd,one] using a.symm
  rw [av] at hy
  have high := (balancedCanonical_high_zero _ _ base Y.val
    (by rw [wireBlock_length]; exact (ZMod.val_lt Y).trans (by norm_num [p])) hy).2
  exact (hframe.2.2 _
    (arith_block_away w hn 1026 2056 256 (by omega) (by omega) (by omega))
    (arith_block_away w hn 1026 770 256 (by omega) (by omega) (by omega))).trans high

/-- At the actual forward-core cleanup boundary, the mask prefix is
preserved, and old Minus/Plus/Cout are clean by core_correct. The live
source guard at 765 is deliberately omitted. No extra clean-bank premise. -/
theorem forwardCarry_clean (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis sign=B)
    (hr : signedRegValue (balancedSharedPorts w sign).r s.basis=X)
    (hyr : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0) :
    ∀q∈carry w,(run (BalancedCircuit.coreProgram (balancedSharedPorts w sign)) m s).basis q=false := by
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have nd := balancedSharedPorts_nodup w sign hn own
  have native := BalancedCircuit.core_correct (balancedSharedPorts w sign)
    (balancedSharedPorts_widths w sign) nd B X Y hx hy s m hs hr hyr
    (balancedSharedPorts_clean w sign s.basis hw hu)
  intro q hq
  simp only [carry,List.mem_append] at hq
  rcases hq with hq|hq
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    have away : w i∉(balancedSharedPorts w sign).r := by
      rw [balancedSharedPorts_r]
      exact arith_block_away w hn i 2056 256 (by omega) (by omega) (by omega)
    have keep := native.2.2.2.2.2 (w i) away
      (wireNe w hn i 1796 (by omega) (by omega) (by omega))
      (wireNe w hn i 765 (by omega) (by omega) (by omega))
    exact keep.trans (maskBit_zero w s.basis hw i (by omega) (by omega))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    all_goals exact native.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean,balancedSharedPorts])

/-- The native core never emits a gate on the canonical high source site.
Thus the derived caller high-zero property reaches active cleanup Cout. -/
theorem forwardCout_frame (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (s : State) (m : List Bool) :
    (run (BalancedCircuit.coreProgram (balancedSharedPorts w sign)) m s).basis (w 1026)=
      s.basis (w 1026) := by
  have own : w 1026∈skywalkSharedWires w := arith_mem w 0 2314 1026 (by omega) (by omega)
  have ns : w 1026 ≠ sign := fun e => hsOut (e ▸ own)
  have neq (j : Nat) (hj : j < 2314) (hne : 1026 ≠ j) : w 1026 ≠ w j :=
    wireNe w hn 1026 j (by omega) hj hne
  have rtail := arith_block_away w hn 1026 2057 254 (by omega) (by omega) (by omega)
  have ylow := arith_block_away w hn 1026 770 255 (by omega) (by omega) (by omega)
  have carryAway := arith_block_away w hn 1026 1540 256 (by omega) (by omega) (by omega)
  have away : w 1026∉(balancedSharedPorts w sign).wires := by
    simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,balancedSharedPorts,
      List.mem_append,List.mem_cons,List.not_mem_nil,rtail,ylow,carryAway,ns,
      neq 765 (by omega) (by omega),neq 768 (by omega) (by omega),
      neq 767 (by omega) (by omega),neq 766 (by omega) (by omega),
      neq 1796 (by omega) (by omega),neq 1797 (by omega) (by omega),
      neq 1027 (by omega) (by omega),neq 2311 (by omega) (by omega),
      neq 1025 (by omega) (by omega),neq 2056 (by omega) (by omega),
      or_false,not_false_eq_true]
  have sub := core_support_sub (balancedSharedPorts w sign)
  have support := balancedSharedPorts_support w sign
  have outside : w 1026∉wires (BalancedCircuit.coreProgram (balancedSharedPorts w sign)) := by
    intro hq
    exact away (List.mem_toFinset.mp (support (sub hq)))
  exact run_preserves_outside (BalancedCircuit.coreProgram (balancedSharedPorts w sign)) m s (w 1026) outside

end ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedCanonicalEnvironment.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
open Secp256k1 BalancedField DirectSkywalk

/-- Existing caller invariants plus the canonical source extension. -/
def Env (w : Nat → Wire) (base : BasisState) : Prop :=
  regValue (skywalkSharedField w).work base=0 ∧
  regValue (skywalkSharedUnused w) base=0 ∧ base (w 1026)=false

theorem field_mem_shared (w : Nat → Wire) (q : Wire)
    (hq : q∈(skywalkSharedField w).wires) : q∈skywalkSharedWires w := by
  have block (start len : Nat) (hb : start+len≤2314)
      (hm : q∈wireBlock w start len) : q∈skywalkSharedWires w := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    simp only [List.mem_range'_1] at hi
    exact arith_mem w 0 2314 i (by omega) (by omega)
  simp only [skywalkSharedField,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
    ModAddCoreLayout.z,ModAddCoreLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq|hq
  · exact block 770 257 (by omega) hq
  · exact block 2056 256 (by omega) hq
  · subst q; exact arith_mem w 0 2314 2312 (by omega) (by omega)
  · exact block 1540 257 (by omega) hq
  · exact block 1798 256 (by omega) hq
  · subst q; exact arith_mem w 0 2314 1797 (by omega) (by omega)
  · exact block 512 257 (by omega) hq
  · subst q; exact arith_mem w 0 2314 2313 (by omega) (by omega)

theorem unused_mem_shared (w : Nat → Wire) (q : Wire) (hq : q∈skywalkSharedUnused w) :
    q∈skywalkSharedWires w := by
  simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  all_goals exact arith_mem w 0 2314 _ (by omega) (by omega)

theorem work_mem_shared (w : Nat → Wire) (q : Wire) (hq : q∈(skywalkSharedField w).work) :
    q∈skywalkSharedWires w := field_mem_shared w q (by simp [ModInPlaceLayout.wires,hq])

theorem env_write (w : Nat → Wire) (q : Wire) (hq : q∉skywalkSharedWires w)
    (base : BasisState) (v : Bool) (h : Env w base) : Env w (writeBit base q v) := by
  have same (i : Wire) (hi : i∈skywalkSharedWires w) : (writeBit base q v) i=base i := by
    simp only [writeBit,Function.update_of_ne (show i≠q from fun e => hq (e ▸ hi))]
  exact ⟨(regValue_congr _ _ _ (fun i hi => same i (work_mem_shared w i hi))).trans h.1,
    (regValue_congr _ _ _ (fun i hi => same i (unused_mem_shared w i hi))).trans h.2.1,
    (same _ (arith_mem w 0 2314 1026 (by omega) (by omega))).trans h.2.2⟩

/-- High-zero follows from the actual original canonical257 source value,
not from a low-word frame or a new unsupported clean-bank premise. -/
theorem env_of_canonical_source (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base : BasisState) (A : Fp)
    (ha : regValue (skywalkSharedField w).a base=A.val)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) : Env w base := by
  have frame : PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
      (regValue (wireBlock w 2056 256) base) (regValue (wireBlock w 770 256) base) base :=
    ⟨rfl,rfl,fun _ _ _ => rfl⟩
  exact ⟨hw,hu,OffsetCleanupBorrowedCaller.callerCout_clean w hn base base A _ _ ha frame⟩

theorem pair_env (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (base current : BasisState) (I J : Nat) (he : Env w base)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base I J current) :
    Env w current := by
  let L := balancedSharedPorts w sign
  have full := skywalkShared_field_nodup w hn
  have dis := (List.nodup_append'.mp full).2.2
  have rSub : L.r⊆(skywalkSharedField w).z := by
    rw [balancedSharedPorts_r,skywalkShared_field_z]
    intro q hq
    have eq := wireBlock_append w 2056 256 1
    have mem : q∈wireBlock w 2056 256++wireBlock w 2312 1 := List.mem_append_left _ hq
    simpa only [Nat.reduceAdd,eq] using mem
  have ySub : L.y⊆(skywalkSharedField w).a := by
    rw [balancedSharedPorts_y]
    intro q hq
    change q∈wireBlock w 770 257
    have eq := wireBlock_append w 770 256 1
    have mem : q∈wireBlock w 770 256++wireBlock w 1026 1 := List.mem_append_left _ hq
    simpa only [Nat.reduceAdd,eq] using mem
  have wa (q : Wire) (hq : q∈(skywalkSharedField w).work) : q∉L.r ∧ q∉L.y := by
    constructor
    · intro hm; exact List.disjoint_left.mp dis (List.mem_append_right _ (rSub hm)) hq
    · intro hm; exact List.disjoint_left.mp dis (List.mem_append_left _ (ySub hm)) hq
  have ua (q : Wire) (hq : q∈skywalkSharedUnused w) : q∉L.r ∧ q∉L.y := by
    have no := skywalkShared_unused_outside w hn q hq
    exact ⟨fun hm => no (by simp [ModInPlaceLayout.wires,rSub hm]),
      fun hm => no (by simp [ModInPlaceLayout.wires,ySub hm])⟩
  refine ⟨(regValue_congr _ _ _ (fun q hq => h.2.2 q (wa q hq).1 (wa q hq).2)).trans he.1,
    (regValue_congr _ _ _ (fun q hq => h.2.2 q (ua q hq).1 (ua q hq).2)).trans he.2.1,?_⟩
  have ar : w 1026∉L.r := by rw [balancedSharedPorts_r]; exact arith_block_away w hn 1026 2056 256 (by omega) (by omega) (by omega)
  have ay : w 1026∉L.y := by rw [balancedSharedPorts_y]; exact arith_block_away w hn 1026 770 256 (by omega) (by omega) (by omega)
  exact (h.2.2 _ ar ay).trans he.2.2

end ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedInverseParity.lean
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedInverse
open BalancedField
attribute [local irreducible] toffoliCount measurementCount run

def recoverParity (w : Nat → Wire) (sign : Wire) : Program :=
  BalancedCleanupOffsetZero.program (OffsetCleanupBorrowedCaller.layout w sign)

/-- The replacement is the same XOR oracle for every target value and for
independent measurement streams. The caller must provide the actual clean
borrowed bank and canonical source extension, not a reversed measurement. -/
theorem recoverParity_equiv (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m n : List Bool)
    (hR : regValue (balancedSharedPorts w sign).r s.basis=encodeWord 256 R)
    (hY : regValue (balancedSharedPorts w sign).y s.basis=encodeWord 256 Y)
    (hS : s.basis sign=B) (hz : s.basis (w 1797)=false)
    (ho : s.basis (w 1027)=false) (hhigh : s.basis (w 1026)=false)
    (hc : ∀q∈(balancedSharedPorts w sign).carry,s.basis q=false)
    (hd : ∀q∈OffsetCleanupBorrowedCaller.carry w,s.basis q=false) :
    run (recoverParity w sign) m s=
      run (BalancedInverse.recoverParity (balancedSharedPorts w sign)) n s := by
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    apply hsOut
    simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by have bound := balancedSharedIds_bound i hi; omega,rfl⟩
  have nd := balancedSharedPorts_nodup w sign hn own
  have old := BalancedCleanupXor.xor_correct (balancedSharedPorts w sign).toLayout
    (balancedSharedPorts_widths w sign) (List.nodup_append'.mp nd).2.1
    R Y B hr hy s n hR hY hS hz ho hc
  have fresh := BalancedCleanupOffsetZero.xor_correct (OffsetCleanupBorrowedCaller.layout w sign)
    (OffsetCleanupBorrowedCaller.widths w sign) (OffsetCleanupBorrowedCaller.nodup w sign hn hsOut)
    R Y B hr hy s m hR hY hS hz ho hhigh hc hd
  exact fresh.trans old.symm

def tail (L : BalancedCircuit.Layout) : Program :=
  BalancedInverse.recoverSelectors L++rotateLeft (BalancedCircuit.rawTarget L)++
    BalancedInverse.undoFold L++BalancedInverse.undoPreparation L++
    BalancedInverse.rawSubtract L++(BalancedCircuit.seedViews L).reverse

/-- Independently measured inverse emission with the cheaper recovery oracle. -/
def program (w : Nat → Wire) (sign : Wire) : Program :=
  let L := balancedSharedPorts w sign
  [.CX L.ymsb L.sourceGuard]++recoverParity w sign++tail L

private theorem original_program_layout (L : BalancedCircuit.Layout) :
    BalancedInverse.program L=[.CX L.ymsb L.sourceGuard]++
      BalancedInverse.recoverParity L++tail L := by
  simp only [BalancedInverse.program,tail,List.append_assoc]

private theorem tail_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (tail L)=513 ∧ measurementCount (tail L)=513 := by
  have full := BalancedInverse.counts L hw
  have old := BalancedCleanup.counts L.toLayout hw
  have layout := original_program_layout L
  rw [layout] at full
  simp only [BalancedInverse.recoverParity,toffoliCount_append,measurementCount_append,
    old.1,old.2,show toffoliCount [.CX L.ymsb L.sourceGuard]=0 by simp only [toffoliCount],
    show measurementCount [.CX L.ymsb L.sourceGuard]=0 by simp only [measurementCount]] at full
  omega

theorem counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (program w sign)=1023 ∧ measurementCount (program w sign)=1023 := by
  have fresh := BalancedCleanupOffsetZero.counts (OffsetCleanupBorrowedCaller.layout w sign)
    (OffsetCleanupBorrowedCaller.widths w sign)
  have old := tail_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  simp only [program,recoverParity,toffoliCount_append,measurementCount_append,fresh.1,fresh.2,
    old.1,old.2,show toffoliCount [.CX (balancedSharedPorts w sign).ymsb
      (balancedSharedPorts w sign).sourceGuard]=0 by simp only [toffoliCount],
    show measurementCount [.CX (balancedSharedPorts w sign).ymsb
      (balancedSharedPorts w sign).sourceGuard]=0 by simp only [measurementCount]]
  norm_num

end ECDSAAdd.Arithmetic.OffsetBorrowedInverse
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedInverseProof.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedInverse
open BalancedField BalancedCircuit DirectSkywalk
attribute [local irreducible] run

private theorem lower_mem_work (L : BalancedCircuit.Layout) : L.lower∈BalancedCircuit.work L := by
  simp [BalancedCircuit.work]

private theorem one_mem_work (L : BalancedCircuit.Layout) : L.one∈BalancedCircuit.work L := by
  simp [BalancedCircuit.work]

private theorem carry_mem_work (L : BalancedCircuit.Layout) (a : Wire) (ha : a∈L.carry) :
    a∈BalancedCircuit.work L := List.mem_append_right _ ha

private theorem old_layout (L : BalancedCircuit.Layout) :
    BalancedInverse.program L=[.CX L.ymsb L.sourceGuard]++
      BalancedInverse.recoverParity L++tail L := by
  simp only [BalancedInverse.program,tail,List.append_assoc]

private theorem run_prefix (a b : Wire) (oracle rest : Program) (m : List Bool) (s : State) :
    run ([.CX a b]++oracle++rest) m s=
      run rest (m.drop (measurementCount oracle))
        (run oracle m (run [.CX a b] m s)) := by
  rw [List.append_assoc,run_append,run_take]
  change run (oracle++rest) m (run [.CX a b] m s)=_
  rw [run_append,run_take]

private theorem guard_records (a b : Wire) (m n : List Bool) (s : State) :
    run [.CX a b] m s=run [.CX a b] n s := by
  simp only [run]

private theorem index_ne (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i j : Nat) (hi : i<2314) (hj : j<2314) (hne : i≠j) : w i≠w j :=
  fun h => hne (skywalkShared_index_inj w hn i j hi hj h)

/-- The borrowed bank omits precisely the live source guard. -/
private theorem bank_guard_away (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (a : Wire) (ha : a∈OffsetCleanupBorrowedCaller.carry w) : a≠w 765 := by
  simp only [OffsetCleanupBorrowedCaller.carry,List.mem_append] at ha
  rcases ha with ha|ha
  · intro e
    exact arith_block_away w hn 765 512 253 (by omega) (by omega) (by omega) (e ▸ ha)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals exact index_ne w hn _ _ (by omega) (by omega) (by omega)

private theorem bank_target_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (a : Wire)
    (ha : a∈OffsetCleanupBorrowedCaller.carry w) : a∉(balancedSharedPorts w sign).r := by
  rw [balancedSharedPorts_r]
  simp only [OffsetCleanupBorrowedCaller.carry,List.mem_append] at ha
  rcases ha with ha|ha
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact arith_block_away w hn i 2056 256 (by omega) (by omega) (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals exact arith_block_away w hn _ 2056 256 (by omega) (by omega) (by omega)

/-- 254 padding records align the 764-record original recovery with the
510-record replacement. Their actual XOR outputs agree on independent records. -/
theorem program_equiv (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hS : s.basis sign=B)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhigh : s.basis (w 1026)=false) :
    run (program w sign) m s=
      run (BalancedInverse.program (balancedSharedPorts w sign))
        (List.replicate 254 false++m) s := by
  let L := balancedSharedPorts w sign
  let n := List.replicate 254 false++m
  let u := run [.CX L.ymsb L.sourceGuard] m s
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have nd := balancedSharedPorts_nodup w sign hn own
  have widths := balancedSharedPorts_widths w sign
  have clean := balancedSharedPorts_clean w sign s.basis hw hu
  have keep (a : Wire) (ha : a≠L.sourceGuard) : u.basis a=s.basis a := by
    simp only [u,run,writeBit,Function.update_of_ne ha]
  have dataAway (a : Wire) (ha : a∈L.r++L.y++L.carry) : a≠L.sourceGuard :=
    fun e => flagAway L nd L.sourceGuard (by simp) (e ▸ ha)
  have R₁ : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 (BalancedCleanup.widths L.toLayout widths).2.1 s.basis R hR)
    exact regValue_congr _ _ _ (fun a ha => keep a (dataAway a (by simp [ha])))
  have Y₁ : regValue L.y u.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 (BalancedCleanup.widths L.toLayout widths).2.2.1 s.basis Y hY)
    exact regValue_congr _ _ _ (fun a ha => keep a (dataAway a (by simp [ha])))
  have scalar := scalarND L nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  rcases scalar with ⟨⟨_,_,_,_,gSign,gLower,gOne,_,_,_⟩,_⟩
  have S₁ : u.basis sign=B := (keep L.sign (Ne.symm gSign)).trans hS
  have low₁ : u.basis (w 1797)=false :=
    (keep L.lower (Ne.symm gLower)).trans (clean L.lower (lower_mem_work L))
  have one₁ : u.basis (w 1027)=false :=
    (keep L.one (Ne.symm gOne)).trans (clean L.one (one_mem_work L))
  have high_ne : w 1026≠L.sourceGuard := by
    change w 1026≠w 765
    exact index_ne w hn 1026 765 (by omega) (by omega) (by omega)
  have high₁ : u.basis (w 1026)=false := (keep _ high_ne).trans hhigh
  have carry₁ : ∀a∈L.carry,u.basis a=false := by
    intro a ha
    exact (keep a (dataAway a (by simp [ha]))).trans (clean a (carry_mem_work L a ha))
  have bank₁ : ∀a∈OffsetCleanupBorrowedCaller.carry w,u.basis a=false := by
    intro a ha
    exact (keep a (by simpa only [L,balancedSharedPorts] using bank_guard_away w hn a ha)).trans
      (OffsetCleanupBorrowedCaller.entryCarry_clean w s.basis hw a ha)
  have oracle := recoverParity_equiv w sign hn hsOut R Y B hr hy u m n
    R₁ Y₁ S₁ low₁ one₁ high₁ carry₁ bank₁
  have oldCount : measurementCount (BalancedInverse.recoverParity L)=764 := by
    simpa only [BalancedInverse.recoverParity] using (BalancedCleanup.counts L.toLayout widths).2
  have freshCount : measurementCount (recoverParity w sign)=510 := by
    simpa only [recoverParity] using (BalancedCleanupOffsetZero.counts
      (OffsetCleanupBorrowedCaller.layout w sign) (OffsetCleanupBorrowedCaller.widths w sign)).2
  have align : n.drop 764=m.drop 510 := by simp [n,List.drop_append]
  have oldGuard : run [.CX L.ymsb L.sourceGuard] n s=u := guard_records _ _ n m s
  have freshRun : run (program w sign) m s=
      run (tail L) (m.drop 510) (run (recoverParity w sign) m u) := by
    rw [program,run_prefix,freshCount]
  have oldRun : run (BalancedInverse.program L) n s=
      run (tail L) (n.drop 764) (run (BalancedInverse.recoverParity L) n u) := by
    rw [old_layout,run_prefix,oldCount,oldGuard]
  rw [freshRun,oldRun,align,oracle]

/-- Complete cheaper inverse, from the actual caller invariant: phase,
centered result, native workspace, borrowed bank, and every outside-R bit. -/
theorem program_correct (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hS : s.basis sign=B)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhigh : s.basis (w 1026)=false) :
    let t := run (program w sign) m s
    t.phase=s.phase ∧
    regValue (balancedSharedPorts w sign).r t.basis=encodeWord 256 (BalancedInverse.result B R Y) ∧
    (∀a∈BalancedCircuit.work (balancedSharedPorts w sign),t.basis a=false) ∧
    (∀a∈OffsetCleanupBorrowedCaller.carry w,t.basis a=false) ∧
    t.basis (w 1026)=false ∧
    (∀a,a∉(balancedSharedPorts w sign).r → t.basis a=s.basis a) := by
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have native := BalancedInverse.program_correct (balancedSharedPorts w sign)
    (balancedSharedPorts_widths w sign) (balancedSharedPorts_nodup w sign hn own)
    B R Y hr hy s (List.replicate 254 false++m) hS hR hY
    (balancedSharedPorts_clean w sign s.basis hw hu)
  have eq := program_equiv w sign hn hsOut R Y B hr hy s m hR hY hS hw hu hhigh
  dsimp only
  rw [eq]
  refine ⟨native.1,native.2.1,native.2.2.1,?_,?_,native.2.2.2⟩
  · intro a ha
    exact (native.2.2.2 a (bank_target_away w sign hn a ha)).trans
      (OffsetCleanupBorrowedCaller.entryCarry_clean w s.basis hw a ha)
  · have high_away : w 1026∉(balancedSharedPorts w sign).r := by
      rw [balancedSharedPorts_r]
      exact arith_block_away w hn 1026 2056 256 (by omega) (by omega) (by omega)
    exact (native.2.2.2 _ high_away).trans hhigh

end ECDSAAdd.Arithmetic.OffsetBorrowedInverse
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedInverseCanonicalCell.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run BalancedInverse.program OffsetBorrowedInverse.program

def double (w : Nat → Wire) (sign : Wire) : Program :=
  [.X sign]++OffsetBorrowedInverse.program w sign++[.X sign]

def body (w : Nat → Wire) (sign effS : Wire) : Program :=
  swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y++double w sign

def cell (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig (transcriptSelectWindow b swap effS is (body w sign effS))

/-- Fresh inverse and original inverse have identical complete States,
including arbitrary input phase and independent measurement records. -/
theorem kernel_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (B : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) (s : State) (m n : List Bool)
    (hs : s.basis sign=B)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y) (he : Env w s.basis) :
    run (OffsetBorrowedInverse.program w sign) m s=
      run (BalancedInverse.program (balancedSharedPorts w sign)) n s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have fresh := OffsetBorrowedInverse.program_correct w sign hn ho R Y B hr hy s m hR hY hs
    he.1 he.2.1 he.2.2
  have old := BalancedInverse.program_correct L (balancedSharedPorts_widths w sign) nd B R Y
    hr hy s n hs hR hY (balancedSharedPorts_clean w sign s.basis he.1 he.2.1)
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) q hq
    · exact (fresh.2.2.2.2.2 q hq).trans (old.2.2.2 q hq).symm

private theorem zero_records (p : Program) (h : measurementCount p=0)
    (s : State) (m n : List Bool) : run p m s=run p n s := by
  have a := run_take p m s
  have b := run_take p n s
  rw [h,List.take_zero] at a b
  exact a.symm.trans b

/-- The control polarity wrapper preserves both selected control and phase. -/
theorem double_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (double w sign) m s=
      run ([.X sign]++BalancedInverse.program (balancedSharedPorts w sign)++[.X sign]) m s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway L nd sign (by simp [L,balancedSharedPorts])
  have sa : sign∉L.r ∧ sign∉L.y := ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have se := pair_env w sign hn base s.basis _ _ he h
  generalize eu : run [.X sign] m s=u
  have us := BalancedCleanupOffset.x_run sign s m
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ue : Env w u.basis := by
    rw [us]
    exact env_write w sign ho s.basis (!s.basis sign) se
  have ug : u.basis sign= !base sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.2.1,centerWord_decode]
  have eq := kernel_eq w sign hn ho (!base sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m m ug ur uy ue
  simp only [double,List.append_assoc]
  rw [run_append,run_take]
  change run (OffsetBorrowedInverse.program w sign++[.X sign]) m
    (run [.X sign] m s)=_
  rw [eu,run_append,run_take,eq]
  rw [run_append,run_take]
  change _=run (BalancedInverse.program L++[.X sign]) m (run [.X sign] m s)
  rw [eu,run_append,run_take]
  exact zero_records [.X sign] (by simp only [measurementCount]) _ _ _

private theorem swap_pair (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have ca : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c ca.1 ca.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

/-- Swap is executed first. Whole-State equality then reuses the original
inverse field-cell frame, without assuming a phase oracle. -/
theorem body_eq (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (body w sign effS) m s=
      run (balancedInverseTranscriptBody (balancedSharedPorts w sign) effS) m s := by
  let L := balancedSharedPorts w sign
  have len := BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)
  have sw := swap_pair L.r L.y effS (len.2.1.trans len.2.2.1.symm) hsw base
    (centerWord X) (centerWord Y) s m h
  generalize eu : run (swapRegisters effS L.r L.y) m s=u at sw
  let A := if base effS then Y else X
  let B := if base effS then X else Y
  have view : PairFrame L.r L.y base (centerWord A) (centerWord B) u.basis := by
    cases e : base effS <;> simpa only [A,B,e,Bool.false_eq_true,if_true,if_false] using sw.2
  have eq := double_eq w sign hn ho base he A B u m view
  have zero := (swapRegisters_resources effS L.r L.y (len.2.1.trans len.2.2.1.symm) hsw).2.1
  have fresh : run (body w sign effS) m s=run (double w sign) m u := by
    rw [body,run_append,run_take,zero,List.drop_zero,eu]
  have old : run (balancedInverseTranscriptBody L effS) m s=
      run ([.X sign]++BalancedInverse.program L++[.X sign]) m u := by
    simp only [balancedInverseTranscriptBody,List.append_assoc]
    rw [run_append,run_take,zero,List.drop_zero,eu]
    simp only [L,balancedSharedPorts]
  rw [fresh,old]
  exact eq

theorem body_frame (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (body w sign effS)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadUncell (base sign) (base effS) (X,Y)).1)
        (centerWord (skywalkPayloadUncell (base sign) (base effS) (X,Y)).2)) := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have old := balancedInverseTranscriptBody_frame (balancedSharedPorts w sign) effS
    (balancedSharedPorts_widths w sign) (balancedSharedPorts_nodup w sign hn own) hsw base
    (balancedSharedPorts_clean w sign base he.1 he.2.1) X Y
  intro s m h
  rw [body_eq w sign effS hn ho hsw base he X Y s m h]
  exact old s m h

theorem cell_counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hsw : (effS::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup) :
    toffoliCount (cell w b g swap sign effS ig is)=1281 ∧
    measurementCount (cell w b g swap sign effS ig is)=1025 := by
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have sw := swapRegisters_resources effS _ _ (width.2.1.trans width.2.2.1.symm) hsw
  have k := OffsetBorrowedInverse.counts w sign
  have si := transcriptSelectWindow_counts b swap effS is (body w sign effS)
  have so := transcriptSelectWindow_counts b g sign ig (transcriptSelectWindow b swap effS is (body w sign effS))
  change toffoliCount (transcriptSelectWindow b g sign ig
      (transcriptSelectWindow b swap effS is (body w sign effS)))=1281 ∧
    measurementCount (transcriptSelectWindow b g sign ig
      (transcriptSelectWindow b swap effS is (body w sign effS)))=1025
  rw [so.1,so.2,si.1,si.2]
  simp only [body,double,toffoliCount_append,measurementCount_append,
    k.1,k.2,sw.1,sw.2.1,width.2.1]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedInverseCanonicalReplay.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical
open Secp256k1 BalancedField OffsetBorrowedCanonical

private theorem selected_other (base : BasisState) (b source flag q : Wire) (v : Bool)
    (hne : q≠flag) : mixedTranscriptBase base b source flag v q=base q := by
  simp only [mixedTranscriptBase,writeBit,Function.update_of_ne hne]

/-- Both mixed selection windows clean their controls and preserve phase
for the recorded or inactive choice on every measurement record. -/
theorem cell_frame (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (cell w b g swap sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadUncell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y)).1)
        (centerWord (skywalkPayloadUncell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y)).2)) := by
  let L := balancedSharedPorts w sign
  let bg := mixedTranscriptBase base b g sign ig
  let bs := mixedTranscriptBase bg b swap effS is
  have sg : [b,g,sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [balancedSharedPorts,List.count_cons,List.count_nil] at h ⊢
    omega
  have ss : [b,swap,effS].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [balancedSharedPorts,List.count_cons,List.count_nil] at h ⊢
    omega
  have d0 := List.nodup_cons.mp hl.controls
  have d1 := List.nodup_cons.mp d0.2
  have d2 := List.nodup_cons.mp d1.2
  have d3 := List.nodup_cons.mp d2.2
  have ne : effS≠sign := Ne.symm (by simpa using d3.1)
  have bn : b≠sign := by
    have h := (List.nodup_cons.mp sg).1
    intro e; exact h (by simp [e])
  have sn : swap≠sign := by
    intro e
    exact d2.1 (by simp [balancedSharedPorts,e])
  have bgS : bg effS=false := (selected_other _ _ _ _ _ _ ne).trans hs0
  have bgB : bg b=base b := selected_other _ _ _ _ _ _ bn
  have bgSwap : bg swap=base swap := selected_other _ _ _ _ _ _ sn
  have bsG : bs sign=mixedTranscriptBit base b g ig := by
    rw [show bs sign=bg sign from selected_other _ _ _ _ _ _ (Ne.symm ne)]
    simp only [bg,mixedTranscriptBase,writeBit,Function.update_self]
  have bsS : bs effS=mixedTranscriptBit base b swap is := by
    simp only [bs,mixedTranscriptBase,writeBit,Function.update_self,mixedTranscriptBit,bgB,bgSwap]
  have ge : Env w bg := env_write w sign ho base _ he
  have se : Env w bs := env_write w effS hoS bg _ ge
  have bd := body_frame w sign effS hn ho hl.swapND bs se X Y
  rw [bsG,bsS] at bd
  have inner := transcriptSelectWindow_pairFrame b swap effS is L.r L.y ss
    (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS (centerWord X) (centerWord Y) _ _ _ bd
  exact transcriptSelectWindow_pairFrame b g sign ig L.r L.y sg
    (hl.outside b (by simp)) (hl.outside g (by simp)) (hl.outside sign (by simp [balancedSharedPorts]))
    base hg0 _ _ _ _ _ inner

/-- Arithmetic inverse cells run in reverse transcript order. No MX is reversed. -/
def replay (w : Nat → Wire) (b sign effS : Wire) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => replay w b sign effS ls++cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2

theorem replay_frame (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (replay w b sign effS ls)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).1)
        (centerWord (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).2)) := by
  induction ls generalizing X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons l ls ih =>
    let Q := skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)
    have r := ih (fun q hq => hf q (by simp [hq])) X Y
    have c := cell_frame w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn
      (balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho)
      (ho sign (by simp)) (ho effS (by simp)) base hg0 hs0 he Q.1 Q.2
    simpa only [replay,mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q] using r.seq c

theorem replay_counts (w : Nat → Wire) (b sign effS : Wire)
    (_hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) :
    toffoliCount (replay w b sign effS ls)=ls.length*1281 ∧
    measurementCount (replay w b sign effS ls)=ls.length*1025 := by
  induction ls with
  | nil => simp [replay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have hl := balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho
    have c := cell_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hl.swapND
    have r := ih (fun q hq => hf q (by simp [hq]))
    change toffoliCount (replay w b sign effS ls++
        cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2)=(ls.length+1)*1281 ∧
      measurementCount (replay w b sign effS ls++
        cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2)=(ls.length+1)*1025
    rw [toffoliCount_append,measurementCount_append,r.1,r.2,c.1,c.2]
    constructor <;> simp only [Nat.add_mul,Nat.one_mul]

end ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedInverseSharedMultiplicationReplay.lean
noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic

/-- Production emission is independent of proof arguments. The concrete
layout certificate is supplied only when proving its semantics/resources. -/
def offsetBorrowedInverseSharedReplayProgram (w : Nat → Wire) (b effG effS : Wire) : Program :=
  BalancedConvert.center (balancedSharedTargetConvert w)++
  BalancedConvert.center (balancedSharedSourceConvert w)++
  OffsetBorrowedInverseCanonical.replay w b effG effS (mixedTranscriptTape w)++
  BalancedConvert.canonical (balancedSharedTargetConvert w)++
  BalancedConvert.canonical (balancedSharedSourceConvert w)

open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedInverseSharedMultiplication.lean
noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
open Secp256k1

def offsetBorrowedInverseSharedFieldMultiplication (w : Nat → Wire) (b effG effS : Wire) : Program :=
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a ++
  offsetBorrowedInverseSharedReplayProgram w b effG effS ++
  halfInPlace (borrowedSkywalkUnary w) p

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedFieldProof.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedField
open BalancedField Secp256k1 DirectSkywalk
attribute [local irreducible] run BalancedCircuit.coreProgram TerminalParityOffset.program

private theorem scalarFacts (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sourceGuard≠L.parity ∧ L.ymsb≠L.sourceGuard ∧ L.ymsb≠L.parity ∧
    L.sign≠L.parity ∧ L.sign≠L.sourceGuard := by
  have f := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at f
  tauto

private theorem nativeWorkAway (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r := by
  intro qr
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr qr
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,BalancedCircuit.work,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.count_append,List.count_cons,List.count_nil] at h a b
  omega

private theorem offsetWorkAway (L : BalancedCleanupOffset.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.offsetCarry) : q∉L.r := by
  have data : (L.r++(L.y++(L.carry++L.offsetCarry))).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (L.allND hn)).2.1
  have dis := (List.nodup_append'.mp data).2.2
  intro h
  exact List.disjoint_left.mp dis h (List.mem_append_right _ (List.mem_append_right _ hq))

/-- Exact forward kernel with the existing caller's clean-mask invariant.
The high-source zero is derived by callerCout_clean at public call sites.
All records preserve phase; both used carry banks and every outsider return. -/
theorem program_correct (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis sign=B)
    (hr : signedRegValue (balancedSharedPorts w sign).r s.basis=X)
    (hyr : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhi : s.basis (w 1026)=false) :
    let t := run (program w sign) m s
    t.phase=s.phase ∧
    regValue (balancedSharedPorts w sign).r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    (∀q∈work w sign,t.basis q=false) ∧
    (∀q,q∉(balancedSharedPorts w sign).r → t.basis q=s.basis q) := by
  let L := balancedSharedPorts w sign
  let O := OffsetCleanupBorrowedCaller.layout w sign
  let R := halfResult (rawSum B X Y)
  let ms := m.drop (measurementCount (BalancedCircuit.coreProgram L))
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have nd : L.wires.Nodup := balancedSharedPorts_nodup w sign hn own
  have widths : L.Widths := balancedSharedPorts_widths w sign
  have clean : ∀q∈BalancedCircuit.work L,s.basis q=false :=
    balancedSharedPorts_clean w sign s.basis hw hu
  generalize ec : run (BalancedCircuit.coreProgram L) m s=c
  have core := BalancedCircuit.core_correct L widths nd B X Y hx hy s m hs hr hyr clean
  rw [ec] at core
  have facts := scalarFacts L nd
  have sgp := facts.1
  have ysg := facts.2.1
  have ypa := facts.2.2.1
  have qflag (q f : Wire) (hq : q∈L.y)
      (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : q≠f := by
    intro e
    have mem : f∈L.y := e ▸ hq
    exact BalancedCircuit.flagAway L nd f hf (by simp [mem])
  have yr (q : Wire) (hq : q∈L.y) : q∉L.r := by
    have a := BalancedCircuit.compose_raw_away L nd q (by simp [hq])
    exact fun h => a (by simp [BalancedCircuit.rawTarget,h])
  have cY : regValue L.y c.basis=encodeWord 256 Y :=
    (regValue_congr L.y c.basis s.basis (fun q hq => core.2.2.2.2.2 q (yr q hq)
      (qflag q L.parity hq (by simp)) (qflag q L.sourceGuard hq (by simp)))).trans
        (BalancedCircuit.word_encoding L.y 256 (BalancedCleanup.widths L.toLayout widths).2.2.1 s.basis Y hyr)
  have signAway : L.sign∉L.r := fun h => BalancedCircuit.flagAway L nd L.sign (by simp) (by simp [h])
  have cS : c.basis L.sign=B :=
    (core.2.2.2.2.2 L.sign signAway facts.2.2.2.1 facts.2.2.2.2).trans hs
  have extra := OffsetCleanupBorrowedCaller.forwardCarry_clean w sign hn hsOut B X Y hx hy
    s m hs hr hyr hw hu
  change ∀q∈OffsetCleanupBorrowedCaller.carry w,(run (BalancedCircuit.coreProgram L) m s).basis q=false at extra
  rw [ec] at extra
  have cout := OffsetCleanupBorrowedCaller.forwardCout_frame w sign hn hsOut s m
  change (run (BalancedCircuit.coreProgram L) m s).basis (w 1026)=s.basis (w 1026) at cout
  rw [ec] at cout
  have ccout : c.basis O.cout=false := cout.trans hhi
  have parity : originalParity (rawSum B X Y)=decide (q < |2*R-signedY B Y|) :=
    decide_eq_decide.mpr (halfResult_parity_interval B X Y hx hy)
  have oND : O.wires.Nodup := OffsetCleanupBorrowedCaller.nodup w sign hn hsOut
  have oWidths : O.Widths := OffsetCleanupBorrowedCaller.widths w sign
  have center : Centered R := (halfResult_spec _ (rawSum_bounds B X Y hx hy)).1
  have lower : c.basis O.lower=false := by
    change c.basis L.lower=false
    exact core.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean])
  have one : c.basis O.one=false := by
    change c.basis L.one=false
    exact core.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean])
  have ownCarry : ∀q∈O.carry,c.basis q=false := by
    change ∀q∈L.carry,c.basis q=false
    intro q hq
    exact core.2.2.2.2.1 q (by simp [BalancedCircuit.coreClean,hq])
  have oldcl := BalancedCleanupOffsetZero.correct O oWidths oND R Y B center hy c ms
    core.2.1 cY cS lower one ccout ownCarry extra
    (core.2.2.1.trans parity)
  have eqcl := TerminalParityOffset.correct O oWidths oND R Y B center hy c ms
    core.2.1 cY cS lower one ccout ownCarry extra
    (core.2.2.1.trans parity)
  have cl := eqcl.trans oldcl
  let d : State := ⟨c.phase,writeBit c.basis L.parity false⟩
  have dp : d.basis L.sourceGuard=s.basis L.ymsb :=
    (show d.basis L.sourceGuard=c.basis L.sourceGuard from by simp [d,writeBit,sgp]).trans core.2.2.2.1
  have dy : d.basis L.ymsb=s.basis L.ymsb := by
    have hy0 : L.ymsb∈L.y := by simp [BalancedCleanup.Layout.y]
    exact (show d.basis L.ymsb=c.basis L.ymsb from by simp [d,writeBit,ypa]).trans
      (core.2.2.2.2.2 L.ymsb (yr _ hy0) ypa ysg)
  let t : State := ⟨c.phase,writeBit d.basis L.sourceGuard false⟩
  have actual : run (program w sign) m s=t := by
    change run (BalancedCircuit.coreProgram L++(TerminalParityOffset.program O++[.CX L.ymsb L.sourceGuard])) m s=t
    rw [run_append,run_take,ec]
    change run (TerminalParityOffset.program O++[.CX L.ymsb L.sourceGuard]) ms c=t
    rw [run_append,run_take,cl]
    change run [.CX L.ymsb L.sourceGuard] _ d=t
    simp only [run]
    change ⟨c.phase,writeBit d.basis L.sourceGuard (d.basis L.sourceGuard ^^ d.basis L.ymsb)⟩=t
    rw [dp,dy,Bool.xor_self]
  have frame (q : Wire) (hq : q∉L.r) : t.basis q=s.basis q := by
    by_cases hp : q=L.parity
    · subst q
      simp only [t,d,writeBit,Function.update_of_ne (Ne.symm sgp),Function.update_self]
      exact (clean _ (by simp [BalancedCircuit.work])).symm
    by_cases hg : q=L.sourceGuard
    · subst q
      simp only [t,writeBit,Function.update_self]
      exact (clean _ (by simp [BalancedCircuit.work])).symm
    simp only [t,d,writeBit,Function.update_of_ne hg,Function.update_of_ne hp]
    exact core.2.2.2.2.2 q hq hp hg
  have nativeAway (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r := by
    exact nativeWorkAway L nd q hq
  have borrowedAway (q : Wire) (hq : q∈OffsetCleanupBorrowedCaller.carry w) : q∉L.r := by
    exact offsetWorkAway O oND q hq
  have highAway : w 1026∉L.r := by
    change w 1026∉(balancedSharedPorts w sign).r
    rw [balancedSharedPorts_r]
    exact arith_block_away w hn 1026 2056 256 (by omega) (by omega) (by omega)
  rw [actual]
  refine ⟨core.1,?_,?_,frame⟩
  · exact (regValue_congr L.r t.basis c.basis (by
      intro q hq
      have np : q≠L.parity := fun e => BalancedCircuit.flagAway L nd L.parity (by simp) (by simp [e ▸ hq])
      have ng : q≠L.sourceGuard := fun e => BalancedCircuit.flagAway L nd L.sourceGuard (by simp) (by simp [e ▸ hq])
      simp only [t,d,writeBit,Function.update_of_ne ng,Function.update_of_ne np])).trans core.2.1
  · intro q hq
    change q∈BalancedCircuit.work L++OffsetCleanupBorrowedCaller.carry w++[w 1026] at hq
    rcases List.mem_append.mp hq with hq|hq
    · rcases List.mem_append.mp hq with hq|hq
      · exact (frame q (nativeAway q hq)).trans (clean q hq)
      · exact (frame q (borrowedAway q hq)).trans (OffsetCleanupBorrowedCaller.entryCarry_clean w s.basis hw q hq)
    · have eq : q=w 1026 := by simpa using hq
      subst q
      exact (frame _ highAway).trans hhi


end ECDSAAdd.Arithmetic.OffsetBorrowedField
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedCanonicalCell.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
open Secp256k1 BalancedField
attribute [local irreducible] run BalancedCircuit.program OffsetBorrowedField.program

def body (w : Nat → Wire) (sign effS : Wire) : Program :=
  [.X sign]++OffsetBorrowedField.program w sign++[.X sign]++
    swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y

def cell (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig (transcriptSelectWindow b swap effS is (body w sign effS))

theorem kernel_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (B : Bool) (X Y : Int)
    (hx : Centered X) (hy : Centered Y) (s : State) (m n : List Bool)
    (hs : s.basis sign=B)
    (hr : signedRegValue (balancedSharedPorts w sign).r s.basis=X)
    (hyv : signedRegValue (balancedSharedPorts w sign).y s.basis=Y) (he : Env w s.basis) :
    run (OffsetBorrowedField.program w sign) m s=
      run (BalancedCircuit.program (balancedSharedPorts w sign)) n s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have fresh := OffsetBorrowedField.program_correct w sign hn ho B X Y hx hy s m hs hr hyv
    he.1 he.2.1 he.2.2
  have old := BalancedCircuit.program_correct L (balancedSharedPorts_widths w sign) nd B X Y
    hx hy s n hs hr hyv (balancedSharedPorts_clean w sign s.basis he.1 he.2.1)
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) q hq
    · exact (fresh.2.2.2 q hq).trans (old.2.2.2 q hq).symm

theorem zero_records (p : Program) (h : measurementCount p=0) (s : State) (m n : List Bool) :
    run p m s=run p n s := by
  have a := run_take p m s
  have b := run_take p n s
  rw [h,List.take_zero] at a b
  exact a.symm.trans b

/-- Whole-body equality permits reuse of the already verified half/swap
frame theorem. Different kernel record counts do not affect the unitary tail. -/
theorem body_eq (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (body w sign effS) m s=run (balancedTranscriptBody (balancedSharedPorts w sign) effS) m s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway L nd sign (by simp [L,balancedSharedPorts])
  have sa : sign∉L.r ∧ sign∉L.y := ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have se := pair_env w sign hn base s.basis _ _ he h
  generalize eu : run [.X sign] m s=u
  have us := BalancedCleanupOffset.x_run sign s m
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ue : Env w u.basis := by
    rw [us]
    exact env_write w sign ho s.basis (!s.basis sign) se
  have ug : u.basis sign= !base sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.2.1,centerWord_decode]
  have eq := kernel_eq w sign hn ho (!base sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m m ug ur uy ue
  let tail := [.X sign]++swapRegisters effS L.r L.y
  have tm : measurementCount tail=0 := by
    have sw := swapRegisters_resources effS L.r L.y
      ((BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)).2.1.trans
        (BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)).2.2.1.symm) hsw
    simp only [tail,measurementCount_append,sw.2.1,measurementCount]
  simp only [body,balancedTranscriptBody,List.append_assoc]
  change run ([.X sign]++(OffsetBorrowedField.program w sign++tail)) m s=
    run ([.X sign]++(BalancedCircuit.program L++tail)) m s
  simp only [run_append]
  simp only [run_take]
  simp only [show measurementCount [.X sign]=0 from rfl,List.drop_zero]
  rw [eu,eq]
  exact zero_records tail tm _ _ _

theorem body_frame (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (body w sign effS)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadCell (base sign) (base effS) (X,Y)).1)
        (centerWord (skywalkPayloadCell (base sign) (base effS) (X,Y)).2)) := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have old := balancedTranscriptBody_frame (balancedSharedPorts w sign) effS
    (balancedSharedPorts_widths w sign) (balancedSharedPorts_nodup w sign hn own) hsw base
    (balancedSharedPorts_clean w sign base he.1 he.2.1) X Y
  intro s m h
  rw [body_eq w sign effS hn ho hsw base he X Y s m h]
  exact old s m h

theorem cell_counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hsw : (effS::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup) :
    toffoliCount (cell w b g swap sign effS ig is)=1280 ∧
    measurementCount (cell w b g swap sign effS ig is)=1025 := by
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have sw := swapRegisters_resources effS _ _ (width.2.1.trans width.2.2.1.symm) hsw
  have k := OffsetBorrowedField.counts w sign
  have si := transcriptSelectWindow_counts b swap effS is (body w sign effS)
  have so := transcriptSelectWindow_counts b g sign ig (transcriptSelectWindow b swap effS is (body w sign effS))
  change toffoliCount (transcriptSelectWindow b g sign ig
      (transcriptSelectWindow b swap effS is (body w sign effS)))=1280 ∧
    measurementCount (transcriptSelectWindow b g sign ig
      (transcriptSelectWindow b swap effS is (body w sign effS)))=1025
  rw [so.1,so.2,si.1,si.2]
  simp only [body,toffoliCount_append,measurementCount_append,k.1,k.2,
    sw.1,sw.2.1,width.2.1]
  norm_num [toffoliCount,measurementCount]
end ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedCanonicalReplay.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
open Secp256k1 BalancedField

theorem cell_frame (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (cell w b g swap sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadCell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y)).1)
        (centerWord (skywalkPayloadCell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y)).2)) := by
  let bg := mixedTranscriptBase base b g sign ig
  let bs := mixedTranscriptBase bg b swap effS is
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ss : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have ne : effS≠sign := Ne.symm (by tauto)
  have bn : b≠sign := by tauto
  have sn : swap≠sign := by tauto
  have bgS : bg effS=false := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne ne,hs0]
  have bgB : bg b=base b := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne bn]
  have bgSwap : bg swap=base swap := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne sn]
  have bsG : bs sign=mixedTranscriptBit base b g ig := by
    simp only [bs,bg,mixedTranscriptBase,writeBit,Function.update_of_ne (Ne.symm ne),Function.update_self]
  have bsS : bs effS=mixedTranscriptBit base b swap is := by
    simp only [bs,mixedTranscriptBase,writeBit,Function.update_self,mixedTranscriptBit,bgB,bgSwap]
  have ge : Env w bg := env_write w sign ho base _ he
  have se : Env w bs := env_write w effS hoS bg _ ge
  have bd := body_frame w sign effS hn ho hl.swapND bs se X Y
  rw [bsG,bsS] at bd
  have inner := transcriptSelectWindow_pairFrame b swap effS is _ _ ss
    (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS (centerWord X) (centerWord Y) _ _ _ bd
  -- The public selection wrapper needs both-word exclusion, supplied by hl.
  exact transcriptSelectWindow_pairFrame b g sign ig _ _ sg
    (hl.outside b (by simp)) (hl.outside g (by simp)) (hl.outside sign (by simp [balancedSharedPorts]))
    base hg0 _ _ _ _ _ inner

def replay (w : Nat → Wire) (b sign effS : Wire) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2++replay w b sign effS ls

theorem replay_frame (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (replay w b sign effS ls)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1)
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2)) := by
  induction ls generalizing X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons l ls ih =>
    let next := skywalkPayloadCell (mixedTranscriptBit base b l.1.1 l.2.1)
      (mixedTranscriptBit base b l.1.2 l.2.2) (X,Y)
    have c := cell_frame w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn
      (balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho)
      (ho sign (by simp)) (ho effS (by simp)) base hg0 hs0 he X Y
    have r := ih (fun q hq => hf q (by simp [hq])) next.1 next.2
    simpa only [replay,mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,next] using c.seq r

theorem replay_counts (w : Nat → Wire) (b sign effS : Wire)
    (_hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) :
    toffoliCount (replay w b sign effS ls)=ls.length*1280 ∧
    measurementCount (replay w b sign effS ls)=ls.length*1025 := by
  induction ls with
  | nil => simp [replay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have hl := balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho
    have c := cell_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hl.swapND
    have r := ih (fun q hq => hf q (by simp [hq]))
    simp only [replay,toffoliCount_append,measurementCount_append,c.1,c.2,r.1,r.2,List.length_cons,Nat.add_mul]
    omega

end ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedSharedEmission.lean
noncomputable section
namespace ECDSAAdd.Arithmetic

/-- Proof-independent emission on the original shared point-addition ports. -/
def offsetBorrowedSharedReplayProgram (w : Nat → Wire) (b effG effS : Wire) : Program :=
  BalancedConvert.center (balancedSharedTargetConvert w)++
  BalancedConvert.center (balancedSharedSourceConvert w)++
  OffsetBorrowedCanonical.replay w b effG effS (mixedTranscriptTape w)++
  BalancedConvert.canonical (balancedSharedTargetConvert w)++
  BalancedConvert.canonical (balancedSharedSourceConvert w)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedSharedDivisionBridge.lean
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
open Secp256k1
attribute [local irreducible] run

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedSharedDivision.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Exact cheaper Stage 2 field division: the original doubling and XOR clear
surround the concrete balanced replay emission. -/
def offsetBorrowedSharedFieldDivision (w : Nat → Wire) (b effG effS : Wire) : Program :=
  dblInPlace (borrowedSkywalkUnary w) p ++
  offsetBorrowedSharedReplayProgram w b effG effS ++
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedDirectArithmetic.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic
open Secp256k1 DirectSkywalk

attribute [local irreducible] skywalkSeed skywalkUnseed literalSkywalkSeed literalSkywalkUnseed
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run
attribute [local irreducible] offsetBorrowedSharedFieldDivision offsetBorrowedInverseSharedFieldMultiplication
attribute [local irreducible] SkywalkTrace.next Nat.iterate

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactOffsetCallerStates.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1 DirectSkywalk

/-- Compact caller changes only the two integer computational passes. Seed, actual
terminal clear/restore, field replay and physical ports remain those of the caller. -/
def compactOffsetCallerArithmetic (divide : Bool) (w : Nat → Wire) (b effG effS : Wire) : Program :=
  literalSkywalkSeed (literalSkywalkPoolSeed w) p ++
  (compactSkywalkForward w 0 512 ++
  (skywalkArithmeticClear w ++
  ((if divide then offsetBorrowedSharedFieldDivision w b effG effS
      else offsetBorrowedInverseSharedFieldMultiplication w b effG effS) ++
  (skywalkArithmeticClear w ++
  (compactSkywalkReverse w 0 512 ++ literalSkywalkUnseed (literalSkywalkPoolSeed w) p)))))

attribute [local irreducible] skywalkSeed skywalkUnseed literalSkywalkSeed literalSkywalkUnseed
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] compactSkywalkForward compactSkywalkReverse run
attribute [local irreducible] offsetBorrowedSharedFieldDivision offsetBorrowedInverseSharedFieldMultiplication
attribute [local irreducible] SkywalkTrace.next Nat.iterate

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactOffsetCallerArithmetic.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1 DirectSkywalk
attribute [local irreducible] run compactSkywalkForward compactSkywalkReverse

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ZeroSeededConstantCompare.lean
noncomputable section
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.ZeroSeededConstantCompare

def prepare (x c : Wire) : Program := [.X c,.CX x c]
def release (x c : Wire) : Program := [.CX x c,.X c]

def program : List Wire → List Wire → Wire → Wire → Program
  | x::x'::xs,c::cs,_,target =>
      prepare x c++compareConstantLt (x'::xs) cs c target 0++release x c
  | [x],_,_,target => prepare x target
  | _,_,_,_ => []

theorem counts (xs carry : List Wire) (cin target : Wire)
    (hc : carry.length+1=xs.length) :
    toffoliCount (program xs carry cin target)=xs.length-1 ∧
    measurementCount (program xs carry cin target)=xs.length-2 := by
  cases xs with
  | nil => simp at hc
  | cons x xs =>
    cases xs with
    | nil => simp [program,prepare,toffoliCount,measurementCount]
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have h := compareConstantLt_counts (x'::xs) cs c target 0 (by simpa using hc)
        simp only [program,toffoliCount_append,measurementCount_append,h.1,h.2]
        simp [prepare,release,toffoliCount,measurementCount]

private theorem prepare_support (x cin c : Wire) :
    wires (prepare x c) ⊆ wires (constantBorrow true x cin c) := by
  intro q hq
  simp [prepare,constantBorrow,mappedMajority,wires,Instr.wires] at hq ⊢
  tauto

private theorem release_support (x cin c : Wire) :
    wires (release x c) ⊆ wires (constantBorrow true x cin c) := by
  intro q hq
  simp [release,constantBorrow,mappedMajority,wires,Instr.wires] at hq ⊢
  tauto

theorem support (xs carry : List Wire) (cin target : Wire) :
    wires (program xs carry cin target) ⊆
      wires (compareConstantLt xs carry cin target 1) := by
  cases xs with
  | nil => simp [program,compareConstantLt,wires]
  | cons x rest =>
    cases rest with
    | nil => exact prepare_support x cin target
    | cons x' rest =>
      cases carry with
      | nil => simp [program,compareConstantLt,wires]
      | cons c cs =>
        intro q hq
        have p := prepare_support x cin c
        have r := release_support x cin c
        simp only [program,compareConstantLt,Nat.one_mod,
          show 1/2=0 from rfl,decide_true,wires_append,Finset.mem_union] at hq ⊢
        have hp : q∈wires (prepare x c) → q∈wires (constantBorrow true x cin c) := fun h => p h
        have hr : q∈wires (release x c) → q∈wires (constantBorrow true x cin c) := fun h => r h
        tauto

end ECDSAAdd.Arithmetic.ZeroSeededConstantCompare
end

-- source: ECDSAAdd/Arithmetic/DirectZeroDivisor.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Replace the zero divisor by one while retaining the original-zero flag.
The literal comparator uses n-1 borrow scratch bits and no constant register. -/
def directZeroDivisorEnter (xs carry : List Wire) (cin flag : Wire) : Program :=
  ZeroSeededConstantCompare.program xs carry cin flag ++ maskedConstant flag xs 1

/-- The caller returns the repaired word unchanged; other caller coordinates
may have changed. Undo the repair before uncomputing the original-zero flag. -/
def directZeroDivisorLeave (xs carry : List Wire) (cin flag : Wire) : Program :=
  maskedConstant flag xs 1 ++ ZeroSeededConstantCompare.program xs carry cin flag

theorem directZeroDivisor_counts (xs carry : List Wire) (cin flag : Wire)
    (hc : carry.length+1=xs.length) :
    toffoliCount (directZeroDivisorEnter xs carry cin flag)=xs.length-1 ∧
    measurementCount (directZeroDivisorEnter xs carry cin flag)=xs.length-2 ∧
    toffoliCount (directZeroDivisorLeave xs carry cin flag)=xs.length-1 ∧
    measurementCount (directZeroDivisorLeave xs carry cin flag)=xs.length-2 := by
  have cmp := ZeroSeededConstantCompare.counts xs carry cin flag hc
  have mask := maskedConstant_counts flag xs 1
  simp [directZeroDivisorEnter,directZeroDivisorLeave,toffoliCount_append,
    measurementCount_append,cmp.1,cmp.2,mask.1,mask.2]

private theorem directBorrow_wires (bit : Bool) (x cin target : Wire) :
    wires (constantBorrow bit x cin target) ⊆ [target,cin,x].toFinset ∧
    wires (constantBorrowErase bit x cin target) ⊆ [target,cin,x].toFinset := by
  cases bit <;>
    simp [constantBorrow,constantBorrowErase,mappedMajority,mappedEraseCarry,
      wires,Instr.wires,correctionWires,Finset.subset_iff]

private theorem directCompare_wires (xs carry : List Wire) (cin target : Wire) (k : Nat) :
    wires (compareConstantLt xs carry cin target k) ⊆ (target::cin::(xs++carry)).toFinset := by
  induction xs generalizing carry cin k with
  | nil => simp [compareConstantLt,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      intro q hq
      have h := (directBorrow_wires (decide (k%2=1)) x cin target).1 hq
      simpa only [List.mem_toFinset,List.mem_cons,List.mem_singleton,List.mem_append,
        List.not_mem_nil,or_false] using
        (show q=target ∨ q=cin ∨ q=x ∨ q∈carry from by
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h; tauto)
    | cons x' xs =>
      cases carry with
      | nil => simp [compareConstantLt,wires]
      | cons c cs =>
        intro q hq
        simp only [compareConstantLt,wires_append,Finset.mem_union] at hq
        rcases hq with (hq|hq)|hq
        · have h := (directBorrow_wires (decide (k%2=1)) x cin c).1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append]; tauto
        · have h := ih cs c (k/2) hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
        · have h := (directBorrow_wires (decide (k%2=1)) x cin c).2 hq
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append]; tauto

/-- Static support of both halves lies within the declared word, borrow
scratch, cin and one flag. There is no materialized constant register. -/
theorem directZeroDivisor_wires (xs carry : List Wire) (cin flag : Wire) :
    wires (directZeroDivisorEnter xs carry cin flag ++
      directZeroDivisorLeave xs carry cin flag) ⊆ (flag::cin::(xs++carry)).toFinset := by
  intro q hq
  simp only [directZeroDivisorEnter,directZeroDivisorLeave,wires_append,
    Finset.mem_union] at hq
  have cmp : wires (ZeroSeededConstantCompare.program xs carry cin flag) ⊆
      (flag::cin::(xs++carry)).toFinset := by
    intro q hq
    exact directCompare_wires xs carry cin flag 1
      (ZeroSeededConstantCompare.support xs carry cin flag hq)
  have mask := maskedConstant_wires_subset flag xs 1
  rcases hq with (hq|hq)|(hq|hq)
  · exact cmp hq
  · have h := mask hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
  · have h := mask hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
  · exact cmp hq

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DirectZeroControlled.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Zero repair around a numerator-only kernel, without a backup divisor. -/
def directZeroControlled (xs carry : List Wire) (cin flag : Wire) (kernel : Program) : Program :=
  directZeroDivisorEnter xs carry cin flag ++
    (kernel ++ directZeroDivisorLeave xs carry cin flag)

/-- Exact emitted cost of the complete zero-repair wrapper. -/
theorem directZeroControlled_counts (xs carry : List Wire) (cin flag : Wire) (kernel : Program)
    (hc : carry.length+1=xs.length) :
    toffoliCount (directZeroControlled xs carry cin flag kernel)=toffoliCount kernel+2*(xs.length-1) ∧
    measurementCount (directZeroControlled xs carry cin flag kernel)=
      measurementCount kernel+2*(xs.length-2) := by
  have h := directZeroDivisor_counts xs carry cin flag hc
  simp only [directZeroControlled,toffoliCount_append,measurementCount_append,
    h.1,h.2.1,h.2.2.1,h.2.2.2]
  omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ReplayLoop.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 十位计数器的比较 scratch 借用载荷格的零工作区。 -/
structure ReplayLayout where
  payload : ModInPlaceLayout
  counter : AdderLayout
  active : Wire

namespace ReplayLayout

end ReplayLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ReplayRoundProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace ReplayState

end ReplayState


end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ReplayLoopProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/ValueWalk.lean
noncomputable section

namespace ECDSAAdd

/-- 值走只保留欧几里得数据与活动计数，不分配整数系数字。 -/
@[ext] structure ValueState where
  u : Nat
  v : Nat
  k : Nat
  deriving DecidableEq

def KState.value (z : KState) : ValueState := ⟨z.u,z.v,z.k⟩
def valueInit (p x : Nat) : ValueState := ⟨p,x,0⟩

def valueCode (z : ValueState) : Bool × Bool :=
  if z.v=0 then (false,false)
  else if z.u%2=0 then (false,false)
  else if z.v%2=0 then (true,false)
  else if z.v<z.u then (false,true)
  else (true,true)

@[simp] theorem valueInit_projection (p x : Nat) :
    (kaliskiInit p x).value=valueInit p x := rfl
@[simp] theorem valueCode_projection (z : KState) :
    valueCode z.value=kaliskiCode z := rfl

/-- Per-round width envelope of the value walk: full width w early on, then 512−i from the product bound, at least 2 bits. -/
def valueWidth (w i : Nat) : Nat := min w (max 2 (512-i))

end ECDSAAdd
end

-- source: ECDSAAdd/Math/ValueReplay.lean
noncomputable section

namespace ECDSAAdd
open Secp256k1

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/ReplayField.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/ValueTrace.lean
noncomputable section

namespace ECDSAAdd

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/DialogReplayMath.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ReplayLoopResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueBody.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 旧布局中的r/s/out不属于值走门列的支持，保持其原值。 -/
def valueBodyProgram (L : RoundDataLayout) (active swap subtract : Wire) : Program :=
  swapRegisters swap L.u L.v ++ inplaceArithmetic L .u .v subtract true ++
  shiftRight active L.u ++ swapRegisters swap L.u L.v

def valueUnbodyProgram (L : RoundDataLayout) (active swap subtract : Wire) : Program :=
  swapRegisters swap L.u L.v ++ shiftLeft active L.u ++
  inplaceArithmetic L .u .v subtract false ++ swapRegisters swap L.u L.v

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueRound.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 两位记录轮沿用原控制段，只以值走体替换原四字算术体。 -/
def valueRound (L : KaliskiRoundLayout) (i : Nat) : Program :=
  loadActive L ++ recordRound L ++ valueBodyProgram L.data L.active L.swap L.subtract ++
  counterInc L.counter ++ zeroControlled L.active L.done (L.data.zeroBits .v) ++ roundActiveXor L i

def valueUnround (L : KaliskiRoundLayout) (i : Nat) : Program :=
  roundActiveXor L i ++ zeroControlled L.active L.done (L.data.zeroBits .v) ++
  valueUnbodyProgram L.data L.active L.swap L.subtract ++ counterDec L.counter.swapCounter ++
  recordRound L ++ loadActive L

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWires.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

def RoundBit.valueUsedWires (b : RoundBit) : List Wire := [b.u,b.v,b.y,b.carry,b.zero]
def RoundDataLayout.valueUsedWires (L : RoundDataLayout) : List Wire :=
  L.cin :: L.bits.flatMap RoundBit.valueUsedWires
def KaliskiRoundLayout.valueUsedWires (L : KaliskiRoundLayout) : List Wire :=
  [L.done,L.swap,L.subtract,L.oddWork,L.bothWork,L.compareCin] ++ L.data.valueUsedWires ++ L.counter.wires

private theorem swap_wires_ValueWires (c : Wire) (a b : List Wire) (hlen : a.length=b.length) (hpos : 0<a.length) :
    wires (swapRegisters c a b)=(c::(a++b)).toFinset ∧
    wires (exchangeRegisters a b)=(a++b).toFinset := by
  have hae : a.isEmpty=false := by cases a <;> simp_all
  have hbe : b.isEmpty=false := by cases b <;> simp_all
  have ha := copyRegister_wires (some c) a b hlen
  have hb := copyRegister_wires none b a hlen.symm
  have hc := copyRegister_wires none a b hlen
  simp only [hae,hbe,Bool.false_eq_true,if_false] at ha hb hc
  constructor <;> ext w <;>
    simp only [swapRegisters,exchangeRegisters,wires_append,ha,hb,hc,Finset.mem_union,List.mem_toFinset,
      List.mem_cons,List.mem_append,Option.toList_some,Option.toList_none,List.mem_nil_iff,or_false,false_or] <;> tauto

private theorem inplace_wires_ValueWires (L : RoundDataLayout) (f g : RoundField) (c : Wire) (neg : Bool)
    (hw : 0<L.width) :
    wires (inplaceArithmetic L f g c neg)=
      (c::L.cin::(L.reg g++L.reg .y++L.reg f++(L.reg .carry).take (L.width-1))).toFinset := by
  have hm := measuredMaskedInPlace_wires c (L.reg g) (L.reg .y) (L.reg f)
    ((L.reg .carry).take (L.width-1)) L.cin
    (by simp [L.reg_length]) (by simp [L.reg_length]) (by simp [L.reg_length]; omega)
  cases neg <;> simp only [inplaceArithmetic,Bool.false_eq_true,if_false,if_true] <;> tauto

private def bodyWires_ValueWires (L : RoundDataLayout) (a sw su : Wire) : Finset Wire :=
  ([a,sw,su,L.cin]++L.u++L.v++L.reg .y++(L.reg .carry).take (L.width-1)).toFinset

private theorem body_wires_ValueWires (L : RoundDataLayout) (a sw su : Wire) (hw : 2≤L.width) :
    wires (valueBodyProgram L a sw su)=bodyWires_ValueWires L a sw su ∧
    wires (valueUnbodyProgram L a sw su)=bodyWires_ValueWires L a sw su := by
  have hp : 0<L.width := by omega
  have huv := (swap_wires_ValueWires sw L.u L.v (by simp [RoundDataLayout.u,RoundDataLayout.v,L.reg_length])
    (by simpa [RoundDataLayout.u,L.reg_length] using hp)).1
  have hru := shift_wires a L.u
  have hu : ¬L.u.length<2 := by simpa [RoundDataLayout.u,L.reg_length] using (show ¬L.width<2 by omega)
  simp only [hu,if_false] at hru
  have hiU := inplace_wires_ValueWires L .u .v su true hp
  have hiUi := inplace_wires_ValueWires L .u .v su false hp
  constructor <;>
    simp only [valueBodyProgram,valueUnbodyProgram,wires_append,
      huv,hru.1,hru.2,hiU,hiUi]
  all_goals
    ext w
    simp only [bodyWires_ValueWires,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_nil_iff,
      RoundDataLayout.u,RoundDataLayout.v]
    clear huv hru hiU hiUi hu hp hw
    tauto

private theorem data_interface_ValueWires (L : RoundDataLayout) :
    L.valueUsedWires.toFinset=(L.cin::(L.u++L.v++L.reg .y++L.reg .carry++L.reg .zero)).toFinset := by
  ext w
  simp [RoundDataLayout.valueUsedWires,RoundDataLayout.u,RoundDataLayout.v,
    RoundDataLayout.reg,RoundBit.valueUsedWires,RoundBit.get,and_or_left,exists_or,eq_comm]

private theorem zero_interface_ValueWires (L : RoundDataLayout) :
    ((L.zeroBits .v).flatMap ZeroBit.wires).toFinset=(L.v++L.reg .zero).toFinset := by
  ext w
  simp [RoundDataLayout.zeroBits,ZeroBit.wires,RoundDataLayout.v,RoundDataLayout.reg,
    RoundBit.get,and_or_left,exists_or,eq_comm]

private theorem activity_wires_ValueWires (L : KaliskiRoundLayout) (i : Nat) :
    wires (roundActiveXor L i)=(L.active::L.compareCin::
      (L.comparator.x++L.comparator.y++L.comparator.carry)).toFinset := by
  exact counterActiveXor_wires L.comparator L.active i

/-- 静态线路并集恰好等于单轮布局，包括共享工作线而非“最大同时存活”估计。 -/
theorem valueRound_wires (L : KaliskiRoundLayout) (hw : L.counter.width=10)
    (hd : 2≤L.data.width) (i : Nat) :
    wires (valueRound L i)=L.valueUsedWires.toFinset ∧ wires (valueUnround L i)=L.valueUsedWires.toFinset := by
  have hb := body_wires_ValueWires L.data L.active L.swap L.subtract hd
  have hr := recordRound_wires L
  have ha := activity_wires_ValueWires L i
  have hz := zeroControlled_wires L.active L.done (L.data.zeroBits .v)
  have hc := (counterMove_wires L.counter hw).1
  have hci := (counterMove_wires L.counter.swapCounter (L.counter.swapCounter_fields.2.2.2.2.2.trans hw)).2
  have hcp : L.counter.swapCounter.wires.toFinset=L.counter.wires.toFinset := by
    ext w
    simpa only [List.mem_toFinset] using L.counter.swapCounter_perm.mem_iff (a:=w)
  rw [hcp] at hci
  have hl : wires (loadActive L)=[L.active,L.done].toFinset := by
    ext w; simp [loadActive,wires,Instr.wires,or_comm]
  have hdata := data_interface_ValueWires L.data
  have hzero := zero_interface_ValueWires L.data
  constructor <;>
    simp only [valueRound,valueUnround,wires_append,hl,hr,ha,hb.1,hb.2,hz,hc,hci]
  all_goals
    ext w
    have hD := (congrArg (fun s => w∈s) hdata).to_iff
    have hZ := (congrArg (fun s => w∈s) hzero).to_iff
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hD hZ
    have hcomp : ∀ w, w∈L.comparator.x++L.comparator.y++L.comparator.carry → w∈L.counter.wires := by
      intro w hm
      have hf := L.counter.swapCounter_perm.mem_iff (a:=w)
      have ht : w∈L.counter.swapCounter.wires := by
        simp only [List.mem_append] at hm
        rcases hm with (h|h)|h
        · exact L.counter.swapCounter.reg_subset.1 h
        · exact L.counter.swapCounter.reg_subset.2.1 h
        · exact L.counter.swapCounter.reg_subset.2.2.2 h
      exact hf.mp ht
    have hcm := hcomp w
    simp only [List.mem_append] at hcm
    have hac : w=L.active → w∈L.counter.wires := fun he => he ▸ List.mem_cons_self
    have htake : w∈(L.data.reg .carry).take (L.data.width-1) → w∈L.data.reg .carry :=
      fun h => List.mem_of_mem_take h
    simp only [bodyWires_ValueWires,KaliskiRoundLayout.valueUsedWires,Finset.mem_union,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.mem_nil_iff,hD,hZ]
    simp only [KaliskiRoundLayout.u,KaliskiRoundLayout.v,RoundDataLayout.u,RoundDataLayout.v,
      ] at *
    clear hb hr ha hz hc hci hcp hl hdata hzero hD hZ
    aesop

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueNarrow.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-! Value-walk width envelope: a round runs only on the first m data bits. The dropped high bits are not
in the gate support and are preserved wire by wire; u/v high bits are zero by the width
envelope, r/s high bits keep their values. -/

namespace KaliskiRoundLayout

/-- Narrow view: keep only the first m data bits; counter, control and record wires are unchanged. -/
def narrow (L : KaliskiRoundLayout) (m : Nat) : KaliskiRoundLayout :=
  { L with low := (L.low++[L.high]).take (m-1), high := (L.low++[L.high]).getD (m-1) L.high }

private theorem take_getD {α : Type} (l : List α) (n : Nat) (d : α) (h : n<l.length) :
    l.take n++[l.getD n d]=l.take (n+1) := by
  rw [List.take_add_one,List.getElem?_eq_getElem h,List.getD_eq_getElem _ _ h]
  rfl

theorem narrow_data (L : KaliskiRoundLayout) (m : Nat) (h1 : 1≤m) (hm : m≤L.data.width) :
    (L.narrow m).data=⟨L.data.bits.take m,L.data.cin⟩ := by
  have hlt : m-1<(L.low++[L.high]).length := by
    simp only [data,RoundDataLayout.width] at hm; omega
  simp only [narrow,data]
  rw [take_getD _ _ _ hlt,Nat.sub_add_cancel h1]

theorem narrow_width (L : KaliskiRoundLayout) (m : Nat) (h1 : 1≤m) (hm : m≤L.data.width) :
    (L.narrow m).data.width=m := by
  rw [narrow_data L m h1 hm]
  simp only [RoundDataLayout.width,List.length_take]
  exact min_eq_left hm

theorem narrow_full (L : KaliskiRoundLayout) : L.narrow L.data.width=L := by
  cases L
  simp [narrow,data,RoundDataLayout.width]

end KaliskiRoundLayout

namespace RoundDataLayout

end RoundDataLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueLoopResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 两位记录逐轮独占；共享字与计数银行交替复用。 -/
-- Width envelope: round i runs only on the low `valueWidth L.data.width i` data bits.
def valueLoop (L : KaliskiRoundLayout) (i : Nat) : List RoundRecord → Program
  | [] => []
  | r::rs => valueRound ((L.withRecord r).narrow (valueWidth L.data.width i)) i ++
      valueLoop L.swapCounter (i+1) rs

def valueUnloop (L : KaliskiRoundLayout) (i : Nat) : List RoundRecord → Program
  | [] => []
  | r::rs => valueUnloop L.swapCounter (i+1) rs ++
      valueUnround ((L.withRecord r).narrow (valueWidth L.data.width i)) i

theorem valueWidth_bounds (w i : Nat) (hd : 2≤w) : 2≤valueWidth w i ∧ valueWidth w i≤w := by
  simp only [valueWidth]
  omega

theorem valueWidth_full (w i : Nat) (hd : 2≤w) (hi : i+w≤512) : valueWidth w i=w := by
  simp only [valueWidth]
  omega

def KaliskiRoundLayout.valueSharedWires (L : KaliskiRoundLayout) : List Wire :=
  [L.done,L.oddWork,L.bothWork,L.compareCin]++L.data.valueUsedWires++L.counter.wires

def KaliskiRoundLayout.valueTapeWires (L : KaliskiRoundLayout) (rs : List RoundRecord) : List Wire :=
  rs.flatMap RoundRecord.wires++L.valueSharedWires

private theorem usedRecord_perm_ValueLoopResources (L : KaliskiRoundLayout) (r : RoundRecord) :
    (L.withRecord r).valueUsedWires.Perm (r.wires++L.valueSharedWires) := by
  apply List.perm_iff_count.mpr
  intro w
  simp [KaliskiRoundLayout.valueUsedWires,KaliskiRoundLayout.withRecord,KaliskiRoundLayout.valueSharedWires,
    RoundRecord.wires,List.count_cons,KaliskiRoundLayout.data,KaliskiRoundLayout.counter]
  omega

private theorem usedShared_swap_ValueLoopResources (L : KaliskiRoundLayout) :
    L.swapCounter.valueSharedWires.Perm L.valueSharedWires := by
  change (_++L.swapCounter.data.valueUsedWires++L.swapCounter.counter.wires).Perm
    (_++L.data.valueUsedWires++L.counter.wires)
  rw [L.swapCounter_data,L.swapCounter_counter]
  exact List.Perm.append_left _ L.counter.swapCounter_perm

/-- A narrowed round touches a subset of the full-width round support; record and control wires are unchanged. -/
private theorem narrow_used_sublist (L : KaliskiRoundLayout) (m : Nat) (h1 : 1≤m) (hm : m≤L.data.width) :
    (L.narrow m).valueUsedWires.Sublist L.valueUsedWires := by
  have hd : (L.narrow m).data.valueUsedWires.Sublist L.data.valueUsedWires := by
    rw [L.narrow_data m h1 hm]
    apply List.Sublist.cons₂
    conv_rhs => rw [← List.take_append_drop m L.data.bits]
    rw [List.flatMap_append]
    exact List.sublist_append_left _ _
  exact (hd.append_left _).append_right _

/-- Support of the narrowed round i: contained in the full-width round support and covering both record wires of the round. -/
theorem valueNarrowRound_wires (L : KaliskiRoundLayout) (r : RoundRecord) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) :
    (wires (valueRound ((L.withRecord r).narrow (valueWidth L.data.width i)) i)=
        ((L.withRecord r).narrow (valueWidth L.data.width i)).valueUsedWires.toFinset ∧
      wires (valueUnround ((L.withRecord r).narrow (valueWidth L.data.width i)) i)=
        ((L.withRecord r).narrow (valueWidth L.data.width i)).valueUsedWires.toFinset) ∧
    ((L.withRecord r).narrow (valueWidth L.data.width i)).valueUsedWires.toFinset ⊆
        (L.withRecord r).valueUsedWires.toFinset ∧
    (r.wires).toFinset ⊆ ((L.withRecord r).narrow (valueWidth L.data.width i)).valueUsedWires.toFinset := by
  have hb := valueWidth_bounds L.data.width i hd
  have hnd : 2≤((L.withRecord r).narrow (valueWidth L.data.width i)).data.width := by
    rw [(L.withRecord r).narrow_width _ (by omega) hb.2]; exact hb.1
  refine ⟨valueRound_wires ((L.withRecord r).narrow (valueWidth L.data.width i)) hw hnd i,?_,?_⟩
  · intro w hm
    exact List.mem_toFinset.mpr ((narrow_used_sublist (L.withRecord r) _ (by omega) hb.2).subset
      (List.mem_toFinset.mp hm))
  · intro w hm
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,RoundRecord.wires,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- Any start round: loop support is contained in the shared layout plus the record tape, and touches every record wire. -/
theorem valueLoop_wires_subset (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) :
    (wires (valueLoop L i rs)⊆(L.valueTapeWires rs).toFinset ∧
      wires (valueUnloop L i rs)⊆(L.valueTapeWires rs).toFinset) ∧
    ((rs.flatMap RoundRecord.wires).toFinset⊆wires (valueLoop L i rs) ∧
      (rs.flatMap RoundRecord.wires).toFinset⊆wires (valueUnloop L i rs)) := by
  induction rs generalizing L i with
  | nil => simp [valueLoop,valueUnloop,wires]
  | cons r rs ih =>
    have hr := valueNarrowRound_wires L r i hw hd
    have hp : (L.withRecord r).valueUsedWires.toFinset ⊆ (r.wires++L.valueSharedWires).toFinset := by
      intro w hm
      exact List.mem_toFinset.mpr ((usedRecord_perm_ValueLoopResources L r).mem_iff.mp (List.mem_toFinset.mp hm))
    have hnw : L.swapCounter.counter.width=10 := by rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := ih L.swapCounter (i+1) hnw hd
    have hs : L.swapCounter.valueSharedWires.toFinset=L.valueSharedWires.toFinset := by
      ext w; simpa only [List.mem_toFinset] using (usedShared_swap_ValueLoopResources L).mem_iff (a:=w)
    have htape : (L.swapCounter.valueTapeWires rs).toFinset ⊆ (L.valueTapeWires (r::rs)).toFinset := by
      intro w hm
      simp only [KaliskiRoundLayout.valueTapeWires,List.toFinset_append,Finset.mem_union,hs] at hm ⊢
      simp only [List.flatMap_cons,List.toFinset_append,Finset.mem_union]
      tauto
    have hhead : (r.wires++L.valueSharedWires).toFinset ⊆ (L.valueTapeWires (r::rs)).toFinset := by
      intro w hm
      simp only [KaliskiRoundLayout.valueTapeWires,List.flatMap_cons,List.toFinset_append,
        Finset.mem_union] at hm ⊢
      tauto
    simp only [valueLoop,valueUnloop,wires_append,hr.1.1,hr.1.2]
    refine ⟨⟨Finset.union_subset ((hr.2.1.trans hp).trans hhead) (ht.1.1.trans htape),
      Finset.union_subset (ht.1.2.trans htape) ((hr.2.1.trans hp).trans hhead)⟩,?_,?_⟩
    · intro w hm
      simp only [List.flatMap_cons,List.toFinset_append,Finset.mem_union] at hm
      rcases hm with hm|hm
      · exact Finset.mem_union_left _ (hr.2.2 hm)
      · exact Finset.mem_union_right _ (ht.2.1 hm)
    · intro w hm
      simp only [List.flatMap_cons,List.toFinset_append,Finset.mem_union] at hm
      rcases hm with hm|hm
      · exact Finset.mem_union_right _ (hr.2.2 hm)
      · exact Finset.mem_union_left _ (ht.2.2 hm)

/-- 空循环没有线路；非空循环恰好使用共享布局和整个两位记录带。 -/
-- With the width envelope, the equality needs a full-width first round (`i+L.data.width≤512`).
theorem valueLoop_wires (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) (hi : i+L.data.width≤512) :
    wires (valueLoop L i rs)=(if rs.isEmpty then ∅ else (L.valueTapeWires rs).toFinset) ∧
    wires (valueUnloop L i rs)=(if rs.isEmpty then ∅ else (L.valueTapeWires rs).toFinset) := by
  cases rs with
  | nil => simp [valueLoop,valueUnloop,wires]
  | cons r rs =>
    have hfull : (L.withRecord r).narrow (valueWidth L.data.width i)=L.withRecord r := by
      rw [valueWidth_full _ _ hd hi]
      exact (L.withRecord r).narrow_full
    have hr := valueRound_wires (L.withRecord r) hw hd i
    have hnw : L.swapCounter.counter.width=10 := by rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := valueLoop_wires_subset L.swapCounter rs (i+1) hnw hd
    have hp : (L.withRecord r).valueUsedWires.toFinset=(r.wires++L.valueSharedWires).toFinset := by
      ext w; simpa only [List.mem_toFinset] using (usedRecord_perm_ValueLoopResources L r).mem_iff (a:=w)
    have hs : L.swapCounter.valueSharedWires.toFinset=L.valueSharedWires.toFinset := by
      ext w; simpa only [List.mem_toFinset] using (usedShared_swap_ValueLoopResources L).mem_iff (a:=w)
    have htape : (L.swapCounter.valueTapeWires rs).toFinset=
        (rs.flatMap RoundRecord.wires).toFinset ∪ L.valueSharedWires.toFinset := by
      simp only [KaliskiRoundLayout.valueTapeWires,List.toFinset_append,hs]
    rw [htape] at ht
    simp only [valueLoop,valueUnloop,wires_append,hfull,hr.1,hr.2,hp,List.isEmpty_cons,
      Bool.false_eq_true,if_false,KaliskiRoundLayout.valueTapeWires,List.flatMap_cons,List.toFinset_append]
    obtain ⟨⟨h1,h2⟩,h3,h4⟩ := ht
    generalize wires (valueLoop L.swapCounter (i+1) rs)=T1 at h1 h3 ⊢
    generalize wires (valueUnloop L.swapCounter (i+1) rs)=T2 at h2 h4 ⊢
    generalize (rs.flatMap RoundRecord.wires).toFinset=R at h1 h2 h3 h4 ⊢
    generalize L.valueSharedWires.toFinset=Sh at h1 h2 ⊢
    generalize r.wires.toFinset=A
    constructor
    · ext w
      have a1 := @h1 w
      have a3 := @h3 w
      simp only [Finset.mem_union] at a1 ⊢
      constructor
      · rintro ((h|h)|h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · rcases a1 h with h'|h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
      · rintro ((h|h)|h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (a3 h)
        · exact Or.inl (Or.inr h)
    · ext w
      have a2 := @h2 w
      have a4 := @h4 w
      simp only [Finset.mem_union] at a2 ⊢
      constructor
      · rintro (h|(h|h))
        · rcases a2 h with h'|h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h|h)|h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl (a4 h)
        · exact Or.inr (Or.inr h)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueLoopProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueBoundary.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 值走旧视图的r/s/out现在分别是X+g、Y、Z，均在值走支持之外。 -/
structure DialogLayout where
  first : KaliskiRoundLayout
  records : List RoundRecord

namespace DialogLayout

end DialogLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogLayoutProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace DialogLayout

end DialogLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SafeDivisor.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogProgram.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogRegisters.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace DialogLayout

end DialogLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogLoad.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace DialogLayout

end DialogLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogReady.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace DialogLayout

end DialogLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogWalk.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogMiddle.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogWires.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace DialogLayout

end DialogLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DialogPool.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace DialogLayout

end DialogLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FieldAddSub.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontAdapterLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace MontLayout

end MontLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontAdapterSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontAdapterResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontAdapterFrame.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FieldMultiply.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MultiplyPorts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/AffineFormula.lean
noncomputable section

namespace ECDSAAdd
namespace Secp256k1



@[simp]
theorem negY_eq_neg (x y : Fp) :
    curve.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, curve]

def genericNumerator (y₁ y₂ : Fp) : Fp :=
  y₁ - y₂

def genericDenominator (x₁ x₂ : Fp) : Fp :=
  x₁ - x₂

def genericSlope (x₁ y₁ x₂ y₂ : Fp) : Fp :=
  genericNumerator y₁ y₂ * (genericDenominator x₁ x₂)⁻¹

def genericX (x₁ y₁ x₂ y₂ : Fp) : Fp :=
  let l := genericSlope x₁ y₁ x₂ y₂
  l ^ 2 - x₁ - x₂

def genericY (x₁ y₁ x₂ y₂ : Fp) : Fp :=
  let l := genericSlope x₁ y₁ x₂ y₂
  let x₃ := genericX x₁ y₁ x₂ y₂
  l * (x₁ - x₃) - y₁

theorem genericSlope_eq_mathlib
    {x₁ y₁ x₂ y₂ : Fp}
    (hx : x₁ ≠ x₂) :
    genericSlope x₁ y₁ x₂ y₂ =
      curve.toAffine.slope x₁ x₂ y₁ y₂ := by
  rw [curve.toAffine.slope_of_X_ne hx]
  simp [genericSlope, genericNumerator, genericDenominator, div_eq_mul_inv]

theorem genericX_eq_mathlib
    {x₁ y₁ x₂ y₂ : Fp}
    (hx : x₁ ≠ x₂) :
    genericX x₁ y₁ x₂ y₂ =
      curve.toAffine.addX x₁ x₂
        (curve.toAffine.slope x₁ x₂ y₁ y₂) := by
  simp [genericX, genericSlope_eq_mathlib hx,
    WeierstrassCurve.Affine.addX, curve]

theorem genericY_eq_mathlib
    {x₁ y₁ x₂ y₂ : Fp}
    (hx : x₁ ≠ x₂) :
    genericY x₁ y₁ x₂ y₂ =
      curve.toAffine.addY x₁ x₂ y₁
        (curve.toAffine.slope x₁ x₂ y₁ y₂) := by
  simp only [genericY]
  rw [genericSlope_eq_mathlib hx, genericX_eq_mathlib hx]
  rw [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, negY_eq_neg]
  ring_nf

theorem generic_nonsingular
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    curve.toAffine.Nonsingular
      (genericX x₁ y₁ x₂ y₂)
      (genericY x₁ y₁ x₂ y₂) := by
  rw [genericX_eq_mathlib hx, genericY_eq_mathlib hx]
  exact curve.toAffine.nonsingular_add h₁ h₂
    (fun hxy => hx hxy.left)

def genericAdd
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    Point :=
  .some (generic_nonsingular h₁ h₂ hx)

theorem genericAdd_correct
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    genericAdd h₁ h₂ hx =
      (.some h₁ : Point) + (.some h₂ : Point) := by
  unfold genericAdd
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨genericX_eq_mathlib hx, genericY_eq_mathlib hx⟩

theorem y_eq_of_x_eq_of_not_inverse
    {x₁ y₁ x₂ y₂ : Fp}
    (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂)
    (hinv : y₁ ≠ -y₂) :
    y₁ = y₂ := by
  apply curve.toAffine.Y_eq_of_Y_ne h₁.left h₂.left hx
  simpa [WeierstrassCurve.Affine.negY, curve] using hinv

end Secp256k1
end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/PointCandidateValues.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 与电路中依次保留的候选寄存器一一对应。 -/
structure PointCandidateValues where
  dx : Fp
  dy : Fp
  divisor : Fp
  inverse : Fp
  slope : Fp
  square : Fp
  offset : Fp
  x : Fp
  delta : Fp
  product : Fp
  y : Fp

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/EqualConstant.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

private theorem zeroBit_count (bs : List ZeroBit) (w : Wire) :
    (bs.flatMap ZeroBit.wires).count w =
      (bs.map ZeroBit.input).count w + (bs.map ZeroBit.work).count w := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons,ZeroBit.wires,List.map_cons,List.count_append,
      List.count_cons,List.count_nil,ih]
    omega

/-- 保留输入，XOR 写入 control ∧ (input = k)；同一组零检测工作位前后均为零。 -/
def equalConstant (control target : Wire) (bs : List ZeroBit) (k : Nat) : Program :=
  xorConstant (bs.map ZeroBit.input) k ++ zeroControlled control target bs ++
    xorConstant (bs.map ZeroBit.input) k

theorem equalConstant_correct (control target : Wire) (bs : List ZeroBit) (k : Nat)
    (hnd : (control::target::bs.flatMap ZeroBit.wires).Nodup) (hk : k<2^bs.length)
    (s : State) (m : List Bool) (hz : ∀ b∈bs,s.basis b.work=false) :
    run (equalConstant control target bs k) m s =
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ (s.basis control && decide (regValue (bs.map ZeroBit.input) s.basis=k)))⟩ := by
  let src := bs.map ZeroBit.input
  have hsrc : src.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hb : src.count w ≤ (bs.flatMap ZeroBit.wires).count w := by
      rw [zeroBit_count]; exact Nat.le_add_right _ _
    have hh := List.nodup_iff_count.mp hnd w
    simp only [List.count_cons] at hh
    omega
  have hin (b : ZeroBit) (hb : b∈bs) : b.input∈bs.flatMap ZeroBit.wires :=
    List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩
  have hwork (b : ZeroBit) (hb : b∈bs) : b.work∉src := by
    intro hi
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hi
    have hni := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
    have hdup : 2≤(bs.flatMap ZeroBit.wires).count b.work := by
      have hwc : 1≤(bs.map ZeroBit.work).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b,hb,rfl⟩)
      have hic : 1≤(bs.map ZeroBit.input).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨a,ha,he⟩)
      have hc := zeroBit_count bs b.work
      omega
    have hh := List.nodup_iff_count.mp hni b.work
    omega
  have hc : control∉src := by
    intro h; obtain ⟨b,hb,he⟩ := List.mem_map.mp h
    exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ (he ▸ hin b hb))
  have ht : target∉src := by
    intro h; obtain ⟨b,hb,he⟩ := List.mem_map.mp h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (he ▸ hin b hb)
  let u := run (xorConstant src k) m s
  obtain ⟨hup,hue,huv⟩ := xorConstant_correct src hsrc k (by simpa [src] using hk) s m
  have huz : ∀ b∈bs,u.basis b.work=false := fun b hb => (hue _ (hwork b hb)).trans (hz b hb)
  have hh := zeroControlled_correct control target bs hnd u m huz
  have hall : bs.all (fun b => !u.basis b.input) = decide (regValue src s.basis=k) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true]
    simp only [Bool.not_eq_true']
    have heq : (∀ b∈bs,u.basis b.input=false) ↔ regValue src u.basis=0 := by
      rw [regValue_zero]
      simp [src]
    rw [heq]
    change (regValue src u.basis=0) ↔ decide (regValue src s.basis=k)=true
    rw [show regValue src u.basis=regValue src s.basis ^^^ k from huv]
    simp
  let v : State := ⟨s.phase,writeBit u.basis target
    (s.basis target ^^ (s.basis control && decide (regValue src s.basis=k)))⟩
  have hv : run (zeroControlled control target bs) m u=v := by
    rw [hh,hall]
    dsimp [v]
    rw [show u.phase=s.phase from hup,show u.basis target=s.basis target from hue _ ht,
      show u.basis control=s.basis control from hue _ hc]
  obtain ⟨hvp,hve,hvv⟩ := xorConstant_correct src hsrc k (by simpa [src] using hk) v (m.drop bs.length)
  have hvs : regValue src v.basis=regValue src u.basis := by
    apply regValue_congr
    intro w hw
    simp [v,writeBit,show w≠target from fun h => ht (h ▸ hw)]
  have hrestore : regValue src (run (xorConstant src k) (m.drop bs.length) v).basis=regValue src s.basis := by
    rw [hvv,hvs,show regValue src u.basis=regValue src s.basis ^^^ k from huv,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  rw [equalConstant,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(xorConstant_counts _ _).2,
    (zeroControlled_counts _ _ _).2,Nat.zero_add,List.drop_zero]
  change run (xorConstant src k) (m.drop bs.length) (run (zeroControlled control target bs) m u)=_
  rw [hv]
  apply (show ∀ a b : State, a.phase=b.phase → a.basis=b.basis → a=b from
    fun ⟨ap,ab⟩ ⟨bp,bb⟩ hp hb => by cases hp; cases hb; rfl)
  · exact hvp
  · funext w
    by_cases hw : w∈src
    · rw [(regValue_eq_iff src _ _).mp hrestore w hw]
      simp [writeBit,show w≠target from fun h => ht (h ▸ hw)]
    · rw [hve w hw]
      dsimp [v]
      by_cases hwt : w=target
      · subst w; simp [writeBit,src]
      · simp [writeBit,hwt,show u.basis w=s.basis w from hue w hw]

theorem equalConstant_counts (control target : Wire) (bs : List ZeroBit) (k : Nat) :
    toffoliCount (equalConstant control target bs k)=bs.length ∧
    measurementCount (equalConstant control target bs k)=bs.length := by
  simp only [equalConstant,toffoliCount_append,measurementCount_append,
    (xorConstant_counts _ _).1,(xorConstant_counts _ _).2,
    (zeroControlled_counts _ _ _).1,(zeroControlled_counts _ _ _).2,Nat.zero_add,Nat.add_zero,and_self]

/-- 常量的取值不改变实际支持：零检测本身已经触及全部布局线。 -/
theorem equalConstant_wires (control target : Wire) (bs : List ZeroBit) (k : Nat) :
    wires (equalConstant control target bs k) =
      (control::target::bs.flatMap ZeroBit.wires).toFinset := by
  have hsub : wires (xorConstant (bs.map ZeroBit.input) k) ⊆
      (control::target::bs.flatMap ZeroBit.wires).toFinset := by
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp
      (List.mem_toFinset.mp (xorConstant_wires_subset _ _ hw))
    simp only [List.mem_toFinset,List.mem_cons]
    exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))
  rw [equalConstant,wires_append,wires_append,zeroControlled_wires,
    Finset.union_eq_right.mpr hsub,Finset.union_eq_left.mpr hsub]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointFlags.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointAddLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 候选计算保留九个 257 位值，另借一个同宽寄存器装载常量或复制乘数。
除数和逆元只需 256 位；两个输入最高位独立保持零。 -/
structure PointAddLayout where
  input : PointReg
  output : PointReg
  dx : List Wire
  dy : List Wire
  slope : List Wire
  square : List Wire
  offset : List Wire
  candidateX : List Wire
  delta : List Wire
  product : List Wire
  candidateY : List Wire
  constant : List Wire
  divisor : List Wire
  inverse : List Wire
  inputXHigh : Wire
  inputYHigh : Wire
  equalX : Wire
  equalNegY : Wire
  generic : Wire
  double : Wire
  pool : List Wire

namespace PointAddLayout

def words (L : PointAddLayout) : List (List Wire) :=
  [L.dx,L.dy,L.slope,L.square,L.offset,L.candidateX,L.delta,L.product,L.candidateY,L.constant]

def flags (L : PointAddLayout) : List Wire :=
  [L.equalX,L.equalNegY,L.generic,L.double]

def pointWires (r : PointReg) : List Wire := r.finite::r.x++r.y

def work (L : PointAddLayout) : List Wire :=
  L.words.flatten++L.divisor++L.inverse++[L.inputXHigh,L.inputYHigh]++L.flags++L.pool

def wires (L : PointAddLayout) : List Wire :=
  pointWires L.input++pointWires L.output++L.work

/-- 宽度是公开布局条件；工作池按求逆的现有分配前缀分配。 -/
structure Widths (L : PointAddLayout) : Prop where
  inputX : L.input.x.length=256
  inputY : L.input.y.length=256
  outputX : L.output.x.length=256
  outputY : L.output.y.length=256
  words : ∀ r∈L.words,r.length=257
  divisor : L.divisor.length=256
  inverse : L.inverse.length=256
  pool : L.pool.length=5699

end PointAddLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SubtractPorts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace PointAddLayout

def poolWire (L : PointAddLayout) : Nat → Wire := fun i => L.pool.getD i 0

end PointAddLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidateLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace PointAddLayout

theorem pool_prefix (L : PointAddLayout) (h : L.Widths) (n : Nat) (hn : n≤5699) :
    wireBlock L.poolWire 0 n=L.pool.take n := by
  apply List.ext_getElem
  · simp [wireBlock,h.pool,Nat.min_eq_left hn]
  · intro i hi hj
    have hi' : i<L.pool.length := lt_of_lt_of_le (by simpa [wireBlock] using hi) (h.pool ▸ hn)
    simp [wireBlock,poolWire,List.getD,List.getElem?_eq_getElem hi']

end PointAddLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidateSupport.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FieldFrame.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidateState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 候选步骤的寄存器名；输入坐标带独立的零最高位。 -/
inductive CandidateField where
  | inputX | inputY | dx | dy | slope | square | offset | x | delta | product | y | constant | divisor | inverse
  deriving DecidableEq

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidateSteps.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidateBlocks.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidateProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidateSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointClassification.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 点的规范编码；这些函数也可用于任意目标位串的 XOR 规格。 -/
def pointFinite (R : Point) : Bool := (coordinates R).isSome
def pointX (R : Point) : Nat := ((coordinates R).getD (0,0)).1.val
def pointY (R : Point) : Nat := ((coordinates R).getD (0,0)).2.val

theorem point_holds (r : PointReg) (R : Point) (s : BasisState) :
    Holds.holds s r R ↔ s r.finite=pointFinite R ∧
      regValue r.x s=pointX R ∧ regValue r.y s=pointY R := by
  cases R <;> rfl

theorem point_coordinates_lt (R : Point) : pointX R<p ∧ pointY R<p := by
  cases R with
  | zero => norm_num [pointX,pointY,coordinates,p]
  | some h => exact ⟨ZMod.val_lt _,ZMod.val_lt _⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointFlagLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 零检测输入直接连接坐标，工作链借共享池的前缀。 -/
def zeroPorts : List Wire → List Wire → List ZeroBit
  | x::xs,w::ws => ⟨x,w⟩::zeroPorts xs ws
  | _,_ => []

theorem zeroPorts_maps (xs ws : List Wire) (h : xs.length=ws.length) :
    (zeroPorts xs ws).map ZeroBit.input=xs ∧ (zeroPorts xs ws).map ZeroBit.work=ws := by
  induction xs generalizing ws with
  | nil => have he : ws=[] := List.eq_nil_of_length_eq_zero h.symm; subst ws; simp [zeroPorts]
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      obtain ⟨hx,hw⟩ := ih ws (by simpa using h)
      simp [zeroPorts,hx,hw]

theorem zeroPorts_perm (xs ws : List Wire) (h : xs.length=ws.length) :
    ((zeroPorts xs ws).flatMap ZeroBit.wires).Perm (xs++ws) := by
  apply List.perm_iff_count.mpr
  intro v
  induction xs generalizing ws with
  | nil => have he : ws=[] := List.eq_nil_of_length_eq_zero h.symm; subst ws; simp [zeroPorts]
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      have ht := ih ws (by simpa using h)
      simp only [zeroPorts,List.flatMap_cons,ZeroBit.wires,List.count_append,List.count_cons,List.count_nil] at ht ⊢
      omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointFlagProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem equalPorts_correct (c t : Wire) (src work : List Wire) (k : Nat)
    (hl : src.length=work.length) (hn : (c::t::src++work).Nodup)
    (hk : k<2^src.length) (s : State) (m : List Bool) (hz : regValue work s.basis=0) :
    run (equalConstant c t (zeroPorts src work) k) m s=
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis c && decide (regValue src s.basis=k)))⟩ := by
  obtain ⟨hx,hw⟩ := zeroPorts_maps src work hl
  have hlen : (zeroPorts src work).length=src.length := by
    simpa using congrArg List.length hx
  have hnd : (c::t::(zeroPorts src work).flatMap ZeroBit.wires).Nodup :=
    ((zeroPorts_perm src work hl).cons t |>.cons c).nodup_iff.mpr hn
  have hz' : ∀ b∈zeroPorts src work,s.basis b.work=false := by
    intro b hb
    apply (regValue_zero _ _).mp hz
    rw [← hw]
    exact List.mem_map.mpr ⟨b,hb,rfl⟩
  simpa only [hx] using equalConstant_correct c t (zeroPorts src work) k hnd (hlen ▸ hk) s m hz'

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointOutput.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 经典点编码只在非零常量位上施 CX。 -/
def maskedPointConstant (c : Wire) (r : PointReg) (C : Point) : Program :=
  maskedConstant c [r.finite] (pointFinite C).toNat++
    maskedConstant c r.x (pointX C)++maskedConstant c r.y (pointY C)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointEffect.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 点输出的逐字段 XOR 和完整外部保持条件；目标无需编码曲线点。 -/
structure PointEffect (r : PointReg) (F : Bool) (X Y : Nat) (s t : State) : Prop where
  phase : t.phase=s.phase
  outside : ∀ w∉PointAddLayout.pointWires r,t.basis w=s.basis w
  finite : t.basis r.finite=(s.basis r.finite ^^ F)
  x : regValue r.x t.basis=regValue r.x s.basis ^^^ X
  y : regValue r.y t.basis=regValue r.y s.basis ^^^ Y

theorem PointEffect.trans {r : PointReg} {F G : Bool} {X Y U V : Nat} {s t u : State}
    (h : PointEffect r F X Y s t) (k : PointEffect r G U V t u) :
    PointEffect r (F^^G) (X^^^U) (Y^^^V) s u := by
  refine ⟨k.phase.trans h.phase,fun w hw => (k.outside w hw).trans (h.outside w hw),?_,?_,?_⟩
  · rw [k.finite,h.finite,Bool.xor_assoc]
  · rw [k.x,h.x,Nat.xor_assoc]
  · rw [k.y,h.y,Nat.xor_assoc]

theorem PointEffect.of_finite (r : PointReg) (hn : (PointAddLayout.pointWires r).Nodup)
    (F : Bool) (s t : State) (hp : t.phase=s.phase)
    (he : ∀ w,w≠r.finite → t.basis w=s.basis w)
    (hv : t.basis r.finite=(s.basis r.finite ^^ F)) : PointEffect r F 0 0 s t := by
  have hh := (List.nodup_cons.mp hn).1
  refine ⟨hp,fun w hw => he w (fun e => hw (by simp [PointAddLayout.pointWires,e])),hv,?_,?_⟩
  · rw [Nat.xor_zero]; apply regValue_congr; intro w hw
    exact he w (fun e => hh (List.mem_append_left _ (e ▸ hw)))
  · rw [Nat.xor_zero]; apply regValue_congr; intro w hw
    exact he w (fun e => hh (List.mem_append_right _ (e ▸ hw)))

theorem PointEffect.of_x (r : PointReg) (hn : (PointAddLayout.pointWires r).Nodup)
    (X : Nat) (s t : State) (hp : t.phase=s.phase)
    (he : ∀ w∉r.x,t.basis w=s.basis w)
    (hv : regValue r.x t.basis=regValue r.x s.basis ^^^ X) : PointEffect r false X 0 s t := by
  have hh := List.nodup_cons.mp hn
  refine ⟨hp,fun w hw => he w (fun e => hw (by simp [PointAddLayout.pointWires,e])),?_,hv,?_⟩
  · rw [Bool.xor_false]; exact he _ (fun e => hh.1 (List.mem_append_left _ e))
  · rw [Nat.xor_zero]; apply regValue_congr; intro w hw
    exact he w (fun hx => List.disjoint_left.mp (List.nodup_append'.mp hh.2).2.2 hx hw)

theorem PointEffect.of_y (r : PointReg) (hn : (PointAddLayout.pointWires r).Nodup)
    (Y : Nat) (s t : State) (hp : t.phase=s.phase)
    (he : ∀ w∉r.y,t.basis w=s.basis w)
    (hv : regValue r.y t.basis=regValue r.y s.basis ^^^ Y) : PointEffect r false 0 Y s t := by
  have hh := List.nodup_cons.mp hn
  refine ⟨hp,fun w hw => he w (fun e => hw (by simp [PointAddLayout.pointWires,e])),?_,?_,hv⟩
  · rw [Bool.xor_false]; exact he _ (fun e => hh.1 (List.mem_append_right _ e))
  · rw [Nat.xor_zero]; apply regValue_congr; intro w hw
    exact he w (List.disjoint_left.mp (List.nodup_append'.mp hh.2).2.2 hw)

/-- 外部坐标或标志可跨输出操作使用，输出本身允许为任意位串。 -/
theorem PointEffect.reg {r : PointReg} {F : Bool} {X Y : Nat} {s t : State}
    (h : PointEffect r F X Y s t) (a : List Wire)
    (hd : a.Disjoint (PointAddLayout.pointWires r)) : regValue a t.basis=regValue a s.basis :=
  regValue_congr _ _ _ (fun w hw => h.outside w (List.disjoint_left.mp hd hw))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointConstantProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem pointFinite_effect (c : Wire) (r : PointReg) (F : Bool)
    (hn : (PointAddLayout.pointWires r).Nodup) (s : State) (m : List Bool) :
    PointEffect r (s.basis c && F) 0 0 s
      (run (maskedConstant c [r.finite] F.toNat) m s) := by
  have hh : run (maskedConstant c [r.finite] F.toNat) m s=
      ⟨s.phase,writeBit s.basis r.finite (s.basis r.finite ^^ (s.basis c && F))⟩ := by
    cases F <;> simp [maskedConstant,run,writeBit]
  rw [hh]
  apply PointEffect.of_finite r hn
  · rfl
  · intro w hw; simp [writeBit,hw]
  · simp [writeBit]

theorem maskedPointConstant_correct (c : Wire) (r : PointReg) (C : Point)
    (hn : (PointAddLayout.pointWires r).Nodup) (hc : c∉PointAddLayout.pointWires r)
    (hx : r.x.length=256) (hy : r.y.length=256) (s : State) (m : List Bool) :
    PointEffect r (s.basis c && pointFinite C)
      (if s.basis c then pointX C else 0) (if s.basis c then pointY C else 0) s
      (run (maskedPointConstant c r C) m s) := by
  have nr := List.nodup_append'.mp (List.nodup_cons.mp hn).2
  have hcx : c∉r.x := fun hw => hc (by simp [PointAddLayout.pointWires,hw])
  have hcy : c∉r.y := fun hw => hc (by simp [PointAddLayout.pointWires,hw])
  have bx : pointX C<2^r.x.length := by
    rw [hx]; exact lt_trans (point_coordinates_lt C).1 (by norm_num [p])
  have by' : pointY C<2^r.y.length := by
    rw [hy]; exact lt_trans (point_coordinates_lt C).2 (by norm_num [p])
  let u := run (maskedConstant c [r.finite] (pointFinite C).toNat) m s
  have e0 := pointFinite_effect c r (pointFinite C) hn s m
  have uc : u.basis c=s.basis c := e0.outside c hc
  obtain ⟨px,ex,vx⟩ := maskedConstant_correct c r.x (pointX C) nr.1 hcx bx u m
  have e1 := PointEffect.of_x r hn _ u _ px ex vx
  let v := run (maskedConstant c r.x (pointX C)) m u
  have vc : v.basis c=s.basis c := (e1.outside c hc).trans uc
  obtain ⟨py,ey,vy⟩ := maskedConstant_correct c r.y (pointY C) nr.2.1 hcy by' v m
  have e2 := PointEffect.of_y r hn _ v _ py ey vy
  have he := e0.trans (e1.trans e2)
  rw [maskedPointConstant,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(maskedConstant_counts _ _ _).2,Nat.zero_add,List.drop_zero]
  simpa only [u,v,uc,vc,Bool.xor_false,Nat.zero_xor,Nat.xor_zero] using he

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCopyProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointOutputProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointAddState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointFlagResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointOutputResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem maskedPointConstant_counts (c : Wire) (r : PointReg) (C : Point) :
    toffoliCount (maskedPointConstant c r C)=0 ∧ measurementCount (maskedPointConstant c r C)=0 := by
  simp [maskedPointConstant,toffoliCount_append,measurementCount_append,maskedConstant_counts]

theorem maskedPointConstant_support (c : Wire) (r : PointReg) (C : Point) :
    wires (maskedPointConstant c r C) ⊆ (c::PointAddLayout.pointWires r).toFinset := by
  simp only [maskedPointConstant,wires_append,Finset.union_subset_iff]
  have hh (a : List Wire) (k : Nat) (ha : a⊆PointAddLayout.pointWires r) :
      wires (maskedConstant c a k) ⊆ (c::PointAddLayout.pointWires r).toFinset := by
    intro w hw
    have hm := maskedConstant_wires_subset c a k hw
    simp only [List.mem_toFinset,List.mem_cons] at hm ⊢
    exact hm.imp_right (fun hw => ha hw)
  exact ⟨⟨hh _ _ (by simp [PointAddLayout.pointWires]),hh _ _ (by simp [PointAddLayout.pointWires])⟩,
    hh _ _ (by simp [PointAddLayout.pointWires])⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointAddSupport.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointCandidateResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointAddFrames.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointAddStages.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointFlagStages.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledPointPorts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 点加共用一套算术布局，额外四线为外部控制与三个最终输出选择位。 -/
structure ControlledPointLayout where
  core : PointAddLayout
  control : Wire
  genericSelect : Wire
  doubleSelect : Wire
  infinitySelect : Wire

namespace ControlledPointLayout

def point (L : ControlledPointLayout) := L.core.input
def temporary (L : ControlledPointLayout) := L.core.output
def selectors (L : ControlledPointLayout) := [L.genericSelect,L.doubleSelect,L.infinitySelect]
def extras (L : ControlledPointLayout) := L.control::L.selectors
def outWork (L : ControlledPointLayout) := L.core.work++L.selectors
def work (L : ControlledPointLayout) := PointAddLayout.pointWires L.temporary++L.outWork
def wires (L : ControlledPointLayout) := L.core.wires++L.extras
def Widths (L : ControlledPointLayout) := L.core.Widths

theorem core_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.core.wires.Nodup :=
  (List.nodup_append'.mp hn).1

end ControlledPointLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MontBorrow.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/Divide.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 除法保留分母/分子，只累加到 acc；inner 的历史保存到乘积清理后。
§16.2 的直接门列；完整规格、逐线保持和资源见 DivideSpec/DivideSupport。 -/
structure DivideLayout where
  control : Wire
  denominator : List Wire
  numerator : List Wire
  acc : List Wire
  inner : InverseLoopLayout

namespace DivideLayout

end DivideLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DivideLayoutProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.DivideLayout

end ECDSAAdd.Arithmetic.DivideLayout
end

-- source: ECDSAAdd/Arithmetic/DivideLoad.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DivideSupport.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace DivideLayout

end DivideLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DivideProduct.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DivideState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace DivideLayout

end DivideLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DivideSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointEncoding.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 与finite::x++y一致的小端完整点编码，O编码为零。 -/
def pointCode (R : Point) : Nat := (pointFinite R).toNat+2*(pointX R+2^256*pointY R)

theorem pointCode_injective : Function.Injective pointCode := by
  intro R C h
  have hp : p<2^256 := by norm_num [p]
  have hx := (point_coordinates_lt R).1.trans hp
  have hc := (point_coordinates_lt C).1.trans hp
  have hf : pointFinite R=pointFinite C := by
    dsimp only [pointCode] at h
    cases hr : pointFinite R <;> cases hc : pointFinite C <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
  have hv : pointX R+2^256*pointY R=pointX C+2^256*pointY C := by
    dsimp only [pointCode] at h
    rw [hf] at h
    omega
  have hxx : pointX R=pointX C := by
    have hm := congrArg (fun a => a%2^256) hv
    simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod,
      Nat.add_zero,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hc] using hm
  have hyy : pointY R=pointY C := by
    rw [hxx] at hv
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel hv)
  cases R with
  | zero => cases C <;> simp_all [pointFinite,coordinates]
  | @some x y hr =>
    cases C with
    | zero => simp [pointFinite,coordinates] at hf
    | @some u v hc =>
      have heX : x=u := ZMod.val_injective p hxx
      have heY : y=v := ZMod.val_injective p hyy
      subst u; subst v; rfl

/-- 规范编码上的可判定相等；在合法点上恰好是点相等。 -/
def pointEqual (R C : Point) : Bool := decide (pointCode R=pointCode C)

theorem pointEqual_true_iff (R C : Point) : pointEqual R C=true ↔ R=C := by
  simp only [pointEqual,decide_eq_true_eq,pointCode_injective.eq_iff]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace ControlledPointLayout

/-- §16的七位沿用旧字段：o/infinitySelect、d/doubleSelect、i/genericSelect，
g/core.generic、e/core.equalX、q/core.equalNegY、h/core.double。 -/
def inPlaceFlags (L : ControlledPointLayout) : List Wire :=
  [L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.generic,L.core.equalX,L.core.equalNegY,L.core.double]

def inPlaceSlope (L : ControlledPointLayout) : List Wire := L.core.slope.take 256

def inPlaceInverse (L : ControlledPointLayout) : InverseLoopLayout :=
  (poolInverse L.core.poolWire L.core.divisor L.core.inverse).inner

end ControlledPointLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceLayoutProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

theorem inPlaceInverse_perm (L : ControlledPointLayout) (hw : L.Widths) :
    L.inPlaceInverse.wires.Perm (L.core.inverse++L.core.pool) := by
  let I := poolInverse L.core.poolWire L.core.divisor L.core.inverse
  have hp := poolInverse_work_perm L.core.poolWire L.core.divisor L.core.inverse hw.inverse
  have hl := L.core.pool_prefix hw 5699 (by omega)
  have he : L.core.pool.take 5699=L.core.pool := by rw [← hw.pool,List.take_length]
  rw [he] at hl
  rw [hl] at hp
  have hi := I.wires_perm
  have hout := poolInverse_inputs L.core.poolWire L.core.divisor L.core.inverse hw.inverse
  apply List.perm_iff_count.mpr; intro q
  have h := hi.count_eq q
  have hwork := hp.count_eq q
  have ho : I.out=L.core.inverse := hout.2
  simp only [InverseLayout.wires,ho,List.count_append] at h
  change I.inner.wires.count q=(L.core.inverse++L.core.pool).count q
  simp only [List.count_append]
  change I.work.count q=L.core.pool.count q at hwork
  omega

/-- 公共布局中抽出的点、控制、斜率、七个标志与整个求逆布局互异。 -/
theorem inPlace_interfaces_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (PointAddLayout.pointWires L.point++[L.control]++L.inPlaceSlope++L.inPlaceFlags++L.inPlaceInverse.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  have hi := (L.inPlaceInverse_perm hw).count_eq q
  have hs := (List.take_sublist 256 L.core.slope).count_le q
  simp only [inPlaceSlope] at *
  simp only [wires,point,inPlaceFlags,extras,selectors,PointAddLayout.wires,PointAddLayout.work,
    PointAddLayout.words,PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.count_append,List.count_cons,List.count_nil] at h hi ⊢
  omega

end ECDSAAdd.Arithmetic.ControlledPointLayout
end

-- source: ECDSAAdd/Arithmetic/SquareReduce.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 三次折叠的实际寄存器。q 留在 r 的高33位，b 独立于 q。 -/
structure SquareReduceLayout where
  low : List Wire
  high : List Wire
  r : List Wire
  pad : List Wire
  mask : List Wire
  carry : List Wire
  cin : Wire
  b : Wire
  flag : Wire

namespace SquareReduceLayout

end SquareReduceLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareReduceResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareSubLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 专用平方减法的共享区：和寄存器借 padding 后128位及独立最高位。
C 借 r 前258位；两个生命周期不重叠。 -/
structure SquareSubLayout where
  x : List Wire
  out : List Wire
  a : List Wire
  d : List Wire
  r : List Wire
  z : List Wire
  mask : List Wire
  carry : List Wire
  cin : Wire
  pad : List Wire
  b : Wire
  flag : Wire
  sourceHigh : Wire
  outputHigh : Wire
  constantHigh : Wire
  maskHigh : Wire
  layoutFlag : Wire
  sumHigh : Wire

namespace SquareSubLayout

end SquareSubLayout

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareSubPool.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace SquareSubLayout

end SquareSubLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointKaratsubaLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace ControlledPointLayout

end ControlledPointLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

/-- 六阶段共用2,613位池；其余旧分配保持，不计入实际支持。 -/
def dialogPool (L : ControlledPointLayout) : List Wire := L.core.pool.take 2613

def dialogUsedWires (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags++L.dialogPool

def dialogUnary (L : ControlledPointLayout) (r : List Wire) : ModInPlaceLayout :=
  {a:=L.dialogPool.take 257,low:=r,high:=L.core.poolWire 257,
    constant:=(L.dialogPool.drop 258).take 257,carry:=(L.dialogPool.drop 515).take 256,
    cin:=L.core.poolWire 771,mask:=(L.dialogPool.drop 772).take 257,flag:=L.core.poolWire 1029}

/-- Concrete 649-site pool binding for the exact streamed-square core. -/
def dialogStreamedSquare (L : ControlledPointLayout) : CuccaroStreamedSquareLayout :=
  { y:=L.point.y,out:=L.point.x,
    product:=L.dialogPool.take 258,
    pad:=(L.dialogPool.drop 258).take 128,
    work:=(L.dialogPool.drop 386).take 256,
    productHigh:=L.core.poolWire 642,
    outHigh:=L.core.poolWire 643,
    workHigh:=L.core.poolWire 644,
    cin:=L.core.poolWire 645,
    normFlag:=L.core.poolWire 646,
    modFlag:=L.core.poolWire 647,
    sumCarry:=L.core.poolWire 648 }

def dialogStreamedSquareWide (L : ControlledPointLayout) : CuccaroStreamedSquareWideLayout :=
  { core:=L.dialogStreamedSquare,
    overflowPad:=(L.dialogPool.drop 649).take 126 }

def dialogPointZero (L : ControlledPointLayout) : List ZeroBit :=
  zeroPorts (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)

theorem dialogPool_length (L : ControlledPointLayout) (hw : L.Widths) : L.dialogPool.length=2613 := by
  simp [dialogPool,hw.pool]

theorem dialogUsed_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    L.dialogUsedWires.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  have hp := (List.take_sublist 2613 L.core.pool).count_le q
  simp only [dialogUsedWires,dialogPool,inPlaceFlags,wires,point,extras,selectors,
    PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,PointAddLayout.flags,
    List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem dialogBit_prefix (L : ControlledPointLayout) (hw : L.Widths) (i : Nat) (hi : i<2613) :
    L.dialogPool.take i++[L.core.poolWire i]=L.dialogPool.take (i+1) := by
  have h : i<L.core.pool.length := by rw [hw.pool]; omega
  simp only [dialogPool,List.take_take]
  rw [Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)]
  change L.core.pool.take i++[L.core.pool.getD i 0]=_
  rw [List.getD_eq_getElem _ _ h,List.take_add_one,List.getElem?_eq_getElem h]
  rfl

theorem dialogStreamedSquare_widths (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogStreamedSquare.Widths := by
  constructor
  · exact hw.inputY
  · exact hw.inputX
  · simp [dialogStreamedSquare,L.dialogPool_length hw]
  · simp [dialogStreamedSquare,L.dialogPool_length hw]
  · simp [dialogStreamedSquare,L.dialogPool_length hw]

theorem dialogStreamedSquare_pool (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogStreamedSquare.product++L.dialogStreamedSquare.pad++
      L.dialogStreamedSquare.work++
      [L.dialogStreamedSquare.productHigh,L.dialogStreamedSquare.outHigh,
        L.dialogStreamedSquare.workHigh,L.dialogStreamedSquare.cin,
        L.dialogStreamedSquare.normFlag,L.dialogStreamedSquare.modFlag,
        L.dialogStreamedSquare.sumCarry]=L.dialogPool.take 649 := by
  simp only [dialogStreamedSquare]
  rw [←List.take_add,←List.take_add]
  norm_num
  calc
    L.dialogPool.take 642++[L.core.poolWire 642,L.core.poolWire 643,
        L.core.poolWire 644,L.core.poolWire 645,L.core.poolWire 646,
        L.core.poolWire 647,L.core.poolWire 648] =
      (L.dialogPool.take 642++[L.core.poolWire 642])++
        [L.core.poolWire 643,L.core.poolWire 644,L.core.poolWire 645,
          L.core.poolWire 646,L.core.poolWire 647,L.core.poolWire 648] := by simp
    _ = (L.dialogPool.take 643++[L.core.poolWire 643])++
        [L.core.poolWire 644,L.core.poolWire 645,L.core.poolWire 646,
          L.core.poolWire 647,L.core.poolWire 648] := by
            rw [L.dialogBit_prefix hw 642 (by omega)]
            norm_num [List.append_assoc]
    _ = (L.dialogPool.take 644++[L.core.poolWire 644])++
        [L.core.poolWire 645,L.core.poolWire 646,L.core.poolWire 647,
          L.core.poolWire 648] := by
            rw [L.dialogBit_prefix hw 643 (by omega)]
            norm_num [List.append_assoc]
    _ = (L.dialogPool.take 645++[L.core.poolWire 645])++
        [L.core.poolWire 646,L.core.poolWire 647,L.core.poolWire 648] := by
          rw [L.dialogBit_prefix hw 644 (by omega)]
          norm_num [List.append_assoc]
    _ = (L.dialogPool.take 646++[L.core.poolWire 646])++
        [L.core.poolWire 647,L.core.poolWire 648] := by
          rw [L.dialogBit_prefix hw 645 (by omega)]
          norm_num [List.append_assoc]
    _ = (L.dialogPool.take 647++[L.core.poolWire 647])++
        [L.core.poolWire 648] := by
          rw [L.dialogBit_prefix hw 646 (by omega)]
          norm_num [List.append_assoc]
    _ = L.dialogPool.take 648++[L.core.poolWire 648] := by
          rw [L.dialogBit_prefix hw 647 (by omega)]
    _ = L.dialogPool.take 649 := by
          simpa using L.dialogBit_prefix hw 648 (by omega)

theorem dialogStreamedSquareWide_widths (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogStreamedSquareWide.Widths := by
  constructor
  · exact L.dialogStreamedSquare_widths hw
  · simp [dialogStreamedSquareWide,L.dialogPool_length hw]

theorem dialogStreamedSquareWide_pool (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogStreamedSquareWide.core.product++L.dialogStreamedSquareWide.core.pad++
      L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,
        L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++
      L.dialogStreamedSquareWide.overflowPad=L.dialogPool.take 775 := by
  rw [show L.dialogStreamedSquareWide.core=L.dialogStreamedSquare by rfl,
    L.dialogStreamedSquare_pool hw]
  simp only [dialogStreamedSquareWide]
  rw [←List.take_add]

theorem dialogStreamedSquareWide_nodup (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : L.dialogStreamedSquareWide.wires.Nodup := by
  have heq : L.dialogStreamedSquareWide.wires=
      L.point.y++L.point.x++L.dialogPool.take 775 := by
    calc
      L.dialogStreamedSquareWide.wires =
          L.dialogStreamedSquareWide.core.y++L.dialogStreamedSquareWide.core.out++
            (L.dialogStreamedSquareWide.core.product++
              L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
              [L.dialogStreamedSquareWide.core.productHigh,
                L.dialogStreamedSquareWide.core.outHigh,
                L.dialogStreamedSquareWide.core.workHigh,
                L.dialogStreamedSquareWide.core.cin,
                L.dialogStreamedSquareWide.core.normFlag,
                L.dialogStreamedSquareWide.core.modFlag,
                L.dialogStreamedSquareWide.core.sumCarry]++
              L.dialogStreamedSquareWide.overflowPad) := by
                simp [CuccaroStreamedSquareWideLayout.wires,
                  CuccaroStreamedSquareLayout.wires,List.append_assoc]
      _ = L.point.y++L.point.x++L.dialogPool.take 775 := by
            rw [L.dialogStreamedSquareWide_pool hw]
            simp [dialogStreamedSquareWide,dialogStreamedSquare]
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 775 L.dialogPool).count_le q
  rw [heq]
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,
    List.count_cons,List.count_nil] at h ⊢
  omega

theorem dialogPointZero_nodup (L : ControlledPointLayout) (hnd : L.wires.Nodup)
    (c t : Wire) (hct : c≠t) (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) :
    (c::t::PointAddLayout.pointWires L.point++L.dialogPool.take 513).Nodup := by
  have hc' : c∈([L.control]++L.inPlaceFlags) := by
    rcases hc with rfl | hc
    · simp
    · simp [hc]
  have ht' : t∈([L.control]++L.inPlaceFlags) := by simp [ht]
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hnd) q
  have hp := (List.take_sublist 513 L.dialogPool).count_le q
  have hh := (List.singleton_sublist.mpr hc').count_le q
  have hh' := (List.singleton_sublist.mpr ht').count_le q
  simp only [dialogUsedWires,List.count_append,List.count_cons,List.count_nil] at h hh hh' ⊢
  by_cases hqc : c=q <;> by_cases hqt : t=q
  · exact False.elim (hct (hqc.trans hqt.symm))
  all_goals simp_all only [beq_iff_eq, ↓reduceIte]
  all_goals omega

end ECDSAAdd.Arithmetic.ControlledPointLayout
end

-- source: ECDSAAdd/Arithmetic/SkywalkPointPool.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Overlay the existing caller coordinate words on the shared port, using
1,802 positions from its clean workspace for all other sites. -/
def skywalkPointWire (pool : Nat → Wire) (x y : List Wire) (i : Nat) : Wire :=
  if 770 ≤ i ∧ i < 1026 then x.getD (i-770) 0
  else if 2056 ≤ i ∧ i < 2312 then y.getD (i-2056) 0
  else pool (i-(if 1026 ≤ i then 256 else 0)-(if 2312 ≤ i then 256 else 0))

private theorem point_getD_range (xs : List Wire) (n : Nat) (hn : xs.length=n) :
    (List.range n).map (fun i => xs.getD i 0)=xs := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem _ _ hj

theorem skywalkPointWire_x (pool : Nat → Wire) (x y : List Wire) (hx : x.length=256) :
    wireBlock (skywalkPointWire pool x y) 770 256=x := by
  rw [wireBlock,List.range'_eq_map_range,List.map_map]
  have he : (List.range 256).map (fun i => skywalkPointWire pool x y (770+i))=
      (List.range 256).map (fun i => x.getD i 0) := by
    apply List.map_congr_left
    intro i hi
    have hb := List.mem_range.mp hi
    simp [skywalkPointWire,show 770 ≤ 770+i ∧ 770+i < 1026 by omega]
  exact he.trans (point_getD_range x 256 hx)

theorem skywalkPointWire_y (pool : Nat → Wire) (x y : List Wire) (hy : y.length=256) :
    wireBlock (skywalkPointWire pool x y) 2056 256=y := by
  rw [wireBlock,List.range'_eq_map_range,List.map_map]
  have he : (List.range 256).map (fun i => skywalkPointWire pool x y (2056+i))=
      (List.range 256).map (fun i => y.getD i 0) := by
    apply List.map_congr_left
    intro i hi
    have hb := List.mem_range.mp hi
    simp [skywalkPointWire,show ¬(770 ≤ 2056+i ∧ 2056+i < 1026) by omega,
      show 2056 ≤ 2056+i ∧ 2056+i < 2312 by omega]
  exact he.trans (point_getD_range y 256 hy)

private theorem point_prefix (pool : Nat → Wire) (x y : List Wire) :
    wireBlock (skywalkPointWire pool x y) 0 770=wireBlock pool 0 770 := by
  simp only [wireBlock,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  simp only [Function.comp_def,Nat.zero_add]
  change skywalkPointWire pool x y i=pool i
  simp [skywalkPointWire,show ¬(770 ≤ i ∧ i < 1026) by omega,
    show ¬(2056 ≤ i ∧ i < 2312) by omega,
    show ¬1026 ≤ i by omega,show ¬2312 ≤ i by omega]

private theorem point_middle (pool : Nat → Wire) (x y : List Wire) :
    wireBlock (skywalkPointWire pool x y) 1026 1030=wireBlock pool 770 1030 := by
  simp only [wireBlock,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  have hid : 1026+i-256=770+i := by omega
  simp [skywalkPointWire,show ¬(2056 ≤ 1026+i ∧ 1026+i < 2312) by omega,
    show 1026 ≤ 1026+i by omega,show ¬2312 ≤ 1026+i by omega,hid]

private theorem point_suffix (pool : Nat → Wire) (x y : List Wire) :
    wireBlock (skywalkPointWire pool x y) 2312 2=wireBlock pool 1800 2 := by
  simp only [wireBlock,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  have hid : 2312+i-256-256=1800+i := by omega
  simp [skywalkPointWire,show ¬(770 ≤ 2312+i ∧ 2312+i < 1026) by omega,
    show 1026 ≤ 2312+i by omega,show 2312 ≤ 2312+i by omega,hid]

theorem skywalkPointWire_shared (pool : Nat → Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256) :
    skywalkSharedWires (skywalkPointWire pool x y)=
      wireBlock pool 0 770++x++wireBlock pool 770 1030++y++wireBlock pool 1800 2 := by
  have hblocks : wireBlock (skywalkPointWire pool x y) 0 2314=
      wireBlock (skywalkPointWire pool x y) 0 770++
      wireBlock (skywalkPointWire pool x y) 770 256++
      wireBlock (skywalkPointWire pool x y) 1026 1030++
      wireBlock (skywalkPointWire pool x y) 2056 256++
      wireBlock (skywalkPointWire pool x y) 2312 2 := by
    symm
    rw [wireBlock_append,wireBlock_append,wireBlock_append,wireBlock_append]
  simpa only [skywalkSharedWires,point_prefix,skywalkPointWire_x pool x y hx,
    point_middle,skywalkPointWire_y pool x y hy,point_suffix] using hblocks

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkPointLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

end ECDSAAdd.Arithmetic.ControlledPointLayout
end

-- source: ECDSAAdd/Arithmetic/SkywalkDirectPointLayout.lean
noncomputable section

set_option maxRecDepth 4096

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

/-- Direct caller-X divisor port. Two selectors and a retained zero flag
occupy three scalar sites beyond the original 1,802-site shared scratch. -/
def skywalkDirectMap (L : ControlledPointLayout) : Nat → Wire :=
  skywalkPointWire L.core.poolWire L.point.x L.point.y

def skywalkDirectSelectorG (L : ControlledPointLayout) := L.core.poolWire 1802
def skywalkDirectSelectorS (L : ControlledPointLayout) := L.core.poolWire 1803
def skywalkDirectZero (L : ControlledPointLayout) := L.core.poolWire 1804

def skywalkDirectDeclaredSites (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags++L.dialogPool.take 1805

theorem skywalkDirectDeclaredSites_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    L.skywalkDirectDeclaredSites.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 1805 L.dialogPool).count_le q
  simp only [skywalkDirectDeclaredSites,dialogUsedWires,List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

theorem skywalkDirectMap_coordinates (L : ControlledPointLayout) (hw : L.Widths) :
    wireBlock L.skywalkDirectMap 770 256=L.point.x ∧
    wireBlock L.skywalkDirectMap 2056 256=L.point.y :=
  ⟨skywalkPointWire_x L.core.poolWire L.point.x L.point.y hw.inputX,
   skywalkPointWire_y L.core.poolWire L.point.x L.point.y hw.inputY⟩

end ECDSAAdd.Arithmetic.ControlledPointLayout
end

-- source: ECDSAAdd/Arithmetic/DirectSkywalkControlledPort.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout DirectSkywalk

def directSkywalkCarry (L : ControlledPointLayout) := wireBlock L.core.poolWire 0 255
def directSkywalkCin (L : ControlledPointLayout) := L.core.poolWire 1801

attribute [local irreducible] run

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DirectSkywalkFieldSupport.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace ECDSAAdd.Arithmetic.DirectSupport
attribute [local irreducible] wireBlock swapRegisters fusedSharedRetainedCell
attribute [local irreducible] mixedTranscriptFieldCell
attribute [local irreducible] FusedHalfPorts.compactForwardProgram

theorem selectWindow (b source flag : Wire) (constant : Bool) (body : Program) (W : Finset Wire)
    (hb : b∈W) (hs : source∈W) (hf : flag∈W) (hbody : wires body⊆W) :
    wires (transcriptSelectWindow b source flag constant body)⊆W := by
  have sides : wires (transcriptSelectCompute b source flag constant)⊆W ∧
      wires (transcriptSelectExpose flag constant)⊆W ∧
      wires (transcriptSelectErase b source flag constant)⊆W := by
    cases constant <;>
      simp [transcriptSelectCompute,transcriptSelectExpose,transcriptSelectErase,
        wires,Instr.wires,correctionWires,Finset.subset_iff] <;> aesop
  simp only [transcriptSelectWindow,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨sides.1,sides.2.1⟩,hbody⟩,sides.2.1⟩,sides.2.2⟩

end ECDSAAdd.Arithmetic.DirectSupport
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedControlledPort.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout DirectSkywalk

/-- Actual caller-X repair, mixed transcript arithmetic, and exact repair
uncomputation. The existing integer borrow scratch is reused for comparison. -/
def pointOffsetBorrowedArithmetic (L : ControlledPointLayout) (multiply : Bool) : Program :=
  directZeroControlled L.point.x (directSkywalkCarry L) (directSkywalkCin L)
    L.skywalkDirectZero (compactOffsetCallerArithmetic (!multiply) L.skywalkDirectMap
      L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS)

attribute [local irreducible] run compactOffsetCallerArithmetic pointOffsetBorrowedArithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedSupport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedSupport
open Secp256k1 BorrowedSkywalkCompactSupport
attribute [local irreducible] BalancedCircuit.coreProgram BalancedCircuit.program
attribute [local irreducible] BalancedInverse.program OffsetBorrowedField.program
attribute [local irreducible] OffsetBorrowedInverse.program BalancedCleanupOffset.program
attribute [local irreducible] wireBlock majority eraseCarry mappedMajority mappedSum mappedEraseCarry
attribute [local irreducible] dblInPlace halfInPlace copyRegister swapRegisters transcriptSelectWindow
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop

/-- Induction over actual emitted heads includes every measured correction. -/
theorem chainSupport (bits : List MappedBit) (xs ys cs ds : List Wire)
    (ci cb t : Wire) (W : Finset Wire)
    (hbits : ∀q∈mappedWires bits,q∈W) (hx : ∀q∈xs,q∈W) (hy : ∀q∈ys,q∈W)
    (hc : ∀q∈cs,q∈W) (hd : ∀q∈ds,q∈W) (hci : ci∈W) (hcb : cb∈W) (ht : t∈W) :
    wires (BalancedCleanupOffset.chain bits xs ys cs ds ci cb t)⊆W := by
  induction bits generalizing xs ys cs ds ci cb with
  | nil =>
    cases xs <;> cases ys <;> cases cs <;> cases ds <;>
      simp [BalancedCleanupOffset.chain,flipBelow_wires,wires,Finset.subset_iff,hcb,ht]
  | cons b bits ih =>
    cases xs with
    | nil => simp [BalancedCleanupOffset.chain,wires]
    | cons a xs =>
      cases ys with
      | nil => simp [BalancedCleanupOffset.chain,wires]
      | cons y ys =>
        cases cs with
        | nil => simp [BalancedCleanupOffset.chain,wires]
        | cons c cs =>
          cases ds with
          | nil => simp [BalancedCleanupOffset.chain,wires]
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
              simpa only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] using
                (show q∈b.wire.toList ∨ q=y ∨ q=ci ∨ q=c from by
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
                  tauto)
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
            simp only [BalancedCleanupOffset.chain,wires_append,Finset.union_subset_iff,and_assoc]
            exact ⟨bit.1.trans headPool,bit.2.2.trans sum,small.2.2,small.1,recurse,
              small.2.1,small.2.2,bit.2.2.trans sum,bit.2.1.trans headPool⟩

end ECDSAAdd.Arithmetic.OffsetBorrowedSupport
end

-- source: ECDSAAdd/Arithmetic/CompactOffsetCallerSupport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1 BorrowedSkywalkCompactSupport
attribute [local irreducible] compactSkywalkForward compactSkywalkReverse

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactPointLayout.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.ControlledPointLayout

end ECDSAAdd.Arithmetic.ControlledPointLayout
end

-- source: ECDSAAdd/Arithmetic/CompactRecoveryConstant.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def compactRecoveryConstant (K : MeasuredCanonicalModLayout) (control : Wire) (c p k : Nat) : Program :=
  maskedConstant control K.src k++K.program c p++maskedConstant control K.src k

theorem compactRecoveryConstant_correct (K : MeasuredCanonicalModLayout) (control : Wire)
    (n c p k : Nat) (hw : K.Widths n) (hn : (control::K.wires).Nodup)
    (npos : 0<n) (hpc : p+c=2^n) (hcpos : 0<c) (hk : k<p)
    (X : Nat) (hX : X<p) (s : State) (records : List Bool)
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X)
    (hh : s.basis K.high=false) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (compactRecoveryConstant K control c p k) records s).phase=s.phase ∧
    regValue K.out (run (compactRecoveryConstant K control c p k) records s).basis=
      (X+(if s.basis control then k else 0))%p ∧
    ∀q,q∉K.out → (run (compactRecoveryConstant K control c p k) records s).basis q=s.basis q := by
  let load := maskedConstant control K.src k
  let u := run load [] s
  let v := run (K.program c p) (records.take (measurementCount (K.program c p))) u
  let out := run load (records.drop (measurementCount (K.program c p))) v
  let A := if s.basis control then k else 0
  have coreNd := (List.nodup_cons.mp hn).2
  have srcNd : K.src.Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have ctrlSrc : control∉K.src := by
    intro bad;exact (List.nodup_cons.mp hn).1 (by simp [MeasuredCanonicalModLayout.wires,bad])
  have protect (q : Wire) (hq : q∈control::K.out++K.carry++[K.high,K.cin,K.flag]) : q∉K.src := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have notOut (q : Wire) (hq : q∈control::K.src++K.carry++[K.high,K.cin,K.flag]) : q∉K.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have kb : k<2^K.src.length := by rw [hw.src];omega
  have loaded := maskedConstant_correct control K.src k srcNd ctrlSrc kb s []
  have srcU : regValue K.src u.basis=A := by simpa [hs,A] using loaded.2.2
  have ctrlU : u.basis control=s.basis control := loaded.2.1 control ctrlSrc
  have outU : regValue K.out u.basis=X :=
    (regValue_congr _ _ _ (fun q hq => loaded.2.1 q (protect q (by simp [hq])))).trans hx
  have highU : u.basis K.high=false := (loaded.2.1 K.high (protect K.high (by simp))).trans hh
  have flagU : u.basis K.flag=false := (loaded.2.1 K.flag (protect K.flag (by simp))).trans hf
  have cinU : u.basis K.cin=false := (loaded.2.1 K.cin (protect K.cin (by simp))).trans hi
  have carryU : ∀q∈K.carry,u.basis q=false := by
    intro q hq;exact (loaded.2.1 q (protect q (by simp [hq]))).trans (hc q hq)
  have ab : A<p := by dsimp [A];split;exact hk;omega
  have core := K.program_correct n c p hw coreNd npos hpc hcpos A X ab hX u
    (records.take (measurementCount (K.program c p))) srcU outU highU flagU carryU cinU
  have srcV : regValue K.src v.basis=A :=
    (regValue_congr _ _ _ (fun q hq => core.2.2 q (notOut q (by simp [hq])))).trans srcU
  have ctrlV : v.basis control=s.basis control := (core.2.2 control (notOut control (by simp))).trans ctrlU
  have unloaded := maskedConstant_correct control K.src k srcNd ctrlSrc kb v
    (records.drop (measurementCount (K.program c p)))
  have srcOut : regValue K.src out.basis=0 := by
    simpa [srcV,ctrlV,A] using unloaded.2.2
  have value : regValue K.out out.basis=(X+A)%p := by
    have h := (regValue_congr _ _ _ (fun q hq => unloaded.2.1 q (protect q (by simp [hq])))).trans core.2.1
    simpa [Nat.add_comm] using h
  have final : out.phase=s.phase ∧ regValue K.out out.basis=(X+A)%p ∧
      ∀q,q∉K.out → out.basis q=s.basis q := by
    refine ⟨unloaded.1.trans (core.1.trans loaded.1),value,?_⟩
    intro q hq
    by_cases source : q∈K.src
    · exact ((regValue_zero _ _).mp srcOut q source).trans ((regValue_zero _ _).mp hs q source).symm
    · exact (unloaded.2.1 q source).trans ((core.2.2 q hq).trans (loaded.2.1 q source))
  have lm := (maskedConstant_counts control K.src k).2
  simpa [compactRecoveryConstant,load,u,v,out,A,run_append,lm] using final

theorem compactRecoveryConstant_counts (K : MeasuredCanonicalModLayout) (control : Wire)
    (n c p k : Nat) (hw : K.Widths n) (npos : 0<n) :
    toffoliCount (compactRecoveryConstant K control c p k)=4*n-1 ∧
    measurementCount (compactRecoveryConstant K control c p k)=4*n-1 := by
  have h := K.program_counts n c p hw npos
  have mask := maskedConstant_counts control K.src k
  simp [compactRecoveryConstant,h.1,h.2,mask.1,mask.2]

theorem compactRecoveryConstant_support (K : MeasuredCanonicalModLayout) (control : Wire) (c p k : Nat) :
    wires (compactRecoveryConstant K control c p k)⊆(control::K.wires).toFinset := by
  have mask := maskedConstant_wires_subset control K.src k
  have core := K.program_wires_subset c p
  have e1 : (control::K.src).toFinset⊆(control::K.wires).toFinset := by
    intro q hq;simp [MeasuredCanonicalModLayout.wires] at hq ⊢;tauto
  have e2 : K.wires.toFinset⊆(control::K.wires).toFinset := by intro q hq;simp [hq]
  have a := mask.trans e1
  have b := core.trans e2
  simpa only [compactRecoveryConstant,wires_append,Finset.union_subset_iff] using And.intro (And.intro a b) a

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactRecoveryNegate.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

theorem xorConstant_ones (word : List Wire) :
    xorConstant word (2^word.length-1)=notRegister word := by
  induction word with
  | nil => rfl
  | cons q qs ih =>
    have pos := Nat.two_pow_pos qs.length
    have value : 2^(qs.length+1)-1=2*(2^qs.length-1)+1 := by rw [Nat.pow_succ];omega
    simp only [List.length_cons,value,xorConstant,Nat.add_mod,Nat.mul_mod,Nat.mod_self,
      Nat.zero_mul,Nat.zero_add,Nat.mod_eq_of_lt (by decide : 1<2),if_true]
    have half : (2*(2^qs.length-1)+1)/2=2^qs.length-1 := by omega
    rw [half,ih]
    rfl

structure CompactRecoveryNegateLayout where
  word : List Wire
  work : List Wire
  cin : Wire
  zero : Wire

namespace CompactRecoveryNegateLayout

def wires (L : CompactRecoveryNegateLayout) (control : Wire) : List Wire :=
  control::L.cin::L.zero::(L.word++L.work)
def carries (L : CompactRecoveryNegateLayout) : List Wire := L.work.take (L.word.length-1)
def checkZero (L : CompactRecoveryNegateLayout) (control : Wire) : Program :=
  equalConstant control L.zero (zeroPorts L.word L.work) 0
def complement (L : CompactRecoveryNegateLayout) (control : Wire) : Program :=
  maskedConstant control L.word (2^L.word.length-1)
def add (L : CompactRecoveryNegateLayout) (control : Wire) (k : Nat) : Program :=
  mappedConstAdd (some control) L.word L.carries L.cin k
def program (L : CompactRecoveryNegateLayout) (control : Wire) (p c : Nat) : Program :=
  L.checkZero control++L.complement control++L.add control (p+1)++L.add L.zero c++L.checkZero control

def mutable (L : CompactRecoveryNegateLayout) : List Wire := L.word++[L.zero]
def Frame (L : CompactRecoveryNegateLayout) (base : BasisState) (X : Nat) (Z : Bool)
    (s : BasisState) : Prop := regValue L.word s=X ∧ s L.zero=Z ∧ ∀q,q∉L.mutable → s q=base q

theorem known_away (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (q : Wire) (hq : q∈control::L.cin::L.work) : q∉L.mutable := by
  intro bad
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [wires,mutable,List.count_cons,List.count_append,List.count_nil] at h a b
  omega

theorem zero_away (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) : L.zero∉L.word := by
  intro bad
  have h := List.nodup_iff_count.mp hn L.zero
  have pos := List.count_pos_iff.mpr bad
  simp only [wires,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
  omega

theorem Frame.clean (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (base s : BasisState) (X : Nat) (Z : Bool)
    (hf : L.Frame base X Z s) (hc : regValue L.work base=0) (hi : base L.cin=false) :
    (∀q∈L.work,s q=false) ∧ s L.cin=false ∧ s control=base control := by
  refine ⟨?_,?_,?_⟩
  · intro q hq
    exact (hf.2.2 q (L.known_away control hn q (by simp [hq]))).trans ((regValue_zero _ _).mp hc q hq)
  · exact (hf.2.2 L.cin (L.known_away control hn L.cin (by simp))).trans hi
  · exact hf.2.2 control (L.known_away control hn control (by simp))

theorem checkZero_frame (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length)
    (base : BasisState) (X : Nat) (Z : Bool) (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X Z) (L.checkZero control)
      (L.Frame base X (Z ^^ (base control && decide (X=0)))) := by
  have maps := zeroPorts_maps L.word L.work hw.symm
  have nd : (control::L.zero::(zeroPorts L.word L.work).flatMap ZeroBit.wires).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have eq := (zeroPorts_perm L.word L.work hw.symm).count_eq q
    simp only [wires,List.count_cons,List.count_append] at h ⊢
    rw [eq]
    simp only [List.count_append]
    omega
  have length : (zeroPorts L.word L.work).length=L.word.length := by
    simpa only [List.length_map] using congrArg List.length maps.1
  intro s m hf
  have clean := Frame.clean L control hn base s.basis X Z hf hc hi
  have zeroWork : ∀b∈zeroPorts L.word L.work,s.basis b.work=false := by
    intro b hb
    apply clean.1 b.work
    rw [←maps.2]
    exact List.mem_map.mpr ⟨b,hb,rfl⟩
  have result := equalConstant_correct control L.zero (zeroPorts L.word L.work) 0 nd
    (by rw [length];exact Nat.two_pow_pos _) s m zeroWork
  rw [checkZero,result]
  refine ⟨rfl,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    simp [writeBit,show q≠L.zero from fun bad => L.zero_away control hn (bad ▸ hq)]
  · simp [writeBit,maps.1,hf.1,hf.2.1,clean.2.2]
  · intro q hq
    have ne : q≠L.zero := fun bad => hq (by simp [mutable,bad])
    simpa [writeBit,ne] using hf.2.2 q hq

theorem complement_frame (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (base : BasisState) (X : Nat) (Z : Bool)
    (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X Z) (L.complement control)
      (L.Frame base (if base control then 2^L.word.length-1-X else X) Z) := by
  have nd : L.word.Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    simp only [wires,List.count_cons,List.count_append] at h
    omega
  have ctrlAway : control∉L.word := fun bad => L.known_away control hn control (by simp) (by simp [mutable,bad])
  intro s m hf
  have clean := Frame.clean L control hn base s.basis X Z hf hc hi
  simp only [complement,maskedConstant_run control L.word _ ctrlAway,xorConstant_ones,clean.2.2]
  cases hb : base control
  · exact ⟨rfl,hf⟩
  · rw [notRegister_correct L.word nd]
    refine ⟨rfl,?_,?_,?_⟩
    · have value : regValue L.word (fun q => if q∈L.word then !s.basis q else s.basis q)=
          2^L.word.length-1-regValue L.word s.basis := by
        rw [regValue_congr _ _ (fun q => !s.basis q) (by intro q hq;simp [hq]),regValue_complement]
      simpa [hb,hf.1] using value
    · simpa [L.zero_away control hn] using hf.2.1
    · intro q hq
      have notWord : q∉L.word := fun bad => hq (by simp [mutable,bad])
      simpa [notWord] using hf.2.2 q hq

theorem add_frame (L : CompactRecoveryNegateLayout) (control selector : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (hnpos : 0<L.word.length)
    (hsel : selector=control ∨ selector=L.zero) (k : Nat) (hk : k<2^L.word.length)
    (base : BasisState) (X : Nat) (Z : Bool) (E : Bool)
    (henabled : E=if selector=L.zero then Z else base control)
    (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X Z) (L.add selector k)
      (L.Frame base (((if E then k else 0)+X)%2^L.word.length) Z) := by
  have nd : (L.cin::L.word++L.carries).Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    have bound := (List.take_sublist (L.word.length-1) L.work).count_le q
    simp only [wires,carries,List.count_cons,List.count_append] at h ⊢
    omega
  have away : ∀q∈some selector,q∉L.cin::L.word++L.carries := by
    intro q hq bad
    have eq : q=selector := by simpa [eq_comm] using hq
    subst q
    have h := List.nodup_iff_count.mp hn selector
    have pos := List.count_pos_iff.mpr bad
    have bound := (List.take_sublist (L.word.length-1) L.work).count_le selector
    simp only [wires,carries,List.count_cons,List.count_append] at h pos
    rcases hsel with rfl|rfl <;> simp only [beq_self_eq_true,if_true] at h <;> omega
  have len : L.carries.length+1=L.word.length := by simp [carries,hw];omega
  intro s m hf
  have clean := Frame.clean L control hn base s.basis X Z hf hc hi
  have selValue : s.basis selector=E := by
    rw [henabled]
    rcases hsel with hsel|hsel
    · subst selector
      have ne : control≠L.zero := by
        intro bad;have h := List.nodup_iff_count.mp hn control
        simp only [wires,bad,List.count_cons,beq_self_eq_true,if_true] at h
        omega
      simp [ne,clean.2.2]
    · rw [hsel]
      simp [hf.2.1]
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct (some selector) L.word L.carries L.cin k nd away len hk s m
    (fun q hq => clean.1 q (List.mem_of_mem_take hq))
  refine ⟨phase,?_,(same L.zero (L.zero_away control hn)).trans hf.2.1,?_⟩
  · simpa [mappedEnabled,selValue,hf.1,clean.2.1] using value
  · intro q hq
    exact (same q (fun bad => hq (by simp [mutable,bad]))).trans (hf.2.2 q hq)

end CompactRecoveryNegateLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/CompactRecoveryNegate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

def compactNegateValue (N p c X : Nat) (enabled : Bool) : Nat :=
  ((if enabled && decide (X=0) then c else 0)+
    ((if enabled then p+1 else 0)+(if enabled then N-1-X else X))%N)%N

theorem compactNegateValue_exact (N p c X : Nat) (enabled : Bool)
    (hpc : p+c=N) (hc : 1<c) (hX : X<p) :
    compactNegateValue N p c X enabled=(if enabled then (p-X)%p else X) := by
  have hp : 0<p := by omega
  have hn : X<N := by omega
  cases enabled
  · simp [compactNegateValue,Nat.mod_eq_of_lt hn]
  · by_cases zero : X=0
    · subst X
      have pb : p<N := by omega
      have sum : p+1+(N-1)=p+N := by omega
      simp only [compactNegateValue,if_true,Bool.true_and,decide_true,Nat.sub_zero]
      rw [sum,Nat.add_mod_right,Nat.mod_eq_of_lt pb,show c+p=N by omega,Nat.mod_self,Nat.mod_self]
    · have pn : p-X<N := by omega
      have pp : p-X<p := by omega
      have sum : p+1+(N-1-X)=N+(p-X) := by omega
      simp only [compactNegateValue,if_true,Bool.true_and,zero,decide_false,Bool.false_eq_true,if_false,Nat.zero_add]
      rw [sum,Nat.add_mod_left,Nat.mod_eq_of_lt pn,Nat.mod_eq_of_lt pn,Nat.mod_eq_of_lt pp]

theorem compactNegateValue_zero (N p c X : Nat) (enabled : Bool)
    (hpc : p+c=N) (hc : 1<c) (hX : X<p) :
    (enabled && decide (compactNegateValue N p c X enabled=0))=(enabled && decide (X=0)) := by
  rw [compactNegateValue_exact N p c X enabled hpc hc hX]
  cases enabled
  · rfl
  · by_cases zero : X=0
    · simp [zero]
    · have pp : p-X<p := by omega
      have nonzero : p-X≠0 := by omega
      simp [zero,Nat.mod_eq_of_lt pp,nonzero]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompactRecoveryNegateProof.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout

theorem program_frame (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (npos : 0<L.word.length)
    (p c X : Nat) (hpc : p+c=2^L.word.length) (hcpos : 1<c) (hX : X<p)
    (base : BasisState) (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X false) (L.program control p c)
      (L.Frame base (if base control then (p-X)%p else X) false) := by
  let B := base control
  let D := B && decide (X=0)
  let X1 := if B then 2^L.word.length-1-X else X
  let X2 := ((if B then p+1 else 0)+X1)%2^L.word.length
  let X3 := ((if D then c else 0)+X2)%2^L.word.length
  have pcBound : p+1<2^L.word.length := by omega
  have cBound : c<2^L.word.length := by omega
  have ne : control≠L.zero := by
    intro bad;have h := List.nodup_iff_count.mp hn control
    simp only [wires,bad,List.count_cons,beq_self_eq_true,if_true] at h
    omega
  have zero := L.checkZero_frame control hn hw base X false hc hi
  simp only [Bool.false_xor] at zero
  have flip := L.complement_frame control hn base X D hc hi
  have add1 := L.add_frame control control hn hw npos (Or.inl rfl) (p+1) pcBound base X1 D B
    (by simp [ne,B]) hc hi
  have add2 := L.add_frame control L.zero hn hw npos (Or.inr rfl) c cBound base X2 D D
    (by simp) hc hi
  have clear := L.checkZero_frame control hn hw base X3 D hc hi
  have eq : X3=(if B then (p-X)%p else X) :=
    compactNegateValue_exact _ p c X B hpc hcpos hX
  have sameZero : (B && decide (X3=0))=D :=
    compactNegateValue_zero _ p c X B hpc hcpos hX
  change Triple (L.Frame base X3 D) (L.checkZero control)
    (L.Frame base X3 (D ^^ (B && decide (X3=0)))) at clear
  rw [sameZero,Bool.xor_self] at clear
  have all := (((zero.seq flip).seq add1).seq add2).seq clear
  rw [eq] at all
  exact all

/-- Direct exact canonical negation; the zero input is restored to zero,
all shared work/control sites and phase return for every measurement record. -/
theorem program_correct (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (npos : 0<L.word.length)
    (p c X : Nat) (hpc : p+c=2^L.word.length) (hcpos : 1<c) (hX : X<p)
    (s : State) (records : List Bool) (hx : regValue L.word s.basis=X)
    (hc : regValue L.work s.basis=0) (hi : s.basis L.cin=false) (hz : s.basis L.zero=false) :
    (run (L.program control p c) records s).phase=s.phase ∧
    regValue L.word (run (L.program control p c) records s).basis=
      (if s.basis control then (p-X)%p else X) ∧
    ∀q,q∉L.word → (run (L.program control p c) records s).basis q=s.basis q := by
  have pre : L.Frame s.basis X false s.basis := ⟨hx,hz,fun _ _ => rfl⟩
  have result := L.program_frame control hn hw npos p c X hpc hcpos hX s.basis hc hi s records pre
  refine ⟨result.1,result.2.1,?_⟩
  intro q hq
  by_cases zero : q=L.zero
  · subst q;exact result.2.2.1.trans hz.symm
  · exact result.2.2.2 q (by simpa only [mutable,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using And.intro hq zero)

theorem program_counts (L : CompactRecoveryNegateLayout) (control : Wire) (p c : Nat)
    (hw : L.work.length=L.word.length) (npos : 0<L.word.length) :
    toffoliCount (L.program control p c)=4*L.word.length-2 ∧
    measurementCount (L.program control p c)=4*L.word.length-2 := by
  have maps := zeroPorts_maps L.word L.work hw.symm
  have len : (zeroPorts L.word L.work).length=L.word.length := by
    simpa only [List.length_map] using congrArg List.length maps.1
  have carryLen : L.carries.length+1=L.word.length := by simp [carries,hw];omega
  have zero := equalConstant_counts control L.zero (zeroPorts L.word L.work) 0
  have flip := maskedConstant_counts control L.word (2^L.word.length-1)
  have add1 := mappedConstAdd_counts (some control) L.word L.carries L.cin (p+1) carryLen
  have add2 := mappedConstAdd_counts (some L.zero) L.word L.carries L.cin c carryLen
  simp only [program,checkZero,complement,add,toffoliCount_append,measurementCount_append,
    zero.1,zero.2,flip.1,flip.2,add1.1,add1.2,add2.1,add2.2,len]
  constructor <;> omega

theorem program_support (L : CompactRecoveryNegateLayout) (control : Wire) (p c : Nat)
    (hw : L.work.length=L.word.length) :
    ECDSAAdd.wires (L.program control p c)⊆(L.wires control).toFinset := by
  have eq := equalConstant_wires control L.zero (zeroPorts L.word L.work) 0
  have perm := zeroPorts_perm L.word L.work hw.symm
  have zero : ECDSAAdd.wires (L.checkZero control)⊆(L.wires control).toFinset := by
    rw [checkZero,eq,List.toFinset_cons,List.toFinset_cons,List.toFinset_eq_of_perm _ _ perm]
    intro q hq
    simp [wires] at hq ⊢
    tauto
  have flip := maskedConstant_wires_subset control L.word (2^L.word.length-1)
  have add1 := mappedConstAdd_wires_subset (some control) L.word L.carries L.cin (p+1)
  have add2 := mappedConstAdd_wires_subset (some L.zero) L.word L.carries L.cin c
  have embed (q : Wire) (hq : q∈L.carries) : q∈L.work := List.mem_of_mem_take hq
  have flipS : ECDSAAdd.wires (L.complement control)⊆(L.wires control).toFinset := by
    intro q hq;have h := flip hq
    simp [wires] at h ⊢
    tauto
  have one : ECDSAAdd.wires (L.add control (p+1))⊆(L.wires control).toFinset := by
    intro q hq;have h := add1 hq
    simp [wires] at h ⊢
    have ht : q∈L.carries → q∈L.work := embed q
    tauto
  have two : ECDSAAdd.wires (L.add L.zero c)⊆(L.wires control).toFinset := by
    intro q hq;have h := add2 hq
    simp [wires] at h ⊢
    have ht : q∈L.carries → q∈L.work := embed q
    tauto
  simpa only [program,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro zero flipS) one) two) zero

def reflection (L : CompactRecoveryNegateLayout) (control : Wire) (p : Nat) : Program :=
  L.complement control++L.add control p

/-- Conditional canonical reflection is the exact frame for fused reverse
subtraction: adding the classical offset+1 finishes offset-X without a
separate zero test or temporary quantum coordinate. -/
theorem reflection_frame (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (npos : 0<L.word.length)
    (p X : Nat) (hp : p<2^L.word.length) (hX : X<p)
    (base : BasisState) (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X false) (L.reflection control p)
      (L.Frame base (if base control then p-1-X else X) false) := by
  have ne : control≠L.zero := by
    intro bad;have h := List.nodup_iff_count.mp hn control
    simp only [wires,bad,List.count_cons,beq_self_eq_true,if_true] at h
    omega
  let V := if base control then 2^L.word.length-1-X else X
  have flip := L.complement_frame control hn base X false hc hi
  have add := L.add_frame control control hn hw npos (Or.inl rfl) p hp base V false (base control)
    (by simp [ne]) hc hi
  have value : ((if base control then p else 0)+V)%2^L.word.length=
      (if base control then p-1-X else X) := by
    cases hb : base control
    · simp [V,hb,Nat.mod_eq_of_lt (hX.trans hp)]
    · have eq : p+(2^L.word.length-1-X)=2^L.word.length+(p-1-X) := by omega
      simp only [V,hb,if_true]
      rw [eq,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
  rw [value] at add
  exact flip.seq add

theorem reflection_correct (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (npos : 0<L.word.length)
    (p X : Nat) (hp : p<2^L.word.length) (hX : X<p)
    (s : State) (records : List Bool) (hx : regValue L.word s.basis=X)
    (hc : regValue L.work s.basis=0) (hi : s.basis L.cin=false) (hz : s.basis L.zero=false) :
    (run (L.reflection control p) records s).phase=s.phase ∧
    regValue L.word (run (L.reflection control p) records s).basis=(if s.basis control then p-1-X else X) ∧
    ∀q,q∉L.word → (run (L.reflection control p) records s).basis q=s.basis q := by
  have pre : L.Frame s.basis X false s.basis := ⟨hx,hz,fun _ _ => rfl⟩
  have result := L.reflection_frame control hn hw npos p X hp hX s.basis hc hi s records pre
  refine ⟨result.1,result.2.1,?_⟩
  intro q hq
  by_cases zero : q=L.zero
  · subst q;exact result.2.2.1.trans hz.symm
  · exact result.2.2.2 q (by simpa only [mutable,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using And.intro hq zero)

theorem reflection_counts (L : CompactRecoveryNegateLayout) (control : Wire) (p : Nat)
    (hw : L.work.length=L.word.length) (npos : 0<L.word.length) :
    toffoliCount (L.reflection control p)=L.word.length-1 ∧
    measurementCount (L.reflection control p)=L.word.length-1 := by
  have carryLen : L.carries.length+1=L.word.length := by simp [carries,hw];omega
  have add := mappedConstAdd_counts (some control) L.word L.carries L.cin p carryLen
  have flip := maskedConstant_counts control L.word (2^L.word.length-1)
  simp [reflection,complement,CompactRecoveryNegateLayout.add,add.1,add.2,flip.1,flip.2]

theorem reflection_support (L : CompactRecoveryNegateLayout) (control : Wire) (p : Nat) :
    ECDSAAdd.wires (L.reflection control p)⊆(L.wires control).toFinset := by
  have flip := maskedConstant_wires_subset control L.word (2^L.word.length-1)
  have add := mappedConstAdd_wires_subset (some control) L.word L.carries L.cin p
  have a : ECDSAAdd.wires (L.complement control)⊆(L.wires control).toFinset := by
    intro q hq;have h := flip hq;simp [wires] at h ⊢;tauto
  have b : ECDSAAdd.wires (L.add control p)⊆(L.wires control).toFinset := by
    intro q hq;have h := add hq
    have take : q∈L.carries → q∈L.work := List.mem_of_mem_take
    simp [wires] at h ⊢
    tauto
  simpa only [reflection,wires_append,Finset.union_subset_iff] using And.intro a b

end ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout
end

-- source: ECDSAAdd/Arithmetic/TranscriptCodec3.lean
noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Arithmetic.TranscriptCodec3

-- Pinned incumbent codec, including its measurement phase correction.
def pack : Program := [
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 3 4,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 1,
  .X 0,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 4,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 2,
  .CX 4 0,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 1,
  .CX 1 3,
  .CX 3 1,
  .CX 0 5,
  .CX 0 4,
  .CX 0 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CCX 0 1 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CX 0 2,
  .CX 0 4,
  .CX 0 5,
  .CX 3 1,
  .CX 1 3,
  .CX 3 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 0,
  .CX 3 2,
  .CX 3 4,
  .CX 3 5,
  .CX 4 0,
  .CX 4 2,
  .CX 4 5,
  .CX 4 2,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 2 1,
  .CX 1 4,
  .CX 1 2,
  .CX 0 3,
  .CX 0 1,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 1,
  .X 0,
  .CX 0 1,
  .CX 0 3,
  .CX 1 2,
  .CX 1 4,
  .CX 2 1,
  .CX 3 0,
  .CX 3 2,
  .CX 3 4,
  .CX 4 2,
  .CX 3 1,
  .CX 3 2,
  .measureX 3 [] [.CZ 1 0]
]

def unpack : Program := [
  .CX 3 2,
  .CX 3 1,
  .CX 3 2,
  .CX 2 3,
  .CX 3 2,
  .CX 1 3,
  .CX 1 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CCX 0 1 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CX 1 2,
  .CX 1 3,
  .CX 3 2,
  .CX 2 3,
  .CX 3 2,
  .CX 3 1,
  .CX 3 2,
  .CX 4 2,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 2 1,
  .CX 1 4,
  .CX 1 2,
  .CX 0 3,
  .CX 0 1,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 1,
  .X 0,
  .CX 0 1,
  .CX 0 3,
  .CX 1 2,
  .CX 1 4,
  .CX 2 1,
  .CX 3 0,
  .CX 3 2,
  .CX 3 4,
  .CX 4 2,
  .CX 4 5,
  .CX 4 2,
  .CX 4 0,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 1,
  .CX 1 3,
  .CX 3 1,
  .CX 0 5,
  .CX 0 4,
  .CX 0 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CCX 0 1 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CX 0 2,
  .CX 0 4,
  .CX 0 5,
  .CX 3 1,
  .CX 1 3,
  .CX 3 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 0,
  .CX 3 2,
  .CX 3 4,
  .CX 3 5,
  .CX 4 0,
  .CX 4 2,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 3 4,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 1,
  .X 0,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 4,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4
]

def raw (a b c d e f : Bool) : BasisState := fun q =>
  if q=0 then a else if q=1 then b else if q=2 then c else
    if q=3 then d else if q=4 then e else if q=5 then f else false

def legal (s : BasisState) : Prop :=
  (s 0 && s 1)=false ∧ (s 2 && s 3)=false ∧ (s 4 && s 5)=false

def kernel : Program := pack ++ unpack

theorem counts : toffoliCount pack=3 ∧ measurementCount pack=1 ∧
    toffoliCount unpack=4 ∧ measurementCount unpack=0 := by decide

theorem support : wires pack=Finset.range 6 ∧ wires unpack=Finset.range 6 := by decide

-- Finite kernel theorem, covering all legal words, measurement outcomes,
-- missing/default measurement records, and both incoming phases.
theorem finite_interface : ∀ (a b c d e f ph : Bool) (record : Option Bool),
    legal (raw a b c d e f) →
    (run pack record.toList ⟨ph,raw a b c d e f⟩).phase=ph ∧
    (run pack record.toList ⟨ph,raw a b c d e f⟩).basis 3=false ∧
    (run kernel record.toList ⟨ph,raw a b c d e f⟩).phase=ph ∧
    ∀ q : Fin 6, (run kernel record.toList ⟨ph,raw a b c d e f⟩).basis q=
      raw a b c d e f q := by unfold legal; decide

attribute [local irreducible] run pack unpack kernel

private theorem records (p : Program) (hm : measurementCount p=1)
    (m : List Bool) (s : State) : run p m s=run p m.head?.toList s := by
  rw [← run_take p m s,hm]
  cases m <;> rfl

theorem fixed_correct (s : State) (m : List Bool) (h : legal s.basis) :
    (run pack m s).phase=s.phase ∧ (run pack m s).basis 3=false ∧
    run kernel m s=s := by
  let t : State := ⟨s.phase,raw (s.basis 0) (s.basis 1) (s.basis 2)
    (s.basis 3) (s.basis 4) (s.basis 5)⟩
  have hb : ∀ q∈Finset.range 6,s.basis q=t.basis q := by
    intro q hq
    have hq6 := Finset.mem_range.mp hq
    interval_cases q <;> simp [t,raw]
  have ht : legal t.basis := by simpa [t,legal,raw] using h
  have finite := finite_interface (s.basis 0) (s.basis 1) (s.basis 2)
    (s.basis 3) (s.basis 4) (s.basis 5) s.phase m.head? ht
  have hs : wires kernel=Finset.range 6 := by
    simp only [kernel,wires_append,support.1,support.2,Finset.union_self]
  have hc : measurementCount kernel=1 := by
    simp only [kernel,measurementCount_append,counts.2.1,counts.2.2.2,Nat.add_zero]
  have pp := pool_run_agrees pack (Finset.range 6) (by rw [support.1]) m s t rfl hb
  have kk := pool_run_agrees kernel (Finset.range 6) (by rw [hs]) m s t rfl hb
  have pk : run pack m t=run pack m.head?.toList t := records pack counts.2.1 m t
  have rk : run kernel m t=run kernel m.head?.toList t := records kernel hc m t
  refine ⟨pp.1.trans ?_,(pp.2 3 (by decide)).trans ?_,?_⟩
  · rw [pk]; exact finite.1
  · rw [pk]; exact finite.2.1
  · have ph : (run kernel m s).phase=s.phase := by
      rw [kk.1,rk]; exact finite.2.2.1
    have bits : (run kernel m s).basis=s.basis := by
      funext q
      by_cases hq : q<6
      · have kq := kk.2 q (Finset.mem_range.mpr hq)
        rw [rk] at kq
        exact kq.trans ((finite.2.2.2 ⟨q,hq⟩).trans (hb q (Finset.mem_range.mpr hq)).symm)
      · apply run_preserves_outside
        rw [hs]; simpa using hq
    exact State.extensionality _ _ ph bits

/-- Relabeling this six-site component also preserves the caller's phase.
An injective map forbids silent aliases between raw transcript sites. -/
theorem placed_roundtrip (f : Wire → Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legal (pullState f s).basis) :
    (run (renameProgram f pack) m s).phase=s.phase ∧
    (run (renameProgram f pack) m s).basis (f 3)=false ∧
    pullState f (run (renameProgram f kernel) m s)=pullState f s := by
  have hc := fixed_correct (pullState f s) m h
  have hp := run_rename f hf pack m s
  have hk := run_rename f hf kernel m s
  refine ⟨?_,?_,hk.trans hc.2.2⟩
  · exact (congrArg State.phase hp).trans hc.1
  · exact (congrArg (fun st : State => st.basis 3) hp).trans hc.2.1

/-- Full caller state, including every unrelated register, is restored.
This is stronger than equality of only the six transcript bits. -/
theorem placed_state (f : Wire → Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legal (pullState f s).basis) :
    run (renameProgram f kernel) m s=s := by
  have hc := (placed_roundtrip f hf s m h).2.2
  apply State.extensionality
  · simpa only [pullState] using congrArg State.phase hc
  · funext q
    by_cases hq : q∈wires (renameProgram f kernel)
    · rw [renameProgram_support] at hq
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
      simpa only [pullState] using congrArg (fun st : State => st.basis j) hc
    · exact run_preserves_outside _ _ _ q hq

end ECDSAAdd.Arithmetic.TranscriptCodec3
end

-- source: ECDSAAdd/Arithmetic/TranscriptCodecPlacement.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.TranscriptCodec3

/-- A six-site placement is extended to a permutation of all wire labels.
The caller's history sites lie above the six local template labels. -/
def placement (w : Fin 6 → Wire) : Equiv.Perm Wire :=
  (Equiv.swap 0 (w 0)).trans ((Equiv.swap 1 (w 1)).trans
    ((Equiv.swap 2 (w 2)).trans ((Equiv.swap 3 (w 3)).trans
      ((Equiv.swap 4 (w 4)).trans (Equiv.swap 5 (w 5))))))

theorem placement_apply (w : Fin 6 → Wire) (hn : Function.Injective w)
    (hlo : ∀ i,6≤w i) (i : Fin 6) : placement w i=w i := by
  have small (i : Fin 6) (j : Nat) (hj : j<6) : w i≠j := by
    exact Ne.symm (ne_of_lt (lt_of_lt_of_le hj (hlo i)))
  have revSmall (j : Nat) (hj : j<6) (i : Fin 6) : j≠w i :=
    Ne.symm (small i j hj)
  fin_cases i <;> simp [placement,Equiv.swap_apply_def,hn.eq_iff,small,revSmall]

def encode (w : Fin 6 → Wire) : Program := renameProgram (placement w) pack
def decode (w : Fin 6 → Wire) : Program := renameProgram (placement w) unpack

theorem placement_counts (w : Fin 6 → Wire) :
    toffoliCount (encode w)=3 ∧ measurementCount (encode w)=1 ∧
    toffoliCount (decode w)=4 ∧ measurementCount (decode w)=0 := by
  have hp := renameProgram_counts (placement w) pack
  have hu := renameProgram_counts (placement w) unpack
  exact ⟨hp.1.trans counts.1,hp.2.trans counts.2.1,
    hu.1.trans counts.2.2.1,hu.2.trans counts.2.2.2⟩

/-- Exact compressed-history interface on six distinct caller sites. The
fourth site is clean after encode, and decode restores the whole caller state. -/
theorem placement_correct (w : Fin 6 → Wire) (hn : Function.Injective w)
    (hlo : ∀ i,6≤w i) (s : State) (m : List Bool)
    (hraw : (s.basis (w 0) && s.basis (w 1))=false ∧
      (s.basis (w 2) && s.basis (w 3))=false ∧
      (s.basis (w 4) && s.basis (w 5))=false) :
    (run (encode w) m s).phase=s.phase ∧
    (run (encode w) m s).basis (w 3)=false ∧
    run (encode w++decode w) m s=s := by
  have hi : legal (pullState (placement w) s).basis := by
    unfold legal pullState
    dsimp only
    have h0 := placement_apply w hn hlo 0
    have h1 := placement_apply w hn hlo 1
    have h2 := placement_apply w hn hlo 2
    have h3 := placement_apply w hn hlo 3
    have h4 := placement_apply w hn hlo 4
    have h5 := placement_apply w hn hlo 5
    change placement w (0 : Wire)=w 0 at h0
    change placement w (1 : Wire)=w 1 at h1
    change placement w (2 : Wire)=w 2 at h2
    change placement w (3 : Wire)=w 3 at h3
    change placement w (4 : Wire)=w 4 at h4
    change placement w (5 : Wire)=w 5 at h5
    rw [h0,h1,h2,h3,h4,h5]
    exact hraw
  have c := placed_roundtrip (placement w) (placement w).injective s m hi
  have state := placed_state (placement w) (placement w).injective s m hi
  have h3 : placement w 3=w 3 := placement_apply w hn hlo 3
  refine ⟨c.1,?_,?_⟩
  · change (run (renameProgram (placement w) pack) m s).basis (w 3)=false
    rw [← h3]
    exact c.2.1
  · simpa only [encode,decode,kernel,renameProgram,List.map_append] using state

private theorem decode_records (w : Fin 6 → Wire) (s : State) (m : List Bool) :
    run (decode w) m s=run (decode w) [] s := by
  rw [← run_take (decode w) m s,(placement_counts w).2.2.2]
  rfl

/-- The decoder uses no measurements. Its record is independent of the
encoder's record, including when either supplied list is empty. -/
theorem decode_encode (w : Fin 6 → Wire) (hn : Function.Injective w)
    (hlo : ∀ i,6≤w i) (s : State) (mE mD : List Bool)
    (hraw : (s.basis (w 0) && s.basis (w 1))=false ∧
      (s.basis (w 2) && s.basis (w 3))=false ∧
      (s.basis (w 4) && s.basis (w 5))=false) :
    run (decode w) mD (run (encode w) mE s)=s := by
  have h := (placement_correct w hn hlo s mE hraw).2.2
  rw [run_append] at h
  rw [run_take] at h
  rw [decode_records] at h
  rw [decode_records]
  exact h

/-- A decoded field window executes the original body on the original caller
state, then re-encodes its output. No arithmetic oracle is introduced. -/
theorem window_states (w : Fin 6 → Wire) (hn : Function.Injective w)
    (hlo : ∀ i,6≤w i) (body : Program) (s : State) (m0 m1 m2 m3 : List Bool)
    (hraw : (s.basis (w 0) && s.basis (w 1))=false ∧
      (s.basis (w 2) && s.basis (w 3))=false ∧
      (s.basis (w 4) && s.basis (w 5))=false) :
    run (encode w) m3 (run body m2 (run (decode w) m1 (run (encode w) m0 s)))=
      run (encode w) m3 (run body m2 s) := by
  rw [decode_encode w hn hlo s m0 m1 hraw]

end ECDSAAdd.Arithmetic.TranscriptCodec3
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- Three adjacent (orientation, sign) history pairs, interleaved for the
six-site codec. These are actual integer-pool sites, not extra registers. -/
def compressedHistoryId (start : Nat) (q : Fin 6) : Nat :=
  if q.val%2=0 then start+q.val/2 else 1028+start+q.val/2

def compressedHistoryMap (w : Nat → Wire) (start : Nat) : Fin 6 → Wire :=
  fun q => w (compressedHistoryId start q)

/-- Only history labels need to avoid the local codec template labels.
The divisor rail may therefore occupy the caller's original X register. -/
def CompressedHistoryAbove (w : Nat → Wire) : Prop :=
  ∀ j,(j < 512 ∨ (1028 ≤ j ∧ j < 1540)) → 6 ≤ w j

theorem compressedHistoryId_region (start : Nat) (hs : start+3 ≤ 512) (q : Fin 6) :
    compressedHistoryId start q < 512 ∨
      (1028 ≤ compressedHistoryId start q ∧ compressedHistoryId start q < 1540) := by
  have hq := q.isLt
  unfold compressedHistoryId
  split
  · left; omega
  · right; constructor <;> omega

theorem compressedHistoryId_bound (start : Nat) (hs : start+3 ≤ 512) (q : Fin 6) :
    compressedHistoryId start q < 1798 := by
  have hq := q.isLt
  unfold compressedHistoryId
  split  <;> omega

theorem compressedHistoryMap_injective (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (start : Nat) (hs : start+3 ≤ 512) :
    Function.Injective (compressedHistoryMap w start) := by
  intro a b he
  have hid := skywalkPool_index_inj w hn _ _
    (compressedHistoryId_bound start hs a) (compressedHistoryId_bound start hs b) he
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  unfold compressedHistoryId at hid
  split_ifs at hid  <;> omega

theorem compressedHistoryMap_above (w : Nat → Wire) (start : Nat) (hs : start+3 ≤ 512)
    (hlo : CompressedHistoryAbove w) : ∀ q,6 ≤ compressedHistoryMap w start q :=
  fun q => hlo _ (compressedHistoryId_region start hs q)

theorem skywalkRecordedSymbol_legal (x p j : Nat) (hp0 : 0 < p) (hpo : p%2=1) :
    let c := SkywalkTrace.code (SkywalkTrace.next^[j]
      (SkywalkRails.encode false false (x:Int) (p:Int)))
    (c.1 && c.2)=false := by
  dsimp only
  let z := SkywalkNat.step^[j] (SkywalkNat.init x p)
  have hc := SkywalkTrace.iter_code_classified j false false (SkywalkNat.init x p) hp0 hpo
  dsimp only [SkywalkNat.init] at hc
  have hg : (SkywalkTrace.code (SkywalkTrace.next^[j]
      (SkywalkRails.encode false false (x:Int) (p:Int)))).1=decide (z.u%2=0) := hc.1
  rw [hg]
  by_cases he : z.u%2=0
  · have hs := hc.2.1 he
    simp only [hs,Bool.and_false]
  · simp only [he,decide_false,Bool.false_and]

def compressedHistoryEncode (w : Nat → Wire) (start : Nat) : Program :=
  TranscriptCodec3.encode (compressedHistoryMap w start)

def compressedHistoryDecode (w : Nat → Wire) (start : Nat) : Program :=
  TranscriptCodec3.decode (compressedHistoryMap w start)

theorem compressedHistory_counts (w : Nat → Wire) (start : Nat) :
    toffoliCount (compressedHistoryEncode w start)=3 ∧
    measurementCount (compressedHistoryEncode w start)=1 ∧
    toffoliCount (compressedHistoryDecode w start)=4 ∧
    measurementCount (compressedHistoryDecode w start)=0 :=
  TranscriptCodec3.placement_counts (compressedHistoryMap w start)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkLoop.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- A group is packed one tick after its final orientation was consumed.
For 512 ticks the packed starts are 0,3,...,507; 510 and 511 stay raw. -/
def compressedPackDue (i : Nat) : Bool := decide (3 ≤ i ∧ i%3=0)

def compressedPackAfter (w : Nat → Wire) (i : Nat) : Program :=
  if compressedPackDue i then compressedHistoryEncode w (i-3) else []

def compressedDecodeBefore (w : Nat → Wire) (i : Nat) : Program :=
  if compressedPackDue i then compressedHistoryDecode w (i-3) else []

def compressedPackCount (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (if compressedPackDue i then 1 else 0)+compressedPackCount (i+1) n

theorem compressedPackAfter_counts (w : Nat → Wire) (i : Nat) :
    toffoliCount (compressedPackAfter w i)=3*(if compressedPackDue i then 1 else 0) ∧
    measurementCount (compressedPackAfter w i)=(if compressedPackDue i then 1 else 0) ∧
    toffoliCount (compressedDecodeBefore w i)=4*(if compressedPackDue i then 1 else 0) ∧
    measurementCount (compressedDecodeBefore w i)=0 := by
  have hc := compressedHistory_counts w (i-3)
  cases he : compressedPackDue i
  · simp [compressedPackAfter,compressedDecodeBefore,he,toffoliCount,measurementCount]
  · simpa [compressedPackAfter,compressedDecodeBefore,he] using hc

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DisjointPrograms.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

def phaseShift (d : Bool) (s : State) : State := ⟨s.phase ^^ d,s.basis⟩

private theorem xor_reorder (a b c : Bool) : ((a ^^ b) ^^ c)=((a ^^ c) ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem correct_phaseShift (cs : List Correction) (d : Bool) (s : State) :
    correct cs (phaseShift d s)=phaseShift d (correct cs s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z q =>
      simp only [correct,phaseShift]
      rw [xor_reorder]
      exact ih ⟨s.phase ^^ s.basis q,s.basis⟩
    | CZ a b =>
      simp only [correct,phaseShift]
      rw [xor_reorder]
      exact ih ⟨s.phase ^^ (s.basis a && s.basis b),s.basis⟩

theorem measure_phaseShift (q : Wire) (c0 c1 : List Correction)
    (d m : Bool) (s : State) :
    measureAndCorrect q c0 c1 m (phaseShift d s)=
      phaseShift d (measureAndCorrect q c0 c1 m s) := by
  unfold measureAndCorrect
  change correct _ ⟨(s.phase ^^ d) ^^ (m && s.basis q),writeBit s.basis q false⟩=_
  rw [xor_reorder]
  exact correct_phaseShift (if m then c1 else c0) d
    ⟨s.phase ^^ (m && s.basis q),writeBit s.basis q false⟩

theorem run_phaseShift (p : Program) (m : List Bool) (d : Bool) (s : State) :
    run p m (phaseShift d s)=phaseShift d (run p m s) := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X q =>
      simpa only [run,phaseShift] using ih m ⟨s.phase,writeBit s.basis q (!s.basis q)⟩
    | CX a q =>
      simpa only [run,phaseShift] using ih m ⟨s.phase,writeBit s.basis q (s.basis q ^^ s.basis a)⟩
    | CCX a b q =>
      simpa only [run,phaseShift] using ih m
        ⟨s.phase,writeBit s.basis q (s.basis q ^^ (s.basis a && s.basis b))⟩
    | measureX q c0 c1 =>
      simp only [run]
      rw [measure_phaseShift]
      exact ih m.tail (measureAndCorrect q c0 c1 (m.headD false) s)

/-- Basis behavior is independent of the supplied measurement outcomes.
Outcome dependence is confined to the separately tracked phase. -/
theorem run_basis_records (p : Program) (s t : State) (m n : List Bool)
    (hb : s.basis=t.basis) : (run p m s).basis=(run p n t).basis := by
  induction p generalizing s t m n with
  | nil => exact hb
  | cons i p ih =>
    cases i <;> simp only [run]
    all_goals apply ih
    all_goals first
      | simp only [hb]
      | simp only [measureAndCorrect,correct_basis,hb]

/-- Local basis agreement preserves the circuit's phase increment, even when
the surrounding caller states have different incoming phases. -/
theorem run_local_increment (p : Program) (s t : State) (m : List Bool)
    (hb : ∀ q∈wires p,s.basis q=t.basis q) :
    ((run p m s).phase ^^ s.phase)=((run p m t).phase ^^ t.phase) ∧
    ∀ q∈wires p,(run p m s).basis q=(run p m t).basis q := by
  let d := s.phase ^^ t.phase
  let u := phaseShift d t
  have ph : s.phase=u.phase := by
    change s.phase=(t.phase ^^ (s.phase ^^ t.phase))
    cases s.phase <;> cases t.phase <;> rfl
  have hbits : ∀ q∈wires p,s.basis q=u.basis q := hb
  have hr := pool_run_agrees p (wires p) (Finset.Subset.refl _) m s u ph hbits
  have hu : run p m u=phaseShift d (run p m t) := run_phaseShift p m d t
  rw [hu] at hr
  have hp : (run p m s).phase=((run p m t).phase ^^ (s.phase ^^ t.phase)) := hr.1
  refine ⟨?_,hr.2⟩
  rw [hp]
  cases s.phase <;> cases t.phase <;> cases (run p m t).phase <;> rfl

private theorem phase_commutation (a b c d e : Bool)
    (h1 : (a ^^ b)=(c ^^ d)) (h2 : (e ^^ c)=(b ^^ d)) : a=e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all

/-- Disjoint gate supports commute, including their measurement corrections.
Each block retains its own independent record list. -/
theorem run_disjoint_commute (p q : Program) (hd : Disjoint (wires p) (wires q))
    (mp mq : List Bool) (s : State) :
    run p mp (run q mq s)=run q mq (run p mp s) := by
  have pRead : ∀ a∈wires p,(run q mq s).basis a=s.basis a := by
    intro a ha
    apply run_preserves_outside
    exact fun hq => Finset.disjoint_left.mp hd ha hq
  have qRead : ∀ a∈wires q,(run p mp s).basis a=s.basis a := by
    intro a ha
    apply run_preserves_outside
    exact fun hp => Finset.disjoint_left.mp hd hp ha
  have hp := run_local_increment p (run q mq s) s mp pRead
  have hq := run_local_increment q (run p mp s) s mq qRead
  apply State.extensionality
  · exact phase_commutation _ _ _ _ _ hp.1 hq.1
  · funext a
    by_cases ha : a∈wires p
    · have away : a∉wires q := fun hh => Finset.disjoint_left.mp hd ha hh
      exact (hp.2 a ha).trans (run_preserves_outside q mq (run p mp s) a away).symm
    · rw [run_preserves_outside p mp (run q mq s) a ha]
      by_cases hb : a∈wires q
      · exact (hq.2 a hb).symm
      · rw [run_preserves_outside q mq (run p mp s) a hb,
          run_preserves_outside q mq s a hb,
          run_preserves_outside p mp s a ha]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkSchedule.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] narrowSkywalkScheduledTick narrowSkywalkScheduledUntick
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

/-- All codec instructions and corrections stay on the six real history
sites. This includes both encoder and decoder support. -/
theorem compressedHistory_gate_mem (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (start : Nat) (hs : start+3 ≤ 512)
    (p : Program) (hp : p=compressedHistoryEncode w start ∨ p=compressedHistoryDecode w start)
    (q : Wire) (hq : q∈wires p) :
    ∃ j : Fin 6,q=w (compressedHistoryId start j) := by
  let f := compressedHistoryMap w start
  have hf := compressedHistoryMap_injective w hn start hs
  have hl := compressedHistoryMap_above w start hs hlo
  have hw : wires p=(Finset.range 6).image (TranscriptCodec3.placement f) := by
    rcases hp with rfl|rfl
    · simp only [f,compressedHistoryEncode,TranscriptCodec3.encode,renameProgram_support,
        TranscriptCodec3.support.1]
    · simp only [f,compressedHistoryDecode,TranscriptCodec3.decode,renameProgram_support,
        TranscriptCodec3.support.2]
  rw [hw] at hq
  obtain ⟨j,hj,hjq⟩ := Finset.mem_image.mp hq
  have hlt := Finset.mem_range.mp hj
  have he : TranscriptCodec3.placement f j=f ⟨j,hlt⟩ :=
    TranscriptCodec3.placement_apply f hf hl ⟨j,hlt⟩
  exact ⟨⟨j,hlt⟩,hjq.symm.trans he⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkPrefix.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- Pure reference encoding of the history groups packed before tick n.
This is also an executable program, not a circuit oracle. -/
def compressedEncodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => compressedEncodePrefix w n ++ compressedPackAfter w n

def compressedDecodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => compressedDecodeBefore w n ++ compressedDecodePrefix w n

attribute [local irreducible] run narrowSkywalkScheduledTick narrowSkywalkScheduledUntick
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] compressedEncodePrefix compressedDecodePrefix

theorem compressedPackDue_true (i : Nat) (h : compressedPackDue i=true) :
    3 ≤ i ∧ i%3=0 := by
  simpa only [compressedPackDue,decide_eq_true_eq] using h

theorem compressedHistory_windows_disjoint (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (a b : Nat) (ha : a+3 ≤ 512) (hb : b+3 ≤ 512) (hab : a+3 ≤ b) :
    Disjoint (wires (compressedHistoryEncode w a)) (wires (compressedHistoryEncode w b)) := by
  apply Finset.disjoint_left.mpr
  intro q hqa hqb
  obtain ⟨j,hj⟩ := compressedHistory_gate_mem w hn hlo a ha _ (Or.inl rfl) q hqa
  obtain ⟨k,hk⟩ := compressedHistory_gate_mem w hn hlo b hb _ (Or.inl rfl) q hqb
  have he := skywalkPool_index_inj w hn _ _
    (compressedHistoryId_bound a ha j) (compressedHistoryId_bound b hb k) (hj.symm.trans hk)
  have hji := j.isLt
  have hki := k.isLt
  unfold compressedHistoryId at he
  split_ifs at he <;> omega

/-- Earlier packed groups cannot change the raw inputs of the next group.
Divisibility by three supplies the exact three-symbol separation. -/
theorem compressedPrefix_disjoint_next (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n i : Nat) (hni : n ≤ i) (hi : i < 512) (hdue : compressedPackDue i=true) :
    Disjoint (wires (compressedEncodePrefix w n)) (wires (compressedHistoryEncode w (i-3))) := by
  induction n with
  | zero => simp [compressedEncodePrefix,wires]
  | succ n ih =>
    have hp := ih (by omega)
    have hc : Disjoint (wires (compressedPackAfter w n)) (wires (compressedHistoryEncode w (i-3))) := by
      cases he : compressedPackDue n
      · simp [compressedPackAfter,he,wires]
      · have hn3 := compressedPackDue_true n he
        have hi3 := compressedPackDue_true i hdue
        have hsep : n+3 ≤ i := by omega
        have hh := compressedHistory_windows_disjoint w hn hlo (n-3) (i-3) (by omega) (by omega) (by omega)
        simpa only [compressedPackAfter,he,if_true] using hh
    simp only [compressedEncodePrefix,wires_append,Finset.disjoint_union_left]
    exact ⟨hp,hc⟩

/-- Every raw group site is present in encoder support, including the site
which becomes zero after packing. -/
theorem compressedHistory_site_mem (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (start : Nat) (hs : start+3 ≤ 512) (j : Fin 6) :
    compressedHistoryMap w start j∈wires (compressedHistoryEncode w start) := by
  let f := compressedHistoryMap w start
  have hf := compressedHistoryMap_injective w hn start hs
  have hl := compressedHistoryMap_above w start hs hlo
  have he := TranscriptCodec3.placement_apply f hf hl j
  unfold compressedHistoryEncode
  change f j∈wires (TranscriptCodec3.encode f)
  rw [TranscriptCodec3.encode,renameProgram_support,TranscriptCodec3.support.1]
  apply Finset.mem_image.mpr
  exact ⟨j,Finset.mem_range.mpr j.isLt,he⟩

theorem compressedPrefix_raw_next (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i : Nat) (hi : i < 512) (hdue : compressedPackDue i=true)
    (s : State) (m : List Bool) (j : Fin 6) :
    (run (compressedEncodePrefix w i) m s).basis (compressedHistoryMap w (i-3) j)=
      s.basis (compressedHistoryMap w (i-3) j) := by
  apply run_preserves_outside
  have hd := compressedPrefix_disjoint_next w hn hlo i i (Nat.le_refl i) hi hdue
  have h3 := compressedPackDue_true i hdue
  intro hq
  exact Finset.disjoint_left.mp hd hq
    (compressedHistory_site_mem w hn hlo (i-3) (by omega) j)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedCompactSupport.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] compactSkywalkTick compressedHistoryEncode compressedEncodePrefix

/-- Exact local support of the actual compact native tick and sign-tail
cleanup excludes any group whose final orientation was already consumed. -/
theorem compressedHistory_disjoint_compactTick (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (start i : Nat) (hs : start+3 ≤ 512) (hlate : start+4 ≤ i) (hi : i < 512) :
    Disjoint (wires (compressedHistoryEncode w start)) (wires (compactSkywalkTick w i)) := by
  apply Finset.disjoint_left.mpr
  intro q hq ht
  obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo start hs _ (Or.inl rfl) q hq
  have mem := List.mem_toFinset.mp (compactSkywalkTick_support w i hi hn ht)
  have width := compactSkywalkTick_width_bounds i hi
  have hpos : i ≠ 0 := by omega
  have away : w (compressedHistoryId start j) ∉ (compactSkywalkTickLayout w i).wires := by
    apply compactSkywalkStage_tick_away w i hi hn (compressedHistoryId start j)
      (compressedHistoryId_bound start hs j)
    all_goals
      have hj := j.isLt
      unfold compressedHistoryId
      split_ifs <;> (try simp only [skywalkPoolPreviousId,if_neg hpos]) <;> omega
  exact away mem

/-- Prefix packing remains disjoint from every later compact tick. The
existing delayed pack schedule is retained verbatim. -/
theorem compressedPrefix_disjoint_compactTick (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n i : Nat) (hni : n ≤ i) (hi : i < 512) :
    Disjoint (wires (compressedEncodePrefix w n)) (wires (compactSkywalkTick w i)) := by
  induction n with
  | zero => simp [compressedEncodePrefix,wires]
  | succ n ih =>
    have old := ih (by omega)
    have now : Disjoint (wires (compressedPackAfter w n)) (wires (compactSkywalkTick w i)) := by
      cases due : compressedPackDue n
      · simp [compressedPackAfter,due,wires]
      · have h3 := compressedPackDue_true n due
        have h := compressedHistory_disjoint_compactTick w hn hlo (n-3) i (by omega) (by omega) hi
        simpa only [compressedPackAfter,due,if_true] using h
    simp only [compressedEncodePrefix,wires_append,Finset.disjoint_union_left]
    exact ⟨old,now⟩

/-- The compact physical stage supplies the exact legal ternary tape to
all codec groups. No expanded-tail circuit is needed for this argument. -/
theorem compressedCompactHistory_legal (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p i start : Nat)
    (hp0 : 0 < p) (hpo : p%2 = 1) (hs : start+3 ≤ i) (hi : i ≤ 512)
    (s : BasisState)
    (h : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s) :
    (s (compressedHistoryMap w start 0) && s (compressedHistoryMap w start 1)) = false ∧
    (s (compressedHistoryMap w start 2) && s (compressedHistoryMap w start 3)) = false ∧
    (s (compressedHistoryMap w start 4) && s (compressedHistoryMap w start 5)) = false := by
  have fields := (compactSkywalkStage_fields_iff w _ i hi hn s).mp h
  have tape := fields.2.2.2.1
  have ternary (j : Nat) (hj : j < i) : (s (w j) && s (w (1028+j))) = false := by
    rw [(tape j hj).1,(tape j hj).2]
    exact skywalkRecordedSymbol_legal x p j hp0 hpo
  have a := ternary start (by omega)
  have b := ternary (start+1) (by omega)
  have c := ternary (start+2) (by omega)
  simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using And.intro a (And.intro b c)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedCompactStage.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- A ghost raw compact state supplies the exact integer invariant. Encoding is
an actual circuit program; the assertion equates the complete caller basis.
Incoming phase is unrestricted and is preserved separately by the Triple. -/
def CompressedCompactStage (w : Nat → Wire) (x p i : Nat) (bits : BasisState) : Prop :=
  ∃ raw : State,
    CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis ∧
    bits = (run (compressedEncodePrefix w i) [] raw).basis

/-- Actual compact native ticks followed by the unchanged delayed codec packs. -/
def compressedCompactForward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compactSkywalkTick w i++compressedPackAfter w i++
      compressedCompactForward w (i+1) n

attribute [local irreducible] run compressedEncodePrefix compressedCompactForward
attribute [local irreducible] compactSkywalkTick compressedHistoryEncode

private theorem xor_neutral (a b : Bool) (h : (a ^^ b) = false) : a = b := by
  cases a <;> cases b <;> simp_all

theorem compressedCompactStage_zero (w : Nat → Wire) (x p : Nat) (s : State)
    (h : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    CompressedCompactStage w x p 0 s.basis := by
  refine ⟨s,h,?_⟩
  simp only [compressedEncodePrefix,run]

theorem compressedCompactStage_step (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hi : i < 512) :
    Triple (CompressedCompactStage w x p i)
      (compactSkywalkTick w i ++ compressedPackAfter w i)
      (CompressedCompactStage w x p (i+1)) := by
  intro s m hs
  obtain ⟨raw,hraw,hbits⟩ := hs
  let tick := compactSkywalkTick w i
  let mt := m.take (measurementCount tick)
  let me := m.drop (measurementCount tick)
  let actual := run tick mt s
  let next := run tick [] raw
  have step := compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hx hc hi
  have hnxt := step raw [] hraw
  have hmt := step raw mt hraw
  have hd := compressedPrefix_disjoint_compactTick w hn hlo i i (Nat.le_refl i) hi
  have read : ∀ q ∈ wires tick,s.basis q = raw.basis q := by
    intro q hq
    rw [hbits]
    apply run_preserves_outside
    exact fun he => Finset.disjoint_left.mp hd he hq
  have hl := run_local_increment tick s raw mt read
  have hphase : actual.phase = s.phase := by
    apply xor_neutral
    have hh := hl.1
    rw [hmt.1] at hh
    simpa only [Bool.xor_self] using hh
  have hcomm := run_disjoint_commute (compressedEncodePrefix w i) tick hd [] [] raw
  have hb0 := run_basis_records tick s (run (compressedEncodePrefix w i) [] raw) mt [] hbits
  have hb : actual.basis = (run (compressedEncodePrefix w i) [] next).basis :=
    hb0.trans (congrArg State.basis hcomm.symm)
  have hpackphase : (run (compressedPackAfter w i) me actual).phase = actual.phase := by
    cases he : compressedPackDue i
    · simp only [compressedPackAfter,he,Bool.false_eq_true,if_false,run]
    · have h3 := compressedPackDue_true i he
      have same (j : Fin 6) : actual.basis (compressedHistoryMap w (i-3) j) = next.basis (compressedHistoryMap w (i-3) j) := by
        rw [hb]
        exact compressedPrefix_raw_next w hn hlo i hi he next [] j
      have legal := compressedCompactHistory_legal w hn x p (i+1) (i-3) hp0 hpo (by omega) (by omega) next.basis hnxt.2
      have actualLegal :
          (actual.basis (compressedHistoryMap w (i-3) 0) && actual.basis (compressedHistoryMap w (i-3) 1)) = false ∧
          (actual.basis (compressedHistoryMap w (i-3) 2) && actual.basis (compressedHistoryMap w (i-3) 3)) = false ∧
          (actual.basis (compressedHistoryMap w (i-3) 4) && actual.basis (compressedHistoryMap w (i-3) 5)) = false := by
        rw [same 0,same 1,same 2,same 3,same 4,same 5]
        exact legal
      have cp := TranscriptCodec3.placement_correct (compressedHistoryMap w (i-3))
        (compressedHistoryMap_injective w hn (i-3) (by omega))
        (compressedHistoryMap_above w (i-3) (by omega) hlo) actual me actualLegal
      simpa only [compressedPackAfter,he,if_true,compressedHistoryEncode] using cp.1
  have hpackbits := run_basis_records (compressedPackAfter w i) actual
    (run (compressedEncodePrefix w i) [] next) me [] hb
  have hbnext : (run (compressedPackAfter w i) me actual).basis = (run (compressedEncodePrefix w (i+1)) [] next).basis := by
    rw [compressedEncodePrefix,run_append]
    simp only [List.take_nil,List.drop_nil]
    exact hpackbits
  rw [run_append]
  exact ⟨hpackphase.trans hphase,⟨next,hnxt.2,hbnext⟩⟩

/-- Complete forward composition for arbitrary records, including phase.
This theorem retains the exact original divisor and all512 compact integer steps. -/
theorem CompressedCompactStage_spec (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p i n : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hi : i+n ≤ 512) :
    Triple (CompressedCompactStage w x p i) (compressedCompactForward w i n)
      (CompressedCompactStage w x p (i+n)) := by
  induction n generalizing i with
  | zero =>
    rw [compressedCompactForward,Nat.add_zero]
    intro s m h
    simpa only [run] using And.intro (rfl : s.phase = s.phase) h
  | succ n ih =>
    have hstep := compressedCompactStage_step w hn hlo x p i hp0 hx0 hpo hp hx hc (by omega)
    have htail := ih (i+1) (by omega)
    have hall := hstep.seq htail
    have hindex : i+(n+1) = (i+1)+n := by omega
    rw [compressedCompactForward,hindex]
    simpa only [List.append_assoc] using hall

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedCompactFrame.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run compactSkywalkTick compressedHistoryEncode compressedCompactForward

/-- The existing seed assertion starts the exact512 compact-plus-codec
campaign, with no changed divisor or shortened integer transcript. -/
theorem compressedCompactForward_512_spec (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) :
    Triple (SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0)
      (compressedCompactForward w 0 512) (CompressedCompactStage w x p 512) := by
  intro s m h
  have compact := (compactSkywalkStage_zero_iff w _ s.basis).mpr h
  exact CompressedCompactStage_spec w hn hlo x p 0 512 hp0 hx0 hpo hp hx hc (by decide)
    s m (compressedCompactStage_zero w x p s compact)

private theorem pack_support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (i : Nat) (hi : i < 512) :
    wires (compressedPackAfter w i) ⊆ (skywalkPoolWires w).toFinset := by
  intro q hq
  cases due : compressedPackDue i
  · simp [compressedPackAfter,due,wires] at hq
  · have h3 := compressedPackDue_true i due
    have hq' : q ∈ wires (compressedHistoryEncode w (i-3)) := by
      simpa only [compressedPackAfter,due,if_true] using hq
    obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo (i-3) (by omega) _ (Or.inl rfl) q hq'
    have bound := compressedHistoryId_bound (i-3) (by omega) j
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨compressedHistoryId (i-3) j,by omega,rfl⟩

/-- Actual instruction support includes compact sign release and all
measurement corrections of the history encoder. -/
theorem compressedCompactForward_support (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hi : i+n ≤ 512) :
    wires (compressedCompactForward w i n) ⊆ (skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,wires]
  | succ n ih =>
    have first : wires (compactSkywalkTick w i) ⊆ (skywalkPoolWires w).toFinset := by
      intro q hq
      exact List.mem_toFinset.mpr (compactSkywalkTick_local_support w i (by omega)
        (List.mem_toFinset.mp (compactSkywalkTick_support w i (by omega) hn hq)))
    have pack := pack_support w hn hlo i (by omega)
    simp only [compressedCompactForward,wires_append,Finset.union_subset_iff]
    exact ⟨⟨first,pack⟩,ih (i+1) (by omega)⟩

/-- Every caller bit outside the original integer pool restores, for all
input states and independent measurement records. -/
theorem compressedCompactForward_frame (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hi : i+n ≤ 512) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ skywalkPoolWires w) :
    (run (compressedCompactForward w i n) m s).basis q = s.basis q := by
  apply run_preserves_outside
  intro h
  exact hq (List.mem_toFinset.mp (compressedCompactForward_support w hn hlo i n hi h))

/-- Component resource recurrence for this actual emission. It is not a
whole-point qubit or stage resource claim. -/
theorem compressedCompactForward_counts (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (i n : Nat) (hi : i+n ≤ 512) :
    toffoliCount (compressedCompactForward w i n) = compactSkywalkForwardT i n+3*compressedPackCount i n ∧
    measurementCount (compressedCompactForward w i n) = compactSkywalkForwardM i n+compressedPackCount i n := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,compactSkywalkForwardT,compactSkywalkForwardM,
      compressedPackCount,toffoliCount,measurementCount]
  | succ n ih =>
    have tick := compactSkywalkTick_counts w i (by omega) hn
    have pack := compressedPackAfter_counts w i
    have tail := ih (i+1) (by omega)
    simp only [compressedCompactForward,toffoliCount_append,measurementCount_append,
      tick.1,tick.2,pack.1,pack.2.1,tail.1,tail.2,compactSkywalkForwardT,
      compactSkywalkForwardM,compressedPackCount]
    constructor <;> omega

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkDecode.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] run compressedEncodePrefix compressedDecodePrefix
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

theorem compressedDecodePrefix_measurements (w : Nat → Wire) (n : Nat) :
    measurementCount (compressedDecodePrefix w n)=0 := by
  induction n with
  | zero => simp [compressedDecodePrefix,measurementCount]
  | succ n ih =>
    simp only [compressedDecodePrefix,measurementCount_append,
      (compressedPackAfter_counts w n).2.2.2,ih,Nat.zero_add]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedSkywalkReverse.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

def compressedDecodeRange (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compressedDecodeRange w (i+1) n ++ compressedDecodeBefore w i

attribute [local irreducible] run narrowSkywalkRoutedUnloop narrowSkywalkScheduledUntick
attribute [local irreducible] compressedHistoryDecode
attribute [local irreducible] compressedDecodeRange compressedDecodePrefix

theorem compressedDecodeRange_measurements (w : Nat → Wire) (i n : Nat) :
    measurementCount (compressedDecodeRange w i n)=0 := by
  induction n generalizing i with
  | zero => simp [compressedDecodeRange,measurementCount]
  | succ n ih =>
    simp only [compressedDecodeRange,measurementCount_append,ih,
      (compressedPackAfter_counts w i).2.2.2,Nat.zero_add]

theorem compressedDecodeRange_last (w : Nat → Wire) (i n : Nat) :
    compressedDecodeRange w i (n+1)=compressedDecodeBefore w (i+n) ++ compressedDecodeRange w i n := by
  induction n generalizing i with
  | zero => simp [compressedDecodeRange]
  | succ n ih =>
    rw [compressedDecodeRange,ih]
    have hi : (i+1)+n=i+(n+1) := by omega
    rw [hi]
    simp only [compressedDecodeRange,List.append_assoc]

theorem compressedDecodeRange_zero (w : Nat → Wire) (n : Nat) :
    compressedDecodeRange w 0 n=compressedDecodePrefix w n := by
  induction n with
  | zero => simp [compressedDecodeRange,compressedDecodePrefix]
  | succ n ih =>
    rw [compressedDecodeRange_last,compressedDecodePrefix,ih,Nat.zero_add]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedCompactReverseProgram.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Actual compact reverse ticks; only each tick's local pre/post tails
are expanded, and the unchanged delayed codec schedule is decoded. -/
def compressedCompactReverse (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compressedCompactReverse w (i+1) n++compressedDecodeBefore w i++
      compactSkywalkReverseTick w i

attribute [local irreducible] run compactSkywalkReverseTick compactSkywalkReverse
attribute [local irreducible] compressedCompactReverse compressedHistoryDecode
attribute [local irreducible] compressedDecodeRange compressedDecodePrefix

theorem compressedHistory_disjoint_compactReverseTick (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (start i : Nat) (hs : start+3 ≤ 512) (hlate : start+4 ≤ i) (hi : i < 512) :
    Disjoint (wires (compressedHistoryDecode w start)) (wires (compactSkywalkReverseTick w i)) := by
  apply Finset.disjoint_left.mpr
  intro q hq ht
  obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo start hs _ (Or.inr rfl) q hq
  have mem := List.mem_toFinset.mp (compactSkywalkReverseTick_support w i hi hn ht)
  have width := compactSkywalkTick_width_bounds i hi
  have hpos : i ≠ 0 := by omega
  have away : w (compressedHistoryId start j) ∉ (compactSkywalkTickLayout w i).wires := by
    apply compactSkywalkStage_tick_away w i hi hn (compressedHistoryId start j)
      (compressedHistoryId_bound start hs j)
    all_goals
      have hj := j.isLt
      unfold compressedHistoryId
      split_ifs <;> (try simp only [skywalkPoolPreviousId,if_neg hpos]) <;> omega
  exact away mem

/-- Component charge equality also supplies exact record alignment when
zero-measurement decoders are moved before disjoint compact inverse ticks. -/
theorem compressedCompactReverse_counts_relative (w : Nat → Wire) (i n : Nat) :
    toffoliCount (compressedCompactReverse w i n) =
      toffoliCount (compactSkywalkReverse w i n)+4*compressedPackCount i n ∧
    measurementCount (compressedCompactReverse w i n) = measurementCount (compactSkywalkReverse w i n) := by
  induction n generalizing i with
  | zero => simp [compressedCompactReverse,compactSkywalkReverse,compressedPackCount,toffoliCount,measurementCount]
  | succ n ih =>
    have pack := compressedPackAfter_counts w i
    have tail := ih (i+1)
    simp only [compressedCompactReverse,compactSkywalkReverse,compressedPackCount,
      toffoliCount_append,measurementCount_append,pack.2.2.1,pack.2.2.2,tail.1,tail.2]
    constructor <;> omega

theorem compressedDecodeBefore_disjoint_compactReverse (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i j n : Nat) (hgap : i < j) (hbound : j+n ≤ 512) :
    Disjoint (wires (compressedDecodeBefore w i)) (wires (compactSkywalkReverse w j n)) := by
  induction n generalizing j with
  | zero => simp [compactSkywalkReverse,wires]
  | succ n ih =>
    have ht := ih (j+1) (by omega) (by omega)
    have hh : Disjoint (wires (compressedDecodeBefore w i)) (wires (compactSkywalkReverseTick w j)) := by
      cases he : compressedPackDue i
      · simp [compressedDecodeBefore,he,wires]
      · have hi3 := compressedPackDue_true i he
        have hs := compressedHistory_disjoint_compactReverseTick w hn hlo (i-3) j (by omega) (by omega) (by omega)
        simpa only [compressedDecodeBefore,he,if_true] using hs
    simp only [compactSkywalkReverse,wires_append,Finset.disjoint_union_right]
    exact ⟨ht,hh⟩

/-- Exact normalization of the emitted reverse program. Decoders consume no
measurements, so moving them ahead of disjoint later ticks preserves the same
record list, not merely a suitably relabeled list. This holds for all states. -/
theorem compressedCompactReverse_normalize (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hbound : i+n ≤ 512) (s : State) (m : List Bool) :
    run (compressedCompactReverse w i n) m s=
      run (compressedDecodeRange w i n ++ compactSkywalkReverse w i n) m s := by
  induction n generalizing i s m with
  | zero => simp [compressedCompactReverse,compressedDecodeRange,compactSkywalkReverse,run]
  | succ n ih =>
    have hm := (compressedCompactReverse_counts_relative w (i+1) n).2
    have hd := compressedDecodeBefore_disjoint_compactReverse w hn hlo i (i+1) n (by omega) (by omega)
    have hc := run_disjoint_commute (compressedDecodeBefore w i)
      (compactSkywalkReverse w (i+1) n) hd []
      (m.take (measurementCount (compactSkywalkReverse w (i+1) n)))
      (run (compressedDecodeRange w (i+1) n) [] s)
    rw [compressedCompactReverse,compressedDecodeRange,compactSkywalkReverse]
    simp only [run_append,measurementCount_append,hm,
      (compressedPackAfter_counts w i).2.2.2,compressedDecodeRange_measurements,
      Nat.add_zero,List.take_zero,List.drop_zero]
    rw [ih (i+1) (by omega)]
    have hzero : min 0 (measurementCount (compactSkywalkReverse w (i+1) n))=0 :=
      Nat.min_eq_left (Nat.zero_le _)
    simp only [run_append,compressedDecodeRange_measurements,List.take_zero,List.drop_zero,
      List.take_take,Nat.min_self,List.drop_take_self,hzero]
    rw [hc]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PhysicalGateCheck.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum
def physicalGateCheck : Instr → Bool
  | .X _ => true
  | .CX a t => a != t
  | .CCX a b t => (a != t) && (b != t)
  | .measureX _ _ _ => true

theorem physicalGateCheck_correct (p : Program) (h : p.all physicalGateCheck = true) :
    GatePhysical p := by
  intro i hi
  have hh := List.all_eq_true.mp h i hi
  cases i with
  | X t => trivial
  | measureX t c d => trivial
  | CX a t => simpa [physicalGateCheck,PhysicalInstr,ProperGate] using hh
  | CCX a b t => simpa [physicalGateCheck,PhysicalInstr,ProperGate] using hh

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedResources.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic

theorem copyNone_free (src dst : List Wire) :
    toffoliCount (copyRegister none src dst)=0 ∧ measurementCount (copyRegister none src dst)=0 := by
  induction src generalizing dst with
  | nil => simp [copyRegister,toffoliCount,measurementCount]
  | cons x xs ih =>
    cases dst with
    | nil => simp [copyRegister,toffoliCount,measurementCount]
    | cons y ys => simp [copyRegister,copyGate,toffoliCount,measurementCount,ih]

namespace CuccaroStreamedSquareWideLayout

theorem measured_bank_widths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.inputBank.length=129 ∧ L.leafCarry.length=257 ∧ L.leafPad.length=1 ∧
    L.foldCarry.length=256 ∧ L.shortCarry.length=255 := by
  simp [inputBank,leafCarry,leafPad,foldCarry,shortCarry,L.foldPad_length hw,hw.core.work]

theorem measuredCore_widths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.measuredCore.Widths 256 :=
  ⟨hw.core.work,hw.core.out,(L.measured_bank_widths hw).2.2.2.1⟩

theorem measured_small_operation_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (toffoliCount L.normalizeSource=511 ∧ measurementCount L.normalizeSource=510) ∧
    (toffoliCount L.restoreSource=511 ∧ measurementCount L.restoreSource=510) ∧
    (toffoliCount L.reflectOutput=255 ∧ measurementCount L.reflectOutput=255) := by
  have banks := L.measured_bank_widths hw
  have cw : L.shortCarry.length+1=L.core.work.length := by rw [banks.2.2.2.2,hw.core.work]
  have co : L.shortCarry.length+1=L.core.out.length := by rw [banks.2.2.2.2,hw.core.out]
  have ge := compareConstantGe_counts L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p cw
  have add := mappedConstAdd_counts (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.c cw
  have sub := mappedConstAdd_counts (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.p cw
  have reflect := mappedConstAdd_counts none L.core.out L.shortCarry L.core.cin SquareReduction.p co
  simp [normalizeSource,restoreSource,reflectOutput,ge.1,ge.2,add.1,add.2,sub.1,sub.2,
    reflect.1,reflect.2,(notRegister_counts L.core.out).1,(notRegister_counts L.core.out).2,
    hw.core.work,hw.core.out]

theorem measuredFold_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (f : MeasuredSquareFold) :
    toffoliCount (L.measuredFold f)=1023+(if f.canonical then 0 else 1022) ∧
    measurementCount (L.measuredFold f)=1023+(if f.canonical then 0 else 1020) := by
  have small := L.measured_small_operation_counts hw
  have copy := copyNone_free f.src (L.foldDestination f)
  have core := L.measuredCore.secp_program_counts (L.measuredCore_widths hw) SquareReduction.c SquareReduction.p
  cases h : f.canonical <;>
    simp [measuredFold,h,copy.1,copy.2,core.1,core.2,small.1.1,small.1.2,small.2.1.1,small.2.1.2]

def measuredFoldsT : Bool → List MeasuredSquareFold → Nat
  | _,[] => 0
  | orientation,f::fs => (if orientation=f.negative then 0 else 255)+
      (1023+(if f.canonical then 0 else 1022))+measuredFoldsT f.negative fs

def measuredFoldsM : Bool → List MeasuredSquareFold → Nat
  | _,[] => 0
  | orientation,f::fs => (if orientation=f.negative then 0 else 255)+
      (1023+(if f.canonical then 0 else 1020))+measuredFoldsM f.negative fs

theorem measuredFolds_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (orientation : Bool) (items : List MeasuredSquareFold) :
    toffoliCount (L.measuredFolds orientation items)=measuredFoldsT orientation items ∧
    measurementCount (L.measuredFolds orientation items)=measuredFoldsM orientation items := by
  induction items generalizing orientation with
  | nil => simp [measuredFolds,measuredFoldsT,measuredFoldsM,toffoliCount,measurementCount]
  | cons f fs ih =>
    have op := L.measuredFold_counts hw f
    have reflect := (L.measured_small_operation_counts hw).2.2
    by_cases same : orientation=f.negative <;>
      simp [measuredFolds,measuredFoldsT,measuredFoldsM,same,op.1,op.2,reflect.1,reflect.2,ih,Nat.add_assoc]

theorem measured_item_prices (L : CuccaroStreamedSquareWideLayout) :
    (measuredFoldsT false L.measuredAItems=7158 ∧ measuredFoldsM false L.measuredAItems=7158) ∧
    (measuredFoldsT false L.measuredBItems=34001 ∧ measuredFoldsM false L.measuredBItems=33993) ∧
    (measuredFoldsT true L.measuredCItems=6648 ∧ measuredFoldsM true L.measuredCItems=6648) := by
  norm_num [measuredAItems,measuredBItems,measuredCItems,nafMinusOneItems,shiftedProductItems,
    measuredFoldsT,measuredFoldsM]

theorem withMeasuredSquare_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (src dst : List Wire) (body : Program)
    (hs : 2≤src.length) (hsmax : src.length≤129) (hd : dst.length=2*src.length) :
    toffoliCount (L.withMeasuredSquare control src dst body)=
      2*(signedSquareRowsCount src.length+dst.length-1)+2*src.length+toffoliCount body ∧
    measurementCount (L.withMeasuredSquare control src dst body)=
      2*(signedSquareRowsCount src.length+dst.length-1)+2*src.length+measurementCount body := by
  have banks := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [banks.1,hsmax]
  have copy := copyRegister_counts (some control) src (L.inputBank.take src.length) inputLen.symm
  have erase := eraseMask_counts control src (L.inputBank.take src.length) inputLen.symm
  have square := mappedSignedSquare_counts (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin
    (by rw [inputLen];exact hs) (by rw [inputLen];exact hd)
    (by rw [banks.2.2.1]) (by rw [banks.2.1,hd];omega)
  simp only [withMeasuredSquare,toffoliCount_append,measurementCount_append,copy.1,copy.2,erase.1,erase.2,
    square.1.1,square.1.2,square.2.1,square.2.2,inputLen,Option.isSome_some,if_true]
  constructor <;> omega

/-- Resource theorem for the complete emitted controlled stage, including
all three producers, fresh-record cleanup, source normalization and frames. -/
theorem measuredProgram_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (L.measuredProgram control)=99902 ∧ measurementCount (L.measuredProgram control)=99382 := by
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := L.withMeasuredSquare_counts hw control L.core.low (L.core.product.take 256)
    (L.measuredFolds false L.measuredAItems) (by omega) (by omega) (by omega)
  have b := L.withMeasuredSquare_counts hw control L.core.high (L.core.product.take 256)
    (L.measuredFolds false L.measuredBItems) (by omega) (by omega) (by omega)
  have c := L.withMeasuredSquare_counts hw control L.core.sum L.core.product
    (L.measuredFolds true L.measuredCItems) (by omega) (by omega) (by rw [hw.core.product,su])
  have fa := L.measuredFolds_counts hw false L.measuredAItems
  have fb := L.measuredFolds_counts hw false L.measuredBItems
  have fc := L.measuredFolds_counts hw true L.measuredCItems
  have prices := L.measured_item_prices
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  rw [prices.2.2.1,prices.2.2.2] at fc
  have reflection := (L.measured_small_operation_counts hw).2.2
  have sum := L.core.sum_counts hw.core
  simp only [measuredProgram,measuredBranchA,measuredBranchB,measuredBranchC,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    reflection.1,reflection.2,sum.1.1,sum.1.2,sum.2.1,sum.2.2,lo,hi,su,p256,hw.core.product]
  norm_num [signedSquareRowsCount]

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MaskedSquareAction.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MaskedSquareCallback.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareProof.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 5000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

theorem regValue_take_mod (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.take n) s=regValue r s%2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  rw [h,Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt ?_).symm
  simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s

theorem regValue_drop_div (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.drop n) s=regValue r s/2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  have hl : regValue (r.take n) s<2^n := by
    simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [h,Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),Nat.div_eq_of_lt hl,Nat.zero_add]

theorem product_take_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P)
    (n : Nat) (hn : n≤258) :
    regValue (L.core.product.take n) s=P%2^n := by
  rw [regValue_take_mod L.core.product n (by rw [hw.core.product]; exact hn),hP]

theorem product_drop_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P)
    (n : Nat) (hn : n≤258) :
    regValue (L.core.product.drop n) s=P/2^n := by
  rw [regValue_drop_div L.core.product n (by rw [hw.core.product]; exact hn),hP]

theorem rotated128_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P) :
    regValue L.rotated128 s=(P/2^128)%2^128+2^128*(P%2^128) := by
  have high := L.product_drop_value hw s P hP 128 (by omega)
  have highLow := regValue_take_mod (L.core.product.drop 128) 128
    (by simp [hw.core.product]) s
  have low := L.product_take_value hw s P hP 128 (by omega)
  rw [rotated128,regValue_append,highLow,high,low]
  simp [hw.core.product]

theorem productTakeDrop_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P)
    (j : Nat) (hj : j≤256) :
    regValue ((L.core.product.take 256).drop (256-j)) s=(P%2^256)/2^(256-j) := by
  rw [regValue_drop_div _ _ (by simp [hw.core.product]),
    L.product_take_value hw s P hP 256 (by omega)]

theorem rotateFull_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (s : BasisState) (P : Nat) (hP : regValue L.core.product s=P)
    (j : Nat) (hj : j≤256) :
    regValue (rotateFull (L.core.product.take 256) j) s=
      (P%2^256)/2^(256-j)+2^j*((P%2^256)%2^(256-j)) := by
  let src := L.core.product.take 256
  have slen : src.length=256 := by simp [src,hw.core.product]
  have sv : regValue src s=P%2^256 := by
    exact L.product_take_value hw s P hP 256 (by omega)
  have hi := regValue_drop_div src (256-j) (by rw [slen]; omega) s
  have lo := regValue_take_mod src (256-j) (by rw [slen]; omega) s
  change regValue (src.drop (256-j)++src.take (256-j)) s=_
  rw [regValue_append,hi,lo,sv,List.length_drop,slen,
    show 256-(256-j)=j by omega]

theorem productDrop_count (L : CuccaroStreamedSquareWideLayout) (k : Nat) (q : Wire) :
    (L.core.product.drop k).count q≤L.core.product.count q :=
  (List.drop_sublist k L.core.product).count_le q

def addModValue (S O : Nat) : Nat :=
  (S%SquareReduction.p+O)%SquareReduction.p

def subModValue (S O : Nat) : Nat :=
  (O+SquareReduction.p-S%SquareReduction.p)%SquareReduction.p

def addCMinusOneValue (H O : Nat) : Nat :=
  addModValue (H*2^32)
    (addModValue (H*2^10)
      (subModValue (H*2^6) (addModValue (H*2^4) O)))

def subCMinusOneValue (H O : Nat) : Nat :=
  subModValue (H*2^32)
    (subModValue (H*2^10)
      (addModValue (H*2^6) (subModValue (H*2^4) O)))

def addRotate128Value (R H E O : Nat) (withOverhang : Bool) : Nat :=
  let main := addCMinusOneValue H (addModValue R O)
  if withOverhang then addModValue (E*2^128) main else main

def subRotate128Value (R H E O : Nat) (withOverhang : Bool) : Nat :=
  let main := subCMinusOneValue H (subModValue R O)
  if withOverhang then subModValue (E*2^128) main else main

def addShiftFullValue (R H O : Nat) : Nat :=
  addCMinusOneValue H (addModValue R O)

def subShiftFullValue (R H O : Nat) : Nat :=
  subCMinusOneValue H (subModValue R O)

def subTimesCValue (P R4 H4 R6 H6 R10 H10 R32 H32 O : Nat) : Nat :=
  subShiftFullValue R32 H32
    (subShiftFullValue R10 H10
      (addShiftFullValue R6 H6
        (subShiftFullValue R4 H4 (subModValue P O))))

/-- Simultaneous frame for the live sub-square product and the point output.
This is the invariant needed by `with_square`: producers change `product`,
folds change `out`, and both preserve every wire outside those two registers. -/
structure PairFrame (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (P O : Nat) (s : BasisState) : Prop where
  product : regValue L.core.product s=P
  out : regValue L.core.out s=O
  frame : ∀q,q∉L.core.product → q∉L.core.out → s q=base q

structure PairClean (L : CuccaroStreamedSquareWideLayout) (base : BasisState) : Prop where
  pad : regValue L.foldPad base=0
  work : regValue L.core.work base=0
  productHigh : base L.core.productHigh=false
  outHigh : base L.core.outHigh=false
  workHigh : base L.core.workHigh=false
  cin : base L.core.cin=false
  normFlag : base L.core.normFlag=false
  modFlag : base L.core.modFlag=false

theorem pairAuxAway (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) (q : Wire)
    (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    q∉L.core.product ∧ q∉L.core.out := by
  constructor <;> intro hm
  all_goals
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega

theorem PairFrame.clean (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) (base : BasisState) (P O : Nat) (s : BasisState)
    (h : PairFrame L base P O s) (hc : PairClean L base) : PairClean L s := by
  have keep (q : Wire)
      (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : s q=base q :=
    h.frame q (L.pairAuxAway hnd q hq).1 (L.pairAuxAway hnd q hq).2
  constructor
  · rw [←hc.pad]
    apply regValue_congr
    intro q hq
    exact keep q (by simp [hq])
  · rw [←hc.work]
    apply regValue_congr
    intro q hq
    exact keep q (by simp [hq])
  · exact (keep _ (by simp)).trans hc.productHigh
  · exact (keep _ (by simp)).trans hc.outHigh
  · exact (keep _ (by simp)).trans hc.workHigh
  · exact (keep _ (by simp)).trans hc.cin
  · exact (keep _ (by simp)).trans hc.normFlag
  · exact (keep _ (by simp)).trans hc.modFlag

theorem product_out_disjoint (L : CuccaroStreamedSquareWideLayout)
    (hnd : L.wires.Nodup) : L.core.product.Disjoint L.core.out := by
  apply List.disjoint_left.mpr
  intro q hp ho
  have h := List.nodup_iff_count.mp hnd q
  have h1 := List.count_pos_iff.mpr hp
  have h2 := List.count_pos_iff.mpr ho
  simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,
    List.count_cons,List.count_nil] at h
  omega

def addRotateProductValue (P O : Nat) (withOverhang : Bool) : Nat :=
  addRotate128Value ((P/2^128)%2^128+2^128*(P%2^128))
    (P/2^128) (P/2^256) O withOverhang

def subRotateProductValue (P O : Nat) (withOverhang : Bool) : Nat :=
  subRotate128Value ((P/2^128)%2^128+2^128*(P%2^128))
    (P/2^128) (P/2^256) O withOverhang

def rotatedFullValue (P j : Nat) : Nat :=
  (P%2^256)/2^(256-j)+2^j*((P%2^256)%2^(256-j))

def highFullValue (P j : Nat) : Nat := (P%2^256)/2^(256-j)

def subTimesProductValue (P O : Nat) : Nat :=
  subTimesCValue (P%2^256)
    (rotatedFullValue P 4) (highFullValue P 4)
    (rotatedFullValue P 6) (highFullValue P 6)
    (rotatedFullValue P 10) (highFullValue P 10)
    (rotatedFullValue P 32) (highFullValue P 32) O

theorem PairClean.corePad (L : CuccaroStreamedSquareWideLayout)
    (base : BasisState) (h : PairClean L base) : regValue L.core.pad base=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  exact (regValue_zero _ _).mp h.pad q (by simp [foldPad,hq])

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredSourceNormalize.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- Normalize one raw word without storing the literal modulus in qubits.
The branch bit is retained until the original source is restored. -/
structure MeasuredSourceNormalizeLayout where
  word : List Wire
  carry : List Wire
  cin : Wire
  flag : Wire

namespace MeasuredSourceNormalizeLayout

def wires (L : MeasuredSourceNormalizeLayout) : List Wire := L.flag::L.cin::(L.word++L.carry)
def mutable (L : MeasuredSourceNormalizeLayout) : List Wire := L.word++[L.flag]
def Frame (L : MeasuredSourceNormalizeLayout) (base : BasisState) (V : Nat) (F : Bool)
    (s : BasisState) : Prop :=
  regValue L.word s=V ∧ s L.flag=F ∧ ∀q,q∉L.mutable → s q=base q

def normalize (L : MeasuredSourceNormalizeLayout) (p c : Nat) : Program :=
  compareConstantGe L.word L.carry L.cin L.flag p++
    mappedConstAdd (some L.flag) L.word L.carry L.cin c
def restore (L : MeasuredSourceNormalizeLayout) (p : Nat) : Program :=
  mappedConstAdd (some L.flag) L.word L.carry L.cin p++
    compareConstantGe L.word L.carry L.cin L.flag p

def reflect (L : MeasuredSourceNormalizeLayout) (p : Nat) : Program :=
  notRegister L.word++mappedConstAdd none L.word L.carry L.cin p

theorem canonical_and_restore (B p c X : Nat) (hpc : p+c=B) (hc : 0<c)
    (hcp : c<p) (hX : X<B) :
    ((if p≤X then c else 0)+X)%B=X%p ∧
    ((if p≤X then p else 0)+X%p)%B=X ∧ X%p<p := by
  have hp : 0<p := by omega
  refine ⟨?_,?_,Nat.mod_lt _ hp⟩
  · by_cases small : X<p
    · rw [if_neg (by omega),Nat.zero_add,Nat.mod_eq_of_lt hX,Nat.mod_eq_of_lt small]
    · have hx : X%p=X-p := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      rw [if_pos (by omega),hx,show c+X=(X-p)+B by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  · by_cases small : X<p
    · rw [if_neg (by omega),Nat.mod_eq_of_lt small,Nat.zero_add,Nat.mod_eq_of_lt hX]
    · have hx : X%p=X-p := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      rw [if_pos (by omega),hx,show p+(X-p)=X by omega,Nat.mod_eq_of_lt hX]

theorem protected_away (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.cin::L.carry) : q∉L.mutable := by
  intro bad
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [wires,mutable,List.count_cons,List.count_append,List.count_nil] at h a b
  omega

theorem flag_away (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup) :
    L.flag∉L.word := by
  intro bad
  have h := List.nodup_iff_count.mp hn L.flag
  have b := List.count_pos_iff.mpr bad
  simp only [wires,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
  omega

theorem Frame.clean (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (base s : BasisState) (V : Nat) (F : Bool) (hf : L.Frame base V F s)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    (∀q∈L.carry,s q=false) ∧ s L.cin=false := by
  constructor
  · intro q hq
    exact (hf.2.2 q (L.protected_away hn q (by simp [hq]))).trans (hc q hq)
  · exact (hf.2.2 L.cin (L.protected_away hn L.cin (by simp))).trans hi

theorem ge_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (p : Nat) (hp : p<2^L.word.length)
    (base : BasisState) (V : Nat) (F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base V F) (compareConstantGe L.word L.carry L.cin L.flag p)
      (L.Frame base V (F ^^ decide (p≤V))) := by
  intro s m hf
  have clean := Frame.clean L hn base s.basis V F hf hc hi
  obtain ⟨phase,same,value⟩ := compareConstantGe_correct L.word L.carry L.cin L.flag p hn hl hp s m clean.2 clean.1
  refine ⟨phase,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => same q (fun bad => L.flag_away hn (bad ▸ hq)))).trans hf.1
  · simpa [hf.1,hf.2.1] using value
  · intro q hq
    exact (same q (fun bad => hq (by simp [mutable,bad]))).trans (hf.2.2 q hq)

theorem add_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (k : Nat) (hk : k<2^L.word.length)
    (base : BasisState) (V : Nat) (F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base V F) (mappedConstAdd (some L.flag) L.word L.carry L.cin k)
      (L.Frame base (((if F then k else 0)+V)%2^L.word.length) F) := by
  have nd : (L.cin::L.word++L.carry).Nodup := (List.nodup_cons.mp hn).2
  have away : ∀q∈some L.flag,q∉L.cin::L.word++L.carry := by
    intro q hq
    have e : q=L.flag := by simpa [eq_comm] using hq
    subst q
    exact (List.nodup_cons.mp hn).1
  intro s m hf
  have clean := Frame.clean L hn base s.basis V F hf hc hi
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct (some L.flag) L.word L.carry L.cin k nd away hl hk s m clean.1
  refine ⟨phase,?_,(same L.flag (L.flag_away hn)).trans hf.2.1,?_⟩
  · simpa [mappedEnabled,hf.1,hf.2.1,clean.2] using value
  · intro q hq
    have awayWord : q∉L.word := fun bad => hq (by simp [mutable,bad])
    exact (same q awayWord).trans (hf.2.2 q hq)

theorem normalize_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (p c X : Nat)
    (hpc : p+c=2^L.word.length) (hcpos : 0<c) (hcp : c<p) (hX : X<2^L.word.length)
    (base : BasisState) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base X false) (L.normalize p c)
      (L.Frame base (X%p) (decide (p≤X))) := by
  have hp : p<2^L.word.length := by omega
  have cb : c<2^L.word.length := by omega
  have ge := L.ge_frame hn hl p hp base X false hc hi
  have add := L.add_frame hn hl c cb base X (decide (p≤X)) hc hi
  have math := canonical_and_restore (2^L.word.length) p c X hpc hcpos hcp hX
  have eq : ((if decide (p≤X) then c else 0)+X)%2^L.word.length=X%p := by
    simpa using math.1
  simp only [Bool.false_xor] at ge
  rw [eq] at add
  exact ge.seq add

theorem restore_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (p c X : Nat)
    (hpc : p+c=2^L.word.length) (hcpos : 0<c) (hcp : c<p) (hX : X<2^L.word.length)
    (base : BasisState) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base (X%p) (decide (p≤X))) (L.restore p)
      (L.Frame base X false) := by
  have hp : p<2^L.word.length := by omega
  have add := L.add_frame hn hl p hp base (X%p) (decide (p≤X)) hc hi
  have ge := L.ge_frame hn hl p hp base X (decide (p≤X)) hc hi
  have math := canonical_and_restore (2^L.word.length) p c X hpc hcpos hcp hX
  have eq : ((if decide (p≤X) then p else 0)+X%p)%2^L.word.length=X := by
    simpa using math.2.1
  rw [eq] at add
  simp only [Bool.xor_self] at ge
  exact add.seq ge

theorem not_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (base : BasisState) (V : Nat) (F : Bool) :
    Triple (L.Frame base V F) (notRegister L.word)
      (L.Frame base (2^L.word.length-1-V) F) := by
  have nd : L.word.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [wires,List.count_cons,List.count_append] at h
    omega
  intro s m hf
  rw [notRegister_correct L.word nd]
  refine ⟨rfl,?_,?_,?_⟩
  · have val : regValue L.word (fun q => if q∈L.word then !s.basis q else s.basis q)=
        2^L.word.length-1-regValue L.word s.basis := by
      rw [regValue_congr L.word _ (fun q => !s.basis q) (by intro q hq; simp [hq]),regValue_complement]
    exact val.trans (by rw [hf.1])
  · simpa [L.flag_away hn] using hf.2.1
  · intro q hq
    have out : q∉L.word := fun bad => hq (by simp [mutable,bad])
    simpa [out] using hf.2.2 q hq

theorem literal_add_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (k : Nat) (hk : k<2^L.word.length)
    (base : BasisState) (V : Nat) (F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base V F) (mappedConstAdd none L.word L.carry L.cin k)
      (L.Frame base ((k+V)%2^L.word.length) F) := by
  have nd : (L.cin::L.word++L.carry).Nodup := (List.nodup_cons.mp hn).2
  intro s m hf
  have clean := Frame.clean L hn base s.basis V F hf hc hi
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct none L.word L.carry L.cin k nd
    (by simp) hl hk s m clean.1
  refine ⟨phase,?_,(same L.flag (L.flag_away hn)).trans hf.2.1,?_⟩
  · simpa [mappedEnabled,hf.1,clean.2] using value
  · intro q hq
    have out : q∉L.word := fun bad => hq (by simp [mutable,bad])
    exact (same q out).trans (hf.2.2 q hq)

/-- Exact canonical reflection, including zero and p-1. Carries and every
wire outside the output are restored; measurement records are arbitrary. -/
theorem reflect_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (p V : Nat)
    (hp : p<2^L.word.length) (hV : V<p) (base : BasisState) (F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base V F) (L.reflect p) (L.Frame base (p-1-V) F) := by
  have inv := L.not_frame hn base V F
  have add := L.literal_add_frame hn hl p hp base (2^L.word.length-1-V) F hc hi
  have math : (p+(2^L.word.length-1-V))%2^L.word.length=p-1-V := by
    have eq : p+(2^L.word.length-1-V)=(p-1-V)+2^L.word.length := by omega
    rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  rw [math] at add
  exact inv.seq add

end MeasuredSourceNormalizeLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredFoldKernel.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def measuredFoldNormalize (K : MeasuredCanonicalModLayout) (flag : Wire) : MeasuredSourceNormalizeLayout :=
  {word:=K.src,carry:=K.carry.take (K.src.length-1),cin:=K.cin,flag:=flag}

def measuredFoldKernel (K : MeasuredCanonicalModLayout) (flag : Wire)
    (canonical : Bool) (c p : Nat) : Program :=
  (if canonical then [] else (measuredFoldNormalize K flag).normalize p c)++
    K.program c p++
    (if canonical then [] else (measuredFoldNormalize K flag).restore p)

/-- The reusable fold kernel accepts any n-bit source, normalizes it when
needed, adds it to the canonical output, and restores the raw source and all
workspace. Its exact guarantee includes every measurement record. -/
theorem measuredFoldKernel_correct (K : MeasuredCanonicalModLayout) (flag : Wire)
    (n c p : Nat) (hw : K.Widths n) (hn : (flag::K.wires).Nodup)
    (npos : 0<n) (hpc : p+c=2^n) (hcpos : 0<c) (hcp : c<p)
    (canonical : Bool) (S O : Nat) (hcanonical : canonical=true → S<p) (hO : O<p)
    (s : State) (records : List Bool) (hs : regValue K.src s.basis=S)
    (ho : regValue K.out s.basis=O) (hf : s.basis flag=false)
    (hhigh : s.basis K.high=false) (hmod : s.basis K.flag=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) (hcin : s.basis K.cin=false) :
    (run (measuredFoldKernel K flag canonical c p) records s).phase=s.phase ∧
    regValue K.out (run (measuredFoldKernel K flag canonical c p) records s).basis=(S+O)%p ∧
    ∀q,q∉K.out → (run (measuredFoldKernel K flag canonical c p) records s).basis q=s.basis q := by
  let N := measuredFoldNormalize K flag
  let preProg := if canonical then [] else N.normalize p c
  let postProg := if canonical then [] else N.restore p
  let rest := records.drop (measurementCount preProg)
  let u := run preProg (records.take (measurementCount preProg)) s
  let v := run (K.program c p) (rest.take (measurementCount (K.program c p))) u
  let out := run postProg (rest.drop (measurementCount (K.program c p))) v
  let A := if canonical then S else S%p
  let D := if canonical then false else decide (p≤S)
  have coreNd : K.wires.Nodup := (List.nodup_cons.mp hn).2
  have nd : N.wires.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist (K.src.length-1) K.carry).count_le q
    simp only [N,measuredFoldNormalize,MeasuredSourceNormalizeLayout.wires,
      MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have length : N.carry.length+1=N.word.length := by
    simp [N,measuredFoldNormalize,hw.src,hw.carry]
    omega
  have modulus : p+c=2^N.word.length := by simpa [N,measuredFoldNormalize,hw.src] using hpc
  have bound : S<2^N.word.length := by
    simpa only [N,measuredFoldNormalize,hs] using regValue_lt K.src s.basis
  have nclean : ∀q∈N.carry,s.basis q=false := by
    intro q hq
    exact hcarry q (List.mem_of_mem_take hq)
  have protect (q : Wire) (hq : q∈K.out++K.carry++[K.high,K.cin,K.flag]) : q∉N.mutable := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [N,measuredFoldNormalize,MeasuredSourceNormalizeLayout.mutable,
      MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a b
    omega
  have srcAway (q : Wire) (hq : q∈K.src) : q∉K.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have flagAway : flag∉K.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [MeasuredCanonicalModLayout.wires,bad])
  have before : u.phase=s.phase ∧ regValue K.src u.basis=A ∧ u.basis flag=D ∧
      ∀q,q∉N.mutable → u.basis q=s.basis q := by
    cases h : canonical
    · have init : N.Frame s.basis S false s.basis := ⟨hs,hf,fun _ _ => rfl⟩
      have result := N.normalize_frame nd length p c S modulus hcpos hcp bound s.basis nclean hcin
        s (records.take (measurementCount preProg)) init
      simpa only [u,preProg,h,if_false,A,D] using result
    · simp [u,preProg,h,A,D,run,hs,hf]
  have aBound : A<p := by
    cases h : canonical
    · simpa [A,h] using Nat.mod_lt S (show 0<p by omega)
    · simpa [A,h] using hcanonical h
  have carryU : ∀q∈K.carry,u.basis q=false := by
    intro q hq
    exact (before.2.2.2 q (protect q (by simp [hq]))).trans (hcarry q hq)
  have cinU : u.basis K.cin=false :=
    (before.2.2.2 K.cin (protect K.cin (by simp))).trans hcin
  have highU : u.basis K.high=false :=
    (before.2.2.2 K.high (protect K.high (by simp))).trans hhigh
  have modU : u.basis K.flag=false :=
    (before.2.2.2 K.flag (protect K.flag (by simp))).trans hmod
  have outU : regValue K.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => before.2.2.2 q (protect q (by simp [hq])))).trans ho
  have core := K.program_correct n c p hw coreNd npos hpc hcpos A O aBound hO
    u (rest.take (measurementCount (K.program c p))) before.2.1 outU highU modU carryU cinU
  have srcV : regValue K.src v.basis=A :=
    (regValue_congr _ _ _ (fun q hq => core.2.2 q (srcAway q hq))).trans before.2.1
  have flagV : v.basis flag=D := (core.2.2 flag flagAway).trans before.2.2.1
  have carryV : ∀q∈N.carry,v.basis q=false := by
    intro q hq
    have inCarry : q∈K.carry := List.mem_of_mem_take hq
    have notOut : q∉K.out := by
      intro bad
      have h := List.nodup_iff_count.mp hn q
      have a := List.count_pos_iff.mpr inCarry
      have b := List.count_pos_iff.mpr bad
      simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
      omega
    exact (core.2.2 q notOut).trans (carryU q inCarry)
  have cinAway : K.cin∉K.out := (K.flags_away coreNd).2.2.1 ∘ List.mem_append_left _
  have cinV : v.basis K.cin=false := (core.2.2 K.cin cinAway).trans cinU
  have after : out.phase=v.phase ∧ regValue K.src out.basis=S ∧ out.basis flag=false ∧
      ∀q,q∉N.mutable → out.basis q=v.basis q := by
    cases h : canonical
    · have init : N.Frame v.basis (S%p) (decide (p≤S)) v.basis := by
        exact ⟨by simpa [A,h] using srcV,by simpa [D,h] using flagV,fun _ _ => rfl⟩
      have result := N.restore_frame nd length p c S modulus hcpos hcp bound v.basis carryV cinV
        v (rest.drop (measurementCount (K.program c p))) init
      simpa only [out,postProg,h,if_false] using result
    · simpa only [out,postProg,h,if_true,run] using
        (show v.phase=v.phase ∧ regValue K.src v.basis=S ∧ v.basis flag=false ∧
          ∀q,q∉N.mutable → v.basis q=v.basis q from
          ⟨rfl,by simpa [A,h] using srcV,by simpa [D,h] using flagV,fun _ _ => rfl⟩)
  have finalValue : regValue K.out out.basis=(S+O)%p := by
    have value := (regValue_congr _ _ _ (fun q hq => after.2.2.2 q (protect q (by simp [hq])))).trans core.2.1
    have eq : (A+O)%p=(S+O)%p := by
      cases h : canonical
      · simp [A,h,Nat.add_mod]
      · simp [A,h]
    exact value.trans eq
  have final : out.phase=s.phase ∧ regValue K.out out.basis=(S+O)%p ∧
      ∀q,q∉K.out → out.basis q=s.basis q := by
    refine ⟨after.1.trans (core.1.trans before.1),finalValue,?_⟩
    intro q hq
    by_cases src : q∈K.src
    · exact (regValue_eq_iff K.src out.basis s.basis).mp (after.2.1.trans hs.symm) q src
    by_cases fl : q=flag
    · subst q; exact after.2.2.1.trans hf.symm
    have notMutable : q∉N.mutable := by
      simpa only [N,measuredFoldNormalize,MeasuredSourceNormalizeLayout.mutable,List.mem_append,
        List.mem_cons,List.not_mem_nil,or_false,not_or] using And.intro src fl
    exact (after.2.2.2 q notMutable).trans ((core.2.2 q hq).trans (before.2.2.2 q notMutable))
  simpa [measuredFoldKernel,N,preProg,postProg,rest,u,v,out,run_append] using final

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredCopySlice.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def copySlice (src word : List Wire) (shift : Nat) : Program :=
  copyRegister none src ((word.drop shift).take src.length)

/-- Zero padding is a property of the already clean word, so copying a
short shifted source needs no extra padding register. -/
theorem copySlice_zero_correct (src word : List Wire) (shift : Nat)
    (hn : (src++word).Nodup) (hl : shift+src.length≤word.length)
    (s : State) (records : List Bool) (hzero : regValue word s.basis=0) :
    (run (copySlice src word shift) records s).phase=s.phase ∧
    regValue word (run (copySlice src word shift) records s).basis=regValue src s.basis*2^shift ∧
    ∀q,q∉(word.drop shift).take src.length →
      (run (copySlice src word shift) records s).basis q=s.basis q := by
  let lo := word.take shift
  let dst := (word.drop shift).take src.length
  let hi := word.drop (shift+src.length)
  have len : dst.length=src.length := by simp [dst];omega
  have lowLen : lo.length=shift := by simp [lo];omega
  have split : word=lo++(dst++hi) := by
    have tail : word.drop shift=dst++hi := by
      simp [dst,hi,List.drop_drop,Nat.add_comm]
    calc
      word=lo++word.drop shift := (List.take_append_drop shift word).symm
      _=lo++(dst++hi) := by rw [tail]
  have nd : (src++dst).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have take := (List.take_sublist src.length (word.drop shift)).count_le q
    have drop := (List.drop_sublist shift word).count_le q
    simp only [List.count_append] at h ⊢
    dsimp only [dst]
    omega
  have wordNd : word.Nodup := (List.nodup_append'.mp hn).2.1
  have loAway (q : Wire) (hq : q∈lo) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp wordNd q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    rw [split] at h
    simp only [List.count_append] at h
    omega
  have hiAway (q : Wire) (hq : q∈hi) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp wordNd q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    rw [split] at h
    simp only [List.count_append] at h
    omega
  have dst0 : regValue dst s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hzero q
      (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  obtain ⟨phase,same,value⟩ := copyRegister_correct none src dst len.symm nd (by simp) s records
  have lo0 : regValue lo (run (copyRegister none src dst) records s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (same q (loAway q hq)).trans
      ((regValue_zero _ _).mp hzero q (List.mem_of_mem_take hq))
  have hi0 : regValue hi (run (copyRegister none src dst) records s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (same q (hiAway q hq)).trans
      ((regValue_zero _ _).mp hzero q (List.mem_of_mem_drop hq))
  refine ⟨phase,?_,same⟩
  change regValue word (run (copyRegister none src dst) records s).basis=_
  rw [split,regValue_append,regValue_append,lo0,hi0,value,dst0,lowLen]
  simp [copyValue,Nat.mul_comm]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredCopiedFold.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def measuredCopiedFold (K : MeasuredCanonicalModLayout) (flag : Wire)
    (src : List Wire) (shift : Nat) (canonical : Bool) (c p : Nat) : Program :=
  copySlice src K.src shift++measuredFoldKernel K flag canonical c p++copySlice src K.src shift

/-- Complete exact fold, including source load and unload. Only the output
register changes; all copied source bits, carries, flags and phase return. -/
theorem measuredCopiedFold_correct (K : MeasuredCanonicalModLayout) (flag : Wire)
    (n c p : Nat) (hw : K.Widths n) (src : List Wire) (shift : Nat)
    (hn : (src++flag::K.wires).Nodup) (hlen : shift+src.length≤n)
    (npos : 0<n) (hpc : p+c=2^n) (hcpos : 0<c) (hcp : c<p)
    (canonical : Bool) (O : Nat) (hO : O<p)
    (s : State) (records : List Bool)
    (hcanonical : canonical=true → regValue src s.basis*2^shift<p)
    (hzero : regValue K.src s.basis=0) (ho : regValue K.out s.basis=O)
    (hf : s.basis flag=false) (hhigh : s.basis K.high=false) (hmod : s.basis K.flag=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) (hcin : s.basis K.cin=false) :
    (run (measuredCopiedFold K flag src shift canonical c p) records s).phase=s.phase ∧
    regValue K.out (run (measuredCopiedFold K flag src shift canonical c p) records s).basis=
      (regValue src s.basis*2^shift+O)%p ∧
    ∀q,q∉K.out → (run (measuredCopiedFold K flag src shift canonical c p) records s).basis q=s.basis q := by
  let dst := (K.src.drop shift).take src.length
  let cp := copySlice src K.src shift
  let kernel := measuredFoldKernel K flag canonical c p
  let S := regValue src s.basis*2^shift
  let u := run cp [] s
  let v := run kernel (records.take (measurementCount kernel)) u
  let out := run cp (records.drop (measurementCount kernel)) v
  have coreNd : (flag::K.wires).Nodup := (List.nodup_append'.mp hn).2.1
  have nd : (src++K.src).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bound : shift+src.length≤K.src.length := by simpa [hw.src] using hlen
  have len : dst.length=src.length := by simp [dst];omega
  have dstSub (q : Wire) (hq : q∈dst) : q∈K.src :=
    List.mem_of_mem_drop (List.mem_of_mem_take hq)
  have notWork (q : Wire) (hq : q∈src++[flag]++K.out++K.carry++[K.high,K.cin,K.flag]) : q∉K.src := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have notDst (q : Wire) (hq : q∈src++[flag]++K.out++K.carry++[K.high,K.cin,K.flag]) : q∉dst :=
    fun bad => notWork q hq (dstSub q bad)
  have notOut (q : Wire) (hq : q∈src++[flag]++K.src++K.carry++[K.high,K.cin,K.flag]) : q∉K.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have copy := copySlice_zero_correct src K.src shift nd bound s [] hzero
  have first : u.phase=s.phase ∧ regValue K.src u.basis=S ∧
      ∀q,q∉dst → u.basis q=s.basis q := copy
  have cleanCarry : ∀q∈K.carry,u.basis q=false := by
    intro q hq
    exact (first.2.2 q (notDst q (by simp [hq]))).trans (hcarry q hq)
  have keep (q : Wire) (hq : q∈[flag]++K.out++[K.high,K.cin,K.flag]) : u.basis q=s.basis q :=
    first.2.2 q (notDst q (by simp only [List.mem_append] at hq ⊢; tauto))
  have outU : regValue K.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ho
  have body := measuredFoldKernel_correct K flag n c p hw coreNd npos hpc hcpos hcp canonical S O
    hcanonical hO u (records.take (measurementCount kernel)) first.2.1 outU
    ((keep flag (by simp)).trans hf) ((keep K.high (by simp)).trans hhigh)
    ((keep K.flag (by simp)).trans hmod) cleanCarry ((keep K.cin (by simp)).trans hcin)
  have nd2 : (src++dst).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp nd q
    have ht := (List.take_sublist src.length (K.src.drop shift)).count_le q
    have hd := (List.drop_sublist shift K.src).count_le q
    simp only [List.count_append] at h ⊢
    dsimp only [dst]
    omega
  have dst0 : regValue dst s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hzero q (dstSub q hq))
  have copied := copyRegister_correct none src dst len.symm nd2 (by simp) s []
  have dstU : regValue dst u.basis=regValue src s.basis := by
    simpa [u,cp,copySlice,dst0,copyValue] using copied.2.2
  have dstV : regValue dst v.basis=regValue src s.basis :=
    (regValue_congr _ _ _ (fun q hq => body.2.2 q (notOut q (by simp [dstSub q hq])))).trans dstU
  have srcV : regValue src v.basis=regValue src s.basis := by
    apply regValue_congr
    intro q hq
    exact (body.2.2 q (notOut q (by simp [hq]))).trans (first.2.2 q (notDst q (by simp [hq])))
  have last := copyRegister_correct none src dst len.symm nd2 (by simp) v (records.drop (measurementCount kernel))
  have lastValue : regValue dst out.basis=0 := by
    simpa [out,cp,copySlice,dstV,srcV,copyValue] using last.2.2
  have finalValue : regValue K.out out.basis=(S+O)%p :=
    (regValue_congr _ _ _ (fun q hq => last.2.1 q (notDst q (by simp [hq])))).trans body.2.1
  have final : out.phase=s.phase ∧ regValue K.out out.basis=(S+O)%p ∧
      ∀q,q∉K.out → out.basis q=s.basis q := by
    refine ⟨last.1.trans (body.1.trans first.1),finalValue,?_⟩
    intro q hq
    by_cases inside : q∈dst
    · exact ((regValue_zero _ _).mp lastValue q inside).trans ((regValue_zero _ _).mp dst0 q inside).symm
    · exact (last.2.1 q inside).trans ((body.2.2 q hq).trans (first.2.2 q inside))
  have cm : measurementCount cp=0 := (copyNone_free src dst).2
  simpa [measuredCopiedFold,cp,kernel,u,v,out,S,run_append,cm] using final

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedFoldProof.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measuredFold_eq_copied (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (f : MeasuredSquareFold) :
    L.measuredFold f=measuredCopiedFold L.measuredCore L.core.normFlag f.src f.shift f.canonical
      SquareReduction.c SquareReduction.p := by
  simp [measuredFold,foldDestination,measuredCopiedFold,copySlice,measuredFoldKernel,
    measuredFoldNormalize,measuredCore,normalizeSource,restoreSource,shortCarry,hw.core.work,
    MeasuredSourceNormalizeLayout.normalize,MeasuredSourceNormalizeLayout.restore,List.append_assoc]

theorem measuredFold_interfaces (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (src : List Wire) (hs : ∀q,src.count q≤L.core.product.count q) :
    (src++L.core.normFlag::L.measuredCore.wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  have bound := hs q
  simp only [wires,CuccaroStreamedSquareLayout.wires,measuredCore,foldCarry,foldPad,
    MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem measuredFold_carry_clean (L : CuccaroStreamedSquareWideLayout) (s : BasisState)
    (hc : L.PairClean s) : ∀q∈L.measuredCore.carry,s q=false := by
  intro q hq
  simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq|rfl|rfl
  · exact (regValue_zero _ _).mp hc.pad q hq
  · exact hc.productHigh
  · exact hc.workHigh

/-- Functional contract for the actual emitted fold, including its
short-source copy, optional normalization, canonical add, undo and unload. -/
theorem measuredFold_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (f : MeasuredSquareFold)
    (hs : ∀q,f.src.count q≤L.core.product.count q) (hl : f.shift+f.src.length≤256)
    (O : Nat) (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hcan : f.canonical=true → regValue f.src s.basis*2^f.shift<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O) (hc : L.PairClean s.basis) :
    (run (L.measuredFold f) records s).phase=s.phase ∧
    regValue L.core.out (run (L.measuredFold f) records s).basis=
      (regValue f.src s.basis*2^f.shift+O)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (L.measuredFold f) records s).basis q=s.basis q := by
  rw [L.measuredFold_eq_copied hw f]
  exact measuredCopiedFold_correct L.measuredCore L.core.normFlag 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw) f.src f.shift (L.measuredFold_interfaces hn f.src hs) hl
    (by decide) (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    (by norm_num [SquareReduction.c]) (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    f.canonical O hO s records hcan hc.work ho hc.normFlag hc.outHigh hc.modFlag
    (L.measuredFold_carry_clean s.basis hc) hc.cin

theorem reflectOutput_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ho : regValue L.core.out s.basis=O)
    (hc : L.PairClean s.basis) :
    (run L.reflectOutput records s).phase=s.phase ∧
    regValue L.core.out (run L.reflectOutput records s).basis=SquareReduction.p-1-O ∧
    ∀q,q∉L.core.out → (run L.reflectOutput records s).basis q=s.basis q := by
  let N : MeasuredSourceNormalizeLayout :=
    {word:=L.core.out,carry:=L.shortCarry,cin:=L.core.cin,flag:=L.core.normFlag}
  have nd : N.wires.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist 255 L.foldCarry).count_le q
    simp only [N,MeasuredSourceNormalizeLayout.wires,shortCarry,foldCarry,foldPad,
      wires,CuccaroStreamedSquareLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ht ⊢
    omega
  have len : N.carry.length+1=N.word.length := by
    change L.shortCarry.length+1=L.core.out.length
    rw [(L.measured_bank_widths hw).2.2.2.2,hw.core.out]
  have carry : ∀q∈N.carry,s.basis q=false := by
    intro q hq
    exact L.measuredFold_carry_clean s.basis hc q (List.mem_of_mem_take hq)
  have init : N.Frame s.basis O false s.basis := ⟨ho,hc.normFlag,fun _ _ => rfl⟩
  have reflected := N.reflect_frame nd len SquareReduction.p O
    (by change SquareReduction.p<2^L.core.out.length;rw [hw.core.out];norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    hO s.basis false carry hc.cin s records init
  have eq : N.reflect SquareReduction.p=L.reflectOutput := rfl
  rw [eq] at reflected
  refine ⟨reflected.1,reflected.2.1,?_⟩
  intro q hq
  by_cases flag : q=L.core.normFlag
  · subst q
    exact reflected.2.2.1.trans hc.normFlag.symm
  · exact reflected.2.2.2 q (by
      simpa only [N,MeasuredSourceNormalizeLayout.mutable,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,not_or] using And.intro hq flag)

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedLoopProof.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

structure MeasuredFoldView (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (f : MeasuredSquareFold) : Prop where
  count : ∀q,f.src.count q≤L.core.product.count q
  span : f.shift+f.src.length≤256
  canonical : f.canonical=true → regValue f.src base*2^f.shift<SquareReduction.p

def measuredFoldPayload (base : BasisState) (f : MeasuredSquareFold) : Nat :=
  regValue f.src base*2^f.shift

theorem squareFrame_clean (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (base s : BasisState) (O : Nat) (hf : SquareFrame L.core.out base O s)
    (hc : L.PairClean base) : L.PairClean s := by
  have productAway (q : Wire) (hq : q∈L.core.product) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have pair : L.PairFrame base (regValue L.core.product base) O s :=
    ⟨regValue_congr _ _ _ (fun q hq => hf.2 q (productAway q hq)),hf.1,fun q _ hq => hf.2 q hq⟩
  exact PairFrame.clean L hn base _ O s pair hc

theorem measuredFold_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (f : MeasuredSquareFold)
    (hv : L.MeasuredFoldView base f) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (L.measuredFold f)
      (SquareFrame L.core.out base ((measuredFoldPayload base f+O)%SquareReduction.p)) := by
  have away (q : Wire) (hq : q∈f.src) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have count := hv.count q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  intro s m hf
  have source : regValue f.src s.basis=regValue f.src base :=
    regValue_congr _ _ _ (fun q hq => hf.2 q (away q hq))
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  have result := L.measuredFold_correct hw hn f hv.count hv.span O hO s m
    (by rw [source];exact hv.canonical) hf.1 clean
  refine ⟨result.1,?_,?_⟩
  · simpa [measuredFoldPayload,source] using result.2.1
  · intro q hq
    exact (result.2.2 q hq).trans (hf.2 q hq)

theorem measuredReflection_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (hc : L.PairClean base)
    (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) L.reflectOutput
      (SquareFrame L.core.out base (SquareReduction.p-1-O)) := by
  intro s m hf
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  have result := L.reflectOutput_correct hw hn O hO s m hf.1 clean
  refine ⟨result.1,result.2.1,?_⟩
  intro q hq
  exact (result.2.2 q hq).trans (hf.2 q hq)

def measuredOrientationCast (orientation : Bool) (O : Nat) : ZMod SquareReduction.p :=
  if orientation then -1-(O : ZMod SquareReduction.p) else O

def measuredSignedPayload (base : BasisState) (f : MeasuredSquareFold) : ZMod SquareReduction.p :=
  if f.negative then -(measuredFoldPayload base f : ZMod SquareReduction.p) else measuredFoldPayload base f

def measuredSignedSum (base : BasisState) : List MeasuredSquareFold → ZMod SquareReduction.p
  | [] => 0
  | f::fs => measuredSignedPayload base f+measuredSignedSum base fs

theorem measuredReflection_zmod (O : Nat) (hO : O<SquareReduction.p) :
    ((SquareReduction.p-1-O : Nat) : ZMod SquareReduction.p)=-1-(O : ZMod SquareReduction.p) := by
  have hp : 1≤SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  rw [Nat.cast_sub (by omega : O≤SquareReduction.p-1),Nat.cast_sub hp]
  simp only [ZMod.natCast_self,Nat.cast_one,zero_sub]

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedMaskedProof.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measured_leaf_bank_count (L : CuccaroStreamedSquareWideLayout) (n : Nat) (q : Wire) :
    (L.inputBank.take n++L.leafPad++L.leafCarry).count q≤
      L.core.work.count q+L.foldPad.count q := by
  have inputBound := (List.take_sublist n L.inputBank).count_le q
  have workSplit := congrArg (List.count q) (List.take_append_drop 129 L.core.work)
  have padSplit := congrArg (List.count q) (List.take_append_drop 1 L.foldPad)
  have tailBound := (List.take_sublist 130 (L.foldPad.drop 1)).count_le q
  simp only [inputBank,leafPad,leafCarry,List.count_append] at inputBound workSplit padSplit ⊢
  omega

theorem measured_leaf_nodup (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) :
    (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  have a := hs q
  have b := hd q
  have banks := L.measured_leaf_bank_count src.length q
  simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_cons,
    List.count_append,List.count_nil] at h a banks ⊢
  omega

theorem measured_leaf_banks_clean (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (hc : L.PairClean base) (n : Nat) :
    regValue (L.inputBank.take n) base=0 ∧ regValue L.leafPad base=0 ∧ regValue L.leafCarry base=0 := by
  refine ⟨?_,?_,?_⟩
  · apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero _ _).mp hc.work q (List.mem_of_mem_take (List.mem_of_mem_take hq))
  · apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_take hq)
  · apply (regValue_zero _ _).mpr
    intro q hq
    simp only [leafCarry,List.mem_append] at hq
    rcases hq with hq|hq
    · exact (regValue_zero _ _).mp hc.work q (List.mem_of_mem_drop hq)
    · exact (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop (List.mem_of_mem_take hq))

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedViews.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measured_short_canonical (src : List Wire) (shift : Nat) (base : BasisState)
    (hlen : src.length+shift≤162) : regValue src base*2^shift<SquareReduction.p := by
  have bound := Nat.mul_lt_mul_of_pos_right (regValue_lt src base) (Nat.two_pow_pos shift)
  rw [←Nat.pow_add] at bound
  have power : 2^(src.length+shift)≤(2^162 : Nat) := Nat.pow_le_pow_right (by decide) hlen
  have prime : (2^162 : Nat)<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  exact lt_trans (lt_of_lt_of_le bound power) prime

theorem measured_short_view (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (src : List Wire) (negative : Bool) (shift : Nat)
    (hsrc : ∀q,src.count q≤L.core.product.count q) (hlen : src.length+shift≤162) :
    L.MeasuredFoldView base {negative:=negative,canonical:=true,src:=src,shift:=shift} :=
  ⟨hsrc,by change shift+src.length≤256;omega,fun _ => measured_short_canonical src shift base hlen⟩

theorem measured_naf_views (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (src : List Wire) (negative : Bool) (hsrc : ∀q,src.count q≤L.core.product.count q)
    (hlen : src.length+32≤162) :
    ∀f∈nafMinusOneItems negative src,L.MeasuredFoldView base f := by
  intro f hf
  simp only [nafMinusOneItems,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> apply L.measured_short_view base src _ _ hsrc <;> omega

theorem measured_rotated_count (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.rotated128.count q≤L.core.product.count q := by
  have split := congrArg (List.count q) (List.take_append_drop 128 L.core.product)
  have take := (List.take_sublist 128 (L.core.product.drop 128)).count_le q
  simp only [rotated128,List.count_append] at split ⊢
  omega

theorem measured_rotated_square_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hP : regValue L.core.product base=Y^2) (negative : Bool) :
    L.MeasuredFoldView base {negative:=negative,canonical:=true,src:=L.rotated128} := by
  refine ⟨L.measured_rotated_count,?_,?_⟩
  · simp [rotated128,hw.core.product]
  · intro _
    have val := L.rotated128_value hw base (Y^2) hP
    have radix : (2^256 : Nat)=2^128*2^128 := by norm_num
    have div : (Y^2/2^128)%2^128=(Y^2%2^256)/2^128 := by
      rw [radix,Nat.mod_mul_right_div_self]
    rw [val,div]
    simpa only [Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_comm] using exactFold_rotate128_canonical Y

theorem measured_leaf128_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hY : Y<2^128) (hP : regValue L.core.product base=Y^2)
    (negative : Bool) :
    L.MeasuredFoldView base {negative:=negative,canonical:=true,src:=L.core.product.take 256} := by
  refine ⟨fun q => (List.take_sublist 256 L.core.product).count_le q,by simp [hw.core.product],?_⟩
  intro _
  have square : Y^2<2^256 := by
    simpa using square_bound Y 128 hY
  rw [L.product_take_value hw base (Y^2) hP 256 (by omega),Nat.pow_zero,Nat.mul_one,Nat.mod_eq_of_lt square]
  exact exactFold_leaf128_canonical Y hY

theorem measured_shifted_product_views (L : CuccaroStreamedSquareWideLayout)
    (base : BasisState) (src : List Wire) (negative : Bool) (j : Nat)
    (hs : ∀q,src.count q≤L.core.product.count q) (hlen : src.length=256)
    (hj : j≤32) (hcanonical : regValue src base<SquareReduction.p) :
    ∀f∈shiftedProductItems negative src j,L.MeasuredFoldView base f := by
  intro f hf
  by_cases zero : j=0
  · simp [shiftedProductItems,zero] at hf
    subst f
    refine ⟨hs,by simp [hlen],?_⟩
    simpa using hcanonical
  · simp only [shiftedProductItems,zero,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|hf
    · refine ⟨?_,?_,by simp⟩
      · intro q
        have split := congrArg (List.count q) (List.take_append_drop (256-j) src)
        have bound := hs q
        simp only [rotateFull,List.count_append] at split ⊢
        omega
      · simp [rotateFull,hlen]
    · apply L.measured_naf_views base (src.drop (256-j)) negative
        (fun q => ((List.drop_sublist (256-j) src).count_le q).trans (hs q))
        (by simp [hlen];omega) f hf

theorem measuredA_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hY : Y<2^128) (hP : regValue L.core.product base=Y^2) :
    ∀f∈L.measuredAItems,L.MeasuredFoldView base f := by
  intro f hf
  simp only [measuredAItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with (rfl|rfl)|hf
  · exact L.measured_leaf128_view hw base Y hY hP true
  · exact L.measured_rotated_square_view hw base Y hP false
  · exact L.measured_naf_views base (L.core.product.drop 128) false (L.productDrop_count 128)
      (by simp [hw.core.product]) f hf

theorem measuredB_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hY : Y<2^128) (hP : regValue L.core.product base=Y^2) :
    ∀f∈L.measuredBItems,L.MeasuredFoldView base f := by
  have can : regValue (L.core.product.take 256) base<SquareReduction.p := by
    have view := L.measured_leaf128_view hw base Y hY hP true
    simpa using view.canonical rfl
  have all (negative : Bool) (j : Nat) (hj : j≤32) :
      ∀f∈shiftedProductItems negative (L.core.product.take 256) j,L.MeasuredFoldView base f :=
    L.measured_shifted_product_views base _ negative j
      (fun q => (List.take_sublist 256 L.core.product).count_le q) (by simp [hw.core.product]) hj can
  intro f hf
  simp only [measuredBItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with (((((rfl|hf)|hf)|hf)|hf)|hf)|hf
  · exact L.measured_rotated_square_view hw base Y hP false
  · exact L.measured_naf_views base (L.core.product.drop 128) false (L.productDrop_count 128)
      (by simp [hw.core.product]) f hf
  · exact all true 0 (by omega) f hf
  · exact all true 4 (by omega) f hf
  · exact all false 6 (by omega) f hf
  · exact all true 10 (by omega) f hf
  · exact all true 32 (by omega) f hf

theorem measuredC_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (Y : Nat) (hP : regValue L.core.product base=Y^2) :
    ∀f∈L.measuredCItems,L.MeasuredFoldView base f := by
  intro f hf
  simp only [measuredCItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with (rfl|hf)|rfl
  · exact L.measured_rotated_square_view hw base Y hP true
  · exact L.measured_naf_views base (L.core.product.drop 128) true (L.productDrop_count 128)
      (by simp [hw.core.product]) f hf
  · exact L.measured_short_view base (L.core.product.drop 256) true 128 (L.productDrop_count 256)
      (by simp [hw.core.product])

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/CuccaroStreamedSquareC.lean
noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

def branchCMiddleValue (S O : Nat) : Nat :=
  subRotateProductValue (S^2) O true

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/StreamedSquareValues.lean
noncomputable section

set_option maxRecDepth 5000000
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

private theorem prime_pos : 0<SquareReduction.p := by
  norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]

theorem addModValue_cast (S O : Nat) :
    (addModValue S O : ZMod SquareReduction.p)=(S : ZMod SquareReduction.p)+O := by
  simp only [addModValue,ZMod.natCast_mod,Nat.cast_add]

theorem subModValue_cast (S O : Nat) :
    (subModValue S O : ZMod SquareReduction.p)=(O : ZMod SquareReduction.p)-S := by
  have hs := Nat.mod_lt S prime_pos
  simp only [subModValue,ZMod.natCast_mod]
  rw [Nat.cast_sub (by omega : S%SquareReduction.p≤O+SquareReduction.p)]
  simp only [Nat.cast_add,ZMod.natCast_self,add_zero,ZMod.natCast_mod]

theorem addCMinusOneValue_cast (H O : Nat) :
    (addCMinusOneValue H O : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)+(SquareReduction.c-1)*(H : ZMod SquareReduction.p) := by
  simp only [addCMinusOneValue,addModValue_cast,subModValue_cast,Nat.cast_mul]
  norm_num [SquareReduction.c]
  ring

theorem subCMinusOneValue_cast (H O : Nat) :
    (subCMinusOneValue H O : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)-(SquareReduction.c-1)*(H : ZMod SquareReduction.p) := by
  simp only [subCMinusOneValue,addModValue_cast,subModValue_cast,Nat.cast_mul]
  norm_num [SquareReduction.c]
  ring

theorem radix_cast : (2^256 : ZMod SquareReduction.p)=SquareReduction.c := by
  have hn : 2^256=SquareReduction.p+SquareReduction.c := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have h := congrArg (fun n : Nat => (n : ZMod SquareReduction.p)) hn
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,ZMod.natCast_self,zero_add] using h

theorem addRotateProductValue_cast (P O : Nat) (hb : P<2^256) :
    (addRotateProductValue P O false : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)+(P : ZMod SquareReduction.p)*2^128 := by
  have hhigh : P/2^128<2^128 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0<2^128)).mpr
    simpa only [←Nat.pow_add,show 128+128=256 by omega] using hb
  simp only [addRotateProductValue,addRotate128Value,Bool.false_eq_true,if_false,
    addCMinusOneValue_cast,addModValue_cast,Nat.mod_eq_of_lt hhigh]
  have split := congrArg (fun n : Nat => (n : ZMod SquareReduction.p))
    (Nat.mod_add_div P (2^128))
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at split ⊢
  have radix : ((2 : ZMod SquareReduction.p)^128)^2=SquareReduction.c := by
    rw [←pow_mul]
    exact radix_cast
  rw [←split,←radix]
  ring

theorem subRotateProductValue_cast (P O : Nat) :
    (subRotateProductValue P O true : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)-(P : ZMod SquareReduction.p)*2^128 := by
  simp only [subRotateProductValue,subRotate128Value,if_true,
    subModValue_cast,subCMinusOneValue_cast,Nat.cast_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat]
  have split := congrArg (fun n : Nat => (n : ZMod SquareReduction.p))
    (Nat.mod_add_div P (2^128))
  have highSplit := congrArg (fun n : Nat => (n : ZMod SquareReduction.p))
    (Nat.mod_add_div (P/2^128) (2^128))
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at split highSplit
  have divDiv : (P/2^128)/2^128=P/2^256 := by
    rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  rw [divDiv] at highSplit
  have radix : ((2 : ZMod SquareReduction.p)^128)^2=SquareReduction.c := by
    rw [←pow_mul]
    exact radix_cast
  rw [←radix,←split]
  linear_combination -highSplit

theorem shiftedFull_cast (P j : Nat) (hj : j≤256) (hb : P<2^256) :
    (rotatedFullValue P j : ZMod SquareReduction.p)+
      (SquareReduction.c-1)*(highFullValue P j : ZMod SquareReduction.p)=
      (P : ZMod SquareReduction.p)*2^j := by
  have hpow : 2^(256-j)*2^j=(2^256 : Nat) := by
    rw [←Nat.pow_add,Nat.sub_add_cancel hj]
  have split := Nat.mod_add_div (P%2^256) (2^(256-j))
  have ident : rotatedFullValue P j+2^256*highFullValue P j=
      (P%2^256)*2^j+highFullValue P j := by
    unfold rotatedFullValue highFullValue
    have expanded := congrArg (fun n => n*2^j) split
    dsimp only at expanded
    rw [Nat.add_mul] at expanded
    have term : (2^(256-j)*(P%2^256/2^(256-j)))*2^j=
        2^256*(P%2^256/2^(256-j)) := by
      calc
        _ = (2^(256-j)*2^j)*(P%2^256/2^(256-j)) := by ring
        _ = _ := by rw [hpow]
    rw [term] at expanded
    nlinarith only [expanded]
  have castIdent := congrArg (fun n : Nat => (n : ZMod SquareReduction.p)) ident
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at castIdent
  have modCast : ((P%2^256 : Nat) : ZMod SquareReduction.p)=P := by
    rw [Nat.mod_eq_of_lt hb]
  rw [radix_cast,modCast] at castIdent
  linear_combination castIdent

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedPayloads.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measuredSignedSum_append (base : BasisState) (a b : List MeasuredSquareFold) :
    measuredSignedSum base (a++b)=measuredSignedSum base a+measuredSignedSum base b := by
  induction a with
  | nil => simp [measuredSignedSum]
  | cons f fs ih => simp [measuredSignedSum,ih,add_assoc]

theorem measured_naf_sum (base : BasisState) (src : List Wire) (negative : Bool) :
    measuredSignedSum base (nafMinusOneItems negative src)=
      if negative then -((SquareReduction.c : ZMod SquareReduction.p)-1)*(regValue src base : ZMod SquareReduction.p)
      else ((SquareReduction.c : ZMod SquareReduction.p)-1)*(regValue src base : ZMod SquareReduction.p) := by
  cases negative <;>
    simp [nafMinusOneItems,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,Nat.cast_mul] <;>
    norm_num [SquareReduction.c] <;> ring

def measuredPositiveRotateItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=false,canonical:=true,src:=L.rotated128}]++
    nafMinusOneItems false (L.core.product.drop 128)

theorem measured_positive_rotate_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) (hb : P<2^256) :
    measuredSignedSum base L.measuredPositiveRotateItems=(P : ZMod SquareReduction.p)*2^128 := by
  have value := addRotateProductValue_cast P 0 hb
  simp only [addRotateProductValue,addRotate128Value,Bool.false_eq_true,if_false,addCMinusOneValue_cast,
    addModValue_cast,Nat.cast_zero,zero_add] at value
  simp only [measuredPositiveRotateItems,measuredSignedSum_append,measuredSignedSum,
    measuredSignedPayload,measuredFoldPayload,Bool.false_eq_true,if_false,Nat.pow_zero,Nat.mul_one,add_zero,
    measured_naf_sum,L.rotated128_value hw base P hP,L.product_drop_value hw base P hP 128 (by omega)]
  simpa only [add_zero] using value

theorem measured_shifted_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) (hb : P<2^256)
    (negative : Bool) (j : Nat) (hj : j≤256) :
    measuredSignedSum base (shiftedProductItems negative (L.core.product.take 256) j)=
      if negative then -(P : ZMod SquareReduction.p)*2^j else (P : ZMod SquareReduction.p)*2^j := by
  have source := L.product_take_value hw base P hP 256 (by omega)
  rw [Nat.mod_eq_of_lt hb] at source
  by_cases zero : j=0
  · subst j
    cases negative <;> simp [shiftedProductItems,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,source]
  · have target := shiftedFull_cast P j hj hb
    have rot := L.rotateFull_value hw base P hP j hj
    have high := L.productTakeDrop_value hw base P hP j hj
    cases h : negative
    · simp only [shiftedProductItems,zero,if_false,measuredSignedSum_append,measuredSignedSum,
        measuredSignedPayload,measuredFoldPayload,Bool.false_eq_true,if_false,Nat.pow_zero,Nat.mul_one,
        add_zero,measured_naf_sum,rot,high]
      simpa only [rotatedFullValue,highFullValue] using target
    · simp only [shiftedProductItems,zero,if_false,measuredSignedSum_append,measuredSignedSum,
        measuredSignedPayload,measuredFoldPayload,if_true,Nat.pow_zero,Nat.mul_one,
        add_zero,measured_naf_sum,rot,high]
      simp only [rotatedFullValue,highFullValue] at target
      linear_combination -target

theorem measuredA_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) (hb : P<2^256) :
    measuredSignedSum base L.measuredAItems=
      (P : ZMod SquareReduction.p)*2^128-P := by
  have rot := L.measured_positive_rotate_sum hw base P hP hb
  have source := L.product_take_value hw base P hP 256 (by omega)
  rw [Nat.mod_eq_of_lt hb] at source
  have split : L.measuredAItems=
      [{negative:=true,canonical:=true,src:=L.core.product.take 256}]++L.measuredPositiveRotateItems := rfl
  rw [split,measuredSignedSum_append,rot]
  simp [measuredSignedSum,measuredSignedPayload,measuredFoldPayload,source]
  ring

theorem measuredB_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) (hb : P<2^256) :
    measuredSignedSum base L.measuredBItems=
      (P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P := by
  have rot := L.measured_positive_rotate_sum hw base P hP hb
  have sh0 := L.measured_shifted_sum hw base P hP hb true 0 (by omega)
  have sh4 := L.measured_shifted_sum hw base P hP hb true 4 (by omega)
  have sh6 := L.measured_shifted_sum hw base P hP hb false 6 (by omega)
  have sh10 := L.measured_shifted_sum hw base P hP hb true 10 (by omega)
  have sh32 := L.measured_shifted_sum hw base P hP hb true 32 (by omega)
  have split : L.measuredBItems=L.measuredPositiveRotateItems++
      shiftedProductItems true (L.core.product.take 256) 0++
      shiftedProductItems true (L.core.product.take 256) 4++
      shiftedProductItems false (L.core.product.take 256) 6++
      shiftedProductItems true (L.core.product.take 256) 10++
      shiftedProductItems true (L.core.product.take 256) 32 := rfl
  rw [split,measuredSignedSum_append,measuredSignedSum_append,measuredSignedSum_append,
    measuredSignedSum_append,measuredSignedSum_append,rot,sh0,sh4,sh6,sh10,sh32]
  norm_num [SquareReduction.c]
  ring

theorem measuredC_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) :
    measuredSignedSum base L.measuredCItems=-(P : ZMod SquareReduction.p)*2^128 := by
  have target := subRotateProductValue_cast P 0
  simp only [subRotateProductValue,subRotate128Value,if_true,subModValue_cast,
    subCMinusOneValue_cast,Nat.cast_zero,zero_sub] at target
  simp only [measuredCItems,measuredSignedSum_append,measuredSignedSum,
    measuredSignedPayload,measuredFoldPayload,if_true,Nat.pow_zero,Nat.mul_one,add_zero,
    measured_naf_sum,L.rotated128_value hw base P hP,L.product_drop_value hw base P hP 128 (by omega),
    L.product_drop_value hw base P hP 256 (by omega),Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at target
  linear_combination target

/-- Exact controlled Karatsuba identity for the three leaf contributions.
The radix congruence is secp256k1's p = 2^256 - c, not an approximation. -/
theorem measured_controlled_square_identity (enabled : Bool) (A B : Nat) :
    (((if enabled then A else 0)^2 : Nat) : ZMod SquareReduction.p)*2^128-
      (((if enabled then A else 0)^2 : Nat) : ZMod SquareReduction.p)+
      ((((if enabled then B else 0)^2 : Nat) : ZMod SquareReduction.p)*2^128-
        SquareReduction.c*(((if enabled then B else 0)^2 : Nat) : ZMod SquareReduction.p))-
      (((if enabled then A+B else 0)^2 : Nat) : ZMod SquareReduction.p)*2^128=
        -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) := by
  cases enabled
  · simp
  · simp only [if_true,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    have radix : ((2 : ZMod SquareReduction.p)^128)^2=SquareReduction.c := by
      rw [←pow_mul]
      exact radix_cast
    rw [←radix]
    ring

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedBranches.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measuredOrientationCast_injective (orientation : Bool) (V W : Nat)
    (hv : V<SquareReduction.p) (hw : W<SquareReduction.p)
    (he : measuredOrientationCast orientation V=measuredOrientationCast orientation W) : V=W := by
  have cast : (V : ZMod SquareReduction.p)=(W : ZMod SquareReduction.p) := by
    cases h : orientation
    · simpa only [measuredOrientationCast,h,Bool.false_eq_true,if_false] using he
    · simp only [measuredOrientationCast,h,if_true] at he
      linear_combination -he
  have result := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt hv,ZMod.val_natCast_of_lt hw] using result

theorem measured_product_frame_clean (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (src : List Wire) (hs : ∀q,src.count q≤L.core.product.count q)
    (base t : BasisState) (hc : L.PairClean base) (same : ∀q,q∉src → t q=base q) : L.PairClean t := by
  have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : t q=base q := by
    apply same q
    intro bad
    have notProduct := (L.pairAuxAway hn q hq).1
    have bound := hs q
    have pos := List.count_pos_iff.mpr bad
    rw [List.count_eq_zero.mpr notProduct] at bound
    omega
  constructor
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
  · exact (keep _ (by simp)).trans hc.productHigh
  · exact (keep _ (by simp)).trans hc.outHigh
  · exact (keep _ (by simp)).trans hc.workHigh
  · exact (keep _ (by simp)).trans hc.cin
  · exact (keep _ (by simp)).trans hc.normFlag
  · exact (keep _ (by simp)).trans hc.modFlag

theorem measured_partial_product_value (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (base t : BasisState) (hzero : regValue L.core.product base=0) (P : Nat)
    (hp : regValue (L.core.product.take 256) t=P)
    (same : ∀q,q∉L.core.product.take 256 → t q=base q) : regValue L.core.product t=P := by
  have nd : L.core.product.Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have dis := List.disjoint_take_drop nd (show 256≤256 by omega)
  have high0 : regValue (L.core.product.drop 256) t=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have away : q∉L.core.product.take 256 := fun bad => List.disjoint_left.mp dis bad hq
    exact (same q away).trans ((regValue_zero _ _).mp hzero q (List.mem_of_mem_drop hq))
  have split := regValue_append (L.core.product.take 256) (L.core.product.drop 256) t
  rw [List.take_append_drop,hp,high0,Nat.mul_zero,Nat.add_zero] at split
  exact split

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end

-- source: ECDSAAdd/Arithmetic/MeasuredStreamedCProof.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measured_sum_count (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
  have take := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
  have drop := (List.drop_sublist 128 L.core.y).count_le q
  simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at take ⊢
  omega

theorem measured_sum_aux_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.sum := by
  intro bad
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  have bound := L.measured_sum_count q
  simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_append,List.count_cons,List.count_nil] at h a bound
  omega

theorem measured_sum_disjoint (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    L.core.sum.Disjoint L.core.product ∧ L.core.sum.Disjoint L.core.out := by
  constructor <;> apply List.disjoint_left.mpr <;> intro q hs hq
  all_goals
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hs
    have b := List.count_pos_iff.mpr hq
    have bound := L.measured_sum_count q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h bound
    omega

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end
