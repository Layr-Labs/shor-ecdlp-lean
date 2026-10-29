import ShorECDLP.Submission.Entrant.V2.LowInv

/-! EDITABLE. The field-inversion engine used by the V2 point arithmetic.

PointAdd reaches the inversion only through the names below:

* `Engine.program`, a clean circuit on the block-structured `Engine.layout`;
* `Engine.contract`: `out = lhs ^ (p - 2) mod p`, with `rhs` an untouched port;
* `Engine.wireBound`: every layout wire lies below it; `Engine.blocks` bounds the block ids
  of the add and multiply engines that share the same offset.

The engine is `LowInv.lowProgram`: the libsecp256k1 addition chain evaluated with
two-level checkpoint pebbling, so only checkpoints and one segment's scratch are live.
Swapping in a different inversion means changing this file only. -/

namespace ShorECDLP
namespace Secp256k1
namespace V2
namespace Engine

open Arithmetic

def program : Circuit := Entrant.LowInv.lowProgram

def layout : RegisterLayout := Entrant.LowInv.lowLayoutX

def cost : Nat := 10425834650

/-- Number of 257-wire blocks spanned by the engine's full registers. -/
def blocks : Nat := 34

/-- Every engine wire lies below this bound.  The engine itself ends with the multiplier flag
at the first wire of block 34; the layout also reserves the 2570 wires above it, so that a
copy of the engine shifted ten blocks up stays inside the layout. -/
def wireBound : Nat := 257 * 34 + 1 + 2570

theorem contract :
    CleanBinaryContract program layout ShorECDLP.p (fun a _ => a ^ (ShorECDLP.p - 2)) cost := by
  have h := Entrant.LowInv.lowProgram_contractX
  rw [Entrant.LowInv.lowCost_eq] at h
  exact h

theorem layout_valid : layout.Valid := Entrant.LowInv.lowLayoutX_valid

theorem program_tCount : tCount program = cost := contract.counted

theorem lhs_length : layout.lhs.length = 257 := (Secp256k1Instance.reg 0).length_eq

theorem rhs_length : layout.rhs.length = 257 := (Secp256k1Instance.reg 1).length_eq

theorem out_length : layout.out.length = 257 := (Secp256k1Instance.reg 2).length_eq

theorem lhs_nodup : layout.lhs.Nodup := (Secp256k1Instance.regBlock 0).wires_nodup

theorem rhs_nodup : layout.rhs.Nodup := (Secp256k1Instance.regBlock 1).wires_nodup

theorem out_nodup : layout.out.Nodup := (Secp256k1Instance.regBlock 2).wires_nodup

theorem allWires_lt : ∀ w ∈ layout.allWires, w < wireBound :=
  Entrant.LowInv.lowLayoutX_allWires_lt

/-- Every wire below the bound belongs to the layout. -/
theorem allWires_covers : ∀ w : Nat, w < wireBound → w ∈ layout.allWires :=
  Entrant.LowInv.lowLayoutX_covers

/-! ## The forward sweep

`fwdProgram` runs the engine's checkpoint chain forward only: it leaves `lhs ^ (p - 2)` in
`out` and its checkpoints in the work wires.  Its reverse uncomputes them. -/

def fwdProgram : Circuit := Entrant.LowInv.lowFwd

def fwdCost : Nat := 5228174644

/-- The engine's own registers, without the reserved headroom. -/
def core : RegisterLayout := Entrant.LowInv.lowLayout

theorem core_valid : core.Valid := Entrant.LowInv.lowLayout_valid

theorem core_lt : ∀ w ∈ core.allWires, w < 257 * 34 + 1 :=
  Entrant.LowInv.lowLayout_allWires_lt

theorem core_lhs_length : core.lhs.length = 257 := (Secp256k1Instance.reg 0).length_eq

theorem core_out_length : core.out.length = 257 := (Secp256k1Instance.reg 2).length_eq

theorem fwd_correct (st : BasisState) (hlhs : regValue core.lhs st < ShorECDLP.p)
    (hclean : Clean (core.out ++ core.work) st) :
    regValue core.out (Classical.run fwdProgram st) =
        regValue core.lhs st ^ (ShorECDLP.p - 2) % ShorECDLP.p ∧
      ∀ w, w ∉ core.allWires → Classical.run fwdProgram st w = st w :=
  Entrant.LowInv.lowFwd_correct st hlhs hclean

theorem fwd_usesOnly : CircuitUsesOnly core.allWires fwdProgram :=
  Entrant.LowInv.lowFwd_usesOnly

/-- The wires the forward sweep actually touches. -/
def engList : List Wire := Entrant.LowInv.engList

theorem fwd_usesOnly_eng : CircuitUsesOnly engList fwdProgram :=
  Entrant.LowInv.lowFwd_usesOnly_eng

theorem core_lhs_eng : ∀ w ∈ core.lhs, w ∈ engList := by
  intro w hw
  have h := Entrant.LowInv.mem_reg.mp hw
  simp only [engList, Entrant.LowInv.engList, List.mem_append, List.mem_range'_1]
  omega

theorem core_out_eng : ∀ w ∈ core.out, w ∈ engList := by
  intro w hw
  have h := Entrant.LowInv.mem_reg.mp hw
  simp only [engList, Entrant.LowInv.engList, List.mem_append, List.mem_range'_1]
  omega

theorem fwd_HPFree : Classical.HPFree fwdProgram := (Entrant.LowInv.lowFwd_good 0).hp

theorem fwd_wellFormed : CircuitWellFormed fwdProgram := (Entrant.LowInv.lowFwd_good 0).wf

theorem fwd_tCount : tCount fwdProgram = fwdCost := by
  rw [show fwdCost = Entrant.LowInv.lowFwdCost from Entrant.LowInv.lowFwdCost_eq.symm]
  exact (Entrant.LowInv.lowFwd_good 0).tc

theorem fwd_length_le : fwdProgram.length ≤ 4140000000 := (Entrant.LowInv.lowFwd_good 0).len

theorem program_length_le : program.length ≤ 4140000000 := Entrant.LowInv.lowProgram_length_le

end Engine
end V2
end Secp256k1
end ShorECDLP
