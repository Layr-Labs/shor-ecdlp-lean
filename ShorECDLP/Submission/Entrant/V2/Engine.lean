import ShorECDLP.Submission.Entrant.V2.LowInv

/-! EDITABLE. The field-inversion engine used by the V2 point arithmetic.

PointAdd reaches the inversion only through the names below:

* `Engine.program`, a clean circuit on the block-structured `Engine.layout`;
* `Engine.contract`: `out = lhs ^ (p - 2) mod p`, with `rhs` an untouched port;
* `Engine.blocks`: every layout wire lies below `257 * Engine.blocks`.

The engine is `LowInv.lowProgram`: the libsecp256k1 addition chain evaluated with
two-level checkpoint pebbling, so only checkpoints and one segment's scratch are live.
Swapping in a different inversion means changing this file only. -/

namespace ShorECDLP
namespace Secp256k1
namespace V2
namespace Engine

open Arithmetic

def program : Circuit := Entrant.LowInv.lowProgram

def layout : RegisterLayout := Entrant.LowInv.lowLayout

def cost : Nat := 10263089914

/-- Number of 257-wire blocks spanned by the engine layout. -/
def blocks : Nat := 43

theorem contract :
    CleanBinaryContract program layout ShorECDLP.p (fun a _ => a ^ (ShorECDLP.p - 2)) cost := by
  have h := Entrant.LowInv.lowProgram_contract
  rw [Entrant.LowInv.lowCost_eq] at h
  exact h

theorem layout_valid : layout.Valid := Entrant.LowInv.lowLayout_valid

theorem program_tCount : tCount program = cost := contract.counted

theorem lhs_length : layout.lhs.length = 257 := (Secp256k1Instance.reg 0).length_eq

theorem rhs_length : layout.rhs.length = 257 := (Secp256k1Instance.reg 1).length_eq

theorem out_length : layout.out.length = 257 := (Secp256k1Instance.reg 2).length_eq

theorem lhs_nodup : layout.lhs.Nodup := (Secp256k1Instance.regBlock 0).wires_nodup

theorem rhs_nodup : layout.rhs.Nodup := (Secp256k1Instance.regBlock 1).wires_nodup

theorem out_nodup : layout.out.Nodup := (Secp256k1Instance.regBlock 2).wires_nodup

theorem allWires_lt : ∀ w ∈ layout.allWires, w < 257 * blocks :=
  Entrant.LowInv.lowLayout_allWires_lt

theorem program_length_le : program.length ≤ 4075000000 := Entrant.LowInv.lowProgram_length_le

end Engine
end V2
end Secp256k1
end ShorECDLP
