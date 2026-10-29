import ShorECDLP.Submission.Entrant.V2.InvChain

/-! EDITABLE. The field-inversion engine used by the V2 point arithmetic.

PointAdd reaches the inversion only through the names below:

* `Engine.program`, a clean circuit on the block-structured `Engine.layout`;
* `Engine.contract`: `out = lhs ^ (p - 2) mod p`, with `rhs` an untouched port;
* `Engine.blocks`: every layout wire lies below `257 * Engine.blocks`.

Swapping in a different inversion means changing this file only. -/

namespace ShorECDLP
namespace Secp256k1
namespace V2
namespace Engine

open Arithmetic

def program : Circuit := InvChain.invProgramFused

def layout : RegisterLayout := InvChain.invLayout

def cost : Nat := 5482463294

/-- Number of 257-wire blocks spanned by the engine layout. -/
def blocks : Nat := 278

theorem contract :
    CleanBinaryContract program layout ShorECDLP.p (fun a _ => a ^ (ShorECDLP.p - 2)) cost :=
  InvChain.inv_contract

theorem layout_valid : layout.Valid := InvChain.invLayout_valid

theorem program_tCount : tCount program = cost := contract.counted

theorem lhs_length : layout.lhs.length = 257 := (Secp256k1Instance.reg 0).length_eq

theorem rhs_length : layout.rhs.length = 257 := (Secp256k1Instance.reg 271).length_eq

theorem out_length : layout.out.length = 257 := (Secp256k1Instance.reg 270).length_eq

theorem lhs_nodup : layout.lhs.Nodup := (Secp256k1Instance.regBlock 0).wires_nodup

theorem rhs_nodup : layout.rhs.Nodup := (Secp256k1Instance.regBlock 271).wires_nodup

theorem out_nodup : layout.out.Nodup := (Secp256k1Instance.regBlock 270).wires_nodup

theorem allWires_lt : ∀ w ∈ layout.allWires, w < 257 * blocks :=
  InvChain.invLayout_allWires_lt

theorem program_length_le : program.length ≤ 2176334853 := InvChain.invProgramFused_length_le

end Engine
end V2
end Secp256k1
end ShorECDLP
