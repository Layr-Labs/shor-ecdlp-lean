import ShorECDLP.Submission.Entrant.Prefix

namespace ShorECDLP.Entrant.TightSupport
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare WideSigned WideSigned.Fast16
noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] List.ofFn WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram
def support : List Wire := PathShare.newSourceH ++ [871, 10000]
theorem old_cover : PathShare.newSourceH ⊆ support := List.subset_append_left _ _

namespace FastSite
open WideSigned.Fast16.FastSite
variable {n : Nat} (f : FastSite n)

end FastSite

namespace FastSite1
open WideSigned.Fast16.FastSite1
variable {n : Nat} (f : FastSite1 n)

end FastSite1



attribute [local irreducible] WideSigned.Row16.code WideSigned.Fast16.fprog
  Straight.instantiate AdaptiveCircuit.run

theorem frame_support (r : Nat) (row : (j : Nat) → Straight 65536 j (j + r))
    (hrow : ∀ j, ChallengeMigration.straightWires (row j) ⊆ support)
    (start : Nat) : ChallengeMigration.straightWires (WideSigned.Frame16.program r row start) ⊆ support := by
  have cover : newSourceH ⊆ support := old_cover
  have hs (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.nProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.nProgram, straightWires_reindex]
    exact (nFast_newH j).trans cover
  have hp (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.prefixProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  have hpost (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.suffixProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  rw [WideSigned.Frame16.program, straightWires_castFinish]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp start, hs start⟩, hrow _⟩, hs _⟩, hpost _⟩


def compact : Wire ≃ Wire :=
  (PathShare.piH.trans (Equiv.swap 1619 1616)).trans (Equiv.swap 14436 1617)

theorem compact_bound (v : Wire) (hv : v∈support) : compact v < 1618 := by
  rcases List.mem_append.mp hv with h | h
  · have hp := (PathShare.piH_apply v).trans_lt (PathShare.piH_bound v h)
    simp only [compact,Equiv.trans_apply,Equiv.swap_apply_def]
    dsimp only [Wire] at hp ⊢
    split_ifs <;> omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl <;> decide

theorem compact_point (v : Wire) (hv : v∈pointLogicalWires) : compact v=v := by
  rw [compact,Equiv.trans_apply,Equiv.trans_apply,PathShare.piH_point v hv]
  have hb := point_wire_small v hv
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact_active : compact 836=836 := by decide

theorem compact_pointWrite (P : Point) (s : BasisState) :
    relabelBasis compact (pointWrite P s) = pointWrite P (relabelBasis compact s) := by
  funext v
  by_cases hv : v ∈ pointLogicalWires
  · have he : compact.symm v = v := (Equiv.symm_apply_eq compact).mpr (compact_point v hv).symm
    simp only [relabelBasis, pointWrite, he, if_pos hv]
  · have hi : compact.symm v ∉ pointLogicalWires := by
      intro h
      have he := compact_point _ h
      rw [Equiv.apply_symm_apply] at he
      exact hv (he.symm ▸ h)
    simp only [relabelBasis, pointWrite, if_neg hv, if_neg hi]


end
end ShorECDLP.Entrant.TightSupport
