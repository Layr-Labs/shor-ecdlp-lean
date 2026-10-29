import ShorECDLP.Submission.Entrant.Single.Physical
import ShorECDLP.Submission.Entrant.Single.Distribution
import ShorECDLP.Challenge.Official

/-! EDITABLE. Single-trial entrant: protected certificate assembly.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Certificate ====

section
/-! Single-trial certificate for the 263/263-bit protected nearest-pair decoder.
The fixed-table packaging follows the Apache-2.0 VerifiedQC Streaming certificate
(PR #551), for the construction of arXiv:2607.13816v2. See LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Generic packaging avoids unfolding a large coefficient table to transport its length. -/
def fixedEntry {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) : StraightEntry where
  coefficients := List.ofFn f
  finalCursor := e
  program := reindexStraight (Fin.cast List.length_ofFn.symm) p

private theorem ofFn_read {n : Nat} (f : Fin n → PointCoeff) (Q : Point) :
    (fun r : ConstantBit n => readConstant (List.ofFn f).get Q
      ⟨Fin.cast (List.length_ofFn).symm r.point, r.field, r.bit⟩) =
      readConstant f Q := by
  funext r
  simp only [readConstant,List.get_eq_getElem,List.getElem_ofFn,Fin.val_cast,Fin.eta]

theorem fixedEntry_instantiate {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (fixedEntry f p).instantiate Q = p.instantiate (readConstant f Q) Fin.elim0 := by
  dsimp only [fixedEntry,StraightEntry.instantiate]
  rw [reindexStraight_instantiate]
  simp only [Function.comp_def,reindexBit]
  rw [ofFn_read]

theorem fixedEntry_slots {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).program.gateSlots = p.gateSlots :=
  reindexStraight_gateSlots _ _

theorem fixedEntry_wellFormed {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).program.WellFormed ↔ p.WellFormed :=
  reindexStraight_wellFormed _ _

theorem fixedEntry_cursor {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).finalCursor = e := rfl

theorem fixedEntry_rows {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).coefficients.length = n := List.length_ofFn

/-- Package the fixed coefficient data with the exact single-trial producer. -/
def entry : StraightEntry := fixedEntry mixedCoefficientAt program

theorem entry_instantiate (Q : Point) :
    entry.instantiate Q = program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0 :=
  fixedEntry_instantiate _ _ Q

attribute [local irreducible] entry

/-- These values are exactly the proved upper bounds and record count. -/
def bounds : Bounds := ⟨855, 16939890938, 1013190576⟩

theorem certificate : Certificate officialLimits layout entry bounds where
  gateBudget := by
    rw [entry, fixedEntry_slots]
    exact program_slots.trans (by decide)
  recordBudget := by
    unfold entry
    change 1013190576 ≤ officialLimits.measurements
    decide
  tableBudget := by
    rw [entry, fixedEntry_rows]
    decide
  candidateBudget := by
    rw [one_candidate_check]
    decide
  wellFormed := by
    rw [entry, fixedEntry_wellFormed]
    exact program_wellFormed
  resources := by
    intro Q
    rw [entry_instantiate]
    obtain ⟨hq, ht, hm⟩ := program_resource_facts Q
    exact ⟨hq, ht, hm.le⟩
  success := by
    intro Q d hn hd
    rw [entry_instantiate]
    exact Distribution.program_success Q d hn hd

end ShorECDLP.Entrant.Single

end
