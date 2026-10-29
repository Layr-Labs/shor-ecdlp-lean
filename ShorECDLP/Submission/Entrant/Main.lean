import ShorECDLP.Submission.Entrant.Protocol

/-! Exact parity-phase inverse QFTs on the accepted single-trial arithmetic entrant.
The complete measurement instrument is preserved, including its decoder record. -/
namespace ShorECDLP.Entrant
open Quantum Secp256k1 Challenge NaiveChallenge Improved
noncomputable section

attribute [local irreducible] Straight.WellFormed tableE improvedProgram

def entry : StraightEntry := optimizedEntry
def layout : DecodeLayout := Frontier.layout
def bounds : Bounds := ⟨13892, 22108079775816, 526⟩

theorem certificate : Certificate officialLimits layout entry bounds where
  gateBudget := optimizedEntry_slots.trans (by decide)
  recordBudget := by decide
  tableBudget := by
    change tableE.length ≤ officialLimits.coefficientRows
    rw [tableE_length]
    decide
  candidateBudget := Frontier.certificate.candidateBudget
  wellFormed := optimizedEntry_wf
  resources := by
    intro Q
    refine ⟨optimizedEntry_qubits Q, (optimizedEntry_t Q).trans (by decide), ?_⟩
    change (entry.program.instantiate _ _).measurementCount ≤ _
    rw [Straight.measurementCount]
    exact Nat.le_refl _
  success := by
    intro Q d hn hd
    change (99 : ℝ) / 100 ≤ Instrument.bornMass
      ((optimizedEntry.instantiate Q).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) _
    rw [optimizedEntry_run]
    exact Frontier.certificate.success Q d hn hd

end
end ShorECDLP.Entrant
