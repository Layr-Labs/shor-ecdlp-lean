import ShorECDLP.Submission.Entrant.Streaming.OuterExecution
import ShorECDLP.Submission.«2607_13816».Window.StreamHistory

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/SourceAxis.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem fourierContinue_seq (dir : PhaseDir) (ws : List Wire) (prior : List Bool)
    (next : List Bool → AdaptiveCircuit) (tail : AdaptiveCircuit) :
    (fourierContinue dir ws prior next).seq tail =
      fourierContinue dir ws prior (fun h => (next h).seq tail) := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih => simp only [fourierContinue,AdaptiveCircuit.seq,ih]

theorem sourceOuterAxis_seq_streamAxis (calls : List AdaptiveCircuit) (prior : List Bool)
    (tail : AdaptiveCircuit) :
    (sourceOuterAxis streamAddress.reverse calls prior).seq tail = streamAxis calls prior tail := by
  induction calls generalizing prior with
  | nil => rfl
  | cons call calls ih =>
    simp only [sourceOuterAxis,streamAxis,List.reverse_reverse,AdaptiveCircuit.seq]
    rw [circuit_seq_assoc,fourierContinue_seq]
    simp only [ih]

theorem sourceOuterRound_streamAxis (left right : List AdaptiveCircuit) (reset : List Wire) :
    sourceOuterRound streamAddress.reverse left right reset =
      AdaptiveCircuit.unitary [.X 836] (streamAxis left List.nil
        (streamAxis right List.nil (.unitary [.X 836] (measureResetWithCorrection reset (fun _ => []))))) := by
  simp only [sourceOuterRound,sourceOuterAxis_seq_streamAxis]

end ShorECDLP.Paper2607_13816.ChallengeMigration
