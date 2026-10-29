import ShorECDLP.Submission.Entrant.Streaming.ResourceCertificate
import ShorECDLP.Submission.Entrant.Streaming.RepeatEvent
import ShorECDLP.Submission.Entrant.Streaming.IdealDistribution

/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/FinalCertificate.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] batchedOuterPlan actualRoundSource streamingEntry

theorem publicPoint_order (Q : Point) (d : Nat) (h : Q=d • G) : order • Q=0 := by
  rw [h,smul_comm,generator_nsmul_eq_zero,nsmul_zero]

theorem actualRoundAcceptedMass_le_one (Q : Point) (hQ : order • Q=0) :
    Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState) ≤ 1 := by
  exact (Instrument.bornMass_filter_le _ _ _).trans_eq (actualRoundSource_total Q hQ)

/-- 26 independent rounds suffice: `1 - (837/1000)^26 ≥ 99/100` (25 rounds would not). -/
theorem retry26_success :
    (99:ℝ)/100 ≤ independentRetrySuccessProbability ((163:ℝ)/1000) 26 := by
  norm_num [independentRetrySuccessProbability]

theorem actualCompiledRounds_success_of_round (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (h : (163:ℝ)/1000 ≤ Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState)) :
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((((batchedOuterPlan.repeat 26 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate streamingLayout Q b.history).isSome)) (ket zeroBasisState) := by
  rw [streamingLayout,actualCompiledRounds_verified_mass Q hQ hn 26 (by decide)]
  have hm := independentRetrySuccessProbability_mono 26 (actualRoundAcceptedMass_le_one Q hQ) h
  exact retry26_success.trans hm

/-- Actual single-round accepted mass, with the protected decoder and no loss term. -/
theorem streamingRound_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d • G) :
    (163:ℝ)/1000 ≤ Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState) := by
  have hQ := publicPoint_order Q d hd
  rw [actualRoundSource_fixedPair_mass Q hQ hn,selectedIdealTwoAxes_event_eq Q hQ hn]
  exact wrappedIdeal_mass_lower Q G_ne_zero hn hQ d hd

/-- Success of the actual fixed 26-round entry, measured by the protected final decoder. -/
theorem streamingEntry_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((streamingEntry.instantiate Q).run.filter
        (fun b => (verifiedCandidate streamingLayout Q b.history).isSome))
      (ket zeroBasisState) := by
  rw [streamingEntry_instantiate]
  exact actualCompiledRounds_success_of_round Q (publicPoint_order Q d hd) hn
    (streamingRound_success Q d hn hd)

/-- Unconditional protected certificate for the entrant's fixed 26-round streaming program. -/
theorem streamingEntry_certificate_unconditional :
    Certificate officialLimits streamingLayout streamingEntry streamingBounds :=
  streamingEntry_certificate streamingEntry_success
end ShorECDLP.Paper2607_13816.ChallengeMigration
