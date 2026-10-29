import ShorECDLP.Submission.Entrant.Single.Certificate

/-! EDITABLE. One 263/263-bit trial of the Streaming construction
(arXiv:2607.13816v2), using the protected nearest-pair decoder.
The physical arithmetic derives from the Apache-2.0 VerifiedQC Streaming
certificate (PR #551); see LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant
open Challenge

def entry : StraightEntry := Single.entry
def layout : DecodeLayout := Single.layout

/-- Exact proved upper bounds, with the exact measurement count. -/
def bounds : Bounds := ⟨855, 16939890938, 1013190576⟩

theorem certificate : Certificate officialLimits layout entry bounds :=
  Single.certificate

end ShorECDLP.Entrant
