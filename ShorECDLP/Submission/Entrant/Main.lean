import ShorECDLP.Submission.Entrant.Streaming.FinalCertificate
import ShorECDLP.Challenge.Official

/-! EDITABLE. Entrant: the certified Streaming construction (arXiv:2607.13816v2) at 26 rounds.

The program is the first 26 rounds of the upstream 56-round Streaming outer plan, ported
from VerifiedQC/ShorECDLP (branch `streaming-dev`, PR #551) under Apache-2.0 into
`Entrant/Streaming`. Every round is the same fixed windowed program with complete coherent
exceptional-case correction; the proved per-round success lower bound 163/1000 already gives
`1 - (837/1000)^26 ≥ 99/100`, so 30 rounds are dropped. This keeps the record count below the
published measurement limit. -/

namespace ShorECDLP.Entrant
open Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

def entry : StraightEntry := streamingEntry
def layout : DecodeLayout := streamingLayout

/-- Qubits ≤ 3,932; T-model ≤ 26 × 14,393,374,641; exactly 26 × 860,607,482 records. -/
def bounds : Bounds := streamingBounds

theorem certificate : Certificate officialLimits layout entry bounds :=
  streamingEntry_certificate_unconditional

end ShorECDLP.Entrant
