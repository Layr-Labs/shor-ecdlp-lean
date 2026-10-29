import ShorECDLP.Submission.Entrant.Streaming.Certificate
import ShorECDLP.Challenge.Official

/-! EDITABLE. Entrant: the certified Streaming construction (arXiv:2607.13816v2) at 6 rounds.

The program is the first 6 rounds of the 56-round Streaming outer plan, ported
from VerifiedQC/ShorECDLP (branch `streaming-dev`, PR #551) under Apache-2.0 into
`Entrant/Streaming`. Every round is the same fixed windowed program with complete coherent
exceptional-case correction. The correction is the in-place XOR block of
`Streaming/Correction.lean`, which works inside the 855-wire core allocation instead of the
upstream five-word batch. `Streaming/Semantics` (part `AveragedSuccess`) proves a per-round
success lower bound of 27/50 by averaging the two Fourier-axis peak probabilities over the
characters (instead of the pointwise worst case 163/1000), and `1 - (23/50)^6 ≥ 99/100`, so
6 rounds suffice. -/

namespace ShorECDLP.Entrant
open Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

def entry : StraightEntry := streamingEntry
def layout : DecodeLayout := streamingLayout

/-- Qubits ≤ 855; T-model ≤ 6 × 14,373,306,005; exactly 6 × 859,686,929 records. -/
def bounds : Bounds := streamingBounds

theorem certificate : Certificate officialLimits layout entry bounds :=
  streamingEntry_certificate_unconditional

end ShorECDLP.Entrant
