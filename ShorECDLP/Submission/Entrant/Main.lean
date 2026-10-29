import ShorECDLP.Submission.Entrant.TightEntry
import ShorECDLP.Challenge.Official

/-! EDITABLE. Entrant: the Naive baseline with a tight per-round reset.

The 26 Naive rounds are unchanged except that each round resets only the
205,856 wires the round can touch (`tightResetWires`) instead of the dense
206,624-wire envelope, so the instantiated program uses fewer distinct qubits
at the same T model. -/

namespace ShorECDLP.Entrant
open ShorECDLP.Challenge
noncomputable section

def entry : StraightEntry := tightEntry
def layout : DecodeLayout := tightLayout
def bounds : Bounds := tightBounds

theorem certificate : Certificate officialLimits layout entry bounds :=
  tightEntry_certificate

end
end ShorECDLP.Entrant
