import ShorECDLP.Submission.Entrant.GeometricPhase

-- Entrant/Main.lean
-- Verification control: contents identical to the current record submission.
-- This exists only to test whether the CI benchmark step can build this entrant tree
-- at all; it declares no new bound and cannot improve the score.
section
namespace ShorECDLP.Entrant
open Challenge
noncomputable section
def bounds : Bounds := ⟨1620,250699932,544000000⟩
def entry : StraightEntry := GeometricActual.entry
def layout : DecodeLayout := GeometricActual.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := GeometricActual.certificate
end
end ShorECDLP.Entrant
end
