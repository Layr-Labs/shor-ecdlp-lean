import ShorECDLP.Submission.Entrant.GeometricPhase
import ShorECDLP.Submission.Entrant.Schedule26

-- Entrant/Main.lean
section
namespace ShorECDLP.Entrant
open Challenge
noncomputable section
def bounds : Bounds := ⟨1615,243599621,544000000⟩
def entry : StraightEntry := Schedule26Actual.entry
def layout : DecodeLayout := Schedule26Actual.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Schedule26Actual.certificate
end
end ShorECDLP.Entrant
end
