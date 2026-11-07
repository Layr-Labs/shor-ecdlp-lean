import ShorECDLP.Submission.Entrant.Schedule27

-- Entrant/Main.lean
section
namespace ShorECDLP.Entrant
open Challenge
noncomputable section
def bounds : Bounds := ⟨1623,251189159,544000000⟩
def entry : StraightEntry := Width16Actual.entry
def layout : DecodeLayout := Width16Actual.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Width16Actual.certificate
end
end ShorECDLP.Entrant
end
