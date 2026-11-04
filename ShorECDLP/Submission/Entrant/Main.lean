import ShorECDLP.Submission.Entrant.Schedule261

namespace ShorECDLP.Entrant
open Challenge

def bounds : Bounds := ⟨1636,269869759,543906879⟩
noncomputable section
def entry : StraightEntry := Schedule29Seventeen244.Flexible.FusedFinal.entry
def layout : DecodeLayout := Schedule29Seventeen244.Flexible.FusedFinal.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Schedule29Seventeen244.Flexible.FusedFinal.certificate
end
end ShorECDLP.Entrant
