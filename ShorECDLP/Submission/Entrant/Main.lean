import ShorECDLP.Submission.Entrant.Schedule262

namespace ShorECDLP.Entrant
open Challenge

def bounds : Bounds := ⟨1636,270265796,543906879⟩
noncomputable section
def entry : StraightEntry := Schedule29Seventeen245.Flexible.FusedFinal.entry
def layout : DecodeLayout := Schedule29Seventeen245.Flexible.FusedFinal.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Schedule29Seventeen245.Flexible.FusedFinal.certificate
end
end ShorECDLP.Entrant
