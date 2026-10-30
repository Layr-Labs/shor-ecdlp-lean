import ShorECDLP.Submission.Entrant.InverseFeedback

namespace ShorECDLP.Entrant
open ShorECDLP.Challenge

noncomputable def entry : StraightEntry := InverseKick.entry
noncomputable def layout : DecodeLayout := InverseKick.layout
def bounds : Bounds := InverseKick.bounds

theorem certificate : Certificate officialLimits layout entry bounds := InverseKick.certificate
end ShorECDLP.Entrant
