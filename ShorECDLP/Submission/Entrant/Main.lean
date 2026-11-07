import ShorECDLP.Submission.Entrant.GeometricPhase

-- Entrant/Main.lean
section
namespace ShorECDLP.Entrant
open Challenge
noncomputable section
def bounds : Bounds := ⟨1620,251189020,544000000⟩
def entry : StraightEntry := GeometricActual.entry
def layout : DecodeLayout := GeometricActual.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := GeometricActual.certificate
end
end ShorECDLP.Entrant
end
