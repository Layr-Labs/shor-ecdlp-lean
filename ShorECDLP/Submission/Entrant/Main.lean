import ShorECDLP.Submission.Entrant.GeometricPhase
import ShorECDLP.Challenge.ExtendedContract

-- Entrant/Main.lean
section
namespace ShorECDLP.Entrant
open Challenge
noncomputable section
def bounds : Bounds := ⟨1620,250699906,544000000⟩
def entry : StraightEntry := GeometricActual.entry
def layout : DecodeLayout := GeometricActual.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := GeometricActual.certificate

/-! ### Optional extended diagnostics

`docs/CHALLENGE.md` allows a submission to supply `extendedBounds` and
`extendedCertificate`. Supplying them makes the judge report these explicit
values instead of the conservative bound it would otherwise derive through
`Certificate.extend` (`Toffoli <= tModel / 7`, `non-Clifford <= gateSlots`).
The numbers below are exactly that derived pair, so this changes no metric. -/

/-- Explicit diagnostics: the Toffoli bound derived from the T model, and the
organizer gate-slot limit for the non-Clifford count. -/
def extendedBounds : ExtendedBounds := ⟨bounds.tModel / 7, officialLimits.gateSlots⟩

/-- The same circuit, the same bounds, checked through the protected extension. -/
theorem extendedCertificate :
    ExtendedCertificate officialLimits layout entry bounds extendedBounds :=
  certificate.extend

end
end ShorECDLP.Entrant
end
