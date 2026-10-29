import ShorECDLP.Submission.«2607_13816».Challenge.Outer

/-! EDITABLE. Decoder layout for an entry with fewer outer rounds.

The protected `OuterPlan.layout` reads 56 rounds. The entrant runs only the first `k ≤ 56`
rounds of the same outer plan, so its layout keeps exactly the first `k` protected trial
position vectors, unchanged. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The protected wrappedShift layout restricted to its first `k` trials. -/
def OuterPlan.roundsLayout {n : Nat} (p : OuterPlan n) (k : Nat) (hk : k ≤ 56) : DecodeLayout :=
  ⟨.wrappedShift, legacyDecoderParams,
    List.ofFn (fun r : Fin k => p.positions (Fin.castLE hk r)), by simpa using hk⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration
