import ShorECDLP.Submission.Entrant.FusedRow14

namespace ShorECDLP.Entrant.Schedule29Seventeen247.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit body ledger cover in
private theorem fusedClearWiden {limits : Limits} {layout : DecodeLayout} {entry : StraightEntry}
    {old new : Bounds} (cert : Certificate limits layout entry old)
    (hq : old.qubits ≤ new.qubits) (ht : old.tModel ≤ new.tModel)
    (hm : old.measurements ≤ new.measurements) : Certificate limits layout entry new :=
  { cert with resources := fun Q =>
      ⟨(cert.resources Q).1.trans hq, (cert.resources Q).2.1.trans ht, (cert.resources Q).2.2.trans hm⟩ }

theorem matched_fused_certificate (n14 : ModNarrow body 13) (n15 : ModNarrow body 14)
    (n16 : ModNarrow body 15)
    (hSupport : ledger.support.length ≤ 1634) (hSlot : body.slotBound ≤ 3000000000)
    (hR15 : n15.records ≤ 1659546) (hR16 : n16.records ≤ 1758490)
    (hReset : body.reset.length ≤ 854)
    (hT15 : n15.tBound ≤ 15844248) (hT16 : n16.tBound ≤ 16536856)
    (hC15 : n15.credit ≤ 2263464) (hC16 : n16.credit ≤ 2362408)
    (hq : (1938 : Wire) ∉ ledger.support) (hy : (1939 : Wire) ∉ 1938 :: ledger.support) :
    letI : Programs body := triPrograms n14 n15 n16
    Certificate officialLimits (lowerLayout 1938 entry layout) (fourEntry 1938 1939 entry)
      ⟨1636, 271057873, 543906879⟩ := by
  letI : Programs body := triPrograms n14 n15 n16
  have hwin : windowSlots ≤ 3000000000 := max_le le_rfl hSlot
  have hbaseS : 32 * windowSlots + 176382 ≤ officialLimits.gateSlots := by
    change 32 * windowSlots + 176382 ≤ 4000000000000000
    omega
  have hbaseR : 131071 + 20 * (triPrograms n14 n15 n16).records16 + 9 * (triPrograms n14 n15 n16).records15 +
      472 + body.reset.length + 34114 ≤ officialLimits.measurements := by
    change 131071 + 20 * n16.records + 9 * n15.records + 472 + body.reset.length + 34114 ≤ 47471340504
    omega
  have hsrc : 917497 + 20 * (triPrograms n14 n15 n16).cost16 + 9 * (triPrograms n14 n15 n16).cost15 +
      56244 ≤ 491238726 := by
    change 917497 + 20 * n16.tBound + 9 * n15.tBound + 56244 ≤ 491238726
    omega
  have hslots : 32 * windowSlots + 176382 + 24 * 491238726 + 2 ≤ officialLimits.gateSlots := by
    change 32 * windowSlots + 176382 + 24 * 491238726 + 2 ≤ 4000000000000000
    omega
  have hrecords : 131071 + 20 * (triPrograms n14 n15 n16).records16 + 9 * (triPrograms n14 n15 n16).records15 +
      472 + body.reset.length + 34114 + 491238726 ≤ officialLimits.measurements := by
    change 131071 + 20 * n16.records + 9 * n15.records + 472 + body.reset.length + 34114 +
      491238726 ≤ 47471340504
    omega
  have raw := bounded_four_certificate (triProgramCredit n14 n15 n16) 1938 1939 491238726
    hbaseS hbaseR hsrc hslots hrecords hq hy
  have hcounts := (source_counts 1938 1939 491238726 hbaseS hbaseR hsrc).1
  have hcursor : entry.finalCursor ≤ 52668153 := by
    rw [source_cursor]
    change 131071 + 20 * n16.records + 9 * n15.records + 472 + body.reset.length + 34114 ≤ 52668153
    omega
  apply fusedClearWiden raw
  · change ledger.support.length + 2 ≤ 1636
    omega
  · change 4 * (131071 + 20 * n16.credit + 9 * n15.credit) + 56244 + 1 ≤ 271057873
    omega
  · change entry.finalCursor + added entry.program ≤ 543906879
    omega
end
end ShorECDLP.Entrant.Schedule29Seventeen247.Flexible

namespace ShorECDLP.Entrant.Schedule29Seventeen247.Flexible.FusedFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] WEXUnlookupWidth13.compactProgram WEXUnlookupWidth14.compactProgram WEXUnlookup.Width15Fused.fastCompactProgram WEXUnlookupWidth14.Fused.fastCompactProgram
  WEXUnlookupWidth13.bodyProgram WEXUnlookupWidth14.bodyProgram
  WEXUnlookupWidth13.ccx WEXUnlookupWidth14.ccx
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount
  WEX.literalToffolis WEX.normalizeW Nat.add Nat.mul AndGadget.added

def narrow13 : ModNarrow WEXUnlookup.compactBody 13 := WEXUnlookupWidth13.fastNarrow
def narrow14 : ModNarrow WEXUnlookup.compactBody 14 := WEXUnlookupWidth14.Fused.fastNarrow
def narrow15 : ModNarrow WEXUnlookup.compactBody 15 := WEXUnlookup.Width15Fused.fastNarrow

theorem n13_records : narrow13.records ≤ 1626836 := by
  exact le_rfl
theorem n14_records : narrow14.records ≤ 1659546 := by
  exact le_rfl
theorem n15_records : narrow15.records ≤ 1758490 := by
  exact le_rfl
theorem n13_cost : narrow13.tBound ≤ 15615278 := by
  exact le_rfl
theorem n14_cost : narrow14.tBound ≤ 15844248 := by
  exact le_rfl
theorem n15_cost : narrow15.tBound ≤ 16536856 := by
  exact le_rfl

attribute [local irreducible] narrow13 narrow14 narrow15
local instance bodyInstance : Single.WindowBody := WEXUnlookup.compactBody
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEXUnlookup.compactBody
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
local instance programInstance : Programs bodyInstance := triPrograms narrow13 narrow14 narrow15

private theorem count13_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 15615278) :
    c ≤ 2230754 := by omega
private theorem count14_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 15844248) :
    c ≤ 2263464 := by omega
private theorem count15_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 16536856) :
    c ≤ 2362408 := by omega

theorem n13_credit : narrow13.credit ≤ 2230754 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow13.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow13.program 0) (narrow13.zero 0) read Fin.elim0
  have hc := narrow13.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count13_bound _ _ he' (ht.trans n13_cost)
theorem n14_credit : narrow14.credit ≤ 2263464 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow14.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow14.program 0) (narrow14.zero 0) read Fin.elim0
  have hc := narrow14.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count14_bound _ _ he' (ht.trans n14_cost)
theorem n15_credit : narrow15.credit ≤ 2362408 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow15.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow15.program 0) (narrow15.zero 0) read Fin.elim0
  have hc := narrow15.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count15_bound _ _ he' (ht.trans n15_cost)

def entry : StraightEntry := fourEntry 1938 1939 Flexible.entry
def layout : DecodeLayout := lowerLayout 1938 Flexible.entry Flexible.layout
def bounds : Bounds := ⟨1636, 271057873, 543906879⟩

theorem certificate : Certificate officialLimits layout entry bounds := by
  apply @matched_fused_certificate bodyInstance resourcesInstance coverInstance narrow13 narrow14 narrow15
  · change WEXUnlookup.compactSupport.length ≤ 1634
    norm_num [WEXUnlookup.compactSupport,MeasuredClear.hotBank]
  · rw [bodyInstance, WEXUnlookup.compactBody]
    decide +kernel
  · exact n14_records.trans (by norm_num)
  · exact n15_records.trans (by norm_num)
  · change WEXUnlookup.compactBody.reset.length ≤ 854
    exact WEXUnlookup.compactBody_ledger.2.2.2.le
  · exact n14_cost.trans (by norm_num)
  · exact n15_cost.trans (by norm_num)
  · exact n14_credit
  · exact n15_credit
  · change (1938 : Wire) ∉ WEXUnlookup.compactSupport
    decide +kernel
  · change (1939 : Wire) ∉ 1938 :: WEXUnlookup.compactSupport
    decide +kernel
end
end ShorECDLP.Entrant.Schedule29Seventeen247.Flexible.FusedFinal

namespace ShorECDLP.Entrant
open Challenge

def bounds : Bounds := ⟨1636,271057873,543906879⟩
noncomputable section
def entry : StraightEntry := Schedule29Seventeen247.Flexible.FusedFinal.entry
def layout : DecodeLayout := Schedule29Seventeen247.Flexible.FusedFinal.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Schedule29Seventeen247.Flexible.FusedFinal.certificate
end
end ShorECDLP.Entrant
