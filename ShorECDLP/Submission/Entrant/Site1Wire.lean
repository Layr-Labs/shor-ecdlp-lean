import ShorECDLP.Submission.Entrant.Site1Fast

/-! Wiring the two-pass SelectSwap replacement for `site1` into both the narrow (15-bit) and
wide (16-bit) window rows.

Replaces only block #2 (`site1`) of `WEXFast.W15G.rowH` and `WideBank8.Row16.code`:
- Narrow (`Narrow15`): records `1,652,890 → 1,645,984`, credit `≤ 2,252,071 → ≤ 2,245,165` (`-6,906`).
- Wide (`Wide16`): records `1,743,514 → 1,728,416`, credit `≤ 2,342,691 → ≤ 2,327,593` (`-15,098`).
Total savings across 19 wide + 8 narrow windows: `342,110` Toffolis = `1,368,440` T-model gates. -/

namespace ShorECDLP.Entrant.Site1Wire
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare Site1Fast
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

attribute [local irreducible] ECDSAAdd.run scrInP1 scrInP2 pair1Prog
  scrPairWires scrShortWires scrDExtraWires WEXUnlookup.rowC WEXUnlookup.rowHead
  WEXFast.W15G.rowH WideBank8.Row16.code WEXFast.rowCF
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8
  MeasuredClear.fixupProgram MeasuredClear.fixupProgram8
  ECDSAAdd.Baselines.normalizeProgram
  WEXFast.hprog WEXFast.hblockProg WideBank8.Fast16.fprog WideBank8.Fast16.fblockProg

/-! ### Shared garbage wire lists and clean-pool invariants -/

def gA1 : List Wire := List.range' 14115 258
def gA2 : List Wire := List.range' 14373 257 ++ [14883]
def gA3 : List Wire := List.range' 15399 256 ++ List.range' 15142 2
def garbA : List Wire := gA1 ++ gA2 ++ gA3
def gB : List Wire := List.range' 14115 258 ++ List.range' 14884 255

theorem gA1_len : gA1.length = 258 := by simp [gA1]
theorem gA2_len : gA2.length = 258 := by simp [gA2]
theorem gA3_len : gA3.length = 258 := by simp [gA3]
theorem garbA_len : garbA.length = 774 := by simp [garbA, gA1_len, gA2_len, gA3_len]
theorem gB_len : gB.length = 513 := by simp [gB]

theorem mem_gA1 {w : Wire} : w ∈ gA1 ↔ 14115 ≤ w ∧ w < 14373 := by simp [gA1, List.mem_range'_1]
theorem mem_gA2 {w : Wire} : w ∈ gA2 ↔ (14373 ≤ w ∧ w < 14630) ∨ w = 14883 := by
  simp [gA2, List.mem_range'_1]
theorem mem_gA3 {w : Wire} : w ∈ gA3 ↔ (15399 ≤ w ∧ w < 15655) ∨ (15142 ≤ w ∧ w < 15144) := by
  simp [gA3, List.mem_range'_1]
theorem mem_gB {w : Wire} : w ∈ gB ↔ (14115 ≤ w ∧ w < 14373) ∨ (14884 ≤ w ∧ w < 15139) := by
  simp [gB, List.mem_range'_1]

theorem mem_garbA {w : Wire} (h : w ∈ garbA) :
    (14115 ≤ w ∧ w < 14630) ∨ w = 14883 ∨ (15142 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
  simp only [garbA, List.mem_append, mem_gA1, mem_gA2, mem_gA3] at h
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem mem_short_garbA {w : Wire} (h : w ∈ shortWires ++ garbA) :
    (14115 ≤ w ∧ w < 14630) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
  rcases List.mem_append.mp h with h | h
  · have := shortWires_bounds w h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · have := mem_garbA h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem mem_pairExtra {w : Wire} (h : w ∈ pairExtraWires) :
    (14373 ≤ w ∧ w < 14630) ∨ w = 14883 ∨ (15399 ≤ w ∧ w < 15654) := by
  rcases List.mem_append.mp h with h | h
  · have := pairWires_bounds w h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rw [scrDExtraWires_explicit, List.mem_range'_1] at h
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem mem_pairExtra_gB {w : Wire} (h : w ∈ pairExtraWires ++ gB) :
    (14115 ≤ w ∧ w < 14630) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
  rcases List.mem_append.mp h with h | h
  · have := mem_pairExtra h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rw [mem_gB] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem pool_band_in_newH7 {w : Wire}
    (h : (14115 ≤ w ∧ w < 14630) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655)) :
    w ∈ PoolHost.newSourceH7 := by
  rw [PoolHost.newSourceH7_mem]
  refine ⟨Or.inr ?_, ?_⟩
  · unfold oldWork; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · unfold PoolHost.retiredH7 retiredH retired; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem pool_band_in_dialogPool {w : Wire}
    (h : (14115 ≤ w ∧ w < 14630) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655)) :
    w ∈ streamLayout.dialogPool := by
  have h1 : w ∈ streamLayout.dialogPool.take 2613 := by
    rw [mem_pool_take 2613 (le_refl _)]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  exact List.mem_of_mem_take h1

theorem short_garbA_nodup : (shortWires ++ garbA).Nodup := by
  have nd1 : gA1.Nodup := List.nodup_range'
  have nd2 : gA2.Nodup := by
    rw [gA2, List.nodup_append]
    refine ⟨List.nodup_range', List.nodup_singleton _, fun a ha b hb hab => ?_⟩
    subst hab; simp only [List.mem_range'_1, List.mem_singleton] at ha hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have nd3 : gA3.Nodup := by
    rw [gA3, List.nodup_append]
    refine ⟨List.nodup_range', List.nodup_range', fun a ha b hb hab => ?_⟩
    subst hab; simp only [List.mem_range'_1] at ha hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have nd12 : (gA1 ++ gA2).Nodup := by
    rw [List.nodup_append]
    refine ⟨nd1, nd2, fun a ha b hb hab => ?_⟩
    subst hab; rw [mem_gA1] at ha; rw [mem_gA2] at hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have ndg : garbA.Nodup := by
    rw [garbA, List.nodup_append]
    refine ⟨nd12, nd3, fun a ha b hb hab => ?_⟩
    subst hab; rw [List.mem_append, mem_gA1, mem_gA2] at ha; rw [mem_gA3] at hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  rw [List.nodup_append]
  refine ⟨scrShortWires_nd, ndg, fun a ha b hb hab => ?_⟩
  subst hab; have h1 := shortWires_bounds a ha; have h2 := mem_garbA hb
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem garbA_nodup : garbA.Nodup := (List.nodup_append.mp short_garbA_nodup).2.1

theorem pairExtra_nodup : pairExtraWires.Nodup := by
  rw [pairExtraWires, List.nodup_append]
  refine ⟨scrPairWires_nd, ?_, fun a ha b hb hab => ?_⟩
  · rw [scrDExtraWires_explicit]; exact List.nodup_range'
  · subst hab; exact extra_not_scrWires a hb (List.mem_append_left _ ha)

theorem gB_nodup : gB.Nodup := by
  rw [gB, List.nodup_append]
  refine ⟨List.nodup_range', List.nodup_range', fun a ha b hb hab => ?_⟩
  subst hab; simp only [List.mem_range'_1] at ha hb; omega

theorem pairExtra_gB_nodup : (pairExtraWires ++ gB).Nodup := by
  rw [List.nodup_append]
  refine ⟨pairExtra_nodup, gB_nodup, fun a ha b hb hab => ?_⟩
  subst hab; have h1 := mem_pairExtra ha; rw [mem_gB] at hb
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem gB_sub_short_garbA : gB ⊆ shortWires ++ garbA := by
  intro w hw
  rw [mem_gB] at hw
  rcases hw with hw | hw
  · exact List.mem_append_right _ (by simp only [garbA, List.mem_append]; left; left; exact mem_gA1.mpr hw)
  · apply List.mem_append_left
    rw [shortWires, scrShortWires_explicit]
    simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.mem_singleton]
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem pairExtra_sub_garbA : pairExtraWires ⊆ garbA := by
  intro w hw
  have h := mem_pairExtra hw
  simp only [garbA, List.mem_append, mem_gA1, mem_gA2, mem_gA3]
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem dialogPool_sub_work : streamLayout.dialogPool ⊆ streamLayout.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 streamLayout.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool] at h1
  simp only [work, outWork, temporary, inPlaceFlags, selectors, PointAddLayout.work, PointAddLayout.words,
    PointAddLayout.flags, List.flatten_cons, List.flatten_nil, List.append_nil, List.count_append,
    List.count_cons, List.count_nil] at h1 ht ⊢
  omega

theorem scrHead_wires_not_pool (w : Wire) (hw : w ∈ ECDSAAdd.wires scrHeadProgram) :
    w < 14115 ∨ w = 19816 := by
  have hs : scrHeadProgram = [.CX streamLayout.control streamLayout.core.double] ++
      [.CX streamLayout.control streamLayout.core.equalX] ++
      zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect := rfl
  have hd : streamLayout.core.double = 14114 := rfl
  have hi : streamLayout.infinitySelect = 19816 := rfl
  rw [hs, zeroFlag] at hw
  simp only [ECDSAAdd.wires_append, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false,
    sl_control, sl_equalX, hd, hi, streamLayout_point] at hw
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem liveReady_pool_after_b01 {n : Nat} (read : ConstantBit n → Bool) (r : Nat → Fin n)
    (a : Nat) (s : BasisState) (hs : liveReady s) (m0 m1 : List Bool) :
    let st0 : ECDSAAdd.State := ⟨false, s⟩
    let st1 := ECDSAAdd.run (reference2 read a ([Block2.plain (WideSigned.Rows.code r (wLiteral ([.X 838])))])) m0 st0
    let st2 := ECDSAAdd.run (reference2 read a ([Block2.plain (WideSigned.Rows.code r scrHead)])) m1 st1
    Clean streamLayout.dialogPool st2.basis := by
  intro st0 st1 st2 w hw
  have hwb : 14115 ≤ w ∧ w < 16728 := by
    have h1 : w ∈ streamLayout.dialogPool.take 2613 := by
      have ht : streamLayout.dialogPool.take 2613 = streamLayout.dialogPool := by
        simp only [dialogPool, List.take_take, Nat.min_self]
      rwa [ht]
    exact (mem_pool_take 2613 (le_refl _)).mp h1
  have hr0 : reference2 read a ([Block2.plain (WideSigned.Rows.code r (wLiteral ([.X 838])))]) = [.X 838] := by
    simp [reference2, erase2, Block2.code, WideSigned.Rows.code, WideSigned.Rows.instr, wLiteral,
      specialize, WInstr.specialize, Tmpl.instantiate_lit]
  have hr1 : reference2 read a ([Block2.plain (WideSigned.Rows.code r scrHead)]) = scrHeadProgram := by
    simp [reference2, erase2, Block2.code, WideSigned.Rows.code, WideSigned.Rows.instr, scrHead,
      scrHeadProgram, wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_append, Tmpl.instantiate_lit]
  have hns1 : w ∉ ECDSAAdd.wires scrHeadProgram := fun hm => by
    have := scrHead_wires_not_pool w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hns0 : w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program) := fun hm => by
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_singleton] at hm
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  dsimp only [st2, st1]
  rw [hr1, run_outside_basis scrHeadProgram m1 _ w hns1, hr0, run_outside_basis [.X 838] m0 st0 w hns0]
  exact hs.2.1 w (List.mem_append_left _ (dialogPool_sub_work hw))

/-! ### Normalized `shortPart` and `tailPart` metrics -/

def shortNorm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram shortPart
def tailNorm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram tailPart
def mShort : Nat := ECDSAAdd.measurementCount shortPart
def mTail : Nat := ECDSAAdd.measurementCount tailPart

theorem shortNorm_meas : ECDSAAdd.measurementCount shortNorm = mShort :=
  ECDSAAdd.Baselines.normalize_measurements shortPart

theorem tailNorm_meas : ECDSAAdd.measurementCount tailNorm = mTail :=
  ECDSAAdd.Baselines.normalize_measurements tailPart

theorem mShort_add_mTail : mShort + mTail = ECDSAAdd.measurementCount site1Arith := by
  rw [mShort, mTail]; exact site1_counts_split.2.1

theorem shortNorm_valid : ∀ i ∈ shortNorm, ECDSAAdd.Challenge.instructionValid i :=
  ECDSAAdd.Baselines.normalize_physical shortPart shortPart_physical

theorem tailNorm_valid : ∀ i ∈ tailNorm, ECDSAAdd.Challenge.instructionValid i :=
  ECDSAAdd.Baselines.normalize_physical tailPart tailPart_physical

theorem norm_toff_split_gen (pA pB pC pD pE : ECDSAAdd.Program) :
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram pB) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (pA ++ (pC ++ (pD ++ pE)))) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (pA ++ (pB ++ (pC ++ (pD ++ pE))))) := by
  have hna (p q : ECDSAAdd.Program) :
      ECDSAAdd.Baselines.normalizeProgram (p ++ q) =
        ECDSAAdd.Baselines.normalizeProgram p ++ ECDSAAdd.Baselines.normalizeProgram q := by
    unfold ECDSAAdd.Baselines.normalizeProgram; simp
  simp only [hna, ECDSAAdd.toffoliCount_append]; omega

theorem norm_toff_split :
    ECDSAAdd.toffoliCount shortNorm + ECDSAAdd.toffoliCount tailNorm =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram site1Arith) := by
  rw [shortNorm, tailNorm, tailPart, site1Arith_eq]
  exact norm_toff_split_gen pairPart shortPart (pointDialogGenericFlag streamLayout)
    (ECDSAAdd.Frontier.zrep streamLayout) pair1Prog

theorem norm_slots_split :
    ECDSAAdd.Challenge.gateSlots shortNorm + ECDSAAdd.Challenge.gateSlots tailNorm =
      ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) := by
  rw [shortNorm, tailNorm, ECDSAAdd.Baselines.normalize_slots, ECDSAAdd.Baselines.normalize_slots,
    ECDSAAdd.Baselines.normalize_slots]
  exact site1_counts_split.2.2

theorem shortPart_wires_newH7 : ECDSAAdd.wires shortNorm ⊆ PoolHost.newSourceH7.toFinset := by
  rw [shortNorm, ECDSAAdd.Baselines.normalize_wires]
  intro w hw
  have hmem : WInstr.literal site1Arith ∈ erase2 WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [h1, h2, List.map_append, erase2_append, erase2_append]
    apply List.mem_append_left; apply List.mem_append_left
    rw [WEXUnlookup.rowPre3]
    simp only [List.map_cons, List.map_nil, erase2_cons, erase2_nil, List.append_nil, toBlock2,
      Block2.code, UnitSite.code, site1, MaskedSite.prefix]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hunit : Block2.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩ ∈ WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [h1, h2, List.map_append]
    apply List.mem_append_left; apply List.mem_append_left
    rw [WEXUnlookup.rowPre3]; simp [toBlock2]
  have hno4 := (PoolHost.rowC_unit_no4 _ hunit).1 site1Arith (by simp [UnitSite.code, site1, MaskedSite.prefix, wLiteral]) w (shortPart_wires_sub hw)
  have hstrict : ¬ (hostWire ∈ ECDSAAdd.wires site1Arith ∨ hostWire2 ∈ ECDSAAdd.wires site1Arith ∨
      hostWire3 ∈ ECDSAAdd.wires site1Arith) := by
    intro hh
    have hm_rowH : WEXFast.HBlock.blk (.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩)) ∈ WEXFast.W15G.rowH := by
      unfold WEXFast.W15G.rowH
      apply List.mem_append_left
      refine List.mem_map.mpr ⟨.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩), ?_, rfl⟩
      rw [WideBank8.Row16.headF]
      apply List.mem_append_left
      rw [WEXUnlookup.rowPre3]; simp [toBlock2]
    have hst := WEXFast.W15G.rowH_strict _ hm_rowH site1Arith
      (by simp [WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, erase2, Block2.code, UnitSite.code, site1, MaskedSite.prefix, wLiteral])
      (by rcases hh with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)))
    obtain ⟨c, hc⟩ := hst; cases hc
  rcases PoolHost.rowC_lit_relaxed7 site1Arith hmem w (shortPart_wires_sub hw) with e | e | e | e | e | e | e | e
  · exact absurd (Or.inl (e ▸ shortPart_wires_sub hw)) hstrict
  · exact absurd (Or.inr (Or.inl (e ▸ shortPart_wires_sub hw))) hstrict
  · exact absurd (Or.inr (Or.inr (e ▸ shortPart_wires_sub hw))) hstrict
  · exact absurd e hno4.1
  · exact absurd e hno4.2.1
  · exact absurd e hno4.2.2.1
  · exact absurd e hno4.2.2.2
  · exact List.mem_toFinset.mpr e

theorem tailPart_wires_newH7 : ECDSAAdd.wires tailNorm ⊆ PoolHost.newSourceH7.toFinset := by
  rw [tailNorm, ECDSAAdd.Baselines.normalize_wires]
  intro w hw
  have hmem : WInstr.literal site1Arith ∈ erase2 WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [h1, h2, List.map_append, erase2_append, erase2_append]
    apply List.mem_append_left; apply List.mem_append_left
    rw [WEXUnlookup.rowPre3]
    simp only [List.map_cons, List.map_nil, erase2_cons, erase2_nil, List.append_nil, toBlock2,
      Block2.code, UnitSite.code, site1, MaskedSite.prefix]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hunit : Block2.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩ ∈ WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [h1, h2, List.map_append]
    apply List.mem_append_left; apply List.mem_append_left
    rw [WEXUnlookup.rowPre3]; simp [toBlock2]
  have hno4 := (PoolHost.rowC_unit_no4 _ hunit).1 site1Arith (by simp [UnitSite.code, site1, MaskedSite.prefix, wLiteral]) w (tailPart_wires_sub hw)
  have hstrict : ¬ (hostWire ∈ ECDSAAdd.wires site1Arith ∨ hostWire2 ∈ ECDSAAdd.wires site1Arith ∨
      hostWire3 ∈ ECDSAAdd.wires site1Arith) := by
    intro hh
    have hm_rowH : WEXFast.HBlock.blk (.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩)) ∈ WEXFast.W15G.rowH := by
      unfold WEXFast.W15G.rowH
      apply List.mem_append_left
      refine List.mem_map.mpr ⟨.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩), ?_, rfl⟩
      rw [WideBank8.Row16.headF]
      apply List.mem_append_left
      rw [WEXUnlookup.rowPre3]; simp [toBlock2]
    have hst := WEXFast.W15G.rowH_strict _ hm_rowH site1Arith
      (by simp [WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, erase2, Block2.code, UnitSite.code, site1, MaskedSite.prefix, wLiteral])
      (by rcases hh with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)))
    obtain ⟨c, hc⟩ := hst; cases hc
  rcases PoolHost.rowC_lit_relaxed7 site1Arith hmem w (tailPart_wires_sub hw) with e | e | e | e | e | e | e | e
  · exact absurd (Or.inl (e ▸ tailPart_wires_sub hw)) hstrict
  · exact absurd (Or.inr (Or.inl (e ▸ tailPart_wires_sub hw))) hstrict
  · exact absurd (Or.inr (Or.inr (e ▸ tailPart_wires_sub hw))) hstrict
  · exact absurd e hno4.1
  · exact absurd e hno4.2.1
  · exact absurd e hno4.2.2.1
  · exact absurd e hno4.2.2.2
  · exact List.mem_toFinset.mpr e

theorem measureThen_slots_le {n R : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor + R))
    (B : Nat) (hn : ∀ cursor refs, (next cursor refs).gateSlots ≤ B)
    (wires : List Wire) (start : Nat) (refs : List (Fin start)) :
    (MeasuredClear.measureThen next wires start refs).gateSlots ≤ B := by
  induction wires generalizing start with
  | nil => exact hn start refs
  | cons w ws ih =>
    simp only [MeasuredClear.measureThen, castFinish_gateSlots, Straight.gateSlots]
    exact ih _ _

theorem rows_port_probeRows (p : LookupPort 32768)
    (h : ∀ a, (p.ref a).point = probeRows a) : WideSigned.Rows.port probeRows p = p := by
  cases p with | mk ref val tgt =>
  simp only [WideSigned.Rows.port]
  congr 1; funext a
  have ha := h a
  cases hr : ref a with | mk pt fld bt =>
  simp only [hr] at ha; subst ha; rfl

theorem rows_ports_probeRows (ps : List (LookupPort 32768))
    (h : ∀ p ∈ ps, ∀ a, (p.ref a).point = probeRows a) :
    WideSigned.Rows.ports probeRows ps = ps := by
  unfold WideSigned.Rows.ports
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, rows_port_probeRows p (h p List.mem_cons_self),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem indexedPorts_row_eq (ws : List Wire) (refs : Nat → Nat → ConstantBit 32768) (v : Bool)
    (hr : ∀ a i, (refs a i).point = probeRows a) :
    ∀ p ∈ indexedPorts ws refs v, ∀ a, (p.ref a).point = probeRows a := by
  induction ws generalizing refs with
  | nil => intro p hp; cases hp
  | cons w ws ih =>
    intro p hp a
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hr a 0
    · exact ih (fun a i => refs a (i + 1)) (fun a i => hr a (i + 1)) p hp a

theorem retarget_row_eq (ps : List (LookupPort 32768)) (ws : List Wire)
    (h : ∀ p ∈ ps, ∀ a, (p.ref a).point = probeRows a) :
    ∀ p ∈ retarget ps ws, ∀ a, (p.ref a).point = probeRows a := by
  induction ps generalizing ws with
  | nil => intro p hp; cases hp
  | cons p ps ih =>
    cases ws with
    | nil => intro q hq; cases hq
    | cons w ws =>
      intro q hq a
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h p List.mem_cons_self a
      · exact ih ws (fun x hx => h x (List.mem_cons_of_mem _ hx)) q hq a

theorem shortPorts_row_eq : ∀ p ∈ shortPorts probeRows, ∀ a, (p.ref a).point = probeRows a := by
  apply retarget_row_eq
  intro p hp a
  unfold scrInShortBits shortNegPorts at hp
  simp only [List.mem_append, List.mem_cons] at hp
  rcases hp with (rfl | hp) | hp
  · rfl
  · exact indexedPorts_row_eq _ _ _ (fun _ _ => rfl) p hp a
  · exact indexedPorts_row_eq _ _ _ (fun _ _ => rfl) p hp a

theorem pairExtraPorts_row_eq : ∀ p ∈ pairExtraPorts probeRows, ∀ a, (p.ref a).point = probeRows a := by
  intro p hp a
  unfold pairExtraPorts at hp
  rcases List.mem_append.mp hp with hp | hp
  · refine retarget_row_eq _ _ ?_ p hp a
    intro q hq b
    unfold scrPairBits pairParityPorts at hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | hq) | rfl
    · rfl
    · exact indexedPorts_row_eq _ _ _ (fun _ _ => rfl) q hq b
    · rfl
  · exact indexedPorts_row_eq _ _ _ (fun _ _ => rfl) p hp a

theorem shortPorts_probeRows_id :
    WideSigned.Rows.ports probeRows (shortPorts probeRows) = shortPorts probeRows :=
  rows_ports_probeRows _ shortPorts_row_eq

theorem pairExtraPorts_probeRows_id :
    WideSigned.Rows.ports probeRows (pairExtraPorts probeRows) = pairExtraPorts probeRows :=
  rows_ports_probeRows _ pairExtraPorts_row_eq

theorem sitePorts_probeRows_id :
    WideSigned.Rows.ports probeRows (sitePorts probeRows) = sitePorts probeRows := by
  apply rows_ports_probeRows
  intro p hp a
  unfold sitePorts WEX.scrInPorts at hp
  simp only [List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · exact pairExtraPorts_row_eq p (List.mem_append_left _ hp) a
  · exact shortPorts_row_eq p hp a
  · exact pairExtraPorts_row_eq p (List.mem_append_right _ hp) a

theorem site1_probeRows_id :
    WideSigned.Rows.site probeRows (site1 probeRows) = site1 probeRows := by
  simp only [WideSigned.Rows.site, site1, sitePorts_probeRows_id, WideSigned.Rows.code,
    WideSigned.Rows.instr, wLiteral, List.map_cons, List.map_nil]

theorem x838_meas_zero : ECDSAAdd.measurementCount ([.X 838] : ECDSAAdd.Program) = 0 := rfl

theorem scrHeadProgram_meas_zero : ECDSAAdd.measurementCount scrHeadProgram = 0 := by
  simp [scrHeadProgram, zeroFlag, ECDSAAdd.measurementCount]

theorem literalSlotSum_le_of_mem {n : Nat} (c : WCode n) (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ c) : ECDSAAdd.Challenge.gateSlots p ≤ literalSlotSum c := by
  induction c with
  | nil => cases hp
  | cons i c ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.le_add_right _ _
    · exact (ih hp).trans (by cases i <;> simp only [literalSlotSum]; exact Nat.le_add_left _ _; exact le_rfl)

theorem hblockRec_std {n} (b : Block2 n) :
    WEXFast.hblockRec (.blk (.std b)) = PathShare.blockRecP2 PathShare.bank15 b := rfl

theorem hblockTP_unit {n} (u : UnitSite n) :
    WEXFast.hblockTP (.blk (.std (.unit u))) = PathShare.blockTP2 PathShare.bank15 (.unit u) := rfl

theorem hrecs_cons {n} (a : WEXFast.HBlock n) (r : WEXFast.HCode n) :
    WEXFast.hrecs (a :: r) = WEXFast.hblockRec a + WEXFast.hrecs r := rfl

theorem hcodeTP_cons {n} (a : WEXFast.HBlock n) (r : WEXFast.HCode n) :
    WEXFast.hcodeTP (a :: r) = WEXFast.hblockTP a + WEXFast.hcodeTP r := rfl

theorem fblockRec_std {n} (b : Block2 n) :
    WideBank8.Fast16.fblockRec (.std b) = WideBank8.blockRecP2 WideBank8.Fast16.bank15 b := rfl

theorem fblockTP_std {n} (b : Block2 n) :
    WideBank8.Fast16.fblockTP (.std b) =
      WideBank8.blockTP2 WideBank8.Fast16.bank15 b + PoolHost.blockExtra b := rfl

theorem frecs_cons {n} (a : WideBank8.Fast16.FBlock2 n) (r : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.frecs (a :: r) = WideBank8.Fast16.fblockRec a + WideBank8.Fast16.frecs r := rfl

theorem fcodeTP_cons {n} (a : WideBank8.Fast16.FBlock2 n) (r : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.fcodeTP (a :: r) = WideBank8.Fast16.fblockTP a + WideBank8.Fast16.fcodeTP r := rfl

attribute [local irreducible] shortPart tailPart pairPart site1Arith shortNorm tailNorm mShort mTail
  ECDSAAdd.measurementCount ECDSAAdd.toffoliCount ECDSAAdd.Challenge.gateSlots
  WEXFast.hcodeTP WEXFast.hrecs WEXFast.hblockRec WEXFast.hblockTP
  WideBank8.Fast16.fcodeTP WideBank8.Fast16.frecs WideBank8.Fast16.fblockRec WideBank8.Fast16.fblockTP
  Straight.WellFormed MeasuredClear.measureThen
  SS2.selCode SS2.swapNet SS1.selCode SS1.swapNet
  shortPorts pairExtraPorts sitePorts clearData

def site1RecGen (cA cB mS mT fR : Nat) : Nat := cA + 774 + mS + 258 + cB + 513 + mT + 513 + fR

theorem add_assoc_3 (s a b : Nat) : s + a + b = s + (a + b) := Nat.add_assoc s a b

theorem twoPass_fin_gen (s rA cA cB mS mT fR : Nat) (hr : rA = cA) :
    s + rA + (774 + (mS + (258 + (cB + (513 + (mT + (513 + fR))))))) =
      s + site1RecGen cA cB mS mT fR := by
  subst hr; unfold site1RecGen; omega

theorem row_cast_arith (s a b c d e : Nat) (h : a + b + c + d = e) :
    s + a + b + c + d = s + e := by omega

theorem row_rec_arith (a b h2 r s1 diff tot : Nat)
    (ht : a + b + h2 + r = tot) (hd : h2 = s1 + diff) :
    a + b + s1 + r = tot - diff := by omega

theorem rowTP_arith (a b h2 r s1 diff : Nat)
    (hd : h2 = s1 + diff) :
    a + b + s1 + r = (a + b + h2 + r) - diff := by omega

theorem rowTP_sub_arith (tot a b h2 r s1 diff : Nat)
    (ht : tot = a + b + h2 + r) (hd : h2 = s1 + diff) :
    a + b + s1 + r = tot - diff := by omega

theorem tcount_mul7_4 (a b c d t : Nat) (h : a + b + c + d = t) :
    7 * a + 7 * b + (7 * c + 7 * d) = 7 * t := by omega

theorem twoPass_tcount_arith (cA gA tS cB gB tT tF : Nat) :
    7 * (cA + gA) + (7 * tS + (7 * (cB + gB) + (7 * tT + 7 * tF))) =
      7 * (cA + gA + tS + cB + gB + tT + tF) := by ring

theorem mPerm_len_arith (nA nB nP nAll : Nat) (h1 : nP ≤ nB) (h2 : nA + nB = nAll) :
    min nP nB + nA + (nB - nP) = nAll := by omega

theorem narrow_rec_diff_arith (mAll mS mT fR : Nat) (hcs : mS + mT = mAll) (hf : fR = 382) :
    mAll + 32767 + 771 + (255 + 127) = site1RecGen 8191 16383 mS mT fR + 6906 := by
  unfold site1RecGen; omega

theorem wide_rec_diff_arith (mAll mS mT fR : Nat) (hcs : mS + mT = mAll) (hf : fR = 510) :
    mAll + 65535 + 771 + (255 + 255) = site1RecGen 16383 32767 mS mT fR + 15098 := by
  unfold site1RecGen; omega

theorem narrow_tp_diff_arith (tS tT : Nat) :
    tS + tT + 1 * (2 ^ 15 - 1) + (255 + 120) =
      (8191 + 774 + tS + 16383 + 513 + tT + (255 + 120)) + 6906 := by omega

theorem wide_tp_diff_arith (tS tT : Nat) :
    tS + tT + 1 * (2 ^ 16 - 1) + (255 + 247) =
      (16383 + 774 + tS + 32767 + 513 + tT + (255 + 247)) + 15098 := by omega

theorem litToff_lookup_lit {n} (ctl : Option Wire) (ps : List (LookupPort n)) (p : ECDSAAdd.Program) :
    literalToffolis (normalizeW ([WInstr.lookup ctl ps, WInstr.literal p])) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram p) := by
  simp [normalizeW, normalizeWInstr, literalToffolis]

theorem trav_lookup_lit {n} (ctl : Option Wire) (ps : List (LookupPort n)) (p : ECDSAAdd.Program) :
    traversals ([WInstr.lookup ctl ps, WInstr.literal p]) = 1 := by
  simp [traversals]

theorem litRec_lookup_lit {n} (ctl : Option Wire) (ps : List (LookupPort n)) (p : ECDSAAdd.Program) :
    literalRecords ([WInstr.lookup ctl ps, WInstr.literal p]) = ECDSAAdd.measurementCount p := by
  simp [literalRecords]

theorem litRec_lookup_lit_lookup {n} (ctl1 ctl2 : Option Wire)
    (ps1 ps2 : List (LookupPort n)) (p : ECDSAAdd.Program) :
    literalRecords ([WInstr.lookup ctl1 ps1, WInstr.literal p, WInstr.lookup ctl2 ps2]) =
      ECDSAAdd.measurementCount p := by
  simp [literalRecords]

attribute [local irreducible] normalizeW literalRecords literalToffolis traversals
  codeSlots literalSlotSum portTotal

theorem phase_cancel_base (ph : Bool) (mag c a1 a2 a3 p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (c * (a1 * a2 * a3 * p)) =
      mag * c * a1 * a2 * a3 * (if ph then (-1 : ℂ) else 1) := by
  calc (if ph then (-1 : ℂ) else 1) * (mag * p) * (c * (a1 * a2 * a3 * p))
      = mag * c * a1 * a2 * a3 * (if ph then (-1 : ℂ) else 1) * (p * p) := by ring
    _ = mag * c * a1 * a2 * a3 * (if ph then (-1 : ℂ) else 1) := by rw [hp, mul_one]

theorem phase_cancel_step2 (ph : Bool) (mag c a1 a2 p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (if ph then (-1 : ℂ) else 1) * (c * a1 * a2 * p) =
      mag * c * a1 * a2 := by
  cases ph <;>
  · simp only [ite_true, ite_false, Bool.false_eq_true]
    calc _ = (mag * c * a1 * a2) * (p * p) := by ring
      _ = mag * c * a1 * a2 := by rw [hp, mul_one]

theorem phase_cancel_step1 (ph : Bool) (mag c a1 p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (if ph then (-1 : ℂ) else 1) * (c * a1 * p) =
      mag * c * a1 := by
  cases ph <;>
  · simp only [ite_true, ite_false, Bool.false_eq_true]
    calc _ = (mag * c * a1) * (p * p) := by ring
      _ = mag * c * a1 := by rw [hp, mul_one]

theorem phase_cancel_step0 (ph : Bool) (mag c p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (if ph then (-1 : ℂ) else 1) * (c * p) =
      mag * c := by
  cases ph <;>
  · simp only [ite_true, ite_false, Bool.false_eq_true]
    calc _ = (mag * c) * (p * p) := by ring
      _ = mag * c := by rw [hp, mul_one]

theorem clearData_loaded_of_clean {n : Nat} (read : ConstantBit n → Bool) (ps : List (LookupPort n))
    (a : Nat) (root : Wire) (s : BasisState) (hroot : s root = true)
    (hnd : (portTargets ps).Nodup)
    (hcl : Clean (portTargets ps) (tableXorState (portMask read ps a) true s)) :
    ∀ q ∈ clearData ps, s q.target = decide (read (q.ref a) = q.value) := by
  intro q hq
  rw [clearData] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hcl' : Clean (portTargets ps) (tableXorState (portMask read ps a) (s root) s) := by
    rw [hroot]; exact hcl
  have hL := loaded_of_clean_unload read ps a root s hnd hcl' p hp
  rw [hroot, Bool.true_and] at hL
  exact hL

theorem clearData_loaded_of_xor {n : Nat} (read : ConstantBit n → Bool) (ps : List (LookupPort n))
    (a : Nat) (s0 s1 : BasisState)
    (hnd : (portTargets ps).Nodup)
    (hcl0 : Clean (portTargets ps) s0)
    (heq : ∀ w ∈ portTargets ps, s1 w = tableXorState (portMask read ps a) true s0 w) :
    ∀ q ∈ clearData ps, s1 q.target = decide (read (q.ref a) = q.value) := by
  intro q hq
  rw [clearData] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hpt : p.target ∈ portTargets ps := List.mem_map.mpr ⟨p, hp, rfl⟩
  change s1 p.target = decide (read (p.ref a) = p.value)
  rw [heq p.target hpt]
  dsimp only [tableXorState]
  rw [port_selected read ps a hnd p hp, hcl0 p.target hpt]
  simp only [Bool.true_and, Bool.false_xor]

theorem clearRegister_eq_xor_of_loaded {n : Nat} (read : ConstantBit n → Bool) (ps : List (LookupPort n))
    (a : Nat) (s : BasisState)
    (hnd : (portTargets ps).Nodup)
    (hload : ∀ q ∈ clearData ps, s q.target = decide (read (q.ref a) = q.value)) :
    clearRegister (portTargets ps) s = tableXorState (portMask read ps a) true s := by
  funext w
  by_cases hw : w ∈ portTargets ps
  · rw [clearRegister_clean (portTargets ps) s w hw]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hL : s p.target = decide (read (p.ref a) = p.value) :=
      hload ⟨p.ref, p.value, p.target⟩ (by rw [clearData]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
    dsimp only [tableXorState]
    rw [port_selected read ps a hnd p hp, hL, Bool.true_and, Bool.xor_self]
  · rw [MeasuredClear.clearRegister_frame (portTargets ps) s w hw]
    exact (tableXorState_outside _ _ _ _ (fun hm => hw (tableBitsMask_subset _ _ hm))).symm

theorem twoPass_state_congr {n : Nat} (read : ConstantBit n → Bool) (sp pp : List (LookupPort n))
    (a : Nat) (sA1 : ECDSAAdd.State) (mB : List Bool) (c : List Wire)
    (hmid : clearRegister c sA1.basis = tableXorState (portMask read sp a) true sA1.basis) :
    let sMid1 : ECDSAAdd.State := ⟨sA1.phase, clearRegister c sA1.basis⟩
    let sL2_1 : ECDSAAdd.State := ⟨sMid1.phase, tableXorState (portMask read pp a) true sMid1.basis⟩
    let sMid2 : ECDSAAdd.State := ⟨sA1.phase, tableXorState (portMask read sp a) true sA1.basis⟩
    let sL2_2 : ECDSAAdd.State := ⟨sMid2.phase, tableXorState (portMask read pp a) true sMid2.basis⟩
    (⟨(ECDSAAdd.run tailPart mB sL2_1).phase,
      tableXorState (portMask read pp a) true (ECDSAAdd.run tailPart mB sL2_1).basis⟩ : ECDSAAdd.State) =
    ⟨(ECDSAAdd.run tailPart mB sL2_2).phase,
      tableXorState (portMask read pp a) true (ECDSAAdd.run tailPart mB sL2_2).basis⟩ := by
  intro sMid1 sL2_1 sMid2 sL2_2
  have hm : sMid1 = sMid2 := congrArg (ECDSAAdd.State.mk sA1.phase) hmid
  have hl : sL2_1 = sL2_2 := congrArg (fun m : ECDSAAdd.State =>
    (⟨m.phase, tableXorState (portMask read pp a) true m.basis⟩ : ECDSAAdd.State)) hm
  rw [hl]

theorem site1_twoPass_run_free {n : Nat} (read : ConstantBit n → Bool) (r : Nat → Fin n)
    (a : Nat) (s sA1 : ECDSAAdd.State) (mA mB : List Bool)
    (hmA : mA.length = ECDSAAdd.measurementCount shortPart)
    (hmB : mB.length = ECDSAAdd.measurementCount tailPart)
    (hroot : s.basis windowRoot = true)
    (hclean : Clean (streamLayout.dialogPool.take 258) s.basis)
    (hsA1 : sA1 = ECDSAAdd.run shortPart mA
      ⟨s.phase, tableXorState (portMask read (WideSigned.Rows.ports r (shortPorts probeRows)) a) true s.basis⟩) :
    let sp := WideSigned.Rows.ports r (shortPorts probeRows)
    let pp := WideSigned.Rows.ports r (pairExtraPorts probeRows)
    let sMid : ECDSAAdd.State := ⟨sA1.phase, tableXorState (portMask read sp a) true sA1.basis⟩
    let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp a) true sMid.basis⟩
    let sB1 := ECDSAAdd.run tailPart mB sL2
    let mPerm := mB.take (ECDSAAdd.measurementCount pairPart) ++ mA ++ mB.drop (ECDSAAdd.measurementCount pairPart)
    (⟨sB1.phase, tableXorState (portMask read pp a) true sB1.basis⟩ : ECDSAAdd.State) =
      ECDSAAdd.run ((specialize (WideSigned.Rows.site r (site1 probeRows)).code a).instantiate read) mPerm s := by
  subst hsA1
  exact (site1_twoPass_run read r a s mA mB hmA hmB hroot hclean).2

theorem add_reassoc4 (a b c d : Nat) : a + (b + (c + d)) = a + b + c + d := by omega

theorem hcodeTP_cons3 {n} (a b c : WEXFast.HBlock n) (r : WEXFast.HCode n) :
    WEXFast.hcodeTP (a :: b :: c :: r) =
      WEXFast.hblockTP a + WEXFast.hblockTP b + WEXFast.hblockTP c + WEXFast.hcodeTP r := by
  rw [hcodeTP_cons, hcodeTP_cons, hcodeTP_cons, add_reassoc4]

theorem fcodeTP_cons3 {n} (a b c : WideBank8.Fast16.FBlock2 n) (r : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.fcodeTP (a :: b :: c :: r) =
      WideBank8.Fast16.fblockTP a + WideBank8.Fast16.fblockTP b + WideBank8.Fast16.fblockTP c +
        WideBank8.Fast16.fcodeTP r := by
  rw [fcodeTP_cons, fcodeTP_cons, fcodeTP_cons, add_reassoc4]

theorem blockRecP2_unit_15 {n} (B : PathShare.Bank) (u : UnitSite n) :
    PathShare.blockRecP2 B (.unit u) =
      codeRecords B.bits B.paths windowRoot (normalizeW u.pre) + u.clear.ports.length +
        (MeasuredClear.recordMeasurements
          (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) u.clear.guard B.hp) + 127) := rfl

theorem blockTP2_unit_15 {n} (B : PathShare.Bank) (u : UnitSite n) :
    PathShare.blockTP2 B (.unit u) =
      literalToffolis (normalizeW u.pre) + traversals u.pre * (2 ^ B.bits.length - 1) +
        ((tableAddressTree B.high 0 1).internalNodes + 120) := rfl

theorem blockRecP2_unit_16 {n} (B : PathShare.Bank) (u : UnitSite n) :
    WideBank8.blockRecP2 B (.unit u) =
      codeRecords B.bits B.paths windowRoot (normalizeW u.pre) + u.clear.ports.length +
        (MeasuredClear.recordMeasurements
          (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) u.clear.guard B.hp) + 255) := rfl

theorem blockTP2_unit_16 {n} (B : PathShare.Bank) (u : UnitSite n) :
    WideBank8.blockTP2 B (.unit u) =
      literalToffolis (normalizeW u.pre) + traversals u.pre * (2 ^ B.bits.length - 1) +
        ((tableAddressTree B.high 0 1).internalNodes + 247) := rfl

/-! ### Part A: Narrow (15-bit) two-pass `site1` and spliced row `Narrow15` -/

namespace Narrow15

def fA : SS2 32768 where
  bits := WEX.windowBits
  paths := PathShare.pathBank
  selBits := WEXFast.selBits
  selPaths := WEXFast.selPaths
  guard := windowRoot
  ports := shortPorts probeRows
  g1 := gA1
  g2 := gA2
  g3 := gA3

def fB : SS1 32768 where
  bits := WEX.windowBits
  paths := PathShare.pathBank
  selBits := WEXFast.selBits1
  selPaths := WEXFast.selPaths1
  guard := windowRoot
  ports := pairExtraPorts probeRows
  g1 := gB

theorem fA_geo : fA.Geo where
  bitsEq := by decide
  pathsSub := by intro w hw; simp only [fA, WEXFast.selPaths, PathShare.pathBank, List.mem_range'_1] at hw ⊢; omega
  selLen := by decide
  selNodup := by decide
  selDisj := by
    apply List.disjoint_left.mpr
    intro w hw hm
    rw [fA, shortPorts_targets] at hm
    have hb := mem_short_garbA hm
    simp only [fA, windowRoot, WEXFast.selBits, WEXFast.selPaths, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change gA1.length = (shortPorts probeRows).length; rw [gA1_len, shortPorts_length]
  len2 := by change gA2.length = (shortPorts probeRows).length; rw [gA2_len, shortPorts_length]
  len3 := by change gA3.length = (shortPorts probeRows).length; rw [gA3_len, shortPorts_length]
  nodup := by rw [fA, shortPorts_targets]; exact short_garbA_nodup
  n855 := fun hm => by rw [fA, shortPorts_targets] at hm; have := mem_short_garbA hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  n856 := fun hm => by rw [fA, shortPorts_targets] at hm; have := mem_short_garbA hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem fB_geo : fB.Geo where
  bitsEq := by decide
  pathsSub := by intro w hw; simp only [fB, WEXFast.selPaths1, PathShare.pathBank, List.mem_range'_1] at hw ⊢; omega
  selLen := by decide
  selNodup := by decide
  selDisj := by
    apply List.disjoint_left.mpr
    intro w hw hm
    rw [fB, pairExtraPorts_targets] at hm
    have hb := mem_pairExtra_gB hm
    simp only [fB, windowRoot, WEXFast.selBits1, WEXFast.selPaths1, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change gB.length = (pairExtraPorts probeRows).length; rw [gB_len, pairExtraPorts_length]
  nodup := by rw [fB, pairExtraPorts_targets]; exact pairExtra_gB_nodup
  n855 := fun hm => by rw [fB, pairExtraPorts_targets] at hm; have := mem_pairExtra_gB hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

def hot7 (i : Fin 128) : Wire := 14374 + i.val
def scratch7 : Wire := 14373
def tree7 : UnaryActionTree := tableAddressTree PathShare.bank15.high 0 1

def d1 : List (MeasuredClear.ClearPort 32768) := clearData fA.garbPorts
def d2 : List (MeasuredClear.ClearPort 32768) := clearData (shortPorts probeRows)
def d3 : List (MeasuredClear.ClearPort 32768) := clearData fB.garbPorts
def d4 : List (MeasuredClear.ClearPort 32768) := clearData (pairExtraPorts probeRows)
def allData : List (MeasuredClear.ClearPort 32768) := d1 ++ d2 ++ d3 ++ d4

theorem d1_targets : d1.map MeasuredClear.ClearPort.target = garbA := by
  rw [d1, clearData_targets]; exact fA.garbPorts_targets fA_geo
theorem d2_targets : d2.map MeasuredClear.ClearPort.target = shortWires := by
  rw [d2, clearData_targets]; exact shortPorts_targets probeRows
theorem d3_targets : d3.map MeasuredClear.ClearPort.target = gB := by
  rw [d3, clearData_targets]; exact fB.garbPorts_targets fB_geo
theorem d4_targets : d4.map MeasuredClear.ClearPort.target = pairExtraWires := by
  rw [d4, clearData_targets]; exact pairExtraPorts_targets probeRows

theorem d1_len : d1.length = 774 := by
  have := congrArg List.length d1_targets; simpa [garbA_len] using this
theorem d2_len : d2.length = 258 := by
  have := congrArg List.length d2_targets; simpa [shortWires_length] using this
theorem d3_len : d3.length = 513 := by
  have := congrArg List.length d3_targets; simpa [gB_len] using this
theorem d4_len : d4.length = 513 := by
  have := congrArg List.length d4_targets; simpa [pairExtraWires_length] using this
theorem allData_len : allData.length = 2058 := by
  simp only [allData, List.length_append, d1_len, d2_len, d3_len, d4_len]

def fixRec7 : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree7 windowRoot PathShare.bank15.hp) + 127

theorem tree7_layout : tree7.Layout windowRoot PathShare.bank15.hp :=
  tableAddressTree_layout _ _ _ 0 1 (by decide) (by decide)

theorem tree7_nodes : tree7.internalNodes = 255 := WEXUnlookup.high_nodes

theorem tree7_leaves : tree7.leaves = 256 := by
  have h := MeasuredClear.addressTree_leaves PathShare.bank15.high 0 1
  simpa [tree7, PathShare.bank15] using h

theorem fixRec7_eq : fixRec7 = 382 := by
  rw [fixRec7, (MeasuredClear.recordUnary_counts tree7 windowRoot PathShare.bank15.hp tree7_layout 0).1,
    tree7_nodes]

theorem fA_rec : codeRecords fA.selBits fA.selPaths windowRoot fA.selCode = 8191 := by
  rw [fA.loadProg_records fA_geo]; decide

theorem fB_rec : codeRecords fB.selBits fB.selPaths windowRoot fB.selCode = 16383 := by
  rw [fB.loadProg_records fB_geo]; decide

def step8 (start : Nat) (refs123 : List (Fin start)) : Straight 32768 start (start + (513 + fixRec7)) :=
  castFinish (by rw [pairExtraWires_length]; exact Nat.add_assoc start 513 fixRec7)
    (MeasuredClear.measureThen (R := fixRec7)
      (fun cursor rs => castFinish (by rw [fixRec7]; exact Nat.add_assoc cursor _ 127)
        (MeasuredClear.fixupProgram allData rs WEXUnlookup.low hot7 tree7 windowRoot scratch7 PathShare.bank15.hp))
      pairExtraWires start refs123)

def step78 (start : Nat) (refs123 : List (Fin start)) : Straight 32768 start (start + (mTail + (513 + fixRec7))) :=
  castFinish (Nat.add_assoc start mTail (513 + fixRec7))
    ((literalFixed tailNorm mTail ((literal_meas (n := 32768) _).trans tailNorm_meas) start).append
      (step8 (start + mTail) (refs123.map (Fin.castLE (Nat.le_add_right _ _)))))

def step678 (start : Nat) (refs12 : List (Fin start)) :
    Straight 32768 start (start + (513 + (mTail + (513 + fixRec7)))) :=
  castFinish (by rw [gB_len]; exact Nat.add_assoc start 513 _)
    (MeasuredClear.measureThen (R := mTail + (513 + fixRec7))
      (fun cursor rs => step78 cursor rs) gB start refs12)

def step5678 (start : Nat) (refs12 : List (Fin start)) :
    Straight 32768 start (start + (16383 + (513 + (mTail + (513 + fixRec7))))) :=
  castFinish (by rw [fB_rec]; exact Nat.add_assoc start 16383 _)
    ((fB.loadProg start).append
      (step678 (start + codeRecords fB.selBits fB.selPaths windowRoot fB.selCode)
        (refs12.map (Fin.castLE (Nat.le_add_right _ _)))))

def step4_8 (start : Nat) (refs1 : List (Fin start)) :
    Straight 32768 start (start + (258 + (16383 + (513 + (mTail + (513 + fixRec7)))))) :=
  castFinish (by rw [shortWires_length]; exact Nat.add_assoc start 258 _)
    (MeasuredClear.measureThen (R := 16383 + (513 + (mTail + (513 + fixRec7))))
      (fun cursor rs => step5678 cursor rs) shortWires start refs1)

def step3_8 (start : Nat) (refs1 : List (Fin start)) :
    Straight 32768 start (start + (mShort + (258 + (16383 + (513 + (mTail + (513 + fixRec7))))))) :=
  castFinish (Nat.add_assoc start mShort _)
    ((literalFixed shortNorm mShort ((literal_meas (n := 32768) _).trans shortNorm_meas) start).append
      (step4_8 (start + mShort) (refs1.map (Fin.castLE (Nat.le_add_right _ _)))))

def step2_8 (start : Nat) :
    Straight 32768 start (start + (774 + (mShort + (258 + (16383 + (513 + (mTail + (513 + fixRec7)))))))) :=
  castFinish (by rw [garbA_len]; exact Nat.add_assoc start 774 _)
    (MeasuredClear.measureThen (R := mShort + (258 + (16383 + (513 + (mTail + (513 + fixRec7))))))
      (fun cursor rs => step3_8 cursor rs) garbA start List.nil)

def site1Rec : Nat := site1RecGen 8191 16383 mShort mTail fixRec7

def twoPassProg (start : Nat) : Straight 32768 start (start + site1Rec) :=
  castFinish (twoPass_fin_gen start _ 8191 16383 mShort mTail fixRec7 fA_rec)
    ((fA.loadProg start).append
      (step2_8 (start + codeRecords fA.selBits fA.selPaths windowRoot fA.selCode)))

attribute [local irreducible] step8 step78 step678 step5678 step4_8 step3_8 step2_8 twoPassProg

def step8Src (read : ConstantBit 32768 → Bool) (o123 : List Bool) : AdaptiveCircuit :=
  measureResetThen pairExtraWires (fun o4 =>
    MeasuredClear.fixupSource allData (o123 ++ o4) read WEXUnlookup.low hot7 tree7 windowRoot scratch7 PathShare.bank15.hp)

def step78Src (read : ConstantBit 32768 → Bool) (o123 : List Bool) : AdaptiveCircuit :=
  (literalSource tailNorm).seq (step8Src read o123)

def step678Src (read : ConstantBit 32768 → Bool) (o12 : List Bool) : AdaptiveCircuit :=
  measureResetThen gB (fun o3 => step78Src read (o12 ++ o3))

def step5678Src (read : ConstantBit 32768 → Bool) (o12 : List Bool) : AdaptiveCircuit :=
  (fB.loadSource read).seq (step678Src read o12)

def step4_8Src (read : ConstantBit 32768 → Bool) (o1 : List Bool) : AdaptiveCircuit :=
  measureResetThen shortWires (fun o2 => step5678Src read (o1 ++ o2))

def step3_8Src (read : ConstantBit 32768 → Bool) (o1 : List Bool) : AdaptiveCircuit :=
  (literalSource shortNorm).seq (step4_8Src read o1)

def step2_8Src (read : ConstantBit 32768 → Bool) : AdaptiveCircuit :=
  measureResetThen garbA (fun o1 => step3_8Src read o1)

def twoPassSrc (read : ConstantBit 32768 → Bool) : AdaptiveCircuit :=
  (fA.loadSource read).seq (step2_8Src read)

theorem step8_run (read : ConstantBit 32768 → Bool) (start : Nat) (refs123 : List (Fin start))
    (h : Fin start → Bool) :
    ((step8 start refs123).instantiate read h).run = (step8Src read (refs123.map h)).run := by
  rw [step8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => MeasuredClear.fixupSource allData o read WEXUnlookup.low hot7 tree7 windowRoot scratch7 PathShare.bank15.hp) read
      (fun cursor rs hh => by rw [castFinish_instantiate, MeasuredClear.fixupProgram_run])]
  rfl

theorem step78_run (read : ConstantBit 32768 → Bool) (start : Nat) (refs123 : List (Fin start))
    (h : Fin start → Bool) :
    ((step78 start refs123).instantiate read h).run = (step78Src read (refs123.map h)).run := by
  rw [step78, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step8Src read (refs123.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step8_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step678_run (read : ConstantBit 32768 → Bool) (start : Nat) (refs12 : List (Fin start))
    (h : Fin start → Bool) :
    ((step678 start refs12).instantiate read h).run = (step678Src read (refs12.map h)).run := by
  rw [step678, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step78Src read o) read
      (fun cursor rs hh => step78_run read cursor rs hh)]
  rfl

theorem step5678_run (read : ConstantBit 32768 → Bool) (start : Nat) (refs12 : List (Fin start))
    (h : Fin start → Bool) :
    ((step5678 start refs12).instantiate read h).run = (step5678Src read (refs12.map h)).run := by
  rw [step5678, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step678Src read (refs12.map h)),
    AdaptiveCircuit.run_seq, fB.loadProg_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step678_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step4_8_run (read : ConstantBit 32768 → Bool) (start : Nat) (refs1 : List (Fin start))
    (h : Fin start → Bool) :
    ((step4_8 start refs1).instantiate read h).run = (step4_8Src read (refs1.map h)).run := by
  rw [step4_8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step5678Src read o) read
      (fun cursor rs hh => step5678_run read cursor rs hh)]
  rfl

theorem step3_8_run (read : ConstantBit 32768 → Bool) (start : Nat) (refs1 : List (Fin start))
    (h : Fin start → Bool) :
    ((step3_8 start refs1).instantiate read h).run = (step3_8Src read (refs1.map h)).run := by
  rw [step3_8, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step4_8Src read (refs1.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step4_8_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step2_8_run (read : ConstantBit 32768 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((step2_8 start).instantiate read h).run = (step2_8Src read).run := by
  rw [step2_8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step3_8Src read o) read
      (fun cursor rs hh => step3_8_run read cursor rs hh)]
  simp only [List.map_nil, List.nil_append]; rfl

theorem twoPass_run (read : ConstantBit 32768 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((twoPassProg start).instantiate read h).run = (twoPassSrc read).run := by
  rw [twoPassProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun hh => step2_8_run read _ hh),
    AdaptiveCircuit.run_seq, fA.loadProg_run, ← AdaptiveCircuit.run_seq]
  rfl

theorem hot7_inj : Function.Injective hot7 := fun i j he => by
  apply Fin.ext; simp only [hot7] at he; dsimp only [Wire] at he; omega

theorem low7_ne_hot7 (i : Fin 7) (j : Fin 128) : WEXUnlookup.low i ≠ hot7 j := by
  have hi := i.isLt; simp only [WEXUnlookup.low, hot7]; dsimp only [Wire]; omega

theorem hot7_disj : (MeasuredClear.hotBank hot7).Disjoint
    (windowRoot :: tree7.indexWires.dedup ++ PathShare.bank15.hp) := by
  have hh : PathShare.bank15.high = List.range' 862 8 := by decide
  have hp : PathShare.bank15.hp = List.range' 14832 8 := by decide
  apply List.disjoint_left.mpr
  intro w hw hm
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  have hi := i.isLt
  rw [tree7, PathShare.bank15_ok.index, hh, hp] at hm
  simp only [hot7, windowRoot, List.mem_cons, List.mem_append, List.mem_range'_1] at hm
  dsimp only [Wire] at *; omega

theorem scratch7_not_tree : scratch7 ∉ windowRoot :: tree7.indexWires.dedup ++ PathShare.bank15.hp := by
  have hh : PathShare.bank15.high = List.range' 862 8 := by decide
  have hp : PathShare.bank15.hp = List.range' 14832 8 := by decide
  rw [tree7, PathShare.bank15_ok.index, hh, hp]
  simp only [scratch7, windowRoot, List.mem_cons, List.mem_append, List.mem_range'_1]
  dsimp only [Wire]; omega

theorem scratch7_not_hot : scratch7 ∉ MeasuredClear.hotBank hot7 := by
  intro hm; obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp only [scratch7, hot7] at hi; dsimp only [Wire] at hi; omega

theorem hot7_in_pairExtra (i : Fin 128) : hot7 i ∈ pairExtraWires := by
  apply List.mem_append_left
  rw [scrPairWires_explicit]
  have hi := i.isLt
  simp only [hot7, List.mem_append, List.mem_cons, List.mem_range'_1, List.mem_singleton]
  dsimp only [Wire, ECDSAAdd.Wire]; omega

theorem twoPass_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((twoPassProg start).instantiate read h).tCount =
      7 * (8191 + 774 + ECDSAAdd.toffoliCount shortNorm + 16383 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 120)) := by
  have h8 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step8 c rs).instantiate read hh).tCount = 7 * (255 + 120) := by
    rw [step8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => by
      rw [castFinish_instantiate, MeasuredClear.fixupProgram_tCount _ _ _ _ _ _ _ _ tree7_layout, tree7_nodes])]
  have h78 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step78 c rs).instantiate read hh).tCount = 7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 120) := by
    rw [step78, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h8 _ _ h'), literalFixed_tCount]
  have h678 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step678 c rs).instantiate read hh).tCount = 7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 120) := by
    rw [step678, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h78 cur rs' h')]
  have h5678 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step5678 c rs).instantiate read hh).tCount =
        7 * (16383 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 120)) := by
    rw [step5678, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h678 _ _ h'),
      fB.loadProg_tCount read fB_geo]
    have hbl : fB.selBits.length = 14 := by decide
    have hpl : fB.ports.length = 513 := pairExtraPorts_length probeRows
    rw [hbl, hpl, show 2 ^ 14 - 1 = 16383 from rfl]
  have h48 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step4_8 c rs).instantiate read hh).tCount =
        7 * (16383 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 120)) := by
    rw [step4_8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h5678 cur rs' h')]
  have h38 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step3_8 c rs).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount shortNorm +
          (7 * (16383 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 120))) := by
    rw [step3_8, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h48 _ _ h'), literalFixed_tCount]
  have h28 (c : Nat) (hh : Fin c → Bool) :
      ((step2_8 c).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount shortNorm +
          (7 * (16383 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 120))) := by
    rw [step2_8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h38 cur rs' h')]
  rw [twoPassProg, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h28 _ h'),
    fA.loadProg_tCount read fA_geo]
  have hbl : fA.selBits.length = 13 := by decide
  have hpl : fA.ports.length = 258 := shortPorts_length probeRows
  rw [hbl, hpl, show 2 ^ 13 - 1 = 8191 from rfl, show 3 * 258 = 774 from rfl]
  exact twoPass_tcount_arith 8191 774 (ECDSAAdd.toffoliCount shortNorm) 16383 513 (ECDSAAdd.toffoliCount tailNorm) (255 + 120)

theorem twoPass_residue (start : Nat) : AndGadget.residue (twoPassProg start) = 0 := by
  have h8 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step8 c rs) = 0 := by
    rw [step8, AndGadget.residue_cast]
    exact MeasuredClear.measureThen_residue _ (fun _ _ => by rw [AndGadget.residue_cast]; exact MeasuredClear.fixupProgram_residue _ _ _ _ _ _ _ _) _ _ _
  have h78 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step78 c rs) = 0 := by
    rw [step78, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast,
      WEXCredit.literal_residue, h8]
  have h678 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step678 c rs) = 0 := by
    rw [step678, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h78 _ _ _
  have h5678 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step5678 c rs) = 0 := by
    rw [step5678, AndGadget.residue_cast, AndGadget.residue_append, fB.loadProg_residue, h678]
  have h48 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step4_8 c rs) = 0 := by
    rw [step4_8, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h5678 _ _ _
  have h38 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step3_8 c rs) = 0 := by
    rw [step3_8, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast,
      WEXCredit.literal_residue, h48]
  have h28 (c : Nat) : AndGadget.residue (step2_8 c) = 0 := by
    rw [step2_8, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h38 _ _ _
  rw [twoPassProg, AndGadget.residue_cast, AndGadget.residue_append, fA.loadProg_residue, h28]

theorem twoPass_wellFormed (start : Nat) : (twoPassProg start).WellFormed := by
  have h8 (c : Nat) (rs : List (Fin c)) : (step8 c rs).WellFormed := by
    rw [step8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := fixRec7) _ (fun _ _ => by
      rw [castFinish_wellFormed]
      exact MeasuredClear.fixupProgram_wellFormed _ _ _ _ _ _ _ _ tree7_layout hot7_inj low7_ne_hot7
        scratch7_not_tree scratch7_not_hot) _ _ _
  have h78 (c : Nat) (rs : List (Fin c)) : (step78 c rs).WellFormed := by
    rw [step78, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ tailNorm_valid _) (h8 _ _)
  have h678 (c : Nat) (rs : List (Fin c)) : (step678 c rs).WellFormed := by
    rw [step678, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mTail + (513 + fixRec7)) (fun cur rs' => step78 cur rs') h78 gB c rs
  have h5678 (c : Nat) (rs : List (Fin c)) : (step5678 c rs).WellFormed := by
    rw [step5678, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (fB.loadProg_wellFormed fB_geo _) (h678 _ _)
  have h48 (c : Nat) (rs : List (Fin c)) : (step4_8 c rs).WellFormed := by
    rw [step4_8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := 16383 + (513 + (mTail + (513 + fixRec7)))) (fun cur rs' => step5678 cur rs') h5678 shortWires c rs
  have h38 (c : Nat) (rs : List (Fin c)) : (step3_8 c rs).WellFormed := by
    rw [step3_8, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ shortNorm_valid _) (h48 _ _)
  have h28 (c : Nat) : (step2_8 c).WellFormed := by
    rw [step2_8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mShort + (258 + (16383 + (513 + (mTail + (513 + fixRec7)))))) (fun cur rs' => step3_8 cur rs') h38 garbA c List.nil
  rw [twoPassProg, castFinish_wellFormed]
  exact straight_append_wellFormed _ _ (fA.loadProg_wellFormed fA_geo _) (h28 _)

theorem twoPass_support (start : Nat) :
    ChallengeMigration.straightWires (twoPassProg start) ⊆ PoolHost.newSourceH7 := by
  have hmem_h7 (w : Wire) (h : w = 10015 ∨ (855 ≤ w ∧ w < 870) ∨ (14832 ≤ w ∧ w < 14847) ∨ w = 14373) :
      w ∈ PoolHost.newSourceH7 := by
    rw [PoolHost.newSourceH7_mem]
    unfold fixedPort oldWork PoolHost.retiredH7 retiredH retired
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hroot : windowRoot ∈ PoolHost.newSourceH7 := hmem_h7 windowRoot (Or.inl rfl)
  have h855 : (855 : Wire) ∈ PoolHost.newSourceH7 := hmem_h7 855 (by dsimp only [Wire]; omega)
  have h856 : (856 : Wire) ∈ PoolHost.newSourceH7 := hmem_h7 856 (by dsimp only [Wire]; omega)
  have hsA : fA.selBits ⊆ PoolHost.newSourceH7 := fun w hw => by
    simp only [fA, WEXFast.selBits, List.mem_range'_1] at hw; exact hmem_h7 w (by dsimp only [Wire] at *; omega)
  have hpA : fA.selPaths ⊆ PoolHost.newSourceH7 := fun w hw => by
    simp only [fA, WEXFast.selPaths, List.mem_range'_1] at hw; exact hmem_h7 w (by dsimp only [Wire] at *; omega)
  have hsB : fB.selBits ⊆ PoolHost.newSourceH7 := fun w hw => by
    simp only [fB, WEXFast.selBits1, List.mem_range'_1] at hw; exact hmem_h7 w (by dsimp only [Wire] at *; omega)
  have hpB : fB.selPaths ⊆ PoolHost.newSourceH7 := fun w hw => by
    simp only [fB, WEXFast.selPaths1, List.mem_range'_1] at hw; exact hmem_h7 w (by dsimp only [Wire] at *; omega)
  have hlow : ∀ i : Fin 7, WEXUnlookup.low i ∈ PoolHost.newSourceH7 := fun i =>
    hmem_h7 _ (by have hi := i.isLt; simp only [WEXUnlookup.low]; dsimp only [Wire]; omega)
  have hhot : ∀ i : Fin 128, hot7 i ∈ PoolHost.newSourceH7 := fun i =>
    pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_left _ (hot7_in_pairExtra i)))
  have hscr : scratch7 ∈ PoolHost.newSourceH7 := hmem_h7 14373 (Or.inr (Or.inr (Or.inr rfl)))
  have htree : tree7.indexWires ⊆ PoolHost.newSourceH7 := by
    intro w hw; rw [tree7] at hw
    have h1 : w ∈ PathShare.bank15.high := by
      have := List.mem_dedup.mpr hw; rw [PathShare.bank15_ok.index] at this; exact this
    have hh : PathShare.bank15.high = List.range' 862 8 := by decide
    rw [hh, List.mem_range'_1] at h1
    exact hmem_h7 w (by dsimp only [Wire] at *; omega)
  have hhp : PathShare.bank15.hp ⊆ PoolHost.newSourceH7 := fun w hw => by
    have hp : PathShare.bank15.hp = List.range' 14832 8 := by decide
    rw [hp, List.mem_range'_1] at hw; exact hmem_h7 w (by dsimp only [Wire] at *; omega)
  have hregA : portTargets fA.ports ++ fA.garb ⊆ PoolHost.newSourceH7 := fun w hw => by
    rw [fA, shortPorts_targets] at hw; exact pool_band_in_newH7 (mem_short_garbA hw)
  have hregB : portTargets fB.ports ++ fB.g1 ⊆ PoolHost.newSourceH7 := fun w hw => by
    rw [fB, pairExtraPorts_targets] at hw; exact pool_band_in_newH7 (mem_pairExtra_gB hw)
  have hgarbA : garbA ⊆ PoolHost.newSourceH7 := fun w hw =>
    pool_band_in_newH7 (mem_short_garbA (List.mem_append_right _ hw))
  have hshortW : shortWires ⊆ PoolHost.newSourceH7 := fun w hw =>
    pool_band_in_newH7 (mem_short_garbA (List.mem_append_left _ hw))
  have hgB : gB ⊆ PoolHost.newSourceH7 := fun w hw =>
    pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_right _ hw))
  have hpairW : pairExtraWires ⊆ PoolHost.newSourceH7 := fun w hw =>
    pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_left _ hw))
  have h8 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step8 c rs) ⊆ PoolHost.newSourceH7 := by
    rw [step8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun _ _ => by
      rw [MeasuredClear.static_cast]
      exact MeasuredClear.fixupProgram_within _ _ _ _ _ _ _ _ _ hroot hscr hlow hhot htree hhp) _ _ _ hpairW
  have h78 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step78 c rs) ⊆ PoolHost.newSourceH7 := by
    rw [step78, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ tailPart_wires_newH7 _, h8 _ _⟩
  have h678 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step678 c rs) ⊆ PoolHost.newSourceH7 := by
    rw [step678, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h78 cur rs') _ _ _ hgB
  have h5678 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step5678 c rs) ⊆ PoolHost.newSourceH7 := by
    rw [step5678, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨fB.loadProg_support fB_geo _ hroot hroot h855 hsB hpB hregB _, h678 _ _⟩
  have h48 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step4_8 c rs) ⊆ PoolHost.newSourceH7 := by
    rw [step4_8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h5678 cur rs') _ _ _ hshortW
  have h38 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step3_8 c rs) ⊆ PoolHost.newSourceH7 := by
    rw [step3_8, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ shortPart_wires_newH7 _, h48 _ _⟩
  have h28 (c : Nat) :
      ChallengeMigration.straightWires (step2_8 c) ⊆ PoolHost.newSourceH7 := by
    rw [step2_8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h38 cur rs') _ _ _ hgarbA
  rw [twoPassProg, support_cast, straightWires_append]
  exact List.append_subset.mpr ⟨fA.loadProg_support fA_geo _ hroot hroot h855 h856 hsA hpA hregA _, h28 _⟩

theorem twoPass_slots (start : Nat) :
    (twoPassProg start).gateSlots ≤
      4 * ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) + 310000000 := by
  have h8 (c : Nat) (rs : List (Fin c)) :
      (step8 c rs).gateSlots ≤ 512 * allData.length * 256 + 10 * 255 + 1140 := by
    rw [step8, castFinish_gateSlots, MeasuredClear.measureThen_slots _
      (fun k => 512 * min allData.length k * 256 + 10 * 255 + 1140)
      (fun cur rs' => by
        rw [castFinish_gateSlots, MeasuredClear.fixupProgram_slots _ _ _ _ _ _ _ _ tree7_layout,
          tree7_leaves, tree7_nodes])]
    have hmin : min allData.length (rs.length + pairExtraWires.length) ≤ allData.length := Nat.min_le_left _ _
    omega
  have h78 (c : Nat) (rs : List (Fin c)) :
      (step78 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots tailNorm + (512 * allData.length * 256 + 10 * 255 + 1140) := by
    rw [step78, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 32768) tailNorm
    have h8' := h8 (c + mTail) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at hl ⊢
    omega
  have h678 (c : Nat) (rs : List (Fin c)) :
      (step678 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots tailNorm + (512 * allData.length * 256 + 10 * 255 + 1140) := by
    rw [step678, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step78 cur rs') _ h78 gB c rs
  have h5678 (c : Nat) (rs : List (Fin c)) :
      (step5678 c rs).gateSlots ≤ (2 ^ 14 * (2 * 513) + 10 * (2 ^ 14 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (512 * allData.length * 256 + 10 * 255 + 1140)) := by
    rw [step5678, castFinish_gateSlots, Straight.gateSlots_append]
    have hb := fB.loadProg_slots fB_geo c
    have hbl : fB.selBits.length = 14 := by decide
    have hpl : fB.ports.length = 513 := pairExtraPorts_length probeRows
    rw [hbl, hpl] at hb
    have h6 := h678 (c + codeRecords fB.selBits fB.selPaths windowRoot fB.selCode) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at h6 ⊢
    omega
  have h48 (c : Nat) (rs : List (Fin c)) :
      (step4_8 c rs).gateSlots ≤ (2 ^ 14 * (2 * 513) + 10 * (2 ^ 14 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (512 * allData.length * 256 + 10 * 255 + 1140)) := by
    rw [step4_8, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step5678 cur rs') _ h5678 shortWires c rs
  have h38 (c : Nat) (rs : List (Fin c)) :
      (step3_8 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots shortNorm +
        ((2 ^ 14 * (2 * 513) + 10 * (2 ^ 14 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (512 * allData.length * 256 + 10 * 255 + 1140))) := by
    rw [step3_8, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 32768) shortNorm
    have h4 := h48 (c + mShort) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots shortNorm = gS at hl ⊢
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at h4 ⊢
    omega
  have h28 (c : Nat) :
      (step2_8 c).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots shortNorm +
        ((2 ^ 14 * (2 * 513) + 10 * (2 ^ 14 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (512 * allData.length * 256 + 10 * 255 + 1140))) := by
    rw [step2_8, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step3_8 cur rs') _ h38 garbA c List.nil
  rw [twoPassProg, castFinish_gateSlots, Straight.gateSlots_append]
  have ha := fA.loadProg_slots fA_geo start
  have hbl : fA.selBits.length = 13 := by decide
  have hpl : fA.ports.length = 258 := shortPorts_length probeRows
  rw [hbl, hpl] at ha
  have h2 := h28 (start + codeRecords fA.selBits fA.selPaths windowRoot fA.selCode)
  have hns := norm_slots_split
  rw [allData_len] at h2
  generalize ECDSAAdd.Challenge.gateSlots shortNorm = gsS at h2 hns
  generalize ECDSAAdd.Challenge.gateSlots tailNorm = gsT at h2 hns
  generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) = gsA at hns ⊢
  omega

/-- Simulation of the 9-step narrow two-pass `site1` circuit. -/
theorem twoPass_sim (read : ConstantBit 32768 → Bool) :
    ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
        ∀ a (st : ECDSAAdd.State), AddrValid WEX.windowBits windowRoot a st →
          Clean PathShare.pathBank st.basis →
          Clean streamLayout.dialogPool st.basis →
          (∀ m', Clean scrAllWires
            (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m' st).basis) →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m st))
      (twoPassSrc read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hsplit : ∀ s : BasisState, 128 * tree7.routeLabel s + MeasuredClear.hotAddress WEXUnlookup.low s =
      tableAddressValue WEX.windowBits s := PathShare.bank15_ok.split
  have hbits_no_pe : ∀ w ∈ WEX.windowBits, w ∉ pairExtraWires := fun w hw hm => by
    have hb := mem_pairExtra hm
    simp only [WEX.windowBits, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hhp_no_pe : ∀ w ∈ PathShare.bank15.hp, w ∉ pairExtraWires := fun w hw hm => by
    have hb := mem_pairExtra hm
    have hp : PathShare.bank15.hp = List.range' 14832 8 := by decide
    rw [hp, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hroot_no_pe : windowRoot ∉ pairExtraWires := windowRoot_not_pairExtra
  have h8_sim (o1 o2 o3 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) (ho3 : o3.length = 513) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∀ a (next : ECDSAAdd.State) (u1 u2 u3 : BasisState),
          tableAddressValue WEX.windowBits next.basis = a →
          next.basis windowRoot = true →
          Clean PathShare.bank15.hp next.basis →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, next.basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet next) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
              Bridge.signedKet ⟨next.phase, clearRegister pairExtraWires next.basis⟩)
        (step8Src read (o1 ++ o2 ++ o3)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step8Src
    apply MeasuredClear.measureResetThen_sim pairExtraWires _
      (fun o4 => BranchCoherentOn (MeasuredClear.basisIdeal id
        (MeasuredClear.fixupFactor allData ((o1 ++ o2 ++ o3) ++ o4) read WEXUnlookup.low hot7 tree7 windowRoot))
        (fun s => MeasuredClear.HotClean hot7 s ∧ Clean PathShare.bank15.hp s))
    · intro o4 _
      exact MeasuredClear.fixupSource_coherent allData _ read WEXUnlookup.low hot7 tree7 windowRoot scratch7
        PathShare.bank15.hp tree7_layout hot7_inj low7_ne_hot7 hot7_disj scratch7_not_tree scratch7_not_hot
    · intro o4 ho4 b c hb a next u1 u2 u3 haddr hroot hhp hu1 hu2 hu3 hu4
      have hk := xResetRegisterKraus_ket pairExtraWires o4 next.basis ho4 pairExtra_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho4] at hk
      set t := clearRegister pairExtraWires next.basis with ht
      have hfr (w : Wire) (hw : w ∉ pairExtraWires) : t w = next.basis w :=
        MeasuredClear.clearRegister_frame _ _ _ hw
      have hhot : MeasuredClear.HotClean hot7 t := fun i => clearRegister_clean _ _ _ (hot7_in_pairExtra i)
      have hvalid : MeasuredClear.HotClean hot7 t ∧ Clean PathShare.bank15.hp t :=
        ⟨hhot, fun w hw => by rw [hfr w (hhp_no_pe w hw)]; exact hhp w hw⟩
      have haddr_t : tableAddressValue WEX.windowBits t = a :=
        (WEX.tableAddressValue_congr _ _ _ (fun w hw => hfr w (hbits_no_pe w hw))).trans haddr
      have hroot_t : t windowRoot = true := (hfr _ hroot_no_pe).trans hroot
      have hfac : MeasuredClear.fixupFactor allData ((o1 ++ o2 ++ o3) ++ o4) read WEXUnlookup.low hot7 tree7 windowRoot t =
          registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 *
            registerXPhase gB o3 u3 * registerXPhase pairExtraWires o4 next.basis := by
        have hlen12 : (o1 ++ o2).length = (d1 ++ d2).length := by simp [ho1, ho2, d1_len, d2_len]
        have hlen123 : (o1 ++ o2 ++ o3).length = (d1 ++ d2 ++ d3).length := by
          simp [ho1, ho2, ho3, d1_len, d2_len, d3_len]
        rw [allData, MeasuredClear.fixupFactor7_append _ _ _ _ hlen123,
          MeasuredClear.fixupFactor7_append _ _ _ _ hlen12,
          MeasuredClear.fixupFactor7_append _ _ _ _ (by rw [ho1, d1_len])]
        have hf1 : MeasuredClear.fixupFactor d1 o1 read WEXUnlookup.low hot7 tree7 windowRoot t =
            registerXPhase garbA o1 u1 := by
          rw [← d1_targets]
          exact MeasuredClear.fixupFactor7_loaded d1 o1 read WEXUnlookup.low hot7 tree7 windowRoot PathShare.bank15.hp
            hot7_inj low7_ne_hot7 hot7_disj t u1 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu1 q hq)
        have hf2 : MeasuredClear.fixupFactor d2 o2 read WEXUnlookup.low hot7 tree7 windowRoot t =
            registerXPhase shortWires o2 u2 := by
          rw [← d2_targets]
          exact MeasuredClear.fixupFactor7_loaded d2 o2 read WEXUnlookup.low hot7 tree7 windowRoot PathShare.bank15.hp
            hot7_inj low7_ne_hot7 hot7_disj t u2 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu2 q hq)
        have hf3 : MeasuredClear.fixupFactor d3 o3 read WEXUnlookup.low hot7 tree7 windowRoot t =
            registerXPhase gB o3 u3 := by
          rw [← d3_targets]
          exact MeasuredClear.fixupFactor7_loaded d3 o3 read WEXUnlookup.low hot7 tree7 windowRoot PathShare.bank15.hp
            hot7_inj low7_ne_hot7 hot7_disj t u3 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu3 q hq)
        have hf4 : MeasuredClear.fixupFactor d4 o4 read WEXUnlookup.low hot7 tree7 windowRoot t =
            registerXPhase pairExtraWires o4 next.basis := by
          rw [← d4_targets]
          exact MeasuredClear.fixupFactor7_loaded d4 o4 read WEXUnlookup.low hot7 tree7 windowRoot PathShare.bank15.hp
            hot7_inj low7_ne_hot7 hot7_disj t next.basis hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu4 q hq)
        rw [hf1, hf2, hf3, hf4]
      have hsq := MeasuredClear.registerXPhase_square pairExtraWires o4 next.basis
      change b.kraus (xResetRegisterKraus pairExtraWires o4 (Bridge.signedKet next)) = _
      simp only [Bridge.signedKet, map_smul, hk, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac, smul_smul, ← ht]
      exact congrArg (· • ket t) (phase_cancel_base next.phase (registerXResetMagnitude pairExtraWires.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 u2) (registerXPhase gB o3 u3)
        (registerXPhase pairExtraWires o4 next.basis) hsq)
  have hsite1_win15 : ∀ w ∈ windowRoot :: WEX.windowBits ++ PathShare.pathBank,
      w ∉ ECDSAAdd.wires site1Arith := fun w hw hm => by
    have hgeo : PathShare.UnitGeoP PathShare.bank15 ⟨(site1 probeRows).prefix, site1 probeRows⟩ :=
      WEXFast.W15G.rowH_hgeo (.blk (.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩))) (by
        unfold WEXFast.W15G.rowH
        apply List.mem_append_left
        refine List.mem_map.mpr ⟨.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩), ?_, rfl⟩
        rw [WideBank8.Row16.headF]
        apply List.mem_append_left
        rw [WEXUnlookup.rowPre3]; simp [toBlock2])
    exact hgeo.placed (WInstr.literal site1Arith)
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) w hw hm
  have htail_avoid_window : ∀ w ∈ windowRoot :: WEX.windowBits ++ PathShare.pathBank, w ∉ ECDSAAdd.wires tailPart := fun w hw hm =>
    hsite1_win15 w hw (tailPart_wires_sub hm)
  have hshort_avoid_window : ∀ w ∈ windowRoot :: WEX.windowBits ++ PathShare.pathBank, w ∉ ECDSAAdd.wires shortPart := fun w hw hm =>
    hsite1_win15 w hw (shortPart_wires_sub hm)
  -- Combine steps 7 + 8
  have h78_sim (o1 o2 o3 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) (ho3 : o3.length = 513) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sL2 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
            AddrValid WEX.windowBits windowRoot a sL2 →
            Clean PathShare.pathBank sL2.basis →
            Clean pairExtraWires (tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sL2) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step78Src read (o1 ++ o2 ++ o3)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation tailNorm
    obtain ⟨c2, a2, m2⟩ := h8_sim o1 o2 o3 ho1 ho2 ho3
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step78Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    refine ⟨b₁.history, by rw [hb₁.1, tailNorm_meas], ?_⟩
    intro a sL2 u1 u2 u3 ha hpath hclOut hu1 hu2 hu3
    set sB1 := ECDSAAdd.run tailPart b₁.history sL2 with hsB1
    have hnorm : ECDSAAdd.run tailNorm b₁.history sL2 = sB1 := by
      rw [tailNorm]; exact ECDSAAdd.Baselines.normalize_run tailPart b₁.history sL2
    have hrootB : sB1.basis windowRoot = true := by
      rw [hsB1, run_outside_basis tailPart b₁.history sL2 windowRoot tailPart_root]; exact ha.2
    have haddrB : tableAddressValue WEX.windowBits sB1.basis = a := by
      rw [← ha.1]; apply WEX.tableAddressValue_congr
      intro w hw; rw [hsB1, run_outside_basis tailPart b₁.history sL2 w (htail_avoid_window w (by simp [hw]))]
    have hhpB : Clean PathShare.bank15.hp sB1.basis := fun w hw => by
      have hw' : w ∈ PathShare.pathBank := PathShare.bank15_ok.sub w hw
      rw [hsB1, run_outside_basis tailPart b₁.history sL2 w (htail_avoid_window w (by simp [hw']))]; exact hpath w hw'
    have hpp_nd : (portTargets (pairExtraPorts probeRows)).Nodup := by rw [pairExtraPorts_targets]; exact pairExtra_nodup
    have hclOut' : Clean (portTargets (pairExtraPorts probeRows))
        (tableXorState (portMask read (pairExtraPorts probeRows) a) (sB1.basis windowRoot) sB1.basis) := by
      rw [pairExtraPorts_targets, hrootB]; exact hclOut
    have hloadedB : ∀ q ∈ d4, sB1.basis q.target = decide (read (q.ref a) = q.value) :=
      clearData_loaded_of_clean read (pairExtraPorts probeRows) a windowRoot sB1.basis hrootB hpp_nd
        (by rw [pairExtraPorts_targets]; exact hclOut)
    have hclr : clearRegister pairExtraWires sB1.basis =
        tableXorState (portMask read (pairExtraPorts probeRows) a) true sB1.basis := by
      have h0 := clear_eq_unload read (pairExtraPorts probeRows) a windowRoot sB1.basis hclOut'
      rw [pairExtraPorts_targets, hrootB] at h0; exact h0
    change b₂.kraus (b₁.kraus (Bridge.signedKet sL2)) = _
    rw [hb₁.2, hnorm, map_smul, hb₂ a sB1 u1 u2 u3 haddrB hrootB hhpB hu1 hu2 hu3 hloadedB, hclr, smul_smul]
    exact congrArg (· • _) (by simp only [mul_assoc])
  -- Combine steps 6 + (7,8)
  have h68_sim (o1 o2 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sB0 : ECDSAAdd.State) (u1 u2 : BasisState),
            let sL2 : ECDSAAdd.State := ⟨sB0.phase, clearRegister gB sB0.basis⟩
            AddrValid WEX.windowBits windowRoot a sL2 →
            Clean PathShare.pathBank sL2.basis →
            Clean pairExtraWires (tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, sB0.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sB0) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step678Src read (o1 ++ o2)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step678Src
    apply MeasuredClear.measureResetThen_sim gB _
      (fun o3 b c => ∃ mB : List Bool, mB.length = mTail ∧
        ∀ a (sL2 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
          AddrValid WEX.windowBits windowRoot a sL2 →
          Clean PathShare.pathBank sL2.basis →
          Clean pairExtraWires (tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sL2) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
              Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
    · intro o3 ho3
      exact h78_sim o1 o2 o3 ho1 ho2 (by rw [gB_len] at ho3; exact ho3)
    · intro o3 ho3 b c hb
      obtain ⟨mB, hmB, hb⟩ := hb
      refine ⟨mB, hmB, ?_⟩
      intro a sB0 u1 u2 sL2 ha hpath hclOut hu1 hu2 hu3
      have hk := xResetRegisterKraus_ket gB o3 sB0.basis ho3 gB_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho3] at hk
      have hsq := MeasuredClear.registerXPhase_square gB o3 sB0.basis
      change b.kraus (xResetRegisterKraus gB o3 (Bridge.signedKet sB0)) = _
      have hstep := hb a sL2 u1 u2 sB0.basis ha hpath hclOut hu1 hu2 hu3
      rw [show Bridge.signedKet sB0 = (if sB0.phase then (-1 : ℂ) else 1) • ket sB0.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister gB sB0.basis)) =
          (if sB0.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet sL2) := by
        simp only [Bridge.signedKet, sL2, map_smul, smul_smul]
        cases sB0.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step2 sB0.phase (registerXResetMagnitude gB.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 u2)
        (registerXPhase gB o3 sB0.basis) hsq)
  -- Combine steps 5 + (6..8)
  have h58_sim (o1 o2 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sMid : ECDSAAdd.State) (u1 u2 : BasisState),
            let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read (pairExtraPorts probeRows) a) true sMid.basis⟩
            AddrValid WEX.windowBits windowRoot a sMid →
            Clean PathShare.pathBank sMid.basis →
            Clean (pairExtraWires ++ gB) sMid.basis →
            Clean pairExtraWires (tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sMid) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step5678Src read (o1 ++ o2)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := fB.load_sim read fB_geo
    obtain ⟨c2, a2, m2⟩ := h68_sim o1 o2 ho1 ho2
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step5678Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨mB, hmB, hb₂⟩ := hb₂
    refine ⟨mB, hmB, ?_⟩
    intro a sMid u1 u2 sL2 ha hpath hclB hclOut hu1 hu2
    have hclB' : Clean (portTargets fB.ports ++ fB.g1) sMid.basis := by
      change Clean (portTargets (pairExtraPorts probeRows) ++ gB) sMid.basis
      rw [pairExtraPorts_targets]; exact hclB
    have hst := fB.load_state read fB_geo a sMid ⟨hpath, ha.1, ha.2⟩ hclB'
    set sB0 := ECDSAAdd.run fB.swapNet List.nil
      (ECDSAAdd.run ((specialize fB.selCode (tableAddressValue fB.selBits sMid.basis)).instantiate read) List.nil sMid) with hsB0
    have hsL2_eq : (⟨sB0.phase, clearRegister gB sB0.basis⟩ : ECDSAAdd.State) = sL2 := by
      refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
      have h2 := hst.2.2.2; change clearRegister gB sB0.basis = tableXorState (portMask read (pairExtraPorts probeRows) a) (sMid.basis windowRoot) sMid.basis at h2
      rw [ha.2] at h2; exact h2
    have hfrB : ∀ w, w ∉ pairExtraWires → w ∉ gB → sL2.basis w = sMid.basis w := fun w h1 h2 => by
      dsimp only [sL2]; exact tableXorState_outside _ _ _ _ (fun hm => h1 (by rw [← pairExtraPorts_targets probeRows]; exact tableBitsMask_subset _ _ hm))
    have haL2 : AddrValid WEX.windowBits windowRoot a sL2 := by
      refine ⟨?_, ?_⟩
      · rw [← ha.1]; apply WEX.tableAddressValue_congr; intro w hw
        exact hfrB w (hbits_no_pe w hw) (fun hm => by rw [mem_gB] at hm; simp only [WEX.windowBits, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      · rw [hfrB windowRoot hroot_no_pe (fun hm => by rw [mem_gB] at hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega)]; exact ha.2
    have hpathL2 : Clean PathShare.pathBank sL2.basis := fun w hw => by
      have h1 : w ∉ pairExtraWires := fun hm => by have := mem_pairExtra hm; simp only [PathShare.pathBank, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have h2 : w ∉ gB := fun hm => by rw [mem_gB] at hm; simp only [PathShare.pathBank, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      rw [hfrB w h1 h2]; exact hpath w hw
    have hu3 : ∀ q ∈ d3, sB0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
      have h1 := hst.2.2.1 q hq
      change sB0.basis q.target = (sMid.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
      rw [ha.2, Bool.true_and] at h1; exact h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet sMid)) = _
    rw [hb₁ a sMid ⟨hpath, ha.1, ha.2⟩ hclB', map_smul]
    have hstep := hb₂ a sB0 u1 u2 (by rw [hsL2_eq]; exact haL2) (by rw [hsL2_eq]; exact hpathL2)
      (by rw [hsL2_eq]; exact hclOut) hu1 hu2 hu3
    rw [hsL2_eq] at hstep
    rw [hstep, smul_smul]
    exact congrArg (· • _) (by simp only [mul_assoc])
  -- Combine steps 4 + (5..8)
  have h48_sim (o1 : List Bool) (ho1 : o1.length = 774) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sA1 : ECDSAAdd.State) (u1 : BasisState),
            let sMid : ECDSAAdd.State := ⟨sA1.phase, clearRegister shortWires sA1.basis⟩
            let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read (pairExtraPorts probeRows) a) true sMid.basis⟩
            AddrValid WEX.windowBits windowRoot a sMid →
            Clean PathShare.pathBank sMid.basis →
            Clean (pairExtraWires ++ gB) sMid.basis →
            Clean pairExtraWires (tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, sA1.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sA1) =
              (c * registerXPhase garbA o1 u1) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step4_8Src read o1).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step4_8Src
    apply MeasuredClear.measureResetThen_sim shortWires _
      (fun o2 b c => ∃ mB : List Bool, mB.length = mTail ∧
        ∀ a (sMid : ECDSAAdd.State) (u1 u2 : BasisState),
          let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read (pairExtraPorts probeRows) a) true sMid.basis⟩
          AddrValid WEX.windowBits windowRoot a sMid →
          Clean PathShare.pathBank sMid.basis →
          Clean (pairExtraWires ++ gB) sMid.basis →
          Clean pairExtraWires (tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sMid) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
              Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
    · intro o2 ho2
      exact h58_sim o1 o2 ho1 (by rw [shortWires_length] at ho2; exact ho2)
    · intro o2 ho2 b c hb
      obtain ⟨mB, hmB, hb⟩ := hb
      refine ⟨mB, hmB, ?_⟩
      intro a sA1 u1 sMid sL2 ha hpath hclB hclOut hu1 hu2
      have hk := xResetRegisterKraus_ket shortWires o2 sA1.basis ho2 scrShortWires_nd
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho2] at hk
      have hsq := MeasuredClear.registerXPhase_square shortWires o2 sA1.basis
      change b.kraus (xResetRegisterKraus shortWires o2 (Bridge.signedKet sA1)) = _
      have hstep := hb a sMid u1 sA1.basis ha hpath hclB hclOut hu1 hu2
      rw [show Bridge.signedKet sA1 = (if sA1.phase then (-1 : ℂ) else 1) • ket sA1.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister shortWires sA1.basis)) =
          (if sA1.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet sMid) := by
        simp only [Bridge.signedKet, sMid, map_smul, smul_smul]
        cases sA1.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step1 sA1.phase (registerXResetMagnitude shortWires.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 sA1.basis) hsq)
  -- Combine steps 3 + (4..8)
  have h38_sim (o1 : List Bool) (ho1 : o1.length = 774) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
          ∀ a (st : ECDSAAdd.State) (u1 : BasisState),
            let sL1 : ECDSAAdd.State := ⟨st.phase, tableXorState (portMask read (shortPorts probeRows) a) true st.basis⟩
            AddrValid WEX.windowBits windowRoot a st →
            Clean PathShare.pathBank st.basis →
            Clean streamLayout.dialogPool st.basis →
            (∀ m', Clean scrAllWires
              (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m' st).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sL1) =
              (c * registerXPhase garbA o1 u1) •
                Bridge.signedKet (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m st))
        (step3_8Src read o1).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation shortNorm
    obtain ⟨c2, a2, m2⟩ := h48_sim o1 ho1
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step3_8Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨mB, hmB, hb₂⟩ := hb₂
    let mA := b₁.history
    have hmA : mA.length = mShort := by rw [hb₁.1, shortNorm_meas]
    let mPerm := mB.take (ECDSAAdd.measurementCount pairPart) ++ mA ++ mB.drop (ECDSAAdd.measurementCount pairPart)
    have hmc_len : mPerm.length = ECDSAAdd.measurementCount site1Arith := by
      have htail_mc : ECDSAAdd.measurementCount pairPart ≤ mTail := by
        rw [mTail, tailPart, ECDSAAdd.measurementCount_append]
        exact Nat.le_add_right _ _
      have hcs : mShort + mTail = ECDSAAdd.measurementCount site1Arith := by
        rw [mShort, mTail]; exact site1_counts_split.2.1
      dsimp only [mPerm]
      rw [List.length_append, List.length_append, List.length_take, List.length_drop, hmA, hmB]
      exact mPerm_len_arith mShort mTail (ECDSAAdd.measurementCount pairPart) (ECDSAAdd.measurementCount site1Arith) htail_mc hcs
    refine ⟨mPerm, hmc_len, ?_⟩
    intro a st u1 sL1 ha hpath hpool hsafe hu1
    have hclean258 : Clean (streamLayout.dialogPool.take 258) st.basis := fun w hw => hpool w (List.mem_of_mem_take hw)
    have hclean258_L1 : Clean (streamLayout.dialogPool.take 258) sL1.basis := fun w hw => by
      dsimp only [sL1]
      rw [tableXorState_outside _ _ _ _ (fun hm => by
        have h1 : w ∈ shortWires := by simpa [shortPorts_targets] using tableBitsMask_subset _ _ hm
        have h2 := shortWires_bounds w h1
        rw [mem_pool_take 258 (by decide)] at hw; dsimp only [Wire, ECDSAAdd.Wire] at hw h2; omega)]
      exact hclean258 w hw
    have hnorm : ECDSAAdd.run shortNorm mA sL1 = ECDSAAdd.run shortPart mA sL1 := by
      rw [shortNorm]; exact ECDSAAdd.Baselines.normalize_run shortPart mA sL1
    have hsA1_form := shortPart_run sL1 mA hclean258_L1
    generalize hsA1 : ECDSAAdd.run shortPart mA sL1 = sA1 at hnorm hsA1_form
    have htwo := site1_twoPass_run_free read probeRows a st sA1 mA mB
      (by rw [← mShort]; exact hmA) (by rw [← mTail]; exact hmB) ha.2 hclean258
      (by rw [shortPorts_probeRows_id]; exact hsA1.symm)
    rw [shortPorts_probeRows_id, pairExtraPorts_probeRows_id, site1_probeRows_id] at htwo
    have hne_eq (w : Wire) (hne : w ≠ streamLayout.core.equalNegY) : sA1.basis w = sL1.basis w := by
      rw [hsA1_form]; simp [ECDSAAdd.writeBit, Function.update, hne]
    have hsp_nd : (portTargets (shortPorts probeRows)).Nodup := by rw [shortPorts_targets]; exact scrShortWires_nd
    have hsA1_loaded : ∀ q ∈ d2, sA1.basis q.target = decide (read (q.ref a) = q.value) :=
      clearData_loaded_of_xor read (shortPorts probeRows) a st.basis sA1.basis hsp_nd
        (fun w hw => by rw [shortPorts_targets] at hw; exact hpool w (pool_band_in_dialogPool (mem_short_garbA (List.mem_append_left _ hw))))
        (fun w hw => by
          rw [shortPorts_targets] at hw
          exact hne_eq w (fun e => scrShortWires_no_flags.2.2.2 (e ▸ hw)))
    have hmid_basis : clearRegister shortWires sA1.basis =
        tableXorState (portMask read (shortPorts probeRows) a) true sA1.basis := by
      rw [← shortPorts_targets probeRows]
      exact clearRegister_eq_xor_of_loaded read (shortPorts probeRows) a sA1.basis hsp_nd hsA1_loaded
    set sMid : ECDSAAdd.State := ⟨sA1.phase, clearRegister shortWires sA1.basis⟩
    set sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read (pairExtraPorts probeRows) a) true sMid.basis⟩
    have hsOut_eq : (⟨(ECDSAAdd.run tailPart mB sL2).phase,
        tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) mPerm st :=
      (twoPass_state_congr read (shortPorts probeRows) (pairExtraPorts probeRows) a sA1 mB shortWires hmid_basis).trans htwo
    have hmid_frame (w : Wire) (hw1 : w ∉ shortWires) (hw2 : w ≠ streamLayout.core.equalNegY) :
        sMid.basis w = st.basis w := by
      dsimp only [sMid]
      rw [MeasuredClear.clearRegister_frame shortWires sA1.basis w hw1, hne_eq w hw2]
      dsimp only [sL1]
      exact tableXorState_outside _ _ _ _ (fun hm => hw1 (by simpa [shortPorts_targets] using tableBitsMask_subset _ _ hm))
    have haMid : AddrValid WEX.windowBits windowRoot a sMid := by
      refine ⟨?_, ?_⟩
      · rw [← ha.1]; apply WEX.tableAddressValue_congr; intro w hw
        exact hmid_frame w
          (fun hm => by have h1 := shortWires_bounds w hm; simp only [WEX.windowBits, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at hw h1; omega)
          (fun e => by rw [e, sl_equalNegY] at hw; simp only [WEX.windowBits, List.mem_range'_1] at hw; omega)
      · rw [hmid_frame windowRoot windowRoot_not_short (by rw [sl_equalNegY]; decide)]; exact ha.2
    have hpathMid : Clean PathShare.pathBank sMid.basis := fun w hw => by
      rw [hmid_frame w
        (fun hm => by have h1 := shortWires_bounds w hm; simp only [PathShare.pathBank, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at hw h1; omega)
        (fun e => by rw [e, sl_equalNegY] at hw; simp only [PathShare.pathBank, List.mem_range'_1] at hw; omega)]
      exact hpath w hw
    have hclMid : Clean (pairExtraWires ++ gB) sMid.basis := fun w hw => by
      by_cases hs : w ∈ shortWires
      · exact clearRegister_clean shortWires sA1.basis w hs
      · rw [hmid_frame w hs (fun e => by have h1 := mem_pairExtra_gB hw; rw [e, sl_equalNegY] at h1; dsimp only [Wire, ECDSAAdd.Wire] at h1; omega)]
        exact hpool w (pool_band_in_dialogPool (mem_pairExtra_gB hw))
    have hclOut : Clean pairExtraWires (tableXorState (portMask read (pairExtraPorts probeRows) a) true (ECDSAAdd.run tailPart mB sL2).basis) := by
      intro w hw
      have h1 := hsafe mPerm w (by
        rcases List.mem_append.mp hw with h | h
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_right _ h)
      have h2 := congrArg (fun x => x.basis w) hsOut_eq
      exact h2.trans h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet sL1)) = _
    rw [hb₁.2, hnorm, map_smul, hb₂ a sA1 u1 haMid hpathMid hclMid hclOut hu1 hsA1_loaded, smul_smul, hsOut_eq]
    exact congrArg (· • _) (by simp only [mul_assoc])
  -- Combine steps 2 + (3..8)
  have h28_sim :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
          ∀ a (st sA0 : ECDSAAdd.State),
            (⟨sA0.phase, clearRegister garbA sA0.basis⟩ : ECDSAAdd.State) =
              ⟨st.phase, tableXorState (portMask read (shortPorts probeRows) a) true st.basis⟩ →
            AddrValid WEX.windowBits windowRoot a st →
            Clean PathShare.pathBank st.basis →
            Clean streamLayout.dialogPool st.basis →
            (∀ m', Clean scrAllWires
              (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m' st).basis) →
            (∀ q ∈ d1, sA0.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sA0) =
              c • Bridge.signedKet (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m st))
        (step2_8Src read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step2_8Src
    apply MeasuredClear.measureResetThen_sim garbA _
      (fun o1 b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
        ∀ a (st : ECDSAAdd.State) (u1 : BasisState),
          let sL1 : ECDSAAdd.State := ⟨st.phase, tableXorState (portMask read (shortPorts probeRows) a) true st.basis⟩
          AddrValid WEX.windowBits windowRoot a st →
          Clean PathShare.pathBank st.basis →
          Clean streamLayout.dialogPool st.basis →
          (∀ m', Clean scrAllWires
            (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m' st).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sL1) =
            (c * registerXPhase garbA o1 u1) •
              Bridge.signedKet (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m st))
    · intro o1 ho1
      exact h38_sim o1 (by rw [garbA_len] at ho1; exact ho1)
    · intro o1 ho1 b c hb
      obtain ⟨m, hm, hb⟩ := hb
      refine ⟨m, hm, ?_⟩
      intro a st sA0 hsL1 ha hpath hpool hsafe hu1
      have hk := xResetRegisterKraus_ket garbA o1 sA0.basis ho1 garbA_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho1] at hk
      have hsq := MeasuredClear.registerXPhase_square garbA o1 sA0.basis
      change b.kraus (xResetRegisterKraus garbA o1 (Bridge.signedKet sA0)) = _
      have hstep := hb a st sA0.basis ha hpath hpool hsafe hu1
      have ⟨hph, hba⟩ := (ECDSAAdd.State.mk.injEq _ _ _ _).mp hsL1
      rw [show Bridge.signedKet sA0 = (if sA0.phase then (-1 : ℂ) else 1) • ket sA0.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister garbA sA0.basis)) =
          (if sA0.phase then (-1 : ℂ) else 1) •
            b.kraus (Bridge.signedKet ⟨st.phase, tableXorState (portMask read (shortPorts probeRows) a) true st.basis⟩) := by
        rw [hba, hph]
        simp only [Bridge.signedKet, map_smul, smul_smul]
        cases st.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step0 sA0.phase (registerXResetMagnitude garbA.length) c
        (registerXPhase garbA o1 sA0.basis) hsq)
  -- Finally combine step 1 + (2..8)
  obtain ⟨c1, a1, m1⟩ := fA.load_sim read fA_geo
  obtain ⟨c2, a2, m2⟩ := h28_sim
  refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
  rw [twoPassSrc, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a1 a2
  intro b₁ k₁ b₂ k₂ hb₁ hb₂
  obtain ⟨m, hm, hb₂⟩ := hb₂
  refine ⟨m, hm, ?_⟩
  intro a st ha hpath hpool hsafe
  have hclA : Clean (portTargets fA.ports ++ fA.garb) st.basis := fun w hw => by
    rw [fA, shortPorts_targets] at hw
    exact hpool w (pool_band_in_dialogPool (mem_short_garbA hw))
  have hst := fA.load_state read fA_geo a st ⟨hpath, ha.1, ha.2⟩ hclA
  set sA0 := ECDSAAdd.run fA.swapNet List.nil
    (ECDSAAdd.run ((specialize fA.selCode (tableAddressValue fA.selBits st.basis)).instantiate read) List.nil st) with hsA0
  have hsL1 : (⟨sA0.phase, clearRegister garbA sA0.basis⟩ : ECDSAAdd.State) =
      ⟨st.phase, tableXorState (portMask read (shortPorts probeRows) a) true st.basis⟩ := by
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
    have h2 := hst.2.2.2
    change clearRegister garbA sA0.basis = tableXorState (portMask read (shortPorts probeRows) a) (st.basis windowRoot) st.basis at h2
    rw [ha.2] at h2; exact h2
  have hu1 : ∀ q ∈ d1, sA0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
    have h1 := hst.2.2.1 q hq
    change sA0.basis q.target = (st.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
    rw [ha.2, Bool.true_and] at h1; exact h1
  change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
  rw [hb₁ a st ⟨hpath, ha.1, ha.2⟩ hclA, map_smul, hb₂ a st sA0 hsL1 ha hpath hpool hsafe hu1, smul_smul]

/-! Splicing `twoPassProg` into `WEXFast.W15G.rowH = h0 :: h1 :: h2 :: restN`. -/

def h0 : WEXFast.HBlock 32768 := .blk (.std (.plain (wLiteral [.X 838])))
def h1 : WEXFast.HBlock 32768 := .blk (.std (.plain scrHead))
def h2 : WEXFast.HBlock 32768 := .blk (.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩))
def restN : WEXFast.HCode 32768 := WEXFast.W15G.rowH.drop 3

theorem rowH_split : WEXFast.W15G.rowH = h0 :: h1 :: h2 :: restN := by
  have h : WEXFast.W15G.rowH =
      h0 :: h1 :: h2 :: ((WEXFast.fgeneric3 ++ (WEXFast.FBlock2.std (.plain WEX.cornerNeg) :: List.nil)).map WEXFast.HBlock.blk ++
        WEXFast.HBlock.pair WEXFast.W15G.corner7 :: WideBank8.Row16.tailF.map WEXFast.HBlock.blk) := by
    unfold WEXFast.W15G.rowH
    rw [WideBank8.Row16.headF, WEXUnlookup.rowPre3]
    simp [h0, h1, h2, toBlock2]
  rw [restN, h]; rfl

theorem h2_rec_diff : WEXFast.hblockRec h2 = site1Rec + 6906 := by
  have hgeo := WEXFast.W15G.rowH_hgeo h2 (by rw [rowH_split]; simp)
  have hlay := PathShare.geo_lay2 PathShare.bank15 PathShare.bank15_ok (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩) hgeo
  have hpre_eq : (site1 probeRows).prefix = [WInstr.lookup (some windowRoot) (sitePorts probeRows), WInstr.literal site1Arith] := rfl
  have hpre : codeRecords PathShare.bank15.bits PathShare.bank15.paths windowRoot (normalizeW (site1 probeRows).prefix) =
      ECDSAAdd.measurementCount site1Arith + 32767 := by
    have h1 : codeRecords PathShare.bank15.bits PathShare.bank15.paths windowRoot (normalizeW (site1 probeRows).prefix) =
        literalRecords (site1 probeRows).prefix + traversals (site1 probeRows).prefix * (2 ^ PathShare.bank15.bits.length - 1) := by
      rw [codeRecords_eq _ _ _ _ hlay.1, literalRecords_normalize, traversals_normalize]
    have h2' : literalRecords (site1 probeRows).prefix = ECDSAAdd.measurementCount site1Arith := by
      rw [hpre_eq]; exact litRec_lookup_lit _ _ _
    have h3' : traversals (site1 probeRows).prefix * (2 ^ PathShare.bank15.bits.length - 1) = 32767 := by
      rw [hpre_eq, trav_lookup_lit]; decide
    exact h1.trans (congrArg₂ (· + ·) h2' h3')
  have hcr : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree PathShare.bank15.high 0 1) (site1 probeRows).guard PathShare.bank15.hp) = 255 := by
    change MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree7 windowRoot PathShare.bank15.hp) = 255
    rw [(MeasuredClear.recordUnary_counts _ _ _ tree7_layout 0).1, tree7_nodes]
  have hlen : (site1 probeRows).ports.length = 771 := by
    have h := congrArg List.length (sitePorts_targets probeRows)
    have hs : scrAllWires.length = 771 := by
      have h1 : scrPairWires.length = 258 := scrPairWires_length
      have h2 : scrShortWires.length = 258 := scrShortWires_length
      have h3 : scrDExtraWires.length = 255 := by rw [scrDExtraWires_explicit]; simp
      simp [scrAllWires, scrWires, h1, h2, h3]
    simpa [site1, portTargets, hs] using h
  have hrec_eq : WEXFast.hblockRec h2 = PathShare.blockRecP2 PathShare.bank15 (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩) :=
    hblockRec_std _
  have hlhs : WEXFast.hblockRec h2 =
      ECDSAAdd.measurementCount site1Arith + 32767 + 771 + (255 + 127) :=
    hrec_eq.trans ((blockRecP2_unit_15 PathShare.bank15 ⟨(site1 probeRows).prefix, site1 probeRows⟩).trans
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) hpre hlen) (congrArg (· + 127) hcr)))
  exact (hlhs.trans (narrow_rec_diff_arith (ECDSAAdd.measurementCount site1Arith) mShort mTail fixRec7 mShort_add_mTail fixRec7_eq)).trans
    (congrArg (· + 6906) (show site1RecGen 8191 16383 mShort mTail fixRec7 = site1Rec from rfl))

theorem h2_tp_diff :
    WEXFast.hblockTP h2 =
      (8191 + 774 + ECDSAAdd.toffoliCount shortNorm + 16383 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 120)) + 6906 := by
  have hpre_eq : (site1 probeRows).prefix = [WInstr.lookup (some windowRoot) (sitePorts probeRows), WInstr.literal site1Arith] := rfl
  have htp_pre : literalToffolis (normalizeW (site1 probeRows).prefix) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram site1Arith) := by
    rw [hpre_eq]; exact litToff_lookup_lit _ _ _
  have htr_pre : traversals (site1 probeRows).prefix = 1 := by
    rw [hpre_eq]; exact trav_lookup_lit _ _ _
  have htp_eq : WEXFast.hblockTP h2 =
      PathShare.blockTP2 PathShare.bank15 (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩) :=
    hblockTP_unit _
  have h1 : literalToffolis (normalizeW (site1 probeRows).prefix) =
      ECDSAAdd.toffoliCount shortNorm + ECDSAAdd.toffoliCount tailNorm :=
    htp_pre.trans norm_toff_split.symm
  have h2' : traversals (site1 probeRows).prefix * (2 ^ PathShare.bank15.bits.length - 1) = 1 * (2 ^ 15 - 1) := by
    rw [htr_pre]; rfl
  have h3 : (tableAddressTree PathShare.bank15.high 0 1).internalNodes + 120 = 255 + 120 :=
    congrArg (· + 120) tree7_nodes
  have hlhs : WEXFast.hblockTP h2 =
      ECDSAAdd.toffoliCount shortNorm + ECDSAAdd.toffoliCount tailNorm + 1 * (2 ^ 15 - 1) + (255 + 120) :=
    htp_eq.trans ((blockTP2_unit_15 PathShare.bank15 ⟨(site1 probeRows).prefix, site1 probeRows⟩).trans
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) h1 h2') h3))
  exact hlhs.trans (narrow_tp_diff_arith (ECDSAAdd.toffoliCount shortNorm) (ECDSAAdd.toffoliCount tailNorm))

theorem newRow_rec :
    WEXFast.hblockRec h0 + WEXFast.hblockRec h1 + site1Rec + WEXFast.hrecs restN = 1645472 := by
  have h := WEXFast.W15G.rowH_hrecords
  rw [rowH_split, hrecs_cons, hrecs_cons, hrecs_cons] at h
  have h' : WEXFast.hblockRec h0 + WEXFast.hblockRec h1 + WEXFast.hblockRec h2 + WEXFast.hrecs restN = 1652378 := by
    simpa only [Nat.add_assoc] using h
  exact row_rec_arith _ _ _ _ _ 6906 1652378 h' h2_rec_diff

def rowProg (start : Nat) : Straight 32768 start (start + 1645472) :=
  castFinish (row_cast_arith start _ _ _ _ _ newRow_rec)
    (((WEXFast.hblockProg h0 start).append
      (WEXFast.hblockProg h1 (start + WEXFast.hblockRec h0))).append
      ((twoPassProg (start + WEXFast.hblockRec h0 + WEXFast.hblockRec h1)).append
        (WEXFast.hprog restN (start + WEXFast.hblockRec h0 + WEXFast.hblockRec h1 + site1Rec))))

def rowSrc (read : ConstantBit 32768 → Bool) : AdaptiveCircuit :=
  ((WEXFast.hblockSrc read h0).seq (WEXFast.hblockSrc read h1)).seq
    ((twoPassSrc read).seq (WEXFast.hsrc read restN))

theorem rowProg_run (read : ConstantBit 32768 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rowProg start).instantiate read h).run = (rowSrc read).run := by
  rw [rowProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun hh1 => by
      rw [append_run_fixed _ _ _ _ _ (fun hh2 => WEXFast.hprog_run read restN _ hh2),
        AdaptiveCircuit.run_seq, twoPass_run read _ hh1, ← AdaptiveCircuit.run_seq]),
    AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun hh1 => WEXFast.hblockProg_run read h1 _ hh1),
    AdaptiveCircuit.run_seq, WEXFast.hblockProg_run read h0 _ h]
  simp only [rowSrc, AdaptiveCircuit.run_seq]

local notation "rowTP15" => (WEXFast.hcodeTP WEXFast.W15G.rowH - 6906)

theorem rowTP_eq :
    WEXFast.hblockTP h0 + WEXFast.hblockTP h1 +
      (8191 + 774 + ECDSAAdd.toffoliCount shortNorm + 16383 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 120)) + WEXFast.hcodeTP restN = rowTP15 :=
  rowTP_sub_arith (WEXFast.hcodeTP WEXFast.W15G.rowH) (WEXFast.hblockTP h0) (WEXFast.hblockTP h1)
    (WEXFast.hblockTP h2) (WEXFast.hcodeTP restN)
    (8191 + 774 + ECDSAAdd.toffoliCount shortNorm + 16383 + 513 + ECDSAAdd.toffoliCount tailNorm + (255 + 120))
    6906 ((congrArg WEXFast.hcodeTP rowH_split).trans (hcodeTP_cons3 h0 h1 h2 restN)) h2_tp_diff

theorem rowProg_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rowProg start).instantiate read h).tCount = 7 * rowTP15 := by
  have hg0 := WEXFast.W15G.rowH_hgeo h0 (by rw [rowH_split]; simp)
  have hg1 := WEXFast.W15G.rowH_hgeo h1 (by rw [rowH_split]; simp)
  have hgr : ∀ b ∈ restN, WEXFast.HBlockGeo b := fun b hb => WEXFast.W15G.rowH_hgeo b (by rw [rowH_split]; simp [hb])
  rw [rowProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun hh1 => by
      rw [append_tCount_fixed _ _ _ _ _ (fun hh2 => WEXFast.hprog_tCount read restN hgr _ hh2),
        twoPass_tCount read _ hh1]),
    append_tCount_fixed _ _ _ _ _ (fun hh1 => WEXFast.hblock_tCount read h1 hg1 _ hh1),
    WEXFast.hblock_tCount read h0 hg0 start h]
  exact tcount_mul7_4 _ _ _ _ _ rowTP_eq

theorem rowProg_residue (start : Nat) : AndGadget.residue (rowProg start) = 0 := by
  have hbr (b : WEXFast.HBlock 32768) (s : Nat) : AndGadget.residue (WEXFast.hblockProg b s) = 0 := by
    have h := WEXFast.hprog_residue [b] s
    rw [WEXFast.hprog, AndGadget.residue_cast, AndGadget.residue_append] at h
    omega
  rw [rowProg, AndGadget.residue_cast, AndGadget.residue_append, AndGadget.residue_append,
    AndGadget.residue_append, hbr, hbr, twoPass_residue, WEXFast.hprog_residue]

theorem rowProg_credit (start : Nat) : ProgramCredit (rowProg start) rowTP15 := by
  have hz := rowProg_residue start
  refine ⟨hz, ?_⟩
  have he := exact_t (rowProg start) hz (fun _ => false) (fun _ => false)
  have ht := rowProg_tCount (fun _ => false) start (fun _ => false)
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7) (he.symm.trans ht)

theorem rowProg_wellFormed (start : Nat) : (rowProg start).WellFormed := by
  have hphys : ∀ p, WInstr.literal p ∈ erase2 (WEXFast.hforget WEXFast.W15G.rowH) → GatePhysical p := by
    rw [WEXFast.W15G.hforget_rowH]; exact WEXUnlookup.rowC_physical
  have hg0 := WEXFast.W15G.rowH_hgeo h0 (by rw [rowH_split]; simp)
  have hg1 := WEXFast.W15G.rowH_hgeo h1 (by rw [rowH_split]; simp)
  have hgr : ∀ b ∈ restN, WEXFast.HBlockGeo b := fun b hb => WEXFast.W15G.rowH_hgeo b (by rw [rowH_split]; simp [hb])
  have hp_sub (b : WEXFast.HBlock 32768) (hb : b ∈ WEXFast.W15G.rowH) :
      ∀ p, WInstr.literal p ∈ erase2 b.forgetL → GatePhysical p := fun p hp =>
    hphys p (by
      rw [WEXFast.hforget, erase2]
      have h1 : b.forgetL ⊆ WEXFast.hforget WEXFast.W15G.rowH := fun x hx => List.mem_flatMap.mpr ⟨b, hb, hx⟩
      obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
      exact List.mem_flatMap.mpr ⟨d, h1 hd, hdp⟩)
  have hwf0 : (WEXFast.hblockProg h0 start).WellFormed := by
    unfold h0 WEXFast.hblockProg WEXFast.hblockRec
    exact WEXFast.gblock_wellFormed (.std (.plain (wLiteral [.X 838]))) hg0
      (fun p hp => hp_sub h0 (by rw [rowH_split]; simp) p (by simpa [h0, WEXFast.HBlock.forgetL, erase2] using hp)) start
  have hwf1 : (WEXFast.hblockProg h1 (start + WEXFast.hblockRec h0)).WellFormed := by
    unfold h1 WEXFast.hblockProg WEXFast.hblockRec
    exact WEXFast.gblock_wellFormed (.std (.plain scrHead)) hg1
      (fun p hp => hp_sub h1 (by rw [rowH_split]; simp) p (by simpa [h1, WEXFast.HBlock.forgetL, erase2] using hp)) _
  rw [rowProg, castFinish_wellFormed]
  exact straight_append_wellFormed _ _
    (straight_append_wellFormed _ _ hwf0 hwf1)
    (straight_append_wellFormed _ _ (twoPass_wellFormed _)
      (WEXFast.hprog_wellFormed restN hgr (fun p hp => by
        obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
        obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
        exact hp_sub b (by rw [rowH_split]; simp [hb]) p (List.mem_flatMap.mpr ⟨d, hdb, hdp⟩)) _))

theorem rowProg_support (start : Nat) :
    ChallengeMigration.straightWires (rowProg start) ⊆ PoolHost.newSourceH7 := by
  have hsup_orig := WEXFast.W15G.addFixedCG_support start
  rw [WEXFast.W15G.addFixedCG, support_cast, rowH_split, WEXFast.hprog, support_cast, straightWires_append] at hsup_orig
  have hs0 : ChallengeMigration.straightWires (WEXFast.hblockProg h0 start) ⊆ PoolHost.newSourceH7 :=
    (List.append_subset.mp hsup_orig).1
  have htail1 := (List.append_subset.mp hsup_orig).2
  rw [WEXFast.hprog, support_cast, straightWires_append] at htail1
  have hs1 : ChallengeMigration.straightWires (WEXFast.hblockProg h1 (start + WEXFast.hblockRec h0)) ⊆ PoolHost.newSourceH7 :=
    (List.append_subset.mp htail1).1
  have hrest_sup (s : Nat) : ChallengeMigration.straightWires (WEXFast.hprog restN s) ⊆ PoolHost.newSourceH7 := by
    have horig_s := WEXFast.W15G.addFixedCG_support s
    -- Prove directly via `hprog_support` on `restN`
    have hmem : ∀ b ∈ restN, b ∈ WEXFast.W15G.rowH := fun b hb => by rw [rowH_split]; simp [hb]
    have hf_sub : ∀ x ∈ erase2 (WEXFast.hforget restN), x ∈ erase2 WEXUnlookup.rowC := fun x hx => by
      rw [← WEXFast.W15G.hforget_rowH]
      obtain ⟨d, hd, hdx⟩ := List.mem_flatMap.mp hx
      obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
      exact List.mem_flatMap.mpr ⟨d, List.mem_flatMap.mpr ⟨b, hmem b hb, hdb⟩, hdx⟩
    exact WEXFast.hprog_support restN (fun b hb => WEXFast.W15G.rowH_hgeo b (hmem b hb))
      (fun p hp => PoolHost.rowC_lit_relaxed7 p (hf_sub _ hp))
      (fun b hb => WEXFast.W15G.rowH_strict b (hmem b hb))
      (fun b hb => WEXFast.W15G.rowH_ctl b (hmem b hb))
      (fun b hb => WEXFast.W15G.rowH_ctl3 b (hmem b hb))
      (fun b hb => WEXFast.W15G.rowH_ctl4 b (hmem b hb))
      (fun c ps hp => PoolHost.rowC_look_newH7 c ps (hf_sub _ hp))
      (fun b hb => WEXFast.W15G.rowH_nohost b (hmem b hb)) s
  rw [rowProg, support_cast, straightWires_append, straightWires_append, straightWires_append]
  exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨hs0, hs1⟩,
    List.append_subset.mpr ⟨twoPass_support _, hrest_sup _⟩⟩

theorem site1_slots_le_rowC :
    ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) ≤
      literalSlotSum (erase2 WEXUnlookup.rowC) := by
  rw [ECDSAAdd.Baselines.normalize_slots]
  have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
    unfold WEXUnlookup.rowC; rfl
  have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
    unfold WEXUnlookup.rowHead; rfl
  apply literalSlotSum_le_of_mem (erase2 WEXUnlookup.rowC) site1Arith
  rw [h1, h2, List.map_append, erase2_append, erase2_append]
  apply List.mem_append_left; apply List.mem_append_left
  rw [WEXUnlookup.rowPre3]
  simp only [List.map_cons, List.map_nil, erase2_cons, erase2_nil, List.append_nil, toBlock2,
    Block2.code, UnitSite.code, site1, MaskedSite.prefix, wLiteral]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem rowProg_slots (start : Nat) :
    (rowProg start).gateSlots ≤
      codeSlots WEX.windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 930000000 := by
  have hg0 := WEXFast.W15G.rowH_hgeo h0 (by rw [rowH_split]; simp)
  have hg1 := WEXFast.W15G.rowH_hgeo h1 (by rw [rowH_split]; simp)
  have hgr : ∀ b ∈ restN, WEXFast.HBlockGeo b := fun b hb => WEXFast.W15G.rowH_hgeo b (by rw [rowH_split]; simp [hb])
  have hs0 := WEXFast.hprog_slots [h0] (fun b hb => by simp at hb; subst hb; exact hg0) start
  rw [WEXFast.hprog, castFinish_gateSlots, Straight.gateSlots_append] at hs0
  simp only [WEXFast.hprog, Straight.gateSlots, WEXFast.hforget, WEXFast.hslack,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero] at hs0
  have hs1 := WEXFast.hprog_slots [h1] (fun b hb => by simp at hb; subst hb; exact hg1)
    (start + WEXFast.hblockRec h0)
  rw [WEXFast.hprog, castFinish_gateSlots, Straight.gateSlots_append] at hs1
  simp only [WEXFast.hprog, Straight.gateSlots, WEXFast.hforget, WEXFast.hslack,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero] at hs1
  have hsr := WEXFast.hprog_slots restN hgr
    (start + WEXFast.hblockRec h0 + WEXFast.hblockRec h1 + site1Rec)
  have htp := twoPass_slots (start + WEXFast.hblockRec h0 + WEXFast.hblockRec h1)
  have hsp_split :
      PathShare.codeSP2 PathShare.bank15 (WEXFast.hforget WEXFast.W15G.rowH) =
        PathShare.codeSP2 PathShare.bank15 h0.forgetL +
        PathShare.codeSP2 PathShare.bank15 h1.forgetL +
        PathShare.codeSP2 PathShare.bank15 h2.forgetL +
        PathShare.codeSP2 PathShare.bank15 (WEXFast.hforget restN) := by
    rw [rowH_split]
    simp only [WEXFast.hforget_cons, WEXFast.codeSP2_append7, Nat.add_assoc]
  have hsl_split :
      WEXFast.hslack WEXFast.W15G.rowH =
        WEXFast.hblockSlack h0 + WEXFast.hblockSlack h1 + WEXFast.hblockSlack h2 + WEXFast.hslack restN := by
    rw [rowH_split]; simp only [WEXFast.hslack, Nat.add_assoc]
  have hsp_all := ShorECDLP.Entrant.WEXFast.W15F.rowC_slotsP start
  rw [WEXFast.W15G.hforget_rowH] at hsp_split
  have hsl_all := WEXFast.W15G.rowH_hslack
  have hlit_le := site1_slots_le_rowC
  have hl0 := WEX.clearReferenceRow_literal_slots_bound
  have hm := WEXUnlookup.rowC_measures.2.2.1
  rw [rowProg, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append, Straight.gateSlots_append]
  generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) = gS at htp hlit_le
  generalize literalSlotSum (erase2 WEXUnlookup.rowC) = L1 at hlit_le hm
  generalize literalSlotSum (WEX.clearReferenceRow probeRows) = L0 at hl0 hm
  generalize codeSlots WEX.windowBits (normalizeW (erase2 WEXUnlookup.rowC)) = CS at hsp_all ⊢
  generalize PathShare.codeSP2 PathShare.bank15 WEXUnlookup.rowC = spAll at hsp_split hsp_all
  generalize PathShare.codeSP2 PathShare.bank15 h0.forgetL = sp0 at hs0 hsp_split
  generalize PathShare.codeSP2 PathShare.bank15 h1.forgetL = sp1 at hs1 hsp_split
  generalize PathShare.codeSP2 PathShare.bank15 h2.forgetL = sp2 at hsp_split
  generalize PathShare.codeSP2 PathShare.bank15 (WEXFast.hforget restN) = spR at hsr hsp_split
  generalize WEXFast.hslack WEXFast.W15G.rowH = slAll at hsl_split hsl_all
  generalize WEXFast.hblockSlack h0 = sl0 at hs0 hsl_split
  generalize WEXFast.hblockSlack h1 = sl1 at hs1 hsl_split
  generalize WEXFast.hblockSlack h2 = sl2 at hsl_split
  generalize WEXFast.hslack restN = slR at hsr hsl_split
  omega

theorem rowSrc_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSrc (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (WEX.rowPointState coeffs Q)) WEXUnlookup.LiveReady := by
  let read := readConstant coeffs Q
  have hg0 := WEXFast.W15G.rowH_hgeo h0 (by rw [rowH_split]; simp)
  have hg1 := WEXFast.W15G.rowH_hgeo h1 (by rw [rowH_split]; simp)
  have hgr : ∀ b ∈ restN, WEXFast.HBlockGeo b := fun b hb => WEXFast.W15G.rowH_hgeo b (by rw [rowH_split]; simp [hb])
  obtain ⟨c0, a0, m0⟩ := WEXFast.hblock_sim read h0 hg0
  obtain ⟨c1, a1, m1⟩ := WEXFast.hblock_sim read h1 hg1
  obtain ⟨c2, a2, m2⟩ := twoPass_sim read
  obtain ⟨cr, ar, mr⟩ := WEXFast.hsrc_sim read restN hgr
  have h01_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (h0.forgetL ++ h1.forgetL)) ∧
        ∀ a st, AddrValid WEX.windowBits windowRoot a st →
          WEXFast.HBlockClean h0 st →
          (∀ m', m'.length = ECDSAAdd.measurementCount (reference2 read a h0.forgetL) →
            WEXFast.HBlockClean h1 (ECDSAAdd.run (reference2 read a h0.forgetL) m' st)) →
          Safe2 read a (h0.forgetL ++ h1.forgetL) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (h0.forgetL ++ h1.forgetL)) m st))
      ((WEXFast.hblockSrc read h0).seq (WEXFast.hblockSrc read h1)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c0 c1, ?_, by rw [simulationCoefficients_mass, m0, m1]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a0 a1
    intro b₀ k₀ b₁ k₁ hb₀ hb₁
    obtain ⟨m₀, lm₀, r₀⟩ := hb₀
    obtain ⟨m₁, lm₁, r₁⟩ := hb₁
    refine ⟨m₀ ++ m₁, by simp [erase2_append, List.length_append, lm₀, lm₁], ?_⟩
    intro a st ha hc0 hc1 hsafe
    have hm₀ : m₀.length = ECDSAAdd.measurementCount (reference2 read a h0.forgetL) :=
      lm₀.trans (specialize_counts read (erase2 h0.forgetL) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a h0.forgetL h1.forgetL st hsafe
    have ha1 := WEXFast.hblock_addr read h0 hg0 a st ha hc0 m₀
    change b₁.kraus (b₀.kraus (Bridge.signedKet st)) = _
    rw [r₀ a st ha hc0 hsp.1, map_smul,
      r₁ a _ ha1 (hc1 m₀ hm₀) (hsp.2 m₀ hm₀), reference2_append, run_append_records _ _ m₀ m₁ st hm₀, smul_smul]
  have h2r_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (h2.forgetL ++ WEXFast.hforget restN)) ∧
        ∀ a st, AddrValid WEX.windowBits windowRoot a st →
          WEXFast.HCodeClean read a (h2 :: restN) st →
          Clean streamLayout.dialogPool st.basis →
          Safe2 read a (h2.forgetL ++ WEXFast.hforget restN) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (h2.forgetL ++ WEXFast.hforget restN)) m st))
      ((twoPassSrc read).seq (WEXFast.hsrc read restN)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c2 cr, ?_, by rw [simulationCoefficients_mass, m2, mr]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a2 ar
    intro b₂ k₂ br kr hb₂ hbr
    obtain ⟨m₂, lm₂, r₂⟩ := hb₂
    obtain ⟨mr', lmr', rr⟩ := hbr
    have h2_lit : literalRecords (erase2 h2.forgetL) = ECDSAAdd.measurementCount site1Arith := by
      have heq : erase2 h2.forgetL =
          [WInstr.lookup (some windowRoot) (sitePorts probeRows), WInstr.literal site1Arith,
           WInstr.lookup (some windowRoot) (sitePorts probeRows)] := by
        simp [h2, WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, erase2, Block2.code, UnitSite.code,
          site1, MaskedSite.prefix, wLiteral]
      rw [heq]; exact litRec_lookup_lit_lookup _ _ _ _ _
    have h2_ref (a : Nat) : reference2 read a h2.forgetL = (specialize (site1 probeRows).code a).instantiate read := by
      simp [h2, WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, reference2, erase2, Block2.code,
        UnitSite.code, site1, MaskedSite.code, MaskedSite.prefix]
    refine ⟨m₂ ++ mr', by simp [erase2_append, List.length_append, h2_lit, lm₂, lmr'], ?_⟩
    intro a st ha hcl hpool hsafe
    have hm₂ : m₂.length = ECDSAAdd.measurementCount (reference2 read a h2.forgetL) := by
      rw [← h2_lit] at lm₂; exact lm₂.trans (specialize_counts read (erase2 h2.forgetL) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a h2.forgetL (WEXFast.hforget restN) st hsafe
    have ha2 := WEXFast.hblock_addr read h2 (WEXFast.W15G.rowH_hgeo h2 (by rw [rowH_split]; simp)) a st ha hcl.1 m₂
    have hpath2 : Clean PathShare.pathBank st.basis := hcl.1.1
    have hsafe2 : ∀ m', Clean scrAllWires (ECDSAAdd.run ((specialize (site1 probeRows).code a).instantiate read) m' st).basis := by
      have hs1 : BlockSafe2 read a (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩) st := hsp.1.1
      intro m'
      simpa [site1, sitePorts_targets] using hs1 m'
    change br.kraus (b₂.kraus (Bridge.signedKet st)) = _
    rw [r₂ a st ha hpath2 hpool hsafe2, ← h2_ref a, map_smul,
      rr a _ ha2 (hcl.2 m₂ hm₂) (hsp.2 m₂ hm₂), reference2_append, run_append_records _ _ m₂ mr' st hm₂, smul_smul]
  obtain ⟨c01, a01, m01⟩ := h01_sim
  obtain ⟨c2r, a2r, m2r⟩ := h2r_sim
  refine ⟨coherentSeqCoefficients c01 c2r, ?_, by rw [simulationCoefficients_mass, m01, m2r]; norm_num⟩
  rw [rowSrc, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a01 a2r
  intro b₁ k₁ b₂ k₂ hb₁ hb₂ s hs
  obtain ⟨m₁, lm₁, r₁⟩ := hb₁
  obtain ⟨m₂, lm₂, r₂⟩ := hb₂
  let a := tableAddressValue WEX.windowBits s
  have hsafe_all : Safe2 read a (WEXFast.hforget WEXFast.W15G.rowH) ⟨false, s⟩ := by
    rw [WEXFast.W15G.hforget_rowH]; exact (WEXUnlookup.rowC_safe_run coeffs Q hQ hn a s hs.1).1
  have hclean_all : WEXFast.HCodeClean read a WEXFast.W15G.rowH ⟨false, s⟩ := by
    unfold WEXFast.W15G.rowH
    refine WEXFast.hclean_pair _ _ _ _ WEXFast.W15G.corner7 _ ?_
    rw [← WEXFast.W15G.rowCF_split]
    exact WEXFast.W15G.gclean_of_fclean _ _ WEXFast.rowCF _ (WEXFast.rowCF_clean coeffs Q hQ hn a s hs.1)
      (by rw [WEXFast.fforget_rowCF]; exact PoolHost.rowC_host4 coeffs Q hQ hn a s hs.1)
  rw [rowH_split] at hsafe_all hclean_all
  simp only [WEXFast.hforget_cons, List.append_assoc] at hsafe_all
  have hsafe_split := WideBank8.Fast16.safe2_append_inv read a (h0.forgetL ++ h1.forgetL)
    (h2.forgetL ++ WEXFast.hforget restN) ⟨false, s⟩ (by simpa [List.append_assoc] using hsafe_all)
  have hm₁ : m₁.length = ECDSAAdd.measurementCount (reference2 read a (h0.forgetL ++ h1.forgetL)) :=
    lm₁.trans (specialize_counts read (erase2 (h0.forgetL ++ h1.forgetL)) a).2.symm
  have h0_m : ECDSAAdd.measurementCount (reference2 read a h0.forgetL) = 0 := by
    have hr : reference2 read a h0.forgetL = [.X 838] := by
      simp [h0, WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, reference2, erase2, Block2.code,
        wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_lit]
    rw [hr]; exact x838_meas_zero
  have h1_m : ECDSAAdd.measurementCount (reference2 read a h1.forgetL) = 0 := by
    have hr : reference2 read a h1.forgetL = scrHeadProgram := by
      simp [h1, WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, reference2, erase2, Block2.code,
        scrHead, scrHeadProgram, wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_append, Tmpl.instantiate_lit]
    rw [hr]; exact scrHeadProgram_meas_zero
  have hm₁_0 : m₁ = List.nil := List.eq_nil_of_length_eq_zero (by
    rw [hm₁, reference2_append, ECDSAAdd.measurementCount_append, h0_m, h1_m])
  have ha0 : AddrValid WEX.windowBits windowRoot a ⟨false, s⟩ := ⟨rfl, hs.1.2.2⟩
  have hcl0 : WEXFast.HBlockClean h0 ⟨false, s⟩ := hclean_all.1
  have hcl1 : ∀ m', m'.length = ECDSAAdd.measurementCount (reference2 read a h0.forgetL) →
      WEXFast.HBlockClean h1 (ECDSAAdd.run (reference2 read a h0.forgetL) m' ⟨false, s⟩) :=
    fun m' hm' => (hclean_all.2 m' hm').1
  have hstep01 := r₁ a ⟨false, s⟩ ha0 hcl0 hcl1 hsafe_split.1
  set st12 := ECDSAAdd.run (reference2 read a (h0.forgetL ++ h1.forgetL)) m₁ ⟨false, s⟩ with hst12
  have hst12_eq : st12 = ECDSAAdd.run (reference2 read a h1.forgetL) List.nil
      (ECDSAAdd.run (reference2 read a h0.forgetL) List.nil ⟨false, s⟩) := by
    rw [hst12, hm₁_0, reference2_append, ECDSAAdd.run_append, h0_m]; rfl
  have hpool12 : Clean streamLayout.dialogPool st12.basis := by
    rw [hst12_eq]
    have h := liveReady_pool_after_b01 read probeRows a s hs.1 List.nil List.nil
    simpa [h0, h1, WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, WideSigned.Rows.code, WideSigned.Rows.instr,
      wLiteral, scrHead] using h
  have ha12 : AddrValid WEX.windowBits windowRoot a st12 := by
    rw [hst12_eq]
    have ha1' := WEXFast.hblock_addr read h0 hg0 a ⟨false, s⟩ ha0 hcl0 List.nil
    exact WEXFast.hblock_addr read h1 hg1 a _ ha1' (hcl1 List.nil (by simp [h0_m])) List.nil
  have hcl2r : WEXFast.HCodeClean read a (h2 :: restN) st12 := by
    rw [hst12_eq]
    exact (hclean_all.2 List.nil (by simp [h0_m])).2 List.nil (by simp [h1_m])
  have hstep2r := r₂ a st12 ha12 hcl2r hpool12 (hsafe_split.2 m₁ hm₁)
  change b₂.kraus (b₁.kraus (ket s)) = _
  rw [← Bridge.signedKet_false s, hstep01, map_smul, hstep2r, smul_smul]
  have hcomb : ECDSAAdd.run (reference2 read a (h2.forgetL ++ WEXFast.hforget restN)) m₂ st12 =
      ECDSAAdd.run (reference2 read a (WEXFast.hforget WEXFast.W15G.rowH)) (m₁ ++ m₂) ⟨false, s⟩ := by
    rw [hst12, ← run_append_records _ _ m₁ m₂ ⟨false, s⟩ hm₁, ← reference2_append, rowH_split]
    simp [WEXFast.hforget_cons, List.append_assoc]
  rw [hcomb, WEXFast.W15G.hforget_rowH, WEXUnlookup.rowC_run_any a coeffs Q hQ hn s hs.1 (m₁ ++ m₂),
    Bridge.signedKet_false, Bridge.signedKet_false]
  simp [ket, WEX.rowPointState, a]

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (WEXUnlookup.fastSignSource.seq (rowSrc (readConstant coeffs Q))).seq WEXUnlookup.fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (WEX.middleState coeffs Q)) WEXUnlookup.LiveReady := by
  have first := composeCoherent WEXUnlookup.fastSign_coherent (rowSrc_coherent coeffs Q hQ hn)
    (fun s hs => WEXUnlookup.live_write _ s hs)
  exact composeCoherent (f := fun s => WEX.rowPointState coeffs Q (WEX.signPointState s))
    (g := WEX.signPointState) first WEXUnlookup.fastSign_coherent
    (fun s hs => WEXUnlookup.live_write _ _ (WEXUnlookup.live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (WEX.prefixSource.seq (fastMiddleSource coeffs Q)).seq WEX.suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastBodySource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (WEX.bodyState coeffs Q)) WEXUnlookup.Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨WEX.windowPrepare_live _ (WEX.rootFlip_live s hs.1), WEXUnlookup.prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => WEX.middleState coeffs Q (WEX.prefixState s))
    (g := WEX.suffixState) h WEX.suffix_coherent (fun _ _ => True.intro)

def fastBodyProgram (start : Nat) : Straight 32768 start (start + 1645984) :=
  castFinish (by omega)
    (((((WEX.prefixProgram start).append (WEX.nFastProgram start)).append (rowProg (start + 256))).append
      (WEX.nFastProgram (start + 256 + 1645472))).append (WEX.suffixProgram (start + 256 + 1645472 + 256)))

attribute [local irreducible] fastBodyProgram rowProg

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((WEX.prefixSource.seq ((WEXUnlookup.fastSignSource.seq (rowSrc (readConstant coeffs Q))).seq
        WEXUnlookup.fastSignSource)).seq WEX.suffixSource).run := by
    rw [fastBodyProgram, castFinish_instantiate]
    exact WEXUnlookup.five_run (readConstant coeffs Q) _ _ _ _ _ WEX.prefixSource WEXUnlookup.fastSignSource
      (rowSrc (readConstant coeffs Q)) WEXUnlookup.fastSignSource WEX.suffixSource
      (WEX.prefixProgram_run _ _) (WEX.nFastProgram_run _ _) (rowProg_run _ _)
      (WEX.nFastProgram_run _ _) (WEX.suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((WEX.prefixSource.seq ((WEXUnlookup.fastSignSource.seq (rowSrc (readConstant coeffs Q))).seq
        WEXUnlookup.fastSignSource)).seq WEX.suffixSource) := by
    delta fastBodySource fastMiddleSource; rfl
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (WEX.bodyState coeffs Q)) WEXUnlookup.Ready := by
  obtain ⟨cs, aligned, mass⟩ := fastBodySource_coherent coeffs Q hQ hn
  refine ⟨cs, ?_, mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + rowTP15) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram)
  have hl : ProgramCredit (WEX.nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (WEX.nFastProgram (start + 256 + 1645472)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact WEXUnlookup.five_credit a rowTP15 (WEXCredit.prefix_credit start) hl (rowProg_credit (start + 256)) hr
    (WEXCredit.suffix_credit (start + 256 + 1645472 + 256))

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram, castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (WEX.prefixProgram_wellFormed start) (WEX.nFastProgram_wellFormed start)
      · exact rowProg_wellFormed _
    · exact WEX.nFastProgram_wellFormed _
  · exact WEX.suffixProgram_wellFormed _

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ PoolHost.newSourceH7 := by
  have hsub (l : List Wire) (hl : l ⊆ newSourceH)
      (h4 : ∀ w ∈ l, w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874) : l ⊆ PoolHost.newSourceH7 :=
    fun w hw => PoolHost.newSourceH7_of_newH w (hl hw) (h4 w hw).1 (h4 w hw).2.1 (h4 w hw).2.2.1 (h4 w hw).2.2.2
  have hp : ChallengeMigration.straightWires (WEX.prefixProgram start) ⊆ PoolHost.newSourceH7 := by
    rw [WEX.prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    exact hsub _ (newSourceH_of_bounds _ (by decide +kernel)) (by decide +kernel)
  have hs (j : Nat) : ChallengeMigration.straightWires (WEX.suffixProgram j) ⊆ PoolHost.newSourceH7 := by
    rw [WEX.suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    exact hsub _ (newSourceH_of_bounds _ (by decide +kernel)) (by decide +kernel)
  rw [fastBodyProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp, TightSupport.nFast_newH7 _⟩, rowProg_support _⟩, TightSupport.nFast_newH7 _⟩, hs _⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2600000000 := by
  rw [fastBodyProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append, WEX.nFastProgram_slots, WEX.prefixProgram, WEX.suffixProgram,
    literalProgram_slots]
  have ha := rowProg_slots (start + 256)
  have len : (signedAddressCircuit 836 870 WEX.windowBits).length = 30 := by decide +kernel
  simp only [len, List.length_cons, List.length_nil]
  have hc := WEX.codeSlots_bound WEX.windowBits (normalizeW (erase2 WEXUnlookup.rowC))
  rw [literalSlotSum_normalize, portTotal_normalize, traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.rowC_measures
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := WEX.fastWindowSign_slots
  have hwlen : WEX.windowBits.length = 15 := rfl
  rw [hwlen] at hc
  generalize codeSlots WEX.windowBits (normalizeW (erase2 WEXUnlookup.rowC)) = C at hc ha
  generalize (rowProg (start + 256)).gateSlots = A at ha ⊢
  generalize ECDSAAdd.Challenge.gateSlots WEX.fastWindowSignProgram = G at sign bound
  generalize Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram)) = S
    at sign ⊢
  have h1 := hm.2.1
  have h2 := hm.2.2.1
  have h3 := hm.2.2.2.1
  generalize literalSlotSum (erase2 WEXUnlookup.rowC) = L1 at hc h2
  generalize literalSlotSum (WEX.clearReferenceRow probeRows) = L0 at hl h2
  generalize portTotal (erase2 WEXUnlookup.rowC) = P1 at hc h3
  generalize portTotal (WEX.clearReferenceRow probeRows) = P0 at hp h3
  generalize traversals (erase2 WEXUnlookup.rowC) = T1 at hc h1
  omega

def compactProgram (start : Nat) : Straight 32768 start (start + 1645984) :=
  relabelStraight PoolHost.piH7 (fastBodyProgram start)

theorem fastCount_upper :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + rowTP15 ≤ 2245165 := by
  have h1 : WEXFast.hcodeTP WEXFast.W15G.rowH =
      WEXFast.hblockTP h0 + WEXFast.hblockTP h1 + WEXFast.hblockTP h2 + WEXFast.hcodeTP restN :=
    (congrArg WEXFast.hcodeTP rowH_split).trans (hcodeTP_cons3 h0 h1 h2 restN)
  have h2tp := h2_tp_diff
  have hold := WEXFast.W15G.fastCount_upper
  generalize WEXFast.hcodeTP WEXFast.W15G.rowH = T at h1 hold ⊢
  generalize WEXFast.hblockTP h2 = T2 at h1 h2tp
  generalize ECDSAAdd.toffoliCount shortNorm = tS at h2tp
  generalize ECDSAAdd.toffoliCount tailNorm = tT at h2tp
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) = tSign at hold ⊢
  omega

end Narrow15

/-! ### Part B: Wide (16-bit) two-pass `site1` and spliced row `Wide16` -/

namespace Wide16
open WideSigned

def r16 : Nat → Fin 65536 := WideBank8.Row16.rows

def sp16 : List (LookupPort 65536) := Rows.ports r16 (shortPorts probeRows)
def pp16 : List (LookupPort 65536) := Rows.ports r16 (pairExtraPorts probeRows)
def site1_16 : MaskedSite 65536 := Rows.site r16 (site1 probeRows)

theorem sp16_targets : portTargets sp16 = shortWires := by
  rw [sp16, Rows.targets]; exact shortPorts_targets probeRows
theorem pp16_targets : portTargets pp16 = pairExtraWires := by
  rw [pp16, Rows.targets]; exact pairExtraPorts_targets probeRows
theorem sp16_length : sp16.length = 258 := by
  rw [sp16, Rows.ports, List.length_map]; exact shortPorts_length probeRows
theorem pp16_length : pp16.length = 513 := by
  rw [pp16, Rows.ports, List.length_map]; exact pairExtraPorts_length probeRows

def fA : SS2 65536 where
  bits := WideBank8.Fast16.windowBits
  paths := WideBank8.Fast16.pathBank
  selBits := WideBank8.Fast16.selBits
  selPaths := WideBank8.Fast16.selPaths
  guard := windowRoot
  ports := sp16
  g1 := gA1
  g2 := gA2
  g3 := gA3

def fB : SS1 65536 where
  bits := WideBank8.Fast16.windowBits
  paths := WideBank8.Fast16.pathBank
  selBits := WideBank8.Fast16.selBits1
  selPaths := WideBank8.Fast16.selPaths1
  guard := windowRoot
  ports := pp16
  g1 := gB

theorem fA_geo : fA.Geo where
  bitsEq := by decide
  pathsSub := by
    intro w hw
    simp only [fA, WideBank8.Fast16.selPaths, WideBank8.Fast16.pathBank,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw ⊢
    dsimp only [Wire, ECDSAAdd.Wire] at hw ⊢; omega
  selLen := by decide
  selNodup := by decide
  selDisj := by
    apply List.disjoint_left.mpr
    intro w hw hm
    rw [fA, sp16_targets] at hm
    have hb := mem_short_garbA hm
    simp only [fA, windowRoot, WideBank8.Fast16.selBits, WideBank8.Fast16.selPaths,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change gA1.length = sp16.length; rw [gA1_len, sp16_length]
  len2 := by change gA2.length = sp16.length; rw [gA2_len, sp16_length]
  len3 := by change gA3.length = sp16.length; rw [gA3_len, sp16_length]
  nodup := by rw [fA, sp16_targets]; exact short_garbA_nodup
  n855 := fun hm => by rw [fA, sp16_targets] at hm; have := mem_short_garbA hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  n856 := fun hm => by rw [fA, sp16_targets] at hm; have := mem_short_garbA hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem fB_geo : fB.Geo where
  bitsEq := by decide
  pathsSub := by
    intro w hw
    simp only [fB, WideBank8.Fast16.selPaths1, WideBank8.Fast16.pathBank,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw ⊢
    dsimp only [Wire, ECDSAAdd.Wire] at hw ⊢; omega
  selLen := by decide
  selNodup := by decide
  selDisj := by
    apply List.disjoint_left.mpr
    intro w hw hm
    rw [fB, pp16_targets] at hm
    have hb := mem_pairExtra_gB hm
    simp only [fB, windowRoot, WideBank8.Fast16.selBits1, WideBank8.Fast16.selPaths1,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change gB.length = pp16.length; rw [gB_len, pp16_length]
  nodup := by rw [fB, pp16_targets]; exact pairExtra_gB_nodup
  n855 := fun hm => by rw [fB, pp16_targets] at hm; have := mem_pairExtra_gB hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

def hot8 (i : Fin 256) : Wire := 14374 + i.val
def scratch8 : Wire := 14373
def tree8 : UnaryActionTree := tableAddressTree WideBank8.Fast16.bank15.high 0 1

def d1 : List (MeasuredClear.ClearPort 65536) := clearData fA.garbPorts
def d2 : List (MeasuredClear.ClearPort 65536) := clearData sp16
def d3 : List (MeasuredClear.ClearPort 65536) := clearData fB.garbPorts
def d4 : List (MeasuredClear.ClearPort 65536) := clearData pp16
def allData : List (MeasuredClear.ClearPort 65536) := d1 ++ d2 ++ d3 ++ d4

theorem d1_targets : d1.map MeasuredClear.ClearPort.target = garbA := by
  rw [d1, clearData_targets]; exact fA.garbPorts_targets fA_geo
theorem d2_targets : d2.map MeasuredClear.ClearPort.target = shortWires := by
  rw [d2, clearData_targets]; exact sp16_targets
theorem d3_targets : d3.map MeasuredClear.ClearPort.target = gB := by
  rw [d3, clearData_targets]; exact fB.garbPorts_targets fB_geo
theorem d4_targets : d4.map MeasuredClear.ClearPort.target = pairExtraWires := by
  rw [d4, clearData_targets]; exact pp16_targets

theorem d1_len : d1.length = 774 := by
  have := congrArg List.length d1_targets; simpa [garbA_len] using this
theorem d2_len : d2.length = 258 := by
  have := congrArg List.length d2_targets; simpa [shortWires_length] using this
theorem d3_len : d3.length = 513 := by
  have := congrArg List.length d3_targets; simpa [gB_len] using this
theorem d4_len : d4.length = 513 := by
  have := congrArg List.length d4_targets; simpa [pairExtraWires_length] using this
theorem allData_len : allData.length = 2058 := by
  simp only [allData, List.length_append, d1_len, d2_len, d3_len, d4_len]

def fixRec8 : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree8 windowRoot WideBank8.Fast16.bank15.hp) + 255

theorem tree8_layout : tree8.Layout windowRoot WideBank8.Fast16.bank15.hp :=
  tableAddressTree_layout _ _ _ 0 1 (by decide) (by decide)

theorem tree8_nodes : tree8.internalNodes = 255 := WideBank8.Fast16.high_nodes

theorem tree8_leaves : tree8.leaves = 256 := by
  have h := MeasuredClear.addressTree_leaves WideBank8.Fast16.bank15.high 0 1
  simpa [tree8, WideBank8.Fast16.bank15, WideBank8.Fast16.high] using h

theorem fixRec8_eq : fixRec8 = 510 := by
  rw [fixRec8, (MeasuredClear.recordUnary_counts tree8 windowRoot WideBank8.Fast16.bank15.hp tree8_layout 0).1,
    tree8_nodes]

theorem fA_rec : codeRecords fA.selBits fA.selPaths windowRoot fA.selCode = 16383 := by
  rw [fA.loadProg_records fA_geo]; decide

theorem fB_rec : codeRecords fB.selBits fB.selPaths windowRoot fB.selCode = 32767 := by
  rw [fB.loadProg_records fB_geo]; decide

def step8 (start : Nat) (refs123 : List (Fin start)) : Straight 65536 start (start + (513 + fixRec8)) :=
  castFinish (by rw [pairExtraWires_length]; exact Nat.add_assoc start 513 fixRec8)
    (MeasuredClear.measureThen (R := fixRec8)
      (fun cursor rs => castFinish (by rw [fixRec8]; exact Nat.add_assoc cursor _ 255)
        (MeasuredClear.fixupProgram8 allData rs WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp))
      pairExtraWires start refs123)

def step78 (start : Nat) (refs123 : List (Fin start)) : Straight 65536 start (start + (mTail + (513 + fixRec8))) :=
  castFinish (Nat.add_assoc start mTail (513 + fixRec8))
    ((literalFixed tailNorm mTail ((literal_meas (n := 65536) _).trans tailNorm_meas) start).append
      (step8 (start + mTail) (refs123.map (Fin.castLE (Nat.le_add_right _ _)))))

def step678 (start : Nat) (refs12 : List (Fin start)) :
    Straight 65536 start (start + (513 + (mTail + (513 + fixRec8)))) :=
  castFinish (by rw [gB_len]; exact Nat.add_assoc start 513 _)
    (MeasuredClear.measureThen (R := mTail + (513 + fixRec8))
      (fun cursor rs => step78 cursor rs) gB start refs12)

def step5678 (start : Nat) (refs12 : List (Fin start)) :
    Straight 65536 start (start + (32767 + (513 + (mTail + (513 + fixRec8))))) :=
  castFinish (by rw [fB_rec]; exact Nat.add_assoc start 32767 _)
    ((fB.loadProg start).append
      (step678 (start + codeRecords fB.selBits fB.selPaths windowRoot fB.selCode)
        (refs12.map (Fin.castLE (Nat.le_add_right _ _)))))

def step4_8 (start : Nat) (refs1 : List (Fin start)) :
    Straight 65536 start (start + (258 + (32767 + (513 + (mTail + (513 + fixRec8)))))) :=
  castFinish (by rw [shortWires_length]; exact Nat.add_assoc start 258 _)
    (MeasuredClear.measureThen (R := 32767 + (513 + (mTail + (513 + fixRec8))))
      (fun cursor rs => step5678 cursor rs) shortWires start refs1)

def step3_8 (start : Nat) (refs1 : List (Fin start)) :
    Straight 65536 start (start + (mShort + (258 + (32767 + (513 + (mTail + (513 + fixRec8))))))) :=
  castFinish (Nat.add_assoc start mShort _)
    ((literalFixed shortNorm mShort ((literal_meas (n := 65536) _).trans shortNorm_meas) start).append
      (step4_8 (start + mShort) (refs1.map (Fin.castLE (Nat.le_add_right _ _)))))

def step2_8 (start : Nat) :
    Straight 65536 start (start + (774 + (mShort + (258 + (32767 + (513 + (mTail + (513 + fixRec8)))))))) :=
  castFinish (by rw [garbA_len]; exact Nat.add_assoc start 774 _)
    (MeasuredClear.measureThen (R := mShort + (258 + (32767 + (513 + (mTail + (513 + fixRec8))))))
      (fun cursor rs => step3_8 cursor rs) garbA start List.nil)

def site1Rec : Nat := site1RecGen 16383 32767 mShort mTail fixRec8

def twoPassProg (start : Nat) : Straight 65536 start (start + site1Rec) :=
  castFinish (twoPass_fin_gen start _ 16383 32767 mShort mTail fixRec8 fA_rec)
    ((fA.loadProg start).append
      (step2_8 (start + codeRecords fA.selBits fA.selPaths windowRoot fA.selCode)))

attribute [local irreducible] step8 step78 step678 step5678 step4_8 step3_8 step2_8 twoPassProg

def step8Src (read : ConstantBit 65536 → Bool) (o123 : List Bool) : AdaptiveCircuit :=
  measureResetThen pairExtraWires (fun o4 =>
    MeasuredClear.fixupSource8 allData (o123 ++ o4) read WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp)

def step78Src (read : ConstantBit 65536 → Bool) (o123 : List Bool) : AdaptiveCircuit :=
  (literalSource tailNorm).seq (step8Src read o123)

def step678Src (read : ConstantBit 65536 → Bool) (o12 : List Bool) : AdaptiveCircuit :=
  measureResetThen gB (fun o3 => step78Src read (o12 ++ o3))

def step5678Src (read : ConstantBit 65536 → Bool) (o12 : List Bool) : AdaptiveCircuit :=
  (fB.loadSource read).seq (step678Src read o12)

def step4_8Src (read : ConstantBit 65536 → Bool) (o1 : List Bool) : AdaptiveCircuit :=
  measureResetThen shortWires (fun o2 => step5678Src read (o1 ++ o2))

def step3_8Src (read : ConstantBit 65536 → Bool) (o1 : List Bool) : AdaptiveCircuit :=
  (literalSource shortNorm).seq (step4_8Src read o1)

def step2_8Src (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  measureResetThen garbA (fun o1 => step3_8Src read o1)

def twoPassSrc (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  (fA.loadSource read).seq (step2_8Src read)

theorem step8_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs123 : List (Fin start))
    (h : Fin start → Bool) :
    ((step8 start refs123).instantiate read h).run = (step8Src read (refs123.map h)).run := by
  rw [step8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => MeasuredClear.fixupSource8 allData o read WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp) read
      (fun cursor rs hh => by rw [castFinish_instantiate, MeasuredClear.fixupProgram_run8])]
  rfl

theorem step78_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs123 : List (Fin start))
    (h : Fin start → Bool) :
    ((step78 start refs123).instantiate read h).run = (step78Src read (refs123.map h)).run := by
  rw [step78, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step8Src read (refs123.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step8_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step678_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs12 : List (Fin start))
    (h : Fin start → Bool) :
    ((step678 start refs12).instantiate read h).run = (step678Src read (refs12.map h)).run := by
  rw [step678, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step78Src read o) read
      (fun cursor rs hh => step78_run read cursor rs hh)]
  rfl

theorem step5678_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs12 : List (Fin start))
    (h : Fin start → Bool) :
    ((step5678 start refs12).instantiate read h).run = (step5678Src read (refs12.map h)).run := by
  rw [step5678, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step678Src read (refs12.map h)),
    AdaptiveCircuit.run_seq, fB.loadProg_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step678_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step4_8_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs1 : List (Fin start))
    (h : Fin start → Bool) :
    ((step4_8 start refs1).instantiate read h).run = (step4_8Src read (refs1.map h)).run := by
  rw [step4_8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step5678Src read o) read
      (fun cursor rs hh => step5678_run read cursor rs hh)]
  rfl

theorem step3_8_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs1 : List (Fin start))
    (h : Fin start → Bool) :
    ((step3_8 start refs1).instantiate read h).run = (step3_8Src read (refs1.map h)).run := by
  rw [step3_8, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step4_8Src read (refs1.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step4_8_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step2_8_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((step2_8 start).instantiate read h).run = (step2_8Src read).run := by
  rw [step2_8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step3_8Src read o) read
      (fun cursor rs hh => step3_8_run read cursor rs hh)]
  simp only [List.map_nil, List.nil_append]; rfl

theorem twoPass_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((twoPassProg start).instantiate read h).run = (twoPassSrc read).run := by
  rw [twoPassProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun hh => step2_8_run read _ hh),
    AdaptiveCircuit.run_seq, fA.loadProg_run, ← AdaptiveCircuit.run_seq]
  rfl

theorem hot8_inj : Function.Injective hot8 := fun i j he => by
  apply Fin.ext; simp only [hot8] at he; dsimp only [Wire] at he; omega

theorem low8_ne_hot8 (i : Fin 8) (j : Fin 256) : WideBank8.low8 i ≠ hot8 j := by
  have hi := i.isLt; simp only [WideBank8.low8, hot8]; dsimp only [Wire]; omega

theorem hot8_disj : (MeasuredClear.hotBank8 hot8).Disjoint
    (windowRoot :: tree8.indexWires.dedup ++ WideBank8.Fast16.bank15.hp) := by
  apply List.disjoint_left.mpr
  intro w hw hm
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  have hi := i.isLt
  rw [tree8, WideBank8.Fast16.bank15_ok.index] at hm
  simp only [hot8, windowRoot, WideBank8.Fast16.bank15, WideBank8.Fast16.high,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hm
  dsimp only [Wire] at *; omega

theorem scratch8_not_tree : scratch8 ∉ windowRoot :: tree8.indexWires.dedup ++ WideBank8.Fast16.bank15.hp := by
  rw [tree8, WideBank8.Fast16.bank15_ok.index]
  simp only [scratch8, windowRoot, WideBank8.Fast16.bank15, WideBank8.Fast16.high,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire]; omega

theorem scratch8_not_hot : scratch8 ∉ MeasuredClear.hotBank8 hot8 := by
  intro hm; obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp only [scratch8, hot8] at hi; dsimp only [Wire] at hi; omega

theorem hot8_in_pairExtra (i : Fin 256) : hot8 i ∈ pairExtraWires := by
  apply List.mem_append_left
  rw [scrPairWires_explicit]
  have hi := i.isLt
  simp only [hot8, List.mem_append, List.mem_cons, List.mem_range'_1, List.mem_singleton]
  dsimp only [Wire, ECDSAAdd.Wire]; omega

theorem twoPass_tCount (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((twoPassProg start).instantiate read h).tCount =
      7 * (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 247)) := by
  have h8 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step8 c rs).instantiate read hh).tCount = 7 * (255 + 247) := by
    rw [step8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => by
      rw [castFinish_instantiate, MeasuredClear.fixupProgram_tCount8 _ _ _ _ _ _ _ _ tree8_layout, tree8_nodes])]
  have h78 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step78 c rs).instantiate read hh).tCount = 7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247) := by
    rw [step78, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h8 _ _ h'), literalFixed_tCount]
  have h678 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step678 c rs).instantiate read hh).tCount = 7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247) := by
    rw [step678, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h78 cur rs' h')]
  have h5678 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step5678 c rs).instantiate read hh).tCount =
        7 * (32767 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247)) := by
    rw [step5678, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h678 _ _ h'),
      fB.loadProg_tCount read fB_geo]
    have hbl : fB.selBits.length = 15 := by decide
    have hpl : fB.ports.length = 513 := pp16_length
    rw [hbl, hpl, show 2 ^ 15 - 1 = 32767 from rfl]
  have h48 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step4_8 c rs).instantiate read hh).tCount =
        7 * (32767 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247)) := by
    rw [step4_8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h5678 cur rs' h')]
  have h38 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step3_8 c rs).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount shortNorm +
          (7 * (32767 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247))) := by
    rw [step3_8, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h48 _ _ h'), literalFixed_tCount]
  have h28 (c : Nat) (hh : Fin c → Bool) :
      ((step2_8 c).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount shortNorm +
          (7 * (32767 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247))) := by
    rw [step2_8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h38 cur rs' h')]
  rw [twoPassProg, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h28 _ h'),
    fA.loadProg_tCount read fA_geo]
  have hbl : fA.selBits.length = 14 := by decide
  have hpl : fA.ports.length = 258 := sp16_length
  rw [hbl, hpl, show 2 ^ 14 - 1 = 16383 from rfl, show 3 * 258 = 774 from rfl]
  exact twoPass_tcount_arith 16383 774 (ECDSAAdd.toffoliCount shortNorm) 32767 513 (ECDSAAdd.toffoliCount tailNorm) (255 + 247)

theorem twoPass_residue (start : Nat) : AndGadget.residue (twoPassProg start) = 0 := by
  have h8 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step8 c rs) = 0 := by
    rw [step8, AndGadget.residue_cast]
    exact MeasuredClear.measureThen_residue _ (fun _ _ => by rw [AndGadget.residue_cast]; exact MeasuredClear.fixupProgram_residue8 _ _ _ _ _ _ _ _) _ _ _
  have h78 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step78 c rs) = 0 := by
    rw [step78, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast,
      WEXCredit.literal_residue, h8]
  have h678 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step678 c rs) = 0 := by
    rw [step678, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h78 _ _ _
  have h5678 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step5678 c rs) = 0 := by
    rw [step5678, AndGadget.residue_cast, AndGadget.residue_append, fB.loadProg_residue, h678]
  have h48 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step4_8 c rs) = 0 := by
    rw [step4_8, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h5678 _ _ _
  have h38 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step3_8 c rs) = 0 := by
    rw [step3_8, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast,
      WEXCredit.literal_residue, h48]
  have h28 (c : Nat) : AndGadget.residue (step2_8 c) = 0 := by
    rw [step2_8, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h38 _ _ _
  rw [twoPassProg, AndGadget.residue_cast, AndGadget.residue_append, fA.loadProg_residue, h28]

theorem twoPass_wellFormed (start : Nat) : (twoPassProg start).WellFormed := by
  have h8 (c : Nat) (rs : List (Fin c)) : (step8 c rs).WellFormed := by
    rw [step8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := fixRec8) _ (fun _ _ => by
      rw [castFinish_wellFormed]
      exact MeasuredClear.fixupProgram_wellFormed8 _ _ _ _ _ _ _ _ tree8_layout hot8_inj low8_ne_hot8
        scratch8_not_tree scratch8_not_hot) _ _ _
  have h78 (c : Nat) (rs : List (Fin c)) : (step78 c rs).WellFormed := by
    rw [step78, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ tailNorm_valid _) (h8 _ _)
  have h678 (c : Nat) (rs : List (Fin c)) : (step678 c rs).WellFormed := by
    rw [step678, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mTail + (513 + fixRec8)) (fun cur rs' => step78 cur rs') h78 gB c rs
  have h5678 (c : Nat) (rs : List (Fin c)) : (step5678 c rs).WellFormed := by
    rw [step5678, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (fB.loadProg_wellFormed fB_geo _) (h678 _ _)
  have h48 (c : Nat) (rs : List (Fin c)) : (step4_8 c rs).WellFormed := by
    rw [step4_8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := 32767 + (513 + (mTail + (513 + fixRec8)))) (fun cur rs' => step5678 cur rs') h5678 shortWires c rs
  have h38 (c : Nat) (rs : List (Fin c)) : (step3_8 c rs).WellFormed := by
    rw [step3_8, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ shortNorm_valid _) (h48 _ _)
  have h28 (c : Nat) : (step2_8 c).WellFormed := by
    rw [step2_8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mShort + (258 + (32767 + (513 + (mTail + (513 + fixRec8)))))) (fun cur rs' => step3_8 cur rs') h38 garbA c List.nil
  rw [twoPassProg, castFinish_wellFormed]
  exact straight_append_wellFormed _ _ (fA.loadProg_wellFormed fA_geo _) (h28 _)

theorem twoPass_support (start : Nat) :
    ChallengeMigration.straightWires (twoPassProg start) ⊆ WideBank8.Fast16.Tight.support := by
  have hcov := WideBank8.Fast16.Tight.old_cover
  have hroot : windowRoot ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.root_new
  have h855 : (855 : Wire) ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new ⟨0, by decide⟩
  have h856 : (856 : Wire) ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new ⟨1, by decide⟩
  have hsA : fA.selBits ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selBits_new
  have hpA : fA.selPaths ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selPaths_new
  have hsB : fB.selBits ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selBits1_new
  have hpB : fB.selPaths ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selPaths1_new
  have hlow : ∀ i : Fin 8, WideBank8.low8 i ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new
  have hhot : ∀ i : Fin 256, hot8 i ∈ WideBank8.Fast16.Tight.support := fun i =>
    hcov (pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_left _ (hot8_in_pairExtra i))))
  have hscr : scratch8 ∈ WideBank8.Fast16.Tight.support :=
    hcov (pool_band_in_newH7 (by rw [scratch8]; left; dsimp only [Wire]; omega))
  have htree : tree8.indexWires ⊆ WideBank8.Fast16.Tight.support := by
    intro w hw; rw [tree8] at hw
    have h1 : w ∈ WideBank8.Fast16.bank15.high := by
      have := List.mem_dedup.mpr hw; rw [WideBank8.Fast16.bank15_ok.index] at this; exact this
    exact WideBank8.Fast16.Tight.high_new h1
  have hhp : WideBank8.Fast16.bank15.hp ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    WideBank8.Fast16.Tight.bank_new (WideBank8.Fast16.bank15_ok.sub w hw)
  have hregA : portTargets fA.ports ++ fA.garb ⊆ WideBank8.Fast16.Tight.support := fun w hw => by
    rw [fA, sp16_targets] at hw; exact hcov (pool_band_in_newH7 (mem_short_garbA hw))
  have hregB : portTargets fB.ports ++ fB.g1 ⊆ WideBank8.Fast16.Tight.support := fun w hw => by
    rw [fB, pp16_targets] at hw; exact hcov (pool_band_in_newH7 (mem_pairExtra_gB hw))
  have hgarbA : garbA ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (pool_band_in_newH7 (mem_short_garbA (List.mem_append_right _ hw)))
  have hshortW : shortWires ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (pool_band_in_newH7 (mem_short_garbA (List.mem_append_left _ hw)))
  have hgB : gB ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_right _ hw)))
  have hpairW : pairExtraWires ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_left _ hw)))
  have hshortN : ECDSAAdd.wires shortNorm ⊆ WideBank8.Fast16.Tight.support.toFinset := fun w hw =>
    List.mem_toFinset.mpr (hcov (List.mem_toFinset.mp (shortPart_wires_newH7 hw)))
  have htailN : ECDSAAdd.wires tailNorm ⊆ WideBank8.Fast16.Tight.support.toFinset := fun w hw =>
    List.mem_toFinset.mpr (hcov (List.mem_toFinset.mp (tailPart_wires_newH7 hw)))
  have h8 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step8 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun _ _ => by
      rw [MeasuredClear.static_cast]
      exact MeasuredClear.fixupProgram_within8 _ _ _ _ _ _ _ _ _ hroot hscr hlow hhot htree hhp) _ _ _ hpairW
  have h78 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step78 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step78, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ htailN _, h8 _ _⟩
  have h678 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step678 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step678, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h78 cur rs') _ _ _ hgB
  have h5678 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step5678 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step5678, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨fB.loadProg_support fB_geo _ hroot hroot h855 hsB hpB hregB _, h678 _ _⟩
  have h48 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step4_8 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step4_8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h5678 cur rs') _ _ _ hshortW
  have h38 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step3_8 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step3_8, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ hshortN _, h48 _ _⟩
  have h28 (c : Nat) :
      ChallengeMigration.straightWires (step2_8 c) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step2_8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h38 cur rs') _ _ _ hgarbA
  rw [twoPassProg, support_cast, straightWires_append]
  exact List.append_subset.mpr ⟨fA.loadProg_support fA_geo _ hroot hroot h855 h856 hsA hpA hregA _, h28 _⟩

theorem twoPass_slots (start : Nat) :
    (twoPassProg start).gateSlots ≤
      4 * ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) + 610000000 := by
  have h8 (c : Nat) (rs : List (Fin c)) :
      (step8 c rs).gateSlots ≤ 1024 * allData.length * 256 + 10 * 255 + 2291 := by
    rw [step8, castFinish_gateSlots, MeasuredClear.measureThen_slots _
      (fun k => 1024 * min allData.length k * 256 + 10 * 255 + 2291)
      (fun cur rs' => by
        rw [castFinish_gateSlots, MeasuredClear.fixupProgram_slots8 _ _ _ _ _ _ _ _ tree8_layout,
          tree8_leaves, tree8_nodes])]
    have hmin : min allData.length (rs.length + pairExtraWires.length) ≤ allData.length := Nat.min_le_left _ _
    omega
  have h78 (c : Nat) (rs : List (Fin c)) :
      (step78 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291) := by
    rw [step78, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 65536) tailNorm
    have h8' := h8 (c + mTail) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at hl ⊢
    omega
  have h678 (c : Nat) (rs : List (Fin c)) :
      (step678 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291) := by
    rw [step678, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step78 cur rs') _ h78 gB c rs
  have h5678 (c : Nat) (rs : List (Fin c)) :
      (step5678 c rs).gateSlots ≤ (2 ^ 15 * (2 * 513) + 10 * (2 ^ 15 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291)) := by
    rw [step5678, castFinish_gateSlots, Straight.gateSlots_append]
    have hb := fB.loadProg_slots fB_geo c
    have hbl : fB.selBits.length = 15 := by decide
    have hpl : fB.ports.length = 513 := pp16_length
    rw [hbl, hpl] at hb
    have h6 := h678 (c + codeRecords fB.selBits fB.selPaths windowRoot fB.selCode) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at h6 ⊢
    omega
  have h48 (c : Nat) (rs : List (Fin c)) :
      (step4_8 c rs).gateSlots ≤ (2 ^ 15 * (2 * 513) + 10 * (2 ^ 15 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291)) := by
    rw [step4_8, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step5678 cur rs') _ h5678 shortWires c rs
  have h38 (c : Nat) (rs : List (Fin c)) :
      (step3_8 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots shortNorm +
        ((2 ^ 15 * (2 * 513) + 10 * (2 ^ 15 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291))) := by
    rw [step3_8, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 65536) shortNorm
    have h4 := h48 (c + mShort) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots shortNorm = gS at hl ⊢
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at h4 ⊢
    omega
  have h28 (c : Nat) :
      (step2_8 c).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots shortNorm +
        ((2 ^ 15 * (2 * 513) + 10 * (2 ^ 15 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291))) := by
    rw [step2_8, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step3_8 cur rs') _ h38 garbA c List.nil
  rw [twoPassProg, castFinish_gateSlots, Straight.gateSlots_append]
  have ha := fA.loadProg_slots fA_geo start
  have hbl : fA.selBits.length = 14 := by decide
  have hpl : fA.ports.length = 258 := sp16_length
  rw [hbl, hpl] at ha
  have h2 := h28 (start + codeRecords fA.selBits fA.selPaths windowRoot fA.selCode)
  have hns := norm_slots_split
  rw [allData_len] at h2
  generalize ECDSAAdd.Challenge.gateSlots shortNorm = gsS at h2 hns
  generalize ECDSAAdd.Challenge.gateSlots tailNorm = gsT at h2 hns
  generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) = gsA at hns ⊢
  omega

theorem twoPass_sim (read : ConstantBit 65536 → Bool) :
    ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
        ∀ a (st : ECDSAAdd.State), AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          Clean WideBank8.Fast16.pathBank st.basis →
          Clean streamLayout.dialogPool st.basis →
          (∀ m', Clean scrAllWires
            (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis) →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m st))
      (twoPassSrc read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hsplit : ∀ s : BasisState, 256 * tree8.routeLabel s + MeasuredClear.hotAddress8 WideBank8.low8 s =
      tableAddressValue WideBank8.Fast16.windowBits s := WideBank8.Fast16.bank15_ok.split
  have hbits_no_pe : ∀ w ∈ WideBank8.Fast16.windowBits, w ∉ pairExtraWires := fun w hw hm => by
    have hb := mem_pairExtra hm
    simp only [WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hhp_no_pe : ∀ w ∈ WideBank8.Fast16.bank15.hp, w ∉ pairExtraWires := fun w hw hm => by
    have hb := mem_pairExtra hm
    simp only [WideBank8.Fast16.bank15, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hroot_no_pe : windowRoot ∉ pairExtraWires := windowRoot_not_pairExtra
  have hsite1_win16 : ∀ w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank,
      w ∉ ECDSAAdd.wires site1Arith := fun w hw hm => by
    have hgeo : PathShare.UnitGeoP WideBank8.Fast16.bank15 (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩) :=
      WideBank8.Row16.geometry (.std (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩))) (by
        unfold WideBank8.Row16.code
        apply List.mem_append_left
        refine List.mem_map.mpr ⟨.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩), ?_, rfl⟩
        rw [WideBank8.Row16.headF]
        apply List.mem_append_left
        rw [WEXUnlookup.rowPre3]; simp [toBlock2])
    exact hgeo.placed (WInstr.literal site1Arith)
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) w hw hm
  have htail_avoid_window : ∀ w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank,
      w ∉ ECDSAAdd.wires tailPart := fun w hw hm => hsite1_win16 w hw (tailPart_wires_sub hm)
  have hshort_avoid_window : ∀ w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank,
      w ∉ ECDSAAdd.wires shortPart := fun w hw hm => hsite1_win16 w hw (shortPart_wires_sub hm)
  have h8_sim (o1 o2 o3 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) (ho3 : o3.length = 513) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∀ a (next : ECDSAAdd.State) (u1 u2 u3 : BasisState),
          tableAddressValue WideBank8.Fast16.windowBits next.basis = a →
          next.basis windowRoot = true →
          Clean WideBank8.Fast16.bank15.hp next.basis →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, next.basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet next) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
              Bridge.signedKet ⟨next.phase, clearRegister pairExtraWires next.basis⟩)
        (step8Src read (o1 ++ o2 ++ o3)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step8Src
    apply MeasuredClear.measureResetThen_sim pairExtraWires _
      (fun o4 => BranchCoherentOn (MeasuredClear.basisIdeal id
        (MeasuredClear.fixupFactor8 allData ((o1 ++ o2 ++ o3) ++ o4) read WideBank8.low8 hot8 tree8 windowRoot))
        (fun s => MeasuredClear.HotClean8 hot8 s ∧ Clean WideBank8.Fast16.bank15.hp s))
    · intro o4 _
      exact MeasuredClear.fixupSource_coherent8 allData _ read WideBank8.low8 hot8 tree8 windowRoot scratch8
        WideBank8.Fast16.bank15.hp tree8_layout hot8_inj low8_ne_hot8 hot8_disj scratch8_not_tree scratch8_not_hot
    · intro o4 ho4 b c hb a next u1 u2 u3 haddr hroot hhp hu1 hu2 hu3 hu4
      have hk := xResetRegisterKraus_ket pairExtraWires o4 next.basis ho4 pairExtra_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho4] at hk
      set t := clearRegister pairExtraWires next.basis with ht
      have hfr (w : Wire) (hw : w ∉ pairExtraWires) : t w = next.basis w :=
        MeasuredClear.clearRegister_frame _ _ _ hw
      have hhot : MeasuredClear.HotClean8 hot8 t := fun i => clearRegister_clean _ _ _ (hot8_in_pairExtra i)
      have hvalid : MeasuredClear.HotClean8 hot8 t ∧ Clean WideBank8.Fast16.bank15.hp t :=
        ⟨hhot, fun w hw => by rw [hfr w (hhp_no_pe w hw)]; exact hhp w hw⟩
      have haddr_t : tableAddressValue WideBank8.Fast16.windowBits t = a :=
        (WEX.tableAddressValue_congr _ _ _ (fun w hw => hfr w (hbits_no_pe w hw))).trans haddr
      have hroot_t : t windowRoot = true := (hfr _ hroot_no_pe).trans hroot
      have hfac : MeasuredClear.fixupFactor8 allData ((o1 ++ o2 ++ o3) ++ o4) read WideBank8.low8 hot8 tree8 windowRoot t =
          registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 *
            registerXPhase gB o3 u3 * registerXPhase pairExtraWires o4 next.basis := by
        have hlen12 : (o1 ++ o2).length = (d1 ++ d2).length := by simp [ho1, ho2, d1_len, d2_len]
        have hlen123 : (o1 ++ o2 ++ o3).length = (d1 ++ d2 ++ d3).length := by
          simp [ho1, ho2, ho3, d1_len, d2_len, d3_len]
        rw [allData, MeasuredClear.fixupFactor8_append _ _ _ _ hlen123,
          MeasuredClear.fixupFactor8_append _ _ _ _ hlen12,
          MeasuredClear.fixupFactor8_append _ _ _ _ (by rw [ho1, d1_len])]
        have hf1 : MeasuredClear.fixupFactor8 d1 o1 read WideBank8.low8 hot8 tree8 windowRoot t =
            registerXPhase garbA o1 u1 := by
          rw [← d1_targets]
          exact MeasuredClear.fixupFactor8_loaded d1 o1 read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            hot8_inj low8_ne_hot8 hot8_disj t u1 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu1 q hq)
        have hf2 : MeasuredClear.fixupFactor8 d2 o2 read WideBank8.low8 hot8 tree8 windowRoot t =
            registerXPhase shortWires o2 u2 := by
          rw [← d2_targets]
          exact MeasuredClear.fixupFactor8_loaded d2 o2 read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            hot8_inj low8_ne_hot8 hot8_disj t u2 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu2 q hq)
        have hf3 : MeasuredClear.fixupFactor8 d3 o3 read WideBank8.low8 hot8 tree8 windowRoot t =
            registerXPhase gB o3 u3 := by
          rw [← d3_targets]
          exact MeasuredClear.fixupFactor8_loaded d3 o3 read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            hot8_inj low8_ne_hot8 hot8_disj t u3 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu3 q hq)
        have hf4 : MeasuredClear.fixupFactor8 d4 o4 read WideBank8.low8 hot8 tree8 windowRoot t =
            registerXPhase pairExtraWires o4 next.basis := by
          rw [← d4_targets]
          exact MeasuredClear.fixupFactor8_loaded d4 o4 read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            hot8_inj low8_ne_hot8 hot8_disj t next.basis hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu4 q hq)
        rw [hf1, hf2, hf3, hf4]
      have hsq := MeasuredClear.registerXPhase_square pairExtraWires o4 next.basis
      change b.kraus (xResetRegisterKraus pairExtraWires o4 (Bridge.signedKet next)) = _
      simp only [Bridge.signedKet, map_smul, hk, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac, smul_smul, ← ht]
      exact congrArg (· • ket t) (phase_cancel_base next.phase (registerXResetMagnitude pairExtraWires.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 u2) (registerXPhase gB o3 u3)
        (registerXPhase pairExtraWires o4 next.basis) hsq)
  have h78_sim (o1 o2 o3 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) (ho3 : o3.length = 513) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sL2 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
            AddrValid WideBank8.Fast16.windowBits windowRoot a sL2 →
            Clean WideBank8.Fast16.pathBank sL2.basis →
            Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sL2) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step78Src read (o1 ++ o2 ++ o3)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation tailNorm
    obtain ⟨c2, a2, m2⟩ := h8_sim o1 o2 o3 ho1 ho2 ho3
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step78Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    refine ⟨b₁.history, by rw [hb₁.1, tailNorm_meas], ?_⟩
    intro a sL2 u1 u2 u3 ha hpath hclOut hu1 hu2 hu3
    set sB1 := ECDSAAdd.run tailPart b₁.history sL2 with hsB1
    have hnorm : ECDSAAdd.run tailNorm b₁.history sL2 = sB1 := by
      rw [tailNorm]; exact ECDSAAdd.Baselines.normalize_run tailPart b₁.history sL2
    have hrootB : sB1.basis windowRoot = true := by
      rw [hsB1, run_outside_basis tailPart b₁.history sL2 windowRoot tailPart_root]; exact ha.2
    have haddrB : tableAddressValue WideBank8.Fast16.windowBits sB1.basis = a := by
      rw [← ha.1]; apply WEX.tableAddressValue_congr
      intro w hw; rw [hsB1, run_outside_basis tailPart b₁.history sL2 w (htail_avoid_window w (by simp [hw]))]
    have hhpB : Clean WideBank8.Fast16.bank15.hp sB1.basis := fun w hw => by
      have hw' : w ∈ WideBank8.Fast16.pathBank := WideBank8.Fast16.bank15_ok.sub w hw
      rw [hsB1, run_outside_basis tailPart b₁.history sL2 w (htail_avoid_window w (by simp [hw']))]; exact hpath w hw'
    have hpp_nd : (portTargets pp16).Nodup := by rw [pp16_targets]; exact pairExtra_nodup
    have hclOut' : Clean (portTargets pp16)
        (tableXorState (portMask read pp16 a) (sB1.basis windowRoot) sB1.basis) := by
      rw [pp16_targets, hrootB]; exact hclOut
    have hloadedB : ∀ q ∈ d4, sB1.basis q.target = decide (read (q.ref a) = q.value) :=
      clearData_loaded_of_clean read pp16 a windowRoot sB1.basis hrootB hpp_nd
        (by rw [pp16_targets]; exact hclOut)
    have hclr : clearRegister pairExtraWires sB1.basis =
        tableXorState (portMask read pp16 a) true sB1.basis := by
      have h0 := clear_eq_unload read pp16 a windowRoot sB1.basis hclOut'
      rw [pp16_targets, hrootB] at h0; exact h0
    change b₂.kraus (b₁.kraus (Bridge.signedKet sL2)) = _
    rw [hb₁.2, hnorm, map_smul, hb₂ a sB1 u1 u2 u3 haddrB hrootB hhpB hu1 hu2 hu3 hloadedB, hclr, smul_smul]
    exact congrArg (· • _) (by simp only [mul_assoc])
  have h68_sim (o1 o2 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sB0 : ECDSAAdd.State) (u1 u2 : BasisState),
            let sL2 : ECDSAAdd.State := ⟨sB0.phase, clearRegister gB sB0.basis⟩
            AddrValid WideBank8.Fast16.windowBits windowRoot a sL2 →
            Clean WideBank8.Fast16.pathBank sL2.basis →
            Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, sB0.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sB0) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step678Src read (o1 ++ o2)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step678Src
    apply MeasuredClear.measureResetThen_sim gB _
      (fun o3 b c => ∃ mB : List Bool, mB.length = mTail ∧
        ∀ a (sL2 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
          AddrValid WideBank8.Fast16.windowBits windowRoot a sL2 →
          Clean WideBank8.Fast16.pathBank sL2.basis →
          Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sL2) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
              Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
    · intro o3 ho3
      exact h78_sim o1 o2 o3 ho1 ho2 (by rw [gB_len] at ho3; exact ho3)
    · intro o3 ho3 b c hb
      obtain ⟨mB, hmB, hb⟩ := hb
      refine ⟨mB, hmB, ?_⟩
      intro a sB0 u1 u2 sL2 ha hpath hclOut hu1 hu2 hu3
      have hk := xResetRegisterKraus_ket gB o3 sB0.basis ho3 gB_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho3] at hk
      have hsq := MeasuredClear.registerXPhase_square gB o3 sB0.basis
      change b.kraus (xResetRegisterKraus gB o3 (Bridge.signedKet sB0)) = _
      have hstep := hb a sL2 u1 u2 sB0.basis ha hpath hclOut hu1 hu2 hu3
      rw [show Bridge.signedKet sB0 = (if sB0.phase then (-1 : ℂ) else 1) • ket sB0.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister gB sB0.basis)) =
          (if sB0.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet sL2) := by
        simp only [Bridge.signedKet, sL2, map_smul, smul_smul]
        cases sB0.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step2 sB0.phase (registerXResetMagnitude gB.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 u2)
        (registerXPhase gB o3 sB0.basis) hsq)
  have h58_sim (o1 o2 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sMid : ECDSAAdd.State) (u1 u2 : BasisState),
            let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp16 a) true sMid.basis⟩
            AddrValid WideBank8.Fast16.windowBits windowRoot a sMid →
            Clean WideBank8.Fast16.pathBank sMid.basis →
            Clean (pairExtraWires ++ gB) sMid.basis →
            Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sMid) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step5678Src read (o1 ++ o2)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := fB.load_sim read fB_geo
    obtain ⟨c2, a2, m2⟩ := h68_sim o1 o2 ho1 ho2
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step5678Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨mB, hmB, hb₂⟩ := hb₂
    refine ⟨mB, hmB, ?_⟩
    intro a sMid u1 u2 sL2 ha hpath hclB hclOut hu1 hu2
    have hclB' : Clean (portTargets fB.ports ++ fB.g1) sMid.basis := by
      change Clean (portTargets pp16 ++ gB) sMid.basis
      rw [pp16_targets]; exact hclB
    have hst := fB.load_state read fB_geo a sMid ⟨hpath, ha.1, ha.2⟩ hclB'
    set sB0 := ECDSAAdd.run fB.swapNet List.nil
      (ECDSAAdd.run ((specialize fB.selCode (tableAddressValue fB.selBits sMid.basis)).instantiate read) List.nil sMid) with hsB0
    have hsL2_eq : (⟨sB0.phase, clearRegister gB sB0.basis⟩ : ECDSAAdd.State) = sL2 := by
      refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
      have h2 := hst.2.2.2; change clearRegister gB sB0.basis = tableXorState (portMask read pp16 a) (sMid.basis windowRoot) sMid.basis at h2
      rw [ha.2] at h2; exact h2
    have hfrB : ∀ w, w ∉ pairExtraWires → w ∉ gB → sL2.basis w = sMid.basis w := fun w h1 h2 => by
      dsimp only [sL2]; exact tableXorState_outside _ _ _ _ (fun hm => h1 (by rw [← pp16_targets]; exact tableBitsMask_subset _ _ hm))
    have haL2 : AddrValid WideBank8.Fast16.windowBits windowRoot a sL2 := by
      refine ⟨?_, ?_⟩
      · rw [← ha.1]; apply WEX.tableAddressValue_congr; intro w hw
        exact hfrB w (hbits_no_pe w hw) (fun hm => by
          rw [mem_gB] at hm
          simp only [WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            List.mem_range'_1] at hw
          dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      · rw [hfrB windowRoot hroot_no_pe (fun hm => by rw [mem_gB] at hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega)]; exact ha.2
    have hpathL2 : Clean WideBank8.Fast16.pathBank sL2.basis := fun w hw => by
      have h1 : w ∉ pairExtraWires := fun hm => by
        have := mem_pairExtra hm
        simp only [WideBank8.Fast16.pathBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_range'_1] at hw
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have h2 : w ∉ gB := fun hm => by
        rw [mem_gB] at hm
        simp only [WideBank8.Fast16.pathBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_range'_1] at hw
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      rw [hfrB w h1 h2]; exact hpath w hw
    have hu3 : ∀ q ∈ d3, sB0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
      have h1 := hst.2.2.1 q hq
      change sB0.basis q.target = (sMid.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
      rw [ha.2, Bool.true_and] at h1; exact h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet sMid)) = _
    rw [hb₁ a sMid ⟨hpath, ha.1, ha.2⟩ hclB', map_smul]
    have hstep := hb₂ a sB0 u1 u2 (by rw [hsL2_eq]; exact haL2) (by rw [hsL2_eq]; exact hpathL2)
      (by rw [hsL2_eq]; exact hclOut) hu1 hu2 hu3
    rw [hsL2_eq] at hstep
    rw [hstep, smul_smul]
    exact congrArg (· • _) (by simp only [mul_assoc])
  have h48_sim (o1 : List Bool) (ho1 : o1.length = 774) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sA1 : ECDSAAdd.State) (u1 : BasisState),
            let sMid : ECDSAAdd.State := ⟨sA1.phase, clearRegister shortWires sA1.basis⟩
            let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp16 a) true sMid.basis⟩
            AddrValid WideBank8.Fast16.windowBits windowRoot a sMid →
            Clean WideBank8.Fast16.pathBank sMid.basis →
            Clean (pairExtraWires ++ gB) sMid.basis →
            Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, sA1.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sA1) =
              (c * registerXPhase garbA o1 u1) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step4_8Src read o1).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step4_8Src
    apply MeasuredClear.measureResetThen_sim shortWires _
      (fun o2 b c => ∃ mB : List Bool, mB.length = mTail ∧
        ∀ a (sMid : ECDSAAdd.State) (u1 u2 : BasisState),
          let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp16 a) true sMid.basis⟩
          AddrValid WideBank8.Fast16.windowBits windowRoot a sMid →
          Clean WideBank8.Fast16.pathBank sMid.basis →
          Clean (pairExtraWires ++ gB) sMid.basis →
          Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sMid) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
              Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
    · intro o2 ho2
      exact h58_sim o1 o2 ho1 (by rw [shortWires_length] at ho2; exact ho2)
    · intro o2 ho2 b c hb
      obtain ⟨mB, hmB, hb⟩ := hb
      refine ⟨mB, hmB, ?_⟩
      intro a sA1 u1 sMid sL2 ha hpath hclB hclOut hu1 hu2
      have hk := xResetRegisterKraus_ket shortWires o2 sA1.basis ho2 scrShortWires_nd
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho2] at hk
      have hsq := MeasuredClear.registerXPhase_square shortWires o2 sA1.basis
      change b.kraus (xResetRegisterKraus shortWires o2 (Bridge.signedKet sA1)) = _
      have hstep := hb a sMid u1 sA1.basis ha hpath hclB hclOut hu1 hu2
      rw [show Bridge.signedKet sA1 = (if sA1.phase then (-1 : ℂ) else 1) • ket sA1.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister shortWires sA1.basis)) =
          (if sA1.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet sMid) := by
        simp only [Bridge.signedKet, sMid, map_smul, smul_smul]
        cases sA1.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step1 sA1.phase (registerXResetMagnitude shortWires.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 sA1.basis) hsq)
  have h38_sim (o1 : List Bool) (ho1 : o1.length = 774) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
          ∀ a (st : ECDSAAdd.State) (u1 : BasisState),
            let sL1 : ECDSAAdd.State := ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩
            AddrValid WideBank8.Fast16.windowBits windowRoot a st →
            Clean WideBank8.Fast16.pathBank st.basis →
            Clean streamLayout.dialogPool st.basis →
            (∀ m', Clean scrAllWires
              (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sL1) =
              (c * registerXPhase garbA o1 u1) •
                Bridge.signedKet (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m st))
        (step3_8Src read o1).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation shortNorm
    obtain ⟨c2, a2, m2⟩ := h48_sim o1 ho1
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step3_8Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨mB, hmB, hb₂⟩ := hb₂
    let mA := b₁.history
    have hmA : mA.length = mShort := by rw [hb₁.1, shortNorm_meas]
    let mPerm := mB.take (ECDSAAdd.measurementCount pairPart) ++ mA ++ mB.drop (ECDSAAdd.measurementCount pairPart)
    have hmc_len : mPerm.length = ECDSAAdd.measurementCount site1Arith := by
      have htail_mc : ECDSAAdd.measurementCount pairPart ≤ mTail := by
        rw [mTail, tailPart, ECDSAAdd.measurementCount_append]
        exact Nat.le_add_right _ _
      have hcs : mShort + mTail = ECDSAAdd.measurementCount site1Arith := by
        rw [mShort, mTail]; exact site1_counts_split.2.1
      dsimp only [mPerm]
      rw [List.length_append, List.length_append, List.length_take, List.length_drop, hmA, hmB]
      exact mPerm_len_arith mShort mTail (ECDSAAdd.measurementCount pairPart) (ECDSAAdd.measurementCount site1Arith) htail_mc hcs
    refine ⟨mPerm, hmc_len, ?_⟩
    intro a st u1 sL1 ha hpath hpool hsafe hu1
    have hclean258 : Clean (streamLayout.dialogPool.take 258) st.basis := fun w hw => hpool w (List.mem_of_mem_take hw)
    have hclean258_L1 : Clean (streamLayout.dialogPool.take 258) sL1.basis := fun w hw => by
      dsimp only [sL1]
      rw [tableXorState_outside _ _ _ _ (fun hm => by
        have h1 : w ∈ shortWires := by simpa [sp16_targets] using tableBitsMask_subset _ _ hm
        have h2 := shortWires_bounds w h1
        rw [mem_pool_take 258 (by decide)] at hw; dsimp only [Wire, ECDSAAdd.Wire] at hw h2; omega)]
      exact hclean258 w hw
    have hnorm : ECDSAAdd.run shortNorm mA sL1 = ECDSAAdd.run shortPart mA sL1 := by
      rw [shortNorm]; exact ECDSAAdd.Baselines.normalize_run shortPart mA sL1
    have hsA1_form := shortPart_run sL1 mA hclean258_L1
    generalize hsA1 : ECDSAAdd.run shortPart mA sL1 = sA1 at hnorm hsA1_form
    have htwo := site1_twoPass_run_free read r16 a st sA1 mA mB
      (by rw [← mShort]; exact hmA) (by rw [← mTail]; exact hmB) ha.2 hclean258 hsA1.symm
    have hne_eq (w : Wire) (hne : w ≠ streamLayout.core.equalNegY) : sA1.basis w = sL1.basis w := by
      rw [hsA1_form]; simp [ECDSAAdd.writeBit, Function.update, hne]
    have hsp_nd : (portTargets sp16).Nodup := by rw [sp16_targets]; exact scrShortWires_nd
    have hsA1_loaded : ∀ q ∈ d2, sA1.basis q.target = decide (read (q.ref a) = q.value) :=
      clearData_loaded_of_xor read sp16 a st.basis sA1.basis hsp_nd
        (fun w hw => by rw [sp16_targets] at hw; exact hpool w (pool_band_in_dialogPool (mem_short_garbA (List.mem_append_left _ hw))))
        (fun w hw => by
          rw [sp16_targets] at hw
          exact hne_eq w (fun e => scrShortWires_no_flags.2.2.2 (e ▸ hw)))
    have hmid_basis : clearRegister shortWires sA1.basis =
        tableXorState (portMask read sp16 a) true sA1.basis := by
      rw [← sp16_targets]
      exact clearRegister_eq_xor_of_loaded read sp16 a sA1.basis hsp_nd hsA1_loaded
    set sMid : ECDSAAdd.State := ⟨sA1.phase, clearRegister shortWires sA1.basis⟩
    set sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp16 a) true sMid.basis⟩
    have hmid_frame (w : Wire) (hw1 : w ∉ shortWires) (hw2 : w ≠ streamLayout.core.equalNegY) :
        sMid.basis w = st.basis w := by
      dsimp only [sMid]
      rw [MeasuredClear.clearRegister_frame shortWires sA1.basis w hw1, hne_eq w hw2]
      dsimp only [sL1]
      exact tableXorState_outside _ _ _ _ (fun hm => hw1 (by simpa [sp16_targets] using tableBitsMask_subset _ _ hm))
    have haMid : AddrValid WideBank8.Fast16.windowBits windowRoot a sMid := by
      refine ⟨?_, ?_⟩
      · rw [← ha.1]; apply WEX.tableAddressValue_congr; intro w hw
        exact hmid_frame w
          (fun hm => by
            have h1 := shortWires_bounds w hm
            simp only [WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
              List.mem_range'_1] at hw
            dsimp only [Wire, ECDSAAdd.Wire] at hw h1; omega)
          (fun e => by
            rw [e, sl_equalNegY] at hw
            simp only [WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
              List.mem_range'_1] at hw
            dsimp only [Wire, ECDSAAdd.Wire] at hw; omega)
      · rw [hmid_frame windowRoot windowRoot_not_short (by rw [sl_equalNegY]; decide)]; exact ha.2
    have hpathMid : Clean WideBank8.Fast16.pathBank sMid.basis := fun w hw => by
      rw [hmid_frame w
        (fun hm => by
          have h1 := shortWires_bounds w hm
          simp only [WideBank8.Fast16.pathBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            List.mem_range'_1] at hw
          dsimp only [Wire, ECDSAAdd.Wire] at hw h1; omega)
        (fun e => by
          rw [e, sl_equalNegY] at hw
          simp only [WideBank8.Fast16.pathBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            List.mem_range'_1] at hw
          dsimp only [Wire, ECDSAAdd.Wire] at hw; omega)]
      exact hpath w hw
    have hclMid : Clean (pairExtraWires ++ gB) sMid.basis := fun w hw => by
      by_cases hs : w ∈ shortWires
      · exact clearRegister_clean shortWires sA1.basis w hs
      · rw [hmid_frame w hs (fun e => by have h1 := mem_pairExtra_gB hw; rw [e, sl_equalNegY] at h1; dsimp only [Wire, ECDSAAdd.Wire] at h1; omega)]
        exact hpool w (pool_band_in_dialogPool (mem_pairExtra_gB hw))
    have hsOut_eq : (⟨(ECDSAAdd.run tailPart mB sL2).phase,
        tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run ((specialize site1_16.code a).instantiate read) mPerm st :=
      (twoPass_state_congr read sp16 pp16 a sA1 mB shortWires hmid_basis).trans htwo
    have hclOut : Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) := by
      intro w hw
      have h1 := hsafe mPerm w (by
        rcases List.mem_append.mp hw with h | h
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_right _ h)
      have h2 := congrArg (fun x => x.basis w) hsOut_eq
      exact h2.trans h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet sL1)) = _
    rw [hb₁.2, hnorm, map_smul, hb₂ a sA1 u1 haMid hpathMid hclMid hclOut hu1 hsA1_loaded, smul_smul, hsOut_eq]
    exact congrArg (· • _) (by simp only [mul_assoc])
  have h28_sim :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
          ∀ a (st sA0 : ECDSAAdd.State),
            (⟨sA0.phase, clearRegister garbA sA0.basis⟩ : ECDSAAdd.State) =
              ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩ →
            AddrValid WideBank8.Fast16.windowBits windowRoot a st →
            Clean WideBank8.Fast16.pathBank st.basis →
            Clean streamLayout.dialogPool st.basis →
            (∀ m', Clean scrAllWires
              (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis) →
            (∀ q ∈ d1, sA0.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sA0) =
              c • Bridge.signedKet (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m st))
        (step2_8Src read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step2_8Src
    apply MeasuredClear.measureResetThen_sim garbA _
      (fun o1 b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
        ∀ a (st : ECDSAAdd.State) (u1 : BasisState),
          let sL1 : ECDSAAdd.State := ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩
          AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          Clean WideBank8.Fast16.pathBank st.basis →
          Clean streamLayout.dialogPool st.basis →
          (∀ m', Clean scrAllWires
            (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sL1) =
            (c * registerXPhase garbA o1 u1) •
              Bridge.signedKet (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m st))
    · intro o1 ho1
      exact h38_sim o1 (by rw [garbA_len] at ho1; exact ho1)
    · intro o1 ho1 b c hb
      obtain ⟨m, hm, hb⟩ := hb
      refine ⟨m, hm, ?_⟩
      intro a st sA0 hsL1 ha hpath hpool hsafe hu1
      have hk := xResetRegisterKraus_ket garbA o1 sA0.basis ho1 garbA_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho1] at hk
      have hsq := MeasuredClear.registerXPhase_square garbA o1 sA0.basis
      change b.kraus (xResetRegisterKraus garbA o1 (Bridge.signedKet sA0)) = _
      have hstep := hb a st sA0.basis ha hpath hpool hsafe hu1
      have ⟨hph, hba⟩ := (ECDSAAdd.State.mk.injEq _ _ _ _).mp hsL1
      rw [show Bridge.signedKet sA0 = (if sA0.phase then (-1 : ℂ) else 1) • ket sA0.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister garbA sA0.basis)) =
          (if sA0.phase then (-1 : ℂ) else 1) •
            b.kraus (Bridge.signedKet ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩) := by
        rw [hba, hph]
        simp only [Bridge.signedKet, map_smul, smul_smul]
        cases st.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step0 sA0.phase (registerXResetMagnitude garbA.length) c
        (registerXPhase garbA o1 sA0.basis) hsq)
  obtain ⟨c1, a1, m1⟩ := fA.load_sim read fA_geo
  obtain ⟨c2, a2, m2⟩ := h28_sim
  refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
  rw [twoPassSrc, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a1 a2
  intro b₁ k₁ b₂ k₂ hb₁ hb₂
  obtain ⟨m, hm, hb₂⟩ := hb₂
  refine ⟨m, hm, ?_⟩
  intro a st ha hpath hpool hsafe
  have hclA : Clean (portTargets fA.ports ++ fA.garb) st.basis := fun w hw => by
    rw [fA, sp16_targets] at hw
    exact hpool w (pool_band_in_dialogPool (mem_short_garbA hw))
  have hst := fA.load_state read fA_geo a st ⟨hpath, ha.1, ha.2⟩ hclA
  set sA0 := ECDSAAdd.run fA.swapNet List.nil
    (ECDSAAdd.run ((specialize fA.selCode (tableAddressValue fA.selBits st.basis)).instantiate read) List.nil st) with hsA0
  have hsL1 : (⟨sA0.phase, clearRegister garbA sA0.basis⟩ : ECDSAAdd.State) =
      ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩ := by
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
    have h2 := hst.2.2.2
    change clearRegister garbA sA0.basis = tableXorState (portMask read sp16 a) (st.basis windowRoot) st.basis at h2
    rw [ha.2] at h2; exact h2
  have hu1 : ∀ q ∈ d1, sA0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
    have h1 := hst.2.2.1 q hq
    change sA0.basis q.target = (st.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
    rw [ha.2, Bool.true_and] at h1; exact h1
  change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
  rw [hb₁ a st ⟨hpath, ha.1, ha.2⟩ hclA, map_smul, hb₂ a st sA0 hsL1 ha hpath hpool hsafe hu1, smul_smul]

/-! Splicing `twoPassProg` into `WideBank8.Row16.code = b0 :: b1 :: b2 :: restW`. -/

def b0 : WideBank8.Fast16.FBlock2 65536 := .std (.plain (Rows.code r16 (wLiteral [.X 838])))
def b1 : WideBank8.Fast16.FBlock2 65536 := .std (.plain (Rows.code r16 scrHead))
def b2 : WideBank8.Fast16.FBlock2 65536 := .std (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩))
def restW : WideBank8.Fast16.FCode2 65536 := WideBank8.Row16.code.drop 3

theorem code_split : WideBank8.Row16.code = b0 :: b1 :: b2 :: restW := by
  have h : WideBank8.Row16.code =
      b0 :: b1 :: b2 :: ((WEXFast.fgeneric3 ++ (WEXFast.FBlock2.std (.plain WEX.cornerNeg) :: List.nil)).map WideBank8.Row16.lift ++
        WideBank8.Fast16.FBlock2.pair WideBank8.Row16.corner :: WideBank8.Row16.tailF.map WideBank8.Row16.lift) := by
    unfold WideBank8.Row16.code
    rw [WideBank8.Row16.headF, WEXUnlookup.rowPre3]
    simp [b0, b1, b2, r16, WideBank8.Row16.lift, Rows.block, toBlock2]
  rw [restW, h]; rfl

theorem b2_rec_diff : WideBank8.Fast16.fblockRec b2 = site1Rec + 15098 := by
  have hgeo := WideBank8.Row16.geometry b2 (by rw [code_split]; simp)
  have hlay := WideBank8.geo_lay2 WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok
    (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) hgeo
  have hpre_eq : (site1 probeRows).prefix = [WInstr.lookup (some windowRoot) (sitePorts probeRows), WInstr.literal site1Arith] := rfl
  have hpre : codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
      (normalizeW (Rows.code r16 (site1 probeRows).prefix)) =
      ECDSAAdd.measurementCount site1Arith + 65535 := by
    have hlay1 : LookupLayouts WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
        (normalizeW (Rows.code r16 (site1 probeRows).prefix)) := hlay.1
    have h1 : codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
        (normalizeW (Rows.code r16 (site1 probeRows).prefix)) =
        literalRecords (site1 probeRows).prefix +
        traversals (site1 probeRows).prefix * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) := by
      rw [codeRecords_eq _ _ _ _ hlay1, literalRecords_normalize, traversals_normalize,
        (WideBank8.Counts.lift_metrics r16 _).2.1, (WideBank8.Counts.lift_metrics r16 _).2.2]
    have h2' : literalRecords (site1 probeRows).prefix = ECDSAAdd.measurementCount site1Arith := by
      rw [hpre_eq]; exact litRec_lookup_lit _ _ _
    have h3' : traversals (site1 probeRows).prefix * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) = 65535 := by
      rw [hpre_eq, trav_lookup_lit]; decide
    exact h1.trans (congrArg₂ (· + ·) h2' h3')
  have hcr : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree WideBank8.Fast16.bank15.high 0 1) (site1 probeRows).guard WideBank8.Fast16.bank15.hp) = 255 := by
    change MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree8 windowRoot WideBank8.Fast16.bank15.hp) = 255
    rw [(MeasuredClear.recordUnary_counts _ _ _ tree8_layout 0).1, tree8_nodes]
  have hlen : (Rows.ports r16 (site1 probeRows).ports).length = 771 := by
    have h := congrArg List.length (sitePorts_targets probeRows)
    have hs : scrAllWires.length = 771 := by
      have h1 : scrPairWires.length = 258 := scrPairWires_length
      have h2 : scrShortWires.length = 258 := scrShortWires_length
      have h3 : scrDExtraWires.length = 255 := by rw [scrDExtraWires_explicit]; simp
      simp [scrAllWires, scrWires, h1, h2, h3]
    rw [Rows.ports, List.length_map]
    simpa [site1, portTargets, hs] using h
  have hrec_eq : WideBank8.Fast16.fblockRec b2 =
      WideBank8.blockRecP2 WideBank8.Fast16.bank15 (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) :=
    fblockRec_std _
  have hlhs : WideBank8.Fast16.fblockRec b2 =
      ECDSAAdd.measurementCount site1Arith + 65535 + 771 + (255 + 255) :=
    hrec_eq.trans ((blockRecP2_unit_16 WideBank8.Fast16.bank15 (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)).trans
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) hpre hlen) (congrArg (· + 255) hcr)))
  exact (hlhs.trans (wide_rec_diff_arith (ECDSAAdd.measurementCount site1Arith) mShort mTail fixRec8 mShort_add_mTail fixRec8_eq)).trans
    (congrArg (· + 15098) (show site1RecGen 16383 32767 mShort mTail fixRec8 = site1Rec from rfl))

theorem b2_tp_diff :
    WideBank8.Fast16.fblockTP b2 =
      (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 247)) + 15098 := by
  have hpre_eq : (site1 probeRows).prefix = [WInstr.lookup (some windowRoot) (sitePorts probeRows), WInstr.literal site1Arith] := rfl
  have htp_pre : literalToffolis (normalizeW (Rows.code r16 (site1 probeRows).prefix)) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram site1Arith) := by
    rw [WideBank8.Counts.lift_normal_metrics, hpre_eq]; exact litToff_lookup_lit _ _ _
  have htr_pre : traversals (Rows.code r16 (site1 probeRows).prefix) = 1 := by
    rw [(WideBank8.Counts.lift_metrics r16 _).2.2, hpre_eq]; exact trav_lookup_lit _ _ _
  have htp_eq : WideBank8.Fast16.fblockTP b2 =
      WideBank8.blockTP2 WideBank8.Fast16.bank15 (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) +
      PoolHost.blockExtra (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) :=
    fblockTP_std _
  have hno_extra : PoolHost.blockExtra (Block2.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) = 0 := rfl
  have h1 : literalToffolis (normalizeW (Rows.code r16 (site1 probeRows).prefix)) =
      ECDSAAdd.toffoliCount shortNorm + ECDSAAdd.toffoliCount tailNorm :=
    htp_pre.trans norm_toff_split.symm
  have h2' : traversals (Rows.code r16 (site1 probeRows).prefix) * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) = 1 * (2 ^ 16 - 1) := by
    rw [htr_pre]; rfl
  have h3 : (tableAddressTree WideBank8.Fast16.bank15.high 0 1).internalNodes + 247 = 255 + 247 :=
    congrArg (· + 247) tree8_nodes
  have hlhs : WideBank8.Fast16.fblockTP b2 =
      ECDSAAdd.toffoliCount shortNorm + ECDSAAdd.toffoliCount tailNorm + 1 * (2 ^ 16 - 1) + (255 + 247) :=
    htp_eq.trans ((congrArg (_ + ·) hno_extra).trans ((Nat.add_zero _).trans
      ((blockTP2_unit_16 WideBank8.Fast16.bank15 (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)).trans
        (congrArg₂ (· + ·) (congrArg₂ (· + ·) h1 h2') h3))))
  exact hlhs.trans (wide_tp_diff_arith (ECDSAAdd.toffoliCount shortNorm) (ECDSAAdd.toffoliCount tailNorm))

theorem newRow_rec :
    WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + site1Rec + WideBank8.Fast16.frecs restW = 1727904 := by
  have h := WideBank8.Row16.row_records
  rw [code_split, frecs_cons, frecs_cons, frecs_cons] at h
  have h' : WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 +
      WideBank8.Fast16.fblockRec b2 + WideBank8.Fast16.frecs restW = 1743002 := by
    simpa only [Nat.add_assoc] using h
  exact row_rec_arith _ _ _ _ _ 15098 1743002 h' b2_rec_diff

def rowProg (start : Nat) : Straight 65536 start (start + 1727904) :=
  castFinish (row_cast_arith start _ _ _ _ _ newRow_rec)
    (((WideBank8.Fast16.fblockProg b0 start).append
      (WideBank8.Fast16.fblockProg b1 (start + WideBank8.Fast16.fblockRec b0))).append
      ((twoPassProg (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1)).append
        (WideBank8.Fast16.fprog restW (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + site1Rec))))

def rowSrc (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  ((WideBank8.Fast16.fblockSrc read b0).seq (WideBank8.Fast16.fblockSrc read b1)).seq
    ((twoPassSrc read).seq (WideBank8.Fast16.fsrc read restW))

theorem rowProg_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rowProg start).instantiate read h).run = (rowSrc read).run := by
  rw [rowProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h1 => by
      rw [append_run_fixed _ _ _ _ _ (fun h2 => WideBank8.Fast16.fprog_run read restW _ h2),
        AdaptiveCircuit.run_seq, twoPass_run read _ h1, ← AdaptiveCircuit.run_seq]),
    AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h1 => WideBank8.Fast16.fblockProg_run read b1 _ h1),
    AdaptiveCircuit.run_seq, WideBank8.Fast16.fblockProg_run read b0 _ h]
  simp only [rowSrc, AdaptiveCircuit.run_seq]

local notation "rowTP16" => (WideBank8.Fast16.fcodeTP WideBank8.Row16.code - 15098)

theorem rowTP_eq :
    WideBank8.Fast16.fblockTP b0 + WideBank8.Fast16.fblockTP b1 +
      (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 247)) + WideBank8.Fast16.fcodeTP restW = rowTP16 :=
  rowTP_sub_arith (WideBank8.Fast16.fcodeTP WideBank8.Row16.code) (WideBank8.Fast16.fblockTP b0)
    (WideBank8.Fast16.fblockTP b1) (WideBank8.Fast16.fblockTP b2) (WideBank8.Fast16.fcodeTP restW)
    (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 + ECDSAAdd.toffoliCount tailNorm + (255 + 247))
    15098 ((congrArg WideBank8.Fast16.fcodeTP code_split).trans (fcodeTP_cons3 b0 b1 b2 restW)) b2_tp_diff

theorem rowProg_tCount (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rowProg start).instantiate read h).tCount = 7 * rowTP16 := by
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split]; simp)
  have hgr : ∀ b ∈ restW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (by rw [code_split]; simp [hb])
  rw [rowProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h1 => by
      rw [append_tCount_fixed _ _ _ _ _ (fun h2 => WideBank8.Fast16.fprog_tCount read restW hgr _ h2),
        twoPass_tCount read _ h1]),
    append_tCount_fixed _ _ _ _ _ (fun h1 => WideBank8.Fast16.fblock_tCount read b1 hg1 _ h1),
    WideBank8.Fast16.fblock_tCount read b0 hg0 start h]
  exact tcount_mul7_4 _ _ _ _ _ rowTP_eq

theorem rowProg_residue (start : Nat) : AndGadget.residue (rowProg start) = 0 := by
  have hbr (b : WideBank8.Fast16.FBlock2 65536) (s : Nat) : AndGadget.residue (WideBank8.Fast16.fblockProg b s) = 0 := by
    have h := WideBank8.Fast16.fprog_residue [b] s
    rw [WideBank8.Fast16.fprog, AndGadget.residue_cast, AndGadget.residue_append] at h
    omega
  rw [rowProg, AndGadget.residue_cast, AndGadget.residue_append, AndGadget.residue_append,
    AndGadget.residue_append, hbr, hbr, twoPass_residue, WideBank8.Fast16.fprog_residue]

theorem rowProg_credit (start : Nat) : ProgramCredit (rowProg start) rowTP16 := by
  have hz := rowProg_residue start
  refine ⟨hz, ?_⟩
  have he := exact_t (rowProg start) hz (fun _ => false) (fun _ => false)
  have ht := rowProg_tCount (fun _ => false) start (fun _ => false)
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7) (he.symm.trans ht)

theorem rowProg_wellFormed (start : Nat) : (rowProg start).WellFormed := by
  have hphys : ∀ p, WInstr.literal p ∈ erase2 (WideBank8.Fast16.fforget WideBank8.Row16.code) → GatePhysical p := by
    rw [WideBank8.Row16.forget]; exact Geometry.row_physical .w16
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split]; simp)
  have hgr : ∀ b ∈ restW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (by rw [code_split]; simp [hb])
  have hp_sub (b : WideBank8.Fast16.FBlock2 65536) (hb : b ∈ WideBank8.Row16.code) :
      ∀ p, WInstr.literal p ∈ erase2 b.forgetL → GatePhysical p := fun p hp =>
    hphys p (by
      rw [WideBank8.Fast16.fforget, erase2]
      have h1 : b.forgetL ⊆ WideBank8.Fast16.fforget WideBank8.Row16.code := fun x hx => List.mem_flatMap.mpr ⟨b, hb, hx⟩
      obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
      exact List.mem_flatMap.mpr ⟨d, h1 hd, hdp⟩)
  rw [rowProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _
    (straight_append_wellFormed _ _
      (WideBank8.Fast16.fblock_wellFormed b0 hg0 (hp_sub b0 (by rw [code_split]; simp)) start)
      (WideBank8.Fast16.fblock_wellFormed b1 hg1 (hp_sub b1 (by rw [code_split]; simp)) _))
    (straight_append_wellFormed _ _ (twoPass_wellFormed _)
      (WideBank8.Fast16.fprog_wellFormed restW hgr (fun p hp => by
        obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
        obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
        exact hp_sub b (by rw [code_split]; simp [hb]) p (List.mem_flatMap.mpr ⟨d, hdb, hdp⟩)) _))

theorem rowProg_support (start : Nat) :
    ChallengeMigration.straightWires (rowProg start) ⊆ WideBank8.Fast16.Tight.support := by
  have hsup_orig := WideBank8.Fast16.Tight.row_program_support start
  rw [WideBank8.Row16.program, code_split, WideBank8.Fast16.fprog, support_cast, straightWires_append] at hsup_orig
  have hs0 : ChallengeMigration.straightWires (WideBank8.Fast16.fblockProg b0 start) ⊆ WideBank8.Fast16.Tight.support :=
    (List.append_subset.mp hsup_orig).1
  have htail1 := (List.append_subset.mp hsup_orig).2
  rw [WideBank8.Fast16.fprog, support_cast, straightWires_append] at htail1
  have hs1 : ChallengeMigration.straightWires (WideBank8.Fast16.fblockProg b1 (start + WideBank8.Fast16.fblockRec b0)) ⊆ WideBank8.Fast16.Tight.support :=
    (List.append_subset.mp htail1).1
  have hrest_sup (s : Nat) : ChallengeMigration.straightWires (WideBank8.Fast16.fprog restW s) ⊆ WideBank8.Fast16.Tight.support := by
    have hmem : ∀ b ∈ restW, b ∈ WideBank8.Row16.code := fun b hb => by rw [code_split]; simp [hb]
    have hf_sub : ∀ x ∈ erase2 (WideBank8.Fast16.fforget restW), x ∈ erase2 (WideBank8.Fast16.fforget WideBank8.Row16.code) := fun x hx => by
      obtain ⟨d, hd, hdx⟩ := List.mem_flatMap.mp hx
      obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
      exact List.mem_flatMap.mpr ⟨d, List.mem_flatMap.mpr ⟨b, hmem b hb, hdb⟩, hdx⟩
    exact WideBank8.Fast16.Tight.fprog_support restW (fun b hb => WideBank8.Row16.geometry b (hmem b hb))
      (fun p hp => WideBank8.Fast16.Tight.row_literals p (hf_sub _ hp))
      (fun b hb => WideBank8.Row16.strict b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl3 b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl4 b (hmem b hb))
      (fun c ps hp => WideBank8.Fast16.Tight.row_lookups c ps (hf_sub _ hp))
      (fun b hb => WideBank8.Fast16.Tight.row_nohost b (hmem b hb)) s
  rw [rowProg, support_cast, straightWires_append, straightWires_append, straightWires_append]
  exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨hs0, hs1⟩,
    List.append_subset.mpr ⟨twoPass_support _, hrest_sup _⟩⟩

theorem rowProg_slots (start : Nat) : (rowProg start).gateSlots ≤ 3290000000 := by
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split]; simp)
  have hgr : ∀ b ∈ restW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (by rw [code_split]; simp [hb])
  have hs0 := WideBank8.Fast16.fprog_slots [b0] (fun b hb => by simp at hb; subst hb; exact hg0) start
  rw [WideBank8.Fast16.fprog, castFinish_gateSlots, Straight.gateSlots_append] at hs0
  simp only [WideBank8.Fast16.fprog, Straight.gateSlots, WideBank8.Fast16.fforget, WideBank8.Fast16.fslack,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero] at hs0
  have hs1 := WideBank8.Fast16.fprog_slots [b1] (fun b hb => by simp at hb; subst hb; exact hg1)
    (start + WideBank8.Fast16.fblockRec b0)
  rw [WideBank8.Fast16.fprog, castFinish_gateSlots, Straight.gateSlots_append] at hs1
  simp only [WideBank8.Fast16.fprog, Straight.gateSlots, WideBank8.Fast16.fforget, WideBank8.Fast16.fslack,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero] at hs1
  have hsr := WideBank8.Fast16.fprog_slots restW hgr
    (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + site1Rec)
  have htp := twoPass_slots (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1)
  have hsp_split :
      WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget WideBank8.Row16.code) =
        WideBank8.codeSP2 WideBank8.Fast16.bank15 b0.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 b1.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 b2.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget restW) := by
    rw [code_split]
    simp only [WideBank8.Fast16.fforget_cons, WideBank8.Fast16.codeSP2_append, Nat.add_assoc]
  have hsl_split :
      WideBank8.Fast16.fslack WideBank8.Row16.code =
        WideBank8.Fast16.fblockSlack b0 + WideBank8.Fast16.fblockSlack b1 +
        WideBank8.Fast16.fblockSlack b2 + WideBank8.Fast16.fslack restW := by
    rw [code_split]; simp only [WideBank8.Fast16.fslack, Nat.add_assoc]
  have hsp_all := WideBank8.Row16.standard_slots
  rw [← WideBank8.Row16.forget] at hsp_all
  have hsl_all := WideBank8.Row16.slack
  have hlit_le := Narrow15.site1_slots_le_rowC
  have hl0 := WEX.clearReferenceRow_literal_slots_bound
  have hm := WEXUnlookup.rowC_measures.2.2.1
  rw [rowProg, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append, Straight.gateSlots_append]
  generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) = gS at htp hlit_le
  generalize literalSlotSum (erase2 WEXUnlookup.rowC) = L1 at hlit_le hm
  generalize literalSlotSum (WEX.clearReferenceRow probeRows) = L0 at hl0 hm
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget WideBank8.Row16.code) = spAll at hsp_split hsp_all
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 b0.forgetL = sp0 at hs0 hsp_split
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 b1.forgetL = sp1 at hs1 hsp_split
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 b2.forgetL = sp2 at hsp_split
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget restW) = spR at hsr hsp_split
  generalize WideBank8.Fast16.fslack WideBank8.Row16.code = slAll at hsl_split hsl_all
  generalize WideBank8.Fast16.fblockSlack b0 = sl0 at hs0 hsl_split
  generalize WideBank8.Fast16.fblockSlack b1 = sl1 at hs1 hsl_split
  generalize WideBank8.Fast16.fblockSlack b2 = sl2 at hsl_split
  generalize WideBank8.Fast16.fslack restW = slR at hsr hsl_split
  omega

theorem rowSrc_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (rowSrc (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  let read := readConstant coeffs Q
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split]; simp)
  have hgr : ∀ b ∈ restW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (by rw [code_split]; simp [hb])
  obtain ⟨c0, a0, m0⟩ := WideBank8.Fast16.fblock_sim read b0 hg0
  obtain ⟨c1, a1, m1⟩ := WideBank8.Fast16.fblock_sim read b1 hg1
  obtain ⟨c2, a2, m2⟩ := twoPass_sim read
  obtain ⟨cr, ar, mr⟩ := WideBank8.Fast16.fsrc_sim read restW hgr
  have h01_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (b0.forgetL ++ b1.forgetL)) ∧
        ∀ a st, AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          WideBank8.Fast16.FBlockClean b0 st →
          (∀ m', m'.length = ECDSAAdd.measurementCount (reference2 read a b0.forgetL) →
            WideBank8.Fast16.FBlockClean b1 (ECDSAAdd.run (reference2 read a b0.forgetL) m' st)) →
          Safe2 read a (b0.forgetL ++ b1.forgetL) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (b0.forgetL ++ b1.forgetL)) m st))
      ((WideBank8.Fast16.fblockSrc read b0).seq (WideBank8.Fast16.fblockSrc read b1)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c0 c1, ?_, by rw [simulationCoefficients_mass, m0, m1]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a0 a1
    intro b₀ k₀ b₁ k₁ hb₀ hb₁
    obtain ⟨m₀, lm₀, r₀⟩ := hb₀
    obtain ⟨m₁, lm₁, r₁⟩ := hb₁
    refine ⟨m₀ ++ m₁, by simp [erase2_append, List.length_append, lm₀, lm₁], ?_⟩
    intro a st ha hc0 hc1 hsafe
    have hm₀ : m₀.length = ECDSAAdd.measurementCount (reference2 read a b0.forgetL) :=
      lm₀.trans (specialize_counts read (erase2 b0.forgetL) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a b0.forgetL b1.forgetL st hsafe
    have ha1 := WideBank8.Fast16.fblock_addr read b0 hg0 a st ha hc0 m₀
    change b₁.kraus (b₀.kraus (Bridge.signedKet st)) = _
    rw [r₀ a st ha hc0 hsp.1, map_smul,
      r₁ a _ ha1 (hc1 m₀ hm₀) (hsp.2 m₀ hm₀), reference2_append, run_append_records _ _ m₀ m₁ st hm₀, smul_smul]
  have h2r_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (b2.forgetL ++ WideBank8.Fast16.fforget restW)) ∧
        ∀ a st, AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          WideBank8.Fast16.FCodeClean read a (b2 :: restW) st →
          Clean streamLayout.dialogPool st.basis →
          Safe2 read a (b2.forgetL ++ WideBank8.Fast16.fforget restW) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (b2.forgetL ++ WideBank8.Fast16.fforget restW)) m st))
      ((twoPassSrc read).seq (WideBank8.Fast16.fsrc read restW)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c2 cr, ?_, by rw [simulationCoefficients_mass, m2, mr]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a2 ar
    intro b₂ k₂ br kr hb₂ hbr
    obtain ⟨m₂, lm₂, r₂⟩ := hb₂
    obtain ⟨mr', lmr', rr⟩ := hbr
    have h2_lit : literalRecords (erase2 b2.forgetL) = ECDSAAdd.measurementCount site1Arith := by
      have heq : erase2 b2.forgetL =
          [WInstr.lookup (some windowRoot) (Rows.ports r16 (sitePorts probeRows)), WInstr.literal site1Arith,
           WInstr.lookup (some windowRoot) (Rows.ports r16 (sitePorts probeRows))] := by
        simp [b2, WideBank8.Fast16.FBlock2.forgetL, erase2, Block2.code, UnitSite.code, Rows.unit, Rows.site,
          Rows.code, Rows.instr, site1, MaskedSite.prefix, wLiteral]
      rw [heq]; exact litRec_lookup_lit_lookup _ _ _ _ _
    have h2_ref (a : Nat) : reference2 read a b2.forgetL = (specialize site1_16.code a).instantiate read := by
      have hce : erase2 b2.forgetL = site1_16.code := by
        simp [b2, WideBank8.Fast16.FBlock2.forgetL, erase2, Block2.code, UnitSite.code, Rows.unit,
          site1_16, Rows.site, MaskedSite.code, MaskedSite.prefix, Rows.code, Rows.instr]
      rw [reference2, hce]
    refine ⟨m₂ ++ mr', by simp [erase2_append, List.length_append, h2_lit, lm₂, lmr'], ?_⟩
    intro a st ha hcl hpool hsafe
    have hm₂ : m₂.length = ECDSAAdd.measurementCount (reference2 read a b2.forgetL) := by
      rw [← h2_lit] at lm₂; exact lm₂.trans (specialize_counts read (erase2 b2.forgetL) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a b2.forgetL (WideBank8.Fast16.fforget restW) st hsafe
    have ha2 := WideBank8.Fast16.fblock_addr read b2 (WideBank8.Row16.geometry b2 (by rw [code_split]; simp)) a st ha hcl.1 m₂
    have hpath2 : Clean WideBank8.Fast16.pathBank st.basis := hcl.1.1
    have hsafe2 : ∀ m', Clean scrAllWires (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis := by
      have hs1 : BlockSafe2 read a (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) st := hsp.1.1
      have hcode_eq : (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩).code = site1_16.code := by
        simp [Rows.unit, UnitSite.code, site1_16, Rows.site, MaskedSite.code, MaskedSite.prefix, Rows.code, Rows.instr]
      have hpr : portTargets (Rows.site r16 (site1 probeRows)).ports = scrAllWires := by
        rw [Rows.site, Rows.targets]; exact sitePorts_targets probeRows
      intro m'
      have hm' := hs1 m'
      rw [hcode_eq] at hm'
      simpa [Rows.unit, hpr] using hm'
    change br.kraus (b₂.kraus (Bridge.signedKet st)) = _
    rw [r₂ a st ha hpath2 hpool hsafe2, ← h2_ref a, map_smul,
      rr a _ ha2 (hcl.2 m₂ hm₂) (hsp.2 m₂ hm₂), reference2_append, run_append_records _ _ m₂ mr' st hm₂, smul_smul]
  obtain ⟨c01, a01, m01⟩ := h01_sim
  obtain ⟨c2r, a2r, m2r⟩ := h2r_sim
  refine ⟨coherentSeqCoefficients c01 c2r, ?_, by rw [simulationCoefficients_mass, m01, m2r]; norm_num⟩
  rw [rowSrc, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a01 a2r
  intro b₁ k₁ b₂ k₂ hb₁ hb₂ s hs
  obtain ⟨m₁, lm₁, r₁⟩ := hb₁
  obtain ⟨m₂, lm₂, r₂⟩ := hb₂
  let a := tableAddressValue WideBank8.Fast16.windowBits s
  have hsafe_all : Safe2 read a (WideBank8.Fast16.fforget WideBank8.Row16.code) ⟨false, s⟩ := by
    rw [WideBank8.Row16.forget]; exact Rows.row_safe _ _ _ hQ hn a s hs
  have hclean_all : WideBank8.Fast16.FCodeClean read a WideBank8.Row16.code ⟨false, s⟩ :=
    WideBank8.Row16.clean_fused _ _ _ (WideBank8.Row16.clean_lift coeffs Q _ _ _
      (WEXFast.rowCF_clean (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs)
      (PoolHost.poolBand_clean_in_rowCF (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs)
      (by rw [WEXFast.fforget_rowCF]; exact PoolHost.rowC_host4 (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs))
  rw [code_split] at hsafe_all hclean_all
  simp only [WideBank8.Fast16.fforget_cons, List.append_assoc] at hsafe_all
  have hsafe_split := WideBank8.Fast16.safe2_append_inv read a (b0.forgetL ++ b1.forgetL)
    (b2.forgetL ++ WideBank8.Fast16.fforget restW) ⟨false, s⟩ (by simpa [List.append_assoc] using hsafe_all)
  have hm₁ : m₁.length = ECDSAAdd.measurementCount (reference2 read a (b0.forgetL ++ b1.forgetL)) :=
    lm₁.trans (specialize_counts read (erase2 (b0.forgetL ++ b1.forgetL)) a).2.symm
  have h0_m : ECDSAAdd.measurementCount (reference2 read a b0.forgetL) = 0 := by
    have hr : reference2 read a b0.forgetL = [.X 838] := by
      simp [b0, WideBank8.Fast16.FBlock2.forgetL, reference2, erase2, Block2.code, Rows.code, Rows.instr,
        wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_lit]
    rw [hr]; exact x838_meas_zero
  have h1_m : ECDSAAdd.measurementCount (reference2 read a b1.forgetL) = 0 := by
    have hr : reference2 read a b1.forgetL = scrHeadProgram := by
      simp [b1, WideBank8.Fast16.FBlock2.forgetL, reference2, erase2, Block2.code, Rows.code, Rows.instr,
        scrHead, scrHeadProgram, wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_append, Tmpl.instantiate_lit]
    rw [hr]; exact scrHeadProgram_meas_zero
  have hm₁_0 : m₁ = List.nil := List.eq_nil_of_length_eq_zero (by
    rw [hm₁, reference2_append, ECDSAAdd.measurementCount_append, h0_m, h1_m])
  have ha0 : AddrValid WideBank8.Fast16.windowBits windowRoot a ⟨false, s⟩ := ⟨rfl, hs.2.2⟩
  have hcl0 : WideBank8.Fast16.FBlockClean b0 ⟨false, s⟩ := hclean_all.1
  have hcl1 : ∀ m', m'.length = ECDSAAdd.measurementCount (reference2 read a b0.forgetL) →
      WideBank8.Fast16.FBlockClean b1 (ECDSAAdd.run (reference2 read a b0.forgetL) m' ⟨false, s⟩) :=
    fun m' hm' => (hclean_all.2 m' hm').1
  have hstep01 := r₁ a ⟨false, s⟩ ha0 hcl0 hcl1 hsafe_split.1
  set st12 := ECDSAAdd.run (reference2 read a (b0.forgetL ++ b1.forgetL)) m₁ ⟨false, s⟩ with hst12
  have hst12_eq : st12 = ECDSAAdd.run (reference2 read a b1.forgetL) List.nil
      (ECDSAAdd.run (reference2 read a b0.forgetL) List.nil ⟨false, s⟩) := by
    rw [hst12, hm₁_0, reference2_append, ECDSAAdd.run_append, h0_m]; rfl
  have hpool12 : Clean streamLayout.dialogPool st12.basis := by
    rw [hst12_eq]
    exact liveReady_pool_after_b01 read r16 a s hs List.nil List.nil
  have ha12 : AddrValid WideBank8.Fast16.windowBits windowRoot a st12 := by
    rw [hst12_eq]
    have ha1' := WideBank8.Fast16.fblock_addr read b0 hg0 a ⟨false, s⟩ ha0 hcl0 List.nil
    exact WideBank8.Fast16.fblock_addr read b1 hg1 a _ ha1' (hcl1 List.nil (by simp [h0_m])) List.nil
  have hcl2r : WideBank8.Fast16.FCodeClean read a (b2 :: restW) st12 := by
    rw [hst12_eq]
    exact (hclean_all.2 List.nil (by simp [h0_m])).2 List.nil (by simp [h1_m])
  have hstep2r := r₂ a st12 ha12 hcl2r hpool12 (hsafe_split.2 m₁ hm₁)
  change b₂.kraus (b₁.kraus (ket s)) = _
  rw [← Bridge.signedKet_false s, hstep01, map_smul, hstep2r, smul_smul]
  have hcomb : ECDSAAdd.run (reference2 read a (b2.forgetL ++ WideBank8.Fast16.fforget restW)) m₂ st12 =
      ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget WideBank8.Row16.code)) (m₁ ++ m₂) ⟨false, s⟩ := by
    rw [hst12, ← run_append_records _ _ m₁ m₂ ⟨false, s⟩ hm₁, ← reference2_append, code_split]
    simp [WideBank8.Fast16.fforget_cons, List.append_assoc]
  have hrun : ECDSAAdd.run (reference2 read a (Geometry.row Geometry.Width.w16)) (m₁ ++ m₂) ⟨false, s⟩ =
      ⟨false, Add.update Geometry.Width.w16 coeffs Q s⟩ :=
    Rows.row_run r16 coeffs Q hQ hn a s hs (m₁ ++ m₂)
  rw [hcomb, WideBank8.Row16.forget, hrun, Bridge.signedKet_false, Bridge.signedKet_false]
  simp [ket]

attribute [local irreducible] rowProg WideSigned.Frame16.program

local notation "signedCredit16" => (2 * Body.signCredit + rowTP16)

def program (start : Nat) : Straight 65536 start (start + 1728416) :=
  castFinish (congrArg (fun m => start + m) (by decide : 512 + 1727904 = 1728416))
    (Frame16.program 1727904 rowProg start)

attribute [local irreducible] program

def source (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (Body.prefixSource .w16).seq ((Body.signSource.seq ((rowSrc (readConstant coeffs Q)).seq Body.signSource)).seq
    (Body.suffixSource .w16))

theorem source_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (source coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  have hs : CoherentlyImplementsOn Body.signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady :=
    fastWindowSign_coherent
  have ha := composeCoherent hs (rowSrc_coherent coeffs Q hQ hn) (fun s h => liveReady_write _ s h)
  have hb := composeCoherent ha hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  have hc := composeCoherent (Body.prefix_coherent .w16) hb
    (fun s h => Body.prepare_live .w16 _ (rootFlip_live s h))
  have hd := composeCoherent hc (Body.suffix_coherent .w16) (fun _ _ => trivial)
  simpa only [source, Body.state, adaptive_seq_assoc] using hd

theorem run (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).run = (source coeffs Q).run := by
  rw [program, castFinish_instantiate]
  have hr (j : Nat) (hist : Fin j → Bool) :
      ((rowProg j).instantiate (readConstant coeffs Q) hist).run = (rowSrc (readConstant coeffs Q)).run :=
    rowProg_run _ j hist
  simpa only [source] using Frame16.run 1727904 rowProg (rowSrc (readConstant coeffs Q))
    (readConstant coeffs Q) hr start history

theorem coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  unfold CoherentlyImplementsOn
  rw [run]
  exact source_coherent coeffs Q hQ hn

def window : Single.Window 65536 := ⟨(Body.logicalBank .w16).reverse, 1728416, program⟩

def model (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) : Single.Distribution.WindowModel (readConstant coeffs Q) where
  physical := window
  point := fun a => if a < 2 ^ Geometry.Width.w16.bits then
    -constantPoint Q (coeffs (Geometry.rows .w16 (2 ^ Geometry.Width.w16.bits - 1 - a)))
    else constantPoint Q (coeffs (Geometry.rows .w16 (a - 2 ^ Geometry.Width.w16.bits)))
  bias := 0
  ideal := Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)
  valid := windowReady
  nodup := by change (Body.logicalBank .w16).reverse.Nodup; exact List.nodup_reverse.mpr (by decide)
  coherent := coherent coeffs Q hQ hn

theorem program_credit (start : Nat) : ProgramCredit (program start) signedCredit16 := by
  rw [program]
  apply credit_cast
  exact Frame16.credit _ _ rowProg rowProg_credit start

theorem wellFormed (start : Nat) : (program start).WellFormed := by
  rw [program, castFinish_wellFormed]
  exact Frame16.wellFormed _ rowProg rowProg_wellFormed start

theorem credit_bound : signedCredit16 ≤ 2327593 := by
  have h1 : WideBank8.Fast16.fcodeTP WideBank8.Row16.code =
      WideBank8.Fast16.fblockTP b0 + WideBank8.Fast16.fblockTP b1 +
      WideBank8.Fast16.fblockTP b2 + WideBank8.Fast16.fcodeTP restW :=
    (congrArg WideBank8.Fast16.fcodeTP code_split).trans (fcodeTP_cons3 b0 b1 b2 restW)
  have h2 := b2_tp_diff
  have hold := WideBank8.Signed16.credit_bound
  generalize WideBank8.Fast16.fcodeTP WideBank8.Row16.code = T at h1 hold ⊢
  generalize WideBank8.Fast16.fblockTP b2 = T2 at h1 h2
  generalize ECDSAAdd.toffoliCount shortNorm = tS at h2
  generalize ECDSAAdd.toffoliCount tailNorm = tT at h2
  generalize Body.signCredit = tSign at hold ⊢
  omega

theorem signed_support (start : Nat) :
    ChallengeMigration.straightWires (program start) ⊆ WideBank8.Fast16.Tight.support := by
  rw [program, straightWires_castFinish]
  exact TightSupport.frame_support17_7 _ rowProg rowProg_support start

theorem packed_support (start : Nat) :
    ChallengeMigration.straightWires (relabelStraight TightSupport.compact17_7 (program start)) ⊆ List.range 1613 := by
  rw [straightWires_relabel]
  intro v hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (TightSupport.compact17_7_bound u (signed_support start hu))

theorem pointRule (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hactive : root 836 = true) (hz : Clean (Body.logicalBank .w16) root) :
    Single.Distribution.PointRule root (model coeffs Q hQ hn) := by
  intro prior output P
  simpa only [Single.Distribution.WindowModel.step, model, window, List.reverse_reverse,
    List.length_reverse, LinearMap.comp_apply] using
    Body.point_sum .w16 coeffs Q hQ hn root hactive hz prior output P

theorem prepared (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hs : windowReady root) (hz : Clean (Body.logicalBank .w16) root)
    (ψ : State) (hψ : SupportedOn (Single.Distribution.pointFamily root) ψ) :
    SupportedOn (model coeffs Q hQ hn).valid
      (Quantum.run ((model coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ) := by
  change SupportedOn (Body.model .w16 coeffs Q hQ hn).valid
    (Quantum.run ((Body.model .w16 coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ)
  exact Body.prepared .w16 coeffs Q hQ hn root hs hz ψ hψ

theorem slots (start : Nat) : (program start).gateSlots ≤ 3300000000 := by
  have hrow := rowProg_slots (start + 256)
  have hsign (j : Nat) : (Body.nProgram .w16 j).gateSlots ≤ 300000 := by
    rw [Body.nProgram, reindexStraight_gateSlots, nFastProgram_slots]
    have h := literal_slot_bound (n := 32768)
      (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
    rw [ECDSAAdd.Baselines.normalize_slots] at h
    have hmax := fastWindowSign_slots
    generalize ECDSAAdd.Challenge.gateSlots fastWindowSignProgram = G at h hmax
    generalize Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) = S at h ⊢
    omega
  rw [program, castFinish_gateSlots, Frame16.slots]
  have h1 := hsign start
  have h2 := hsign (start + 256 + 1727904)
  omega

end Wide16

end
end ShorECDLP.Entrant.Site1Wire
