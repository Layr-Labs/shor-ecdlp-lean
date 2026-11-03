import ShorECDLP.Submission.Entrant.FusedRow

/-! The fused row at physical width 14. -/

section
namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem pairRoot_nodup14 :
    (lookupRoot windowRoot (some streamLayout.core.generic) :: bits ++ windowPaths).Nodup := by
  decide +kernel

theorem pairTargets_window14 :
    ∀ w ∈ windowRoot :: lookupRoot windowRoot (some streamLayout.core.generic) :: bits ++ windowPaths,
      w ∉ pairTargets := by
  decide +kernel

theorem pairWireList_window14 : ∀ w ∈ windowRoot :: bits ++ windowPaths, w ∉ pairWireList := by
  decide +kernel

theorem pairSite_placed14 (refsA refsB : Nat → Nat → ConstantBit 32768) :
    ∀ i ∈ (pairSite refsA refsB).code, Placed bits windowPaths windowRoot i := by
  have ht : portTargets (pairSite refsA refsB).ports = pairTargets := pairSite_targets refsA refsB
  have look : Placed bits windowPaths windowRoot
      (WInstr.lookup (n := 32768) (some streamLayout.core.generic) (pairSite refsA refsB).ports) := by
    refine ⟨pairRoot_nodup14,?_,?_⟩
    · rw [ht]; exact pairTargets_nodup
    · rw [ht]; intro a ha hb; exact pairTargets_window14 a ha hb
  intro i hi
  rw [pairSite_code] at hi
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact look
  · exact wires_avoid_of pairArith_subset pairWireList_window14
  · exact look

theorem row2_geometry : ∀ b ∈ row2, BlockGeometry b := by
  intro b hb
  rcases row2_blocks b hb with h | rfl | rfl
  · exact row_geometry b h
  · exact ⟨pairSite_geometry _ _,pairSite_placed14 _ _,(pairSite_geometry _ _).bank⟩
  · exact ⟨pairSite_geometry _ _,pairSite_placed14 _ _,(pairSite_geometry _ _).bank⟩

theorem row2_masks14 : masks row2 = 5 := rfl

theorem lookup_meas14 (ps : List (LookupPort 32768)) :
    lookupMeasurements (portOps ps bits windowPaths (lookupRoot windowRoot (some streamLayout.core.generic))) =
      16383 := by
  rw [portOps_measurements ps bits windowPaths _ (by simp [bits,WEX.widthBits,windowPaths]) pairRoot_nodup14]
  decide +kernel

theorem site3_records14 (c : Option Wire) (ps : List (LookupPort 32768)) (p : ECDSAAdd.Program) :
    codeRecords bits windowPaths windowRoot (normalizeW ([.lookup c ps,.literal p,.lookup c ps] : WCode 32768)) =
      2 * lookupMeasurements (portOps ps bits windowPaths (lookupRoot windowRoot c)) +
        ECDSAAdd.measurementCount p := by
  simp only [codeRecords,normalizeW,List.map_cons,List.map_nil,normalizeWInstr,
    ECDSAAdd.Baselines.normalize_measurements]
  omega

theorem generic2_records14 :
    codeRecords bits windowPaths windowRoot (normalizeW (erase (generic2 probeRows))) + 4 * 16383 =
      codeRecords bits windowPaths windowRoot (normalizeW (erase (generic streamLayout probeRows))) := by
  have hy := yPair_counts
  rw [generic2_list,generic_list]
  simp only [erase,List.flatMap_cons,List.flatMap_nil,List.append_nil,Block.code,wLiteral,pairSite_code,
    constSite_code,normalize_append,records_old_append]
  simp only [site3_records14,lookup_meas14]
  have eb : ECDSAAdd.measurementCount pairArith =
      ECDSAAdd.measurementCount ((streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p) +
        ECDSAAdd.measurementCount ((streamLayout.recoveryConstant streamLayout.point.y).program SquareReduction.c ECDSAAdd.p) := by
    unfold pairArith; rw [ECDSAAdd.measurementCount_append,hy.1]
  rw [eb]
  omega

theorem row2_records_code14 :
    codeRecords bits windowPaths windowRoot (normalizeW (erase row2)) = 1802644 - 4 * 16383 := by
  have g := generic2_records14
  have h := WEX.clearReferenceRow_width_records 14 (by omega)
  have hn : 1556899 + 15 * (2 ^ 14 - 1) = 1802644 := by norm_num
  have hr : codeRecords bits windowPaths windowRoot (normalizeW (clearReferenceRow probeRows)) = 1802644 := by
    simpa only [bits] using h.trans hn
  rw [← erase_row] at hr
  rw [row2_split,row_split] at *
  simp only [erase_append,normalize_append,records_old_append] at *
  omega

theorem row2_records : records row2 = 1659034 := by
  have h := records_relation row2 row2_geometry
  rw [row2_masks14,WEXUnlookup.row2_lens,row2_records_code14] at h
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx Nat.add Nat.mul in
theorem row2_ccx_upper : ccx row2 ≤ 2262960 := by
  have h := ccx_relation row2
  have hn := WEX.literalToffolis_normalize (erase row2)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis,h0]
  rw [row2_masks14,WEXUnlookup.row2_measures.2.1] at h
  rw [WEXUnlookup.row2_measures.1,hrow] at hn
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_wellFormed (start : Nat) : (program row2 start).WellFormed :=
  program_wellFormed row2 row2_geometry row2_physical start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_support (start : Nat) : ChallengeMigration.straightWires (program row2 start) ⊆ logicalSupport :=
  program_support row2 row2_geometry row2_oldWithin start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_slots_upper (start : Nat) : (program row2 start).gateSlots ≤ 1000000000 := by
  have h := program_slots_upper row2 row2_geometry start
  rw [row2_masks14] at h
  have hc := WEX.codeSlots_bound bits (normalizeW (erase row2))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.row2_measures
  have hl2 := hm.2.2.1
  rw [← hm.2.2.2.1] at hp
  rw [hm.2.1] at hc
  have hlen : bits.length = 14 := by simp [bits,WEX.widthBits]
  rw [hlen] at hc
  norm_num at hc
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_coherent (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program row2 start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program_coherent (readConstant coeffs Q) row2 row2_geometry liveReady (rowState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1) (by
      intro s hs m
      simpa only [rowState] using row2_run_any (tableAddressValue bits s) coeffs Q hQ hn s hs m) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩

def rowSource2 (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode (readConstant coeffs Q) row2

theorem rowSource2_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (rowSource2 coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := row2_coherent coeffs Q hQ hn 0 Fin.elim0
  have he : rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold rowState rowPointState
    rw [show tableAddressValue bits s = tableAddressValue (WEX.widthBits 14) s from rfl,
      WEX.width_table 14 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  simpa only [program_run,rowSource2,LiveReady] using aligned

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  MeasuredClear.measuredClear ccx Nat.add Nat.mul

def addFixed2 (start : Nat) : Straight 32768 start (start+1659034) :=
  castFinish (congrArg (fun m => start+m) row2_records) (program row2 start)

attribute [local irreducible] addFixed2

theorem addFixed2_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed2 start).instantiate read history).run = (sourceCode read row2).run := by
  rw [addFixed2,castFinish_instantiate,program_run]

theorem addFixed2_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed2 start).instantiate read history).tCount = 7*ccx row2 := by
  rw [addFixed2,castFinish_instantiate,program_tCount read row2 row2_geometry]

theorem addFixed2_wellFormed (start : Nat) : (addFixed2 start).WellFormed := by
  rw [addFixed2,castFinish_wellFormed]
  exact row2_wellFormed start

theorem addFixed2_support (start : Nat) : ChallengeMigration.straightWires (addFixed2 start) ⊆ logicalSupport := by
  rw [addFixed2,support_cast]
  exact row2_support start

theorem addFixed2_residue (start : Nat) : residue (addFixed2 start) = 0 := by
  rw [addFixed2,residue_cast]
  exact program_residue row2 start

theorem addFixed2_credit (start : Nat) : ProgramCredit (addFixed2 start) (ccx row2) := by
  have hz := addFixed2_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed2 start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed2_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixed2_slots_upper (start : Nat) : (addFixed2 start).gateSlots ≤ 1000000000 := by
  rw [addFixed2,castFinish_gateSlots]
  exact row2_slots_upper start

end
end ShorECDLP.Entrant.WEXUnlookupWidth14
end

namespace ShorECDLP.Entrant.WEXUnlookupWidth14.Fused
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible WEXUnlookupWidth14
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program blockProgram clearProgram addFixed2 WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx Nat.add Nat.mul
def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSource2 coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource2_coherent coeffs Q hQ hn halias)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn halias)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)
def fastBodyProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed2 (start+256))).append
      (nFastProgram (start+256+1659034))).append (suffixProgram (start+256+1659034+256)))

attribute [local irreducible] fastBodyProgram

theorem fastBodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode read row2)).seq fastSignSource)).seq suffixSource).run := by
  rw [fastBodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource fastSignSource (sourceCode read row2) fastSignSource suffixSource
    (prefixProgram_run _ read) (nFastProgram_run _ read) (addFixed2_run read _)
    (nFastProgram_run _ read) (suffixProgram_run _ read) history

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode (readConstant coeffs Q) row2)).seq fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSource2
    rfl
  have hr := fastBodyProgram_run_read (readConstant coeffs Q) start history
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs,aligned,mass⟩ := fastBodySource_coherent coeffs Q hQ hn halias
  refine ⟨cs,?_,mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1659034)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row2) (prefix_credit start) hl (addFixed2_credit (start+256)) hr
    (suffix_credit (start+256+1659034+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  have hc := fastBodyProgram_credit start
  have h := exact_t (fastBodyProgram start) hc.1 read history
  rw [hc.2] at h
  exact h

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram,castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixed2_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem fastBodyProgram_support (start : Nat) : ChallengeMigration.straightWires (fastBodyProgram start) ⊆ logicalSupport := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ sourceSupport := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ sourceSupport := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  rw [fastBodyProgram,support_cast]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp.trans (List.subset_append_left _ _),(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,
    addFixed2_support _⟩,(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := addFixed2_slots_upper (start+256)
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  omega
def fastCompactProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  relabelStraight WEX.compactPerm (fastBodyProgram start)

theorem fastCompactProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastCompactProgram start) ⊆ compactSupport := by
  rw [fastCompactProgram,straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  have hh := fastBodyProgram_support start hv
  rcases List.mem_append.mp hh with ho | hh
  · exact List.mem_range.mpr (WEX.compactPerm_bound v ho)
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact List.mem_range.mpr (WEX.compactPerm_bound _ (recycledHot_source i))

theorem fastCompactProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastCompactProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
      (fun s => WEXUnlookup.compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have hc : CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready :=
    fastBodyProgram_coherent coeffs Q hQ hn halias start history
  have h := hc.relabel WEX.compactPerm
  have hr : CoherentlyImplementsOn
      (((fastBodyProgram start).instantiate (readConstant coeffs Q) history).relabel WEX.compactPerm)
      ((relabelState WEX.compactPerm).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState WEX.compactPerm.symm)))
      (fun s => WEXUnlookup.compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,aligned,mass⟩ := h
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb s hs
    apply hb s
    refine ⟨hs.1.1,?_⟩
    intro i
    exact (pull_hot s i).trans (hs.1.2 i)
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
    (by intro s _; simp [compactState,compactPull,LinearMap.comp_apply,relabelState,ket])
  rw [fastCompactProgram,relabelStraight_instantiate]
  exact he

theorem fastCount_upper : 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    ccx row2 ≤ 2263464 := by
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := WEXUnlookupWidth14.row2_ccx_upper
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 14 where
  records := 1659546
  tBound := 15844248
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2
  program := fastCompactProgram
  coherent := by
    intro coeffs Q hQ hn halias start history
    have ha : WEX.WidthAliased 14 coeffs := by simpa only [WEX.WidthAliased, ModAliased, reducedAddress] using halias
    have h := fastCompactProgram_coherent coeffs Q hQ hn ha start history
    simpa only [Single.BodyValid, WEXUnlookup.compactBody] using h
  wellFormed := by
    intro start
    rw [fastCompactProgram]
    exact (relabelStraight_wellFormed WEX.compactPerm (fastBodyProgram start)).mpr (fastBodyProgram_wellFormed start)
  slots := by
    intro start
    rw [fastCompactProgram,relabelStraight_slots]
    exact (fastBodyProgram_slots_upper start).trans (by rw [WEXUnlookup.compactBody]; decide +kernel)
  wires := by
    intro start
    simpa only [WEXUnlookup.compactBody] using fastCompactProgram_support start
  tCount := by
    intro start read history
    rw [fastCompactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,fastBodyProgram_tCount]
    have h := fastCount_upper
    omega
  zero := by
    intro start
    rw [fastCompactProgram,WEXUnlookup.residue_relabel]
    exact (fastBodyProgram_credit start).1
  count_eq := by
    intro start
    rw [fastCompactProgram,AndGadget.added_relabel]
    exact (fastBodyProgram_credit start).2
end
end ShorECDLP.Entrant.WEXUnlookupWidth14.Fused
