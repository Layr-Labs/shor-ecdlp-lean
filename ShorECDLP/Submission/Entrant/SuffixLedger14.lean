import ShorECDLP.Submission.Entrant.SuffixLedger
import ShorECDLP.Submission.Entrant.FusedRow14

/-! The row with the output scratch site at physical width 14. -/

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

theorem row2_instr14 (i : WInstr 32768) (hi : i ∈ erase row2) :
    PlacedPair bits windowPaths windowRoot i ∧ HotAvoid i := by
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  have g := row2_geometry b hb
  cases b with
  | plain c => exact ⟨g.1 i hib, g.2 i hib⟩
  | masked site => exact ⟨placed_implies_pair _ _ _ _ (g.placed i hib), g.bank i hib⟩

theorem scrFSite_geometry14 : SiteGeometry (WEX.scrFSite probeRows) := by
  obtain ⟨pp, hh⟩ := row2_instr14 _ scrDLookup_mem
  have look : Placed bits windowPaths windowRoot
      (WInstr.lookup (n := 32768) (some windowRoot) (scrDPorts probeRows)) :=
    ⟨pp.1, by rw [scrDPorts_targets]; exact scrAllWires_nodup, pp.2.2.2⟩
  have lit : ∀ w ∈ windowRoot :: bits ++ windowPaths, w ∉ ECDSAAdd.wires WEX.scrFArith :=
    fun w hw => litConcat_avoid WEX.scrFMid w
      (fun p hp => (row2_instr14 _ (sfxE_sub _ (scrFMid_subE p hp))).1 w hw)
  refine ⟨scrFSite_geometry, ?_, scrFSite_geometry.bank⟩
  intro i hi
  rw [WEX.scrFSite_code] at hi
  simp only [List.mem_append, List.mem_singleton, wLiteral] at hi
  rcases hi with (rfl | rfl) | rfl
  · exact look
  · exact lit
  · exact look

theorem row3F_geometry14 : ∀ b ∈ row3F, BlockGeometry b := by
  intro b hb
  rcases row3F_blocks b hb with h | rfl | rfl | rfl
  · exact row2_geometry b h
  · exact ⟨fun i hi => (row2_instr14 i (sfxE_sub _ (cornersPre_sub i hi))).1,
      fun i hi => (row2_instr14 i (sfxE_sub _ (cornersPre_sub i hi))).2⟩
  · exact scrFSite_geometry14
  · exact ⟨fun i hi => (row2_instr14 i (sfxE_sub _ (tailF_sub i hi))).1,
      fun i hi => (row2_instr14 i (sfxE_sub _ (tailF_sub i hi))).2⟩

theorem row3F_masks14 : masks row3F = 5 := rfl

theorem lit_records14 (code : WCode 32768) (hc : LitOnly code) :
    codeRecords bits windowPaths windowRoot (normalizeW code) = ECDSAAdd.measurementCount (litConcat code) := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    obtain ⟨p, rfl⟩ := hc i List.mem_cons_self
    have := ih (fun j hj => hc j (List.mem_cons_of_mem _ hj))
    simp only [normalizeW] at this
    simp [normalizeW, normalizeWInstr, codeRecords, litConcat, ECDSAAdd.Baselines.normalize_measurements,
      ECDSAAdd.measurementCount_append, this]

theorem lit_single14 (code : WCode 32768) (hc : LitOnly code) :
    codeRecords bits windowPaths windowRoot (normalizeW ([WInstr.literal (litConcat code)] : WCode 32768)) =
      codeRecords bits windowPaths windowRoot (normalizeW code) := by
  rw [lit_records14 _ hc]
  simp only [normalizeW, List.map_cons, List.map_nil, normalizeWInstr, codeRecords,
    ECDSAAdd.Baselines.normalize_measurements, Nat.add_zero]

theorem lookup_root_records14 (ps : List (LookupPort 32768)) :
    codeRecords bits windowPaths windowRoot (normalizeW [WInstr.lookup (some windowRoot) ps]) =
      codeRecords bits windowPaths windowRoot (normalizeW [WInstr.lookup (n := 32768) none ps]) := by
  simp only [normalizeW, List.map_cons, List.map_nil, normalizeWInstr, codeRecords, lookupRoot, Option.getD]

theorem fe_rec14 : codeRecords bits windowPaths windowRoot (normalizeW (WEX.portSuffixCodeF probeRows)) =
    codeRecords bits windowPaths windowRoot (normalizeW (portSuffixCodeE probeRows)) := by
  have rec_mid : codeRecords bits windowPaths windowRoot (normalizeW ([WInstr.literal WEX.scrFArith] : WCode 32768)) =
      codeRecords bits windowPaths windowRoot (normalizeW WEX.scrFMid) := lit_single14 _ WEX.scrFMid_litOnly
  have hm : codeRecords bits windowPaths windowRoot (normalizeW WEX.scrFMid) =
      codeRecords bits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrSw1)) +
      codeRecords bits windowPaths windowRoot (normalizeW sfxCC) +
      codeRecords bits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrSw1)) +
      codeRecords bits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrNegP)) +
      codeRecords bits windowPaths windowRoot (normalizeW sfxF) +
      codeRecords bits windowPaths windowRoot (normalizeW scrDMiddle) := by
    simp only [WEX.scrFMid, normalize_append, records_old_append]
  rw [suffixF_eq, (suffixE_split probeRows).1, cornersE_split]
  simp only [normalize_append, records_old_append, WEX.cornersPre, sfxL]
  rw [rec_mid, hm, lookup_root_records14]
  generalize codeRecords bits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrNegE)) = a1
  generalize codeRecords bits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrNegP)) = a2
  generalize codeRecords bits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrW1)) = a3
  generalize codeRecords bits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrW2)) = a4
  generalize codeRecords bits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrSw1)) = a5
  generalize codeRecords bits windowPaths windowRoot (normalizeW sfxCC) = a6
  generalize codeRecords bits windowPaths windowRoot (normalizeW sfxF) = a7
  generalize codeRecords bits windowPaths windowRoot (normalizeW scrDMiddle) = a8
  generalize codeRecords bits windowPaths windowRoot (normalizeW sfxZ0) = a9
  generalize codeRecords bits windowPaths windowRoot (normalizeW sfxPadE) = a10
  generalize codeRecords bits windowPaths windowRoot
    (normalizeW ([.lookup none (scrDPorts probeRows)] : WCode 32768)) = a11
  generalize codeRecords bits windowPaths windowRoot
    (normalizeW ([.lookup (some streamLayout.doubleSelect) (scrCPorts probeRows)] : WCode 32768)) = a12
  omega

theorem row3F_records_code14 :
    codeRecords bits windowPaths windowRoot (normalizeW (erase row3F)) = 1802644 - 4 * 16383 := by
  have h2 := row2_records_code14
  have f := fe_rec14
  have e2 : erase row2 = erase rowPre ++ (erase (generic2 probeRows) ++
      (portSuffixCodeE probeRows ++ wLiteral [.X 838])) := by
    rw [row2_split, erase_append, erase_append, erase_rowPost]
  have e3 : erase row3F = erase rowPre ++ (erase (generic2 probeRows) ++
      (WEX.portSuffixCodeF probeRows ++ wLiteral [.X 838])) := by
    unfold row3F
    rw [erase_append, erase_append, erase_rowPostF]
  rw [e2] at h2
  rw [e3]
  rw [normalize_append, normalize_append, normalize_append, records_old_append, records_old_append,
    records_old_append] at h2 ⊢
  rw [f]
  exact h2

theorem row3F_records14 : records row3F = 1659034 := by
  have h := records_relation row3F row3F_geometry14
  rw [row3F_masks14, WEXUnlookup.row3F_lens, row3F_records_code14] at h
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx Nat.add Nat.mul in
theorem row3F_ccx_upper14 : ccx row3F ≤ 2262960 := by
  have h := ccx_relation row3F
  have hn := WEX.literalToffolis_normalize (erase row3F)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis,h0]
  have m := WEXUnlookup.row3F_measures
  rw [row3F_masks14, m.2.1] at h
  rw [m.1, WEXUnlookup.row2_measures.1, hrow] at hn
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row3F_wellFormed14 (start : Nat) : (program row3F start).WellFormed :=
  program_wellFormed row3F row3F_geometry14 row3F_physical start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row3F_support14 (start : Nat) : ChallengeMigration.straightWires (program row3F start) ⊆ logicalSupport :=
  program_support row3F row3F_geometry14 row3F_oldWithin start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row3F_slots_upper14 (start : Nat) : (program row3F start).gateSlots ≤ 1000000000 := by
  have h := program_slots_upper row3F row3F_geometry14 start
  rw [row3F_masks14] at h
  have hc := WEX.codeSlots_bound bits (normalizeW (erase row3F))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.row2_measures
  have hm3 := WEXUnlookup.row3F_measures
  have hl2 := hm.2.2.1
  rw [← hm.2.2.2.1] at hp
  rw [hm3.2.1, hm3.2.2.1, hm3.2.2.2.1] at hc
  have hlen : bits.length = 14 := by simp [bits,WEX.widthBits]
  rw [hlen] at hc
  norm_num at hc
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row3F_coherent14 (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program row3F start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program_coherent (readConstant coeffs Q) row3F row3F_geometry14 liveReady (rowState coeffs Q)
    (fun s hs => (row3F_safe_run coeffs Q hQ hn _ s hs).1) (by
      intro s hs m
      simpa only [rowState] using row3F_run_any (tableAddressValue bits s) coeffs Q hQ hn s hs m) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩

def rowSource3 (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode (readConstant coeffs Q) row3F

theorem rowSource3_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (rowSource3 coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := row3F_coherent14 coeffs Q hQ hn 0 Fin.elim0
  have he : rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold rowState rowPointState
    rw [show tableAddressValue bits s = tableAddressValue (WEX.widthBits 14) s from rfl,
      WEX.width_table 14 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  simpa only [program_run,rowSource3,LiveReady] using aligned

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  MeasuredClear.measuredClear ccx Nat.add Nat.mul

def addFixed3 (start : Nat) : Straight 32768 start (start+1659034) :=
  castFinish (congrArg (fun m => start+m) row3F_records14) (program row3F start)

attribute [local irreducible] addFixed3

theorem addFixed3_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed3 start).instantiate read history).run = (sourceCode read row3F).run := by
  rw [addFixed3,castFinish_instantiate,program_run]

theorem addFixed3_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed3 start).instantiate read history).tCount = 7*ccx row3F := by
  rw [addFixed3,castFinish_instantiate,program_tCount read row3F row3F_geometry14]

theorem addFixed3_wellFormed (start : Nat) : (addFixed3 start).WellFormed := by
  rw [addFixed3,castFinish_wellFormed]
  exact row3F_wellFormed14 start

theorem addFixed3_support (start : Nat) : ChallengeMigration.straightWires (addFixed3 start) ⊆ logicalSupport := by
  rw [addFixed3,support_cast]
  exact row3F_support14 start

theorem addFixed3_residue (start : Nat) : residue (addFixed3 start) = 0 := by
  rw [addFixed3,residue_cast]
  exact program_residue row3F start

theorem addFixed3_credit (start : Nat) : ProgramCredit (addFixed3 start) (ccx row3F) := by
  have hz := addFixed3_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed3 start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed3_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixed3_slots_upper (start : Nat) : (addFixed3 start).gateSlots ≤ 1000000000 := by
  rw [addFixed3,castFinish_gateSlots]
  exact row3F_slots_upper14 start

end
end ShorECDLP.Entrant.WEXUnlookupWidth14
end

namespace ShorECDLP.Entrant.WEXUnlookupWidth14.FusedOut
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible WEXUnlookupWidth14
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program blockProgram clearProgram addFixed3 WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx Nat.add Nat.mul
def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSource3 coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource3_coherent coeffs Q hQ hn halias)
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
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed3 (start+256))).append
      (nFastProgram (start+256+1659034))).append (suffixProgram (start+256+1659034+256)))

attribute [local irreducible] fastBodyProgram

theorem fastBodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode read row3F)).seq fastSignSource)).seq suffixSource).run := by
  rw [fastBodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource fastSignSource (sourceCode read row3F) fastSignSource suffixSource
    (prefixProgram_run _ read) (nFastProgram_run _ read) (addFixed3_run read _)
    (nFastProgram_run _ read) (suffixProgram_run _ read) history

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode (readConstant coeffs Q) row3F)).seq fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSource3
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
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row3F) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1659034)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row3F) (prefix_credit start) hl (addFixed3_credit (start+256)) hr
    (suffix_credit (start+256+1659034+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row3F) := by
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
      · exact addFixed3_wellFormed _
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
    addFixed3_support _⟩,(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := addFixed3_slots_upper (start+256)
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
    ccx row3F ≤ 2263464 := by
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := row3F_ccx_upper14
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 14 where
  records := 1659546
  tBound := 15844248
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row3F
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
end ShorECDLP.Entrant.WEXUnlookupWidth14.FusedOut
