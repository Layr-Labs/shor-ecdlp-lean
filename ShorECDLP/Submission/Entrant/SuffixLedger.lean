import ShorECDLP.Submission.Entrant.SuffixRow

/-! Ledgers of the row with the output scratch site. -/

section
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ### Instructions and geometry -/

theorem sfxE_sub : ∀ i ∈ portSuffixCodeE probeRows, i ∈ erase row2 := by
  intro i hi
  rw [row2_split, erase_append, erase_append, erase_rowPost]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hi))

theorem cornersPre_sub : ∀ i ∈ WEX.cornersPre probeRows, i ∈ portSuffixCodeE probeRows := by
  intro i hi
  rw [(suffixE_split probeRows).1, cornersE_split]
  simp only [WEX.cornersPre, List.mem_append] at hi ⊢
  tauto

theorem tailF_sub : ∀ i ∈ WEX.sfxZ0 ++ WEX.sfxPadE, i ∈ portSuffixCodeE probeRows := by
  intro i hi
  rw [(suffixE_split probeRows).1]
  simp only [List.mem_append] at hi ⊢
  tauto

theorem scrFMid_subE (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ WEX.scrFMid) :
    WInstr.literal p ∈ portSuffixCodeE probeRows := by
  rw [(suffixE_split probeRows).1, cornersE_split]
  unfold WEX.scrFMid at hp
  simp only [List.mem_append] at hp ⊢
  tauto

theorem row2_instr (i : WInstr 32768) (hi : i ∈ erase row2) :
    PlacedPair windowBits windowPaths windowRoot i ∧ HotAvoid i := by
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  have g := row2_geometry b hb
  cases b with
  | plain c => exact ⟨g.1 i hib, g.2 i hib⟩
  | masked site => exact ⟨placed_implies_pair _ _ _ _ (g.placed i hib), g.bank i hib⟩

theorem scrDLookup_mem : WInstr.lookup none (scrDPorts probeRows) ∈ erase row2 :=
  sfxE_sub _ (by simp [portSuffixCodeE])

theorem scrFSite_geometry : SiteGeometry (WEX.scrFSite probeRows) := by
  obtain ⟨pp, hh⟩ := row2_instr _ scrDLookup_mem
  have look : Placed windowBits windowPaths windowRoot
      (WInstr.lookup (n := 32768) (some windowRoot) (scrDPorts probeRows)) :=
    ⟨pp.1, by rw [scrDPorts_targets]; exact scrAllWires_nodup, pp.2.2.2⟩
  have lit : ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ ECDSAAdd.wires WEX.scrFArith :=
    fun w hw => litConcat_avoid WEX.scrFMid w
      (fun p hp => (row2_instr _ (sfxE_sub _ (scrFMid_subE p hp))).1 w hw)
  have hotL : ∀ i, hot i ∉ ECDSAAdd.wires WEX.scrFArith :=
    fun i => litConcat_avoid WEX.scrFMid _ (fun p hp => (row2_instr _ (sfxE_sub _ (scrFMid_subE p hp))).2 i)
  refine ⟨?_, ?_, Or.inr (Or.inr (Or.inr ⟨scrDPorts_targets probeRows, rfl⟩))⟩
  · intro i hi
    rw [WEX.scrFSite_code] at hi
    simp only [List.mem_append, List.mem_singleton, wLiteral] at hi
    rcases hi with (rfl | rfl) | rfl
    · exact look
    · exact lit
    · exact look
  · intro i hi
    rw [WEX.scrFSite_code] at hi
    simp only [List.mem_append, List.mem_singleton, wLiteral] at hi
    rcases hi with (rfl | rfl) | rfl
    · exact hh
    · exact hotL
    · exact hh

theorem row3F_blocks (b : Block 32768) (hb : b ∈ row3F) :
    b ∈ row2 ∨ b = .plain (WEX.cornersPre probeRows) ∨ b = .masked (WEX.scrFSite probeRows) ∨
      b = .plain (WEX.sfxZ0 ++ WEX.sfxPadE) := by
  have hx : Block.plain (wLiteral [.X 838]) ∈ row2 := by
    rw [row2_split]; simp [rowPost]
  unfold row3F at hb
  rw [row2_split]
  simp only [rowPostF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
  rcases hb with h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · subst h
    rw [row2_split] at hx
    simp only [List.mem_append] at hx
    exact Or.inl hx

theorem row3F_geometry : ∀ b ∈ row3F, BlockGeometry b := by
  intro b hb
  rcases row3F_blocks b hb with h | rfl | rfl | rfl
  · exact row2_geometry b h
  · exact ⟨fun i hi => (row2_instr i (sfxE_sub _ (cornersPre_sub i hi))).1,
      fun i hi => (row2_instr i (sfxE_sub _ (cornersPre_sub i hi))).2⟩
  · exact scrFSite_geometry
  · exact ⟨fun i hi => (row2_instr i (sfxE_sub _ (tailF_sub i hi))).1,
      fun i hi => (row2_instr i (sfxE_sub _ (tailF_sub i hi))).2⟩

theorem row3F_instrs (i : WInstr 32768) (hi : i ∈ erase row3F) :
    i ∈ erase row2 ∨ i ∈ (WEX.scrFSite probeRows).code := by
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  rcases row3F_blocks b hb with h | rfl | rfl | rfl
  · exact Or.inl (List.mem_flatMap.mpr ⟨b, h, hib⟩)
  · exact Or.inl (sfxE_sub _ (cornersPre_sub i hib))
  · exact Or.inr hib
  · exact Or.inl (sfxE_sub _ (tailF_sub i hib))

theorem row3F_physical : ∀ p, WInstr.literal p ∈ erase row3F → GatePhysical p := by
  intro p hp
  rcases row3F_instrs _ hp with h | h
  · exact row2_physical p h
  · rw [WEX.scrFSite_code] at h
    simp only [List.mem_append, List.mem_singleton, wLiteral, WInstr.literal.injEq, reduceCtorEq,
      or_false, false_or] at h
    subst h
    exact litConcat_physical _ (fun q hq => row2_physical q (sfxE_sub _ (scrFMid_subE q hq)))

theorem row3F_oldWithin : OldWithin (erase row3F) := by
  have look := row2_oldWithin.2 none (scrDPorts probeRows) scrDLookup_mem
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases row3F_instrs _ hp with h | h
    · exact row2_oldWithin.1 p h
    · rw [WEX.scrFSite_code] at h
      simp only [List.mem_append, List.mem_singleton, wLiteral, WInstr.literal.injEq, reduceCtorEq,
        or_false, false_or] at h
      subst h
      exact litConcat_subset _ _ (fun q hq => row2_oldWithin.1 q (sfxE_sub _ (scrFMid_subE q hq)))
  · rcases row3F_instrs _ hp with h | h
    · exact row2_oldWithin.2 c ps h
    · rw [WEX.scrFSite_code] at h
      simp only [List.mem_append, List.mem_singleton, wLiteral, WInstr.lookup.injEq, reduceCtorEq,
        or_false, false_or, or_self] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun q hq => ?_, look.2⟩
      rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]
      exact (sourceSupport_mem _).mpr (Or.inr (by unfold oldWork windowRoot; omega))

theorem row3F_masks : masks row3F = 5 := rfl

/-! ### Counts against `row2` -/

theorem lit_zero (code : WCode 32768) (hc : LitOnly code) : traversals code = 0 ∧ portTotal code = 0 := by
  induction code with
  | nil => exact ⟨rfl, rfl⟩
  | cons i code ih =>
    obtain ⟨p, rfl⟩ := hc i List.mem_cons_self
    have := ih (fun j hj => hc j (List.mem_cons_of_mem _ hj))
    simpa [traversals, portTotal] using this

theorem lit_records (code : WCode 32768) (hc : LitOnly code) :
    codeRecords windowBits windowPaths windowRoot (normalizeW code) = ECDSAAdd.measurementCount (litConcat code) := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    obtain ⟨p, rfl⟩ := hc i List.mem_cons_self
    have := ih (fun j hj => hc j (List.mem_cons_of_mem _ hj))
    simp only [normalizeW] at this
    simp [normalizeW, normalizeWInstr, codeRecords, litConcat, ECDSAAdd.Baselines.normalize_measurements,
      ECDSAAdd.measurementCount_append, this]

theorem middle_litOnly : LitOnly scrDMiddle := fun i hi => WEX.scrFMid_litOnly i (by
  unfold WEX.scrFMid; simp only [List.mem_append]; tauto)

theorem suffixF_eq : WEX.portSuffixCodeF probeRows = WEX.cornersPre probeRows ++
    ([.lookup (some windowRoot) (scrDPorts probeRows)] ++ [WInstr.literal WEX.scrFArith] ++
      [.lookup (some windowRoot) (scrDPorts probeRows)]) ++ (WEX.sfxZ0 ++ WEX.sfxPadE) := by
  simp only [WEX.portSuffixCodeF, WEX.scrFSite_code, wLiteral, List.append_assoc]

theorem fe_tof : literalToffolis (WEX.portSuffixCodeF probeRows) = literalToffolis (portSuffixCodeE probeRows) := by
  have tof_mid : literalToffolis ([WInstr.literal WEX.scrFArith] : WCode 32768) =
      literalToffolis (wLiteral (n := 32768) scrSw1) + literalToffolis sfxCC + literalToffolis (wLiteral (n := 32768) scrSw1) +
        literalToffolis (wLiteral (n := 32768) scrNegP) + literalToffolis sfxF + literalToffolis scrDMiddle := by
    simp only [literalToffolis, WEX.scrFArith, litConcat_toffoli, Nat.add_zero]
    simp only [WEX.scrFMid, literalToffolis_append]
  have l1 : ∀ (c : Option Wire) (ps : List (LookupPort 32768)), literalToffolis ([.lookup c ps] : WCode 32768) = 0 :=
    fun _ _ => rfl
  rw [suffixF_eq, (suffixE_split probeRows).1, cornersE_split]
  simp only [literalToffolis_append, tof_mid, WEX.cornersPre, sfxL, l1]
  omega

theorem fe_trav : traversals (WEX.portSuffixCodeF probeRows) = traversals (portSuffixCodeE probeRows) := by
  have mz := lit_zero _ middle_litOnly
  have l0 : ∀ p : ECDSAAdd.Program, traversals (wLiteral (n := 32768) p) = 0 := fun _ => rfl
  have l1 : ∀ (c : Option Wire) (ps : List (LookupPort 32768)), traversals ([.lookup c ps] : WCode 32768) = 1 :=
    fun _ _ => rfl
  have l2 : traversals ([WInstr.literal WEX.scrFArith] : WCode 32768) = 0 := rfl
  rw [suffixF_eq, (suffixE_split probeRows).1, cornersE_split]
  simp only [traversals_append, WEX.cornersPre, sfxL, mz.1, l0, l1, l2, sfxCC, sfxF]
  omega

theorem fe_slot : literalSlotSum (WEX.portSuffixCodeF probeRows) = literalSlotSum (portSuffixCodeE probeRows) := by
  have slot_mid : literalSlotSum ([WInstr.literal WEX.scrFArith] : WCode 32768) =
      literalSlotSum (wLiteral (n := 32768) scrSw1) + literalSlotSum sfxCC + literalSlotSum (wLiteral (n := 32768) scrSw1) +
        literalSlotSum (wLiteral (n := 32768) scrNegP) + literalSlotSum sfxF + literalSlotSum scrDMiddle := by
    simp only [literalSlotSum, WEX.scrFArith, litConcat_slots, Nat.add_zero]
    simp only [WEX.scrFMid, literalSlotSum_append']
  have l1 : ∀ (c : Option Wire) (ps : List (LookupPort 32768)), literalSlotSum ([.lookup c ps] : WCode 32768) = 0 :=
    fun _ _ => rfl
  rw [suffixF_eq, (suffixE_split probeRows).1, cornersE_split]
  simp only [literalSlotSum_append', slot_mid, WEX.cornersPre, sfxL, l1]
  omega

theorem fe_port : portTotal (WEX.portSuffixCodeF probeRows) = portTotal (portSuffixCodeE probeRows) := by
  have mz := lit_zero _ middle_litOnly
  have l0 : ∀ p : ECDSAAdd.Program, portTotal (wLiteral (n := 32768) p) = 0 := fun _ => rfl
  have l1 : ∀ (c : Option Wire) (ps : List (LookupPort 32768)), portTotal ([.lookup c ps] : WCode 32768) = ps.length :=
    fun _ _ => by simp [portTotal]
  have l2 : portTotal ([WInstr.literal WEX.scrFArith] : WCode 32768) = 0 := rfl
  rw [suffixF_eq, (suffixE_split probeRows).1, cornersE_split]
  simp only [portTotal_append', WEX.cornersPre, sfxL, mz.2, l0, l1, l2, sfxCC, sfxF]
  omega

theorem lit_single (code : WCode 32768) (hc : LitOnly code) :
    codeRecords windowBits windowPaths windowRoot (normalizeW ([WInstr.literal (litConcat code)] : WCode 32768)) =
      codeRecords windowBits windowPaths windowRoot (normalizeW code) := by
  rw [lit_records _ hc]
  simp only [normalizeW, List.map_cons, List.map_nil, normalizeWInstr, codeRecords,
    ECDSAAdd.Baselines.normalize_measurements, Nat.add_zero]

theorem lookup_root_records (ps : List (LookupPort 32768)) :
    codeRecords windowBits windowPaths windowRoot (normalizeW [WInstr.lookup (some windowRoot) ps]) =
      codeRecords windowBits windowPaths windowRoot (normalizeW [WInstr.lookup (n := 32768) none ps]) := by
  simp only [normalizeW, List.map_cons, List.map_nil, normalizeWInstr, codeRecords, lookupRoot, Option.getD]

theorem fe_rec : codeRecords windowBits windowPaths windowRoot (normalizeW (WEX.portSuffixCodeF probeRows)) =
    codeRecords windowBits windowPaths windowRoot (normalizeW (portSuffixCodeE probeRows)) := by
  have rec_mid : codeRecords windowBits windowPaths windowRoot (normalizeW ([WInstr.literal WEX.scrFArith] : WCode 32768)) =
      codeRecords windowBits windowPaths windowRoot (normalizeW WEX.scrFMid) := lit_single _ WEX.scrFMid_litOnly
  have hm : codeRecords windowBits windowPaths windowRoot (normalizeW WEX.scrFMid) =
      codeRecords windowBits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrSw1)) +
      codeRecords windowBits windowPaths windowRoot (normalizeW sfxCC) +
      codeRecords windowBits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrSw1)) +
      codeRecords windowBits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrNegP)) +
      codeRecords windowBits windowPaths windowRoot (normalizeW sfxF) +
      codeRecords windowBits windowPaths windowRoot (normalizeW scrDMiddle) := by
    simp only [WEX.scrFMid, normalize_append, records_old_append]
  rw [suffixF_eq, (suffixE_split probeRows).1, cornersE_split]
  simp only [normalize_append, records_old_append, WEX.cornersPre, sfxL]
  rw [rec_mid, hm, lookup_root_records]
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrNegE)) = a1
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrNegP)) = a2
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrW1)) = a3
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrW2)) = a4
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW (wLiteral (n := 32768) scrSw1)) = a5
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW sfxCC) = a6
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW sfxF) = a7
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW scrDMiddle) = a8
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW sfxZ0) = a9
  generalize codeRecords windowBits windowPaths windowRoot (normalizeW sfxPadE) = a10
  generalize codeRecords windowBits windowPaths windowRoot
    (normalizeW ([.lookup none (scrDPorts probeRows)] : WCode 32768)) = a11
  generalize codeRecords windowBits windowPaths windowRoot
    (normalizeW ([.lookup (some streamLayout.doubleSelect) (scrCPorts probeRows)] : WCode 32768)) = a12
  omega

theorem suffixFE_measures :
    literalToffolis (WEX.portSuffixCodeF probeRows) = literalToffolis (portSuffixCodeE probeRows) ∧
    traversals (WEX.portSuffixCodeF probeRows) = traversals (portSuffixCodeE probeRows) ∧
    literalSlotSum (WEX.portSuffixCodeF probeRows) = literalSlotSum (portSuffixCodeE probeRows) ∧
    portTotal (WEX.portSuffixCodeF probeRows) = portTotal (portSuffixCodeE probeRows) ∧
    codeRecords windowBits windowPaths windowRoot (normalizeW (WEX.portSuffixCodeF probeRows)) =
      codeRecords windowBits windowPaths windowRoot (normalizeW (portSuffixCodeE probeRows)) :=
  ⟨fe_tof, fe_trav, fe_slot, fe_port, fe_rec⟩

theorem scrDPorts_length : (scrDPorts probeRows).length = 771 := by
  have h := congrArg List.length (scrDPorts_targets probeRows)
  simp only [portTargets, List.length_map] at h
  rw [h, scrAll_eq]
  simp

theorem row3F_lens : lens row3F = 2567 := by
  have h := row2_lens
  rw [row2_split, lens_append, lens_append] at h
  unfold row3F
  rw [lens_append, lens_append]
  have hp : lens rowPost = 0 := rfl
  have hf : lens rowPostF = 771 := by
    simp only [rowPostF, lens, blockLen, WEX.scrFSite, scrDPorts_length]
  omega

theorem row3F_measures :
    literalToffolis (erase row3F) = literalToffolis (erase row2) ∧
    traversals (erase row3F) = 11 ∧
    literalSlotSum (erase row3F) = literalSlotSum (erase row2) ∧
    portTotal (erase row3F) = portTotal (erase row2) ∧
    codeRecords windowBits windowPaths windowRoot (normalizeW (erase row3F)) = 2048404 - 4 * 32767 := by
  have f := suffixFE_measures
  have m2 := row2_measures
  rw [row2_split] at m2 ⊢
  unfold row3F
  simp only [erase_append, erase_rowPostF, erase_rowPost, literalToffolis_append, traversals_append,
    literalSlotSum_append', portTotal_append', normalize_append, records_old_append] at m2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem row3F_records : records row3F = 1757978 := by
  have h := records_relation row3F row3F_geometry
  rw [row3F_masks, row3F_lens, row3F_measures.2.2.2.2] at h
  omega

theorem row3F_slots (start : Nat) : (program row3F start).gateSlots =
    codeSlots windowBits (normalizeW (erase row3F)) + 250725868 := by
  have h := program_slots_relation row3F row3F_geometry start
  rw [row3F_masks, row3F_lens] at h
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row3F_wellFormed (start : Nat) : (program row3F start).WellFormed :=
  program_wellFormed row3F row3F_geometry row3F_physical start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row3F_support (start : Nat) : ChallengeMigration.straightWires (program row3F start) ⊆ logicalSupport :=
  program_support row3F row3F_geometry row3F_oldWithin start

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

/-- `rowF_facts` at any address, with `row2`'s reference run. -/
theorem row3F_safe_run (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    Safe (readConstant coeffs Q) a row3F ⟨false,s⟩ ∧
      ∀ m, ECDSAAdd.run (reference (readConstant coeffs Q) a row3F) m ⟨false,s⟩ =
        ECDSAAdd.run (reference (readConstant coeffs Q) a row2) m ⟨false,s⟩ := by
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P,hP⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P) true (fun _=>false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P) (StreamPoint.of_coordinates s P hs.1.1.1.1 hP),?_,?_,?_⟩
    · simpa [streamLayout_control,flipInfinity,ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  cases he : Bridge.toB C with
  | zero =>
    have hzero : C = 0 := congrArg ECDSAAdd.ShorPort.toA he
    exact (hC hzero).elim
  | @some cx cy hc =>
    have ce : C = toA (.some hc) := congrArg toA he
    have hr : RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
      readConstant_rowReads coeffs Q _ _ ce
    have ho : ShorECDLP.order • (.some hc : Point) = 0 := by rw [← he]; exact hord
    have hp2 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 2
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hp3 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 3
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hd : (.some hc : Point)+.some hc ≠ 0 := by simpa only [two_nsmul] using hp2
    have ht : (.some hc : Point)+.some hc+.some hc ≠ 0 := by
      simpa only [show (3 : Nat) = 2+1 from rfl,succ_nsmul,two_nsmul] using hp3
    have en := enables_true hc hd ht
    have hdo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0 := by rw [nsmul_add,ho,zero_add]
    exact rowF_facts (readConstant coeffs Q) a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial hs.2.2

theorem row3F_run_any (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (s : BasisState) (hs : liveReady s)
    (m : List Bool) :
    ECDSAAdd.run (reference (readConstant coeffs Q) a row3F) m ⟨false,s⟩ =
      ⟨false,pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q a) s⟩ := by
  rw [(row3F_safe_run coeffs Q hQ hn a s hs).2 m]
  exact row2_run_any a coeffs Q hQ hn s hs m

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row3F_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program row3F start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program_coherent (readConstant coeffs Q) row3F row3F_geometry liveReady (rowPointState coeffs Q)
    (fun s hs => (row3F_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs m => row3F_run_any _ coeffs Q hQ hn s hs m) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩

def rowSource3 (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode (readConstant coeffs Q) row3F

theorem rowSource3_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSource3 coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  obtain ⟨cs,aligned,mass⟩ := row3F_coherent coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs,?_,mass⟩
  simpa only [program_run,rowSource3] using aligned

attribute [local irreducible] Straight.instantiate AdaptiveCircuit.tCount AdaptiveCircuit.run
  program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram WEX.codeRecords WEX.codeSlots WEX.literalToffolis
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps ccx masks

def addFixed3 (start : Nat) : Straight 32768 start (start+1757978) :=
  castFinish (congrArg (fun m => start+m) row3F_records) (program row3F start)

theorem addFixed3_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed3 start).instantiate read history).run = (sourceCode read row3F).run := by
  rw [addFixed3,castFinish_instantiate,program_run]

theorem addFixed3_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed3 start).instantiate read history).tCount = 7*ccx row3F := by
  rw [addFixed3,castFinish_instantiate,program_tCount read row3F row3F_geometry]

theorem addFixed3_slots (start : Nat) : (addFixed3 start).gateSlots =
    codeSlots windowBits (normalizeW (erase row3F)) + 250725868 := by
  rw [addFixed3,castFinish_gateSlots,row3F_slots]

theorem addFixed3_wellFormed (start : Nat) : (addFixed3 start).WellFormed := by
  rw [addFixed3,castFinish_wellFormed]
  exact row3F_wellFormed start

theorem addFixed3_support (start : Nat) : ChallengeMigration.straightWires (addFixed3 start) ⊆ logicalSupport := by
  rw [addFixed3,support_cast]
  exact row3F_support start

open AndGadget in
theorem addFixed3_residue (start : Nat) : residue (addFixed3 start) = 0 := by
  rw [addFixed3,residue_cast]
  exact program_residue row3F start

open AndGadget WEXCredit in
theorem addFixed3_credit (start : Nat) : ProgramCredit (addFixed3 start) (ccx row3F) := by
  have hz := addFixed3_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed3 start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed3_tCount (fun _ => false) start (fun _ => false)
  omega

theorem row3F_ccx_upper : ccx row3F ≤ 2361904 := by
  have h := ccx_relation row3F
  have hn := WEX.literalToffolis_normalize (erase row3F)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis,h0]
  have m := row3F_measures
  rw [row3F_masks, m.2.1] at h
  rw [m.1, row2_measures.1, hrow] at hn
  omega

end
end ShorECDLP.Entrant.WEXUnlookup
end

namespace ShorECDLP.Entrant.WEXUnlookup.Width15Out
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
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
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource3_coherent coeffs Q hQ hn)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1758490) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed3 (start+256))).append
      (nFastProgram (start+256+1757978))).append (suffixProgram (start+256+1757978+256)))

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
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs,aligned,mass⟩ := fastBodySource_coherent coeffs Q hQ hn
  refine ⟨cs,?_,mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row3F) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1757978)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row3F) (prefix_credit start) hl (addFixed3_credit (start+256)) hr
    (suffix_credit (start+256+1757978+256))

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

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,addFixed3_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (erase row3F))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.row2_measures
  have hm3 := WEXUnlookup.row3F_measures
  have hl2 := hm.2.2.1
  rw [← hm.2.2.2.1] at hp
  rw [hm3.2.1, hm3.2.2.1, hm3.2.2.2.1] at hc
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  norm_num [windowBits] at hc
  simp only [windowBits]
  omega

def fastCompactProgram (start : Nat) : Straight 32768 start (start+1758490) :=
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
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastCompactProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
      (fun s => WEXUnlookup.compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have hc : CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready :=
    fastBodyProgram_coherent coeffs Q hQ hn start history
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
    ccx row3F ≤ 2362408 := by
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := row3F_ccx_upper
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 15 where
  records := 1758490
  tBound := 16536856
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row3F
  program := fastCompactProgram
  coherent := by
    intro coeffs Q hQ hn _ start history
    have h := fastCompactProgram_coherent coeffs Q hQ hn start history
    simpa only [Single.BodyValid, WEXUnlookup.compactBody] using h
  wellFormed := by
    intro start
    rw [fastCompactProgram]
    exact (relabelStraight_wellFormed WEX.compactPerm (fastBodyProgram start)).mpr (fastBodyProgram_wellFormed start)
  slots := by
    intro start
    rw [fastCompactProgram,relabelStraight_slots]
    exact (fastBodyProgram_slots_upper start).trans (by rw [WEXUnlookup.compactBody])
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
end ShorECDLP.Entrant.WEXUnlookup.Width15Out
