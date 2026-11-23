import ShorECDLP.Submission.Entrant.Prefix

/-! Shared avoidance and cleanliness proofs for the thirty clean dialog-pool wires `14848..14877`.
None of these wires are touched by any lookup site, unit, corner block, or non-arithmetic helper
of `WEXUnlookup.rowC` or `WEXFast.rowCF`, and all thirty are clean (`false`) at every block
boundary. This simultaneously supports:
1. Replacing wire `10000` in the wide-row lookup path bank with `14848` (-1 qubit, 0 T-cost).
2. Hosting `14877, 14876, 14875, 14874` on untouched flag/finite wires during `arithS`/`SquareOB5`. -/

namespace ShorECDLP.Entrant.PoolHost
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-- Dialog-pool positions 733..762 (`14848..14877`): clean pool wires unused outside `arithS`/`SquareOB5`. -/
def poolBand : List Wire := List.range' 14848 30

theorem mem_poolBand (w : Wire) : w ∈ poolBand ↔ 14848 ≤ w ∧ w < 14878 := by
  simp only [poolBand, List.mem_range'_1]

theorem poolBand_pool : InPool poolBand := by
  intro q hq
  rw [mem_poolBand] at hq
  have hp : streamLayout.dialogPool = ((List.range' 4115 5699).map streamWire).take 2613 := rfl
  rw [hp, List.mem_iff_getElem]
  refine ⟨q - 14115, by
    simp only [List.length_take, List.length_map, List.length_range']
    rw [Nat.min_eq_left (by norm_num)]
    dsimp only [Wire] at hq
    omega, ?_⟩
  simp only [List.getElem_take, List.getElem_map, List.getElem_range']
  unfold streamWire
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem poolBand_not_of (L : List Wire) (hL : (L.all fun b => decide (b < 14848 ∨ 14878 ≤ b)) = true) :
    ∀ w ∈ poolBand, w ∉ L := by
  intro w hw hm
  have h1 := List.all_eq_true.mp hL w hm
  simp only [decide_eq_true_eq] at h1
  rw [mem_poolBand] at hw
  dsimp only [Wire] at *
  omega

def AvoidsB (code : WCode 32768) : Prop :=
  (∀ w ∈ poolBand, ∀ p, WInstr.literal p ∈ code → w ∉ ECDSAAdd.wires p) ∧
    (∀ w ∈ poolBand, ∀ c ps, WInstr.lookup c ps ∈ code → w ∉ portTargets ps ∧ ∀ q ∈ c, q ≠ w)

theorem avoidsB_append {a b : WCode 32768} (ha : AvoidsB a) (hb : AvoidsB b) : AvoidsB (a ++ b) := by
  refine ⟨fun w hw p hp => ?_, fun w hw c ps hp => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact ha.1 w hw p h
    · exact hb.1 w hw p h
  · rcases List.mem_append.mp hp with h | h
    · exact ha.2 w hw c ps h
    · exact hb.2 w hw c ps h

theorem avoidsB_sub {a b : WCode 32768} (h : ∀ i ∈ a, i ∈ b) (hb : AvoidsB b) : AvoidsB a :=
  ⟨fun w hw p hp => hb.1 w hw p (h _ hp), fun w hw c ps hp => hb.2 w hw c ps (h _ hp)⟩

theorem avoidsB_lit (p : ECDSAAdd.Program) (h : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires p) :
    AvoidsB (wLiteral (n := 32768) p) := by
  refine ⟨fun w hw q hq => ?_, fun w hw c ps hp => ?_⟩
  · simp only [wLiteral, List.mem_singleton, WInstr.literal.injEq] at hq
    rw [hq]; exact h w hw
  · simp [wLiteral] at hp

theorem avoidsB_lookup {c : Option Wire} {ps : List (LookupPort 32768)}
    (ht : ∀ w ∈ poolBand, w ∉ portTargets ps) (hc : ∀ w ∈ poolBand, ∀ q ∈ c, q ≠ w) :
    AvoidsB [.lookup c ps] := by
  refine ⟨fun _ _ _ hp => by simp at hp, fun w hw c' ps' hp => ?_⟩
  simp only [List.mem_singleton, WInstr.lookup.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨ht w hw, hc w hw⟩

theorem avoidsB_of_all (code : WCode 32768) (h : code.all (avoidW poolBand) = true) : AvoidsB code := by
  refine ⟨fun w hw p hp => progAvoid_sound poolBand p (List.all_eq_true.mp h _ hp) w hw,
    fun w hw c ps hp => ?_⟩
  obtain ⟨h1, h2⟩ := avoidW_lookup poolBand c ps (List.all_eq_true.mp h _ hp)
  exact ⟨h1 w hw, fun q hq e => h2 q hq (e ▸ hw)⟩

theorem avoidsB_frame (read : ConstantBit 32768 → Bool) (a : Nat) (code : WCode 32768) (h : AvoidsB code)
    (m : List Bool) (st : ECDSAAdd.State) (w : Wire) (hw : w ∈ poolBand) :
    (ECDSAAdd.run ((specialize code a).instantiate read) m st).basis w = st.basis w := by
  induction code generalizing m st with
  | nil => simp [specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]
  | cons i code ih =>
    have ht : AvoidsB code := ⟨fun u hu p hp => h.1 u hu p (List.mem_cons_of_mem _ hp),
      fun u hu c ps hp => h.2 u hu c ps (List.mem_cons_of_mem _ hp)⟩
    rw [show i :: code = [i] ++ code from rfl, specialize_append, ECDSAAdd.ShorPort.Tmpl.instantiate_append,
      ECDSAAdd.run_append, ih ht]
    apply ECDSAAdd.run_preserves_outside _ _ _ w
    cases i with
    | literal p =>
      simp only [specialize, List.flatMap_cons, List.flatMap_nil, List.append_nil, WInstr.specialize,
        ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      exact h.1 w hw p (by simp)
    | lookup c ps =>
      simp only [specialize, List.flatMap_cons, List.flatMap_nil, List.append_nil, WInstr.specialize]
      obtain ⟨hT, hC⟩ := h.2 w hw c ps (by simp)
      exact lookup_frame read c ps a w hT hC

theorem poolBand_scrAll : ∀ w ∈ poolBand, w ∉ WEX.scrAllWires := by
  rw [WEX.scrAllWires, WEX.scrWires, pbPairWires_eq, pbShortWires_eq, pbExtraWires_eq]
  exact poolBand_not_of _ (by decide +kernel)

theorem poolBand_yWires : ∀ w ∈ poolBand, w ∉ WEX.yWires := by
  intro w hw h
  have h1 := (WEX.yWires_bounds w h).2
  rw [mem_poolBand] at hw
  dsimp only [Wire] at *
  omega

theorem root_ne_poolBand : ∀ w ∈ poolBand, ∀ q ∈ (some windowRoot : Option Wire), q ≠ w := by
  intro w hw q hq
  rw [Option.mem_def, Option.some.injEq] at hq
  subst hq
  rw [mem_poolBand] at hw
  unfold windowRoot
  dsimp only [Wire] at *
  omega

theorem scrDLookup_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (WEX.scrDPorts probeRows)] :=
  avoidsB_lookup (by rw [WEX.scrDPorts_targets]; exact poolBand_scrAll) root_ne_poolBand

theorem siteLookup_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (sitePorts probeRows)] :=
  avoidsB_lookup (by rw [sitePorts_targets]; exact poolBand_scrAll) root_ne_poolBand

theorem cornerLoad_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (WEX.cornerPorts probeRows)] := by
  refine avoidsB_lookup ?_ root_ne_poolBand
  rw [WEX.cornerPorts_targets]
  intro w hw hm
  rcases List.mem_append.mp hm with h | h
  · exact poolBand_scrAll w hw h
  · exact poolBand_yWires w hw h

theorem yLookup_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (WEX.yPorts probeRows)] :=
  avoidsB_lookup (by rw [WEX.yPorts_targets]; exact poolBand_yWires) root_ne_poolBand

theorem scrNegP_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires WEX.scrNegP :=
  WEX.neg_disjoint (negateYLayout streamLayout) streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths streamLayout streamLayout_widths).2 poolBand (poolBand_not_of _ (by decide +kernel))

theorem sfxCC_avoidsB : AvoidsB WEX.sfxCC := by
  simp only [WEX.sfxCC, WEX.scrDWires, pbShortWires_eq, pbExtraWires_eq]
  exact avoidsB_of_all _ (by unfold poolBand; decide +kernel)

theorem scrDMiddle_avoidsB : AvoidsB WEX.scrDMiddle := by
  simp only [WEX.scrDMiddle, pbPairWires_eq, pbShortWires_eq]
  repeat' (with_reducible apply avoidsB_append)
  all_goals exact avoidsB_of_all _ (by unfold poolBand; decide +kernel)

theorem scrD_avoidsB : AvoidsB scrDSite.code := by
  have hP : AvoidsB (wLiteral (n := 32768) WEX.scrNegP) := avoidsB_lit _ scrNegP_avoidB
  rw [scrDSite_code, WEX.sfxMidF, WEX.cornersE_split]
  repeat' (with_reducible apply avoidsB_append)
  all_goals first
    | (with_reducible exact hP)
    | exact scrDLookup_avoidsB
    | exact sfxCC_avoidsB
    | exact scrDMiddle_avoidsB
    | exact avoidsB_of_all _ (by unfold poolBand; decide +kernel)

theorem cornerNeg_avoidsB : AvoidsB WEX.cornerNeg :=
  avoidsB_sub (fun i hi => sfxMid_in_scrD _ (WEX.cornerNeg_sub i hi)) scrD_avoidsB

theorem scrCWrite_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires WEX.scrCWrite := by
  have h1 : ∀ w ∈ poolBand, w ∉ [streamLayout.doubleSelect] := poolBand_not_of _ (by decide +kernel)
  have h2 : ∀ w ∈ poolBand, w ∉ WEX.cSources := by
    rw [WEX.cSources, pbPairWires_eq, WEX.yWires]
    exact poolBand_not_of _ (by decide +kernel)
  have h3 : ∀ w ∈ poolBand, w ∉ WEX.scrDTargets := poolBand_not_of _ (by decide +kernel)
  intro w hw hm
  rcases ccxList_wires _ _ _ _ hm with h | h | h
  · exact h1 w hw (by simp [h])
  · exact h2 w hw h
  · exact h3 w hw h

theorem unit1_avoidsB : AvoidsB WEXUnlookup.cornerUnit₁.code := by
  rw [WEXUnlookup.cornerUnit₁_code, WEX.cornerUnit₁, WEX.cornerPre₁]
  refine avoidsB_append (avoidsB_append cornerLoad_avoidsB ?_) yLookup_avoidsB
  refine ⟨fun w hw p hp => ?_, fun w hw c ps hp => ?_⟩
  · rcases WEX.cornerA1_mem _ hp with h | h
    · exact scrD_avoidsB.1 w hw p (sfxMid_in_scrD _ h)
    · cases h
      exact scrCWrite_avoidB w hw
  · rcases WEX.cornerA1_mem _ hp with h | h
    · exact scrD_avoidsB.2 w hw c ps (sfxMid_in_scrD _ h)
    · cases h

theorem unit2_avoidsB : AvoidsB WEXUnlookup.cornerUnit₂.code := by
  apply avoidsB_sub _ scrD_avoidsB
  intro i hi
  rw [WEXUnlookup.cornerUnit₂_code, WEX.cornerUnit₂] at hi
  rcases List.mem_append.mp hi with h | h
  · exact sfxMid_in_scrD _ (WEX.cornerA2_sub _ h)
  · rw [List.mem_singleton.mp h]
    exact WEXUnlookup.scrD_unload_mem

theorem poolBand_flip : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program) := by
  intro w hw hm
  simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hm
  subst hm
  rw [mem_poolBand] at hw
  dsimp only [Wire] at *
  omega

theorem poolBand_head : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires scrHeadProgram :=
  progAvoid_sound poolBand scrHeadProgram (by unfold poolBand scrHeadProgram; decide +kernel)

theorem sfxTailF_avoidsB : AvoidsB WEX.sfxTailF :=
  avoidsB_of_all _ (by unfold poolBand; decide +kernel)

theorem flip_avoidsB : AvoidsB (wLiteral (n := 32768) [.X 838]) := avoidsB_lit _ poolBand_flip

theorem band_not_poolBand (w : Nat) (h : newBand w) : w ∉ poolBand := by
  rw [mem_poolBand]
  unfold newBand at h
  dsimp only [Wire] at *
  omega

theorem pair1Prog_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires pair1Prog :=
  wires_avoid_of pair1Prog_subset (fun w hw h => band_not_poolBand w (lists_band.1 w h) hw)

theorem pair2Prog_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires pair2Prog :=
  wires_avoid_of pair2Prog_subset (fun w hw h => band_not_poolBand w (lists_band.2.1 w h) hw)

theorem gf_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (pointDialogGenericFlag streamLayout) :=
  progAvoid_sound poolBand _ (by unfold poolBand; decide +kernel)

theorem zrep_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.zrep streamLayout) := by
  intro w hw hm
  rcases ECDSAAdd.Frontier.zrep_wires streamLayout _ hm with h | h
  · exact poolBand_not_of [streamLayout.point.finite] (by decide +kernel) w hw (by simp [h])
  · simp only [streamLayout_point, List.mem_range'_1] at h
    rw [mem_poolBand] at hw
    dsimp only [Wire] at *
    omega

theorem scrInArith_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires scrInArith := by
  simp only [WEX.scrInArith, WEX.scrInMid, pbPairWires_eq, pbShortWires_eq]
  exact progAvoid_sound poolBand _ (by unfold poolBand; decide +kernel)

theorem site1Arith_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires site1Arith := by
  intro w hw
  simp only [site1Arith, ECDSAAdd.wires_append, Finset.mem_union, not_or]
  exact ⟨⟨⟨scrInArith_avoidB w hw, gf_avoidB w hw⟩, zrep_avoidB w hw⟩, pair1Prog_avoidB w hw⟩

theorem site1_avoidsB : AvoidsB (site1 probeRows).code := by
  rw [site1_code]
  exact avoidsB_append (a := [_]) siteLookup_avoidsB
    (avoidsB_append (a := [_]) (avoidsB_lit site1Arith site1Arith_avoidB) siteLookup_avoidsB)

theorem site2Lookup_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (site2Ports probeRows)] :=
  avoidsB_lookup (by rw [site2Ports_targets]; exact fun w hw h => poolBand_scrAll w hw (site2_sub _ h)) root_ne_poolBand

theorem site2_avoidsB : AvoidsB (site2 probeRows).code := by
  rw [site2_code]
  exact avoidsB_append (a := [_]) site2Lookup_avoidsB
    (avoidsB_append (a := [_]) (avoidsB_lit pair2Prog pair2Prog_avoidB) site2Lookup_avoidsB)

theorem triple_avoidsB : AvoidsB (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).code := by
  have hw : ∀ w ∈ poolBand, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).wires :=
    poolBand_not_of _ (by decide +kernel)
  have ht : ∀ w ∈ poolBand, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).src :=
    poolBand_not_of _ (by decide +kernel)
  have hg : ∀ w ∈ poolBand, streamLayout.core.generic ≠ w := fun w hwm h =>
    poolBand_not_of [streamLayout.core.generic] (by decide +kernel) w hwm (by simp [h])
  rw [constSite_code]
  refine ⟨fun w hwm p hp => ?_, fun w hwm c ps hp => ?_⟩
  · rcases List.mem_cons.mp hp with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact wires_avoid_of (MeasuredCanonicalModLayout.program_wires_subset _ _ _) hw w hwm
    · cases List.mem_singleton.mp h
  · have hp' : c = some streamLayout.core.generic ∧
        ps = indexedPorts (streamLayout.recoveryConstant streamLayout.point.x).src (wFields probeRows .tripleX) true := by
      rcases List.mem_cons.mp hp with h | h
      · exact WInstr.lookup.inj h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact WInstr.lookup.inj (List.mem_singleton.mp h)
    obtain ⟨rfl, rfl⟩ := hp'
    refine ⟨fun hm => ht w hwm (by rw [indexed_targets] at hm; exact hm), fun q hq => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hg w hwm

theorem rowC_unit_avoidsB (u : UnitSite 32768) (hu : Block2.unit u ∈ WEXUnlookup.rowC) : AvoidsB u.code := by
  rcases List.mem_append.mp hu with h | h
  · obtain ⟨c, hc, he⟩ := List.mem_map.mp h
    cases c with
    | plain code => cases he
    | masked site =>
      cases he
      rcases rowL_masked_cases site (WEXUnlookup.rowHead_sub _ hc) with rfl | rfl | rfl | rfl
      · exact site1_avoidsB
      · exact triple_avoidsB
      · exact site2_avoidsB
      · exact scrD_avoidsB
  · simp only [WEXUnlookup.rowPost3, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Block2.unit.injEq] at h
    rcases h with rfl | rfl
    · exact unit1_avoidsB
    · exact unit2_avoidsB

theorem rowPost3_cleanB (read : ConstantBit 32768 → Bool) (a : Nat) (t : ECDSAAdd.State)
    (ht : Clean poolBand t.basis) : CodeClean2 read poolBand a WEXUnlookup.rowPost3 t := by
  rw [WEXUnlookup.rowPost3]
  refine ⟨trivial, fun m₁ _ => ⟨?_, fun m₂ _ => ⟨?_, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩⟩⟩
  · intro w hw
    rw [blockReference2, Block2.code, avoidsB_frame read a WEX.cornerNeg cornerNeg_avoidsB m₁ t w hw]
    exact ht w hw
  · intro w hw
    rw [blockReference2, Block2.code, avoidsB_frame read a WEXUnlookup.cornerUnit₁.code unit1_avoidsB m₂ _ w hw,
      blockReference2, Block2.code, avoidsB_frame read a WEX.cornerNeg cornerNeg_avoidsB m₁ t w hw]
    exact ht w hw

theorem rowC_clean_poolBand (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeClean2 (readConstant coeffs Q) poolBand a WEXUnlookup.rowC ⟨false, s⟩ := by
  have h := rowL_clean poolBand poolBand_pool poolBand_flip poolBand_head coeffs Q hQ hn a s hs
  rw [WEXUnlookup.rowL_eq] at h
  obtain ⟨h1, h2⟩ := clean_split _ _ _ _ _ _ h
  rw [WEXUnlookup.rowC]
  apply clean2_append _ _ _ _ _ _ (clean_map _ _ _ _ _ h1)
  intro m hm
  rw [reference2_map] at hm ⊢
  have h3 := h2 m hm
  rw [WEXUnlookup.rowPost] at h3
  exact rowPost3_cleanB _ _ _ h3.1

theorem poolBand_clean_in_rowCF (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeClean2 (readConstant coeffs Q) poolBand a (WEXFast.fforget WEXFast.rowCF) ⟨false, s⟩ := by
  rw [WEXFast.fforget_rowCF]
  exact rowC_clean_poolBand coeffs Q hQ hn a s hs

/-! ### Extending 15-bit placed instructions to 16-bit bank with extra path wire `14848` -/

def wideBits : List Wire := WEX.windowBits ++ [871]
def widePathBank : List Wire := PathShare.pathBank ++ [14848]

theorem mem_14848_poolBand : (14848 : Wire) ∈ poolBand := by
  decide

theorem wide_bits_paths_nodup : (wideBits ++ widePathBank).Nodup := by decide +kernel

theorem wide_root_nodup (q : Wire) (hq : q ∈ newSource) (h14848 : q ≠ 14848)
    (hold : (q :: WEX.windowBits ++ PathShare.pathBank).Nodup) :
    (q :: wideBits ++ widePathBank).Nodup := by
  rw [List.cons_append, List.nodup_cons]
  refine ⟨?_, wide_bits_paths_nodup⟩
  intro hm
  have hn := (List.nodup_cons.mp hold).1
  have ha := (WideSigned.Geometry.newSource_away .w16 q hq).1
  simp only [wideBits, widePathBank, List.mem_append, List.mem_singleton] at hm
  rcases hm with (h | h) | h | h
  · exact hn (List.mem_append_left _ h)
  · exact ha (by simpa [WideSigned.Geometry.extra, WideSigned.Geometry.Width.bits] using h)
  · exact hn (List.mem_append_right _ h)
  · exact h14848 h

theorem extend_literal_wide (p : ECDSAAdd.Program)
    (hs : ECDSAAdd.wires p ⊆ newSource.toFinset)
    (h14848 : (14848 : Wire) ∉ ECDSAAdd.wires p)
    (hp : PlacedPair WEX.windowBits PathShare.pathBank windowRoot (WInstr.literal (n := 32768) p)) :
    PlacedPair wideBits widePathBank windowRoot (WInstr.literal (n := 32768) p) := by
  intro v hv hm
  have ha := (WideSigned.Geometry.newSource_away .w16 v (List.mem_toFinset.mp (hs hm))).1
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hp _ (by simp) hm
  rcases List.mem_append.mp hv with hb | hp'
  · rcases List.mem_append.mp hb with h | h
    · exact hp v (by simp [h]) hm
    · exact ha (by simpa [WideSigned.Geometry.extra, WideSigned.Geometry.Width.bits] using h)
  · rcases List.mem_append.mp hp' with h | h
    · exact hp v (by simp [h]) hm
    · rw [List.mem_singleton.mp h] at hm
      exact h14848 hm

theorem extend_lookup_wide (c : Option Wire) (ps : List (LookupPort 32768))
    (hs : (∀ q ∈ c, q ∈ newSource) ∧ portTargets ps ⊆ newSource)
    (h14848 : (14848 : Wire) ∉ portTargets ps ∧ ∀ q ∈ c, q ≠ 14848)
    (hp : PlacedPair WEX.windowBits PathShare.pathBank windowRoot (WInstr.lookup c ps)) :
    PlacedPair wideBits widePathBank windowRoot (WInstr.lookup c ps) := by
  have hq : lookupRoot windowRoot c ∈ newSource := by
    cases c with
    | none =>
      change windowRoot ∈ newSource
      exact newSource_of_bounds [windowRoot] (by decide) (by simp)
    | some q => exact hs.1 q rfl
  have hq48 : lookupRoot windowRoot c ≠ 14848 := by
    cases c with
    | none => decide
    | some q => exact h14848.2 q rfl
  refine ⟨wide_root_nodup _ hq hq48 hp.1, hp.2.1, hp.2.2.1, ?_⟩
  intro v hv ht
  have ha := (WideSigned.Geometry.newSource_away .w16 v (hs.2 ht)).1
  rcases List.mem_cons.mp hv with rfl | hv
  · exact List.disjoint_left.mp hp.2.2.2 (by simp) ht
  rcases List.mem_cons.mp hv with rfl | hv
  · exact List.disjoint_left.mp hp.2.2.2 (by simp) ht
  rcases List.mem_append.mp hv with hb | hp'
  · rcases List.mem_append.mp hb with h | h
    · exact List.disjoint_left.mp hp.2.2.2 (by simp [h]) ht
    · exact ha (by simpa [WideSigned.Geometry.extra, WideSigned.Geometry.Width.bits] using h)
  · rcases List.mem_append.mp hp' with h | h
    · exact List.disjoint_left.mp hp.2.2.2 (by simp [h]) ht
    · rw [List.mem_singleton.mp h] at ht
      exact h14848.1 ht

theorem extend_site_wide (B : PathShare.Bank) (hbits : B.bits = wideBits) (hpaths : B.paths = widePathBank)
    (u : UnitSite 32768) (hu : Block2.unit u ∈ WEXUnlookup.rowC)
    (hg : SiteGeoP PathShare.bank15 u.clear) :
    SiteGeoP B (WideSigned.Rows.site (WideSigned.Geometry.rows .w16) u.clear) := by
  have hsup := WideSigned.Geometry.site_support u hu hg.kind
  have hav := rowC_unit_avoidsB u hu
  have hclr : ∀ i ∈ u.clear.code, i ∈ u.code := by
    intro i hi
    rcases List.mem_append.mp hu with h | h
    · obtain ⟨b, _, he⟩ := List.mem_map.mp h
      cases b with
      | plain _ => cases he
      | masked s => cases he; exact hi
    · simp only [WEXUnlookup.rowPost3, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
        Block2.unit.injEq, false_or, or_false] at h
      rcases h with rfl | rfl <;>
      · simp only [WEXUnlookup.cornerUnit₁, WEXUnlookup.cornerUnit₂, WEXUnlookup.ySite,
          WEXUnlookup.scrDClear, MaskedSite.code, MaskedSite.prefix, UnitSite.code,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        rcases hi with rfl | rfl <;> simp
  refine ⟨?_, WideSigned.Rows.kind _ _ hg.kind⟩
  intro i hi
  rw [WideSigned.Rows.site_code] at hi
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hi
  have hp := hg.placed old ho
  have hmem := hclr old ho
  cases old with
  | literal p =>
    rw [hbits, hpaths]
    exact extend_literal_wide p (hsup.1 p ho) (hav.1 14848 mem_14848_poolBand p hmem) hp
  | lookup c ps =>
    have he := extend_lookup_wide c ps (hsup.2 c ps ho) (hav.2 14848 mem_14848_poolBand c ps hmem)
      (placed_implies_pair WEX.windowBits PathShare.pathBank windowRoot _ hp)
    have ht : portTargets (WideSigned.Rows.ports (WideSigned.Geometry.rows .w16) ps) = portTargets ps :=
      WideSigned.Rows.targets _ _
    rw [hbits, hpaths]
    exact ⟨he.1, ht ▸ hp.2.1, ht ▸ he.2.2.2⟩

theorem extend_unit_wide (B : PathShare.Bank) (hbits : B.bits = wideBits) (hpaths : B.paths = widePathBank)
    (u : UnitSite 32768) (hu : Block2.unit u ∈ WEXUnlookup.rowC)
    (hg : UnitGeoP PathShare.bank15 u) :
    UnitGeoP B (WideSigned.Rows.unit (WideSigned.Geometry.rows .w16) u) := by
  have hav := rowC_unit_avoidsB u hu
  refine ⟨?_, extend_site_wide B hbits hpaths u hu hg.site⟩
  intro i hi
  rw [WideSigned.Rows.unit_code] at hi
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hi
  have hp := hg.placed old ho
  have hmem : old ∈ erase2 WEXUnlookup.rowC := List.mem_flatMap.mpr ⟨.unit u, hu, ho⟩
  have hext : PlacedPair wideBits widePathBank windowRoot old := by
    cases old with
    | literal p =>
      exact extend_literal_wide p (W15C.rowC_lit_new p hmem) (hav.1 14848 mem_14848_poolBand p ho) hp
    | lookup c ps =>
      exact extend_lookup_wide c ps (W15C.rowC_look_new c ps hmem) (hav.2 14848 mem_14848_poolBand c ps ho) hp
  rw [hbits, hpaths]
  exact WideSigned.Geometry.placed_lift (WideSigned.Geometry.rows .w16) wideBits widePathBank old hext

/-! ### Four-wire flag hosting (`14874..14877` on `14111, 19816, 838, 14112`) -/

def hostWire4 : Wire := 14877
def hostWire5 : Wire := 14876
def hostWire6 : Wire := 14875
def hostWire7 : Wire := 14874

def hostCtl4 : Wire := 14111
def hostCtl5 : Wire := 19816
def hostCtl6 : Wire := 838
def hostCtl7 : Wire := 14112

def perm4 (w : Wire) : Wire :=
  if w = 14877 then 14111
  else if w = 14111 then 14877
  else if w = 14876 then 19816
  else if w = 19816 then 14876
  else if w = 14875 then 838
  else if w = 838 then 14875
  else if w = 14874 then 14112
  else if w = 14112 then 14874
  else w

theorem perm4_involutive : Function.Involutive perm4 := by
  intro w
  dsimp only [Wire] at w
  unfold perm4
  by_cases h1 : w = 14877; · simp [h1]
  by_cases h2 : w = 14111; · simp [h2]
  by_cases h3 : w = 14876; · simp [h3]
  by_cases h4 : w = 19816; · simp [h4]
  by_cases h5 : w = 14875; · simp [h5]
  by_cases h6 : w = 838; · simp [h6]
  by_cases h7 : w = 14874; · simp [h7]
  by_cases h8 : w = 14112; · simp [h8]
  simp [h1, h2, h3, h4, h5, h6, h7, h8]

theorem perm4_injective : Function.Injective perm4 := perm4_involutive.injective

def enc4 : ECDSAAdd.Program :=
  [.X 14111,
   .CX 838 19816, .X 19816,
   .CX 14113 838, .CX 19815 838, .CX 19814 838, .CX 14112 838,
   .CX 14112 19815, .CX 14112 19814,
   .CCX 19815 19814 14112]

def dec4 : ECDSAAdd.Program :=
  [.CCX 19815 19814 14112,
   .CX 14112 19814, .CX 14112 19815,
   .CX 14112 838, .CX 19814 838, .CX 19815 838, .CX 14113 838,
   .X 19816, .CX 838 19816,
   .X 14111]

def host4Set (p : ECDSAAdd.Program) : Prop :=
  (14877 ∈ ECDSAAdd.wires p ∨ 14876 ∈ ECDSAAdd.wires p ∨
    14875 ∈ ECDSAAdd.wires p ∨ 14874 ∈ ECDSAAdd.wires p) ∧
  14111 ∉ ECDSAAdd.wires p ∧ 19816 ∉ ECDSAAdd.wires p ∧
  838 ∉ ECDSAAdd.wires p ∧ 14112 ∉ ECDSAAdd.wires p ∧
  19815 ∉ ECDSAAdd.wires p ∧ 19814 ∉ ECDSAAdd.wires p

instance (p : ECDSAAdd.Program) : Decidable (host4Set p) :=
  inferInstanceAs (Decidable
    ((14877 ∈ ECDSAAdd.wires p ∨ 14876 ∈ ECDSAAdd.wires p ∨
      14875 ∈ ECDSAAdd.wires p ∨ 14874 ∈ ECDSAAdd.wires p) ∧
    14111 ∉ ECDSAAdd.wires p ∧ 19816 ∉ ECDSAAdd.wires p ∧
    838 ∉ ECDSAAdd.wires p ∧ 14112 ∉ ECDSAAdd.wires p ∧
    19815 ∉ ECDSAAdd.wires p ∧ 19814 ∉ ECDSAAdd.wires p))

def hostBlock7 (p : ECDSAAdd.Program) : ECDSAAdd.Program :=
  if host4Set p then
    enc4 ++ progRelabel perm4 (hostBlock3 p) ++ dec4
  else hostBlock3 p

def hostExtra (p : ECDSAAdd.Program) : Nat :=
  if host4Set p then 2 else 0

theorem hostExtra_le (p : ECDSAAdd.Program) : hostExtra p ≤ 2 := by
  unfold hostExtra; split_ifs <;> omega

theorem hostExtra_zero_of (p : ECDSAAdd.Program)
    (h : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires p) : hostExtra p = 0 := by
  have hn : ¬host4Set p := by
    rintro ⟨h1 | h2 | h3 | h4, -⟩
    · exact h 14877 (by decide) h1
    · exact h 14876 (by decide) h2
    · exact h 14875 (by decide) h3
    · exact h 14874 (by decide) h4
  simp [hostExtra, hn]

theorem hostBlock7_meas (p : ECDSAAdd.Program) :
    ECDSAAdd.measurementCount (hostBlock7 p) = ECDSAAdd.measurementCount p := by
  unfold hostBlock7
  split_ifs
  · simp [ECDSAAdd.measurementCount_append, enc4, dec4, ECDSAAdd.measurementCount,
      relabel_meas, hostBlock3_meas]
  · exact hostBlock3_meas p

theorem hostBlock7_toffoli (p : ECDSAAdd.Program) :
    ECDSAAdd.toffoliCount (hostBlock7 p) = ECDSAAdd.toffoliCount p + hostExtra p := by
  unfold hostBlock7 hostExtra
  split_ifs
  · simp only [ECDSAAdd.toffoliCount_append, relabel_toffoli, hostBlock3_toffoli]
    have h1 : ECDSAAdd.toffoliCount enc4 = 1 := rfl
    have h2 : ECDSAAdd.toffoliCount dec4 = 1 := rfl
    omega
  · simp [hostBlock3_toffoli]

theorem hostBlock7_slots {n : Nat} (p : ECDSAAdd.Program) :
    Bridge.tmplSlots (WEX.literalT (n := n) (hostBlock7 p)) ≤
      Bridge.tmplSlots (WEX.literalT (n := n) p) + 26 := by
  have h3 := hostBlock3_slots (n := n) p
  unfold hostBlock7
  split_ifs
  · have hr := relabel_slots (n := n) perm4 (hostBlock3 p)
    simp only [Bridge.tmplSlots, WEX.literalT, List.map_append, List.sum_append] at h3 hr ⊢
    rw [hr]
    have h1 : (List.map Bridge.TInstr.slots (List.map (Bridge.TInstr.lit (n := n)) enc4)).sum = 10 := by
      simp [enc4, Bridge.TInstr.slots]
    have h2 : (List.map Bridge.TInstr.slots (List.map (Bridge.TInstr.lit (n := n)) dec4)).sum = 10 := by
      simp [dec4, Bridge.TInstr.slots]
    omega
  · omega

theorem enc4_valid : ∀ i ∈ enc4, ECDSAAdd.Challenge.instructionValid i := by
  intro i hi
  simp only [enc4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ECDSAAdd.Challenge.instructionValid]

theorem dec4_valid : ∀ i ∈ dec4, ECDSAAdd.Challenge.instructionValid i := by
  intro i hi
  simp only [dec4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ECDSAAdd.Challenge.instructionValid]

theorem hostBlock7_valid (p : ECDSAAdd.Program) (h : ∀ i ∈ p, ECDSAAdd.Challenge.instructionValid i) :
    ∀ i ∈ hostBlock7 p, ECDSAAdd.Challenge.instructionValid i := by
  unfold hostBlock7
  split_ifs
  · intro i hi
    simp only [List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact enc4_valid i hi
    · exact relabel_valid perm4 perm4_injective _ (hostBlock3_valid p h) i hi
    · exact dec4_valid i hi
  · exact hostBlock3_valid p h

def FlagInv7 (b : BasisState) : Prop :=
  b 14111 = true ∧
  b 19816 = !b 838 ∧
  b 838 = (b 14113 ^^ b 19815 ^^ b 19814 ^^ b 14112) ∧
  (b 19815 = true → b 19814 = false) ∧
  (b 14112 = true → b 19815 = false ∧ b 19814 = false)

def Clean4 (b : BasisState) : Prop :=
  b 14877 = false ∧ b 14876 = false ∧ b 14875 = false ∧ b 14874 = false

def encBasis (b : BasisState) : BasisState :=
  ECDSAAdd.writeBit
    (ECDSAAdd.writeBit
      (ECDSAAdd.writeBit
        (ECDSAAdd.writeBit
          (ECDSAAdd.writeBit
            (ECDSAAdd.writeBit b 14111 false)
            19816 false)
          838 false)
        14112 false)
      19815 (b 19815 ^^ b 14112))
    19814 (b 19814 ^^ b 14112)

private theorem enc4_step_eq (ph : Bool) (b : BasisState) (m : List Bool) :
    ECDSAAdd.run enc4 m ⟨ph, b⟩ =
      let b1 := ECDSAAdd.writeBit b 14111 (!b 14111)
      let b2 := ECDSAAdd.writeBit b1 19816 (b1 19816 ^^ b1 838)
      let b3 := ECDSAAdd.writeBit b2 19816 (!b2 19816)
      let b4 := ECDSAAdd.writeBit b3 838 (b3 838 ^^ b3 14113)
      let b5 := ECDSAAdd.writeBit b4 838 (b4 838 ^^ b4 19815)
      let b6 := ECDSAAdd.writeBit b5 838 (b5 838 ^^ b5 19814)
      let b7 := ECDSAAdd.writeBit b6 838 (b6 838 ^^ b6 14112)
      let b8 := ECDSAAdd.writeBit b7 19815 (b7 19815 ^^ b7 14112)
      let b9 := ECDSAAdd.writeBit b8 19814 (b8 19814 ^^ b8 14112)
      let b10 := ECDSAAdd.writeBit b9 14112 (b9 14112 ^^ (b9 19815 && b9 19814))
      ⟨ph, b10⟩ := rfl

private theorem dec4_step_eq (ph : Bool) (b : BasisState) (m : List Bool) :
    ECDSAAdd.run dec4 m ⟨ph, b⟩ =
      let b1 := ECDSAAdd.writeBit b 14112 (b 14112 ^^ (b 19815 && b 19814))
      let b2 := ECDSAAdd.writeBit b1 19814 (b1 19814 ^^ b1 14112)
      let b3 := ECDSAAdd.writeBit b2 19815 (b2 19815 ^^ b2 14112)
      let b4 := ECDSAAdd.writeBit b3 838 (b3 838 ^^ b3 14112)
      let b5 := ECDSAAdd.writeBit b4 838 (b4 838 ^^ b4 19814)
      let b6 := ECDSAAdd.writeBit b5 838 (b5 838 ^^ b5 19815)
      let b7 := ECDSAAdd.writeBit b6 838 (b6 838 ^^ b6 14113)
      let b8 := ECDSAAdd.writeBit b7 19816 (!b7 19816)
      let b9 := ECDSAAdd.writeBit b8 19816 (b8 19816 ^^ b8 838)
      let b10 := ECDSAAdd.writeBit b9 14111 (!b9 14111)
      ⟨ph, b10⟩ := rfl

private theorem wb_hit (b : BasisState) (k : Wire) (v : Bool) : ECDSAAdd.writeBit b k v k = v := by
  simp [ECDSAAdd.writeBit]

private theorem wb_miss (b : BasisState) {k w : Wire} (v : Bool) (h : w ≠ k) :
    ECDSAAdd.writeBit b k v w = b w := by
  simp [ECDSAAdd.writeBit, h]

theorem enc4_run (s : ECDSAAdd.State) (hf : FlagInv7 s.basis) (m : List Bool) :
    ECDSAAdd.run enc4 m s = ⟨s.phase, encBasis s.basis⟩ := by
  obtain ⟨h11, h16, h838, hDI, hH⟩ := hf
  cases s with
  | mk ph b =>
    dsimp only at h11 h16 h838 hDI hH
    rw [enc4_step_eq]
    dsimp only
    congr 1
    funext w
    set b1 := ECDSAAdd.writeBit b 14111 (!b 14111)
    set b2 := ECDSAAdd.writeBit b1 19816 (b1 19816 ^^ b1 838)
    set b3 := ECDSAAdd.writeBit b2 19816 (!b2 19816)
    set b4 := ECDSAAdd.writeBit b3 838 (b3 838 ^^ b3 14113)
    set b5 := ECDSAAdd.writeBit b4 838 (b4 838 ^^ b4 19815)
    set b6 := ECDSAAdd.writeBit b5 838 (b5 838 ^^ b5 19814)
    set b7 := ECDSAAdd.writeBit b6 838 (b6 838 ^^ b6 14112)
    set b8 := ECDSAAdd.writeBit b7 19815 (b7 19815 ^^ b7 14112)
    set b9 := ECDSAAdd.writeBit b8 19814 (b8 19814 ^^ b8 14112)
    have e1_11 : b1 14111 = false := by simp only [b1, wb_hit, h11]; rfl
    have e1_o : ∀ k, k ≠ 14111 → b1 k = b k := fun k hk => wb_miss b _ hk
    have e2_16 : b2 19816 = true := by
      simp only [b2, wb_hit, e1_o 19816 (by decide), e1_o 838 (by decide), h16]; cases b 838 <;> rfl
    have e3_16 : b3 19816 = false := by simp only [b3, wb_hit, e2_16]; rfl
    have e3_o : ∀ k, k ≠ 19816 → b3 k = b1 k := fun k hk =>
      (wb_miss b2 _ hk).trans (wb_miss b1 _ hk)
    have e4_838 : b4 838 = (b 838 ^^ b 14113) := by
      have c1 : b3 838 = b 838 := (e3_o 838 (by decide)).trans (e1_o 838 (by decide))
      have c2 : b3 14113 = b 14113 := (e3_o 14113 (by decide)).trans (e1_o 14113 (by decide))
      simp only [b4, wb_hit, c1, c2]
    have e5_838 : b5 838 = (b 838 ^^ b 14113 ^^ b 19815) := by
      have c3 : b4 19815 = b 19815 := (wb_miss b3 _ (by decide)).trans ((e3_o 19815 (by decide)).trans (e1_o 19815 (by decide)))
      simp only [b5, wb_hit, e4_838, c3]
    have e6_838 : b6 838 = (b 838 ^^ b 14113 ^^ b 19815 ^^ b 19814) := by
      have c4 : b5 19814 = b 19814 := (wb_miss b4 _ (by decide)).trans ((wb_miss b3 _ (by decide)).trans ((e3_o 19814 (by decide)).trans (e1_o 19814 (by decide))))
      simp only [b6, wb_hit, e5_838, c4]
    have e7_838 : b7 838 = false := by
      have c5 : b6 14112 = b 14112 := (wb_miss b5 _ (by decide)).trans ((wb_miss b4 _ (by decide)).trans ((wb_miss b3 _ (by decide)).trans ((e3_o 14112 (by decide)).trans (e1_o 14112 (by decide)))))
      simp only [b7, wb_hit, e6_838, c5, h838]
      cases b 14113 <;> cases b 19815 <;> cases b 19814 <;> cases b 14112 <;> rfl
    have e7_o : ∀ k, k ≠ 838 → b7 k = b3 k := fun k hk =>
      (wb_miss b6 _ hk).trans ((wb_miss b5 _ hk).trans ((wb_miss b4 _ hk).trans (wb_miss b3 _ hk)))
    have e8_15 : b8 19815 = (b 19815 ^^ b 14112) := by
      simp only [b8, wb_hit, e7_o 19815 (by decide), e3_o 19815 (by decide), e1_o 19815 (by decide),
        e7_o 14112 (by decide), e3_o 14112 (by decide), e1_o 14112 (by decide)]
    have e9_14 : b9 19814 = (b 19814 ^^ b 14112) := by
      have d1 : b8 19814 = b7 19814 := wb_miss b7 _ (by decide)
      have d2 : b8 14112 = b7 14112 := wb_miss b7 _ (by decide)
      simp only [b9, wb_hit, d1, d2,
        e7_o 19814 (by decide), e3_o 19814 (by decide), e1_o 19814 (by decide),
        e7_o 14112 (by decide), e3_o 14112 (by decide), e1_o 14112 (by decide)]
    have e9_15 : b9 19815 = (b 19815 ^^ b 14112) := (wb_miss b8 _ (by decide)).trans e8_15
    have e9_12 : b9 14112 = b 14112 :=
      (wb_miss b8 _ (by decide)).trans ((wb_miss b7 _ (by decide)).trans
        ((e7_o 14112 (by decide)).trans ((e3_o 14112 (by decide)).trans (e1_o 14112 (by decide)))))
    have e10_12 : ECDSAAdd.writeBit b9 14112 (b9 14112 ^^ (b9 19815 && b9 19814)) 14112 = false := by
      rw [wb_hit, e9_12, e9_15, e9_14]
      cases hD : b 19815 <;> cases hI : b 19814 <;> cases hQ : b 14112 <;> simp_all
    by_cases w12 : w = 14112
    · subst w12; rw [e10_12]; simp [encBasis, ECDSAAdd.writeBit]
    rw [wb_miss b9 _ w12]
    by_cases w14 : w = 19814
    · subst w14; rw [e9_14]; simp [encBasis, ECDSAAdd.writeBit]
    change b9 w = _; simp only [b9, wb_miss b8 _ w14]
    by_cases w15 : w = 19815
    · subst w15; rw [e8_15]; simp [encBasis, ECDSAAdd.writeBit]
    change b8 w = _; simp only [b8, wb_miss b7 _ w15]
    by_cases w838 : w = 838
    · subst w838; rw [e7_838]; simp [encBasis, ECDSAAdd.writeBit]
    rw [e7_o w w838]
    by_cases w16 : w = 19816
    · subst w16; rw [e3_16]; simp [encBasis, ECDSAAdd.writeBit]
    rw [e3_o w w16]
    by_cases w11 : w = 14111
    · subst w11; rw [e1_11]; simp [encBasis, ECDSAAdd.writeBit]
    rw [e1_o w w11]
    simp [encBasis, ECDSAAdd.writeBit, w14, w15, w12, w838, w16, w11]

theorem dec4_run (t : ECDSAAdd.State) (hf : FlagInv7 t.basis) (m : List Bool) :
    ECDSAAdd.run dec4 m ⟨t.phase, encBasis t.basis⟩ = t := by
  obtain ⟨h11, h16, h838, hDI, hH⟩ := hf
  cases t with
  | mk ph b =>
    dsimp only at h11 h16 h838 hDI hH
    rw [dec4_step_eq]
    dsimp only
    congr 1
    funext w
    set b0 := encBasis b
    set b1 := ECDSAAdd.writeBit b0 14112 (b0 14112 ^^ (b0 19815 && b0 19814))
    set b2 := ECDSAAdd.writeBit b1 19814 (b1 19814 ^^ b1 14112)
    set b3 := ECDSAAdd.writeBit b2 19815 (b2 19815 ^^ b2 14112)
    set b4 := ECDSAAdd.writeBit b3 838 (b3 838 ^^ b3 14112)
    set b5 := ECDSAAdd.writeBit b4 838 (b4 838 ^^ b4 19814)
    set b6 := ECDSAAdd.writeBit b5 838 (b5 838 ^^ b5 19815)
    set b7 := ECDSAAdd.writeBit b6 838 (b6 838 ^^ b6 14113)
    set b8 := ECDSAAdd.writeBit b7 19816 (!b7 19816)
    set b9 := ECDSAAdd.writeBit b8 19816 (b8 19816 ^^ b8 838)
    have f14 : b0 19814 = (b 19814 ^^ b 14112) := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f15 : b0 19815 = (b 19815 ^^ b 14112) := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f12 : b0 14112 = false := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f838 : b0 838 = false := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f16 : b0 19816 = false := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f11 : b0 14111 = false := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f13 : b0 14113 = b 14113 := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have e1_12 : b1 14112 = b 14112 := by
      simp only [b1, wb_hit, f12, f15, f14]
      cases hD : b 19815 <;> cases hI : b 19814 <;> cases hQ : b 14112 <;> simp_all
    have e2_14 : b2 19814 = b 19814 := by
      have d0 : b1 19814 = b0 19814 := wb_miss b0 _ (by decide)
      simp only [b2, wb_hit, d0, f14, e1_12]
      cases b 19814 <;> cases b 14112 <;> rfl
    have e3_15 : b3 19815 = b 19815 := by
      have c1 : b2 19815 = b0 19815 := (wb_miss b1 _ (by decide)).trans (wb_miss b0 _ (by decide))
      have c2 : b2 14112 = b1 14112 := wb_miss b1 _ (by decide)
      simp only [b3, wb_hit, c1, f15, c2, e1_12]
      cases b 19815 <;> cases b 14112 <;> rfl
    have e3_14 : b3 19814 = b 19814 := (wb_miss b2 _ (by decide)).trans e2_14
    have e3_12 : b3 14112 = b 14112 := (wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans e1_12)
    have e3_838 : b3 838 = false :=
      (wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans ((wb_miss b0 _ (by decide)).trans f838))
    have e3_13 : b3 14113 = b 14113 :=
      (wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans ((wb_miss b0 _ (by decide)).trans f13))
    have e4_838 : b4 838 = (false ^^ b 14112) := by simp only [b4, wb_hit, e3_838, e3_12]
    have e5_838 : b5 838 = (false ^^ b 14112 ^^ b 19814) := by
      have c4 : b4 19814 = b 19814 := (wb_miss b3 _ (by decide)).trans e3_14
      simp only [b5, wb_hit, e4_838, c4]
    have e6_838 : b6 838 = (false ^^ b 14112 ^^ b 19814 ^^ b 19815) := by
      have c5 : b5 19815 = b 19815 := (wb_miss b4 _ (by decide)).trans ((wb_miss b3 _ (by decide)).trans e3_15)
      simp only [b6, wb_hit, e5_838, c5]
    have e7_838 : b7 838 = b 838 := by
      have c6 : b6 14113 = b 14113 := (wb_miss b5 _ (by decide)).trans ((wb_miss b4 _ (by decide)).trans ((wb_miss b3 _ (by decide)).trans e3_13))
      simp only [b7, wb_hit, e6_838, c6, h838]
      cases b 14113 <;> cases b 19815 <;> cases b 19814 <;> cases b 14112 <;> rfl
    have e7_o : ∀ k, k ≠ 838 → b7 k = b3 k := fun k hk =>
      (wb_miss b6 _ hk).trans ((wb_miss b5 _ hk).trans ((wb_miss b4 _ hk).trans (wb_miss b3 _ hk)))
    have e8_16 : b8 19816 = true := by
      have c7 : b7 19816 = false :=
        (e7_o 19816 (by decide)).trans ((wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans ((wb_miss b0 _ (by decide)).trans f16)))
      simp only [b8, wb_hit, c7]; rfl
    have e9_16 : b9 19816 = b 19816 := by
      have c8 : b8 838 = b 838 := (wb_miss b7 _ (by decide)).trans e7_838
      simp only [b9, wb_hit, e8_16, c8, h16]
      cases b 838 <;> rfl
    have e10_11 : ECDSAAdd.writeBit b9 14111 (!b9 14111) 14111 = b 14111 := by
      have c9 : b9 14111 = false :=
        (wb_miss b8 _ (by decide)).trans ((wb_miss b7 _ (by decide)).trans
          ((e7_o 14111 (by decide)).trans ((wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans ((wb_miss b0 _ (by decide)).trans f11)))))
      rw [wb_hit, c9, h11]; rfl
    by_cases w11 : w = 14111
    · subst w11; exact e10_11
    rw [wb_miss b9 _ w11]
    by_cases w16 : w = 19816
    · subst w16; exact e9_16
    change b9 w = _; simp only [b9, wb_miss b8 _ w16]; simp only [b8, wb_miss b7 _ w16]
    by_cases w838 : w = 838
    · subst w838; exact e7_838
    rw [e7_o w w838]
    by_cases w15 : w = 19815
    · subst w15; exact e3_15
    change b3 w = _; simp only [b3, wb_miss b2 _ w15]
    by_cases w14 : w = 19814
    · subst w14; exact e2_14
    change b2 w = _; simp only [b2, wb_miss b1 _ w14]
    by_cases w12 : w = 14112
    · subst w12; exact e1_12
    change b1 w = _; simp only [b1, wb_miss b0 _ w12]
    simp [b0, encBasis, ECDSAAdd.writeBit, w14, w15, w12, w838, w16, w11]

theorem hostBlock3_avoid_extra (p : ECDSAAdd.Program) (w : Wire)
    (hw : w ∉ ECDSAAdd.wires p)
    (h1 : w ≠ windowRoot) (h2 : w ≠ hostWire)
    (h3 : w ≠ hostCtl) (h4 : w ≠ hostWire2)
    (h5 : w ≠ hostCtl3) (h6 : w ≠ hostWire3) :
    w ∉ ECDSAAdd.wires (hostBlock3 p) := by
  have hb0 : w ∉ ECDSAAdd.wires (hostP hostWire windowRoot p) := by
    intro hm
    rcases hostP_wires_mem _ _ _ _ hm with e | e | e
    · exact h1 e
    · exact h2 e
    · exact hw e
  have hb1 : w ∉ ECDSAAdd.wires (hostBlock p) := by
    unfold hostBlock
    split
    · intro hm
      rcases hostP_wires_mem _ _ _ _ hm with e | e | e
      · exact h3 e
      · exact h4 e
      · exact hb0 e
    · exact hb0
  unfold hostBlock3
  split
  · intro hm
    rcases hostP_wires_mem _ _ _ _ hm with e | e | e
    · exact h5 e
    · exact h6 e
    · exact hb1 e
  · exact hb1

theorem pullS_perm4_encBasis (ph : Bool) (b : BasisState) (hc : Clean4 b) :
    pullS perm4 ⟨ph, encBasis b⟩ = ⟨ph, encBasis b⟩ := by
  obtain ⟨c7, c6, c5, c4⟩ := hc
  simp only [pullS, ECDSAAdd.State.mk.injEq, true_and]
  funext w
  unfold perm4
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · subst h1; simp [encBasis, ECDSAAdd.writeBit, Function.update, c7]
  · subst h2; simp [encBasis, ECDSAAdd.writeBit, Function.update, c7]
  · subst h3; simp [encBasis, ECDSAAdd.writeBit, Function.update, c6]
  · subst h4; simp [encBasis, ECDSAAdd.writeBit, Function.update, c6]
  · subst h5; simp [encBasis, ECDSAAdd.writeBit, Function.update, c5]
  · subst h6; simp [encBasis, ECDSAAdd.writeBit, Function.update, c5]
  · subst h7; simp [encBasis, ECDSAAdd.writeBit, Function.update, c4]
  · subst h8; simp [encBasis, ECDSAAdd.writeBit, Function.update, c4]
  · rfl

theorem hostBlock7_run (p : ECDSAAdd.Program) (hR : windowRoot ∉ ECDSAAdd.wires p) (m : List Bool)
    (s : ECDSAAdd.State) (h1 : s.basis windowRoot = true) (h2 : s.basis hostWire = false)
    (h3 : (ECDSAAdd.run p m s).basis hostWire = false)
    (h4 : hostWire2 ∈ ECDSAAdd.wires p → hostCtl ∉ ECDSAAdd.wires p →
      s.basis hostCtl = true ∧ s.basis hostWire2 = false ∧ (ECDSAAdd.run p m s).basis hostWire2 = false)
    (h5 : hostWire3 ∈ ECDSAAdd.wires p → hostCtl3 ∉ ECDSAAdd.wires p →
      s.basis hostCtl3 = true ∧ s.basis hostWire3 = false ∧ (ECDSAAdd.run p m s).basis hostWire3 = false)
    (h7 : host4Set p → FlagInv7 s.basis ∧ Clean4 s.basis ∧ Clean4 (ECDSAAdd.run p m s).basis ∧
      (ECDSAAdd.run p m s).basis 14113 = s.basis 14113) :
    ECDSAAdd.run (hostBlock7 p) m s = ECDSAAdd.run p m s := by
  have inner := hostBlock3_run p hR m s h1 h2 h3 h4 h5
  unfold hostBlock7
  split_ifs with hcond
  · obtain ⟨hf, hc0, hc1, hG⟩ := h7 hcond
    let q := hostBlock3 p
    have hq11 : (14111 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 14111 hcond.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq16 : (19816 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 19816 hcond.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq838 : (838 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 838 hcond.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq12 : (14112 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 14112 hcond.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq15 : (19815 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 19815 hcond.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq14 : (19814 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 19814 hcond.2.2.2.2.2.2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hme : ECDSAAdd.measurementCount enc4 = 0 := rfl
    have hmc : ECDSAAdd.measurementCount (enc4 ++ progRelabel perm4 q) = ECDSAAdd.measurementCount (progRelabel perm4 q) := by
      rw [ECDSAAdd.measurementCount_append, hme, Nat.zero_add]
    rw [ECDSAAdd.run_append, ECDSAAdd.run_append, hmc, hme, List.take_zero, List.drop_zero,
      enc4_run s hf List.nil, run_relabel perm4 perm4_involutive q,
      pullS_perm4_encBasis s.phase s.basis hc0]
    have hqrun : ECDSAAdd.run q (m.take (ECDSAAdd.measurementCount (progRelabel perm4 q)))
        ⟨s.phase, encBasis s.basis⟩ = ⟨(ECDSAAdd.run p m s).phase, encBasis (ECDSAAdd.run p m s).basis⟩ := by
      have hupd (ph : Bool) (b : BasisState) (w : Wire) (v : Bool) (hw : w ∉ ECDSAAdd.wires q) :
          ECDSAAdd.run q m ⟨ph, ECDSAAdd.writeBit b w v⟩ =
            ⟨(ECDSAAdd.run q m ⟨ph, b⟩).phase, ECDSAAdd.writeBit (ECDSAAdd.run q m ⟨ph, b⟩).basis w v⟩ :=
        run_update_outside q m ⟨ph, b⟩ w v hw
      rw [relabel_meas, ECDSAAdd.run_take]
      unfold encBasis
      rw [hupd _ _ 19814 _ hq14, hupd _ _ 19815 _ hq15, hupd _ _ 14112 _ hq12,
          hupd _ _ 838 _ hq838, hupd _ _ 19816 _ hq16, hupd _ _ 14111 _ hq11]
      have hp12 : (ECDSAAdd.run q m s).basis 14112 = s.basis 14112 := ECDSAAdd.run_preserves_outside q m s 14112 hq12
      have hp15 : (ECDSAAdd.run q m s).basis 19815 = s.basis 19815 := ECDSAAdd.run_preserves_outside q m s 19815 hq15
      have hp14 : (ECDSAAdd.run q m s).basis 19814 = s.basis 19814 := ECDSAAdd.run_preserves_outside q m s 19814 hq14
      rw [inner] at hp12 hp15 hp14 ⊢
      rw [hp12, hp15, hp14]
    have hf' : FlagInv7 (ECDSAAdd.run p m s).basis := by
      have p11 : (ECDSAAdd.run p m s).basis 14111 = s.basis 14111 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 14111 hq11
      have p16 : (ECDSAAdd.run p m s).basis 19816 = s.basis 19816 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 19816 hq16
      have p838 : (ECDSAAdd.run p m s).basis 838 = s.basis 838 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 838 hq838
      have p12 : (ECDSAAdd.run p m s).basis 14112 = s.basis 14112 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 14112 hq12
      have p15 : (ECDSAAdd.run p m s).basis 19815 = s.basis 19815 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 19815 hq15
      have p14 : (ECDSAAdd.run p m s).basis 19814 = s.basis 19814 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 19814 hq14
      rw [FlagInv7, p11, p16, p838, p12, p15, p14, hG]
      exact hf
    rw [hqrun, pullS_perm4_encBasis (ECDSAAdd.run p m s).phase (ECDSAAdd.run p m s).basis hc1]
    exact dec4_run (ECDSAAdd.run p m s) hf' _
  · exact inner

theorem hostBlock7_wires (p : ECDSAAdd.Program) (S : List Wire)
    (hroot : windowRoot ∈ S) (hctl : hostCtl ∈ S) (hctl3 : hostCtl3 ∈ S)
    (hc11 : (14111 : Wire) ∈ S) (hc16 : (19816 : Wire) ∈ S) (hc838 : (838 : Wire) ∈ S)
    (hc12 : (14112 : Wire) ∈ S) (hc15 : (19815 : Wire) ∈ S) (hc14 : (19814 : Wire) ∈ S)
    (hc13 : (14113 : Wire) ∈ S)
    (hR : windowRoot ∉ ECDSAAdd.wires p)
    (h : ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = hostWire4 ∨ w = hostWire5 ∨ w = hostWire6 ∨ w = hostWire7 ∨ w ∈ S)
    (hc : hostWire2 ∈ ECDSAAdd.wires p → hostCtl ∉ ECDSAAdd.wires p)
    (hc3 : hostWire3 ∈ ECDSAAdd.wires p → hostCtl3 ∉ ECDSAAdd.wires p)
    (hc4 : (14877 ∈ ECDSAAdd.wires p ∨ 14876 ∈ ECDSAAdd.wires p ∨
        14875 ∈ ECDSAAdd.wires p ∨ 14874 ∈ ECDSAAdd.wires p) →
      14111 ∉ ECDSAAdd.wires p ∧ 19816 ∉ ECDSAAdd.wires p ∧
      838 ∉ ECDSAAdd.wires p ∧ 14112 ∉ ECDSAAdd.wires p ∧
      19815 ∉ ECDSAAdd.wires p ∧ 19814 ∉ ECDSAAdd.wires p) :
    ECDSAAdd.wires (hostBlock7 p) ⊆ S.toFinset := by
  unfold hostBlock7
  split_ifs with hcond
  · have henc_sub : ECDSAAdd.wires enc4 ⊆ ({14111, 19816, 838, 14112, 19815, 19814, 14113} : Finset Wire) := by
      decide
    have hdec_sub : ECDSAAdd.wires dec4 ⊆ ({14111, 19816, 838, 14112, 19815, 19814, 14113} : Finset Wire) := by
      decide
    have h7S : ({14111, 19816, 838, 14112, 19815, 19814, 14113} : Finset Wire) ⊆ S.toFinset := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      apply List.mem_toFinset.mpr
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    have henc : ECDSAAdd.wires enc4 ⊆ S.toFinset := henc_sub.trans h7S
    have hdec : ECDSAAdd.wires dec4 ⊆ S.toFinset := hdec_sub.trans h7S
    have hin : ECDSAAdd.wires (hostBlock3 p) ⊆ (14877 :: 14876 :: 14875 :: 14874 :: S).toFinset := by
      apply hostBlock3_wires p (14877 :: 14876 :: 14875 :: 14874 :: S)
        (by simp [hroot]) (by simp [hctl]) (by simp [hctl3]) hR _ hc hc3
      intro w hw
      rcases h w hw with e | e | e | e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (by simp [e, hostWire4])))
      · exact Or.inr (Or.inr (Or.inr (by simp [e, hostWire5])))
      · exact Or.inr (Or.inr (Or.inr (by simp [e, hostWire6])))
      · exact Or.inr (Or.inr (Or.inr (by simp [e, hostWire7])))
      · exact Or.inr (Or.inr (Or.inr (by simp [e])))
    have hq11 : (14111 : Wire) ∉ ECDSAAdd.wires (hostBlock3 p) :=
      hostBlock3_avoid_extra p 14111 hcond.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq16 : (19816 : Wire) ∉ ECDSAAdd.wires (hostBlock3 p) :=
      hostBlock3_avoid_extra p 19816 hcond.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq838 : (838 : Wire) ∉ ECDSAAdd.wires (hostBlock3 p) :=
      hostBlock3_avoid_extra p 838 hcond.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq12 : (14112 : Wire) ∉ ECDSAAdd.wires (hostBlock3 p) :=
      hostBlock3_avoid_extra p 14112 hcond.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hmid : ECDSAAdd.wires (progRelabel perm4 (hostBlock3 p)) ⊆ S.toFinset := by
      rw [relabel_wires]
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      have hvs := List.mem_toFinset.mp (hin hv)
      apply List.mem_toFinset.mpr
      simp only [List.mem_cons] at hvs
      rcases hvs with rfl | rfl | rfl | rfl | hvs
      · simpa [perm4] using hc11
      · simpa [perm4] using hc16
      · simpa [perm4] using hc838
      · simpa [perm4] using hc12
      · unfold perm4
        split_ifs with e1 e2 e3 e4 e5 e6 e7 e8
        · exact hc11
        · exact absurd (e2 ▸ hv) hq11
        · exact hc16
        · exact absurd (e4 ▸ hv) hq16
        · exact hc838
        · exact absurd (e6 ▸ hv) hq838
        · exact hc12
        · exact absurd (e8 ▸ hv) hq12
        · exact hvs
    simp only [ECDSAAdd.wires_append, Finset.union_subset_iff]
    exact ⟨⟨henc, hmid⟩, hdec⟩
  · have hno : ¬(14877 ∈ ECDSAAdd.wires p ∨ 14876 ∈ ECDSAAdd.wires p ∨
        14875 ∈ ECDSAAdd.wires p ∨ 14874 ∈ ECDSAAdd.wires p) :=
      fun h0 => hcond ⟨h0, hc4 h0⟩
    apply hostBlock3_wires p S hroot hctl hctl3 hR _ hc hc3
    intro w hw
    rcases h w hw with e | e | e | e | e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · rw [hostWire4] at e; subst e; exact absurd (Or.inl hw) hno
    · rw [hostWire5] at e; subst e; exact absurd (Or.inr (Or.inl hw)) hno
    · rw [hostWire6] at e; subst e; exact absurd (Or.inr (Or.inr (Or.inl hw))) hno
    · rw [hostWire7] at e; subst e; exact absurd (Or.inr (Or.inr (Or.inr hw))) hno
    · exact Or.inr (Or.inr (Or.inr e))

/-! ### `hostCode7`, `HostOK7`, `CodeHost7`, and `rowC_host7` -/

def hostCode7 {n} (code : WCode n) : WCode n :=
  if code.all isLit then
    [.literal (hostBlock7 (ECDSAAdd.Baselines.normalizeProgram (litProg code)))]
  else normalizeW code

def hostCodeExtra {n} (code : WCode n) : Nat :=
  if code.all isLit then
    hostExtra (ECDSAAdd.Baselines.normalizeProgram (litProg code))
  else 0

theorem hostCode7_eq_host {n} {code : WCode n} (h : code.all isLit = true) :
    hostCode7 code = [.literal (hostBlock7 (ECDSAAdd.Baselines.normalizeProgram (litProg code)))] := by
  simp [hostCode7, h]

theorem hostCode7_eq_norm {n} {code : WCode n} (h : ¬ code.all isLit = true) :
    hostCode7 code = normalizeW code := by
  simp [hostCode7, h]

theorem hostCode7_layouts {n} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : LookupLayouts bits paths root (normalizeW code)) : LookupLayouts bits paths root (hostCode7 code) := by
  by_cases h : code.all isLit = true
  · rw [hostCode7_eq_host h]
    exact ⟨hl.1, fun c ps hm => by simp at hm⟩
  · rw [hostCode7_eq_norm h]
    exact hl

theorem hostCode7_counts {n} (bits paths : List Wire) (root : Wire) (code : WCode n) :
    codeRecords bits paths root (hostCode7 code) = codeRecords bits paths root (normalizeW code) ∧
    literalToffolis (hostCode7 code) = literalToffolis (normalizeW code) + hostCodeExtra code ∧
    traversals (hostCode7 code) = traversals code := by
  by_cases h : code.all isLit = true
  · rw [hostCode7_eq_host h]
    obtain ⟨h1, h2, -, h4⟩ := litProg_counts bits paths root code ((allLit_iff code).mp h)
    refine ⟨?_, ?_, ?_⟩
    · simp only [codeRecords, h1, hostBlock7_meas, ECDSAAdd.Baselines.normalize_measurements, Nat.add_zero]
    · simp only [literalToffolis, hostCodeExtra, h, ↓reduceIte, h2, hostBlock7_toffoli, Nat.add_zero]
    · simp only [traversals, h4]
  · rw [hostCode7_eq_norm h]
    refine ⟨rfl, ?_, traversals_normalize code⟩
    simp [hostCodeExtra, h]

theorem hostCode7_slots {n} (bits : List Wire) (code : WCode n) :
    codeSlots bits (hostCode7 code) ≤ codeSlots bits (normalizeW code) + 26 := by
  by_cases h : code.all isLit = true
  · rw [hostCode7_eq_host h]
    obtain ⟨-, -, h3, -⟩ := litProg_counts bits ([] : List Wire) 0 code ((allLit_iff code).mp h)
    rw [h3]
    have hs := hostBlock7_slots (n := n) (ECDSAAdd.Baselines.normalizeProgram (litProg code))
    simp only [codeSlots]
    omega
  · rw [hostCode7_eq_norm h]
    omega

theorem hostCodeExtra_zero_of_avoidsB (code : WCode 32768) (hav : AvoidsB code) :
    hostCodeExtra code = 0 := by
  unfold hostCodeExtra
  split_ifs
  · apply hostExtra_zero_of
    intro w hw hm
    rw [ECDSAAdd.Baselines.normalize_wires] at hm
    obtain ⟨p, hp, hwp⟩ := litProg_wires code w hm
    exact hav.1 w hw p hp hwp
  · rfl

theorem hostCodeExtra_le {n} (code : WCode n) : hostCodeExtra code ≤ 2 := by
  unfold hostCodeExtra
  split_ifs
  · exact hostExtra_le _
  · omega

def HostOK4 {n} : Block2 n → ECDSAAdd.State → Prop
  | .plain code, st =>
      host4Set (litProg code) →
        FlagInv7 st.basis ∧ Clean4 st.basis ∧
        ∀ m, Clean4 (ECDSAAdd.run (litProg code) m st).basis ∧
          (ECDSAAdd.run (litProg code) m st).basis 14113 = st.basis 14113
  | .unit _, _ => True

def HostOK7 {n} (b : Block2 n) (st : ECDSAAdd.State) : Prop :=
  HostOK b st ∧ HostOK4 b st

def CodeHost4 {n} (read : ConstantBit n → Bool) (address : Nat) : Code n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => HostOK4 (toBlock2 b) st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference read address b) →
        CodeHost4 read address code (ECDSAAdd.run (blockReference read address b) m st)

def CodeHost4_2 {n} (read : ConstantBit n → Bool) (address : Nat) : Code2 n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => HostOK4 b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference2 read address b) →
        CodeHost4_2 read address code (ECDSAAdd.run (blockReference2 read address b) m st)

def CodeHost7 {n} (read : ConstantBit n → Bool) (address : Nat) : Code2 n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => HostOK7 b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference2 read address b) →
        CodeHost7 read address code (ECDSAAdd.run (blockReference2 read address b) m st)

theorem codeHost7_of_pair {n} (read : ConstantBit n → Bool) (address : Nat) (code : Code2 n)
    (st : ECDSAAdd.State) (h1 : CodeHost2 read address code st) (h2 : CodeHost4_2 read address code st) :
    CodeHost7 read address code st := by
  induction code generalizing st with
  | nil => trivial
  | cons b code ih =>
    exact ⟨⟨h1.1, h2.1⟩, fun m hm => ih _ (h1.2 m hm) (h2.2 m hm)⟩

theorem host4_append {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code n)
    (st : ECDSAAdd.State) (ha : CodeHost4 read address a st)
    (hb : ∀ m, m.length = ECDSAAdd.measurementCount (reference read address a) →
      CodeHost4 read address b (ECDSAAdd.run (reference read address a) m st)) :
    CodeHost4 read address (a ++ b) st := by
  induction a generalizing st with
  | nil => simpa [CodeHost4, ECDSAAdd.run] using hb [] rfl
  | cons x xs ih =>
    refine ⟨ha.1, ?_⟩
    intro m hm
    apply ih _ (ha.2 m hm)
    intro tail ht
    have hc := hb (m ++ tail) (by simp [ECDSAAdd.measurementCount_append, hm, ht])
    rw [reference_cons, run_append_records _ _ m tail st hm] at hc
    exact hc

theorem host4_split {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code n)
    (st : ECDSAAdd.State) (h : CodeHost4 read address (a ++ b) st) :
    CodeHost4 read address a st ∧ ∀ m, m.length = ECDSAAdd.measurementCount (reference read address a) →
      CodeHost4 read address b (ECDSAAdd.run (reference read address a) m st) := by
  induction a generalizing st with
  | nil =>
    exact ⟨trivial, fun m _ => by
      simpa [reference, erase, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run] using h⟩
  | cons x xs ih =>
    rw [List.cons_append] at h
    refine ⟨⟨h.1, fun m hm => (ih _ (h.2 m hm)).1⟩, fun m hm => ?_⟩
    rw [reference_cons, ECDSAAdd.measurementCount_append] at hm
    rw [reference_cons, ECDSAAdd.run_append]
    exact (ih _ (h.2 _ (by rw [List.length_take]; omega))).2 _ (by rw [List.length_drop]; omega)

theorem host4_2_append {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code2 n)
    (st : ECDSAAdd.State) (ha : CodeHost4_2 read address a st)
    (hb : ∀ m, m.length = ECDSAAdd.measurementCount (reference2 read address a) →
      CodeHost4_2 read address b (ECDSAAdd.run (reference2 read address a) m st)) :
    CodeHost4_2 read address (a ++ b) st := by
  induction a generalizing st with
  | nil => simpa [CodeHost4_2, ECDSAAdd.run] using hb [] rfl
  | cons x xs ih =>
    refine ⟨ha.1, ?_⟩
    intro m hm
    apply ih _ (ha.2 m hm)
    intro tail ht
    have hc := hb (m ++ tail) (by simp [ECDSAAdd.measurementCount_append, hm, ht])
    rw [reference2_cons, run_append_records _ _ m tail st hm] at hc
    exact hc

theorem host4_map {n} (read : ConstantBit n → Bool) (address : Nat) (code : Code n)
    (st : ECDSAAdd.State) (h : CodeHost4 read address code st) :
    CodeHost4_2 read address (code.map toBlock2) st := by
  induction code generalizing st with
  | nil => trivial
  | cons b code ih =>
    rw [List.map_cons]
    refine ⟨h.1, fun m hm => ?_⟩
    rw [blockReference2_map] at hm ⊢
    exact ih _ (h.2 m hm)

theorem streamLayout_infSel : streamLayout.infinitySelect = 19816 := by decide +kernel
theorem streamLayout_dblSel : streamLayout.doubleSelect = 19815 := by decide +kernel
theorem streamLayout_genSel : streamLayout.genericSelect = 19814 := by decide +kernel
theorem streamLayout_eqX : streamLayout.core.equalX = 14111 := by decide +kernel
theorem streamLayout_eqNegY : streamLayout.core.equalNegY = 14112 := by decide +kernel
theorem streamLayout_gen : streamLayout.core.generic = 14113 := by decide +kernel
theorem streamLayout_fin : streamLayout.point.finite = 838 := by decide +kernel

theorem head_avoidsB : AvoidsB scrHead := by
  simp only [scrHead]
  repeat' (with_reducible apply avoidsB_append)
  all_goals exact avoidsB_of_all _ (by unfold poolBand; decide +kernel)

theorem guard5_avoidsB : AvoidsB (wLiteral (n := 32768) guard5) :=
  avoidsB_lit _ (wires_avoid_of guard5_subset (fun w hw h => band_not_poolBand w (lists_band.2.2.1 w h) hw))

theorem negXReg_avoidsB : AvoidsB (wLiteral (n := 32768) negXReg) :=
  avoidsB_lit _ (wires_avoid_of negXReg_subset (fun w hw h => band_not_poolBand w (lists_band.2.2.2 w h) hw))

theorem zrep_avoidsB : AvoidsB (wLiteral (n := 32768) (ECDSAAdd.Frontier.zrep streamLayout)) :=
  avoidsB_lit _ zrep_avoidB

theorem hostOK4_avoid (code : WCode 32768) (hav : AvoidsB code) (st : ECDSAAdd.State) :
    HostOK4 (.plain code) st := by
  rintro ⟨h1 | h2 | h3 | h4, -⟩
  · obtain ⟨p, hp, hw⟩ := litProg_wires code 14877 h1
    exact absurd hw (hav.1 14877 (by decide) p hp)
  · obtain ⟨p, hp, hw⟩ := litProg_wires code 14876 h2
    exact absurd hw (hav.1 14876 (by decide) p hp)
  · obtain ⟨p, hp, hw⟩ := litProg_wires code 14875 h3
    exact absurd hw (hav.1 14875 (by decide) p hp)
  · obtain ⟨p, hp, hw⟩ := litProg_wires code 14874 h4
    exact absurd hw (hav.1 14874 (by decide) p hp)

theorem values_clean4 {X Y : ECDSAAdd.Fp} {G : Bool} {base s : BasisState}
    (h : PointDialogValues streamLayout X Y G base s) : Clean4 s := by
  have hc : ∀ q ∈ poolBand, s q = false := fun q hq =>
    (regValue_zero _ _).mp h.clean q (poolBand_pool q hq)
  exact ⟨hc 14877 (by decide), hc 14876 (by decide), hc 14875 (by decide), hc 14874 (by decide)⟩

theorem values_flagInv7 {X Y : ECDSAAdd.Fp} {G : Bool} {base s : BasisState}
    (h : PointDialogValues streamLayout X Y G base s) (_hG : base 14113 = G)
    (hf : FlagInv7 base) : FlagInv7 s := by
  have hout : ∀ q, q ∈ ([14111, 19816, 838, 14112, 19815, 19814, 14113] : List Wire) → s q = base q := by
    intro q hq
    apply h.rest q
    intro hm
    simp only [streamLayout_point, List.mem_append, List.mem_range'_1] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hm with hm | hm
    · rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [FlagInv7, hout 14111 (by simp), hout 19816 (by simp), hout 838 (by simp),
    hout 14112 (by simp), hout 19815 (by simp), hout 19814 (by simp), hout 14113 (by simp)]
  exact hf

structure CheckedH4 {n} (read : ConstantBit n → Bool) (address : Nat)
    (Pre : BasisState → Prop) (code : Code n) (Post : BasisState → Prop) : Prop where
  checked : Checked read address Pre code Post
  host4 : ∀ st, Pre st.basis → CodeHost4 read address code st

namespace CheckedH4
variable {n : Nat} {read : ConstantBit n → Bool} {address : Nat}
variable {A B C : BasisState → Prop} {a b : Code n}

theorem seq (ha : CheckedH4 read address A a B) (hb : CheckedH4 read address B b C) :
    CheckedH4 read address A (a ++ b) C :=
  ⟨ha.checked.seq hb.checked, fun st hs => host4_append read address a b st (ha.host4 st hs)
    (fun m _ => hb.host4 _ (ha.checked.correct st m hs).2)⟩

theorem masked {site : MaskedSite n} (h : Checked read address A ([.masked site] : Code n) B) :
    CheckedH4 read address A ([.masked site] : Code n) B :=
  ⟨h, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩

theorem plainV {p : ECDSAAdd.Program} {X Y X' Y' : ECDSAAdd.Fp} {G : Bool} {base : BasisState}
    (hG : base 14113 = G) (hf : FlagInv7 base)
    (h : Checked read address (PointDialogValues streamLayout X Y G base) ([.plain (wLiteral p)] : Code n)
      (PointDialogValues streamLayout X' Y' G base)) :
    CheckedH4 read address (PointDialogValues streamLayout X Y G base) ([.plain (wLiteral p)] : Code n)
      (PointDialogValues streamLayout X' Y' G base) := by
  refine ⟨h, fun st hs => ⟨fun _ => ?_, fun _ _ => trivial⟩⟩
  refine ⟨values_flagInv7 hs hG hf, values_clean4 hs, fun m => ?_⟩
  have post : PointDialogValues streamLayout X' Y' G base (ECDSAAdd.run (litProg (wLiteral (n := n) p)) m st).basis := by
    have e := (h.correct st m hs).2
    simp only [reference, erase_plain] at e
    rw [litProg_inst read (wLiteral (n := n) p) address (by simp [wLiteral])] at e
    exact e
  refine ⟨values_clean4 post, ?_⟩
  have g1 := hs.generic
  have g2 := post.generic
  rw [streamLayout_gen] at g1 g2
  exact g2.trans g1.symm

end CheckedH4

theorem literal_checkedV4 {n} (read : ConstantBit n → Bool) (address : Nat) (p : ECDSAAdd.Program)
    {X Y X' Y' : ECDSAAdd.Fp} {G : Bool} {base : BasisState}
    (hG : base 14113 = G) (hf : FlagInv7 base)
    (h : ECDSAAdd.Triple (PointDialogValues streamLayout X Y G base) p
      (PointDialogValues streamLayout X' Y' G base)) :
    CheckedH4 read address (PointDialogValues streamLayout X Y G base) ([.plain (wLiteral p)] : Code n)
      (PointDialogValues streamLayout X' Y' G base) :=
  CheckedH4.plainV hG hf (literal_checked read address p _ _ h)

attribute [local irreducible] ECDSAAdd.run

theorem chainH4_plain (read : ConstantBit 32768 → Bool) (address : Nat)
    (rows : Nat → Fin 32768)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState)
    (hroot : base windowRoot = true) (hctl : base streamLayout.control = true)
    (hG : base 14113 = G) (hf : FlagInv7 base)
    (hD : base streamLayout.doubleSelect = false) (hI : base streamLayout.genericSelect = false)
    (X0 X1 a X3 X5 X6 Y6 : ECDSAAdd.Fp)
    (hX0 : X0.val = X.val ^^^ (if base streamLayout.point.finite then 0 else 5))
    (hX1d : X1 = X0 - cx) (hX1 : X1 ≠ 0) (ha : a = (Y - cy)/X1)
    (hX3d : X3 = X1 - (if G then a*a else 0) + (if G then 3*cx else 0)) (hX3 : X3 ≠ 0)
    (hX5 : X5 = (if G then -X3 else X3) + cx)
    (hX6 : X6.val = X5.val ^^^ (if base streamLayout.point.finite then 0 else 5))
    (hY6 : Y6 = a * X3 + (if G then -cy else cy)) :
    CheckedH4 read address (PointDialogValues streamLayout X Y G base) (generic3' rows)
      (PointDialogValues streamLayout X6 Y6 G base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hex : ¬ (base streamLayout.doubleSelect = true ∧ base streamLayout.genericSelect = true) := by
    rw [hD]; simp
  have gid : ∀ (Z : ECDSAAdd.Fp), Z.val = (Z.val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := by
    intro Z; rw [hD, hI]; simp
  have z1 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X X0 Y G base hX0)
  have p1 := CheckedH4.masked (pair1_checked read address rows hc hr X0 Y G base hroot hctl)
  rw [← hX1d] at p1
  have g1 := CheckedH4.plainV hG hf (guard5_checked read address X1 X1 (Y - cy) G base hex (gid X1))
  have d1 := literal_checkedV4 read address _ hG hf
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X1 (Y - cy) G base false hX1)
  simp only [Bool.false_eq_true, if_false] at d1
  rw [← ha] at d1
  have g2 := CheckedH4.plainV hG hf (guard5_checked read address X1 X1 a G base hex (gid X1))
  have sq := literal_checkedV4 read address _ hG hf
    (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn X1 a G base)
  have t3 := CheckedH4.masked (addX_checked read address streamLayout hw hn (X1 - (if G then a * a else 0)) a G base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc)))
  rw [← hX3d] at t3
  have g3 := CheckedH4.plainV hG hf (guard5_checked read address X3 X3 a G base hex (gid X3))
  have m1 := literal_checkedV4 read address _ hG hf
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X3 a G base true hX3)
  simp only [if_true] at m1
  have g4 := CheckedH4.plainV hG hf (guard5_checked read address X3 X3 (a * X3) G base hex (gid X3))
  have ng := literal_checkedV4 read address _ hG hf (negXReg_step X3 (a * X3) G base (fun _ => hX3))
  have p2 := CheckedH4.masked (pair2_checked read address rows hc hr (if G then -X3 else X3) (a * X3) G base hroot hctl)
  rw [← hX5, ← hY6] at p2
  have z2 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X5 X6 Y6 G base hX6)
  have h := (((((((((((z1.seq p1).seq g1).seq d1).seq g2).seq sq).seq t3).seq g3).seq m1).seq g4).seq ng).seq p2).seq z2
  simpa only [generic3', preBlock, generic3, constAdd, List.append_assoc, List.cons_append, List.nil_append] using h

theorem chainH4_toggle (read : ConstantBit 32768 → Bool) (address : Nat)
    (rows : Nat → Fin 32768)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState)
    (hroot : base windowRoot = true) (hctl : base streamLayout.control = true)
    (hG : base 14113 = false) (hf : FlagInv7 base)
    (hfin : base streamLayout.point.finite = true)
    (hex : ¬ (base streamLayout.doubleSelect = true ∧ base streamLayout.genericSelect = true))
    (hD : base streamLayout.doubleSelect = true → X = cx) (hI : base streamLayout.genericSelect = true → X = cx)
    (hX1 : base streamLayout.doubleSelect = false → base streamLayout.genericSelect = false → X - cx ≠ 0) :
    CheckedH4 read address (PointDialogValues streamLayout X Y false base) (generic3' rows)
      (PointDialogValues streamLayout X Y false base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  set E := (base streamLayout.doubleSelect || base streamLayout.genericSelect) with hE
  let xg : ECDSAAdd.Fp := if E then 5 else X - cx
  have hxg0 : xg ≠ 0 := by
    simp only [xg]
    split
    · exact ECDSAAdd.Frontier.finFive_ne_zero
    · rename_i hne
      simp only [hE, Bool.or_eq_true, not_or, Bool.not_eq_true] at hne
      exact hX1 hne.1 hne.2
  have hzero : E = true → X - cx = 0 := by
    intro h
    simp only [hE, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [hD h, sub_self]
    · rw [hI h, sub_self]
  have fwd : xg.val = ((X - cx).val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := by
    simp only [xg]
    cases hd : base streamLayout.doubleSelect <;> cases hi : base streamLayout.genericSelect
    · simp [hE, hd, hi]
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]
      rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]
      rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · exact absurd ⟨hd, hi⟩ hex
  have back : (X - cx).val = (xg.val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := by
    simp only [xg]
    cases hd : base streamLayout.doubleSelect <;> cases hi : base streamLayout.genericSelect
    · simp [hE, hd, hi]
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]
      rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]
      rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · exact absurd ⟨hd, hi⟩ hex
  have zid : X.val = X.val ^^^ (if base streamLayout.point.finite then 0 else 5) := by rw [hfin]; simp
  have z1 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X X Y false base zid)
  have p1 := CheckedH4.masked (pair1_checked read address rows hc hr X Y false base hroot hctl)
  have g1 := CheckedH4.plainV hG hf (guard5_checked read address (X - cx) xg (Y - cy) false base hex fwd)
  have d1 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn xg (Y - cy) false base false hxg0)
  simp only [Bool.false_eq_true, if_false] at d1
  have g2 := CheckedH4.plainV hG hf (guard5_checked read address xg (X - cx) ((Y - cy)/xg) false base hex back)
  have sq := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn (X - cx) ((Y - cy)/xg) false base)
  simp only [Bool.false_eq_true, if_false, sub_zero] at sq
  have t3 := CheckedH4.masked (addX_checked read address streamLayout hw hn (X - cx) ((Y - cy)/xg) false base (3*cx) (wFields rows .tripleX)
    (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc)))
  simp only [Bool.false_eq_true, if_false, add_zero] at t3
  have g3 := CheckedH4.plainV hG hf (guard5_checked read address (X - cx) xg ((Y - cy)/xg) false base hex fwd)
  have m1 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn xg ((Y - cy)/xg) false base true hxg0)
  simp only [if_true, div_mul_cancel₀ _ hxg0] at m1
  have g4 := CheckedH4.plainV hG hf (guard5_checked read address xg (X - cx) (Y - cy) false base hex back)
  have ng := literal_checkedV4 read address _ hG hf (negXReg_step (X - cx) (Y - cy) false base (fun h => by cases h))
  simp only [Bool.false_eq_true, if_false] at ng
  have p2 := CheckedH4.masked (pair2_checked read address rows hc hr (X - cx) (Y - cy) false base hroot hctl)
  simp only [Bool.false_eq_true, if_false, sub_add_cancel] at p2
  have z2 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X X Y false base zid)
  have h := (((((((((((z1.seq p1).seq g1).seq d1).seq g2).seq sq).seq t3).seq g3).seq m1).seq g4).seq ng).seq p2).seq z2
  simpa only [generic3', preBlock, generic3, constAdd, List.append_assoc, List.cons_append, List.nil_append] using h

theorem generic3_host4 (read : ConstantBit 32768 → Bool) (address : Nat)
    (rows : Nat → Fin 32768)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc)) (h₁ : cy ≠ -cy)
    (h₂ : dialogExceptionEnabled (.some hc))
    (st : ECDSAAdd.State)
    (hs : PointDialogBoundary streamLayout R true (flags streamLayout R (.some hc) true cy) st.basis)
    (hroot : st.basis windowRoot = true) :
    CodeHost4 read address (generic3' rows) st := by
  classical
  have hp := (point_holds _ _ _).mp hs.point
  have hctl : st.basis streamLayout.control = true := hs.control
  have hCneg := some_ne_neg hc h₁
  have hC0 : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have rd := dialogFlagState_read streamLayout streamLayout_nodup (dialogInfinity true R)
    (dialogDouble true R (.some hc)) (dialogInversePoint true R (.some hc)) (dialogOrdinary true R (.some hc))
    (true && decide (dialogExceptionEnabled (.some hc))) (dialogException true R (.some hc))
    (true && decide (cy ≠ -cy))
  have sO : st.basis 19816 = dialogInfinity true R := by
    rw [← streamLayout_infSel]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.1
  have sD : st.basis 19815 = dialogDouble true R (.some hc) := by
    rw [← streamLayout_dblSel]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.1
  have sI : st.basis 19814 = dialogInversePoint true R (.some hc) := by
    rw [← streamLayout_genSel]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.2.1
  have sG : st.basis 14113 = dialogOrdinary true R (.some hc) := by
    rw [← streamLayout_gen]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.2.2.1
  have sE : st.basis 14111 = (true && decide (dialogExceptionEnabled (.some hc))) := by
    rw [← streamLayout_eqX]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.2.2.2.1
  have sH : st.basis 14112 = dialogException true R (.some hc) := by
    rw [← streamLayout_eqNegY]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.2.2.2.2.1
  have sD' : st.basis 19815 = decide (R = (.some hc : Point)) := by
    rw [sD, dialogDouble, decide_eq_true hCneg]; simp
  have sI' : st.basis 19814 = decide (R = -(.some hc : Point)) := by
    rw [sI]; simp [dialogInversePoint]
  have h11 : st.basis 14111 = true := by
    rw [sE, decide_eq_true h₂]; rfl
  have hfin_eq : st.basis 838 = !dialogInfinity true R := by
    rw [← streamLayout_fin]
    cases R with
    | zero =>
      have hp0 : st.basis streamLayout.point.finite = false := ((point_holds _ _ _).mp hs.point).1
      rw [hp0, dialogInfinity, show (WeierstrassCurve.Affine.Point.zero : Point) = 0 from rfl]
      simp
    | some hrp =>
      have hp1 := (point_holds _ _ _).mp hs.point
      rw [hp1.1, dialogInfinity, decide_eq_false (WeierstrassCurve.Affine.Point.some_ne_zero hrp)]
      rfl
  have h16 : st.basis 19816 = !st.basis 838 := by
    rw [sO, hfin_eq, Bool.not_not]
  have h838 : st.basis 838 = (st.basis 14113 ^^ st.basis 19815 ^^ st.basis 19814 ^^ st.basis 14112) := by
    rw [hfin_eq, sG, sD, sI, sH, dialogOrdinary]
    cases dialogInfinity true R <;> cases dialogDouble true R (.some hc) <;>
      cases dialogInversePoint true R (.some hc) <;> cases dialogException true R (.some hc) <;> rfl
  have hex : ¬ (st.basis 19815 = true ∧ st.basis 19814 = true) := by
    rw [sD', sI']
    simp only [decide_eq_true_eq, not_and]
    intro h1 h2
    exact hCneg (h1.symm.trans h2)
  have hDI : st.basis 19815 = true → st.basis 19814 = false := by
    intro hD1
    cases hI1 : st.basis 19814
    · rfl
    · exact absurd ⟨hD1, hI1⟩ hex
  have hH_ex : st.basis 14112 = true → st.basis 19815 = false ∧ st.basis 19814 = false := by
    intro hh
    rw [sH] at hh
    constructor
    · cases hD1 : st.basis 19815
      · rfl
      · rw [sD', decide_eq_true_eq] at hD1
        rw [hD1, dialogException_self] at hh; cases hh
    · cases hI1 : st.basis 19814
      · rfl
      · rw [sI', decide_eq_true_eq] at hI1
        rw [hI1, dialogException_neg] at hh; cases hh
  have hf : FlagInv7 st.basis := ⟨h11, h16, h838, hDI, hH_ex⟩
  cases R with
  | zero =>
    have hG : st.basis 14113 = false := by
      rw [sG]
      cases h : dialogOrdinary true 0 (.some hc)
      · rfl
      · exact absurd rfl ((dialogOrdinary_true true 0 _ hC0).mp h).2.1
    have hD0 : st.basis streamLayout.doubleSelect = false := by
      rw [streamLayout_dblSel, sD']; simp [hC0.symm]
    have hI0 : st.basis streamLayout.genericSelect = false := by
      rw [streamLayout_genSel, sI']; simp [(neg_ne_zero.mpr hC0).symm]
    have values : PointDialogValues streamLayout 0 0 false st.basis st.basis :=
      ⟨hp.2.1, hp.2.2, by rw [streamLayout_gen]; exact hG, hs.clean, fun _ _ => rfl⟩
    have hfin : st.basis streamLayout.point.finite = false := hp.1
    have hX1 : (5 : ECDSAAdd.Fp) - cx ≠ 0 := sub_ne_zero.mpr (ECDSAAdd.Frontier.x_ne_five hc).symm
    have new := chainH4_plain read address rows hc hr 0 0 false st.basis hroot hctl hG hf hD0 hI0
      5 (5 - cx) ((0 - cy)/(5 - cx)) (5 - cx) 5 0 0
      (by rw [hfin, ECDSAAdd.Frontier.finFive_val, ZMod.val_zero]; decide) rfl hX1 rfl (by simp) hX1 (by simp)
      (by rw [hfin, ECDSAAdd.Frontier.finFive_val, ZMod.val_zero]; decide)
      (by simp [div_mul_cancel₀ _ hX1])
    exact new.host4 st values
  | @some x y hrp =>
    have hfin : st.basis streamLayout.point.finite = true := hp.1
    cases hG : dialogOrdinary true (.some hrp) (.some hc) with
    | false =>
      have sG' : st.basis 14113 = false := sG.trans hG
      have values : PointDialogValues streamLayout x y false st.basis st.basis :=
        ⟨hp.2.1, hp.2.2, by rw [streamLayout_gen]; exact sG', hs.clean, fun _ _ => rfl⟩
      have hD : st.basis streamLayout.doubleSelect = true → x = cx := by
        rw [streamLayout_dblSel, sD']; intro h
        have := of_decide_eq_true h
        exact (WeierstrassCurve.Affine.Point.some.inj this).1
      have hI : st.basis streamLayout.genericSelect = true → x = cx := by
        rw [streamLayout_genSel, sI']; intro h
        have := of_decide_eq_true h
        rw [WeierstrassCurve.Affine.Point.neg_some] at this
        exact (WeierstrassCurve.Affine.Point.some.inj this).1
      have hX1 : st.basis streamLayout.doubleSelect = false → st.basis streamLayout.genericSelect = false →
          x - cx ≠ 0 := by
        rw [streamLayout_dblSel, streamLayout_genSel, sD', sI']
        intro h1 h2 hz
        rcases (sameX_iff_eq_or_neg hrp hc).mp (sub_eq_zero.mp hz) with h | h
        · exact absurd (decide_eq_true h) (by rw [h1]; decide)
        · exact absurd (decide_eq_true h) (by rw [h2]; decide)
      have new := chainH4_toggle read address rows hc hr x y st.basis hroot hctl sG' hf hfin
        (by rw [streamLayout_dblSel, streamLayout_genSel]; exact hex) hD hI hX1
      exact new.host4 st values
    | true =>
      have he := ((dialogOrdinary_true true _ _ hC0).mp hG).2
      have den := dialog_denominators_ne_zero hrp hc he.2.1 he.2.2.1 he.2.2.2
      have sG' : st.basis 14113 = true := sG.trans hG
      have values : PointDialogValues streamLayout x y true st.basis st.basis :=
        ⟨hp.2.1, hp.2.2, by rw [streamLayout_gen]; exact sG', hs.clean, fun _ _ => rfl⟩
      have hD0 : st.basis streamLayout.doubleSelect = false := by
        rw [streamLayout_dblSel, sD']; exact decide_eq_false he.2.1
      have hI0 : st.basis streamLayout.genericSelect = false := by
        rw [streamLayout_genSel, sI']; exact decide_eq_false he.2.2.1
      let a := genericSlope x y cx cy
      let d := cx - genericX x y cx cy
      have hv := generic_inplace_values x y cx cy den.1
      have ha : (y - cy)/(x - cx) = a := rfl
      have new := chainH4_plain read address rows hc hr x y true st.basis hroot hctl sG' hf hD0 hI0
        x (x - cx) a d (-d + cx) (genericX x y cx cy) (genericY x y cx cy)
        (by rw [hfin]; simp) rfl (sub_ne_zero.mpr den.1) ha
        (by simp only [if_true]; exact hv.2.1.symm) den.2 (by simp only [if_true])
        (by rw [hfin]; simp only [if_true, Nat.xor_zero]; congr 1; simp only [d]; ring)
        (by simp only [if_true]; rw [← sub_eq_add_neg]; exact hv.2.2.symm)
      exact new.host4 st values

theorem rowPost3_host4 (read : ConstantBit 32768 → Bool) (a : Nat) (t : ECDSAAdd.State) :
    CodeHost4_2 read a WEXUnlookup.rowPost3 t := by
  rw [WEXUnlookup.rowPost3]
  exact ⟨hostOK4_avoid _ cornerNeg_avoidsB t, fun _ _ =>
    ⟨trivial, fun _ _ => ⟨trivial, fun _ _ =>
      ⟨hostOK4_avoid _ sfxTailF_avoidsB _, fun _ _ =>
        ⟨hostOK4_avoid _ flip_avoidsB _, fun _ _ => trivial⟩⟩⟩⟩⟩

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

theorem rowC_host4 (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeHost4_2 (readConstant coeffs Q) a WEXUnlookup.rowC ⟨false, s⟩ := by
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P0, hP0⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P0) true (fun _ => false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P0) (StreamPoint.of_coordinates s P0 hs.1.1.1.1 hP0), ?_, ?_, ?_⟩
    · simpa [streamLayout_control, flipInfinity, ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  have pre : CodeHost4 (readConstant coeffs Q) a rowPre3 ⟨false, s⟩ :=
    ⟨hostOK4_avoid _ flip_avoidsB _, fun _ _ =>
      ⟨hostOK4_avoid _ head_avoidsB _, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩
  have hhead : CodeHost4 (readConstant coeffs Q) a WEXUnlookup.rowHead ⟨false, s⟩ := by
    cases he : Bridge.toB C with
    | zero => exact (hC (congrArg ECDSAAdd.ShorPort.toA he)).elim
    | @some cx cy hc =>
      have ce : C = toA (.some hc) := congrArg toA he
      have hr : RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
        readConstant_rowReads coeffs Q _ _ ce
      have ho : ShorECDLP.order • (.some hc : Point) = 0 := by rw [← he]; exact hord
      have hp2 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 2
        (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
      have hp3 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 3
        (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
      have hd : (.some hc : Point) + .some hc ≠ 0 := by simpa only [two_nsmul] using hp2
      have ht : (.some hc : Point) + .some hc + .some hc ≠ 0 := by
        simpa only [show (3 : Nat) = 2 + 1 from rfl, succ_nsmul, two_nsmul] using hp3
      have en := enables_true hc hd ht
      have hdo : ShorECDLP.order • ((.some hc : Point) + .some hc) = 0 := by rw [nsmul_add, ho, zero_add]
      have hen : dialogExceptionEnabled (.some hc) := by
        refine ⟨neg_ne_zero.mpr hd, ?_, ?_⟩
        · intro e
          unfold dialogExceptionPoint at e
          have h3 : ((.some hc : Point) + .some hc) + .some hc = 0 := by
            have h0 := add_neg_cancel ((.some hc : Point) + .some hc)
            rwa [e] at h0
          exact ht h3
        · intro e
          unfold dialogExceptionPoint at e
          have h2 : (.some hc : Point) + .some hc = .some hc := neg_inj.mp e
          have h1 : (.some hc : Point) = 0 := by
            have := congrArg (· - (.some hc : Point)) h2
            simpa using this
          exact WeierstrassCurve.Affine.Point.some_ne_zero hc h1
      have g := fun m => generic3_host4 (readConstant coeffs Q) a probeRows (Bridge.toB P0) hc hr en.1 hen _
        (rowPre_boundary (readConstant coeffs Q) a (Bridge.toB P0) hc hr en.1 en.2 hd hdo s initial hs.2.2 m)
        (WEX.root_preserves (readConstant coeffs Q) windowBits windowPaths windowRoot (erase rowPre) a rowPre_placed
          ⟨false, s⟩ hs.2.2 m)
      have hk : ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a rowPre3) =
          ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a rowPre) +
            ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a (preBlock probeRows)) := by
        rw [rowPre3_records, reference_append, ECDSAAdd.measurementCount_append]
      have e1 (m : List Bool) : ECDSAAdd.run (reference (readConstant coeffs Q) a rowPre3) m ⟨false, s⟩ =
          ECDSAAdd.run (reference (readConstant coeffs Q) a (preBlock probeRows))
            (m.drop (ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a rowPre)))
            (ECDSAAdd.run (reference (readConstant coeffs Q) a rowPre) m ⟨false, s⟩) := by
        rw [rowPre3_run, reference_append, run_meas_append]
      rw [WEXUnlookup.rowHead]
      apply host4_append _ _ rowPre3 _ _ pre
      intro m hm
      have gs := host4_split _ _ (preBlock probeRows) (generic3 probeRows) _ (g m)
      rw [e1]
      have hlen : (m.drop (ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a rowPre))).length =
          ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a (preBlock probeRows)) := by
        rw [List.length_drop, hm, hk]; omega
      exact gs.2 _ hlen
  rw [WEXUnlookup.rowC]
  exact host4_2_append _ _ _ _ _ (host4_map _ _ _ _ hhead) (fun _ _ => rowPost3_host4 _ _ _)

theorem rowC_host7 (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeHost7 (readConstant coeffs Q) a WEXUnlookup.rowC ⟨false, s⟩ :=
  codeHost7_of_pair _ _ _ _ (PathShare.rowC_host coeffs Q hQ hn a s hs) (rowC_host4 coeffs Q hQ hn a s hs)

/-! ### Support retirement and compaction for the 4 newly hosted wires (`1612` narrow, `1613` wide) -/

def retiredH7 (w : Nat) : Prop :=
  retiredH w ∨ w = 14877 ∨ w = 14876 ∨ w = 14875 ∨ w = 14874
instance : DecidablePred retiredH7 := fun w =>
  inferInstanceAs (Decidable (retiredH w ∨ w = 14877 ∨ w = 14876 ∨ w = 14875 ∨ w = 14874))

def newSourceH7 : List Wire := sourceSupport.filter (fun w => decide (¬retiredH7 w))

theorem newSourceH7_mem (w : Nat) : w ∈ newSourceH7 ↔ (fixedPort w ∨ oldWork w) ∧ ¬retiredH7 w := by
  rw [newSourceH7, List.mem_filter, sourceSupport_mem, decide_eq_true_eq]

theorem newSourceH7_of_bounds (xs : List Wire) (h : ∀ w ∈ xs, (fixedPort w ∨ oldWork w) ∧ ¬retiredH7 w) :
    xs ⊆ newSourceH7 :=
  fun w hw => (newSourceH7_mem w).mpr (h w hw)

theorem newSourceH7_of_newH (w : Nat) (h : w ∈ newSourceH)
    (h4 : w ≠ 14877) (h5 : w ≠ 14876) (h6 : w ≠ 14875) (h7 : w ≠ 14874) : w ∈ newSourceH7 := by
  obtain ⟨h1, h2⟩ := (newSourceH_mem w).mp h
  exact (newSourceH7_mem w).mpr ⟨h1, fun hr => hr.elim h2 (fun a => a.elim h4 (fun b => b.elim h5 (fun c => c.elim h6 h7)))⟩

theorem newSourceH7_sub_newSourceH : newSourceH7 ⊆ newSourceH := by
  intro w hw
  obtain ⟨h1, h2⟩ := (newSourceH7_mem w).mp hw
  exact (newSourceH_mem w).mpr ⟨h1, fun hr => h2 (Or.inl hr)⟩

theorem relaxed7_of_new (w : Nat) (h : w ∈ newSource) :
    w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
    w = hostWire4 ∨ w = hostWire5 ∨ w = hostWire6 ∨ w = hostWire7 ∨ w ∈ newSourceH7 := by
  rcases relaxed_of_new w h with e | e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl e))
  · by_cases h4 : w = 14877
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    by_cases h5 : w = 14876
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    by_cases h6 : w = 14875
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    by_cases h7 : w = 14874
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (newSourceH7_of_newH w e h4 h5 h6 h7)))))))

def tau4Wire (w : Nat) : Nat :=
  if w = 14877 then 15640
  else if w = 15640 then 14877
  else if w = 14876 then 15639
  else if w = 15639 then 14876
  else if w = 14875 then 15638
  else if w = 15638 then 14875
  else if w = 14874 then 15637
  else if w = 15637 then 14874
  else w

theorem tau4Wire_involutive : Function.Involutive tau4Wire := by
  intro w
  unfold tau4Wire
  by_cases h1 : w = 14877; · simp [h1]
  by_cases h2 : w = 15640; · simp [h2]
  by_cases h3 : w = 14876; · simp [h3]
  by_cases h4 : w = 15639; · simp [h4]
  by_cases h5 : w = 14875; · simp [h5]
  by_cases h6 : w = 15638; · simp [h6]
  by_cases h7 : w = 14874; · simp [h7]
  by_cases h8 : w = 15637; · simp [h8]
  simp [h1, h2, h3, h4, h5, h6, h7, h8]

def tau4 : Wire ≃ Wire := ⟨tau4Wire, tau4Wire, tau4Wire_involutive, tau4Wire_involutive⟩

def tauH7 : Wire ≃ Wire := tau4.trans tauH

def piH7 : Wire ≃ Wire := tauH7.trans compactPerm

theorem piH7_apply (w : Wire) : piH7 w = compactWire (tauWireH (tau4Wire w)) := rfl

theorem piH7_fixed (w : Wire) (h : fixedPort w) : piH7 w = w := by
  have h4 : tau4Wire w = w := by
    unfold tau4Wire fixedPort at *
    dsimp only [Wire] at w h ⊢
    have hne : w ≠ 14877 ∧ w ≠ 15640 ∧ w ≠ 14876 ∧ w ≠ 15639 ∧ w ≠ 14875 ∧ w ≠ 15638 ∧ w ≠ 14874 ∧ w ≠ 15637 := by omega
    simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2]
  rw [piH7_apply, h4]
  exact PathShare.piH_fixed w h

theorem piH7_hot (i : Fin 128) : piH7 (hot i) = hot i := by
  have h4 : ∀ j : Fin 128, tau4Wire (hot j) = hot j := by decide
  rw [piH7_apply, h4 i]
  exact PathShare.piH_hot i

theorem piH7_point (w : Wire) (hw : w ∈ pointLogicalWires) : piH7 w = w := by
  have h4 : tau4Wire w = w := by
    have hlt : (w : Nat) < 1000 := by
      simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
        List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hw
      dsimp only [Wire] at *; omega
    unfold tau4Wire
    dsimp only [Wire] at w hlt ⊢
    have hne : w ≠ 14877 ∧ w ≠ 15640 ∧ w ≠ 14876 ∧ w ≠ 15639 ∧ w ≠ 14875 ∧ w ≠ 15638 ∧ w ≠ 14874 ∧ w ≠ 15637 := by omega
    simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2]
  rw [piH7_apply, h4]
  exact PathShare.piH_point w hw

private theorem freeAt_lt_1612 (i : Nat) (hi : i < 1082) : freeAt i < 1612 := by
  unfold freeAt; split_ifs <;> omega

theorem piH7_bound (w : Nat) (hw : w ∈ newSourceH7) : (piH7 w : Nat) < 1612 := by
  obtain ⟨h1, h2⟩ := (newSourceH7_mem w).mp hw
  unfold retiredH7 retiredH retired at h2
  by_cases hD : w = 15640 ∨ w = 15639 ∨ w = 15638 ∨ w = 15637
  · rcases hD with rfl | rfl | rfl | rfl <;>
    · rw [piH7_apply]; unfold tau4Wire tauWireH compactWire oldWork freeAt oldRank; decide
  · have h4 : tau4Wire w = w := by
      unfold tau4Wire
      have hne : w ≠ 14877 ∧ w ≠ 15640 ∧ w ≠ 14876 ∧ w ≠ 15639 ∧ w ≠ 14875 ∧ w ≠ 15638 ∧ w ≠ 14874 ∧ w ≠ 15637 := by omega
      simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2]
    rw [piH7_apply, h4]
    by_cases hA : 15644 ≤ w ∧ w < 15655
    · have ht : tauWireH w = w - 5644 := by unfold tauWireH; split_ifs <;> omega
      have ho : oldWork (w - 5644) := by unfold oldWork; omega
      rw [ht, compactWire, if_pos ho]
      exact freeAt_lt_1612 _ (by unfold oldRank; split_ifs <;> omega)
    by_cases hC : w = 15643 ∨ w = 15642 ∨ w = 15641
    · rcases hC with rfl | rfl | rfl <;>
      · unfold tauWireH compactWire oldWork freeAt oldRank; decide
    by_cases hB : 19814 ≤ w ∧ w < 19817
    · have ht : tauWireH w = w - 9802 := by unfold tauWireH; split_ifs <;> omega
      have ho : oldWork (w - 9802) := by unfold oldWork; omega
      rw [ht, compactWire, if_pos ho]
      exact freeAt_lt_1612 _ (by unfold oldRank; split_ifs <;> omega)
    · have ht : tauWireH w = w := by unfold tauWireH; split_ifs <;> omega
      rw [ht]
      rcases h1 with hf | ho
      · have he : compactWire w = w := compactPerm_fixed w hf
        show compactWire w < 1612
        rw [he]; unfold fixedPort at hf; omega
      · rw [compactWire, if_pos ho]
        unfold oldWork at ho
        exact freeAt_lt_1612 _ (by unfold oldRank; split_ifs <;> omega)

theorem relabelH7_support {n s e} (p : Straight n s e) (hp : straightWires p ⊆ newSourceH7) :
    straightWires (relabelStraight piH7 p) ⊆ List.range 1612 := by
  rw [straightWires_relabel]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr (piH7_bound v (hp hv))

theorem ctl4_sites_not :
    ∀ w ∈ ([14111, 19816, 838, 14112, 19815, 19814] : List Wire),
      w ∉ ECDSAAdd.Frontier.OB5Support.sites streamLayout := by
  intro w hw h
  simp only [ECDSAAdd.Frontier.OB5Support.sites, List.mem_cons, List.mem_append] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases h with ((h | h) | h) | h
  · rw [streamLayout_gen] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
  · rw [streamLayout_point] at h; simp only [List.mem_range'_1] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [streamLayout_point] at h; simp only [List.mem_range'_1] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · obtain ⟨i, hi, e⟩ := ECDSAAdd.Frontier.OB5Support.pool_index streamLayout _ h
    rw [streamPool_at i (by omega)] at e
    (try dsimp only [ShorECDLP.Wire, ECDSAAdd.Wire] at e)
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem ctl4_arithS (b : Bool) :
    14111 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    19816 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    838 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    14112 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    19815 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    19814 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) := by
  have h := wires_avoid_of
    ((ECDSAAdd.Frontier.arithS_sub streamLayout streamLayout_widths streamLayout_nodup b).wires_sub.trans
      (ECDSAAdd.Frontier.ArithmeticOB5.arith_support streamLayout streamLayout_widths b))
    ctl4_sites_not
  exact ⟨h 14111 (by simp), h 19816 (by simp), h 838 (by simp),
    h 14112 (by simp), h 19815 (by simp), h 19814 (by simp)⟩

theorem ctl4_square :
    14111 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    19816 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    838 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    14112 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    19815 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    19814 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) := by
  have h := wires_avoid_of
    (ECDSAAdd.Frontier.SquareOB5.support streamLayout streamLayout_widths streamLayout_nodup)
    ctl4_sites_not
  exact ⟨h 14111 (by simp), h 19816 (by simp), h 838 (by simp),
    h 14112 (by simp), h 19815 (by simp), h 19814 (by simp)⟩

theorem code_avoid4 (c : WCode 32768) (hav : AvoidsB c) :
    (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
      14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
    14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
    838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
    19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c) := by
  intro h0
  exfalso
  rcases h0 with h1 | h2 | h3 | h4
  · obtain ⟨p, hp, hw⟩ := litProg_wires c 14877 h1; exact hav.1 14877 (by decide) p hp hw
  · obtain ⟨p, hp, hw⟩ := litProg_wires c 14876 h2; exact hav.1 14876 (by decide) p hp hw
  · obtain ⟨p, hp, hw⟩ := litProg_wires c 14875 h3; exact hav.1 14875 (by decide) p hp hw
  · obtain ⟨p, hp, hw⟩ := litProg_wires c 14874 h4; exact hav.1 14874 (by decide) p hp hw

theorem lit_ctl4 (p : ECDSAAdd.Program)
    (h : 14111 ∉ ECDSAAdd.wires p ∧ 19816 ∉ ECDSAAdd.wires p ∧
      838 ∉ ECDSAAdd.wires p ∧ 14112 ∉ ECDSAAdd.wires p ∧
      19815 ∉ ECDSAAdd.wires p ∧ 19814 ∉ ECDSAAdd.wires p) :
    (14877 ∈ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∨
      14876 ∈ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∨
      14875 ∈ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∨
      14874 ∈ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p))) →
    14111 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    19816 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    838 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    14112 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    19815 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    19814 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) := by
  intro _; rw [litProg_wLiteral]; exact h

theorem rowC_plain_ctl4 (code : WCode 32768) (hb : Block2.plain code ∈ WEXUnlookup.rowC) :
    (14877 ∈ ECDSAAdd.wires (litProg code) ∨ 14876 ∈ ECDSAAdd.wires (litProg code) ∨
      14875 ∈ ECDSAAdd.wires (litProg code) ∨ 14874 ∈ ECDSAAdd.wires (litProg code)) →
    14111 ∉ ECDSAAdd.wires (litProg code) ∧ 19816 ∉ ECDSAAdd.wires (litProg code) ∧
    838 ∉ ECDSAAdd.wires (litProg code) ∧ 14112 ∉ ECDSAAdd.wires (litProg code) ∧
    19815 ∉ ECDSAAdd.wires (litProg code) ∧ 19814 ∉ ECDSAAdd.wires (litProg code) := by
  have key : ∀ b ∈ WEXUnlookup.rowC, ∀ c, b = Block2.plain c →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c) := by
    rw [WEXUnlookup.rowC, WEXUnlookup.rowHead, WEXUnlookup.rowPre3, generic3_list, WEXUnlookup.rowPost3]
    simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.forall_mem_cons, List.forall_mem_nil, List.not_mem_nil, toBlock2, Block2.plain.injEq, reduceCtorEq,
      false_implies, implies_true, forall_eq', forall_const, and_true, true_and]
    exact ⟨code_avoid4 _ flip_avoidsB, code_avoid4 _ head_avoidsB, code_avoid4 _ guard5_avoidsB,
      lit_ctl4 _ (ctl4_arithS false), code_avoid4 _ guard5_avoidsB, lit_ctl4 _ ctl4_square,
      code_avoid4 _ guard5_avoidsB, lit_ctl4 _ (ctl4_arithS true), code_avoid4 _ guard5_avoidsB,
      code_avoid4 _ negXReg_avoidsB, code_avoid4 _ zrep_avoidsB, code_avoid4 _ cornerNeg_avoidsB,
      code_avoid4 _ sfxTailF_avoidsB, code_avoid4 _ flip_avoidsB⟩
  exact key _ hb code rfl

theorem rowC_unit_no4 (u : UnitSite 32768) (hu : Block2.unit u ∈ WEXUnlookup.rowC) :
    (∀ p, WInstr.literal p ∈ u.code → ∀ w ∈ ECDSAAdd.wires p,
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874) ∧
    (∀ c ps, WInstr.lookup c ps ∈ u.code →
      (∀ q ∈ c, q ≠ 14877 ∧ q ≠ 14876 ∧ q ≠ 14875 ∧ q ≠ 14874) ∧
      (∀ w ∈ portTargets ps, w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874)) := by
  have hav := rowC_unit_avoidsB u hu
  refine ⟨fun p hp w hw => ⟨fun e => hav.1 14877 (by decide) p hp (e ▸ hw),
    fun e => hav.1 14876 (by decide) p hp (e ▸ hw),
    fun e => hav.1 14875 (by decide) p hp (e ▸ hw),
    fun e => hav.1 14874 (by decide) p hp (e ▸ hw)⟩, fun c ps hp => ⟨fun q hq =>
      ⟨(hav.2 14877 (by decide) c ps hp).2 q hq, (hav.2 14876 (by decide) c ps hp).2 q hq,
       (hav.2 14875 (by decide) c ps hp).2 q hq, (hav.2 14874 (by decide) c ps hp).2 q hq⟩,
      fun w hw => ⟨fun e => (hav.2 14877 (by decide) c ps hp).1 (e ▸ hw),
        fun e => (hav.2 14876 (by decide) c ps hp).1 (e ▸ hw),
        fun e => (hav.2 14875 (by decide) c ps hp).1 (e ▸ hw),
        fun e => (hav.2 14874 (by decide) c ps hp).1 (e ▸ hw)⟩⟩⟩

theorem rowC_look_newH7 (c : Option Wire) (ps : List (LookupPort 32768))
    (hm : WInstr.lookup c ps ∈ erase2 WEXUnlookup.rowC) :
    (∀ q ∈ c, q ∈ newSourceH7) ∧ portTargets ps ⊆ newSourceH7 := by
  have h0 := PathShare.rowC_look_newH c ps hm
  obtain ⟨b, hb, hbi⟩ := List.mem_flatMap.mp hm
  cases b with
  | plain code =>
    obtain ⟨p, hp⟩ := PathShare.rowC_plain_lit code hb _ hbi
    cases hp
  | unit u =>
    have hu := (rowC_unit_no4 u hb).2 c ps hbi
    exact ⟨fun q hq => newSourceH7_of_newH q (h0.1 q hq) (hu.1 q hq).1 (hu.1 q hq).2.1 (hu.1 q hq).2.2.1 (hu.1 q hq).2.2.2,
      fun w hw => newSourceH7_of_newH w (h0.2 hw) (hu.2 w hw).1 (hu.2 w hw).2.1 (hu.2 w hw).2.2.1 (hu.2 w hw).2.2.2⟩

theorem rowC_lit_relaxed7 (p : ECDSAAdd.Program) (hm : WInstr.literal p ∈ erase2 WEXUnlookup.rowC) :
    ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = hostWire4 ∨ w = hostWire5 ∨ w = hostWire6 ∨ w = hostWire7 ∨ w ∈ newSourceH7 :=
  fun w hw => relaxed7_of_new w (List.mem_toFinset.mp (W15C.rowC_lit_new p hm hw))

def blockExtra {n} : Block2 n → Nat
  | .plain code => hostCodeExtra code
  | .unit _ => 0

def codeExtra {n} : Code2 n → Nat
  | [] => 0
  | b :: code => blockExtra b + codeExtra code

theorem codeExtra_append {n} (a b : Code2 n) : codeExtra (a ++ b) = codeExtra a + codeExtra b := by
  induction a with
  | nil => simp [codeExtra]
  | cons x a ih => simp [codeExtra, ih, Nat.add_assoc]

private theorem codeExtra_cons_le {n} (b : Block2 n) (bs : Code2 n) (k m : Nat)
    (hb : blockExtra b ≤ k) (hbs : codeExtra bs ≤ m) : codeExtra (b :: bs) ≤ k + m := by
  simp only [codeExtra]; omega

theorem rowC_codeExtra_le : codeExtra WEXUnlookup.rowC ≤ 6 := by
  have h0 (c : WCode 32768) (hav : AvoidsB c) : blockExtra (.plain c) ≤ 0 :=
    Nat.le_of_eq (hostCodeExtra_zero_of_avoidsB c hav)
  have hu (u : UnitSite 32768) : blockExtra (.unit u) ≤ 0 := Nat.le_refl 0
  have h2 (p : ECDSAAdd.Program) : blockExtra (.plain (wLiteral (n := 32768) p)) ≤ 2 :=
    hostCodeExtra_le _
  rw [WEXUnlookup.rowC, WEXUnlookup.rowHead, WEXUnlookup.rowPre3, generic3_list, WEXUnlookup.rowPost3]
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, toBlock2]
  refine codeExtra_cons_le _ _ 0 6 (h0 _ flip_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 6 (h0 _ head_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 6 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 6 (h0 _ guard5_avoidsB) ?_
  refine codeExtra_cons_le _ _ 2 4 (h2 _) ?_
  refine codeExtra_cons_le _ _ 0 4 (h0 _ guard5_avoidsB) ?_
  refine codeExtra_cons_le _ _ 2 2 (h2 _) ?_
  refine codeExtra_cons_le _ _ 0 2 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 2 (h0 _ guard5_avoidsB) ?_
  refine codeExtra_cons_le _ _ 2 0 (h2 _) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ guard5_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ negXReg_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ zrep_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ cornerNeg_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 0 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ sfxTailF_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ flip_avoidsB) ?_
  exact Nat.le_refl 0

theorem hostCodeExtra_rows {m} (f : Nat → Fin m) (c : WCode 32768) :
    hostCodeExtra (WideSigned.Rows.code f c) = hostCodeExtra c := by
  have hall : (WideSigned.Rows.code f c).all isLit = c.all isLit := by
    induction c with
    | nil => rfl
    | cons i c ih =>
      cases i with
      | literal p =>
        change (isLit (WInstr.literal p) && (WideSigned.Rows.code f c).all isLit) =
          (isLit (WInstr.literal p) && c.all isLit)
        rw [ih]; rfl
      | lookup ctrl ps => rfl
  have hlit : litProg (WideSigned.Rows.code f c) = litProg c := by
    clear hall
    induction c with
    | nil => rfl
    | cons i c ih =>
      cases i with
      | literal p =>
        change p ++ litProg (WideSigned.Rows.code f c) = p ++ litProg c
        rw [ih]
      | lookup ctrl ps =>
        change litProg (WideSigned.Rows.code f c) = litProg c
        exact ih
  simp only [hostCodeExtra, hall, hlit]

theorem codeExtra_rows {m} (f : Nat → Fin m) (code : Code2 32768) :
    codeExtra (code.map (WideSigned.Rows.block f)) = codeExtra code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    cases b with
    | plain c => simp [WideSigned.Rows.block, codeExtra, blockExtra, hostCodeExtra_rows, ih]
    | unit u => simp [WideSigned.Rows.block, codeExtra, blockExtra, ih]

/-! ### Hosted narrow blocks (`PathShare.Bank`) using `hostCode7` -/

def blockProgH7 {n} (B : PathShare.Bank) (b : Block2 n) (start : Nat) :
    Straight n start (start + blockRecP2 B b) :=
  match b with
  | .plain code => castFinish (congrArg (fun k => start + k) (hostCode7_counts B.bits B.paths windowRoot code).1)
      (compile B.bits B.paths windowRoot (hostCode7 code) start)
  | .unit u => blockProgP2 B (.unit u) start

def blockSourceH7 {n} (B : PathShare.Bank) (read : ConstantBit n → Bool) : Block2 n → AdaptiveCircuit
  | .plain code => source read B.bits B.paths windowRoot (hostCode7 code)
  | .unit u => blockSourceP2 B read (.unit u)

def blockTP7 {n} (B : PathShare.Bank) : Block2 n → Nat
  | .plain code => blockTP2 B (.plain code) + hostCodeExtra code
  | .unit u => blockTP2 B (.unit u)

def BlockSimH7 {n} (read : ConstantBit n → Bool) (B : PathShare.Bank) (block : Block2 n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, AddrValid B.bits windowRoot address st → BlockClean2 B.paths block st → HostOK7 block st →
      BlockSafe2 read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference2 read address block) m st)

theorem blockProgH7_run {n} (B : PathShare.Bank) (read : ConstantBit n → Bool) (b : Block2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgH7 B b start).instantiate read history).run = (blockSourceH7 B read b).run := by
  cases b with
  | plain code =>
    rw [blockProgH7, castFinish_instantiate]
    exact compile_run read _ _ _ _ _ _
  | unit u => exact blockProgP2_run B read (.unit u) start history

theorem block_simulationH7 {n} (read : ConstantBit n → Bool) (B : PathShare.Bank) (hB : BankOK B)
    (block : Block2 n) (hg : BlockGeoP2 B block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimH7 read B block) (blockSourceH7 B read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    have hlit : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    let P := ECDSAAdd.Baselines.normalizeProgram (litProg code)
    have hc : hostCode7 code = [.literal (hostBlock7 P)] :=
      hostCode7_eq_host ((allLit_iff code).mpr hlit)
    have hRP : windowRoot ∉ ECDSAAdd.wires P := by
      intro hw
      rw [ECDSAAdd.Baselines.normalize_wires] at hw
      obtain ⟨p, hp, hw⟩ := litProg_wires code windowRoot hw
      obtain ⟨q, he, hq⟩ := hg' _ hp
      cases he
      exact hq windowRoot (by simp) hw
    show ∃ cs : List ℂ, List.Forall₂ (BlockSimH7 read B (.plain code))
      (source read B.bits B.paths windowRoot (hostCode7 code)).run cs ∧ (cs.map Complex.normSq).sum = 1
    rw [hc]
    obtain ⟨cs, aligned, mass⟩ := lit_simulation read B.bits B.paths windowRoot
      ([.literal (hostBlock7 P)] : WCode n) (by simp)
    refine ⟨cs, aligned.imp ?_, mass⟩
    intro b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, ?_, fun address st hs _ hh _ => ?_⟩
    · rw [hm]
      simp only [literalRecords, hostBlock7_meas, P, ECDSAAdd.Baselines.normalize_measurements, Nat.add_zero]
      exact litProg_meas code hlit
    · rw [hb address st]
      have e1 : (specialize ([.literal (hostBlock7 P)] : WCode n) address).instantiate read = hostBlock7 P := by
        rw [show ([.literal (hostBlock7 P)] : WCode n) = wLiteral (hostBlock7 P) from rfl,
          specialize_literal, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      have e2 : blockReference2 read address (.plain code : Block2 n) = litProg code := by
        simp only [blockReference2, Block2.code]
        exact litProg_inst read code address hlit
      have hrun : ECDSAAdd.run P m st = ECDSAAdd.run (litProg code) m st :=
        ECDSAAdd.Baselines.normalize_run _ m st
      have hwP : ECDSAAdd.wires P = ECDSAAdd.wires (litProg code) := ECDSAAdd.Baselines.normalize_wires _
      have hh3 := hh.1
      have hh4 := hh.2
      rw [e1, e2, hostBlock7_run P hRP m st hs.2 hh3.1.1.1 (by rw [hrun]; exact hh3.1.1.2 m)
        (fun c1 c2 => by
          rw [hwP] at c1 c2
          obtain ⟨d1, d2, d3⟩ := hh3.1.2 c1 c2
          exact ⟨d1, d2, by rw [hrun]; exact d3 m⟩)
        (fun c1 c2 => by
          rw [hwP] at c1 c2
          obtain ⟨d1, d2, d3⟩ := hh3.2 c1 c2
          exact ⟨d1, d2, by rw [hrun]; exact d3 m⟩)
        (fun c4 => by
          have c4' : host4Set (litProg code) := by simpa [host4Set, hwP] using c4
          obtain ⟨f1, f2, f3⟩ := hh4 c4'
          exact ⟨f1, f2, by rw [hrun]; exact (f3 m).1, by rw [hrun]; exact (f3 m).2⟩), hrun]
  | unit u =>
    obtain ⟨cs, aligned, mass⟩ := block_simulationP2 read B hB (.unit u) hg
    refine ⟨cs, aligned.imp ?_, mass⟩
    intro b c hb
    obtain ⟨m, hm, hb⟩ := hb
    exact ⟨m, hm, fun address st hs hc _ hsafe => hb address st hs hc hsafe⟩

theorem blockH7_wellFormed {n} (B : PathShare.Bank) (hB : BankOK B) (b : Block2 n) (hgb : BlockGeoP2 B b)
    (hpb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (blockProgH7 B b start).WellFormed := by
  cases b with
  | plain code =>
    have hg' : LitAvoid B.bits code := hgb
    have hlit : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    rw [blockProgH7, castFinish_wellFormed, hostCode7_eq_host ((allLit_iff code).mpr hlit)]
    apply compile_wellFormedLit _ _ _ _ (by simp)
    intro p hp
    rw [List.mem_singleton, WInstr.literal.injEq] at hp
    subst hp
    apply hostBlock7_valid
    apply ECDSAAdd.Baselines.normalize_physical
    intro i hi
    obtain ⟨q, hq, hi⟩ := litProg_mem code i hi
    exact hpb q hq i hi
  | unit u =>
    exact blockH_wellFormed B hB (.unit u) hgb hpb start

theorem blockH7_tCount {n} (read : ConstantBit n → Bool) (B : PathShare.Bank) (b : Block2 n) (hl : BlockLay2 B b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgH7 B b start).instantiate read history).tCount = 7 * blockTP7 B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    obtain ⟨-, e2, e3⟩ := hostCode7_counts B.bits B.paths windowRoot code
    rw [blockProgH7, castFinish_instantiate,
      WEX.compile_tCount read _ _ _ _ (hostCode7_layouts _ _ _ code hl') start history, e2, e3]
    simp only [blockTP7, blockTP2]; ring
  | unit u => exact blockProgP2_tCount read B (.unit u) hl start history

theorem blockH7_slots {n} (B : PathShare.Bank) (b : Block2 n) (hl : BlockLay2 B b) (start : Nat) :
    (blockProgH7 B b start).gateSlots ≤ blockSP2 B b + 26 := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgH7, castFinish_gateSlots, WEX.compile_slots _ _ _ _ (hostCode7_layouts _ _ _ code hl') start]
    exact hostCode7_slots B.bits code
  | unit u =>
    have h := blockProgP2_slots B (.unit u) hl start
    change (blockProgP2 B (.unit u) start).gateSlots ≤ _
    omega

theorem blockH7_residue {n} (B : PathShare.Bank) (b : Block2 n) (start : Nat) :
    AndGadget.residue (blockProgH7 B b start) = 0 := by
  cases b with
  | plain code =>
    rw [blockProgH7, AndGadget.residue_cast]
    exact WEXCredit.compile_residue _ _ _ _ _
  | unit u => exact blockH_residue B (.unit u) start

theorem blockH7_support (B : PathShare.Bank) (hB : BankOK B) (b : Block2 32768) (hg : BlockGeoP2 B b)
    (S : List Wire) (hroot : windowRoot ∈ S) (hctl : hostCtl ∈ S) (hctl3 : hostCtl3 ∈ S)
    (hc11 : (14111 : Wire) ∈ S) (hc16 : (19816 : Wire) ∈ S) (hc838 : (838 : Wire) ∈ S)
    (hc12 : (14112 : Wire) ∈ S) (hc15 : (19815 : Wire) ∈ S) (hc14 : (19814 : Wire) ∈ S)
    (hc13 : (14113 : Wire) ∈ S)
    (hbits : B.bits ⊆ S) (hpaths : B.paths ⊆ S) (hlow : ∀ i, WEXUnlookup.low i ∈ S) (hhigh : B.high ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ b.code → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = hostWire4 ∨ w = hostWire5 ∨ w = hostWire6 ∨ w = hostWire7 ∨ w ∈ S)
    (hstrict : ∀ p, WInstr.literal p ∈ b.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       hostWire4 ∈ ECDSAAdd.wires p ∨ hostWire5 ∈ ECDSAAdd.wires p ∨ hostWire6 ∈ ECDSAAdd.wires p ∨
       hostWire7 ∈ ECDSAAdd.wires p) → ∃ c, b = .plain c)
    (hctl2 : ∀ c, b = .plain c → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3' : ∀ c, b = .plain c → hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hctl4 : ∀ c, b = .plain c →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ b.code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (blockProgH7 B b start) ⊆ S := by
  cases b with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    have hlit' : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    rw [blockProgH7, support_cast, hostCode7_eq_host ((allLit_iff code).mpr hlit')]
    apply compile_support B.bits B.paths windowRoot _ S hroot hbits hpaths _ (fun c ps hm => by simp at hm) start
    intro p hp
    rw [List.mem_singleton, WInstr.literal.injEq] at hp
    subst hp
    let P := ECDSAAdd.Baselines.normalizeProgram (litProg code)
    have hwP : ECDSAAdd.wires P = ECDSAAdd.wires (litProg code) := ECDSAAdd.Baselines.normalize_wires _
    have hRP : windowRoot ∉ ECDSAAdd.wires P := by
      intro hw
      rw [hwP] at hw
      obtain ⟨q, hq, hqw⟩ := litProg_wires code windowRoot hw
      obtain ⟨q', he, hq'⟩ := hg' _ hq
      cases he; exact hq' windowRoot (by simp) hqw
    exact hostBlock7_wires P S hroot hctl hctl3 hc11 hc16 hc838 hc12 hc15 hc14 hc13 hRP
      (fun w hw => by
        rw [hwP] at hw
        obtain ⟨q, hq, hqw⟩ := litProg_wires code w hw
        exact hlit q hq w hqw)
      (fun hm => by rw [hwP] at hm ⊢; exact hctl2 code rfl hm)
      (fun hm => by rw [hwP] at hm ⊢; exact hctl3' code rfl hm)
      (fun hm => by rw [hwP] at hm ⊢; exact hctl4 code rfl hm)
  | unit u =>
    have hlitU : ∀ p, WInstr.literal p ∈ (Block2.unit u).code → ECDSAAdd.wires p ⊆ S.toFinset := by
      intro p hp w hw
      rcases hlit p hp w hw with e | e | e | e | e | e | e | e
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inl (e ▸ hw)); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inl (e ▸ hw))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inl (e ▸ hw)))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw)))))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e ▸ hw))))))); cases hc
      · exact List.mem_toFinset.mpr e
    have hg' : UnitGeoP B u := hg
    have hpl : ∀ p, WInstr.literal p ∈ u.pre → ECDSAAdd.wires p ⊆ S.toFinset :=
      fun p hm => hlitU p (List.mem_append_left _ hm)
    have hpk : ∀ c ps, WInstr.lookup c ps ∈ u.pre → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
      fun c ps hm => hlook c ps (List.mem_append_left _ hm)
    have hlast := hlook (some u.clear.guard) u.clear.ports (by simp [Block2.code, UnitSite.code])
    show ChallengeMigration.straightWires (blockProgP2 B (.unit u) start) ⊆ S
    rw [blockProgP2, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
      (normalized_lit_support _ S hpl) (normalized_look_support _ S hpk) start,
      clearP_support B hB u.clear hg'.site.kind S hlast.2 (hlast.1 u.clear.guard (Option.mem_def.mpr rfl))
        hlow hhigh hpaths _⟩

end
end ShorECDLP.Entrant.PoolHost
