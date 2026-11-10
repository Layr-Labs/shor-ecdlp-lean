import ShorECDLP.Submission.Entrant.WideBank8

/-! # Deferred garbage fixups on the narrow (width-15) rows

Each narrow fast site measures its garbage register at once (the register is reset for reuse) but
repays that measurement's phase inside the site clear after the arithmetic: the clear's fixup carries
the garbage ports as well as its own. The measurement, the arithmetic and the fused fixup are proved
as one unit (`tail_sim7`); the deferred phase is read from the guard and the address at fixup time,
which the arithmetic leaves unchanged. -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem fixupFactor7_append {n : Nat} (d1 d2 : List (ClearPort n)) (o1 o2 : List Bool)
    (h : o1.length = d1.length) (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) :
    fixupFactor (d1 ++ d2) (o1 ++ o2) read low hot tree root s =
      fixupFactor d1 o1 read low hot tree root s * fixupFactor d2 o2 read low hot tree root s := by
  have hz : (d1 ++ d2).zip ((o1 ++ o2).map boolRecord) = d1.zip (o1.map boolRecord) ++ d2.zip (o2.map boolRecord) := by
    rw [List.map_append]
    exact List.zip_append (by simp [h])
  simp only [fixupFactor, phaseLookupFactor, logicalPorts, hz, phasePorts, List.flatMap_append,
    recordTargets_append, xorPhase_append]

theorem fixupFactor7_loaded {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (t u : BasisState) (hhot : HotClean hot t)
    (hw : ∀ p ∈ data, u p.target =
      (t root && decide (read (p.ref (128 * tree.routeLabel t + hotAddress low t)) = p.value))) :
    fixupFactor data outcomes read low hot tree root t =
      registerXPhase (data.map ClearPort.target) outcomes u := by
  let prepared := Classical.run (hotPrepare low hot) t
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = t w :=
    hotPrepare_frame low hot t w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)
  have hroute : tree.routeLabel prepared = tree.routeLabel t := by
    apply tree.routeLabel_congr prepared t
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 128 := ⟨hotAddress low t, hotAddress_bound low t⟩
  apply phaseFactor_loaded data outcomes read hot tree root u prepared selected
  · intro i
    simpa only [Fin.ext_iff] using hotPrepare_marker low hot hi hdlow t hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hw p hp

end
end ShorECDLP.Entrant.MeasuredClear

/-! ### The deferred tail of a narrow fast site -/

namespace ShorECDLP.Entrant.WEXFast.Defer
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open MeasuredClear (ClearPort)
open WideBank8 (GuardKept guardKept_run)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def fuseRec {n} (B : Bank) (site : MaskedSite n) : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) site.guard B.hp) + 127

def fusedFix {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat)
    (refs : List (Fin start)) : Straight n start (start + site.ports.length + fuseRec B site) :=
  castFinish (by simp [clearData]) (MeasuredClear.measureThen (R := fuseRec B site)
    (fun cursor rs => castFinish (by simp only [fuseRec]; omega)
      (MeasuredClear.fixupProgram (gd ++ clearData site.ports) rs low (clearHot site)
        (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp))
    ((clearData site.ports).map ClearPort.target) start refs)

def tailRec {n} (B : Bank) (site : MaskedSite n) : Nat :=
  codeRecords B.bits B.paths windowRoot (normalizeW site.arithmetic) + (site.ports.length + fuseRec B site)

def deferTail {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat) :
    Straight n start (start + gd.length + tailRec B site) :=
  castFinish (by simp) (MeasuredClear.measureThen (R := tailRec B site)
    (fun cursor grefs => castFinish (by simp only [tailRec]; omega)
      ((compile B.bits B.paths windowRoot (normalizeW site.arithmetic) cursor).append
        (fusedFix B site gd (cursor + codeRecords B.bits B.paths windowRoot (normalizeW site.arithmetic))
          (grefs.map (Fin.castLE (Nat.le_add_right _ _))))))
    (gd.map ClearPort.target) start List.nil)

def fusedFixSource {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (og : List Bool) : AdaptiveCircuit :=
  measureResetThen ((clearData site.ports).map ClearPort.target) (fun os =>
    MeasuredClear.fixupSource (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
      (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp)

def deferSource {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) : AdaptiveCircuit :=
  measureResetThen (gd.map ClearPort.target) (fun og =>
    (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq (fusedFixSource B read site gd og))

theorem fusedFix_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((fusedFix B site gd start refs).instantiate read history).run =
      (fusedFixSource B read site gd (refs.map history)).run := by
  rw [fusedFix, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun outcomes => MeasuredClear.fixupSource (gd ++ clearData site.ports) outcomes
      read low (clearHot site) (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp) read
      (by intro cursor rs h; rw [castFinish_instantiate, MeasuredClear.fixupProgram_run])]
  rfl

theorem deferTail_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (start : Nat) (history : Fin start → Bool) :
    ((deferTail B site gd start).instantiate read history).run = (deferSource B read site gd).run := by
  rw [deferTail, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun og => (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
      (fusedFixSource B read site gd og)) read]
  · simp only [List.map_nil, List.nil_append]
    rfl
  · intro cursor grefs h
    rw [castFinish_instantiate,
      MeasuredClear.append_run_prefix _ _ read (Nat.le_refl cursor) h h rfl
        (fusedFixSource B read site gd (grefs.map h)),
      AdaptiveCircuit.run_seq, compile_run, ← AdaptiveCircuit.run_seq]
    intro h' hh'
    rw [fusedFix_run, List.map_map]
    congr 2
    rw [← hh']
    rfl

theorem site_clear_facts {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site) :
    (tableAddressTree B.high 0 1).Layout site.guard B.hp ∧
    Function.Injective (clearHot site) ∧
    (∀ i j, low i ≠ clearHot site j) ∧
    (MeasuredClear.hotBank (clearHot site)).Disjoint
      (site.guard :: (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp) ∧
    scratch site ∉ site.guard :: (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp ∧
    scratch site ∉ MeasuredClear.hotBank (clearHot site) ∧
    (∀ w ∈ site.guard :: List.ofFn low ++ (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp,
      w ∉ portTargets site.ports) ∧
    (∀ w ∈ B.bits, w ∉ portTargets site.ports) ∧
    (∀ i, clearHot site i ∈ portTargets site.ports) := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  obtain ⟨hn,hbd,hhot,hmem,hsm,hgd,-⟩ := kind_facts site hg.kind
  have hP : ∀ w ∈ B.hp, 871 ≤ w ∧ w ∉ portTargets site.ports := by
    intro w hw
    refine ⟨hB.out w hw, fun ht => ?_⟩
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
        simp [hB.sub w hw]) ht
  have notT : ∀ w ∈ site.guard :: List.ofFn low ++ B.high ++ B.hp, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with ((h | h) | h) | h
    · rw [h] at h2; rcases hgd with e | e <;> rw [e] at h2 <;> dsimp only [Wire] at * <;> omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      have := low_lt i
      dsimp only [Wire] at *; omega
    · have := hB.high w h
      dsimp only [Wire] at *; omega
    · exact (hP w h).2 ht
  have hgH : site.guard ∉ B.high := by
    intro h; have := hB.high _ h; rcases hgd with e | e <;> rw [e] at this <;> dsimp only [Wire] at * <;> omega
  have hPg : site.guard ∉ B.hp := by
    intro hg'
    have hn := hlast.1
    simp only [lookupRoot, Option.getD_some, List.cons_append, List.nodup_cons] at hn
    exact hn.1 (List.mem_append_right _ (hB.sub _ hg'))
  have hnodup : (site.guard :: B.high ++ B.hp).Nodup := by
    rw [List.cons_append, List.nodup_cons]
    refine ⟨fun h => ?_, hB.nodup⟩
    rcases List.mem_append.mp h with h | h
    · exact hgH h
    · exact hPg h
  refine ⟨tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len hnodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem⟩
  · intro i j he; apply Fin.ext; rw [hhot i,hhot j] at he; dsimp only [Wire] at he; omega
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low_lt i
    rw [← he] at h1
    dsimp only [Wire] at *
    omega
  · apply List.disjoint_left.mpr
    intro w hw hm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    rw [hB.index] at hm
    exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) (hmem i)
  · rw [hB.index]
    intro hm
    exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) hsm
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    rw [hhot i] at hi
    dsimp only [Wire] at hi
    omega
  · rw [hB.index]
    intro w hw hm
    exact notT w hw hm
  · intro w hw ht
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by simp [hw]) ht

def FixSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ (next : ECDSAAdd.State) (u : BasisState), Clean B.hp next.basis →
    (∀ p ∈ site.ports, next.basis p.target =
      (next.basis site.guard && decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value))) →
    (∀ p ∈ gd, u p.target =
      (next.basis site.guard && decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value))) →
    b.kraus (Bridge.signedKet next) =
      (c * registerXPhase (gd.map ClearPort.target) og u) •
        Bridge.signedKet ⟨next.phase, clearRegister (portTargets site.ports) next.basis⟩

theorem fusedFix_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (gd : List (ClearPort n)) (og : List Bool) (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (FixSim B read site gd og) (fusedFixSource B read site gd og).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨hl, hi, hdlow, hbank, hs, hshot, ha, hbits, hmem⟩ := site_clear_facts B hB site hg
  obtain ⟨hn,-,-,-,-,-,-⟩ := kind_facts site hg.kind
  unfold fusedFixSource
  apply MeasuredClear.measureResetThen_sim ((clearData site.ports).map ClearPort.target)
    (fun os => MeasuredClear.fixupSource (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
      (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp)
    (fun os => BranchCoherentOn (MeasuredClear.basisIdeal id
      (MeasuredClear.fixupFactor (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
        (tableAddressTree B.high 0 1) site.guard))
      (fun s => MeasuredClear.HotClean (clearHot site) s ∧ Clean B.hp s))
  · intro os _
    exact MeasuredClear.fixupSource_coherent (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
      (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp
      hl hi hdlow hbank hs hshot
  · intro os hos b c hb next u hhp hsite hgarb
    rw [clearData_targets] at hos ⊢
    have hk := xResetRegisterKraus_ket (portTargets site.ports) os next.basis hos hn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hos] at hk
    set t := clearRegister (portTargets site.ports) next.basis with ht
    have hfr : ∀ w, w ∉ portTargets site.ports → t w = next.basis w :=
      fun w hw => MeasuredClear.clearRegister_frame _ _ _ hw
    have hhot : MeasuredClear.HotClean (clearHot site) t := fun i => clearRegister_clean _ _ _ (hmem i)
    have hvalid : MeasuredClear.HotClean (clearHot site) t ∧ Clean B.hp t :=
      ⟨hhot, fun w hw => by rw [hfr w (ha w (by simp [hw]))]; exact hhp w hw⟩
    have hsplit : ∀ s : BasisState, 128 * (tableAddressTree B.high 0 1).routeLabel s +
        MeasuredClear.hotAddress low s = tableAddressValue B.bits s := hB.split
    have haddr : tableAddressValue B.bits t = tableAddressValue B.bits next.basis :=
      WEX.tableAddressValue_congr _ _ _ (fun w hw => hfr w (hbits w hw))
    have hguard : t site.guard = next.basis site.guard := hfr _ (ha _ (by simp))
    have hfac : MeasuredClear.fixupFactor (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
        (tableAddressTree B.high 0 1) site.guard t =
        registerXPhase (gd.map ClearPort.target) og u * registerXPhase (portTargets site.ports) os next.basis := by
      rw [MeasuredClear.fixupFactor7_append _ _ _ _ hog]
      congr 1
      · apply MeasuredClear.fixupFactor7_loaded gd og read low (clearHot site) _ site.guard B.hp
          hi hdlow hbank t u hhot
        intro p hp
        rw [hsplit, haddr, hguard]
        exact hgarb p hp
      · have h := MeasuredClear.fixupFactor_recycled (clearData site.ports) os read low (clearHot site)
          (tableAddressTree B.high 0 1) site.guard B.hp hi hdlow hbank
          (by rw [clearData_targets]; exact ha) (by rw [clearData_targets]; exact hmem) next.basis
          ⟨hhp, by
            intro q hq
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            simpa [hsplit] using hsite p hp⟩
        simpa only [clearData_targets] using h
    have hsq := MeasuredClear.registerXPhase_square (portTargets site.ports) os next.basis
    change b.kraus (xResetRegisterKraus (portTargets site.ports) os (Bridge.signedKet next)) = _
    simp only [Bridge.signedKet, map_smul, hk, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac,
      smul_smul]
    congr 1
    linear_combination ((if next.phase then (-1 : ℂ) else 1) * registerXResetMagnitude (portTargets site.ports).length *
      c * registerXPhase (gd.map ClearPort.target) og u) * hsq

def InnerSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords site.arithmetic ∧
    ∀ a (st : ECDSAAdd.State) (u : BasisState), SimulationValid B.bits B.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports)
        (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      (∀ p ∈ gd, u p.target = (st.basis site.guard && decide (read (p.ref a) = p.value))) →
      b.kraus (Bridge.signedKet ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) =
        (c * registerXPhase (gd.map ClearPort.target) og u) •
          Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st)

theorem inner_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (hk : GuardKept site) (gd : List (ClearPort n)) (og : List Bool)
    (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (InnerSim B read site gd og)
      ((source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
        (fusedFixSource B read site gd og)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hpre : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have harith : ∀ i ∈ site.arithmetic, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    hpre i (List.mem_cons_of_mem _ hi)
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen site.arithmetic
    (fun i hi => pair_of_placed_lit _ _ i (harith i hi))
  obtain ⟨c2, a2, m2⟩ := fusedFix_sim read B hB site hg gd og hog
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₁⟩ := h₁
    refine ⟨m, hm, ?_⟩
    intro a st u hs hun hu
    have hload := hg.placed (.lookup (some site.guard) site.ports)
      (by simp [MaskedSite.code, MaskedSite.prefix])
    have hL := lookup_preserves_simulation read (some site.guard) site.ports B.bits B.paths
      windowRoot a hload st hs
    simp only [lookupRoot, Option.getD_some] at hL
    have hroot : site.guard ∉ portTargets site.ports :=
      List.disjoint_left.mp hload.2.2 (by simp [lookupRoot])
    have e : ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st =
        ECDSAAdd.run ((specialize site.arithmetic a).instantiate read) m
          ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩ := by
      simp only [MaskedSite.prefix, specialize, List.flatMap_cons, WInstr.specialize,
        ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.run_append, (portTemplate_counts read _ _ _).2,
        List.take_zero, List.drop_zero]
      rw [portTemplate_run read (some site.guard) site.ports a windowRoot List.nil st hload.2.1 hroot hs.2.2]
      rfl
    have hn := strict_preserves read B.bits B.paths site.prefix a hpre st hs m
    have hrun := masked_runP read B site hg a st m hs
    set L : ECDSAAdd.State :=
      ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩ with hLdef
    set next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st with hnext
    have hclean : Clean (portTargets site.ports)
        (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
      have h := hun m
      rw [hrun] at h
      exact h
    have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
    have hguard : next.basis site.guard = st.basis site.guard := by
      rw [e, guardKept_run read B site hk harith a L hL m]
      exact tableXorState_outside _ _ _ _ (fun hm => hroot (tableBitsMask_subset _ _ hm))
    have hsite : ∀ p ∈ site.ports, next.basis p.target = (next.basis site.guard &&
        decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
      rw [hn.2.1]
      exact loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
    have h2 := h₂ next u (fun w hw => hn.1 w (hB.sub w hw)) hsite (by
      intro p hp
      rw [hn.2.1, hguard]
      exact hu p hp)
    have hfin : (⟨next.phase, clearRegister (portTargets site.ports) next.basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run ((specialize site.code a).instantiate read) m st := by
      rw [hrun, clear_eq_unload read site.ports a site.guard next.basis hclean]
    have h1 := h₁ a L ⟨hL.2.1, hL.2.2⟩ (strict_pathsClean read B.bits B.paths site.arithmetic a harith L hL)
    rw [← e] at h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet L)) = _
    rw [h1, map_smul, h2, hfin, smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def TailSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords site.arithmetic ∧
    ∀ a (st u : ECDSAAdd.State), SimulationValid B.bits B.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports)
        (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      (∀ p ∈ gd, u.basis p.target = (st.basis site.guard && decide (read (p.ref a) = p.value))) →
      u.phase = st.phase →
      clearRegister (gd.map ClearPort.target) u.basis =
        tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis →
      b.kraus (Bridge.signedKet u) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st)

/-- Measurement of the deferred register, the arithmetic and the fused fixup, as one unit. -/
theorem tail_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (hk : GuardKept site) (gd : List (ClearPort n))
    (hgn : (gd.map ClearPort.target).Nodup) :
    ∃ cs : List ℂ, List.Forall₂ (TailSim B read site gd) (deferSource B read site gd).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  unfold deferSource
  apply MeasuredClear.measureResetThen_sim (gd.map ClearPort.target)
    (fun og => (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
      (fusedFixSource B read site gd og)) (fun og => InnerSim B read site gd og)
  · intro og hog
    exact inner_sim read B hB site hg hk gd og (by simpa using hog)
  · intro og hog b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, hm, ?_⟩
    intro a st u hs hun hu hph hclr
    have hk' := xResetRegisterKraus_ket (gd.map ClearPort.target) og u.basis hog hgn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hog, hclr] at hk'
    have h := hb a st u.basis hs hun hu
    have hsq := MeasuredClear.registerXPhase_square (gd.map ClearPort.target) og u.basis
    change b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet u)) = _
    have hstep : b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet u)) =
        (registerXResetMagnitude (gd.map ClearPort.target).length *
          registerXPhase (gd.map ClearPort.target) og u.basis) •
          b.kraus (Bridge.signedKet ⟨st.phase,
            tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) := by
      simp only [Bridge.signedKet, hph, map_smul, hk', smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (gd.map ClearPort.target).length * c) * hsq

theorem fusedFix_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (gd : List (ClearPort n)) (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((fusedFix B site gd start refs).instantiate read history).tCount =
      7 * (tableAddressTree B.high 0 1).internalNodes + 840 := by
  rw [fusedFix, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (by
    intro cursor rs h
    rw [castFinish_instantiate, MeasuredClear.fixupProgram_tCount _ rs low (clearHot site) _ site.guard
      (scratch site) B.hp hl])]

theorem deferTail_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (gd : List (ClearPort n)) (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (hal : LookupLayouts B.bits B.paths windowRoot (normalizeW site.arithmetic))
    (start : Nat) (history : Fin start → Bool) :
    ((deferTail B site gd start).instantiate read history).tCount =
      7 * literalToffolis (normalizeW site.arithmetic) +
        7 * traversals (normalizeW site.arithmetic) * (2 ^ B.bits.length - 1) +
        (7 * (tableAddressTree B.high 0 1).internalNodes + 840) := by
  rw [deferTail, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (by
    intro cursor grefs h
    rw [castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => fusedFix_tCount read B site gd hl _ _ h'),
      compile_tCount read _ _ _ _ hal])]

theorem fusedFix_slots {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n))
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp) (start : Nat) (refs : List (Fin start)) :
    (fusedFix B site gd start refs).gateSlots =
      512 * min (gd.length + site.ports.length) (refs.length + site.ports.length) *
        (tableAddressTree B.high 0 1).leaves + 10 * (tableAddressTree B.high 0 1).internalNodes + 1140 := by
  rw [fusedFix, castFinish_gateSlots, MeasuredClear.measureThen_slots _
    (fun k => 512 * min (gd ++ clearData site.ports).length k * (tableAddressTree B.high 0 1).leaves +
      10 * (tableAddressTree B.high 0 1).internalNodes + 1140)
    (by intro cursor rs; rw [castFinish_gateSlots, MeasuredClear.fixupProgram_slots _ rs low (clearHot site) _
      site.guard (scratch site) B.hp hl])]
  simp [clearData]

theorem deferTail_slots {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n))
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (hal : LookupLayouts B.bits B.paths windowRoot (normalizeW site.arithmetic)) (start : Nat) :
    (deferTail B site gd start).gateSlots = codeSlots B.bits (normalizeW site.arithmetic) +
      (512 * (gd.length + site.ports.length) * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 1140) := by
  rw [deferTail, castFinish_gateSlots, MeasuredClear.measureThen_slots _
    (fun k => codeSlots B.bits (normalizeW site.arithmetic) +
      (512 * min (gd.length + site.ports.length) (k + site.ports.length) * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 1140))
    (by intro cursor grefs; rw [castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ hal,
      fusedFix_slots B site gd hl]; simp)]
  simp

theorem deferTail_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (gd : List (ClearPort n))
    (hlit : ∀ p, WInstr.literal p ∈ site.arithmetic → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (deferTail B site gd start).WellFormed := by
  obtain ⟨hl, hi, hdlow, hbank, hs, hshot, -, -, -⟩ := site_clear_facts B hB site hg
  have harith : ∀ i ∈ site.arithmetic, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))
  rw [deferTail, castFinish_wellFormed]
  apply MeasuredClear.measureThen_wellFormed
  intro cursor grefs
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed
  · exact pair_compile_wellFormed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ harith)
      (normalized_literals_valid site.arithmetic hlit) _
  · rw [fusedFix, castFinish_wellFormed]
    apply MeasuredClear.measureThen_wellFormed
    intro c rs
    rw [castFinish_wellFormed]
    exact MeasuredClear.fixupProgram_wellFormed _ rs low (clearHot site) _ site.guard (scratch site) B.hp hl
      hi hdlow hs hshot

open AndGadget WEXCredit in
theorem deferTail_residue {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat) :
    residue (deferTail B site gd start) = 0 := by
  rw [deferTail, residue_cast]
  apply MeasuredClear.measureThen_residue
  intro cursor grefs
  rw [residue_cast, residue_append, compile_residue, fusedFix, residue_cast, Nat.zero_add]
  apply MeasuredClear.measureThen_residue
  intro c rs
  rw [residue_cast]
  exact MeasuredClear.fixupProgram_residue _ _ _ _ _ _ _ _

theorem deferTail_support {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hk : SiteKind site)
    (gd : List (ClearPort n)) (S : List Wire)
    (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low i ∈ S)
    (hhigh : B.high ⊆ S) (hpaths : B.paths ⊆ S) (hroot : windowRoot ∈ S) (hbits : B.bits ⊆ S)
    (hgd : gd.map ClearPort.target ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ site.arithmetic → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ site.arithmetic → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (deferTail B site gd start) ⊆ S := by
  obtain ⟨-,-,-,hmem,hsm,-,-⟩ := kind_facts site hk
  rw [support_agrees, deferTail, MeasuredClear.static_cast]
  apply MeasuredClear.measureThen_within _ S _ _ _ _ hgd
  intro cursor grefs
  rw [MeasuredClear.static_cast, ← support_agrees, straightWires_append]
  refine List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
    (normalized_lit_support _ S hlit) (normalized_look_support _ S hlook) _, ?_⟩
  rw [support_agrees, fusedFix, MeasuredClear.static_cast]
  apply MeasuredClear.measureThen_within _ S _ _ _ _ (by rw [clearData_targets]; exact hS)
  intro c rs
  rw [MeasuredClear.static_cast]
  apply MeasuredClear.fixupProgram_within _ _ _ _ _ _ _ _ S hgS (hS hsm) hlow
    (fun i => hS (hmem i)) _ (fun w hw => hpaths (hB.sub w hw))
  intro w hw
  apply hhigh
  rw [← hB.index]
  exact List.mem_dedup.mpr hw

end
end ShorECDLP.Entrant.WEXFast.Defer

/-! ### Fused narrow fast sites -/

section
namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open AndGadget WEXCredit
open MeasuredClear (ClearPort)
open WideBank8 (GuardKept)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace FastSite
variable {n : Nat} (f : FastSite n)

def fusedRecords : Nat :=
  codeRecords selBits selPaths windowRoot f.selCode + 0 + (f.garbPorts.length + Defer.tailRec bank15 f.site)

def fusedProgram (start : Nat) : Straight n start (start + f.fusedRecords) :=
  castFinish (by simp only [fusedRecords, clearData, List.length_map]; omega)
    (((f.selProgram start).append
      (f.swapProgram (start + codeRecords selBits selPaths windowRoot f.selCode))).append
      (Defer.deferTail bank15 f.site (clearData f.garbPorts)
        (start + codeRecords selBits selPaths windowRoot f.selCode + 0)))

def fusedSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  ((source read selBits selPaths windowRoot f.selCode).seq (literalSource f.swapNet)).seq
    (Defer.deferSource bank15 read f.site (clearData f.garbPorts))

theorem fusedProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).run = (f.fusedSource read).run := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_run_fixed _ _ _ _ _ (fun h => Defer.deferTail_run bank15 read f.site _ _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
    compile_run]
  simp only [fusedSource, AdaptiveCircuit.run_seq]

theorem load_garb (read : ConstantBit n → Bool) (hg : FastGeometry f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st)
    ∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.site.guard && decide (read (q.ref a) = q.value)) := by
  intro s₂
  obtain ⟨hp, frame, T, G1, G2, G3⟩ := load_state f read hg a st hs hc
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  simp only [garbPorts, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G1 i hi hgi
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G2 i hi hgi
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G3 i hi hgi

theorem fused_simulation (read : ConstantBit n → Bool) (hg : FastGeometry f) (hk : GuardKept f.site) :
    ∃ cs : List ℂ, List.Forall₂ (f.FastSim read) (f.fusedSource read).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := swap_simulation f read hg
  obtain ⟨c2, a2, m2⟩ := Defer.tail_sim read bank15 bank15_ok f.site hg.site hk (clearData f.garbPorts)
    (by rw [clearData_targets, garbPorts_targets f hg]; exact garb_nodup f hg)
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [fusedSource, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₂⟩ := h₂
    refine ⟨m, by simpa [MaskedSite.code, MaskedSite.prefix, literalRecords] using hm, ?_⟩
    intro a st hs hc hun
    have hgarb := load_garb f read hg a st hs hc
    have heq := load_clear_eq f read hg a st hs hc
    have hph := (load_state f read hg a st hs hc).1
    dsimp only at hgarb heq hph
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ a st hs hc, map_smul, h₂ a st _ hs hun hgarb hph
      (by rw [clearData_targets, garbPorts_targets f hg]; exact heq), smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

def fusedTP : Nat :=
  8191 + ECDSAAdd.toffoliCount f.swapNet +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 32767) + 375

theorem fused_tCount (read : ConstantBit n → Bool) (hg : FastGeometry f) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).tCount = 7 * f.fusedTP := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_tCount_fixed _ _ _ _ _ (fun h => Defer.deferTail_tCount read bank15 f.site _ (site_layout_bank f hg)
      (arith_layouts f hg) _ h),
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read selBits selPaths windowRoot _ (sel_layouts f hg), traversals_normalize, bank_tree_nodes]
  simp only [fusedTP, FastSite.selCode, literalToffolis, traversals, selBits, bank15, windowBits, List.length_range']
  norm_num
  try ring

theorem fused_tp_relation (hg : FastGeometry f) :
    f.fusedTP + (24576 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have h := f.fast_tp_relation hg
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  simp only [fastTP, fusedTP] at h ⊢
  omega

theorem fused_records_relation (hg : FastGeometry f) :
    f.fusedRecords + (24576 - f.garb.length) = blockRecP2 bank15 (.unit (siteUnit f.site)) := by
  have hsel := sel_records f hg
  have hgl := garbPorts_length f hg
  have hlen := garb_length f hg
  have hpl := (facts f hg).2.2.2.1
  have hcr := (MeasuredClear.recordUnary_counts _ _ _ (site_layout_bank f hg) 0).1
  rw [bank_tree_nodes] at hcr
  have hcr' : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) f.site.guard bankHp) = 255 := hcr
  have hpre := codeRecords_eq _ _ _ _ (prefix_layouts f hg)
  have hari := codeRecords_eq _ _ _ _ (arith_layouts f hg)
  have hlr : literalRecords (normalizeW f.site.prefix) = literalRecords (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalRecords_append, (lookup_records_bank _ _).1, Nat.zero_add]
  have htr : traversals (normalizeW f.site.prefix) = traversals (normalizeW f.site.arithmetic) + 1 := by
    rw [prefix_split, normalize_append, traversals_append, (lookup_records_bank _ _).2]
    omega
  have hb : 2 ^ windowBits.length - 1 = 32767 := by simp [windowBits]
  simp only [blockRecP2, siteUnit, FastSite.fusedRecords, Defer.tailRec, Defer.fuseRec, hsel, hgl, hcr, hcr', hpre, hari, hlr, htr, hb]
  simp only [show bank15.bits = windowBits from rfl, show bank15.paths = pathBank from rfl, hb] at hpre hari ⊢
  omega

theorem fused_slots (hg : FastGeometry f) (start : Nat) :
    (f.fusedProgram start).gateSlots ≤ blockSP2 bank15 (.unit (siteUnit f.site)) + f.fastSlack := by
  rw [fusedProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append]
  rw [Defer.deferTail_slots bank15 f.site _ (site_layout_bank f hg) (arith_layouts f hg), swapProgram,
    literalFixed_slots, selProgram, compile_slots _ _ _ _ (sel_layouts f hg), sel_slots f hg]
  have hsw := literal_slot_bound (n := n) f.swapNet
  have hd : (clearData f.garbPorts).length = f.garb.length := by
    rw [clearData, List.length_map, garbPorts_length f hg]
  have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
      (32768 * f.site.ports.length + 327670) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, old_slots_append, lookup_slots]
  simp only [blockSP2, siteUnit, fastSlack, show bank15.bits = windowBits from rfl, hpre, hd, bank_tree_leaves,
    bank_tree_nodes]
  omega

theorem fused_wellFormed (hg : FastGeometry f) (hp : ∀ p, WInstr.literal p ∈ f.site.code → GatePhysical p)
    (start : Nat) : (f.fusedProgram start).WellFormed := by
  rw [fusedProgram, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (straight_append_wellFormed _ _ ?_ ?_) ?_
  · exact pair_compile_wellFormed _ _ _ _ (by decide)
      (fun i hi => by
        simp only [FastSite.selCode, List.mem_singleton] at hi
        subst hi
        exact placed_implies_pair _ _ _ _ (sel_placed f hg))
      (fun p hp => by simp [FastSite.selCode] at hp) start
  · exact literalFixed_wellFormed _ _ _ (f.swapNet_valid hg) _
  · exact Defer.deferTail_wellFormed bank15 bank15_ok f.site hg.site _
      (fun p hm => hp p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

theorem fused_residue (start : Nat) : residue (f.fusedProgram start) = 0 := by
  rw [fusedProgram, residue_cast]
  simp only [residue_append]
  rw [selProgram, compile_residue, swapProgram, literalFixed, residue_naive_cast, literal_residue,
    Defer.deferTail_residue]

theorem fused_support_new (hg : FastGeometry f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ newSourceH.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ newSourceH) ∧ portTargets ps ⊆ newSourceH)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3)
    (start : Nat) : ChallengeMigration.straightWires (f.fusedProgram start) ⊆ newSourceH := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fusedProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine compile_support selBits selPaths windowRoot f.selCode newSourceH root_new selBits_new selPaths_new
      (fun p hp => by simp [FastSite.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ newSourceH ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | rfl | h
    · exact bits_new (by simp [windowBits])
    · exact bits_new (by simp [windowBits])
    · exact hreg _ h
  · exact Defer.deferTail_support bank15 bank15_ok f.site hg.site.kind _ newSourceH hlast.2
      (hlast.1 _ (Option.mem_def.mpr rfl)) low_new high_new bank_new root_new bits_new
      (by rw [clearData_targets, garbPorts_targets f hg]; exact fun w hw => hreg w (List.mem_append_right _ hw))
      (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
      (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

def fusedRecords : Nat :=
  codeRecords selBits1 selPaths1 windowRoot f.selCode + 0 + (f.garbPorts.length + Defer.tailRec bank15 f.site)

def fusedProgram (start : Nat) : Straight n start (start + f.fusedRecords) :=
  castFinish (by simp only [fusedRecords, clearData, List.length_map]; omega)
    (((f.selProgram start).append
      (f.swapProgram (start + codeRecords selBits1 selPaths1 windowRoot f.selCode))).append
      (Defer.deferTail bank15 f.site (clearData f.garbPorts)
        (start + codeRecords selBits1 selPaths1 windowRoot f.selCode + 0)))

def fusedSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  ((source read selBits1 selPaths1 windowRoot f.selCode).seq (literalSource f.swapNet)).seq
    (Defer.deferSource bank15 read f.site (clearData f.garbPorts))

theorem fusedProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).run = (f.fusedSource read).run := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_run_fixed _ _ _ _ _ (fun h => Defer.deferTail_run bank15 read f.site _ _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
    compile_run]
  simp only [fusedSource, AdaptiveCircuit.run_seq]

theorem load_garb (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st)
    ∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.site.guard && decide (read (q.ref a) = q.value)) := by
  intro s₂
  obtain ⟨hp, frame, T, G1⟩ := load_state f read hg a st hs hc
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
  exact G1 i hi hgi

theorem fused_simulation (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (hk : GuardKept f.site) :
    ∃ cs : List ℂ, List.Forall₂ (f.FastSim read) (f.fusedSource read).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := swap_simulation f read hg
  obtain ⟨c2, a2, m2⟩ := Defer.tail_sim read bank15 bank15_ok f.site hg.site hk (clearData f.garbPorts)
    (by rw [clearData_targets, garbPorts_targets f hg]; exact garb_nodup f hg)
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [fusedSource, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₂⟩ := h₂
    refine ⟨m, by simpa [MaskedSite.code, MaskedSite.prefix, literalRecords] using hm, ?_⟩
    intro a st hs hc hun
    have hgarb := load_garb f read hg a st hs hc
    have heq := load_clear_eq f read hg a st hs hc
    have hph := (load_state f read hg a st hs hc).1
    dsimp only at hgarb heq hph
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ a st hs hc, map_smul, h₂ a st _ hs hun hgarb hph
      (by rw [clearData_targets, garbPorts_targets f hg]; exact heq), smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

def fusedTP : Nat :=
  16383 + ECDSAAdd.toffoliCount f.swapNet +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 32767) + 375

theorem fused_tCount (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).tCount = 7 * f.fusedTP := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_tCount_fixed _ _ _ _ _ (fun h => Defer.deferTail_tCount read bank15 f.site _ (site_layout_bank f hg)
      (arith_layouts f hg) _ h),
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read selBits1 selPaths1 windowRoot _ (sel_layouts f hg), traversals_normalize, bank_tree_nodes]
  simp only [fusedTP, FastSite1.selCode, literalToffolis, traversals, selBits1, bank15, windowBits, List.length_range']
  norm_num
  try ring

theorem fused_tp_relation (hg : FastGeometry1 f) :
    f.fusedTP + (16384 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have h := f.fast_tp_relation hg
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  simp only [fastTP, fusedTP] at h ⊢
  omega

theorem fused_records_relation (hg : FastGeometry1 f) :
    f.fusedRecords + (16384 - f.garb.length) = blockRecP2 bank15 (.unit (siteUnit f.site)) := by
  have hsel := sel_records f hg
  have hgl := garbPorts_length f hg
  have hlen := garb_length f hg
  have hpl := (facts f hg).2.2.2.1
  have hcr := (MeasuredClear.recordUnary_counts _ _ _ (site_layout_bank f hg) 0).1
  rw [bank_tree_nodes] at hcr
  have hcr' : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) f.site.guard bankHp) = 255 := hcr
  have hpre := codeRecords_eq _ _ _ _ (prefix_layouts f hg)
  have hari := codeRecords_eq _ _ _ _ (arith_layouts f hg)
  have hlr : literalRecords (normalizeW f.site.prefix) = literalRecords (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalRecords_append, (lookup_records_bank _ _).1, Nat.zero_add]
  have htr : traversals (normalizeW f.site.prefix) = traversals (normalizeW f.site.arithmetic) + 1 := by
    rw [prefix_split, normalize_append, traversals_append, (lookup_records_bank _ _).2]
    omega
  have hb : 2 ^ windowBits.length - 1 = 32767 := by simp [windowBits]
  simp only [blockRecP2, siteUnit, FastSite1.fusedRecords, Defer.tailRec, Defer.fuseRec, hsel, hgl, hcr, hcr', hpre, hari, hlr, htr, hb]
  simp only [show bank15.bits = windowBits from rfl, show bank15.paths = pathBank from rfl, hb] at hpre hari ⊢
  omega

theorem fused_slots (hg : FastGeometry1 f) (start : Nat) :
    (f.fusedProgram start).gateSlots ≤ blockSP2 bank15 (.unit (siteUnit f.site)) + f.fastSlack := by
  rw [fusedProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append]
  rw [Defer.deferTail_slots bank15 f.site _ (site_layout_bank f hg) (arith_layouts f hg), swapProgram,
    literalFixed_slots, selProgram, compile_slots _ _ _ _ (sel_layouts f hg), sel_slots f hg]
  have hsw := literal_slot_bound (n := n) f.swapNet
  have hd : (clearData f.garbPorts).length = f.garb.length := by
    rw [clearData, List.length_map, garbPorts_length f hg]
  have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
      (32768 * f.site.ports.length + 327670) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, old_slots_append, FastSite.lookup_slots]
  simp only [blockSP2, siteUnit, fastSlack, show bank15.bits = windowBits from rfl, hpre, hd, bank_tree_leaves,
    bank_tree_nodes]
  omega

theorem fused_wellFormed (hg : FastGeometry1 f) (hp : ∀ p, WInstr.literal p ∈ f.site.code → GatePhysical p)
    (start : Nat) : (f.fusedProgram start).WellFormed := by
  rw [fusedProgram, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (straight_append_wellFormed _ _ ?_ ?_) ?_
  · exact pair_compile_wellFormed _ _ _ _ (by decide)
      (fun i hi => by
        simp only [FastSite1.selCode, List.mem_singleton] at hi
        subst hi
        exact placed_implies_pair _ _ _ _ (sel_placed f hg))
      (fun p hp => by simp [FastSite1.selCode] at hp) start
  · exact literalFixed_wellFormed _ _ _ (f.swapNet_valid hg) _
  · exact Defer.deferTail_wellFormed bank15 bank15_ok f.site hg.site _
      (fun p hm => hp p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

theorem fused_residue (start : Nat) : residue (f.fusedProgram start) = 0 := by
  rw [fusedProgram, residue_cast]
  simp only [residue_append]
  rw [selProgram, compile_residue, swapProgram, literalFixed, residue_naive_cast, literal_residue,
    Defer.deferTail_residue]

theorem fused_support_new (hg : FastGeometry1 f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ newSourceH.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ newSourceH) ∧ portTargets ps ⊆ newSourceH)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3)
    (start : Nat) : ChallengeMigration.straightWires (f.fusedProgram start) ⊆ newSourceH := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fusedProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine compile_support selBits1 selPaths1 windowRoot f.selCode newSourceH root_new selBits1_new selPaths1_new
      (fun p hp => by simp [FastSite1.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite1.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ newSourceH ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact bits_new (by simp [windowBits])
    · exact hreg _ h
  · exact Defer.deferTail_support bank15 bank15_ok f.site hg.site.kind _ newSourceH hlast.2
      (hlast.1 _ (Option.mem_def.mpr rfl)) low_new high_new bank_new root_new bits_new
      (by rw [clearData_targets, garbPorts_targets f hg]; exact fun w hw => hreg w (List.mem_append_right _ hw))
      (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
      (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

end FastSite1

end
end ShorECDLP.Entrant.WEXFast
end

/-! ### Narrow rows with fused fast sites -/

section
namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open WideBank8 (GuardKept)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

def gblockRec {n} : FBlock2 n → Nat
  | .std b => blockRecP2 bank15 b
  | .fast f => f.fusedRecords
  | .fast1 f => f.fusedRecords

def gblockProg {n} : (b : FBlock2 n) → (start : Nat) → Straight n start (start + gblockRec b)
  | .std b, start => blockProgH bank15 b start
  | .fast f, start => f.fusedProgram start
  | .fast1 f, start => f.fusedProgram start

def grecs {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockRec b + grecs code

def gprog {n} : (code : FCode2 n) → (start : Nat) → Straight n start (start + grecs code)
  | [], _ => .done
  | b :: code, start => castFinish (by simp [grecs]; omega)
      ((gblockProg b start).append (gprog code (start + gblockRec b)))

def gblockSrc {n} (read : ConstantBit n → Bool) : FBlock2 n → AdaptiveCircuit
  | .std b => blockSourceH bank15 read b
  | .fast f => f.fusedSource read
  | .fast1 f => f.fusedSource read

def gsrc {n} (read : ConstantBit n → Bool) : FCode2 n → AdaptiveCircuit
  | [] => .done
  | b :: code => (gblockSrc read b).seq (gsrc read code)

theorem gblockProg_run {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (start : Nat)
    (history : Fin start → Bool) :
    ((gblockProg b start).instantiate read history).run = (gblockSrc read b).run := by
  cases b with
  | std b => exact blockProgH_run bank15 read b start history
  | fast f => exact f.fusedProgram_run read start history
  | fast1 f => exact f.fusedProgram_run read start history

theorem gprog_run {n} (read : ConstantBit n → Bool) (code : FCode2 n) (start : Nat)
    (history : Fin start → Bool) :
    ((gprog code start).instantiate read history).run = (gsrc read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [gprog, castFinish_instantiate, append_run_fixed _ _ _ _ _ (ih _), AdaptiveCircuit.run_seq, gblockProg_run]
    simp only [gsrc, AdaptiveCircuit.run_seq]

/-- Fused blocks additionally need the guard to survive the site arithmetic. -/
def GBlockGeo {n} : FBlock2 n → Prop
  | .std b => BlockGeoP2 bank15 b
  | .fast f => FastGeometry f ∧ GuardKept f.site
  | .fast1 f => FastGeometry1 f ∧ GuardKept f.site

theorem gblock_geo {n} (b : FBlock2 n) (hg : GBlockGeo b) : FBlockGeo b := by
  cases b with
  | std b => exact hg
  | fast f => exact hg.1
  | fast1 f => exact hg.1

theorem gblock_sim {n} (read : ConstantBit n → Bool) (block : FBlock2 n) (hg : GBlockGeo block) :
    ∃ cs : List ℂ, List.Forall₂ (FBlockSim read block) (gblockSrc read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | std b =>
    obtain ⟨cs, al, mass⟩ := block_simulationH read bank15 bank15_ok b hg
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    exact ⟨m, hm, fun a st hs hc hsafe => h a st hs hc.1 hc.2 hsafe⟩
  | fast f =>
    obtain ⟨cs, al, mass⟩ := f.fused_simulation read hg.1 hg.2
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    refine ⟨m, hm, fun a st hs hc hsafe => ?_⟩
    exact h a st ⟨hc.1, hs.1, hs.2⟩ hc.2 hsafe
  | fast1 f =>
    obtain ⟨cs, al, mass⟩ := f.fused_simulation read hg.1 hg.2
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    refine ⟨m, hm, fun a st hs hc hsafe => ?_⟩
    exact h a st ⟨hc.1, hs.1, hs.2⟩ hc.2 hsafe

theorem gsrc_sim {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b) :
    ∃ cs : List ℂ, List.Forall₂ (FSim read code) (gsrc read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    exact ⟨[], rfl, fun a st _ _ _ => by
      simp [reference2, erase2, fforget, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁, h₁, mass₁⟩ := gblock_sim read b (hg b (by simp))
    obtain ⟨cs₂, h₂, mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    refine ⟨coherentSeqCoefficients cs₁ cs₂, ?_, ?_⟩
    · rw [gsrc, AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁, len₁, run₁⟩ := hb₁
      obtain ⟨m₂, len₂, run₂⟩ := hb₂
      refine ⟨m₁ ++ m₂, ?_, ?_⟩
      · simp [fforget_cons, erase2, List.length_append, len₁, len₂]
      · intro a st hs hc hsafe
        rw [fforget_cons] at hsafe ⊢
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a b.forget) :=
          len₁.trans (specialize_counts read b.forget.code a).2.symm
        have hn := fblock_addr read b (gblock_geo b (hg b (by simp))) a st hs hc.1 m₁
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hc.1 hsafe.1, map_smul,
          run₂ a (ECDSAAdd.run (blockReference2 read a b.forget) m₁ st) hn (hc.2 m₁ hm) (hsafe.2 m₁ hm),
          reference2_cons, run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass, mass₁, mass₂]
      norm_num

theorem gprog_coherent {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue windowBits s) (fforget code) ⟨false,s⟩)
    (hclean : ∀ s, Valid s → FCodeClean read (tableAddressValue windowBits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue windowBits s) (fforget code)) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((gprog code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := gsrc_sim read code hg
  refine ⟨cs, ?_, mass⟩
  rw [gprog_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨rfl, hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [Bridge.signedKet_false, hrun s hs.2 m, Bridge.signedKet_false] at he
  simpa [ket] using he

def gblockTP {n} : FBlock2 n → Nat
  | .std b => blockTP2 bank15 b
  | .fast f => f.fusedTP
  | .fast1 f => f.fusedTP

def gcodeTP {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockTP b + gcodeTP code

def gblockSave {n} : FBlock2 n → Nat
  | .std _ => 0
  | .fast f => 24576 - ECDSAAdd.toffoliCount f.swapNet
  | .fast1 f => 16384 - ECDSAAdd.toffoliCount f.swapNet

def gsave {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockSave b + gsave code

def gblockRSave {n} : FBlock2 n → Nat
  | .std _ => 0
  | .fast f => 24576 - f.garb.length
  | .fast1 f => 16384 - f.garb.length

def grsave {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockRSave b + grsave code

theorem gblock_tCount {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (hg : GBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((gblockProg b start).instantiate read history).tCount = 7 * gblockTP b := by
  cases b with
  | std b => exact blockH_tCount read bank15 b (geo_lay2 bank15 bank15_ok b hg) start history
  | fast f => exact f.fused_tCount read hg.1 start history
  | fast1 f => exact f.fused_tCount read hg.1 start history

theorem gprog_tCount {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((gprog code start).instantiate read history).tCount = 7 * gcodeTP code := by
  induction code generalizing start with
  | nil => simp [gprog, grecs, gcodeTP, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [gprog, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      gblock_tCount read b (hg b (by simp))]
    simp only [gcodeTP]; ring

theorem gcodeTP_relation {n} (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b) :
    gcodeTP code + gsave code = codeTP2 bank15 (fforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : gblockTP b + gblockSave b = blockTP2 bank15 b.forget := by
      have hgb := hg b (by simp)
      cases b with
      | std b => simp [gblockTP, gblockSave, FBlock2.forget]
      | fast f => exact f.fused_tp_relation hgb.1
      | fast1 f => exact f.fused_tp_relation hgb.1
    simp only [gcodeTP, gsave, fforget_cons, codeTP2]
    omega

theorem grecs_relation {n} (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b) :
    grecs code + grsave code = recordsP2 bank15 (fforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : gblockRec b + gblockRSave b = blockRecP2 bank15 b.forget := by
      have hgb := hg b (by simp)
      cases b with
      | std b => simp [gblockRec, gblockRSave, FBlock2.forget]
      | fast f => exact f.fused_records_relation hgb.1
      | fast1 f => exact f.fused_records_relation hgb.1
    simp only [grecs, grsave, fforget_cons, recordsP2]
    omega

theorem gprog_slots {n} (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b) (start : Nat) :
    (gprog code start).gateSlots ≤ codeSP2 bank15 (fforget code) + fslack code := by
  induction code generalizing start with
  | nil => simp [gprog, grecs, fslack, Straight.gateSlots, codeSP2]
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd])) (start + gblockRec b)
    have hb : (gblockProg b start).gateSlots ≤ blockSP2 bank15 b.forget + fblockSlack b := by
      have hgb := hg b (by simp)
      cases b with
      | std b =>
        rw [show gblockProg (.std b) start = blockProgH bank15 b start from rfl]
        exact blockH_slots bank15 b (geo_lay2 bank15 bank15_ok b hgb) start
      | fast f => exact f.fused_slots hgb.1 start
      | fast1 f => exact f.fused_slots hgb.1 start
    rw [gprog, castFinish_gateSlots, Straight.gateSlots_append]
    simp only [fforget_cons, codeSP2, fslack]
    omega

theorem gblock_wellFormed {n} (b : FBlock2 n) (hg : GBlockGeo b)
    (hp : ∀ p, WInstr.literal p ∈ b.forget.code → GatePhysical p) (start : Nat) :
    (gblockProg b start).WellFormed := by
  cases b with
  | std b =>
    show (blockProgH bank15 b start).WellFormed
    exact blockH_wellFormed bank15 bank15_ok b hg hp start
  | fast f =>
    exact f.fused_wellFormed hg.1 (fun p hm => hp p (by simpa [FBlock2.forget, siteUnit_code] using hm)) start
  | fast1 f =>
    exact f.fused_wellFormed hg.1 (fun p hm => hp p (by simpa [FBlock2.forget, siteUnit_code] using hm)) start

theorem gprog_wellFormed {n} (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → GatePhysical p) (start : Nat) :
    (gprog code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons b code ih =>
    rw [gprog, castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact gblock_wellFormed b (hg b (by simp)) (fun p hm => hp p (by simp [erase2_cons, hm])) start
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase2_cons, hm])) _

theorem gprog_residue {n} (code : FCode2 n) (start : Nat) : AndGadget.residue (gprog code start) = 0 := by
  induction code generalizing start with
  | nil => simp [gprog, grecs]
  | cons b code ih =>
    have hb : AndGadget.residue (gblockProg b start) = 0 := by
      cases b with
      | std b => exact blockH_residue bank15 b start
      | fast f => exact f.fused_residue start
      | fast1 f => exact f.fused_residue start
    simp [gprog, AndGadget.residue_cast, AndGadget.residue_append, hb, ih]

end
end ShorECDLP.Entrant.WEXFast
end

section
namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.ShorPort ECDSAAdd.Entrant
open WideBank8 (GuardKept)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

theorem gblock_support (b : FBlock2 32768) (hg : GBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ b.forget.code → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ newSourceH)
    (hstrict : ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ c, b = .std (.plain c) → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ b.forget.code → (∀ q ∈ c, q ∈ newSourceH) ∧ portTargets ps ⊆ newSourceH)
    (hgarb : FNoHost b)
    (start : Nat) : ChallengeMigration.straightWires (gblockProg b start) ⊆ newSourceH := by
  have strict : (∀ c, b ≠ .std (.plain c)) → ∀ p, WInstr.literal p ∈ b.forget.code →
      ECDSAAdd.wires p ⊆ newSourceH.toFinset := by
    intro hb p hp w hw
    rcases hlit p hp w hw with e | e | e | e
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inl (e ▸ hw))
      exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inl (e ▸ hw)))
      exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (e ▸ hw)))
      exact absurd hc (hb c)
    · exact List.mem_toFinset.mpr e
  cases b with
  | std b => exact fblock_support (.std b) hg hlit hstrict hctl hctl3 hlook hgarb start
  | fast f =>
    exact f.fused_support_new hg.1
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start
  | fast1 f =>
    exact f.fused_support_new hg.1
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start

theorem gprog_support (code : FCode2 32768) (hg : ∀ b ∈ code, GBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ newSourceH)
    (hstrict : ∀ b ∈ code, ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget code) →
      (∀ q ∈ c, q ∈ newSourceH) ∧ portTargets ps ⊆ newSourceH)
    (hgarb : ∀ b ∈ code, FNoHost b)
    (start : Nat) : ChallengeMigration.straightWires (gprog code start) ⊆ newSourceH := by
  induction code generalizing start with
  | nil => simp [gprog, grecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    rw [gprog, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨gblock_support b (hg b (by simp))
      (fun p hm => hlit p (by simp [erase2_cons, hm])) (hstrict b (by simp)) (hctl b (by simp)) (hctl3 b (by simp))
      (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (hgarb b (by simp)) start,
      ih (fun d hd => hg d (by simp [hd])) (fun p hm => hlit p (by simp [erase2_cons, hm]))
        (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd])) (fun d hd => hctl3 d (by simp [hd]))
        (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (fun d hd => hgarb d (by simp [hd])) _⟩

theorem rowCF_ggeo : ∀ b ∈ rowCF, GBlockGeo b := by
  intro b hb
  have h := rowCF_geo b hb
  cases b with
  | std c => exact h
  | fast f => exact ⟨h, by rw [fast_mem_rowCF f hb]; exact WideBank8.triple_guardKept⟩
  | fast1 f => exact ⟨h, by rw [fast1_mem_rowCF f hb]; exact WideBank8.site2_guardKept⟩

end
end ShorECDLP.Entrant.WEXFast
end

/-! ### The narrow body with fused fast sites -/

namespace ShorECDLP.Entrant.WEXFast.W15G
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup WEXFast
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem gsave_append (x y : FCode2 32768) : gsave (x ++ y) = gsave x + gsave y := by
  induction x with
  | nil => simp [gsave]
  | cons b xs ih => simp [gsave, ih, Nat.add_assoc]
theorem grsave_append (x y : FCode2 32768) : grsave (x ++ y) = grsave x + grsave y := by
  induction x with
  | nil => simp [grsave]
  | cons b xs ih => simp [grsave, ih, Nat.add_assoc]
theorem gsave_std (code : Code2 32768) : gsave (code.map FBlock2.std) = 0 := by
  induction code with
  | nil => rfl
  | cons b code ih => simp [gsave, gblockSave, ih]
theorem grsave_std (code : Code2 32768) : grsave (code.map FBlock2.std) = 0 := by
  induction code with
  | nil => rfl
  | cons b code ih => simp [grsave, gblockRSave, ih]

theorem rowCF_gsave : gsave rowCF = 39680 := by
  have h := tripleF.swapNet_toff tripleF_geometry
  rw [show tripleF.site = tripleSite from rfl, tripleSite_length] at h
  have h1 := site2F.swapNet_toff site2F_geometry
  rw [show site2F.site.ports = site2Ports probeRows from rfl, site2Ports_length] at h1
  rw [rowCF, gsave_append, gsave_append, gsave_std, gsave_std]
  simp only [fgeneric3, gsave, gblockSave, h, h1]

theorem rowCF_grsave : grsave rowCF = 39680 := by
  rw [rowCF, grsave_append, grsave_append, grsave_std, grsave_std]
  simp only [fgeneric3, grsave, gblockRSave, tripleF_garb_length, site2F_garb_length]

theorem rowCF_gtp : gcodeTP rowCF + 39680 = ccx2 WEXUnlookup.rowC := by
  have h := gcodeTP_relation rowCF rowCF_ggeo
  rw [rowCF_gsave, fforget_rowCF, W15C.codeTP2_15] at h
  exact h

theorem sub_arith (x : Nat) (h : x + 39680 = 1692440) : x = 1652760 := by omega

theorem rowCF_grecords : grecs rowCF = 1652760 := by
  have h := grecs_relation rowCF rowCF_ggeo
  rw [rowCF_grsave, fforget_rowCF, W15C.rowC_recordsP] at h
  exact sub_arith _ h

theorem rowCF_gslots (start : Nat) : (gprog rowCF start).gateSlots ≤
    codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 418411946 := by
  have h := gprog_slots rowCF rowCF_ggeo start
  rw [fforget_rowCF, ShorECDLP.Entrant.WEXFast.W15F.rowC_slotsP start, ShorECDLP.Entrant.WEXFast.W15F.rowCF_slack] at h
  exact ShorECDLP.Entrant.WEXFast.W15F.slots_arith _ _ h

attribute [local irreducible] gprog gblockProg blockProgP2 clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx2 gcodeTP Nat.add Nat.mul

def addFixedCG (start : Nat) : Straight 32768 start (start+1652760) :=
  castFinish (congrArg (fun m => start+m) rowCF_grecords) (gprog rowCF start)

theorem addFixedCG_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedCG start).instantiate read history).run = (gsrc read rowCF).run := by
  rw [addFixedCG, castFinish_instantiate, gprog_run]

theorem addFixedCG_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedCG start).instantiate read history).tCount = 7 * gcodeTP rowCF := by
  rw [addFixedCG, castFinish_instantiate, gprog_tCount read rowCF rowCF_ggeo]

theorem addFixedCG_slots (start : Nat) : (addFixedCG start).gateSlots ≤
    codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 418411946 := by
  rw [addFixedCG, castFinish_gateSlots]
  exact rowCF_gslots start

theorem addFixedCG_wellFormed (start : Nat) : (addFixedCG start).WellFormed := by
  rw [addFixedCG, castFinish_wellFormed]
  exact gprog_wellFormed rowCF rowCF_ggeo (by rw [fforget_rowCF]; exact WEXUnlookup.rowC_physical) start

theorem addFixedCG_residue (start : Nat) : residue (addFixedCG start) = 0 := by
  rw [addFixedCG, residue_cast]
  exact gprog_residue rowCF start

theorem addFixedCG_credit (start : Nat) : ProgramCredit (addFixedCG start) (gcodeTP rowCF) := by
  have hz := addFixedCG_residue start
  refine ⟨hz, ?_⟩
  have he := exact_t (addFixedCG start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedCG_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixedCG_support (start : Nat) : ChallengeMigration.straightWires (addFixedCG start) ⊆ newSourceH := by
  rw [addFixedCG, support_cast]
  exact gprog_support rowCF rowCF_ggeo (by rw [fforget_rowCF]; exact rowC_lit_relaxed) ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict ShorECDLP.Entrant.WEXFast.W15F.rowCF_ctl
    ShorECDLP.Entrant.WEXFast.W15F.rowCF_ctl3 (by rw [fforget_rowCF]; exact rowC_look_newH) ShorECDLP.Entrant.WEXFast.W15F.rowCF_nohost start

def rowSourceCG (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  gsrc (readConstant coeffs Q) rowCF

theorem rowSourceCG_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSourceCG coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := gprog_coherent (readConstant coeffs Q) rowCF rowCF_ggeo liveReady (rowPointState coeffs Q)
    (fun s hs => by rw [fforget_rowCF]; exact (WEXUnlookup.rowC_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => rowCF_clean coeffs Q hQ hn _ s hs)
    (fun s hs m => by rw [fforget_rowCF]; exact WEXUnlookup.rowC_run_any _ coeffs Q hQ hn s hs m) 0 Fin.elim0
  obtain ⟨cs, aligned, mass⟩ := h
  refine ⟨cs, ?_, mass⟩
  rw [gprog_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceCG coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceCG_coherent coeffs Q hQ hn)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1), prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1653272) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedCG (start+256))).append
      (nFastProgram (start+256+1652760))).append (suffixProgram (start+256+1652760+256)))

attribute [local irreducible] fastBodyProgram addFixedCG

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (gsrc (readConstant coeffs Q) rowCF)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram, castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (gsrc (readConstant coeffs Q) rowCF) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedCG_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (gsrc (readConstant coeffs Q) rowCF)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceCG
    rfl
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs, aligned, mass⟩ := fastBodySource_coherent coeffs Q hQ hn
  refine ⟨cs, ?_, mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
      gcodeTP rowCF) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1652760)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (gcodeTP rowCF) (prefix_credit start) hl (addFixedCG_credit (start+256)) hr
    (suffix_credit (start+256+1652760+256))

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram, castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixedCG_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ newSourceH := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ newSourceH := by
    rw [prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    apply newSourceH_of_bounds
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ newSourceH := by
    rw [suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    apply newSourceH_of_bounds
    decide +kernel
  rw [fastBodyProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp, nFast_newH _⟩, addFixedCG_support _⟩, nFast_newH _⟩, hs _⟩

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append, nFastProgram_slots, prefixProgram, suffixProgram, literalProgram_slots]
  have ha := addFixedCG_slots (start+256)
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len, List.length_cons, List.length_nil]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (erase2 WEXUnlookup.rowC))
  rw [literalSlotSum_normalize, portTotal_normalize, traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.rowC_measures
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  generalize codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) = C at hc ha
  generalize (addFixedCG (start + 256)).gateSlots = A at ha ⊢
  generalize ECDSAAdd.Challenge.gateSlots fastWindowSignProgram = G at sign bound
  generalize Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) = S
    at sign ⊢
  exact ShorECDLP.Entrant.WEXFast.W15F.body_slot_arith S A G C _ _ _ _ windowBits.length _ sign bound ha hc rfl hm.2.1 hm.2.2.1 hl hm.2.2.2.1 hp

def compactProgram (start : Nat) : Straight 32768 start (start+1653272) :=
  relabelStraight piH (fastBodyProgram start)

theorem count_arith (s x y : Nat) (h : s + y ≤ 2292120) (hr : x + 39680 = y) : s + x ≤ 2252440 := by omega

theorem fastCount_upper : 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    gcodeTP rowCF ≤ 2252440 := by
  exact count_arith _ _ _ Width15Corner.fastCount_upper rowCF_gtp

end
end ShorECDLP.Entrant.WEXFast.W15G
