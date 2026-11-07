import ShorECDLP.Submission.Entrant.Prefix

namespace ShorECDLP.Entrant.TightSupport
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare WideSigned WideSigned.Fast16
noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] List.ofFn WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram
def support : List Wire := PathShare.newSourceH ++ [871, 10000]
theorem old_cover : PathShare.newSourceH ⊆ support := List.subset_append_left _ _
theorem support_length : support.length = 1618 := by decide
theorem root_new : windowRoot ∈ support := by decide
theorem bits_new : WideSigned.Fast16.windowBits ⊆ support := by decide
theorem bank_new : WideSigned.Fast16.pathBank ⊆ support := by decide
theorem high_new : WideSigned.Fast16.high ⊆ support := by decide
theorem low_new (i : Fin 7) : WEXUnlookup.low i ∈ support := by
  apply old_cover
  rw [newSourceH_mem]
  have hi := i.isLt
  simp only [WEXUnlookup.low, fixedPort, oldWork, retiredH, retired]
  omega
theorem selBits_new : WideSigned.Fast16.selBits ⊆ support := by decide
theorem selBits1_new : WideSigned.Fast16.selBits1 ⊆ support := by decide
theorem selPaths_new : WideSigned.Fast16.selPaths ⊆ support := by decide
theorem selPaths1_new : WideSigned.Fast16.selPaths1 ⊆ support := by decide
theorem bankHp_new : WideSigned.Fast16.bankHp ⊆ support := by decide
theorem work_new (w : Wire) (h : 14115 ≤ w ∧ oldWork w)
    (hw : w ≠ hostWire) (hw2 : w ≠ hostWire2) (hw3 : w ≠ hostWire3) : w ∈ support := by
  apply old_cover
  rw [newSourceH_mem]
  refine ⟨Or.inr h.2, ?_⟩
  unfold retiredH retired
  dsimp only [Wire] at *
  unfold hostWire hostWire2 hostWire3 at *
  omega
theorem guard_new (g : Wire) (h : g = 14113 ∨ g = 10015) : g ∈ support := by
  rcases h with rfl | rfl <;> decide
abbrev clearP_support := @WideSigned.Bank.clearP_support

theorem gclear_new_of {n : Nat} (data : List (MeasuredClear.ClearPort n)) (hot : Fin 128 → Wire) (guard sc : Wire)
    (hdata : ∀ w ∈ data.map MeasuredClear.ClearPort.target, w ∈ support)
    (hhot : ∀ i, hot i ∈ support) (hguard : guard ∈ support)
    (hsc : sc ∈ data.map MeasuredClear.ClearPort.target) (start : Nat) :
    ChallengeMigration.straightWires (MeasuredClear.measuredClear data WEXUnlookup.low hot (tableAddressTree WideSigned.Fast16.high 0 1)
      guard sc WideSigned.Fast16.bankHp start) ⊆ support := by
  have hindex := tableAddressTree_index WideSigned.Fast16.high 0 1 (by decide +kernel)
  rw [support_agrees]
  apply List.Subset.trans (MeasuredClear.measuredClear_static _ _ _ _ _ _ _ hsc start)
  intro w hw
  simp only [MeasuredClear.clearSupport, hindex, List.mem_append, List.mem_cons, or_assoc] at hw
  rcases hw with hs | hl | hh | hr | hb | hp
  · exact hdata w hs
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact low_new i
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hh
    exact hhot i
  · rw [hr]; exact hguard
  · exact high_new hb
  · exact bankHp_new hp

namespace FastSite
open WideSigned.Fast16.FastSite
variable {n : Nat} (f : FastSite n)

theorem regs_new (hg : FastGeometry f) (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3) :
    ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ support := by
  intro w hw
  have hk : w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 := by
    rcases List.mem_append.mp hw with h | h
    · exact ⟨fun e => kind_nohost f.site hg.site.kind (e ▸ h), fun e => kind_nohost2 f.site hg.site.kind (e ▸ h), fun e => PathShare.kind_nohost3 f.site hg.site.kind (e ▸ h)⟩
    · exact hgarb w h
  exact work_new w ((facts f hg).2.2.2.2.2.2 w hw) hk.1 hk.2.1 hk.2.2

theorem fast_support_new (hg : FastGeometry f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3)
    (start : Nat) : ChallengeMigration.straightWires (f.fastProgram start) ⊆ support := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fastProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine compile_support WideSigned.Fast16.selBits WideSigned.Fast16.selPaths windowRoot f.selCode support root_new selBits_new selPaths_new
      (fun p hp => by simp [FastSite.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ support ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | rfl | h
    · exact bits_new (by simp [WideSigned.Fast16.windowBits])
    · exact bits_new (by simp [WideSigned.Fast16.windowBits])
    · exact hreg _ h
  · unfold gclearProgram
    apply gclear_new_of
    · rw [clearData_targets, garbPorts_targets f hg]
      exact fun w hw => hreg w (List.mem_append_right _ hw)
    · intro i; exact hreg _ (List.mem_append_right _ (g1_sub f _ (hg.bank i)))
    · exact hg0
    · rw [clearData_targets, garbPorts_targets f hg]; exact g1_sub f _ hg.head
  · exact compile_support _ _ _ _ support root_new bits_new bank_new
      (normalized_lit_support _ support (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))))
      (normalized_look_support _ support (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))))
      _
  · exact clearP_support WideSigned.Fast16.bank15 bank15_ok f.site hg.site.kind support hlast.2 (hlast.1 _ (Option.mem_def.mpr rfl))
      low_new high_new bank_new _

end FastSite

namespace FastSite1
open WideSigned.Fast16.FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem regs_new (hg : FastGeometry1 f) (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3) :
    ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ support := by
  intro w hw
  have hk : w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 := by
    rcases List.mem_append.mp hw with h | h
    · exact ⟨fun e => kind_nohost f.site hg.site.kind (e ▸ h), fun e => kind_nohost2 f.site hg.site.kind (e ▸ h), fun e => PathShare.kind_nohost3 f.site hg.site.kind (e ▸ h)⟩
    · exact hgarb w h
  exact work_new w ((facts f hg).2.2.2.2.2.2 w hw) hk.1 hk.2.1 hk.2.2

theorem fast_support_new (hg : FastGeometry1 f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3)
    (start : Nat) : ChallengeMigration.straightWires (f.fastProgram start) ⊆ support := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fastProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine compile_support WideSigned.Fast16.selBits1 WideSigned.Fast16.selPaths1 windowRoot f.selCode support root_new selBits1_new selPaths1_new
      (fun p hp => by simp [FastSite1.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite1.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ support ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact bits_new (by simp [WideSigned.Fast16.windowBits])
    · exact hreg _ h
  · unfold gclearProgram
    apply gclear_new_of
    · rw [clearData_targets, garbPorts_targets f hg]
      exact fun w hw => hreg w (List.mem_append_right _ hw)
    · intro i; exact hreg _ (List.mem_append_right _ (hg.bank i))
    · exact hg0
    · rw [clearData_targets, garbPorts_targets f hg]; exact hg.head
  · exact compile_support _ _ _ _ support root_new bits_new bank_new
      (normalized_lit_support _ support (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))))
      (normalized_look_support _ support (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))))
      _
  · exact clearP_support WideSigned.Fast16.bank15 bank15_ok f.site hg.site.kind support hlast.2 (hlast.1 _ (Option.mem_def.mpr rfl))
      low_new high_new bank_new _

end FastSite1



def NoHost3 {n} : FBlock2 n → Prop
  | .std _ => True
  | .fast f => ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3
  | .fast1 f => ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3
theorem ctl_newH : hostCtl ∈ support := by decide
theorem ctl3_newH : hostCtl3 ∈ support := by decide
theorem fblock_support (b : FBlock2 65536) (hg : FBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ b.forget.code → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ support)
    (hstrict : ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ c, b = .std (.plain c) → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ b.forget.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : NoHost3 b)
    (start : Nat) : ChallengeMigration.straightWires (fblockProg b start) ⊆ support := by
  have strict : (∀ c, b ≠ .std (.plain c)) → ∀ p, WInstr.literal p ∈ b.forget.code →
      ECDSAAdd.wires p ⊆ support.toFinset := by
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
  | std b =>
    cases b with
    | plain code =>
      exact plainH_support WideSigned.Fast16.bank15 code hg support root_new bits_new bank_new ctl_newH ctl3_newH
        (fun p hp w hw => hlit p hp w hw) (hctl code rfl) (hctl3 code rfl) start
    | unit u =>
      have h := WideSigned.Fast16.programP2_support WideSigned.Fast16.bank15 WideSigned.Fast16.bank15_ok (Block2.unit u :: []) (fun d hd => by
          simp only [List.mem_singleton] at hd; subst hd; exact hg) support root_new bits_new bank_new low_new high_new
        (fun p hm => strict (fun c e => by cases e) p (by simpa [erase2] using hm))
        (fun c ps hm => hlook c ps (by simpa [erase2] using hm)) start
      rw [programP2, support_cast, straightWires_append] at h
      exact fun w hw => h (List.mem_append_left _ hw)
  | fast f =>
    exact ShorECDLP.Entrant.TightSupport.FastSite.fast_support_new f hg
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start
  | fast1 f =>
    exact ShorECDLP.Entrant.TightSupport.FastSite1.fast_support_new f hg
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start

theorem fprog_support (code : FCode2 65536) (hg : ∀ b ∈ code, FBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ support)
    (hstrict : ∀ b ∈ code, ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget code) →
      (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ b ∈ code, NoHost3 b)
    (start : Nat) : ChallengeMigration.straightWires (fprog code start) ⊆ support := by
  induction code generalizing start with
  | nil => simp [fprog, frecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    rw [fprog, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨fblock_support b (hg b (by simp))
      (fun p hm => hlit p (by simp [erase2_cons, hm])) (hstrict b (by simp)) (hctl b (by simp)) (hctl3 b (by simp))
      (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (hgarb b (by simp)) start,
      ih (fun d hd => hg d (by simp [hd])) (fun p hm => hlit p (by simp [erase2_cons, hm]))
        (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd])) (fun d hd => hctl3 d (by simp [hd]))
        (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (fun d hd => hgarb d (by simp [hd])) _⟩



attribute [local irreducible] WideSigned.Row16.code WideSigned.Fast16.fprog
  Straight.instantiate AdaptiveCircuit.run

theorem row_literals (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ erase2 (WideSigned.Fast16.fforget WideSigned.Row16.code)) :
    ∀ v ∈ ECDSAAdd.wires p, v=hostWire ∨ v=hostWire2 ∨ v=hostWire3 ∨ v∈support := by
  rw [WideSigned.Row16.forget,WideSigned.Geometry.row,WideSigned.Rows.erase_blocks] at hp
  have hold := WideSigned.Row16.literal_back _ p hp
  intro v hv
  rcases PathShare.rowC_lit_relaxed p hold v hv with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (old_cover h)))

theorem row_lookups (ctl : Option Wire) (ps : List (LookupPort 65536))
    (hp : WInstr.lookup ctl ps ∈ erase2 (WideSigned.Fast16.fforget WideSigned.Row16.code)) :
    (∀ q∈ctl,q∈support) ∧ portTargets ps ⊆ support := by
  rw [WideSigned.Row16.forget,WideSigned.Geometry.row,WideSigned.Rows.erase_blocks] at hp
  obtain ⟨old,ho,rfl⟩ := WideSigned.Row16.lookup_back _ ctl ps hp
  have h := PathShare.rowC_look_newH ctl old ho
  rw [WideSigned.Rows.targets]
  exact ⟨fun q hq => old_cover (h.1 q hq),fun v hv => old_cover (h.2 hv)⟩

theorem row_nohost (b : WideSigned.Fast16.FBlock2 65536) (hb : b∈WideSigned.Row16.code) : NoHost3 b := by
  rw [WideSigned.Row16.code] at hb
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hb
  have h := WEXFast.W15F.rowCF_nohost old ho
  cases old with
  | std b => trivial
  | fast f =>
    simpa only [WideSigned.Row16.lift,WideSigned.Row16.fast,NoHost3,WEXFast.FNoHost,
      WideSigned.Fast16.FastSite.garb,WEXFast.FastSite.garb] using h
  | fast1 f =>
    simpa only [WideSigned.Row16.lift,WideSigned.Row16.fast1,NoHost3,WEXFast.FNoHost,
      WideSigned.Fast16.FastSite1.garb,WEXFast.FastSite1.garb] using h

theorem row_program_support (start : Nat) :
    straightWires (WideSigned.Row16.program start) ⊆ support := by
  exact fprog_support WideSigned.Row16.code WideSigned.Row16.geometry row_literals
    WideSigned.Row16.strict WideSigned.Row16.ctl WideSigned.Row16.ctl3 row_lookups row_nohost start

theorem fixed_program_support (start : Nat) :
    straightWires (WideSigned.Row16.fixedProgram start) ⊆ support := by
  rw [WideSigned.Row16.fixedProgram,straightWires_castFinish]
  exact row_program_support start
theorem frame_support (r : Nat) (row : (j : Nat) → Straight 65536 j (j + r))
    (hrow : ∀ j, ChallengeMigration.straightWires (row j) ⊆ support)
    (start : Nat) : ChallengeMigration.straightWires (WideSigned.Frame16.program r row start) ⊆ support := by
  have cover : newSourceH ⊆ support := old_cover
  have hs (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.nProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.nProgram, straightWires_reindex]
    exact (nFast_newH j).trans cover
  have hp (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.prefixProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  have hpost (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.suffixProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  rw [WideSigned.Frame16.program, straightWires_castFinish]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp start, hs start⟩, hrow _⟩, hs _⟩, hpost _⟩


theorem signed_support (start : Nat) :
    straightWires (WideSigned.Signed16.program start) ⊆ support := by
  rw [WideSigned.Signed16.program,straightWires_castFinish]
  exact frame_support _ WideSigned.Row16.fixedProgram fixed_program_support start

def compact : Wire ≃ Wire :=
  (PathShare.piH.trans (Equiv.swap 1619 1616)).trans (Equiv.swap 14436 1617)

theorem compact_bound (v : Wire) (hv : v∈support) : compact v < 1618 := by
  rcases List.mem_append.mp hv with h | h
  · have hp := (PathShare.piH_apply v).trans_lt (PathShare.piH_bound v h)
    simp only [compact,Equiv.trans_apply,Equiv.swap_apply_def]
    dsimp only [Wire] at hp ⊢
    split_ifs <;> omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl <;> decide

theorem compact_point (v : Wire) (hv : v∈pointLogicalWires) : compact v=v := by
  rw [compact,Equiv.trans_apply,Equiv.trans_apply,PathShare.piH_point v hv]
  have hb := point_wire_small v hv
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact_active : compact 836=836 := by decide
theorem compact_sign : compact 870=870 := by decide
theorem compact_extra : compact 871=1617 := by decide

theorem compact_address (v : Wire) (hv : v∈streamAddress) : compact v=v := by
  have hb : 855≤v ∧ v<871 := by simpa only [streamAddress,List.mem_range'_1] using hv
  have hf : fixedPort v := by unfold fixedPort; dsimp only [Wire] at *; omega
  rw [compact,Equiv.trans_apply,Equiv.trans_apply,PathShare.piH_fixed v hf]
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem packed_support (start : Nat) :
    straightWires (relabelStraight compact (WideSigned.Signed16.program start)) ⊆ List.range 1618 := by
  rw [straightWires_relabel]
  intro v hv
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (compact_bound u (signed_support start hu))
theorem compact_pointWrite (P : Point) (s : BasisState) :
    relabelBasis compact (pointWrite P s) = pointWrite P (relabelBasis compact s) := by
  funext v
  by_cases hv : v ∈ pointLogicalWires
  · have he : compact.symm v = v := (Equiv.symm_apply_eq compact).mpr (compact_point v hv).symm
    simp only [relabelBasis, pointWrite, he, if_pos hv]
  · have hi : compact.symm v ∉ pointLogicalWires := by
      intro h
      have he := compact_point _ h
      rw [Equiv.apply_symm_apply] at he
      exact hv (he.symm ▸ h)
    simp only [relabelBasis, pointWrite, if_neg hv, if_neg hi]


end
end ShorECDLP.Entrant.TightSupport
