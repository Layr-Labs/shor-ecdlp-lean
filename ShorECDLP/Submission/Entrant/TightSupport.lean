import ShorECDLP.Submission.Entrant.Prefix
import ShorECDLP.Submission.Entrant.PoolHost

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

/-- Tight support without wire `10000`: `PathShare.newSourceH` (1616 wires) plus wire `871`. -/
def support17 : List Wire := PathShare.newSourceH ++ [871]
theorem old_cover17 : PathShare.newSourceH ⊆ support17 := List.subset_append_left _ _
theorem support17_length : support17.length = 1617 := by decide

theorem frame_support17 (r : Nat) (row : (j : Nat) → Straight 65536 j (j + r))
    (hrow : ∀ j, ChallengeMigration.straightWires (row j) ⊆ support17)
    (start : Nat) : ChallengeMigration.straightWires (WideSigned.Frame16.program r row start) ⊆ support17 := by
  have cover : newSourceH ⊆ support17 := old_cover17
  have hs (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.nProgram .w16 j) ⊆ support17 := by
    rw [WideSigned.Body.nProgram, straightWires_reindex]
    exact (nFast_newH j).trans cover
  have hp (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.prefixProgram .w16 j) ⊆ support17 := by
    rw [WideSigned.Body.prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  have hpost (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.suffixProgram .w16 j) ⊆ support17 := by
    rw [WideSigned.Body.suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  rw [WideSigned.Frame16.program, straightWires_castFinish]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp start, hs start⟩, hrow _⟩, hs _⟩, hpost _⟩

def compact17 : Wire ≃ Wire :=
  PathShare.piH.trans (Equiv.swap 14436 1616)

theorem compact17_bound (v : Wire) (hv : v ∈ support17) : compact17 v < 1617 := by
  rcases List.mem_append.mp hv with h | h
  · have hp := (PathShare.piH_apply v).trans_lt (PathShare.piH_bound v h)
    simp only [compact17, Equiv.trans_apply, Equiv.swap_apply_def]
    dsimp only [Wire] at hp ⊢
    split_ifs <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    decide

theorem compact17_point (v : Wire) (hv : v ∈ pointLogicalWires) : compact17 v = v := by
  rw [compact17, Equiv.trans_apply, PathShare.piH_point v hv]
  have hb := point_wire_small v hv
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact17_active : compact17 836 = 836 := by decide
theorem compact17_sign : compact17 870 = 870 := by decide
theorem compact17_extra : compact17 871 = 1616 := by decide

theorem compact17_address (v : Wire) (hv : v ∈ streamAddress) : compact17 v = v := by
  have hb : 855 ≤ v ∧ v < 871 := by simpa only [streamAddress, List.mem_range'_1] using hv
  have hf : fixedPort v := by unfold fixedPort; dsimp only [Wire] at *; omega
  rw [compact17, Equiv.trans_apply, PathShare.piH_fixed v hf]
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact17_pointWrite (P : Point) (s : BasisState) :
    relabelBasis compact17 (pointWrite P s) = pointWrite P (relabelBasis compact17 s) := by
  funext v
  by_cases hv : v ∈ pointLogicalWires
  · have he : compact17.symm v = v := (Equiv.symm_apply_eq compact17).mpr (compact17_point v hv).symm
    simp only [relabelBasis, pointWrite, he, if_pos hv]
  · have hi : compact17.symm v ∉ pointLogicalWires := by
      intro h
      have he := compact17_point _ h
      rw [Equiv.apply_symm_apply] at he
      exact hv (he.symm ▸ h)
    simp only [relabelBasis, pointWrite, if_neg hv, if_neg hi]

/-- Tight support with 4 flag-hosted pool wires retired (`14874..14877`): `PoolHost.newSourceH7` (1612 wires) plus wire `871`. -/
def support17_7 : List Wire := PoolHost.newSourceH7 ++ [871]
theorem old_cover17_7 : PoolHost.newSourceH7 ⊆ support17_7 := List.subset_append_left _ _
theorem support17_7_length : support17_7.length = 1613 := by decide

theorem nFast_newH7 (start : Nat) : ChallengeMigration.straightWires (nFastProgram start) ⊆ PoolHost.newSourceH7 := by
  apply literalFixed_support (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) 256
    ((literal_meas (n := 32768) _).trans fastWindowSign_normalized_counts.2) PoolHost.newSourceH7 (start := start)
  rw [ECDSAAdd.Baselines.normalize_wires]
  have hs := WEX.finiteSignMeasured_support (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p
  have cover : 870 :: 838 :: (negateYLayout streamLayout).wires streamLayout.core.generic ⊆ PoolHost.newSourceH7 := by
    apply PoolHost.newSourceH7_of_bounds; decide +kernel
  have sub : ECDSAAdd.wires fastWindowSignProgram ⊆ ECDSAAdd.wires
      (WEX.finiteSignMeasured (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p) := by
    simp only [fastWindowSignProgram, WEX.finiteSignMeasured, ECDSAAdd.wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (fun _ h => h) WEX.TrimmedSign.reflection_wires)
      (fun _ h => h)
  exact sub.trans (hs.trans (fun w hw => List.mem_toFinset.mpr (cover (List.mem_toFinset.mp hw))))

theorem frame_support17_7 (r : Nat) (row : (j : Nat) → Straight 65536 j (j + r))
    (hrow : ∀ j, ChallengeMigration.straightWires (row j) ⊆ support17_7)
    (start : Nat) : ChallengeMigration.straightWires (WideSigned.Frame16.program r row start) ⊆ support17_7 := by
  have cover : PoolHost.newSourceH7 ⊆ support17_7 := old_cover17_7
  have hs (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.nProgram .w16 j) ⊆ support17_7 := by
    rw [WideSigned.Body.nProgram, straightWires_reindex]
    exact (nFast_newH7 j).trans cover
  have hp (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.prefixProgram .w16 j) ⊆ support17_7 := by
    rw [WideSigned.Body.prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  have hpost (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.suffixProgram .w16 j) ⊆ support17_7 := by
    rw [WideSigned.Body.suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  rw [WideSigned.Frame16.program, straightWires_castFinish]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp start, hs start⟩, hrow _⟩, hs _⟩, hpost _⟩

def compact17_7 : Wire ≃ Wire :=
  PoolHost.piH7.trans (Equiv.swap 14436 1612)

theorem compact17_7_bound (v : Wire) (hv : v ∈ support17_7) : (compact17_7 v : Nat) < 1613 := by
  rcases List.mem_append.mp hv with h | h
  · have hp := PoolHost.piH7_bound v h
    simp only [compact17_7, Equiv.trans_apply, Equiv.swap_apply_def]
    dsimp only [Wire] at hp ⊢
    split_ifs <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    decide

theorem compact17_7_point (v : Wire) (hv : v ∈ pointLogicalWires) : compact17_7 v = v := by
  rw [compact17_7, Equiv.trans_apply, PoolHost.piH7_point v hv]
  have hb := point_wire_small v hv
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact17_7_active : compact17_7 836 = 836 := by decide
theorem compact17_7_sign : compact17_7 870 = 870 := by decide
theorem compact17_7_extra : compact17_7 871 = 1612 := by decide

theorem compact17_7_address (v : Wire) (hv : v ∈ streamAddress) : compact17_7 v = v := by
  have hb : 855 ≤ v ∧ v < 871 := by simpa only [streamAddress, List.mem_range'_1] using hv
  have hf : fixedPort v := by unfold fixedPort; dsimp only [Wire] at *; omega
  rw [compact17_7, Equiv.trans_apply, PoolHost.piH7_fixed v hf]
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact17_7_pointWrite (P : Point) (s : BasisState) :
    relabelBasis compact17_7 (pointWrite P s) = pointWrite P (relabelBasis compact17_7 s) := by
  funext v
  by_cases hv : v ∈ pointLogicalWires
  · have he : compact17_7.symm v = v := (Equiv.symm_apply_eq compact17_7).mpr (compact17_7_point v hv).symm
    simp only [relabelBasis, pointWrite, he, if_pos hv]
  · have hi : compact17_7.symm v ∉ pointLogicalWires := by
      intro h
      have he := compact17_7_point _ h
      rw [Equiv.apply_symm_apply] at he
      exact hv (he.symm ▸ h)
    simp only [relabelBasis, pointWrite, if_neg hv, if_neg hi]

/-! ### Narrow-window compaction transport (`PoolHost.piH7`, `< 1612`) -/

theorem piH7_address (w : Wire) (h : w ∈ streamAddress) : PoolHost.piH7 w = w := by
  apply PoolHost.piH7_fixed
  exact Or.inr (Or.inr (Or.inr (by simpa [streamAddress] using h)))

def pullH7 (s : BasisState) : BasisState := relabelBasis PoolHost.piH7.symm s

theorem pullH7_at (s : BasisState) (w : Wire) (h : fixedPort w) : pullH7 s w = s w := by
  simp only [pullH7, relabelBasis, Equiv.symm_symm, PoolHost.piH7_fixed w h]

theorem pullH7_hot (s : BasisState) (i : Fin 128) : pullH7 s (hot i) = s (hot i) := by
  simp only [pullH7, relabelBasis, Equiv.symm_symm, PoolHost.piH7_hot]

theorem pullH7_write (P : Point) (s : BasisState) : pullH7 (pointWrite P s) = pointWrite P (pullH7 s) := by
  funext w
  by_cases hp : w ∈ pointLogicalWires
  · have h1 : PoolHost.piH7 w = w := PoolHost.piH7_point w hp
    simp only [pullH7, relabelBasis, Equiv.symm_symm, pointWrite, h1, if_pos hp]
  · have h2 : PoolHost.piH7 w ∉ pointLogicalWires := by
      intro hm
      have he := PoolHost.piH7_point _ hm
      exact hp (PoolHost.piH7.injective he ▸ hm)
    simp only [pullH7, relabelBasis, Equiv.symm_symm, pointWrite, if_neg hp, if_neg h2]

theorem pushH7_write (P : Point) (s : BasisState) :
    relabelBasis PoolHost.piH7 (pointWrite P (pullH7 s)) = pointWrite P s := by
  rw [← pullH7_write P s]
  funext w
  simp only [pullH7, relabelBasis, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem pullH7_coordinates (s : BasisState) : pointStateCoordinates (pullH7 s) = pointStateCoordinates s := by
  have he (ws : List Wire) (h : ∀ w ∈ ws, w ∈ pointLogicalWires) : wireValues ws (pullH7 s) = wireValues ws s :=
    List.map_congr_left fun w hw => by
      simp only [pullH7, relabelBasis, Equiv.symm_symm, PoolHost.piH7_point w (h w hw)]
  have hx : wireValues (List.range' 263 256) (pullH7 s) = wireValues (List.range' 263 256) s :=
    he _ (fun w hw => List.mem_append_left _ hw)
  have hy : wireValues (List.range' 580 256) (pullH7 s) = wireValues (List.range' 580 256) s :=
    he _ (fun w hw => List.mem_append_right _ (List.mem_append_left _ hw))
  have h838 : pullH7 s 838 = s 838 := by
    simp only [pullH7, relabelBasis, Equiv.symm_symm,
      PoolHost.piH7_point 838 (by simp [pointLogicalWires, pointCorrectionYInf])]
  simp only [pointStateCoordinates, hx, hy, h838]

theorem pullH7_digit (s : BasisState) : windowRawDigit 0 (pullH7 s) = windowRawDigit 0 s := by
  have he : wireValues (windowAddressBits 0) (pullH7 s) = wireValues (windowAddressBits 0) s :=
    List.map_congr_left fun w hw => by
      have hfix : fixedPort w := by
        simp only [windowAddressBits, windowBankStart, List.mem_range'_1] at hw
        unfold fixedPort; omega
      exact pullH7_at s w hfix
  have h870 : pullH7 s (windowBankStart 0 + 15) = s (windowBankStart 0 + 15) :=
    pullH7_at s 870 (by decide +kernel)
  simp only [windowRawDigit, he, h870]

def readyH7 (s : BasisState) : Prop := windowReady (pullH7 s) ∧ MeasuredClear.HotClean hot s

theorem readyH7_active (s : BasisState) (h : readyH7 s) : s 836 = true := by
  simpa only [pullH7_at s 836 (by decide +kernel)] using windowReady_active (pullH7 s) h.1

theorem readyH7_write (P : Point) (s : BasisState) (h : readyH7 s) :
    readyH7 (pointWrite P s) := by
  refine ⟨?_, pointWrite_hot P s h.2⟩
  rw [pullH7_write]
  exact windowReady_write P (pullH7 s) h.1

theorem pullH7_address (s : BasisState) (v : Wire) (hv : v ∈ streamAddress) (b : Bool) :
    pullH7 (s[v ↦ b]) = (pullH7 s)[v ↦ b] := by
  have hh' : PoolHost.piH7.symm v = v := by
    rw [Equiv.symm_apply_eq]; exact (piH7_address v hv).symm
  simp only [pullH7, relabelBasis_upd, hh']

theorem readyH7_address (s : BasisState) (h : readyH7 s)
    (v : Wire) (hv : v ∈ streamAddress) (b : Bool) : readyH7 (s[v ↦ b]) := by
  refine ⟨?_, ?_⟩
  · rw [pullH7_address s v hv b]
    exact windowReady_address (pullH7 s) h.1 v hv b
  · intro i
    have hn : hot i ≠ v := fun he => hot_outside_address i (he.symm ▸ hv)
    exact (upd_other s v b hn).trans (h.2 i)

theorem pullH7_first (s : BasisState) (h : FirstWindowInput s) : FirstWindowInput (pullH7 s) := by
  constructor
  · simpa only [pullH7_at s 836 (by decide +kernel)] using h.1
  · intro w hw ha
    change s (PoolHost.piH7 w) = false
    apply h.2
    · intro hh
      have hfix : PoolHost.piH7 836 = 836 := PoolHost.piH7_fixed _ (by decide +kernel)
      exact hw (PoolHost.piH7.injective (hh.trans hfix.symm))
    · intro hh
      have hfix := piH7_address _ hh
      have he : PoolHost.piH7 w = w := PoolHost.piH7.injective hfix
      exact ha (he ▸ hh)

theorem readyH7_first (s : BasisState) (h : FirstWindowInput s) (P : Point) :
    readyH7 (pointWrite P s) := by
  refine ⟨?_, ?_⟩
  · rw [pullH7_write]
    exact windowReady_first (pullH7 s) (pullH7_first s h) P
  · apply pointWrite_hot P s
    intro i
    apply h.2
    · have hi := i.isLt
      simp only [hot]
      dsimp only [Wire] at *
      omega
    · exact hot_outside_address i

def stateH7 (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  relabelBasis PoolHost.piH7 (bodyState coeffs Q (pullH7 s))

theorem stateH7_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (s : BasisState) (hs : readyH7 s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    stateH7 coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s), signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s), signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩))
        else 0) s := by
  unfold stateH7
  rw [bodyState_correct coeffs Q (pullH7 s) hs.1 P ((pullH7_coordinates s).trans hP), pushH7_write]
  simp only [pullH7_at s 836 (by decide +kernel), pullH7_at s 870 (by decide +kernel), pullH7_digit]

theorem relabelH7_coherent {s e : Nat} (p : Straight 32768 s e) (coeffs : Fin 32768 → PointCoeff)
    (Q : Point) (history : Fin s → Bool)
    (hc : CoherentlyImplementsOn (p.instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready) :
    CoherentlyImplementsOn ((relabelStraight PoolHost.piH7 p).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (stateH7 coeffs Q))
      (fun s => readyH7 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := hc.relabel PoolHost.piH7
  have hr : CoherentlyImplementsOn
      ((p.instantiate (readConstant coeffs Q) history).relabel PoolHost.piH7)
      ((relabelState PoolHost.piH7).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState PoolHost.piH7.symm)))
      (fun s => readyH7 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs, aligned, mass⟩ := h
    refine ⟨cs, aligned.imp ?_, mass⟩
    intro b c hb s hs
    apply hb s
    refine ⟨hs.1.1, ?_⟩
    intro i
    exact (pullH7_hot s i).trans (hs.1.2 i)
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (stateH7 coeffs Q))
    (by intro s _; simp [stateH7, pullH7, LinearMap.comp_apply, relabelState, ket])
  rw [relabelStraight_instantiate]
  exact he

end
end ShorECDLP.Entrant.TightSupport
