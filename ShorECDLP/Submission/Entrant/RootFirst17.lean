import ShorECDLP.Submission.Entrant.RootWindows
namespace ShorECDLP.Entrant.RootFirst17
open Quantum Challenge Secp256k1 AndGadget WEXCredit ConditionalCatalyst RootPass ConstRoot
open Paper2607_13816 Paper2607_13816.ChallengeMigration MeasuredClear
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
theorem first17_leaf_safe (label : Nat) (control : Wire) (g : TemplateGate 131072)
    (hg : g∈First17.selLeaf label control) : safeTemplate 836 g := by
  simp only [First17.selLeaf,lookupLeafGates,List.mem_map] at hg
  obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
  change target≠836
  have ht : target∈pointLogicalWires ∨ target∈First17.garb := by
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl (List.of_mem_zip h).2
    · exact Or.inr (List.of_mem_zip h).2
  intro he
  subst target
  rcases ht with hp | hg
  · have h := First17.mem_point hp
    omega
  · have h := First17.mem_garb hg
    omega

theorem first17_leaf_hits (label : Nat) (control : Wire) :
    ((First17.selLeaf label control).map (templateHits 836)).sum=0 := by
  simp [First17.selLeaf,lookupLeafGates,List.map_map,Function.comp_def,templateHits]

theorem first17_selOps_safe : ∀ op∈First17.selOps,safeOp 836 op := by
  rw [First17.selOps]
  obtain ⟨hb,hp⟩ := layout_avoids First17.sel_layout
  exact unaryOps_safe 836 First17.selLeaf _ _ _ first17_leaf_safe hb hp

theorem first17_selOps_hits : opsHits 836 First17.selOps=1 := by
  rw [First17.selOps]
  exact unaryOps_root_hits 836 First17.selLeaf _ _ First17.sel_layout
    (by rw [First17.sel_nodes]; decide) first17_leaf_hits


theorem selProgram_safe (start : Nat) : safeProgram 836 (First17.selProgram start) := by
  rw [First17.selProgram,safeProgram_cast]
  exact lookupProgram_safe 836 _ start first17_selOps_safe

theorem selProgram_hits (start : Nat) : literalHits 836 (First17.selProgram start)=1 := by
  rw [First17.selProgram,literalHits_cast,literalHits_lookupProgram,first17_selOps_hits]
theorem first17_swap_noRoot (start : Nat) : 836∉straightWires (First17.swapProgram start) := by
  rw [First17.swapProgram,literalProgram_support]
  intro h
  rcases First17.swap_wires 836 h with h | h | h
  · dsimp only [Wire] at *; omega
  · have h := First17.mem_point h
    dsimp only [Wire] at *; omega
  · have h := First17.mem_garb h
    dsimp only [Wire] at *; omega

theorem first17_low_ne (i : Fin 7) : First17.low i≠836 := by
  simp only [First17.low]
  dsimp only [Wire] at *
  omega

theorem first17_hot_ne (i : Fin 128) : First17.hot i≠836 := by
  simp only [First17.hot]
  dsimp only [Wire] at *
  omega


theorem clear_safe (start : Nat) : safeProgram 836 (First17.clearProgram start) := by
  apply readOnlyProgram_safe
  obtain ⟨hb,hp⟩:=layout_avoids First17.clear_layout
  rw [First17.clearProgram,readOnlyProgram_cast]
  apply measuredClear7_readOnly 836 _ _ _ _ _ _ _ _ first17_low_ne first17_hot_ne (by decide) hb hp
  intro p hp he
  apply First17.tree_not_targets 836 (by simp)
  exact List.mem_map.mpr ⟨p,hp,he⟩
theorem fixup7_hits {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (MeasuredClear.fixupProgram data refs low hot tree root scratch paths)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  obtain ⟨hn,hprep,_⟩ := fixup7_noRoot_parts (n:=n) known low hot hl hh
  have hz (start : Nat) : literalHits known (literalProgram (n:=n) (s:=start) (MeasuredClear.hotPrepare low hot))=0 :=
    literalHits_zero_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn)
  simp only [MeasuredClear.fixupProgram,literalHits_append,literalHits_cast,literalHits_recordLookupProgram,
    literalHits_hadamards,literalHits_adjoint_hadamards,literalHits_eraseNetwork,literalHits_X,hz,
    zero_add,add_zero]

theorem measured7_hits {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (MeasuredClear.measuredClear data low hot tree root scratch paths start)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  rw [MeasuredClear.measuredClear,literalHits_cast]
  apply literalHits_measureThen
  intro cursor refs
  rw [literalHits_cast]
  exact fixup7_hits known data refs low hot tree root scratch paths hl hh




theorem clear_hits (start : Nat) : literalHits 836 (First17.clearProgram start)=1 := by
  rw [First17.clearProgram,literalHits_cast,measured7_hits 836 _ _ _ _ _ _ _ _ first17_low_ne first17_hot_ne]
  exact recordUnaryOps_root_hits 836 _ _ First17.clear_layout (by rw [First17.clear_nodes];decide)

theorem program_safe (start : Nat) : safeProgram 836 (First17.program start) := by
  simp only [First17.program,safeProgram_cast,safeProgram_append]
  exact ⟨⟨selProgram_safe start,safeProgram_of_not_mem 836 _ (first17_swap_noRoot _)⟩,clear_safe _⟩

theorem program_hits (start : Nat) : literalHits 836 (First17.program start)=2 := by
  simp only [First17.program,literalHits_cast,literalHits_append,selProgram_hits,
    clear_hits,literalHits_zero_of_not_mem 836 _ (first17_swap_noRoot _)]

def rootProgram (start : Nat) : Straight 131072 start (start+67198) :=
  seedProgram 836 (First17.program start)

theorem rootProgram_coherent (coeffs : Fin 131072 → PointCoeff) (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((rootProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (ScheduleFirst17.tablePoint coeffs Q
        (tableAddressValue ScheduleFirst17.bits s)) s)) ScheduleFirst17.Input := by
  apply seedProgram_coherent 836 _ _ _ _ _ (program_safe start) (fun _ hs => hs.1)
  exact First17.program_coherent coeffs Q start history

theorem rootProgram_residue (start : Nat) : residue (rootProgram start)=0 := by
  have h := seedProgram_residue_le 836 (First17.program start)
  rw [First17.program_residue] at h
  exact Nat.eq_zero_of_le_zero h

theorem rootProgram_added (start : Nat) : added (rootProgram start)=67189 := by
  have h := seedProgram_added 836 (First17.program start)
  rw [First17.program_added,program_hits] at h
  change added (seedProgram 836 (First17.program start))=67189
  omega

theorem rootProgram_slots (start : Nat) : (rootProgram start).gateSlots≤1000000000 := by
  rw [rootProgram,seedProgram_slots]
  exact First17.program_slots start

theorem rootProgram_support (start : Nat) :
    straightWires (rootProgram start)⊆First17.support :=
  (seedProgram_wires 836 _).trans (First17.program_support start)

theorem rootProgram_wellFormed (start : Nat) : (rootProgram start).WellFormed :=
  seedProgram_wellFormed 836 _ (First17.program_wellFormed start)

def windowGeneric {n : Nat} (rows : Fin 131072 → Fin n) : Single.Window n :=
  ⟨ScheduleFirst17.bits.reverse,67198,fun start => reindexStraight rows (rootProgram start)⟩

theorem program_tCount (coeffs : Fin 131072 → PointCoeff) (Q : Secp256k1.Point) (start : Nat) (history : Fin start → Bool) :
    ((rootProgram start).instantiate (readConstant coeffs Q) history).tCount = 470323 := by
  rw [exact_t _ (rootProgram_residue start),rootProgram_added]

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 131072 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 131072,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    Single.WindowLaw coeffs (windowGeneric rows) (ScheduleFirst17.update init)
      ScheduleFirst17.Input := by
  intro Q hQ hn start history
  have hvalid := rootProgram_coherent (fun a => coeffs (rows a)) Q start history
  have hupdate : (fun s => pointWrite
      (ScheduleFirst17.tablePoint (fun a => coeffs (rows a)) Q
        (tableAddressValue ScheduleFirst17.bits s)) s) = ScheduleFirst17.update init Q := by
    funext s
    unfold ScheduleFirst17.tablePoint ScheduleFirst17.update
    have hbound : tableAddressValue ScheduleFirst17.bits s < 131072 := by
      have hb := tableAddressValue_lt ScheduleFirst17.bits s
      have hlen : ScheduleFirst17.bits.length = 17 := by decide +kernel
      simpa only [hlen] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

theorem window_wellFormed {n : Nat} (rows : Fin 131072 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).WellFormed := by
  unfold windowGeneric
  exact (reindexStraight_wellFormed rows (rootProgram start)).mpr (rootProgram_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 131072 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).gateSlots ≤ 1000000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact rootProgram_slots start

theorem window_support {n : Nat} (rows : Fin 131072 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ First17.support := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact rootProgram_support start

theorem window_t {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 131072 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    (((windowGeneric rows).program start).instantiate (readConstant coeffs Q) history).tCount = 470323 := by
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact program_tCount (fun a => coeffs (rows a)) Q start history

theorem window_credit {n : Nat} (_coeffs : Fin n → PointCoeff) (rows : Fin 131072 → Fin n)
    (_Q : Point) (start : Nat) (_history : Fin start → Bool) :
    added ((windowGeneric rows).program start) = 67189 := by
  unfold windowGeneric
  rw [added_reindex]
  exact rootProgram_added start

#print axioms rootProgram_coherent
#print axioms rootProgram_added
#print axioms window_law_generic
end
end ShorECDLP.Entrant.RootFirst17
