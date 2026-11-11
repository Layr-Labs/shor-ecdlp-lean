import ShorECDLP.Submission.Entrant.First18Loader
namespace ShorECDLP.Entrant.KnownRoot
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem unitary_prefix_congr (old new : Circuit) (tail : AdaptiveCircuit)
    (ideal : State →ₗ[ℂ] State) (Valid : BasisState → Prop)
    (he : ∀ s, Valid s → Quantum.run old (ket s) = Quantum.run new (ket s))
    (hc : CoherentlyImplementsOn (.unitary old tail) ideal Valid) :
    CoherentlyImplementsOn (.unitary new tail) ideal Valid := by
  obtain ⟨cs,hc,hm⟩ := hc
  refine ⟨cs,?_,hm⟩
  simp only [AdaptiveCircuit.run,List.forall₂_map_left_iff] at hc ⊢
  apply hc.imp
  intro b c hb s hs
  change b.kraus (Quantum.run new (ket s)) = c • ideal (ket s)
  rw [← he s hs]
  exact hb s hs

def seededZeroAnd (_root bit path : Wire) : Circuit := [.X bit,.CX bit path,.X bit]

theorem seededZeroAnd_ket (root bit path : Wire) (s : BasisState)
    (hr : s root=true) (hneq : root≠bit) :
    Quantum.run (computeZeroAnd root bit path) (ket s) = Quantum.run (seededZeroAnd root bit path) (ket s) := by
  rw [run_ket_agrees_classical _ _ (by simp [computeZeroAnd]),
    run_ket_agrees_classical _ _ (by simp [seededZeroAnd])]
  congr 1
  funext w
  simp [computeZeroAnd,seededZeroAnd,Classical.run,Classical.applyGate,upd,hr,hneq]


theorem lookup_prefix_weight {n} (root bit path : Wire) (ops : List (LookupOp n)) (start : Nat) :
    ConditionalCatalyst.weight4 (lookupProgram n (ordinaryOp (seededZeroAnd root bit path)::ops) start)+4 =
      ConditionalCatalyst.weight4 (lookupProgram n (ordinaryOp (computeZeroAnd root bit path)::ops) start) := by
  simp [lookupProgram,ordinaryOp,seededZeroAnd,computeZeroAnd,gateProgram,
    ConditionalCatalyst.weight4_append,ConditionalCatalyst.weight4,ConditionalCatalyst.weightedLiteral,
    ConditionalCatalyst.weightedGate,ConditionalCatalyst.phaseTwoGate,ShorECDLP.tCost]
  omega


theorem first18_head : First18.selOps = ordinaryOp (computeZeroAnd 836 856 519)::First18.selOps.tail := by
  rw [First18.selOps,First18.selBits,First18.selPaths]
  rfl

def first18_seededOps : List (LookupOp 262144) :=
  ordinaryOp (seededZeroAnd 836 856 519)::First18.selOps.tail

open WEXCredit

theorem lookup_prefix_residue {n} (root bit path : Wire) (ops : List (LookupOp n)) (start : Nat) :
    residue (lookupProgram n (ordinaryOp (seededZeroAnd root bit path)::ops) start) =
      residue (lookupProgram n (ordinaryOp (computeZeroAnd root bit path)::ops) start) := by
  simp [lookupProgram,ordinaryOp,seededZeroAnd,computeZeroAnd,gateProgram,residue_append,residue,primitivePhaseCost]

theorem lookup_prefix_slots {n} (root bit path : Wire) (ops : List (LookupOp n)) (start : Nat) :
    (lookupProgram n (ordinaryOp (seededZeroAnd root bit path)::ops) start).gateSlots =
      (lookupProgram n (ordinaryOp (computeZeroAnd root bit path)::ops) start).gateSlots := by
  simp [lookupProgram,ordinaryOp,seededZeroAnd,computeZeroAnd,gateProgram,Straight.gateSlots_append,Straight.gateSlots]

theorem lookup_prefix_support {n} (root bit path : Wire) (ops : List (LookupOp n)) (start : Nat) :
    straightWires (lookupProgram n (ordinaryOp (seededZeroAnd root bit path)::ops) start) ⊆
      straightWires (lookupProgram n (ordinaryOp (computeZeroAnd root bit path)::ops) start) := by
  intro w hw
  simp only [lookupProgram,ordinaryOp,seededZeroAnd,computeZeroAnd,straightWires_append,
    gateProgram_support,List.flatMap_map,templateGateWires,gateWires,List.flatMap_cons,
    List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
  tauto

theorem first18_seeded_measurements : lookupMeasurements first18_seededOps = 131071 := by
  have h := First18.selOps_measurements
  rw [first18_head] at h
  simpa only [first18_seededOps,ordinaryOp,lookupMeasurements] using h

def first18_seededSel (start : Nat) : Straight 262144 start (start+131071) :=
  castFinish (by rw [first18_seeded_measurements]) (lookupProgram 262144 first18_seededOps start)

def first18_seededProgram (start : Nat) : Straight 262144 start (start+132606) :=
  castFinish (First18.program_finish start)
    (((first18_seededSel start).append (First18.swapProgram (start+131071))).append (First18.clearProgram (start+131071)))

def first18_seededSource (read : ConstantBit 262144 → Bool) : AdaptiveCircuit :=
  ((lookupCircuit read first18_seededOps).seq (.unitary First18.swapCircuit .done)).seq (First18.clearSource read)

theorem first18_seededSource_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Secp256k1.Point) :
    CoherentlyImplementsOn (first18_seededSource (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  have h := First18.source_coherent coeffs Q
  unfold First18.source at h
  rw [first18_head] at h
  simp only [first18_seededSource,first18_seededOps,lookupCircuit,ordinaryOp,literal_gates,
    AdaptiveCircuit.seq] at h ⊢
  exact unitary_prefix_congr _ _ _ _ _ (fun s hs => seededZeroAnd_ket 836 856 519 s hs.1 (by decide)) h

theorem first18_seededSel_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((first18_seededSel start).instantiate read history).run = (lookupCircuit read first18_seededOps).run := by
  rw [first18_seededSel,castFinish_instantiate,lookupProgram_run]

theorem first18_seededProgram_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((first18_seededProgram start).instantiate read history).run = (first18_seededSource read).run := by
  rw [first18_seededProgram,castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => First18.clear_run read _ h),AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => First18.swap_run read _ h),AdaptiveCircuit.run_seq,
    first18_seededSel_run read start history]
  simp only [first18_seededSource,AdaptiveCircuit.run_seq]

theorem first18_seededProgram_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Secp256k1.Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((first18_seededProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  unfold CoherentlyImplementsOn
  rw [first18_seededProgram_run]
  exact first18_seededSource_coherent coeffs Q


open ConditionalCatalyst Secp256k1
set_option linter.unusedSimpArgs false

theorem first18_seededSel_residue (start : Nat) : residue (first18_seededSel start) = 0 := by
  have h := lookup_prefix_residue 836 856 519 First18.selOps.tail start
  have he : residue (first18_seededSel start) = residue (First18.selProgram start) := by
    simp only [first18_seededSel,First18.selProgram,residue_cast,first18_seededOps]
    conv_rhs => rw [first18_head]
    exact h
  exact he.trans (First18.sel_residue start)

theorem first18_seededProgram_residue (start : Nat) : residue (first18_seededProgram start) = 0 := by
  rw [first18_seededProgram,residue_cast,residue_append,residue_append,first18_seededSel_residue,
    First18.swap_residue,First18.clear_residue]

theorem first18_seededSel_weight (start : Nat) : weight4 (first18_seededSel start)+4 = weight4 (First18.selProgram start) := by
  have h := lookup_prefix_weight 836 856 519 First18.selOps.tail start
  simp only [first18_seededSel,First18.selProgram,weight4_cast,first18_seededOps]
  conv_rhs => rw [first18_head]
  exact h

theorem first18_seededProgram_added (start : Nat) : added (first18_seededProgram start) = 132596 := by
  have hs := first18_seededSel_weight start
  have h : weight4 (first18_seededProgram start)+4 = weight4 (First18.program start) := by
    simp only [first18_seededProgram,First18.program,weight4_cast,weight4_append]
    omega
  rw [weight4_zero _ (first18_seededProgram_residue start),weight4_zero _ (First18.program_residue start),First18.program_added] at h
  omega

theorem first18_seededSel_slots (start : Nat) : (first18_seededSel start).gateSlots = (First18.selProgram start).gateSlots := by
  have h := lookup_prefix_slots 836 856 519 First18.selOps.tail start
  simp only [first18_seededSel,First18.selProgram,castFinish_gateSlots,first18_seededOps]
  conv_rhs => rw [first18_head]
  exact h

theorem first18_seededProgram_slots (start : Nat) : (first18_seededProgram start).gateSlots ≤ 1000000000 := by
  have h := First18.program_slots start
  simpa only [first18_seededProgram,First18.program,castFinish_gateSlots,Straight.gateSlots_append,
    first18_seededSel_slots] using h

theorem first18_seededSel_support (start : Nat) : straightWires (first18_seededSel start) ⊆ First18.support := by
  have h := lookup_prefix_support 836 856 519 First18.selOps.tail start
  have he : straightWires (first18_seededSel start) ⊆ straightWires (First18.selProgram start) := by
    simp only [first18_seededSel,First18.selProgram,straightWires_castFinish,first18_seededOps]
    conv_rhs => rw [first18_head]
    exact h
  exact he.trans (First18.sel_support start)

theorem first18_seededProgram_support (start : Nat) : straightWires (first18_seededProgram start) ⊆ First18.support := by
  rw [first18_seededProgram,straightWires_castFinish,straightWires_append,straightWires_append]
  exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨first18_seededSel_support start,First18.swap_support _⟩,First18.clear_support _⟩

theorem first18_seededOps_physical : ∀ op ∈ first18_seededOps, op.Physical := by
  intro op ho
  simp only [first18_seededOps,List.mem_cons] at ho
  rcases ho with rfl | ho
  · simp [ordinaryOp,seededZeroAnd,LookupOp.Physical,TemplateGate.WellFormed,Gate.WellFormed]
  · exact First18.selOps_physical op (List.mem_of_mem_tail ho)

theorem first18_seededProgram_wellFormed (start : Nat) : (first18_seededProgram start).WellFormed := by
  have hs : (first18_seededSel start).WellFormed := by
    rw [first18_seededSel,castFinish_wellFormed]
    exact lookupProgram_wellFormed _ first18_seededOps_physical _
  rw [first18_seededProgram,castFinish_wellFormed]
  exact straight_append_wellFormed _ _
    (straight_append_wellFormed _ _ hs (First18.swap_wellFormed _)) (First18.clear_wellFormed _)

def windowGeneric {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨SelectSchedule18.bits.reverse,132606,fun start => reindexStraight rows (first18_seededProgram start)⟩

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 262144,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    Single.WindowLaw coeffs (windowGeneric rows) (SelectSchedule18.update init)
      SelectSchedule18.Input := by
  intro Q hQ hn start history
  have hvalid := first18_seededProgram_coherent (fun a => coeffs (rows a)) Q start history
  have hupdate : (fun s => pointWrite
      (SelectSchedule18.tablePoint (fun a => coeffs (rows a)) Q
        (tableAddressValue SelectSchedule18.bits s)) s) = SelectSchedule18.update init Q := by
    funext s
    unfold SelectSchedule18.tablePoint SelectSchedule18.update
    have hbound : tableAddressValue SelectSchedule18.bits s < 262144 := by
      have hb := tableAddressValue_lt SelectSchedule18.bits s
      have hlen : SelectSchedule18.bits.length = 18 := by decide +kernel
      simpa only [hlen] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

#print axioms first18_seededProgram_added
#print axioms window_law_generic
end
end ShorECDLP.Entrant.KnownRoot
