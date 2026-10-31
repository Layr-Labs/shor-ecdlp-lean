import ShorECDLP.Submission.Entrant.Corners

section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
namespace ShorECDLP.Entrant.WEX
open Quantum Challenge ShorECDLP.Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open ECDSAAdd ECDSAAdd.RecordedQuantum ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩
attribute [local irreducible] compile ECDSAAdd.run literalToffolis literalRecords normalizeW codeRecords
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Baselines.normalizeProgram

def tightReferenceRow (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ wFiniteTight streamLayout rows ++ wLiteral ([.X 838])

theorem tightReferenceRow_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ tightReferenceRow rows, Placed windowBits windowPaths windowRoot i := by
  intro i hi
  simp only [tightReferenceRow, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · simp only [wLiteral, List.mem_singleton] at hi
    subst i
    change ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ ECDSAAdd.wires ([.X 838] : Program)
    intro w hw hp
    have hg := window_reserved_gap w hw
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hp
    rw [hp] at hg
    norm_num at hg
  · exact windowOne_placed rows i hi
  · simp only [wLiteral, List.mem_singleton] at hi
    subst i
    change ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ ECDSAAdd.wires ([.X 838] : Program)
    intro w hw hp
    have hg := window_reserved_gap w hw
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hp
    rw [hp] at hg
    norm_num at hg















theorem tightReferenceRow_width_placed (k : Nat) (hk : k ≤ 15) (rows : Nat → Fin 32768) :
    ∀ i ∈ tightReferenceRow rows, Placed (widthBits k) windowPaths windowRoot i := by
  intro i hi
  have hp := tightReferenceRow_placed rows i hi
  cases i with
  | literal p =>
    intro w hw
    exact hp w ((List.Sublist.cons₂ windowRoot (width_sublist k hk)).subset hw)
  | lookup c ports =>
    refine ⟨(List.Sublist.cons₂ _ (width_sublist k hk)).nodup hp.1, hp.2.1, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw ht
    exact List.disjoint_left.mp hp.2.2
      ((List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (width_sublist k hk))).subset hw) ht


end
noncomputable def clearReferenceRow (rows : Nat → Fin 32768) : WCode 32768 := portRowCode5 rows

theorem clearReferenceRow_eq (rows : Nat → Fin 32768) :
    clearReferenceRow rows = wLiteral ([.X 838]) ++ portFinite5 rows ++ wLiteral ([.X 838]) := rfl

theorem portFinite_eq (rows : Nat → Fin 32768) :
    portFinite3 rows = portPrefixCode rows ++ wGeneric streamLayout rows ++
      portSuffixCodeD rows := rfl


theorem clearReferenceRow_placed :
    ∀ i ∈ clearReferenceRow probeRows, PlacedPair windowBits windowPaths windowRoot i := portRow5_placed

theorem clearReferenceRow_physical :
    ∀ p, WInstr.literal p ∈ clearReferenceRow probeRows → GatePhysical p := portRow5_physical

theorem clearReferenceRow_literal_source (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ clearReferenceRow probeRows) :
    ECDSAAdd.wires p ⊆ sourceSupport.toFinset := portRow5_literal_source p hp

theorem clearReferenceRow_literalToffolis (rows : Nat → Fin 32768) :
    literalToffolis (clearReferenceRow rows) = literalToffolis (rowAddCode rows) + 1535 := by
  have h5 := (portRow5_measures rows).1
  have h4 := (portRow4_measures rows).1
  have h3 := (portRow3_measures rows).1
  have h2 := (portRow2_measures rows).1
  have h1 := (portRow_measures rows).1
  change literalToffolis (portRowCode5 rows) = _
  omega

theorem clearReferenceRow_run (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (s : BasisState) (hs : liveReady s) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (clearReferenceRow probeRows))
      (tableAddressValue windowBits s)).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ =
        ⟨false,rowPointState coeffs Q s⟩ :=
  portRow5_transport _ coeffs Q hQ hn s hs _
    (fun m => (portRow4_run_same _ coeffs Q hQ hn s hs m).trans (rowAddCode_run coeffs Q hQ hn s hs m)) m

theorem clearReferenceRow_run_any (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (s : BasisState) (hs : liveReady s) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (clearReferenceRow probeRows))
      a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ =
        ⟨false,pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q a) s⟩ :=
  portRow5_transport a coeffs Q hQ hn s hs _
    (fun m => (portRow4_run_same a coeffs Q hQ hn s hs m).trans (rowAddCode_run_any a coeffs Q hQ hn s hs m)) m

theorem clearReferenceRow_traversals : traversals (normalizeW (clearReferenceRow probeRows)) = 15 :=
  portRow5_traversals

theorem clearReferenceRow_records : codeRecords windowBits windowPaths windowRoot
    (normalizeW (clearReferenceRow probeRows)) = 2048404 := portRow5_records

theorem clearReferenceRow_sourceLookupOK :
    (normalizeW (clearReferenceRow probeRows)).all sourceLookupOK = true := portRow5_sourceLookupOK

theorem clearReferenceRow_literal_slots_bound : literalSlotSum (clearReferenceRow probeRows) ≤ 50021565 :=
  portRow5_literal_slots_bound

theorem clearReferenceRow_portTotal : portTotal (clearReferenceRow probeRows) ≤ 20000 := portRow5_portTotal

theorem clearReferenceRow_count_upper (k : Nat) :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (clearReferenceRow probeRows)) + 15 * (2^k-1) ≤
      2165436 + 15 * (2^k-1) := by
  have e : clearReferenceRow probeRows = portRowCode5 probeRows := rfl
  rw [e]
  exact portRow5_count_upper k

theorem clearReferenceRow_width_placed (k : Nat) (hk : k ≤ 15) :
    ∀ i ∈ clearReferenceRow probeRows, PlacedPair (widthBits k) windowPaths windowRoot i :=
  portRow5_width_placed k hk

theorem clearReferenceRow_width_records (k : Nat) (hk : k ≤ 15) :
    codeRecords (widthBits k) windowPaths windowRoot (normalizeW (clearReferenceRow probeRows)) =
      1556899 + 15 * (2 ^ k - 1) := portRow5_width_records k hk

set_option allowUnsafeReducibility true in
attribute [irreducible] clearReferenceRow portRowCode5 portFinite5 portRowCodeE portFiniteE portSuffixCodeE scrECorners portRowCode4 portRowCode3 portFinite3 portSuffixCodeD scrDCorners portRowCode2 portFinite2 portPrefixCode scrInCompare portRowCode portFinite portSuffixCode scrOutCompare scrCorners

end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000

/-- Static legality of a record-aware lookup operation. -/
def RecordPhysical {n base} (ports : List (RecordPort n base)) (scratch : Wire) : RecordLookupOp → Prop
  | .gates gs => CircuitWellFormed gs
  | .leaf _ control => control ≠ scratch ∧ ∀ p ∈ ports, scratch ≠ p.target
  | .erase a b _ => a ≠ b

theorem recordLeaf_wellFormed {n base} (ports : List (RecordPort n base)) (scratch row control start : Nat)
    (hb : base ≤ start) (hc : control ≠ scratch) (ht : ∀ p ∈ ports, scratch ≠ p.target) :
    (recordLeaf ports scratch row control start hb).WellFormed := by
  induction ports with
  | nil => trivial
  | cons p ps ih =>
    apply straight_append_wellFormed
    · simpa [mixedCX,Straight.WellFormed,TemplateGate.WellFormed,Gate.WellFormed] using
        (And.intro hc (And.intro (ht p (by simp)) (And.intro hc (And.intro (ht p (by simp)) True.intro))))
    · exact ih (fun q hq => ht q (by simp [hq]))

theorem recordLookupProgram_wellFormed {n base} (ports : List (RecordPort n base)) (scratch : Wire)
    (ops : List RecordLookupOp) (hp : ∀ op ∈ ops, RecordPhysical ports scratch op)
    (start : Nat) (hb : base ≤ start) : (recordLookupProgram ports scratch ops start hb).WellFormed := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    have ho := hp op (by simp)
    have ht := ih (fun o hm => hp o (by simp [hm]))
    cases op with
    | gates gs => exact straight_append_wellFormed _ _ (literalProgram_wellFormed gs ho) (ht start hb)
    | leaf row control =>
      exact straight_append_wellFormed _ _
        (recordLeaf_wellFormed ports scratch row control start hb ho.1 ho.2) (ht start hb)
    | erase a b t =>
      rw [recordLookupProgram,castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (andEraseProgram_wellFormed n start a b t ho)
        (ht (start+1) (by omega))

theorem recordUnary_physical {n base} (ports : List (RecordPort n base)) (scratch : Wire)
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire) (hl : tree.Layout q paths)
    (hleaf : ∀ l c, c ∈ q::paths → RecordPhysical ports scratch (.leaf l c)) :
    ∀ op ∈ recordUnaryOps tree q paths, RecordPhysical ports scratch op := by
  induction hl with
  | leaf l q paths hn => simpa only [recordUnaryOps,List.forall_mem_singleton] using hleaf l q (by simp)
  | node bit q path zero one rest hn hz ho ihz iho =>
    have hhead := (List.nodup_cons.mp hn).1
    have hcross := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
    have hbit : bit ∈ (UnaryActionTree.node bit zero one).indexWires.dedup := by simp [UnaryActionTree.indexWires]
    have hqb : q ≠ bit := by intro he; apply hhead; rw [he]; simp [hbit]
    have hqp : q ≠ path := by intro he; apply hhead; rw [he]; simp
    have hbp : bit ≠ path := by intro he; exact hcross bit hbit path (by simp) he
    have hleaf' : ∀ l c, c ∈ path::rest → RecordPhysical ports scratch (.leaf l c) :=
      fun l c hc => hleaf l c (by simp [hc])
    have hx := ihz hleaf'
    have hy := iho hleaf'
    have hc : RecordPhysical ports scratch (.gates (computeZeroAnd q bit path)) := by
      simp [RecordPhysical,computeZeroAnd,CircuitWellFormed,Gate.WellFormed,hqb,hqp,hbp]
    have hcx : RecordPhysical ports scratch (.gates [.CX q path]) := by
      simp [RecordPhysical,CircuitWellFormed,Gate.WellFormed,hqp]
    have hxb : RecordPhysical ports scratch (.gates [.X bit]) := by
      simp [RecordPhysical,CircuitWellFormed,Gate.WellFormed]
    simp only [recordUnaryOps,List.forall_mem_append,List.forall_mem_cons,List.mem_nil_iff,false_implies]
    exact ⟨⟨⟨⟨⟨hc,fun _ => trivial⟩,hx⟩,⟨hcx,fun _ => trivial⟩⟩,hy⟩,hcx,hxb,hqb,hxb,fun _ => trivial⟩

theorem eraseNetwork_wellFormed (n : Nat) (cs : List SplitCell) (hp : ∀ c ∈ cs, c.Physical) (start : Nat) :
    (eraseNetwork n cs start).WellFormed := by
  induction cs generalizing start with
  | nil => trivial
  | cons c cs ih =>
    rw [eraseNetwork,castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (ih (fun d hd => hp d (by simp [hd])) start)
      (eraseSplit_wellFormed n _ c.bit c.parent c.child (hp c (by simp)).1 (hp c (by simp)).2.2)

theorem fixupProgram_wellFormed {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank hot) :
    (fixupProgram data refs low hot tree root scratch paths).WellFormed := by
  have hp := hotNetwork_physical low hot hi hdlow
  have hH (ws : List Wire) : CircuitWellFormed (ws.map Gate.H) := by
    intro g hg; obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg; trivial
  unfold fixupProgram
  apply straight_append_wellFormed
  · apply literalProgram_wellFormed
    rw [hotPrepare,circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed,Gate.WellFormed],splitNetwork_wellFormed _ hp⟩
  · apply straight_append_wellFormed
    · exact literalProgram_wellFormed _ (hH _)
    · apply straight_append_wellFormed
      · apply recordLookupProgram_wellFormed
        apply recordUnary_physical _ _ _ _ _ hl
        intro row c hc
        refine ⟨?_,?_⟩
        · intro he; apply hs; subst c; simp only [List.mem_cons,List.mem_append] at hc ⊢; tauto
        · intro p hpm he
          exact hshot (he.symm ▸ phasePorts_targets hot _ p hpm)
      · apply straight_append_wellFormed
        · exact literalProgram_wellFormed _ ((circuitWellFormed_adjoint _).mpr (hH _))
        · rw [castFinish_wellFormed]
          exact straight_append_wellFormed _ _ (eraseNetwork_wellFormed n _ hp _)
            (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed]))

theorem measureThen_wellFormed {n R}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor+R))
    (hn : ∀ cursor refs, (next cursor refs).WellFormed) (ws : List Wire) (start : Nat) (refs : List (Fin start)) :
    (measureThen next ws start refs).WellFormed := by
  induction ws generalizing start with
  | nil => exact hn _ _
  | cons w ws ih => simpa only [measureThen,castFinish_wellFormed,Straight.WellFormed] using ih _ _

theorem measuredClear_wellFormed {n} (data : List (ClearPort n))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank hot) (start : Nat) :
    (measuredClear data low hot tree root scratch paths start).WellFormed := by
  rw [measuredClear,castFinish_wellFormed]
  apply measureThen_wellFormed
  intro cursor refs
  rw [castFinish_wellFormed]
  exact fixupProgram_wellFormed data refs low hot tree root scratch paths hl hi hdlow hs hshot

open AndGadget in
 theorem eraseNetwork_residue (n : Nat) (cs : List SplitCell) (start : Nat) :
    residue (eraseNetwork n cs start) = 0 := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simp [eraseNetwork,residue_cast,residue_append,ih,eraseSplit,residue,primitivePhaseCost]

open AndGadget in
 theorem recordLeaf_residue {n base} (ports : List (RecordPort n base)) (scratch row control start : Nat) (hb : base ≤ start) :
    residue (recordLeaf ports scratch row control start hb) = 0 := by
  induction ports with
  | nil => rfl
  | cons p ps ih => simp [recordLeaf,residue_append,mixedCX,residue,tCost,ih]

open AndGadget in
 theorem recordLookup_residue {n base} (ports : List (RecordPort n base)) (scratch : Wire)
    (ops : List RecordLookupOp) (start : Nat) (hb : base ≤ start)
    (hp : ∀ gs, .gates gs ∈ ops → (gs.map primitivePhaseCost).sum = 0) :
    residue (recordLookupProgram ports scratch ops start hb) = 0 := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    have ht := ih (hp := fun gs hgs => hp gs (by simp [hgs]))
    cases op with
    | gates gs => simp [recordLookupProgram,residue_append,residue_literal,hp gs (by simp),ht]
    | leaf row c => simp [recordLookupProgram,residue_append,recordLeaf_residue,ht]
    | erase a b t => simp [recordLookupProgram,residue_cast,residue_append,ht]

open AndGadget in
 theorem recordUnary_phaseFree (tree : UnaryActionTree) (root : Wire) (paths : List Wire) :
    ∀ gs, .gates gs ∈ recordUnaryOps tree root paths → (gs.map primitivePhaseCost).sum = 0 := by
  induction tree generalizing root paths with
  | leaf row => simp [recordUnaryOps]
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp [recordUnaryOps]
    | cons path rest =>
      intro gs hg
      simp only [recordUnaryOps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with (((hg | hg) | hg) | hg) | hg
      · cases hg; simp [computeZeroAnd,primitivePhaseCost]
      · exact ihz path rest gs hg
      · cases hg; simp [primitivePhaseCost]
      · exact iho path rest gs hg
      · rcases hg with hg | hg | hg | hg
        · cases hg; simp [primitivePhaseCost]
        · cases hg; simp [primitivePhaseCost]
        · cases hg
        · cases hg; simp [primitivePhaseCost]

open AndGadget in
 theorem fixupProgram_residue {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) :
    residue (fixupProgram data refs low hot tree root scratch paths) = 0 := by
  unfold fixupProgram
  rw [residue_append,residue_literal_HPFree _ (hotPrepare_hp low hot)]
  simp only [residue_append,residue_literal,residue_cast,eraseNetwork_residue,
    recordLookup_residue _ _ _ _ _ (recordUnary_phaseFree tree root paths),Nat.zero_add]
  simp [List.map_map,Function.comp_def,primitivePhaseCost,Circuit.adjoint,List.map_reverse,Gate.adjoint]

open AndGadget in
 theorem measureThen_residue {n R}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor+R))
    (hn : ∀ cursor refs, residue (next cursor refs) = 0) (ws : List Wire) (start : Nat) (refs : List (Fin start)) :
    residue (measureThen next ws start refs) = 0 := by
  induction ws generalizing start with
  | nil => exact hn _ _
  | cons w ws ih => simpa only [measureThen,residue_cast,residue] using ih _ _

open AndGadget in
 theorem measuredClear_residue {n} (data : List (ClearPort n))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    residue (measuredClear data low hot tree root scratch paths start) = 0 := by
  rw [measuredClear,residue_cast]
  apply measureThen_residue
  intro cursor refs
  rw [residue_cast]
  exact fixupProgram_residue data refs low hot tree root scratch paths

end
end ShorECDLP.Entrant.MeasuredClear

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section

theorem measuredClear_static {n : Nat} (data : List (ClearPort n))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hsc : scratch ∈ data.map ClearPort.target)
    (start : Nat) :
    NaiveChallenge.straightWires (measuredClear data low hot tree root scratch paths start) ⊆
      clearSupport data low hot tree root paths := by
  rw [measuredClear, static_cast]
  apply measureThen_within _ _ (by
    intro cursor refs
    rw [static_cast]
    apply fixupProgram_within
    · simp [clearSupport]
    · simp [clearSupport, hsc]
    · intro i
      have hm : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro i
      have hm : hot i ∈ hotBank hot := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro w hw
      simp [clearSupport, hw]
    · intro w hw
      simp [clearSupport, hw])
  intro w hw
  simp [clearSupport, hw]

end
end ShorECDLP.Entrant.MeasuredClear




namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def low (i : Fin 7) : Wire := 855+i.val
def high : List Wire := List.range' 862 8
def highPaths : List Wire := List.range' 10000 8
def hot (i : Fin 128) : Wire := 1930+i.val

/-- The first data wire remains the phase scratch; the next eight host the hot bank. -/
def recycledHot (i : Fin 128) : Wire := 14116+i.val

theorem recycledHot_source (i : Fin 128) : recycledHot i ∈ sourceSupport := by
  rw [sourceSupport_mem]
  right
  unfold oldWork recycledHot
  have hi := i.isLt
  dsimp only [Wire] at *
  omega

def clearData {n} (ps : List (LookupPort n)) : List (MeasuredClear.ClearPort n) :=
  ps.map fun p => ⟨p.ref,p.value,p.target⟩
@[simp] theorem clearData_targets {n} (ps : List (LookupPort n)) :
    (clearData ps).map MeasuredClear.ClearPort.target = portTargets ps := by
  simp [clearData,portTargets,List.map_map,Function.comp_def]

@[simp] theorem portMask_cons {n} (read : ConstantBit n → Bool) (p : LookupPort n) (ps : List (LookupPort n)) (a : Nat) :
    portMask read (p::ps) a = if read (p.ref a) = p.value then p.target :: portMask read ps a else portMask read ps a := by
  by_cases h : read (p.ref a) = p.value <;> simp [portMask,portTargets,tableBitsMask,h]

theorem port_selected {n} (read : ConstantBit n → Bool) (ps : List (LookupPort n)) (a : Nat)
    (hn : (portTargets ps).Nodup) (p : LookupPort n) (hp : p ∈ ps) :
    decide (p.target ∈ portMask read ps a) = decide (read (p.ref a) = p.value) := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    have hnd : q.target ∉ portTargets qs ∧ (portTargets qs).Nodup := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      have hout : q.target ∉ portMask read qs a := fun h => hnd.1 (tableBitsMask_subset _ _ h)
      by_cases h : read (q.ref a) = q.value <;> simp [h,hout]
    · have hne : p.target ≠ q.target := by
        intro he; apply hnd.1; exact he ▸ List.mem_map.mpr ⟨p,hp,rfl⟩
      have hi := ih hnd.2 hp
      by_cases h : read (q.ref a) = q.value <;> simpa [h,hne] using hi

theorem clear_eq_unload {n} (read : ConstantBit n → Bool) (ps : List (LookupPort n))
    (a : Nat) (q : Wire) (s : BasisState)
    (hc : Clean (portTargets ps) (tableXorState (portMask read ps a) (s q) s)) :
    clearRegister (portTargets ps) s = tableXorState (portMask read ps a) (s q) s := by
  funext w
  by_cases hw : w ∈ portTargets ps
  · exact (clearRegister_clean _ s w hw).trans (hc w hw).symm
  · rw [MeasuredClear.clearRegister_frame _ _ _ hw,tableXorState_outside]
    intro hm
    exact hw (tableBitsMask_subset _ _ hm)

theorem loaded_of_clean_unload {n} (read : ConstantBit n → Bool) (ps : List (LookupPort n))
    (a : Nat) (q : Wire) (s : BasisState) (hn : (portTargets ps).Nodup)
    (hc : Clean (portTargets ps) (tableXorState (portMask read ps a) (s q) s)) :
    ∀ p ∈ ps, s p.target = (s q && decide (read (p.ref a) = p.value)) := by
  intro p hp
  have hz := hc p.target (List.mem_map.mpr ⟨p,hp,rfl⟩)
  simp only [tableXorState,port_selected read ps a hn p hp] at hz
  cases h1 : s p.target <;> cases h2 : s q && decide (read (p.ref a) = p.value) <;> simp_all

/-- Literal state assertions are framed over the clean phase-fixup bank. -/
def HotAvoid {n} : WInstr n → Prop
  | .literal p => ∀ i, hot i ∉ ECDSAAdd.wires p
  | .lookup _ ps => ∀ i, hot i ∉ portTargets ps

theorem reference_preserves {n} (read : ConstantBit n → Bool) (code : WCode n) (a : Nat)
    (hp : ∀ i ∈ code, PlacedPair windowBits windowPaths windowRoot i)
    (hh : ∀ i ∈ code, HotAvoid i)
    (st : ECDSAAdd.State) (hs : SimulationValid windowBits windowPaths windowRoot a st)
    (hc : MeasuredClear.HotClean hot st.basis) (m : List Bool) :
    SimulationValid windowBits windowPaths windowRoot a
        (ECDSAAdd.run ((specialize code a).instantiate read) m st) ∧
      MeasuredClear.HotClean hot (ECDSAAdd.run ((specialize code a).instantiate read) m st).basis := by
  induction code generalizing st m with
  | nil => exact ⟨hs,hc⟩
  | cons i code ih =>
    have ht := fun j hj => hp j (List.mem_cons_of_mem i hj)
    have hht := fun j hj => hh j (List.mem_cons_of_mem i hj)
    have hi := hp i (by simp)
    have hhi := hh i (by simp)
    simp only [specialize,List.flatMap_cons,ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.run_append]
    cases i with
    | literal p =>
      simp only [WInstr.specialize,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      apply ih ht hht
      · exact literal_preserves_simulation (n := n) p _ _ _ _ hi st hs _
      · intro i
        rw [ECDSAAdd.run_preserves_outside p _ st (hot i) (hhi i)]
        exact hc i
    | lookup control ps =>
      have hip := hi
      dsimp only [PlacedPair] at hip
      have hmemq : lookupRoot windowRoot control ∈ windowRoot :: lookupRoot windowRoot control :: windowBits ++ windowPaths := by simp
      have hmemr : windowRoot ∈ windowRoot :: lookupRoot windowRoot control :: windowBits ++ windowPaths := by simp
      have hqa : lookupRoot windowRoot control ∉ portTargets (ps.take 258) := by
        intro hm; rw [portTargets,List.map_take] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemq (List.take_subset _ _ hm)
      have hqb : lookupRoot windowRoot control ∉ portTargets (ps.drop 258) := by
        intro hm; rw [portTargets,List.map_drop] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemq (List.drop_subset _ _ hm)
      have hra : windowRoot ∉ portTargets (ps.take 258) := by
        intro hm; rw [portTargets,List.map_take] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemr (List.take_subset _ _ hm)
      have hspec (m' : List Bool) := pairPort_specialize_run_control read control (ps.take 258) (ps.drop 258)
        a windowRoot m' st hip.2.1 hip.2.2.1 hqa hqb hra hs.2.2
      simp only [List.take_append_drop] at hspec
      rw [WInstr.specialize,hspec]
      apply ih ht hht
      · exact pair_lookup_preserves_simulation read control ps _ _ _ _ hi st hs
      · intro i
        have hout₁ : hot i ∉ portMask read (ps.take 258) a := fun hm => hhi i (by
          have h' := tableBitsMask_subset _ _ hm
          rw [portTargets,List.map_take] at h'
          exact List.take_subset _ _ h')
        have hout₂ : hot i ∉ portMask read (ps.drop 258) a := fun hm => hhi i (by
          have h' := tableBitsMask_subset _ _ hm
          rw [portTargets,List.map_drop] at h'
          exact List.drop_subset _ _ h')
        change tableXorState (portMask read (ps.drop 258) a) (st.basis (lookupRoot windowRoot control))
          (tableXorState (portMask read (ps.take 258) a) (st.basis (lookupRoot windowRoot control)) st.basis) (hot i) = false
        rw [tableXorState_outside _ _ _ _ hout₂,tableXorState_outside _ _ _ _ hout₁]
        exact hc i


end
end ShorECDLP.Entrant.WEXUnlookup


/-! ### Masked-site kinds

A masked site either clears the shared constant source word (pool positions 0..255, guarded by the generic
flag) or one of the comparison scratch words (guarded by the window root).  Both clears recycle the 128 wires
after the head of their own target word as the one-hot bank, so every geometric side condition of the
recycled measured clear reduces to the bounds below. -/
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def scratch {n} (site : MaskedSite n) : Wire := (portTargets site.ports).headD 0

def clearHot {n} (site : MaskedSite n) : Fin 128 → Wire :=
  if site.guard = windowRoot then scrSiteHot else recycledHot

def SiteKind {n} (site : MaskedSite n) : Prop :=
  (portTargets site.ports = List.range' 14115 256 ∧ site.guard = 14113) ∨
    (portTargets site.ports = WEX.scrWires ∧ site.guard = windowRoot)

theorem kind_facts {n} (site : MaskedSite n) (hk : SiteKind site) :
    (portTargets site.ports).Nodup ∧ (∀ w ∈ portTargets site.ports, 14115 ≤ w ∧ oldWork w) ∧
    (∀ i : Fin 128, clearHot site i = scratch site + 1 + i.val) ∧
    (∀ i, clearHot site i ∈ portTargets site.ports) ∧
    scratch site ∈ portTargets site.ports ∧
    (site.guard = 14113 ∨ site.guard = 10015) ∧ site.ports.length ≤ 516 := by
  have hlen : site.ports.length = (portTargets site.ports).length := by simp [portTargets]
  rcases hk with ⟨ht,hg⟩ | ⟨ht,hg⟩
  · have hc : clearHot site = recycledHot := by
      unfold clearHot
      rw [hg,if_neg (by decide)]
    have hs : scratch site = 14115 := by rw [scratch,ht]; decide +kernel
    rw [hc,hs]
    refine ⟨by rw [ht]; exact List.nodup_range',?_,?_,?_,?_,Or.inl hg,?_⟩
    · intro w hw
      rw [ht,List.mem_range'_1] at hw
      unfold oldWork
      dsimp only [Wire] at *
      omega
    · intro i
      simp only [recycledHot]
    · intro i
      rw [ht,List.mem_range'_1]
      have hi := i.isLt
      simp only [recycledHot]
      dsimp only [Wire] at *
      omega
    · rw [ht,List.mem_range'_1]
      omega
    · rw [hlen,ht,List.length_range']
      omega
  · have hc : clearHot site = scrSiteHot := by
      unfold clearHot
      rw [hg,if_pos rfl]
    have hs : scratch site = 14373 := by rw [scratch,ht]; exact scrWires_head
    rw [hc,hs]
    refine ⟨by rw [ht]; exact WEX.scrWires_nodup,?_,?_,?_,?_,Or.inr hg,?_⟩
    · intro w hw
      rw [ht,scrWires_eq] at hw
      simp only [List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,
        or_false] at hw
      unfold oldWork
      dsimp only [Wire] at *
      omega
    · intro i
      simp only [scrSiteHot]
    · intro i
      rw [ht]
      exact scrSiteHot_mem i
    · rw [ht,scrWires_eq]
      simp
    · rw [hlen,ht,scrWires_eq]
      simp

theorem low_lt (i : Fin 7) : low i < 862 := by
  have hi := i.isLt
  simp only [low]
  dsimp only [Wire] at *
  omega

/-- The guard, the low address wires, the high tree and its paths all lie below the pool. -/
theorem tree_below {n} (site : MaskedSite n) (hk : SiteKind site) (H P : List Wire)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 871) (hP : ∀ w ∈ P, 10000 ≤ w ∧ w < 10015) :
    ∀ w ∈ site.guard :: List.ofFn low ++ H ++ P, w < 14115 := by
  have hg := (kind_facts site hk).2.2.2.2.2.1
  intro w hw
  simp only [List.mem_append,List.mem_cons] at hw
  rcases hw with ((h | h) | h) | h
  · rw [h]; rcases hg with e | e <;> rw [e] <;> decide
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    have := low_lt i
    dsimp only [Wire] at *
    omega
  · have := hH w h
    dsimp only [Wire] at *
    omega
  · have := hP w h
    dsimp only [Wire] at *
    omega

theorem tree_geom {n} (site : MaskedSite n) (hk : SiteKind site) (H P : List Wire)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 871) (hP : ∀ w ∈ P, 10000 ≤ w ∧ w < 10015) (hnd : (H ++ P).Nodup) :
    (site.guard :: H ++ P).Nodup := by
  have hg := (kind_facts site hk).2.2.2.2.2.1
  rw [List.cons_append,List.nodup_cons]
  refine ⟨fun h => ?_,hnd⟩
  rcases List.mem_append.mp h with h | h
  · have := hH _ h
    rcases hg with e | e <;> rw [e] at this <;> dsimp only [Wire] at this <;> omega
  · have := hP _ h
    rcases hg with e | e <;> rw [e] at this <;> dsimp only [Wire] at this <;> omega

theorem clear_coherent_gen {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hk : SiteKind site)
    (bitsW H P : List Wire)
    (hsplit : ∀ s : BasisState, 128 * (tableAddressTree H 0 1).routeLabel s + MeasuredClear.hotAddress low s =
      tableAddressValue bitsW s)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 871) (hP : ∀ w ∈ P, 10000 ≤ w ∧ w < 10015)
    (hPW : ∀ w ∈ P, w ∈ windowPaths) (hindex : (tableAddressTree H 0 1).indexWires.dedup = H)
    (hnd : (H ++ P).Nodup) (hhl : H.length ≤ P.length)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((MeasuredClear.measuredClear (clearData site.ports) low (clearHot site)
        (tableAddressTree H 0 1) site.guard (scratch site) P start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => MeasuredClear.HotClean hot s ∧ Clean windowPaths s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue bitsW s)) = p.value))) := by
  obtain ⟨hn,hbd,hhot,hmem,hsm,-,-⟩ := kind_facts site hk
  have below := tree_below site hk H P hH hP
  have hl := tableAddressTree_layout H P site.guard 0 1 hhl (tree_geom site hk H P hH hP hnd)
  have hc := MeasuredClear.measuredClear_recycled_coherent (clearData site.ports) read low (clearHot site)
    (tableAddressTree H 0 1) site.guard (scratch site) P hl
    (by intro i j he; apply Fin.ext; rw [hhot i,hhot j] at he; dsimp only [Wire] at he; omega)
    (by
      intro i j he
      have h1 := (hbd _ (hmem j)).1
      have h2 := low_lt i
      rw [← he] at h1
      dsimp only [Wire] at *
      omega)
    (by
      apply List.disjoint_left.mpr
      intro w hw hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      rw [hindex] at hm
      have h1 := below _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto)
      have h2 := (hbd _ (hmem i)).1
      dsimp only [Wire] at *
      omega)
    (by
      rw [hindex]
      intro hm
      have h1 := below _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto)
      have h2 := (hbd _ hsm).1
      dsimp only [Wire] at *
      omega)
    (by
      intro hm
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      rw [hhot i] at hi
      dsimp only [Wire] at hi
      omega)
    (by simpa using hn)
    (by
      rw [clearData_targets,hindex]
      intro w hw hm
      have h1 := below w hw
      have h2 := (hbd _ hm).1
      dsimp only [Wire] at *
      omega)
    (by rw [clearData_targets]; exact hmem)
    start history
  simp only [clearData_targets] at hc
  obtain ⟨cs,aligned,mass⟩ := hc
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  apply hb s
  refine ⟨?_,?_⟩
  · intro w hw
    exact hs.2.1 w (hPW w hw)
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    simpa [MeasuredClear.LoadedClear,clearData,hsplit] using hs.2.2 q hq

theorem clear_wellFormed_gen {n} (site : MaskedSite n) (hk : SiteKind site) (H P : List Wire)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 871) (hP : ∀ w ∈ P, 10000 ≤ w ∧ w < 10015)
    (hindex : (tableAddressTree H 0 1).indexWires.dedup = H)
    (hnd : (H ++ P).Nodup) (hhl : H.length ≤ P.length) (start : Nat) :
    (MeasuredClear.measuredClear (clearData site.ports) low (clearHot site)
        (tableAddressTree H 0 1) site.guard (scratch site) P start).WellFormed := by
  obtain ⟨-,hbd,hhot,hmem,hsm,-,-⟩ := kind_facts site hk
  have below := tree_below site hk H P hH hP
  apply MeasuredClear.measuredClear_wellFormed
  · exact tableAddressTree_layout H P site.guard 0 1 hhl (tree_geom site hk H P hH hP hnd)
  · intro i j he; apply Fin.ext; rw [hhot i,hhot j] at he; dsimp only [Wire] at he; omega
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low_lt i
    rw [← he] at h1
    dsimp only [Wire] at *
    omega
  · rw [hindex]
    intro hm
    have h1 := below _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto)
    have h2 := (hbd _ hsm).1
    dsimp only [Wire] at *
    omega
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    rw [hhot i] at hi
    dsimp only [Wire] at hi
    omega

theorem clear_slots_gen {n} (site : MaskedSite n) (H P : List Wire)
    (hl : (tableAddressTree H 0 1).Layout site.guard P) (start : Nat) :
    (MeasuredClear.measuredClear (clearData site.ports) low (clearHot site)
        (tableAddressTree H 0 1) site.guard (scratch site) P start).gateSlots =
      512 * site.ports.length * 2 ^ H.length + 10 * (tableAddressTree H 0 1).internalNodes + 1020 := by
  rw [MeasuredClear.measuredClear_slots _ _ _ _ _ _ _ hl,MeasuredClear.addressTree_leaves]
  simp [clearData]

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def clearProgram {n} (site : MaskedSite n) (start : Nat) :=
  MeasuredClear.measuredClear (clearData site.ports) low (clearHot site) (tableAddressTree high 0 1)
    site.guard (scratch site) highPaths start

def clearSource {n} (read : ConstantBit n → Bool) (site : MaskedSite n) : AdaptiveCircuit :=
  (clearProgram site 0).instantiate read Fin.elim0

theorem clearProgram_run {n} (read : ConstantBit n → Bool) (site : MaskedSite n)
    (start : Nat) (history : Fin start → Bool) :
    ((clearProgram site start).instantiate read history).run = (clearSource read site).run := by
  simp only [clearProgram,clearSource,MeasuredClear.measuredClear_run]

def blockRecords {n} : Block n → Nat
  | .plain code => codeRecords windowBits windowPaths windowRoot (normalizeW code)
  | .masked site => codeRecords windowBits windowPaths windowRoot (normalizeW site.prefix) +
      site.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) site.guard highPaths)+127)

def blockProgram {n} (b : Block n) (start : Nat) : Straight n start (start+blockRecords b) :=
  match b with
  | .plain code => compile windowBits windowPaths windowRoot (normalizeW code) start
  | .masked site => castFinish (by simp [blockRecords,clearData]; omega)
      ((compile windowBits windowPaths windowRoot (normalizeW site.prefix) start).append
        (clearProgram site (start+codeRecords windowBits windowPaths windowRoot (normalizeW site.prefix))))

def records {n} : Code n → Nat
  | [] => 0
  | b::code => blockRecords b + records code

def program {n} : (code : Code n) → (start : Nat) → Straight n start (start+records code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [records]; omega)
      ((blockProgram b start).append (program code (start+blockRecords b)))

def blockSource {n} (read : ConstantBit n → Bool) : Block n → AdaptiveCircuit
  | .plain code => source read windowBits windowPaths windowRoot (normalizeW code)
  | .masked site => (source read windowBits windowPaths windowRoot (normalizeW site.prefix)).seq
      (clearSource read site)

def sourceCode {n} (read : ConstantBit n → Bool) : Code n → AdaptiveCircuit
  | [] => .done
  | b::code => (blockSource read b).seq (sourceCode read code)

theorem blockProgram_run {n} (read : ConstantBit n → Bool) (b : Block n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram b start).instantiate read history).run = (blockSource read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | masked site =>
    rw [blockProgram,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearProgram_run read site _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSource,AdaptiveCircuit.run_seq]

theorem program_run {n} (read : ConstantBit n → Bool) (code : Code n)
    (start : Nat) (history : Fin start → Bool) :
    ((program code start).instantiate read history).run = (sourceCode read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [program,castFinish_instantiate,append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,blockProgram_run]
    simp only [sourceCode,AdaptiveCircuit.run_seq]

structure SiteGeometry {n} (site : MaskedSite n) : Prop where
  placed : ∀ i ∈ site.code, Placed windowBits windowPaths windowRoot i
  bank : ∀ i ∈ site.code, HotAvoid i
  kind : SiteKind site

/-- The address split uses the original little-endian WEX address. -/
theorem splitAddress (s : BasisState) :
    128*(tableAddressTree high 0 1).routeLabel s + MeasuredClear.hotAddress low s =
      tableAddressValue windowBits s := by
  have h := MeasuredClear.splitAddress_value low high s
  have he : [MeasuredClear.lowN low 0,MeasuredClear.lowN low 1,MeasuredClear.lowN low 2,MeasuredClear.lowN low 3,MeasuredClear.lowN low 4,MeasuredClear.lowN low 5,MeasuredClear.lowN low 6]++high = windowBits := by decide +kernel
  rw [he] at h
  exact h

theorem clearProgram_coherent {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeometry site)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((clearProgram site start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => MeasuredClear.HotClean hot s ∧ Clean windowPaths s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue windowBits s)) = p.value))) := by
  unfold clearProgram
  exact clear_coherent_gen read site hg.kind windowBits high highPaths splitAddress
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,windowPaths,List.mem_range'_1] at hw ⊢; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) (by decide +kernel) (by decide +kernel) start history

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem normalized_simulation {n} (read : ConstantBit n → Bool) (code : WCode n)
    (hp : ∀ i ∈ code, PlacedPair windowBits windowPaths windowRoot i) :
    ∃ cs : List ℂ, List.Forall₂ (SimulationBranch read code windowBits windowPaths windowRoot)
      (source read windowBits windowPaths windowRoot (normalizeW code)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cs,aligned,mass⟩ := pair_source_simulation read windowBits windowPaths windowRoot
    (by simp [windowBits,windowPaths]) (normalizeW code) (pair_placed_normalize _ _ _ _ hp)
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb
  obtain ⟨m,hm,hb⟩ := hb
  refine ⟨m,by simpa [literalRecords_normalize] using hm,?_⟩
  intro address st hs
  simpa only [specialize_normalize_run] using hb address st hs

theorem masked_run {n} (read : ConstantBit n → Bool) (site : MaskedSite n)
    (hg : SiteGeometry site) (a : Nat) (st : ECDSAAdd.State) (m : List Bool)
    (hs : SimulationValid windowBits windowPaths windowRoot a st)
    (hh : MeasuredClear.HotClean hot st.basis) :
    ECDSAAdd.run ((specialize site.code a).instantiate read) m st =
      let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
      ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩ := by
  have hp : ∀ i ∈ site.prefix, PlacedPair windowBits windowPaths windowRoot i := by
    intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have hhot : ∀ i ∈ site.prefix, HotAvoid i := by
    intro i hi; exact hg.bank i (List.mem_append_left _ hi)
  have hnext := reference_preserves read site.prefix a hp hhot st hs hh m
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  have hroot : site.guard ∉ portTargets site.ports := List.disjoint_left.mp hlast.2.2 (by simp [lookupRoot])
  simp only [MaskedSite.code,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
    ECDSAAdd.run_append,ECDSAAdd.run_take]
  simpa [specialize,WInstr.specialize] using portTemplate_run read (some site.guard) site.ports a windowRoot
    (m.drop (ECDSAAdd.measurementCount ((specialize site.prefix a).instantiate read)))
    (ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st)
    hlast.2.1 hroot hnext.1.2.2

def BlockSimulation {n} (read : ConstantBit n → Bool) (block : Block n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, SimulationValid windowBits windowPaths windowRoot address st →
      MeasuredClear.HotClean hot st.basis → BlockSafe read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference read address block) m st)

def BlockGeometry {n} : Block n → Prop
  | .plain code => (∀ i ∈ code, PlacedPair windowBits windowPaths windowRoot i) ∧
      (∀ i ∈ code, HotAvoid i)
  | .masked site => SiteGeometry site

theorem block_simulation {n} (read : ConstantBit n → Bool) (block : Block n)
    (hg : BlockGeometry block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimulation read block) (blockSource read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    obtain ⟨cs,aligned,mass⟩ := normalized_simulation read code hg.1
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    exact ⟨m,hm,fun address st hs _ _ => hb address st hs⟩
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair windowBits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hhot : ∀ i ∈ site.prefix, HotAvoid i := by
      intro i hi; exact hg.bank i (List.mem_append_left _ hi)
    obtain ⟨preCs,preAligned,preMass⟩ := normalized_simulation read site.prefix hp
    obtain ⟨cs,aligned,mass⟩ := clearProgram_coherent read site hg 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSource,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block.code,MaskedSite.code,literalRecords] using hm
      · intro a st hs hh hsafe
        let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
        have hn := reference_preserves read site.prefix a hp hhot st hs hh m
        have hrun := masked_run read site hg a st m hs hh
        have hclean : Clean (portTargets site.ports)
            (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
        have hvalid : MeasuredClear.HotClean hot next.basis ∧ Clean windowPaths next.basis ∧
            ∀ p ∈ site.ports, next.basis p.target = (next.basis site.guard &&
              decide (read (p.ref (tableAddressValue windowBits next.basis)) = p.value)) := by
          refine ⟨hn.2,hn.1.1,?_⟩
          rw [hn.1.2.1]
          exact loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
        have hclear : b₂.kraus (ket next.basis) =
            c₂ • ket (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          rw [← clear_eq_unload read site.ports a site.guard next.basis hclean]
          simpa [ket] using h₂ next.basis hvalid
        have hsigned : b₂.kraus (Bridge.signedKet next) = c₂ •
            Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st) := by
          rw [hrun]
          change b₂.kraus (Bridge.signedKet next) = c₂ • Bridge.signedKet
            ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩
          cases hphase : next.phase <;> simp [Bridge.signedKet,hphase,hclear,map_neg]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [h₁ a st hs,map_smul,hsigned]
        simp [smul_smul,blockReference,Block.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem block_placed {n} (b : Block n) (hg : BlockGeometry b) :
    (∀ i ∈ b.code, PlacedPair windowBits windowPaths windowRoot i) ∧
      (∀ i ∈ b.code, HotAvoid i) := by
  cases b with
  | plain code => exact hg
  | masked site => exact ⟨fun i hi => placed_implies_pair _ _ _ _ (hg.placed i hi),hg.bank⟩

def Simulation {n} (read : ConstantBit n → Bool) (code : Code n)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase code) ∧
    ∀ a st, SimulationValid windowBits windowPaths windowRoot a st →
      MeasuredClear.HotClean hot st.basis → Safe read a code st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference read a code) m st)

theorem source_simulation {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b) :
    ∃ cs : List ℂ, List.Forall₂ (Simulation read code) (sourceCode read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1],.cons ?_ .nil,by simp⟩
    exact ⟨[],rfl,fun a st _ _ _ => by simp [reference,erase,specialize,ECDSAAdd.ShorPort.Tmpl.instantiate,ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁,h₁,mass₁⟩ := block_simulation read b (hg b (by simp))
    obtain ⟨cs₂,h₂,mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    have geo := block_placed b (hg b (by simp))
    refine ⟨coherentSeqCoefficients cs₁ cs₂,?_,?_⟩
    · rw [sourceCode,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁,len₁,run₁⟩ := hb₁
      obtain ⟨m₂,len₂,run₂⟩ := hb₂
      refine ⟨m₁++m₂,?_,?_⟩
      · simp [erase,List.length_append,len₁,len₂]
      · intro a st hs hh hsafe
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference read a b) :=
          len₁.trans (specialize_counts read b.code a).2.symm
        have hn := reference_preserves read b.code a geo.1 geo.2 st hs hh m₁
        change SimulationValid windowBits windowPaths windowRoot a
            (ECDSAAdd.run (blockReference read a b) m₁ st) ∧ MeasuredClear.HotClean hot
            (ECDSAAdd.run (blockReference read a b) m₁ st).basis at hn
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hh hsafe.1,map_smul,run₂ a (ECDSAAdd.run (blockReference read a b) m₁ st) hn.1 hn.2 (hsafe.2 m₁ hm),
          reference_cons,run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass,mass₁,mass₂]
      norm_num

/-- All addresses share one normalized branch coefficient list. -/
theorem program_coherent {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe read (tableAddressValue windowBits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference read (tableAddressValue windowBits s) code) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result)
      (fun s => Clean windowPaths s ∧ s windowRoot = true ∧ MeasuredClear.HotClean hot s ∧ Valid s) := by
  obtain ⟨cs,aligned,mass⟩ := source_simulation read code hg
  refine ⟨cs,?_,mass⟩
  rw [program_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m,_,h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨hs.1,rfl,hs.2.1⟩ hs.2.2.1 (hsafe s hs.2.2.2)
  rw [Bridge.signedKet_false,hrun s hs.2.2.2 m,Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.WEXUnlookup



namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] ECDSAAdd.run

def tightRow : Code 32768 := [.plain (wLiteral [.X 838])] ++ finite streamLayout probeRows ++
  [.plain (wLiteral [.X 838])]
@[simp] theorem erase_tightRow : erase tightRow = tightReferenceRow probeRows := by
  unfold tightRow
  rw [erase_append,erase_append,erase_finite,erase_plain]
  rfl

/-- The parent's block row (scratch unloads as reference traversals); kept for its safety proof. -/
def portFused3 : Code 32768 := [.plain (portPrefixCode probeRows)] ++ generic streamLayout probeRows ++
  [.plain (portSuffixCodeD probeRows)]

def row3 : Code 32768 := [.plain (wLiteral [.X 838])] ++ portFused3 ++
  [.plain (wLiteral [.X 838])]

theorem row3_masked_tight (site : MaskedSite 32768) (hb : Block.masked site ∈ row3) :
    Block.masked site ∈ tightRow := by
  simpa [row3,tightRow,portFused3,finite] using hb


theorem hot_outside_source (i : Fin 128) : hot i ∉ WEX.sourceSupport := by
  rw [sourceSupport_mem]
  simp only [fixedPort,oldWork,hot]
  omega

theorem row_hotavoid : ∀ i ∈ clearReferenceRow probeRows, HotAvoid i := by
  intro i hi
  cases i with
  | literal p =>
    have hs : ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
      exact clearReferenceRow_literal_source p hi
    intro j hj
    exact hot_outside_source j (List.mem_toFinset.mp (hs hj))
  | lookup c ps =>
    have hn : WInstr.lookup c ps ∈ normalizeW (clearReferenceRow probeRows) := List.mem_map.mpr ⟨.lookup c ps,hi,rfl⟩
    have h := List.all_eq_true.mp clearReferenceRow_sourceLookupOK _ hn
    have h : (∀ q ∈ c, fixedPort q ∨ oldWork q) ∧
        (∀ w ∈ portTargets ps, fixedPort w ∨ oldWork w) := by
      simpa [sourceLookupOK,List.all_eq_true] using h
    intro j hj
    exact hot_outside_source j ((sourceSupport_mem _).mpr (h.2 _ hj))

theorem block_mem_erase {n} (code : Code n) (b : Block n) (hb : b ∈ code) (i : WInstr n) (hi : i ∈ b.code) :
    i ∈ erase code := List.mem_flatMap.mpr ⟨b,hb,hi⟩

def Shared {n} : Block n → Prop
  | .plain _ => True
  | .masked site => portTargets site.ports = List.range' 14115 256 ∧ site.guard = 14113

theorem const_shared {n} (r : List Wire) (refs : Nat → Nat → ConstantBit n) :
    Shared (.masked (constSite streamLayout r refs)) := by
  change portTargets (indexedPorts (streamLayout.recoveryConstant r).src refs true) = _ ∧ _
  rw [indexed_targets]
  change streamLayout.dialogPool.take 256 = List.range' 14115 256 ∧ streamLayout.core.generic = 14113
  constructor <;> decide +kernel

@[simp] theorem shared_plain {n} (code : WCode n) : Shared (.plain code) := True.intro

theorem row3_shared : ∀ b ∈ row3, Shared b := by
  simp [row3,portFused3,generic,core,recovery,constAdd,const_shared]

theorem tightRow_safe_of_boundary (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s)) :
    Safe read address tightRow ⟨false,s⟩ := by
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro m _
  have he : ECDSAAdd.run (blockReference read address (.plain (wLiteral [.X 838]))) m ⟨false,s⟩ =
      ⟨false,flipInfinity s⟩ := by
    simp only [blockReference,Block.code,specialize_literal,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    exact flip_run _ _
  rw [he]
  apply safe_append _ _ _ _ _
  · exact finite_safe read streamLayout streamLayout_widths streamLayout_nodup probeRows address R hc hr
      h₁ h₂ hD hDo true ⟨false,flipInfinity s⟩ hs
  · intro m hm
    exact safe_plain _ _ _ _

theorem safe_tail_swap {n} (read : ConstantBit n → Bool) (address : Nat) (p q x : WCode n) (pre : Code n)
    (st : ECDSAAdd.State) (h : Safe read address (pre ++ [Block.plain p,Block.plain x]) st) :
    Safe read address (pre ++ [Block.plain q,Block.plain x]) st := by
  induction pre generalizing st with
  | nil => exact ⟨True.intro,fun _ _ => ⟨True.intro,fun _ _ => True.intro⟩⟩
  | cons b pre ih =>
    simp only [List.cons_append,Safe] at h ⊢
    exact ⟨h.1,fun m hm => ih _ (h.2 m hm)⟩

theorem safe_head_swap_run {n} (read : ConstantBit n → Bool) (address : Nat) (x p q : WCode n) (rest : Code n)
    (st : ECDSAAdd.State)
    (hrec : ECDSAAdd.measurementCount ((specialize q address).instantiate read) =
      ECDSAAdd.measurementCount ((specialize p address).instantiate read))
    (hrun : ∀ k m, ECDSAAdd.run ((specialize q address).instantiate read) m
        (ECDSAAdd.run ((specialize x address).instantiate read) k st) =
      ECDSAAdd.run ((specialize p address).instantiate read) m
        (ECDSAAdd.run ((specialize x address).instantiate read) k st))
    (h : Safe read address (Block.plain x :: Block.plain p :: rest) st) :
    Safe read address (Block.plain x :: Block.plain q :: rest) st := by
  simp only [Safe] at h ⊢
  refine ⟨h.1, fun k hk => ⟨True.intro, fun m hm => ?_⟩⟩
  have hm' : m.length = ECDSAAdd.measurementCount ((specialize p address).instantiate read) := hm.trans hrec
  have h3 := (h.2 k hk).2 m hm'
  have e := hrun k m
  simp only [blockReference, Block.code] at h3 ⊢
  rw [e]
  exact h3

theorem row3_safe_of_boundary (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s)) :
    Safe read address row3 ⟨false,s⟩ := by
  have h := tightRow_safe_of_boundary read address R hc hr h₁ h₂ hD hDo s hs
  have e₁ : tightRow = Block.plain (wLiteral [.X 838]) ::
      Block.plain (prefixCode streamLayout probeRows) ::
        (generic streamLayout probeRows ++ [Block.plain (suffixCode streamLayout probeRows)] ++
          [Block.plain (wLiteral [.X 838])]) := by
    simp [tightRow,finite,List.append_assoc]
  rw [e₁] at h
  have hop := row_opposite read probeRows address hc hr h₁
  have h' := safe_head_swap_run read address _ _ (WEX.portPrefixCode probeRows) _ ⟨false,s⟩
    (WEX.portPrefix_records read probeRows address)
    (fun k m => by
      have he : ECDSAAdd.run ((specialize (wLiteral (n := 32768) [.X 838]) address).instantiate read) k ⟨false,s⟩ =
          ⟨false,flipInfinity s⟩ := by
        simp only [specialize_literal,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
        exact flip_run _ _
      rw [he]
      exact WEX.portPrefix_run read probeRows address hop m _
        (fun w hw => (ECDSAAdd.Arithmetic.regValue_zero _ _).mp hs.clean w (WEX.scrWires_pool w hw))) h
  have e₂ : Block.plain (wLiteral [.X 838]) :: Block.plain (WEX.portPrefixCode probeRows) ::
        (generic streamLayout probeRows ++ [Block.plain (suffixCode streamLayout probeRows)] ++
          [Block.plain (wLiteral [.X 838])]) =
      ([Block.plain (wLiteral [.X 838])] ++ Block.plain (WEX.portPrefixCode probeRows) ::
        generic streamLayout probeRows) ++
        [Block.plain (suffixCode streamLayout probeRows),Block.plain (wLiteral [.X 838])] := by
    simp [List.append_assoc]
  have e₃ : row3 = ([Block.plain (wLiteral [.X 838])] ++ Block.plain (WEX.portPrefixCode probeRows) ::
        generic streamLayout probeRows) ++
        [Block.plain (portSuffixCodeD probeRows),Block.plain (wLiteral [.X 838])] := by
    simp [row3,portFused3,List.append_assoc]
  rw [e₂] at h'
  rw [e₃]
  exact safe_tail_swap read address _ _ _ _ _ h'

/-- The three literal comparisons before the scratch site. -/
def scrHead : WCode 32768 := wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
  wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect)

/-- The entry comparisons form a masked site: their scratch unload becomes a measured clear. -/
def portFused : Code 32768 := [.plain scrHead,.masked (WEX.scrInSite probeRows),
    .plain (wLiteral (pointDialogGenericFlag streamLayout))] ++ generic streamLayout probeRows ++
  [.plain (portSuffixCodeE probeRows)]

theorem erase_portFused : erase portFused = WEX.portFinite5 probeRows := by
  unfold portFused
  rw [erase_append,erase_append,erase_generic,erase_plain]
  simp only [erase,List.flatMap_cons,List.flatMap_nil,Block.code,List.append_nil,WEX.portFinite5,
    WEX.portPrefixCode4,scrHead,List.append_assoc]

def row : Code 32768 := [.plain (wLiteral [.X 838])] ++ portFused ++
  [.plain (wLiteral [.X 838])]

@[simp] theorem erase_row : erase row = clearReferenceRow probeRows := by
  unfold row
  rw [erase_append,erase_append,erase_portFused,erase_plain,clearReferenceRow_eq]

theorem row_masked (site : MaskedSite 32768) (hb : Block.masked site ∈ row) :
    Block.masked site ∈ row3 ∨ site = WEX.scrInSite probeRows := by
  simp only [row,portFused,row3,portFused3,List.mem_append,List.mem_cons,List.not_mem_nil,
    Block.masked.injEq,reduceCtorEq,or_false,false_or] at hb ⊢
  tauto

theorem scr_placed (bits : List Wire)
    (hp : ∀ i ∈ (WEX.scrInSite probeRows).code, PlacedPair bits windowPaths windowRoot i) :
    ∀ i ∈ (WEX.scrInSite probeRows).code, Placed bits windowPaths windowRoot i := by
  intro i hi
  have hpp := hp i hi
  cases i with
  | literal q => exact hpp
  | lookup c ps =>
    have hps : ps = WEX.scrInPorts probeRows := by
      rw [WEX.scrInSite_code] at hi
      simp [wLiteral] at hi
      tauto
    refine ⟨hpp.1,?_,hpp.2.2.2⟩
    rw [hps,WEX.scrInPorts_targets]
    exact WEX.scrWires_nodup

theorem safe_split_masked {n} (read : ConstantBit n → Bool) (address : Nat) (x A F P : WCode n)
    (S : MaskedSite n) (rest : Code n) (st : ECDSAAdd.State)
    (hrec : ECDSAAdd.measurementCount ((specialize P address).instantiate read) =
      ECDSAAdd.measurementCount ((specialize A address).instantiate read) +
      ECDSAAdd.measurementCount ((specialize S.code address).instantiate read) +
      ECDSAAdd.measurementCount ((specialize F address).instantiate read))
    (hrun : ∀ k a m f, a.length = ECDSAAdd.measurementCount ((specialize A address).instantiate read) →
      m.length = ECDSAAdd.measurementCount ((specialize S.code address).instantiate read) →
      ECDSAAdd.run ((specialize P address).instantiate read) (a ++ m ++ f)
          (ECDSAAdd.run ((specialize x address).instantiate read) k st) =
        ECDSAAdd.run ((specialize F address).instantiate read) f
          (ECDSAAdd.run ((specialize S.code address).instantiate read) m
            (ECDSAAdd.run ((specialize A address).instantiate read) a
              (ECDSAAdd.run ((specialize x address).instantiate read) k st))))
    (hsafe : ∀ k a, BlockSafe read address (Block.masked S)
      (ECDSAAdd.run ((specialize A address).instantiate read) a
        (ECDSAAdd.run ((specialize x address).instantiate read) k st)))
    (h : Safe read address (Block.plain x :: Block.plain P :: rest) st) :
    Safe read address (Block.plain x :: Block.plain A :: Block.masked S :: Block.plain F :: rest) st := by
  simp only [Safe] at h ⊢
  refine ⟨h.1,fun k hk => ⟨True.intro,fun a ha => ⟨hsafe k a,fun m hm => ⟨True.intro,fun f hf => ?_⟩⟩⟩⟩
  simp only [blockReference,Block.code] at h hk ha hm hf ⊢
  have h3 := (h.2 k hk).2 (a ++ m ++ f) (by simp only [List.length_append,ha,hm,hf,hrec])
  rw [hrun k a m f ha hm] at h3
  exact h3

theorem row_safe_of_boundary (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s))
    (hroot : s windowRoot = true) :
    Safe read address row ⟨false,s⟩ := by
  have h := row3_safe_of_boundary read address R hc hr h₁ h₂ hD hDo s hs
  have e3 : row3 = Block.plain (wLiteral [.X 838]) :: Block.plain (WEX.portPrefixCode probeRows) ::
      (generic streamLayout probeRows ++ [Block.plain (portSuffixCodeD probeRows),Block.plain (wLiteral [.X 838])]) := by
    simp [row3,portFused3,List.append_assoc]
  have e4 : row = Block.plain (wLiteral [.X 838]) :: Block.plain scrHead :: Block.masked (WEX.scrInSite probeRows) ::
      Block.plain (wLiteral (pointDialogGenericFlag streamLayout)) ::
      (generic streamLayout probeRows ++ [Block.plain (portSuffixCodeE probeRows),Block.plain (wLiteral [.X 838])]) := by
    simp [row,portFused,List.append_assoc]
  rw [e3] at h
  have h := safe_tail_swap read address (portSuffixCodeD probeRows) (portSuffixCodeE probeRows) (wLiteral [.X 838])
    (Block.plain (wLiteral [.X 838]) :: Block.plain (WEX.portPrefixCode probeRows) :: generic streamLayout probeRows)
    ⟨false,s⟩ h
  rw [e4]
  have hx (k : List Bool) : ECDSAAdd.run ((specialize (wLiteral (n := 32768) [.X 838]) address).instantiate read) k
      ⟨false,s⟩ = ⟨false,flipInfinity s⟩ := by
    simp only [specialize_literal,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    exact flip_run _ _
  have hA : (specialize scrHead address).instantiate read = WEX.scrInHead := WEX.portPrefix_head read address
  have hroot' : (flipInfinity s) windowRoot = true := by
    have hne : (838 : Wire) ≠ windowRoot := by decide
    simpa [flipInfinity,ECDSAAdd.writeBit,hne] using hroot
  have hclean : ∀ w ∈ WEX.scrWires, flipInfinity s w = false :=
    fun w hw => (ECDSAAdd.Arithmetic.regValue_zero _ _).mp hs.clean w (WEX.scrWires_pool w hw)
  have e5 : (specialize (WEX.portPrefixCode4 probeRows) address).instantiate read =
      (specialize scrHead address).instantiate read ++
        (specialize (WEX.scrInSite probeRows).code address).instantiate read ++
        (specialize (wLiteral (n := 32768) (pointDialogGenericFlag streamLayout)) address).instantiate read := by
    simp only [WEX.portPrefixCode4,scrHead,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
      List.append_assoc]
  apply safe_split_masked read address _ _ _ _ _ _ _ _ _ _ h
  · rw [← WEX.portPrefix4_records,e5]
    simp only [ECDSAAdd.measurementCount_append]
  · intro k a m f ha hm
    rw [hx,← WEX.portPrefix4_eq3 read probeRows address _ _ hroot',e5,
      run_append_records _ _ (a ++ m) f _ (by simp only [List.length_append,ECDSAAdd.measurementCount_append,ha,hm]),
      run_append_records _ _ a m _ ha]
  · intro k a m w hw
    rw [hx] at *
    change w ∈ portTargets (WEX.scrInPorts probeRows) at hw
    rw [WEX.scrInPorts_targets] at hw
    apply WEX.scrInSite_clean read probeRows address m _ _ _ w hw
    · rw [hA,ECDSAAdd.run_preserves_outside _ _ _ _ WEX.scrInHead_root]
      exact hroot'
    · intro v hv
      rw [hA,ECDSAAdd.run_preserves_outside _ _ _ _ (WEX.scrInHead_avoid v hv)]
      exact hclean v hv

theorem row_geometry : ∀ b ∈ row, BlockGeometry b := by
  intro b hb
  have hp : ∀ i ∈ b.code, PlacedPair windowBits windowPaths windowRoot i := by
    intro i hi
    exact clearReferenceRow_placed i (erase_row ▸ block_mem_erase row b hb i hi)
  have hh : ∀ i ∈ b.code, HotAvoid i := by
    intro i hi
    exact row_hotavoid i (erase_row ▸ block_mem_erase row b hb i hi)
  cases b with
  | plain code => exact ⟨hp,hh⟩
  | masked site =>
    rcases row_masked site hb with h3 | hs
    · have ht := row3_masked_tight site h3
      have hq : ∀ i ∈ (Block.masked site).code, Placed windowBits windowPaths windowRoot i := by
        intro i hi
        exact tightReferenceRow_placed probeRows i (erase_tightRow ▸ block_mem_erase tightRow _ ht i hi)
      exact ⟨hq,hh,Or.inl (row3_shared _ h3)⟩
    · subst hs
      exact ⟨scr_placed windowBits hp,hh,Or.inr ⟨WEX.scrInPorts_targets probeRows,rfl⟩⟩

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

theorem row_safe (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (s : BasisState) (hs : liveReady s) :
    Safe (readConstant coeffs Q) (tableAddressValue windowBits s) row ⟨false,s⟩ := by
  let a := tableAddressValue windowBits s
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
    exact row_safe_of_boundary (readConstant coeffs Q) a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial hs.2.2

end
end ShorECDLP.Entrant.WEXUnlookup


namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program blockProgram clearProgram


def blockCCX {n} : Block n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * 32767
  | .masked site => literalToffolis (normalizeW site.prefix) + 32767 + 382

def blockMasks {n} : Block n → Nat
  | .plain _ => 0
  | .masked _ => 1

def ccx {n} : Code n → Nat
  | [] => 0
  | b::code => blockCCX b + ccx code

def masks {n} : Code n → Nat
  | [] => 0
  | b::code => blockMasks b + masks code

theorem site_high_layout {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    (tableAddressTree high 0 1).Layout site.guard highPaths := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide +kernel)
  rcases (kind_facts site hg.kind).2.2.2.2.2.1 with h | h <;> rw [h] <;> decide +kernel

theorem high_nodes : (tableAddressTree high 0 1).internalNodes = 255 := by
  have h := tableAddressTree_nodes high 0 1
  have hl : high.length = 8 := by decide +kernel
  rw [hl] at h
  norm_num at h
  omega

theorem clearProgram_tCount {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeometry site)
    (start : Nat) (history : Fin start → Bool) :
    ((clearProgram site start).instantiate read history).tCount = 2674 := by
  rw [clearProgram,MeasuredClear.measuredClear_tCount _ _ _ _ _ _ _ (site_high_layout site hg),high_nodes]

theorem clearProgram_slots {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    (clearProgram site start).gateSlots = 131072 * site.ports.length + 3570 := by
  rw [clearProgram,clear_slots_gen site high highPaths (site_high_layout site hg),high_nodes,
    show (2:Nat) ^ high.length = 256 by decide +kernel]
  omega

theorem high_records {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) site.guard highPaths) = 255 := by
  rw [(MeasuredClear.recordUnary_counts _ _ _ (site_high_layout site hg) 0).1,high_nodes]

theorem block_tCount {n} (read : ConstantBit n → Bool) (b : Block n) (hg : BlockGeometry b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram b start).instantiate read history).tCount = 7 * blockCCX b := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW code)
      (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram,WEX.compile_tCount read windowBits windowPaths windowRoot (normalizeW code) hl start history,traversals_normalize]
    simp [blockCCX,windowBits,Nat.mul_add,Nat.mul_assoc]
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair windowBits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hl := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW site.prefix)
      (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    rw [blockProgram,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearProgram_tCount read site hg _ h),
      WEX.compile_tCount read windowBits windowPaths windowRoot (normalizeW site.prefix) hl start history,traversals_normalize]
    simp [blockCCX,MaskedSite.prefix,traversals,windowBits]
    ring

theorem program_tCount {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b) (start : Nat) (history : Fin start → Bool) :
    ((program code start).instantiate read history).tCount = 7 * ccx code := by
  induction code generalizing start with
  | nil => simp [program,records,ccx,Straight.instantiate,AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [program,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      block_tCount read b (hg b (by simp))]
    simp [ccx,Nat.mul_add]

@[simp] theorem normalize_append {n} (a b : WCode n) : normalizeW (a++b) = normalizeW a ++ normalizeW b := by
  simp [normalizeW,List.map_append]

@[simp] theorem erase_cons {n} (b : Block n) (code : Code n) : erase (b::code) = b.code ++ erase code := rfl

theorem block_ccx_relation {n} (b : Block n) :
    blockCCX b + blockMasks b * 32385 = literalToffolis (normalizeW b.code) + traversals b.code * 32767 := by
  cases b with
  | plain code => simp [blockCCX,blockMasks,Block.code]
  | masked site =>
    have hl : literalToffolis (normalizeW site.code) = literalToffolis (normalizeW site.prefix) := by
      simp [MaskedSite.code,MaskedSite.prefix,normalizeW,normalizeWInstr,literalToffolis]
    have ht : traversals site.code = 2 := by
      simp [MaskedSite.code,MaskedSite.prefix,traversals]
    simp only [blockCCX,blockMasks,Block.code]
    omega

theorem ccx_relation {n} (code : Code n) :
    ccx code + masks code * 32385 = literalToffolis (normalizeW (erase code)) + traversals (erase code) * 32767 := by
  induction code with
  | nil => simp [ccx,masks,erase,normalizeW,literalToffolis,traversals]
  | cons b code ih =>
    have hb := block_ccx_relation b
    simp only [ccx,masks,erase_cons,normalize_append,literalToffolis_append,traversals_append,Nat.add_mul]
    omega

theorem row_masks : masks row = 6 := rfl


end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-- Total port count of the masked sites (each clear writes one record per port). -/
def blockLen {n} : Block n → Nat
  | .plain _ => 0
  | .masked site => site.ports.length

def lens {n} : Code n → Nat
  | [] => 0
  | b::code => blockLen b + lens code

theorem lens_append {n} (a b : Code n) : lens (a ++ b) = lens a + lens b := by
  induction a with
  | nil => simp [lens]
  | cons x a ih => simp [lens,ih,Nat.add_assoc]

theorem lens_shared {n} (code : Code n) (h : ∀ b ∈ code, Shared b) : lens code = 256 * masks code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have hb := h b List.mem_cons_self
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    cases b with
    | plain c =>
      simp only [lens,masks,blockLen,blockMasks,ht]
      omega
    | masked site =>
      have hl : site.ports.length = 256 := by
        have := congrArg List.length hb.1
        simpa [portTargets] using this
      simp only [lens,masks,blockLen,blockMasks,ht,hl]
      omega

theorem row_lens : lens row = 1796 := by
  have hg : lens (generic streamLayout probeRows) = 1280 := by
    rw [lens_shared _ (fun b hb => row3_shared b (by simp [row3,portFused3,hb]))]
    rfl
  have hs : (WEX.scrInPorts probeRows).length = 516 := by
    have := congrArg List.length (WEX.scrInPorts_targets probeRows)
    simp only [portTargets,List.length_map] at this
    rw [this,scrWires_eq]
    simp
  simp only [row,portFused,lens_append,hg]
  simp [lens,blockLen,WEX.scrInSite,hs]

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program blockProgram clearProgram


@[simp] theorem records_old_append {n} (a b : WCode n) :
    codeRecords windowBits windowPaths windowRoot (a++b) =
      codeRecords windowBits windowPaths windowRoot a + codeRecords windowBits windowPaths windowRoot b := by
  induction a with
  | nil => simp [codeRecords]
  | cons i code ih => cases i <;> simp [codeRecords,ih,Nat.add_assoc]

theorem single_lookup_records {n} (bits paths : List Wire) (root : Wire) (c : Option Wire)
    (ports : List (LookupPort n)) (hlen : bits.length ≤ paths.length)
    (hn : (lookupRoot root c :: bits ++ paths).Nodup) :
    codeRecords bits paths root ([.lookup c ports] : WCode n) = 2^bits.length-1 := by
  simp only [codeRecords,Nat.add_zero]
  exact portOps_measurements ports bits paths (lookupRoot root c) hlen hn

theorem site_old_clear_records {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    codeRecords windowBits windowPaths windowRoot ([.lookup (some site.guard) site.ports] : WCode n) = 32767 := by
  have hp := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  have h := single_lookup_records windowBits windowPaths windowRoot (some site.guard) site.ports
    (by simp [windowBits,windowPaths]) hp.1
  exact h.trans (by decide +kernel)

theorem block_records_relation {n} (b : Block n) (hg : BlockGeometry b) :
    blockRecords b + blockMasks b * 32385 = codeRecords windowBits windowPaths windowRoot (normalizeW b.code) + blockLen b := by
  cases b with
  | plain code => simp [blockRecords,blockMasks,Block.code,blockLen]
  | masked site =>
    rw [blockRecords,high_records site hg]
    rw [Block.code,MaskedSite.code,normalize_append,records_old_append]
    have hc : normalizeW ([.lookup (some site.guard) site.ports] : WCode n) = [.lookup (some site.guard) site.ports] := by simp [normalizeW,normalizeWInstr]
    rw [hc,site_old_clear_records site hg]
    have hm : blockMasks (Block.masked site) = 1 := rfl
    have hl : blockLen (Block.masked site) = site.ports.length := rfl
    omega

theorem records_relation {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b) :
    records code + masks code * 32385 = codeRecords windowBits windowPaths windowRoot (normalizeW (erase code)) + lens code := by
  induction code with
  | nil => simp [records,masks,erase,normalizeW,codeRecords,lens]
  | cons b code ih =>
    have hb := block_records_relation b (hg b (by simp))
    have ht := ih (fun d hd => hg d (by simp [hd]))
    simp only [records,masks,lens,erase_cons,normalize_append,records_old_append,Nat.add_mul]
    omega

theorem records_credit5 {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hm : masks code = 6) (hl : lens code = 1796)
    (ho : codeRecords windowBits windowPaths windowRoot (normalizeW (erase code)) = 2048404) :
    records code = 1855890 := by
  have h := records_relation code hg
  rw [hm,ho,hl] at h
  omega

theorem row_records : records row = 1855890 := by
  apply records_credit5 row row_geometry row_masks row_lens
  exact (congrArg (fun c : WCode 32768 => codeRecords windowBits windowPaths windowRoot (normalizeW c)) erase_row).trans clearReferenceRow_records


end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program blockProgram clearProgram


theorem row_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program row start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program_coherent (readConstant coeffs Q) row row_geometry liveReady (rowPointState coeffs Q)
    (row_safe coeffs Q hQ hn) (by
      intro s hs m
      have old := clearReferenceRow_run coeffs Q hQ hn s hs m
      rw [specialize_normalize_run] at old
      simpa only [reference,erase_row] using old) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩

end
end ShorECDLP.Entrant.WEXUnlookup



namespace ShorECDLP.Entrant.WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

 theorem clearProgram_wellFormed {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    (clearProgram site start).WellFormed := by
  unfold clearProgram
  exact clear_wellFormed_gen site hg.kind high highPaths
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) (by decide +kernel) (by decide +kernel) start

theorem block_wellFormed {n} (b : Block n) (hg : BlockGeometry b)
    (hp : ∀ p, WInstr.literal p ∈ b.code → GatePhysical p) (start : Nat) :
    (blockProgram b start).WellFormed := by
  cases b with
  | plain code =>
    unfold blockProgram
    exact pair_compile_wellFormed _ _ _ _ (by simp [windowBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hg.1) (normalized_literals_valid code hp) start
  | masked site =>
    have hpref : ∀ i ∈ site.prefix, PlacedPair windowBits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hphys : ∀ p, WInstr.literal p ∈ site.prefix → GatePhysical p := by
      intro p hm; exact hp p (List.mem_append_left _ hm)
    rw [blockProgram,castFinish_wellFormed]
    exact straight_append_wellFormed _ _
      (pair_compile_wellFormed _ _ _ _ (by simp [windowBits,windowPaths])
        (pair_placed_normalize _ _ _ _ hpref) (normalized_literals_valid site.prefix hphys) start)
      (clearProgram_wellFormed site hg _)

theorem program_wellFormed {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hp : ∀ p, WInstr.literal p ∈ erase code → GatePhysical p) (start : Nat) :
    (program code start).WellFormed := by
  induction code generalizing start with
  | nil => simp [program,records,Straight.WellFormed]
  | cons b code ih =>
    rw [program,castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact block_wellFormed b (hg b (by simp)) (fun p hm => hp p (by simp [erase_cons,hm])) start
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase_cons,hm])) _

theorem row_wellFormed (start : Nat) : (program row start).WellFormed := by
  apply program_wellFormed row row_geometry
  intro p hp
  rw [erase_row] at hp
  exact clearReferenceRow_physical p hp

open AndGadget WEXCredit in
 theorem block_residue {n} (b : Block n) (start : Nat) : residue (blockProgram b start) = 0 := by
  cases b with
  | plain code => rw [blockProgram]; exact compile_residue _ _ _ _ _
  | masked site => simp [blockProgram,residue_cast,residue_append,compile_residue,
      clearProgram,MeasuredClear.measuredClear_residue]

open AndGadget in
 theorem program_residue {n} (code : Code n) (start : Nat) : residue (program code start) = 0 := by
  induction code generalizing start with
  | nil => simp [program,records]
  | cons b code ih => simp [program,residue_cast,residue_append,block_residue,ih]

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram WEX.codeSlots WEX.normalizeW WEX.codeRecords
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.portOps lookupMeasurements tableAddressTree

@[simp] theorem old_slots_append {n} (a b : WCode n) :
    codeSlots windowBits (a++b) = codeSlots windowBits a + codeSlots windowBits b := by
  induction a with
  | nil => simp [codeSlots]
  | cons i code ih => cases i <;> simp [codeSlots,ih,Nat.add_assoc]

theorem site_old_clear_slots {n} (site : MaskedSite n) :
    codeSlots windowBits ([.lookup (some site.guard) site.ports] : WCode n) = 32768 * site.ports.length + 327670 := by
  simp [codeSlots,windowBits]

theorem block_slots_relation {n} (b : Block n) (hg : BlockGeometry b) (start : Nat) :
    (blockProgram b start).gateSlots + blockMasks b * 324100 =
      codeSlots windowBits (normalizeW b.code) + blockLen b * 98304 := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW code)
      (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram,compile_slots windowBits windowPaths windowRoot (normalizeW code) hl start]
    simp [blockMasks,blockLen,Block.code]
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair windowBits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hl := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW site.prefix)
      (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    rw [blockProgram,castFinish_gateSlots,Straight.gateSlots_append,clearProgram_slots site hg,
      compile_slots windowBits windowPaths windowRoot (normalizeW site.prefix) hl start,Block.code,MaskedSite.code,normalize_append,old_slots_append]
    have hc : normalizeW ([.lookup (some site.guard) site.ports] : WCode n) = [.lookup (some site.guard) site.ports] := by simp [normalizeW,normalizeWInstr]
    rw [hc,site_old_clear_slots site]
    simp only [blockMasks,blockLen]
    omega

theorem program_slots_relation {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b) (start : Nat) :
    (program code start).gateSlots + masks code * 324100 =
      codeSlots windowBits (normalizeW (erase code)) + lens code * 98304 := by
  induction code generalizing start with
  | nil => simp [program,records,masks,lens,Straight.gateSlots,erase,normalizeW,codeSlots]
  | cons b code ih =>
    have hb := block_slots_relation b (hg b (by simp)) start
    have ht := ih (fun d hd => hg d (by simp [hd])) (start+blockRecords b)
    rw [program,castFinish_gateSlots,Straight.gateSlots_append]
    simp only [masks,lens,erase_cons,normalize_append,old_slots_append,Nat.add_mul]
    omega

theorem slots_credit5 {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hm : masks code = 6) (hl : lens code = 1796) (start : Nat) :
    (program code start).gateSlots = codeSlots windowBits (normalizeW (erase code)) + 174609384 := by
  have h := program_slots_relation code hg start
  rw [hm,hl] at h
  omega

theorem row_slots (start : Nat) : (program row start).gateSlots =
    codeSlots windowBits (normalizeW (clearReferenceRow probeRows)) + 174609384 := by
  exact (slots_credit5 row row_geometry row_masks row_lens start).trans
    (congrArg (fun c : WCode 32768 => codeSlots windowBits (normalizeW c) + 174609384) erase_row)

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.wires ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

theorem support_cast {n s e f} (h : e=f) (p : Straight n s e) :
    ChallengeMigration.straightWires (castFinish h p) = ChallengeMigration.straightWires p := by
  subst f
  rfl

def logicalSupport : List Wire := sourceSupport ++ MeasuredClear.hotBank recycledHot

def OldWithin {n} (code : WCode n) : Prop :=
  (∀ p, WInstr.literal p ∈ code → ECDSAAdd.wires p ⊆ sourceSupport.toFinset) ∧
  (∀ c ps, WInstr.lookup c ps ∈ code → (∀ q ∈ c, q ∈ sourceSupport) ∧ portTargets ps ⊆ sourceSupport)

theorem row_oldWithin : OldWithin (clearReferenceRow probeRows) := by
  refine ⟨?_,?_⟩
  · intro p hi
    exact clearReferenceRow_literal_source p hi
  · intro c ps hi
    have hm : WInstr.lookup c ps ∈ normalizeW (clearReferenceRow probeRows) := by
      rw [normalizeW]
      exact List.mem_map.mpr ⟨WInstr.lookup c ps,hi,rfl⟩
    have h := List.all_eq_true.mp clearReferenceRow_sourceLookupOK (WInstr.lookup c ps) hm
    have h : (∀ q ∈ c, fixedPort q ∨ oldWork q) ∧
        (∀ w ∈ portTargets ps, fixedPort w ∨ oldWork w) := by
      simpa [sourceLookupOK,List.all_eq_true] using h
    exact ⟨fun q hq => (sourceSupport_mem q).mpr (h.1 q hq),fun w hw => (sourceSupport_mem w).mpr (h.2 w hw)⟩

theorem oldWithin_sub {n} (a b : WCode n) (h : a ⊆ b) (hb : OldWithin b) : OldWithin a :=
  ⟨fun p hp => hb.1 p (h hp),fun c ps hp => hb.2 c ps (h hp)⟩

theorem oldWithin_normalize {n} (code : WCode n) (h : OldWithin code) : OldWithin (normalizeW code) := by
  refine ⟨?_,?_⟩
  · intro p hp
    rw [normalizeW] at hp
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
    cases j with
    | literal q =>
      cases he
      rw [ECDSAAdd.Baselines.normalize_wires]
      exact h.1 q hj
    | lookup c ps => cases he
  · intro c ps hp
    rw [normalizeW] at hp
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
    cases j with
    | literal q => cases he
    | lookup d qs => cases he; exact h.2 c ps hj

theorem old_compile_support {n} (code : WCode n) (h : OldWithin code) (start : Nat) :
    ChallengeMigration.straightWires (compile windowBits windowPaths windowRoot (normalizeW code) start) ⊆ sourceSupport := by
  have hn := oldWithin_normalize code h
  exact compile_support _ _ _ _ sourceSupport (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hn.1 hn.2 start

theorem clear_support_gen {n} (site : MaskedSite n) (hk : SiteKind site) (H P : List Wire)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 871) (hP : ∀ w ∈ P, 10000 ≤ w ∧ w < 10015)
    (hindex : (tableAddressTree H 0 1).indexWires.dedup = H) (start : Nat) :
    ChallengeMigration.straightWires (MeasuredClear.measuredClear (clearData site.ports) low (clearHot site)
        (tableAddressTree H 0 1) site.guard (scratch site) P start) ⊆ logicalSupport := by
  obtain ⟨-,hbd,-,hmem,hsm,hg,-⟩ := kind_facts site hk
  have hscratch : scratch site ∈ (clearData site.ports).map MeasuredClear.ClearPort.target := by
    rw [clearData_targets]
    exact hsm
  rw [support_agrees]
  apply List.Subset.trans (MeasuredClear.measuredClear_static _ _ _ _ _ _ _ hscratch start)
  intro w hw
  simp only [MeasuredClear.clearSupport,clearData_targets,hindex,List.mem_append,List.mem_cons,or_assoc] at hw
  apply List.mem_append_left
  rw [sourceSupport_mem]
  rcases hw with hs | hl | hh | hr | hb | hp
  · exact Or.inr (hbd w hs).2
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    left
    have hi := i.isLt
    unfold fixedPort
    simp only [low]
    dsimp only [Wire] at *
    omega
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact Or.inr (hbd _ (hmem i)).2
  · right
    rw [hr]
    unfold oldWork
    rcases hg with e | e <;> rw [e] <;> omega
  · left
    have := hH w hb
    unfold fixedPort
    dsimp only [Wire] at *
    omega
  · right
    have := hP w hp
    unfold oldWork
    dsimp only [Wire] at *
    omega

theorem clearProgram_support {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    ChallengeMigration.straightWires (clearProgram site start) ⊆ logicalSupport := by
  unfold clearProgram
  exact clear_support_gen site hg.kind high highPaths
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) start

theorem block_support {n} (b : Block n) (hg : BlockGeometry b) (hw : OldWithin b.code) (start : Nat) :
    ChallengeMigration.straightWires (blockProgram b start) ⊆ logicalSupport := by
  cases b with
  | plain code => rw [blockProgram]; exact (old_compile_support code hw start).trans (List.subset_append_left _ _)
  | masked site =>
    have hp : OldWithin site.prefix := oldWithin_sub site.prefix site.code (List.subset_append_left _ _) hw
    rw [blockProgram,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨(old_compile_support site.prefix hp start).trans (List.subset_append_left _ _),
      clearProgram_support site hg _⟩

theorem program_support {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hw : OldWithin (erase code)) (start : Nat) :
    ChallengeMigration.straightWires (program code start) ⊆ logicalSupport := by
  induction code generalizing start with
  | nil => simp [program,records,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hb : OldWithin b.code := oldWithin_sub b.code (erase (b::code)) (by rw [erase_cons]; exact List.subset_append_left _ _) hw
    have ht : OldWithin (erase code) := oldWithin_sub (erase code) (erase (b::code)) (by rw [erase_cons]; exact List.subset_append_right _ _) hw
    rw [program,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨block_support b (hg b (by simp)) hb start,
      ih (fun d hd => hg d (by simp [hd])) ht _⟩

theorem row_support (start : Nat) : ChallengeMigration.straightWires (program row start) ⊆ logicalSupport := by
  apply program_support row row_geometry
  rw [erase_row]
  exact row_oldWithin

end
end ShorECDLP.Entrant.WEXUnlookup



namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

def LiveReady (s : BasisState) : Prop := liveReady s ∧ MeasuredClear.HotClean hot s

def Ready (s : BasisState) : Prop := windowReady s ∧ MeasuredClear.HotClean hot s

theorem pointWrite_hot (P : Secp256k1.Point) (s : BasisState) (hs : MeasuredClear.HotClean hot s) :
    MeasuredClear.HotClean hot (pointWrite P s) := by
  intro i
  have hi := i.isLt
  have hpoint : hot i ∉ pointLogicalWires := by
    intro hm
    have hb := point_wire_small _ hm
    simp only [hot] at hb
    dsimp only [Wire] at *
    omega
  rw [pointWrite_frame P s _ hpoint]
  exact hs i

theorem live_write (P : Secp256k1.Point) (s : BasisState) (hs : LiveReady s) : LiveReady (pointWrite P s) :=
  ⟨liveReady_write P s hs.1,pointWrite_hot P s hs.2⟩

def rowSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode (readConstant coeffs Q) row

theorem rowSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  obtain ⟨cs,aligned,mass⟩ := row_coherent coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs,?_,mass⟩
  simpa only [program_run,rowSource] using aligned

theorem sign_coherent : CoherentlyImplementsOn signSource (Finsupp.lmapDomain ℂ ℂ signPointState) LiveReady := by
  obtain ⟨cs,aligned,mass⟩ := windowSign_coherent
  exact ⟨cs,aligned.imp (fun _ _ hb s hs => hb s hs.1),mass⟩

def middleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (signSource.seq (rowSource coeffs Q)).seq signSource

theorem middle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (middleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent sign_coherent (rowSource_coherent coeffs Q hQ hn)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState) first sign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

theorem prefix_hot (s : BasisState) (hs : MeasuredClear.HotClean hot s) :
    MeasuredClear.HotClean hot (prefixState s) := by
  intro i
  have hi := i.isLt
  have ha : hot i ∉ windowBits := by
    simp only [hot,windowBits,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  have hr : hot i ≠ windowRoot := by
    simp only [hot,windowRoot]
    dsimp only [Wire] at *
    omega
  rw [prefixState,windowPrepareState_frame _ _ ha]
  simpa [rootFlip,ECDSAAdd.writeBit,hr] using hs i

theorem prefix_coherent : CoherentlyImplementsOn prefixSource (Finsupp.lmapDomain ℂ ℂ prefixState) Ready := by
  obtain ⟨cs,aligned,mass⟩ := WEX.prefix_coherent
  exact ⟨cs,aligned.imp (fun _ _ hb s hs => hb s hs.1),mass⟩

def bodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (middleSource coeffs Q)).seq suffixSource

theorem bodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (bodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent prefix_coherent (middle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program blockProgram clearProgram


attribute [local irreducible] ccx blockCCX masks blockMasks row WEX.traversals

theorem ccx_credit5 {n} (code : Code n) (k : Nat) (hm : masks code = 6)
    (hk : literalToffolis (normalizeW (erase code)) + traversals (erase code)*32767 = k) :
    ccx code + 194310 = k := by
  have h := ccx_relation code
  rw [hm] at h
  omega

theorem row_ccx_relation : ccx row + 194310 = literalToffolis (normalizeW (clearReferenceRow probeRows)) + 15*32767 := by
  have ht := WEX.clearReferenceRow_traversals
  rw [traversals_normalize] at ht
  apply ccx_credit5 row _ row_masks
  rw [erase_row]
  exact congrArg (fun t => literalToffolis (normalizeW (clearReferenceRow probeRows)) + t*32767) ht

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.run ECDSAAdd.Baselines.normalizeProgram



end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] Straight.instantiate AdaptiveCircuit.tCount AdaptiveCircuit.run
  WEX.nProgram WEX.prefixProgram WEX.suffixProgram WEX.literalFixed WEX.compilerFixed
  AndGadget.added AndGadget.residue sourceCode rowSource middleSource bodySource WEX.signSource WEX.prefixSource WEX.suffixSource
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram WEX.codeRecords WEX.codeSlots WEX.literalToffolis
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps ccx masks

def addFixed (start : Nat) : Straight 32768 start (start+1855890) :=
  castFinish (congrArg (fun m => start+m) row_records) (program row start)

theorem addFixed_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed start).instantiate read history).run = (sourceCode read row).run := by
  rw [addFixed,castFinish_instantiate,program_run]

theorem addFixed_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed start).instantiate read history).tCount = 7*ccx row := by
  rw [addFixed,castFinish_instantiate,program_tCount read row row_geometry]

theorem addFixed_slots (start : Nat) : (addFixed start).gateSlots =
    codeSlots windowBits (normalizeW (clearReferenceRow probeRows)) + 174609384 := by
  rw [addFixed,castFinish_gateSlots,row_slots]

theorem addFixed_wellFormed (start : Nat) : (addFixed start).WellFormed := by
  rw [addFixed,castFinish_wellFormed]
  exact row_wellFormed start

theorem addFixed_support (start : Nat) : ChallengeMigration.straightWires (addFixed start) ⊆ logicalSupport := by
  rw [addFixed,support_cast]
  exact row_support start

open AndGadget in
 theorem addFixed_residue (start : Nat) : residue (addFixed start) = 0 := by
  rw [addFixed,residue_cast]
  exact program_residue row start

def bodyProgram (start : Nat) : Straight 32768 start (start+1857934) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nProgram start)).append (addFixed (start+1022))).append
      (nProgram (start+1022+1855890))).append (suffixProgram (start+1022+1855890+1022)))

theorem regroup_runs (p l a r s : AdaptiveCircuit) :
    ((((p.run.seq l.run).seq a.run).seq r.run).seq s.run) =
      ((p.seq ((l.seq a).seq r)).seq s).run := by
  rw [← AdaptiveCircuit.run_seq,← AdaptiveCircuit.run_seq,← AdaptiveCircuit.run_seq,← AdaptiveCircuit.run_seq]
  simp only [adaptive_seq_assoc]

theorem five_run {n s t u v w e} (read : ConstantBit n → Bool)
    (p : Straight n s t) (l : Straight n t u) (a : Straight n u v)
    (r : Straight n v w) (q : Straight n w e) (P L A R S : AdaptiveCircuit)
    (hp : ∀ h, (p.instantiate read h).run = P.run)
    (hl : ∀ h, (l.instantiate read h).run = L.run)
    (ha : ∀ h, (a.instantiate read h).run = A.run)
    (hr : ∀ h, (r.instantiate read h).run = R.run)
    (hq : ∀ h, (q.instantiate read h).run = S.run)
    (history : Fin s → Bool) :
    (((((p.append l).append a).append r).append q).instantiate read history).run =
      ((P.seq ((L.seq A).seq R)).seq S).run := by
  rw [append_run_fixed _ _ _ _ _ hq,AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ hr,AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ ha,AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ hl,AdaptiveCircuit.run_seq,hp]
  exact regroup_runs P L A R S

theorem bodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((bodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((signSource.seq (sourceCode read row)).seq signSource)).seq suffixSource).run := by
  rw [bodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource signSource (sourceCode read row) signSource suffixSource
    (prefixProgram_run _ read) (nProgram_run _ read) (addFixed_run read _)
    (nProgram_run _ read) (suffixProgram_run _ read) history

theorem bodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((bodyProgram start).instantiate (readConstant coeffs Q) history).run = (bodySource coeffs Q).run := by
  have he : bodySource coeffs Q =
      ((prefixSource.seq ((signSource.seq (sourceCode (readConstant coeffs Q) row)).seq signSource)).seq suffixSource) := by
    delta bodySource middleSource rowSource
    rfl
  have hr := bodyProgram_run_read (readConstant coeffs Q) start history
  have hs := congrArg AdaptiveCircuit.run he.symm
  exact hr.trans hs

open AndGadget WEXCredit in
 theorem addFixed_credit (start : Nat) : ProgramCredit (addFixed start) (ccx row) := by
  have hz := addFixed_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed_tCount (fun _ => false) start (fun _ => false)
  omega

open AndGadget WEXCredit in
 theorem five_credit {n s t u v w e} {p : Straight n s t} {l : Straight n t u} {ad : Straight n u v}
    {r : Straight n v w} {q : Straight n w e} (a b : Nat)
    (hp : ProgramCredit p 0) (hl : ProgramCredit l a) (ha : ProgramCredit ad b)
    (hr : ProgramCredit r a) (hq : ProgramCredit q 0) :
    ProgramCredit ((((p.append l).append ad).append r).append q) (2*a+b) := by
  have h1 := credit_append hp hl
  have h2 := credit_append h1 ha
  have h3 := credit_append h2 hr
  have h := credit_append h3 hq
  have hs : 0+a+b+a+0 = 2*a+b := by omega
  exact ⟨h.1,h.2.trans hs⟩

open AndGadget WEXCredit in
 theorem bodyProgram_credit (start : Nat) : ProgramCredit (bodyProgram start) (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram) + WEXUnlookup.ccx WEXUnlookup.row) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)
  have hl : ProgramCredit (nProgram start) a := ⟨n_residue start,n_added start⟩
  have hr : ProgramCredit (nProgram (start+1022+1855890)) a := ⟨n_residue _,n_added _⟩
  rw [bodyProgram]
  apply credit_cast
  exact five_credit a (ccx row) (prefix_credit start) hl (addFixed_credit (start+1022)) hr
    (suffix_credit (start+1022+1855890+1022))

open AndGadget WEXCredit in
 theorem bodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((bodyProgram start).instantiate read history).tCount = 7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram) + WEXUnlookup.ccx WEXUnlookup.row) := by
  have hc := bodyProgram_credit start
  have h := exact_t (bodyProgram start) hc.1 read history
  rw [hc.2] at h
  exact h

theorem bodyProgram_slots (start : Nat) : (bodyProgram start).gateSlots =
    2*Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram windowSignProgram)) +
      codeSlots windowBits (normalizeW (clearReferenceRow probeRows)) + 62 + 174609384 := by
  rw [bodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nProgram_slots,addFixed_slots,prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  omega

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals

theorem bodyProgram_slots_bound (start : Nat) : (bodyProgram start).gateSlots ≤ 2000000000 := by
  rw [bodyProgram_slots]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (clearReferenceRow probeRows))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have ht := WEX.clearReferenceRow_traversals
  rw [traversals_normalize] at ht
  rw [ht] at hc
  have hs := WEX.sign_slots_bound
  have hb := WEX.literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at hb
  norm_num [windowBits] at hc
  simp only [windowBits]
  omega

theorem bodyProgram_wellFormed (start : Nat) : (bodyProgram start).WellFormed := by
  rw [bodyProgram,castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nProgram_wellFormed start)
      · exact addFixed_wellFormed _
    · exact nProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem bodyProgram_support (start : Nat) : ChallengeMigration.straightWires (bodyProgram start) ⊆ logicalSupport := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ sourceSupport := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  have hs (k : Nat) : ChallengeMigration.straightWires (suffixProgram k) ⊆ sourceSupport := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  rw [bodyProgram,support_cast]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp.trans (List.subset_append_left _ _),(nProgram_source _).trans (List.subset_append_left _ _)⟩,
    addFixed_support _⟩,(nProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩


end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] Straight.instantiate AdaptiveCircuit.tCount AdaptiveCircuit.run
  WEX.nProgram WEX.prefixProgram WEX.suffixProgram WEX.literalFixed WEX.compilerFixed
  AndGadget.added AndGadget.residue
attribute [local irreducible] program blockProgram clearProgram bodyProgram addFixed WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram WEX.codeRecords WEX.codeSlots WEX.literalToffolis WEX.normalizeW
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps ccx masks


theorem window_count_upper : (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.windowSignProgram) + WEXUnlookup.ccx WEXUnlookup.row) ≤ 2592677 := by
  have h := WEX.clearReferenceRow_count_upper 15
  have r := row_ccx_relation
  norm_num at h
  omega

theorem compactPerm_hot (i : Fin 128) : compactPerm (hot i) = hot i := by
  have hi := i.isLt
  have ho : ¬oldWork (hot i) := by unfold oldWork hot; dsimp only [Wire] at *; omega
  have hf : ¬freeWork (hot i) := by unfold freeWork hot; dsimp only [Wire] at *; omega
  simp only [compactPerm,Equiv.coe_fn_mk,compactWire,if_neg ho,if_neg hf]

theorem pull_hot (s : BasisState) (i : Fin 128) : compactPull s (hot i) = s (hot i) := by
  simp only [compactPull,relabelBasis,Equiv.symm_symm,compactPerm_hot]

def compactReady (s : BasisState) : Prop := WEX.compactReady s ∧ MeasuredClear.HotClean hot s

theorem compactReady_active (s : BasisState) (hs : compactReady s) : s 836 = true := WEX.compactReady_active s hs.1

theorem compactReady_write (P : Secp256k1.Point) (s : BasisState) (hs : compactReady s) : compactReady (pointWrite P s) :=
  ⟨WEX.compactReady_write P s hs.1,pointWrite_hot P s hs.2⟩

theorem hot_outside_address (i : Fin 128) : hot i ∉ streamAddress := by
  have hi := i.isLt
  simp only [streamAddress,List.mem_range'_1,hot]
  dsimp only [Wire] at *
  omega

theorem compactReady_address (s : BasisState) (hs : compactReady s) (v : Wire)
    (hv : v ∈ streamAddress) (b : Bool) : compactReady (s[v ↦ b]) := by
  refine ⟨WEX.compactReady_address s hs.1 v hv b,?_⟩
  intro i
  have hn : hot i ≠ v := fun he => hot_outside_address i (he.symm ▸ hv)
  exact (upd_other s v b hn).trans (hs.2 i)

theorem compactReady_first (s : BasisState) (hs : FirstWindowInput s) (P : Secp256k1.Point) :
    compactReady (pointWrite P s) := by
  refine ⟨WEX.compactReady_first s hs P,pointWrite_hot P s ?_⟩
  intro i
  apply hs.2
  · have hi := i.isLt
    simp only [hot]
    dsimp only [Wire] at *
    omega
  · exact hot_outside_address i

def compactSupport : List Wire := List.range 1634

def compactProgram (start : Nat) : Straight 32768 start (start+1857934) :=
  relabelStraight compactPerm (bodyProgram start)

theorem compactProgram_support (start : Nat) :
    ChallengeMigration.straightWires (compactProgram start) ⊆ compactSupport := by
  rw [compactProgram,straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  have hh := bodyProgram_support start hv
  rcases List.mem_append.mp hh with ho | hh
  · exact List.mem_range.mpr (WEX.compactPerm_bound v ho)
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact List.mem_range.mpr (WEX.compactPerm_bound _ (recycledHot_source i))

theorem compactProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((compactProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have hc : CoherentlyImplementsOn ((bodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
    obtain ⟨cs,aligned,mass⟩ := bodySource_coherent coeffs Q hQ hn
    refine ⟨cs,?_,mass⟩
    rw [bodyProgram_run]
    exact aligned
  have h := hc.relabel compactPerm
  have hr : CoherentlyImplementsOn
      (((bodyProgram start).instantiate (readConstant coeffs Q) history).relabel compactPerm)
      ((relabelState compactPerm).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState compactPerm.symm)))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,aligned,mass⟩ := h
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb s hs
    apply hb s
    refine ⟨hs.1.1,?_⟩
    intro i
    exact (pull_hot s i).trans (hs.1.2 i)
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
    (by intro s _; simp [compactState,compactPull,LinearMap.comp_apply,relabelState,ket])
  rw [compactProgram,relabelStraight_instantiate]
  exact he

def compactBody : Single.WindowBody where
  records := 1857934
  tBound := 18148739
  slotBound := 2000000000
  support := compactSupport
  reset := resetWires
  ready := compactReady
  active := compactReady_active
  ready_write := compactReady_write
  ready_address := compactReady_address
  ready_first := compactReady_first
  program := compactProgram
  update := compactState
  correct := fun coeffs Q _ _ s hs P hP => compactState_correct coeffs Q s hs.1 P hP
  coherent := compactProgram_coherent
  wellFormed := fun start => (relabelStraight_wellFormed compactPerm (bodyProgram start)).mpr
    (bodyProgram_wellFormed start)
  slots := fun start => (relabelStraight_slots compactPerm (bodyProgram start)).trans_le (bodyProgram_slots_bound start)
  tCount := by
    intro coeffs Q start history
    rw [compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,bodyProgram_tCount]
    have h := window_count_upper
    omega
  wires := compactProgram_support
  reset_support := by
    intro w hw
    exact compact_base_support (List.mem_cons_of_mem 837 hw)
  skeleton_support := by
    intro w hw
    exact compact_base_support hw

theorem compactBody_ledger : compactBody.records = 1857934 ∧ compactBody.tBound = 18148739 ∧
    compactBody.support.length = 1634 ∧ compactBody.reset.length = 854 := by
  exact ⟨rfl,rfl,by norm_num [compactBody,compactSupport,MeasuredClear.hotBank],by norm_num [compactBody,resetWires]⟩

open AndGadget in
 theorem residue_relabel {n s e} (p : Straight n s e) (f : Wire ≃ Wire) : residue (relabelStraight f p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [relabelStraight,relabelTemplateGate,Gate.relabel,residue,primitivePhaseCost]
    | whenBit r v g => cases g <;> simp_all [relabelStraight,relabelTemplateGate,Gate.relabel,residue,tCost]
  | recordGate i v g p ih => cases g <;> simp_all [relabelStraight,Gate.relabel,residue,tCost]
  | measure => simp_all [relabelStraight,residue]


end
end ShorECDLP.Entrant.WEXUnlookup



namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def bits : List Wire := WEX.widthBits 13
def high : List Wire := List.range' 862 6
def highPaths : List Wire := List.range' 10000 6

def clearProgram {n} (site : MaskedSite n) (start : Nat) :=
  MeasuredClear.measuredClear (clearData site.ports) low (clearHot site) (tableAddressTree high 0 1)
    site.guard (scratch site) highPaths start

theorem splitAddress (s : BasisState) :
    128*(tableAddressTree high 0 1).routeLabel s + MeasuredClear.hotAddress low s =
      tableAddressValue bits s := by
  have h := MeasuredClear.splitAddress_value low high s
  have he : [MeasuredClear.lowN low 0,MeasuredClear.lowN low 1,MeasuredClear.lowN low 2,MeasuredClear.lowN low 3,MeasuredClear.lowN low 4,MeasuredClear.lowN low 5,MeasuredClear.lowN low 6]++high = bits := by decide +kernel
  rw [he] at h
  exact h

theorem clearProgram_coherent {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeometry site)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((clearProgram site start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => MeasuredClear.HotClean hot s ∧ Clean windowPaths s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue bits s)) = p.value))) := by
  unfold clearProgram
  exact clear_coherent_gen read site hg.kind bits high highPaths splitAddress
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,windowPaths,List.mem_range'_1] at hw ⊢; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) (by decide +kernel) (by decide +kernel) start history

theorem site_high_layout {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    (tableAddressTree high 0 1).Layout site.guard highPaths := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide +kernel)
  rcases (kind_facts site hg.kind).2.2.2.2.2.1 with h | h <;> rw [h] <;> decide +kernel

theorem high_nodes : (tableAddressTree high 0 1).internalNodes = 63 := by
  have h := tableAddressTree_nodes high 0 1
  have hl : high.length = 6 := by decide +kernel
  rw [hl] at h
  norm_num at h
  omega

theorem clearProgram_tCount {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeometry site)
    (start : Nat) (history : Fin start → Bool) :
    ((clearProgram site start).instantiate read history).tCount = 1330 := by
  rw [clearProgram,MeasuredClear.measuredClear_tCount _ _ _ _ _ _ _ (site_high_layout site hg),high_nodes]

theorem high_records {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) site.guard highPaths) = 63 := by
  rw [(MeasuredClear.recordUnary_counts _ _ _ (site_high_layout site hg) 0).1,high_nodes]

theorem clearProgram_slots {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    (clearProgram site start).gateSlots ≤ 33595442 := by
  rw [clearProgram,clear_slots_gen site high highPaths (site_high_layout site hg),high_nodes,
    show (2:Nat) ^ high.length = 64 by decide +kernel]
  have := (kind_facts site hg.kind).2.2.2.2.2.2
  omega


end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def bits : List Wire := WEX.widthBits 14
def high : List Wire := List.range' 862 7
def highPaths : List Wire := List.range' 10000 7

def clearProgram {n} (site : MaskedSite n) (start : Nat) :=
  MeasuredClear.measuredClear (clearData site.ports) low (clearHot site) (tableAddressTree high 0 1)
    site.guard (scratch site) highPaths start

theorem splitAddress (s : BasisState) :
    128*(tableAddressTree high 0 1).routeLabel s + MeasuredClear.hotAddress low s =
      tableAddressValue bits s := by
  have h := MeasuredClear.splitAddress_value low high s
  have he : [MeasuredClear.lowN low 0,MeasuredClear.lowN low 1,MeasuredClear.lowN low 2,MeasuredClear.lowN low 3,MeasuredClear.lowN low 4,MeasuredClear.lowN low 5,MeasuredClear.lowN low 6]++high = bits := by decide +kernel
  rw [he] at h
  exact h

theorem clearProgram_coherent {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeometry site)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((clearProgram site start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => MeasuredClear.HotClean hot s ∧ Clean windowPaths s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue bits s)) = p.value))) := by
  unfold clearProgram
  exact clear_coherent_gen read site hg.kind bits high highPaths splitAddress
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,windowPaths,List.mem_range'_1] at hw ⊢; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) (by decide +kernel) (by decide +kernel) start history

theorem site_high_layout {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    (tableAddressTree high 0 1).Layout site.guard highPaths := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide +kernel)
  rcases (kind_facts site hg.kind).2.2.2.2.2.1 with h | h <;> rw [h] <;> decide +kernel

theorem high_nodes : (tableAddressTree high 0 1).internalNodes = 127 := by
  have h := tableAddressTree_nodes high 0 1
  have hl : high.length = 7 := by decide +kernel
  rw [hl] at h
  norm_num at h
  omega

theorem clearProgram_tCount {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeometry site)
    (start : Nat) (history : Fin start → Bool) :
    ((clearProgram site start).instantiate read history).tCount = 1778 := by
  rw [clearProgram,MeasuredClear.measuredClear_tCount _ _ _ _ _ _ _ (site_high_layout site hg),high_nodes]

theorem high_records {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) site.guard highPaths) = 127 := by
  rw [(MeasuredClear.recordUnary_counts _ _ _ (site_high_layout site hg) 0).1,high_nodes]

theorem clearProgram_slots {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    (clearProgram site start).gateSlots ≤ 33818866 := by
  rw [clearProgram,clear_slots_gen site high highPaths (site_high_layout site hg),high_nodes,
    show (2:Nat) ^ high.length = 128 by decide +kernel]
  have := (kind_facts site hg.kind).2.2.2.2.2.2
  omega


end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] MeasuredClear.measuredClear
 theorem clearProgram_wellFormed {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    (clearProgram site start).WellFormed := by
  unfold clearProgram
  exact clear_wellFormed_gen site hg.kind high highPaths
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) (by decide +kernel) (by decide +kernel) start

end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] MeasuredClear.measuredClear
 theorem clearProgram_wellFormed {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    (clearProgram site start).WellFormed := by
  unfold clearProgram
  exact clear_wellFormed_gen site hg.kind high highPaths
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) (by decide +kernel) (by decide +kernel) start

end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] MeasuredClear.measuredClear
theorem clearProgram_support {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    ChallengeMigration.straightWires (clearProgram site start) ⊆ logicalSupport := by
  unfold clearProgram
  exact clear_support_gen site hg.kind high highPaths
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) start

end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] MeasuredClear.measuredClear
theorem clearProgram_support {n} (site : MaskedSite n) (hg : SiteGeometry site) (start : Nat) :
    ChallengeMigration.straightWires (clearProgram site start) ⊆ logicalSupport := by
  unfold clearProgram
  exact clear_support_gen site hg.kind high highPaths
    (by intro w hw; simp only [high,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (by intro w hw; simp only [highPaths,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
    (tableAddressTree_index high 0 1 (by decide +kernel)) start

end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup

end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup

end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] MeasuredClear.measuredClear

theorem reference_preserves {n} (read : ConstantBit n → Bool) (code : WCode n) (a : Nat)
    (hp : ∀ i ∈ code, PlacedPair bits windowPaths windowRoot i)
    (hh : ∀ i ∈ code, HotAvoid i)
    (st : ECDSAAdd.State) (hs : SimulationValid bits windowPaths windowRoot a st)
    (hc : MeasuredClear.HotClean hot st.basis) (m : List Bool) :
    SimulationValid bits windowPaths windowRoot a
        (ECDSAAdd.run ((specialize code a).instantiate read) m st) ∧
      MeasuredClear.HotClean hot (ECDSAAdd.run ((specialize code a).instantiate read) m st).basis := by
  induction code generalizing st m with
  | nil => exact ⟨hs,hc⟩
  | cons i code ih =>
    have ht := fun j hj => hp j (List.mem_cons_of_mem i hj)
    have hht := fun j hj => hh j (List.mem_cons_of_mem i hj)
    have hi := hp i (by simp)
    have hhi := hh i (by simp)
    simp only [specialize,List.flatMap_cons,ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.run_append]
    cases i with
    | literal p =>
      simp only [WInstr.specialize,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      apply ih ht hht
      · exact literal_preserves_simulation (n := n) p _ _ _ _ hi st hs _
      · intro i
        rw [ECDSAAdd.run_preserves_outside p _ st (hot i) (hhi i)]
        exact hc i
    | lookup control ps =>
      have hip := hi
      dsimp only [PlacedPair] at hip
      have hmemq : lookupRoot windowRoot control ∈ windowRoot :: lookupRoot windowRoot control :: bits ++ windowPaths := by simp
      have hmemr : windowRoot ∈ windowRoot :: lookupRoot windowRoot control :: bits ++ windowPaths := by simp
      have hqa : lookupRoot windowRoot control ∉ portTargets (ps.take 258) := by
        intro hm; rw [portTargets,List.map_take] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemq (List.take_subset _ _ hm)
      have hqb : lookupRoot windowRoot control ∉ portTargets (ps.drop 258) := by
        intro hm; rw [portTargets,List.map_drop] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemq (List.drop_subset _ _ hm)
      have hra : windowRoot ∉ portTargets (ps.take 258) := by
        intro hm; rw [portTargets,List.map_take] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemr (List.take_subset _ _ hm)
      have hspec (m' : List Bool) := pairPort_specialize_run_control read control (ps.take 258) (ps.drop 258)
        a windowRoot m' st hip.2.1 hip.2.2.1 hqa hqb hra hs.2.2
      simp only [List.take_append_drop] at hspec
      rw [WInstr.specialize,hspec]
      apply ih ht hht
      · exact pair_lookup_preserves_simulation read control ps _ _ _ _ hi st hs
      · intro i
        have hout₁ : hot i ∉ portMask read (ps.take 258) a := fun hm => hhi i (by
          have h' := tableBitsMask_subset _ _ hm
          rw [portTargets,List.map_take] at h'
          exact List.take_subset _ _ h')
        have hout₂ : hot i ∉ portMask read (ps.drop 258) a := fun hm => hhi i (by
          have h' := tableBitsMask_subset _ _ hm
          rw [portTargets,List.map_drop] at h'
          exact List.drop_subset _ _ h')
        change tableXorState (portMask read (ps.drop 258) a) (st.basis (lookupRoot windowRoot control))
          (tableXorState (portMask read (ps.take 258) a) (st.basis (lookupRoot windowRoot control)) st.basis) (hot i) = false
        rw [tableXorState_outside _ _ _ _ hout₂,tableXorState_outside _ _ _ _ hout₁]
        exact hc i


def clearSource {n} (read : ConstantBit n → Bool) (site : MaskedSite n) : AdaptiveCircuit :=
  (clearProgram site 0).instantiate read Fin.elim0

theorem clearProgram_run {n} (read : ConstantBit n → Bool) (site : MaskedSite n)
    (start : Nat) (history : Fin start → Bool) :
    ((clearProgram site start).instantiate read history).run = (clearSource read site).run := by
  simp only [clearProgram,clearSource,MeasuredClear.measuredClear_run]

def blockRecords {n} : Block n → Nat
  | .plain code => codeRecords bits windowPaths windowRoot (normalizeW code)
  | .masked site => codeRecords bits windowPaths windowRoot (normalizeW site.prefix) +
      site.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) site.guard highPaths)+127)

def blockProgram {n} (b : Block n) (start : Nat) : Straight n start (start+blockRecords b) :=
  match b with
  | .plain code => compile bits windowPaths windowRoot (normalizeW code) start
  | .masked site => castFinish (by simp [blockRecords,clearData]; omega)
      ((compile bits windowPaths windowRoot (normalizeW site.prefix) start).append
        (clearProgram site (start+codeRecords bits windowPaths windowRoot (normalizeW site.prefix))))

def records {n} : Code n → Nat
  | [] => 0
  | b::code => blockRecords b + records code

def program {n} : (code : Code n) → (start : Nat) → Straight n start (start+records code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [records]; omega)
      ((blockProgram b start).append (program code (start+blockRecords b)))

def blockSource {n} (read : ConstantBit n → Bool) : Block n → AdaptiveCircuit
  | .plain code => source read bits windowPaths windowRoot (normalizeW code)
  | .masked site => (source read bits windowPaths windowRoot (normalizeW site.prefix)).seq
      (clearSource read site)

def sourceCode {n} (read : ConstantBit n → Bool) : Code n → AdaptiveCircuit
  | [] => .done
  | b::code => (blockSource read b).seq (sourceCode read code)

theorem blockProgram_run {n} (read : ConstantBit n → Bool) (b : Block n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram b start).instantiate read history).run = (blockSource read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | masked site =>
    rw [blockProgram,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearProgram_run read site _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSource,AdaptiveCircuit.run_seq]

theorem program_run {n} (read : ConstantBit n → Bool) (code : Code n)
    (start : Nat) (history : Fin start → Bool) :
    ((program code start).instantiate read history).run = (sourceCode read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [program,castFinish_instantiate,append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,blockProgram_run]
    simp only [sourceCode,AdaptiveCircuit.run_seq]


structure SiteGeometry {n} (site : MaskedSite n) : Prop where
  original : WEXUnlookup.SiteGeometry site
  placed : ∀ i ∈ site.code, Placed bits windowPaths windowRoot i
  bank : ∀ i ∈ site.code, HotAvoid i


theorem normalized_simulation {n} (read : ConstantBit n → Bool) (code : WCode n)
    (hp : ∀ i ∈ code, PlacedPair bits windowPaths windowRoot i) :
    ∃ cs : List ℂ, List.Forall₂ (SimulationBranch read code bits windowPaths windowRoot)
      (source read bits windowPaths windowRoot (normalizeW code)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cs,aligned,mass⟩ := pair_source_simulation read bits windowPaths windowRoot
    (by simp [bits,WEX.widthBits,windowPaths]) (normalizeW code) (pair_placed_normalize _ _ _ _ hp)
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb
  obtain ⟨m,hm,hb⟩ := hb
  refine ⟨m,by simpa [literalRecords_normalize] using hm,?_⟩
  intro address st hs
  simpa only [specialize_normalize_run] using hb address st hs

theorem masked_run {n} (read : ConstantBit n → Bool) (site : MaskedSite n)
    (hg : SiteGeometry site) (a : Nat) (st : ECDSAAdd.State) (m : List Bool)
    (hs : SimulationValid bits windowPaths windowRoot a st)
    (hh : MeasuredClear.HotClean hot st.basis) :
    ECDSAAdd.run ((specialize site.code a).instantiate read) m st =
      let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
      ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩ := by
  have hp : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
    intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have hhot : ∀ i ∈ site.prefix, HotAvoid i := by
    intro i hi; exact hg.bank i (List.mem_append_left _ hi)
  have hnext := reference_preserves read site.prefix a hp hhot st hs hh m
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  have hroot : site.guard ∉ portTargets site.ports := List.disjoint_left.mp hlast.2.2 (by simp [lookupRoot])
  simp only [MaskedSite.code,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
    ECDSAAdd.run_append,ECDSAAdd.run_take]
  simpa [specialize,WInstr.specialize] using portTemplate_run read (some site.guard) site.ports a windowRoot
    (m.drop (ECDSAAdd.measurementCount ((specialize site.prefix a).instantiate read)))
    (ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st)
    hlast.2.1 hroot hnext.1.2.2

def BlockSimulation {n} (read : ConstantBit n → Bool) (block : Block n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, SimulationValid bits windowPaths windowRoot address st →
      MeasuredClear.HotClean hot st.basis → BlockSafe read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference read address block) m st)

def BlockGeometry {n} : Block n → Prop
  | .plain code => (∀ i ∈ code, PlacedPair bits windowPaths windowRoot i) ∧
      (∀ i ∈ code, HotAvoid i)
  | .masked site => SiteGeometry site

theorem block_simulation {n} (read : ConstantBit n → Bool) (block : Block n)
    (hg : BlockGeometry block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimulation read block) (blockSource read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    obtain ⟨cs,aligned,mass⟩ := normalized_simulation read code hg.1
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    exact ⟨m,hm,fun address st hs _ _ => hb address st hs⟩
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hhot : ∀ i ∈ site.prefix, HotAvoid i := by
      intro i hi; exact hg.bank i (List.mem_append_left _ hi)
    obtain ⟨preCs,preAligned,preMass⟩ := normalized_simulation read site.prefix hp
    obtain ⟨cs,aligned,mass⟩ := clearProgram_coherent read site hg.original 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSource,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block.code,MaskedSite.code,literalRecords] using hm
      · intro a st hs hh hsafe
        let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
        have hn := reference_preserves read site.prefix a hp hhot st hs hh m
        have hrun := masked_run read site hg a st m hs hh
        have hclean : Clean (portTargets site.ports)
            (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
        have hvalid : MeasuredClear.HotClean hot next.basis ∧ Clean windowPaths next.basis ∧
            ∀ p ∈ site.ports, next.basis p.target = (next.basis site.guard &&
              decide (read (p.ref (tableAddressValue bits next.basis)) = p.value)) := by
          refine ⟨hn.2,hn.1.1,?_⟩
          rw [hn.1.2.1]
          exact loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
        have hclear : b₂.kraus (ket next.basis) =
            c₂ • ket (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          rw [← clear_eq_unload read site.ports a site.guard next.basis hclean]
          simpa [ket] using h₂ next.basis hvalid
        have hsigned : b₂.kraus (Bridge.signedKet next) = c₂ •
            Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st) := by
          rw [hrun]
          change b₂.kraus (Bridge.signedKet next) = c₂ • Bridge.signedKet
            ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩
          cases hphase : next.phase <;> simp [Bridge.signedKet,hphase,hclear,map_neg]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [h₁ a st hs,map_smul,hsigned]
        simp [smul_smul,blockReference,Block.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num


theorem block_placed {n} (b : Block n) (hg : BlockGeometry b) :
    (∀ i ∈ b.code, PlacedPair bits windowPaths windowRoot i) ∧
      (∀ i ∈ b.code, HotAvoid i) := by
  cases b with
  | plain code => exact hg
  | masked site => exact ⟨fun i hi => placed_implies_pair _ _ _ _ (hg.placed i hi),hg.bank⟩

def Simulation {n} (read : ConstantBit n → Bool) (code : Code n)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase code) ∧
    ∀ a st, SimulationValid bits windowPaths windowRoot a st →
      MeasuredClear.HotClean hot st.basis → Safe read a code st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference read a code) m st)

theorem source_simulation {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b) :
    ∃ cs : List ℂ, List.Forall₂ (Simulation read code) (sourceCode read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1],.cons ?_ .nil,by simp⟩
    exact ⟨[],rfl,fun a st _ _ _ => by simp [reference,erase,specialize,ECDSAAdd.ShorPort.Tmpl.instantiate,ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁,h₁,mass₁⟩ := block_simulation read b (hg b (by simp))
    obtain ⟨cs₂,h₂,mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    have geo := block_placed b (hg b (by simp))
    refine ⟨coherentSeqCoefficients cs₁ cs₂,?_,?_⟩
    · rw [sourceCode,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁,len₁,run₁⟩ := hb₁
      obtain ⟨m₂,len₂,run₂⟩ := hb₂
      refine ⟨m₁++m₂,?_,?_⟩
      · simp [erase,List.length_append,len₁,len₂]
      · intro a st hs hh hsafe
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference read a b) :=
          len₁.trans (specialize_counts read b.code a).2.symm
        have hn := reference_preserves read b.code a geo.1 geo.2 st hs hh m₁
        change SimulationValid bits windowPaths windowRoot a
            (ECDSAAdd.run (blockReference read a b) m₁ st) ∧ MeasuredClear.HotClean hot
            (ECDSAAdd.run (blockReference read a b) m₁ st).basis at hn
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hh hsafe.1,map_smul,run₂ a (ECDSAAdd.run (blockReference read a b) m₁ st) hn.1 hn.2 (hsafe.2 m₁ hm),
          reference_cons,run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass,mass₁,mass₂]
      norm_num

/-- All addresses share one normalized branch coefficient list. -/
theorem program_coherent {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe read (tableAddressValue bits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference read (tableAddressValue bits s) code) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result)
      (fun s => Clean windowPaths s ∧ s windowRoot = true ∧ MeasuredClear.HotClean hot s ∧ Valid s) := by
  obtain ⟨cs,aligned,mass⟩ := source_simulation read code hg
  refine ⟨cs,?_,mass⟩
  rw [program_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m,_,h⟩ := hb
  have he := h (tableAddressValue bits s) ⟨false,s⟩ ⟨hs.1,rfl,hs.2.1⟩ hs.2.2.1 (hsafe s hs.2.2.2)
  rw [Bridge.signedKet_false,hrun s hs.2.2.2 m,Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.WEXUnlookupWidth13


namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] MeasuredClear.measuredClear

theorem reference_preserves {n} (read : ConstantBit n → Bool) (code : WCode n) (a : Nat)
    (hp : ∀ i ∈ code, PlacedPair bits windowPaths windowRoot i)
    (hh : ∀ i ∈ code, HotAvoid i)
    (st : ECDSAAdd.State) (hs : SimulationValid bits windowPaths windowRoot a st)
    (hc : MeasuredClear.HotClean hot st.basis) (m : List Bool) :
    SimulationValid bits windowPaths windowRoot a
        (ECDSAAdd.run ((specialize code a).instantiate read) m st) ∧
      MeasuredClear.HotClean hot (ECDSAAdd.run ((specialize code a).instantiate read) m st).basis := by
  induction code generalizing st m with
  | nil => exact ⟨hs,hc⟩
  | cons i code ih =>
    have ht := fun j hj => hp j (List.mem_cons_of_mem i hj)
    have hht := fun j hj => hh j (List.mem_cons_of_mem i hj)
    have hi := hp i (by simp)
    have hhi := hh i (by simp)
    simp only [specialize,List.flatMap_cons,ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.run_append]
    cases i with
    | literal p =>
      simp only [WInstr.specialize,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      apply ih ht hht
      · exact literal_preserves_simulation (n := n) p _ _ _ _ hi st hs _
      · intro i
        rw [ECDSAAdd.run_preserves_outside p _ st (hot i) (hhi i)]
        exact hc i
    | lookup control ps =>
      have hip := hi
      dsimp only [PlacedPair] at hip
      have hmemq : lookupRoot windowRoot control ∈ windowRoot :: lookupRoot windowRoot control :: bits ++ windowPaths := by simp
      have hmemr : windowRoot ∈ windowRoot :: lookupRoot windowRoot control :: bits ++ windowPaths := by simp
      have hqa : lookupRoot windowRoot control ∉ portTargets (ps.take 258) := by
        intro hm; rw [portTargets,List.map_take] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemq (List.take_subset _ _ hm)
      have hqb : lookupRoot windowRoot control ∉ portTargets (ps.drop 258) := by
        intro hm; rw [portTargets,List.map_drop] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemq (List.drop_subset _ _ hm)
      have hra : windowRoot ∉ portTargets (ps.take 258) := by
        intro hm; rw [portTargets,List.map_take] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemr (List.take_subset _ _ hm)
      have hspec (m' : List Bool) := pairPort_specialize_run_control read control (ps.take 258) (ps.drop 258)
        a windowRoot m' st hip.2.1 hip.2.2.1 hqa hqb hra hs.2.2
      simp only [List.take_append_drop] at hspec
      rw [WInstr.specialize,hspec]
      apply ih ht hht
      · exact pair_lookup_preserves_simulation read control ps _ _ _ _ hi st hs
      · intro i
        have hout₁ : hot i ∉ portMask read (ps.take 258) a := fun hm => hhi i (by
          have h' := tableBitsMask_subset _ _ hm
          rw [portTargets,List.map_take] at h'
          exact List.take_subset _ _ h')
        have hout₂ : hot i ∉ portMask read (ps.drop 258) a := fun hm => hhi i (by
          have h' := tableBitsMask_subset _ _ hm
          rw [portTargets,List.map_drop] at h'
          exact List.drop_subset _ _ h')
        change tableXorState (portMask read (ps.drop 258) a) (st.basis (lookupRoot windowRoot control))
          (tableXorState (portMask read (ps.take 258) a) (st.basis (lookupRoot windowRoot control)) st.basis) (hot i) = false
        rw [tableXorState_outside _ _ _ _ hout₂,tableXorState_outside _ _ _ _ hout₁]
        exact hc i


def clearSource {n} (read : ConstantBit n → Bool) (site : MaskedSite n) : AdaptiveCircuit :=
  (clearProgram site 0).instantiate read Fin.elim0

theorem clearProgram_run {n} (read : ConstantBit n → Bool) (site : MaskedSite n)
    (start : Nat) (history : Fin start → Bool) :
    ((clearProgram site start).instantiate read history).run = (clearSource read site).run := by
  simp only [clearProgram,clearSource,MeasuredClear.measuredClear_run]

def blockRecords {n} : Block n → Nat
  | .plain code => codeRecords bits windowPaths windowRoot (normalizeW code)
  | .masked site => codeRecords bits windowPaths windowRoot (normalizeW site.prefix) +
      site.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) site.guard highPaths)+127)

def blockProgram {n} (b : Block n) (start : Nat) : Straight n start (start+blockRecords b) :=
  match b with
  | .plain code => compile bits windowPaths windowRoot (normalizeW code) start
  | .masked site => castFinish (by simp [blockRecords,clearData]; omega)
      ((compile bits windowPaths windowRoot (normalizeW site.prefix) start).append
        (clearProgram site (start+codeRecords bits windowPaths windowRoot (normalizeW site.prefix))))

def records {n} : Code n → Nat
  | [] => 0
  | b::code => blockRecords b + records code

def program {n} : (code : Code n) → (start : Nat) → Straight n start (start+records code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [records]; omega)
      ((blockProgram b start).append (program code (start+blockRecords b)))

def blockSource {n} (read : ConstantBit n → Bool) : Block n → AdaptiveCircuit
  | .plain code => source read bits windowPaths windowRoot (normalizeW code)
  | .masked site => (source read bits windowPaths windowRoot (normalizeW site.prefix)).seq
      (clearSource read site)

def sourceCode {n} (read : ConstantBit n → Bool) : Code n → AdaptiveCircuit
  | [] => .done
  | b::code => (blockSource read b).seq (sourceCode read code)

theorem blockProgram_run {n} (read : ConstantBit n → Bool) (b : Block n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram b start).instantiate read history).run = (blockSource read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | masked site =>
    rw [blockProgram,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearProgram_run read site _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSource,AdaptiveCircuit.run_seq]

theorem program_run {n} (read : ConstantBit n → Bool) (code : Code n)
    (start : Nat) (history : Fin start → Bool) :
    ((program code start).instantiate read history).run = (sourceCode read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [program,castFinish_instantiate,append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,blockProgram_run]
    simp only [sourceCode,AdaptiveCircuit.run_seq]


structure SiteGeometry {n} (site : MaskedSite n) : Prop where
  original : WEXUnlookup.SiteGeometry site
  placed : ∀ i ∈ site.code, Placed bits windowPaths windowRoot i
  bank : ∀ i ∈ site.code, HotAvoid i


theorem normalized_simulation {n} (read : ConstantBit n → Bool) (code : WCode n)
    (hp : ∀ i ∈ code, PlacedPair bits windowPaths windowRoot i) :
    ∃ cs : List ℂ, List.Forall₂ (SimulationBranch read code bits windowPaths windowRoot)
      (source read bits windowPaths windowRoot (normalizeW code)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cs,aligned,mass⟩ := pair_source_simulation read bits windowPaths windowRoot
    (by simp [bits,WEX.widthBits,windowPaths]) (normalizeW code) (pair_placed_normalize _ _ _ _ hp)
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb
  obtain ⟨m,hm,hb⟩ := hb
  refine ⟨m,by simpa [literalRecords_normalize] using hm,?_⟩
  intro address st hs
  simpa only [specialize_normalize_run] using hb address st hs

theorem masked_run {n} (read : ConstantBit n → Bool) (site : MaskedSite n)
    (hg : SiteGeometry site) (a : Nat) (st : ECDSAAdd.State) (m : List Bool)
    (hs : SimulationValid bits windowPaths windowRoot a st)
    (hh : MeasuredClear.HotClean hot st.basis) :
    ECDSAAdd.run ((specialize site.code a).instantiate read) m st =
      let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
      ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩ := by
  have hp : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
    intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have hhot : ∀ i ∈ site.prefix, HotAvoid i := by
    intro i hi; exact hg.bank i (List.mem_append_left _ hi)
  have hnext := reference_preserves read site.prefix a hp hhot st hs hh m
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  have hroot : site.guard ∉ portTargets site.ports := List.disjoint_left.mp hlast.2.2 (by simp [lookupRoot])
  simp only [MaskedSite.code,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
    ECDSAAdd.run_append,ECDSAAdd.run_take]
  simpa [specialize,WInstr.specialize] using portTemplate_run read (some site.guard) site.ports a windowRoot
    (m.drop (ECDSAAdd.measurementCount ((specialize site.prefix a).instantiate read)))
    (ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st)
    hlast.2.1 hroot hnext.1.2.2

def BlockSimulation {n} (read : ConstantBit n → Bool) (block : Block n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, SimulationValid bits windowPaths windowRoot address st →
      MeasuredClear.HotClean hot st.basis → BlockSafe read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference read address block) m st)

def BlockGeometry {n} : Block n → Prop
  | .plain code => (∀ i ∈ code, PlacedPair bits windowPaths windowRoot i) ∧
      (∀ i ∈ code, HotAvoid i)
  | .masked site => SiteGeometry site

theorem block_simulation {n} (read : ConstantBit n → Bool) (block : Block n)
    (hg : BlockGeometry block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimulation read block) (blockSource read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    obtain ⟨cs,aligned,mass⟩ := normalized_simulation read code hg.1
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    exact ⟨m,hm,fun address st hs _ _ => hb address st hs⟩
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hhot : ∀ i ∈ site.prefix, HotAvoid i := by
      intro i hi; exact hg.bank i (List.mem_append_left _ hi)
    obtain ⟨preCs,preAligned,preMass⟩ := normalized_simulation read site.prefix hp
    obtain ⟨cs,aligned,mass⟩ := clearProgram_coherent read site hg.original 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSource,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block.code,MaskedSite.code,literalRecords] using hm
      · intro a st hs hh hsafe
        let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
        have hn := reference_preserves read site.prefix a hp hhot st hs hh m
        have hrun := masked_run read site hg a st m hs hh
        have hclean : Clean (portTargets site.ports)
            (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
        have hvalid : MeasuredClear.HotClean hot next.basis ∧ Clean windowPaths next.basis ∧
            ∀ p ∈ site.ports, next.basis p.target = (next.basis site.guard &&
              decide (read (p.ref (tableAddressValue bits next.basis)) = p.value)) := by
          refine ⟨hn.2,hn.1.1,?_⟩
          rw [hn.1.2.1]
          exact loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
        have hclear : b₂.kraus (ket next.basis) =
            c₂ • ket (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          rw [← clear_eq_unload read site.ports a site.guard next.basis hclean]
          simpa [ket] using h₂ next.basis hvalid
        have hsigned : b₂.kraus (Bridge.signedKet next) = c₂ •
            Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st) := by
          rw [hrun]
          change b₂.kraus (Bridge.signedKet next) = c₂ • Bridge.signedKet
            ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩
          cases hphase : next.phase <;> simp [Bridge.signedKet,hphase,hclear,map_neg]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [h₁ a st hs,map_smul,hsigned]
        simp [smul_smul,blockReference,Block.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num


theorem block_placed {n} (b : Block n) (hg : BlockGeometry b) :
    (∀ i ∈ b.code, PlacedPair bits windowPaths windowRoot i) ∧
      (∀ i ∈ b.code, HotAvoid i) := by
  cases b with
  | plain code => exact hg
  | masked site => exact ⟨fun i hi => placed_implies_pair _ _ _ _ (hg.placed i hi),hg.bank⟩

def Simulation {n} (read : ConstantBit n → Bool) (code : Code n)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase code) ∧
    ∀ a st, SimulationValid bits windowPaths windowRoot a st →
      MeasuredClear.HotClean hot st.basis → Safe read a code st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference read a code) m st)

theorem source_simulation {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b) :
    ∃ cs : List ℂ, List.Forall₂ (Simulation read code) (sourceCode read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1],.cons ?_ .nil,by simp⟩
    exact ⟨[],rfl,fun a st _ _ _ => by simp [reference,erase,specialize,ECDSAAdd.ShorPort.Tmpl.instantiate,ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁,h₁,mass₁⟩ := block_simulation read b (hg b (by simp))
    obtain ⟨cs₂,h₂,mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    have geo := block_placed b (hg b (by simp))
    refine ⟨coherentSeqCoefficients cs₁ cs₂,?_,?_⟩
    · rw [sourceCode,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁,len₁,run₁⟩ := hb₁
      obtain ⟨m₂,len₂,run₂⟩ := hb₂
      refine ⟨m₁++m₂,?_,?_⟩
      · simp [erase,List.length_append,len₁,len₂]
      · intro a st hs hh hsafe
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference read a b) :=
          len₁.trans (specialize_counts read b.code a).2.symm
        have hn := reference_preserves read b.code a geo.1 geo.2 st hs hh m₁
        change SimulationValid bits windowPaths windowRoot a
            (ECDSAAdd.run (blockReference read a b) m₁ st) ∧ MeasuredClear.HotClean hot
            (ECDSAAdd.run (blockReference read a b) m₁ st).basis at hn
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hh hsafe.1,map_smul,run₂ a (ECDSAAdd.run (blockReference read a b) m₁ st) hn.1 hn.2 (hsafe.2 m₁ hm),
          reference_cons,run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass,mass₁,mass₂]
      norm_num

/-- All addresses share one normalized branch coefficient list. -/
theorem program_coherent {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe read (tableAddressValue bits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference read (tableAddressValue bits s) code) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result)
      (fun s => Clean windowPaths s ∧ s windowRoot = true ∧ MeasuredClear.HotClean hot s ∧ Valid s) := by
  obtain ⟨cs,aligned,mass⟩ := source_simulation read code hg
  refine ⟨cs,?_,mass⟩
  rw [program_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m,_,h⟩ := hb
  have he := h (tableAddressValue bits s) ⟨false,s⟩ ⟨hs.1,rfl,hs.2.1⟩ hs.2.2.1 (hsafe s hs.2.2.2)
  rw [Bridge.signedKet_false,hrun s hs.2.2.2 m,Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] ECDSAAdd.run program blockProgram clearProgram

theorem row_geometry : ∀ b ∈ row, BlockGeometry b := by
  intro b hb
  have hnarrow : ∀ i ∈ b.code, PlacedPair bits windowPaths windowRoot i := by
    intro i hi
    have hmem : i ∈ clearReferenceRow probeRows := erase_row ▸ block_mem_erase row b hb i hi
    simpa only [bits] using WEX.clearReferenceRow_width_placed 13 (by omega) i hmem
  have hold := WEXUnlookup.row_geometry b hb
  cases b with
  | plain code => exact ⟨hnarrow,hold.2⟩
  | masked site =>
    have hq : ∀ i ∈ (Block.masked site).code, Placed bits windowPaths windowRoot i := by
      rcases row_masked site hb with h3 | hs
      · have ht := row3_masked_tight site h3
        intro i hi
        have hmem : i ∈ tightReferenceRow probeRows := erase_tightRow ▸ block_mem_erase tightRow _ ht i hi
        simpa only [bits] using WEX.tightReferenceRow_width_placed 13 (by omega) probeRows i hmem
      · subst hs
        exact scr_placed bits hnarrow
    exact ⟨hold,hq,hold.bank⟩

theorem row_safe (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (s : BasisState) (hs : liveReady s) :
    Safe (readConstant coeffs Q) (tableAddressValue bits s) row ⟨false,s⟩ := by
  let a := tableAddressValue bits s
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
    exact row_safe_of_boundary (readConstant coeffs Q) a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial hs.2.2


def rowState (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (s : BasisState) : BasisState :=
  pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q (tableAddressValue bits s)) s

theorem row_coherent (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program row start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program_coherent (readConstant coeffs Q) row row_geometry liveReady (rowState coeffs Q)
    (row_safe coeffs Q hQ hn) (by
      intro s hs m
      have old := clearReferenceRow_run_any (tableAddressValue bits s) coeffs Q hQ hn s hs m
      rw [specialize_normalize_run] at old
      simpa only [reference,erase_row,rowState] using old) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩
end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] ECDSAAdd.run program blockProgram clearProgram

theorem row_geometry : ∀ b ∈ row, BlockGeometry b := by
  intro b hb
  have hnarrow : ∀ i ∈ b.code, PlacedPair bits windowPaths windowRoot i := by
    intro i hi
    have hmem : i ∈ clearReferenceRow probeRows := erase_row ▸ block_mem_erase row b hb i hi
    simpa only [bits] using WEX.clearReferenceRow_width_placed 14 (by omega) i hmem
  have hold := WEXUnlookup.row_geometry b hb
  cases b with
  | plain code => exact ⟨hnarrow,hold.2⟩
  | masked site =>
    have hq : ∀ i ∈ (Block.masked site).code, Placed bits windowPaths windowRoot i := by
      rcases row_masked site hb with h3 | hs
      · have ht := row3_masked_tight site h3
        intro i hi
        have hmem : i ∈ tightReferenceRow probeRows := erase_tightRow ▸ block_mem_erase tightRow _ ht i hi
        simpa only [bits] using WEX.tightReferenceRow_width_placed 14 (by omega) probeRows i hmem
      · subst hs
        exact scr_placed bits hnarrow
    exact ⟨hold,hq,hold.bank⟩

theorem row_safe (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (s : BasisState) (hs : liveReady s) :
    Safe (readConstant coeffs Q) (tableAddressValue bits s) row ⟨false,s⟩ := by
  let a := tableAddressValue bits s
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
    exact row_safe_of_boundary (readConstant coeffs Q) a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial hs.2.2


def rowState (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (s : BasisState) : BasisState :=
  pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q (tableAddressValue bits s)) s

theorem row_coherent (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program row start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program_coherent (readConstant coeffs Q) row row_geometry liveReady (rowState coeffs Q)
    (row_safe coeffs Q hQ hn) (by
      intro s hs m
      have old := clearReferenceRow_run_any (tableAddressValue bits s) coeffs Q hQ hn s hs m
      rw [specialize_normalize_run] at old
      simpa only [reference,erase_row,rowState] using old) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩
end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program blockProgram clearProgram

def blockCCX {n} : Block n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * 8191
  | .masked site => literalToffolis (normalizeW site.prefix) + 8191 + 190

def blockMasks {n} : Block n → Nat
  | .plain _ => 0
  | .masked _ => 1

def ccx {n} : Code n → Nat
  | [] => 0
  | b::code => blockCCX b + ccx code

def masks {n} : Code n → Nat
  | [] => 0
  | b::code => blockMasks b + masks code


theorem block_tCount {n} (read : ConstantBit n → Bool) (b : Block n) (hg : BlockGeometry b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram b start).instantiate read history).tCount = 7 * blockCCX b := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW code)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram,WEX.compile_tCount read bits windowPaths windowRoot (normalizeW code) hl start history,traversals_normalize]
    simp [blockCCX,bits,WEX.widthBits,Nat.mul_add,Nat.mul_assoc]
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW site.prefix)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    rw [blockProgram,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearProgram_tCount read site hg.original _ h),
      WEX.compile_tCount read bits windowPaths windowRoot (normalizeW site.prefix) hl start history,traversals_normalize]
    simp [blockCCX,MaskedSite.prefix,traversals,bits,WEX.widthBits]
    ring

theorem program_tCount {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b) (start : Nat) (history : Fin start → Bool) :
    ((program code start).instantiate read history).tCount = 7 * ccx code := by
  induction code generalizing start with
  | nil => simp [program,records,ccx,Straight.instantiate,AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [program,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      block_tCount read b (hg b (by simp))]
    simp [ccx,Nat.mul_add]

end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program blockProgram clearProgram

def blockCCX {n} : Block n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * 16383
  | .masked site => literalToffolis (normalizeW site.prefix) + 16383 + 254

def blockMasks {n} : Block n → Nat
  | .plain _ => 0
  | .masked _ => 1

def ccx {n} : Code n → Nat
  | [] => 0
  | b::code => blockCCX b + ccx code

def masks {n} : Code n → Nat
  | [] => 0
  | b::code => blockMasks b + masks code


theorem block_tCount {n} (read : ConstantBit n → Bool) (b : Block n) (hg : BlockGeometry b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram b start).instantiate read history).tCount = 7 * blockCCX b := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW code)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram,WEX.compile_tCount read bits windowPaths windowRoot (normalizeW code) hl start history,traversals_normalize]
    simp [blockCCX,bits,WEX.widthBits,Nat.mul_add,Nat.mul_assoc]
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW site.prefix)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    rw [blockProgram,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearProgram_tCount read site hg.original _ h),
      WEX.compile_tCount read bits windowPaths windowRoot (normalizeW site.prefix) hl start history,traversals_normalize]
    simp [blockCCX,MaskedSite.prefix,traversals,bits,WEX.widthBits]
    ring

theorem program_tCount {n} (read : ConstantBit n → Bool) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeometry b) (start : Nat) (history : Fin start → Bool) :
    ((program code start).instantiate read history).tCount = 7 * ccx code := by
  induction code generalizing start with
  | nil => simp [program,records,ccx,Straight.instantiate,AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [program,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      block_tCount read b (hg b (by simp))]
    simp [ccx,Nat.mul_add]

end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program blockProgram clearProgram

theorem block_ccx_relation {n} (b : Block n) :
    blockCCX b + blockMasks b * 8001 = literalToffolis (normalizeW b.code) + traversals b.code * 8191 := by
  cases b with
  | plain code => simp [blockCCX,blockMasks,Block.code]
  | masked site =>
    have hl : literalToffolis (normalizeW site.code) = literalToffolis (normalizeW site.prefix) := by
      simp [MaskedSite.code,MaskedSite.prefix,normalizeW,normalizeWInstr,literalToffolis]
    have ht : traversals site.code = 2 := by
      simp [MaskedSite.code,MaskedSite.prefix,traversals]
    simp only [blockCCX,blockMasks,Block.code]
    omega

theorem ccx_relation {n} (code : Code n) :
    ccx code + masks code * 8001 = literalToffolis (normalizeW (erase code)) + traversals (erase code) * 8191 := by
  induction code with
  | nil => simp [ccx,masks,erase,normalizeW,literalToffolis,traversals]
  | cons b code ih =>
    have hb := block_ccx_relation b
    simp only [ccx,masks,erase_cons,normalize_append,literalToffolis_append,traversals_append,Nat.add_mul]
    omega

theorem row_masks : masks row = 6 := rfl


@[simp] theorem records_old_append {n} (a b : WCode n) :
    codeRecords bits windowPaths windowRoot (a++b) =
      codeRecords bits windowPaths windowRoot a + codeRecords bits windowPaths windowRoot b := by
  induction a with
  | nil => simp [codeRecords]
  | cons i code ih => cases i <;> simp [codeRecords,ih,Nat.add_assoc]

theorem single_lookup_records {n} (bits paths : List Wire) (root : Wire) (c : Option Wire)
    (ports : List (LookupPort n)) (hlen : bits.length ≤ paths.length)
    (hn : (lookupRoot root c :: bits ++ paths).Nodup) :
    codeRecords bits paths root ([.lookup c ports] : WCode n) = 2^bits.length-1 := by
  simp only [codeRecords,Nat.add_zero]
  exact portOps_measurements ports bits paths (lookupRoot root c) hlen hn

theorem site_old_clear_records {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    codeRecords bits windowPaths windowRoot ([.lookup (some site.guard) site.ports] : WCode n) = 8191 := by
  have hp := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  have h := single_lookup_records bits windowPaths windowRoot (some site.guard) site.ports
    (by simp [bits,WEX.widthBits,windowPaths]) hp.1
  exact h.trans (by decide +kernel)

theorem block_records_relation {n} (b : Block n) (hg : BlockGeometry b) :
    blockRecords b + blockMasks b * 8001 = codeRecords bits windowPaths windowRoot (normalizeW b.code) + blockLen b := by
  cases b with
  | plain code => simp [blockRecords,blockMasks,Block.code,blockLen]
  | masked site =>
    rw [blockRecords,high_records site hg.original]
    rw [Block.code,MaskedSite.code,normalize_append,records_old_append]
    have hc : normalizeW ([.lookup (some site.guard) site.ports] : WCode n) = [.lookup (some site.guard) site.ports] := by simp [normalizeW,normalizeWInstr]
    rw [hc,site_old_clear_records site hg]
    have hm : blockMasks (Block.masked site) = 1 := rfl
    have hl : blockLen (Block.masked site) = site.ports.length := rfl
    omega

theorem records_relation {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b) :
    records code + masks code * 8001 = codeRecords bits windowPaths windowRoot (normalizeW (erase code)) + lens code := by
  induction code with
  | nil => simp [records,masks,erase,normalizeW,codeRecords,lens]
  | cons b code ih =>
    have hb := block_records_relation b (hg b (by simp))
    have ht := ih (fun d hd => hg d (by simp [hd]))
    simp only [records,masks,lens,erase_cons,normalize_append,records_old_append,Nat.add_mul]
    omega

theorem records_credit5 {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hm : masks code = 6) (hl : lens code = 1796)
    (ho : codeRecords bits windowPaths windowRoot (normalizeW (erase code)) = 1679764) :
    records code = 1633554 := by
  have h := records_relation code hg
  rw [hm,ho,hl] at h
  omega

theorem row_records : records row = 1633554 := by
  apply records_credit5 row row_geometry row_masks row_lens
  have h := WEX.clearReferenceRow_width_records 13 (by omega)
  have hn : 1556899 + 15 * (2 ^ 13 - 1) = 1679764 := by norm_num
  exact (congrArg (fun c : WCode 32768 => codeRecords bits windowPaths windowRoot (normalizeW c)) erase_row).trans (by simpa only [bits] using h.trans hn)

end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program blockProgram clearProgram

theorem block_ccx_relation {n} (b : Block n) :
    blockCCX b + blockMasks b * 16129 = literalToffolis (normalizeW b.code) + traversals b.code * 16383 := by
  cases b with
  | plain code => simp [blockCCX,blockMasks,Block.code]
  | masked site =>
    have hl : literalToffolis (normalizeW site.code) = literalToffolis (normalizeW site.prefix) := by
      simp [MaskedSite.code,MaskedSite.prefix,normalizeW,normalizeWInstr,literalToffolis]
    have ht : traversals site.code = 2 := by
      simp [MaskedSite.code,MaskedSite.prefix,traversals]
    simp only [blockCCX,blockMasks,Block.code]
    omega

theorem ccx_relation {n} (code : Code n) :
    ccx code + masks code * 16129 = literalToffolis (normalizeW (erase code)) + traversals (erase code) * 16383 := by
  induction code with
  | nil => simp [ccx,masks,erase,normalizeW,literalToffolis,traversals]
  | cons b code ih =>
    have hb := block_ccx_relation b
    simp only [ccx,masks,erase_cons,normalize_append,literalToffolis_append,traversals_append,Nat.add_mul]
    omega

theorem row_masks : masks row = 6 := rfl


@[simp] theorem records_old_append {n} (a b : WCode n) :
    codeRecords bits windowPaths windowRoot (a++b) =
      codeRecords bits windowPaths windowRoot a + codeRecords bits windowPaths windowRoot b := by
  induction a with
  | nil => simp [codeRecords]
  | cons i code ih => cases i <;> simp [codeRecords,ih,Nat.add_assoc]

theorem single_lookup_records {n} (bits paths : List Wire) (root : Wire) (c : Option Wire)
    (ports : List (LookupPort n)) (hlen : bits.length ≤ paths.length)
    (hn : (lookupRoot root c :: bits ++ paths).Nodup) :
    codeRecords bits paths root ([.lookup c ports] : WCode n) = 2^bits.length-1 := by
  simp only [codeRecords,Nat.add_zero]
  exact portOps_measurements ports bits paths (lookupRoot root c) hlen hn

theorem site_old_clear_records {n} (site : MaskedSite n) (hg : SiteGeometry site) :
    codeRecords bits windowPaths windowRoot ([.lookup (some site.guard) site.ports] : WCode n) = 16383 := by
  have hp := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  have h := single_lookup_records bits windowPaths windowRoot (some site.guard) site.ports
    (by simp [bits,WEX.widthBits,windowPaths]) hp.1
  exact h.trans (by decide +kernel)

theorem block_records_relation {n} (b : Block n) (hg : BlockGeometry b) :
    blockRecords b + blockMasks b * 16129 = codeRecords bits windowPaths windowRoot (normalizeW b.code) + blockLen b := by
  cases b with
  | plain code => simp [blockRecords,blockMasks,Block.code,blockLen]
  | masked site =>
    rw [blockRecords,high_records site hg.original]
    rw [Block.code,MaskedSite.code,normalize_append,records_old_append]
    have hc : normalizeW ([.lookup (some site.guard) site.ports] : WCode n) = [.lookup (some site.guard) site.ports] := by simp [normalizeW,normalizeWInstr]
    rw [hc,site_old_clear_records site hg]
    have hm : blockMasks (Block.masked site) = 1 := rfl
    have hl : blockLen (Block.masked site) = site.ports.length := rfl
    omega

theorem records_relation {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b) :
    records code + masks code * 16129 = codeRecords bits windowPaths windowRoot (normalizeW (erase code)) + lens code := by
  induction code with
  | nil => simp [records,masks,erase,normalizeW,codeRecords,lens]
  | cons b code ih =>
    have hb := block_records_relation b (hg b (by simp))
    have ht := ih (fun d hd => hg d (by simp [hd]))
    simp only [records,masks,lens,erase_cons,normalize_append,records_old_append,Nat.add_mul]
    omega

theorem records_credit5 {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hm : masks code = 6) (hl : lens code = 1796)
    (ho : codeRecords bits windowPaths windowRoot (normalizeW (erase code)) = 1802644) :
    records code = 1707666 := by
  have h := records_relation code hg
  rw [hm,ho,hl] at h
  omega

theorem row_records : records row = 1707666 := by
  apply records_credit5 row row_geometry row_masks row_lens
  have h := WEX.clearReferenceRow_width_records 14 (by omega)
  have hn : 1556899 + 15 * (2 ^ 14 - 1) = 1802644 := by norm_num
  exact (congrArg (fun c : WCode 32768 => codeRecords bits windowPaths windowRoot (normalizeW c)) erase_row).trans (by simpa only [bits] using h.trans hn)

end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.wires ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

theorem block_wellFormed {n} (b : Block n) (hg : BlockGeometry b)
    (hp : ∀ p, WInstr.literal p ∈ b.code → GatePhysical p) (start : Nat) :
    (blockProgram b start).WellFormed := by
  cases b with
  | plain code =>
    unfold blockProgram
    exact pair_compile_wellFormed _ _ _ _ (by simp [bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hg.1) (normalized_literals_valid code hp) start
  | masked site =>
    have hpref : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hphys : ∀ p, WInstr.literal p ∈ site.prefix → GatePhysical p := by
      intro p hm; exact hp p (List.mem_append_left _ hm)
    rw [blockProgram,castFinish_wellFormed]
    exact straight_append_wellFormed _ _
      (pair_compile_wellFormed _ _ _ _ (by simp [bits,WEX.widthBits,windowPaths])
        (pair_placed_normalize _ _ _ _ hpref) (normalized_literals_valid site.prefix hphys) start)
      (clearProgram_wellFormed site hg.original _)

theorem program_wellFormed {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hp : ∀ p, WInstr.literal p ∈ erase code → GatePhysical p) (start : Nat) :
    (program code start).WellFormed := by
  induction code generalizing start with
  | nil => simp [program,records,Straight.WellFormed]
  | cons b code ih =>
    rw [program,castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact block_wellFormed b (hg b (by simp)) (fun p hm => hp p (by simp [erase_cons,hm])) start
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase_cons,hm])) _

theorem row_wellFormed (start : Nat) : (program row start).WellFormed := by
  apply program_wellFormed row row_geometry
  intro p hp
  rw [erase_row] at hp
  exact clearReferenceRow_physical p hp

open AndGadget WEXCredit in
 theorem block_residue {n} (b : Block n) (start : Nat) : residue (blockProgram b start) = 0 := by
  cases b with
  | plain code => rw [blockProgram]; exact compile_residue _ _ _ _ _
  | masked site => simp [blockProgram,residue_cast,residue_append,compile_residue,
      clearProgram,MeasuredClear.measuredClear_residue]

open AndGadget in
 theorem program_residue {n} (code : Code n) (start : Nat) : residue (program code start) = 0 := by
  induction code generalizing start with
  | nil => simp [program,records]
  | cons b code ih => simp [program,residue_cast,residue_append,block_residue,ih]

theorem old_compile_support {n} (code : WCode n) (h : OldWithin code) (start : Nat) :
    ChallengeMigration.straightWires (compile bits windowPaths windowRoot (normalizeW code) start) ⊆ sourceSupport := by
  have hn := oldWithin_normalize code h
  exact compile_support _ _ _ _ sourceSupport (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hn.1 hn.2 start


theorem block_support {n} (b : Block n) (hg : BlockGeometry b) (hw : OldWithin b.code) (start : Nat) :
    ChallengeMigration.straightWires (blockProgram b start) ⊆ logicalSupport := by
  cases b with
  | plain code => rw [blockProgram]; exact (old_compile_support code hw start).trans (List.subset_append_left _ _)
  | masked site =>
    have hp : OldWithin site.prefix := oldWithin_sub site.prefix site.code (List.subset_append_left _ _) hw
    rw [blockProgram,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨(old_compile_support site.prefix hp start).trans (List.subset_append_left _ _),
      clearProgram_support site hg.original _⟩

theorem program_support {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hw : OldWithin (erase code)) (start : Nat) :
    ChallengeMigration.straightWires (program code start) ⊆ logicalSupport := by
  induction code generalizing start with
  | nil => simp [program,records,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hb : OldWithin b.code := oldWithin_sub b.code (erase (b::code)) (by rw [erase_cons]; exact List.subset_append_left _ _) hw
    have ht : OldWithin (erase code) := oldWithin_sub (erase code) (erase (b::code)) (by rw [erase_cons]; exact List.subset_append_right _ _) hw
    rw [program,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨block_support b (hg b (by simp)) hb start,
      ih (fun d hd => hg d (by simp [hd])) ht _⟩

theorem row_support (start : Nat) : ChallengeMigration.straightWires (program row start) ⊆ logicalSupport := by
  apply program_support row row_geometry
  rw [erase_row]
  exact row_oldWithin

end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.wires ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

theorem block_wellFormed {n} (b : Block n) (hg : BlockGeometry b)
    (hp : ∀ p, WInstr.literal p ∈ b.code → GatePhysical p) (start : Nat) :
    (blockProgram b start).WellFormed := by
  cases b with
  | plain code =>
    unfold blockProgram
    exact pair_compile_wellFormed _ _ _ _ (by simp [bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hg.1) (normalized_literals_valid code hp) start
  | masked site =>
    have hpref : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hphys : ∀ p, WInstr.literal p ∈ site.prefix → GatePhysical p := by
      intro p hm; exact hp p (List.mem_append_left _ hm)
    rw [blockProgram,castFinish_wellFormed]
    exact straight_append_wellFormed _ _
      (pair_compile_wellFormed _ _ _ _ (by simp [bits,WEX.widthBits,windowPaths])
        (pair_placed_normalize _ _ _ _ hpref) (normalized_literals_valid site.prefix hphys) start)
      (clearProgram_wellFormed site hg.original _)

theorem program_wellFormed {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hp : ∀ p, WInstr.literal p ∈ erase code → GatePhysical p) (start : Nat) :
    (program code start).WellFormed := by
  induction code generalizing start with
  | nil => simp [program,records,Straight.WellFormed]
  | cons b code ih =>
    rw [program,castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact block_wellFormed b (hg b (by simp)) (fun p hm => hp p (by simp [erase_cons,hm])) start
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase_cons,hm])) _

theorem row_wellFormed (start : Nat) : (program row start).WellFormed := by
  apply program_wellFormed row row_geometry
  intro p hp
  rw [erase_row] at hp
  exact clearReferenceRow_physical p hp

open AndGadget WEXCredit in
 theorem block_residue {n} (b : Block n) (start : Nat) : residue (blockProgram b start) = 0 := by
  cases b with
  | plain code => rw [blockProgram]; exact compile_residue _ _ _ _ _
  | masked site => simp [blockProgram,residue_cast,residue_append,compile_residue,
      clearProgram,MeasuredClear.measuredClear_residue]

open AndGadget in
 theorem program_residue {n} (code : Code n) (start : Nat) : residue (program code start) = 0 := by
  induction code generalizing start with
  | nil => simp [program,records]
  | cons b code ih => simp [program,residue_cast,residue_append,block_residue,ih]

theorem old_compile_support {n} (code : WCode n) (h : OldWithin code) (start : Nat) :
    ChallengeMigration.straightWires (compile bits windowPaths windowRoot (normalizeW code) start) ⊆ sourceSupport := by
  have hn := oldWithin_normalize code h
  exact compile_support _ _ _ _ sourceSupport (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hn.1 hn.2 start


theorem block_support {n} (b : Block n) (hg : BlockGeometry b) (hw : OldWithin b.code) (start : Nat) :
    ChallengeMigration.straightWires (blockProgram b start) ⊆ logicalSupport := by
  cases b with
  | plain code => rw [blockProgram]; exact (old_compile_support code hw start).trans (List.subset_append_left _ _)
  | masked site =>
    have hp : OldWithin site.prefix := oldWithin_sub site.prefix site.code (List.subset_append_left _ _) hw
    rw [blockProgram,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨(old_compile_support site.prefix hp start).trans (List.subset_append_left _ _),
      clearProgram_support site hg.original _⟩

theorem program_support {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b)
    (hw : OldWithin (erase code)) (start : Nat) :
    ChallengeMigration.straightWires (program code start) ⊆ logicalSupport := by
  induction code generalizing start with
  | nil => simp [program,records,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hb : OldWithin b.code := oldWithin_sub b.code (erase (b::code)) (by rw [erase_cons]; exact List.subset_append_left _ _) hw
    have ht : OldWithin (erase code) := oldWithin_sub (erase code) (erase (b::code)) (by rw [erase_cons]; exact List.subset_append_right _ _) hw
    rw [program,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨block_support b (hg b (by simp)) hb start,
      ih (fun d hd => hg d (by simp [hd])) ht _⟩

theorem row_support (start : Nat) : ChallengeMigration.straightWires (program row start) ⊆ logicalSupport := by
  apply program_support row row_geometry
  rw [erase_row]
  exact row_oldWithin

end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

def rowSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode (readConstant coeffs Q) row

theorem rowSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 13 coeffs) :
    CoherentlyImplementsOn (rowSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := row_coherent coeffs Q hQ hn 0 Fin.elim0
  have he : rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold rowState rowPointState
    rw [show tableAddressValue bits s = tableAddressValue (WEX.widthBits 13) s from rfl,
      WEX.width_table 13 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  simpa only [program_run,rowSource,LiveReady] using aligned




end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

def rowSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode (readConstant coeffs Q) row

theorem rowSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (rowSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := row_coherent coeffs Q hQ hn 0 Fin.elim0
  have he : rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold rowState rowPointState
    rw [show tableAddressValue bits s = tableAddressValue (WEX.widthBits 14) s from rfl,
      WEX.width_table 14 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  simpa only [program_run,rowSource,LiveReady] using aligned




end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps MeasuredClear.measuredClear ccx Nat.add Nat.mul

def addFixed (start : Nat) : Straight 32768 start (start+1633554) :=
  castFinish (congrArg (fun m => start+m) row_records) (program row start)

attribute [local irreducible] addFixed

theorem addFixed_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed start).instantiate read history).run = (sourceCode read row).run := by
  rw [addFixed,castFinish_instantiate,program_run]

theorem addFixed_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed start).instantiate read history).tCount = 7*ccx row := by
  rw [addFixed,castFinish_instantiate,program_tCount read row row_geometry]

theorem addFixed_wellFormed (start : Nat) : (addFixed start).WellFormed := by
  rw [addFixed,castFinish_wellFormed]
  exact row_wellFormed start

theorem addFixed_support (start : Nat) : ChallengeMigration.straightWires (addFixed start) ⊆ logicalSupport := by
  rw [addFixed,support_cast]
  exact row_support start

theorem addFixed_residue (start : Nat) : residue (addFixed start) = 0 := by
  rw [addFixed,residue_cast]
  exact program_residue row start

theorem addFixed_credit (start : Nat) : ProgramCredit (addFixed start) (ccx row) := by
  have hz := addFixed_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed_tCount (fun _ => false) start (fun _ => false)
  omega

def bodyProgram (start : Nat) : Straight 32768 start (start+1635598) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nProgram start)).append (addFixed (start+1022))).append
      (nProgram (start+1022+1633554))).append (suffixProgram (start+1022+1633554+1022)))

attribute [local irreducible] bodyProgram








theorem row_ccx_relation : ccx row + 6 * 8001 =
    literalToffolis (normalizeW (clearReferenceRow probeRows)) + 15 * 8191 := by
  have hr := ccx_relation row
  rw [row_masks,erase_row] at hr
  have ht := WEX.clearReferenceRow_traversals
  rw [traversals_normalize] at ht
  rw [ht] at hr
  exact hr



end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps MeasuredClear.measuredClear ccx Nat.add Nat.mul

def addFixed (start : Nat) : Straight 32768 start (start+1707666) :=
  castFinish (congrArg (fun m => start+m) row_records) (program row start)

attribute [local irreducible] addFixed

theorem addFixed_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed start).instantiate read history).run = (sourceCode read row).run := by
  rw [addFixed,castFinish_instantiate,program_run]

theorem addFixed_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed start).instantiate read history).tCount = 7*ccx row := by
  rw [addFixed,castFinish_instantiate,program_tCount read row row_geometry]

theorem addFixed_wellFormed (start : Nat) : (addFixed start).WellFormed := by
  rw [addFixed,castFinish_wellFormed]
  exact row_wellFormed start

theorem addFixed_support (start : Nat) : ChallengeMigration.straightWires (addFixed start) ⊆ logicalSupport := by
  rw [addFixed,support_cast]
  exact row_support start

theorem addFixed_residue (start : Nat) : residue (addFixed start) = 0 := by
  rw [addFixed,residue_cast]
  exact program_residue row start

theorem addFixed_credit (start : Nat) : ProgramCredit (addFixed start) (ccx row) := by
  have hz := addFixed_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed_tCount (fun _ => false) start (fun _ => false)
  omega

def bodyProgram (start : Nat) : Straight 32768 start (start+1709710) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nProgram start)).append (addFixed (start+1022))).append
      (nProgram (start+1022+1707666))).append (suffixProgram (start+1022+1707666+1022)))

attribute [local irreducible] bodyProgram








theorem row_ccx_relation : ccx row + 6 * 16129 =
    literalToffolis (normalizeW (clearReferenceRow probeRows)) + 15 * 16383 := by
  have hr := ccx_relation row
  rw [row_masks,erase_row] at hr
  have ht := WEX.clearReferenceRow_traversals
  rw [traversals_normalize] at ht
  rw [ht] at hr
  exact hr



end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram addFixed bodyProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.codeSlots WEX.literalSlotSum WEX.portTotal lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

@[simp] theorem codeSlots_append {n} (a b : WCode n) :
    codeSlots bits (a++b) = codeSlots bits a + codeSlots bits b := by
  induction a with
  | nil => simp [codeSlots]
  | cons i code ih => cases i <;> simp [codeSlots,ih,Nat.add_assoc]

theorem block_slots_upper {n} (b : Block n) (hg : BlockGeometry b) (start : Nat) :
    (blockProgram b start).gateSlots ≤ codeSlots bits (normalizeW b.code) + blockMasks b * 33595442 := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW code)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram,compile_slots bits windowPaths windowRoot (normalizeW code) hl]
    simp [Block.code,blockMasks]
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW site.prefix)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    have hc := clearProgram_slots site hg.original (start + codeRecords bits windowPaths windowRoot (normalizeW site.prefix))
    rw [blockProgram,castFinish_gateSlots,Straight.gateSlots_append,
      compile_slots bits windowPaths windowRoot (normalizeW site.prefix) hl]
    rw [Block.code,MaskedSite.code,normalize_append,codeSlots_append]
    simp only [blockMasks,Nat.one_mul]
    omega

theorem program_slots_upper {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b) (start : Nat) :
    (program code start).gateSlots ≤ codeSlots bits (normalizeW (erase code)) + masks code * 33595442 := by
  induction code generalizing start with
  | nil => simp [program,records,erase,normalizeW,codeSlots,masks,Straight.gateSlots]
  | cons b code ih =>
    have hb := block_slots_upper b (hg b (by simp)) start
    have ht := ih (fun d hd => hg d (by simp [hd])) (start + blockRecords b)
    rw [program,castFinish_gateSlots,Straight.gateSlots_append]
    simp only [erase_cons,normalize_append,codeSlots_append,masks,Nat.add_mul]
    omega

theorem row_slots_upper (start : Nat) : (program row start).gateSlots ≤ 1000000000 := by
  have h := program_slots_upper row row_geometry start
  rw [row_masks,erase_row] at h
  have hc := WEX.codeSlots_bound bits (normalizeW (clearReferenceRow probeRows))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have ht := WEX.clearReferenceRow_traversals
  rw [traversals_normalize] at ht
  rw [ht] at hc
  have hlen : bits.length = 13 := by simp [bits,WEX.widthBits]
  rw [hlen] at hc
  norm_num at hc
  omega

end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram addFixed bodyProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.codeSlots WEX.literalSlotSum WEX.portTotal lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

@[simp] theorem codeSlots_append {n} (a b : WCode n) :
    codeSlots bits (a++b) = codeSlots bits a + codeSlots bits b := by
  induction a with
  | nil => simp [codeSlots]
  | cons i code ih => cases i <;> simp [codeSlots,ih,Nat.add_assoc]

theorem block_slots_upper {n} (b : Block n) (hg : BlockGeometry b) (start : Nat) :
    (blockProgram b start).gateSlots ≤ codeSlots bits (normalizeW b.code) + blockMasks b * 33818866 := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW code)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram,compile_slots bits windowPaths windowRoot (normalizeW code) hl]
    simp [Block.code,blockMasks]
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW site.prefix)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    have hc := clearProgram_slots site hg.original (start + codeRecords bits windowPaths windowRoot (normalizeW site.prefix))
    rw [blockProgram,castFinish_gateSlots,Straight.gateSlots_append,
      compile_slots bits windowPaths windowRoot (normalizeW site.prefix) hl]
    rw [Block.code,MaskedSite.code,normalize_append,codeSlots_append]
    simp only [blockMasks,Nat.one_mul]
    omega

theorem program_slots_upper {n} (code : Code n) (hg : ∀ b ∈ code, BlockGeometry b) (start : Nat) :
    (program code start).gateSlots ≤ codeSlots bits (normalizeW (erase code)) + masks code * 33818866 := by
  induction code generalizing start with
  | nil => simp [program,records,erase,normalizeW,codeSlots,masks,Straight.gateSlots]
  | cons b code ih =>
    have hb := block_slots_upper b (hg b (by simp)) start
    have ht := ih (fun d hd => hg d (by simp [hd])) (start + blockRecords b)
    rw [program,castFinish_gateSlots,Straight.gateSlots_append]
    simp only [erase_cons,normalize_append,codeSlots_append,masks,Nat.add_mul]
    omega

theorem row_slots_upper (start : Nat) : (program row start).gateSlots ≤ 1000000000 := by
  have h := program_slots_upper row row_geometry start
  rw [row_masks,erase_row] at h
  have hc := WEX.codeSlots_bound bits (normalizeW (clearReferenceRow probeRows))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have ht := WEX.clearReferenceRow_traversals
  rw [traversals_normalize] at ht
  rw [ht] at hc
  have hlen : bits.length = 14 := by simp [bits,WEX.widthBits]
  rw [hlen] at hc
  norm_num at hc
  omega

end
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram addFixed bodyProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx Nat.add Nat.mul

def compactProgram (start : Nat) : Straight 32768 start (start+1635598) :=
  relabelStraight WEX.compactPerm (bodyProgram start)



end
end ShorECDLP.Entrant.WEXUnlookupWidth13

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] program blockProgram clearProgram addFixed bodyProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx Nat.add Nat.mul

def compactProgram (start : Nat) : Straight 32768 start (start+1709710) :=
  relabelStraight WEX.compactPerm (bodyProgram start)



end
end ShorECDLP.Entrant.WEXUnlookupWidth14





end


section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge WindowMassSharpProof
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000

theorem sin_pi_mul_ge_309 (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1/16) :
    (309/100 : ℝ)*u ≤ Real.sin (Real.pi*u) := by
  have hpL : (314 : ℝ)/100 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hpU : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hpu0 : 0 ≤ Real.pi*u := mul_nonneg Real.pi_pos.le hu0
  have hpu : Real.pi*u ≤ 4*u := mul_le_mul_of_nonneg_right hpU hu0
  have hu2 : u^2 ≤ (1/16 : ℝ)^2 := pow_le_pow_left₀ hu0 hu 2
  have hu3 : u^3 ≤ u/256 := by
    have h := mul_le_mul_of_nonneg_left hu2 hu0
    nlinarith
  have hcube : (Real.pi*u)^3 ≤ u/4 := by
    calc
      _ ≤ (4*u)^3 := pow_le_pow_left₀ hpu0 hpu 3
      _ = 64*u^3 := by ring
      _ ≤ 64*(u/256) := mul_le_mul_of_nonneg_left hu3 (by norm_num)
      _ = u/4 := by ring
  have hs := sin_ge_cubic (Real.pi*u) hpu0
  have hp := mul_le_mul_of_nonneg_right hpL hu0
  nlinarith

theorem point_bound_of_abs_sin_309 (N : Nat) (hN : 0<N) (x d : ℝ) (hd : 0<d)
    (hs : (309/100 : ℝ)*d/(N : ℝ) ≤ |Real.sin (x/2)|) :
    Complex.normSq ((N : ℂ)⁻¹ * ∑ y ∈ Finset.range N,
      Complex.exp (Complex.I*(x : ℂ))^y) ≤ 1/((309/100 : ℝ)^2*d^2) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hsp : 0 < |Real.sin (x/2)| := lt_of_lt_of_le (by positivity) hs
  have hden : (309/100 : ℝ)*d ≤ (N : ℝ)*|Real.sin (x/2)| := by
    have h := (div_le_iff₀ hNR).mp hs
    simpa only [mul_comm] using h
  calc
    _ ≤ (1/((N : ℝ)*|Real.sin (x/2)|))^2 := amp_normSq_le N x (abs_pos.mp hsp)
    _ ≤ (1/((309/100 : ℝ)*d))^2 := pow_le_pow_left₀ (by positivity)
      (one_div_le_one_div_of_le (by positivity) hden) 2
    _ = 1/((309/100 : ℝ)^2*d^2) := by field_simp

theorem ampSq_phiR_local_309 (N : Nat) (hN : 0<N) (β : ℝ) (a : Nat)
    (hd : 0<phiR N ((N : ℝ)*β) a)
    (hsmall : phiR N ((N : ℝ)*β) a/(N : ℝ)≤1/16) :
    ampSq N β a ≤ 1/((309/100 : ℝ)^2*(phiR N ((N : ℝ)*β) a)^2) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  apply point_bound_of_abs_sin_309 N hN _ _ hd
  rw [show (2*Real.pi*(β-(a : ℝ)/N))/2=Real.pi*(β-(a : ℝ)/N) by ring,
    abs_sin_phiR N hN β a hd hsmall]
  simpa only [mul_div_assoc] using sin_pi_mul_ge_309
    (phiR N ((N : ℝ)*β) a/(N : ℝ)) (div_nonneg hd.le hNR.le) hsmall

theorem ampSq_phiL_local_309 (N : Nat) (hN : 0<N) (β : ℝ) (a : Nat)
    (hd : 0<phiL N ((N : ℝ)*β) a)
    (hsmall : phiL N ((N : ℝ)*β) a/(N : ℝ)≤1/16) :
    ampSq N β a ≤ 1/((309/100 : ℝ)^2*(phiL N ((N : ℝ)*β) a)^2) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  apply point_bound_of_abs_sin_309 N hN _ _ hd
  rw [show (2*Real.pi*(β-(a : ℝ)/N))/2=Real.pi*(β-(a : ℝ)/N) by ring,
    abs_sin_phiL N hN β a hd hsmall]
  simpa only [mul_div_assoc] using sin_pi_mul_ge_309
    (phiL N ((N : ℝ)*β) a/(N : ℝ)) (div_nonneg hd.le hNR.le) hsmall

theorem directed_tail_309 (N : Nat) (β : ℝ) (S : Finset Nat) (d : Nat→ℝ)
    (R : ℝ) (hR : 1<R) (hd : ∀a∈S,R≤d a)
    (hsep : ∀a∈S,∀b∈S,|d a-d b|<1→a=b)
    (hpt : ∀a∈S,ampSq N β a≤1/((309/100 : ℝ)^2*(d a)^2)) :
    ∑a∈S,ampSq N β a≤(1/((309/100 : ℝ)^2))*(1/(R-1)) := by
  have hi := sum_inv_sq_le S d R hR hd hsep
  calc
    _ ≤ ∑a∈S,(1/((309/100 : ℝ)^2))*(1/(d a)^2) := by
      apply Finset.sum_le_sum
      intro a ha
      convert hpt a ha using 1
      field_simp
    _ = (1/((309/100 : ℝ)^2))*(∑a∈S,1/(d a)^2) := by rw [Finset.mul_sum]
    _ ≤ (1/((309/100 : ℝ)^2))*(1/(R-1)) := mul_le_mul_of_nonneg_left hi (by positivity)

end
end ShorECDLP.Entrant.NeighborReadout


namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge WindowMassSharpProof
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000

theorem directed_tail_309_27 (N : Nat) (β : ℝ) (S : Finset Nat) (d : Nat → ℝ)
    (hd : ∀ a ∈ S, 27 ≤ d a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |d a - d b| < 1 → a = b)
    (hpt : ∀ a ∈ S, ampSq N β a ≤ 1 / ((309/100 : ℝ)^2 * (d a)^2)) :
    ∑ a ∈ S, ampSq N β a ≤ (1 : ℝ)/248 := by
  exact (directed_tail_309 N β S d 27 (by norm_num) hd hsep hpt).trans (by norm_num)

theorem circular_mass_27_309 (N : Nat) (hNbig : 65536≤N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β<1) :
    (9918 : ℝ)/10000 ≤ ∑a∈Finset.range N,
      if phiR N ((N : ℝ)*β) a<27 ∨ phiL N ((N : ℝ)*β) a<27
      then ampSq N β a else 0 := by
  classical
  have hN : 0<N := by omega
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hNreal : (65536 : ℝ)≤N := by exact_mod_cast hNbig
  let R := (Finset.range N).filter (fun a=>27≤phiR N ((N : ℝ)*β) a ∧ phiR N ((N : ℝ)*β) a<4096)
  let L := (Finset.range N).filter (fun a=>27≤phiL N ((N : ℝ)*β) a ∧ phiL N ((N : ℝ)*β) a<4096)
  have rBound : ∑a∈R,ampSq N β a≤(1 : ℝ)/248 := by
    apply directed_tail_309_27 N β R (phiR N ((N : ℝ)*β))
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiR_sep N ((N : ℝ)*β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiR_local_309 N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      nlinarith [hd.2]
  have lBound : ∑a∈L,ampSq N β a≤(1 : ℝ)/248 := by
    apply directed_tail_309_27 N β L (phiL N ((N : ℝ)*β))
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiL_sep N ((N : ℝ)*β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiL_local_309 N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      nlinarith [hd.2]
  have fBound : (∑a∈Finset.range N,
      if ¬(phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096)
      then ampSq N β a else 0)≤(1 : ℝ)/10000 := by
    have hc := circular_mass N hN β 4096 hβ0 hβ1 (by norm_num)
    have hs : (∑a∈Finset.range N,
        if phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0) +
      (∑a∈Finset.range N,
        if ¬(phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096)
        then ampSq N β a else 0)=1 := by
      rw [←Finset.sum_add_distrib]
      convert parseval N hN β using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    linarith [far_tail_budget]
  have cover (a : Nat) :
      (if ¬(phiR N ((N : ℝ)*β) a<27 ∨ phiL N ((N : ℝ)*β) a<27)
        then ampSq N β a else 0) ≤
      (if 27≤phiR N ((N : ℝ)*β) a ∧ phiR N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0) +
      (if 27≤phiL N ((N : ℝ)*β) a ∧ phiL N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0) +
      (if ¬(phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096)
        then ampSq N β a else 0) := by
    have ha0 : 0≤ampSq N β a := Complex.normSq_nonneg _
    by_cases hb : ¬(phiR N ((N : ℝ)*β) a<27 ∨ phiL N ((N : ℝ)*β) a<27)
    · rw [if_pos hb]
      have hr : 27≤phiR N ((N : ℝ)*β) a := le_of_not_gt (fun h=>hb (Or.inl h))
      have hl : 27≤phiL N ((N : ℝ)*β) a := le_of_not_gt (fun h=>hb (Or.inr h))
      by_cases hR : 27≤phiR N ((N : ℝ)*β) a ∧ phiR N ((N : ℝ)*β) a<4096
      · rw [if_pos hR]
        split_ifs <;> linarith
      · rw [if_neg hR]
        by_cases hL : 27≤phiL N ((N : ℝ)*β) a ∧ phiL N ((N : ℝ)*β) a<4096
        · rw [if_pos hL]
          split_ifs <;> linarith
        · rw [if_neg hL]
          have hf : ¬(phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096) := by
            rintro (h|h)
            · exact hR ⟨hr,h⟩
            · exact hL ⟨hl,h⟩
          rw [if_pos hf]
          linarith
    · rw [if_neg hb]
      split_ifs <;> linarith
  have badBound : (∑a∈Finset.range N,
      if ¬(phiR N ((N : ℝ)*β) a<27 ∨ phiL N ((N : ℝ)*β) a<27)
      then ampSq N β a else 0)≤(82 : ℝ)/10000 := by
    have h := Finset.sum_le_sum (fun a (_ : a∈Finset.range N)=>cover a)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at h
    have hR : (∑a∈Finset.range N,
        if 27≤phiR N ((N : ℝ)*β) a ∧ phiR N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0)≤(1 : ℝ)/248 := by
      simpa only [R,Finset.sum_filter] using rBound
    have hL : (∑a∈Finset.range N,
        if 27≤phiL N ((N : ℝ)*β) a ∧ phiL N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0)≤(1 : ℝ)/248 := by
      simpa only [L,Finset.sum_filter] using lBound
    have hb : (1 : ℝ)/248 + 1/248 + 1/10000 ≤ 82/10000 := by norm_num
    linarith
  have htotal : (∑a∈Finset.range N,
      if phiR N ((N : ℝ)*β) a<27 ∨ phiL N ((N : ℝ)*β) a<27
      then ampSq N β a else 0) +
    (∑a∈Finset.range N,
      if ¬(phiR N ((N : ℝ)*β) a<27 ∨ phiL N ((N : ℝ)*β) a<27)
      then ampSq N β a else 0)=1 := by
    rw [←Finset.sum_add_distrib]
    convert parseval N hN β using 1
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> ring
  linarith


theorem directed_tail_309_128 (N : Nat) (β : ℝ) (S : Finset Nat) (d : Nat → ℝ)
    (hd : ∀ a ∈ S, 128 ≤ d a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |d a - d b| < 1 → a = b)
    (hpt : ∀ a ∈ S, ampSq N β a ≤ 1 / ((309/100 : ℝ)^2 * (d a)^2)) :
    ∑ a ∈ S, ampSq N β a ≤ (1 : ℝ)/1212 := by
  exact (directed_tail_309 N β S d 128 (by norm_num) hd hsep hpt).trans (by norm_num)

theorem circular_mass_128_309 (N : Nat) (hNbig : 65536≤N) (β : ℝ)
    (hβ0 : 0≤β) (hβ1 : β<1) :
    (9982 : ℝ)/10000 ≤ ∑a∈Finset.range N,
      if phiR N ((N : ℝ)*β) a<128 ∨ phiL N ((N : ℝ)*β) a<128
      then ampSq N β a else 0 := by
  classical
  have hN : 0<N := by omega
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hNreal : (65536 : ℝ)≤N := by exact_mod_cast hNbig
  let R := (Finset.range N).filter (fun a=>128≤phiR N ((N : ℝ)*β) a ∧ phiR N ((N : ℝ)*β) a<4096)
  let L := (Finset.range N).filter (fun a=>128≤phiL N ((N : ℝ)*β) a ∧ phiL N ((N : ℝ)*β) a<4096)
  have rBound : ∑a∈R,ampSq N β a≤(1 : ℝ)/1212 := by
    apply directed_tail_309_128 N β R (phiR N ((N : ℝ)*β))
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiR_sep N ((N : ℝ)*β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiR_local_309 N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      nlinarith [hd.2]
  have lBound : ∑a∈L,ampSq N β a≤(1 : ℝ)/1212 := by
    apply directed_tail_309_128 N β L (phiL N ((N : ℝ)*β))
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiL_sep N ((N : ℝ)*β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiL_local_309 N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      nlinarith [hd.2]
  have fBound : (∑a∈Finset.range N,
      if ¬(phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096)
      then ampSq N β a else 0)≤(1 : ℝ)/10000 := by
    have hc := circular_mass N hN β 4096 hβ0 hβ1 (by norm_num)
    have hs : (∑a∈Finset.range N,
        if phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0) +
      (∑a∈Finset.range N,
        if ¬(phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096)
        then ampSq N β a else 0)=1 := by
      rw [←Finset.sum_add_distrib]
      convert parseval N hN β using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    linarith [far_tail_budget]
  have cover (a : Nat) :
      (if ¬(phiR N ((N : ℝ)*β) a<128 ∨ phiL N ((N : ℝ)*β) a<128)
        then ampSq N β a else 0) ≤
      (if 128≤phiR N ((N : ℝ)*β) a ∧ phiR N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0) +
      (if 128≤phiL N ((N : ℝ)*β) a ∧ phiL N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0) +
      (if ¬(phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096)
        then ampSq N β a else 0) := by
    have ha0 : 0≤ampSq N β a := Complex.normSq_nonneg _
    by_cases hb : ¬(phiR N ((N : ℝ)*β) a<128 ∨ phiL N ((N : ℝ)*β) a<128)
    · rw [if_pos hb]
      have hr : 128≤phiR N ((N : ℝ)*β) a := le_of_not_gt (fun h=>hb (Or.inl h))
      have hl : 128≤phiL N ((N : ℝ)*β) a := le_of_not_gt (fun h=>hb (Or.inr h))
      by_cases hR : 128≤phiR N ((N : ℝ)*β) a ∧ phiR N ((N : ℝ)*β) a<4096
      · rw [if_pos hR]
        split_ifs <;> linarith
      · rw [if_neg hR]
        by_cases hL : 128≤phiL N ((N : ℝ)*β) a ∧ phiL N ((N : ℝ)*β) a<4096
        · rw [if_pos hL]
          split_ifs <;> linarith
        · rw [if_neg hL]
          have hf : ¬(phiR N ((N : ℝ)*β) a<4096 ∨ phiL N ((N : ℝ)*β) a<4096) := by
            rintro (h|h)
            · exact hR ⟨hr,h⟩
            · exact hL ⟨hl,h⟩
          rw [if_pos hf]
          linarith
    · rw [if_neg hb]
      split_ifs <;> linarith
  have badBound : (∑a∈Finset.range N,
      if ¬(phiR N ((N : ℝ)*β) a<128 ∨ phiL N ((N : ℝ)*β) a<128)
      then ampSq N β a else 0)≤(18 : ℝ)/10000 := by
    have h := Finset.sum_le_sum (fun a (_ : a∈Finset.range N)=>cover a)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at h
    have hR : (∑a∈Finset.range N,
        if 128≤phiR N ((N : ℝ)*β) a ∧ phiR N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0)≤(1 : ℝ)/1212 := by
      simpa only [R,Finset.sum_filter] using rBound
    have hL : (∑a∈Finset.range N,
        if 128≤phiL N ((N : ℝ)*β) a ∧ phiL N ((N : ℝ)*β) a<4096
        then ampSq N β a else 0)≤(1 : ℝ)/1212 := by
      simpa only [L,Finset.sum_filter] using lBound
    have hb : (1 : ℝ)/1212 + 1/1212 + 1/10000 ≤ 18/10000 := by norm_num
    linarith
  have htotal : (∑a∈Finset.range N,
      if phiR N ((N : ℝ)*β) a<128 ∨ phiL N ((N : ℝ)*β) a<128
      then ampSq N β a else 0) +
    (∑a∈Finset.range N,
      if ¬(phiR N ((N : ℝ)*β) a<128 ∨ phiL N ((N : ℝ)*β) a<128)
      then ampSq N β a else 0)=1 := by
    rw [←Finset.sum_add_distrib]
    convert parseval N hN β using 1
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> ring
  linarith


end
end ShorECDLP.Entrant.NeighborReadout


namespace ShorECDLP.Entrant.WindowMassSharpProof
open Finset NeighborReadout
noncomputable section
set_option maxHeartbeats 1500000

theorem window_mass_left264_309 (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r)
    (hNbig : 65536 ≤ N) (hrN : 256 * r ≤ N) :
    (9982 : ℝ) / 10000 ≤ ∑ a ∈ range N,
      if (2 * r * a + N) / (2 * N) = n then ampSq N ((n : ℝ) / (r : ℝ)) a else 0 := by
  have hr : 0 < r := by omega
  have hN : 0 < N := by omega
  set β : ℝ := (n : ℝ) / (r : ℝ) with hβ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR0 : (0 : ℝ) ≤ n := by positivity
  have hnR : (n : ℝ) < r := by exact_mod_cast hnr
  set c : ℝ := (N : ℝ) * n / r with hc
  set L : ℝ := (N : ℝ) / (2 * r) with hL
  have hcr : c * r = N * n := by rw [hc]; field_simp
  have hLr : L * (2 * r) = N := by rw [hL]; field_simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnr' : (n : ℝ) + 1 ≤ r := by exact_mod_cast hnr
  have hrN' : 256 * (r : ℝ) ≤ N := by exact_mod_cast hrN
  have hL128 : 128 ≤ L := by nlinarith
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβ1 : β < 1 := by rw [hβ]; exact (div_lt_one hrR).2 hnR
  have hmass := circular_mass_128_309 N hNbig β hβ0 hβ1
  have hcβ : (N : ℝ) * β = c := by rw [hβ,hc]; ring
  rw [hcβ] at hmass
  apply hmass.trans
  apply Finset.sum_le_sum
  intro a ha
  have haN : (a : ℝ) < N := by exact_mod_cast (mem_range.mp ha)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hgood : (phiR N c a < 128 ∨ phiL N c a < 128) →
      (2 * r * a + N) / (2 * N) = n := by
    intro hnear
    by_contra hbad
    have hreg : c + L ≤ (a : ℝ) ∨ (a : ℝ) + L ≤ c := by
      rcases window_cases r N n a hN hbad with h | h
      · left
        have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
        nlinarith
      · right
        have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
        nlinarith
    have hR : L ≤ phiR N c a := by
      unfold phiR
      split_ifs with h
      · rcases hreg with hA | hA <;> linarith
      · linarith
    have hL' : L ≤ phiL N c a := by
      unfold phiL
      split_ifs with h
      · rcases hreg with hA | hA <;> linarith
      · linarith
    rcases hnear with hn | hn <;> linarith
  have hnneg : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
  split_ifs with hn hg
  · exact le_rfl
  · exact (hg (hgood hn)).elim
  · exact hnneg
  · exact le_rfl
end
end ShorECDLP.Entrant.WindowMassSharpProof


namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout WindowMassSharpProof
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000

theorem rightMass_lower_309 (r : Nat) (hr : 0<r) (k : Fin r) :
    (9918 : ℝ)/10000≤rightMass r k := by
  classical
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have h:=circular_mass_27_309 (2^208) (by norm_num) ((k.val : ℝ)/r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt))
  have hfin : (9918 : ℝ)/10000 ≤ ∑b : Fin (2^208),
      if phiR (2^208) ((2^208 : Nat)*((k.val : ℝ)/r)) b.val<27 ∨
        phiL (2^208) ((2^208 : Nat)*((k.val : ℝ)/r)) b.val<27
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ)/r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b=>
      if phiR (2^208) ((2^208 : Nat)*((k.val : ℝ)/r)) b<27 ∨
        phiL (2^208) ((2^208 : Nat)*((k.val : ℝ)/r)) b<27
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ)/r) b) else 0)]
    simpa only [ampSq,paperPhaseAmplitude,eigenvalue] using h
  refine hfin.trans (Finset.sum_le_sum (fun b _=>?_))
  dsimp only [rightMass]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem rightMass_average_309 (r d : Nat) (hr : 0<r) :
    (9918 : ℝ)/10000*((r : ℝ)-1) ≤ ∑k : Fin r,
      if k.val=0 then 0 else rightMass r ⟨d*k.val%r,Nat.mod_lt _ hr⟩ := by
  classical
  have hz : (∑k : Fin r,if k.val=0 then (1 : ℝ) else 0)=1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k=>if k=0 then (1 : ℝ) else 0)]
    simp [hr]
  have hs : (∑k : Fin r,if k.val=0 then (0 : ℝ) else 9918/10000)=
      (9918 : ℝ)/10000*((r : ℝ)-1) := by
    calc
      _ = ∑k : Fin r,((9918 : ℝ)/10000-(9918/10000)*(if k.val=0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib,←Finset.mul_sum,hz]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
        ring
  rw [←hs]
  apply Finset.sum_le_sum
  intro k _
  split_ifs
  · exact le_rfl
  · exact rightMass_lower_309 _ hr _

end
end ShorECDLP.Entrant.NeighborReadout


namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 300

theorem precision264_309 : 256 * order ≤ 2^264 := by norm_num [order]

theorem success_budget264_309 (r : ℝ) (hr : 1000000 ≤ r) :
    (99 : ℝ)/100 ≤ (9982/10000)*(9918/10000)*(1-1/r) := by
  have hr0 : 0 < r := by linarith
  have hinv : 1/r ≤ (1 : ℝ)/1000000 :=
    one_div_le_one_div_of_le (by norm_num) hr
  nlinarith

theorem neighbor_pair_coverage264_309 (r n d : Nat) (hr : r.Prime)
    (hNbig : 65536 ≤ 2^n) (hprecision : 256*r ≤ 2^n)
    (accept : Fin (2^n) → Fin (2^208) → Prop) [∀ a b, Decidable (accept a b)]
    (haccept : ∀ (k : Fin r), k.val ≠ 0 → ∀ a b,
      ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val →
      rightGood r ⟨d*k.val%r, Nat.mod_lt _ hr.pos⟩ b →
      accept a b) :
    (9982 : ℝ)/10000 * (9918/10000) * (1-1/r) ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208),
      if accept a b then asymmetricPairMass r n 208 d (a,b) else 0 := by
  classical
  let A : Fin r → Fin (2^n) → ℝ := fun k a =>
    Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ)/r) a.val)
  let B : Fin r → Fin (2^208) → ℝ := fun k b =>
    Complex.normSq (paperPhaseAmplitude 208 (((d*k.val%r : Nat) : ℝ)/r) b.val)
  let good : Fin r → Fin (2^n) → Fin (2^208) → Prop := fun k a b =>
    k.val ≠ 0 ∧ ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val ∧
      rightGood r ⟨d*k.val%r, Nat.mod_lt _ hr.pos⟩ b
  let F : Fin r → Fin (2^n) → Fin (2^208) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  have hA : ∀ k a, 0 ≤ A k a := fun _ _ => Complex.normSq_nonneg _
  have hB : ∀ k b, 0 ≤ B k b := fun _ _ => Complex.normSq_nonneg _
  have hF : ∀ k a b, 0 ≤ F k a b := by
    intro k a b
    dsimp only [F]
    split_ifs
    · exact mul_nonneg (hA k a) (hB k b)
    · exact le_rfl
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hrinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  have hjp : ∀ a : Fin (2^n), ∀ b : Fin (2^208),
      asymmetricPairMass r n 208 d (a,b) = (r : ℝ)⁻¹ * ∑ k : Fin r, A k a * B k b := by
    intro a b
    simp only [asymmetricPairMass, one_div, A, B]
  have step1 :
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2^n), ∑ b : Fin (2^208),
          if accept a b then asymmetricPairMass r n 208 d (a,b) else 0 := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    by_cases hp : accept a b
    · rw [if_pos hp, hjp]
      apply mul_le_mul_of_nonneg_left _ hrinv
      apply Finset.sum_le_sum
      intro k _
      dsimp only [F]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hA k a) (hB k b)
    · rw [if_neg hp]
      have hz : ∀ k, F k a b = 0 := by
        intro k
        dsimp only [F]
        rw [if_neg]
        rintro ⟨hk, ha, hb⟩
        exact hp (haccept k hk a b ha hb)
      simp [hz]
  have step2 :
      (r : ℝ)⁻¹ * ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b =
        ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have hleft (k : Fin r) (hk : k.val ≠ 0) :
      (9982 : ℝ)/10000 ≤ ∑ a : Fin (2^n),
        if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val then A k a else 0 := by
    have h := ShorECDLP.Entrant.WindowMassSharpProof.window_mass_left264_309 r (2^n) k.val
      (Nat.pos_of_ne_zero hk) k.isLt hNbig hprecision
    rw [Fin.sum_univ_eq_sum_range (fun a =>
      if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a = k.val then
        Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ)/r) a) else 0)]
    simpa only [ShorECDLP.Quantum.OrderFinding.nearestNumerator, paperPhaseAmplitude, eigenvalue] using h
  have step3 : ∀ k : Fin r,
      (9982 : ℝ)/10000 * (if k.val = 0 then 0 else
        rightMass r ⟨d*k.val%r, Nat.mod_lt _ hr.pos⟩) ≤
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    intro k
    by_cases hk : k.val = 0
    · rw [if_pos hk, mul_zero]
      exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF k a b))
    · rw [if_neg hk]
      have he : (∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b) =
          (∑ a : Fin (2^n), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val then A k a else 0) *
            rightMass r ⟨d*k.val%r, Nat.mod_lt _ hr.pos⟩ := by
        rw [rightMass, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F, good, B]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [he]
      exact mul_le_mul_of_nonneg_right (hleft k hk) (rightMass_nonneg _ _)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  rw [← Finset.mul_sum] at hsum
  have havg := rightMass_average_309 r d hr.pos
  have hprod : (9982 : ℝ)/10000 * ((9918:ℝ)/10000*(r-1)) ≤
      ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b :=
    (mul_le_mul_of_nonneg_left havg (by norm_num)).trans hsum
  have hlower := mul_le_mul_of_nonneg_left hprod hrinv
  have heval : (r : ℝ)⁻¹ * ((9982 : ℝ)/10000 * ((9918:ℝ)/10000*(r-1))) =
      (9982 : ℝ)/10000 * ((9918:ℝ)/10000) * (1-1/r) := by field_simp
  rw [heval, step2] at hlower
  exact hlower.trans step1


def params264 : DecoderParams := ⟨264,208,by decide,by decide,by decide,by decide⟩
def pairRecovered264 (d a b : Nat) : Bool :=
  decide (∃i : Fin 55,(d : ZMod order)∈fixedCandidates params264 a (neighborWord b ((i.val : ℤ)-27)))

theorem pairRecovered264_of_character (d : Nat) (k : Fin order) (hk : k.val≠0)
    (a : Fin (2^264)) (b : Fin (2^208))
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 264 a.val=k.val)
    (hb : rightGood order ⟨d*k.val%order,Nat.mod_lt _ order_prime.pos⟩ b) :
    pairRecovered264 d a.val b.val=true := by
  classical
  obtain ⟨j,hlo,hhi,hj⟩:=hb
  let i : Fin 55:=⟨(j+27).toNat,by omega⟩
  have hi : (i.val : ℤ)-27=j := by dsimp [i];omega
  haveI : Fact (Nat.Prime order):=⟨order_prime⟩
  have hk0 : ((k.val : Nat) : ZMod order)≠0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
  apply decide_eq_true
  refine ⟨i,?_⟩
  rw [hi]
  unfold fixedCandidates
  apply Finset.mem_image.mpr
  refine ⟨d*k.val%order,?_,?_⟩
  · change d*k.val%order∈wrappedNumeratorCandidates order 208 (neighborWord b.val j)
    rw [hj]
    exact reducedPeak_mem_candidates order 208 _
  · change ((d*k.val%order : Nat) : ZMod order)*
      (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 264 a.val : ZMod order)⁻¹=d
    rw [ha]
    simp only [ZMod.natCast_mod,Nat.cast_mul]
    field_simp


theorem pair_success264 (Q : Point) (d : Nat) (_hn : Q≠0) (_hd : Q=d•G) :
    (99 : ℝ)/100 ≤ ∑a : Fin (2^264),∑b : Fin (2^208),
      if pairRecovered264 d a.val b.val then asymmetricPairMass order 264 208 d (a,b) else 0 := by
  have h:=neighbor_pair_coverage264_309 order 264 d order_prime (by norm_num) precision264_309
    (fun a b=>pairRecovered264 d a.val b.val=true)
    (fun k hk a b ha hb=>pairRecovered264_of_character d k hk a b ha hb)
  exact (success_budget264_309 order (by norm_num [order])).trans h

end
end ShorECDLP.Entrant.NeighborReadout



namespace ShorECDLP.Entrant.Schedule31Eighteen264
open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000




inductive Digit where
  | left15 (index : Fin 8)
  | left14 (index : Fin 9)
  | right15 (index : Fin 12)
  | right14 (index : Fin 2)

def Digit.width : Digit → Nat
  | .left15 _ | .right15 _ => 15
  | .left14 _ | .right14 _ => 14

def Digit.exponent : Digit → Nat
  | .left15 j => 231 - 15 * j.val
  | .left14 j => 112 - 14 * j.val
  | .right15 j => 193 - 15 * j.val
  | .right14 j => 14 - 14 * j.val

def firstRow (a : Fin 262144) : Fin 679936 := ⟨a.val, by omega⟩

def row : (w : Digit) → Fin (2^(w.width-1)) → Fin 679936
  | .left15 j, a => ⟨262144 + j.val*16384 + a.val, by
    have h : a.val < 16384 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .left14 j, a => ⟨393216 + j.val*8192 + a.val, by
    have h : a.val < 8192 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .right15 j, a => ⟨466944 + j.val*16384 + a.val, by
    have h : a.val < 16384 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .right14 j, a => ⟨663552 + j.val*8192 + a.val, by
    have h : a.val < 8192 := by simpa only [Digit.width] using a.isLt
    omega⟩

theorem width_cases (w : Digit) : w.width = 14 ∨ w.width = 15 := by
  cases w <;> simp [Digit.width]

def leftDigits : List Digit := List.ofFn (fun j : Fin 8 => .left15 j) ++
  List.ofFn (fun j : Fin 9 => .left14 j)
def rightDigits : List Digit := List.ofFn (fun j : Fin 12 => .right15 j) ++
  List.ofFn (fun j : Fin 2 => .right14 j)

theorem left_widths : leftDigits.map Digit.width =
    List.replicate 8 15 ++ List.replicate 9 14 := by
  simp [leftDigits, List.ofFn_succ, Digit.width, List.replicate]
theorem right_widths : rightDigits.map Digit.width =
    List.replicate 12 15 ++ List.replicate 2 14 := by
  simp [rightDigits, List.ofFn_succ, Digit.width, List.replicate]

def leftOffset : Nat := (leftDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum
def rightOffset : Nat := (rightDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum

def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients (v * 2^246 + leftOffset) rightOffset

def signedCoefficients (w : Digit) (a : Nat) : PointCoeff :=
  match w with
  | .left15 _ | .left14 _ => coefficients (Single.oddScalar w.exponent a) 0
  | .right15 _ | .right14 _ => coefficients 0 (Single.oddScalar w.exponent a)

def coefficientAt (i : Fin 679936) : PointCoeff :=
  if i.val < 262144 then initialCoefficients i.val
  else if i.val < 393216 then
    coefficients (Single.oddScalar (231 - 15 * ((i.val - 262144) / 16384)) ((i.val - 262144) % 16384)) 0
  else if i.val < 466944 then
    coefficients (Single.oddScalar (112 - 14 * ((i.val - 393216) / 8192)) ((i.val - 393216) % 8192)) 0
  else if i.val < 663552 then
    coefficients 0 (Single.oddScalar (193 - 15 * ((i.val - 466944) / 16384)) ((i.val - 466944) % 16384))
  else coefficients 0 (Single.oddScalar (14 - 14 * ((i.val - 663552) / 8192)) ((i.val - 663552) % 8192))

theorem coefficientAt_first (a : Fin 262144) :
    coefficientAt (firstRow a) = initialCoefficients a.val := by
  simp [coefficientAt, firstRow, a.isLt]

theorem coefficientAt_row (w : Digit) (a : Fin (2^(w.width-1))) :
    coefficientAt (row w a) = signedCoefficients w a.val := by
  cases w with
  | left15 j =>
    have ha : a.val < 16384 := by
      simpa only [Digit.width] using a.isLt
    have he : (row (.left15 j) a).val < 393216 := by simp only [row]; omega
    have hbase : ¬ (row (.left15 j) a).val < 262144 := by simp only [row]; omega
    have hj : ((row (.left15 j) a).val - 262144) / 16384 = j.val := by simp only [row]; omega
    have hh : ((row (.left15 j) a).val - 262144) % 16384 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, he, hj, hh, signedCoefficients, Digit.exponent]
  | left14 j =>
    have ha : a.val < 8192 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.left14 j) a).val < 262144 := by simp only [row]; omega
    have he : (row (.left14 j) a).val < 466944 := by simp only [row]; omega
    have hbase : ¬ (row (.left14 j) a).val < 393216 := by simp only [row]; omega
    have hj : ((row (.left14 j) a).val - 393216) / 8192 = j.val := by simp only [row]; omega
    have hh : ((row (.left14 j) a).val - 393216) % 8192 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, he, hj, hh, signedCoefficients, Digit.exponent]
  | right15 j =>
    have ha : a.val < 16384 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.right15 j) a).val < 262144 := by simp only [row]; omega
    have hn1 : ¬ (row (.right15 j) a).val < 393216 := by simp only [row]; omega
    have he : (row (.right15 j) a).val < 663552 := by simp only [row]; omega
    have hbase : ¬ (row (.right15 j) a).val < 466944 := by simp only [row]; omega
    have hj : ((row (.right15 j) a).val - 466944) / 16384 = j.val := by simp only [row]; omega
    have hh : ((row (.right15 j) a).val - 466944) % 16384 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, hn1, he, hj, hh, signedCoefficients, Digit.exponent]
  | right14 j =>
    have ha : a.val < 8192 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.right14 j) a).val < 262144 := by simp only [row]; omega
    have hn1 : ¬ (row (.right14 j) a).val < 393216 := by simp only [row]; omega
    have hn2 : ¬ (row (.right14 j) a).val < 466944 := by simp only [row]; omega
    have hbase : ¬ (row (.right14 j) a).val < 663552 := by simp only [row]; omega
    have hj : ((row (.right14 j) a).val - 663552) / 8192 = j.val := by simp only [row]; omega
    have hh : ((row (.right14 j) a).val - 663552) % 8192 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, hn1, hn2, hj, hh, signedCoefficients, Digit.exponent]

end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def initialPoint (Q : Point) (v : Nat) : Point :=
  (v * 2^246 + leftOffset) • G + rightOffset • Q

theorem initialCoefficients_point (Q : Point) (hQ : order • Q = 0) (v : Nat) :
    constantPoint Q (initialCoefficients v) = initialPoint Q v := by
  unfold initialCoefficients initialPoint
  exact coefficients_point _ _ Q hQ

def firstWindow : Single.Window 679936 := ScheduleFirst18.windowGeneric firstRow

theorem firstWindow_law : WindowLaw coefficientAt firstWindow
    (ScheduleFirst18.update initialPoint) ScheduleFirst18.Input := by
  apply ScheduleFirst18.window_law_generic
  intro Q hQ a
  rw [coefficientAt_first]
  exact initialCoefficients_point Q hQ a.val

end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def Digit.base (Q : Point) : Digit → Point
  | .left15 _ | .left14 _ => G
  | .right15 _ | .right14 _ => Q

noncomputable def positivePoint (Q : Point) (w : Digit) (a : Nat) : Point :=
  Single.oddScalar w.exponent a • w.base Q

theorem signedCoefficients_point (Q : Point) (hQ : order • Q = 0)
    (w : Digit) (a : Nat) :
    constantPoint Q (signedCoefficients w a) = positivePoint Q w a := by
  cases w <;> simp [signedCoefficients, coefficients_point _ _ Q hQ,
    positivePoint, Digit.base]

theorem positivePoint_ne_zero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (address : Nat) (ha : address < 2^(w.width-1)) :
    positivePoint Q w address ≠ 0 := by
  let P := w.base Q
  have hp : P ≠ 0 := by
    cases w with
    | left15 _ | left14 _ => exact G_ne_zero
    | right15 _ | right14 _ => exact hn
  have hr : order • P = 0 := by
    cases w with
    | left15 _ | left14 _ => exact generator_nsmul_eq_zero
    | right15 _ | right14 _ => exact hQ
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf P = order := addOrderOf_eq_prime hr hp
  have hw : 2^(w.width-1) ≤ 32768 := by cases w <;> norm_num [Digit.width]
  have hl : 65535 < order := by norm_num [order]
  have hs : 0 < 2*address+1 ∧ 2*address+1 < order := by omega
  have hh : 0 < Single.halfOrder ∧ Single.halfOrder < order := by
    dsimp [Single.halfOrder]; omega
  have hodd : ¬ order ∣ 2*address+1 :=
    fun h => (Nat.le_of_dvd hs.1 h).not_gt hs.2
  have hhalf : ¬ order ∣ Single.halfOrder := fun h => (Nat.le_of_dvd hh.1 h).not_gt hh.2
  have htwo : ¬ order ∣ 2 := fun h => (Nat.le_of_dvd (by decide : 0 < 2) h).not_gt (by omega)
  intro hz
  have he : ((2*address+1)*2^w.exponent*Single.halfOrder) • P = 0 := by
    simpa only [positivePoint, Single.oddScalar] using hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  rw [ho] at hd
  rcases order_prime.dvd_mul.mp hd with hd | hd
  · rcases order_prime.dvd_mul.mp hd with hd | hd
    · exact hodd hd
    · exact htwo (order_prime.dvd_of_dvd_pow hd)
  · exact hhalf hd


noncomputable def increment (P : Point) (width exponent v : Nat) : Point :=
  ((2 * (v : Int) - (2 : Int)^width + 1) : Int) •
    ((Single.halfOrder * 2^exponent) • P)

theorem increment_offset (P : Point) (hr : order • P = 0)
    (width exponent v : Nat) (hw : width = 14 ∨ width = 15) :
    increment P width exponent v + Single.offsetScalar width exponent • P =
      (v * 2^exponent) • P := by
  have hh : Single.halfOrder ≤ 2^(width-1) + order := by
    have hl : Single.halfOrder ≤ order := by norm_num [Single.halfOrder, order]
    exact hl.trans (Nat.le_add_left _ _)
  have he : (2^(width-1) + order - Single.halfOrder) • P + Single.halfOrder • P =
      2^(width-1) • P := by
    rw [← add_nsmul, Nat.sub_add_cancel hh, add_nsmul, hr, add_zero]
  have hoff : Single.offsetScalar width exponent • P =
      2^(width-1) • (2^exponent • P) - (Single.halfOrder * 2^exponent) • P := by
    unfold Single.offsetScalar
    rw [mul_smul, smul_comm (2^(width-1) + order - Single.halfOrder) (2^exponent),
      eq_sub_iff_add_eq.mpr he, nsmul_sub]
    simp only [mul_smul]
    rw [smul_comm (2^exponent) (2^(width-1)), smul_comm (2^exponent) Single.halfOrder]
  let H := (Single.halfOrder * 2^exponent) • P
  have hd : H + H = 2^exponent • P := by
    change (Single.halfOrder * 2^exponent) • P + (Single.halfOrder * 2^exponent) • P = _
    rw [mul_smul, smul_comm Single.halfOrder (2^exponent), ← nsmul_add]
    exact congrArg (fun R : Point => 2^exponent • R)
      (signedWindowHalfPoint_double P order (by decide +kernel) hr)
  have hp : (2 : Int)^width = 2 * (2^(width-1) : Nat) := by
    rcases hw with rfl | rfl <;> norm_num
  have hcalc : ((2*(v:Int)-(2:Int)^width+1) • H) +
      (2^(width-1) • (H+H) - H) = v • (H+H) := by
    rw [hp]
    module
  change ((2*(v:Int)-(2:Int)^width+1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2^exponent) P).symm


open Quantum ShorECDLP.Paper2607_13816

def logicalValue14 (low : Nat) (sign : Bool) : Nat := low + 8192 * sign.toNat
def logicalValue15 (low : Nat) (sign : Bool) : Nat := low + 16384 * sign.toNat
theorem padded_address14 (low : Nat) (sign : Bool) (hlow : low < 8192) :
    signedTableAddress 32768 (Single.paddedValue low sign) % 8192 =
      signedTableAddress 8192 (logicalValue14 low sign) := by
  cases sign with
  | false =>
    have hbig : low < 32768 := by omega
    have hsub : 32767 - low = 24576 + (8191 - low) := by omega
    have hrem : 8191 - low < 8192 := by omega
    simp only [Single.paddedValue, logicalValue14, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      signedTableAddress, if_pos hbig, if_pos hlow]
    rw [hsub, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hrem]
  | true =>
    have hbig : ¬ low + 32768 < 32768 := by omega
    have hsmall : ¬ low + 8192 < 8192 := by omega
    simp only [Single.paddedValue, logicalValue14, Bool.toNat_true, Nat.mul_one,
      signedTableAddress, if_neg hbig, if_neg hsmall]
    have h1 : low + 32768 - 32768 = low := by omega
    have h2 : low + 8192 - 8192 = low := by omega
    rw [h1, h2, Nat.mod_eq_of_lt hlow]



theorem padded_address15 (low : Nat) (sign : Bool) (hlow : low < 16384) :
    signedTableAddress 32768 (Single.paddedValue low sign) % 16384 =
      signedTableAddress 16384 (logicalValue15 low sign) := by
  cases sign with
  | false =>
    have hbig : low < 32768 := by omega
    have hsub : 32767 - low = 16384 + (16383 - low) := by omega
    have hrem : 16383 - low < 16384 := by omega
    simp only [Single.paddedValue, logicalValue15, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      signedTableAddress, if_pos hbig, if_pos hlow]
    rw [hsub, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hrem]
  | true =>
    have hbig : ¬ low + 32768 < 32768 := by omega
    have hsmall : ¬ low + 16384 < 16384 := by omega
    simp only [Single.paddedValue, logicalValue15, Bool.toNat_true, Nat.mul_one,
      signedTableAddress, if_neg hbig, if_neg hsmall]
    have h1 : low + 32768 - 32768 = low := by omega
    have h2 : low + 16384 - 16384 = low := by omega
    rw [h1, h2, Nat.mod_eq_of_lt hlow]


theorem address_append (xs ys : List Wire) (s : BasisState) :
    tableAddressValue (xs ++ ys) s =
      tableAddressValue xs s + 2^xs.length * tableAddressValue ys s := by
  induction xs with
  | nil => simp [tableAddressValue]
  | cons x xs ih =>
    simp only [List.cons_append, tableAddressValue, List.length_cons, ih, pow_succ]
    ring

def bank (width : Nat) : List Wire := List.range' 855 (width-1) ++ [870]

def digit (width : Nat) (s : BasisState) : Nat := tableAddressValue (bank width) s

theorem bank_length (width : Nat) (hw : width = 14 ∨ width = 15) :
    (bank width).length = width := by
  rcases hw with rfl | rfl <;> simp [bank]

theorem digit14_low (s : BasisState) :
    digit 14 s = logicalValue14 (tableAddressValue (List.range' 855 13) s) (s 870) := by
  change tableAddressValue (List.range' 855 13 ++ [870]) s =
    tableAddressValue (List.range' 855 13) s + 8192 * (s 870).toNat
  rw [address_append]
  simp [tableAddressValue]

theorem digit15_low (s : BasisState) :
    digit 15 s = logicalValue15 (tableAddressValue (List.range' 855 14) s) (s 870) := by
  change tableAddressValue (List.range' 855 14 ++ [870]) s =
    tableAddressValue (List.range' 855 14) s + 16384 * (s 870).toNat
  rw [address_append]
  simp [tableAddressValue]

theorem physical_padding14 (s : BasisState) (h868 : s 868 = false) (h869 : s 869 = false) :
    windowRawDigit 0 s = Single.paddedValue (tableAddressValue (List.range' 855 13) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, Single.paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat, h868, h869]

theorem physical_padding15 (s : BasisState) (h869 : s 869 = false) :
    windowRawDigit 0 s = Single.paddedValue (tableAddressValue (List.range' 855 14) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, Single.paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat, h869]

theorem bank_nodup (width : Nat) (hw : width = 14 ∨ width = 15) : (bank width).Nodup := by
  rcases hw with rfl | rfl <;> decide +kernel

theorem bank_subset (width : Nat) (hw : width = 14 ∨ width = 15) :
    ∀ v ∈ bank width, v ∈ streamAddress := by
  rcases hw with rfl | rfl <;> decide +kernel

theorem bank_not_point (width : Nat) (hw : width = 14 ∨ width = 15) :
    ∀ v ∈ bank width, v ∉ pointLogicalWires := by
  intro v hv
  exact (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v
    (bank_subset width hw v hv)

theorem digit_low_sign (width : Nat) (hw : width = 14 ∨ width = 15) (s : BasisState) :
    digit width s < 2^(width-1) ↔ s 870 = false := by
  rcases hw with rfl | rfl
  · rw [digit14_low]
    have hb := tableAddressValue_lt (List.range' 855 13) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue14]
  · rw [digit15_low]
    have hb := tableAddressValue_lt (List.range' 855 14) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue15]

theorem selected_address_alias (width : Nat) (hw : width = 14 ∨ width = 15) (s : BasisState)
    (h869 : s 869 = false) (h868 : width = 14 → s 868 = false) :
    signedTableAddress 32768 (windowRawDigit 0 s) % 2^(width-1) =
      signedTableAddress (2^(width-1)) (digit width s) := by
  rcases hw with rfl | rfl
  · rw [physical_padding14 s (h868 rfl) h869, digit14_low]
    exact padded_address14 _ _ (by simpa using tableAddressValue_lt (List.range' 855 13) s)
  · rw [physical_padding15 s h869, digit15_low]
    exact padded_address15 _ _ (by simpa using tableAddressValue_lt (List.range' 855 14) s)

theorem selected_increment (Q : Point) (w : Digit) (s : BasisState)
    (h869 : s 869 = false) (h868 : w.width = 14 → s 868 = false) :
    (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))) =
      increment (w.base Q) w.width w.exponent (digit w.width s) := by
  have hpow : (2 : Int)^w.width = 2 * (2^(w.width-1) : Nat) := by
    rcases width_cases w with hw | hw <;> rw [hw] <;> norm_num
  have hs : (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))) =
      signedTableOdd (2^(w.width-1)) (digit w.width s) •
        ((Single.halfOrder * 2^w.exponent) • w.base Q) := by
    simp only [positivePoint, selected_address_alias w.width (width_cases w) s h869 h868,
      Single.oddScalar, mul_smul]
    rw [smul_comm Single.halfOrder (2^w.exponent)]
    cases h : s 870
    · rw [if_neg (by decide), signedTableOdd, if_pos ((digit_low_sign w.width (width_cases w) s).mpr h)]
      simp only [neg_zsmul, natCast_zsmul]
    · rw [if_pos rfl, signedTableOdd, if_neg (by
        intro hh
        have he := (digit_low_sign w.width (width_cases w) s).mp hh
        simp [h] at he)]
      simp only [natCast_zsmul]
  rw [hs, signedTableOdd_value]
  unfold increment
  rw [hpow]

def paddedRow (w : Digit) (a : Fin 32768) : Fin 679936 :=
  row w ⟨a.val % 2^(w.width-1), Nat.mod_lt _ (pow_pos (by decide) _)⟩

noncomputable def windowCoefficients (w : Digit) : Fin 32768 → PointCoeff :=
  fun a => coefficientAt (paddedRow w a)

theorem window_table_point (Q : Point) (hQ : order • Q = 0) (w : Digit) (a : Nat) :
    constantPoint Q (windowCoefficients w ⟨a % 32768, Nat.mod_lt _ (by decide)⟩) =
      positivePoint Q w (a % 2^(w.width-1)) := by
  unfold windowCoefficients paddedRow
  rw [coefficientAt_row, signedCoefficients_point Q hQ]
  have ha : a % 32768 % 2^(w.width-1) = a % 2^(w.width-1) := by
    cases w <;> norm_num [Digit.width]
  simp only [ha]






end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
variable [b : Single.WindowBody]

def WindowValid (w : Digit) (s : BasisState) : Prop :=
  Single.BodyValid b s ∧ s 869 = false ∧ (w.width = 14 → s 868 = false)

def signedWindow (w : Digit) : Single.Window 679936 :=
  ⟨(bank w.width).reverse, b.records,
    fun start => reindexStraight (paddedRow w) (b.program start)⟩


noncomputable def windowUpdate (Q : Point) (w : Digit) : BasisState → BasisState :=
  b.update (windowCoefficients w) Q

theorem windowUpdate_correct (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (s : BasisState) (hs : WindowValid w s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    windowUpdate Q w s = pointWrite (P + increment (w.base Q) w.width w.exponent (digit w.width s)) s := by
  have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
    intro a
    have he := window_table_point Q hQ w a.val
    simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
    rw [he]
    exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
  unfold windowUpdate
  rw [b.correct _ Q hQ htable s hs.1.1 P hP, b.active s hs.1.1, if_pos rfl]
  have ha := signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)
  have he := window_table_point Q hQ w (signedTableAddress 32768 (windowRawDigit 0 s))
  simp only [Nat.mod_eq_of_lt ha] at he
  rw [he, selected_increment Q w s hs.2.1 hs.2.2]

theorem signedWindow_coherent (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((signedWindow w).program start |>.instantiate
      (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w) := by
  have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
    intro a
    have he := window_table_point Q hQ w a.val
    simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
    rw [he]
    exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
  have h := b.coherent (windowCoefficients w) Q hQ htable start history
  unfold signedWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
  obtain ⟨cs, hc, hm⟩ := h
  exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩




theorem signedWindow_wires (w : Digit) : (signedWindow w).wires = (bank w.width).reverse := rfl


theorem signedWindow_wellFormed (w : Digit) (start : Nat) :
    ((signedWindow w).program start).WellFormed := by
  unfold signedWindow
  exact (reindexStraight_wellFormed (paddedRow w) (b.program start)).mpr (b.wellFormed start)

theorem signedWindow_slots (w : Digit) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ b.slotBound := by
  unfold signedWindow
  rw [reindexStraight_gateSlots]
  exact b.slots start


end

end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def SignedWeights (Q P : Point) : List Digit → Prop
  | [] => True
  | w :: ws => w.base Q = P ∧ w.exponent = (ws.map Digit.width).sum ∧ SignedWeights Q P ws

theorem left_signed_weights (Q : Point) : SignedWeights Q G leftDigits := by
  norm_num [leftDigits, List.ofFn_succ, SignedWeights, Digit.width, Digit.exponent, Digit.base]

theorem right_signed_weights (Q : Point) : SignedWeights Q Q rightDigits := by
  norm_num [rightDigits, List.ofFn_succ, SignedWeights, Digit.width, Digit.exponent, Digit.base]

theorem modelWeights {n : Nat} {read : ConstantBit n → Bool}
    (Q P : Point) (hr : order • P = 0) (f : Digit → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = w.width)
    (hpoint : ∀ w v, (f w).point v = increment (w.base Q) w.width w.exponent v)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (ws : List Digit) (hw : SignedWeights Q P ws) : ModelWeights P (ws.map f) := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · intro v
      have hwidths : ((ws.map f).map (fun w => w.physical.wires.length)).sum =
          (ws.map Digit.width).sum := by
        simp only [List.map_map, Function.comp_def, hwidth]
      rw [hwidths, ← hw.2.1, hpoint, hbias, hw.1]
      exact increment_offset P hr w.width w.exponent v (width_cases w)
    · exact ih hw.2.2


theorem left_base (Q : Point) (w : Digit) (hw : w ∈ leftDigits) : w.base Q = G := by
  simp only [leftDigits, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem right_base (Q : Point) (w : Digit) (hw : w ∈ rightDigits) : w.base Q = Q := by
  simp only [rightDigits, List.mem_append, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rfl

theorem left_modelWeights {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (first : WindowModel read) (f : Digit → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = w.width)
    (hpoint : ∀ w v, (f w).point v = increment (w.base Q) w.width w.exponent v)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (hfirst : ∀ v, first.point v = initialPoint Q v)
    (hfirstBias : first.bias = -(leftOffset • G + rightOffset • Q)) :
    ModelWeights G (first :: leftDigits.map f) := by
  constructor
  · intro v
    have hwidths : ((leftDigits.map f).map (fun w => w.physical.wires.length)).sum = 246 := by
      simp only [List.map_map, Function.comp_def, hwidth, left_widths]
      norm_num [List.replicate]
    rw [hwidths, hfirst, hfirstBias]
    unfold initialPoint
    simp only [add_nsmul]
    abel
  · exact modelWeights Q G generator_nsmul_eq_zero f hwidth hpoint hbias leftDigits (left_signed_weights Q)

theorem sum_nsmul (xs : List Nat) (P : Point) : (xs.map (fun k => k • P)).sum = xs.sum • P := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, add_nsmul]

theorem signed_bias_sum {n : Nat} {read : ConstantBit n → Bool}
    (Q P : Point) (f : Digit → WindowModel read)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (ws : List Digit) (hbase : ∀ w ∈ ws, w.base Q = P) :
    ((ws.map f).map WindowModel.bias).sum =
      (ws.map (fun w => Single.offsetScalar w.width w.exponent)).sum • P := by
  rw [← sum_nsmul]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  rw [hbias, hbase w hw]

theorem model_bias_cancels {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (first : WindowModel read) (f : Digit → WindowModel read)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (hfirstBias : first.bias = -(leftOffset • G + rightOffset • Q)) :
    ((first :: leftDigits.map f).map WindowModel.bias).sum +
      ((rightDigits.map f).map WindowModel.bias).sum = 0 := by
  simp only [List.map_cons, List.sum_cons]
  rw [signed_bias_sum Q G f hbias leftDigits (left_base Q),
    signed_bias_sum Q Q f hbias rightDigits (right_base Q), hfirstBias]
  change -(leftOffset • G + rightOffset • Q) + leftOffset • G + rightOffset • Q = 0
  abel


section
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]

theorem model_kernel {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (hQ : order • Q = 0) (root : BasisState) (ψ : State)
    (first : WindowModel read) (f : Digit → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = w.width)
    (hpoint : ∀ w v, (f w).point v = increment (w.base Q) w.width w.exponent v)
    (hbias : ∀ w, (f w).bias = Single.offsetScalar w.width w.exponent • w.base Q)
    (hfirstPoint : ∀ v, first.point v = initialPoint Q v)
    (hfirstBias : first.bias = -(leftOffset • G + rightOffset • Q))
    (hfirstRule : FirstRule root ψ first)
    (hpointRule : ∀ w ∈ leftDigits ++ rightDigits, PointRule root (f w)) :
    KernelLaw Q root (first :: leftDigits.map f) (rightDigits.map f) ψ := by
  apply kernelLaw_of_windows Q root ψ first (leftDigits.map f) (rightDigits.map f)
  · exact hfirstRule
  · intro w hw
    rw [← List.map_append] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hpointRule v hv
  · exact left_modelWeights Q first f hwidth hpoint hbias hfirstPoint hfirstBias
  · exact modelWeights Q Q hQ f hwidth hpoint hbias rightDigits (right_signed_weights Q)
  · exact model_bias_cancels Q first f hbias hfirstBias

end

end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
variable [b : Single.WindowBody]
noncomputable section
attribute [local irreducible] fourierOutcomes
omit b in
theorem bank_padding869 (w : Digit) : 869 ∉ bank w.width := by
  rcases width_cases w with h | h <;> rw [h] <;> decide +kernel

omit b in
theorem bank_padding868 (w : Digit) (hw : w.width = 14) : 868 ∉ bank w.width := by
  rw [hw]
  decide +kernel

omit b in
theorem bank_clean (width : Nat) (hw : width = 14 ∨ width = 15)
    (s : BasisState) (hz : Clean streamAddress s) : Clean (bank width) s :=
  fun v hv => hz v (bank_subset width hw v hv)

omit b in
theorem point_bank_clean (width : Nat) (hw : width = 14 ∨ width = 15)
    (P : Point) (s : BasisState) (hz : Clean streamAddress s) :
    Clean (bank width) (pointWrite P s) := by
  intro v hv
  simpa only [pointWrite_frame P s v (bank_not_point width hw v hv)] using
    bank_clean width hw s hz v hv

theorem assigned_valid (w : Digit) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) (input : List Bool) :
    WindowValid w (phaseWordState (bank w.width) input (pointWrite P s)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact phaseWordState_preserves (Single.BodyValid b) (bank w.width)
      (fun t ht v hv bit => Single.bodyValid_address t ht v
        (bank_subset w.width (width_cases w) v hv) bit) input _ (Single.bodyValid_first s hs P)
  · rw [phaseWordState_frame _ _ _ 869 (bank_padding869 w),
      pointWrite_frame P s 869 (by decide +kernel)]
    exact hz 869 (by decide +kernel)
  · intro hw
    rw [phaseWordState_frame _ _ _ 868 (bank_padding868 w hw),
      pointWrite_frame P s 868 (by decide +kernel)]
    exact hz 868 (by decide +kernel)

omit b in
theorem assigned_coordinates (width : Nat) (hw : width = 14 ∨ width = 15)
    (P : Point) (s : BasisState) (input : List Bool) :
    pointStateCoordinates (phaseWordState (bank width) input (pointWrite P s)) =
      fig14PointEncoding P := by
  rw [phaseWordState_pointWrite _ (bank_not_point width hw), pointWrite_coordinates]

omit b in
theorem assigned_digit (width : Nat) (hw : width = 14 ∨ width = 15)
    (s : BasisState) (input : List Bool) (hi : input.length = (bank width).length) :
    digit width (phaseWordState (bank width) input s) = boolWordToNat input := by
  have he (ws : List Wire) (t : BasisState) :
      tableAddressValue ws t = boolWordToNat (wireValues ws t) := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      change (t w).toNat + 2 * tableAddressValue ws t =
        (t w).toNat + 2 * boolWordToNat (wireValues ws t)
      rw [ih]
  rw [digit, he, phaseWordState_word _ (bank_nodup width hw) input hi s]

theorem signed_assigned_clear (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = w.width) :
    fourierClear (bank w.width).reverse
      (windowUpdate Q w (phaseWordState (bank w.width) input (pointWrite P s))) =
      pointWrite (P + increment (w.base Q) w.width w.exponent (boolWordToNat input)) s := by
  rw [windowUpdate_correct Q hQ hn w _ (assigned_valid w P s hs hz input) P
    (assigned_coordinates w.width (width_cases w) P s input),
    assigned_digit w.width (width_cases w) _ input (hi.trans (bank_length _ (width_cases w)).symm),
    clear_assigned_point _ input (pointWrite P s) (point_bank_clean w.width (width_cases w) P s hz)
      (bank_not_point w.width (width_cases w)), pointWrite_overwrite]


theorem signed_address_word (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = w.width) :
    (bank w.width).map
      (windowUpdate Q w (phaseWordState (bank w.width) input (pointWrite P s))) = input := by
  rw [windowUpdate_correct Q hQ hn w _ (assigned_valid w P s hs hz input) P
    (assigned_coordinates w.width (width_cases w) P s input)]
  have he : (bank w.width).map
      (pointWrite (P + increment (w.base Q) w.width w.exponent (digit w.width
        (phaseWordState (bank w.width) input (pointWrite P s))))
          (phaseWordState (bank w.width) input (pointWrite P s))) =
      (bank w.width).map (phaseWordState (bank w.width) input (pointWrite P s)) := by
    apply List.map_congr_left
    intro v hv
    exact pointWrite_frame _ _ v (bank_not_point w.width (width_cases w) v hv)
  rw [he]
  exact phaseWordState_word _ (bank_nodup w.width (width_cases w)) input
    (hi.trans (bank_length _ (width_cases w)).symm) _

theorem signed_window_point_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (prior output : List Bool) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse (bank w.width).reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)
        (Quantum.run ((bank w.width).map Gate.H) (ket (pointWrite P s)))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (P + increment (w.base Q) w.width w.exponent (boolWordToNat input)) s))).sum := by
  rw [window_branch_uniform .inverse (bank w.width) (bank_nodup w.width (width_cases w))
    (windowUpdate Q w) prior output _ (point_bank_clean w.width (width_cases w) P s hz)
    (fun input hi => signed_address_word Q hQ hn w P s hs hz input
      (by simpa only [bank_length _ (width_cases w)] using (fourierOutcomes_mem _ _).mp hi)),
    bank_length _ (width_cases w)]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [signed_assigned_clear Q hQ hn w P s hs hz input ((fourierOutcomes_mem _ _).mp hi)]

end
end

end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes

def signedModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit) :
    WindowModel (readConstant coefficientAt Q) where
  physical := signedWindow w
  point := increment (w.base Q) w.width w.exponent
  bias := Single.offsetScalar w.width w.exponent • w.base Q
  ideal := Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)
  valid := WindowValid w
  nodup := by rw [signedWindow_wires]; exact List.nodup_reverse.mpr (bank_nodup w.width (width_cases w))
  coherent := signedWindow_coherent Q hQ hn w

def firstModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) : WindowModel (readConstant coefficientAt Q) where
  physical := firstWindow
  point := initialPoint Q
  bias := -(leftOffset • G + rightOffset • Q)
  ideal := Finsupp.lmapDomain ℂ ℂ (ScheduleFirst18.update initialPoint Q)
  valid := ScheduleFirst18.Input
  nodup := by change ScheduleFirst18.bits.reverse.Nodup; exact List.nodup_reverse.mpr Single.first18_nodup
  coherent := by
    intro start history
    exact firstWindow_law Q hQ hn start history

omit ledger in
theorem signedModel_step (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (prior bits : List Bool) (P : Point) (root : BasisState)
    (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (signedModel Q hQ hn w).step prior bits (ket (pointWrite P root)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (P + increment (w.base Q) w.width w.exponent (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, signedModel, signedWindow_wires, List.reverse_reverse, LinearMap.comp_apply]
  exact signed_window_point_sum Q hQ hn w prior bits P root hs hz

omit b ledger in
theorem firstModel_step (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (prior bits : List Bool) (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (firstModel Q hQ hn).step prior bits (ket root) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 18) •
        ((fourierOutcomes 18).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (initialPoint Q (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, firstModel, firstWindow, ScheduleFirst18.windowGeneric, List.reverse_reverse, LinearMap.comp_apply]
  exact Single.first18_window_point_sum_generic initialPoint Q prior bits root hs hz

omit ledger in
theorem signedModel_pointRule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (signedModel Q hQ hn w) := by
  intro prior bits P
  simpa only [signedModel, signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)] using
    signedModel_step Q hQ hn w prior bits P root hs hz

omit b ledger in
theorem firstModel_firstRule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    FirstRule root (ket root) (firstModel Q hQ hn) := by
  intro prior bits
  have hlen : ScheduleFirst18.bits.length = 18 := by decide +kernel
  simpa only [firstModel, firstWindow, ScheduleFirst18.windowGeneric, List.length_reverse, hlen] using
    firstModel_step Q hQ hn prior bits root hs hz


omit ledger in
theorem signedModel_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (signedModel Q hQ hn w).valid
      (Quantum.run ((signedModel Q hQ hn w).physical.wires.reverse.map Gate.H) ψ) := by
  simp only [signedModel, signedWindow_wires, List.reverse_reverse]
  apply Support.linear (pointFamily root) (WindowValid w) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [phaseHadamards_uniform _ (bank_nodup w.width (width_cases w)) _
    (point_bank_clean w.width (width_cases w) P root hz)]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact supportedOn_ket _ _ (assigned_valid w P root hs hz input)

omit ledger in
theorem signedModel_preserves (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (prior bits : List Bool) (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (pointFamily root) ((signedModel Q hQ hn w).step prior bits ψ) := by
  apply Support.linear (pointFamily root) (pointFamily root) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [signedModel_step Q hQ hn w prior bits P root hs hz]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

omit ledger in
theorem ready_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    Ready (ws.map (signedModel Q hQ hn)) ψ := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · exact signedModel_prepared Q hQ hn w root hs hz ψ hψ
    · intro prior bits
      exact ih _ (signedModel_preserves Q hQ hn w root hs hz prior bits ψ hψ)

omit ledger in
theorem ready_first_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready (firstModel Q hQ hn :: ws.map (signedModel Q hQ hn)) (ket root) := by
  constructor
  · simp only [firstModel, firstWindow, ScheduleFirst18.windowGeneric, List.reverse_reverse]
    exact ScheduleFirst18.input_prepare _ (fun _ h => h) _
      (supportedOn_ket _ _ (ScheduleFirst18.input_of_strong root hs))
  · intro prior bits
    apply ready_signed Q hQ hn ws root hs hz
    rw [firstModel_step Q hQ hn prior bits root hs hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit ledger in
theorem concrete_ready (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready ((firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)) ++
      rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  rw [List.cons_append, ← List.map_append]
  exact ready_first_signed Q hQ hn (leftDigits ++ rightDigits) root hs hz

theorem concrete_kernel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    KernelLaw Q root (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  apply model_kernel Q hQ root (ket root) (firstModel Q hQ hn) (signedModel Q hQ hn)
  · intro w
    simp only [signedModel, signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]
  · intro w v
    rfl
  · intro w
    rfl
  · intro v
    rfl
  · rfl
  · exact firstModel_firstRule Q hQ hn root hs hz
  · intro w _
    exact signedModel_pointRule Q hQ hn w root hs hz

omit ledger in
theorem left_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)) = 264 := by
  rw [precision, List.map_cons, List.sum_cons]
  have hlen : ScheduleFirst18.bits.length = 18 := by decide +kernel
  simp only [firstModel, firstWindow, ScheduleFirst18.windowGeneric, List.length_reverse, hlen,
    List.map_map, Function.comp_def, signedModel, signedWindow_wires,
    bank_length _ (width_cases _), left_widths]
  norm_num [List.replicate]

omit ledger in
theorem right_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (rightDigits.map (signedModel Q hQ hn)) = 208 := by
  rw [precision]
  simp only [List.map_map, Function.comp_def, signedModel, signedWindow_wires,
    List.length_reverse, bank_length _ (width_cases _), right_widths]
  norm_num [List.replicate]
end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem concrete_event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (start : Nat) (history : Fin start → Bool) (J : Instrument)
    (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedTwoAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) start history (fun lhs rhs =>
        if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass (ket root) =
      idealEventMass Q root 264 208 accept := by
  rw [physicalTwoAxes_event_mass Q root _ _ start history _
    (concrete_ready Q hQ hn root hs hz) (concrete_kernel Q hQ hn root hs hz) J hJ accept,
    left_precision Q hQ hn, right_precision Q hQ hn]

end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody]
noncomputable section
attribute [local irreducible] resetProgram

def leftWindows : List (Single.Window 679936) := firstWindow :: leftDigits.map signedWindow

def rightWindows : List (Single.Window 679936) := rightDigits.map signedWindow

def leftMetadata : List (Nat × Nat) :=
  (262143, 18) :: List.replicate 8 (body.records, 15) ++ List.replicate 9 (body.records, 14)

def rightMetadata : List (Nat × Nat) :=
  List.replicate 12 (body.records, 15) ++ List.replicate 2 (body.records, 14)

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftDigits, signedWindow,
    Digit.width, bank, firstWindow, ScheduleFirst18.windowGeneric, ScheduleFirst18.bits, leftMetadata, List.ofFn_succ, List.replicate]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightDigits, signedWindow,
    Digit.width, bank, rightMetadata, List.ofFn_succ, List.replicate]

theorem left_record_count : recordCount leftMetadata = 262143 + 17 * body.records + 264 := by
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_record_count : recordCount rightMetadata = 14 * body.records + 208 := by
  simp [rightMetadata, recordCount, List.replicate]
  omega

variable [ledger : Single.ProducerResources body]

theorem left_count : axisCount leftWindows = 262143 + 17 * body.records + 264 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 14 * body.records + 208 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

def resetBody (start : Nat) : Straight 679936 start (start + body.reset.length) :=
  resetProgram 679936 start body.reset

omit ledger in
theorem resetBody_run (start : Nat) (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).run =
      (measureResetWithCorrection body.reset (fun _ => [])).run := by
  unfold resetBody
  rw [resetProgram_run]

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + body.reset.length

theorem trialCount_eq : trialCount = 262143 + 31 * body.records + 472 + body.reset.length := by
  rw [trialCount, left_count, right_count]
  omega

def trial (start : Nat) : Straight 679936 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

def program : Straight 679936 0 (262143 + 31 * body.records + 472 + body.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end
end


section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 264 := by
  rw [positions_length]
  simp [leftMetadata, List.replicate]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length]
  simp [rightMetadata, List.replicate]

def trialPositions : TrialPositions NeighborReadout.params264 where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params264] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (262143 + 17 * body.records + 264)).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params264] using right_positions_length (262143 + 17 * body.records + 264)⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 262143 + 17 * body.records + 264 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (262143 + 17 * body.records + 264) ≤ i ∧ i < 262143 + 31 * body.records + 472 := by
  have h := positions_bounds rightMetadata (262143 + 17 * body.records + 264) i
    (show i ∈ positions rightMetadata (262143 + 17 * body.records + 264) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

def finePositions : List (Fin (262143 + 31 * body.records + 472 + body.reset.length)) :=
  trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(right_position_bound i.val i.property).2.trans_le (by omega)⟩

theorem finePositions_length : finePositions.length = 208 := by
  simp [finePositions, NeighborReadout.params264]

def fineBits : Vector (Fin (262143 + 31 * body.records + 472 + body.reset.length)) 208 :=
  Vector.ofFn fun i=> finePositions[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout : Straight 679936 (262143 + 31 * body.records + 472 + body.reset.length)
    (262143 + 31 * body.records + 472 + body.reset.length + 34114) :=
  castFinish (by omega) (NeighborReadout.neighborSuffix 679936
    (262143 + 31 * body.records + 472 + body.reset.length) 208 fineBits)

def fullProgram : Straight 679936 0 (262143 + 31 * body.records + 472 + body.reset.length + 34114) :=
  program.append readout

def positionsFor (ps : Vector Nat 208) : TrialPositions NeighborReadout.params264 where
  left := trialPositions.left
  right := ps

def layout : DecodeLayout := ⟨.wrappedShift, NeighborReadout.params264,
  (NeighborReadout.rightWords fineBits).map positionsFor, by
    simp only [List.length_map, NeighborReadout.rightWords_length]; decide⟩

theorem readout_wellFormed : readout.WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact NeighborReadout.neighborSuffix_wellFormed 679936 (262143 + 31 * body.records + 472 + body.reset.length) 208 fineBits

theorem readout_t (read : ConstantBit 679936 → Bool)
    (h : Fin (262143 + 31 * body.records + 472 + body.reset.length) → Bool) :
    (readout.instantiate read h).tCount = 0 := by
  unfold readout
  rw [castFinish_instantiate]
  exact NeighborReadout.neighborSuffix_t 679936 (262143 + 31 * body.records + 472 + body.reset.length) 208 fineBits read h

end
end

end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] Single.axis resetProgram

omit ledger in
theorem concrete_model_left (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)).map WindowModel.physical = leftWindows := by
  simp only [firstModel, signedModel, leftWindows, List.map_cons, List.map_map, Function.comp_def]

omit ledger in
theorem concrete_model_right (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightDigits.map (signedModel Q hQ hn)).map WindowModel.physical = rightWindows := by
  simp only [signedModel, rightWindows, List.map_map, Function.comp_def]

omit ledger in
theorem left_positions (start : Nat) : axisPositions leftWindows start = positions leftMetadata start := by
  rw [Single.axisPositions, left_metadata]

omit ledger in
theorem right_positions (start : Nat) : axisPositions rightWindows start = positions rightMetadata start := by
  rw [Single.axisPositions, right_metadata]

def fineEvent (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  pairAccept trialPositions.left.toList trialPositions.right.toList accept history

theorem event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (J : Instrument) (hJ : ∀ ψ, J.bornMass ψ = normSq ψ) (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((physicalAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq J).filter
        (fun b => fineEvent accept b.history)) (ket root) =
      idealEventMass Q root 264 208 accept := by
  have hm := concrete_event_mass Q hQ hn root hs hz 0 Fin.elim0 J hJ accept
  rw [selectedTwoAxes_fixed_filter, concrete_model_left Q hQ hn, concrete_model_right Q hQ hn,
    left_count, left_positions, right_positions] at hm
  simpa only [fineEvent, trialPositions, Vector.toList_mk, List.toList_toArray] using hm

theorem program_run_data (read : ConstantBit 679936 → Bool) :
    (program.instantiate read Fin.elim0).run =
      ((physicalAxesData leftWindows rightWindows read 0 Fin.elim0).seq terminalInstrument).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  calc
    _ = ((trial 0).instantiate read Fin.elim0).run := by
      unfold program
      rw [castFinish_instantiate]
    _ = _ := by
      have hf : 0 + axisCount leftWindows + axisCount rightWindows + body.reset.length = 0 + trialCount := by
        unfold trialCount
        omega
      simpa only [trial, physicalAxesData, terminalInstrument] using
        framed_reset_run (axis leftWindows 0 List.nil)
          (axis rightWindows (0 + axisCount leftWindows) List.nil)
          (resetBody (0 + axisCount leftWindows + axisCount rightWindows)) hf read Fin.elim0
          (measureResetWithCorrection body.reset (fun _ => List.nil))
          (resetBody_run _ read)

theorem assembled_program_run (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).run =
      ((physicalAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq terminalInstrument).map
          (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  apply (program_run_data (readConstant coefficientAt Q)).trans
  apply congrArg (fun I : Instrument => (I.seq terminalInstrument).map
    (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b))
  change physicalAxesData leftWindows rightWindows _ _ _ = physicalAxesData _ _ _ _ _
  rw [concrete_model_left Q hQ hn, concrete_model_right Q hQ hn]

theorem program_event_mass (Q : Point) (hn : Q ≠ 0) (hQ : order • Q = 0)
    (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((program.instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent accept b.history)) (ket zeroBasisState) =
      idealEventMass Q initialRoot 264 208 accept := by
  rw [assembled_program_run Q hQ hn,
    prefix_filter_mass _ ([Gate.X 836]) (fineEvent accept) (ket zeroBasisState)]
  have hs : Quantum.run [.X 836] (ket zeroBasisState) = ket initialRoot := by
    simp [Quantum.run, applyGate_ket, onKet, initialRoot, zeroBasisState]
  rw [hs]
  exact event_mass Q hQ hn initialRoot initialRoot_input initialRoot_clean
    terminalInstrument terminalInstrument_mass accept

theorem program_neighbor_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ)/100 ≤ Instrument.bornMass
      (((program.instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent (NeighborReadout.pairRecovered264 d) b.history)) (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by
    rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [program_event_mass Q hn hQ, idealEventMass_distribution Q d hd]
  exact NeighborReadout.pair_success264 Q d hn hd

end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution RoundedReadout
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem fineBits_vals : fineBits.map Fin.val=trialPositions.right := by
  apply Vector.ext
  intro i hi
  simp [fineBits,finePositions]
  rfl

theorem program_clean (read : ConstantBit 679936 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (program.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [program_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  simp only [Single.Distribution.terminalInstrument, AdaptiveCircuit.run] at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean body.reset ledger.reset_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 ledger.reset_zero, h s hs 1 ledger.reset_one⟩

theorem verified_of_reads (ps : Vector Nat 208) (hps : ps∈NeighborReadout.rightWords fineBits)
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist trialPositions.left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d : ZMod order)∈fixedCandidates NeighborReadout.params264 a b) :
    (verifiedCandidate layout Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order),?_,?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨positionsFor ps,List.mem_map.mpr ⟨ps,hps,rfl⟩,?_⟩
    simpa only [decodeTrial,trialCandidates,positionsFor,layout,hl,hr,fixedCandidates_take,Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq,ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order];exact Nat.mod_mod _ _)

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q=d•G)
    (read : ConstantBit 679936→Bool) (history : Fin (262143 + 31 * body.records + 472 + body.reset.length)→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : fineEvent (NeighborReadout.pairRecovered264 d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈(readout.instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate layout Q (List.ofFn history++b.history)).isSome := by
  have hr:=NeighborReadout.input_read fineBits history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩:=Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩:=of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩:=NeighborReadout.neighborSuffix_reads 679936 (262143 + 31 * body.records + 472 + body.reset.length) fineBits
    read history ψ hψ b (by simpa only [readout, castFinish_instantiate] using hb) hn ((i.val : ℤ)-27) (by have h:=i.isLt;omega)
  apply verified_of_reads ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h:=left_position_bound j hj
    simpa only [List.length_ofFn] using h.trans (by omega : (262143 + 17 * body.records + 264)<(262143 + 31 * body.records + 472 + body.reset.length))

theorem program_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99/100 : ℝ) ≤ Instrument.bornMass ((fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) := by
  apply (program_neighbor_success Q d hn hd).trans
  unfold fullProgram
  rw [Single.append_run_history]
  apply Rounded.appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout.instantiate_wellFormed _ _ readout_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = (262143 + 31 * body.records + 472 + body.reset.length) := by
      have h := straight_history_length program (readConstant coefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter (262143 + 31 * body.records + 472 + body.reset.length) Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant coefficientAt Q)
      (Single.historyAfter (262143 + 31 * body.records + 472 + body.reset.length) Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

end
end ShorECDLP.Entrant.Schedule31Eighteen264


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes

def count (c14 c15 : Nat) (w : Digit) : Nat := if w.width = 14 then c14 else c15

class Programs (body : Single.WindowBody) where
  records14 : Nat
  records15 : Nat
  cost14 : Nat
  cost15 : Nat
  program : (w : Digit) → (start : Nat) → Straight 679936 start
    (start + count records14 records15 w)
  coherent : ∀ Q, order • Q = 0 → Q ≠ 0 → ∀ w start history,
    CoherentlyImplementsOn ((program w start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w)
  wellFormed : ∀ w start, (program w start).WellFormed
  slots : ∀ w start, (program w start).gateSlots ≤ body.slotBound
  wires : ∀ w start, straightWires (program w start) ⊆ body.support
  tCount : ∀ Q w start history,
    ((program w start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count cost14 cost15 w

variable [impl : Programs b]

def signedWindow (w : Digit) : Single.Window 679936 :=
  ⟨(bank w.width).reverse, count impl.records14 impl.records15 w, impl.program w⟩

def signedModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit) :
    WindowModel (readConstant coefficientAt Q) where
  physical := signedWindow w
  point := increment (w.base Q) w.width w.exponent
  bias := Single.offsetScalar w.width w.exponent • w.base Q
  ideal := Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)
  valid := WindowValid w
  nodup := by rw [signedWindow]; exact List.nodup_reverse.mpr (bank_nodup w.width (width_cases w))
  coherent := impl.coherent Q hQ hn w

omit ledger in
theorem signedModel_step (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (prior bits : List Bool) (P : Point) (root : BasisState)
    (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    (signedModel Q hQ hn w).step prior bits (ket (pointWrite P root)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.width) •
        ((fourierOutcomes w.width).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (P + increment (w.base Q) w.width w.exponent (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, signedModel, signedWindow, List.reverse_reverse, LinearMap.comp_apply]
  exact signed_window_point_sum Q hQ hn w prior bits P root hs hz

omit ledger in
theorem signedModel_pointRule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (signedModel Q hQ hn w) := by
  intro prior bits P
  simpa only [signedModel, signedWindow, List.length_reverse, bank_length _ (width_cases w)] using
    signedModel_step Q hQ hn w prior bits P root hs hz

omit ledger in
theorem signedModel_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (signedModel Q hQ hn w).valid
      (Quantum.run ((signedModel Q hQ hn w).physical.wires.reverse.map Gate.H) ψ) := by
  simp only [signedModel, signedWindow, List.reverse_reverse]
  apply Support.linear (pointFamily root) (WindowValid w) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [phaseHadamards_uniform _ (bank_nodup w.width (width_cases w)) _
    (point_bank_clean w.width (width_cases w) P root hz)]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact supportedOn_ket _ _ (assigned_valid w P root hs hz input)

omit ledger in
theorem signedModel_preserves (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (w : Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (prior bits : List Bool) (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (pointFamily root) ((signedModel Q hQ hn w).step prior bits ψ) := by
  apply Support.linear (pointFamily root) (pointFamily root) _ ?_ ψ hψ
  intro s h
  obtain ⟨P, rfl⟩ := h
  rw [signedModel_step Q hQ hn w prior bits P root hs hz]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

omit ledger in
theorem ready_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    Ready (ws.map (signedModel Q hQ hn)) ψ := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · exact signedModel_prepared Q hQ hn w root hs hz ψ hψ
    · intro prior bits
      exact ih _ (signedModel_preserves Q hQ hn w root hs hz prior bits ψ hψ)

omit ledger in
theorem ready_first_signed (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready (firstModel Q hQ hn :: ws.map (signedModel Q hQ hn)) (ket root) := by
  constructor
  · simp only [firstModel, firstWindow, ScheduleFirst18.windowGeneric, List.reverse_reverse]
    exact ScheduleFirst18.input_prepare _ (fun _ h => h) _
      (supportedOn_ket _ _ (ScheduleFirst18.input_of_strong root hs))
  · intro prior bits
    apply ready_signed Q hQ hn ws root hs hz
    rw [firstModel_step Q hQ hn prior bits root hs hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit ledger in
theorem concrete_ready (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    Ready ((firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)) ++
      rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  rw [List.cons_append, ← List.map_append]
  exact ready_first_signed Q hQ hn (leftDigits ++ rightDigits) root hs hz

theorem concrete_kernel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    KernelLaw Q root (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) (ket root) := by
  apply model_kernel Q hQ root (ket root) (firstModel Q hQ hn) (signedModel Q hQ hn)
  · intro w
    simp only [signedModel, signedWindow, List.length_reverse, bank_length _ (width_cases w)]
  · intro w v
    rfl
  · intro w
    rfl
  · intro v
    rfl
  · rfl
  · exact firstModel_firstRule Q hQ hn root hs hz
  · intro w _
    exact signedModel_pointRule Q hQ hn w root hs hz

omit ledger in
theorem left_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)) = 264 := by
  rw [precision, List.map_cons, List.sum_cons]
  have hlen : ScheduleFirst18.bits.length = 18 := by decide +kernel
  simp only [firstModel, firstWindow, ScheduleFirst18.windowGeneric, List.length_reverse, hlen,
    List.map_map, Function.comp_def, signedModel, signedWindow,
    bank_length _ (width_cases _), left_widths]
  norm_num [List.replicate]

omit ledger in
theorem right_precision (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    precision (rightDigits.map (signedModel Q hQ hn)) = 208 := by
  rw [precision]
  simp only [List.map_map, Function.comp_def, signedModel, signedWindow,
    List.length_reverse, bank_length _ (width_cases _), right_widths]
  norm_num [List.replicate]
end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem concrete_event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (start : Nat) (history : Fin start → Bool) (J : Instrument)
    (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedTwoAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
      (rightDigits.map (signedModel Q hQ hn)) start history (fun lhs rhs =>
        if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass (ket root) =
      idealEventMass Q root 264 208 accept := by
  rw [physicalTwoAxes_event_mass Q root _ _ start history _
    (concrete_ready Q hQ hn root hs hz) (concrete_kernel Q hQ hn root hs hz) J hJ accept,
    left_precision Q hQ hn, right_precision Q hQ hn]

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible



namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body]
noncomputable section
attribute [local irreducible] resetProgram

def leftWindows : List (Single.Window 679936) := firstWindow :: leftDigits.map signedWindow

def rightWindows : List (Single.Window 679936) := rightDigits.map signedWindow

def leftMetadata : List (Nat × Nat) :=
  (262143, 18) :: List.replicate 8 (impl.records15, 15) ++ List.replicate 9 (impl.records14, 14)

def rightMetadata : List (Nat × Nat) :=
  List.replicate 12 (impl.records15, 15) ++ List.replicate 2 (impl.records14, 14)

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftDigits, signedWindow,
    Digit.width, count, bank, firstWindow, ScheduleFirst18.windowGeneric, ScheduleFirst18.bits, leftMetadata, List.ofFn_succ, List.replicate]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightDigits, signedWindow,
    Digit.width, count, bank, rightMetadata, List.ofFn_succ, List.replicate]

theorem left_record_count : recordCount leftMetadata = 262143 + 8 * impl.records15 + 9 * impl.records14 + 264 := by
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_record_count : recordCount rightMetadata = 12 * impl.records15 + 2 * impl.records14 + 208 := by
  simp [rightMetadata, recordCount, List.replicate]
  omega

variable [ledger : Single.ProducerResources body]

theorem left_count : axisCount leftWindows = 262143 + 8 * impl.records15 + 9 * impl.records14 + 264 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 12 * impl.records15 + 2 * impl.records14 + 208 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

def resetBody (start : Nat) : Straight 679936 start (start + body.reset.length) :=
  resetProgram 679936 start body.reset

omit ledger impl in
theorem resetBody_run (start : Nat) (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).run =
      (measureResetWithCorrection body.reset (fun _ => [])).run := by
  unfold resetBody
  rw [resetProgram_run]

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + body.reset.length

theorem trialCount_eq : trialCount = 262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length := by
  rw [trialCount, left_count, right_count]
  omega

def trial (start : Nat) : Straight 679936 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

def program : Straight 679936 0 (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end
end


section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 264 := by
  rw [positions_length]
  simp [leftMetadata, List.replicate]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length]
  simp [rightMetadata, List.replicate]

def trialPositions : TrialPositions NeighborReadout.params264 where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params264] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (262143 + 8 * impl.records15 + 9 * impl.records14 + 264)).toArray, by
    simpa only [List.size_toArray, NeighborReadout.params264] using right_positions_length (262143 + 8 * impl.records15 + 9 * impl.records14 + 264)⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 262143 + 8 * impl.records15 + 9 * impl.records14 + 264 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (262143 + 8 * impl.records15 + 9 * impl.records14 + 264) ≤ i ∧ i < 262143 + 20 * impl.records15 + 11 * impl.records14 + 472 := by
  have h := positions_bounds rightMetadata (262143 + 8 * impl.records15 + 9 * impl.records14 + 264) i
    (show i ∈ positions rightMetadata (262143 + 8 * impl.records15 + 9 * impl.records14 + 264) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

def finePositions : List (Fin (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length)) :=
  trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(right_position_bound i.val i.property).2.trans_le (by omega)⟩

theorem finePositions_length : finePositions.length = 208 := by
  simp [finePositions, NeighborReadout.params264]

def fineBits : Vector (Fin (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length)) 208 :=
  Vector.ofFn fun i=> finePositions[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout : Straight 679936 (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length)
    (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length + 34114) :=
  castFinish (by omega) (NeighborReadout.neighborSuffix 679936
    (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) 208 fineBits)

def fullProgram : Straight 679936 0 (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length + 34114) :=
  program.append readout

def positionsFor (ps : Vector Nat 208) : TrialPositions NeighborReadout.params264 where
  left := trialPositions.left
  right := ps

def layout : DecodeLayout := ⟨.wrappedShift, NeighborReadout.params264,
  (NeighborReadout.rightWords fineBits).map positionsFor, by
    simp only [List.length_map, NeighborReadout.rightWords_length]; decide⟩

theorem readout_wellFormed : readout.WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact NeighborReadout.neighborSuffix_wellFormed 679936 (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) 208 fineBits

theorem readout_t (read : ConstantBit 679936 → Bool)
    (h : Fin (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) → Bool) :
    (readout.instantiate read h).tCount = 0 := by
  unfold readout
  rw [castFinish_instantiate]
  exact NeighborReadout.neighborSuffix_t 679936 (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) 208 fineBits read h

end
end

end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] Single.axis resetProgram

omit ledger in
theorem concrete_model_left (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)).map WindowModel.physical = leftWindows := by
  simp only [firstModel, signedModel, leftWindows, List.map_cons, List.map_map, Function.comp_def]

omit ledger in
theorem concrete_model_right (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightDigits.map (signedModel Q hQ hn)).map WindowModel.physical = rightWindows := by
  simp only [signedModel, rightWindows, List.map_map, Function.comp_def]

omit ledger in
theorem left_positions (start : Nat) : axisPositions leftWindows start = positions leftMetadata start := by
  rw [Single.axisPositions, left_metadata]

omit ledger in
theorem right_positions (start : Nat) : axisPositions rightWindows start = positions rightMetadata start := by
  rw [Single.axisPositions, right_metadata]

def fineEvent (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  pairAccept trialPositions.left.toList trialPositions.right.toList accept history

theorem event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (J : Instrument) (hJ : ∀ ψ, J.bornMass ψ = normSq ψ) (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((physicalAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq J).filter
        (fun b => fineEvent accept b.history)) (ket root) =
      idealEventMass Q root 264 208 accept := by
  have hm := concrete_event_mass Q hQ hn root hs hz 0 Fin.elim0 J hJ accept
  rw [selectedTwoAxes_fixed_filter, concrete_model_left Q hQ hn, concrete_model_right Q hQ hn,
    left_count, left_positions, right_positions] at hm
  simpa only [fineEvent, trialPositions, Vector.toList_mk, List.toList_toArray] using hm

theorem program_run_data (read : ConstantBit 679936 → Bool) :
    (program.instantiate read Fin.elim0).run =
      ((physicalAxesData leftWindows rightWindows read 0 Fin.elim0).seq terminalInstrument).map
        (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  calc
    _ = ((trial 0).instantiate read Fin.elim0).run := by
      unfold program
      rw [castFinish_instantiate]
    _ = _ := by
      have hf : 0 + axisCount leftWindows + axisCount rightWindows + body.reset.length = 0 + trialCount := by
        unfold trialCount
        omega
      simpa only [trial, physicalAxesData, terminalInstrument] using
        framed_reset_run (axis leftWindows 0 List.nil)
          (axis rightWindows (0 + axisCount leftWindows) List.nil)
          (resetBody (0 + axisCount leftWindows + axisCount rightWindows)) hf read Fin.elim0
          (measureResetWithCorrection body.reset (fun _ => List.nil))
          (resetBody_run _ read)

theorem assembled_program_run (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).run =
      ((physicalAxes (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn))
        (rightDigits.map (signedModel Q hQ hn)) 0 Fin.elim0).seq terminalInstrument).map
          (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b) := by
  apply (program_run_data (readConstant coefficientAt Q)).trans
  apply congrArg (fun I : Instrument => (I.seq terminalInstrument).map
    (fun b => ({history := List.nil, kraus := Quantum.run [.X 836]} : InstrumentBranch).seq b))
  change physicalAxesData leftWindows rightWindows _ _ _ = physicalAxesData _ _ _ _ _
  rw [concrete_model_left Q hQ hn, concrete_model_right Q hQ hn]

theorem program_event_mass (Q : Point) (hn : Q ≠ 0) (hQ : order • Q = 0)
    (accept : Nat → Nat → Bool) :
    Instrument.bornMass
      (((program.instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent accept b.history)) (ket zeroBasisState) =
      idealEventMass Q initialRoot 264 208 accept := by
  rw [assembled_program_run Q hQ hn,
    prefix_filter_mass _ ([Gate.X 836]) (fineEvent accept) (ket zeroBasisState)]
  have hs : Quantum.run [.X 836] (ket zeroBasisState) = ket initialRoot := by
    simp [Quantum.run, applyGate_ket, onKet, initialRoot, zeroBasisState]
  rw [hs]
  exact event_mass Q hQ hn initialRoot initialRoot_input initialRoot_clean
    terminalInstrument terminalInstrument_mass accept

theorem program_neighbor_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99 : ℝ)/100 ≤ Instrument.bornMass
      (((program.instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => fineEvent (NeighborReadout.pairRecovered264 d) b.history)) (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by
    rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [program_event_mass Q hn hQ, idealEventMass_distribution Q d hd]
  exact NeighborReadout.pair_success264 Q d hn hd

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution RoundedReadout
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem fineBits_vals : fineBits.map Fin.val=trialPositions.right := by
  apply Vector.ext
  intro i hi
  simp [fineBits,finePositions]
  rfl

theorem program_clean (read : ConstantBit 679936 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (program.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [program_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  simp only [Single.Distribution.terminalInstrument, AdaptiveCircuit.run] at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean body.reset ledger.reset_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 ledger.reset_zero, h s hs 1 ledger.reset_one⟩

theorem verified_of_reads (ps : Vector Nat 208) (hps : ps∈NeighborReadout.rightWords fineBits)
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist trialPositions.left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d : ZMod order)∈fixedCandidates NeighborReadout.params264 a b) :
    (verifiedCandidate layout Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order),?_,?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨positionsFor ps,List.mem_map.mpr ⟨ps,hps,rfl⟩,?_⟩
    simpa only [decodeTrial,trialCandidates,positionsFor,layout,hl,hr,fixedCandidates_take,Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq,ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order];exact Nat.mod_mod _ _)

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q=d•G)
    (read : ConstantBit 679936→Bool) (history : Fin (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length)→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : fineEvent (NeighborReadout.pairRecovered264 d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈(readout.instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate layout Q (List.ofFn history++b.history)).isSome := by
  have hr:=NeighborReadout.input_read fineBits history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩:=Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩:=of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩:=NeighborReadout.neighborSuffix_reads 679936 (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) fineBits
    read history ψ hψ b (by simpa only [readout, castFinish_instantiate] using hb) hn ((i.val : ℤ)-27) (by have h:=i.isLt;omega)
  apply verified_of_reads ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h:=left_position_bound j hj
    simpa only [List.length_ofFn] using h.trans (by omega : (262143 + 8 * impl.records15 + 9 * impl.records14 + 264)<(262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length))

theorem program_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99/100 : ℝ) ≤ Instrument.bornMass ((fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) := by
  apply (program_neighbor_success Q d hn hd).trans
  unfold fullProgram
  rw [Single.append_run_history]
  apply Rounded.appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout.instantiate_wellFormed _ _ readout_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) := by
      have h := straight_history_length program (readConstant coefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant coefficientAt Q)
      (Single.historyAfter (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit body in
theorem coefficients_aliased (w : Digit) : ModAliased (w.width-1) (windowCoefficients w) := by
  intro a
  unfold windowCoefficients paddedRow reducedAddress
  congr 2
  apply Fin.ext
  simp only [Nat.mod_mod]

omit body in
theorem coefficients_half_aliased (w : Digit) : HalfAliased (windowCoefficients w) := by
  intro a
  unfold windowCoefficients paddedRow
  congr 2
  apply Fin.ext
  cases w <;> norm_num [Digit.width]

def dualPrograms (n14 : ModNarrow body 13) (n15 : UniformNarrow body) : Programs body where
  records14 := n14.records
  records15 := n15.records
  cost14 := n14.tBound
  cost15 := n15.tBound
  program := fun w start =>
    if h : w.width = 14 then
      castFinish (by simp [count,h]) (reindexStraight (paddedRow w) (n14.program start))
    else castFinish (by simp [count,h]) (reindexStraight (paddedRow w) (n15.program start))
  coherent := by
    intro Q hQ hn w start history
    have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
      intro a
      have he := window_table_point Q hQ w a.val
      simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
      rw [he]
      exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
    by_cases hw : w.width = 14
    · have ha : ModAliased 13 (windowCoefficients w) := by
        simpa only [hw, Nat.reduceSub] using coefficients_aliased w
      have h := n14.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_pos hw, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
    · have hw15 : w.width = 15 := (width_cases w).resolve_left hw
      have ha : HalfAliased (windowCoefficients w) := coefficients_half_aliased w
      have h := n15.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_neg hw, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
  wellFormed := by
    intro w start
    by_cases h : w.width = 14
    · rw [dif_pos h, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n14.wellFormed start)
    · rw [dif_neg h, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n15.wellFormed start)
  slots := by
    intro w start
    by_cases h : w.width = 14
    · rw [dif_pos h, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n14.slots start
    · rw [dif_neg h, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n15.slots start
  wires := by
    intro w start
    by_cases h : w.width = 14
    · rw [dif_pos h, straightWires_castFinish, straightWires_reindex]
      exact n14.wires start
    · rw [dif_neg h, straightWires_castFinish, straightWires_reindex]
      exact n15.wires start
  tCount := by
    intro Q w start history
    by_cases h : w.width = 14
    · rw [dif_pos h, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h, if_true] using n14.tCount start _ history
    · rw [dif_neg h, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h, if_false] using n15.tCount start _ history

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ScheduleFirst18.program resetProgram leftWindows rightWindows resetBody

def leftCosts (cost15 cost14 : Nat) : List (Nat × Nat) :=
  (1835001, 18) :: List.replicate 8 (cost15, 15) ++ List.replicate 9 (cost14, 14)
def rightCosts (cost15 cost14 : Nat) : List (Nat × Nat) :=
  List.replicate 12 (cost15, 15) ++ List.replicate 2 (cost14, 14)

omit body impl ledger in
theorem left_t_budget (cost15 cost14 : Nat) :
    Single.metadataT (leftCosts cost15 cost14) 0 =
      1835001 + 8 * cost15 + 9 * cost14 + 34716 := by
  simp [leftCosts, List.replicate, Single.metadataT, fourierSlots]
  omega

omit body impl ledger in
theorem right_t_budget (cost15 cost14 : Nat) :
    Single.metadataT (rightCosts cost15 cost14) 0 = 12 * cost15 + 2 * cost14 + 21528 := by
  simp [rightCosts, List.replicate, Single.metadataT, fourierSlots]
  omega

omit body impl ledger in
theorem firstWindow_wellFormed (start : Nat) : (firstWindow.program start).WellFormed := by
  exact ScheduleFirst18.window_wellFormed firstRow start

omit body impl ledger in
theorem firstWindow_slots (start : Nat) : (firstWindow.program start).gateSlots ≤ 3000000000 := by
  exact (ScheduleFirst18.window_slots firstRow start).trans (by norm_num)

omit body impl ledger in
theorem firstWindow_t_uniform (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 1835001 := by
  exact ScheduleFirst18.window_t coefficientAt firstRow Q start history

omit impl ledger in
theorem resetBody_wellFormed (start : Nat) : (resetBody start).WellFormed := by
  unfold resetBody
  exact resetProgram_wellFormed _ _ _
omit impl ledger in
theorem resetBody_slots (start : Nat) : (resetBody start).gateSlots = 0 := by
  unfold resetBody
  rw [resetProgram_gateSlots]
omit impl ledger in
theorem resetBody_t (start : Nat) (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).tCount = 0 := by
  unfold resetBody
  rw [resetProgram_t]

omit ledger in
theorem signedWindow_wires (w : Digit) : (signedWindow w).wires = (bank w.width).reverse := rfl

omit ledger in
theorem signedWindow_t (Q : Point) (w : Digit) (start : Nat) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count impl.cost14 impl.cost15 w := impl.tCount Q w start history

omit ledger in
theorem signedWindow_wellFormed (w : Digit) (start : Nat) :
    ((signedWindow w).program start).WellFormed := impl.wellFormed w start

omit ledger in
theorem signedWindow_slots (w : Digit) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ body.slotBound := impl.slots w start

omit ledger in
theorem windows_cases (w : Single.Window 679936) (hw : w ∈ leftWindows ++ rightWindows) :
    w = firstWindow ∨ ∃ s, w = signedWindow s := by
  simp only [leftWindows, rightWindows, List.mem_append, List.mem_cons, List.mem_map] at hw
  rcases hw with (h | ⟨s, _, h⟩) | ⟨s, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h.symm⟩
  · exact Or.inr ⟨s, h.symm⟩

omit ledger in
theorem windows_wellFormed (w : Single.Window 679936) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).WellFormed := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_wellFormed start
  · exact signedWindow_wellFormed s start

def windowSlots : Nat := max 3000000000 body.slotBound

omit ledger in
theorem windows_slots (w : Single.Window 679936) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).gateSlots ≤ windowSlots := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact (firstWindow_slots start).trans (Nat.le_max_left _ _)
  · exact (signedWindow_slots s start).trans (Nat.le_max_right _ _)

theorem trial_wellFormed (start : Nat) : (trial start).WellFormed := by
  unfold trial
  apply framed_wellFormed
  · exact axis_wellFormed leftWindows (fun w hw => windows_wellFormed w (List.mem_append_left _ hw)) _ _
  · exact axis_wellFormed rightWindows (fun w hw => windows_wellFormed w (List.mem_append_right _ hw)) _ _
  · exact resetBody_wellFormed _

omit ledger in
theorem slots_budget : metadataSlots windowSlots leftMetadata 0 +
    metadataSlots windowSlots rightMetadata 0 + 2 = 32 * windowSlots + 56718 := by
  simp [leftMetadata, rightMetadata, metadataSlots, List.replicate, fourierSlots]
  omega

theorem trial_slots (start : Nat) : (trial start).gateSlots ≤ 32 * windowSlots + 56718 := by
  have hl := axis_slots leftWindows windowSlots
    (fun w hw => windows_slots w (List.mem_append_left _ hw)) start List.nil
  have hr := axis_slots rightWindows windowSlots
    (fun w hw => windows_slots w (List.mem_append_right _ hw)) (start + axisCount leftWindows) List.nil
  rw [left_metadata] at hl
  rw [right_metadata] at hr
  simp only [List.length_nil] at hl hr
  unfold trial
  rw [framed_slots, resetBody_slots]
  have h := slots_budget
  omega

theorem program_wellFormed : program.WellFormed := by
  unfold program
  rw [castFinish_wellFormed]
  exact trial_wellFormed 0

theorem program_slots : program.gateSlots ≤ 32 * windowSlots + 56718 := by
  unfold program
  rw [castFinish_gateSlots]
  exact trial_slots 0


omit ledger in
theorem signed_costs (Q : Point) (ws : List Digit) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      (ws.map signedWindow) (ws.map (fun w => (count impl.cost14 impl.cost15 w, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => signedWindow_t Q w start h⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

omit ledger in
theorem left_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      leftWindows (leftCosts impl.cost15 impl.cost14) := by
  have he : leftCosts impl.cost15 impl.cost14 =
      (1835001, 18) :: leftDigits.map (fun w => (count impl.cost14 impl.cost15 w, w.width)) := by
    simp [leftCosts, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  unfold leftWindows
  refine .cons ⟨?_, fun start h => (firstWindow_t_uniform Q start h).le⟩ (signed_costs Q leftDigits)
  simp only [firstWindow, ScheduleFirst18.windowGeneric, List.length_reverse]
  decide

omit ledger in
theorem right_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      rightWindows (rightCosts impl.cost15 impl.cost14) := by
  have he : rightCosts impl.cost15 impl.cost14 =
      rightDigits.map (fun w => (count impl.cost14 impl.cost15 w, w.width)) := by
    simp [rightCosts, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  simpa only [rightWindows] using signed_costs Q rightDigits

theorem left_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      1835001 + 8 * impl.cost15 + 9 * impl.cost14 + 34716 := by
  have h := axis_t leftWindows (readConstant coefficientAt Q) (leftCosts impl.cost15 impl.cost14)
    (left_costs Q) start List.nil history
  have hm := left_t_budget impl.cost15 impl.cost14
  simp only [List.length_nil, hm] at h
  omega

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      12 * impl.cost15 + 2 * impl.cost14 + 21528 := by
  have h := axis_t rightWindows (readConstant coefficientAt Q) (rightCosts impl.cost15 impl.cost14)
    (right_costs Q) start List.nil history
  have hm := right_t_budget impl.cost15 impl.cost14
  simp only [List.length_nil, hm] at h
  omega

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      1835001 + 20 * impl.cost15 + 11 * impl.cost14 + 56244 := by
  unfold trial
  apply (framed_t_le _ _ _ _ _ history (1835001 + 8 * impl.cost15 + 9 * impl.cost14 + 34716)
    (12 * impl.cost15 + 2 * impl.cost14 + 21528) (left_axis_t Q start history)
    (fun h => right_axis_t Q _ h) (fun h => resetBody_t _ _ h)).trans
  omega

theorem program_t (Q : Point) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      1835001 + 20 * impl.cost15 + 11 * impl.cost14 + 56244 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ScheduleFirst18.program resetProgram leftWindows rightWindows resetBody

class SupportCover (body : Single.WindowBody) (ledger : Single.ProducerResources body) : Prop where
  covers : body.support ⊆ ledger.support

variable [cover : SupportCover body ledger]

omit impl cover in
theorem stream_support : streamAddress ⊆ ledger.support := by
  intro v hv
  exact ledger.initial_support (List.mem_append_right _ hv)

omit cover in
theorem windows_bank_support (w : Single.Window 679936) (hw : w ∈ leftWindows ++ rightWindows) :
    w.wires ⊆ ledger.support := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · intro v hv
    apply ledger.initial_support
    have hbits : ScheduleFirst18.bits ⊆ resetWires := by decide +kernel
    exact hbits (List.mem_reverse.mp hv)
  · rw [signedWindow_wires]
    intro v hv
    exact stream_support (bank_subset s.width (width_cases s) v (List.mem_reverse.mp hv))

theorem windows_support (w : Single.Window 679936) (hw : w ∈ leftWindows ++ rightWindows)
    (start : Nat) (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ ledger.support := by
  apply (straight_instantiate_support _ read history).trans
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact (ScheduleFirst18.window_support firstRow start).trans ledger.initial_support
  · exact (impl.wires s start).trans cover.covers

omit impl cover in
private theorem flag_support : (836 : Wire) ∈ ledger.support := by
  apply ledger.initial_support
  simp [resetWires]

omit impl cover in
theorem resetBody_support (start : Nat) (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).wires ⊆ ledger.support := by
  unfold resetBody
  exact resetProgram_support _ _ _ _ read history ledger.reset_support

theorem left_axis_support (start : Nat) (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support leftWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_left _ hw))
    (fun w hw => windows_support w (List.mem_append_left _ hw)) start List.nil read history

theorem right_axis_support (start : Nat) (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support rightWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_right _ hw))
    (fun w hw => windows_support w (List.mem_append_right _ hw)) start List.nil read history

theorem trial_support (start : Nat) (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    ((trial start).instantiate read history).wires ⊆ ledger.support := by
  unfold trial
  exact framed_support _ _ _ _ read history ledger.support flag_support
    (left_axis_support start read history) (fun h => right_axis_support _ read h)
    (fun h => resetBody_support _ read h)

theorem program_support (read : ConstantBit 679936 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ ledger.support := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_support 0 read Fin.elim0

omit cover in
theorem readout_support (read : ConstantBit 679936 → Bool)
    (h : Fin (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) → Bool) :
    (readout.instantiate read h).wires ⊆ ledger.support := by
  unfold readout
  rw [castFinish_instantiate]
  apply (NeighborReadout.neighborSuffix_support 679936
    (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) 208 fineBits read h).trans
  have hs : [0,1] ⊆ resetWires := by simp [List.subset_def, resetWires]
  exact hs.trans ledger.initial_support

theorem fullProgram_support (read : ConstantBit 679936 → Bool) :
    (fullProgram.instantiate read Fin.elim0).wires ⊆ ledger.support :=
  outer_append_support _ _ read Fin.elim0 ledger.support (program_support read) (readout_support read)

theorem fullProgram_qubits (read : ConstantBit 679936 → Bool) :
    (fullProgram.instantiate read Fin.elim0).qubitCount ≤ ledger.support.length := by
  have hs : (fullProgram.instantiate read Fin.elim0).wires.dedup.toFinset ⊆
      ledger.support.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (fullProgram_support read (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount] using hc

omit cover in
theorem fullProgram_t (Q : Point) :
    (fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      1835001 + 20 * impl.cost15 + 11 * impl.cost14 + 56244 := by
  have h := outer_append_t_le program readout (readConstant coefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  change ((program.append readout).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤ _
  exact h.trans (by simpa only [Nat.add_zero] using program_t Q)

omit cover in
theorem fullProgram_wellFormed : fullProgram.WellFormed :=
  straight_append_wellFormed _ _ program_wellFormed readout_wellFormed

omit cover in
theorem fullProgram_slots : fullProgram.gateSlots ≤ 32 * windowSlots + 176382 := by
  unfold fullProgram
  rw [Straight.gateSlots_append]
  have hr : readout.gateSlots = 119399 := by
    unfold readout
    rw [castFinish_gateSlots]
    exact NeighborReadout.neighborSuffix_slots 679936
      (262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length) 208 fineBits
  rw [hr]
  have h := program_slots
  omega


def entry : StraightEntry := Single.fixedEntry coefficientAt fullProgram

def bounds : Bounds := ⟨ledger.support.length, 1835001 + 20 * impl.cost15 + 11 * impl.cost14 + 56244,
  262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length + 34114⟩

theorem certificate
    (hSlots : 32 * windowSlots + 176382 ≤ officialLimits.gateSlots)
    (hRecords : 262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length + 34114 ≤ officialLimits.measurements) :
    Certificate officialLimits layout entry bounds where
  gateBudget := by
    rw [entry, Single.fixedEntry_slots]
    exact fullProgram_slots.trans hSlots
  recordBudget := by
    exact hRecords
  tableBudget := by
    rw [entry, Single.fixedEntry_rows]
    decide
  candidateBudget := by
    change 55 * (2*(order/2^208+2)) ≤ 56*(2^49+2)
    exact NeighborReadout.decoder_budget
  wellFormed := by
    rw [entry, Single.fixedEntry_wellFormed]
    exact fullProgram_wellFormed
  resources := by
    intro Q
    rw [entry, Single.fixedEntry_instantiate]
    exact ⟨fullProgram_qubits _, fullProgram_t Q, (fullProgram.measurementCount _ _).le⟩
  success := by
    intro Q d hn hd
    rw [entry, Single.fixedEntry_instantiate]
    exact program_success Q d hn hd

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] leftWindows rightWindows program fullProgram readout entry Single.axis ScheduleFirst18.program

omit body impl ledger in
theorem first_count (start : Nat) : AtLeast (firstWindow.program start) 262143 := by
  have h := ScheduleFirst18.window_credit coefficientAt firstRow 0 start (fun _ => false)
  exact h.ge

structure ProgramCredit (c14 c15 : Nat) : Prop where
  zero : ∀ w start, residue (impl.program w start) = 0
  count_eq : ∀ w start, added (impl.program w start) = count c14 c15 w

variable {c14 c15 : Nat} (hc : ProgramCredit c14 c15)
include hc

omit ledger in
theorem signed_credit (w : Digit) (start : Nat) :
    AtLeast ((signedWindow w).program start) (count c14 c15 w) := by
  simpa only [signedWindow, AtLeast] using (hc.count_eq w start).ge

def leftCounted : List (CountedWindow 679936) :=
  ⟨firstWindow, 262143, first_count⟩ :: leftDigits.map
    (fun w => ⟨signedWindow w, count c14 c15 w, signed_credit hc w⟩)

def rightCounted : List (CountedWindow 679936) :=
  rightDigits.map (fun w => ⟨signedWindow w, count c14 c15 w, signed_credit hc w⟩)

theorem parent_credit : AtLeast entry.program (262143 + 20 * c15 + 11 * c14) := by
  have hl := counted_axis (leftCounted hc) 0 List.nil
  have hr := counted_axis (rightCounted hc) (0 + Single.axisCount leftWindows) List.nil
  have hls : (leftCounted hc).map CountedWindow.source = leftWindows := by
    simp [leftCounted, leftWindows]
  have hrs : (rightCounted hc).map CountedWindow.source = rightWindows := by
    simp [rightCounted, rightWindows]
  have hln : ((leftCounted hc).map CountedWindow.saving).sum = 262143 + 8 * c15 + 9 * c14 := by
    simp [leftCounted, leftDigits, List.ofFn_succ, Digit.width, count]
    omega
  have hrn : ((rightCounted hc).map CountedWindow.saving).sum = 12 * c15 + 2 * c14 := by
    simp [rightCounted, rightDigits, List.ofFn_succ, Digit.width, count]
    omega
  rw [hls, hln] at hl
  rw [hrs, hrn] at hr
  have ht : AtLeast (trial 0) (262143 + 20 * c15 + 11 * c14) := by
    unfold trial
    exact (framed_credit _ _ _ _ hl hr).castCount (by omega)
  have hp : AtLeast program (262143 + 20 * c15 + 11 * c14) := by
    unfold program
    exact ht.castFinish _
  unfold entry fullProgram
  apply fixedEntry_credit
  exact (hp.append (AtLeast.zero _)).castCount (by omega)

omit ledger in
theorem signed_t (w : Digit) (start : Nat)
    (read : ConstantBit 679936 → Bool) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate read history).tCount =
      7 * count c14 c15 w := by
  unfold signedWindow
  rw [exact_t _ (hc.zero w start), hc.count_eq w start]

def creditLeftCosts : List (Nat × Nat) := leftCosts (7*c15) (7*c14)
def creditRightCosts : List (Nat × Nat) := rightCosts (7*c15) (7*c14)

omit ledger in
theorem signed_costs_credit (ws : List Digit) (read : ConstantBit 679936 → Bool) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1)
      (ws.map signedWindow) (ws.map (fun w => (7 * count c14 c15 w, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => (signed_t hc w start read h).le⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

theorem producer_t (Q : Point) :
    (fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      7 * (262143 + 20 * c15 + 11 * c14) + 56244 := by
  let read := readConstant coefficientAt Q
  have lc : List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1) leftWindows
      (creditLeftCosts (c14 := c14) (c15 := c15)) := by
    have he : creditLeftCosts (c14 := c14) (c15 := c15) =
        (1835001,18) :: leftDigits.map (fun w => (7 * count c14 c15 w, w.width)) := by
      simp [creditLeftCosts, leftCosts, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
    rw [he]
    unfold leftWindows
    refine .cons ⟨?_, fun start h => (firstWindow_t_uniform Q start h).le⟩
      (signed_costs_credit hc leftDigits read)
    simp only [firstWindow, ScheduleFirst18.windowGeneric, List.length_reverse]
    decide
  have hl := Single.axis_t leftWindows read _ lc 0 List.nil Fin.elim0
  have hr : ∀ h, ((Single.axis rightWindows
      (0 + Single.axisCount leftWindows) List.nil).instantiate read h).tCount ≤
      Single.metadataT (creditRightCosts (c14 := c14) (c15 := c15)) 0 := by
    intro h
    apply Single.axis_t rightWindows read _ _ _ List.nil h
    have he : creditRightCosts (c14 := c14) (c15 := c15) =
        rightDigits.map (fun w => (7 * count c14 c15 w, w.width)) := by
      simp [creditRightCosts, rightCosts, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
    rw [he]
    simpa only [rightWindows] using signed_costs_credit hc rightDigits read
  have hln : Single.metadataT (creditLeftCosts (c14 := c14) (c15 := c15)) 0 =
      1835001 + 8 * (7*c15) + 9 * (7*c14) + 34716 := left_t_budget _ _
  have hrn : Single.metadataT (creditRightCosts (c14 := c14) (c15 := c15)) 0 =
      12 * (7*c15) + 2 * (7*c14) + 21528 := right_t_budget _ _
  have ht := Single.framed_t_le (Single.axis leftWindows 0 List.nil)
    (Single.axis rightWindows (0 + Single.axisCount leftWindows) List.nil)
    (resetBody (0 + Single.axisCount leftWindows + Single.axisCount rightWindows))
    (show 0 + Single.axisCount leftWindows + Single.axisCount rightWindows +
      body.reset.length = 0 + trialCount from by unfold trialCount; omega)
    read Fin.elim0 _ _ hl hr (resetBody_t _ read)
  have hp : (program.instantiate read Fin.elim0).tCount ≤
      Single.metadataT (creditLeftCosts (c14 := c14) (c15 := c15)) 0 +
        Single.metadataT (creditRightCosts (c14 := c14) (c15 := c15)) 0 := by
    unfold program trial
    simpa only [castFinish_instantiate] using ht
  have hs := outer_append_t_le program readout read Fin.elim0 0
    (fun h => (readout_t read h).le)
  unfold fullProgram
  change ((program.append readout).instantiate read Fin.elim0).tCount ≤ _
  rw [hln] at hp
  rw [hrn] at hp
  omega


omit hc body impl ledger in
private theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m)
    (ws : List Wire) (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hp.2⟩
  | measure => exact ⟨hp.1, by apply_assumption; exact hp.2⟩

variable [cover : SupportCover body ledger]

omit hc body impl ledger in
private theorem fixedEntry_within {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (ws : List Wire) (hp : Within ws p) : Within ws (Single.fixedEntry f p).program := by
  unfold Single.fixedEntry
  exact within_reindex p _ ws hp

omit hc in
theorem fullProgram_within : Within ledger.support fullProgram := by
  apply within_of_instantiate
  intro read history
  have he : history = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst history
  exact fullProgram_support read

omit hc in
theorem compiler_within : Within ledger.support entry.program := by
  unfold entry
  exact fixedEntry_within coefficientAt fullProgram ledger.support fullProgram_within

theorem four_certificate (q y : Wire)
    (hBaseSlots : 32 * windowSlots + 176382 ≤ officialLimits.gateSlots)
    (hBaseRecords : 262143 + 20 * impl.records15 + 11 * impl.records14 + 472 +
      body.reset.length + 34114 ≤ officialLimits.measurements)
    (hq : q ∉ ledger.support) (hy : y ∉ q :: ledger.support)
    (hslots : entry.program.gateSlots + 21 * added entry.program +
      3 * Catalyst.saved entry.program + 2 ≤ officialLimits.gateSlots)
    (hrecords : entry.finalCursor + added entry.program ≤ officialLimits.measurements) :
    Certificate officialLimits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ledger.support (262143 + 20 * c15 + 11 * c14) 56244) := by
  have base := certificate hBaseSlots hBaseRecords
  have source : Certificate officialLimits layout entry
      ⟨ledger.support.length, 7 * (262143 + 20 * c15 + 11 * c14) + 56244, entry.finalCursor⟩ :=
    { base with
      resources := by
        intro Q
        refine ⟨(base.resources Q).1, ?_, ?_⟩
        change (entry.instantiate Q).tCount ≤ _
        rw [entry, Single.fixedEntry_instantiate]
        · exact producer_t hc Q
        · simpa only [bounds, entry, Single.fixedEntry] using (base.resources Q).2.2 }
  exact WEXCredit.four_certificate officialLimits layout entry ledger.support
    (262143 + 20 * c15 + 11 * c14) 56244 q y source compiler_within hq hy
    (parent_credit hc) hslots hrecords

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
variable [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] entry program fullProgram readout Single.fixedEntry AndGadget.added Catalyst.saved

omit cover in
theorem source_cursor : entry.finalCursor =
    262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length + 34114 := by
  unfold entry
  rw [Single.fixedEntry_cursor]

omit cover in
theorem source_slots : entry.program.gateSlots ≤ 32 * windowSlots + 176382 := by
  unfold entry
  rw [Single.fixedEntry_slots]
  exact fullProgram_slots

theorem source_counts (q y : Wire) (sourceBound : Nat)
    (hBaseSlots : 32 * windowSlots + 176382 ≤ officialLimits.gateSlots)
    (hBaseRecords : 262143 + 20 * impl.records15 + 11 * impl.records14 + 472 +
      body.reset.length + 34114 ≤ officialLimits.measurements)
    (hSource : 1835001 + 20 * impl.cost15 + 11 * impl.cost14 + 56244 ≤ sourceBound) :
    added entry.program ≤ sourceBound ∧ Catalyst.saved entry.program ≤ sourceBound := by
  have h := four_identity q y entry.program (readConstant entry.coefficients.get 0) Fin.elim0
  have ht := ((certificate hBaseSlots hBaseRecords).resources 0).2.1
  change (entry.program.instantiate (readConstant entry.coefficients.get 0) Fin.elim0).tCount ≤
    1835001 + 20 * impl.cost15 + 11 * impl.cost14 + 56244 at ht
  omega

theorem bounded_four_certificate {c14 c15 : Nat} (hc : ProgramCredit c14 c15)
    (q y : Wire) (sourceBound : Nat)
    (hBaseSlots : 32 * windowSlots + 176382 ≤ officialLimits.gateSlots)
    (hBaseRecords : 262143 + 20 * impl.records15 + 11 * impl.records14 + 472 +
      body.reset.length + 34114 ≤ officialLimits.measurements)
    (hSource : 1835001 + 20 * impl.cost15 + 11 * impl.cost14 + 56244 ≤ sourceBound)
    (hSlots : 32 * windowSlots + 176382 + 24 * sourceBound + 2 ≤ officialLimits.gateSlots)
    (hRecords : 262143 + 20 * impl.records15 + 11 * impl.records14 + 472 + body.reset.length +
      34114 + sourceBound ≤ officialLimits.measurements)
    (hq : q ∉ ledger.support) (hy : y ∉ q :: ledger.support) :
    Certificate officialLimits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ledger.support (262143 + 20 * c15 + 11 * c14) 56244) := by
  have hc' := source_counts q y sourceBound hBaseSlots hBaseRecords hSource
  have hs := source_slots
  have hm := source_cursor
  apply four_certificate hc q y hBaseSlots hBaseRecords hq hy
  · omega
  · omega

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem dualProgramCredit (n14 : ModNarrow body 13) (n15 : UniformNarrow body) :
    @ProgramCredit body (dualPrograms n14 n15) n14.credit n15.credit := by
  refine @ProgramCredit.mk body (dualPrograms n14 n15) n14.credit n15.credit ?_ ?_
  · intro w start
    by_cases h : w.width = 14
    · change residue (if h : w.width = 14 then castFinish _ (reindexStraight (paddedRow w) (n14.program start))
        else castFinish _ (reindexStraight (paddedRow w) (n15.program start))) = 0
      rw [dif_pos h, residue_cast, residue_reindex]
      exact n14.zero start
    · change residue (if h : w.width = 14 then castFinish _ (reindexStraight (paddedRow w) (n14.program start))
        else castFinish _ (reindexStraight (paddedRow w) (n15.program start))) = 0
      rw [dif_neg h, residue_cast, residue_reindex]
      exact n15.zero start
  · intro w start
    by_cases h : w.width = 14
    · change added (if h : w.width = 14 then castFinish _ (reindexStraight (paddedRow w) (n14.program start))
        else castFinish _ (reindexStraight (paddedRow w) (n15.program start))) = count n14.credit n15.credit w
      rw [dif_pos h, added_cast, added_reindex, n14.count_eq start]
      simp [count,h]
    · change added (if h : w.width = 14 then castFinish _ (reindexStraight (paddedRow w) (n14.program start))
        else castFinish _ (reindexStraight (paddedRow w) (n15.program start))) = count n14.credit n15.credit w
      rw [dif_neg h, added_cast, added_reindex, n15.count_eq start]
      simp [count,h]

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible






end

namespace ShorECDLP.Entrant
open ShorECDLP Secp256k1
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem numericNoncube : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 38597363079105398474523661669562635951089994888546854679819194669302944890554 = ((55594575648329892869085402983802832744385952214688224221778511981742606582254 : Nat) : Fp) := by
  have h0 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1 = ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) := by simp
  have h1 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2 = ((49 : Nat) : Fp) := by
    rw [show (2 : Nat) = 1 * 2 + 0 from rfl, pow_add, pow_mul, h0, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h2 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 5 = ((115792089237316195423570985008687907853269984665640564039457584007908834654856 : Nat) : Fp) := by
    rw [show (5 : Nat) = 2 * 2 + 1 from rfl, pow_add, pow_mul, h1, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h3 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 10 = ((282475249 : Nat) : Fp) := by
    rw [show (10 : Nat) = 5 * 2 + 0 from rfl, pow_add, pow_mul, h2, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h4 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 21 = ((115792089237316195423570985008687907853269984665640564039457025462044751387656 : Nat) : Fp) := by
    rw [show (21 : Nat) = 10 * 2 + 1 from rfl, pow_add, pow_mul, h3, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h5 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 42 = ((311973482284542371301330321821976049 : Nat) : Fp) := by
    rw [show (42 : Nat) = 21 * 2 + 0 from rfl, pow_add, pow_mul, h4, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h6 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 85 = ((115791407945140654217861498477676213610033413355780191279366061751326927118856 : Nat) : Fp) := by
    rw [show (85 : Nat) = 42 * 2 + 1 from rfl, pow_add, pow_mul, h5, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h7 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 170 = ((87148117373801171930577940919474928790314434041307146863971672161775006287828 : Nat) : Fp) := by
    rw [show (170 : Nat) = 85 * 2 + 0 from rfl, pow_add, pow_mul, h6, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h8 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 341 = ((11670274311942621407522636024318331851529863944052938155220666316256716437841 : Nat) : Fp) := by
    rw [show (341 : Nat) = 170 * 2 + 1 from rfl, pow_add, pow_mul, h7, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h9 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 682 = ((6290206582281333064583891106380535924855300648875041265288094855696568584647 : Nat) : Fp) := by
    rw [show (682 : Nat) = 341 * 2 + 0 from rfl, pow_add, pow_mul, h8, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h10 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1365 = ((18904131434715043613350691152443812524618480232860081148592315459759038168525 : Nat) : Fp) := by
    rw [show (1365 : Nat) = 682 * 2 + 1 from rfl, pow_add, pow_mul, h9, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h11 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2730 = ((63715549478547472247427046846895688580574588172528502549461527261681585309996 : Nat) : Fp) := by
    rw [show (2730 : Nat) = 1365 * 2 + 0 from rfl, pow_add, pow_mul, h10, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h12 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 5461 = ((51326719014686317818543512923802109457408900876830541112954433133014590961916 : Nat) : Fp) := by
    rw [show (5461 : Nat) = 2730 * 2 + 1 from rfl, pow_add, pow_mul, h11, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h13 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 10922 = ((45616462631252662483532343888479175542028943577518925198410187721079638939717 : Nat) : Fp) := by
    rw [show (10922 : Nat) = 5461 * 2 + 0 from rfl, pow_add, pow_mul, h12, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h14 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 21845 = ((57278431290033993104725012980543019047407540515678671969254800032223558439639 : Nat) : Fp) := by
    rw [show (21845 : Nat) = 10922 * 2 + 1 from rfl, pow_add, pow_mul, h13, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h15 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 43690 = ((106264381190160609101552613149668150170531843904815863574855309298169310143701 : Nat) : Fp) := by
    rw [show (43690 : Nat) = 21845 * 2 + 0 from rfl, pow_add, pow_mul, h14, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h16 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 87381 = ((82457823345146664411665713323702993902176052727014699217227570115804087684568 : Nat) : Fp) := by
    rw [show (87381 : Nat) = 43690 * 2 + 1 from rfl, pow_add, pow_mul, h15, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h17 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 174762 = ((8946746289730628007270778589115420543442579651984516130737039258203660335677 : Nat) : Fp) := by
    rw [show (174762 : Nat) = 87381 * 2 + 0 from rfl, pow_add, pow_mul, h16, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h18 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 349525 = ((82383840761917436080792454802283618306061492823668166552571324811066410616135 : Nat) : Fp) := by
    rw [show (349525 : Nat) = 174762 * 2 + 1 from rfl, pow_add, pow_mul, h17, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h19 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 699050 = ((59741106052438371505500988119956228571605064461268211022534154194821258180783 : Nat) : Fp) := by
    rw [show (699050 : Nat) = 349525 * 2 + 0 from rfl, pow_add, pow_mul, h18, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h20 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1398101 = ((71155237064500919965368971696555275735711752371410021777629976903843327615405 : Nat) : Fp) := by
    rw [show (1398101 : Nat) = 699050 * 2 + 1 from rfl, pow_add, pow_mul, h19, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h21 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2796202 = ((36339241279265304517380107137055602084857002579201191268958955552571441836092 : Nat) : Fp) := by
    rw [show (2796202 : Nat) = 1398101 * 2 + 0 from rfl, pow_add, pow_mul, h20, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h22 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 5592405 = ((110456198574347130220357126604647299899884939970391729382698242727479775962953 : Nat) : Fp) := by
    rw [show (5592405 : Nat) = 2796202 * 2 + 1 from rfl, pow_add, pow_mul, h21, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h23 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 11184810 = ((67045383516225953069918313113051530471537395933067066524800453062504333393649 : Nat) : Fp) := by
    rw [show (11184810 : Nat) = 5592405 * 2 + 0 from rfl, pow_add, pow_mul, h22, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h24 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 22369621 = ((98774563018936037876553171569425556744845942131111262576794858633718148338267 : Nat) : Fp) := by
    rw [show (22369621 : Nat) = 11184810 * 2 + 1 from rfl, pow_add, pow_mul, h23, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h25 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 44739242 = ((109265180444758137226230957020464527071382209745848938229758874900426682587809 : Nat) : Fp) := by
    rw [show (44739242 : Nat) = 22369621 * 2 + 0 from rfl, pow_add, pow_mul, h24, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h26 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 89478485 = ((25768271117101405199315638803562981113920576581227667042758524032840948306202 : Nat) : Fp) := by
    rw [show (89478485 : Nat) = 44739242 * 2 + 1 from rfl, pow_add, pow_mul, h25, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h27 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 178956970 = ((18630464392908229227090407106585547139665925939739831433567577940309686393554 : Nat) : Fp) := by
    rw [show (178956970 : Nat) = 89478485 * 2 + 0 from rfl, pow_add, pow_mul, h26, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h28 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 357913941 = ((12909726029998486783177864577907462543142000096255108109063198145086023048751 : Nat) : Fp) := by
    rw [show (357913941 : Nat) = 178956970 * 2 + 1 from rfl, pow_add, pow_mul, h27, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h29 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 715827882 = ((23353503594186287250092159609746168004389456068718269296258898465101650271134 : Nat) : Fp) := by
    rw [show (715827882 : Nat) = 357913941 * 2 + 0 from rfl, pow_add, pow_mul, h28, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h30 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1431655765 = ((57266785286434301861090629743276721656686125464959706015086976026172533677877 : Nat) : Fp) := by
    rw [show (1431655765 : Nat) = 715827882 * 2 + 1 from rfl, pow_add, pow_mul, h29, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h31 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2863311530 = ((3126471454098042949711442365070970076405764838111181588740610616718485012679 : Nat) : Fp) := by
    rw [show (2863311530 : Nat) = 1431655765 * 2 + 0 from rfl, pow_add, pow_mul, h30, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h32 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 5726623061 = ((13910051886530225312438803246341412892799997474343529944154254169654379372678 : Nat) : Fp) := by
    rw [show (5726623061 : Nat) = 2863311530 * 2 + 1 from rfl, pow_add, pow_mul, h31, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h33 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 11453246122 = ((87970157137084166613430101996368831136032452938770851709811861910473911536632 : Nat) : Fp) := by
    rw [show (11453246122 : Nat) = 5726623061 * 2 + 0 from rfl, pow_add, pow_mul, h32, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h34 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 22906492245 = ((86510195296188049310558620096785284241198711225002039011578441978596282269414 : Nat) : Fp) := by
    rw [show (22906492245 : Nat) = 11453246122 * 2 + 1 from rfl, pow_add, pow_mul, h33, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h35 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 45812984490 = ((38429792057460019363190176914530812591771258756951974985126372919240417495412 : Nat) : Fp) := by
    rw [show (45812984490 : Nat) = 22906492245 * 2 + 0 from rfl, pow_add, pow_mul, h34, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h36 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 91625968981 = ((78147488758019617939564587742571188475585449691717570410281541718809033718702 : Nat) : Fp) := by
    rw [show (91625968981 : Nat) = 45812984490 * 2 + 1 from rfl, pow_add, pow_mul, h35, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h37 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 183251937962 = ((56432906178872135595847772930535997378872438271104099918897170718739014948820 : Nat) : Fp) := by
    rw [show (183251937962 : Nat) = 91625968981 * 2 + 0 from rfl, pow_add, pow_mul, h36, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h38 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 366503875925 = ((3791706797647533210617931268968217119290385357176354134026937474090825958288 : Nat) : Fp) := by
    rw [show (366503875925 : Nat) = 183251937962 * 2 + 1 from rfl, pow_add, pow_mul, h37, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h39 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 733007751850 = ((20633019071260931739967835216741822645615008671823084849531947405862540028400 : Nat) : Fp) := by
    rw [show (733007751850 : Nat) = 366503875925 * 2 + 0 from rfl, pow_add, pow_mul, h38, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h40 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1466015503701 = ((89082354230060793220098041288236389299246080487775418557983304543750820169981 : Nat) : Fp) := by
    rw [show (1466015503701 : Nat) = 733007751850 * 2 + 1 from rfl, pow_add, pow_mul, h39, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h41 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2932031007402 = ((107727322279893299870510498874501721220064377783066138544746895754564906358465 : Nat) : Fp) := by
    rw [show (2932031007402 : Nat) = 1466015503701 * 2 + 0 from rfl, pow_add, pow_mul, h40, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h42 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 5864062014805 = ((53549824874776083135821177923946462608198817010835592371095852518822058778099 : Nat) : Fp) := by
    rw [show (5864062014805 : Nat) = 2932031007402 * 2 + 1 from rfl, pow_add, pow_mul, h41, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h43 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 11728124029610 = ((111873817380072923692494794364622016754743982547929724031527842365743614245478 : Nat) : Fp) := by
    rw [show (11728124029610 : Nat) = 5864062014805 * 2 + 0 from rfl, pow_add, pow_mul, h42, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h44 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 23456248059221 = ((82419480504488661208396463428512099389071495443511985887271096936589419256514 : Nat) : Fp) := by
    rw [show (23456248059221 : Nat) = 11728124029610 * 2 + 1 from rfl, pow_add, pow_mul, h43, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h45 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 46912496118442 = ((114155628388819053091842418049705075753529166283431698743579778943137530210562 : Nat) : Fp) := by
    rw [show (46912496118442 : Nat) = 23456248059221 * 2 + 0 from rfl, pow_add, pow_mul, h44, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h46 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 93824992236885 = ((17740148964839144206350523745278749354095560109558237863712083909391602140169 : Nat) : Fp) := by
    rw [show (93824992236885 : Nat) = 46912496118442 * 2 + 1 from rfl, pow_add, pow_mul, h45, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h47 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 187649984473770 = ((38794470726003736958038452252290654557410798609867798086230836169510970690630 : Nat) : Fp) := by
    rw [show (187649984473770 : Nat) = 93824992236885 * 2 + 0 from rfl, pow_add, pow_mul, h46, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h48 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 375299968947541 = ((22292240854109929301734573494010825222049920719154201212599025831264491420140 : Nat) : Fp) := by
    rw [show (375299968947541 : Nat) = 187649984473770 * 2 + 1 from rfl, pow_add, pow_mul, h47, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h49 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 750599937895082 = ((87260780461196222333384727897123749802793553847534915841399952709899541078974 : Nat) : Fp) := by
    rw [show (750599937895082 : Nat) = 375299968947541 * 2 + 0 from rfl, pow_add, pow_mul, h48, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h50 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1501199875790165 = ((50203116255325675223790043706437721619432277130886004520467134943508267565 : Nat) : Fp) := by
    rw [show (1501199875790165 : Nat) = 750599937895082 * 2 + 1 from rfl, pow_add, pow_mul, h49, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h51 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3002399751580330 = ((7880995578728594602473907165513419281459664616281629116649978160799231589742 : Nat) : Fp) := by
    rw [show (3002399751580330 : Nat) = 1501199875790165 * 2 + 0 from rfl, pow_add, pow_mul, h50, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h52 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 6004799503160661 = ((56408696362973905955541547608250305390125689212509837280445835608241391987415 : Nat) : Fp) := by
    rw [show (6004799503160661 : Nat) = 3002399751580330 * 2 + 1 from rfl, pow_add, pow_mul, h51, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h53 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 12009599006321322 = ((104230609484671125887923010162470258586316976466603874896183377026597126651171 : Nat) : Fp) := by
    rw [show (12009599006321322 : Nat) = 6004799503160661 * 2 + 0 from rfl, pow_add, pow_mul, h52, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h54 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 24019198012642645 = ((38935787116164502007736016129015986684891047093903297758918545818951388286914 : Nat) : Fp) := by
    rw [show (24019198012642645 : Nat) = 12009599006321322 * 2 + 1 from rfl, pow_add, pow_mul, h53, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h55 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 48038396025285290 = ((31607132951957223821076381449443975973195041457945554169368282216740514695843 : Nat) : Fp) := by
    rw [show (48038396025285290 : Nat) = 24019198012642645 * 2 + 0 from rfl, pow_add, pow_mul, h54, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h56 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 96076792050570581 = ((37282819869064410966610129008493964141982911470153575782876077757672436277485 : Nat) : Fp) := by
    rw [show (96076792050570581 : Nat) = 48038396025285290 * 2 + 1 from rfl, pow_add, pow_mul, h55, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h57 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 192153584101141162 = ((87857953242140456237243911609150062306008050857365325667535925806171540217361 : Nat) : Fp) := by
    rw [show (192153584101141162 : Nat) = 96076792050570581 * 2 + 0 from rfl, pow_add, pow_mul, h56, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h58 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 384307168202282325 = ((16286231835520562515838427807626461170326335065876532017998526711334733538241 : Nat) : Fp) := by
    rw [show (384307168202282325 : Nat) = 192153584101141162 * 2 + 1 from rfl, pow_add, pow_mul, h57, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h59 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 768614336404564650 = ((2761165657123386019536889101935211447971311113845005878633619212301644173087 : Nat) : Fp) := by
    rw [show (768614336404564650 : Nat) = 384307168202282325 * 2 + 0 from rfl, pow_add, pow_mul, h58, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h60 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1537228672809129301 = ((18150096097851531519346303671619302714319572760461066720383229792390179876307 : Nat) : Fp) := by
    rw [show (1537228672809129301 : Nat) = 768614336404564650 * 2 + 1 from rfl, pow_add, pow_mul, h59, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h61 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3074457345618258602 = ((2515794628051404484441580330863594643174472080228955448554786264943333502899 : Nat) : Fp) := by
    rw [show (3074457345618258602 : Nat) = 1537228672809129301 * 2 + 0 from rfl, pow_add, pow_mul, h60, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h62 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 6148914691236517205 = ((104765814908155708163691215240458482440012458792931111981114389833022341704618 : Nat) : Fp) := by
    rw [show (6148914691236517205 : Nat) = 3074457345618258602 * 2 + 1 from rfl, pow_add, pow_mul, h61, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h63 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 12297829382473034410 = ((99694589728260684704920004031300956481483404073924784426893665847624307706714 : Nat) : Fp) := by
    rw [show (12297829382473034410 : Nat) = 6148914691236517205 * 2 + 0 from rfl, pow_add, pow_mul, h62, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h64 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 24595658764946068821 = ((68647559313308156331782250140321145552658101926504645706217701725986520826843 : Nat) : Fp) := by
    rw [show (24595658764946068821 : Nat) = 12297829382473034410 * 2 + 1 from rfl, pow_add, pow_mul, h63, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h65 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 49191317529892137642 = ((111797722323278646824335603533305635191266854938786215473429322116267822026000 : Nat) : Fp) := by
    rw [show (49191317529892137642 : Nat) = 24595658764946068821 * 2 + 0 from rfl, pow_add, pow_mul, h64, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h66 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 98382635059784275285 = ((11078574019058512021960665018146663998361463547980321659400609527415438180340 : Nat) : Fp) := by
    rw [show (98382635059784275285 : Nat) = 49191317529892137642 * 2 + 1 from rfl, pow_add, pow_mul, h65, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h67 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 196765270119568550570 = ((66873744855872365428699150311793129121923865169106542091186949786980513105468 : Nat) : Fp) := by
    rw [show (196765270119568550570 : Nat) = 98382635059784275285 * 2 + 0 from rfl, pow_add, pow_mul, h66, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h68 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 393530540239137101141 = ((14534214126582595339070544830195428687366727451944569427223582682558985748370 : Nat) : Fp) := by
    rw [show (393530540239137101141 : Nat) = 196765270119568550570 * 2 + 1 from rfl, pow_add, pow_mul, h67, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h69 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 787061080478274202282 = ((7216468390216749462989334423941514590146588808431606703519054689179354888865 : Nat) : Fp) := by
    rw [show (787061080478274202282 : Nat) = 393530540239137101141 * 2 + 0 from rfl, pow_add, pow_mul, h68, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h70 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1574122160956548404565 = ((21495985081863351393796932733875075305058294957030338569356887842189622233768 : Nat) : Fp) := by
    rw [show (1574122160956548404565 : Nat) = 787061080478274202282 * 2 + 1 from rfl, pow_add, pow_mul, h69, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h71 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3148244321913096809130 = ((37197434818240401096632559295813222360871770928658765135697485689707177075353 : Nat) : Fp) := by
    rw [show (3148244321913096809130 : Nat) = 1574122160956548404565 * 2 + 0 from rfl, pow_add, pow_mul, h70, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h72 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 6296488643826193618261 = ((27261277614488193089632954337008081803758669069825273125383038031228451494003 : Nat) : Fp) := by
    rw [show (6296488643826193618261 : Nat) = 3148244321913096809130 * 2 + 1 from rfl, pow_add, pow_mul, h71, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h73 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 12592977287652387236522 = ((52311248902545033863250739187017611852338642793565623192202232359197382274586 : Nat) : Fp) := by
    rw [show (12592977287652387236522 : Nat) = 6296488643826193618261 * 2 + 0 from rfl, pow_add, pow_mul, h72, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h74 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 25185954575304774473045 = ((110432206694632116615284331647386186384650571550843623281951690641673696014398 : Nat) : Fp) := by
    rw [show (25185954575304774473045 : Nat) = 12592977287652387236522 * 2 + 1 from rfl, pow_add, pow_mul, h73, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h75 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 50371909150609548946090 = ((79067011711656134237514482838270134380594726362498394711353888236606861406803 : Nat) : Fp) := by
    rw [show (50371909150609548946090 : Nat) = 25185954575304774473045 * 2 + 0 from rfl, pow_add, pow_mul, h74, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h76 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 100743818301219097892181 = ((111262111720845096287588435892905113464206601515978849737078670978694164944313 : Nat) : Fp) := by
    rw [show (100743818301219097892181 : Nat) = 50371909150609548946090 * 2 + 1 from rfl, pow_add, pow_mul, h75, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h77 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 201487636602438195784362 = ((72283782183776327376101422325261305561811906974081203715606579499638822974054 : Nat) : Fp) := by
    rw [show (201487636602438195784362 : Nat) = 100743818301219097892181 * 2 + 0 from rfl, pow_add, pow_mul, h76, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h78 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 402975273204876391568725 = ((55003706824719305639804854639547259814548732368303657745804803730371113316535 : Nat) : Fp) := by
    rw [show (402975273204876391568725 : Nat) = 201487636602438195784362 * 2 + 1 from rfl, pow_add, pow_mul, h77, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h79 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 805950546409752783137450 = ((31555166125647732967298197218793456950868266925661949432699457470374662631840 : Nat) : Fp) := by
    rw [show (805950546409752783137450 : Nat) = 402975273204876391568725 * 2 + 0 from rfl, pow_add, pow_mul, h78, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h80 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1611901092819505566274901 = ((53189250157740658043225343454120092453530534877375219829903567625389548336054 : Nat) : Fp) := by
    rw [show (1611901092819505566274901 : Nat) = 805950546409752783137450 * 2 + 1 from rfl, pow_add, pow_mul, h79, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h81 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3223802185639011132549802 = ((36349159474008570932271003179876595239318733902933559061923443582834183533742 : Nat) : Fp) := by
    rw [show (3223802185639011132549802 : Nat) = 1611901092819505566274901 * 2 + 0 from rfl, pow_add, pow_mul, h80, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h82 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 6447604371278022265099605 = ((99825267548745631165155844933395906523404795892328655295138147922672026784752 : Nat) : Fp) := by
    rw [show (6447604371278022265099605 : Nat) = 3223802185639011132549802 * 2 + 1 from rfl, pow_add, pow_mul, h81, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h83 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 12895208742556044530199210 = ((105556572277707243496999695154759207193206802556623582361690931584356439086880 : Nat) : Fp) := by
    rw [show (12895208742556044530199210 : Nat) = 6447604371278022265099605 * 2 + 0 from rfl, pow_add, pow_mul, h82, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h84 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 25790417485112089060398421 = ((24874548690146524909814307316193529862098755240203635096284735127910177604839 : Nat) : Fp) := by
    rw [show (25790417485112089060398421 : Nat) = 12895208742556044530199210 * 2 + 1 from rfl, pow_add, pow_mul, h83, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h85 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 51580834970224178120796842 = ((30906294687459664771907444567801968235505584981712969564350692192533786636403 : Nat) : Fp) := by
    rw [show (51580834970224178120796842 : Nat) = 25790417485112089060398421 * 2 + 0 from rfl, pow_add, pow_mul, h84, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h86 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 103161669940448356241593685 = ((90045678553885953850237529031022710856122351661411094484206205210097489959743 : Nat) : Fp) := by
    rw [show (103161669940448356241593685 : Nat) = 51580834970224178120796842 * 2 + 1 from rfl, pow_add, pow_mul, h85, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h87 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 206323339880896712483187370 = ((43972388463218012299204134280299126233125454068948759772279166055342699526004 : Nat) : Fp) := by
    rw [show (206323339880896712483187370 : Nat) = 103161669940448356241593685 * 2 + 0 from rfl, pow_add, pow_mul, h86, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h88 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 412646679761793424966374741 = ((71367782303121147405198828815003921013076191110236279245049844102520061381978 : Nat) : Fp) := by
    rw [show (412646679761793424966374741 : Nat) = 206323339880896712483187370 * 2 + 1 from rfl, pow_add, pow_mul, h87, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h89 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 825293359523586849932749482 = ((550063334528049305474300730952148730298745814741443152544110601876865462929 : Nat) : Fp) := by
    rw [show (825293359523586849932749482 : Nat) = 412646679761793424966374741 * 2 + 0 from rfl, pow_add, pow_mul, h88, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h90 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1650586719047173699865498965 = ((14281131569099385515079691036575606835608394300100869016436288659099784740260 : Nat) : Fp) := by
    rw [show (1650586719047173699865498965 : Nat) = 825293359523586849932749482 * 2 + 1 from rfl, pow_add, pow_mul, h89, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h91 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3301173438094347399730997930 = ((14993685592828940183755108071085350984882568881645395913663784404978663550743 : Nat) : Fp) := by
    rw [show (3301173438094347399730997930 : Nat) = 1650586719047173699865498965 * 2 + 0 from rfl, pow_add, pow_mul, h90, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h92 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 6602346876188694799461995861 = ((290688021759326142091774966080283249213729284597325317567672096797586550769 : Nat) : Fp) := by
    rw [show (6602346876188694799461995861 : Nat) = 3301173438094347399730997930 * 2 + 1 from rfl, pow_add, pow_mul, h91, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h93 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 13204693752377389598923991722 = ((48883022263437020073640603710263996923448302710736285166638683650261088496241 : Nat) : Fp) := by
    rw [show (13204693752377389598923991722 : Nat) = 6602346876188694799461995861 * 2 + 0 from rfl, pow_add, pow_mul, h92, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h94 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 26409387504754779197847983445 = ((115005640896614450226855344383277526835517626387016905764686321999960976644126 : Nat) : Fp) := by
    rw [show (26409387504754779197847983445 : Nat) = 13204693752377389598923991722 * 2 + 1 from rfl, pow_add, pow_mul, h93, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h95 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 52818775009509558395695966890 = ((84640006329275225471412150425949081727759455521127057108645724701379152378646 : Nat) : Fp) := by
    rw [show (52818775009509558395695966890 : Nat) = 26409387504754779197847983445 * 2 + 0 from rfl, pow_add, pow_mul, h94, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h96 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 105637550019019116791391933781 = ((11197371745042030015646707917453437979489421627830957077618240785604674309855 : Nat) : Fp) := by
    rw [show (105637550019019116791391933781 : Nat) = 52818775009509558395695966890 * 2 + 1 from rfl, pow_add, pow_mul, h95, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h97 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 211275100038038233582783867562 = ((41920215069285921727067143122242626322678798368078710574736793106844683528158 : Nat) : Fp) := by
    rw [show (211275100038038233582783867562 : Nat) = 105637550019019116791391933781 * 2 + 0 from rfl, pow_add, pow_mul, h96, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h98 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 422550200076076467165567735125 = ((26614492252404642939385105139536281308564471070384388736453068572262986168535 : Nat) : Fp) := by
    rw [show (422550200076076467165567735125 : Nat) = 211275100038038233582783867562 * 2 + 1 from rfl, pow_add, pow_mul, h97, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h99 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 845100400152152934331135470250 = ((108082061671180633206629724164853790953242644435429040110840266123470518787454 : Nat) : Fp) := by
    rw [show (845100400152152934331135470250 : Nat) = 422550200076076467165567735125 * 2 + 0 from rfl, pow_add, pow_mul, h98, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h100 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1690200800304305868662270940501 = ((33542493970797314685364117540414414548544711343259378934755815920660572099802 : Nat) : Fp) := by
    rw [show (1690200800304305868662270940501 : Nat) = 845100400152152934331135470250 * 2 + 1 from rfl, pow_add, pow_mul, h99, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h101 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3380401600608611737324541881002 = ((20940459371718519869340610013645750045802309543680221150848690612683741065878 : Nat) : Fp) := by
    rw [show (3380401600608611737324541881002 : Nat) = 1690200800304305868662270940501 * 2 + 0 from rfl, pow_add, pow_mul, h100, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h102 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 6760803201217223474649083762005 = ((41048205128990890240766392225034434396602013877431445026938575038956056468472 : Nat) : Fp) := by
    rw [show (6760803201217223474649083762005 : Nat) = 3380401600608611737324541881002 * 2 + 1 from rfl, pow_add, pow_mul, h101, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h103 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 13521606402434446949298167524010 = ((104168503235771234091070672623441175398732407346897755569879156830709345698590 : Nat) : Fp) := by
    rw [show (13521606402434446949298167524010 : Nat) = 6760803201217223474649083762005 * 2 + 0 from rfl, pow_add, pow_mul, h102, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h104 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 27043212804868893898596335048021 = ((61963843860992186505931699231520121374231068404051591651365646435263108254266 : Nat) : Fp) := by
    rw [show (27043212804868893898596335048021 : Nat) = 13521606402434446949298167524010 * 2 + 1 from rfl, pow_add, pow_mul, h103, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h105 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 54086425609737787797192670096042 = ((32564908920831625350634667010459209849362748035902349907849005011229457433957 : Nat) : Fp) := by
    rw [show (54086425609737787797192670096042 : Nat) = 27043212804868893898596335048021 * 2 + 0 from rfl, pow_add, pow_mul, h104, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h106 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 108172851219475575594385340192085 = ((9522328195972047364923667785761616274070070897360377840685532945966660724654 : Nat) : Fp) := by
    rw [show (108172851219475575594385340192085 : Nat) = 54086425609737787797192670096042 * 2 + 1 from rfl, pow_add, pow_mul, h105, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h107 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 216345702438951151188770680384170 = ((82534086113414329682985725419380956781306943824724345309793160537432881231589 : Nat) : Fp) := by
    rw [show (216345702438951151188770680384170 : Nat) = 108172851219475575594385340192085 * 2 + 0 from rfl, pow_add, pow_mul, h106, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h108 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 432691404877902302377541360768341 = ((24621490557286332988899774029617551333450204832249209522047647451279394283185 : Nat) : Fp) := by
    rw [show (432691404877902302377541360768341 : Nat) = 216345702438951151188770680384170 * 2 + 1 from rfl, pow_add, pow_mul, h107, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h109 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 865382809755804604755082721536682 = ((27082922526434902397978725105952427321720099911785591037192037378025490176107 : Nat) : Fp) := by
    rw [show (865382809755804604755082721536682 : Nat) = 432691404877902302377541360768341 * 2 + 0 from rfl, pow_add, pow_mul, h108, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h110 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1730765619511609209510165443073365 = ((45560776003517383098353916070251515849629942560105719307315184591785661185461 : Nat) : Fp) := by
    rw [show (1730765619511609209510165443073365 : Nat) = 865382809755804604755082721536682 * 2 + 1 from rfl, pow_add, pow_mul, h109, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h111 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3461531239023218419020330886146730 = ((70599706375645959209257353271105055400441236785686811931245315098257208992830 : Nat) : Fp) := by
    rw [show (3461531239023218419020330886146730 : Nat) = 1730765619511609209510165443073365 * 2 + 0 from rfl, pow_add, pow_mul, h110, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h112 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 6923062478046436838040661772293461 = ((27418458744094674912521173775768233369626887803745666907333042488779614199491 : Nat) : Fp) := by
    rw [show (6923062478046436838040661772293461 : Nat) = 3461531239023218419020330886146730 * 2 + 1 from rfl, pow_add, pow_mul, h111, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h113 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 13846124956092873676081323544586922 = ((28809592468768867445241427692392117304752426605640637591254658739605754868386 : Nat) : Fp) := by
    rw [show (13846124956092873676081323544586922 : Nat) = 6923062478046436838040661772293461 * 2 + 0 from rfl, pow_add, pow_mul, h112, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h114 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 27692249912185747352162647089173845 = ((95889425314020676571545051685917987232087496739543569391041353113175091153791 : Nat) : Fp) := by
    rw [show (27692249912185747352162647089173845 : Nat) = 13846124956092873676081323544586922 * 2 + 1 from rfl, pow_add, pow_mul, h113, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h115 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 55384499824371494704325294178347690 = ((54748927645115882258045891438182958182688618709661654938735397158653152212220 : Nat) : Fp) := by
    rw [show (55384499824371494704325294178347690 : Nat) = 27692249912185747352162647089173845 * 2 + 0 from rfl, pow_add, pow_mul, h114, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h116 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 110768999648742989408650588356695381 = ((53040186025180604921584301355349518155986200427452578432288669216682803780446 : Nat) : Fp) := by
    rw [show (110768999648742989408650588356695381 : Nat) = 55384499824371494704325294178347690 * 2 + 1 from rfl, pow_add, pow_mul, h115, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h117 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 221537999297485978817301176713390762 = ((37305459626504707996167055577362779816020823913683305070292854261098646149751 : Nat) : Fp) := by
    rw [show (221537999297485978817301176713390762 : Nat) = 110768999648742989408650588356695381 * 2 + 0 from rfl, pow_add, pow_mul, h116, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h118 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 443075998594971957634602353426781525 = ((36485947307302379049996435877114892423684181397392300200382513498523460988370 : Nat) : Fp) := by
    rw [show (443075998594971957634602353426781525 : Nat) = 221537999297485978817301176713390762 * 2 + 1 from rfl, pow_add, pow_mul, h117, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h119 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 886151997189943915269204706853563050 = ((71013954711409468511419299414945954043602821310966129742837982661895117391803 : Nat) : Fp) := by
    rw [show (886151997189943915269204706853563050 : Nat) = 443075998594971957634602353426781525 * 2 + 0 from rfl, pow_add, pow_mul, h118, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h120 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1772303994379887830538409413707126101 = ((41351144109339023380905453714367247758872256755949529518965210956099431415057 : Nat) : Fp) := by
    rw [show (1772303994379887830538409413707126101 : Nat) = 886151997189943915269204706853563050 * 2 + 1 from rfl, pow_add, pow_mul, h119, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h121 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3544607988759775661076818827414252202 = ((2272027923591210979224239241343326390313126782280832902571918757880966015564 : Nat) : Fp) := by
    rw [show (3544607988759775661076818827414252202 : Nat) = 1772303994379887830538409413707126101 * 2 + 0 from rfl, pow_add, pow_mul, h120, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h122 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 7089215977519551322153637654828504405 = ((53744956196199221870949503337604670999652609094596506848063870755763228404474 : Nat) : Fp) := by
    rw [show (7089215977519551322153637654828504405 : Nat) = 3544607988759775661076818827414252202 * 2 + 1 from rfl, pow_add, pow_mul, h121, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h123 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 14178431955039102644307275309657008810 = ((35952703341953888321856868750276804216698496589704149780514454482762983255743 : Nat) : Fp) := by
    rw [show (14178431955039102644307275309657008810 : Nat) = 7089215977519551322153637654828504405 * 2 + 0 from rfl, pow_add, pow_mul, h122, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h124 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 28356863910078205288614550619314017621 = ((62587298922917329011715021451397859602737161547398191872162109269374224854794 : Nat) : Fp) := by
    rw [show (28356863910078205288614550619314017621 : Nat) = 14178431955039102644307275309657008810 * 2 + 1 from rfl, pow_add, pow_mul, h123, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h125 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 56713727820156410577229101238628035242 = ((107191021377031068639704768314789668771281152002338196860852604765517733332878 : Nat) : Fp) := by
    rw [show (56713727820156410577229101238628035242 : Nat) = 28356863910078205288614550619314017621 * 2 + 0 from rfl, pow_add, pow_mul, h124, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h126 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 113427455640312821154458202477256070485 = ((6869199659010212688756057649385147329507442878855152801775746338584334652139 : Nat) : Fp) := by
    rw [show (113427455640312821154458202477256070485 : Nat) = 56713727820156410577229101238628035242 * 2 + 1 from rfl, pow_add, pow_mul, h125, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h127 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 226854911280625642308916404954512140970 = ((54483357038393815160253239932889160087931558429354006815121714057513501894486 : Nat) : Fp) := by
    rw [show (226854911280625642308916404954512140970 : Nat) = 113427455640312821154458202477256070485 * 2 + 0 from rfl, pow_add, pow_mul, h126, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h128 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 453709822561251284617832809909024281941 = ((76135470293510877172165853965189548319641802926445514480851867867496932640338 : Nat) : Fp) := by
    rw [show (453709822561251284617832809909024281941 : Nat) = 226854911280625642308916404954512140970 * 2 + 1 from rfl, pow_add, pow_mul, h127, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h129 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 907419645122502569235665619818048563882 = ((76804524280316274113098701929627705678710553739382024913303811920332597960036 : Nat) : Fp) := by
    rw [show (907419645122502569235665619818048563882 : Nat) = 453709822561251284617832809909024281941 * 2 + 0 from rfl, pow_add, pow_mul, h128, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h130 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1814839290245005138471331239636097127765 = ((48888548795645040451031257011657771272477574788464354579023507125124810377456 : Nat) : Fp) := by
    rw [show (1814839290245005138471331239636097127765 : Nat) = 907419645122502569235665619818048563882 * 2 + 1 from rfl, pow_add, pow_mul, h129, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h131 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3629678580490010276942662479272194255530 = ((21087251873606971364007228793177358291454416192763879037053352805105664674838 : Nat) : Fp) := by
    rw [show (3629678580490010276942662479272194255530 : Nat) = 1814839290245005138471331239636097127765 * 2 + 0 from rfl, pow_add, pow_mul, h130, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h132 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 7259357160980020553885324958544388511061 = ((108799946428467352953229865712710472630564372748562283693298174856954643441031 : Nat) : Fp) := by
    rw [show (7259357160980020553885324958544388511061 : Nat) = 3629678580490010276942662479272194255530 * 2 + 1 from rfl, pow_add, pow_mul, h131, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h133 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 14518714321960041107770649917088777022122 = ((36393860264704856578973794199491090097449141794838427096791414865483009833431 : Nat) : Fp) := by
    rw [show (14518714321960041107770649917088777022122 : Nat) = 7259357160980020553885324958544388511061 * 2 + 0 from rfl, pow_add, pow_mul, h132, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h134 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 29037428643920082215541299834177554044245 = ((94838087216236713867395319138082336709752820789495290341135827833225169089212 : Nat) : Fp) := by
    rw [show (29037428643920082215541299834177554044245 : Nat) = 14518714321960041107770649917088777022122 * 2 + 1 from rfl, pow_add, pow_mul, h133, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h135 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 58074857287840164431082599668355108088490 = ((68736847097148343803659342534993881876485028603229304254988234166524422928177 : Nat) : Fp) := by
    rw [show (58074857287840164431082599668355108088490 : Nat) = 29037428643920082215541299834177554044245 * 2 + 0 from rfl, pow_add, pow_mul, h134, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h136 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 116149714575680328862165199336710216176981 = ((100773856967381927163459303459715767076958839031855812936746900428560407362101 : Nat) : Fp) := by
    rw [show (116149714575680328862165199336710216176981 : Nat) = 58074857287840164431082599668355108088490 * 2 + 1 from rfl, pow_add, pow_mul, h135, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h137 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 232299429151360657724330398673420432353962 = ((62799089563126392353426359649915826547394516371987351399318011977604567596754 : Nat) : Fp) := by
    rw [show (232299429151360657724330398673420432353962 : Nat) = 116149714575680328862165199336710216176981 * 2 + 0 from rfl, pow_add, pow_mul, h136, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h138 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 464598858302721315448660797346840864707925 = ((7057215481499360742801455009525622482791398742948541878878298260958613312746 : Nat) : Fp) := by
    rw [show (464598858302721315448660797346840864707925 : Nat) = 232299429151360657724330398673420432353962 * 2 + 1 from rfl, pow_add, pow_mul, h137, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h139 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 929197716605442630897321594693681729415850 = ((34618392853918106716507644447139930162063293309130816420099381908647796747863 : Nat) : Fp) := by
    rw [show (929197716605442630897321594693681729415850 : Nat) = 464598858302721315448660797346840864707925 * 2 + 0 from rfl, pow_add, pow_mul, h138, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h140 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1858395433210885261794643189387363458831701 = ((44924186429456017448807038963625547915636554810373259710990280953602289257912 : Nat) : Fp) := by
    rw [show (1858395433210885261794643189387363458831701 : Nat) = 929197716605442630897321594693681729415850 * 2 + 1 from rfl, pow_add, pow_mul, h139, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h141 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3716790866421770523589286378774726917663402 = ((70426463516621331026916903048894611182390395498774157590478963199492999525333 : Nat) : Fp) := by
    rw [show (3716790866421770523589286378774726917663402 : Nat) = 1858395433210885261794643189387363458831701 * 2 + 0 from rfl, pow_add, pow_mul, h140, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h142 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 7433581732843541047178572757549453835326805 = ((87632687556460508422906120876731553544825698377794533362218504364792996136592 : Nat) : Fp) := by
    rw [show (7433581732843541047178572757549453835326805 : Nat) = 3716790866421770523589286378774726917663402 * 2 + 1 from rfl, pow_add, pow_mul, h141, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h143 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 14867163465687082094357145515098907670653610 = ((16404779462004460048636370103417842325539313766650706669931643808380510933107 : Nat) : Fp) := by
    rw [show (14867163465687082094357145515098907670653610 : Nat) = 7433581732843541047178572757549453835326805 * 2 + 0 from rfl, pow_add, pow_mul, h142, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h144 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 29734326931374164188714291030197815341307221 = ((44449688001421166400665182045279162209317684191124799069696287408082569709109 : Nat) : Fp) := by
    rw [show (29734326931374164188714291030197815341307221 : Nat) = 14867163465687082094357145515098907670653610 * 2 + 1 from rfl, pow_add, pow_mul, h143, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h145 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 59468653862748328377428582060395630682614442 = ((30563714579994482523175988397361939302314261245030651243352978405731677720882 : Nat) : Fp) := by
    rw [show (59468653862748328377428582060395630682614442 : Nat) = 29734326931374164188714291030197815341307221 * 2 + 0 from rfl, pow_add, pow_mul, h144, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h146 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 118937307725496656754857164120791261365228885 = ((75360349469256181187301358598159711512667399865016000150115938490910374653833 : Nat) : Fp) := by
    rw [show (118937307725496656754857164120791261365228885 : Nat) = 59468653862748328377428582060395630682614442 * 2 + 1 from rfl, pow_add, pow_mul, h145, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h147 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 237874615450993313509714328241582522730457770 = ((113542226404550688622607577902572428149383434324370396278626143156017221481585 : Nat) : Fp) := by
    rw [show (237874615450993313509714328241582522730457770 : Nat) = 118937307725496656754857164120791261365228885 * 2 + 0 from rfl, pow_add, pow_mul, h146, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h148 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 475749230901986627019428656483165045460915541 = ((60899794547400275914951553979302161322968130509602768240112597659564617537714 : Nat) : Fp) := by
    rw [show (475749230901986627019428656483165045460915541 : Nat) = 237874615450993313509714328241582522730457770 * 2 + 1 from rfl, pow_add, pow_mul, h147, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h149 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 951498461803973254038857312966330090921831082 = ((66320495699608858931358487788748648061703517608123390770123355669319144791630 : Nat) : Fp) := by
    rw [show (951498461803973254038857312966330090921831082 : Nat) = 475749230901986627019428656483165045460915541 * 2 + 0 from rfl, pow_add, pow_mul, h148, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h150 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1902996923607946508077714625932660181843662165 = ((106231257018553234568654883066350600883554951188792100657813804760554775119489 : Nat) : Fp) := by
    rw [show (1902996923607946508077714625932660181843662165 : Nat) = 951498461803973254038857312966330090921831082 * 2 + 1 from rfl, pow_add, pow_mul, h149, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h151 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3805993847215893016155429251865320363687324330 = ((4713518186954206388714244490935135103992822974838680677135137950968302479074 : Nat) : Fp) := by
    rw [show (3805993847215893016155429251865320363687324330 : Nat) = 1902996923607946508077714625932660181843662165 * 2 + 0 from rfl, pow_add, pow_mul, h150, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h152 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 7611987694431786032310858503730640727374648661 = ((84612945976856190118943183147997415976083868220645026458718256564902600997576 : Nat) : Fp) := by
    rw [show (7611987694431786032310858503730640727374648661 : Nat) = 3805993847215893016155429251865320363687324330 * 2 + 1 from rfl, pow_add, pow_mul, h151, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h153 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 15223975388863572064621717007461281454749297322 = ((115109932429464443046148764948985069703061418747623022900891792616113993515916 : Nat) : Fp) := by
    rw [show (15223975388863572064621717007461281454749297322 : Nat) = 7611987694431786032310858503730640727374648661 * 2 + 0 from rfl, pow_add, pow_mul, h152, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h154 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 30447950777727144129243434014922562909498594645 = ((44928425866289567449892298596779646866085886992175347479460095209790047244314 : Nat) : Fp) := by
    rw [show (30447950777727144129243434014922562909498594645 : Nat) = 15223975388863572064621717007461281454749297322 * 2 + 1 from rfl, pow_add, pow_mul, h153, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h155 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 60895901555454288258486868029845125818997189290 = ((18076938912679138970022450901967808010661276639992019336902850101581481720482 : Nat) : Fp) := by
    rw [show (60895901555454288258486868029845125818997189290 : Nat) = 30447950777727144129243434014922562909498594645 * 2 + 0 from rfl, pow_add, pow_mul, h154, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h156 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 121791803110908576516973736059690251637994378581 = ((32564882423292773219050785580368991358436411822357218972274933226105234033930 : Nat) : Fp) := by
    rw [show (121791803110908576516973736059690251637994378581 : Nat) = 60895901555454288258486868029845125818997189290 * 2 + 1 from rfl, pow_add, pow_mul, h155, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h157 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 243583606221817153033947472119380503275988757162 = ((32552367010794342621130455638503334697097512701776238637477919219310317942797 : Nat) : Fp) := by
    rw [show (243583606221817153033947472119380503275988757162 : Nat) = 121791803110908576516973736059690251637994378581 * 2 + 0 from rfl, pow_add, pow_mul, h156, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h158 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 487167212443634306067894944238761006551977514325 = ((102929209122444587827777699026944410683899678022352825493067503714745504057159 : Nat) : Fp) := by
    rw [show (487167212443634306067894944238761006551977514325 : Nat) = 243583606221817153033947472119380503275988757162 * 2 + 1 from rfl, pow_add, pow_mul, h157, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h159 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 974334424887268612135789888477522013103955028650 = ((86526498128133317626630141702813837074367111932637409868187941854288427591568 : Nat) : Fp) := by
    rw [show (974334424887268612135789888477522013103955028650 : Nat) = 487167212443634306067894944238761006551977514325 * 2 + 0 from rfl, pow_add, pow_mul, h158, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h160 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1948668849774537224271579776955044026207910057301 = ((88361233885819673367588753378636896569249530588595265310110137596440966353511 : Nat) : Fp) := by
    rw [show (1948668849774537224271579776955044026207910057301 : Nat) = 974334424887268612135789888477522013103955028650 * 2 + 1 from rfl, pow_add, pow_mul, h159, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h161 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3897337699549074448543159553910088052415820114602 = ((97295057363833635958625727837300621710348386114506051145619388231245061104307 : Nat) : Fp) := by
    rw [show (3897337699549074448543159553910088052415820114602 : Nat) = 1948668849774537224271579776955044026207910057301 * 2 + 0 from rfl, pow_add, pow_mul, h160, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h162 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 7794675399098148897086319107820176104831640229205 = ((36663078590024217204418750652753931757818634217088178956414007872110377736052 : Nat) : Fp) := by
    rw [show (7794675399098148897086319107820176104831640229205 : Nat) = 3897337699549074448543159553910088052415820114602 * 2 + 1 from rfl, pow_add, pow_mul, h161, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h163 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 15589350798196297794172638215640352209663280458410 = ((31202990417790643235432813288641803388915616814742264563088358317007829710066 : Nat) : Fp) := by
    rw [show (15589350798196297794172638215640352209663280458410 : Nat) = 7794675399098148897086319107820176104831640229205 * 2 + 0 from rfl, pow_add, pow_mul, h162, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h164 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 31178701596392595588345276431280704419326560916821 = ((105444524707405465121336077948537574699913001511158514634884314399116410936387 : Nat) : Fp) := by
    rw [show (31178701596392595588345276431280704419326560916821 : Nat) = 15589350798196297794172638215640352209663280458410 * 2 + 1 from rfl, pow_add, pow_mul, h163, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h165 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 62357403192785191176690552862561408838653121833642 = ((11884417450457523770287002322943211174420363265326718726939123521017453812754 : Nat) : Fp) := by
    rw [show (62357403192785191176690552862561408838653121833642 : Nat) = 31178701596392595588345276431280704419326560916821 * 2 + 0 from rfl, pow_add, pow_mul, h164, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h166 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 124714806385570382353381105725122817677306243667285 = ((100148799449159930653291217019635587192652592626456786484600231356308420076820 : Nat) : Fp) := by
    rw [show (124714806385570382353381105725122817677306243667285 : Nat) = 62357403192785191176690552862561408838653121833642 * 2 + 1 from rfl, pow_add, pow_mul, h165, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h167 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 249429612771140764706762211450245635354612487334570 = ((100556213281901405356619926930785698037693303774351613818917765167590532018720 : Nat) : Fp) := by
    rw [show (249429612771140764706762211450245635354612487334570 : Nat) = 124714806385570382353381105725122817677306243667285 * 2 + 0 from rfl, pow_add, pow_mul, h166, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h168 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 498859225542281529413524422900491270709224974669141 = ((84670543276892736877644224180034259415730239159161747858160120373050077725398 : Nat) : Fp) := by
    rw [show (498859225542281529413524422900491270709224974669141 : Nat) = 249429612771140764706762211450245635354612487334570 * 2 + 1 from rfl, pow_add, pow_mul, h167, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h169 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 997718451084563058827048845800982541418449949338282 = ((12063297397266672965241161667724755939078649295629608397460352714230688858640 : Nat) : Fp) := by
    rw [show (997718451084563058827048845800982541418449949338282 : Nat) = 498859225542281529413524422900491270709224974669141 * 2 + 0 from rfl, pow_add, pow_mul, h168, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h170 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1995436902169126117654097691601965082836899898676565 = ((108604885799337313853841518672026076771001180710430763455545159680535687891409 : Nat) : Fp) := by
    rw [show (1995436902169126117654097691601965082836899898676565 : Nat) = 997718451084563058827048845800982541418449949338282 * 2 + 1 from rfl, pow_add, pow_mul, h169, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h171 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 3990873804338252235308195383203930165673799797353130 = ((42639796339947200859994826751723476010210938070819166578039597467986569278106 : Nat) : Fp) := by
    rw [show (3990873804338252235308195383203930165673799797353130 : Nat) = 1995436902169126117654097691601965082836899898676565 * 2 + 0 from rfl, pow_add, pow_mul, h170, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h172 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 7981747608676504470616390766407860331347599594706261 = ((49534283133873617341354642197833456846602332034498618911393547561416892583522 : Nat) : Fp) := by
    rw [show (7981747608676504470616390766407860331347599594706261 : Nat) = 3990873804338252235308195383203930165673799797353130 * 2 + 1 from rfl, pow_add, pow_mul, h171, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h173 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 15963495217353008941232781532815720662695199189412522 = ((110046373041040105685241540769040406061660660669158436787314938832525932764838 : Nat) : Fp) := by
    rw [show (15963495217353008941232781532815720662695199189412522 : Nat) = 7981747608676504470616390766407860331347599594706261 * 2 + 0 from rfl, pow_add, pow_mul, h172, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h174 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 31926990434706017882465563065631441325390398378825045 = ((98129362582552938839486619212323042547544460398965400087095304384229373757495 : Nat) : Fp) := by
    rw [show (31926990434706017882465563065631441325390398378825045 : Nat) = 15963495217353008941232781532815720662695199189412522 * 2 + 1 from rfl, pow_add, pow_mul, h173, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h175 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 63853980869412035764931126131262882650780796757650090 = ((66127419070458723933494103035893381332902000753136946168216864463193008412678 : Nat) : Fp) := by
    rw [show (63853980869412035764931126131262882650780796757650090 : Nat) = 31926990434706017882465563065631441325390398378825045 * 2 + 0 from rfl, pow_add, pow_mul, h174, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h176 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 127707961738824071529862252262525765301561593515300181 = ((65130340515658333760836103208536111564265659375731864415681736231222325362609 : Nat) : Fp) := by
    rw [show (127707961738824071529862252262525765301561593515300181 : Nat) = 63853980869412035764931126131262882650780796757650090 * 2 + 1 from rfl, pow_add, pow_mul, h175, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h177 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 255415923477648143059724504525051530603123187030600362 = ((87280494561911244935264608446634960929635147117022267521373405193578625129062 : Nat) : Fp) := by
    rw [show (255415923477648143059724504525051530603123187030600362 : Nat) = 127707961738824071529862252262525765301561593515300181 * 2 + 0 from rfl, pow_add, pow_mul, h176, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h178 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 510831846955296286119449009050103061206246374061200725 = ((55040005587495510643040373153236710054936303898362800615361167187449839471082 : Nat) : Fp) := by
    rw [show (510831846955296286119449009050103061206246374061200725 : Nat) = 255415923477648143059724504525051530603123187030600362 * 2 + 1 from rfl, pow_add, pow_mul, h177, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h179 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1021663693910592572238898018100206122412492748122401450 = ((84006688438946083716829264011931749034497470460454721854088340049671270108866 : Nat) : Fp) := by
    rw [show (1021663693910592572238898018100206122412492748122401450 : Nat) = 510831846955296286119449009050103061206246374061200725 * 2 + 0 from rfl, pow_add, pow_mul, h178, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h180 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2043327387821185144477796036200412244824985496244802901 = ((81331280572657032068972283043588092110319645295202103181809423810210406953622 : Nat) : Fp) := by
    rw [show (2043327387821185144477796036200412244824985496244802901 : Nat) = 1021663693910592572238898018100206122412492748122401450 * 2 + 1 from rfl, pow_add, pow_mul, h179, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h181 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 4086654775642370288955592072400824489649970992489605802 = ((60366262703844161198300037241384471858893526474605100850588313584662496862368 : Nat) : Fp) := by
    rw [show (4086654775642370288955592072400824489649970992489605802 : Nat) = 2043327387821185144477796036200412244824985496244802901 * 2 + 0 from rfl, pow_add, pow_mul, h180, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h182 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 8173309551284740577911184144801648979299941984979211605 = ((85555566816181871814206736529093600005372908877319231312945560608701842681217 : Nat) : Fp) := by
    rw [show (8173309551284740577911184144801648979299941984979211605 : Nat) = 4086654775642370288955592072400824489649970992489605802 * 2 + 1 from rfl, pow_add, pow_mul, h181, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h183 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 16346619102569481155822368289603297958599883969958423210 = ((97442264923044366100228621716191438771295332692678317247966910575260372432133 : Nat) : Fp) := by
    rw [show (16346619102569481155822368289603297958599883969958423210 : Nat) = 8173309551284740577911184144801648979299941984979211605 * 2 + 0 from rfl, pow_add, pow_mul, h182, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h184 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 32693238205138962311644736579206595917199767939916846421 = ((7545245492087383711941544220651356235233540515459593688798843069394965352717 : Nat) : Fp) := by
    rw [show (32693238205138962311644736579206595917199767939916846421 : Nat) = 16346619102569481155822368289603297958599883969958423210 * 2 + 1 from rfl, pow_add, pow_mul, h183, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h185 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 65386476410277924623289473158413191834399535879833692842 = ((50551371773477419817527402587000496480142510001407602590144314071685715625691 : Nat) : Fp) := by
    rw [show (65386476410277924623289473158413191834399535879833692842 : Nat) = 32693238205138962311644736579206595917199767939916846421 * 2 + 0 from rfl, pow_add, pow_mul, h184, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h186 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 130772952820555849246578946316826383668799071759667385685 = ((81227726352914418543316156698155303325868822050589738238485058660348011846574 : Nat) : Fp) := by
    rw [show (130772952820555849246578946316826383668799071759667385685 : Nat) = 65386476410277924623289473158413191834399535879833692842 * 2 + 1 from rfl, pow_add, pow_mul, h185, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h187 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 261545905641111698493157892633652767337598143519334771370 = ((24632732923219529134154976588509848579822841936798531804867943126285647754008 : Nat) : Fp) := by
    rw [show (261545905641111698493157892633652767337598143519334771370 : Nat) = 130772952820555849246578946316826383668799071759667385685 * 2 + 0 from rfl, pow_add, pow_mul, h186, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h188 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 523091811282223396986315785267305534675196287038669542741 = ((81936307483096720214623910993074046519837873897449712522251708310252049337959 : Nat) : Fp) := by
    rw [show (523091811282223396986315785267305534675196287038669542741 : Nat) = 261545905641111698493157892633652767337598143519334771370 * 2 + 1 from rfl, pow_add, pow_mul, h187, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h189 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1046183622564446793972631570534611069350392574077339085482 = ((96932837235087638730128035762894017843515115406816208020551824175746664223157 : Nat) : Fp) := by
    rw [show (1046183622564446793972631570534611069350392574077339085482 : Nat) = 523091811282223396986315785267305534675196287038669542741 * 2 + 0 from rfl, pow_add, pow_mul, h188, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h190 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2092367245128893587945263141069222138700785148154678170965 = ((16491529010479469898461586310368126639953175505908525949875657922098520631396 : Nat) : Fp) := by
    rw [show (2092367245128893587945263141069222138700785148154678170965 : Nat) = 1046183622564446793972631570534611069350392574077339085482 * 2 + 1 from rfl, pow_add, pow_mul, h189, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h191 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 4184734490257787175890526282138444277401570296309356341930 = ((81138277857917790009130749792060046992338312805118569845547311026363257725179 : Nat) : Fp) := by
    rw [show (4184734490257787175890526282138444277401570296309356341930 : Nat) = 2092367245128893587945263141069222138700785148154678170965 * 2 + 0 from rfl, pow_add, pow_mul, h190, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h192 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 8369468980515574351781052564276888554803140592618712683861 = ((44095710361525749177769421922611999237708155871807900305397634878608235975731 : Nat) : Fp) := by
    rw [show (8369468980515574351781052564276888554803140592618712683861 : Nat) = 4184734490257787175890526282138444277401570296309356341930 * 2 + 1 from rfl, pow_add, pow_mul, h191, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h193 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 16738937961031148703562105128553777109606281185237425367722 = ((66780749579750956991657381445018314603354909259725027036937898207328337789174 : Nat) : Fp) := by
    rw [show (16738937961031148703562105128553777109606281185237425367722 : Nat) = 8369468980515574351781052564276888554803140592618712683861 * 2 + 0 from rfl, pow_add, pow_mul, h192, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h194 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 33477875922062297407124210257107554219212562370474850735445 = ((50563902709330004076907815045033997930720086294604002539026034808765292383630 : Nat) : Fp) := by
    rw [show (33477875922062297407124210257107554219212562370474850735445 : Nat) = 16738937961031148703562105128553777109606281185237425367722 * 2 + 1 from rfl, pow_add, pow_mul, h193, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h195 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 66955751844124594814248420514215108438425124740949701470890 = ((14957638267340832524584291279090351014419402205683968363206225868240439900333 : Nat) : Fp) := by
    rw [show (66955751844124594814248420514215108438425124740949701470890 : Nat) = 33477875922062297407124210257107554219212562370474850735445 * 2 + 0 from rfl, pow_add, pow_mul, h194, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h196 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 133911503688249189628496841028430216876850249481899402941781 = ((77605081090370714447325538934482125977762222292783202406836507662492662052695 : Nat) : Fp) := by
    rw [show (133911503688249189628496841028430216876850249481899402941781 : Nat) = 66955751844124594814248420514215108438425124740949701470890 * 2 + 1 from rfl, pow_add, pow_mul, h195, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h197 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 267823007376498379256993682056860433753700498963798805883562 = ((71558377608622861846853183637022701189597744193635015922221660589987339541253 : Nat) : Fp) := by
    rw [show (267823007376498379256993682056860433753700498963798805883562 : Nat) = 133911503688249189628496841028430216876850249481899402941781 * 2 + 0 from rfl, pow_add, pow_mul, h196, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h198 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 535646014752996758513987364113720867507400997927597611767125 = ((26562340324080305406582353486340154202052485146169211785405477139222043470231 : Nat) : Fp) := by
    rw [show (535646014752996758513987364113720867507400997927597611767125 : Nat) = 267823007376498379256993682056860433753700498963798805883562 * 2 + 1 from rfl, pow_add, pow_mul, h197, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h199 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1071292029505993517027974728227441735014801995855195223534250 = ((32398553090938844410539515942181354799069850286953113461965676316635780300181 : Nat) : Fp) := by
    rw [show (1071292029505993517027974728227441735014801995855195223534250 : Nat) = 535646014752996758513987364113720867507400997927597611767125 * 2 + 0 from rfl, pow_add, pow_mul, h198, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h200 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2142584059011987034055949456454883470029603991710390447068501 = ((10354059515440905839921568960835405153679408473881474466608563083939355987315 : Nat) : Fp) := by
    rw [show (2142584059011987034055949456454883470029603991710390447068501 : Nat) = 1071292029505993517027974728227441735014801995855195223534250 * 2 + 1 from rfl, pow_add, pow_mul, h199, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h201 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 4285168118023974068111898912909766940059207983420780894137002 = ((27290498843891043091898394866958579276463611983721779323270385999825884953623 : Nat) : Fp) := by
    rw [show (4285168118023974068111898912909766940059207983420780894137002 : Nat) = 2142584059011987034055949456454883470029603991710390447068501 * 2 + 0 from rfl, pow_add, pow_mul, h200, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h202 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 8570336236047948136223797825819533880118415966841561788274005 = ((76738304037029016215830559201082745698579772019905334074256324742196563626309 : Nat) : Fp) := by
    rw [show (8570336236047948136223797825819533880118415966841561788274005 : Nat) = 4285168118023974068111898912909766940059207983420780894137002 * 2 + 1 from rfl, pow_add, pow_mul, h201, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h203 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 17140672472095896272447595651639067760236831933683123576548010 = ((62720256307150072992340190508170823678542083920663867449474328766212241782989 : Nat) : Fp) := by
    rw [show (17140672472095896272447595651639067760236831933683123576548010 : Nat) = 8570336236047948136223797825819533880118415966841561788274005 * 2 + 0 from rfl, pow_add, pow_mul, h202, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h204 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 34281344944191792544895191303278135520473663867366247153096021 = ((34067231008761597245431691133290430602022458767755857416883645197403256712690 : Nat) : Fp) := by
    rw [show (34281344944191792544895191303278135520473663867366247153096021 : Nat) = 17140672472095896272447595651639067760236831933683123576548010 * 2 + 1 from rfl, pow_add, pow_mul, h203, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h205 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 68562689888383585089790382606556271040947327734732494306192042 = ((55742143337033258325325824284345113329299925525974415391970522722962117690679 : Nat) : Fp) := by
    rw [show (68562689888383585089790382606556271040947327734732494306192042 : Nat) = 34281344944191792544895191303278135520473663867366247153096021 * 2 + 0 from rfl, pow_add, pow_mul, h204, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h206 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 137125379776767170179580765213112542081894655469464988612384085 = ((2491073597398498883933974497968121351266788702932384893726738736377813043527 : Nat) : Fp) := by
    rw [show (137125379776767170179580765213112542081894655469464988612384085 : Nat) = 68562689888383585089790382606556271040947327734732494306192042 * 2 + 1 from rfl, pow_add, pow_mul, h205, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h207 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 274250759553534340359161530426225084163789310938929977224768170 = ((106288369319057783908781584461272290922343276320876160071354438992126607988924 : Nat) : Fp) := by
    rw [show (274250759553534340359161530426225084163789310938929977224768170 : Nat) = 137125379776767170179580765213112542081894655469464988612384085 * 2 + 0 from rfl, pow_add, pow_mul, h206, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h208 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 548501519107068680718323060852450168327578621877859954449536341 = ((103850233365223076479532141708173946544957758827039214516269064452153113753154 : Nat) : Fp) := by
    rw [show (548501519107068680718323060852450168327578621877859954449536341 : Nat) = 274250759553534340359161530426225084163789310938929977224768170 * 2 + 1 from rfl, pow_add, pow_mul, h207, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h209 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1097003038214137361436646121704900336655157243755719908899072682 = ((97444625851781361183753331129117330505570250373951668064078330551041960702573 : Nat) : Fp) := by
    rw [show (1097003038214137361436646121704900336655157243755719908899072682 : Nat) = 548501519107068680718323060852450168327578621877859954449536341 * 2 + 0 from rfl, pow_add, pow_mul, h208, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h210 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2194006076428274722873292243409800673310314487511439817798145365 = ((17153020943936058073683628034762256264159671452039990182202940204161733970816 : Nat) : Fp) := by
    rw [show (2194006076428274722873292243409800673310314487511439817798145365 : Nat) = 1097003038214137361436646121704900336655157243755719908899072682 * 2 + 1 from rfl, pow_add, pow_mul, h209, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h211 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 4388012152856549445746584486819601346620628975022879635596290730 = ((113956565367746925387003256365315248327978958763793663824244136512433964947678 : Nat) : Fp) := by
    rw [show (4388012152856549445746584486819601346620628975022879635596290730 : Nat) = 2194006076428274722873292243409800673310314487511439817798145365 * 2 + 0 from rfl, pow_add, pow_mul, h210, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h212 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 8776024305713098891493168973639202693241257950045759271192581461 = ((36065346467493113423045924795170233349856352756275763379035040758065414244167 : Nat) : Fp) := by
    rw [show (8776024305713098891493168973639202693241257950045759271192581461 : Nat) = 4388012152856549445746584486819601346620628975022879635596290730 * 2 + 1 from rfl, pow_add, pow_mul, h211, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h213 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 17552048611426197782986337947278405386482515900091518542385162922 = ((72178040321360069057126347549882656397681138120123153523239299979955744446302 : Nat) : Fp) := by
    rw [show (17552048611426197782986337947278405386482515900091518542385162922 : Nat) = 8776024305713098891493168973639202693241257950045759271192581461 * 2 + 0 from rfl, pow_add, pow_mul, h212, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h214 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 35104097222852395565972675894556810772965031800183037084770325845 = ((41408224617457028616706622671878041268309234300227608941436594441781530824026 : Nat) : Fp) := by
    rw [show (35104097222852395565972675894556810772965031800183037084770325845 : Nat) = 17552048611426197782986337947278405386482515900091518542385162922 * 2 + 1 from rfl, pow_add, pow_mul, h213, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h215 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 70208194445704791131945351789113621545930063600366074169540651690 = ((107733786724976900454515759094762723494403940245205900852953293741293467002063 : Nat) : Fp) := by
    rw [show (70208194445704791131945351789113621545930063600366074169540651690 : Nat) = 35104097222852395565972675894556810772965031800183037084770325845 * 2 + 0 from rfl, pow_add, pow_mul, h214, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h216 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 140416388891409582263890703578227243091860127200732148339081303381 = ((45494917462585760168971731364791984456863013872906240519324515094071483704980 : Nat) : Fp) := by
    rw [show (140416388891409582263890703578227243091860127200732148339081303381 : Nat) = 70208194445704791131945351789113621545930063600366074169540651690 * 2 + 1 from rfl, pow_add, pow_mul, h215, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h217 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 280832777782819164527781407156454486183720254401464296678162606762 = ((25218770006344711906654714933791456087072877227418337872741717452783655028353 : Nat) : Fp) := by
    rw [show (280832777782819164527781407156454486183720254401464296678162606762 : Nat) = 140416388891409582263890703578227243091860127200732148339081303381 * 2 + 0 from rfl, pow_add, pow_mul, h216, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h218 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 561665555565638329055562814312908972367440508802928593356325213525 = ((4276705941037597481296148467121751650144311780671902386572476181482025824069 : Nat) : Fp) := by
    rw [show (561665555565638329055562814312908972367440508802928593356325213525 : Nat) = 280832777782819164527781407156454486183720254401464296678162606762 * 2 + 1 from rfl, pow_add, pow_mul, h217, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h219 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1123331111131276658111125628625817944734881017605857186712650427050 = ((65873599361807677953706524750899848350300395192192789547450267063499509425829 : Nat) : Fp) := by
    rw [show (1123331111131276658111125628625817944734881017605857186712650427050 : Nat) = 561665555565638329055562814312908972367440508802928593356325213525 * 2 + 0 from rfl, pow_add, pow_mul, h218, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h220 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2246662222262553316222251257251635889469762035211714373425300854101 = ((19738156028150097466206502523269903229927739095308312385281060833504397119307 : Nat) : Fp) := by
    rw [show (2246662222262553316222251257251635889469762035211714373425300854101 : Nat) = 1123331111131276658111125628625817944734881017605857186712650427050 * 2 + 1 from rfl, pow_add, pow_mul, h219, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h221 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 4493324444525106632444502514503271778939524070423428746850601708202 = ((51682805713523334951665757530306101513439611805278395303960343807024771010579 : Nat) : Fp) := by
    rw [show (4493324444525106632444502514503271778939524070423428746850601708202 : Nat) = 2246662222262553316222251257251635889469762035211714373425300854101 * 2 + 0 from rfl, pow_add, pow_mul, h220, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h222 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 8986648889050213264889005029006543557879048140846857493701203416404 = ((5301293233194660667164003282273788026743876831882006050292227044248396651979 : Nat) : Fp) := by
    rw [show (8986648889050213264889005029006543557879048140846857493701203416404 : Nat) = 4493324444525106632444502514503271778939524070423428746850601708202 * 2 + 0 from rfl, pow_add, pow_mul, h221, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h223 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 17973297778100426529778010058013087115758096281693714987402406832809 = ((56620154816527963112708977431643077712931259201076799323287932296424568585800 : Nat) : Fp) := by
    rw [show (17973297778100426529778010058013087115758096281693714987402406832809 : Nat) = 8986648889050213264889005029006543557879048140846857493701203416404 * 2 + 1 from rfl, pow_add, pow_mul, h222, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h224 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 35946595556200853059556020116026174231516192563387429974804813665619 = ((111081889463643415724240330942503385925118077069169858770075827346725462612542 : Nat) : Fp) := by
    rw [show (35946595556200853059556020116026174231516192563387429974804813665619 : Nat) = 17973297778100426529778010058013087115758096281693714987402406832809 * 2 + 1 from rfl, pow_add, pow_mul, h223, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h225 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 71893191112401706119112040232052348463032385126774859949609627331239 = ((93210606584930179328877266166804247976730264873479709798036365055839032247348 : Nat) : Fp) := by
    rw [show (71893191112401706119112040232052348463032385126774859949609627331239 : Nat) = 35946595556200853059556020116026174231516192563387429974804813665619 * 2 + 1 from rfl, pow_add, pow_mul, h224, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h226 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 143786382224803412238224080464104696926064770253549719899219254662479 = ((82204949332478849860622221723132028099118544183175880466585687737217096905441 : Nat) : Fp) := by
    rw [show (143786382224803412238224080464104696926064770253549719899219254662479 : Nat) = 71893191112401706119112040232052348463032385126774859949609627331239 * 2 + 1 from rfl, pow_add, pow_mul, h225, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h227 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 287572764449606824476448160928209393852129540507099439798438509324959 = ((25143339960338629168068068292193125033883758918712054259943725014154214625149 : Nat) : Fp) := by
    rw [show (287572764449606824476448160928209393852129540507099439798438509324959 : Nat) = 143786382224803412238224080464104696926064770253549719899219254662479 * 2 + 1 from rfl, pow_add, pow_mul, h226, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h228 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 575145528899213648952896321856418787704259081014198879596877018649919 = ((79521888744121243883404262221730029241357122683792595861203663151345784036044 : Nat) : Fp) := by
    rw [show (575145528899213648952896321856418787704259081014198879596877018649919 : Nat) = 287572764449606824476448160928209393852129540507099439798438509324959 * 2 + 1 from rfl, pow_add, pow_mul, h227, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h229 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1150291057798427297905792643712837575408518162028397759193754037299839 = ((111424544175995719012518708408817842958485409881550092234953820352960653974850 : Nat) : Fp) := by
    rw [show (1150291057798427297905792643712837575408518162028397759193754037299839 : Nat) = 575145528899213648952896321856418787704259081014198879596877018649919 * 2 + 1 from rfl, pow_add, pow_mul, h228, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h230 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2300582115596854595811585287425675150817036324056795518387508074599679 = ((72144455311319705231420089336300084740454427624088597413741977718507831769739 : Nat) : Fp) := by
    rw [show (2300582115596854595811585287425675150817036324056795518387508074599679 : Nat) = 1150291057798427297905792643712837575408518162028397759193754037299839 * 2 + 1 from rfl, pow_add, pow_mul, h229, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h231 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 4601164231193709191623170574851350301634072648113591036775016149199359 = ((10808956845271040667836185201731597551551983299110812397208428059068631629278 : Nat) : Fp) := by
    rw [show (4601164231193709191623170574851350301634072648113591036775016149199359 : Nat) = 2300582115596854595811585287425675150817036324056795518387508074599679 * 2 + 1 from rfl, pow_add, pow_mul, h230, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h232 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 9202328462387418383246341149702700603268145296227182073550032298398719 = ((26481203721056074394063498689472630328515090116819380919648344385012949523818 : Nat) : Fp) := by
    rw [show (9202328462387418383246341149702700603268145296227182073550032298398719 : Nat) = 4601164231193709191623170574851350301634072648113591036775016149199359 * 2 + 1 from rfl, pow_add, pow_mul, h231, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h233 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 18404656924774836766492682299405401206536290592454364147100064596797439 = ((81664150152220180393627507703102520126812031821565846450140317769343622584859 : Nat) : Fp) := by
    rw [show (18404656924774836766492682299405401206536290592454364147100064596797439 : Nat) = 9202328462387418383246341149702700603268145296227182073550032298398719 * 2 + 1 from rfl, pow_add, pow_mul, h232, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h234 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 36809313849549673532985364598810802413072581184908728294200129193594879 = ((111263724153329290141562469373188531558916305239311825383115353091992263313099 : Nat) : Fp) := by
    rw [show (36809313849549673532985364598810802413072581184908728294200129193594879 : Nat) = 18404656924774836766492682299405401206536290592454364147100064596797439 * 2 + 1 from rfl, pow_add, pow_mul, h233, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h235 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 73618627699099347065970729197621604826145162369817456588400258387189759 = ((35873123886532800611856120051578523000338817844083698895947072954027517860073 : Nat) : Fp) := by
    rw [show (73618627699099347065970729197621604826145162369817456588400258387189759 : Nat) = 36809313849549673532985364598810802413072581184908728294200129193594879 * 2 + 1 from rfl, pow_add, pow_mul, h234, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h236 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 147237255398198694131941458395243209652290324739634913176800516774379519 = ((17615749632424539050245731220920988209775161980797413840147889463540940480199 : Nat) : Fp) := by
    rw [show (147237255398198694131941458395243209652290324739634913176800516774379519 : Nat) = 73618627699099347065970729197621604826145162369817456588400258387189759 * 2 + 1 from rfl, pow_add, pow_mul, h235, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h237 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 294474510796397388263882916790486419304580649479269826353601033548759039 = ((2642804854438212590683254389317805677131980739664488289654773621595044696475 : Nat) : Fp) := by
    rw [show (294474510796397388263882916790486419304580649479269826353601033548759039 : Nat) = 147237255398198694131941458395243209652290324739634913176800516774379519 * 2 + 1 from rfl, pow_add, pow_mul, h236, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h238 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 588949021592794776527765833580972838609161298958539652707202067097518079 = ((108712249935760612717825935177801978183829407230252885080354643215088985814608 : Nat) : Fp) := by
    rw [show (588949021592794776527765833580972838609161298958539652707202067097518079 : Nat) = 294474510796397388263882916790486419304580649479269826353601033548759039 * 2 + 1 from rfl, pow_add, pow_mul, h237, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h239 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1177898043185589553055531667161945677218322597917079305414404134195036159 = ((61547749146004792929610850923191947556819905493331265236297821891210712137617 : Nat) : Fp) := by
    rw [show (1177898043185589553055531667161945677218322597917079305414404134195036159 : Nat) = 588949021592794776527765833580972838609161298958539652707202067097518079 * 2 + 1 from rfl, pow_add, pow_mul, h238, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h240 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2355796086371179106111063334323891354436645195834158610828808268390072319 = ((10981936276098837399040684762719329570410877576837705508122617827311680536810 : Nat) : Fp) := by
    rw [show (2355796086371179106111063334323891354436645195834158610828808268390072319 : Nat) = 1177898043185589553055531667161945677218322597917079305414404134195036159 * 2 + 1 from rfl, pow_add, pow_mul, h239, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h241 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 4711592172742358212222126668647782708873290391668317221657616536780144639 = ((81683499704637554097087984612249985357004481383968812783332901713366524561714 : Nat) : Fp) := by
    rw [show (4711592172742358212222126668647782708873290391668317221657616536780144639 : Nat) = 2355796086371179106111063334323891354436645195834158610828808268390072319 * 2 + 1 from rfl, pow_add, pow_mul, h240, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h242 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 9423184345484716424444253337295565417746580783336634443315233073560289279 = ((26194615348824015200460093506677566321548545767707685287865662493167805925056 : Nat) : Fp) := by
    rw [show (9423184345484716424444253337295565417746580783336634443315233073560289279 : Nat) = 4711592172742358212222126668647782708873290391668317221657616536780144639 * 2 + 1 from rfl, pow_add, pow_mul, h241, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h243 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 18846368690969432848888506674591130835493161566673268886630466147120578559 = ((10132886880626546059808416701832163699497684339937323924000525318334255834728 : Nat) : Fp) := by
    rw [show (18846368690969432848888506674591130835493161566673268886630466147120578559 : Nat) = 9423184345484716424444253337295565417746580783336634443315233073560289279 * 2 + 1 from rfl, pow_add, pow_mul, h242, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h244 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 37692737381938865697777013349182261670986323133346537773260932294241157119 = ((96145228036791272347287591001595652681705751830372679236349976095125901623452 : Nat) : Fp) := by
    rw [show (37692737381938865697777013349182261670986323133346537773260932294241157119 : Nat) = 18846368690969432848888506674591130835493161566673268886630466147120578559 * 2 + 1 from rfl, pow_add, pow_mul, h243, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h245 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 75385474763877731395554026698364523341972646266693075546521864588482314239 = ((41782768751604672819376458854884897694342149918888059375266245379808888448893 : Nat) : Fp) := by
    rw [show (75385474763877731395554026698364523341972646266693075546521864588482314239 : Nat) = 37692737381938865697777013349182261670986323133346537773260932294241157119 * 2 + 1 from rfl, pow_add, pow_mul, h244, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h246 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 150770949527755462791108053396729046683945292533386151093043729176964628478 = ((48182855768544207673659395879916164314193685121842011314843417349281473232689 : Nat) : Fp) := by
    rw [show (150770949527755462791108053396729046683945292533386151093043729176964628478 : Nat) = 75385474763877731395554026698364523341972646266693075546521864588482314239 * 2 + 0 from rfl, pow_add, pow_mul, h245, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h247 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 301541899055510925582216106793458093367890585066772302186087458353929256957 = ((113914995989222913384846916963315931267312877007247552587612980423938598643668 : Nat) : Fp) := by
    rw [show (301541899055510925582216106793458093367890585066772302186087458353929256957 : Nat) = 150770949527755462791108053396729046683945292533386151093043729176964628478 * 2 + 1 from rfl, pow_add, pow_mul, h246, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h248 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 603083798111021851164432213586916186735781170133544604372174916707858513914 = ((16917694604137855099959345955774822495829732572303578119586360570209079987762 : Nat) : Fp) := by
    rw [show (603083798111021851164432213586916186735781170133544604372174916707858513914 : Nat) = 301541899055510925582216106793458093367890585066772302186087458353929256957 * 2 + 0 from rfl, pow_add, pow_mul, h247, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h249 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 1206167596222043702328864427173832373471562340267089208744349833415717027829 = ((5275473803500525352526026164633111500304804289437806846072862508717690556340 : Nat) : Fp) := by
    rw [show (1206167596222043702328864427173832373471562340267089208744349833415717027829 : Nat) = 603083798111021851164432213586916186735781170133544604372174916707858513914 * 2 + 1 from rfl, pow_add, pow_mul, h248, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h250 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 2412335192444087404657728854347664746943124680534178417488699666831434055659 = ((47033123427715144957970898848337074550213844492785242091248698844584856999432 : Nat) : Fp) := by
    rw [show (2412335192444087404657728854347664746943124680534178417488699666831434055659 : Nat) = 1206167596222043702328864427173832373471562340267089208744349833415717027829 * 2 + 1 from rfl, pow_add, pow_mul, h249, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h251 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 4824670384888174809315457708695329493886249361068356834977399333662868111319 = ((87217155786056462017332245134470873361821475905372260434560935159578659505550 : Nat) : Fp) := by
    rw [show (4824670384888174809315457708695329493886249361068356834977399333662868111319 : Nat) = 2412335192444087404657728854347664746943124680534178417488699666831434055659 * 2 + 1 from rfl, pow_add, pow_mul, h250, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h252 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 9649340769776349618630915417390658987772498722136713669954798667325736222638 = ((92918902052465737461182286990515267478741849099176759764925929837520548598330 : Nat) : Fp) := by
    rw [show (9649340769776349618630915417390658987772498722136713669954798667325736222638 : Nat) = 4824670384888174809315457708695329493886249361068356834977399333662868111319 * 2 + 0 from rfl, pow_add, pow_mul, h251, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h253 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 19298681539552699237261830834781317975544997444273427339909597334651472445277 = ((60197513588986302554485582024885075108884032450952339817679072026166228089408 : Nat) : Fp) := by
    rw [show (19298681539552699237261830834781317975544997444273427339909597334651472445277 : Nat) = 9649340769776349618630915417390658987772498722136713669954798667325736222638 * 2 + 1 from rfl, pow_add, pow_mul, h252, pow_two, pow_one, ← Nat.cast_mul, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  have h254 : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) ^ 38597363079105398474523661669562635951089994888546854679819194669302944890554 = ((55594575648329892869085402983802832744385952214688224221778511981742606582254 : Nat) : Fp) := by
    rw [show (38597363079105398474523661669562635951089994888546854679819194669302944890554 : Nat) = 19298681539552699237261830834781317975544997444273427339909597334651472445277 * 2 + 0 from rfl, pow_add, pow_mul, h253, pow_two, pow_zero, mul_one, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq, p]
  exact h254

theorem castMinusSeven : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : Nat) : Fp) = -7 := by
  have h : (p-7)+7=p := by norm_num [p]
  have hc := congrArg (fun n : Nat => (n : Fp)) h
  have hm : ((p-7 : Nat) : Fp) = -7 := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self] using hc
  norm_num [p] at hm
  exact hm

theorem residueNeOne : ((55594575648329892869085402983802832744385952214688224221778511981742606582254 : Nat) : Fp) ≠ 1 := by
  intro h
  have hc : ((55594575648329892869085402983802832744385952214688224221778511981742606582254 : Nat) : Fp) = ((1 : Nat) : Fp) := by simpa only [Nat.cast_one] using h
  have hm := (ZMod.natCast_eq_natCast_iff 55594575648329892869085402983802832744385952214688224221778511981742606582254 1 p).1 hc
  norm_num [Nat.ModEq, p] at hm

theorem sevenNeZero : (7 : Fp) ≠ 0 := by
  intro h
  have hc : ((7 : Nat) : Fp) = ((0 : Nat) : Fp) := by simpa only [Nat.cast_ofNat, Nat.cast_zero] using h
  have hm := (ZMod.natCast_eq_natCast_iff 7 0 p).1 hc
  norm_num [Nat.ModEq, p] at hm

theorem noCube : ∀ x : Fp, x^3 ≠ -7 := by
  intro x h
  have hx : x ≠ 0 := by
    intro hz
    subst x
    have bad : (-7 : Fp) = 0 := by simpa using h.symm
    exact sevenNeZero (neg_eq_zero.mp bad)
  have hf : x^(p-1) = 1 := by
    simpa only [Fp, ZMod.card] using FiniteField.pow_card_sub_one_eq_one x hx
  have hnum : (3 : Nat) * 38597363079105398474523661669562635951089994888546854679819194669302944890554 = p-1 := by norm_num [p]
  have heq : (-7 : Fp)^38597363079105398474523661669562635951089994888546854679819194669302944890554 = 1 := by
    rw [← h, ← pow_mul, hnum]
    exact hf
  apply residueNeOne
  rw [← numericNoncube, castMinusSeven]
  exact heq
theorem finiteYNeZero {x y : Fp} (h : curve.toAffine.Nonsingular x y) : y ≠ 0 := by
  intro hy
  have heq := h.1
  rw [curve.toAffine.equation_iff] at heq
  have heq2 : y^2 = x^3 + 7 := by simpa [curve, curveA, curveB] using heq
  rw [hy] at heq2
  have hc : x^3 = -7 := by linear_combination -heq2
  exact noCube x hc


theorem ecdsaPointYNonzero (P : ECDSAAdd.Secp256k1.Point) (hp : P ≠ 0) :
    ECDSAAdd.Arithmetic.pointY P ≠ 0 := by
  cases P with
  | zero => exact (hp rfl).elim
  | @some x y hc =>
    have hy : y ≠ 0 := finiteYNeZero hc
    intro h
    have hz : y.val = 0 := by simpa [ECDSAAdd.Arithmetic.pointY, ECDSAAdd.Secp256k1.coordinates] using h
    exact hy ((ZMod.val_eq_zero y).mp hz)


end ShorECDLP.Entrant

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

def finiteSignFlag (sign inf flag : Wire) : Program :=
  [.X sign, .X inf, .CCX sign inf flag, .X inf, .X sign]

theorem finiteSignFlag_run (sign inf flag : Wire) (hsi : sign ≠ inf)
    (hsf : sign ≠ flag) (hif : inf ≠ flag) (st : State) (m : List Bool) :
    run (finiteSignFlag sign inf flag) m st =
      ⟨st.phase, writeBit st.basis flag (st.basis flag ^^ ((!st.basis sign) && (!st.basis inf)))⟩ := by
  apply State.extensionality
  · rfl
  funext w
  by_cases hw1 : w = sign <;> by_cases hw2 : w = inf <;> by_cases hw3 : w = flag <;>
    simp_all [finiteSignFlag, run, writeBit, Function.update_apply, Ne.symm hsi, Ne.symm hsf, Ne.symm hif]


open ECDSAAdd.Entrant

def finiteSignErase (sign inf flag : Wire) : Program :=
  [.X sign] ++ chainErase sign inf flag ++ [.X sign]

theorem finiteSignErase_run (sign inf flag : Wire) (hsi : sign ≠ inf)
    (hsf : sign ≠ flag) (hif : inf ≠ flag) (st : State) (m : List Bool)
    (hf : st.basis flag = ((!st.basis sign) && (!st.basis inf))) :
    run (finiteSignErase sign inf flag) m st = ⟨st.phase, writeBit st.basis flag false⟩ := by
  let v : State := ⟨st.phase, writeBit st.basis sign (!st.basis sign)⟩
  have hv : v.basis flag = (v.basis sign && !v.basis inf) := by
    simp [v, writeBit, Ne.symm hsf, Ne.symm hsi, hf]
  have he := chainErase_run sign inf flag hsi hif hsf v (m.take 1) hv
  have hc : measurementCount (chainErase sign inf flag) = 1 := rfl
  rw [finiteSignErase, run_append, run_append]
  simp only [measurementCount_append, measurementCount, hc, Nat.zero_add, List.take_zero, List.drop_zero]
  change run [.X sign] (m.drop 1) (run (chainErase sign inf flag) (m.take 1) v) = _
  rw [he]
  simp only [run]
  apply State.extensionality
  · rfl
  funext w
  by_cases hs : w = sign <;> by_cases ht : w = flag <;>
    simp_all [v, writeBit, Function.update_apply, Ne.symm hsf]


def finiteSignMeasured (K : NegLayout) (sign inf flag p : Nat) : Program :=
  finiteSignFlag sign inf flag ++ K.reflection flag (p+1) ++ finiteSignErase sign inf flag

theorem finiteSignMeasured_run (K : NegLayout) (sign inf flag p : Nat)
    (hn : (K.wires flag).Nodup) (hw : K.work.length = K.word.length)
    (npos : 0 < K.word.length) (hp : p + 1 < 2 ^ K.word.length)
    (hsi : sign ≠ inf) (hsf : sign ≠ flag) (hif : inf ≠ flag)
    (hsign : sign ∉ K.word) (hinf : inf ∉ K.word)
    (st : State) (hflag : st.basis flag = false) (hY : ECDSAAdd.regValue K.word st.basis < p)
    (hwork : ECDSAAdd.regValue K.work st.basis = 0) (hcin : st.basis K.cin = false)
    (hzero : st.basis K.zero = false) (m : List Bool) :
    (run (finiteSignMeasured K sign inf flag p) m st).phase = st.phase ∧
      ECDSAAdd.regValue K.word (run (finiteSignMeasured K sign inf flag p) m st).basis =
        (if st.basis sign then ECDSAAdd.regValue K.word st.basis
         else if st.basis inf then ECDSAAdd.regValue K.word st.basis
         else p - ECDSAAdd.regValue K.word st.basis) ∧
      ∀ w ∉ K.word, (run (finiteSignMeasured K sign inf flag p) m st).basis w = st.basis w := by
  have head := (List.nodup_cons.mp hn).1
  have fw : flag ∉ K.word := fun h => head (by simp [CompactRecoveryNegateLayout.wires, h])
  have fp : flag ∉ K.work := fun h => head (by simp [CompactRecoveryNegateLayout.wires, h])
  have fc : K.cin ≠ flag := by intro h; apply head; simp [CompactRecoveryNegateLayout.wires, h]
  have fz : K.zero ≠ flag := by intro h; apply head; simp [CompactRecoveryNegateLayout.wires, h]
  let v : State := ⟨st.phase, writeBit st.basis flag (st.basis flag ^^ ((!st.basis sign) && (!st.basis inf)))⟩
  let u := run (K.reflection flag (p+1)) m v
  have vword : ECDSAAdd.regValue K.word v.basis = ECDSAAdd.regValue K.word st.basis :=
    reg_update_outside _ _ _ _ fw
  have vn := K.reflection_correct flag hn hw npos (p+1) (ECDSAAdd.regValue K.word st.basis)
    hp (by omega) v m vword ((reg_update_outside _ _ _ _ fp).trans hwork)
    (by simpa [v, writeBit, fc] using hcin) (by simpa [v, writeBit, fz] using hzero)
  have vf : v.basis flag = (!st.basis sign && !st.basis inf) := by simp [v, writeBit, hflag]
  have vs : v.basis sign = st.basis sign := by simp [v, writeBit, hsf]
  have vi : v.basis inf = st.basis inf := by simp [v, writeBit, hif]
  have uf : u.basis flag = (!st.basis sign && !st.basis inf) := (vn.2.2 _ fw).trans vf
  have us : u.basis sign = st.basis sign := (vn.2.2 _ hsign).trans vs
  have ui : u.basis inf = st.basis inf := (vn.2.2 _ hinf).trans vi
  have hwhole : run (finiteSignMeasured K sign inf flag p) m st =
      ⟨u.phase, writeBit u.basis flag false⟩ := by
    have hc : measurementCount (finiteSignFlag sign inf flag) = 0 := rfl
    rw [finiteSignMeasured, run_append, run_append]
    simp only [measurementCount_append, hc, Nat.zero_add, List.take_zero, List.drop_zero, run_take]
    rw [finiteSignFlag_run sign inf flag hsi hsf hif]
    change run (finiteSignErase sign inf flag) _ u = _
    apply finiteSignErase_run sign inf flag hsi hsf hif
    rw [uf, us, ui]
  rw [hwhole]
  refine ⟨vn.1, ?_, ?_⟩
  · rw [reg_update_outside _ _ _ _ fw, vn.2.1, vf]
    cases hs : st.basis sign <;> cases hi : st.basis inf <;> simp [hs, hi]
  · intro w hw
    by_cases hf : w = flag
    · subst w
      simp [writeBit, hflag]
    · have hu := vn.2.2 w hw
      simpa [v, writeBit, hf] using hu

open ECDSAAdd.Secp256k1

theorem pointFiniteSignValue (P : ECDSAAdd.Secp256k1.Point) (sign : Bool) :
    (if sign then pointY P else if !pointFinite P then pointY P else ECDSAAdd.p - pointY P) =
      (if sign then pointY P else (ECDSAAdd.p - pointY P) % ECDSAAdd.p) := by
  cases hp : P with
  | zero => simp [pointY, pointFinite, ECDSAAdd.Secp256k1.coordinates]
  | @some x y hc =>
    have hn : pointY (.some hc : ECDSAAdd.Secp256k1.Point) ≠ 0 :=
      ecdsaPointYNonzero (.some hc) (WeierstrassCurve.Affine.Point.some_ne_zero hc)
    have hy := (point_coordinates_lt (.some hc : ECDSAAdd.Secp256k1.Point)).2
    have hlt : ECDSAAdd.p - pointY (.some hc : ECDSAAdd.Secp256k1.Point) < ECDSAAdd.p := by omega
    simp [pointFinite, ECDSAAdd.Secp256k1.coordinates, Nat.mod_eq_of_lt hlt]

def fastWindowSignProgram : Program := finiteSignMeasured (negateYLayout streamLayout) 870 838
  streamLayout.core.generic ECDSAAdd.p

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.regValue

open ECDSAAdd.Arithmetic.ControlledPointLayout

theorem fastWindowSignProgram_point (st : State) (P : ECDSAAdd.Secp256k1.Point)
    (hs : StreamPoint st.basis P) (hc : ECDSAAdd.regValue streamLayout.work st.basis = 0)
    (m : List Bool) :
    (run fastWindowSignProgram m st).phase = st.phase ∧
      StreamPoint (run fastWindowSignProgram m st).basis (if st.basis 870 then P else -P) ∧
      ∀ w ∉ List.range' 580 256, (run fastWindowSignProgram m st).basis w = st.basis w := by
  let L := streamLayout
  let K := negateYLayout L
  have width := negateYLayout_widths L streamLayout_widths
  have word : K.word = List.range' 580 256 := by
    change L.point.y = _
    rw [streamLayout_point]
  have genWork : L.core.generic ∈ L.work := one_boundary_work_subset L
    (List.mem_append_left _ (by simp [inPlaceFlags]))
  have genFalse : st.basis L.core.generic = false := (regValue_zero _ _).mp hc _ genWork
  have clean (q : Wire) (hq : q ∈ K.work ++ [K.cin,K.zero]) : st.basis q = false := by
    change q ∈ (negateYLayout L).work ++ [(negateYLayout L).cin,(negateYLayout L).zero] at hq
    rw [negateYLayout_pool L streamLayout_widths] at hq
    exact (regValue_zero _ _).mp hc q (one_boundary_work_subset L
      (List.mem_append_right _ (List.mem_of_mem_take hq)))
  have signNe : (870 : Wire) ≠ L.core.generic := by
    have h := streamWork_lower _ genWork
    dsimp only [Wire] at *
    omega
  have hY : ECDSAAdd.regValue K.word st.basis < ECDSAAdd.p := by
    rw [word, hs.2.2]
    exact (point_coordinates_lt P).2
  have infNe : (838 : Wire) ≠ L.core.generic := by
    have h := streamWork_lower _ genWork
    dsimp only [Wire] at *
    omega
  have h := finiteSignMeasured_run K 870 838 L.core.generic ECDSAAdd.p
    (negateYLayout_nodup_generic L streamLayout_widths streamLayout_nodup) width.2
    (by rw [width.1]; decide) (by rw [width.1]; norm_num [ECDSAAdd.p])
    (by decide) signNe infNe (by rw [word]; decide +kernel) (by rw [word]; decide +kernel)
    st genFalse hY ((regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq])))
    (clean _ (by simp)) (clean _ (by simp)) m
  change (run fastWindowSignProgram m st).phase = _ ∧ _ at h
  rw [word] at h
  have hyOut : ECDSAAdd.regValue (List.range' 580 256) (run fastWindowSignProgram m st).basis =
      (if st.basis 870 then ECDSAAdd.regValue (List.range' 580 256) st.basis else
        (ECDSAAdd.p-ECDSAAdd.regValue (List.range' 580 256) st.basis)%ECDSAAdd.p) := by
    simpa only [hs.1, hs.2.2, pointFiniteSignValue] using h.2.1
  have hf : (run fastWindowSignProgram m st).basis 838 = st.basis 838 := h.2.2 _ (by decide +kernel)
  have hx : ECDSAAdd.regValue (List.range' 263 256) (run fastWindowSignProgram m st).basis =
      ECDSAAdd.regValue (List.range' 263 256) st.basis := by
    apply ECDSAAdd.Arithmetic.regValue_congr
    intro w hw
    apply h.2.2 w
    simp only [List.mem_range'_1] at hw ⊢
    dsimp only [Wire] at *
    omega
  refine ⟨h.1, ?_, h.2.2⟩
  by_cases hsign : st.basis 870 = true
  · simp only [hsign, if_true]
    refine ⟨hf.trans hs.1, hx.trans hs.2.1, ?_⟩
    have hyEq : ECDSAAdd.regValue (List.range' 580 256) (run fastWindowSignProgram m st).basis =
        ECDSAAdd.regValue (List.range' 580 256) st.basis := by simpa [hsign] using hyOut
    exact hyEq.trans hs.2.2
  · have hfalse : st.basis 870 = false := Bool.eq_false_iff.mpr hsign
    simp only [hfalse, Bool.false_eq_true, if_false]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ECDSAAdd.ShorPort.pointFinite_neg] using hf.trans hs.1
    · simpa only [ECDSAAdd.ShorPort.pointX_neg] using hx.trans hs.2.1
    · have hyEq : ECDSAAdd.regValue (List.range' 580 256) (run fastWindowSignProgram m st).basis =
          (ECDSAAdd.p-pointY P)%ECDSAAdd.p := by simpa [hfalse, hs.2.2] using hyOut
      exact hyEq.trans (pointY_neg_mod P).symm



theorem finiteSignMeasured_counts (K : NegLayout) (sign inf flag p : Nat)
    (hw : K.work.length = K.word.length) (hn : K.word.length = 256) :
    ECDSAAdd.toffoliCount (finiteSignMeasured K sign inf flag p) = 256 ∧
      ECDSAAdd.measurementCount (finiteSignMeasured K sign inf flag p) = 256 := by
  have h := K.reflection_counts flag (p+1) hw (by omega)
  simp [finiteSignMeasured, finiteSignFlag, finiteSignErase, chainErase,
    toffoliCount_append, measurementCount_append, toffoliCount, measurementCount, h.1, h.2, hn]

theorem fastWindowSign_counts : ECDSAAdd.toffoliCount fastWindowSignProgram = 256 ∧
    ECDSAAdd.measurementCount fastWindowSignProgram = 256 := by
  have width := negateYLayout_widths streamLayout streamLayout_widths
  exact finiteSignMeasured_counts (negateYLayout streamLayout) 870 838 streamLayout.core.generic
    ECDSAAdd.p width.2 width.1

open Quantum Challenge ShorECDLP.Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
theorem fastWindowSign_coherent : CoherentlyImplementsOn
    (literalSource (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram))
    (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady := by
  apply literal_coherent
  intro s hs m
  rw [ECDSAAdd.Baselines.normalize_run]
  obtain ⟨P,hP⟩ := hs.1.2
  have secp := hs.1.1.1.1
  have point := StreamPoint.of_coordinates s P secp hP
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (ECDSAAdd.Arithmetic.regValue_zero _ _).mpr
      (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h := fastWindowSignProgram_point ⟨false,s⟩ (Bridge.toB P) point work m
  apply ECDSAAdd.State.extensionality
  · exact h.1
  unfold signPointState
  rw [inputPoint_eq s P hP]
  apply StreamPoint.state_eq s _ _ secp
  · by_cases hb : s 870 = true
    · simpa [hb] using h.2.1
    · have hf : s 870 = false := Bool.eq_false_iff.mpr hb
      simpa [hf, Bridge.toB_neg] using h.2.1
  · intro w hw
    apply h.2.2 w
    intro hy
    exact hw (by simp [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, hy])


open ECDSAAdd.RecordedQuantum

theorem finiteSignFlag_physical (sign inf flag : Wire) (hsf : sign ≠ flag) (hif : inf ≠ flag) :
    GatePhysical (finiteSignFlag sign inf flag) := by
  simp [finiteSignFlag, GatePhysical, PhysicalInstr, ECDSAAdd.ProperGate, hsf, hif]


theorem finiteSignErase_physical (sign inf flag : Wire) : GatePhysical (finiteSignErase sign inf flag) := by
  simp [finiteSignErase, chainErase, GatePhysical, PhysicalInstr, ECDSAAdd.ProperGate]

theorem finiteSignMeasured_physical (K : NegLayout) (sign inf flag p : Nat)
    (hn : (K.wires flag).Nodup) (hsf : sign ≠ flag) (hif : inf ≠ flag) :
    GatePhysical (finiteSignMeasured K sign inf flag p) := by
  simp only [finiteSignMeasured, gatePhysical_append]
  exact ⟨⟨finiteSignFlag_physical sign inf flag hsf hif,
    K.reflection_physical flag (p+1) hn⟩, finiteSignErase_physical sign inf flag⟩

theorem fastWindowSign_physical : GatePhysical fastWindowSignProgram := by
  unfold fastWindowSignProgram
  exact finiteSignMeasured_physical (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p
    (negateYLayout_nodup_generic streamLayout streamLayout_widths streamLayout_nodup)
    (by decide +kernel) (by decide +kernel)


theorem finiteSignMeasured_slots (K : NegLayout) (sign inf flag p : Nat) (width : K.word.length = 256) :
    ECDSAAdd.Challenge.gateSlots (finiteSignMeasured K sign inf flag p) ≤ 100000 := by
  have flip := ECDSAAdd.Baselines.maskedConstant_gateSlots_le flag K.word (2^K.word.length-1)
  have add := ECDSAAdd.Baselines.mappedConst_gateSlots_le (some flag) K.word K.carries K.cin (p+1)
  simp only [finiteSignMeasured, finiteSignErase, chainErase, CompactRecoveryNegateLayout.reflection,
    CompactRecoveryNegateLayout.complement, CompactRecoveryNegateLayout.add,
    ECDSAAdd.Challenge.gateSlots_append, finiteSignFlag, ECDSAAdd.Baselines.gateSlots_cons,
    ECDSAAdd.Baselines.gateSlots_nil, ECDSAAdd.Challenge.instructionSlots, List.length_nil, List.length_cons]
  omega

theorem fastWindowSign_slots : ECDSAAdd.Challenge.gateSlots fastWindowSignProgram ≤ 100000 :=
  finiteSignMeasured_slots _ _ _ _ _ (negateYLayout_widths streamLayout streamLayout_widths).1

theorem fastWindowSign_normalized_counts :
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) ≤ 256 ∧
      ECDSAAdd.measurementCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) = 256 := by
  exact ⟨(ECDSAAdd.Baselines.normalize_toffoli fastWindowSignProgram).trans fastWindowSign_counts.1.le,
    (ECDSAAdd.Baselines.normalize_measurements fastWindowSignProgram).trans fastWindowSign_counts.2⟩


theorem finiteSignMeasured_support (K : NegLayout) (sign inf flag p : Nat) :
    ECDSAAdd.wires (finiteSignMeasured K sign inf flag p) ⊆ (sign :: inf :: K.wires flag).toFinset := by
  have hr := K.reflection_support flag (p+1)
  simp only [finiteSignMeasured, ECDSAAdd.wires_append, Finset.union_subset_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro w hw
    simp [finiteSignFlag, ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hw
    rcases hw with rfl | rfl | rfl <;> simp [CompactRecoveryNegateLayout.wires]
  · exact hr.trans (fun w hw => List.mem_toFinset.mpr
      (List.mem_cons_of_mem sign (List.mem_cons_of_mem inf (List.mem_toFinset.mp hw))))
  · intro w hw
    simp [finiteSignErase, chainErase, ECDSAAdd.wires, ECDSAAdd.Instr.wires, ECDSAAdd.correctionWires] at hw
    rcases hw with rfl | rfl | rfl <;> simp [CompactRecoveryNegateLayout.wires]

open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration

def nFastProgram (start : Nat) : Straight 32768 start (start+256) :=
  literalFixed (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) 256
    ((literal_meas (n := 32768) _).trans fastWindowSign_normalized_counts.2) start

theorem nFastProgram_run (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((nFastProgram start).instantiate read history).run =
      (literalSource (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)).run :=
  literalFixed_run (n := 32768) _ _ _ start read history

theorem nFastProgram_credit (start : Nat) :
    WEXCredit.ProgramCredit (nFastProgram start)
      (ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) := by
  unfold nFastProgram literalFixed
  constructor
  · rw [WEXCredit.residue_naive_cast]
    exact WEXCredit.literal_residue _ _
  · rw [WEXCredit.added_naive_cast, WEXCredit.literal_added]


def widthFastBodyRecords (k : Nat) : Nat := widthAddRecords k + 512

def widthFastBodyProgram (k : Nat) (hk : k ≤ 15) (start : Nat) :
    Straight 32768 start (start + widthFastBodyRecords k) :=
  NaiveChallenge.castFinish (by unfold widthFastBodyRecords; omega)
    (((((prefixProgram start).append (nFastProgram start)).append
      (widthAddProgram k hk (start + 256))).append
      (nFastProgram (start + 256 + widthAddRecords k))).append
      (suffixProgram (start + 256 + widthAddRecords k + 256)))

def widthFastMiddleSource (k : Nat) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) : AdaptiveCircuit :=
  ((literalSource (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)).seq
    (widthRowSource k coeffs Q)).seq (literalSource (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram))

def widthFastBodySource (k : Nat) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (widthFastMiddleSource k coeffs Q)).seq suffixSource

theorem widthFastMiddle_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (widthFastMiddleSource k coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (widthMiddleState k coeffs Q)) liveReady := by
  have hs := fastWindowSign_coherent
  have first := composeCoherent hs (widthRowSource_coherent k hk coeffs Q hQ hn)
    (fun s h => liveReady_write _ s h)
  have all := composeCoherent first hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  exact all

theorem widthFastBodySource_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (widthFastBodySource k coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (widthBodyState k coeffs Q)) windowReady := by
  have h := composeCoherent prefix_coherent (widthFastMiddle_coherent k hk coeffs Q hQ hn)
    (fun s hs => windowPrepare_live _ (rootFlip_live s hs))
  exact composeCoherent (f := fun s => widthMiddleState k coeffs Q (prefixState s)) (g := suffixState)
    h suffix_coherent (fun _ _ => trivial)

theorem widthFastBodyProgram_run (k : Nat) (hk : k ≤ 15) (start : Nat)
    (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (history : Fin start → Bool) :
    ((widthFastBodyProgram k hk start).instantiate (readConstant coeffs Q) history).run =
      (widthFastBodySource k coeffs Q).run := by
  rw [widthFastBodyProgram,NaiveChallenge.instantiate_castFinish]
  rw [append_run_fixed _ _ _ _ _ (fun h => suffixProgram_run _ _ h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => nFastProgram_run _ _ h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => widthAddProgram_run k hk _ coeffs Q h),AdaptiveCircuit.run_seq]
  rw [append_run_fixed _ _ _ _ _ (fun h => nFastProgram_run _ _ h),AdaptiveCircuit.run_seq,prefixProgram_run]
  simp only [← AdaptiveCircuit.run_seq,widthFastBodySource,widthFastMiddleSource,adaptive_seq_assoc]

theorem widthFastBodyProgram_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (halias : WidthAliased k coeffs)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((widthFastBodyProgram k hk start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) windowReady := by
  have h := widthFastBodySource_coherent k hk coeffs Q hQ hn
  have he := h.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) (by
    intro s hs
    obtain ⟨P,hP⟩ := hs.1.2
    have he : widthBodyState k coeffs Q s = bodyState coeffs Q s := by
      rw [widthBodyState_correct k hk coeffs Q halias s hs P hP,bodyState_correct coeffs Q s hs P hP]
    simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,he])
  obtain ⟨cs,aligned,mass⟩ := he
  refine ⟨cs,?_,mass⟩
  rw [widthFastBodyProgram_run]
  exact aligned

theorem widthFastBodyProgram_credit (k : Nat) (hk : k ≤ 15) (start : Nat) :
    WEXCredit.ProgramCredit (widthFastBodyProgram k hk start)
      (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) +
        literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2 ^ k - 1)) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  let b := literalToffolis (normalizeW (rowAddCode probeRows))
  have hl : WEXCredit.ProgramCredit (nFastProgram start) a := nFastProgram_credit start
  have ha : WEXCredit.ProgramCredit (widthAddProgram k hk (start + 256)) (b + 21 * (2 ^ k - 1)) :=
    widthAddProgram_credit k hk _
  have hr : WEXCredit.ProgramCredit (nFastProgram (start + 256 + widthAddRecords k)) a := nFastProgram_credit _
  have ht := WEXCredit.credit_append (WEXCredit.credit_append (WEXCredit.credit_append
    (WEXCredit.credit_append (WEXCredit.prefix_credit start) hl) ha) hr)
    (WEXCredit.suffix_credit (start + 256 + widthAddRecords k + 256))
  have hn : (((0 + a) + (b + 21 * (2 ^ k - 1))) + a) + 0 = 2 * a + b + 21 * (2 ^ k - 1) := by omega
  have ht : WEXCredit.ProgramCredit _ (2 * a + b + 21 * (2 ^ k - 1)) := hn ▸ ht
  unfold widthFastBodyProgram
  exact WEXCredit.credit_naive_cast _ ht


theorem nFastProgram_wellFormed (start : Nat) : (nFastProgram start).WellFormed :=
  literalFixed_wellFormed (n := 32768) _ _ _
    (ECDSAAdd.Baselines.normalize_physical fastWindowSignProgram
      (by simpa only [GatePhysical] using fastWindowSign_physical)) start

theorem nFastProgram_slots (start : Nat) : (nFastProgram start).gateSlots =
    Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) :=
  literalFixed_slots (n := 32768) _ _ _ start

theorem nFastProgram_source (start : Nat) : ChallengeMigration.straightWires (nFastProgram start) ⊆ sourceSupport := by
  apply literalFixed_support (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) 256
    ((literal_meas (n := 32768) _).trans fastWindowSign_normalized_counts.2) sourceSupport (start := start)
  rw [ECDSAAdd.Baselines.normalize_wires]
  have hs := finiteSignMeasured_support (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p
  have cover : 870 :: 838 :: (negateYLayout streamLayout).wires streamLayout.core.generic ⊆ sourceSupport := by
    apply source_of_bounds; decide +kernel
  exact hs.trans (fun w hw => List.mem_toFinset.mpr (cover (List.mem_toFinset.mp hw)))

attribute [local irreducible] widthAddProgram compile Bridge.translate ECDSAAdd.Baselines.normalizeProgram
  ECDSAAdd.toffoliCount literalToffolis normalizeW Nat.add Nat.mul

theorem widthFastBodyProgram_wellFormed (k : Nat) (hk : k ≤ 15) (start : Nat) :
    (widthFastBodyProgram k hk start).WellFormed := by
  rw [widthFastBodyProgram,NaiveChallenge.wellFormed_castFinish]
  apply ChallengeMigration.straight_append_wellFormed
  · apply ChallengeMigration.straight_append_wellFormed
    · apply ChallengeMigration.straight_append_wellFormed
      · exact ChallengeMigration.straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact widthAddProgram_wellFormed k hk (start + 256)
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem widthFastBodyProgram_slots (k : Nat) (hk : k = 12 ∨ k = 13) (start : Nat) :
    (widthFastBodyProgram k (by omega) start).gateSlots ≤ 1100000000 := by
  rw [widthFastBodyProgram,NaiveChallenge.gateSlots_castFinish]
  simp only [Straight.gateSlots_append,nFastProgram_slots,widthAddProgram_slots,prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  have row := widthRow_slots_bound k hk start
  rw [widthAddProgram_slots] at row
  omega

theorem widthFastBodyProgram_source (k : Nat) (hk : k ≤ 15) (start : Nat) :
    ChallengeMigration.straightWires (widthFastBodyProgram k hk start) ⊆ sourceSupport := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ sourceSupport := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ sourceSupport := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    decide +kernel
  rw [widthFastBodyProgram,support_castFinish]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,nFastProgram_source _⟩,widthAddProgram_source k hk _⟩,nFastProgram_source _⟩,hs _⟩


attribute [local irreducible] widthFastBodyProgram AndGadget.added

theorem widthFastBodyProgram_tBound (k : Nat) (hk : k ≤ 15) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((widthFastBodyProgram k hk start).instantiate read history).tCount ≤
      7 * (2162369 + 21 * (2 ^ k - 1)) := by
  have ha := literalToffolis_normalize (rowAddCode probeRows)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (rowAddCode probeRows) = 2161857 := by
    simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
      Nat.zero_add,Nat.add_zero,hc]
  rw [hrow] at ha
  have hs := widthFastBodyProgram_credit k hk start
  have ht := WEXCredit.exact_t (widthFastBodyProgram k hk start) hs.1 read history
  rw [hs.2] at ht
  have hn := fastWindowSign_normalized_counts.1
  omega

def widthFastCompactProgram (k : Nat) (hk : k ≤ 15) (start : Nat) :
    Straight 32768 start (start + widthFastBodyRecords k) :=
  relabelStraight compactPerm (widthFastBodyProgram k hk start)

theorem widthFastCompactProgram_support (k : Nat) (hk : k ≤ 15) (start : Nat) :
    ChallengeMigration.straightWires (widthFastCompactProgram k hk start) ⊆ List.range 1634 := by
  rw [widthFastCompactProgram,straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr (compactPerm_bound v (widthFastBodyProgram_source k hk start hv))

theorem widthFastCompactProgram_slots (k : Nat) (hk : k = 12 ∨ k = 13) (start : Nat) :
    (widthFastCompactProgram k (by omega) start).gateSlots ≤ 1100000000 := by
  rw [widthFastCompactProgram,relabelStraight_slots]
  exact widthFastBodyProgram_slots k hk start

theorem widthFastCompactProgram_t (k : Nat) (hk : k ≤ 15) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((widthFastCompactProgram k hk start).instantiate read history).tCount ≤
      7 * (2162369 + 21 * (2 ^ k - 1)) := by
  rw [widthFastCompactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]
  exact widthFastBodyProgram_tBound k hk start read history

theorem widthFastCompactProgram_coherent (k : Nat) (hk : k ≤ 15) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (halias : WidthAliased k coeffs)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((widthFastCompactProgram k hk start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := (widthFastBodyProgram_coherent k hk coeffs Q hQ hn halias start history).relabel compactPerm
  have hr : CoherentlyImplementsOn
      (((widthFastBodyProgram k hk start).instantiate (readConstant coeffs Q) history).relabel compactPerm)
      ((relabelState compactPerm).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState compactPerm.symm)))
      (fun s => compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,hc,hm⟩ := h
    refine ⟨cs,hc.imp (fun _ _ hb s hs => hb s hs.1),hm⟩
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
    (by intro s _; simp [compactState,compactPull,LinearMap.comp_apply,relabelState,ket])
  rw [widthFastCompactProgram,relabelStraight_instantiate]
  exact he

private theorem fastResidue_relabel {n s e : Nat} (p : Straight n s e) (f : Wire ≃ Wire) :
    residue (relabelStraight f p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [relabelStraight,relabelTemplateGate,Gate.relabel,residue,primitivePhaseCost]
    | whenBit r v g => cases g <;> simp_all [relabelStraight,relabelTemplateGate,Gate.relabel,residue,tCost]
  | recordGate i v g p ih => cases g <;> simp_all [relabelStraight,Gate.relabel,residue,tCost]
  | measure => simp_all [relabelStraight,residue]

theorem widthFastCompactProgram_credit (k : Nat) (hk : k ≤ 15) (start : Nat) :
    WEXCredit.ProgramCredit (widthFastCompactProgram k hk start)
      (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) +
        literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2 ^ k - 1)) := by
  constructor
  · rw [widthFastCompactProgram,fastResidue_relabel]
    exact (widthFastBodyProgram_credit k hk start).1
  · rw [widthFastCompactProgram,added_relabel]
    exact (widthFastBodyProgram_credit k hk start).2

open ShorECDLP.Entrant.Schedule33.Flexible

def widthFastNarrow (k : Nat) (hk : k = 12 ∨ k = 13) : ModNarrow compactBody k where
  records := widthFastBodyRecords k
  tBound := 7 * (2162369 + 21 * (2 ^ k - 1))
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) +
    literalToffolis (normalizeW (rowAddCode probeRows)) + 21 * (2 ^ k - 1)
  program := widthFastCompactProgram k (by omega)
  coherent := by
    intro coeffs Q hQ hn halias start history
    have ha : WidthAliased k coeffs := by simpa only [WidthAliased, ModAliased, reducedAddress] using halias
    have h := widthFastCompactProgram_coherent k (by omega) coeffs Q hQ hn ha start history
    simpa only [Single.BodyValid, compactBody] using h
  wellFormed := by
    intro start
    rw [widthFastCompactProgram]
    exact (relabelStraight_wellFormed compactPerm (widthFastBodyProgram k (by omega) start)).mpr
      (widthFastBodyProgram_wellFormed k (by omega) start)
  slots := by
    intro start
    have h := widthFastCompactProgram_slots k hk start
    simpa only [compactBody] using h
  wires := by
    intro start
    have h := widthFastCompactProgram_support k (by omega) start
    simpa only [compactBody] using h
  tCount := widthFastCompactProgram_t k (by omega)
  zero := fun start => (widthFastCompactProgram_credit k (by omega) start).1
  count_eq := fun start => (widthFastCompactProgram_credit k (by omega) start).2

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.Schedule33.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution ShorECDLP.Entrant.Schedule33
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]



end
end ShorECDLP.Entrant.Schedule33.Flexible

namespace ShorECDLP.Entrant.Schedule33.FastFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] WEX.widthFastNarrow WEX.widthCompactProgram WEX.widthBodyProgram
  WEX.compile WEX.normalizeW ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount WEX.literalToffolis
  Nat.add Nat.mul AndGadget.added

def narrow12 : ModNarrow WEX.compactBody 12 := WEX.widthFastNarrow 12 (Or.inl rfl)
def narrow13 : ModNarrow WEX.compactBody 13 := WEX.widthFastNarrow 13 (Or.inr rfl)

attribute [local irreducible] narrow12 narrow13








local instance bodyInstance : Single.WindowBody := WEX.compactBody
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEX.compactBody
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
local instance programInstance : Programs bodyInstance := dualPrograms narrow12 narrow13


end
end ShorECDLP.Entrant.Schedule33.FastFinal


namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def fastSignSource : AdaptiveCircuit := literalSource (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram)

theorem fastSign_coherent : CoherentlyImplementsOn fastSignSource (Finsupp.lmapDomain ℂ ℂ signPointState) LiveReady := by
  obtain ⟨cs,aligned,mass⟩ := WEX.fastWindowSign_coherent
  exact ⟨cs,aligned.imp (fun _ _ hb s hs => hb s hs.1),mass⟩
end
end ShorECDLP.Entrant.WEXUnlookup


namespace ShorECDLP.Entrant.WEXUnlookupWidth13
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program blockProgram clearProgram addFixed WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx Nat.add Nat.mul
def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSource coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 13 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource_coherent coeffs Q hQ hn halias)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 13 coeffs) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn halias)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)
def fastBodyProgram (start : Nat) : Straight 32768 start (start+1634066) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed (start+256))).append
      (nFastProgram (start+256+1633554))).append (suffixProgram (start+256+1633554+256)))

attribute [local irreducible] fastBodyProgram

theorem fastBodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode read row)).seq fastSignSource)).seq suffixSource).run := by
  rw [fastBodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource fastSignSource (sourceCode read row) fastSignSource suffixSource
    (prefixProgram_run _ read) (nFastProgram_run _ read) (addFixed_run read _)
    (nFastProgram_run _ read) (suffixProgram_run _ read) history

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode (readConstant coeffs Q) row)).seq fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSource
    rfl
  have hr := fastBodyProgram_run_read (readConstant coeffs Q) start history
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 13 coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs,aligned,mass⟩ := fastBodySource_coherent coeffs Q hQ hn halias
  refine ⟨cs,?_,mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1633554)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row) (prefix_credit start) hl (addFixed_credit (start+256)) hr
    (suffix_credit (start+256+1633554+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row) := by
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
      · exact addFixed_wellFormed _
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
    addFixed_support _⟩,(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := row_slots_upper (start+256)
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,addFixed,castFinish_gateSlots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  omega
def fastCompactProgram (start : Nat) : Straight 32768 start (start+1634066) :=
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
    (halias : WEX.WidthAliased 13 coeffs) (start : Nat) (history : Fin start → Bool) :
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
    ccx row ≤ 2238763 := by
  have ha := WEX.literalToffolis_normalize (clearReferenceRow probeRows)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis, h0]
  rw [hrow] at ha
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := WEXUnlookupWidth13.row_ccx_relation
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 13 where
  records := 1634066
  tBound := 15671341
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row
  program := fastCompactProgram
  coherent := by
    intro coeffs Q hQ hn halias start history
    have ha : WEX.WidthAliased 13 coeffs := by simpa only [WEX.WidthAliased, ModAliased, reducedAddress] using halias
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
end ShorECDLP.Entrant.WEXUnlookupWidth13


namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program blockProgram clearProgram addFixed WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx Nat.add Nat.mul
def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSource coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource_coherent coeffs Q hQ hn halias)
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
def fastBodyProgram (start : Nat) : Straight 32768 start (start+1708178) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed (start+256))).append
      (nFastProgram (start+256+1707666))).append (suffixProgram (start+256+1707666+256)))

attribute [local irreducible] fastBodyProgram

theorem fastBodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode read row)).seq fastSignSource)).seq suffixSource).run := by
  rw [fastBodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource fastSignSource (sourceCode read row) fastSignSource suffixSource
    (prefixProgram_run _ read) (nFastProgram_run _ read) (addFixed_run read _)
    (nFastProgram_run _ read) (suffixProgram_run _ read) history

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode (readConstant coeffs Q) row)).seq fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSource
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
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1707666)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row) (prefix_credit start) hl (addFixed_credit (start+256)) hr
    (suffix_credit (start+256+1707666+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row) := by
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
      · exact addFixed_wellFormed _
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
    addFixed_support _⟩,(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := row_slots_upper (start+256)
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,addFixed,castFinish_gateSlots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  omega
def fastCompactProgram (start : Nat) : Straight 32768 start (start+1708178) :=
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
    ccx row ≤ 2312875 := by
  have ha := WEX.literalToffolis_normalize (clearReferenceRow probeRows)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis, h0]
  rw [hrow] at ha
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := WEXUnlookupWidth14.row_ccx_relation
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 14 where
  records := 1708178
  tBound := 16190125
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row
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
end ShorECDLP.Entrant.WEXUnlookupWidth14


namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit body ledger cover in
private theorem fastClearWiden {limits : Limits} {layout : DecodeLayout} {entry : StraightEntry}
    {old new : Bounds} (cert : Certificate limits layout entry old)
    (hq : old.qubits ≤ new.qubits) (ht : old.tModel ≤ new.tModel)
    (hm : old.measurements ≤ new.measurements) : Certificate limits layout entry new :=
  { cert with resources := fun Q =>
      ⟨(cert.resources Q).1.trans hq, (cert.resources Q).2.1.trans ht, (cert.resources Q).2.2.trans hm⟩ }

theorem matched_fast_clear_certificate (n14 : ModNarrow body 13) (n15 : UniformNarrow body)
    (hSupport : ledger.support.length ≤ 1634) (hSlot : body.slotBound ≤ 3000000000)
    (hR14 : n14.records ≤ 1634066) (hR15 : n15.records ≤ 1708178)
    (hReset : body.reset.length ≤ 854)
    (hT14 : n14.tBound ≤ 15671341) (hT15 : n15.tBound ≤ 16190125)
    (hC14 : n14.credit ≤ 2238763) (hC15 : n15.credit ≤ 2312875)
    (hq : (1938 : Wire) ∉ ledger.support) (hy : (1939 : Wire) ∉ 1938 :: ledger.support) :
    letI : Programs body := dualPrograms n14 n15
    Certificate officialLimits (lowerLayout 1938 entry layout) (fourEntry 1938 1939 entry)
      ⟨1636, 284640389, 550514365⟩ := by
  letI : Programs body := dualPrograms n14 n15
  have hwin : windowSlots ≤ 3000000000 := max_le le_rfl hSlot
  have hbaseS : 32 * windowSlots + 176382 ≤ officialLimits.gateSlots := by
    change 32 * windowSlots + 176382 ≤ 4000000000000000
    omega
  have hbaseR : 262143 + 20 * (dualPrograms n14 n15).records15 + 11 * (dualPrograms n14 n15).records14 +
      472 + body.reset.length + 34114 ≤ officialLimits.measurements := by
    change 262143 + 20 * n15.records + 11 * n14.records + 472 + body.reset.length + 34114 ≤ 47471340504
    omega
  have hsrc : 1835001 + 20 * (dualPrograms n14 n15).cost15 + 11 * (dualPrograms n14 n15).cost14 +
      56244 ≤ 498078496 := by
    change 1835001 + 20 * n15.tBound + 11 * n14.tBound + 56244 ≤ 498078496
    omega
  have hslots : 32 * windowSlots + 176382 + 24 * 498078496 + 2 ≤ officialLimits.gateSlots := by
    change 32 * windowSlots + 176382 + 24 * 498078496 + 2 ≤ 4000000000000000
    omega
  have hrecords : 262143 + 20 * (dualPrograms n14 n15).records15 + 11 * (dualPrograms n14 n15).records14 +
      472 + body.reset.length + 34114 + 498078496 ≤ officialLimits.measurements := by
    change 262143 + 20 * n15.records + 11 * n14.records + 472 + body.reset.length + 34114 + 498078496 ≤ 47471340504
    omega
  have raw := bounded_four_certificate (dualProgramCredit n14 n15) 1938 1939 498078496
    hbaseS hbaseR hsrc hslots hrecords hq hy
  have hcounts := (source_counts 1938 1939 498078496 hbaseS hbaseR hsrc).1
  have hcursor : entry.finalCursor ≤ 52435869 := by
    rw [source_cursor]
    change 262143 + 20 * n15.records + 11 * n14.records + 472 + body.reset.length + 34114 ≤ 52435869
    omega
  apply fastClearWiden raw
  · change ledger.support.length + 2 ≤ 1636
    omega
  · change 4 * (262143 + 20 * n15.credit + 11 * n14.credit) + 56244 + 1 ≤ 284640389
    omega
  · change entry.finalCursor + added entry.program ≤ 550514365
    omega
end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible

namespace ShorECDLP.Entrant.Schedule31Eighteen264.Flexible.FastClearFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] WEXUnlookupWidth13.compactProgram WEXUnlookupWidth14.compactProgram
  WEXUnlookupWidth13.bodyProgram WEXUnlookupWidth14.bodyProgram
  WEXUnlookupWidth13.ccx WEXUnlookupWidth14.ccx
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount
  WEX.literalToffolis WEX.normalizeW Nat.add Nat.mul AndGadget.added

def narrow13 : ModNarrow WEXUnlookup.compactBody 13 := WEXUnlookupWidth13.fastNarrow

def uniform14 : UniformNarrow WEXUnlookup.compactBody where
  records := WEXUnlookupWidth14.fastNarrow.records
  tBound := WEXUnlookupWidth14.fastNarrow.tBound
  credit := WEXUnlookupWidth14.fastNarrow.credit
  program := WEXUnlookupWidth14.fastNarrow.program
  coherent := by
    intro coeffs Q hQ hn halias start history
    have ha : ModAliased 14 coeffs := by
      simpa only [ModAliased, reducedAddress, HalfAliased] using halias
    exact WEXUnlookupWidth14.fastNarrow.coherent coeffs Q hQ hn ha start history
  wellFormed := WEXUnlookupWidth14.fastNarrow.wellFormed
  slots := WEXUnlookupWidth14.fastNarrow.slots
  wires := WEXUnlookupWidth14.fastNarrow.wires
  tCount := WEXUnlookupWidth14.fastNarrow.tCount
  zero := WEXUnlookupWidth14.fastNarrow.zero
  count_eq := WEXUnlookupWidth14.fastNarrow.count_eq

theorem n13_records : narrow13.records ≤ 1634066 := by
  exact le_rfl
theorem n14_records : uniform14.records ≤ 1708178 := by
  exact le_rfl
theorem n13_cost : narrow13.tBound ≤ 15671341 := by
  exact le_rfl
theorem n14_cost : uniform14.tBound ≤ 16190125 := by
  exact le_rfl

attribute [local irreducible] narrow13 uniform14
local instance bodyInstance : Single.WindowBody := WEXUnlookup.compactBody
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEXUnlookup.compactBody
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
local instance programInstance : Programs bodyInstance := dualPrograms narrow13 uniform14

private theorem count13_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 15671341) :
    c ≤ 2238763 := by omega
private theorem count14_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 16190125) :
    c ≤ 2312875 := by omega

theorem n13_credit : narrow13.credit ≤ 2238763 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow13.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow13.program 0) (narrow13.zero 0) read Fin.elim0
  have hc := narrow13.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count13_bound _ _ he' (ht.trans n13_cost)
theorem n14_credit : uniform14.credit ≤ 2312875 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := uniform14.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (uniform14.program 0) (uniform14.zero 0) read Fin.elim0
  have hc := uniform14.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count14_bound _ _ he' (ht.trans n14_cost)

def entry : StraightEntry := fourEntry 1938 1939 Flexible.entry
def layout : DecodeLayout := lowerLayout 1938 Flexible.entry Flexible.layout
def bounds : Bounds := ⟨1636, 284640389, 550514365⟩

theorem certificate : Certificate officialLimits layout entry bounds := by
  apply @matched_fast_clear_certificate bodyInstance resourcesInstance coverInstance narrow13 uniform14
  · change WEXUnlookup.compactSupport.length ≤ 1634
    norm_num [WEXUnlookup.compactSupport,MeasuredClear.hotBank]
  · rw [bodyInstance, WEXUnlookup.compactBody]
    decide +kernel
  · exact n13_records
  · exact n14_records
  · change WEXUnlookup.compactBody.reset.length ≤ 854
    exact WEXUnlookup.compactBody_ledger.2.2.2.le
  · exact n13_cost
  · exact n14_cost
  · exact n13_credit
  · exact n14_credit
  · change (1938 : Wire) ∉ WEXUnlookup.compactSupport
    decide +kernel
  · change (1939 : Wire) ∉ 1938 :: WEXUnlookup.compactSupport
    decide +kernel
end
end ShorECDLP.Entrant.Schedule31Eighteen264.Flexible.FastClearFinal

namespace ShorECDLP.Entrant
open Challenge

def bounds : Bounds := ⟨1636,284640389,550514365⟩
noncomputable section
def entry : StraightEntry := Schedule31Eighteen264.Flexible.FastClearFinal.entry
def layout : DecodeLayout := Schedule31Eighteen264.Flexible.FastClearFinal.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Schedule31Eighteen264.Flexible.FastClearFinal.certificate
end
end ShorECDLP.Entrant
