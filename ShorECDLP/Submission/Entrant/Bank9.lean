import ShorECDLP.Submission.Entrant.MainB

/-! Nine-bit instance of the recycled measured-clear bank.

The shipped `MeasuredClear` bank is instantiated at seven low address bits (128 unary wires,
127 split cells). For a measured clear over a `k`-bit address it costs
`(2^7 - 1) + (2^(k-7) - 1)` CCX. This file instantiates the same generic split network
(`hotNetN`, `net_run`, `HotLayout`) at nine low bits (512 unary wires, 511 cells), costing
`(2^9 - 2) + (2^(k-9) - 1)` CCX after specializing the known-one first split. Every declaration is the seven-bit one with the bank
width changed; the generic network, phase lookup and record machinery are shared. -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Replace the first split's known-one control by a Clifford copy. -/
def seededSplitNetwork : List SplitCell → Circuit
  | [] => []
  | c :: cs => [.CX c.bit c.child, .CX c.child c.parent] ++ splitNetwork cs

theorem seededSplitNetwork_run (c : SplitCell) (cs : List SplitCell) (s : BasisState)
    (hp : s c.parent = true) :
    Classical.run (seededSplitNetwork (c :: cs)) s =
      Classical.run (splitNetwork (c :: cs)) s := by
  simp only [seededSplitNetwork,splitNetwork,SplitCell.circuit,splitCircuit,Classical.run_append]
  congr 1
  funext w
  simp [Classical.run,Classical.applyGate,upd,hp]

theorem hotNetN_first (bitsN hotN : Nat → Wire) (j : Nat) :
    ∃ cs, hotNetN bitsN hotN (j+1) = ⟨bitsN 0,hotN 0,hotN 1⟩ :: cs := by
  induction j with
  | zero => exact ⟨[], by simp [hotNetN,hotLevelN]⟩
  | succ j ih =>
    obtain ⟨cs,he⟩ := ih
    exact ⟨cs ++ hotLevelN bitsN hotN (j+1), by rw [hotNetN,he,List.cons_append]⟩

theorem seededHotNet_run (bitsN hotN : Nat → Wire) (j : Nat) (s : BasisState)
    (hp : s (hotN 0) = true) :
    Classical.run (seededSplitNetwork (hotNetN bitsN hotN (j+1))) s =
    Classical.run (splitNetwork (hotNetN bitsN hotN (j+1))) s := by
  obtain ⟨cs,he⟩ := hotNetN_first bitsN hotN j
  rw [he]
  exact seededSplitNetwork_run _ _ _ hp

theorem seededSplitNetwork_hp (cs : List SplitCell) :
    Classical.HPFree (seededSplitNetwork cs) := by
  cases cs <;> simp [seededSplitNetwork,splitNetwork_hp]

theorem seededSplitNetwork_tCount (cs : List SplitCell) :
    ShorECDLP.tCount (seededSplitNetwork cs) = 7 * (cs.length-1) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    rw [seededSplitNetwork,ShorECDLP.tCount_append,splitNetwork_tCount]
    simp [ShorECDLP.tCount,ShorECDLP.tCost]

theorem seededSplitNetwork_length (cs : List SplitCell) :
    (seededSplitNetwork cs).length = 2 * cs.length := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    simp only [seededSplitNetwork,List.length_append,List.length_cons,List.length_nil,splitNetwork_length]
    omega

theorem seededSplitNetwork_frame (cs : List SplitCell) (s : BasisState) (w : Wire)
    (hw : ∀ c ∈ cs, w ≠ c.parent ∧ w ≠ c.child) :
    Classical.run (seededSplitNetwork cs) s w = s w := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have hc := hw c (by simp)
    rw [seededSplitNetwork,Classical.run_append,
      splitNetwork_frame cs _ w (fun d hd => hw d (by simp [hd]))]
    simp [Classical.run,Classical.applyGate,upd,hc.1,hc.2]

theorem seededSplitNetwork_wellFormed (cs : List SplitCell)
    (hp : ∀ c ∈ cs, c.Physical) : CircuitWellFormed (seededSplitNetwork cs) := by
  cases cs with
  | nil => simp [seededSplitNetwork,CircuitWellFormed]
  | cons c cs =>
    have hc := hp c (by simp)
    rw [seededSplitNetwork,circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed,Gate.WellFormed,hc.2.1,Ne.symm hc.2.2],
      splitNetwork_wellFormed cs (fun d hd => hp d (by simp [hd]))⟩

theorem seededSplitNetwork_within (cs : List SplitCell) (S : List Wire)
    (hp : ∀ c ∈ cs, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S) :
    circuitWires (seededSplitNetwork cs) ⊆ S := by
  cases cs with
  | nil => simp [seededSplitNetwork,circuitWires]
  | cons c cs =>
    have hc := hp c (by simp)
    rw [seededSplitNetwork,circuitWires_append]
    refine List.append_subset.mpr ⟨?_,splitNetwork_within cs S (fun d hd => hp d (by simp [hd]))⟩
    intro w hw
    simp [circuitWires,gateWires] at hw
    rcases hw with rfl | rfl | rfl
    · exact hc.1
    · exact hc.2.2
    · exact hc.2.1

/-- Nat-indexed views of the nine low address wires and the 512 unary wires. -/
def lowN9 (low : Fin 9 → Wire) (j : Nat) : Wire := if h : j < 9 then low ⟨j, h⟩ else low 0

def hotNat9 (hot : Fin 512 → Wire) (x : Nat) : Wire := if h : x < 512 then hot ⟨x, h⟩ else hot 0

/-- The low-address bank: nine address bits split into 512 unary wires. -/
def hotNetwork9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) : List SplitCell :=
  hotNetN (lowN9 low) (hotNat9 hot) 9

def slowHotPrepare9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) : Circuit :=
  [.X (hot 0)] ++ splitNetwork (hotNetwork9 low hot)

def hotPrepare9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) : Circuit :=
  [.X (hot 0)] ++ seededSplitNetwork (hotNetwork9 low hot)

def hotAddress9 (low : Fin 9 → Wire) (s : BasisState) : Nat := addrN (lowN9 low) s 9

def HotClean9 (hot : Fin 512 → Wire) (s : BasisState) : Prop := ∀ i, s (hot i) = false

theorem hotPrepare_eq9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (s : BasisState) (hs : HotClean9 hot s) :
    Classical.run (hotPrepare9 low hot) s = Classical.run (slowHotPrepare9 low hot) s := by
  rw [hotPrepare9,slowHotPrepare9,Classical.run_append,Classical.run_append]
  apply seededHotNet_run (lowN9 low) (hotNat9 hot) 8
  simp [hotNat9,Classical.run,Classical.applyGate,upd,hs 0]

theorem hotNetwork_length9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) :
    (hotNetwork9 low hot).length = 511 := by
  simp [hotNetwork9, hotNetN_length]

theorem hotLayout_of9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    HotLayout 9 (lowN9 low) (hotNat9 hot) := by
  constructor
  · intro x y hx hy he
    have hx' : x < 512 := by simpa using hx
    have hy' : y < 512 := by simpa using hy
    simp only [hotNat9, hx', hy', dite_true] at he
    exact congrArg Fin.val (hi he)
  · intro j x hj hx
    have hx' : x < 512 := by simpa using hx
    simp only [lowN9, hotNat9, hj, hx', dite_true]
    exact hd _ _

theorem mem_hotNetwork9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (c : SplitCell)
    (hc : c ∈ hotNetwork9 low hot) :
    ∃ j : Fin 9, ∃ x y : Fin 512, c = ⟨low j, hot x, hot y⟩ ∧ x ≠ y := by
  obtain ⟨j, i, hj, hi, rfl⟩ := mem_hotNetN _ _ 9 c hc
  have h2 : i + 2^j < 2^9 := pow_level_lt hj i hi
  have h2' : i + 2^j < 512 := by simpa using h2
  have h1 : i < 512 := by omega
  refine ⟨⟨j, hj⟩, ⟨i, h1⟩, ⟨i + 2^j, h2'⟩, ?_, ?_⟩
  · simp [lowN9, hotNat9, hj, h1, h2']
  · intro he
    have := congrArg Fin.val he
    have hp : 0 < 2^j := by positivity
    simp at this

theorem hotNetwork_physical9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    ∀ c ∈ hotNetwork9 low hot, c.Physical := by
  intro c hc
  obtain ⟨j, x, y, rfl, hxy⟩ := mem_hotNetwork9 low hot c hc
  exact ⟨hd j x, hd j y, fun he => hxy (hi he)⟩

theorem hotStart9 (hot : Fin 512 → Wire) (hi : Function.Injective hot)
    (s : BasisState) (hs : HotClean9 hot s) :
    ∀ x, x < 2^9 → Classical.run [.X (hot 0)] s (hotNat9 hot x) = decide (x = 0) := by
  intro x hx
  have hx' : x < 512 := by simpa using hx
  simp only [hotNat9, hx', dite_true]
  by_cases h0 : x = 0
  · subst h0
    simp [Classical.run, Classical.applyGate, upd, hs 0]
  · have hne : hot ⟨x, hx'⟩ ≠ hot 0 := fun he => h0 (congrArg Fin.val (hi he))
    simp [Classical.run, Classical.applyGate, upd, hne, hs ⟨x, hx'⟩, h0]

theorem hotNetwork_ready9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean9 hot s) :
    NetworkReady (hotNetwork9 low hot) (Classical.run [.X (hot 0)] s) :=
  (net_run 9 (lowN9 low) (hotNat9 hot) (hotLayout_of9 low hot hi hd) _ (hotStart9 hot hi s hs) 9 le_rfl).2.2

theorem hotPrepare_marker9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean9 hot s) (i : Fin 512) :
    Classical.run (hotPrepare9 low hot) s (hot i) = decide (i.val = hotAddress9 low s) := by
  have h := (net_run 9 (lowN9 low) (hotNat9 hot) (hotLayout_of9 low hot hi hd) _ (hotStart9 hot hi s hs) 9 le_rfl).1
    i.val (by simp)
  have hhot : hotNat9 hot i.val = hot i := by simp [hotNat9, i.isLt]
  rw [hhot] at h
  rw [hotPrepare_eq9 low hot s hs, slowHotPrepare9, Classical.run_append, hotNetwork9, h, hotAddress9]
  congr 2
  apply addrN_congr
  intro j hj
  have hj' : j < 9 := hj
  simp only [lowN9, hj', dite_true]
  have hne : low ⟨j, hj'⟩ ≠ hot 0 := hd _ _
  simp [Classical.run, Classical.applyGate, upd, hne]

theorem hotPrepare_frame9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (s : BasisState) (w : Wire) (hw : ∀ i, w ≠ hot i) :
    Classical.run (hotPrepare9 low hot) s w = s w := by
  rw [hotPrepare9, Classical.run_append, seededSplitNetwork_frame _ _ _ (by
    intro c hc
    obtain ⟨j, x, y, rfl, _⟩ := mem_hotNetwork9 low hot c hc
    exact ⟨hw x, hw y⟩)]
  simp [Classical.run, Classical.applyGate, upd, hw]

theorem hotAddress_bound9 (low : Fin 9 → Wire) (s : BasisState) : hotAddress9 low s < 512 := by
  have h := addrN_lt (lowN9 low) s 9
  simpa [hotAddress9] using h

attribute [irreducible] hotNetwork9

def phasePorts9 {n base : Nat} (hot : Fin 512 → Wire)
    (items : List (ClearPort n × Fin base)) : List (RecordPort n base) :=
  items.flatMap fun item => List.ofFn fun i : Fin 512 =>
    ⟨fun h => item.1.ref (512 * h + i.val), item.1.value, item.2, hot i⟩

def logicalPorts9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (hot : Fin 512 → Wire) : List (RecordPort n 2) :=
  phasePorts9 hot (data.zip (outcomes.map boolRecord))

def hotBank9 (hot : Fin 512 → Wire) : List Wire := List.ofFn hot

def fixupSource9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (hotPrepare9 low hot) .done).seq
    ((phaseLookupSource (logicalPorts9 data outcomes hot) scratch read boolHistory
      tree root paths (hotBank9 hot)).seq
      ((eraseNetworkSource (hotNetwork9 low hot)).seq (.unitary [.X (hot 0)] .done)))

def fixupProgram9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) :
    Straight n base (base + recordMeasurements (recordUnaryOps tree root paths) + 511) :=
  (literalProgram (hotPrepare9 low hot)).append
    ((literalProgram ((hotBank9 hot).map Gate.H)).append
      ((recordLookupProgram (phasePorts9 hot (data.zip refs)) scratch
        (recordUnaryOps tree root paths) base (Nat.le_refl base)).append
        ((literalProgram (Circuit.adjoint ((hotBank9 hot).map Gate.H))).append
          (castFinish (by simp [hotNetwork_length9])
            ((eraseNetwork n (hotNetwork9 low hot)
              (base + recordMeasurements (recordUnaryOps tree root paths))).append
              (literalProgram [.X (hot 0)]))))))

def measuredClear9 {n : Nat} (data : List (ClearPort n)) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    Straight n start (start + data.length + (recordMeasurements (recordUnaryOps tree root paths) + 511)) :=
  castFinish (by simp) (measureThen (R := recordMeasurements (recordUnaryOps tree root paths) + 511)
    (fun cursor refs => castFinish (by omega) (fixupProgram9 data refs low hot tree root scratch paths))
    (data.map ClearPort.target) start ([] : List (Fin start)))

def LoadedClear9 {n : Nat} (data : List (ClearPort n)) (read : ConstantBit n → Bool)
    (low : Fin 9 → Wire) (tree : UnaryActionTree) (root : Wire) (s : BasisState) : Prop :=
  ∀ p ∈ data, s p.target = (s root && decide (read (p.ref (512 * tree.routeLabel s + hotAddress9 low s)) = p.value))

theorem phasePorts_targets9 {n base : Nat} (hot : Fin 512 → Wire)
    (items : List (ClearPort n × Fin base)) :
    ∀ p ∈ phasePorts9 hot items, p.target ∈ hotBank9 hot := by
  intro p hp
  obtain ⟨item, _, hi⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem hotPrepare_hp9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) :
    Classical.HPFree (hotPrepare9 low hot) := by
  simp [hotPrepare9, seededSplitNetwork_hp]

def fixupFactor9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) : ℂ :=
  phaseLookupFactor (logicalPorts9 data outcomes hot) read boolHistory tree root
    (Classical.run (hotPrepare9 low hot) s)

theorem fixupSource_coherent9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot)
    (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank9 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths)
    (hshot : scratch ∉ hotBank9 hot) :
    CoherentlyImplementsOn (fixupSource9 data outcomes read low hot tree root scratch paths)
      (basisIdeal id (fixupFactor9 data outcomes read low hot tree root))
      (fun s => HotClean9 hot s ∧ Clean paths s) := by
  have hp := phasePorts_targets9 hot (data.zip (outcomes.map boolRecord))
  have htarget : ∀ p ∈ logicalPorts9 data outcomes hot, scratch ≠ p.target := by
    intro p hpp he
    exact hshot (he.symm ▸ hp p hpp)
  have hq := phaseLookup_coherent (logicalPorts9 data outcomes hot) scratch read boolHistory
    tree root paths (hotBank9 hot) hl (List.nodup_ofFn.mpr hi) hbank hs hp htarget
  have hpre := (CoherentlyImplementsOn.unitary (hotPrepare9 low hot)
    (fun s => HotClean9 hot s ∧ Clean paths s)).seq hq (by
      intro s hvalid
      rw [run_ket_agrees_classical _ _ (hotPrepare_hp9 low hot)]
      apply supportedOn_ket
      intro w hw
      rw [hotPrepare_frame9 low hot s w (by
        intro i he
        exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) (by simp [hw]))]
      exact hvalid.2 w hw)
  have hn := eraseNetwork_coherent (hotNetwork9 low hot) (hotNetwork_physical9 low hot hi hdlow)
  have hpost := hn.seq (CoherentlyImplementsOn.unitary [.X (hot 0)] (fun _ => True)) (by
    intro s hvalid v hv
    trivial)
  have htotal := hpre.seq hpost (by
    intro s hvalid
    simp only [LinearMap.comp_apply]
    rw [run_ket_agrees_classical _ _ (hotPrepare_hp9 low hot), basisIdeal_ket]
    apply supported_smul_state
    apply supportedOn_ket
    exact ⟨Classical.run [.X (hot 0)] s, hotNetwork_ready9 low hot hi hdlow s hvalid.1,
      by rw [hotPrepare_eq9 low hot s hvalid.1]; rfl⟩)
  rw [fixupSource9, ← adaptive_seq_assoc]
  apply htotal.congrIdeal
  intro s hvalid
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [run_ket_agrees_classical _ _ (hotPrepare_hp9 low hot), basisIdeal_ket]
  simp only [map_smul, id_eq]
  rw [run_ket_agrees_classical _ _ (inverseNetwork_hp (hotNetwork9 low hot))]
  rw [hotPrepare_eq9 low hot s hvalid.1, slowHotPrepare9, Classical.run_append,
    inverseNetwork_correct (hotNetwork9 low hot) (hotNetwork_physical9 low hot hi hdlow) _
      (hotNetwork_ready9 low hot hi hdlow s hvalid.1),
    run_ket_agrees_classical _ _ (by simp), classical_x_twice]
  simp only [basisIdeal_ket, id_eq]
  rw [fixupFactor9, hotPrepare_eq9 low hot s hvalid.1, slowHotPrepare9, Classical.run_append]

theorem phasePorts_block9 (p : ClearPort n) (m : Bool) (hot : Fin 512 → Wire)
    (read : ConstantBit n → Bool) (row root : Nat) (s : BasisState) (selected : Fin 512)
    (hm : ∀ i, s (hot i) = decide (i = selected)) :
    xorPhase root (recordTargets (phasePorts9 hot ([(p, boolRecord m)])) row read boolHistory) s =
      if m && (s root && decide (read (p.ref (512 * row + selected.val)) = p.value)) then (-1 : ℂ) else 1 := by
  rw [xorPhase_recordTargets]
  simp only [phasePorts9, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_ofFn,
    List.prod_ofFn, Function.comp_def]
  rw [Finset.prod_eq_single selected]
  · rw [hm selected]
    cases hm0 : m <;> cases hr : s root <;>
      by_cases hrd : read (p.ref (12128 * row + selected.val)) = p.value <;>
      simp [boolHistory, boolRecord]
  · intro i _ hi
    rw [hm i]
    simp [hi]
  · simp

theorem logicalPorts_cons9 (p : ClearPort n) (ps : List (ClearPort n)) (m : Bool)
    (ms : List Bool) (hot : Fin 512 → Wire) :
    logicalPorts9 (p :: ps) (m :: ms) hot = phasePorts9 hot ([(p, boolRecord m)]) ++ logicalPorts9 ps ms hot := by
  simp only [logicalPorts9, List.map_cons, List.zip_cons_cons, phasePorts9, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem phaseFactor_loaded9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root : Wire)
    (original prepared : BasisState) (selected : Fin 512)
    (hm : ∀ i, prepared (hot i) = decide (i = selected))
    (hw : ∀ p ∈ data, original p.target =
      (prepared root && decide (read (p.ref (512 * tree.routeLabel prepared + selected.val)) = p.value))) :
    phaseLookupFactor (logicalPorts9 data outcomes hot) read boolHistory tree root prepared =
      registerXPhase (data.map ClearPort.target) outcomes original := by
  unfold phaseLookupFactor
  induction data generalizing outcomes with
  | nil =>
    simp only [logicalPorts9, List.zip_nil_left, phasePorts9, List.flatMap_nil]
    simp [recordTargets, xorPhase, registerXPhase]
  | cons p ps ih =>
    cases outcomes with
    | nil =>
      simp only [logicalPorts9, List.map_nil, List.zip_nil_right, phasePorts9, List.flatMap_nil]
      simp [recordTargets, xorPhase, registerXPhase]
    | cons m ms =>
      rw [logicalPorts_cons9, recordTargets_append, xorPhase_append, phasePorts_block9 p m hot read _ root prepared selected hm,
        ih ms (fun q hq => hw q (by simp [hq]))]
      simp only [List.map_cons, registerXPhase, hw p (by simp)]

theorem phasePorts_cons9 {n base : Nat} (hot : Fin 512 → Wire)
    (item : ClearPort n × Fin base) (items : List (ClearPort n × Fin base)) :
    phasePorts9 hot (item :: items) = phasePorts9 hot ([item]) ++ phasePorts9 hot items := by
  simp only [phasePorts9, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem phasePorts_resolve9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 512 → Wire) (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) :
    recordLeafCircuit (phasePorts9 hot (data.zip refs)) scratch row control read saved =
      recordLeafCircuit (logicalPorts9 data (refs.map saved) hot) scratch row control read boolHistory := by
  induction data generalizing refs with
  | nil => rfl
  | cons p ps ih =>
    cases refs with
    | nil => rfl
    | cons r rs =>
      simp only [List.zip_cons_cons, List.map_cons]
      rw [phasePorts_cons9, logicalPorts_cons9, recordLeafCircuit_append, recordLeafCircuit_append]
      rw [ih rs]
      congr 1
      simp only [phasePorts9, List.flatMap_cons, List.flatMap_nil, List.append_nil, recordLeafCircuit]
      apply flatMap_ofFn_congr
      intro i
      cases hm : saved r <;> simp [boolRecord, boolHistory]

theorem recordSource_resolve9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 512 → Wire) (scratch : Wire) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (ops : List RecordLookupOp) :
    recordLookupSource (phasePorts9 hot (data.zip refs)) scratch read saved ops =
      recordLookupSource (logicalPorts9 data (refs.map saved) hot) scratch read boolHistory ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [recordLookupSource, ih]
    | leaf row control => simp only [recordLookupSource, phasePorts_resolve9, ih]
    | erase a b t => simp only [recordLookupSource, ih]

theorem fixupProgram_run9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (history : Fin base → Bool) :
    ((fixupProgram9 data refs low hot tree root scratch paths).instantiate read history).run =
      (fixupSource9 data (refs.map history) read low hot tree root scratch paths).run := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork9 low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).run =
      ((eraseNetworkSource (hotNetwork9 low hot)).seq (.unitary [.X (hot 0)] .done)).run := by
    rw [append_run_fixed _ _ _ _ _ (fun h => literalProgram_run [.X (hot 0)] read h),
      AdaptiveCircuit.run_seq, eraseNetwork_source, ← AdaptiveCircuit.run_seq]
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank9 hot).map Gate.H))).append
        (castFinish (f := cursor + 511) (by simp [hotNetwork_length9])
          ((eraseNetwork n (hotNetwork9 low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).run =
      (AdaptiveCircuit.unitary (Circuit.adjoint ((hotBank9 hot).map Gate.H))
        ((eraseNetworkSource (hotNetwork9 low hot)).seq (.unitary [.X (hot 0)] .done))).run := by
    rw [literalProgram_append_run]
    apply unitary_run_congr
    rw [castFinish_instantiate, hpost]
  have hsource : fixupSource9 data (refs.map history) read low hot tree root scratch paths =
      .unitary (hotPrepare9 low hot) (.unitary ((hotBank9 hot).map Gate.H)
        ((recordLookupSource (logicalPorts9 data (refs.map history) hot) scratch read boolHistory
          (recordUnaryOps tree root paths)).seq
          (.unitary (Circuit.adjoint ((hotBank9 hot).map Gate.H))
            ((eraseNetworkSource (hotNetwork9 low hot)).seq (.unitary [.X (hot 0)] .done))))) := by
    simp only [fixupSource9, phaseLookupSource, adaptive_seq_assoc, AdaptiveCircuit.seq]
  rw [hsource, fixupProgram9, literalProgram_append_run]
  apply unitary_run_congr
  rw [literalProgram_append_run]
  apply unitary_run_congr
  rw [append_run_fixed _ _ _ _ _ (fun h => htail _ h),
    AdaptiveCircuit.run_seq, recordLookup_run]
  have hh : historyPrefix (Nat.le_refl base) history = history := rfl
  rw [hh, recordSource_resolve9, ← AdaptiveCircuit.run_seq]

theorem measuredClear_run9 {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear9 data low hot tree root scratch paths start).instantiate read history).run =
      (measureResetThen (data.map ClearPort.target)
        (fun outcomes => fixupSource9 data outcomes read low hot tree root scratch paths)).run := by
  rw [measuredClear9, castFinish_instantiate,
    measureThen_run _ (fun outcomes => fixupSource9 data outcomes read low hot tree root scratch paths) read
      (by intro cursor refs h; rw [castFinish_instantiate, fixupProgram_run9])]
  rfl

theorem fixupSource_wellFormed9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank9 hot) :
    (fixupSource9 data outcomes read low hot tree root scratch paths).WellFormed := by
  rw [fixupSource9]
  apply AdaptiveCircuit.WellFormed.seq
  · refine ⟨?_, trivial⟩
    rw [hotPrepare9, circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed, Gate.WellFormed],
      seededSplitNetwork_wellFormed _ (hotNetwork_physical9 low hot hi hdlow)⟩
  · apply AdaptiveCircuit.WellFormed.seq
    · apply phaseLookupSource_wellFormed _ _ _ _ _ _ _ _ hl hs
      intro p hp he
      exact hshot (he.symm ▸ phasePorts_targets9 hot _ p hp)
    · apply AdaptiveCircuit.WellFormed.seq
      · exact eraseNetworkSource_wellFormed _ (hotNetwork_physical9 low hot hi hdlow)
      · exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], trivial⟩

theorem hotPrepare_tCount9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) :
    ShorECDLP.tCount (hotPrepare9 low hot) = 3570 := by
  rw [hotPrepare9, ShorECDLP.tCount_append, seededSplitNetwork_tCount, hotNetwork_length9]
  rfl

theorem hotPrepare_length9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) :
    (hotPrepare9 low hot).length = 1023 := by
  rw [hotPrepare9, List.length_append, seededSplitNetwork_length, hotNetwork_length9]
  rfl

theorem phasePorts_length9 {n base : Nat} (hot : Fin 512 → Wire) (items : List (ClearPort n × Fin base)) :
    (phasePorts9 hot items).length = 512 * items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rw [phasePorts_cons9, List.length_append, ih]
    simp only [phasePorts9, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.length_ofFn, List.length_nil, List.length_cons]
    omega

theorem fixupProgram_tCount9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (history : Fin base → Bool) :
    ((fixupProgram9 data refs low hot tree root scratch paths).instantiate read history).tCount =
      7 * tree.internalNodes + 3570 := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork9 low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).tCount = 0 := by
    rw [append_tCount_fixed _ _ _ _ _ (fun h => literalProgram_tCount [.X (hot 0)] read h), eraseNetwork_tCount]
    rfl
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank9 hot).map Gate.H))).append
        (castFinish (f := cursor + 511) (by simp [hotNetwork_length9])
          ((eraseNetwork n (hotNetwork9 low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).tCount = 0 := by
    rw [literalProgram_append_tCount, castFinish_instantiate, hpost, ShorECDLP.tCount_adjoint, hadamards_tCount]
  simp only [fixupProgram9, literalProgram_append_tCount]
  rw [append_tCount_fixed _ _ _ _ _ (fun h => htail _ h), recordLookup_tCount,
    (recordUnary_counts tree root paths hl 0).2.1, hotPrepare_tCount9, hadamards_tCount]
  omega

theorem measuredClear_tCount9 {n : Nat} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear9 data low hot tree root scratch paths start).instantiate read history).tCount =
      7 * (tree.internalNodes + 510) := by
  rw [measuredClear9, castFinish_instantiate, measureThen_tCount _ read (by
    intro cursor refs h
    rw [castFinish_instantiate, fixupProgram_tCount9 data refs low hot tree root scratch paths hl])]
  omega

theorem fixupProgram_slots9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) :
    (fixupProgram9 data refs low hot tree root scratch paths).gateSlots =
      2048 * min data.length refs.length * tree.leaves + 10 * tree.internalNodes + 4092 := by
  simp only [fixupProgram9, Straight.gateSlots_append, literalProgram_slots, castFinish_gateSlots]
  rw [recordLookup_slots, (recordUnary_counts tree root paths hl _).2.2, eraseNetwork_slots]
  simp only [phasePorts_length9, List.length_zip, hotPrepare_length9, hotBank9,
    List.length_ofFn, List.length_map, Circuit.adjoint, List.length_reverse,
    hotNetwork_length9, List.length_cons, List.length_nil]
  ring

theorem measuredClear_slots9 {n : Nat} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) (start : Nat) :
    (measuredClear9 data low hot tree root scratch paths start).gateSlots =
      2048 * data.length * tree.leaves + 10 * tree.internalNodes + 4092 := by
  rw [measuredClear9, castFinish_gateSlots, measureThen_slots _
    (fun k => 2048 * min data.length k * tree.leaves + 10 * tree.internalNodes + 4092)
    (by intro cursor refs; rw [castFinish_gateSlots, fixupProgram_slots9 data refs low hot tree root scratch paths hl])]
  simp

def clearSupport9 {n : Nat} (data : List (ClearPort n)) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire) : List Wire :=
  data.map ClearPort.target ++ List.ofFn low ++ hotBank9 hot ++ (root :: tree.indexWires.dedup ++ paths)

theorem hotNetwork_within9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) :
    ∀ c ∈ hotNetwork9 low hot, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S := by
  intro c hc
  obtain ⟨j, x, y, rfl, _⟩ := mem_hotNetwork9 low hot c hc
  exact ⟨hl _, hh _, hh _⟩

theorem hotPrepare_within9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) : circuitWires (hotPrepare9 low hot) ⊆ S := by
  rw [hotPrepare9, circuitWires_append]
  exact List.append_subset.mpr ⟨by simpa [circuitWires, gateWires] using hh 0,
    seededSplitNetwork_within _ S (hotNetwork_within9 low hot S hl hh)⟩

theorem fixupProgram_within9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths S : List Wire)
    (hr : root ∈ S) (hs : scratch ∈ S) (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S)
    (hi : tree.indexWires ⊆ S) (ha : paths ⊆ S) :
    NaiveChallenge.straightWires (fixupProgram9 data refs low hot tree root scratch paths) ⊆ S := by
  have hb : hotBank9 hot ⊆ S := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact hh i
  unfold fixupProgram9
  apply static_within_append
  · rw [literal_static]
    exact hotPrepare_within9 low hot S hl hh
  · apply static_within_append
    · rw [literal_static, hadamards_wires]
      exact hb
    · apply static_within_append
      · rw [recordLookup_static]
        apply recordWireList_within
        exact recordUnary_within _ scratch tree root paths S hr hs hi ha
          (fun p hp => hb (phasePorts_targets9 hot _ p hp))
      · apply static_within_append
        · rw [literal_static, hadamards_adjoint_wires]
          intro w hw
          exact hb (List.mem_reverse.mp hw)
        · rw [static_cast]
          apply static_within_append (eraseNetwork_within n _ _ S (hotNetwork_within9 low hot S hl hh))
          rw [literal_static]
          simpa [circuitWires, gateWires] using hh 0

/-- The generic row reference is exactly the physical little-endian address. -/
theorem splitAddress_value9 (low : Fin 9 → Wire) (high : List Wire) (s : BasisState) :
    512 * (tableAddressTree high 0 1).routeLabel s + hotAddress9 low s =
      tableAddressValue ([lowN9 low 0, lowN9 low 1, lowN9 low 2, lowN9 low 3, lowN9 low 4, lowN9 low 5,
        lowN9 low 6, lowN9 low 7, lowN9 low 8] ++ high) s := by
  simp only [tableAddressTree_route, zero_add, one_mul, List.cons_append, List.nil_append,
    tableAddressValue, hotAddress9, addrN]
  ring

/-- The measured data bank is available to the phase fixup after reset. -/
theorem fixupFactor_recycled9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank9 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (s : BasisState) (hs : Clean paths s ∧ LoadedClear9 data read low tree root s) :
    fixupFactor9 data outcomes read low hot tree root (clearRegister (data.map ClearPort.target) s) =
      registerXPhase (data.map ClearPort.target) outcomes s := by
  let cleared := clearRegister (data.map ClearPort.target) s
  let prepared := Classical.run (hotPrepare9 low hot) cleared
  have hhot : HotClean9 hot cleared := by
    intro i
    change clearRegister (data.map ClearPort.target) s (hot i) = false
    exact clearRegister_clean _ s _ (hh i)
  have hlow : ∀ i, cleared (low i) = s (low i) := by
    intro i
    have hw : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact clearRegister_frame _ _ _ (ha _ (by simp only [List.mem_cons, List.mem_append, hw, or_true, true_or]))
  have haddr : hotAddress9 low cleared = hotAddress9 low s :=
    addrN_congr _ _ _ 9 (fun j hj => by simp only [lowN9, hj, dite_true]; exact hlow _)
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = s w := by
    change Classical.run (hotPrepare9 low hot) cleared w = s w
    rw [hotPrepare_frame9 low hot cleared w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)]
    apply clearRegister_frame
    apply ha
    simp only [List.mem_cons, List.mem_append] at hw ⊢
    tauto
  have hroute : tree.routeLabel prepared = tree.routeLabel s := by
    apply tree.routeLabel_congr prepared s
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 512 := ⟨hotAddress9 low s, hotAddress_bound9 low s⟩
  apply phaseFactor_loaded9 data outcomes read hot tree root s prepared selected
  · intro i
    simpa only [Fin.ext_iff, haddr] using hotPrepare_marker9 low hot hi hdlow cleared hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hs.2 p hp

theorem measuredClear_recycled_coherent9 {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank9 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank9 hot)
    (hn : (data.map ClearPort.target).Nodup)
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((measuredClear9 data low hot tree root scratch paths start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (data.map ClearPort.target)))
      (fun s => Clean paths s ∧ LoadedClear9 data read low tree root s) := by
  unfold CoherentlyImplementsOn
  rw [measuredClear_run9]
  apply measureResetThen_coherent (data.map ClearPort.target)
    (fun outcomes => fixupSource9 data outcomes read low hot tree root scratch paths)
    (fun outcomes => basisIdeal id (fixupFactor9 data outcomes read low hot tree root))
    (fun _ s => HotClean9 hot s ∧ Clean paths s)
    (fun s => Clean paths s ∧ LoadedClear9 data read low tree root s)
    (clearRegister (data.map ClearPort.target)) hn (witness := zeroBasisState)
  · intro outcomes hout
    exact fixupSource_wellFormed9 data outcomes read low hot tree root scratch paths hl hi hdlow hs hshot
  · intro outcomes
    exact fixupSource_coherent9 data outcomes read low hot tree root scratch paths hl hi hdlow hbank hs hshot
  · intro outcomes hout s hvalid
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact clearRegister_clean _ s _ (hh i)
    · intro w hw
      rw [clearRegister_frame _ _ _ (ha w (by simp [hw]))]
      exact hvalid.1 w hw
    · rw [basisIdeal_ket, fixupFactor_recycled9 data outcomes read low hot tree root paths hi hdlow hbank ha hh s hvalid]
      rfl
  · simp [Clean, LoadedClear9, zeroBasisState]

end
end ShorECDLP.Entrant.MeasuredClear

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem fixupProgram_wellFormed9 {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank9 hot) :
    (fixupProgram9 data refs low hot tree root scratch paths).WellFormed := by
  have hp := hotNetwork_physical9 low hot hi hdlow
  have hH (ws : List Wire) : CircuitWellFormed (ws.map Gate.H) := by
    intro g hg; obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg; trivial
  unfold fixupProgram9
  apply straight_append_wellFormed
  · apply literalProgram_wellFormed
    rw [hotPrepare9,circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed,Gate.WellFormed],seededSplitNetwork_wellFormed _ hp⟩
  · apply straight_append_wellFormed
    · exact literalProgram_wellFormed _ (hH _)
    · apply straight_append_wellFormed
      · apply recordLookupProgram_wellFormed
        apply recordUnary_physical _ _ _ _ _ hl
        intro row c hc
        refine ⟨?_,?_⟩
        · intro he; apply hs; subst c; simp only [List.mem_cons,List.mem_append] at hc ⊢; tauto
        · intro p hpm he
          exact hshot (he.symm ▸ phasePorts_targets9 hot _ p hpm)
      · apply straight_append_wellFormed
        · exact literalProgram_wellFormed _ ((circuitWellFormed_adjoint _).mpr (hH _))
        · rw [castFinish_wellFormed]
          exact straight_append_wellFormed _ _ (eraseNetwork_wellFormed n _ hp _)
            (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed]))

theorem measuredClear_wellFormed9 {n} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank9 hot) (start : Nat) :
    (measuredClear9 data low hot tree root scratch paths start).WellFormed := by
  rw [measuredClear9,castFinish_wellFormed]
  apply measureThen_wellFormed
  intro cursor refs
  rw [castFinish_wellFormed]
  exact fixupProgram_wellFormed9 data refs low hot tree root scratch paths hl hi hdlow hs hshot

open AndGadget in
 theorem fixupProgram_residue9 {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) :
    residue (fixupProgram9 data refs low hot tree root scratch paths) = 0 := by
  unfold fixupProgram9
  rw [residue_append,residue_literal_HPFree _ (hotPrepare_hp9 low hot)]
  simp only [residue_append,residue_literal,residue_cast,eraseNetwork_residue,
    recordLookup_residue _ _ _ _ _ (recordUnary_phaseFree tree root paths),Nat.zero_add]
  simp [List.map_map,Function.comp_def,primitivePhaseCost,Circuit.adjoint,List.map_reverse,Gate.adjoint]

open AndGadget in
 theorem measuredClear_residue9 {n} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    residue (measuredClear9 data low hot tree root scratch paths start) = 0 := by
  rw [measuredClear9,residue_cast]
  apply measureThen_residue
  intro cursor refs
  rw [residue_cast]
  exact fixupProgram_residue9 data refs low hot tree root scratch paths

theorem measuredClear_static9 {n : Nat} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hsc : scratch ∈ data.map ClearPort.target)
    (start : Nat) :
    NaiveChallenge.straightWires (measuredClear9 data low hot tree root scratch paths start) ⊆
      clearSupport9 data low hot tree root paths := by
  rw [measuredClear9, static_cast]
  apply measureThen_within _ _ (by
    intro cursor refs
    rw [static_cast]
    apply fixupProgram_within9
    · simp [clearSupport9]
    · simp [clearSupport9, hsc]
    · intro i
      have hm : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport9, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro i
      have hm : hot i ∈ hotBank9 hot := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport9, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro w hw
      simp [clearSupport9, hw]
    · intro w hw
      simp [clearSupport9, hw])
  intro w hw
  simp [clearSupport9, hw]

end
end ShorECDLP.Entrant.MeasuredClear
