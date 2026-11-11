import ShorECDLP.Submission.Entrant.ParityBank
import ShorECDLP.Submission.Entrant.Prefix
import ShorECDLP.Submission.Entrant.Bank9
import ShorECDLP.Submission.Entrant.TightSupport

/-! Balanced eight-bit bank for the sixteen-bit clears of the wide (seventeen-bit) window rows.

Every masked clear of a wide row is a recycled measured clear over the sixteen address bits
`855..869, 871`. The shipped bank splits them seven low / nine high, costing
`(2^7 - 1) + (2^9 - 1) = 638` CCX per clear. This file instantiates the generic split network at
eight low bits (256 unary wires, 255 cells) with an eight-wire high tree, costing `254 + 255 = 502` after specializing the known-one first split.

The 256 hot wires are the first 256 cleared targets (`headD + i`), and the phase scratch is the
ninth wire `14840` of the old clear path bank, which the eight-level tree no longer uses. The
scratch is only a dirty ancilla of `mixedCircuit`, so it need not be a cleared target.

Everything bank-independent (site geometry, swap networks, select code, frame, sign) is imported;
only the declarations whose definitions contain the clear are re-instantiated below. -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Nat-indexed views of the eight low address wires and the 256 unary wires. -/
def lowN8 (low : Fin 8 → Wire) (j : Nat) : Wire := if h : j < 8 then low ⟨j, h⟩ else low 0

def hotNat8 (hot : Fin 256 → Wire) (x : Nat) : Wire := if h : x < 256 then hot ⟨x, h⟩ else hot 0

/-- The low-address bank: eight address bits split into 256 unary wires. -/
def hotNetwork8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) : List SplitCell :=
  hotNetN (lowN8 low) (hotNat8 hot) 8

def slowHotPrepare8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) : Circuit :=
  [.X (hot 0)] ++ splitNetwork (hotNetwork8 low hot)

def hotPrepare8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) : Circuit :=
  [.X (hot 0)] ++ ParityBank.parityNet (lowN8 low) (hotNat8 hot) 8

def hotAddress8 (low : Fin 8 → Wire) (s : BasisState) : Nat := addrN (lowN8 low) s 8

def HotClean8 (hot : Fin 256 → Wire) (s : BasisState) : Prop := ∀ i, s (hot i) = false

theorem hotNetwork_length8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) :
    (hotNetwork8 low hot).length = 255 := by
  simp [hotNetwork8, hotNetN_length]

theorem hotLayout_of8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    HotLayout 8 (lowN8 low) (hotNat8 hot) := by
  constructor
  · intro x y hx hy he
    have hx' : x < 256 := by simpa using hx
    have hy' : y < 256 := by simpa using hy
    simp only [hotNat8, hx', hy', dite_true] at he
    exact congrArg Fin.val (hi he)
  · intro j x hj hx
    have hx' : x < 256 := by simpa using hx
    simp only [lowN8, hotNat8, hj, hx', dite_true]
    exact hd _ _

theorem mem_hotNetwork8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (c : SplitCell)
    (hc : c ∈ hotNetwork8 low hot) :
    ∃ j : Fin 8, ∃ x y : Fin 256, c = ⟨low j, hot x, hot y⟩ ∧ x ≠ y := by
  obtain ⟨j, i, hj, hi, rfl⟩ := mem_hotNetN _ _ 8 c hc
  have h2 : i + 2^j < 2^8 := pow_level_lt hj i hi
  have h2' : i + 2^j < 256 := by simpa using h2
  have h1 : i < 256 := by omega
  refine ⟨⟨j, hj⟩, ⟨i, h1⟩, ⟨i + 2^j, h2'⟩, ?_, ?_⟩
  · simp [lowN8, hotNat8, hj, h1, h2']
  · intro he
    have := congrArg Fin.val he
    have hp : 0 < 2^j := by positivity
    simp at this

theorem hotNetwork_physical8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    ∀ c ∈ hotNetwork8 low hot, c.Physical := by
  intro c hc
  obtain ⟨j, x, y, rfl, hxy⟩ := mem_hotNetwork8 low hot c hc
  exact ⟨hd j x, hd j y, fun he => hxy (hi he)⟩

theorem hotStart8 (hot : Fin 256 → Wire) (hi : Function.Injective hot)
    (s : BasisState) (hs : HotClean8 hot s) :
    ∀ x, x < 2^8 → Classical.run [.X (hot 0)] s (hotNat8 hot x) = decide (x = 0) := by
  intro x hx
  have hx' : x < 256 := by simpa using hx
  simp only [hotNat8, hx', dite_true]
  by_cases h0 : x = 0
  · subst h0
    simp [Classical.run, Classical.applyGate, upd, hs 0]
  · have hne : hot ⟨x, hx'⟩ ≠ hot 0 := fun he => h0 (congrArg Fin.val (hi he))
    simp [Classical.run, Classical.applyGate, upd, hne, hs ⟨x, hx'⟩, h0]

theorem hotPrepare_eq8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j,low i≠hot j)
    (s : BasisState) (hs : HotClean8 hot s) :
    Classical.run (hotPrepare8 low hot) s=Classical.run (slowHotPrepare8 low hot) s := by
  rw [hotPrepare8,slowHotPrepare8,Classical.run_append,Classical.run_append,hotNetwork8]
  exact ParityBank.parityNet_eq 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hd)
    _ (hotStart8 hot hi s hs) 8 le_rfl

theorem hotNetwork_ready8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean8 hot s) :
    NetworkReady (hotNetwork8 low hot) (Classical.run [.X (hot 0)] s) :=
  (net_run 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hd) _ (hotStart8 hot hi s hs) 8 le_rfl).2.2

theorem hotPrepare_marker8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean8 hot s) (i : Fin 256) :
    Classical.run (hotPrepare8 low hot) s (hot i) = decide (i.val = hotAddress8 low s) := by
  have h := (net_run 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hd) _ (hotStart8 hot hi s hs) 8 le_rfl).1
    i.val (by simp)
  have hhot : hotNat8 hot i.val = hot i := by simp [hotNat8, i.isLt]
  rw [hhot] at h
  rw [hotPrepare_eq8 low hot hi hd s hs, slowHotPrepare8, Classical.run_append, hotNetwork8, h, hotAddress8]
  congr 2
  apply addrN_congr
  intro j hj
  have hj' : j < 8 := hj
  simp only [lowN8, hj', dite_true]
  have hne : low ⟨j, hj'⟩ ≠ hot 0 := hd _ _
  simp [Classical.run, Classical.applyGate, upd, hne]

theorem hotPrepare_frame8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (s : BasisState) (w : Wire) (hw : ∀ i,w≠hot i) :
    Classical.run (hotPrepare8 low hot) s w=s w := by
  rw [hotPrepare8,Classical.run_append,ParityBank.parityNet_frame 8 _ _ 8 le_rfl _ w (by
    intro x hx
    have hx' : x<256 := by simpa using hx
    simpa only [hotNat8,hx',dite_true] using hw ⟨x,hx'⟩)]
  simp [Classical.run,Classical.applyGate,upd,hw]

theorem hotAddress_bound8 (low : Fin 8 → Wire) (s : BasisState) : hotAddress8 low s < 256 := by
  have h := addrN_lt (lowN8 low) s 8
  simpa [hotAddress8] using h

attribute [irreducible] hotNetwork8

def phasePorts8 {n base : Nat} (hot : Fin 256 → Wire)
    (items : List (ClearPort n × Fin base)) : List (RecordPort n base) :=
  items.flatMap fun item => List.ofFn fun i : Fin 256 =>
    ⟨fun h => item.1.ref (256 * h + i.val), item.1.value, item.2, hot i⟩

def logicalPorts8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (hot : Fin 256 → Wire) : List (RecordPort n 2) :=
  phasePorts8 hot (data.zip (outcomes.map boolRecord))

def hotBank8 (hot : Fin 256 → Wire) : List Wire := List.ofFn hot

def fixupSource8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (hotPrepare8 low hot) .done).seq
    ((phaseLookupSource (logicalPorts8 data outcomes hot) scratch read boolHistory
      tree root paths (hotBank8 hot)).seq
      ((eraseNetworkSource (hotNetwork8 low hot)).seq (.unitary [.X (hot 0)] .done)))

def fixupProgram8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) :
    Straight n base (base + recordMeasurements (recordUnaryOps tree root paths) + 255) :=
  (literalProgram (hotPrepare8 low hot)).append
    ((literalProgram ((hotBank8 hot).map Gate.H)).append
      ((recordLookupProgram (phasePorts8 hot (data.zip refs)) scratch
        (recordUnaryOps tree root paths) base (Nat.le_refl base)).append
        ((literalProgram (Circuit.adjoint ((hotBank8 hot).map Gate.H))).append
          (castFinish (by simp [hotNetwork_length8])
            ((eraseNetwork n (hotNetwork8 low hot)
              (base + recordMeasurements (recordUnaryOps tree root paths))).append
              (literalProgram [.X (hot 0)]))))))

def measuredClear8 {n : Nat} (data : List (ClearPort n)) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    Straight n start (start + data.length + (recordMeasurements (recordUnaryOps tree root paths) + 255)) :=
  castFinish (by simp) (measureThen (R := recordMeasurements (recordUnaryOps tree root paths) + 255)
    (fun cursor refs => castFinish (by omega) (fixupProgram8 data refs low hot tree root scratch paths))
    (data.map ClearPort.target) start ([] : List (Fin start)))

def LoadedClear8 {n : Nat} (data : List (ClearPort n)) (read : ConstantBit n → Bool)
    (low : Fin 8 → Wire) (tree : UnaryActionTree) (root : Wire) (s : BasisState) : Prop :=
  ∀ p ∈ data, s p.target = (s root && decide (read (p.ref (256 * tree.routeLabel s + hotAddress8 low s)) = p.value))

theorem phasePorts_targets8 {n base : Nat} (hot : Fin 256 → Wire)
    (items : List (ClearPort n × Fin base)) :
    ∀ p ∈ phasePorts8 hot items, p.target ∈ hotBank8 hot := by
  intro p hp
  obtain ⟨item, _, hi⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem hotPrepare_hp8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) :
    Classical.HPFree (hotPrepare8 low hot) := by
  simp [hotPrepare8, ParityBank.parityNet_hp]

def fixupFactor8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) : ℂ :=
  phaseLookupFactor (logicalPorts8 data outcomes hot) read boolHistory tree root
    (Classical.run (hotPrepare8 low hot) s)

theorem fixupSource_coherent8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot)
    (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths)
    (hshot : scratch ∉ hotBank8 hot) :
    CoherentlyImplementsOn (fixupSource8 data outcomes read low hot tree root scratch paths)
      (basisIdeal id (fixupFactor8 data outcomes read low hot tree root))
      (fun s => HotClean8 hot s ∧ Clean paths s) := by
  have hp := phasePorts_targets8 hot (data.zip (outcomes.map boolRecord))
  have htarget : ∀ p ∈ logicalPorts8 data outcomes hot, scratch ≠ p.target := by
    intro p hpp he
    exact hshot (he.symm ▸ hp p hpp)
  have hq := phaseLookup_coherent (logicalPorts8 data outcomes hot) scratch read boolHistory
    tree root paths (hotBank8 hot) hl (List.nodup_ofFn.mpr hi) hbank hs hp htarget
  have hpre := (CoherentlyImplementsOn.unitary (hotPrepare8 low hot)
    (fun s => HotClean8 hot s ∧ Clean paths s)).seq hq (by
      intro s hvalid
      rw [run_ket_agrees_classical _ _ (hotPrepare_hp8 low hot)]
      apply supportedOn_ket
      intro w hw
      rw [hotPrepare_frame8 low hot s w (by
        intro i he
        exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) (by simp [hw]))]
      exact hvalid.2 w hw)
  have hn := eraseNetwork_coherent (hotNetwork8 low hot) (hotNetwork_physical8 low hot hi hdlow)
  have hpost := hn.seq (CoherentlyImplementsOn.unitary [.X (hot 0)] (fun _ => True)) (by
    intro s hvalid v hv
    trivial)
  have htotal := hpre.seq hpost (by
    intro s hvalid
    simp only [LinearMap.comp_apply]
    rw [run_ket_agrees_classical _ _ (hotPrepare_hp8 low hot), basisIdeal_ket]
    apply supported_smul_state
    apply supportedOn_ket
    exact ⟨Classical.run [.X (hot 0)] s, hotNetwork_ready8 low hot hi hdlow s hvalid.1,
      by rw [hotPrepare_eq8 low hot hi hdlow s hvalid.1]; rfl⟩)
  rw [fixupSource8, ← adaptive_seq_assoc]
  apply htotal.congrIdeal
  intro s hvalid
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [run_ket_agrees_classical _ _ (hotPrepare_hp8 low hot), basisIdeal_ket]
  simp only [map_smul, id_eq]
  rw [run_ket_agrees_classical _ _ (inverseNetwork_hp (hotNetwork8 low hot))]
  rw [hotPrepare_eq8 low hot hi hdlow s hvalid.1, slowHotPrepare8, Classical.run_append,
    inverseNetwork_correct (hotNetwork8 low hot) (hotNetwork_physical8 low hot hi hdlow) _
      (hotNetwork_ready8 low hot hi hdlow s hvalid.1),
    run_ket_agrees_classical _ _ (by simp), classical_x_twice]
  simp only [basisIdeal_ket, id_eq]
  rw [fixupFactor8, hotPrepare_eq8 low hot hi hdlow s hvalid.1, slowHotPrepare8, Classical.run_append]

theorem phasePorts_block8 (p : ClearPort n) (m : Bool) (hot : Fin 256 → Wire)
    (read : ConstantBit n → Bool) (row root : Nat) (s : BasisState) (selected : Fin 256)
    (hm : ∀ i, s (hot i) = decide (i = selected)) :
    xorPhase root (recordTargets (phasePorts8 hot ([(p, boolRecord m)])) row read boolHistory) s =
      if m && (s root && decide (read (p.ref (256 * row + selected.val)) = p.value)) then (-1 : ℂ) else 1 := by
  rw [xorPhase_recordTargets]
  simp only [phasePorts8, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_ofFn,
    List.prod_ofFn, Function.comp_def]
  rw [Finset.prod_eq_single selected]
  · rw [hm selected]
    cases hm0 : m <;> cases hr : s root <;>
      by_cases hrd : read (p.ref (256 * row + selected.val)) = p.value <;>
      simp [boolHistory, boolRecord]
  · intro i _ hi
    rw [hm i]
    simp [hi]
  · simp

theorem logicalPorts_cons8 (p : ClearPort n) (ps : List (ClearPort n)) (m : Bool)
    (ms : List Bool) (hot : Fin 256 → Wire) :
    logicalPorts8 (p :: ps) (m :: ms) hot = phasePorts8 hot ([(p, boolRecord m)]) ++ logicalPorts8 ps ms hot := by
  simp only [logicalPorts8, List.map_cons, List.zip_cons_cons, phasePorts8, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem phaseFactor_loaded8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root : Wire)
    (original prepared : BasisState) (selected : Fin 256)
    (hm : ∀ i, prepared (hot i) = decide (i = selected))
    (hw : ∀ p ∈ data, original p.target =
      (prepared root && decide (read (p.ref (256 * tree.routeLabel prepared + selected.val)) = p.value))) :
    phaseLookupFactor (logicalPorts8 data outcomes hot) read boolHistory tree root prepared =
      registerXPhase (data.map ClearPort.target) outcomes original := by
  unfold phaseLookupFactor
  induction data generalizing outcomes with
  | nil =>
    simp only [logicalPorts8, List.zip_nil_left, phasePorts8, List.flatMap_nil]
    simp [recordTargets, xorPhase, registerXPhase]
  | cons p ps ih =>
    cases outcomes with
    | nil =>
      simp only [logicalPorts8, List.map_nil, List.zip_nil_right, phasePorts8, List.flatMap_nil]
      simp [recordTargets, xorPhase, registerXPhase]
    | cons m ms =>
      rw [logicalPorts_cons8, recordTargets_append, xorPhase_append, phasePorts_block8 p m hot read _ root prepared selected hm,
        ih ms (fun q hq => hw q (by simp [hq]))]
      simp only [List.map_cons, registerXPhase, hw p (by simp)]

theorem phasePorts_cons8 {n base : Nat} (hot : Fin 256 → Wire)
    (item : ClearPort n × Fin base) (items : List (ClearPort n × Fin base)) :
    phasePorts8 hot (item :: items) = phasePorts8 hot ([item]) ++ phasePorts8 hot items := by
  simp only [phasePorts8, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem phasePorts_resolve8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 256 → Wire) (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) :
    recordLeafCircuit (phasePorts8 hot (data.zip refs)) scratch row control read saved =
      recordLeafCircuit (logicalPorts8 data (refs.map saved) hot) scratch row control read boolHistory := by
  induction data generalizing refs with
  | nil => rfl
  | cons p ps ih =>
    cases refs with
    | nil => rfl
    | cons r rs =>
      simp only [List.zip_cons_cons, List.map_cons]
      rw [phasePorts_cons8, logicalPorts_cons8, recordLeafCircuit_append, recordLeafCircuit_append]
      rw [ih rs]
      congr 1
      simp only [phasePorts8, List.flatMap_cons, List.flatMap_nil, List.append_nil, recordLeafCircuit]
      apply flatMap_ofFn_congr
      intro i
      cases hm : saved r <;> simp [boolRecord, boolHistory]

theorem recordSource_resolve8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 256 → Wire) (scratch : Wire) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (ops : List RecordLookupOp) :
    recordLookupSource (phasePorts8 hot (data.zip refs)) scratch read saved ops =
      recordLookupSource (logicalPorts8 data (refs.map saved) hot) scratch read boolHistory ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [recordLookupSource, ih]
    | leaf row control => simp only [recordLookupSource, phasePorts_resolve8, ih]
    | erase a b t => simp only [recordLookupSource, ih]

theorem fixupProgram_run8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (history : Fin base → Bool) :
    ((fixupProgram8 data refs low hot tree root scratch paths).instantiate read history).run =
      (fixupSource8 data (refs.map history) read low hot tree root scratch paths).run := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork8 low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).run =
      ((eraseNetworkSource (hotNetwork8 low hot)).seq (.unitary [.X (hot 0)] .done)).run := by
    rw [append_run_fixed _ _ _ _ _ (fun h => literalProgram_run [.X (hot 0)] read h),
      AdaptiveCircuit.run_seq, eraseNetwork_source, ← AdaptiveCircuit.run_seq]
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank8 hot).map Gate.H))).append
        (castFinish (f := cursor + 255) (by simp [hotNetwork_length8])
          ((eraseNetwork n (hotNetwork8 low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).run =
      (AdaptiveCircuit.unitary (Circuit.adjoint ((hotBank8 hot).map Gate.H))
        ((eraseNetworkSource (hotNetwork8 low hot)).seq (.unitary [.X (hot 0)] .done))).run := by
    rw [literalProgram_append_run]
    apply unitary_run_congr
    rw [castFinish_instantiate, hpost]
  have hsource : fixupSource8 data (refs.map history) read low hot tree root scratch paths =
      .unitary (hotPrepare8 low hot) (.unitary ((hotBank8 hot).map Gate.H)
        ((recordLookupSource (logicalPorts8 data (refs.map history) hot) scratch read boolHistory
          (recordUnaryOps tree root paths)).seq
          (.unitary (Circuit.adjoint ((hotBank8 hot).map Gate.H))
            ((eraseNetworkSource (hotNetwork8 low hot)).seq (.unitary [.X (hot 0)] .done))))) := by
    simp only [fixupSource8, phaseLookupSource, adaptive_seq_assoc, AdaptiveCircuit.seq]
  rw [hsource, fixupProgram8, literalProgram_append_run]
  apply unitary_run_congr
  rw [literalProgram_append_run]
  apply unitary_run_congr
  rw [append_run_fixed _ _ _ _ _ (fun h => htail _ h),
    AdaptiveCircuit.run_seq, recordLookup_run]
  have hh : historyPrefix (Nat.le_refl base) history = history := rfl
  rw [hh, recordSource_resolve8, ← AdaptiveCircuit.run_seq]

theorem measuredClear_run8 {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear8 data low hot tree root scratch paths start).instantiate read history).run =
      (measureResetThen (data.map ClearPort.target)
        (fun outcomes => fixupSource8 data outcomes read low hot tree root scratch paths)).run := by
  rw [measuredClear8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun outcomes => fixupSource8 data outcomes read low hot tree root scratch paths) read
      (by intro cursor refs h; rw [castFinish_instantiate, fixupProgram_run8])]
  rfl

theorem fixupSource_wellFormed8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank8 hot) :
    (fixupSource8 data outcomes read low hot tree root scratch paths).WellFormed := by
  rw [fixupSource8]
  apply AdaptiveCircuit.WellFormed.seq
  · refine ⟨?_, trivial⟩
    rw [hotPrepare8, circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed, Gate.WellFormed],
      ParityBank.parityNet_wellFormed 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hdlow) 8 le_rfl⟩
  · apply AdaptiveCircuit.WellFormed.seq
    · apply phaseLookupSource_wellFormed _ _ _ _ _ _ _ _ hl hs
      intro p hp he
      exact hshot (he.symm ▸ phasePorts_targets8 hot _ p hp)
    · apply AdaptiveCircuit.WellFormed.seq
      · exact eraseNetworkSource_wellFormed _ (hotNetwork_physical8 low hot hi hdlow)
      · exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], trivial⟩

theorem hotPrepare_tCount8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) :
    ShorECDLP.tCount (hotPrepare8 low hot)=1729 := by
  have h := ParityBank.parityNet_tCount (lowN8 low) (hotNat8 hot) 8
  rw [hotPrepare8,ShorECDLP.tCount_append]
  change 0+ShorECDLP.tCount (ParityBank.parityNet (lowN8 low) (hotNat8 hot) 8)=1729
  norm_num at h
  omega

theorem hotPrepare_length8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) :
    (hotPrepare8 low hot).length=758 := by
  have h := ParityBank.parityNet_length (lowN8 low) (hotNat8 hot) 8
  rw [hotPrepare8,List.length_append]
  simp only [List.length_cons,List.length_nil]
  norm_num at h
  omega

theorem phasePorts_length8 {n base : Nat} (hot : Fin 256 → Wire) (items : List (ClearPort n × Fin base)) :
    (phasePorts8 hot items).length = 256 * items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rw [phasePorts_cons8, List.length_append, ih]
    simp only [phasePorts8, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.length_ofFn, List.length_nil, List.length_cons]
    omega

theorem fixupProgram_tCount8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (history : Fin base → Bool) :
    ((fixupProgram8 data refs low hot tree root scratch paths).instantiate read history).tCount =
      7 * tree.internalNodes + 1729 := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork8 low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).tCount = 0 := by
    rw [append_tCount_fixed _ _ _ _ _ (fun h => literalProgram_tCount [.X (hot 0)] read h), eraseNetwork_tCount]
    rfl
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank8 hot).map Gate.H))).append
        (castFinish (f := cursor + 255) (by simp [hotNetwork_length8])
          ((eraseNetwork n (hotNetwork8 low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).tCount = 0 := by
    rw [literalProgram_append_tCount, castFinish_instantiate, hpost, ShorECDLP.tCount_adjoint, hadamards_tCount]
  simp only [fixupProgram8, literalProgram_append_tCount]
  rw [append_tCount_fixed _ _ _ _ _ (fun h => htail _ h), recordLookup_tCount,
    (recordUnary_counts tree root paths hl 0).2.1, hotPrepare_tCount8, hadamards_tCount]
  omega

theorem measuredClear_tCount8 {n : Nat} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear8 data low hot tree root scratch paths start).instantiate read history).tCount =
      7 * (tree.internalNodes + 247) := by
  rw [measuredClear8, castFinish_instantiate, measureThen_tCount _ read (by
    intro cursor refs h
    rw [castFinish_instantiate, fixupProgram_tCount8 data refs low hot tree root scratch paths hl])]
  omega

theorem fixupProgram_slots8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) :
    (fixupProgram8 data refs low hot tree root scratch paths).gateSlots =
      1024 * min data.length refs.length * tree.leaves + 10 * tree.internalNodes + 2291 := by
  simp only [fixupProgram8, Straight.gateSlots_append, literalProgram_slots, castFinish_gateSlots]
  rw [recordLookup_slots, (recordUnary_counts tree root paths hl _).2.2, eraseNetwork_slots]
  simp only [phasePorts_length8, List.length_zip, hotPrepare_length8, hotBank8,
    List.length_ofFn, List.length_map, Circuit.adjoint, List.length_reverse,
    hotNetwork_length8, List.length_cons, List.length_nil]
  ring

theorem measuredClear_slots8 {n : Nat} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) (start : Nat) :
    (measuredClear8 data low hot tree root scratch paths start).gateSlots =
      1024 * data.length * tree.leaves + 10 * tree.internalNodes + 2291 := by
  rw [measuredClear8, castFinish_gateSlots, measureThen_slots _
    (fun k => 1024 * min data.length k * tree.leaves + 10 * tree.internalNodes + 2291)
    (by intro cursor refs; rw [castFinish_gateSlots, fixupProgram_slots8 data refs low hot tree root scratch paths hl])]
  simp

/-- Unlike the seven- and nine-bit instances the scratch wire is not required to be a cleared
target: `mixedCircuit` uses it as a dirty ancilla, so it is listed separately. -/
def clearSupport8 {n : Nat} (data : List (ClearPort n)) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) : List Wire :=
  data.map ClearPort.target ++ List.ofFn low ++ hotBank8 hot ++ (root :: tree.indexWires.dedup ++ paths) ++ [scratch]

theorem hotNetwork_within8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) :
    ∀ c ∈ hotNetwork8 low hot, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S := by
  intro c hc
  obtain ⟨j, x, y, rfl, _⟩ := mem_hotNetwork8 low hot c hc
  exact ⟨hl _, hh _, hh _⟩

theorem hotPrepare_within8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) : circuitWires (hotPrepare8 low hot) ⊆ S := by
  rw [hotPrepare8, circuitWires_append]
  exact List.append_subset.mpr ⟨by simpa [circuitWires, gateWires] using hh 0,
    ParityBank.parityNet_within 8 (lowN8 low) (hotNat8 hot) 8 le_rfl S
      (by intro j hj; simpa [lowN8,hj] using hl ⟨j,hj⟩)
      (by
        intro x hx
        have hx' : x<256 := by simpa using hx
        simpa [hotNat8,hx'] using hh ⟨x,hx'⟩)⟩

theorem fixupProgram_within8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths S : List Wire)
    (hr : root ∈ S) (hs : scratch ∈ S) (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S)
    (hi : tree.indexWires ⊆ S) (ha : paths ⊆ S) :
    NaiveChallenge.straightWires (fixupProgram8 data refs low hot tree root scratch paths) ⊆ S := by
  have hb : hotBank8 hot ⊆ S := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact hh i
  unfold fixupProgram8
  apply static_within_append
  · rw [literal_static]
    exact hotPrepare_within8 low hot S hl hh
  · apply static_within_append
    · rw [literal_static, hadamards_wires]
      exact hb
    · apply static_within_append
      · rw [recordLookup_static]
        apply recordWireList_within
        exact recordUnary_within _ scratch tree root paths S hr hs hi ha
          (fun p hp => hb (phasePorts_targets8 hot _ p hp))
      · apply static_within_append
        · rw [literal_static, hadamards_adjoint_wires]
          intro w hw
          exact hb (List.mem_reverse.mp hw)
        · rw [static_cast]
          apply static_within_append (eraseNetwork_within n _ _ S (hotNetwork_within8 low hot S hl hh))
          rw [literal_static]
          simpa [circuitWires, gateWires] using hh 0

/-- The generic row reference is exactly the physical little-endian address. -/
theorem splitAddress_value8 (low : Fin 8 → Wire) (high : List Wire) (s : BasisState) :
    256 * (tableAddressTree high 0 1).routeLabel s + hotAddress8 low s =
      tableAddressValue ([lowN8 low 0, lowN8 low 1, lowN8 low 2, lowN8 low 3, lowN8 low 4, lowN8 low 5,
        lowN8 low 6, lowN8 low 7] ++ high) s := by
  simp only [tableAddressTree_route, zero_add, one_mul, List.cons_append, List.nil_append,
    tableAddressValue, hotAddress8, addrN]
  ring

/-- The measured data bank is available to the phase fixup after reset. -/
theorem fixupFactor_recycled8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (s : BasisState) (hs : Clean paths s ∧ LoadedClear8 data read low tree root s) :
    fixupFactor8 data outcomes read low hot tree root (clearRegister (data.map ClearPort.target) s) =
      registerXPhase (data.map ClearPort.target) outcomes s := by
  let cleared := clearRegister (data.map ClearPort.target) s
  let prepared := Classical.run (hotPrepare8 low hot) cleared
  have hhot : HotClean8 hot cleared := by
    intro i
    change clearRegister (data.map ClearPort.target) s (hot i) = false
    exact clearRegister_clean _ s _ (hh i)
  have hlow : ∀ i, cleared (low i) = s (low i) := by
    intro i
    have hw : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact clearRegister_frame _ _ _ (ha _ (by simp only [List.mem_cons, List.mem_append, hw, or_true, true_or]))
  have haddr : hotAddress8 low cleared = hotAddress8 low s :=
    addrN_congr _ _ _ 8 (fun j hj => by simp only [lowN8, hj, dite_true]; exact hlow _)
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = s w := by
    change Classical.run (hotPrepare8 low hot) cleared w = s w
    rw [hotPrepare_frame8 low hot cleared w (by
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
  let selected : Fin 256 := ⟨hotAddress8 low s, hotAddress_bound8 low s⟩
  apply phaseFactor_loaded8 data outcomes read hot tree root s prepared selected
  · intro i
    simpa only [Fin.ext_iff, haddr] using hotPrepare_marker8 low hot hi hdlow cleared hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hs.2 p hp

theorem measuredClear_recycled_coherent8 {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank8 hot)
    (hn : (data.map ClearPort.target).Nodup)
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((measuredClear8 data low hot tree root scratch paths start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (data.map ClearPort.target)))
      (fun s => Clean paths s ∧ LoadedClear8 data read low tree root s) := by
  unfold CoherentlyImplementsOn
  rw [measuredClear_run8]
  apply measureResetThen_coherent (data.map ClearPort.target)
    (fun outcomes => fixupSource8 data outcomes read low hot tree root scratch paths)
    (fun outcomes => basisIdeal id (fixupFactor8 data outcomes read low hot tree root))
    (fun _ s => HotClean8 hot s ∧ Clean paths s)
    (fun s => Clean paths s ∧ LoadedClear8 data read low tree root s)
    (clearRegister (data.map ClearPort.target)) hn (witness := zeroBasisState)
  · intro outcomes hout
    exact fixupSource_wellFormed8 data outcomes read low hot tree root scratch paths hl hi hdlow hs hshot
  · intro outcomes
    exact fixupSource_coherent8 data outcomes read low hot tree root scratch paths hl hi hdlow hbank hs hshot
  · intro outcomes hout s hvalid
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact clearRegister_clean _ s _ (hh i)
    · intro w hw
      rw [clearRegister_frame _ _ _ (ha w (by simp [hw]))]
      exact hvalid.1 w hw
    · rw [basisIdeal_ket, fixupFactor_recycled8 data outcomes read low hot tree root paths hi hdlow hbank ha hh s hvalid]
      rfl
  · simp [Clean, LoadedClear8, zeroBasisState]

end
end ShorECDLP.Entrant.MeasuredClear

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem fixupProgram_wellFormed8 {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank8 hot) :
    (fixupProgram8 data refs low hot tree root scratch paths).WellFormed := by
  have hp := hotNetwork_physical8 low hot hi hdlow
  have hH (ws : List Wire) : CircuitWellFormed (ws.map Gate.H) := by
    intro g hg; obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg; trivial
  unfold fixupProgram8
  apply straight_append_wellFormed
  · apply literalProgram_wellFormed
    rw [hotPrepare8,circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed,Gate.WellFormed],ParityBank.parityNet_wellFormed 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hdlow) 8 le_rfl⟩
  · apply straight_append_wellFormed
    · exact literalProgram_wellFormed _ (hH _)
    · apply straight_append_wellFormed
      · apply recordLookupProgram_wellFormed
        apply recordUnary_physical _ _ _ _ _ hl
        intro row c hc
        refine ⟨?_,?_⟩
        · intro he; apply hs; subst c; simp only [List.mem_cons,List.mem_append] at hc ⊢; tauto
        · intro p hpm he
          exact hshot (he.symm ▸ phasePorts_targets8 hot _ p hpm)
      · apply straight_append_wellFormed
        · exact literalProgram_wellFormed _ ((circuitWellFormed_adjoint _).mpr (hH _))
        · rw [castFinish_wellFormed]
          exact straight_append_wellFormed _ _ (eraseNetwork_wellFormed n _ hp _)
            (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed]))

theorem measuredClear_wellFormed8 {n} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank8 hot) (start : Nat) :
    (measuredClear8 data low hot tree root scratch paths start).WellFormed := by
  rw [measuredClear8,castFinish_wellFormed]
  apply measureThen_wellFormed
  intro cursor refs
  rw [castFinish_wellFormed]
  exact fixupProgram_wellFormed8 data refs low hot tree root scratch paths hl hi hdlow hs hshot

open AndGadget in
 theorem fixupProgram_residue8 {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) :
    residue (fixupProgram8 data refs low hot tree root scratch paths) = 0 := by
  unfold fixupProgram8
  rw [residue_append,residue_literal_HPFree _ (hotPrepare_hp8 low hot)]
  simp only [residue_append,residue_literal,residue_cast,eraseNetwork_residue,
    recordLookup_residue _ _ _ _ _ (recordUnary_phaseFree tree root paths),Nat.zero_add]
  simp [List.map_map,Function.comp_def,primitivePhaseCost,Circuit.adjoint,List.map_reverse,Gate.adjoint]

open AndGadget in
 theorem measuredClear_residue8 {n} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    residue (measuredClear8 data low hot tree root scratch paths start) = 0 := by
  rw [measuredClear8,residue_cast]
  apply measureThen_residue
  intro cursor refs
  rw [residue_cast]
  exact fixupProgram_residue8 data refs low hot tree root scratch paths

theorem measuredClear_static8 {n : Nat} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat) :
    NaiveChallenge.straightWires (measuredClear8 data low hot tree root scratch paths start) ⊆
      clearSupport8 data low hot tree root scratch paths := by
  rw [measuredClear8, static_cast]
  apply measureThen_within _ _ (by
    intro cursor refs
    rw [static_cast]
    apply fixupProgram_within8
    · simp [clearSupport8]
    · simp [clearSupport8]
    · intro i
      have hm : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport8, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro i
      have hm : hot i ∈ hotBank8 hot := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport8, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro w hw
      simp [clearSupport8, hw]
    · intro w hw
      simp [clearSupport8, hw])
  intro w hw
  simp [clearSupport8, hw]

end
end ShorECDLP.Entrant.MeasuredClear

/-! ### Deferred phase fixups: generic measurement lemma and fixup-factor algebra -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem normSq_resetMagnitude (m : Nat) :
    Complex.normSq (registerXResetMagnitude m) = (1 / 2 : ℝ) ^ m := by
  rw [registerXResetMagnitude, map_pow, Complex.normSq_ofReal, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem registerXPhase_square (targets : List Wire) (outcomes : List Bool) (s : BasisState) :
    registerXPhase targets outcomes s * registerXPhase targets outcomes s = 1 := by
  induction targets generalizing outcomes with
  | nil => simp [registerXPhase]
  | cons t ts ih =>
    cases outcomes with
    | nil => simp [registerXPhase]
    | cons o os =>
      rw [registerXPhase, mul_mul_mul_comm, ih]
      cases o <;> cases s t <;> norm_num

/-- A register measure/reset followed by an outcome-dependent continuation, in simulation form:
every continuation branch, prefixed by the register's Kraus map, satisfies `P` with coefficient
`2^(-m/2)` times its own input-independent coefficient. -/
theorem measureResetThen_sim (targets : List Wire) (next : List Bool → AdaptiveCircuit)
    (Q : List Bool → InstrumentBranch → ℂ → Prop) (P : InstrumentBranch → ℂ → Prop)
    (hn : ∀ o, o.length = targets.length →
      ∃ cs : List ℂ, List.Forall₂ (Q o) (next o).run cs ∧ (cs.map Complex.normSq).sum = 1)
    (hlift : ∀ o, o.length = targets.length → ∀ b c, Q o b c →
      P ⟨o ++ b.history, b.kraus.comp (xResetRegisterKraus targets o)⟩
        (registerXResetMagnitude targets.length * c)) :
    ∃ cs : List ℂ, List.Forall₂ P (measureResetThen targets next).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hrun : (measureResetThen targets next).run =
      (boolTranscripts targets.length).flatMap (fun o => (next o).run.map
        (fun b => (⟨o ++ b.history, b.kraus.comp (xResetRegisterKraus targets o)⟩ : InstrumentBranch))) :=
    run_measureResetThen targets next
  rw [hrun]
  have key : ∀ outs : List (List Bool), (∀ o ∈ outs, o.length = targets.length) →
      ∃ cs : List ℂ, List.Forall₂ P (outs.flatMap (fun o => (next o).run.map
          (fun b => (⟨o ++ b.history, b.kraus.comp (xResetRegisterKraus targets o)⟩ : InstrumentBranch)))) cs ∧
        (cs.map Complex.normSq).sum =
          (outs.length : ℝ) * Complex.normSq (registerXResetMagnitude targets.length) := by
    intro outs
    induction outs with
    | nil => intro _; exact ⟨[], .nil, by simp⟩
    | cons o os ih =>
      intro hall
      obtain ⟨c1, h1, m1⟩ := hn o (hall o (by simp))
      obtain ⟨c2, h2, m2⟩ := ih (fun v hv => hall v (by simp [hv]))
      refine ⟨c1.map (fun c => registerXResetMagnitude targets.length * c) ++ c2, ?_, ?_⟩
      · rw [List.flatMap_cons]
        apply List.rel_append _ h2
        apply List.forall₂_map_left_iff.mpr
        apply List.forall₂_map_right_iff.mpr
        exact h1.imp (fun b c hb => hlift o (hall o (by simp)) b c hb)
      · rw [List.map_append, List.sum_append, m2, List.map_map]
        have hm : (c1.map (Complex.normSq ∘ fun c => registerXResetMagnitude targets.length * c)) =
            c1.map (fun c => Complex.normSq (registerXResetMagnitude targets.length) * Complex.normSq c) := by
          apply List.map_congr_left
          intro c _
          simp [Complex.normSq_mul]
        rw [hm, List.sum_map_mul_left, m1, List.length_cons]
        push_cast
        ring
  obtain ⟨cs, h, m⟩ := key _ (fun o ho => mem_boolTranscripts_length ho)
  refine ⟨cs, h, ?_⟩
  rw [m, boolTranscripts_length, normSq_resetMagnitude, Nat.cast_pow, ← mul_pow]
  norm_num

theorem fixupFactor8_append {n : Nat} (d1 d2 : List (ClearPort n)) (o1 o2 : List Bool)
    (h : o1.length = d1.length) (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) :
    fixupFactor8 (d1 ++ d2) (o1 ++ o2) read low hot tree root s =
      fixupFactor8 d1 o1 read low hot tree root s * fixupFactor8 d2 o2 read low hot tree root s := by
  have hz : (d1 ++ d2).zip ((o1 ++ o2).map boolRecord) = d1.zip (o1.map boolRecord) ++ d2.zip (o2.map boolRecord) := by
    rw [List.map_append]
    exact List.zip_append (by simp [h])
  simp only [fixupFactor8, phaseLookupFactor, logicalPorts8, hz, phasePorts8, List.flatMap_append,
    recordTargets_append, xorPhase_append]

/-- A deferred clear's phase, evaluated at a later state whose root and address agree. -/
theorem fixupFactor8_loaded {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (t u : BasisState) (hhot : HotClean8 hot t)
    (hw : ∀ p ∈ data, u p.target =
      (t root && decide (read (p.ref (256 * tree.routeLabel t + hotAddress8 low t)) = p.value))) :
    fixupFactor8 data outcomes read low hot tree root t =
      registerXPhase (data.map ClearPort.target) outcomes u := by
  let prepared := Classical.run (hotPrepare8 low hot) t
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = t w :=
    hotPrepare_frame8 low hot t w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)
  have hroute : tree.routeLabel prepared = tree.routeLabel t := by
    apply tree.routeLabel_congr prepared t
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 256 := ⟨hotAddress8 low t, hotAddress_bound8 low t⟩
  apply phaseFactor_loaded8 data outcomes read hot tree root u prepared selected
  · intro i
    simpa only [Fin.ext_iff] using hotPrepare_marker8 low hot hi hdlow t hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hw p hp

end
end ShorECDLP.Entrant.MeasuredClear

/-! ### The eight-bit clear on a sixteen-bit window bank -/

set_option Elab.async false
namespace ShorECDLP.Entrant.WideBank8
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- The eight low address bits `855..862`. -/
def low8 (i : Fin 8) : Wire := 855 + i.val

theorem low8_lt (i : Fin 8) : low8 i < 863 := by
  have hi := i.isLt
  show 855 + i.val < 863
  omega

/-- The phase bank of a site: its first 256 cleared targets. -/
def hot8 {n} (site : MaskedSite n) : Fin 256 → Wire := fun i => scratch site + i.val

/-- The phase scratch of every eight-bit clear: the ninth wire of the old clear path bank. -/
def scratch8 : Wire := 14840

theorem kind_hot8 {n} (site : MaskedSite n) (hk : SiteKind site) (i : Fin 256) :
    hot8 site i ∈ portTargets site.ports := by
  have hi := i.isLt
  show scratch site + i.val ∈ portTargets site.ports
  rcases hk with ⟨ht,-⟩ | ⟨ht,-⟩ | ⟨ht,-⟩ | ⟨ht,-⟩ | ⟨ht,-⟩ | ⟨ht,-⟩
  · have hs : scratch site = 14115 := by rw [scratch,ht]; decide +kernel
    rw [hs, ht, List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14373 := by rw [scratch,ht]; exact scrWires_head
    rw [hs, ht, scrWires_eq]
    simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.cons_append, List.not_mem_nil, or_false]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14115 := by rw [scratch,ht]; decide +kernel
    rw [hs, ht]
    simp only [List.mem_append, List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14373 := by rw [scratch,ht,scrAllWires_eq,scrWires_eq]; rfl
    rw [hs, ht, scrAllWires_eq, scrWires_eq]
    simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.cons_append, List.not_mem_nil, or_false]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14115 := by rw [scratch,ht]; decide +kernel
    rw [hs, ht, List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14374 := by rw [scratch,ht]; rfl
    rw [hs, ht]
    simp only [List.mem_append, List.mem_cons, List.mem_range'_1]
    dsimp only [Wire] at *
    omega

theorem hot8_injective {n} (site : MaskedSite n) : Function.Injective (hot8 site) := by
  intro i j he
  apply Fin.ext
  simp only [hot8] at he
  dsimp only [Wire] at he
  omega

structure BankOK (B : PathShare.Bank) : Prop where
  split : ∀ s : BasisState, 256 * (tableAddressTree B.high 0 1).routeLabel s + MeasuredClear.hotAddress8 low8 s =
    tableAddressValue B.bits s
  high : ∀ w ∈ B.high, 862 ≤ w ∧ w < 10000
  index : (tableAddressTree B.high 0 1).indexWires.dedup = B.high
  nodup : (B.high ++ B.hp).Nodup
  len : B.high.length ≤ B.hp.length
  sub : ∀ w ∈ B.hp, w ∈ B.paths
  out : ∀ w ∈ B.hp, 871 ≤ w
  bitsLen : B.bits.length ≤ B.paths.length
  scr : scratch8 ∈ B.paths ∧ scratch8 ∉ B.hp

-- WideSigned.Bank.clear_coherent_bank at eight low bits, with the dirty scratch `14840`.
theorem clear_coherent_bank {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hk : SiteKind site)
    (bitsW H P : List Wire)
    (hsplit : ∀ s : BasisState, 256 * (tableAddressTree H 0 1).routeLabel s + MeasuredClear.hotAddress8 low8 s =
      tableAddressValue bitsW s)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 10000) (hP : ∀ w ∈ P, 871 ≤ w ∧ w ∉ portTargets site.ports)
    (hPg : site.guard ∉ P) (hindex : (tableAddressTree H 0 1).indexWires.dedup = H)
    (hnd : (H ++ P).Nodup) (hhl : H.length ≤ P.length)
    (hsP : scratch8 ∉ P) (hsT : scratch8 ∉ portTargets site.ports)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((MeasuredClear.measuredClear8 (clearData site.ports) low8 (hot8 site)
        (tableAddressTree H 0 1) site.guard scratch8 P start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => Clean P s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue bitsW s)) = p.value))) := by
  obtain ⟨hn,hbd,-,-,-,hg,-⟩ := kind_facts site hk
  have hmem := kind_hot8 site hk
  have hgl : site.guard < 14115 := by rcases hg with e | e <;> rw [e] <;> decide
  have notT : ∀ w ∈ site.guard :: List.ofFn low8 ++ H ++ P, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with ((h | h) | h) | h
    · rw [h] at h2; dsimp only [Wire] at *; omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      have := low8_lt i
      dsimp only [Wire] at *; omega
    · have := hH w h
      dsimp only [Wire] at *; omega
    · exact (hP w h).2 ht
  have hgH : site.guard ∉ H := by
    intro h; have := hH _ h; dsimp only [Wire] at *; omega
  have hnodup : (site.guard :: H ++ P).Nodup := by
    rw [List.cons_append, List.nodup_cons]
    refine ⟨fun h => ?_, hnd⟩
    rcases List.mem_append.mp h with h | h
    · exact hgH h
    · exact hPg h
  have hl := tableAddressTree_layout H P site.guard 0 1 hhl hnodup
  have hc := MeasuredClear.measuredClear_recycled_coherent8 (clearData site.ports) read low8 (hot8 site)
    (tableAddressTree H 0 1) site.guard scratch8 P hl (hot8_injective site)
    (by
      intro i j he
      have h1 := (hbd _ (hmem j)).1
      have h2 := low8_lt i
      rw [← he] at h1
      dsimp only [Wire] at *
      omega)
    (by
      apply List.disjoint_left.mpr
      intro w hw hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      rw [hindex] at hm
      exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) (hmem i))
    (by
      rw [hindex]
      intro hm
      simp only [List.mem_cons, List.mem_append] at hm
      rcases hm with (h | h) | h
      · have hne : site.guard ≠ scratch8 := by rcases hg with e | e <;> rw [e] <;> decide
        exact hne h.symm
      · exact absurd (hH _ h).2 (by decide)
      · exact hsP h)
    (by
      intro hm
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      exact hsT (hi ▸ hmem i))
    (by simpa using hn)
    (by
      rw [clearData_targets,hindex]
      intro w hw hm
      exact notT w hw hm)
    (by rw [clearData_targets]; exact hmem)
    start history
  simp only [clearData_targets] at hc
  obtain ⟨cs,aligned,mass⟩ := hc
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  apply hb s
  refine ⟨hs.1,?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  simpa [MeasuredClear.LoadedClear8,clearData,hsplit] using hs.2 q hq

def clearP {n} (B : Bank) (site : MaskedSite n) (start : Nat) :=
  MeasuredClear.measuredClear8 (clearData site.ports) low8 (hot8 site) (tableAddressTree B.high 0 1)
    site.guard scratch8 B.hp start

def clearSourceP {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) : AdaptiveCircuit :=
  (clearP B site 0).instantiate read Fin.elim0

theorem clearP_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (start : Nat) (history : Fin start → Bool) :
    ((clearP B site start).instantiate read history).run = (clearSourceP B read site).run := by
  simp only [clearP,clearSourceP,MeasuredClear.measuredClear_run8]

theorem scratch8_not_targets {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site) :
    scratch8 ∉ portTargets site.ports := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  intro ht
  exact List.disjoint_left.mp hlast.2.2
    (show scratch8 ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
      simp [hB.scr.1]) ht

theorem clearP_coherent {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (site : MaskedSite n) (hg : SiteGeoP B site) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((clearP B site start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => Clean B.hp s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue B.bits s)) = p.value))) := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  unfold clearP
  refine clear_coherent_bank read site hg.kind B.bits B.high B.hp hB.split hB.high ?_ ?_ hB.index hB.nodup hB.len
    hB.scr.2 (scratch8_not_targets B hB site hg) start history
  · intro w hw
    refine ⟨hB.out w hw, fun ht => ?_⟩
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
        simp [hB.sub w hw]) ht
  · intro hg'
    have hn := hlast.1
    simp only [lookupRoot, Option.getD_some, List.cons_append, List.nodup_cons] at hn
    exact hn.1 (List.mem_append_right _ (hB.sub _ hg'))

theorem site_tree_nodup {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site) :
    (site.guard :: B.high ++ B.hp).Nodup := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  have hn := hlast.1
  simp only [lookupRoot, Option.getD_some, List.cons_append, List.nodup_cons] at hn
  have hgl := (kind_facts site hg.kind).2.2.2.2.2.1
  rw [List.cons_append, List.nodup_cons]
  refine ⟨fun h => ?_, hB.nodup⟩
  rcases List.mem_append.mp h with h | h
  · have := hB.high _ h
    rcases hgl with e | e <;> rw [e] at this <;> dsimp only [Wire] at this <;> omega
  · exact hn.1 (List.mem_append_right _ (hB.sub _ h))

theorem geo_lay {n} (B : Bank) (hB : BankOK B) (b : Block n) (hg : BlockGeoP B b) : BlockLay B b := by
  cases b with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    refine ⟨hB.bitsLen, ?_⟩
    intro c ps hm
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    obtain ⟨p, rfl, -⟩ := hg' j hj
    simp [normalizeWInstr] at he
  | masked site =>
    have hg' : SiteGeoP B site := hg
    have hp : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg'.placed i (List.mem_append_left _ hi))
    exact ⟨pair_layouts_of_placed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ hp),
      tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len (site_tree_nodup B hB site hg')⟩

theorem clearP_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (start : Nat) : (clearP B site start).WellFormed := by
  obtain ⟨-,hbd,-,-,-,hgl,-⟩ := kind_facts site hg.kind
  have hmem := kind_hot8 site hg.kind
  unfold clearP
  apply MeasuredClear.measuredClear_wellFormed8
  · exact tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len (site_tree_nodup B hB site hg)
  · exact hot8_injective site
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low8_lt i
    rw [← he] at h1
    dsimp only [Wire] at *
    omega
  · rw [hB.index]
    intro hm
    simp only [List.mem_cons, List.mem_append] at hm
    rcases hm with (h | h) | h
    · have hne : site.guard ≠ scratch8 := by rcases hgl with e | e <;> rw [e] <;> decide
      exact hne h.symm
    · exact absurd (hB.high _ h).2 (by decide)
    · exact hB.scr.2 h
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact scratch8_not_targets B hB site hg (hi ▸ hmem i)

theorem clearP_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp) (start : Nat) (history : Fin start → Bool) :
    ((clearP B site start).instantiate read history).tCount =
      7 * ((tableAddressTree B.high 0 1).internalNodes + 247) := by
  unfold clearP
  exact MeasuredClear.measuredClear_tCount8 _ _ _ _ _ _ _ hl read start history

theorem clearP_support {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hk : SiteKind site)
    (S : List Wire) (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low8 i ∈ S)
    (hhigh : B.high ⊆ S) (hpaths : B.paths ⊆ S) (start : Nat) :
    ChallengeMigration.straightWires (clearP B site start) ⊆ S := by
  have hmem := kind_hot8 site hk
  unfold clearP
  rw [support_agrees]
  apply List.Subset.trans (MeasuredClear.measuredClear_static8 _ _ _ _ _ _ _ start)
  intro w hw
  simp only [MeasuredClear.clearSupport8,clearData_targets,hB.index,MeasuredClear.hotBank8,
    List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at hw
  rcases hw with hs | hl | hh | hr | hb | hp | hsc
  · exact hS hs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    exact hlow i
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact hS (hmem i)
  · rw [hr]; exact hgS
  · exact hhigh hb
  · exact hpaths (hB.sub _ hp)
  · rw [hsc]; exact hpaths hB.scr.1

theorem clearP_residue {n} (B : Bank) (site : MaskedSite n) (start : Nat) :
    AndGadget.residue (clearP B site start) = 0 :=
  MeasuredClear.measuredClear_residue8 _ _ _ _ _ _ _ start

/-! #### Units on the eight-bit bank -/

def blockRecP2 {n} (B : Bank) : Block2 n → Nat
  | .plain code => codeRecords B.bits B.paths windowRoot (normalizeW code)
  | .unit u => codeRecords B.bits B.paths windowRoot (normalizeW u.pre) +
      u.clear.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) u.clear.guard B.hp)+255)

def blockProgP2 {n} (B : Bank) (b : Block2 n) (start : Nat) : Straight n start (start+blockRecP2 B b) :=
  match b with
  | .plain code => compile B.bits B.paths windowRoot (normalizeW code) start
  | .unit u => castFinish (by simp [blockRecP2,clearData]; omega)
      ((compile B.bits B.paths windowRoot (normalizeW u.pre) start).append
        (clearP B u.clear (start+codeRecords B.bits B.paths windowRoot (normalizeW u.pre))))

def recordsP2 {n} (B : Bank) : Code2 n → Nat
  | [] => 0
  | b::code => blockRecP2 B b + recordsP2 B code

def programP2 {n} (B : Bank) : (code : Code2 n) → (start : Nat) → Straight n start (start+recordsP2 B code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [recordsP2]; omega)
      ((blockProgP2 B b start).append (programP2 B code (start+blockRecP2 B b)))

def blockSourceP2 {n} (B : Bank) (read : ConstantBit n → Bool) : Block2 n → AdaptiveCircuit
  | .plain code => source read B.bits B.paths windowRoot (normalizeW code)
  | .unit u => (source read B.bits B.paths windowRoot (normalizeW u.pre)).seq (clearSourceP B read u.clear)

theorem blockProgP2_run {n} (B : Bank) (read : ConstantBit n → Bool) (b : Block2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgP2 B b start).instantiate read history).run = (blockSourceP2 B read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | unit u =>
    rw [blockProgP2,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearP_run B read u.clear _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSourceP2,AdaptiveCircuit.run_seq]

theorem block_simulationP2 {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (block : Block2 n) (hg : BlockGeoP2 B block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimP2 read B block) (blockSourceP2 B read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    obtain ⟨cs,aligned,mass⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen code
      (litAvoid_placed _ _ code hg')
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    exact ⟨m,hm,fun address st hs _ _ =>
      hb address st hs (litAvoid_pathsClean read B.bits B.paths code address hg' st)⟩
  | unit u =>
    have hg' : UnitGeoP B u := hg
    have hp : ∀ i ∈ u.pre, PlacedPair B.bits B.paths windowRoot i := by
      intro i hi; exact hg'.placed i (List.mem_append_left _ hi)
    obtain ⟨preCs,preAligned,preMass⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen u.pre
      (fun i hi => pair_of_placed_lit _ _ i (hp i hi))
    obtain ⟨cs,aligned,mass⟩ := clearP_coherent read B hB u.clear hg'.site 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSourceP2,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block2.code,UnitSite.code,literalRecords_append,literalRecords] using hm
      · intro a st hs hcl hsafe
        have hcl' : Clean B.paths st.basis := hcl
        have hsv : SimulationValid B.bits B.paths windowRoot a st := ⟨hcl',hs.1,hs.2⟩
        let next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m st
        have hn := strict_preserves read B.bits B.paths u.pre a hp st hsv m
        have hrun := unit_runP read B u hg' a st m hsv
        have hclean : Clean (portTargets u.clear.ports)
            (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg'.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
        have hvalid : Clean B.hp next.basis ∧
            ∀ p ∈ u.clear.ports, next.basis p.target = (next.basis u.clear.guard &&
              decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
          refine ⟨fun w hw => hn.1 w (hB.sub w hw),?_⟩
          rw [hn.2.1]
          exact loaded_of_clean_unload read u.clear.ports a u.clear.guard next.basis hlast.2.1 hclean
        have hclear : b₂.kraus (ket next.basis) =
            c₂ • ket (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
          rw [← clear_eq_unload read u.clear.ports a u.clear.guard next.basis hclean]
          simpa [ket] using h₂ next.basis hvalid
        have hsigned : b₂.kraus (Bridge.signedKet next) = c₂ •
            Bridge.signedKet (ECDSAAdd.run ((specialize u.code a).instantiate read) m st) := by
          rw [hrun]
          change b₂.kraus (Bridge.signedKet next) = c₂ • Bridge.signedKet
            ⟨next.phase,tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis⟩
          cases hphase : next.phase <;> simp [Bridge.signedKet,hphase,hclear,map_neg]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [h₁ a st hs (strict_pathsClean read B.bits B.paths u.pre a hp st hsv),map_smul,hsigned]
        simp [smul_smul,blockReference2,Block2.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num

theorem geo_lay2 {n} (B : Bank) (hB : BankOK B) (b : Block2 n) (hg : BlockGeoP2 B b) : BlockLay2 B b := by
  cases b with
  | plain code => exact geo_lay B hB (.plain code) hg
  | unit u =>
    have hg' : UnitGeoP B u := hg
    have hp : ∀ i ∈ u.pre, PlacedPair B.bits B.paths windowRoot i := by
      intro i hi; exact hg'.placed i (List.mem_append_left _ hi)
    exact ⟨pair_layouts_of_placed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ hp),
      tableAddressTree_layout B.high B.hp u.clear.guard 0 1 hB.len (site_tree_nodup B hB u.clear hg'.site)⟩

def blockTP2 {n} (B : Bank) : Block2 n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * (2^B.bits.length - 1)
  | .unit u => literalToffolis (normalizeW u.pre) + traversals u.pre * (2^B.bits.length - 1) +
      ((tableAddressTree B.high 0 1).internalNodes + 247)

def codeTP2 {n} (B : Bank) : Code2 n → Nat
  | [] => 0
  | b::code => blockTP2 B b + codeTP2 B code

theorem blockProgP2_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (b : Block2 n) (hl : BlockLay2 B b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgP2 B b start).instantiate read history).tCount = 7 * blockTP2 B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgP2, WEX.compile_tCount read _ _ _ _ hl' start history, traversals_normalize]
    simp only [blockTP2]; ring
  | unit u =>
    obtain ⟨h1, h2⟩ := hl
    rw [blockProgP2, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearP_tCount read B u.clear h2 _ h),
      WEX.compile_tCount read _ _ _ _ h1 start history, traversals_normalize]
    simp only [blockTP2]; ring

def blockSP2 {n} (B : Bank) : Block2 n → Nat
  | .plain code => codeSlots B.bits (normalizeW code)
  | .unit u => codeSlots B.bits (normalizeW u.pre) +
      (1024 * u.clear.ports.length * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 2291)

def codeSP2 {n} (B : Bank) : Code2 n → Nat
  | [] => 0
  | b::code => blockSP2 B b + codeSP2 B code

theorem blockProgP2_slots {n} (B : Bank) (b : Block2 n) (hl : BlockLay2 B b) (start : Nat) :
    (blockProgP2 B b start).gateSlots = blockSP2 B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgP2, WEX.compile_slots _ _ _ _ hl' start]
    rfl
  | unit u =>
    obtain ⟨h1, h2⟩ := hl
    rw [blockProgP2, castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ h1 start]
    have hc : (clearP B u.clear (start + codeRecords B.bits B.paths windowRoot (normalizeW u.pre))).gateSlots =
        1024 * u.clear.ports.length * (tableAddressTree B.high 0 1).leaves +
          10 * (tableAddressTree B.high 0 1).internalNodes + 2291 := by
      unfold clearP
      rw [MeasuredClear.measuredClear_slots8 _ _ _ _ _ _ _ h2]
      simp [clearData]
    rw [hc]
    rfl

theorem programP2_support {n} (B : Bank) (hB : BankOK B) (code : Code2 n) (hg : ∀ b ∈ code, BlockGeoP2 B b)
    (S : List Wire) (hroot : windowRoot ∈ S) (hbits : B.bits ⊆ S) (hpaths : B.paths ⊆ S)
    (hlow : ∀ i, low8 i ∈ S) (hhigh : B.high ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 code → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (programP2 B code start) ⊆ S := by
  induction code generalizing start with
  | nil => simp [programP2,recordsP2,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hlb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.wires p ⊆ S.toFinset :=
      fun p hm => hlit p (by simp [erase2_cons,hm])
    have hkb : ∀ c ps, WInstr.lookup c ps ∈ b.code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
      fun c ps hm => hlook c ps (by simp [erase2_cons,hm])
    rw [programP2,support_cast,straightWires_append]
    refine List.append_subset.mpr ⟨?_, ih (fun d hd => hg d (by simp [hd]))
      (fun p hm => hlit p (by simp [erase2_cons,hm])) (fun c ps hm => hlook c ps (by simp [erase2_cons,hm])) _⟩
    cases b with
    | plain code =>
      exact compile_support _ _ _ _ S hroot hbits hpaths (normalized_lit_support code S hlb)
        (normalized_look_support code S hkb) start
    | unit u =>
      have hg' : UnitGeoP B u := hg (.unit u) (by simp)
      have hpl : ∀ p, WInstr.literal p ∈ u.pre → ECDSAAdd.wires p ⊆ S.toFinset :=
        fun p hm => hlb p (List.mem_append_left _ hm)
      have hpk : ∀ c ps, WInstr.lookup c ps ∈ u.pre → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
        fun c ps hm => hkb c ps (List.mem_append_left _ hm)
      have hlast := hkb (some u.clear.guard) u.clear.ports (by simp [Block2.code,UnitSite.code])
      rw [blockProgP2,support_cast,straightWires_append]
      exact List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
        (normalized_lit_support _ S hpl) (normalized_look_support _ S hpk) start,
        clearP_support B hB u.clear hg'.site.kind S hlast.2 (hlast.1 u.clear.guard (Option.mem_def.mpr rfl))
          hlow hhigh hpaths _⟩

/-! #### Hosted blocks on the eight-bit bank -/

def blockProgH {n} (B : Bank) (b : Block2 n) (start : Nat) : Straight n start (start + blockRecP2 B b) :=
  match b with
  | .plain code => castFinish (congrArg (fun k => start + k) (hostCode_counts B.bits B.paths windowRoot code).1)
      (compile B.bits B.paths windowRoot (hostCode code) start)
  | .unit u => blockProgP2 B (.unit u) start

def blockSourceH {n} (B : Bank) (read : ConstantBit n → Bool) : Block2 n → AdaptiveCircuit
  | .plain code => source read B.bits B.paths windowRoot (hostCode code)
  | .unit u => blockSourceP2 B read (.unit u)

theorem blockProgH_run {n} (B : Bank) (read : ConstantBit n → Bool) (b : Block2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgH B b start).instantiate read history).run = (blockSourceH B read b).run := by
  cases b with
  | plain code =>
    rw [blockProgH, castFinish_instantiate]
    exact compile_run read _ _ _ _ _ _
  | unit u => exact blockProgP2_run B read (.unit u) start history

theorem block_simulationH {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (block : Block2 n) (hg : BlockGeoP2 B block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimH read B block) (blockSourceH B read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    have hlit : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    let P := ECDSAAdd.Baselines.normalizeProgram (litProg code)
    have hc : hostCode code = [.literal (hostBlock3 P)] :=
      hostCode_eq_host ((allLit_iff code).mpr hlit)
    have hRP : windowRoot ∉ ECDSAAdd.wires P := by
      intro hw
      rw [ECDSAAdd.Baselines.normalize_wires] at hw
      obtain ⟨p, hp, hw⟩ := litProg_wires code windowRoot hw
      obtain ⟨q, he, hq⟩ := hg' _ hp
      cases he
      exact hq windowRoot (by simp) hw
    show ∃ cs : List ℂ, List.Forall₂ (BlockSimH read B (.plain code))
      (source read B.bits B.paths windowRoot (hostCode code)).run cs ∧ (cs.map Complex.normSq).sum = 1
    rw [hc]
    obtain ⟨cs,aligned,mass⟩ := lit_simulation read B.bits B.paths windowRoot
      ([.literal (hostBlock3 P)] : WCode n) (by simp)
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    refine ⟨m, ?_, fun address st hs _ hh _ => ?_⟩
    · rw [hm]
      simp only [literalRecords, hostBlock3_meas, P, ECDSAAdd.Baselines.normalize_measurements, Nat.add_zero]
      exact litProg_meas code hlit
    · rw [hb address st]
      have e1 : (specialize ([.literal (hostBlock3 P)] : WCode n) address).instantiate read = hostBlock3 P := by
        rw [show ([.literal (hostBlock3 P)] : WCode n) = wLiteral (hostBlock3 P) from rfl,
          specialize_literal, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      have e2 : blockReference2 read address (.plain code : Block2 n) = litProg code := by
        simp only [blockReference2, Block2.code]
        exact litProg_inst read code address hlit
      have hrun : ECDSAAdd.run P m st = ECDSAAdd.run (litProg code) m st :=
        ECDSAAdd.Baselines.normalize_run _ m st
      have hwP : ECDSAAdd.wires P = ECDSAAdd.wires (litProg code) := ECDSAAdd.Baselines.normalize_wires _
      rw [e1, e2, hostBlock3_run P hRP m st hs.2 hh.1.1.1 (by rw [hrun]; exact hh.1.1.2 m) (fun c1 c2 => by
          rw [hwP] at c1 c2
          obtain ⟨d1, d2, d3⟩ := hh.1.2 c1 c2
          exact ⟨d1, d2, by rw [hrun]; exact d3 m⟩) (fun c1 c2 => by
          rw [hwP] at c1 c2
          obtain ⟨d1, d2, d3⟩ := hh.2 c1 c2
          exact ⟨d1, d2, by rw [hrun]; exact d3 m⟩), hrun]
  | unit u =>
    obtain ⟨cs,aligned,mass⟩ := block_simulationP2 read B hB (.unit u) hg
    refine ⟨cs, aligned.imp ?_, mass⟩
    intro b c hb
    obtain ⟨m, hm, hb⟩ := hb
    exact ⟨m, hm, fun address st hs hc _ hsafe => hb address st hs hc hsafe⟩

theorem blockH_wellFormed {n} (B : Bank) (hB : BankOK B) (b : Block2 n) (hgb : BlockGeoP2 B b)
    (hpb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (blockProgH B b start).WellFormed := by
  cases b with
  | plain code =>
    have hg' : LitAvoid B.bits code := hgb
    have hlit : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    rw [blockProgH, castFinish_wellFormed, hostCode_eq_host ((allLit_iff code).mpr hlit)]
    apply compile_wellFormedLit _ _ _ _ (by simp)
    intro p hp
    rw [List.mem_singleton, WInstr.literal.injEq] at hp
    subst hp
    apply hostBlock3_valid
    apply ECDSAAdd.Baselines.normalize_physical
    intro i hi
    obtain ⟨q, hq, hi⟩ := litProg_mem code i hi
    exact hpb q hq i hi
  | unit u =>
    have hg' : UnitGeoP B u := hgb
    have hpref : ∀ i ∈ u.pre, LPlaced B.bits B.paths windowRoot i := fun i hi =>
      pair_of_placed_lit _ _ i (hg'.placed i (List.mem_append_left _ hi))
    have hphys : ∀ p, WInstr.literal p ∈ u.pre → ECDSAAdd.Arithmetic.GatePhysical p := by
      intro p hm; exact hpb p (List.mem_append_left _ hm)
    show (blockProgP2 B (.unit u) start).WellFormed
    rw [blockProgP2, castFinish_wellFormed]
    exact straight_append_wellFormed _ _
      (compile_wellFormedL _ _ _ _ hB.bitsLen (lplaced_normalize _ _ _ _ hpref)
        (normalized_literals_valid u.pre hphys) start)
      (clearP_wellFormed B hB u.clear hg'.site _)

theorem blockH_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (b : Block2 n) (hl : BlockLay2 B b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgH B b start).instantiate read history).tCount = 7 * blockTP2 B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    obtain ⟨-, e2, e3⟩ := hostCode_counts B.bits B.paths windowRoot code
    rw [blockProgH, castFinish_instantiate,
      WEX.compile_tCount read _ _ _ _ (hostCode_layouts _ _ _ code hl') start history, e2, e3]
    simp only [blockTP2]; ring
  | unit u => exact blockProgP2_tCount read B (.unit u) hl start history

theorem blockH_slots {n} (B : Bank) (b : Block2 n) (hl : BlockLay2 B b) (start : Nat) :
    (blockProgH B b start).gateSlots ≤ blockSP2 B b + 6 := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgH, castFinish_gateSlots, WEX.compile_slots _ _ _ _ (hostCode_layouts _ _ _ code hl') start]
    exact hostCode_slots B.bits code
  | unit u =>
    have h := blockProgP2_slots B (.unit u) hl start
    change (blockProgP2 B (.unit u) start).gateSlots ≤ blockSP2 B (.unit u) + 6
    omega

theorem blockH_residue {n} (B : Bank) (b : Block2 n) (start : Nat) :
    AndGadget.residue (blockProgH B b start) = 0 := by
  cases b with
  | plain code =>
    rw [blockProgH, AndGadget.residue_cast]
    exact WEXCredit.compile_residue _ _ _ _ _
  | unit u =>
    show AndGadget.residue (blockProgP2 B (.unit u) start) = 0
    simp [blockProgP2, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
      clearP_residue]

end
end ShorECDLP.Entrant.WideBank8

/-! ### The deferred tail of a fast site on the eight-bit bank -/

namespace ShorECDLP.Entrant.WideBank8
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open MeasuredClear (ClearPort)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Records of one fixup on the bank. -/
def fuseRec {n} (B : Bank) (site : MaskedSite n) : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) site.guard B.hp) + 255

/-- The site clear whose fixup also carries the deferred ports `gd`, read from records `refs`. -/
def fusedFix {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat)
    (refs : List (Fin start)) : Straight n start (start + site.ports.length + fuseRec B site) :=
  castFinish (by simp [clearData]) (MeasuredClear.measureThen (R := fuseRec B site)
    (fun cursor rs => castFinish (by simp only [fuseRec]; omega)
      (MeasuredClear.fixupProgram8 (gd ++ clearData site.ports) rs low8 (hot8 site)
        (tableAddressTree B.high 0 1) site.guard scratch8 B.hp))
    ((clearData site.ports).map ClearPort.target) start refs)

def tailRec {n} (B : Bank) (site : MaskedSite n) : Nat :=
  codeRecords B.bits B.paths windowRoot (normalizeW site.arithmetic) + (site.ports.length + fuseRec B site)

/-- Measure the deferred register `gd` now (it is reset for reuse); its phase is repaid by the
site clear after the arithmetic. -/
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
    MeasuredClear.fixupSource8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
      (tableAddressTree B.high 0 1) site.guard scratch8 B.hp)

def deferSource {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) : AdaptiveCircuit :=
  measureResetThen (gd.map ClearPort.target) (fun og =>
    (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq (fusedFixSource B read site gd og))

theorem fusedFix_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((fusedFix B site gd start refs).instantiate read history).run =
      (fusedFixSource B read site gd (refs.map history)).run := by
  rw [fusedFix, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun outcomes => MeasuredClear.fixupSource8 (gd ++ clearData site.ports) outcomes read
      low8 (hot8 site) (tableAddressTree B.high 0 1) site.guard scratch8 B.hp) read
      (by intro cursor rs h; rw [castFinish_instantiate, MeasuredClear.fixupProgram_run8])]
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
      MeasuredClear.append_run_prefix _ _ read (Nat.le_refl cursor) h h rfl (fusedFixSource B read site gd (grefs.map h)),
      AdaptiveCircuit.run_seq, compile_run, ← AdaptiveCircuit.run_seq]
    intro h' hh'
    rw [fusedFix_run, List.map_map]
    congr 2
    rw [← hh']
    rfl

/-! #### Geometry of a site clear on a bank -/

theorem site_clear_facts {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site) :
    (tableAddressTree B.high 0 1).Layout site.guard B.hp ∧
    (∀ i j, low8 i ≠ hot8 site j) ∧
    (MeasuredClear.hotBank8 (hot8 site)).Disjoint (site.guard :: (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp) ∧
    scratch8 ∉ site.guard :: (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp ∧
    scratch8 ∉ MeasuredClear.hotBank8 (hot8 site) ∧
    (∀ w ∈ site.guard :: List.ofFn low8 ++ (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp,
      w ∉ portTargets site.ports) ∧
    (∀ w ∈ B.bits, w ∉ portTargets site.ports) := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  obtain ⟨hn,hbd,-,-,-,hgd,-⟩ := kind_facts site hg.kind
  have hmem := kind_hot8 site hg.kind
  have hP : ∀ w ∈ B.hp, 871 ≤ w ∧ w ∉ portTargets site.ports := by
    intro w hw
    refine ⟨hB.out w hw, fun ht => ?_⟩
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
        simp [hB.sub w hw]) ht
  have hsT := scratch8_not_targets B hB site hg
  have notT : ∀ w ∈ site.guard :: List.ofFn low8 ++ B.high ++ B.hp, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with ((h | h) | h) | h
    · rw [h] at h2; rcases hgd with e | e <;> rw [e] at h2 <;> dsimp only [Wire] at * <;> omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      have := low8_lt i
      dsimp only [Wire] at *; omega
    · have := hB.high w h
      dsimp only [Wire] at *; omega
    · exact (hP w h).2 ht
  refine ⟨tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len (site_tree_nodup B hB site hg), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low8_lt i
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
    simp only [List.mem_cons, List.mem_append] at hm
    rcases hm with (h | h) | h
    · have hne : site.guard ≠ scratch8 := by rcases hgd with e | e <;> rw [e] <;> decide
      exact hne h.symm
    · exact absurd (hB.high _ h).2 (by decide)
    · exact hB.scr.2 h
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact hsT (hi ▸ hmem i)
  · rw [hB.index]
    intro w hw hm
    exact notT w hw hm
  · intro w hw ht
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by simp [hw]) ht

/-! #### Simulation of the fused fixup -/

/-- After the site measurement the fused fixup repays both the site's and the deferred register's
phases; the deferred phase is read from the root and address at fixup time. -/
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
  obtain ⟨hl, hdlow, hbank, hs, hshot, ha, hbits⟩ := site_clear_facts B hB site hg
  obtain ⟨hn,-,-,-,-,-,-⟩ := kind_facts site hg.kind
  have hmem := kind_hot8 site hg.kind
  unfold fusedFixSource
  apply MeasuredClear.measureResetThen_sim ((clearData site.ports).map ClearPort.target)
    (fun os => MeasuredClear.fixupSource8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
      (tableAddressTree B.high 0 1) site.guard scratch8 B.hp)
    (fun os => BranchCoherentOn (MeasuredClear.basisIdeal id
      (MeasuredClear.fixupFactor8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
        (tableAddressTree B.high 0 1) site.guard))
      (fun s => MeasuredClear.HotClean8 (hot8 site) s ∧ Clean B.hp s))
  · intro os _
    exact MeasuredClear.fixupSource_coherent8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
      (tableAddressTree B.high 0 1) site.guard scratch8 B.hp
      hl (hot8_injective site) hdlow hbank hs hshot
  · intro os hos b c hb next u hhp hsite hgarb
    rw [clearData_targets] at hos ⊢
    have hk := xResetRegisterKraus_ket (portTargets site.ports) os next.basis hos hn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hos] at hk
    set t := clearRegister (portTargets site.ports) next.basis with ht
    have hfr : ∀ w, w ∉ portTargets site.ports → t w = next.basis w :=
      fun w hw => MeasuredClear.clearRegister_frame _ _ _ hw
    have hhot : MeasuredClear.HotClean8 (hot8 site) t := fun i => clearRegister_clean _ _ _ (hmem i)
    have hvalid : MeasuredClear.HotClean8 (hot8 site) t ∧ Clean B.hp t :=
      ⟨hhot, fun w hw => by rw [hfr w (ha w (by simp [hw]))]; exact hhp w hw⟩
    have hsplit : ∀ s : BasisState, 256 * (tableAddressTree B.high 0 1).routeLabel s +
        MeasuredClear.hotAddress8 low8 s = tableAddressValue B.bits s := hB.split
    have haddr : tableAddressValue B.bits t = tableAddressValue B.bits next.basis :=
      WEX.tableAddressValue_congr _ _ _ (fun w hw => hfr w (hbits w hw))
    have hguard : t site.guard = next.basis site.guard := hfr _ (ha _ (by simp))
    have hfac : MeasuredClear.fixupFactor8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
        (tableAddressTree B.high 0 1) site.guard t =
        registerXPhase (gd.map ClearPort.target) og u * registerXPhase (portTargets site.ports) os next.basis := by
      rw [MeasuredClear.fixupFactor8_append _ _ _ _ hog]
      congr 1
      · apply MeasuredClear.fixupFactor8_loaded gd og read low8 (hot8 site) _ site.guard B.hp
          (hot8_injective site) hdlow hbank t u hhot
        intro p hp
        rw [hsplit, haddr, hguard]
        exact hgarb p hp
      · have h := MeasuredClear.fixupFactor_recycled8 (clearData site.ports) os read low8 (hot8 site)
          (tableAddressTree B.high 0 1) site.guard B.hp (hot8_injective site) hdlow hbank
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
    linear_combination ((if next.phase = true then (-1 : ℂ) else 1) * registerXResetMagnitude (portTargets site.ports).length *
      c * registerXPhase (gd.map ClearPort.target) og u) * hsq

/-! #### Arithmetic, then the fused clear -/

/-- The site's guard survives its arithmetic: it is the window root, or the arithmetic is one
literal program that never touches it. -/
def GuardKept {n} (site : MaskedSite n) : Prop :=
  site.guard = windowRoot ∨ ∃ p, site.arithmetic = [.literal p] ∧ site.guard ∉ ECDSAAdd.wires p

theorem guardKept_run {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n) (hk : GuardKept site)
    (hp : ∀ i ∈ site.arithmetic, PlacedPair B.bits B.paths windowRoot i) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid B.bits B.paths windowRoot a st) (m : List Bool) :
    (ECDSAAdd.run ((specialize site.arithmetic a).instantiate read) m st).basis site.guard = st.basis site.guard := by
  rcases hk with h | ⟨p, hp', hw⟩
  · rw [h, (strict_preserves read B.bits B.paths site.arithmetic a hp st hs m).2.2, hs.2.2]
  · rw [hp']
    show (ECDSAAdd.run ((specialize (wLiteral p) a).instantiate read) m st).basis site.guard = _
    rw [specialize_literal, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    exact ECDSAAdd.run_preserves_outside p m st _ hw

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

/-! #### Resources of the deferred tail -/

theorem fusedFix_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (gd : List (ClearPort n)) (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((fusedFix B site gd start refs).instantiate read history).tCount =
      7 * (tableAddressTree B.high 0 1).internalNodes + 1729 := by
  rw [fusedFix, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (by
    intro cursor rs h
    rw [castFinish_instantiate, MeasuredClear.fixupProgram_tCount8 _ rs low8 (hot8 site) _ site.guard
      scratch8 B.hp hl])]

theorem deferTail_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (gd : List (ClearPort n)) (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (hal : LookupLayouts B.bits B.paths windowRoot (normalizeW site.arithmetic))
    (start : Nat) (history : Fin start → Bool) :
    ((deferTail B site gd start).instantiate read history).tCount =
      7 * literalToffolis (normalizeW site.arithmetic) +
        7 * traversals (normalizeW site.arithmetic) * (2 ^ B.bits.length - 1) +
        (7 * (tableAddressTree B.high 0 1).internalNodes + 1729) := by
  rw [deferTail, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (by
    intro cursor grefs h
    rw [castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => fusedFix_tCount read B site gd hl _ _ h'),
      compile_tCount read _ _ _ _ hal])]

theorem fusedFix_slots {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n))
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp) (start : Nat) (refs : List (Fin start)) :
    (fusedFix B site gd start refs).gateSlots =
      1024 * min (gd.length + site.ports.length) (refs.length + site.ports.length) *
        (tableAddressTree B.high 0 1).leaves + 10 * (tableAddressTree B.high 0 1).internalNodes + 2291 := by
  rw [fusedFix, castFinish_gateSlots, MeasuredClear.measureThen_slots _
    (fun k => 1024 * min (gd ++ clearData site.ports).length k * (tableAddressTree B.high 0 1).leaves +
      10 * (tableAddressTree B.high 0 1).internalNodes + 2291)
    (by intro cursor rs; rw [castFinish_gateSlots, MeasuredClear.fixupProgram_slots8 _ rs low8 (hot8 site) _
      site.guard scratch8 B.hp hl])]
  simp [clearData]

theorem deferTail_slots {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n))
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (hal : LookupLayouts B.bits B.paths windowRoot (normalizeW site.arithmetic)) (start : Nat) :
    (deferTail B site gd start).gateSlots = codeSlots B.bits (normalizeW site.arithmetic) +
      (1024 * (gd.length + site.ports.length) * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 2291) := by
  rw [deferTail, castFinish_gateSlots, MeasuredClear.measureThen_slots _
    (fun k => codeSlots B.bits (normalizeW site.arithmetic) +
      (1024 * min (gd.length + site.ports.length) (k + site.ports.length) * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 2291))
    (by intro cursor grefs; rw [castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ hal,
      fusedFix_slots B site gd hl]; simp)]
  simp

theorem deferTail_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (gd : List (ClearPort n))
    (hlit : ∀ p, WInstr.literal p ∈ site.arithmetic → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (deferTail B site gd start).WellFormed := by
  obtain ⟨hl, hdlow, hbank, hs, hshot, -, -⟩ := site_clear_facts B hB site hg
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
    exact MeasuredClear.fixupProgram_wellFormed8 _ rs low8 (hot8 site) _ site.guard scratch8 B.hp hl
      (hot8_injective site) hdlow hs hshot

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
  exact MeasuredClear.fixupProgram_residue8 _ _ _ _ _ _ _ _

theorem deferTail_support {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hk : SiteKind site)
    (gd : List (ClearPort n)) (S : List Wire)
    (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low8 i ∈ S)
    (hhigh : B.high ⊆ S) (hpaths : B.paths ⊆ S) (hroot : windowRoot ∈ S) (hbits : B.bits ⊆ S)
    (hgd : gd.map ClearPort.target ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ site.arithmetic → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ site.arithmetic → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (deferTail B site gd start) ⊆ S := by
  have hmem := kind_hot8 site hk
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
  apply MeasuredClear.fixupProgram_within8 _ _ _ _ _ _ _ _ S hgS (hpaths hB.scr.1) hlow
    (fun i => hS (hmem i)) _ (fun w hw => hpaths (hB.sub w hw))
  intro w hw
  apply hhigh
  rw [← hB.index]
  exact List.mem_dedup.mpr hw

/-- The triple site's arithmetic is one uncontrolled constant addition on the dialog pool, which
never touches its guard `generic`. -/
theorem guard_not_program (L : ECDSAAdd.Arithmetic.MeasuredCanonicalModLayout) (c p : Nat) (w : Wire)
    (hw : w ∉ L.wires) : w ∉ ECDSAAdd.wires (L.program c p) :=
  fun h => hw (List.mem_toFinset.mp (L.program_wires_subset c p h))

theorem triple_guardKept : GuardKept WEXFast.tripleSite := by
  have hw : streamLayout.core.generic ∉ (streamLayout.recoveryConstant streamLayout.point.x).wires := by
    decide +kernel
  exact Or.inr ⟨(streamLayout.recoveryConstant streamLayout.point.x).program
    ECDSAAdd.Arithmetic.SquareReduction.c ECDSAAdd.p, rfl, guard_not_program _ _ _ _ hw⟩

/-- The second fast site is guarded by the window root. -/
theorem site2_guardKept : GuardKept WEXFast.site2F.site := Or.inl rfl

end
end ShorECDLP.Entrant.WideBank8

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
def windowBits : List Wire := List.range' 855 15 ++ [871]
def pathBank : List Wire := List.range' 14832 15 ++ [10000]
/-- The eight high address bits; the low eight `855..862` feed the hot bank. -/
def high : List Wire := List.range' 863 7 ++ [871]
/-- The clear path bank is the first eight bank wires; the ninth, `14840`, is the dirty scratch. -/
def bank15 : PathShare.Bank := ⟨windowBits, high, List.range' 14832 8, pathBank⟩
theorem high_nodes : (tableAddressTree high 0 1).internalNodes = 255 := by
  have h := tableAddressTree_nodes high 0 1
  rw [show high.length = 8 from rfl] at h
  omega
theorem slots_append_wide {n} (a b : WCode n) :
    codeSlots windowBits (a ++ b) = codeSlots windowBits a + codeSlots windowBits b := by
  induction a with
  | nil => simp [codeSlots]
  | cons i a ih => cases i <;> simp [codeSlots, ih, Nat.add_assoc]
theorem splitAddress (s : BasisState) :
    256 * (tableAddressTree high 0 1).routeLabel s + MeasuredClear.hotAddress8 low8 s =
      tableAddressValue windowBits s := by
  exact MeasuredClear.splitAddress_value8 low8 high s
theorem bank15_ok : BankOK bank15 where
  split := splitAddress
  high := by intro v hv; simp only [bank15, high, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
  index := tableAddressTree_index _ _ _ (by decide)
  nodup := by decide
  len := by decide
  sub := by intro v hv; simp only [bank15, pathBank, List.mem_range'_1, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; dsimp only [Wire] at *; omega
  out := by intro v hv; simp only [bank15, List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
  bitsLen := by decide
  scr := by
    refine ⟨?_, ?_⟩
    · simp only [bank15, pathBank, scratch8, List.mem_append, List.mem_range'_1]; omega
    · simp only [bank15, scratch8, List.mem_range'_1]; omega

/-! The re-balanced bank keeps the old bank's address bits and lookup paths, so the
bank-independent row geometry transfers; only the clear tree (`high`, `hp`) changed. -/
theorem siteGeo_new {n} {site : MaskedSite n} (h : SiteGeoP (Geometry.bank .w16) site) :
    SiteGeoP bank15 site :=
  ⟨h.placed, h.kind⟩

theorem blockGeo_new {n} {b : Block2 n} (h : BlockGeoP2 (Geometry.bank .w16) b) : BlockGeoP2 bank15 b := by
  cases b with
  | plain code => exact h
  | unit u => exact ⟨h.placed, siteGeo_new h.site⟩
end
end ShorECDLP.Entrant.WideBank8.Fast16

section
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-! ### Controlled swap layers -/

/-- Pairwise controlled swaps of two aligned registers. -/
def swapLayer (c : Wire) : List Wire → List Wire → ECDSAAdd.Program
  | a :: as, b :: bs => cswap c a b ++ swapLayer c as bs
  | _, _ => []

theorem swapLayer_meas (c : Wire) : ∀ as bs : List Wire, ECDSAAdd.measurementCount (swapLayer c as bs) = 0
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    rw [swapLayer, ECDSAAdd.measurementCount_append, swapLayer_meas c as bs]
    rfl

theorem swapLayer_toff (c : Wire) : ∀ as bs : List Wire,
    ECDSAAdd.toffoliCount (swapLayer c as bs) = min as.length bs.length
  | [], _ => by simp [swapLayer, ECDSAAdd.toffoliCount]
  | _ :: _, [] => by simp [swapLayer, ECDSAAdd.toffoliCount]
  | a :: as, b :: bs => by
    rw [swapLayer, ECDSAAdd.toffoliCount_append, swapLayer_toff c as bs]
    have h1 : ECDSAAdd.toffoliCount (cswap c a b) = 1 := rfl
    simp only [List.length_cons]
    omega

theorem swapLayer_slots (c : Wire) : ∀ as bs : List Wire,
    ECDSAAdd.Challenge.gateSlots (swapLayer c as bs) = 3 * min as.length bs.length
  | [], _ => by simp [swapLayer, ECDSAAdd.Challenge.gateSlots]
  | _ :: _, [] => by simp [swapLayer, ECDSAAdd.Challenge.gateSlots]
  | a :: as, b :: bs => by
    rw [swapLayer, ECDSAAdd.Challenge.gateSlots_append, swapLayer_slots c as bs]
    have h3 : ECDSAAdd.Challenge.gateSlots (cswap c a b) = 3 := rfl
    simp only [List.length_cons]
    omega

theorem swapLayer_wires (c : Wire) : ∀ as bs : List Wire,
    ECDSAAdd.wires (swapLayer c as bs) ⊆ (c :: as ++ bs).toFinset
  | [], _ => by simp [swapLayer, ECDSAAdd.wires]
  | _ :: _, [] => by simp [swapLayer, ECDSAAdd.wires]
  | a :: as, b :: bs => by
    rw [swapLayer, ECDSAAdd.wires_append]
    apply Finset.union_subset
    · have hw3 : ECDSAAdd.wires (cswap c a b) = [c,a,b].toFinset := by
        ext w; simp [cswap, ECDSAAdd.wires, ECDSAAdd.Instr.wires]; tauto
      rw [hw3]
      intro w hw
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append]
      rcases hw with rfl | rfl | rfl <;> simp
    · intro w hw
      have h := swapLayer_wires c as bs hw
      simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append] at h ⊢
      rcases h with h | h | h <;> simp [h]

theorem swapLayer_valid (c : Wire) : ∀ as bs : List Wire, c ∉ as ++ bs → (as ++ bs).Nodup →
    ∀ i ∈ swapLayer c as bs, ECDSAAdd.Challenge.instructionValid i
  | [], _, _, _ => by simp [swapLayer]
  | _ :: _, [], _, _ => by simp [swapLayer]
  | a :: as, b :: bs, hc, hn => by
    have hca : c ≠ a := fun h => hc (by simp [h])
    have hcb : c ≠ b := fun h => hc (by simp [h])
    have hc' : c ∉ as ++ bs := fun h => hc (by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h ⊢; tauto)
    have hn1 := List.nodup_cons.mp (by simpa only [List.cons_append] using hn)
    have hab : a ≠ b := fun h => hn1.1 (by simp [h])
    have hn' : (as ++ bs).Nodup := hn1.2.sublist ((List.sublist_cons_self b bs).append_left as)
    intro i hi
    rw [swapLayer, List.mem_append] at hi
    rcases hi with hi | hi
    · simp only [cswap, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact Ne.symm hab
      · exact ⟨hca, hcb, hab⟩
      · exact Ne.symm hab
    · exact swapLayer_valid c as bs hc' hn' i hi

/-- Both registers of a layer are permuted in place; wires outside are untouched. -/
theorem swapLayer_run (c : Wire) : ∀ (as bs : List Wire), c ∉ as ++ bs → (as ++ bs).Nodup →
    as.length = bs.length → ∀ (s : ECDSAAdd.State) (m : List Bool),
    (ECDSAAdd.run (swapLayer c as bs) m s).phase = s.phase ∧
    (∀ w, w ∉ as → w ∉ bs → (ECDSAAdd.run (swapLayer c as bs) m s).basis w = s.basis w) ∧
    (∀ i (ha : i < as.length) (hb : i < bs.length),
      (ECDSAAdd.run (swapLayer c as bs) m s).basis (getElem as i ha) =
        (if s.basis c then s.basis (getElem bs i hb) else s.basis (getElem as i ha)) ∧
      (ECDSAAdd.run (swapLayer c as bs) m s).basis (getElem bs i hb) =
        (if s.basis c then s.basis (getElem as i ha) else s.basis (getElem bs i hb)))
  | [], bs, _, _, _, s, m => by
    refine ⟨rfl, fun _ _ _ => rfl, ?_⟩
    intro i ha
    simp at ha
  | a :: as, [], _, _, hl, _, _ => by simp at hl
  | a :: as, b :: bs, hc, hn, hl, s, m => by
    have hca : c ≠ a := fun h => hc (by simp [h])
    have hcb : c ≠ b := fun h => hc (by simp [h])
    have hc' : c ∉ as ++ bs := fun h => hc (by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h ⊢; tauto)
    have hn1 := List.nodup_cons.mp (by simpa only [List.cons_append] using hn)
    have hab : a ≠ b := fun h => hn1.1 (by simp [h])
    have ha_as : a ∉ as := fun h => hn1.1 (by simp [h])
    have ha_bs : a ∉ bs := fun h => hn1.1 (by simp [h])
    have hn2 := List.nodup_cons.mp (List.nodup_append_comm.mp hn1.2)
    have hb_bs : b ∉ bs := fun h => hn2.1 (by simp [h])
    have hb_as : b ∉ as := fun h => hn2.1 (by simp [h])
    have hn' : (as ++ bs).Nodup := hn1.2.sublist ((List.sublist_cons_self b bs).append_left as)
    have hl' : as.length = bs.length := by simpa using hl
    have hnd : [c, a, b].Nodup := by simp [hca, hcb, hab]
    rw [swapLayer, ECDSAAdd.run_append]
    have hm0 : ECDSAAdd.measurementCount (cswap c a b) = 0 := rfl
    rw [hm0, List.take_zero, List.drop_zero]
    obtain ⟨hp, hf, hA, hB⟩ := cswap_correct c a b hnd s List.nil
    obtain ⟨ihp, ihf, ihz⟩ := swapLayer_run c as bs hc' hn' hl' (ECDSAAdd.run (cswap c a b) List.nil s) m
    refine ⟨ihp.trans hp, ?_, ?_⟩
    · intro w hw1 hw2
      have hwa : w ≠ a := fun h => hw1 (by simp [h])
      have hwb : w ≠ b := fun h => hw2 (by simp [h])
      rw [ihf w (fun h => hw1 (by simp [h])) (fun h => hw2 (by simp [h])), hf w hwa hwb]
    · intro i ha hb
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [ihf a ha_as ha_bs, ihf b hb_as hb_bs, hA, hB]
        exact ⟨rfl, rfl⟩
      | succ j =>
        simp only [List.getElem_cons_succ]
        have hja : j < as.length := by simpa using ha
        have hjb : j < bs.length := by simpa using hb
        obtain ⟨h1, h2⟩ := ihz j hja hjb
        have hma : getElem as j hja ∈ as := List.getElem_mem hja
        have hmb : getElem bs j hjb ∈ bs := List.getElem_mem hjb
        rw [h1, h2, hf c hca hcb, hf (getElem as j hja) (fun h => ha_as (h ▸ hma)) (fun h => hb_as (h ▸ hma)),
          hf (getElem bs j hjb) (fun h => ha_bs (h ▸ hmb)) (fun h => hb_bs (h ▸ hmb))]
        exact ⟨rfl, rfl⟩

/-! ### Fast sites -/

/-- A masked site with three garbage registers aligned with its ports. -/
structure FastSite (n : Nat) where
  site : MaskedSite n
  g1 : List Wire
  g2 : List Wire
  g3 : List Wire

/-- Ports of one register, reading row `rowOf a` at the compiled address `a`. -/
def regPorts {n} (rowOf : Nat → Nat) (ports : List (LookupPort n)) (g : List Wire) :
    List (LookupPort n) :=
  List.zipWith (fun (p : LookupPort n) (w : Wire) => ⟨fun a => p.ref (rowOf a), p.value, w⟩) ports g

theorem regPorts_targets {n} (rowOf : Nat → Nat) : ∀ (ports : List (LookupPort n)) (g : List Wire),
    g.length = ports.length → portTargets (regPorts rowOf ports g) = g
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, w :: g, h => by
    have e : regPorts rowOf (p :: ps) (w :: g) =
        ⟨fun a => p.ref (rowOf a), p.value, w⟩ :: regPorts rowOf ps g := rfl
    rw [e]
    simp only [portTargets, List.map_cons]
    exact congrArg (List.cons w) (regPorts_targets rowOf ps g (by simpa using h))

namespace FastSite
variable {n : Nat} (f : FastSite n)

def garb : List Wire := f.g1 ++ f.g2 ++ f.g3
def ghot (i : Fin 256) : Wire := f.g1.headD 0 + i.val

def rowOf1 (a : Nat) : Nat := 4 * (a / 4) + (1 - a % 2)
def rowOf2 (a : Nat) : Nat := 4 * (a / 4) + 2 * (1 - a / 2 % 2) + a % 2
def rowOf3 (a : Nat) : Nat := 4 * (a / 4) + 3 - a % 2

def selPorts : List (LookupPort n) :=
  f.site.ports.map (fun p => ⟨fun h => p.ref (4 * h), p.value, p.target⟩) ++
  regPorts (fun h => 4 * h + 1) f.site.ports f.g1 ++ regPorts (fun h => 4 * h + 2) f.site.ports f.g2 ++
  regPorts (fun h => 4 * h + 3) f.site.ports f.g3

def garbPorts : List (LookupPort n) :=
  regPorts rowOf1 f.site.ports f.g1 ++ regPorts rowOf2 f.site.ports f.g2 ++ regPorts rowOf3 f.site.ports f.g3

def swapNet : ECDSAAdd.Program :=
  swapLayer 855 (portTargets f.site.ports) f.g1 ++ swapLayer 855 f.g2 f.g3 ++
    swapLayer 856 (portTargets f.site.ports) f.g2

def selCode : WCode n := [.lookup (some f.site.guard) f.selPorts]

end FastSite

def selBits : List Wire := List.range' 857 13 ++ [871]
def selPaths : List Wire := List.range' 14834 13 ++ [10000]
/-- The clear path bank of the garbage clears: the first eight bank wires (`bank15.hp`). -/
def bankHp : List Wire := List.range' 14832 8

theorem windowBits_eq : windowBits = 855 :: 856 :: selBits := rfl

/-- Geometry of a fast site at width 15. -/
structure FastGeometry {n} (f : FastSite n) : Prop where
  site : SiteGeoP bank15 f.site
  len1 : f.g1.length = f.site.ports.length
  len2 : f.g2.length = f.site.ports.length
  len3 : f.g3.length = f.site.ports.length
  nodup : (portTargets f.site.ports ++ f.garb).Nodup
  bounds : ∀ w ∈ f.garb, 14115 ≤ w ∧ oldWork w
  free : ∀ w ∈ f.garb, w < 14832 ∨ 14847 ≤ w
  head : f.g1.headD 0 ∈ f.g1
  bank : ∀ i : Fin 256, f.ghot i ∈ f.g1

namespace FastSite
variable {n : Nat} (f : FastSite n)

@[simp] theorem portTargets_append (a b : List (LookupPort n)) : portTargets (a ++ b) = portTargets a ++ portTargets b := by
  simp [portTargets]

theorem selPorts_targets (hg : FastGeometry f) : portTargets f.selPorts = portTargets f.site.ports ++ f.garb := by
  simp only [selPorts, portTargets_append, regPorts_targets _ _ _ hg.len1, regPorts_targets _ _ _ hg.len2,
    regPorts_targets _ _ _ hg.len3, garb, List.append_assoc]
  congr 1
  simp [portTargets, List.map_map, Function.comp_def]

theorem garbPorts_targets (hg : FastGeometry f) : portTargets f.garbPorts = f.garb := by
  simp only [garbPorts, portTargets_append, regPorts_targets _ _ _ hg.len1, regPorts_targets _ _ _ hg.len2,
    regPorts_targets _ _ _ hg.len3, garb]

theorem garbPorts_length (hg : FastGeometry f) : f.garbPorts.length = f.garb.length := by
  have h := congrArg List.length (garbPorts_targets f hg)
  simpa [portTargets] using h

theorem selPorts_length (hg : FastGeometry f) : f.selPorts.length = 4 * f.site.ports.length := by
  have h := congrArg List.length (selPorts_targets f hg)
  simp only [portTargets, List.length_map, List.length_append, garb, hg.len1, hg.len2, hg.len3] at h
  omega

theorem garb_length (hg : FastGeometry f) : f.garb.length = 3 * f.site.ports.length := by
  simp only [garb, List.length_append, hg.len1, hg.len2, hg.len3]
  omega

theorem swapNet_meas : ECDSAAdd.measurementCount f.swapNet = 0 := by
  simp [swapNet, ECDSAAdd.measurementCount_append, swapLayer_meas]

theorem swapNet_toff (hg : FastGeometry f) : ECDSAAdd.toffoliCount f.swapNet = 3 * f.site.ports.length := by
  have ht : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  simp only [swapNet, ECDSAAdd.toffoliCount_append, swapLayer_toff, ht, hg.len1, hg.len2, hg.len3, Nat.min_self]
  omega

theorem swapNet_slots (hg : FastGeometry f) : ECDSAAdd.Challenge.gateSlots f.swapNet = 9 * f.site.ports.length := by
  have ht : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  simp only [swapNet, ECDSAAdd.Challenge.gateSlots_append, swapLayer_slots, ht, hg.len1, hg.len2, hg.len3, Nat.min_self]
  omega

theorem swapNet_wires : ECDSAAdd.wires f.swapNet ⊆ (855 :: 856 :: portTargets f.site.ports ++ f.garb).toFinset := by
  simp only [swapNet, ECDSAAdd.wires_append]
  refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
  · intro w hw
    have h := swapLayer_wires 855 _ _ hw
    simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, garb] at h ⊢
    tauto
  · intro w hw
    have h := swapLayer_wires 855 _ _ hw
    simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, garb] at h ⊢
    tauto
  · intro w hw
    have h := swapLayer_wires 856 _ _ hw
    simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, garb] at h ⊢
    tauto

/-- Facts drawn from the geometry. -/
theorem facts (hg : FastGeometry f) :
    (portTargets f.site.ports).Nodup ∧ (∀ w ∈ portTargets f.site.ports, 14115 ≤ w ∧ oldWork w) ∧
    (f.site.guard = 14113 ∨ f.site.guard = 10015) ∧ f.site.ports.length ≤ 771 ∧
    f.garb.Nodup ∧ (∀ w ∈ f.garb, w ∉ portTargets f.site.ports) ∧
    (∀ w ∈ portTargets f.site.ports ++ f.garb, 14115 ≤ w ∧ oldWork w) := by
  obtain ⟨hn, hbd, -, -, -, hgd, hlen⟩ := kind_facts f.site hg.site.kind
  have hnd := List.nodup_append.mp hg.nodup
  refine ⟨hn, hbd, hgd, hlen, hnd.2.1, ?_, ?_⟩
  · intro w hw hm
    exact hnd.2.2 w hm w hw rfl
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hbd w h
    · exact hg.bounds w h

theorem garb_nodup (hg : FastGeometry f) : f.garb.Nodup := (facts f hg).2.2.2.2.1

theorem g1_sub : ∀ w ∈ f.g1, w ∈ f.garb := fun w hw => by simp [garb, hw]
theorem g2_sub : ∀ w ∈ f.g2, w ∈ f.garb := fun w hw => by simp [garb, hw]
theorem g3_sub : ∀ w ∈ f.g3, w ∈ f.garb := fun w hw => by simp [garb, hw]

theorem guard_lt (hg : FastGeometry f) : f.site.guard < 14115 := by
  rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;> decide

theorem bank_not_targets (hg : FastGeometry f) : ∀ w ∈ pathBank, w ∉ portTargets f.site.ports := by
  intro w hw ht
  have hlast := hg.site.placed (.lookup (some f.site.guard) f.site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  exact List.disjoint_left.mp hlast.2.2
    (show w ∈ windowRoot :: lookupRoot windowRoot (some f.site.guard) :: bank15.bits ++ bank15.paths by
      simp [bank15, hw]) ht

theorem bank_not_garb (hg : FastGeometry f) : ∀ w ∈ pathBank, w ∉ f.garb := by
  intro w hw hm
  have := hg.free w hm
  have hbd := (hg.bounds w hm).1
  simp only [pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  dsimp only [Wire] at *
  omega

theorem sel_free (hg : FastGeometry f) : ∀ w ∈ portTargets f.site.ports ++ f.garb, w < 14832 ∨ 14847 ≤ w := by
  intro w hw
  by_contra h
  have hb : w ∈ pathBank := by
    simp only [pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; dsimp only [Wire] at *; omega
  rcases List.mem_append.mp hw with h1 | h1
  · exact bank_not_targets f hg w hb h1
  · exact bank_not_garb f hg w hb h1

theorem site_bank_layout (hg : FastGeometry f) : (tableAddressTree high 0 1).Layout f.site.guard bankHp := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide +kernel)
  rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;> decide +kernel

end FastSite

/-! ### The compiled fast block -/

namespace FastSite
variable {n : Nat} (f : FastSite n)

def selProgram (start : Nat) := compile selBits selPaths windowRoot f.selCode start

def swapProgram (start : Nat) : Straight n start (start + 0) :=
  literalFixed f.swapNet 0 ((literal_meas (n := n) _).trans f.swapNet_meas) start

end FastSite

/-- A masked site with one garbage register aligned with its ports. -/
structure FastSite1 (n : Nat) where
  site : MaskedSite n
  g1 : List Wire

def selBits1 : List Wire := List.range' 856 14 ++ [871]
def selPaths1 : List Wire := List.range' 14833 14 ++ [10000]

theorem windowBits_eq1 : windowBits = 855 :: selBits1 := rfl

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

def garb : List Wire := f.g1
def ghot (i : Fin 256) : Wire := f.g1.headD 0 + i.val
def rowOf1 (a : Nat) : Nat := 2 * (a / 2) + (1 - a % 2)

def selPorts : List (LookupPort n) :=
  f.site.ports.map (fun p => ⟨fun h => p.ref (2 * h), p.value, p.target⟩) ++
  regPorts (fun h => 2 * h + 1) f.site.ports f.g1

def garbPorts : List (LookupPort n) := regPorts rowOf1 f.site.ports f.g1

def swapNet : ECDSAAdd.Program := swapLayer 855 (portTargets f.site.ports) f.g1

def selCode : WCode n := [.lookup (some f.site.guard) f.selPorts]

end FastSite1

/-- Geometry of a two-register fast site at width 15. -/
structure FastGeometry1 {n} (f : FastSite1 n) : Prop where
  site : SiteGeoP bank15 f.site
  len1 : f.g1.length = f.site.ports.length
  nodup : (portTargets f.site.ports ++ f.garb).Nodup
  bounds : ∀ w ∈ f.garb, 14115 ≤ w ∧ oldWork w
  free : ∀ w ∈ f.garb, w < 14832 ∨ 14847 ≤ w
  head : f.g1.headD 0 ∈ f.g1
  bank : ∀ i : Fin 256, f.ghot i ∈ f.g1

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem selPorts_targets (hg : FastGeometry1 f) : portTargets f.selPorts = portTargets f.site.ports ++ f.garb := by
  simp only [selPorts, FastSite.portTargets_append, regPorts_targets _ _ _ hg.len1, garb]
  congr 1
  simp [portTargets, List.map_map, Function.comp_def]

theorem garbPorts_targets (hg : FastGeometry1 f) : portTargets f.garbPorts = f.garb := by
  simp only [garbPorts, regPorts_targets _ _ _ hg.len1, garb]

theorem garbPorts_length (hg : FastGeometry1 f) : f.garbPorts.length = f.garb.length := by
  have h := congrArg List.length (garbPorts_targets f hg)
  simpa [portTargets] using h

theorem selPorts_length (hg : FastGeometry1 f) : f.selPorts.length = 2 * f.site.ports.length := by
  have h := congrArg List.length (selPorts_targets f hg)
  simp only [portTargets, List.length_map, List.length_append, garb, hg.len1] at h
  omega

theorem garb_length (hg : FastGeometry1 f) : f.garb.length = f.site.ports.length := by
  simp only [garb, hg.len1]

theorem swapNet_meas : ECDSAAdd.measurementCount f.swapNet = 0 := by
  simp [swapNet, swapLayer_meas]

theorem swapNet_toff (hg : FastGeometry1 f) : ECDSAAdd.toffoliCount f.swapNet = f.site.ports.length := by
  have ht : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  simp only [swapNet, swapLayer_toff, ht, hg.len1, Nat.min_self]

theorem swapNet_slots (hg : FastGeometry1 f) : ECDSAAdd.Challenge.gateSlots f.swapNet = 3 * f.site.ports.length := by
  have ht : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  simp only [swapNet, swapLayer_slots, ht, hg.len1, Nat.min_self]

theorem swapNet_wires : ECDSAAdd.wires f.swapNet ⊆ (855 :: portTargets f.site.ports ++ f.garb).toFinset := by
  intro w hw
  have h := swapLayer_wires 855 _ _ hw
  simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, garb] at h ⊢
  tauto

theorem facts (hg : FastGeometry1 f) :
    (portTargets f.site.ports).Nodup ∧ (∀ w ∈ portTargets f.site.ports, 14115 ≤ w ∧ oldWork w) ∧
    (f.site.guard = 14113 ∨ f.site.guard = 10015) ∧ f.site.ports.length ≤ 771 ∧
    f.garb.Nodup ∧ (∀ w ∈ f.garb, w ∉ portTargets f.site.ports) ∧
    (∀ w ∈ portTargets f.site.ports ++ f.garb, 14115 ≤ w ∧ oldWork w) := by
  obtain ⟨hn, hbd, -, -, -, hgd, hlen⟩ := kind_facts f.site hg.site.kind
  have hnd := List.nodup_append.mp hg.nodup
  refine ⟨hn, hbd, hgd, hlen, hnd.2.1, ?_, ?_⟩
  · intro w hw hm
    exact hnd.2.2 w hm w hw rfl
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hbd w h
    · exact hg.bounds w h

theorem garb_nodup (hg : FastGeometry1 f) : f.garb.Nodup := (facts f hg).2.2.2.2.1

theorem guard_lt (hg : FastGeometry1 f) : f.site.guard < 14115 := by
  rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;> decide

theorem bank_not_targets (hg : FastGeometry1 f) : ∀ w ∈ pathBank, w ∉ portTargets f.site.ports := by
  intro w hw ht
  have hlast := hg.site.placed (.lookup (some f.site.guard) f.site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  exact List.disjoint_left.mp hlast.2.2
    (show w ∈ windowRoot :: lookupRoot windowRoot (some f.site.guard) :: bank15.bits ++ bank15.paths by
      simp [bank15, hw]) ht

theorem bank_not_garb (hg : FastGeometry1 f) : ∀ w ∈ pathBank, w ∉ f.garb := by
  intro w hw hm
  have := hg.free w hm
  have hbd := (hg.bounds w hm).1
  simp only [pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  dsimp only [Wire] at *
  omega

theorem sel_free (hg : FastGeometry1 f) : ∀ w ∈ portTargets f.site.ports ++ f.garb, w < 14832 ∨ 14847 ≤ w := by
  intro w hw
  by_contra h
  have hb : w ∈ pathBank := by
    simp only [pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; dsimp only [Wire] at *; omega
  rcases List.mem_append.mp hw with h1 | h1
  · exact bank_not_targets f hg w hb h1
  · exact bank_not_garb f hg w hb h1

theorem site_bank_layout (hg : FastGeometry1 f) : (tableAddressTree high 0 1).Layout f.site.guard bankHp := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide +kernel)
  rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;> decide +kernel

def selProgram (start : Nat) := compile selBits1 selPaths1 windowRoot f.selCode start

def swapProgram (start : Nat) : Straight n start (start + 0) :=
  literalFixed f.swapNet 0 ((literal_meas (n := n) _).trans f.swapNet_meas) start

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16
end
/-! ### Semantics of the fast load -/

section
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

theorem mem_regPorts {n} (rowOf : Nat → Nat) (ports : List (LookupPort n)) (g : List Wire)
    (i : Nat) (hi : i < ports.length) (hgi : i < g.length) :
    (⟨fun a => (getElem ports i hi).ref (rowOf a), (getElem ports i hi).value, getElem g i hgi⟩ : LookupPort n) ∈
      regPorts rowOf ports g := by
  rw [List.mem_iff_getElem]
  refine ⟨i, by simp [regPorts]; omega, ?_⟩
  simp [regPorts, List.getElem_zipWith]

theorem of_mem_regPorts {n} (rowOf : Nat → Nat) (ports : List (LookupPort n)) (g : List Wire)
    (q : LookupPort n) (hq : q ∈ regPorts rowOf ports g) :
    ∃ i, ∃ (hi : i < ports.length) (hgi : i < g.length),
      q = ⟨fun a => (getElem ports i hi).ref (rowOf a), (getElem ports i hi).value, getElem g i hgi⟩ := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hq
  simp only [regPorts, List.length_zipWith] at hi
  refine ⟨i, by omega, by omega, ?_⟩
  rw [← he]
  simp [regPorts, List.getElem_zipWith]

namespace FastSite
variable {n : Nat} (f : FastSite n)

/-- Register `g`, aligned with `ports`, holds the word of row `r` under flag `flag`. -/
def Holds (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (g : List Wire) (r : Nat)
    (flag : Bool) (s : BasisState) : Prop :=
  ∀ i (hi : i < ports.length) (hgi : i < g.length),
    s (getElem g i hgi) = (flag && decide (read ((getElem ports i hi).ref r) = (getElem ports i hi).value))

theorem holds_frame (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (g : List Wire) (r : Nat)
    (flag : Bool) (s t : BasisState) (h : Holds read ports g r flag s) (hf : ∀ w ∈ g, t w = s w) :
    Holds read ports g r flag t := by
  intro i hi hgi
  rw [hf _ (List.getElem_mem hgi)]
  exact h i hi hgi

theorem holds_row (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (g : List Wire) (r r' : Nat)
    (flag : Bool) (s : BasisState) (h : Holds read ports g r flag s) (he : r = r') :
    Holds read ports g r' flag s := he ▸ h

theorem holds_swap (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (as bs : List Wire)
    (c : Wire) (r₁ r₂ : Nat) (flag : Bool) (s : ECDSAAdd.State) (m : List Bool)
    (hc : c ∉ as ++ bs) (hn : (as ++ bs).Nodup) (ha : as.length = ports.length) (hb : bs.length = ports.length)
    (h1 : Holds read ports as r₁ flag s.basis) (h2 : Holds read ports bs r₂ flag s.basis) :
    Holds read ports as (if s.basis c then r₂ else r₁) flag (ECDSAAdd.run (swapLayer c as bs) m s).basis ∧
    Holds read ports bs (if s.basis c then r₁ else r₂) flag (ECDSAAdd.run (swapLayer c as bs) m s).basis := by
  obtain ⟨-, -, hz⟩ := swapLayer_run c as bs hc hn (ha.trans hb.symm) s m
  constructor
  · intro i hi hai
    have hbi : i < bs.length := by omega
    rw [(hz i hai hbi).1]
    cases s.basis c
    · simpa using h1 i hi hai
    · simpa using h2 i hi hbi
  · intro i hi hbi
    have hai : i < as.length := by omega
    rw [(hz i hai hbi).2]
    cases s.basis c
    · simpa using h2 i hi hbi
    · simpa using h1 i hi hai

theorem sel_valid (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st) :
    SimulationValid selBits selPaths windowRoot (tableAddressValue selBits st.basis) st := by
  refine ⟨?_, rfl, hs.2.2⟩
  intro w hw
  apply hs.1
  simp only [selPaths, pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem address_split (st : BasisState) :
    tableAddressValue windowBits st = (st 855).toNat + 2 * ((st 856).toNat + 2 * tableAddressValue selBits st) := by
  simp only [windowBits_eq, tableAddressValue]

theorem swapNet_run (s : ECDSAAdd.State) :
    ECDSAAdd.run f.swapNet List.nil s =
      ECDSAAdd.run (swapLayer 856 (portTargets f.site.ports) f.g2) List.nil
        (ECDSAAdd.run (swapLayer 855 f.g2 f.g3) List.nil
          (ECDSAAdd.run (swapLayer 855 (portTargets f.site.ports) f.g1) List.nil s)) := by
  simp only [swapNet, ECDSAAdd.run_append, ECDSAAdd.measurementCount_append, swapLayer_meas,
    Nat.add_zero, List.take_zero, List.drop_zero, List.take_nil, List.drop_nil]

/-- Pairwise disjointness of the four registers. -/
theorem disjoints (hg : FastGeometry f) :
    (∀ w ∈ f.g1, w ∉ portTargets f.site.ports) ∧ (∀ w ∈ f.g2, w ∉ portTargets f.site.ports) ∧
    (∀ w ∈ f.g3, w ∉ portTargets f.site.ports) ∧ (∀ w ∈ f.g2, w ∉ f.g1) ∧ (∀ w ∈ f.g3, w ∉ f.g1) ∧
    (∀ w ∈ f.g3, w ∉ f.g2) := by
  have h := List.nodup_append.mp hg.nodup
  have hd : ∀ w ∈ f.garb, w ∉ portTargets f.site.ports := fun w hw hm => h.2.2 w hm w hw rfl
  have h' := List.nodup_append.mp h.2.1
  have h'' := List.nodup_append.mp h'.1
  refine ⟨fun w hw => hd w (g1_sub f w hw), fun w hw => hd w (g2_sub f w hw), fun w hw => hd w (g3_sub f w hw),
    fun w hw h1 => h''.2.2 w h1 w hw rfl, fun w hw h1 => ?_, fun w hw h2 => ?_⟩
  · exact h'.2.2 w (List.mem_append_left _ h1) w hw rfl
  · exact h'.2.2 w (List.mem_append_right _ h2) w hw rfl

/-- The state after the select traversal and the swap network. -/
theorem load_state (read : ConstantBit n → Bool) (hg : FastGeometry f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st)
    s₂.phase = st.phase ∧
    (∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₂.basis w = st.basis w) ∧
    Holds read f.site.ports (portTargets f.site.ports) a (st.basis f.site.guard) s₂.basis ∧
    Holds read f.site.ports f.g1 (rowOf1 a) (st.basis f.site.guard) s₂.basis ∧
    Holds read f.site.ports f.g2 (rowOf2 a) (st.basis f.site.guard) s₂.basis ∧
    Holds read f.site.ports f.g3 (rowOf3 a) (st.basis f.site.guard) s₂.basis := by
  intro s₂
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  obtain ⟨d1, d2, d3, d21, d31, d32⟩ := disjoints f hg
  have hsel := selPorts_targets f hg
  have hselnd : (portTargets f.selPorts).Nodup := by rw [hsel]; exact hg.nodup
  have hglt := guard_lt f hg
  have hguard : f.site.guard ∉ portTargets f.selPorts := by
    rw [hsel]; intro h; have := (hall _ h).1; dsimp only [Wire] at *; omega
  have lt : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  have g1s := g1_sub f
  have g2s := g2_sub f
  have g3s := g3_sub f
  -- stage 1
  set h := tableAddressValue selBits st.basis with hh
  have e1 : specialize f.selCode h = portTemplate (some f.site.guard) f.selPorts h := by
    simp [FastSite.selCode, specialize, WInstr.specialize]
  set s₁ := ECDSAAdd.run ((specialize f.selCode h).instantiate read) List.nil st with hs₁
  have r1 : s₁ = ⟨st.phase, tableXorState (portMask read f.selPorts h) (st.basis f.site.guard) st.basis⟩ := by
    rw [hs₁, e1]
    exact portTemplate_run read (some f.site.guard) f.selPorts h windowRoot List.nil st hselnd hguard hs.2.2
  have sel_at : ∀ q ∈ f.selPorts, s₁.basis q.target =
      (st.basis f.site.guard && decide (read (q.ref h) = q.value)) := by
    intro q hq
    rw [r1]
    show tableXorState _ _ _ q.target = _
    simp only [tableXorState]
    rw [port_selected read f.selPorts h hselnd q hq]
    have hz : st.basis q.target = false := by
      have hm : q.target ∈ portTargets f.selPorts := List.mem_map.mpr ⟨q, hq, rfl⟩
      rw [hsel] at hm
      exact hc _ hm
    rw [hz]
    simp
  have frame1 : ∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₁.basis w = st.basis w := by
    intro w h1 h2
    rw [r1]
    show tableXorState _ _ _ w = _
    apply tableXorState_outside
    intro hm
    have hm' : w ∈ portTargets f.selPorts := tableBitsMask_subset _ _ hm
    rw [hsel] at hm'
    rcases List.mem_append.mp hm' with h | h
    · exact h1 h
    · exact h2 h
  have H0 : Holds read f.site.ports (portTargets f.site.ports) (4*h) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq : (⟨fun h => (getElem f.site.ports i hi).ref (4*h), (getElem f.site.ports i hi).value,
        (getElem f.site.ports i hi).target⟩ : LookupPort n) ∈ f.selPorts := by
      simp only [FastSite.selPorts, List.mem_append]
      left; left; left
      exact List.mem_map.mpr ⟨getElem f.site.ports i hi, List.getElem_mem hi, rfl⟩
    have := sel_at _ hq
    simpa [portTargets, List.getElem_map] using this
  have H1 : Holds read f.site.ports f.g1 (4*h+1) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq := mem_regPorts (fun h => 4*h+1) f.site.ports f.g1 i hi hgi
    exact sel_at _ (by simp only [FastSite.selPorts, List.mem_append]; left; left; right; exact hq)
  have H2 : Holds read f.site.ports f.g2 (4*h+2) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq := mem_regPorts (fun h => 4*h+2) f.site.ports f.g2 i hi hgi
    exact sel_at _ (by simp only [FastSite.selPorts, List.mem_append]; left; right; exact hq)
  have H3 : Holds read f.site.ports f.g3 (4*h+3) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq := mem_regPorts (fun h => 4*h+3) f.site.ports f.g3 i hi hgi
    exact sel_at _ (by simp only [FastSite.selPorts, List.mem_append]; right; exact hq)
  -- stage 2
  have c855 : (855 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have c856 : (856 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have sub1 : List.Sublist (portTargets f.site.ports ++ f.g1) (portTargets f.site.ports ++ f.garb) :=
    ((List.sublist_append_left f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have sub2 : List.Sublist (f.g2 ++ f.g3) (portTargets f.site.ports ++ f.garb) := by
    have h23 : List.Sublist (f.g2 ++ f.g3) f.garb := by
      simp only [garb, List.append_assoc]
      exact List.sublist_append_right f.g1 (f.g2 ++ f.g3)
    exact h23.trans (List.sublist_append_right _ _)
  have sub3 : List.Sublist (portTargets f.site.ports ++ f.g2) (portTargets f.site.ports ++ f.garb) :=
    ((List.sublist_append_right f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have nd1 := hg.nodup.sublist sub1
  have nd2 := hg.nodup.sublist sub2
  have nd3 := hg.nodup.sublist sub3
  have c1 : (855 : Wire) ∉ portTargets f.site.ports ++ f.g1 := fun h => c855 (sub1.subset h)
  have c2 : (855 : Wire) ∉ f.g2 ++ f.g3 := fun h => c855 (sub2.subset h)
  have c3 : (856 : Wire) ∉ portTargets f.site.ports ++ f.g2 := fun h => c856 (sub3.subset h)
  have n855t : (855 : Wire) ∉ portTargets f.site.ports := fun h => c855 (List.mem_append_left _ h)
  have n855g : (855 : Wire) ∉ f.garb := fun h => c855 (List.mem_append_right _ h)
  have n856t : (856 : Wire) ∉ portTargets f.site.ports := fun h => c856 (List.mem_append_left _ h)
  have n856g : (856 : Wire) ∉ f.garb := fun h => c856 (List.mem_append_right _ h)
  set t₁ := ECDSAAdd.run (swapLayer 855 (portTargets f.site.ports) f.g1) List.nil s₁ with ht₁
  set t₂ := ECDSAAdd.run (swapLayer 855 f.g2 f.g3) List.nil t₁ with ht₂
  have hs₂ : s₂ = ECDSAAdd.run (swapLayer 856 (portTargets f.site.ports) f.g2) List.nil t₂ := by
    show ECDSAAdd.run f.swapNet List.nil s₁ = _
    rw [swapNet_run]
  obtain ⟨p1, fr1, -⟩ := swapLayer_run 855 _ _ c1 nd1 (by rw [lt, hg.len1]) s₁ List.nil
  obtain ⟨p2, fr2, -⟩ := swapLayer_run 855 _ _ c2 nd2 (by rw [hg.len2, hg.len3]) t₁ List.nil
  obtain ⟨p3, fr3, -⟩ := swapLayer_run 856 _ _ c3 nd3 (by rw [lt, hg.len2]) t₂ List.nil
  have frame : ∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₂.basis w = st.basis w := by
    intro w h1 h2
    rw [hs₂, fr3 w h1 (fun h => h2 (g2s w h)), ht₂, fr2 w (fun h => h2 (g2s w h)) (fun h => h2 (g3s w h)),
      ht₁, fr1 w h1 (fun h => h2 (g1s w h)), frame1 w h1 h2]
  have b0_1 : s₁.basis 855 = st.basis 855 := frame1 _ n855t n855g
  have b0_2 : t₁.basis 855 = st.basis 855 := by
    rw [ht₁, fr1 855 n855t (fun h => n855g (g1s _ h)), b0_1]
  have b1_3 : t₂.basis 856 = st.basis 856 := by
    rw [ht₂, fr2 856 (fun h => n856g (g2s _ h)) (fun h => n856g (g3s _ h)),
      ht₁, fr1 856 n856t (fun h => n856g (g1s _ h)), frame1 856 n856t n856g]
  -- layer 1: targets and g1
  obtain ⟨T1, G1⟩ := holds_swap read f.site.ports _ _ 855 (4*h) (4*h+1) (st.basis f.site.guard) s₁ List.nil
    c1 nd1 lt hg.len1 H0 H1
  rw [b0_1] at T1 G1
  have H2' := holds_frame read f.site.ports f.g2 _ _ _ _ H2
    (fun w hw => fr1 w (d2 w hw) (d21 w hw))
  have H3' := holds_frame read f.site.ports f.g3 _ _ _ _ H3
    (fun w hw => fr1 w (d3 w hw) (d31 w hw))
  -- layer 2: g2 and g3
  obtain ⟨G2, G3⟩ := holds_swap read f.site.ports _ _ 855 (4*h+2) (4*h+3) (st.basis f.site.guard) t₁ List.nil
    c2 nd2 hg.len2 hg.len3 H2' H3'
  rw [b0_2] at G2 G3
  have T2 := holds_frame read f.site.ports _ _ _ _ _ T1
    (fun w hw => fr2 w (fun h => d2 _ h hw) (fun h => d3 _ h hw))
  have G1' := holds_frame read f.site.ports f.g1 _ _ _ _ G1
    (fun w hw => fr2 w (fun h => d21 _ h hw) (fun h => d31 _ h hw))
  -- layer 3: targets and g2
  obtain ⟨T3, G2'⟩ := holds_swap read f.site.ports _ _ 856 _ _ (st.basis f.site.guard) t₂ List.nil
    c3 nd3 lt hg.len2 T2 G2
  rw [b1_3] at T3 G2'
  have G1'' := holds_frame read f.site.ports f.g1 _ _ _ _ G1'
    (fun w hw => fr3 w (d1 w hw) (fun h => d21 _ h hw))
  have G3' := holds_frame read f.site.ports f.g3 _ _ _ _ G3
    (fun w hw => fr3 w (d3 w hw) (d32 w hw))
  rw [← hs₂] at T3 G2' G1'' G3'
  -- rows
  have ha : a = (st.basis 855).toNat + 2 * ((st.basis 856).toNat + 2 * h) := by
    rw [← hs.2.1, address_split, ← hh]
  have hp : s₂.phase = st.phase := by rw [hs₂, p3, ht₂, p2, ht₁, p1, r1]
  refine ⟨hp, frame, ?_, ?_, ?_, ?_⟩
  · refine holds_row read _ _ _ _ _ _ T3 ?_
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1] at ha ⊢ <;> omega
  · refine holds_row read _ _ _ _ _ _ G1'' ?_
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf1] at ha ⊢ <;> omega
  · refine holds_row read _ _ _ _ _ _ G2' ?_
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf2] at ha ⊢ <;> omega
  · refine holds_row read _ _ _ _ _ _ G3' ?_
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf3] at ha ⊢ <;> omega

/-- Clearing the garbage leaves exactly the reference load. -/
theorem load_clear_eq (read : ConstantBit n → Bool) (hg : FastGeometry f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st)
    clearRegister f.garb s₂.basis = tableXorState (portMask read f.site.ports a) (st.basis f.site.guard) st.basis := by
  intro s₂
  obtain ⟨hp, frame, T, G1, G2, G3⟩ := load_state f read hg a st hs hc
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  funext w
  by_cases hw : w ∈ f.garb
  · rw [clearRegister_clean _ _ w hw, tableXorState_outside]
    · exact (hc w (List.mem_append_right _ hw)).symm
    · intro hm
      exact hdisj w hw (tableBitsMask_subset _ _ hm)
  · rw [MeasuredClear.clearRegister_frame _ _ _ hw]
    by_cases ht : w ∈ portTargets f.site.ports
    · unfold portTargets at ht
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have hT := T i hi (by simpa [portTargets] using hi)
      simp only [portTargets, List.getElem_map] at hT
      rw [hT]
      simp only [tableXorState]
      rw [port_selected read f.site.ports a hn _ (List.getElem_mem hi),
        hc _ (List.mem_append_left _ ht)]
      simp
    · rw [frame w ht hw, tableXorState_outside]
      intro hm
      exact ht (tableBitsMask_subset _ _ hm)

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)
/-! Semantics. -/

theorem sel_valid (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st) :
    SimulationValid selBits1 selPaths1 windowRoot (tableAddressValue selBits1 st.basis) st := by
  refine ⟨?_, rfl, hs.2.2⟩
  intro w hw
  apply hs.1
  simp only [selPaths1, pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem address_split (st : BasisState) :
    tableAddressValue windowBits st = (st 855).toNat + 2 * tableAddressValue selBits1 st := by
  simp only [windowBits_eq1, tableAddressValue]

theorem disjoints (hg : FastGeometry1 f) : ∀ w ∈ f.g1, w ∉ portTargets f.site.ports := by
  have h := List.nodup_append.mp hg.nodup
  exact fun w hw hm => h.2.2 w hm w hw rfl

/-- The state after the select traversal and the swap layer. -/
theorem load_state (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st)
    s₂.phase = st.phase ∧
    (∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₂.basis w = st.basis w) ∧
    FastSite.Holds read f.site.ports (portTargets f.site.ports) a (st.basis f.site.guard) s₂.basis ∧
    FastSite.Holds read f.site.ports f.g1 (rowOf1 a) (st.basis f.site.guard) s₂.basis := by
  intro s₂
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  have d1 := disjoints f hg
  have hsel := selPorts_targets f hg
  have hselnd : (portTargets f.selPorts).Nodup := by rw [hsel]; exact hg.nodup
  have hglt := guard_lt f hg
  have hguard : f.site.guard ∉ portTargets f.selPorts := by
    rw [hsel]; intro h; have := (hall _ h).1; dsimp only [Wire] at *; omega
  have lt : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  set h := tableAddressValue selBits1 st.basis with hh
  have e1 : specialize f.selCode h = portTemplate (some f.site.guard) f.selPorts h := by
    simp [FastSite1.selCode, specialize, WInstr.specialize]
  set s₁ := ECDSAAdd.run ((specialize f.selCode h).instantiate read) List.nil st with hs₁
  have r1 : s₁ = ⟨st.phase, tableXorState (portMask read f.selPorts h) (st.basis f.site.guard) st.basis⟩ := by
    rw [hs₁, e1]
    exact portTemplate_run read (some f.site.guard) f.selPorts h windowRoot List.nil st hselnd hguard hs.2.2
  have sel_at : ∀ q ∈ f.selPorts, s₁.basis q.target =
      (st.basis f.site.guard && decide (read (q.ref h) = q.value)) := by
    intro q hq
    rw [r1]
    show tableXorState _ _ _ q.target = _
    simp only [tableXorState]
    rw [port_selected read f.selPorts h hselnd q hq]
    have hz : st.basis q.target = false := by
      have hm : q.target ∈ portTargets f.selPorts := List.mem_map.mpr ⟨q, hq, rfl⟩
      rw [hsel] at hm
      exact hc _ hm
    rw [hz]
    simp
  have frame1 : ∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₁.basis w = st.basis w := by
    intro w h1 h2
    rw [r1]
    show tableXorState _ _ _ w = _
    apply tableXorState_outside
    intro hm
    have hm' : w ∈ portTargets f.selPorts := tableBitsMask_subset _ _ hm
    rw [hsel] at hm'
    rcases List.mem_append.mp hm' with h | h
    · exact h1 h
    · exact h2 h
  have H0 : FastSite.Holds read f.site.ports (portTargets f.site.ports) (2*h) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq : (⟨fun h => (getElem f.site.ports i hi).ref (2*h), (getElem f.site.ports i hi).value,
        (getElem f.site.ports i hi).target⟩ : LookupPort n) ∈ f.selPorts := by
      simp only [FastSite1.selPorts, List.mem_append]
      left
      exact List.mem_map.mpr ⟨getElem f.site.ports i hi, List.getElem_mem hi, rfl⟩
    have := sel_at _ hq
    simpa [portTargets, List.getElem_map] using this
  have H1 : FastSite.Holds read f.site.ports f.g1 (2*h+1) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq := mem_regPorts (fun h => 2*h+1) f.site.ports f.g1 i hi hgi
    exact sel_at _ (by simp only [FastSite1.selPorts, List.mem_append]; right; exact hq)
  have c855 : (855 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have n855t : (855 : Wire) ∉ portTargets f.site.ports := fun h => c855 (List.mem_append_left _ h)
  have n855g : (855 : Wire) ∉ f.garb := fun h => c855 (List.mem_append_right _ h)
  have c1 : (855 : Wire) ∉ portTargets f.site.ports ++ f.g1 := c855
  have nd1 : (portTargets f.site.ports ++ f.g1).Nodup := hg.nodup
  have hs₂ : s₂ = ECDSAAdd.run (swapLayer 855 (portTargets f.site.ports) f.g1) List.nil s₁ := rfl
  obtain ⟨p1, fr1, -⟩ := swapLayer_run 855 (portTargets f.site.ports) f.g1 c1 nd1 (by rw [lt, hg.len1]) s₁ List.nil
  have frame : ∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₂.basis w = st.basis w := by
    intro w h1 h2
    rw [hs₂, fr1 w h1 h2, frame1 w h1 h2]
  have b0_1 : s₁.basis 855 = st.basis 855 := frame1 _ n855t n855g
  obtain ⟨T1, G1⟩ := FastSite.holds_swap read f.site.ports _ _ 855 (2*h) (2*h+1) (st.basis f.site.guard) s₁ List.nil
    c1 nd1 lt hg.len1 H0 H1
  rw [b0_1] at T1 G1
  rw [← hs₂] at T1 G1
  have ha : a = (st.basis 855).toNat + 2 * h := by
    rw [← hs.2.1, address_split, ← hh]
  have hp : s₂.phase = st.phase := by rw [hs₂, p1, r1]
  refine ⟨hp, frame, ?_, ?_⟩
  · refine FastSite.holds_row read _ _ _ _ _ _ T1 ?_
    cases hb0 : st.basis 855 <;> simp [hb0] at ha ⊢ <;> omega
  · refine FastSite.holds_row read _ _ _ _ _ _ G1 ?_
    cases hb0 : st.basis 855 <;> simp [hb0, rowOf1] at ha ⊢ <;> omega

theorem load_clear_eq (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st)
    clearRegister f.garb s₂.basis = tableXorState (portMask read f.site.ports a) (st.basis f.site.guard) st.basis := by
  intro s₂
  obtain ⟨hp, frame, T, G1⟩ := load_state f read hg a st hs hc
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  funext w
  by_cases hw : w ∈ f.garb
  · rw [clearRegister_clean _ _ w hw, tableXorState_outside]
    · exact (hc w (List.mem_append_right _ hw)).symm
    · intro hm
      exact hdisj w hw (tableBitsMask_subset _ _ hm)
  · rw [MeasuredClear.clearRegister_frame _ _ _ hw]
    by_cases ht : w ∈ portTargets f.site.ports
    · unfold portTargets at ht
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have hT := T i hi (by simpa [portTargets] using hi)
      simp only [portTargets, List.getElem_map] at hT
      rw [hT]
      simp only [tableXorState]
      rw [port_selected read f.site.ports a hn _ (List.getElem_mem hi),
        hc _ (List.mem_append_left _ ht)]
      simp
    · rw [frame w ht hw, tableXorState_outside]
      intro hm
      exact ht (tableBitsMask_subset _ _ hm)

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16
end
/-! ### The garbage clear and the fast block simulation -/

section
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace FastSite
variable {n : Nat} (f : FastSite n)

theorem sel_placed (hg : FastGeometry f) :
    Placed selBits selPaths windowRoot (WInstr.lookup (n := n) (some f.site.guard) f.selPorts) := by
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  have hglt := guard_lt f hg
  refine ⟨?_, ?_, ?_⟩
  · show (f.site.guard :: selBits ++ selPaths).Nodup
    rcases hgd with e | e <;> rw [e] <;> decide +kernel
  · rw [selPorts_targets f hg]; exact hg.nodup
  · apply List.disjoint_left.mpr
    intro w hw hm
    rw [selPorts_targets f hg] at hm
    have h1 := (hall w hm).1
    have h2 := sel_free f hg w hm
    have hr : windowRoot = 10015 := rfl
    simp only [List.mem_cons, List.mem_append, selBits, selPaths, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, lookupRoot,
      Option.getD, hr] at hw
    dsimp only [Wire] at *
    omega

theorem sel_layouts (hg : FastGeometry f) : LookupLayouts selBits selPaths windowRoot f.selCode :=
  pair_layouts_of_placed selBits selPaths windowRoot f.selCode (by decide)
    (fun i hi => by
      simp only [FastSite.selCode, List.mem_singleton] at hi
      subst hi
      exact placed_implies_pair _ _ _ _ (sel_placed f hg))

theorem arith_pair (hg : FastGeometry f) :
    ∀ i ∈ f.site.arithmetic, PlacedPair windowBits pathBank windowRoot i := fun i hi =>
  placed_implies_pair _ _ _ _ (hg.site.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))

theorem arith_layouts (hg : FastGeometry f) :
    LookupLayouts windowBits pathBank windowRoot (normalizeW f.site.arithmetic) :=
  pair_layouts_of_placed _ _ _ _ (by simp [windowBits, pathBank])
    (pair_placed_normalize _ _ _ _ (arith_pair f hg))

theorem sel_records (hg : FastGeometry f) : codeRecords selBits selPaths windowRoot f.selCode = 16383 := by
  have h := single_lookup_records selBits selPaths windowRoot (some f.site.guard) f.selPorts (by decide)
    (sel_placed f hg).1
  simpa [FastSite.selCode] using h

theorem layer_facts (hg : FastGeometry f) :
    ((855 : Wire) ∉ portTargets f.site.ports ++ f.g1 ∧ (portTargets f.site.ports ++ f.g1).Nodup) ∧
    ((855 : Wire) ∉ f.g2 ++ f.g3 ∧ (f.g2 ++ f.g3).Nodup) ∧
    ((856 : Wire) ∉ portTargets f.site.ports ++ f.g2 ∧ (portTargets f.site.ports ++ f.g2).Nodup) := by
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  have c855 : (855 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have c856 : (856 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have sub1 : List.Sublist (portTargets f.site.ports ++ f.g1) (portTargets f.site.ports ++ f.garb) :=
    ((List.sublist_append_left f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have sub2 : List.Sublist (f.g2 ++ f.g3) (portTargets f.site.ports ++ f.garb) := by
    have h23 : List.Sublist (f.g2 ++ f.g3) f.garb := by
      simp only [garb, List.append_assoc]
      exact List.sublist_append_right f.g1 (f.g2 ++ f.g3)
    exact h23.trans (List.sublist_append_right _ _)
  have sub3 : List.Sublist (portTargets f.site.ports ++ f.g2) (portTargets f.site.ports ++ f.garb) :=
    ((List.sublist_append_right f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  exact ⟨⟨fun h => c855 (sub1.subset h), hg.nodup.sublist sub1⟩, ⟨fun h => c855 (sub2.subset h), hg.nodup.sublist sub2⟩,
    ⟨fun h => c856 (sub3.subset h), hg.nodup.sublist sub3⟩⟩

theorem swapNet_valid (hg : FastGeometry f) : ∀ i ∈ f.swapNet, ECDSAAdd.Challenge.instructionValid i := by
  obtain ⟨⟨c1, n1⟩, ⟨c2, n2⟩, ⟨c3, n3⟩⟩ := layer_facts f hg
  intro i hi
  simp only [swapNet, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact swapLayer_valid 855 _ _ c1 n1 i hi
  · exact swapLayer_valid 855 _ _ c2 n2 i hi
  · exact swapLayer_valid 856 _ _ c3 n3 i hi

/-! The garbage clear. -/

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in

attribute [local irreducible] MeasuredClear.measuredClear8 in

/-! The staged simulation. -/

def SwapSim (read : ConstantBit n → Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ address st, SimulationValid windowBits pathBank windowRoot address st →
    Clean (portTargets f.site.ports ++ f.garb) st.basis →
    b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st))

theorem swap_simulation (read : ConstantBit n → Bool) (hg : FastGeometry f) :
    ∃ cs : List ℂ, List.Forall₂ (f.SwapSim read)
      ((source read selBits selPaths windowRoot f.selCode).seq (literalSource f.swapNet)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hp1 : ∀ i ∈ f.selCode, PlacedPair selBits selPaths windowRoot i := by
    intro i hi
    simp only [FastSite.selCode, List.mem_singleton] at hi
    subst hi
    exact placed_implies_pair _ _ _ _ (sel_placed f hg)
  obtain ⟨c1, a1, m1⟩ := pair_source_simulation read selBits selPaths windowRoot (by decide) f.selCode hp1
  obtain ⟨c2, a2, m2⟩ := literal_simulation f.swapNet
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂ address st hs hc
    obtain ⟨m, hm, h₁⟩ := h₁
    have hm0 : m = [] := List.eq_nil_of_length_eq_zero (by simpa [FastSite.selCode, literalRecords] using hm)
    have hh0 : b₂.history = [] := List.eq_nil_of_length_eq_zero (by rw [h₂.1]; exact f.swapNet_meas)
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ _ st (sel_valid address st hs), map_smul, h₂.2, hm0, hh0]
    simp [smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def FastSim (read : ConstantBit n → Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords f.site.code ∧
    ∀ a st, SimulationValid windowBits pathBank windowRoot a st →
      Clean (portTargets f.site.ports ++ f.garb) st.basis →
      (∀ m, Clean (portTargets f.site.ports)
        (ECDSAAdd.run ((specialize f.site.code a).instantiate read) m st).basis) →
      b.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize f.site.code a).instantiate read) m st)

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem sel_placed (hg : FastGeometry1 f) :
    Placed selBits1 selPaths1 windowRoot (WInstr.lookup (n := n) (some f.site.guard) f.selPorts) := by
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  have hglt := guard_lt f hg
  refine ⟨?_, ?_, ?_⟩
  · show (f.site.guard :: selBits1 ++ selPaths1).Nodup
    rcases hgd with e | e <;> rw [e] <;> decide +kernel
  · rw [selPorts_targets f hg]; exact hg.nodup
  · apply List.disjoint_left.mpr
    intro w hw hm
    rw [selPorts_targets f hg] at hm
    have h1 := (hall w hm).1
    have h2 := sel_free f hg w hm
    have hr : windowRoot = 10015 := rfl
    simp only [List.mem_cons, List.mem_append, selBits1, selPaths1, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, lookupRoot,
      Option.getD, hr] at hw
    dsimp only [Wire] at *
    omega

theorem sel_layouts (hg : FastGeometry1 f) : LookupLayouts selBits1 selPaths1 windowRoot f.selCode :=
  pair_layouts_of_placed selBits1 selPaths1 windowRoot f.selCode (by decide)
    (fun i hi => by
      simp only [FastSite1.selCode, List.mem_singleton] at hi
      subst hi
      exact placed_implies_pair _ _ _ _ (sel_placed f hg))

theorem arith_pair (hg : FastGeometry1 f) :
    ∀ i ∈ f.site.arithmetic, PlacedPair windowBits pathBank windowRoot i := fun i hi =>
  placed_implies_pair _ _ _ _ (hg.site.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))

theorem arith_layouts (hg : FastGeometry1 f) :
    LookupLayouts windowBits pathBank windowRoot (normalizeW f.site.arithmetic) :=
  pair_layouts_of_placed _ _ _ _ (by simp [windowBits, pathBank])
    (pair_placed_normalize _ _ _ _ (arith_pair f hg))

theorem sel_records (hg : FastGeometry1 f) : codeRecords selBits1 selPaths1 windowRoot f.selCode = 32767 := by
  have h := single_lookup_records selBits1 selPaths1 windowRoot (some f.site.guard) f.selPorts (by decide)
    (sel_placed f hg).1
  simpa [FastSite1.selCode] using h

theorem layer_facts (hg : FastGeometry1 f) :
    (855 : Wire) ∉ portTargets f.site.ports ++ f.g1 ∧ (portTargets f.site.ports ++ f.g1).Nodup := by
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  exact ⟨fun h => by have := (hall _ h).1; dsimp only [Wire] at *; omega, hg.nodup⟩

theorem swapNet_valid (hg : FastGeometry1 f) : ∀ i ∈ f.swapNet, ECDSAAdd.Challenge.instructionValid i := by
  obtain ⟨c1, n1⟩ := layer_facts f hg
  exact swapLayer_valid 855 _ _ c1 n1

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in

attribute [local irreducible] MeasuredClear.measuredClear8 in

def SwapSim (read : ConstantBit n → Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ address st, SimulationValid windowBits pathBank windowRoot address st →
    Clean (portTargets f.site.ports ++ f.garb) st.basis →
    b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st))

theorem swap_simulation (read : ConstantBit n → Bool) (hg : FastGeometry1 f) :
    ∃ cs : List ℂ, List.Forall₂ (f.SwapSim read)
      ((source read selBits1 selPaths1 windowRoot f.selCode).seq (literalSource f.swapNet)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hp1 : ∀ i ∈ f.selCode, PlacedPair selBits1 selPaths1 windowRoot i := by
    intro i hi
    simp only [FastSite1.selCode, List.mem_singleton] at hi
    subst hi
    exact placed_implies_pair _ _ _ _ (sel_placed f hg)
  obtain ⟨c1, a1, m1⟩ := pair_source_simulation read selBits1 selPaths1 windowRoot (by decide) f.selCode hp1
  obtain ⟨c2, a2, m2⟩ := literal_simulation f.swapNet
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂ address st hs hc
    obtain ⟨m, hm, h₁⟩ := h₁
    have hm0 : m = [] := List.eq_nil_of_length_eq_zero (by simpa [FastSite1.selCode, literalRecords] using hm)
    have hh0 : b₂.history = [] := List.eq_nil_of_length_eq_zero (by rw [h₂.1]; exact f.swapNet_meas)
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ _ st (sel_valid address st hs), map_smul, h₂.2, hm0, hh0]
    simp [smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def FastSim (read : ConstantBit n → Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords f.site.code ∧
    ∀ a st, SimulationValid windowBits pathBank windowRoot a st →
      Clean (portTargets f.site.ports ++ f.garb) st.basis →
      (∀ m, Clean (portTargets f.site.ports)
        (ECDSAAdd.run ((specialize f.site.code a).instantiate read) m st).basis) →
      b.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize f.site.code a).instantiate read) m st)

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16
end

/-! ### Resources of one fast site on the pool bank, against the unit it replaces -/

section
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

/-- The unit a fast site replaces: the site's own load and arithmetic, then its measured clear. -/
def siteUnit {n} (site : MaskedSite n) : UnitSite n := ⟨site.prefix, site⟩

theorem siteUnit_code {n} (site : MaskedSite n) : (siteUnit site).code = site.code := rfl

theorem prefix_split {n} (site : MaskedSite n) :
    site.prefix = [WInstr.lookup (some site.guard) site.ports] ++ site.arithmetic := rfl

theorem bank_tree_nodes : (tableAddressTree bank15.high 0 1).internalNodes = 255 := high_nodes

theorem bank_tree_leaves : (tableAddressTree bank15.high 0 1).leaves = 256 := by
  rw [MeasuredClear.addressTree_leaves]; decide +kernel

theorem bank_pair_len : windowBits.length ≤ pathBank.length := by decide

theorem lookup_records_bank {n} (c : Option Wire) (ps : List (LookupPort n)) :
    literalRecords (normalizeW ([WInstr.lookup c ps] : WCode n)) = 0 ∧
      traversals (normalizeW ([WInstr.lookup c ps] : WCode n)) = 1 := by
  simp [normalizeW, normalizeWInstr, literalRecords, traversals]

namespace FastSite
variable {n : Nat} (f : FastSite n)

theorem site_layout_bank (hg : FastGeometry f) :
    (tableAddressTree bank15.high 0 1).Layout f.site.guard bank15.hp := site_bank_layout f hg

theorem prefix_layouts (hg : FastGeometry f) :
    LookupLayouts windowBits pathBank windowRoot (normalizeW f.site.prefix) :=
  pair_layouts_of_placed _ _ _ _ bank_pair_len
    (pair_placed_normalize _ _ _ _ (fun i hi =>
      placed_implies_pair _ _ _ _ (hg.site.placed i (List.mem_append_left _ hi))))

/-- Toffoli count of the fast block, in units of seven T gates. -/
def fastTP : Nat :=
  16383 + ECDSAAdd.toffoliCount f.swapNet + 502 +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502

theorem fast_tp_relation (hg : FastGeometry f) :
    f.fastTP + (48650 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  have hl : literalToffolis (normalizeW f.site.prefix) = literalToffolis (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalToffolis_append]
    simp [normalizeW, normalizeWInstr, literalToffolis]
  have ht : traversals f.site.prefix = traversals f.site.arithmetic + 1 := by
    rw [prefix_split, traversals_append]
    simp [traversals]
    omega
  have hb : 2 ^ bank15.bits.length - 1 = 65535 := by simp [bank15, windowBits]
  simp only [blockTP2, siteUnit, fastTP, hl, ht, hb, bank_tree_nodes]
  omega

theorem sel_slots (hg : FastGeometry f) : codeSlots selBits f.selCode = 65536 * f.site.ports.length + 163830 := by
  simp only [codeSlots, FastSite.selCode, selBits, List.length_range', List.length_append, List.length_cons, List.length_nil, selPorts_length f hg]
  norm_num
  try omega

theorem lookup_slots (c : Option Wire) (ps : List (LookupPort n)) :
    codeSlots windowBits (normalizeW ([WInstr.lookup c ps] : WCode n)) = 65536 * ps.length + 655350 := by
  simp [codeSlots, normalizeW, normalizeWInstr, windowBits]

def fastSlack : Nat := 262144 * f.garb.length + 3 * ECDSAAdd.Challenge.gateSlots f.swapNet

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem site_layout_bank (hg : FastGeometry1 f) :
    (tableAddressTree bank15.high 0 1).Layout f.site.guard bank15.hp := site_bank_layout f hg

theorem prefix_layouts (hg : FastGeometry1 f) :
    LookupLayouts windowBits pathBank windowRoot (normalizeW f.site.prefix) :=
  pair_layouts_of_placed _ _ _ _ bank_pair_len
    (pair_placed_normalize _ _ _ _ (fun i hi =>
      placed_implies_pair _ _ _ _ (hg.site.placed i (List.mem_append_left _ hi))))

def fastTP : Nat :=
  32767 + ECDSAAdd.toffoliCount f.swapNet + 502 +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502

theorem fast_tp_relation (hg : FastGeometry1 f) :
    f.fastTP + (32266 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  have hl : literalToffolis (normalizeW f.site.prefix) = literalToffolis (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalToffolis_append]
    simp [normalizeW, normalizeWInstr, literalToffolis]
  have ht : traversals f.site.prefix = traversals f.site.arithmetic + 1 := by
    rw [prefix_split, traversals_append]
    simp [traversals]
    omega
  have hb : 2 ^ bank15.bits.length - 1 = 65535 := by simp [bank15, windowBits]
  simp only [blockTP2, siteUnit, fastTP, hl, ht, hb, bank_tree_nodes]
  omega

theorem sel_slots (hg : FastGeometry1 f) : codeSlots selBits1 f.selCode = 65536 * f.site.ports.length + 327670 := by
  simp only [codeSlots, FastSite1.selCode, selBits1, List.length_range', List.length_append, List.length_cons, List.length_nil, selPorts_length f hg]
  norm_num
  try omega

def fastSlack : Nat := 262144 * f.garb.length + 3 * ECDSAAdd.Challenge.gateSlots f.swapNet

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16
end

/-! ### Fused fast sites on the eight-bit bank -/

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open MeasuredClear (ClearPort)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace FastSite
variable {n : Nat} (f : FastSite n)

/-- Records of the fused fast block: select, swap, then the deferred tail. -/
def fusedRecords : Nat :=
  codeRecords selBits selPaths windowRoot f.selCode + 0 + (f.garbPorts.length + tailRec bank15 f.site)

def fusedProgram (start : Nat) : Straight n start (start + f.fusedRecords) :=
  castFinish (by simp only [fusedRecords, clearData, List.length_map]; omega)
    (((f.selProgram start).append
      (f.swapProgram (start + codeRecords selBits selPaths windowRoot f.selCode))).append
      (deferTail bank15 f.site (clearData f.garbPorts) (start + codeRecords selBits selPaths windowRoot f.selCode + 0)))

def fusedSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  ((source read selBits selPaths windowRoot f.selCode).seq (literalSource f.swapNet)).seq
    (deferSource bank15 read f.site (clearData f.garbPorts))

theorem fusedProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).run = (f.fusedSource read).run := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_run_fixed _ _ _ _ _ (fun h => deferTail_run bank15 read f.site _ _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
    compile_run]
  simp only [fusedSource, AdaptiveCircuit.run_seq]

/-- After select and swap, each garbage wire holds its row's word under the original guard. -/
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
  obtain ⟨c2, a2, m2⟩ := tail_sim read bank15 bank15_ok f.site hg.site hk (clearData f.garbPorts)
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
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

def fusedTP : Nat :=
  16383 + ECDSAAdd.toffoliCount f.swapNet +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502

theorem fused_tCount (read : ConstantBit n → Bool) (hg : FastGeometry f) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).tCount = 7 * f.fusedTP := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_tCount_fixed _ _ _ _ _ (fun h => deferTail_tCount read bank15 f.site _ (site_layout_bank f hg)
      (arith_layouts f hg) _ h),
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read selBits selPaths windowRoot _ (sel_layouts f hg), traversals_normalize, bank_tree_nodes]
  simp only [fusedTP, FastSite.selCode, literalToffolis, traversals, selBits, bank15, windowBits,
    List.length_range', List.length_append, List.length_cons, List.length_nil]
  norm_num
  try ring

theorem fused_tp_relation (hg : FastGeometry f) :
    f.fusedTP + (49152 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have h := f.fast_tp_relation hg
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  simp only [fastTP, fusedTP] at h ⊢
  omega

theorem fused_records_relation (hg : FastGeometry f) :
    f.fusedRecords + (49152 - f.garb.length) = blockRecP2 bank15 (.unit (siteUnit f.site)) := by
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
  have hb : 2 ^ windowBits.length - 1 = 65535 := by simp [windowBits]
  simp only [blockRecP2, siteUnit, FastSite.fusedRecords, tailRec, fuseRec, hsel, hgl, hcr, hcr', hpre, hari, hlr, htr, hb]
  simp only [show bank15.bits = windowBits from rfl, show bank15.paths = pathBank from rfl, hb] at hpre hari ⊢
  omega

theorem fused_slots (hg : FastGeometry f) (start : Nat) :
    (f.fusedProgram start).gateSlots ≤ blockSP2 bank15 (.unit (siteUnit f.site)) + f.fastSlack := by
  rw [fusedProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append]
  rw [deferTail_slots bank15 f.site _ (site_layout_bank f hg) (arith_layouts f hg), swapProgram, literalFixed_slots,
    selProgram, compile_slots _ _ _ _ (sel_layouts f hg), sel_slots f hg]
  have hsw := literal_slot_bound (n := n) f.swapNet
  have hd : (clearData f.garbPorts).length = f.garb.length := by
    rw [clearData, List.length_map, garbPorts_length f hg]
  have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
      (65536 * f.site.ports.length + 655350) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, slots_append_wide, lookup_slots]
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
  · exact deferTail_wellFormed bank15 bank15_ok f.site hg.site _
      (fun p hm => hp p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

theorem fused_residue (start : Nat) : residue (f.fusedProgram start) = 0 := by
  rw [fusedProgram, residue_cast]
  simp only [residue_append]
  rw [selProgram, compile_residue, swapProgram, literalFixed, residue_naive_cast, literal_residue,
    deferTail_residue]

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

def fusedRecords : Nat :=
  codeRecords selBits1 selPaths1 windowRoot f.selCode + 0 + (f.garbPorts.length + tailRec bank15 f.site)

def fusedProgram (start : Nat) : Straight n start (start + f.fusedRecords) :=
  castFinish (by simp only [fusedRecords, clearData, List.length_map]; omega)
    (((f.selProgram start).append
      (f.swapProgram (start + codeRecords selBits1 selPaths1 windowRoot f.selCode))).append
      (deferTail bank15 f.site (clearData f.garbPorts) (start + codeRecords selBits1 selPaths1 windowRoot f.selCode + 0)))

def fusedSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  ((source read selBits1 selPaths1 windowRoot f.selCode).seq (literalSource f.swapNet)).seq
    (deferSource bank15 read f.site (clearData f.garbPorts))

theorem fusedProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).run = (f.fusedSource read).run := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_run_fixed _ _ _ _ _ (fun h => deferTail_run bank15 read f.site _ _ h), AdaptiveCircuit.run_seq,
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
  obtain ⟨c2, a2, m2⟩ := tail_sim read bank15 bank15_ok f.site hg.site hk (clearData f.garbPorts)
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
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

def fusedTP : Nat :=
  32767 + ECDSAAdd.toffoliCount f.swapNet +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502

theorem fused_tCount (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).tCount = 7 * f.fusedTP := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_tCount_fixed _ _ _ _ _ (fun h => deferTail_tCount read bank15 f.site _ (site_layout_bank f hg)
      (arith_layouts f hg) _ h),
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read selBits1 selPaths1 windowRoot _ (sel_layouts f hg), traversals_normalize, bank_tree_nodes]
  simp only [fusedTP, FastSite1.selCode, literalToffolis, traversals, selBits1, bank15, windowBits,
    List.length_range', List.length_append, List.length_cons, List.length_nil]
  norm_num
  try ring

theorem fused_tp_relation (hg : FastGeometry1 f) :
    f.fusedTP + (32768 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have h := f.fast_tp_relation hg
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  simp only [fastTP, fusedTP] at h ⊢
  omega

theorem fused_records_relation (hg : FastGeometry1 f) :
    f.fusedRecords + (32768 - f.garb.length) = blockRecP2 bank15 (.unit (siteUnit f.site)) := by
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
  have hb : 2 ^ windowBits.length - 1 = 65535 := by simp [windowBits]
  simp only [blockRecP2, siteUnit, FastSite1.fusedRecords, tailRec, fuseRec, hsel, hgl, hcr, hcr', hpre, hari, hlr, htr, hb]
  simp only [show bank15.bits = windowBits from rfl, show bank15.paths = pathBank from rfl, hb] at hpre hari ⊢
  omega

theorem fused_slots (hg : FastGeometry1 f) (start : Nat) :
    (f.fusedProgram start).gateSlots ≤ blockSP2 bank15 (.unit (siteUnit f.site)) + f.fastSlack := by
  rw [fusedProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append]
  rw [deferTail_slots bank15 f.site _ (site_layout_bank f hg) (arith_layouts f hg), swapProgram, literalFixed_slots,
    selProgram, compile_slots _ _ _ _ (sel_layouts f hg), sel_slots f hg]
  have hsw := literal_slot_bound (n := n) f.swapNet
  have hd : (clearData f.garbPorts).length = f.garb.length := by
    rw [clearData, List.length_map, garbPorts_length f hg]
  have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
      (65536 * f.site.ports.length + 655350) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, slots_append_wide, FastSite.lookup_slots]
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
  · exact deferTail_wellFormed bank15 bank15_ok f.site hg.site _
      (fun p hm => hp p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

theorem fused_residue (start : Nat) : residue (f.fusedProgram start) = 0 := by
  rw [fusedProgram, residue_cast]
  simp only [residue_append]
  rw [selProgram, compile_residue, swapProgram, literalFixed, residue_naive_cast, literal_residue,
    deferTail_residue]

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

inductive FBlock2 (n : Nat) where
  | std (b : Block2 n)
  | fast (f : FastSite n)
  | fast1 (f : FastSite1 n)
abbrev FCode2 (n : Nat) := List (FBlock2 n)

/-- The `Code2` block a fast block replaces. -/
def FBlock2.forget {n} : FBlock2 n → Block2 n
  | .std b => b
  | .fast f => .unit (siteUnit f.site)
  | .fast1 f => .unit (siteUnit f.site)

def fforget {n} (code : FCode2 n) : Code2 n := code.map FBlock2.forget

@[simp] theorem fforget_cons {n} (b : FBlock2 n) (code : FCode2 n) :
    fforget (b :: code) = b.forget :: fforget code := rfl

def fblockRec {n} : FBlock2 n → Nat
  | .std b => blockRecP2 bank15 b
  | .fast f => f.fusedRecords
  | .fast1 f => f.fusedRecords

def fblockProg {n} : (b : FBlock2 n) → (start : Nat) → Straight n start (start + fblockRec b)
  | .std b, start => blockProgH bank15 b start
  | .fast f, start => f.fusedProgram start
  | .fast1 f, start => f.fusedProgram start

def frecs {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockRec b + frecs code

def fblockSrc {n} (read : ConstantBit n → Bool) : FBlock2 n → AdaptiveCircuit
  | .std b => blockSourceH bank15 read b
  | .fast f => f.fusedSource read
  | .fast1 f => f.fusedSource read

theorem fblockProg_run {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (start : Nat)
    (history : Fin start → Bool) :
    ((fblockProg b start).instantiate read history).run = (fblockSrc read b).run := by
  cases b with
  | std b => exact blockProgH_run bank15 read b start history
  | fast f => exact f.fusedProgram_run read start history
  | fast1 f => exact f.fusedProgram_run read start history

/-! Geometry, the clean-bank premise and the per-block simulation. -/

def FBlockGeo {n} : FBlock2 n → Prop
  | .std b => BlockGeoP2 bank15 b
  | .fast f => FastGeometry f ∧ GuardKept f.site
  | .fast1 f => FastGeometry1 f ∧ GuardKept f.site

/-- At a fast block both the bank and the site's four registers are clean. -/
def FBlockClean {n} : FBlock2 n → ECDSAAdd.State → Prop
  | .std b, st => BlockClean2 pathBank b st ∧ HostOK b st
  | .fast f, st => Clean pathBank st.basis ∧ Clean (portTargets f.site.ports ++ f.garb) st.basis
  | .fast1 f, st => Clean pathBank st.basis ∧ Clean (portTargets f.site.ports ++ f.garb) st.basis

def FCodeClean {n} (read : ConstantBit n → Bool) (address : Nat) : FCode2 n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => FBlockClean b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference2 read address b.forget) →
        FCodeClean read address code (ECDSAAdd.run (blockReference2 read address b.forget) m st)

def FBlockSim {n} (read : ConstantBit n → Bool) (block : FBlock2 n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.forget.code ∧
    ∀ address st, AddrValid windowBits windowRoot address st → FBlockClean block st →
      BlockSafe2 read address block.forget st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference2 read address block.forget) m st)

theorem fblock_sim {n} (read : ConstantBit n → Bool) (block : FBlock2 n) (hg : FBlockGeo block) :
    ∃ cs : List ℂ, List.Forall₂ (FBlockSim read block) (fblockSrc read block).run cs ∧
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

theorem fblock_addr {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (hg : FBlockGeo b)
    (a : Nat) (st : ECDSAAdd.State) (hs : AddrValid windowBits windowRoot a st)
    (hc : FBlockClean b st) (m : List Bool) :
    AddrValid windowBits windowRoot a (ECDSAAdd.run (blockReference2 read a b.forget) m st) := by
  cases b with
  | std b => exact block_addr2 read bank15 b hg a st hs hc.1 m
  | fast f =>
    have hp : ∀ i ∈ f.site.code, PlacedPair windowBits pathBank windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.1.site.placed i hi)
    have h := strict_preserves read windowBits pathBank f.site.code a hp st ⟨hc.1, hs.1, hs.2⟩ m
    exact ⟨h.2.1, h.2.2⟩
  | fast1 f =>
    have hp : ∀ i ∈ f.site.code, PlacedPair windowBits pathBank windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.1.site.placed i hi)
    have h := strict_preserves read windowBits pathBank f.site.code a hp st ⟨hc.1, hs.1, hs.2⟩ m
    exact ⟨h.2.1, h.2.2⟩

/-! Resources against the forgotten `Code2` program. -/

def fblockTP {n} : FBlock2 n → Nat
  | .std b => blockTP2 bank15 b
  | .fast f => f.fusedTP
  | .fast1 f => f.fusedTP

def fcodeTP {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockTP b + fcodeTP code

def fblockSave {n} : FBlock2 n → Nat
  | .std _ => 0
  | .fast f => 49152 - ECDSAAdd.toffoliCount f.swapNet
  | .fast1 f => 32768 - ECDSAAdd.toffoliCount f.swapNet

def fsave {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockSave b + fsave code

def fblockRSave {n} : FBlock2 n → Nat
  | .std _ => 0
  | .fast f => 49152 - f.garb.length
  | .fast1 f => 32768 - f.garb.length

def frsave {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockRSave b + frsave code

def fblockSlack {n} : FBlock2 n → Nat
  | .std _ => 6
  | .fast f => f.fastSlack
  | .fast1 f => f.fastSlack

def fslack {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockSlack b + fslack code

theorem fblock_tCount {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (hg : FBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((fblockProg b start).instantiate read history).tCount = 7 * fblockTP b := by
  cases b with
  | std b => exact blockH_tCount read bank15 b (geo_lay2 bank15 bank15_ok b hg) start history
  | fast f => exact f.fused_tCount read hg.1 start history
  | fast1 f => exact f.fused_tCount read hg.1 start history

theorem fcodeTP_relation {n} (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b) :
    fcodeTP code + fsave code = codeTP2 bank15 (fforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : fblockTP b + fblockSave b = blockTP2 bank15 b.forget := by
      have hgb := hg b (by simp)
      cases b with
      | std b => simp [fblockTP, fblockSave, FBlock2.forget]
      | fast f => exact f.fused_tp_relation hgb.1
      | fast1 f => exact f.fused_tp_relation hgb.1
    simp only [fcodeTP, fsave, fforget_cons, codeTP2]
    omega

theorem frecs_relation {n} (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b) :
    frecs code + frsave code = recordsP2 bank15 (fforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : fblockRec b + fblockRSave b = blockRecP2 bank15 b.forget := by
      have hgb := hg b (by simp)
      cases b with
      | std b => simp [fblockRec, fblockRSave, FBlock2.forget]
      | fast f => exact f.fused_records_relation hgb.1
      | fast1 f => exact f.fused_records_relation hgb.1
    simp only [frecs, frsave, fforget_cons, recordsP2]
    omega

theorem fblock_wellFormed {n} (b : FBlock2 n) (hg : FBlockGeo b)
    (hp : ∀ p, WInstr.literal p ∈ b.forget.code → GatePhysical p) (start : Nat) :
    (fblockProg b start).WellFormed := by
  cases b with
  | std b =>
    show (blockProgH bank15 b start).WellFormed
    exact blockH_wellFormed bank15 bank15_ok b hg hp start
  | fast f =>
    exact f.fused_wellFormed hg.1 (fun p hm => hp p (by simpa [FBlock2.forget, siteUnit_code] using hm)) start
  | fast1 f =>
    exact f.fused_wellFormed hg.1 (fun p hm => hp p (by simpa [FBlock2.forget, siteUnit_code] using hm)) start

end
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] WEXFast.rowCF WEXUnlookup.rowC
  Straight.WellFormed Straight.instantiate AdaptiveCircuit.run

def rows : Nat → Fin 65536 := Geometry.rows .w16
def fast (f : WEXFast.FastSite 32768) : Fast16.FastSite 65536 :=
  ⟨Rows.site rows f.site, f.g1, f.g2, f.g3⟩
def fast1 (f : WEXFast.FastSite1 32768) : Fast16.FastSite1 65536 :=
  ⟨Rows.site rows f.site, f.g1⟩
def lift : WEXFast.FBlock2 32768 → Fast16.FBlock2 65536
  | .std b => .std (Rows.block rows b)
  | .fast f => .fast (fast f)
  | .fast1 f => .fast1 (fast1 f)
def code : Fast16.FCode2 65536 := WEXFast.rowCF.map lift

theorem forget_lift (b : WEXFast.FBlock2 32768) :
    (lift b).forget = Rows.block rows b.forget := by
  cases b with
  | std b => rfl
  | fast f =>
    simp [lift, fast, Fast16.FBlock2.forget, WEXFast.FBlock2.forget, Fast16.siteUnit,
      WEXFast.siteUnit, Rows.block, Rows.unit, Rows.site, Rows.code, Rows.instr, MaskedSite.prefix]
  | fast1 f =>
    simp [lift, fast1, Fast16.FBlock2.forget, WEXFast.FBlock2.forget, Fast16.siteUnit,
      WEXFast.siteUnit, Rows.block, Rows.unit, Rows.site, Rows.code, Rows.instr, MaskedSite.prefix]

theorem forget : Fast16.fforget code = Geometry.row .w16 := by
  change (WEXFast.rowCF.map lift).map Fast16.FBlock2.forget = Rows.blocks rows WEXUnlookup.rowC
  rw [List.map_map]
  change WEXFast.rowCF.map (fun b => (lift b).forget) = Rows.blocks rows WEXUnlookup.rowC
  have h : WEXFast.rowCF.map (fun b => (lift b).forget) =
      WEXFast.rowCF.map (fun b => Rows.block rows b.forget) := by
    apply List.map_congr_left
    intro b hb
    exact forget_lift b
  rw [h]
  change WEXFast.rowCF.map ((Rows.block rows) ∘ WEXFast.FBlock2.forget) =
    Rows.blocks rows WEXUnlookup.rowC
  rw [← List.map_map, ← WEXFast.fforget, WEXFast.fforget_rowCF]
  rfl

theorem tripleF_bank8 : ∀ i : Fin 256, WEXFast.tripleF.g1.headD 0 + i.val ∈ WEXFast.tripleF.g1 := by
  intro i
  have hi := i.isLt
  show (List.range' 14371 256).headD 0 + i.val ∈ List.range' 14371 256
  rw [show (List.range' 14371 256).headD 0 = 14371 from rfl, List.mem_range'_1]
  omega

theorem site2F_bank8 : ∀ i : Fin 256, WEXFast.site2F.g1.headD 0 + i.val ∈ WEXFast.site2F.g1 := by
  intro i
  have hi := i.isLt
  show (List.range' 14115 258 ++ List.range' 14884 254).headD 0 + i.val ∈
    List.range' 14115 258 ++ List.range' 14884 254
  rw [show (List.range' 14115 258 ++ List.range' 14884 254).headD 0 = 14115 from rfl, List.mem_append,
    List.mem_range'_1]
  left
  omega

theorem fast_geometry (f : WEXFast.FastSite 32768) (hg : WEXFast.FastGeometry f)
    (hm : Block2.unit (WEXFast.siteUnit f.site) ∈ WEXUnlookup.rowC)
    (hb8 : ∀ i : Fin 256, f.g1.headD 0 + i.val ∈ f.g1) : Fast16.FastGeometry (fast f) := by
  refine ⟨Fast16.siteGeo_new (Geometry.extend_site .w16 _ hm hg.site), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [fast, Rows.site, Rows.ports] using hg.len1
  · simpa [fast, Rows.site, Rows.ports] using hg.len2
  · simpa [fast, Rows.site, Rows.ports] using hg.len3
  · simpa only [fast, Rows.site, Rows.targets, Fast16.FastSite.garb, WEXFast.FastSite.garb] using hg.nodup
  · exact hg.bounds
  · exact hg.free
  · exact hg.head
  · exact hb8

theorem fast1_geometry (f : WEXFast.FastSite1 32768) (hg : WEXFast.FastGeometry1 f)
    (hm : Block2.unit (WEXFast.siteUnit f.site) ∈ WEXUnlookup.rowC)
    (hb8 : ∀ i : Fin 256, f.g1.headD 0 + i.val ∈ f.g1) : Fast16.FastGeometry1 (fast1 f) := by
  refine ⟨Fast16.siteGeo_new (Geometry.extend_site .w16 _ hm hg.site), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [fast1, Rows.site, Rows.ports] using hg.len1
  · simpa only [fast1, Rows.site, Rows.targets, Fast16.FastSite1.garb, WEXFast.FastSite1.garb] using hg.nodup
  · exact hg.bounds
  · exact hg.free
  · exact hg.head
  · exact hb8

/-- Lifting to sixteen-bit rows keeps the guard and the literal arithmetic. -/
theorem guardKept_lift (s : MaskedSite 32768) (h : GuardKept s) : GuardKept (Rows.site rows s) := by
  rcases h with h | ⟨p, hp, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, by simp only [Rows.site, Rows.code, hp, List.map_cons, List.map_nil, Rows.instr], hw⟩

theorem geometry : ∀ b ∈ code, Fast16.FBlockGeo b := by
  intro b hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  cases old with
  | std b =>
    have hm : b ∈ WEXUnlookup.rowC := by
      rw [← WEXFast.fforget_rowCF]
      exact List.mem_map.mpr ⟨.std b, ho, rfl⟩
    exact Fast16.blockGeo_new (Geometry.row_geometry .w16 _ (List.mem_map.mpr ⟨b, hm, rfl⟩))
  | fast f =>
    have he := WEXFast.fast_mem_rowCF f ho
    subst f
    exact ⟨fast_geometry _ WEXFast.tripleF_geometry WEXFast.triple_unit_mem tripleF_bank8,
      guardKept_lift _ triple_guardKept⟩
  | fast1 f =>
    have he := WEXFast.fast1_mem_rowCF f ho
    subst f
    exact ⟨fast1_geometry _ WEXFast.site2F_geometry WEXFast.site2_unit_mem site2F_bank8,
      guardKept_lift _ site2_guardKept⟩

theorem litProg_lift (c : WCode 32768) : litProg (Rows.code rows c) = litProg c := by
  induction c with
  | nil => rfl
  | cons i c ih =>
    simp only [Rows.code] at ih
    cases i <;> simp [Rows.code, Rows.instr, litProg, ih]

theorem host_lift (b : Block2 32768) (st : ECDSAAdd.State) (h : HostOK b st) : HostOK (Rows.block rows b) st := by
  cases b with
  | plain c => simpa only [Rows.block, HostOK, litProg_lift] using h
  | unit u => trivial

theorem old_instr_placed (b : WEXFast.FBlock2 32768) (hb : b ∈ WEXFast.rowCF) :
    ∀ i ∈ b.forget.code, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  apply WEXUnlookup.rowC_placed
  rw [← WEXFast.fforget_rowCF, WEXFast.fforget, erase2]
  exact List.mem_flatMap.mpr ⟨b.forget, List.mem_map.mpr ⟨b, hb, rfl⟩, hi⟩

theorem clean_lift (coeffs : Fin 65536 → PointCoeff) (Q : Point) (a : Nat)
    (c : WEXFast.FCode2 32768) (hc : ∀ b ∈ c, b ∈ WEXFast.rowCF) (st : ECDSAAdd.State)
    (hold : WEXFast.FCodeClean (readConstant (fun _ : Fin 32768 => coeffs (rows a)) Q) a c st)
    (hextra : Clean windowPaths st.basis) :
    Fast16.FCodeClean (readConstant coeffs Q) a (c.map lift) st := by
  induction c generalizing st with
  | nil => trivial
  | cons b c ih =>
    have hbank (h : Clean PathShare.pathBank st.basis) : Clean Fast16.pathBank st.basis := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h v hv
      · have he : v = 10000 := by simpa using hv
        subst v
        exact hextra _ (by decide)
    refine ⟨?_, ?_⟩
    · cases b with
      | std b =>
        refine ⟨?_, host_lift b st hold.1.2⟩
        cases b with
        | plain p => trivial
        | unit u => exact hbank hold.1.1
      | fast f =>
        refine ⟨hbank hold.1.1, ?_⟩
        simpa only [lift, fast, Rows.site, Rows.targets, Fast16.FastSite.garb,
          WEXFast.FastSite.garb] using hold.1.2
      | fast1 f =>
        refine ⟨hbank hold.1.1, ?_⟩
        simpa only [lift, fast1, Rows.site, Rows.targets, Fast16.FastSite1.garb,
          WEXFast.FastSite1.garb] using hold.1.2
    · intro m hm
      have he : blockReference2 (readConstant coeffs Q) a (lift b).forget =
          blockReference2 (readConstant (fun _ : Fin 32768 => coeffs (rows a)) Q) a b.forget := by
        rw [forget_lift, Rows.block_reference]
      rw [he] at hm ⊢
      apply ih (fun d hd => hc d (List.mem_cons_of_mem _ hd)) _ (hold.2 m hm)
      intro v hv
      rw [blockReference2, Add.code_frame _ a windowPaths b.forget.code
        (old_instr_placed b (hc b (by simp))) st m v hv]
      exact hextra v hv

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Counts
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare Geometry
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram literalToffolis literalRecords normalizeW

theorem lift_metrics {n} (r : Nat → Fin n) (c : WCode 32768) :
    literalToffolis (Rows.code r c) = literalToffolis c ∧
    literalRecords (Rows.code r c) = literalRecords c ∧
    traversals (Rows.code r c) = traversals c := by
  induction c with
  | nil => simp [Rows.code, literalToffolis, literalRecords, traversals]
  | cons i c ih =>
    cases i <;> simpa [Rows.code, Rows.instr, literalToffolis, literalRecords, traversals] using ih

theorem lift_normal_code {n} (r : Nat → Fin n) (c : WCode 32768) :
    normalizeW (Rows.code r c) = Rows.code r (normalizeW c) := by
  induction c with
  | nil => simp [normalizeW, Rows.code]
  | cons i c ih =>
    cases i <;> simpa [Rows.code, Rows.instr, normalizeW, normalizeWInstr] using ih

theorem lift_normal_metrics {n} (r : Nat → Fin n) (c : WCode 32768) :
    literalToffolis (normalizeW (Rows.code r c)) = literalToffolis (normalizeW c) := by
  rw [lift_normal_code, (lift_metrics r (normalizeW c)).1]

theorem lifted_credit {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768) :
    codeTP2 B (Rows.blocks r c) + masks2 c * (2 ^ B.bits.length - 1) =
      literalToffolis (normalizeW (erase2 c)) + traversals (erase2 c) * (2 ^ B.bits.length - 1) +
        masks2 c * ((tableAddressTree B.high 0 1).internalNodes + 247) := by
  induction c with
  | nil => simp [Rows.blocks, codeTP2, masks2, erase2, normalizeW, literalToffolis, traversals]
  | cons b c ih =>
    have hb : blockTP2 B (Rows.block r b) + blockMasks2 b * (2 ^ B.bits.length - 1) =
        literalToffolis (normalizeW b.code) + traversals b.code * (2 ^ B.bits.length - 1) +
          blockMasks2 b * ((tableAddressTree B.high 0 1).internalNodes + 247) := by
      cases b with
      | plain p =>
        simp [Rows.block, blockTP2, blockMasks2, Block2.code, lift_normal_metrics, (lift_metrics r p).2.2]
      | unit u =>
        rw [show (Rows.block r (Block2.unit u)) = .unit (Rows.unit r u) from rfl]
        simp only [blockTP2, Rows.unit, lift_normal_metrics, (lift_metrics r u.pre).2.2,
          Block2.code, UnitSite.code, normalize_append, literalToffolis_append, traversals_append,
          blockMasks2, Nat.one_mul]
        simp [normalizeW, normalizeWInstr, literalToffolis, traversals]
        ring
    simp only [Rows.blocks, List.map_cons, codeTP2, masks2, erase2_cons, normalize_append,
      literalToffolis_append, traversals_append, Nat.add_mul] at ih ⊢
    omega

end
end ShorECDLP.Entrant.WideBank8.Counts

namespace ShorECDLP.Entrant.WideBank8.Counts
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] codeTP2 WEXUnlookup.ccx2 literalToffolis normalizeW

theorem credit_change {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768)
    (hb : B.bits.length = 16) (hn : (tableAddressTree B.high 0 1).internalNodes = 255)
    (hm : masks2 c = 5) (ht : traversals (erase2 c) = 9) :
    codeTP2 B (Rows.blocks r c) = WEXUnlookup.ccx2 c + 131707 := by
  have hw := lifted_credit r B c
  have ho := WEXUnlookup.ccx2_relation c
  rw [hb, hn, hm, ht] at hw
  rw [hm, ht] at ho
  omega

end
end ShorECDLP.Entrant.WideBank8.Counts

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WEXFast.rowCF WEXUnlookup.rowC
  ECDSAAdd.toffoliCount ECDSAAdd.Baselines.normalizeProgram literalToffolis normalizeW
  Fast16.fcodeTP Fast16.fsave WEXFast.fcodeTP WEXUnlookup.ccx2 codeTP2

theorem saving : Fast16.fsave code = 80640 := by
  have hp : (fast WEXFast.tripleF).site.ports.length = 256 := by
    simpa [fast, Rows.site, Rows.ports, WEXFast.tripleF] using WEXFast.tripleSite_length
  have hp1 : (fast1 WEXFast.site2F).site.ports.length = 512 := by
    have hl := WEXFast.site2F_geometry.len1
    have hg := WEXFast.site2F_garb_length
    change WEXFast.site2F.g1.length = 512 at hg
    have h := hl.symm.trans hg
    simpa [fast1, Rows.site, Rows.ports] using h
  have hs := Fast16.FastSite.swapNet_toff (fast WEXFast.tripleF)
    (fast_geometry _ WEXFast.tripleF_geometry WEXFast.triple_unit_mem tripleF_bank8)
  have hs1 := Fast16.FastSite1.swapNet_toff (fast1 WEXFast.site2F)
    (fast1_geometry _ WEXFast.site2F_geometry WEXFast.site2_unit_mem site2F_bank8)
  rw [hp] at hs
  rw [hp1] at hs1
  have hstd (c : WEXUnlookup.Code2 32768) : Fast16.fsave ((c.map WEXFast.FBlock2.std).map lift) = 0 := by
    induction c with
    | nil => simp [Fast16.fsave]
    | cons b c ih => simpa [Fast16.fsave, Fast16.fblockSave, lift] using ih
  have happ (a b : Fast16.FCode2 65536) : Fast16.fsave (a ++ b) = Fast16.fsave a + Fast16.fsave b := by
    induction a with
    | nil => simp [Fast16.fsave]
    | cons x a ih => simp [Fast16.fsave, ih, Nat.add_assoc]
  rw [code, WEXFast.rowCF, List.map_append, List.map_append, happ, happ, hstd, hstd]
  simp only [WEXFast.fgeneric3, List.map_cons, List.map_nil, lift, Fast16.fsave,
    Fast16.fblockSave, hs, hs1]

theorem cost_arith (fresh old wideStd oldStd : Nat)
    (hnew : fresh + 80640 = wideStd) (hold : old + 38930 = oldStd)
    (hwide : wideStd = oldStd + 131707) : fresh = old + 89997 := by omega

theorem fast_standard_relation :
    Fast16.fcodeTP code + 80640 = codeTP2 Fast16.bank15 (Geometry.row .w16) := by
  have h := Fast16.fcodeTP_relation code geometry
  rw [saving, forget] at h
  exact h

theorem wide_standard_relation :
    codeTP2 Fast16.bank15 (Geometry.row .w16) = WEXUnlookup.ccx2 WEXUnlookup.rowC + 131707 :=
  Counts.credit_change rows Fast16.bank15 WEXUnlookup.rowC rfl Fast16.high_nodes
    WEXUnlookup.rowC_masks WEXUnlookup.rowC_measures.2.1

theorem credit_increment : Fast16.fcodeTP code = WEXFast.fcodeTP WEXFast.rowCF + 89997 := by
  exact cost_arith _ _ _ _ fast_standard_relation WEXFast.W15F.rowCF_tp wide_standard_relation

theorem body_credit_bound :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) +
      Fast16.fcodeTP code ≤ 2343187 := by
  rw [credit_increment]
  have h := WEXFast.W15F.fastCount_upper
  rw [← Nat.add_assoc]
  exact Nat.add_le_add_right h 89997

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

namespace FastSite
variable {n : Nat} (f : FastSite n)

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

end FastSite1

-- Conditional arithmetic only. The actual final bounds/certificate are required.
end
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code Straight.instantiate AdaptiveCircuit.run

theorem literal_back (c : WCode 32768) (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ Rows.code rows c) : WInstr.literal p ∈ c := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hp
  cases i with
  | literal p' => cases he; exact hi
  | lookup ctl ps => cases he

theorem lookup_back (c : WCode 32768) (ctl : Option Wire) (ps : List (LookupPort 65536))
    (hp : WInstr.lookup ctl ps ∈ Rows.code rows c) :
    ∃ old, WInstr.lookup ctl old ∈ c ∧ ps = Rows.ports rows old := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hp
  cases i with
  | literal p => cases he
  | lookup ctl' old => cases he; exact ⟨old, hi, rfl⟩

theorem strict (b : Fast16.FBlock2 65536) (hb : b ∈ code) :
    ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c) := by
  rw [code] at hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  intro p hp hh
  rw [forget_lift, Rows.block_code] at hp
  obtain ⟨c, he⟩ := WEXFast.W15F.rowCF_strict old ho p (literal_back _ p hp) hh
  rw [he]
  exact ⟨Rows.code rows c, rfl⟩

theorem ctl (b : Fast16.FBlock2 65536) (hb : b ∈ code) :
    ∀ c, b = .std (.plain c) → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c) := by
  rw [code] at hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  intro c he hh
  cases old with
  | std old =>
    cases old with
    | plain oldc =>
      change Fast16.FBlock2.std (.plain (Rows.code rows oldc)) = .std (.plain c) at he
      have hec := Block2.plain.inj (Fast16.FBlock2.std.inj he)
      subst c
      rw [litProg_lift] at hh ⊢
      exact WEXFast.W15F.rowCF_ctl _ ho oldc rfl hh
    | unit u => cases he
  | fast f => cases he
  | fast1 f => cases he

theorem ctl3 (b : Fast16.FBlock2 65536) (hb : b ∈ code) :
    ∀ c, b = .std (.plain c) → hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c) := by
  rw [code] at hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  intro c he hh
  cases old with
  | std old =>
    cases old with
    | plain oldc =>
      change Fast16.FBlock2.std (.plain (Rows.code rows oldc)) = .std (.plain c) at he
      have hec := Block2.plain.inj (Fast16.FBlock2.std.inj he)
      subst c
      rw [litProg_lift] at hh ⊢
      exact WEXFast.W15F.rowCF_ctl3 _ ho oldc rfl hh
    | unit u => cases he
  | fast f => cases he
  | fast1 f => cases he

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Counts
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] codeRecords lookupMeasurements portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  ECDSAAdd.measurementCount ECDSAAdd.Baselines.normalizeProgram literalRecords normalizeW

theorem records_formula {n} (B : PathShare.Bank) (c : Code2 n)
    (hl : ∀ b ∈ c, BlockLay2 B b) :
    recordsP2 B c + masks2 c * (2 ^ B.bits.length - 1) =
      literalRecords (normalizeW (erase2 c)) + traversals (erase2 c) * (2 ^ B.bits.length - 1) +
        lens2 c + masks2 c * ((tableAddressTree B.high 0 1).internalNodes + 255) := by
  induction c with
  | nil => simp [recordsP2, masks2, erase2, normalizeW, literalRecords, traversals, lens2]
  | cons b c ih =>
    have hb : blockRecP2 B b + blockMasks2 b * (2 ^ B.bits.length - 1) =
        literalRecords (normalizeW b.code) + traversals b.code * (2 ^ B.bits.length - 1) +
          blockLen2 b + blockMasks2 b * ((tableAddressTree B.high 0 1).internalNodes + 255) := by
      have hlb := hl b (by simp)
      cases b with
      | plain p =>
        rw [blockRecP2, codeRecords_eq _ _ _ _ hlb, traversals_normalize]
        simp [blockMasks2, blockLen2, Block2.code]
      | unit u =>
        rcases hlb with ⟨hpre, hclear⟩
        rw [blockRecP2, codeRecords_eq _ _ _ _ hpre,
          (MeasuredClear.recordUnary_counts _ _ _ hclear 0).1, traversals_normalize]
        simp only [blockMasks2, blockLen2, Block2.code, UnitSite.code, normalize_append,
          literalRecords_append, traversals_append, Nat.one_mul]
        simp [normalizeW, normalizeWInstr, literalRecords, traversals]
        ring
    have hi := ih (fun d hd => hl d (List.mem_cons_of_mem _ hd))
    simp only [recordsP2, masks2, lens2, erase2_cons, normalize_append,
      literalRecords_append, traversals_append, Nat.add_mul]
    omega

theorem lift_record_metrics {n} (r : Nat → Fin n) (c : Code2 32768) :
    masks2 (Rows.blocks r c) = masks2 c ∧ lens2 (Rows.blocks r c) = lens2 c := by
  induction c with
  | nil => exact ⟨rfl, rfl⟩
  | cons b c ih =>
    cases b <;> simpa [Rows.blocks, Rows.block, Rows.unit, Rows.site, Rows.ports,
      masks2, lens2, blockMasks2, blockLen2] using ih

theorem lift_normal_records {n} (r : Nat → Fin n) (c : WCode 32768) :
    literalRecords (normalizeW (Rows.code r c)) = literalRecords (normalizeW c) := by
  rw [literalRecords_normalize, literalRecords_normalize, (lift_metrics r c).2.1]

theorem lifted_records {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768)
    (hl : ∀ b ∈ Rows.blocks r c, BlockLay2 B b) :
    recordsP2 B (Rows.blocks r c) + masks2 c * (2 ^ B.bits.length - 1) =
      literalRecords (normalizeW (erase2 c)) + traversals (erase2 c) * (2 ^ B.bits.length - 1) +
        lens2 c + masks2 c * ((tableAddressTree B.high 0 1).internalNodes + 255) := by
  have h := records_formula B (Rows.blocks r c) hl
  rw [(lift_record_metrics r c).1, (lift_record_metrics r c).2, Rows.erase_blocks,
    lift_normal_records, (lift_metrics r (erase2 c)).2.2] at h
  exact h

theorem records_change {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768)
    (hl : ∀ b ∈ Rows.blocks r c, BlockLay2 B b)
    (hold : ∀ b ∈ c, BlockLay2 PathShare.bank15 b)
    (hb : B.bits.length = 16) (hn : (tableAddressTree B.high 0 1).internalNodes = 255)
    (hm : masks2 c = 5) (ht : traversals (erase2 c) = 9) :
    recordsP2 B (Rows.blocks r c) = PathShare.recordsP2 PathShare.bank15 c + 131712 := by
  have hw := lifted_records r B c hl
  have ho := WideSigned.Counts.records_formula PathShare.bank15 c hold
  rw [hb, hn, hm, ht] at hw
  rw [hm, ht, show PathShare.bank15.bits.length = 15 from rfl,
    show (tableAddressTree PathShare.bank15.high 0 1).internalNodes = 255 from WEXUnlookup.high_nodes] at ho
  omega

end
end ShorECDLP.Entrant.WideBank8.Counts

namespace ShorECDLP.Entrant.WideBank8.Counts
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.Baselines.normalizeProgram Bridge.tmplSlots literalT

theorem slots_append {n} (bits : List Wire) (a b : WCode n) :
    codeSlots bits (a ++ b) = codeSlots bits a + codeSlots bits b := by
  induction a with
  | nil => simp [codeSlots]
  | cons i a ih => cases i <;> simp [codeSlots, ih, Nat.add_assoc]

theorem std_slots {n} (B : PathShare.Bank) (c : Code2 n) :
    codeSP2 B c ≤ codeSlots B.bits (normalizeW (erase2 c)) +
      1024 * lens2 c * (tableAddressTree B.high 0 1).leaves +
      masks2 c * (10 * (tableAddressTree B.high 0 1).internalNodes + 2291) := by
  induction c with
  | nil => simp [codeSP2, codeSlots, lens2, masks2, erase2, normalizeW]
  | cons b c ih =>
    have hb : blockSP2 B b ≤ codeSlots B.bits (normalizeW b.code) +
        1024 * blockLen2 b * (tableAddressTree B.high 0 1).leaves +
        blockMasks2 b * (10 * (tableAddressTree B.high 0 1).internalNodes + 2291) := by
      cases b with
      | plain p => simp [blockSP2, Block2.code, blockLen2, blockMasks2]
      | unit u =>
        simp only [blockSP2, Block2.code, UnitSite.code, normalize_append, slots_append,
          blockLen2, blockMasks2, Nat.one_mul]
        omega
    simp only [codeSP2, lens2, masks2, erase2_cons, normalize_append, slots_append,
      Nat.mul_add, Nat.add_mul] at ih hb ⊢
    omega

theorem lift_slot_metrics {n} (r : Nat → Fin n) (c : WCode 32768) :
    literalSlotSum (Rows.code r c) = literalSlotSum c ∧
      portTotal (Rows.code r c) = portTotal c := by
  induction c with
  | nil => exact ⟨rfl, rfl⟩
  | cons i c ih =>
    cases i <;> simpa [Rows.code, Rows.instr, Rows.ports, literalSlotSum, portTotal] using ih

theorem standard_wide_slots {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768)
    (hb : B.bits.length = 16) (hleaf : (tableAddressTree B.high 0 1).leaves = 256)
    (hnode : (tableAddressTree B.high 0 1).internalNodes = 255)
    (hm : masks2 c = 5) (hlen : lens2 c = 2566) (ht : traversals (erase2 c) = 9)
    (hL : literalSlotSum (erase2 c) ≤ 50115160) (hP : portTotal (erase2 c) ≤ 20003) :
    codeSP2 B (Rows.blocks r c) ≤ 2139852392 := by
  have h := std_slots B (Rows.blocks r c)
  have hc := WEX.codeSlots_bound B.bits (normalizeW (Rows.code r (erase2 c)))
  rw [literalSlotSum_normalize, portTotal_normalize, traversals_normalize,
    (lift_slot_metrics r (erase2 c)).1, (lift_slot_metrics r (erase2 c)).2,
    (lift_metrics r (erase2 c)).2.2, hb, ht] at hc
  rw [(lift_record_metrics r c).1, (lift_record_metrics r c).2, Rows.erase_blocks,
    hm, hlen, hleaf, hnode] at h
  omega

end
end ShorECDLP.Entrant.WideBank8.Counts

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WEXFast.rowCF WEXUnlookup.rowC
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  ECDSAAdd.measurementCount ECDSAAdd.Baselines.normalizeProgram literalRecords normalizeW
  Fast16.frecs Fast16.frsave recordsP2 masks2 lens2

theorem record_saving : Fast16.frsave code = 80640 := by
  have hstd (c : WEXUnlookup.Code2 32768) :
      Fast16.frsave ((c.map WEXFast.FBlock2.std).map lift) = 0 := by
    induction c with
    | nil => simp [Fast16.frsave]
    | cons b c ih => simpa [Fast16.frsave, Fast16.fblockRSave, lift] using ih
  have happ (a b : Fast16.FCode2 65536) :
      Fast16.frsave (a ++ b) = Fast16.frsave a + Fast16.frsave b := by
    induction a with
    | nil => simp [Fast16.frsave]
    | cons x a ih => simp [Fast16.frsave, ih, Nat.add_assoc]
  have h1 : (fast WEXFast.tripleF).garb.length = 768 := by
    simpa only [fast, Fast16.FastSite.garb, WEXFast.FastSite.garb] using WEXFast.tripleF_garb_length
  have h2 : (fast1 WEXFast.site2F).garb.length = 512 := by
    simpa only [fast1, Fast16.FastSite1.garb, WEXFast.FastSite1.garb] using WEXFast.site2F_garb_length
  rw [code, WEXFast.rowCF, List.map_append, List.map_append, happ, happ, hstd, hstd]
  simp only [WEXFast.fgeneric3, List.map_cons, List.map_nil, lift, Fast16.frsave,
    Fast16.fblockRSave, h1, h2]

theorem record_arith (fresh standard old : Nat)
    (hfast : fresh + 80640 = standard)
    (hnew : standard = old + 131712) (hold : old = 1692440) :
    fresh = 1743512 := by omega

theorem row_records : Fast16.frecs code = 1743512 := by
  have hf := Fast16.frecs_relation code geometry
  rw [record_saving, forget] at hf
  have hn := Counts.records_change rows Fast16.bank15 WEXUnlookup.rowC
    (fun b hb => geo_lay2 Fast16.bank15 Fast16.bank15_ok b (Fast16.blockGeo_new (Geometry.row_geometry .w16 b hb)))
    W15C.lay15 rfl Fast16.high_nodes WEXUnlookup.rowC_masks WEXUnlookup.rowC_measures.2.1
  exact record_arith _ _ _ hf hn W15C.rowC_recordsP

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WEXFast.rowCF WEXUnlookup.rowC
  codeSlots literalSlotSum portTotal traversals normalizeW ECDSAAdd.Baselines.normalizeProgram
  Fast16.fslack codeSP2 masks2 lens2

theorem slack : Fast16.fslack code = 335555942 := by
  have hp : (fast WEXFast.tripleF).site.ports.length = 256 := by
    simpa [fast, Rows.site, Rows.ports, WEXFast.tripleF] using WEXFast.tripleSite_length
  have hp1 : (fast1 WEXFast.site2F).site.ports.length = 512 := by
    have hl := WEXFast.site2F_geometry.len1
    have hg := WEXFast.site2F_garb_length
    change WEXFast.site2F.g1.length = 512 at hg
    simpa [fast1, Rows.site, Rows.ports] using hl.symm.trans hg
  have hs := Fast16.FastSite.swapNet_slots (fast WEXFast.tripleF)
    (fast_geometry _ WEXFast.tripleF_geometry WEXFast.triple_unit_mem tripleF_bank8)
  have hs1 := Fast16.FastSite1.swapNet_slots (fast1 WEXFast.site2F)
    (fast1_geometry _ WEXFast.site2F_geometry WEXFast.site2_unit_mem site2F_bank8)
  rw [hp] at hs
  rw [hp1] at hs1
  have hstd (c : WEXUnlookup.Code2 32768) :
      Fast16.fslack ((c.map WEXFast.FBlock2.std).map lift) = 6 * c.length := by
    induction c with
    | nil => simp [Fast16.fslack]
    | cons b c ih =>
      simp only [List.map_map] at ih
      simp [Fast16.fslack, Fast16.fblockSlack, lift, ih, Nat.mul_add, Nat.add_comm]
  have happ (a b : Fast16.FCode2 65536) :
      Fast16.fslack (a ++ b) = Fast16.fslack a + Fast16.fslack b := by
    induction a with
    | nil => simp [Fast16.fslack]
    | cons x a ih => simp [Fast16.fslack, ih, Nat.add_assoc]
  have h1 : (fast WEXFast.tripleF).garb.length = 768 := by
    simpa only [fast, Fast16.FastSite.garb, WEXFast.FastSite.garb] using WEXFast.tripleF_garb_length
  have h2 : (fast1 WEXFast.site2F).garb.length = 512 := by
    simpa only [fast1, Fast16.FastSite1.garb, WEXFast.FastSite1.garb] using WEXFast.site2F_garb_length
  have l1 : (WEXUnlookup.rowPre3.map toBlock2).length = 3 := rfl
  have l2 : WEXUnlookup.rowPost3.length = 5 := rfl
  rw [code, WEXFast.rowCF, List.map_append, List.map_append, happ, happ, hstd, hstd, l1, l2]
  simp only [WEXFast.fgeneric3, List.map_cons, List.map_nil, lift, Fast16.fslack,
    Fast16.fblockSlack, Fast16.FastSite.fastSlack, Fast16.FastSite1.fastSlack, h1, h2, hs, hs1]

theorem standard_slots : codeSP2 Fast16.bank15 (Geometry.row .w16) ≤ 2139852392 := by
  have lit_arith (L L0 : Nat) (h : L ≤ L0 + 93082 + 513) (h0 : L0 ≤ 50021565) :
      L ≤ 50115160 := by omega
  have port_arith (P P0 : Nat) (h : P ≤ P0 + 3) (h0 : P0 ≤ 20000) : P ≤ 20003 := by omega
  exact Counts.standard_wide_slots rows Fast16.bank15 WEXUnlookup.rowC rfl
    Fast16.bank_tree_leaves Fast16.high_nodes WEXUnlookup.rowC_masks WEXUnlookup.rowC_lens
    WEXUnlookup.rowC_measures.2.1
    (lit_arith _ _ WEXUnlookup.rowC_measures.2.2.1 WEX.clearReferenceRow_literal_slots_bound)
    (port_arith _ _ WEXUnlookup.rowC_measures.2.2.2.1 WEX.clearReferenceRow_portTotal)

end
end ShorECDLP.Entrant.WideBank8.Row16

set_option Elab.async false

/-! ### Tight support of the re-balanced wide window -/

namespace ShorECDLP.Entrant.WideBank8.Fast16.Tight
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare WideSigned
noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] List.ofFn WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram
abbrev support : List Wire := TightSupport.support
theorem old_cover : PathShare.newSourceH ⊆ support := List.subset_append_left _ _
theorem root_new : windowRoot ∈ support := by decide
theorem bits_new : windowBits ⊆ support := by decide
theorem bank_new : pathBank ⊆ support := by decide
theorem high_new : high ⊆ support := by decide
theorem low8_new (i : Fin 8) : low8 i ∈ support := by
  apply bits_new
  have hi := i.isLt
  simp only [windowBits, low8, List.mem_append, List.mem_range'_1, List.mem_singleton]
  omega
theorem selBits_new : selBits ⊆ support := by decide
theorem selBits1_new : selBits1 ⊆ support := by decide
theorem selPaths_new : selPaths ⊆ support := by decide
theorem selPaths1_new : selPaths1 ⊆ support := by decide
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

namespace FastSite
open ShorECDLP.Entrant.WideBank8.Fast16.FastSite
variable {n : Nat} (f : FastSite n)

theorem regs_new (hg : FastGeometry f) (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3) :
    ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ support := by
  intro w hw
  have hk : w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 := by
    rcases List.mem_append.mp hw with h | h
    · exact ⟨fun e => kind_nohost f.site hg.site.kind (e ▸ h), fun e => kind_nohost2 f.site hg.site.kind (e ▸ h), fun e => PathShare.kind_nohost3 f.site hg.site.kind (e ▸ h)⟩
    · exact hgarb w h
  exact work_new w ((facts f hg).2.2.2.2.2.2 w hw) hk.1 hk.2.1 hk.2.2

theorem fused_support_new (hg : FastGeometry f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3)
    (start : Nat) : ChallengeMigration.straightWires (f.fusedProgram start) ⊆ support := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fusedProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine compile_support selBits selPaths windowRoot f.selCode support root_new selBits_new selPaths_new
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
    · exact bits_new (by simp [windowBits])
    · exact bits_new (by simp [windowBits])
    · exact hreg _ h
  · exact deferTail_support bank15 bank15_ok f.site hg.site.kind _ support hlast.2
      (hlast.1 _ (Option.mem_def.mpr rfl)) low8_new high_new bank_new root_new bits_new
      (by rw [clearData_targets, garbPorts_targets f hg]; exact fun w hw => hreg w (List.mem_append_right _ hw))
      (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
      (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _
end FastSite

namespace FastSite1
open ShorECDLP.Entrant.WideBank8.Fast16.FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem regs_new (hg : FastGeometry1 f) (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3) :
    ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ support := by
  intro w hw
  have hk : w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 := by
    rcases List.mem_append.mp hw with h | h
    · exact ⟨fun e => kind_nohost f.site hg.site.kind (e ▸ h), fun e => kind_nohost2 f.site hg.site.kind (e ▸ h), fun e => PathShare.kind_nohost3 f.site hg.site.kind (e ▸ h)⟩
    · exact hgarb w h
  exact work_new w ((facts f hg).2.2.2.2.2.2 w hw) hk.1 hk.2.1 hk.2.2

theorem fused_support_new (hg : FastGeometry1 f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3)
    (start : Nat) : ChallengeMigration.straightWires (f.fusedProgram start) ⊆ support := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fusedProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine compile_support selBits1 selPaths1 windowRoot f.selCode support root_new selBits1_new selPaths1_new
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
    · exact bits_new (by simp [windowBits])
    · exact hreg _ h
  · exact deferTail_support bank15 bank15_ok f.site hg.site.kind _ support hlast.2
      (hlast.1 _ (Option.mem_def.mpr rfl)) low8_new high_new bank_new root_new bits_new
      (by rw [clearData_targets, garbPorts_targets f hg]; exact fun w hw => hreg w (List.mem_append_right _ hw))
      (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
      (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _
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
      exact plainH_support bank15 code hg support root_new bits_new bank_new ctl_newH ctl3_newH
        (fun p hp w hw => hlit p hp w hw) (hctl code rfl) (hctl3 code rfl) start
    | unit u =>
      have h := programP2_support bank15 bank15_ok (Block2.unit u :: []) (fun d hd => by
          simp only [List.mem_singleton] at hd; subst hd; exact hg) support root_new bits_new bank_new low8_new high_new
        (fun p hm => strict (fun c e => by cases e) p (by simpa [erase2] using hm))
        (fun c ps hm => hlook c ps (by simpa [erase2] using hm)) start
      rw [programP2, support_cast, straightWires_append] at h
      exact fun w hw => h (List.mem_append_left _ hw)
  | fast f =>
    exact ShorECDLP.Entrant.WideBank8.Fast16.Tight.FastSite.fused_support_new f hg.1
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start
  | fast1 f =>
    exact ShorECDLP.Entrant.WideBank8.Fast16.Tight.FastSite1.fused_support_new f hg.1
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start

attribute [local irreducible] Row16.code
  Straight.instantiate AdaptiveCircuit.run

theorem row_literals (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ erase2 (fforget Row16.code)) :
    ∀ v ∈ ECDSAAdd.wires p, v=hostWire ∨ v=hostWire2 ∨ v=hostWire3 ∨ v∈support := by
  rw [Row16.forget,WideSigned.Geometry.row,WideSigned.Rows.erase_blocks] at hp
  have hold := Row16.literal_back _ p hp
  intro v hv
  rcases PathShare.rowC_lit_relaxed p hold v hv with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (old_cover h)))

theorem row_lookups (ctl : Option Wire) (ps : List (LookupPort 65536))
    (hp : WInstr.lookup ctl ps ∈ erase2 (fforget Row16.code)) :
    (∀ q∈ctl,q∈support) ∧ portTargets ps ⊆ support := by
  rw [Row16.forget,WideSigned.Geometry.row,WideSigned.Rows.erase_blocks] at hp
  obtain ⟨old,ho,rfl⟩ := Row16.lookup_back _ ctl ps hp
  have h := PathShare.rowC_look_newH ctl old ho
  rw [WideSigned.Rows.targets]
  exact ⟨fun q hq => old_cover (h.1 q hq),fun v hv => old_cover (h.2 hv)⟩

theorem row_nohost (b : FBlock2 65536) (hb : b∈Row16.code) : NoHost3 b := by
  rw [Row16.code] at hb
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hb
  have h := WEXFast.W15F.rowCF_nohost old ho
  cases old with
  | std b => trivial
  | fast f =>
    simpa only [Row16.lift,Row16.fast,NoHost3,WEXFast.FNoHost,
      FastSite.garb,WEXFast.FastSite.garb] using h
  | fast1 f =>
    simpa only [Row16.lift,Row16.fast1,NoHost3,WEXFast.FNoHost,
      FastSite1.garb,WEXFast.FastSite1.garb] using h

end
end ShorECDLP.Entrant.WideBank8.Fast16.Tight

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

def gblockSrc {n} (read : ConstantBit n → Bool) : FBlock2 n → AdaptiveCircuit
  | .std b => blockSourceH bank15 read b
  | .fast f => f.fusedSource read
  | .fast1 f => f.fusedSource read

theorem gblockProg_run {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (start : Nat)
    (history : Fin start → Bool) :
    ((gblockProg b start).instantiate read history).run = (gblockSrc read b).run := by
  cases b with
  | std b => exact blockProgH_run bank15 read b start history
  | fast f => exact f.fusedProgram_run read start history
  | fast1 f => exact f.fusedProgram_run read start history

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

attribute [local irreducible] gblockProg blockProgP2 clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx2 gcodeTP Nat.add Nat.mul

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in

theorem count_arith (s x y : Nat) (h : s + y ≤ 2292120) (hr : x + 39680 = y) : s + x ≤ 2252440 := by omega

theorem fastCount_upper : 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    gcodeTP rowCF ≤ 2252440 := by
  exact count_arith _ _ _ Width15Corner.fastCount_upper rowCF_gtp

end
end ShorECDLP.Entrant.WEXFast.W15G
