import ShorECDLP.Submission.Entrant.Schedule27
import ShorECDLP.Submission.Entrant.ComplementLoss
import ShorECDLP.Submission.Entrant.ExtraPhase
import ShorECDLP.Submission.Entrant.AffineLoss
import ShorECDLP.Submission.Entrant.Phase23Partial
import ShorECDLP.Submission.Entrant.WideBank8

/-! ## The concrete width-16 implementation and the Stage-2 row-level deferred fixups it uses.
Placed in this module, their only consumer: the generic `Width16Schedule` layer in `Schedule27`
(all that `AffineLoss`, `ExtraPhase` and `Phase23Partial` use) does not depend on them. -/

/-! ### Stage 2 (row-level deferred fixups), formerly `RowFused.lean` -/

section

/-! # Row-level deferred fixups (stage 2)

Inside a window row every clear guarded by the window root reads the same root and the same
read-only window address. Such a clear's measurement stays where it is (its register is reset for
reuse), but its phase fixup is deferred: the row carries a *phase debt* — the deferred ports and their
measurement outcomes — to the last root-guarded clear of the row, whose single fixup repays every
deferred phase together with its own.

The debt is a function of the address alone (`debtPhase`), so it commutes with every intervening
block, each of which keeps the root and the address (`fblock_addr`). The whole row is proved as one
unit: a deferred measurement is followed by an outcome-dependent continuation that is the rest of the
row (`dprog`, `dsrc`, `dsrc_sim`). No measure-only block is ever claimed coherent on its own. -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- The phase still owed by deferred clears with ports `data` and outcomes `outcomes`, under a true
guard at address `a`. -/
def debtPhase {n : Nat} (read : ConstantBit n → Bool) (a : Nat) : List (ClearPort n) → List Bool → ℂ
  | p :: ps, o :: os => (if o && decide (read (p.ref a) = p.value) then -1 else 1) * debtPhase read a ps os
  | _, _ => 1

@[simp] theorem debtPhase_nil {n : Nat} (read : ConstantBit n → Bool) (a : Nat) (os : List Bool) :
    debtPhase read a List.nil os = 1 := by
  cases os <;> rfl

theorem debtPhase_append {n : Nat} (read : ConstantBit n → Bool) (a : Nat) (d1 d2 : List (ClearPort n))
    (o1 o2 : List Bool) (h : o1.length = d1.length) :
    debtPhase read a (d1 ++ d2) (o1 ++ o2) = debtPhase read a d1 o1 * debtPhase read a d2 o2 := by
  induction d1 generalizing o1 with
  | nil =>
    cases o1 with
    | nil => simp
    | cons _ _ => simp at h
  | cons p ps ih =>
    cases o1 with
    | nil => simp at h
    | cons o os =>
      simp only [List.cons_append, debtPhase]
      rw [ih os (by simpa using h)]
      ring

theorem debtPhase_square {n : Nat} (read : ConstantBit n → Bool) (a : Nat) (d : List (ClearPort n))
    (o : List Bool) : debtPhase read a d o * debtPhase read a d o = 1 := by
  induction d generalizing o with
  | nil => simp
  | cons p ps ih =>
    cases o with
    | nil => simp [debtPhase]
    | cons o os =>
      simp only [debtPhase]
      rw [mul_mul_mul_comm, ih]
      split <;> norm_num

/-- A measured register whose bits hold their loaded values under a true guard owes exactly the debt. -/
theorem registerXPhase_debt {n : Nat} (read : ConstantBit n → Bool) (a : Nat) (data : List (ClearPort n))
    (os : List Bool) (s : BasisState) (hw : ∀ p ∈ data, s p.target = decide (read (p.ref a) = p.value)) :
    registerXPhase (data.map ClearPort.target) os s = debtPhase read a data os := by
  induction data generalizing os with
  | nil => cases os <;> simp [registerXPhase]
  | cons p ps ih =>
    cases os with
    | nil => simp [registerXPhase, debtPhase]
    | cons o os =>
      simp only [List.map_cons, registerXPhase, debtPhase, hw p (by simp),
        ih os (fun q hq => hw q (by simp [hq]))]

theorem phaseFactor_debt8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root : Wire)
    (prepared : BasisState) (selected : Fin 256) (a : Nat)
    (hm : ∀ i, prepared (hot i) = decide (i = selected)) (hr : prepared root = true)
    (ha : 256 * tree.routeLabel prepared + selected.val = a) :
    phaseLookupFactor (logicalPorts8 data outcomes hot) read boolHistory tree root prepared =
      debtPhase read a data outcomes := by
  unfold phaseLookupFactor
  induction data generalizing outcomes with
  | nil =>
    simp only [logicalPorts8, List.zip_nil_left, phasePorts8, List.flatMap_nil]
    simp [recordTargets, xorPhase]
  | cons p ps ih =>
    cases outcomes with
    | nil =>
      simp only [logicalPorts8, List.map_nil, List.zip_nil_right, phasePorts8, List.flatMap_nil]
      simp [recordTargets, xorPhase, debtPhase]
    | cons m ms =>
      rw [logicalPorts_cons8, recordTargets_append, xorPhase_append,
        phasePorts_block8 p m hot read _ root prepared selected hm, ih ms]
      simp only [debtPhase, hr, ha, Bool.true_and]

/-- A deferred phase evaluated by a later fixup whose root is true and whose address is `a`. -/
theorem fixupFactor8_debt {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (t : BasisState) (hhot : HotClean8 hot t) (a : Nat) (hroot : t root = true)
    (haddr : 256 * tree.routeLabel t + hotAddress8 low t = a) :
    fixupFactor8 data outcomes read low hot tree root t = debtPhase read a data outcomes := by
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
  apply phaseFactor_debt8 data outcomes read hot tree root prepared selected a
  · intro i
    simpa only [Fin.ext_iff] using hotPrepare_marker8 low hot hi hdlow t hhot i
  · rw [hframe root (by simp)]; exact hroot
  · rw [hroute]; exact haddr

end
end ShorECDLP.Entrant.MeasuredClear

/-! ### The repaying fixup on the eight-bit bank -/

namespace ShorECDLP.Entrant.WideBank8
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open MeasuredClear (ClearPort debtPhase)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- After the site measurement the site's fixup repays its own phase and the whole row debt `gd`. -/
def PayFixSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ (next : ECDSAAdd.State) (a : Nat), Clean B.hp next.basis → tableAddressValue B.bits next.basis = a →
    next.basis site.guard = true →
    (∀ p ∈ site.ports, next.basis p.target = decide (read (p.ref a) = p.value)) →
    b.kraus (Bridge.signedKet next) =
      (c * debtPhase read a gd og) • Bridge.signedKet ⟨next.phase, clearRegister (portTargets site.ports) next.basis⟩

theorem payFix_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (gd : List (ClearPort n)) (og : List Bool) (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (PayFixSim B read site gd og) (fusedFixSource B read site gd og).run cs ∧
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
  · intro os hos b c hb next a hhp haddr0 hroot0 hsite
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
        debtPhase read a gd og * registerXPhase (portTargets site.ports) os next.basis := by
      rw [MeasuredClear.fixupFactor8_append _ _ _ _ hog]
      congr 1
      · apply MeasuredClear.fixupFactor8_debt gd og read low8 (hot8 site) _ site.guard B.hp
          (hot8_injective site) hdlow hbank t hhot a
        · rw [hguard]; exact hroot0
        · rw [hsplit, haddr, haddr0]
      · have h := MeasuredClear.fixupFactor_recycled8 (clearData site.ports) os read low8 (hot8 site)
          (tableAddressTree B.high 0 1) site.guard B.hp (hot8_injective site) hdlow hbank
          (by rw [clearData_targets]; exact ha) (by rw [clearData_targets]; exact hmem) next.basis
          ⟨hhp, by
            intro q hq
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            rw [hsplit, haddr0, hroot0, Bool.true_and]
            exact hsite p hp⟩
        simpa only [clearData_targets] using h
    have hsq := MeasuredClear.registerXPhase_square (portTargets site.ports) os next.basis
    change b.kraus (xResetRegisterKraus (portTargets site.ports) os (Bridge.signedKet next)) = _
    simp only [Bridge.signedKet, map_smul, hk, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac,
      smul_smul]
    congr 1
    linear_combination ((if next.phase = true then (-1 : ℂ) else 1) *
      registerXResetMagnitude (portTargets site.ports).length * c * debtPhase read a gd og) * hsq

end
end ShorECDLP.Entrant.WideBank8

/-! ### Wide rows with a phase debt -/

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic
open MeasuredClear (ClearPort debtPhase)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

/-- A block of a row with deferred fixups. `defer` and `defer1` measure their clear registers and add
their ports to the debt; `pay` measures its register and repays the debt with its own fixup. -/
inductive DBlock (n : Nat) where
  | std (b : FBlock2 n)
  | defer (u : UnitSite n)
  | defer1 (f : FastSite1 n)
  | pay (u : UnitSite n)
abbrev DCode (n : Nat) := List (DBlock n)

/-- The stage-1 block a deferred block replaces. -/
def DBlock.toF {n} : DBlock n → FBlock2 n
  | .std b => b
  | .defer u => .std (.unit u)
  | .defer1 f => .fast1 f
  | .pay u => .std (.unit u)

def dfor {n} (code : DCode n) : FCode2 n := code.map DBlock.toF

@[simp] theorem dfor_cons {n} (b : DBlock n) (code : DCode n) : dfor (b :: code) = b.toF :: dfor code := rfl
@[simp] theorem dfor_nil {n} : dfor (List.nil : DCode n) = List.nil := rfl

abbrev preRec {n} (u : UnitSite n) : Nat := codeRecords bank15.bits bank15.paths windowRoot (normalizeW u.pre)
abbrev selRec1 {n} (f : FastSite1 n) : Nat := codeRecords selBits1 selPaths1 windowRoot f.selCode
abbrev arithRec {n} (site : MaskedSite n) : Nat :=
  codeRecords bank15.bits bank15.paths windowRoot (normalizeW site.arithmetic)

def dblockRec {n} : DBlock n → Nat
  | .std b => fblockRec b
  | .defer u => preRec u + u.clear.ports.length
  | .defer1 f => selRec1 f + 0 + (f.garbPorts.length + (arithRec f.site + f.site.ports.length))
  | .pay u => preRec u + (u.clear.ports.length + fuseRec bank15 u.clear)

def drecs {n} : DCode n → Nat
  | [] => 0
  | b :: code => dblockRec b + drecs code

/-- The row program. `debt` is the list of deferred ports, `refs` their records. -/
def dprog {n} : (code : DCode n) → (debt : List (ClearPort n)) → (start : Nat) → List (Fin start) →
    Straight n start (start + drecs code)
  | [], _, _, _ => .done
  | .std b :: code, debt, start, refs => castFinish (by simp only [drecs, dblockRec]; omega)
      ((fblockProg b start).append
        (dprog code debt (start + fblockRec b) (refs.map (Fin.castLE (Nat.le_add_right _ _)))))
  | .defer u :: code, debt, start, refs => castFinish (by simp only [drecs, dblockRec, clearData, List.length_map]; omega)
      ((compile bank15.bits bank15.paths windowRoot (normalizeW u.pre) start).append
        (MeasuredClear.measureThen (R := drecs code)
          (fun cursor rs => dprog code (debt ++ clearData u.clear.ports) cursor rs)
          ((clearData u.clear.ports).map ClearPort.target) (start + preRec u)
          (refs.map (Fin.castLE (Nat.le_add_right _ _)))))
  | .defer1 f :: code, debt, start, refs => castFinish (by simp only [drecs, dblockRec, clearData, List.length_map]; omega)
      (((f.selProgram start).append (f.swapProgram (start + selRec1 f))).append
        (MeasuredClear.measureThen (R := arithRec f.site + (f.site.ports.length + drecs code))
          (fun cursor grefs => castFinish (by simp only [clearData, List.length_map]; omega)
            ((compile bank15.bits bank15.paths windowRoot (normalizeW f.site.arithmetic) cursor).append
              (MeasuredClear.measureThen (R := drecs code)
                (fun c2 srefs => dprog code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) c2 srefs)
                ((clearData f.site.ports).map ClearPort.target) (cursor + arithRec f.site)
                (grefs.map (Fin.castLE (Nat.le_add_right _ _))))))
          ((clearData f.garbPorts).map ClearPort.target) (start + selRec1 f + 0)
          (refs.map (Fin.castLE (by omega)))))
  | .pay u :: code, debt, start, refs => castFinish (by simp only [drecs, dblockRec]; omega)
      ((compile bank15.bits bank15.paths windowRoot (normalizeW u.pre) start).append
        ((fusedFix bank15 u.clear debt (start + preRec u) (refs.map (Fin.castLE (Nat.le_add_right _ _)))).append
          (dprog code List.nil (start + preRec u + u.clear.ports.length + fuseRec bank15 u.clear) List.nil)))

/-- The row source: the deferred outcomes `og` flow into the rest of the row. -/
def dsrc {n} (read : ConstantBit n → Bool) : DCode n → List (ClearPort n) → List Bool → AdaptiveCircuit
  | [], _, _ => .done
  | .std b :: code, debt, og => (fblockSrc read b).seq (dsrc read code debt og)
  | .defer u :: code, debt, og => (source read bank15.bits bank15.paths windowRoot (normalizeW u.pre)).seq
      (measureResetThen ((clearData u.clear.ports).map ClearPort.target)
        (fun o => dsrc read code (debt ++ clearData u.clear.ports) (og ++ o)))
  | .defer1 f :: code, debt, og =>
      ((source read selBits1 selPaths1 windowRoot f.selCode).seq (literalSource f.swapNet)).seq
        (measureResetThen ((clearData f.garbPorts).map ClearPort.target) (fun og1 =>
          (source read bank15.bits bank15.paths windowRoot (normalizeW f.site.arithmetic)).seq
            (measureResetThen ((clearData f.site.ports).map ClearPort.target) (fun os =>
              dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) ((og ++ og1) ++ os)))))
  | .pay u :: code, debt, og => (source read bank15.bits bank15.paths windowRoot (normalizeW u.pre)).seq
      ((fusedFixSource bank15 read u.clear debt og).seq (dsrc read code List.nil List.nil))

theorem dprog_run {n} (read : ConstantBit n → Bool) (code : DCode n) (debt : List (ClearPort n))
    (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((dprog code debt start refs).instantiate read history).run = (dsrc read code debt (refs.map history)).run := by
  induction code generalizing debt start with
  | nil => rfl
  | cons b code ih =>
    cases b with
    | std b =>
      rw [dprog, castFinish_instantiate,
        MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) history history rfl
          (dsrc read code debt (refs.map history)),
        AdaptiveCircuit.run_seq, fblockProg_run]
      · simp only [dsrc, AdaptiveCircuit.run_seq]
      · intro h' hh'
        rw [ih, List.map_map]
        congr 2
        rw [← hh']
        rfl
    | defer u =>
      rw [dprog, castFinish_instantiate,
        MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) history history rfl
          (measureResetThen ((clearData u.clear.ports).map ClearPort.target)
            (fun o => dsrc read code (debt ++ clearData u.clear.ports) (refs.map history ++ o))),
        AdaptiveCircuit.run_seq, compile_run]
      · simp only [dsrc, AdaptiveCircuit.run_seq]
      · intro h' hh'
        rw [MeasuredClear.measureThen_run _ (fun ol => dsrc read code (debt ++ clearData u.clear.ports) ol) read
          (fun cursor rs hist => ih _ cursor rs hist), List.map_map]
        congr 3
        funext o
        congr 2
        rw [← hh']
        rfl
    | defer1 f =>
      rw [dprog, castFinish_instantiate,
        MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) history history rfl
          (measureResetThen ((clearData f.garbPorts).map ClearPort.target) (fun og1 =>
            (source read bank15.bits bank15.paths windowRoot (normalizeW f.site.arithmetic)).seq
              (measureResetThen ((clearData f.site.ports).map ClearPort.target) (fun os =>
                dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports)
                  ((refs.map history ++ og1) ++ os))))),
        AdaptiveCircuit.run_seq, FastSite1.swapProgram, FastSite1.selProgram,
        append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
        compile_run]
      · simp only [dsrc, AdaptiveCircuit.run_seq]
      · intro h' hh'
        rw [MeasuredClear.measureThen_run _ (fun gl =>
            (source read bank15.bits bank15.paths windowRoot (normalizeW f.site.arithmetic)).seq
              (measureResetThen ((clearData f.site.ports).map ClearPort.target) (fun os =>
                dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) (gl ++ os)))) read,
          List.map_map]
        · congr 3
          funext og1
          congr 4
          funext os
          congr 3
          rw [← hh']
          rfl
        · intro cursor grefs hist
          rw [castFinish_instantiate,
            MeasuredClear.append_run_prefix _ _ read (Nat.le_refl cursor) hist hist rfl
              (measureResetThen ((clearData f.site.ports).map ClearPort.target) (fun os =>
                dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) (grefs.map hist ++ os))),
            AdaptiveCircuit.run_seq, compile_run, ← AdaptiveCircuit.run_seq]
          intro h2 hh2
          rw [MeasuredClear.measureThen_run _
            (fun sl => dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) sl) read
            (fun c2 rs hist2 => ih _ c2 rs hist2), List.map_map]
          congr 3
          funext os
          congr 2
          rw [← hh2]
          rfl
    | pay u =>
      rw [dprog, castFinish_instantiate,
        MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) history history rfl
          ((fusedFixSource bank15 read u.clear debt (refs.map history)).seq (dsrc read code List.nil List.nil)),
        AdaptiveCircuit.run_seq, compile_run]
      · simp only [dsrc, AdaptiveCircuit.run_seq]
      · intro h' hh'
        have e : (refs.map (Fin.castLE (Nat.le_add_right start (preRec u)))).map h' = refs.map history := by
          rw [List.map_map, ← hh']
          rfl
        rw [append_run_fixed _ _ _ _ (dsrc read code List.nil List.nil) (fun h => ih List.nil _ List.nil h),
          AdaptiveCircuit.run_seq, AdaptiveCircuit.run_seq, fusedFix_run, e]

/-! #### Simulation with a phase debt -/

/-- Geometry, plus a window-root guard on every deferring or repaying clear. -/
def DGuard {n} : DBlock n → Prop
  | .std _ => True
  | .defer u => u.clear.guard = windowRoot
  | .defer1 f => f.site.guard = windowRoot
  | .pay u => u.clear.guard = windowRoot

def DGeo {n} (b : DBlock n) : Prop := FBlockGeo b.toF ∧ DGuard b

/-- Every deferred phase is repaid by the end of the row. -/
def Paid {n} : DCode n → List (ClearPort n) → Prop
  | [], d => d = List.nil
  | .std _ :: c, d => Paid c d
  | .defer u :: c, d => Paid c (d ++ clearData u.clear.ports)
  | .defer1 f :: c, d => Paid c ((d ++ clearData f.garbPorts) ++ clearData f.site.ports)
  | .pay _ :: c, _ => Paid c List.nil

/-- A branch of a row suffix that still owes the phase of `debt`. -/
def DSim {n} (read : ConstantBit n → Bool) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a st, AddrValid windowBits windowRoot a st → FCodeClean read a (dfor code) st →
      Safe2 read a (fforget (dfor code)) st →
      b.kraus (Bridge.signedKet st) =
        (c * debtPhase read a debt og) •
          Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m st)

/-- A measured clear followed by the rest of the row, seen from the state before the measurement. -/
def MSim {n} (read : ConstantBit n → Bool) (data : List (ClearPort n)) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a (st : ECDSAAdd.State), (∀ p ∈ data, st.basis p.target = decide (read (p.ref a) = p.value)) →
      AddrValid windowBits windowRoot a ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩ →
      FCodeClean read a (dfor code) ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩ →
      Safe2 read a (fforget (dfor code)) ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩ →
      b.kraus (Bridge.signedKet st) =
        (c * debtPhase read a debt og) • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m
          ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩)

/-- Measuring a loaded register adds its ports to the debt: the measurement phase equals the new
debt factor, which the rest of the row repays. -/
theorem measure_dsim {n} (read : ConstantBit n → Bool) (data : List (ClearPort n))
    (hnd : (data.map ClearPort.target).Nodup) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (hog : og.length = debt.length) (next : List Bool → AdaptiveCircuit)
    (hn : ∀ o, o.length = data.length → ∃ cs : List ℂ,
      List.Forall₂ (DSim read code (debt ++ data) (og ++ o)) (next o).run cs ∧ (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (MSim read data code debt og)
      (measureResetThen (data.map ClearPort.target) next).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  apply MeasuredClear.measureResetThen_sim (data.map ClearPort.target) next
    (fun o => DSim read code (debt ++ data) (og ++ o))
  · intro o ho
    exact hn o (by simpa using ho)
  · intro o ho b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, hm, ?_⟩
    intro a st hw hs hc hsafe
    have hk := xResetRegisterKraus_ket (data.map ClearPort.target) o st.basis ho hnd
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho,
      MeasuredClear.registerXPhase_debt read a data o st.basis hw] at hk
    have h := hb a _ hs hc hsafe
    rw [MeasuredClear.debtPhase_append read a debt data og o hog] at h
    have hsq := MeasuredClear.debtPhase_square read a data o
    change b.kraus (xResetRegisterKraus (data.map ClearPort.target) o (Bridge.signedKet st)) = _
    have hstep : b.kraus (xResetRegisterKraus (data.map ClearPort.target) o (Bridge.signedKet st)) =
        (registerXResetMagnitude (data.map ClearPort.target).length * debtPhase read a data o) •
          b.kraus (Bridge.signedKet ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩) := by
      simp only [Bridge.signedKet, map_smul, hk, smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (data.map ClearPort.target).length * c *
      debtPhase read a debt og) * hsq

/-- What a unit's clear and the rest of the row do, seen from the state after the unit's prefix. -/
def ASim {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a (st : ECDSAAdd.State), SimulationValid bank15.bits bank15.paths windowRoot a st →
      (∀ p ∈ site.ports, st.basis p.target = decide (read (p.ref a) = p.value)) →
      AddrValid windowBits windowRoot a ⟨st.phase, clearRegister (portTargets site.ports) st.basis⟩ →
      FCodeClean read a (dfor code) ⟨st.phase, clearRegister (portTargets site.ports) st.basis⟩ →
      Safe2 read a (fforget (dfor code)) ⟨st.phase, clearRegister (portTargets site.ports) st.basis⟩ →
      b.kraus (Bridge.signedKet st) =
        (c * debtPhase read a debt og) • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m
          ⟨st.phase, clearRegister (portTargets site.ports) st.basis⟩)

theorem defer_asim {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hnd : (portTargets site.ports).Nodup)
    (code : DCode n) (debt : List (ClearPort n)) (og : List Bool) (hog : og.length = debt.length)
    (hn : ∀ o, o.length = (clearData site.ports).length → ∃ cs : List ℂ,
      List.Forall₂ (DSim read code (debt ++ clearData site.ports) (og ++ o))
        (dsrc read code (debt ++ clearData site.ports) (og ++ o)).run cs ∧ (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (ASim read site code debt og)
      (measureResetThen ((clearData site.ports).map ClearPort.target)
        (fun o => dsrc read code (debt ++ clearData site.ports) (og ++ o))).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cs, al, mass⟩ := measure_dsim read (clearData site.ports) (by rw [clearData_targets]; exact hnd)
    code debt og hog _ hn
  refine ⟨cs, al.imp ?_, mass⟩
  intro b c hb
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨m, hm, fun a st _ hw hs hc hsafe => ?_⟩
  have h := hb a st (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact hw p hp)
    (by rw [clearData_targets]; exact hs) (by rw [clearData_targets]; exact hc)
    (by rw [clearData_targets]; exact hsafe)
  rw [clearData_targets] at h
  exact h

theorem pay_asim {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeoP bank15 site)
    (hr : site.guard = windowRoot) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (hog : og.length = debt.length)
    (hn : ∃ cs : List ℂ, List.Forall₂ (DSim read code List.nil List.nil) (dsrc read code List.nil List.nil).run cs ∧
      (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (ASim read site code debt og)
      ((fusedFixSource bank15 read site debt og).seq (dsrc read code List.nil List.nil)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := payFix_sim read bank15 bank15_ok site hg debt og hog
  obtain ⟨c2, a2, m2⟩ := hn
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₂⟩ := h₂
    refine ⟨m, hm, ?_⟩
    intro a st hs hw haddr hc hsafe
    have h1 := h₁ st a (fun w hw => hs.1 w (bank15_ok.sub w hw)) hs.2.1 (by rw [hr]; exact hs.2.2) hw
    have h2 := h₂ a _ haddr hc hsafe
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h1, map_smul, h2, MeasuredClear.debtPhase_nil, smul_smul]
    congr 1
    ring
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

/-- A unit block: its prefix, then its clear with the rest of the row. -/
theorem unit_dsim {n} (read : ConstantBit n → Bool) (u : UnitSite n) (hg : UnitGeoP bank15 u)
    (hr : u.clear.guard = windowRoot) (D : DBlock n) (hD : D.toF = .std (.unit u)) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (k : AdaptiveCircuit)
    (hk : ∃ cs : List ℂ, List.Forall₂ (ASim read u.clear code debt og) k.run cs ∧
      (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (DSim read (D :: code) debt og)
      ((source read bank15.bits bank15.paths windowRoot (normalizeW u.pre)).seq k).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hp : ∀ i ∈ u.pre, PlacedPair bank15.bits bank15.paths windowRoot i := by
    intro i hi; exact hg.placed i (List.mem_append_left _ hi)
  obtain ⟨preCs, preAligned, preMass⟩ := lnormalized_simulation read bank15.bits bank15.paths
    bank15_ok.bitsLen u.pre (fun i hi => pair_of_placed_lit _ _ i (hp i hi))
  obtain ⟨cs, aligned, mass⟩ := hk
  have hlast := hg.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
  have hlen : literalRecords (Block2.unit u).code = literalRecords u.pre := by
    simp [Block2.code, UnitSite.code, literalRecords_append, literalRecords]
  refine ⟨coherentSeqCoefficients preCs cs, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq preAligned aligned
    intro b₁ c₁ b₂ c₂ h₁ h₂
    obtain ⟨m₁, hm₁, h₁⟩ := h₁
    obtain ⟨m₂, hm₂, h₂⟩ := h₂
    refine ⟨m₁ ++ m₂, ?_, ?_⟩
    · simp only [dfor_cons, hD, fforget_cons, FBlock2.forget, erase2_cons, literalRecords_append,
        List.length_append, hm₁, hm₂, hlen]
    · intro a st hs hc hsafe
      simp only [dfor_cons, hD, fforget_cons, FBlock2.forget] at hc hsafe ⊢
      have hcl : Clean bank15.paths st.basis := hc.1.1
      have hsv : SimulationValid bank15.bits bank15.paths windowRoot a st := ⟨hcl, hs.1, hs.2⟩
      have hn := strict_preserves read bank15.bits bank15.paths u.pre a hp st hsv m₁
      have hrun := unit_runP read bank15 u hg a st m₁ hsv
      set next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m₁ st with hnext
      have hclean : Clean (portTargets u.clear.ports)
          (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
        have h := hsafe.1 m₁
        rw [hrun] at h
        exact h
      have hload := loaded_of_clean_unload read u.clear.ports a u.clear.guard next.basis hlast.2.1 hclean
      have hroot : next.basis u.clear.guard = true := by rw [hr]; exact hn.2.2
      have hblock : ECDSAAdd.run (blockReference2 read a (.unit u)) m₁ st =
          ⟨next.phase, clearRegister (portTargets u.clear.ports) next.basis⟩ := by
        show ECDSAAdd.run ((specialize u.code a).instantiate read) m₁ st = _
        rw [hrun, clear_eq_unload read u.clear.ports a u.clear.guard next.basis hclean]
      have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a (.unit u)) :=
        (hm₁.trans hlen.symm).trans (specialize_counts read (Block2.unit u).code a).2.symm
      have haddr := fblock_addr read (.std (.unit u)) hg a st hs hc.1 m₁
      simp only [FBlock2.forget] at haddr
      rw [hblock] at haddr
      have hc2 := hc.2 m₁ hm
      have hs2 := hsafe.2 m₁ hm
      simp only [FBlock2.forget] at hc2
      rw [hblock] at hc2 hs2
      have h2 := h₂ a next hn (fun p hp => by rw [hload p hp, hroot, Bool.true_and]) haddr hc2 hs2
      change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
      rw [h₁ a st hs (strict_pathsClean read bank15.bits bank15.paths u.pre a hp st hsv), map_smul, h2,
        reference2_cons, run_append_records _ _ m₁ m₂ st hm, hblock]
      simp [smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, preMass, mass]
    norm_num

/-! #### The deferred second fast site -/

/-- The arithmetic and the site measurement, followed by the rest of the row, seen from the reference
state after the site's load. -/
def InnerD {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m₁ m₂ : List Bool, m₁.length = literalRecords site.arithmetic ∧
    m₂.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a (st : ECDSAAdd.State), SimulationValid bank15.bits bank15.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports) (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      FCodeClean read a (dfor code) (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st) →
      Safe2 read a (fforget (dfor code)) (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st) →
      b.kraus (Bridge.signedKet ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) =
        (c * debtPhase read a debt og) • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m₂
          (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st))

theorem inner_d {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeoP bank15 site)
    (hr : site.guard = windowRoot) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (hog : og.length = debt.length)
    (hn : ∀ o, o.length = (clearData site.ports).length → ∃ cs : List ℂ,
      List.Forall₂ (DSim read code (debt ++ clearData site.ports) (og ++ o))
        (dsrc read code (debt ++ clearData site.ports) (og ++ o)).run cs ∧ (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (InnerD read site code debt og)
      ((source read bank15.bits bank15.paths windowRoot (normalizeW site.arithmetic)).seq
        (measureResetThen ((clearData site.ports).map ClearPort.target)
          (fun os => dsrc read code (debt ++ clearData site.ports) (og ++ os)))).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hpre : ∀ i ∈ site.prefix, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have harith : ∀ i ∈ site.arithmetic, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
    hpre i (List.mem_cons_of_mem _ hi)
  have hcode : ∀ i ∈ site.code, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i hi)
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read bank15.bits bank15.paths bank15_ok.bitsLen site.arithmetic
    (fun i hi => pair_of_placed_lit _ _ i (harith i hi))
  obtain ⟨c2, a2, m2⟩ := measure_dsim read (clearData site.ports) (by rw [clearData_targets]; exact hlast.2.1)
    code debt og hog _ hn
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₁⟩ := h₁
    obtain ⟨m', hm', h₂⟩ := h₂
    refine ⟨m, m', hm, hm', ?_⟩
    intro a st hs hun hc hsafe
    have hload := hg.placed (.lookup (some site.guard) site.ports)
      (by simp [MaskedSite.code, MaskedSite.prefix])
    have hL := lookup_preserves_simulation read (some site.guard) site.ports bank15.bits bank15.paths
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
    have hn := strict_preserves read bank15.bits bank15.paths site.prefix a hpre st hs m
    have hrun := masked_runP read bank15 site hg a st m hs
    set L : ECDSAAdd.State :=
      ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩ with hLdef
    set next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st with hnext
    have hclean : Clean (portTargets site.ports)
        (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
      have h := hun m
      rw [hrun] at h
      exact h
    have hsite := loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
    have hgt : next.basis site.guard = true := by rw [hr]; exact hn.2.2
    have hfin : (⟨next.phase, clearRegister ((clearData site.ports).map ClearPort.target) next.basis⟩ :
        ECDSAAdd.State) = ECDSAAdd.run ((specialize site.code a).instantiate read) m st := by
      rw [clearData_targets, hrun, clear_eq_unload read site.ports a site.guard next.basis hclean]
    have hcv := strict_preserves read bank15.bits bank15.paths site.code a hcode st hs m
    have h2 := h₂ a next (by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        rw [hsite p hp, hgt, Bool.true_and])
      (by rw [hfin]; exact ⟨hcv.2.1, hcv.2.2⟩) (by rw [hfin]; exact hc) (by rw [hfin]; exact hsafe)
    have h1 := h₁ a L ⟨hL.2.1, hL.2.2⟩ (strict_pathsClean read bank15.bits bank15.paths site.arithmetic a harith L hL)
    rw [← e] at h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet L)) = _
    rw [h1, map_smul, h2, hfin, smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

/-- The garbage measurement, then `InnerD`: the garbage ports join the debt. -/
def TailD {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n)) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m₁ m₂ : List Bool, m₁.length = literalRecords site.arithmetic ∧
    m₂.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a (st u : ECDSAAdd.State), SimulationValid bank15.bits bank15.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports) (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      FCodeClean read a (dfor code) (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st) →
      Safe2 read a (fforget (dfor code)) (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st) →
      (∀ p ∈ gd, u.basis p.target = decide (read (p.ref a) = p.value)) → u.phase = st.phase →
      clearRegister (gd.map ClearPort.target) u.basis =
        tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis →
      b.kraus (Bridge.signedKet u) =
        (c * debtPhase read a debt og) • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m₂
          (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st))

theorem tail_d {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeoP bank15 site)
    (hr : site.guard = windowRoot) (gd : List (ClearPort n)) (hgn : (gd.map ClearPort.target).Nodup)
    (code : DCode n) (debt : List (ClearPort n)) (og : List Bool) (hog : og.length = debt.length)
    (hn : ∀ og1 os, og1.length = gd.length → os.length = (clearData site.ports).length → ∃ cs : List ℂ,
      List.Forall₂ (DSim read code ((debt ++ gd) ++ clearData site.ports) ((og ++ og1) ++ os))
        (dsrc read code ((debt ++ gd) ++ clearData site.ports) ((og ++ og1) ++ os)).run cs ∧
        (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (TailD read site gd code debt og)
      (measureResetThen (gd.map ClearPort.target) (fun og1 =>
        (source read bank15.bits bank15.paths windowRoot (normalizeW site.arithmetic)).seq
          (measureResetThen ((clearData site.ports).map ClearPort.target) (fun os =>
            dsrc read code ((debt ++ gd) ++ clearData site.ports) ((og ++ og1) ++ os))))).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  apply MeasuredClear.measureResetThen_sim (gd.map ClearPort.target) _
    (fun og1 => InnerD read site code (debt ++ gd) (og ++ og1))
  · intro og1 hog1
    exact inner_d read site hg hr code (debt ++ gd) (og ++ og1) (by simp [hog, hog1])
      (fun os hos => hn og1 os (by simpa using hog1) hos)
  · intro og1 hog1 b c hb
    obtain ⟨m₁, m₂, hm₁, hm₂, hb⟩ := hb
    refine ⟨m₁, m₂, hm₁, hm₂, ?_⟩
    intro a st u hs hun hc hsafe hu hph hclr
    have hk' := xResetRegisterKraus_ket (gd.map ClearPort.target) og1 u.basis hog1 hgn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hog1, hclr,
      MeasuredClear.registerXPhase_debt read a gd og1 u.basis hu] at hk'
    have h := hb a st hs hun hc hsafe
    rw [MeasuredClear.debtPhase_append read a debt gd og og1 hog] at h
    have hsq := MeasuredClear.debtPhase_square read a gd og1
    change b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og1 (Bridge.signedKet u)) = _
    have hstep : b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og1 (Bridge.signedKet u)) =
        (registerXResetMagnitude (gd.map ClearPort.target).length * debtPhase read a gd og1) •
          b.kraus (Bridge.signedKet ⟨st.phase,
            tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) := by
      simp only [Bridge.signedKet, hph, map_smul, hk', smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (gd.map ClearPort.target).length * c *
      debtPhase read a debt og) * hsq

/-- The second fast site with both of its measurements deferred to the row's last clear. -/
theorem defer1_dsim {n} (read : ConstantBit n → Bool) (f : FastSite1 n) (hg : FastGeometry1 f)
    (hr : f.site.guard = windowRoot) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (hog : og.length = debt.length)
    (hn : ∀ og1 os, og1.length = (clearData f.garbPorts).length → os.length = (clearData f.site.ports).length →
      ∃ cs : List ℂ,
      List.Forall₂ (DSim read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) ((og ++ og1) ++ os))
        (dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) ((og ++ og1) ++ os)).run cs ∧
        (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (DSim read (.defer1 f :: code) debt og)
      (dsrc read (.defer1 f :: code) debt og).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := FastSite1.swap_simulation f read hg
  obtain ⟨c2, a2, m2⟩ := tail_d read f.site hg.site hr (clearData f.garbPorts)
    (by rw [clearData_targets, FastSite1.garbPorts_targets f hg]; exact FastSite1.garb_nodup f hg)
    code debt og hog hn
  have hlen : literalRecords (Block2.unit (siteUnit f.site)).code = literalRecords f.site.arithmetic := by
    simp [Block2.code, siteUnit_code, MaskedSite.code, MaskedSite.prefix, literalRecords, literalRecords_append]
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [dsrc, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m₁, m₂, hm₁, hm₂, h₂⟩ := h₂
    refine ⟨m₁ ++ m₂, ?_, ?_⟩
    · simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget, erase2_cons, literalRecords_append,
        List.length_append, hm₁, hm₂, hlen]
    · intro a st hs hc hsafe
      simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget] at hc hsafe ⊢
      have hsv : SimulationValid windowBits pathBank windowRoot a st := ⟨hc.1.1, hs.1, hs.2⟩
      have hgarb := FastSite1.load_garb f read hg a st hsv hc.1.2
      have heq := FastSite1.load_clear_eq f read hg a st hsv hc.1.2
      have hph := (FastSite1.load_state f read hg a st hsv hc.1.2).1
      dsimp only at hgarb heq hph
      have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a (.unit (siteUnit f.site))) :=
        (hm₁.trans hlen.symm).trans (specialize_counts read (Block2.unit (siteUnit f.site)).code a).2.symm
      have hc2 := hc.2 m₁ hm
      have hs2 := hsafe.2 m₁ hm
      change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
      rw [h₁ a st hsv hc.1.2, map_smul, h₂ a st _ hsv hsafe.1 hc2 hs2
        (by
          intro q hq
          rw [hgarb q hq, hr, hs.2, Bool.true_and])
        hph (by rw [clearData_targets, FastSite1.garbPorts_targets f hg]; exact heq),
        reference2_cons, run_append_records _ _ m₁ m₂ st hm]
      simp [smul_smul, mul_assoc, blockReference2, Block2.code, siteUnit_code]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

/-! #### The whole row -/

theorem dsrc_sim {n} (read : ConstantBit n → Bool) (code : DCode n) (hg : ∀ b ∈ code, DGeo b)
    (debt : List (ClearPort n)) (og : List Bool) (hog : og.length = debt.length) (hp : Paid code debt) :
    ∃ cs : List ℂ, List.Forall₂ (DSim read code debt og) (dsrc read code debt og).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code generalizing debt og with
  | nil =>
    have hd : debt = List.nil := hp
    subst hd
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    exact ⟨List.nil, rfl, fun a st _ _ _ => by
      simp [reference2, erase2, fforget, dfor, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]⟩
  | cons b code ih =>
    have hgb := hg b (by simp)
    have hgc : ∀ d ∈ code, DGeo d := fun d hd => hg d (by simp [hd])
    cases b with
    | std b =>
      obtain ⟨cs₁, h₁, mass₁⟩ := fblock_sim read b hgb.1
      obtain ⟨cs₂, h₂, mass₂⟩ := ih hgc debt og hog hp
      refine ⟨coherentSeqCoefficients cs₁ cs₂, ?_, ?_⟩
      · rw [dsrc, AdaptiveCircuit.run_seq]
        apply simulationAligned_seq h₁ h₂
        intro b₁ c₁ b₂ c₂ hb₁ hb₂
        obtain ⟨m₁, len₁, run₁⟩ := hb₁
        obtain ⟨m₂, len₂, run₂⟩ := hb₂
        refine ⟨m₁ ++ m₂, ?_, ?_⟩
        · simp [dfor_cons, DBlock.toF, fforget_cons, erase2, List.length_append, len₁, len₂]
        · intro a st hs hc hsafe
          simp only [dfor_cons, DBlock.toF, fforget_cons] at hc hsafe ⊢
          have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a b.forget) :=
            len₁.trans (specialize_counts read b.forget.code a).2.symm
          have hn := fblock_addr read b hgb.1 a st hs hc.1 m₁
          change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
          rw [run₁ a st hs hc.1 hsafe.1, map_smul,
            run₂ a (ECDSAAdd.run (blockReference2 read a b.forget) m₁ st) hn (hc.2 m₁ hm) (hsafe.2 m₁ hm),
            reference2_cons, run_append_records _ _ m₁ m₂ st hm]
          simp [smul_smul, mul_assoc]
      · rw [simulationCoefficients_mass, mass₁, mass₂]
        norm_num
    | defer u =>
      obtain ⟨hgF, hr⟩ := hgb
      have hu : UnitGeoP bank15 u := hgF
      have hlast := hu.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
      exact unit_dsim read u hu hr (.defer u) rfl code debt og _
        (defer_asim read u.clear hlast.2.1 code debt og hog
          (fun o ho => ih hgc _ _ (by simp [hog, ho]) hp))
    | defer1 f =>
      obtain ⟨hgF, hr⟩ := hgb
      exact defer1_dsim read f hgF.1 hr code debt og hog
        (fun og1 os h1 h2 => ih hgc _ _ (by simp [hog, h1, h2]) hp)
    | pay u =>
      obtain ⟨hgF, hr⟩ := hgb
      have hu : UnitGeoP bank15 u := hgF
      exact unit_dsim read u hu hr (.pay u) rfl code debt og _
        (pay_asim read u.clear hu.site hr code debt og hog (ih hgc List.nil List.nil rfl hp))

theorem dprog_coherent {n} (read : ConstantBit n → Bool) (code : DCode n) (hg : ∀ b ∈ code, DGeo b)
    (hp : Paid code List.nil) (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue windowBits s) (fforget (dfor code)) ⟨false,s⟩)
    (hclean : ∀ s, Valid s → FCodeClean read (tableAddressValue windowBits s) (dfor code) ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue windowBits s) (fforget (dfor code))) m ⟨false,s⟩ =
        ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((dprog code List.nil start List.nil).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := dsrc_sim read code hg List.nil List.nil rfl hp
  refine ⟨cs, ?_, mass⟩
  rw [dprog_run, List.map_nil]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨rfl, hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [MeasuredClear.debtPhase_nil, mul_one, Bridge.signedKet_false, hrun s hs.2 m, Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.WideBank8.Fast16

/-! #### Resources of the deferred row -/

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic
open MeasuredClear (ClearPort debtPhase)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

def dblockTP {n} : DBlock n → Nat
  | .std b => fblockTP b
  | .defer u => literalToffolis (normalizeW u.pre) + traversals u.pre * (2 ^ bank15.bits.length - 1)
  | .defer1 f => 32767 + ECDSAAdd.toffoliCount f.swapNet +
      (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535)
  | .pay u => literalToffolis (normalizeW u.pre) + traversals u.pre * (2 ^ bank15.bits.length - 1) +
      ((tableAddressTree bank15.high 0 1).internalNodes + 247)

def dcodeTP {n} : DCode n → Nat
  | [] => 0
  | b :: code => dblockTP b + dcodeTP code

/-- The Toffoli units each deferred fixup saves. -/
def dsave {n} : DCode n → Nat
  | [] => 0
  | .std _ :: c => dsave c
  | .defer _ :: c => 502 + dsave c
  | .defer1 _ :: c => 502 + dsave c
  | .pay _ :: c => dsave c

/-- The records each deferred fixup saves. -/
def drsave {n} : DCode n → Nat
  | [] => 0
  | .std _ :: c => drsave c
  | .defer _ :: c => 510 + drsave c
  | .defer1 _ :: c => 510 + drsave c
  | .pay _ :: c => drsave c

@[simp] theorem paid_std {n} {α : Type} (l : List α) (g : α → FBlock2 n) (rest : DCode n)
    (d : List (ClearPort n)) : Paid (l.map (fun x => DBlock.std (g x)) ++ rest) d = Paid rest d := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [Paid] using ih

@[simp] theorem dsave_std {n} {α : Type} (l : List α) (g : α → FBlock2 n) (rest : DCode n) :
    dsave (l.map (fun x => DBlock.std (g x)) ++ rest) = dsave rest := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [dsave] using ih

@[simp] theorem drsave_std {n} {α : Type} (l : List α) (g : α → FBlock2 n) (rest : DCode n) :
    drsave (l.map (fun x => DBlock.std (g x)) ++ rest) = drsave rest := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [drsave] using ih

theorem guard_std {n} {α : Type} (l : List α) (g : α → FBlock2 n) :
    ∀ b ∈ l.map (fun x => DBlock.std (g x)), DGuard b := by
  intro b hb
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
  trivial

theorem dprog_tCount {n} (read : ConstantBit n → Bool) (code : DCode n) (hg : ∀ b ∈ code, DGeo b)
    (debt : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((dprog code debt start refs).instantiate read history).tCount = 7 * dcodeTP code := by
  induction code generalizing debt start with
  | nil => simp [dprog, drecs, dcodeTP, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons b code ih =>
    have hgb := hg b (by simp)
    have hgc : ∀ d ∈ code, DGeo d := fun d hd => hg d (by simp [hd])
    cases b with
    | std b =>
      rw [dprog, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h => ih hgc _ _ _ h),
        fblock_tCount read b hgb.1]
      simp only [dcodeTP, dblockTP]; ring
    | defer u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      rw [dprog, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h =>
          MeasuredClear.measureThen_tCount _ read (fun cursor rs hist => ih hgc _ cursor rs hist) _ _ _ h),
        compile_tCount read _ _ _ _ hl.1 start history, traversals_normalize]
      simp only [dcodeTP, dblockTP]; ring
    | defer1 f =>
      rw [dprog, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h =>
          MeasuredClear.measureThen_tCount _ read (fun cursor grefs hist => by
            rw [castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h2 =>
                MeasuredClear.measureThen_tCount _ read (fun c2 rs hist2 => ih hgc _ c2 rs hist2) _ _ _ h2),
              compile_tCount read bank15.bits bank15.paths windowRoot _ (FastSite1.arith_layouts f hgb.1.1) _ hist])
            _ _ _ h),
        FastSite1.swapProgram, FastSite1.selProgram,
        append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
        compile_tCount read selBits1 selPaths1 windowRoot _ (FastSite1.sel_layouts f hgb.1.1), traversals_normalize]
      simp only [dcodeTP, dblockTP, FastSite1.selCode, literalToffolis, traversals, selBits1, bank15, windowBits,
        List.length_range', List.length_append, List.length_cons, List.length_nil]
      norm_num
      try ring
    | pay u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      rw [dprog, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h => by
          rw [append_tCount_fixed _ _ _ _ _ (fun h' => ih hgc _ _ _ h'),
            fusedFix_tCount read bank15 u.clear _ hl.2 _ _ h]),
        compile_tCount read _ _ _ _ hl.1 start history, traversals_normalize]
      simp only [dcodeTP, dblockTP]; ring

theorem dcodeTP_relation {n} (code : DCode n) (hg : ∀ b ∈ code, DGeo b) :
    dcodeTP code + dsave code = fcodeTP (dfor code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    cases b with
    | std b => simp only [dcodeTP, dsave, dblockTP, dfor_cons, DBlock.toF, fcodeTP]; omega
    | defer u =>
      simp only [dcodeTP, dsave, dblockTP, dfor_cons, DBlock.toF, fcodeTP, fblockTP, blockTP2, bank_tree_nodes]
      omega
    | defer1 f =>
      simp only [dcodeTP, dsave, dblockTP, dfor_cons, DBlock.toF, fcodeTP, fblockTP, FastSite1.fusedTP]
      omega
    | pay u => simp only [dcodeTP, dsave, dblockTP, dfor_cons, DBlock.toF, fcodeTP, fblockTP, blockTP2]; omega

theorem drecs_relation {n} (code : DCode n) (hg : ∀ b ∈ code, DGeo b) :
    drecs code + drsave code = frecs (dfor code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hgb := hg b (by simp)
    cases b with
    | std b => simp only [drecs, drsave, dblockRec, dfor_cons, DBlock.toF, frecs]; omega
    | defer u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      have hcr := (MeasuredClear.recordUnary_counts _ _ _ hl.2 0).1
      rw [bank_tree_nodes] at hcr
      simp only [drecs, drsave, dblockRec, dfor_cons, DBlock.toF, frecs, fblockRec, blockRecP2, hcr, preRec]
      omega
    | defer1 f =>
      simp only [drecs, drsave, dblockRec, dfor_cons, DBlock.toF, frecs, fblockRec, FastSite1.fusedRecords,
        tailRec, fuseRec, selRec1, arithRec]
      have hcr := (MeasuredClear.recordUnary_counts _ _ _ (FastSite1.site_layout_bank f hgb.1.1) 0).1
      rw [bank_tree_nodes] at hcr
      have hcr' : MeasuredClear.recordMeasurements
          (MeasuredClear.recordUnaryOps (tableAddressTree bank15.high 0 1) f.site.guard bank15.hp) = 255 := hcr
      rw [hcr']
      omega
    | pay u =>
      simp only [drecs, drsave, dblockRec, dfor_cons, DBlock.toF, frecs, fblockRec, blockRecP2, fuseRec, preRec]
      omega

theorem measureThen_slots_le {n R : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor + R)) (B : Nat)
    (hn : ∀ cursor refs, (next cursor refs).gateSlots ≤ B) :
    ∀ (wires : List Wire) (start : Nat) (refs : List (Fin start)),
      (MeasuredClear.measureThen next wires start refs).gateSlots ≤ B
  | [], start, refs => by simpa [MeasuredClear.measureThen] using hn start refs
  | w :: ws, start, refs => by
    simp only [MeasuredClear.measureThen, castFinish_gateSlots, Straight.gateSlots]
    exact measureThen_slots_le next B hn ws _ _

theorem fblock_slots {n} (b : FBlock2 n) (hg : FBlockGeo b) (start : Nat) :
    (fblockProg b start).gateSlots ≤ blockSP2 bank15 b.forget + fblockSlack b := by
  cases b with
  | std b =>
    rw [show fblockProg (.std b) start = blockProgH bank15 b start from rfl]
    exact blockH_slots bank15 b (geo_lay2 bank15 bank15_ok b hg) start
  | fast f => exact f.fused_slots hg.1 start
  | fast1 f => exact f.fused_slots hg.1 start

/-- The repaying fixup's slot term grows with the debt; each deferred clear saved at least as much. -/
theorem dprog_slots {n} (code : DCode n) (hg : ∀ b ∈ code, DGeo b) (debt : List (ClearPort n))
    (start : Nat) (refs : List (Fin start)) :
    (dprog code debt start refs).gateSlots ≤
      codeSP2 bank15 (fforget (dfor code)) + fslack (dfor code) + 262144 * debt.length := by
  induction code generalizing debt start with
  | nil => simp [dprog, drecs, Straight.gateSlots, codeSP2]
  | cons b code ih =>
    have hgb := hg b (by simp)
    have hgc : ∀ d ∈ code, DGeo d := fun d hd => hg d (by simp [hd])
    cases b with
    | std b =>
      have hb := fblock_slots b hgb.1 start
      have hr := ih hgc debt (start + fblockRec b) (refs.map (Fin.castLE (Nat.le_add_right _ _)))
      rw [dprog, castFinish_gateSlots, Straight.gateSlots_append]
      simp only [dfor_cons, DBlock.toF, fforget_cons, codeSP2, fslack]
      omega
    | defer u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      have hm := measureThen_slots_le (R := drecs code)
        (fun cursor rs => dprog code (debt ++ clearData u.clear.ports) cursor rs) _
        (fun cursor rs => ih hgc (debt ++ clearData u.clear.ports) cursor rs)
        ((clearData u.clear.ports).map ClearPort.target) (start + preRec u)
        (refs.map (Fin.castLE (Nat.le_add_right _ _)))
      rw [dprog, castFinish_gateSlots, Straight.gateSlots_append, compile_slots _ _ _ _ hl.1 start]
      simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget, codeSP2, fslack, fblockSlack, blockSP2,
        bank_tree_leaves, bank_tree_nodes, clearData, List.length_append, List.length_map] at hm ⊢
      omega
    | defer1 f =>
      have hgf := hgb.1.1
      rw [dprog, castFinish_gateSlots]
      simp only [Straight.gateSlots_append]
      refine le_trans (Nat.add_le_add_left (measureThen_slots_le _
        (codeSlots bank15.bits (normalizeW f.site.arithmetic) + (codeSP2 bank15 (fforget (dfor code)) +
          fslack (dfor code) + 262144 * ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports).length))
        (fun cursor grefs => ?_) _ _ _) _) ?_
      · rw [castFinish_gateSlots, Straight.gateSlots_append,
          compile_slots bank15.bits bank15.paths windowRoot _ (FastSite1.arith_layouts f hgf)]
        exact Nat.add_le_add_left (measureThen_slots_le _ _
          (fun c2 rs => ih hgc ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) c2 rs) _ _ _) _
      rw [FastSite1.swapProgram, literalFixed_slots, FastSite1.selProgram,
        compile_slots _ _ _ _ (FastSite1.sel_layouts f hgf), FastSite1.sel_slots f hgf]
      have hsw := literal_slot_bound (n := n) f.swapNet
      have hd : (clearData f.garbPorts).length = f.garb.length := by
        rw [clearData, List.length_map, FastSite1.garbPorts_length f hgf]
      have hds : (clearData f.site.ports).length = f.site.ports.length := by
        rw [clearData, List.length_map]
      have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
          (65536 * f.site.ports.length + 655350) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
        rw [prefix_split, normalize_append, slots_append_wide, FastSite.lookup_slots]
      simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget, codeSP2, fslack, fblockSlack, blockSP2, siteUnit,
        FastSite1.fastSlack, show bank15.bits = windowBits from rfl, hpre, bank_tree_leaves, bank_tree_nodes,
        List.length_append, hd, hds]
      omega
    | pay u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      have hr := ih hgc List.nil (start + preRec u + u.clear.ports.length + fuseRec bank15 u.clear) List.nil
      rw [dprog, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append,
        compile_slots _ _ _ _ hl.1 start, fusedFix_slots bank15 u.clear debt hl.2]
      simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget, codeSP2, fslack, fblockSlack, blockSP2,
        bank_tree_leaves, bank_tree_nodes, List.length_nil, Nat.mul_zero, Nat.add_zero] at hr ⊢
      have hmin := Nat.min_le_left (debt.length + u.clear.ports.length)
        ((refs.map (Fin.castLE (Nat.le_add_right start (preRec u)))).length + u.clear.ports.length)
      generalize min (debt.length + u.clear.ports.length)
        ((refs.map (Fin.castLE (Nat.le_add_right start (preRec u)))).length + u.clear.ports.length) = k at hmin ⊢
      have : 1024 * k * 256 ≤ 1024 * (debt.length + u.clear.ports.length) * 256 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmin)
      omega

theorem fusedFix_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (gd : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) :
    (fusedFix B site gd start refs).WellFormed := by
  obtain ⟨hl, hdlow, hbank, hs, hshot, -, -⟩ := site_clear_facts B hB site hg
  rw [fusedFix, castFinish_wellFormed]
  apply MeasuredClear.measureThen_wellFormed
  intro c rs
  rw [castFinish_wellFormed]
  exact MeasuredClear.fixupProgram_wellFormed8 _ rs low8 (hot8 site) _ site.guard scratch8 B.hp hl
    (hot8_injective site) hdlow hs hshot

theorem dprog_wellFormed {n} (code : DCode n) (hg : ∀ b ∈ code, DGeo b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 (fforget (dfor code)) → GatePhysical p)
    (debt : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) :
    (dprog code debt start refs).WellFormed := by
  induction code generalizing debt start with
  | nil => trivial
  | cons b code ih =>
    have hgb := hg b (by simp)
    have hgc : ∀ d ∈ code, DGeo d := fun d hd => hg d (by simp [hd])
    have hpb : ∀ p, WInstr.literal p ∈ b.toF.forget.code → GatePhysical p :=
      fun p hm => hp p (by simp [erase2_cons, hm])
    have hpc : ∀ p, WInstr.literal p ∈ erase2 (fforget (dfor code)) → GatePhysical p :=
      fun p hm => hp p (by simp [erase2_cons, hm])
    have hunit (u : UnitSite n) (hu : UnitGeoP bank15 u)
        (hpu : ∀ p, WInstr.literal p ∈ u.code → GatePhysical p) :
        (compile bank15.bits bank15.paths windowRoot (normalizeW u.pre) start).WellFormed := by
      have hpref : ∀ i ∈ u.pre, LPlaced bank15.bits bank15.paths windowRoot i := fun i hi =>
        pair_of_placed_lit _ _ i (hu.placed i (List.mem_append_left _ hi))
      exact compile_wellFormedL _ _ _ _ bank15_ok.bitsLen (lplaced_normalize _ _ _ _ hpref)
        (normalized_literals_valid u.pre (fun p hm => hpu p (List.mem_append_left _ hm))) start
    cases b with
    | std b =>
      rw [dprog, castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (fblock_wellFormed b hgb.1 hpb start) (ih hgc hpc _ _ _)
    | defer u =>
      rw [dprog, castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (hunit u hgb.1 hpb)
        (MeasuredClear.measureThen_wellFormed _ (fun cursor rs => ih hgc hpc _ _ _) _ _ _)
    | defer1 f =>
      have hgf := hgb.1.1
      have harith : ∀ i ∈ f.site.arithmetic, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
        placed_implies_pair _ _ _ _ (hgf.site.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))
      have hlit : ∀ p, WInstr.literal p ∈ f.site.arithmetic → GatePhysical p := fun p hm =>
        hpb p (show WInstr.literal p ∈ f.site.code from List.mem_append_left _ (List.mem_cons_of_mem _ hm))
      rw [dprog, castFinish_wellFormed]
      refine straight_append_wellFormed _ _ (straight_append_wellFormed _ _ ?_ ?_) ?_
      · exact pair_compile_wellFormed _ _ _ _ (by decide)
          (fun i hi => by
            simp only [FastSite1.selCode, List.mem_singleton] at hi
            subst hi
            exact placed_implies_pair _ _ _ _ (FastSite1.sel_placed f hgf))
          (fun p hp => by simp [FastSite1.selCode] at hp) start
      · exact literalFixed_wellFormed _ _ _ (f.swapNet_valid hgf) _
      · apply MeasuredClear.measureThen_wellFormed
        intro cursor grefs
        rw [castFinish_wellFormed]
        exact straight_append_wellFormed _ _
          (pair_compile_wellFormed _ _ _ _ bank15_ok.bitsLen (pair_placed_normalize _ _ _ _ harith)
            (normalized_literals_valid f.site.arithmetic hlit) _)
          (MeasuredClear.measureThen_wellFormed _ (fun c2 rs => ih hgc hpc _ _ _) _ _ _)
    | pay u =>
      have hu : UnitGeoP bank15 u := hgb.1
      rw [dprog, castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (hunit u hu hpb)
        (straight_append_wellFormed _ _ (fusedFix_wellFormed bank15 bank15_ok u.clear hu.site _ _ _)
          (ih hgc hpc _ _ _))

theorem dprog_residue {n} (code : DCode n) (debt : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) :
    residue (dprog code debt start refs) = 0 := by
  induction code generalizing debt start with
  | nil => simp [dprog, drecs]
  | cons b code ih =>
    cases b with
    | std b =>
      have hb : residue (fblockProg b start) = 0 := by
        cases b with
        | std b => exact blockH_residue bank15 b start
        | fast f => exact f.fused_residue start
        | fast1 f => exact f.fused_residue start
      rw [dprog, residue_cast, residue_append, hb, ih]
    | defer u =>
      rw [dprog, residue_cast, residue_append, compile_residue,
        MeasuredClear.measureThen_residue _ (fun cursor rs => ih _ _ _)]
    | defer1 f =>
      rw [dprog, residue_cast]
      simp only [residue_append]
      rw [FastSite1.selProgram, compile_residue, FastSite1.swapProgram, literalFixed, residue_naive_cast,
        literal_residue, MeasuredClear.measureThen_residue]
      intro cursor grefs
      rw [residue_cast, residue_append, compile_residue,
        MeasuredClear.measureThen_residue _ (fun c2 rs => ih _ _ _)]
    | pay u =>
      have hf : residue (fusedFix bank15 u.clear debt (start + preRec u)
          (refs.map (Fin.castLE (Nat.le_add_right _ _)))) = 0 := by
        rw [fusedFix, residue_cast]
        apply MeasuredClear.measureThen_residue
        intro c rs
        rw [residue_cast]
        exact MeasuredClear.fixupProgram_residue8 _ _ _ _ _ _ _ _
      rw [dprog, residue_cast, residue_append, residue_append, compile_residue, hf, ih]

end
end ShorECDLP.Entrant.WideBank8.Fast16

/-! #### Tight support of the deferred wide row -/

namespace ShorECDLP.Entrant.WideBank8.Fast16.Tight
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare WideSigned
open MeasuredClear (ClearPort)
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

theorem fusedFix_support {n} (site : MaskedSite n) (hk : SiteKind site) (gd : List (ClearPort n))
    (S : List Wire) (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low8 i ∈ S)
    (hhigh : bank15.high ⊆ S) (hpaths : bank15.paths ⊆ S) (start : Nat) (refs : List (Fin start)) :
    ChallengeMigration.straightWires (fusedFix bank15 site gd start refs) ⊆ S := by
  have hmem := kind_hot8 site hk
  rw [support_agrees, fusedFix, MeasuredClear.static_cast]
  apply MeasuredClear.measureThen_within _ S _ _ _ _ (by rw [clearData_targets]; exact hS)
  intro c rs
  rw [MeasuredClear.static_cast]
  apply MeasuredClear.fixupProgram_within8 _ _ _ _ _ _ _ _ S hgS (hpaths bank15_ok.scr.1) hlow
    (fun i => hS (hmem i)) _ (fun w hw => hpaths (bank15_ok.sub w hw))
  intro w hw
  apply hhigh
  rw [← bank15_ok.index]
  exact List.mem_dedup.mpr hw

theorem dprog_tsupport (code : DCode 65536) (hg : ∀ b ∈ code, DGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget (dfor code)) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ support)
    (hstrict : ∀ b ∈ dfor code, ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ dfor code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ dfor code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget (dfor code)) →
      (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ b ∈ dfor code, NoHost3 b)
    (debt : List (ClearPort 65536)) (start : Nat) (refs : List (Fin start)) :
    ChallengeMigration.straightWires (dprog code debt start refs) ⊆ support := by
  induction code generalizing debt start with
  | nil => simp [dprog, drecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    have hgb := hg b (by simp)
    have ih' := ih (fun d hd => hg d (by simp [hd])) (fun p hm => hlit p (by simp [erase2_cons, hm]))
      (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd]))
      (fun d hd => hctl3 d (by simp [hd])) (fun c ps hm => hlook c ps (by simp [erase2_cons, hm]))
      (fun d hd => hgarb d (by simp [hd]))
    have hlb : ∀ p, WInstr.literal p ∈ b.toF.forget.code → ∀ w ∈ ECDSAAdd.wires p,
        w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ support :=
      fun p hm => hlit p (by simp [erase2_cons, hm])
    have hkb : ∀ c ps, WInstr.lookup c ps ∈ b.toF.forget.code →
        (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support :=
      fun c ps hm => hlook c ps (by simp [erase2_cons, hm])
    have hsb := hstrict b.toF (by simp)
    have hblk := fblock_support b.toF hgb.1 hlb hsb (hctl _ (by simp)) (hctl3 _ (by simp)) hkb
      (hgarb _ (by simp)) start
    cases b with
    | std b =>
      rw [dprog, support_cast, straightWires_append]
      exact List.append_subset.mpr ⟨hblk, ih' _ _ _⟩
    | defer u =>
      change ChallengeMigration.straightWires (blockProgP2 bank15 (.unit u) start) ⊆ support at hblk
      rw [blockProgP2, support_cast, straightWires_append] at hblk
      have hlast := hkb (some u.clear.guard) u.clear.ports
        (by simp [DBlock.toF, FBlock2.forget, Block2.code, UnitSite.code])
      rw [dprog, support_cast, straightWires_append]
      refine List.append_subset.mpr ⟨fun w hw => hblk (List.mem_append_left _ hw), ?_⟩
      rw [support_agrees]
      apply MeasuredClear.measureThen_within _ support _ _ _ _ (by rw [clearData_targets]; exact hlast.2)
      intro cursor rs
      rw [← support_agrees]
      exact ih' _ _ _
    | pay u =>
      have hu : UnitGeoP bank15 u := hgb.1
      change ChallengeMigration.straightWires (blockProgP2 bank15 (.unit u) start) ⊆ support at hblk
      rw [blockProgP2, support_cast, straightWires_append] at hblk
      have hlast := hkb (some u.clear.guard) u.clear.ports
        (by simp [DBlock.toF, FBlock2.forget, Block2.code, UnitSite.code])
      rw [dprog, support_cast, straightWires_append, straightWires_append]
      refine List.append_subset.mpr ⟨fun w hw => hblk (List.mem_append_left _ hw),
        List.append_subset.mpr ⟨?_, ih' _ _ _⟩⟩
      exact fusedFix_support u.clear hu.site.kind _ support hlast.2 (hlast.1 _ (Option.mem_def.mpr rfl))
        low8_new high_new bank_new _ _
    | defer1 f =>
      have hgf : FastGeometry1 f := hgb.1.1
      have hreg := FastSite1.regs_new f hgf (hgarb (FBlock2.fast1 f) (by simp [DBlock.toF]))
      change ChallengeMigration.straightWires (f.fusedProgram start) ⊆ support at hblk
      rw [FastSite1.fusedProgram, support_cast, straightWires_append, straightWires_append] at hblk
      have hlitA : ∀ p, WInstr.literal p ∈ f.site.arithmetic → ECDSAAdd.wires p ⊆ support.toFinset := by
        intro p hp w hw
        have hm : WInstr.literal p ∈ (DBlock.defer1 f).toF.forget.code :=
          show WInstr.literal p ∈ f.site.code from List.mem_append_left _ (List.mem_cons_of_mem _ hp)
        rcases hlb p hm w hw with e | e | e | e
        · obtain ⟨c, hc⟩ := hsb p hm (Or.inl (e ▸ hw)); cases hc
        · obtain ⟨c, hc⟩ := hsb p hm (Or.inr (Or.inl (e ▸ hw))); cases hc
        · obtain ⟨c, hc⟩ := hsb p hm (Or.inr (Or.inr (e ▸ hw))); cases hc
        · exact List.mem_toFinset.mpr e
      have hlookA : ∀ c ps, WInstr.lookup c ps ∈ f.site.arithmetic →
          (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support := fun c ps hm =>
        hkb c ps (show WInstr.lookup c ps ∈ f.site.code from List.mem_append_left _ (List.mem_cons_of_mem _ hm))
      rw [dprog, support_cast, straightWires_append, straightWires_append]
      refine List.append_subset.mpr ⟨List.append_subset.mpr
        ⟨fun w hw => hblk (List.mem_append_left _ (List.mem_append_left _ hw)),
         fun w hw => hblk (List.mem_append_left _ (List.mem_append_right _ hw))⟩, ?_⟩
      rw [support_agrees]
      apply MeasuredClear.measureThen_within _ support _ _ _ _
        (by rw [clearData_targets, FastSite1.garbPorts_targets f hgf]
            exact fun w hw => hreg w (List.mem_append_right _ hw))
      intro cursor grefs
      rw [MeasuredClear.static_cast, ← support_agrees, straightWires_append]
      refine List.append_subset.mpr ⟨compile_support _ _ _ _ support root_new bits_new bank_new
        (normalized_lit_support _ support hlitA) (normalized_look_support _ support hlookA) _, ?_⟩
      rw [support_agrees]
      apply MeasuredClear.measureThen_within _ support _ _ _ _
        (by rw [clearData_targets]; exact fun w hw => hreg w (List.mem_append_left _ hw))
      intro c2 rs
      rw [← support_agrees]
      exact ih' _ _ _

end
end ShorECDLP.Entrant.WideBank8.Fast16.Tight


namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem phaseFactor_debt7 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (hot : Fin 128 → Wire) (tree : UnaryActionTree) (root : Wire)
    (prepared : BasisState) (selected : Fin 128) (a : Nat)
    (hm : ∀ i, prepared (hot i) = decide (i = selected)) (hr : prepared root = true)
    (ha : 128 * tree.routeLabel prepared + selected.val = a) :
    phaseLookupFactor (logicalPorts data outcomes hot) read boolHistory tree root prepared =
      debtPhase read a data outcomes := by
  unfold phaseLookupFactor
  induction data generalizing outcomes with
  | nil =>
    simp only [logicalPorts, List.zip_nil_left, phasePorts, List.flatMap_nil]
    simp [recordTargets, xorPhase]
  | cons p ps ih =>
    cases outcomes with
    | nil =>
      simp only [logicalPorts, List.map_nil, List.zip_nil_right, phasePorts, List.flatMap_nil]
      simp [recordTargets, xorPhase, debtPhase]
    | cons m ms =>
      rw [logicalPorts_cons, recordTargets_append, xorPhase_append,
        phasePorts_block p m hot read _ root prepared selected hm, ih ms]
      simp only [debtPhase, hr, ha, Bool.true_and]

theorem fixupFactor7_debt {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (t : BasisState) (hhot : HotClean hot t) (a : Nat) (hroot : t root = true)
    (haddr : 128 * tree.routeLabel t + hotAddress low t = a) :
    fixupFactor data outcomes read low hot tree root t = debtPhase read a data outcomes := by
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
  apply phaseFactor_debt7 data outcomes read hot tree root prepared selected a
  · intro i
    simpa only [Fin.ext_iff] using hotPrepare_marker low hot hi hdlow t hhot i
  · rw [hframe root (by simp)]; exact hroot
  · rw [hroute]; exact haddr

end
end ShorECDLP.Entrant.MeasuredClear

/-! ### The repaying fixup on the narrow (seven-bit) bank -/

namespace ShorECDLP.Entrant.WEXFast.Defer
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open MeasuredClear (ClearPort debtPhase)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def PayFixSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ (next : ECDSAAdd.State) (a : Nat), Clean B.hp next.basis → tableAddressValue B.bits next.basis = a →
    next.basis site.guard = true →
    (∀ p ∈ site.ports, next.basis p.target = decide (read (p.ref a) = p.value)) →
    b.kraus (Bridge.signedKet next) =
      (c * debtPhase read a gd og) • Bridge.signedKet ⟨next.phase, clearRegister (portTargets site.ports) next.basis⟩

theorem payFix_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (gd : List (ClearPort n)) (og : List Bool) (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (PayFixSim B read site gd og) (fusedFixSource B read site gd og).run cs ∧
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
  · intro os hos b c hb next a hhp haddr0 hroot0 hsite
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
        debtPhase read a gd og * registerXPhase (portTargets site.ports) os next.basis := by
      rw [MeasuredClear.fixupFactor7_append _ _ _ _ hog]
      congr 1
      · apply MeasuredClear.fixupFactor7_debt gd og read low (clearHot site) _ site.guard B.hp
          hi hdlow hbank t hhot a
        · rw [hguard]; exact hroot0
        · rw [hsplit, haddr, haddr0]
      · have h := MeasuredClear.fixupFactor_recycled (clearData site.ports) os read low (clearHot site)
          (tableAddressTree B.high 0 1) site.guard B.hp hi hdlow hbank
          (by rw [clearData_targets]; exact ha) (by rw [clearData_targets]; exact hmem) next.basis
          ⟨hhp, by
            intro q hq
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            rw [hsplit, haddr0, hroot0, Bool.true_and]
            exact hsite p hp⟩
        simpa only [clearData_targets] using h
    have hsq := MeasuredClear.registerXPhase_square (portTargets site.ports) os next.basis
    change b.kraus (xResetRegisterKraus (portTargets site.ports) os (Bridge.signedKet next)) = _
    simp only [Bridge.signedKet, map_smul, hk, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac,
      smul_smul]
    congr 1
    linear_combination ((if next.phase then (-1 : ℂ) else 1) *
      registerXResetMagnitude (portTargets site.ports).length * c * debtPhase read a gd og) * hsq

end
end ShorECDLP.Entrant.WEXFast.Defer

/-! ### Narrow rows with a phase debt -/

namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open AndGadget WEXCredit
open MeasuredClear (ClearPort debtPhase)
open WideBank8 (GuardKept)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

/-- A block of a row with deferred fixups. `defer` and `defer1` measure their clear registers and add
their ports to the debt; `pay` measures its register and repays the debt with its own fixup. -/
inductive DBlock (n : Nat) where
  | std (b : FBlock2 n)
  | defer (u : UnitSite n)
  | defer1 (f : FastSite1 n)
  | pay (u : UnitSite n)
abbrev DCode (n : Nat) := List (DBlock n)

/-- The stage-1 block a deferred block replaces. -/
def DBlock.toF {n} : DBlock n → FBlock2 n
  | .std b => b
  | .defer u => .std (.unit u)
  | .defer1 f => .fast1 f
  | .pay u => .std (.unit u)

def dfor {n} (code : DCode n) : FCode2 n := code.map DBlock.toF

@[simp] theorem dfor_cons {n} (b : DBlock n) (code : DCode n) : dfor (b :: code) = b.toF :: dfor code := rfl
@[simp] theorem dfor_nil {n} : dfor (List.nil : DCode n) = List.nil := rfl

abbrev preRec {n} (u : UnitSite n) : Nat := codeRecords bank15.bits bank15.paths windowRoot (normalizeW u.pre)
abbrev selRec1 {n} (f : FastSite1 n) : Nat := codeRecords selBits1 selPaths1 windowRoot f.selCode
abbrev arithRec {n} (site : MaskedSite n) : Nat :=
  codeRecords bank15.bits bank15.paths windowRoot (normalizeW site.arithmetic)

def dblockRec {n} : DBlock n → Nat
  | .std b => gblockRec b
  | .defer u => preRec u + u.clear.ports.length
  | .defer1 f => selRec1 f + 0 + (f.garbPorts.length + (arithRec f.site + f.site.ports.length))
  | .pay u => preRec u + (u.clear.ports.length + Defer.fuseRec bank15 u.clear)

def drecs {n} : DCode n → Nat
  | [] => 0
  | b :: code => dblockRec b + drecs code

/-- The row program. `debt` is the list of deferred ports, `refs` their records. -/
def dprog {n} : (code : DCode n) → (debt : List (ClearPort n)) → (start : Nat) → List (Fin start) →
    Straight n start (start + drecs code)
  | [], _, _, _ => .done
  | .std b :: code, debt, start, refs => castFinish (by simp only [drecs, dblockRec]; omega)
      ((gblockProg b start).append
        (dprog code debt (start + gblockRec b) (refs.map (Fin.castLE (Nat.le_add_right _ _)))))
  | .defer u :: code, debt, start, refs => castFinish (by simp only [drecs, dblockRec, clearData, List.length_map]; omega)
      ((compile bank15.bits bank15.paths windowRoot (normalizeW u.pre) start).append
        (MeasuredClear.measureThen (R := drecs code)
          (fun cursor rs => dprog code (debt ++ clearData u.clear.ports) cursor rs)
          ((clearData u.clear.ports).map ClearPort.target) (start + preRec u)
          (refs.map (Fin.castLE (Nat.le_add_right _ _)))))
  | .defer1 f :: code, debt, start, refs => castFinish (by simp only [drecs, dblockRec, clearData, List.length_map]; omega)
      (((f.selProgram start).append (f.swapProgram (start + selRec1 f))).append
        (MeasuredClear.measureThen (R := arithRec f.site + (f.site.ports.length + drecs code))
          (fun cursor grefs => castFinish (by simp only [clearData, List.length_map]; omega)
            ((compile bank15.bits bank15.paths windowRoot (normalizeW f.site.arithmetic) cursor).append
              (MeasuredClear.measureThen (R := drecs code)
                (fun c2 srefs => dprog code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) c2 srefs)
                ((clearData f.site.ports).map ClearPort.target) (cursor + arithRec f.site)
                (grefs.map (Fin.castLE (Nat.le_add_right _ _))))))
          ((clearData f.garbPorts).map ClearPort.target) (start + selRec1 f + 0)
          (refs.map (Fin.castLE (by omega)))))
  | .pay u :: code, debt, start, refs => castFinish (by simp only [drecs, dblockRec]; omega)
      ((compile bank15.bits bank15.paths windowRoot (normalizeW u.pre) start).append
        ((Defer.fusedFix bank15 u.clear debt (start + preRec u) (refs.map (Fin.castLE (Nat.le_add_right _ _)))).append
          (dprog code List.nil (start + preRec u + u.clear.ports.length + Defer.fuseRec bank15 u.clear) List.nil)))

/-- The row source: the deferred outcomes `og` flow into the rest of the row. -/
def dsrc {n} (read : ConstantBit n → Bool) : DCode n → List (ClearPort n) → List Bool → AdaptiveCircuit
  | [], _, _ => .done
  | .std b :: code, debt, og => (gblockSrc read b).seq (dsrc read code debt og)
  | .defer u :: code, debt, og => (source read bank15.bits bank15.paths windowRoot (normalizeW u.pre)).seq
      (measureResetThen ((clearData u.clear.ports).map ClearPort.target)
        (fun o => dsrc read code (debt ++ clearData u.clear.ports) (og ++ o)))
  | .defer1 f :: code, debt, og =>
      ((source read selBits1 selPaths1 windowRoot f.selCode).seq (literalSource f.swapNet)).seq
        (measureResetThen ((clearData f.garbPorts).map ClearPort.target) (fun og1 =>
          (source read bank15.bits bank15.paths windowRoot (normalizeW f.site.arithmetic)).seq
            (measureResetThen ((clearData f.site.ports).map ClearPort.target) (fun os =>
              dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) ((og ++ og1) ++ os)))))
  | .pay u :: code, debt, og => (source read bank15.bits bank15.paths windowRoot (normalizeW u.pre)).seq
      ((Defer.fusedFixSource bank15 read u.clear debt og).seq (dsrc read code List.nil List.nil))

theorem dprog_run {n} (read : ConstantBit n → Bool) (code : DCode n) (debt : List (ClearPort n))
    (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((dprog code debt start refs).instantiate read history).run = (dsrc read code debt (refs.map history)).run := by
  induction code generalizing debt start with
  | nil => rfl
  | cons b code ih =>
    cases b with
    | std b =>
      rw [dprog, castFinish_instantiate,
        MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) history history rfl
          (dsrc read code debt (refs.map history)),
        AdaptiveCircuit.run_seq, gblockProg_run]
      · simp only [dsrc, AdaptiveCircuit.run_seq]
      · intro h' hh'
        rw [ih, List.map_map]
        congr 2
        rw [← hh']
        rfl
    | defer u =>
      rw [dprog, castFinish_instantiate,
        MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) history history rfl
          (measureResetThen ((clearData u.clear.ports).map ClearPort.target)
            (fun o => dsrc read code (debt ++ clearData u.clear.ports) (refs.map history ++ o))),
        AdaptiveCircuit.run_seq, compile_run]
      · simp only [dsrc, AdaptiveCircuit.run_seq]
      · intro h' hh'
        rw [MeasuredClear.measureThen_run _ (fun ol => dsrc read code (debt ++ clearData u.clear.ports) ol) read
          (fun cursor rs hist => ih _ cursor rs hist), List.map_map]
        congr 3
        funext o
        congr 2
        rw [← hh']
        rfl
    | defer1 f =>
      rw [dprog, castFinish_instantiate,
        MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) history history rfl
          (measureResetThen ((clearData f.garbPorts).map ClearPort.target) (fun og1 =>
            (source read bank15.bits bank15.paths windowRoot (normalizeW f.site.arithmetic)).seq
              (measureResetThen ((clearData f.site.ports).map ClearPort.target) (fun os =>
                dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports)
                  ((refs.map history ++ og1) ++ os))))),
        AdaptiveCircuit.run_seq, FastSite1.swapProgram, FastSite1.selProgram,
        append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
        compile_run]
      · simp only [dsrc, AdaptiveCircuit.run_seq]
      · intro h' hh'
        rw [MeasuredClear.measureThen_run _ (fun gl =>
            (source read bank15.bits bank15.paths windowRoot (normalizeW f.site.arithmetic)).seq
              (measureResetThen ((clearData f.site.ports).map ClearPort.target) (fun os =>
                dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) (gl ++ os)))) read,
          List.map_map]
        · congr 3
          funext og1
          congr 4
          funext os
          congr 3
          rw [← hh']
          rfl
        · intro cursor grefs hist
          rw [castFinish_instantiate,
            MeasuredClear.append_run_prefix _ _ read (Nat.le_refl cursor) hist hist rfl
              (measureResetThen ((clearData f.site.ports).map ClearPort.target) (fun os =>
                dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) (grefs.map hist ++ os))),
            AdaptiveCircuit.run_seq, compile_run, ← AdaptiveCircuit.run_seq]
          intro h2 hh2
          rw [MeasuredClear.measureThen_run _
            (fun sl => dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) sl) read
            (fun c2 rs hist2 => ih _ c2 rs hist2), List.map_map]
          congr 3
          funext os
          congr 2
          rw [← hh2]
          rfl
    | pay u =>
      rw [dprog, castFinish_instantiate,
        MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) history history rfl
          ((Defer.fusedFixSource bank15 read u.clear debt (refs.map history)).seq (dsrc read code List.nil List.nil)),
        AdaptiveCircuit.run_seq, compile_run]
      · simp only [dsrc, AdaptiveCircuit.run_seq]
      · intro h' hh'
        have e : (refs.map (Fin.castLE (Nat.le_add_right start (preRec u)))).map h' = refs.map history := by
          rw [List.map_map, ← hh']
          rfl
        rw [append_run_fixed _ _ _ _ (dsrc read code List.nil List.nil) (fun h => ih List.nil _ List.nil h),
          AdaptiveCircuit.run_seq, AdaptiveCircuit.run_seq, Defer.fusedFix_run, e]

/-! #### Simulation with a phase debt -/

/-- Geometry, plus a window-root guard on every deferring or repaying clear. -/
def DGuard {n} : DBlock n → Prop
  | .std _ => True
  | .defer u => u.clear.guard = windowRoot
  | .defer1 f => f.site.guard = windowRoot
  | .pay u => u.clear.guard = windowRoot

def DGeo {n} (b : DBlock n) : Prop := GBlockGeo b.toF ∧ DGuard b

/-- Every deferred phase is repaid by the end of the row. -/
def Paid {n} : DCode n → List (ClearPort n) → Prop
  | [], d => d = List.nil
  | .std _ :: c, d => Paid c d
  | .defer u :: c, d => Paid c (d ++ clearData u.clear.ports)
  | .defer1 f :: c, d => Paid c ((d ++ clearData f.garbPorts) ++ clearData f.site.ports)
  | .pay _ :: c, _ => Paid c List.nil

/-- A branch of a row suffix that still owes the phase of `debt`. -/
def DSim {n} (read : ConstantBit n → Bool) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a st, AddrValid windowBits windowRoot a st → FCodeClean read a (dfor code) st →
      Safe2 read a (fforget (dfor code)) st →
      b.kraus (Bridge.signedKet st) =
        (c * debtPhase read a debt og) •
          Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m st)

/-- A measured clear followed by the rest of the row, seen from the state before the measurement. -/
def MSim {n} (read : ConstantBit n → Bool) (data : List (ClearPort n)) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a (st : ECDSAAdd.State), (∀ p ∈ data, st.basis p.target = decide (read (p.ref a) = p.value)) →
      AddrValid windowBits windowRoot a ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩ →
      FCodeClean read a (dfor code) ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩ →
      Safe2 read a (fforget (dfor code)) ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩ →
      b.kraus (Bridge.signedKet st) =
        (c * debtPhase read a debt og) • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m
          ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩)

/-- Measuring a loaded register adds its ports to the debt: the measurement phase equals the new
debt factor, which the rest of the row repays. -/
theorem measure_dsim {n} (read : ConstantBit n → Bool) (data : List (ClearPort n))
    (hnd : (data.map ClearPort.target).Nodup) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (hog : og.length = debt.length) (next : List Bool → AdaptiveCircuit)
    (hn : ∀ o, o.length = data.length → ∃ cs : List ℂ,
      List.Forall₂ (DSim read code (debt ++ data) (og ++ o)) (next o).run cs ∧ (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (MSim read data code debt og)
      (measureResetThen (data.map ClearPort.target) next).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  apply MeasuredClear.measureResetThen_sim (data.map ClearPort.target) next
    (fun o => DSim read code (debt ++ data) (og ++ o))
  · intro o ho
    exact hn o (by simpa using ho)
  · intro o ho b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, hm, ?_⟩
    intro a st hw hs hc hsafe
    have hk := xResetRegisterKraus_ket (data.map ClearPort.target) o st.basis ho hnd
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho,
      MeasuredClear.registerXPhase_debt read a data o st.basis hw] at hk
    have h := hb a _ hs hc hsafe
    rw [MeasuredClear.debtPhase_append read a debt data og o hog] at h
    have hsq := MeasuredClear.debtPhase_square read a data o
    change b.kraus (xResetRegisterKraus (data.map ClearPort.target) o (Bridge.signedKet st)) = _
    have hstep : b.kraus (xResetRegisterKraus (data.map ClearPort.target) o (Bridge.signedKet st)) =
        (registerXResetMagnitude (data.map ClearPort.target).length * debtPhase read a data o) •
          b.kraus (Bridge.signedKet ⟨st.phase, clearRegister (data.map ClearPort.target) st.basis⟩) := by
      simp only [Bridge.signedKet, map_smul, hk, smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (data.map ClearPort.target).length * c *
      debtPhase read a debt og) * hsq

/-- What a unit's clear and the rest of the row do, seen from the state after the unit's prefix. -/
def ASim {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a (st : ECDSAAdd.State), SimulationValid bank15.bits bank15.paths windowRoot a st →
      (∀ p ∈ site.ports, st.basis p.target = decide (read (p.ref a) = p.value)) →
      AddrValid windowBits windowRoot a ⟨st.phase, clearRegister (portTargets site.ports) st.basis⟩ →
      FCodeClean read a (dfor code) ⟨st.phase, clearRegister (portTargets site.ports) st.basis⟩ →
      Safe2 read a (fforget (dfor code)) ⟨st.phase, clearRegister (portTargets site.ports) st.basis⟩ →
      b.kraus (Bridge.signedKet st) =
        (c * debtPhase read a debt og) • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m
          ⟨st.phase, clearRegister (portTargets site.ports) st.basis⟩)

theorem defer_asim {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hnd : (portTargets site.ports).Nodup)
    (code : DCode n) (debt : List (ClearPort n)) (og : List Bool) (hog : og.length = debt.length)
    (hn : ∀ o, o.length = (clearData site.ports).length → ∃ cs : List ℂ,
      List.Forall₂ (DSim read code (debt ++ clearData site.ports) (og ++ o))
        (dsrc read code (debt ++ clearData site.ports) (og ++ o)).run cs ∧ (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (ASim read site code debt og)
      (measureResetThen ((clearData site.ports).map ClearPort.target)
        (fun o => dsrc read code (debt ++ clearData site.ports) (og ++ o))).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cs, al, mass⟩ := measure_dsim read (clearData site.ports) (by rw [clearData_targets]; exact hnd)
    code debt og hog _ hn
  refine ⟨cs, al.imp ?_, mass⟩
  intro b c hb
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨m, hm, fun a st _ hw hs hc hsafe => ?_⟩
  have h := hb a st (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact hw p hp)
    (by rw [clearData_targets]; exact hs) (by rw [clearData_targets]; exact hc)
    (by rw [clearData_targets]; exact hsafe)
  rw [clearData_targets] at h
  exact h

theorem pay_asim {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeoP bank15 site)
    (hr : site.guard = windowRoot) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (hog : og.length = debt.length)
    (hn : ∃ cs : List ℂ, List.Forall₂ (DSim read code List.nil List.nil) (dsrc read code List.nil List.nil).run cs ∧
      (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (ASim read site code debt og)
      ((Defer.fusedFixSource bank15 read site debt og).seq (dsrc read code List.nil List.nil)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := Defer.payFix_sim read bank15 bank15_ok site hg debt og hog
  obtain ⟨c2, a2, m2⟩ := hn
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₂⟩ := h₂
    refine ⟨m, hm, ?_⟩
    intro a st hs hw haddr hc hsafe
    have h1 := h₁ st a (fun w hw => hs.1 w (bank15_ok.sub w hw)) hs.2.1 (by rw [hr]; exact hs.2.2) hw
    have h2 := h₂ a _ haddr hc hsafe
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h1, map_smul, h2, MeasuredClear.debtPhase_nil, smul_smul]
    congr 1
    ring
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

/-- A unit block: its prefix, then its clear with the rest of the row. -/
theorem unit_dsim {n} (read : ConstantBit n → Bool) (u : UnitSite n) (hg : UnitGeoP bank15 u)
    (hr : u.clear.guard = windowRoot) (D : DBlock n) (hD : D.toF = .std (.unit u)) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (k : AdaptiveCircuit)
    (hk : ∃ cs : List ℂ, List.Forall₂ (ASim read u.clear code debt og) k.run cs ∧
      (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (DSim read (D :: code) debt og)
      ((source read bank15.bits bank15.paths windowRoot (normalizeW u.pre)).seq k).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hp : ∀ i ∈ u.pre, PlacedPair bank15.bits bank15.paths windowRoot i := by
    intro i hi; exact hg.placed i (List.mem_append_left _ hi)
  obtain ⟨preCs, preAligned, preMass⟩ := lnormalized_simulation read bank15.bits bank15.paths
    bank15_ok.bitsLen u.pre (fun i hi => pair_of_placed_lit _ _ i (hp i hi))
  obtain ⟨cs, aligned, mass⟩ := hk
  have hlast := hg.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
  have hlen : literalRecords (Block2.unit u).code = literalRecords u.pre := by
    simp [Block2.code, UnitSite.code, literalRecords_append, literalRecords]
  refine ⟨coherentSeqCoefficients preCs cs, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq preAligned aligned
    intro b₁ c₁ b₂ c₂ h₁ h₂
    obtain ⟨m₁, hm₁, h₁⟩ := h₁
    obtain ⟨m₂, hm₂, h₂⟩ := h₂
    refine ⟨m₁ ++ m₂, ?_, ?_⟩
    · simp only [dfor_cons, hD, fforget_cons, FBlock2.forget, erase2_cons, literalRecords_append,
        List.length_append, hm₁, hm₂, hlen]
    · intro a st hs hc hsafe
      simp only [dfor_cons, hD, fforget_cons, FBlock2.forget] at hc hsafe ⊢
      have hcl : Clean bank15.paths st.basis := hc.1.1
      have hsv : SimulationValid bank15.bits bank15.paths windowRoot a st := ⟨hcl, hs.1, hs.2⟩
      have hn := strict_preserves read bank15.bits bank15.paths u.pre a hp st hsv m₁
      have hrun := unit_runP read bank15 u hg a st m₁ hsv
      set next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m₁ st with hnext
      have hclean : Clean (portTargets u.clear.ports)
          (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
        have h := hsafe.1 m₁
        rw [hrun] at h
        exact h
      have hload := loaded_of_clean_unload read u.clear.ports a u.clear.guard next.basis hlast.2.1 hclean
      have hroot : next.basis u.clear.guard = true := by rw [hr]; exact hn.2.2
      have hblock : ECDSAAdd.run (blockReference2 read a (.unit u)) m₁ st =
          ⟨next.phase, clearRegister (portTargets u.clear.ports) next.basis⟩ := by
        show ECDSAAdd.run ((specialize u.code a).instantiate read) m₁ st = _
        rw [hrun, clear_eq_unload read u.clear.ports a u.clear.guard next.basis hclean]
      have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a (.unit u)) :=
        (hm₁.trans hlen.symm).trans (specialize_counts read (Block2.unit u).code a).2.symm
      have haddr := fblock_addr read (.std (.unit u)) hg a st hs hc.1 m₁
      simp only [FBlock2.forget] at haddr
      rw [hblock] at haddr
      have hc2 := hc.2 m₁ hm
      have hs2 := hsafe.2 m₁ hm
      simp only [FBlock2.forget] at hc2
      rw [hblock] at hc2 hs2
      have h2 := h₂ a next hn (fun p hp => by rw [hload p hp, hroot, Bool.true_and]) haddr hc2 hs2
      change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
      rw [h₁ a st hs (strict_pathsClean read bank15.bits bank15.paths u.pre a hp st hsv), map_smul, h2,
        reference2_cons, run_append_records _ _ m₁ m₂ st hm, hblock]
      simp [smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, preMass, mass]
    norm_num

/-! #### The deferred second fast site -/

/-- The arithmetic and the site measurement, followed by the rest of the row, seen from the reference
state after the site's load. -/
def InnerD {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m₁ m₂ : List Bool, m₁.length = literalRecords site.arithmetic ∧
    m₂.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a (st : ECDSAAdd.State), SimulationValid bank15.bits bank15.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports) (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      FCodeClean read a (dfor code) (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st) →
      Safe2 read a (fforget (dfor code)) (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st) →
      b.kraus (Bridge.signedKet ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) =
        (c * debtPhase read a debt og) • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m₂
          (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st))

theorem inner_d {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeoP bank15 site)
    (hr : site.guard = windowRoot) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (hog : og.length = debt.length)
    (hn : ∀ o, o.length = (clearData site.ports).length → ∃ cs : List ℂ,
      List.Forall₂ (DSim read code (debt ++ clearData site.ports) (og ++ o))
        (dsrc read code (debt ++ clearData site.ports) (og ++ o)).run cs ∧ (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (InnerD read site code debt og)
      ((source read bank15.bits bank15.paths windowRoot (normalizeW site.arithmetic)).seq
        (measureResetThen ((clearData site.ports).map ClearPort.target)
          (fun os => dsrc read code (debt ++ clearData site.ports) (og ++ os)))).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hpre : ∀ i ∈ site.prefix, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have harith : ∀ i ∈ site.arithmetic, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
    hpre i (List.mem_cons_of_mem _ hi)
  have hcode : ∀ i ∈ site.code, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i hi)
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read bank15.bits bank15.paths bank15_ok.bitsLen site.arithmetic
    (fun i hi => pair_of_placed_lit _ _ i (harith i hi))
  obtain ⟨c2, a2, m2⟩ := measure_dsim read (clearData site.ports) (by rw [clearData_targets]; exact hlast.2.1)
    code debt og hog _ hn
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₁⟩ := h₁
    obtain ⟨m', hm', h₂⟩ := h₂
    refine ⟨m, m', hm, hm', ?_⟩
    intro a st hs hun hc hsafe
    have hload := hg.placed (.lookup (some site.guard) site.ports)
      (by simp [MaskedSite.code, MaskedSite.prefix])
    have hL := lookup_preserves_simulation read (some site.guard) site.ports bank15.bits bank15.paths
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
    have hn := strict_preserves read bank15.bits bank15.paths site.prefix a hpre st hs m
    have hrun := masked_runP read bank15 site hg a st m hs
    set L : ECDSAAdd.State :=
      ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩ with hLdef
    set next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st with hnext
    have hclean : Clean (portTargets site.ports)
        (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
      have h := hun m
      rw [hrun] at h
      exact h
    have hsite := loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
    have hgt : next.basis site.guard = true := by rw [hr]; exact hn.2.2
    have hfin : (⟨next.phase, clearRegister ((clearData site.ports).map ClearPort.target) next.basis⟩ :
        ECDSAAdd.State) = ECDSAAdd.run ((specialize site.code a).instantiate read) m st := by
      rw [clearData_targets, hrun, clear_eq_unload read site.ports a site.guard next.basis hclean]
    have hcv := strict_preserves read bank15.bits bank15.paths site.code a hcode st hs m
    have h2 := h₂ a next (by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        rw [hsite p hp, hgt, Bool.true_and])
      (by rw [hfin]; exact ⟨hcv.2.1, hcv.2.2⟩) (by rw [hfin]; exact hc) (by rw [hfin]; exact hsafe)
    have h1 := h₁ a L ⟨hL.2.1, hL.2.2⟩ (strict_pathsClean read bank15.bits bank15.paths site.arithmetic a harith L hL)
    rw [← e] at h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet L)) = _
    rw [h1, map_smul, h2, hfin, smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

/-- The garbage measurement, then `InnerD`: the garbage ports join the debt. -/
def TailD {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n)) (code : DCode n)
    (debt : List (ClearPort n)) (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m₁ m₂ : List Bool, m₁.length = literalRecords site.arithmetic ∧
    m₂.length = literalRecords (erase2 (fforget (dfor code))) ∧
    ∀ a (st u : ECDSAAdd.State), SimulationValid bank15.bits bank15.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports) (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      FCodeClean read a (dfor code) (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st) →
      Safe2 read a (fforget (dfor code)) (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st) →
      (∀ p ∈ gd, u.basis p.target = decide (read (p.ref a) = p.value)) → u.phase = st.phase →
      clearRegister (gd.map ClearPort.target) u.basis =
        tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis →
      b.kraus (Bridge.signedKet u) =
        (c * debtPhase read a debt og) • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget (dfor code))) m₂
          (ECDSAAdd.run ((specialize site.code a).instantiate read) m₁ st))

theorem tail_d {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hg : SiteGeoP bank15 site)
    (hr : site.guard = windowRoot) (gd : List (ClearPort n)) (hgn : (gd.map ClearPort.target).Nodup)
    (code : DCode n) (debt : List (ClearPort n)) (og : List Bool) (hog : og.length = debt.length)
    (hn : ∀ og1 os, og1.length = gd.length → os.length = (clearData site.ports).length → ∃ cs : List ℂ,
      List.Forall₂ (DSim read code ((debt ++ gd) ++ clearData site.ports) ((og ++ og1) ++ os))
        (dsrc read code ((debt ++ gd) ++ clearData site.ports) ((og ++ og1) ++ os)).run cs ∧
        (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (TailD read site gd code debt og)
      (measureResetThen (gd.map ClearPort.target) (fun og1 =>
        (source read bank15.bits bank15.paths windowRoot (normalizeW site.arithmetic)).seq
          (measureResetThen ((clearData site.ports).map ClearPort.target) (fun os =>
            dsrc read code ((debt ++ gd) ++ clearData site.ports) ((og ++ og1) ++ os))))).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  apply MeasuredClear.measureResetThen_sim (gd.map ClearPort.target) _
    (fun og1 => InnerD read site code (debt ++ gd) (og ++ og1))
  · intro og1 hog1
    exact inner_d read site hg hr code (debt ++ gd) (og ++ og1) (by simp [hog, hog1])
      (fun os hos => hn og1 os (by simpa using hog1) hos)
  · intro og1 hog1 b c hb
    obtain ⟨m₁, m₂, hm₁, hm₂, hb⟩ := hb
    refine ⟨m₁, m₂, hm₁, hm₂, ?_⟩
    intro a st u hs hun hc hsafe hu hph hclr
    have hk' := xResetRegisterKraus_ket (gd.map ClearPort.target) og1 u.basis hog1 hgn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hog1, hclr,
      MeasuredClear.registerXPhase_debt read a gd og1 u.basis hu] at hk'
    have h := hb a st hs hun hc hsafe
    rw [MeasuredClear.debtPhase_append read a debt gd og og1 hog] at h
    have hsq := MeasuredClear.debtPhase_square read a gd og1
    change b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og1 (Bridge.signedKet u)) = _
    have hstep : b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og1 (Bridge.signedKet u)) =
        (registerXResetMagnitude (gd.map ClearPort.target).length * debtPhase read a gd og1) •
          b.kraus (Bridge.signedKet ⟨st.phase,
            tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) := by
      simp only [Bridge.signedKet, hph, map_smul, hk', smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (gd.map ClearPort.target).length * c *
      debtPhase read a debt og) * hsq

/-- The second fast site with both of its measurements deferred to the row's last clear. -/
theorem defer1_dsim {n} (read : ConstantBit n → Bool) (f : FastSite1 n) (hg : FastGeometry1 f)
    (hr : f.site.guard = windowRoot) (code : DCode n) (debt : List (ClearPort n)) (og : List Bool)
    (hog : og.length = debt.length)
    (hn : ∀ og1 os, og1.length = (clearData f.garbPorts).length → os.length = (clearData f.site.ports).length →
      ∃ cs : List ℂ,
      List.Forall₂ (DSim read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) ((og ++ og1) ++ os))
        (dsrc read code ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) ((og ++ og1) ++ os)).run cs ∧
        (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ, List.Forall₂ (DSim read (.defer1 f :: code) debt og)
      (dsrc read (.defer1 f :: code) debt og).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := FastSite1.swap_simulation f read hg
  obtain ⟨c2, a2, m2⟩ := tail_d read f.site hg.site hr (clearData f.garbPorts)
    (by rw [clearData_targets, FastSite1.garbPorts_targets f hg]; exact FastSite1.garb_nodup f hg)
    code debt og hog hn
  have hlen : literalRecords (Block2.unit (siteUnit f.site)).code = literalRecords f.site.arithmetic := by
    simp [Block2.code, siteUnit_code, MaskedSite.code, MaskedSite.prefix, literalRecords, literalRecords_append]
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [dsrc, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m₁, m₂, hm₁, hm₂, h₂⟩ := h₂
    refine ⟨m₁ ++ m₂, ?_, ?_⟩
    · simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget, erase2_cons, literalRecords_append,
        List.length_append, hm₁, hm₂, hlen]
    · intro a st hs hc hsafe
      simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget] at hc hsafe ⊢
      have hsv : SimulationValid windowBits pathBank windowRoot a st := ⟨hc.1.1, hs.1, hs.2⟩
      have hgarb := FastSite1.load_garb f read hg a st hsv hc.1.2
      have heq := FastSite1.load_clear_eq f read hg a st hsv hc.1.2
      have hph := (FastSite1.load_state f read hg a st hsv hc.1.2).1
      dsimp only at hgarb heq hph
      have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a (.unit (siteUnit f.site))) :=
        (hm₁.trans hlen.symm).trans (specialize_counts read (Block2.unit (siteUnit f.site)).code a).2.symm
      have hc2 := hc.2 m₁ hm
      have hs2 := hsafe.2 m₁ hm
      change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
      rw [h₁ a st hsv hc.1.2, map_smul, h₂ a st _ hsv hsafe.1 hc2 hs2
        (by
          intro q hq
          rw [hgarb q hq, hr, hs.2, Bool.true_and])
        hph (by rw [clearData_targets, FastSite1.garbPorts_targets f hg]; exact heq),
        reference2_cons, run_append_records _ _ m₁ m₂ st hm]
      simp [smul_smul, mul_assoc, blockReference2, Block2.code, siteUnit_code]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

/-! #### The whole row -/

theorem dsrc_sim {n} (read : ConstantBit n → Bool) (code : DCode n) (hg : ∀ b ∈ code, DGeo b)
    (debt : List (ClearPort n)) (og : List Bool) (hog : og.length = debt.length) (hp : Paid code debt) :
    ∃ cs : List ℂ, List.Forall₂ (DSim read code debt og) (dsrc read code debt og).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code generalizing debt og with
  | nil =>
    have hd : debt = List.nil := hp
    subst hd
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    exact ⟨List.nil, rfl, fun a st _ _ _ => by
      simp [reference2, erase2, fforget, dfor, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]⟩
  | cons b code ih =>
    have hgb := hg b (by simp)
    have hgc : ∀ d ∈ code, DGeo d := fun d hd => hg d (by simp [hd])
    cases b with
    | std b =>
      obtain ⟨cs₁, h₁, mass₁⟩ := gblock_sim read b hgb.1
      obtain ⟨cs₂, h₂, mass₂⟩ := ih hgc debt og hog hp
      refine ⟨coherentSeqCoefficients cs₁ cs₂, ?_, ?_⟩
      · rw [dsrc, AdaptiveCircuit.run_seq]
        apply simulationAligned_seq h₁ h₂
        intro b₁ c₁ b₂ c₂ hb₁ hb₂
        obtain ⟨m₁, len₁, run₁⟩ := hb₁
        obtain ⟨m₂, len₂, run₂⟩ := hb₂
        refine ⟨m₁ ++ m₂, ?_, ?_⟩
        · simp [dfor_cons, DBlock.toF, fforget_cons, erase2, List.length_append, len₁, len₂]
        · intro a st hs hc hsafe
          simp only [dfor_cons, DBlock.toF, fforget_cons] at hc hsafe ⊢
          have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a b.forget) :=
            len₁.trans (specialize_counts read b.forget.code a).2.symm
          have hn := fblock_addr read b (gblock_geo b hgb.1) a st hs hc.1 m₁
          change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
          rw [run₁ a st hs hc.1 hsafe.1, map_smul,
            run₂ a (ECDSAAdd.run (blockReference2 read a b.forget) m₁ st) hn (hc.2 m₁ hm) (hsafe.2 m₁ hm),
            reference2_cons, run_append_records _ _ m₁ m₂ st hm]
          simp [smul_smul, mul_assoc]
      · rw [simulationCoefficients_mass, mass₁, mass₂]
        norm_num
    | defer u =>
      obtain ⟨hgF, hr⟩ := hgb
      have hu : UnitGeoP bank15 u := hgF
      have hlast := hu.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
      exact unit_dsim read u hu hr (.defer u) rfl code debt og _
        (defer_asim read u.clear hlast.2.1 code debt og hog
          (fun o ho => ih hgc _ _ (by simp [hog, ho]) hp))
    | defer1 f =>
      obtain ⟨hgF, hr⟩ := hgb
      exact defer1_dsim read f hgF.1 hr code debt og hog
        (fun og1 os h1 h2 => ih hgc _ _ (by simp [hog, h1, h2]) hp)
    | pay u =>
      obtain ⟨hgF, hr⟩ := hgb
      have hu : UnitGeoP bank15 u := hgF
      exact unit_dsim read u hu hr (.pay u) rfl code debt og _
        (pay_asim read u.clear hu.site hr code debt og hog (ih hgc List.nil List.nil rfl hp))

theorem dprog_coherent {n} (read : ConstantBit n → Bool) (code : DCode n) (hg : ∀ b ∈ code, DGeo b)
    (hp : Paid code List.nil) (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue windowBits s) (fforget (dfor code)) ⟨false,s⟩)
    (hclean : ∀ s, Valid s → FCodeClean read (tableAddressValue windowBits s) (dfor code) ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue windowBits s) (fforget (dfor code))) m ⟨false,s⟩ =
        ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((dprog code List.nil start List.nil).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := dsrc_sim read code hg List.nil List.nil rfl hp
  refine ⟨cs, ?_, mass⟩
  rw [dprog_run, List.map_nil]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨rfl, hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [MeasuredClear.debtPhase_nil, mul_one, Bridge.signedKet_false, hrun s hs.2 m, Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.WEXFast

/-! #### Resources of the deferred row -/

namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open AndGadget WEXCredit
open MeasuredClear (ClearPort debtPhase)
open WideBank8 (GuardKept)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

def dblockTP {n} : DBlock n → Nat
  | .std b => gblockTP b
  | .defer u => literalToffolis (normalizeW u.pre) + traversals u.pre * (2 ^ bank15.bits.length - 1)
  | .defer1 f => 16383 + ECDSAAdd.toffoliCount f.swapNet +
      (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 32767)
  | .pay u => literalToffolis (normalizeW u.pre) + traversals u.pre * (2 ^ bank15.bits.length - 1) +
      ((tableAddressTree bank15.high 0 1).internalNodes + 120)

def dcodeTP {n} : DCode n → Nat
  | [] => 0
  | b :: code => dblockTP b + dcodeTP code

/-- The Toffoli units each deferred narrow fixup saves. -/
def dsave {n} : DCode n → Nat
  | [] => 0
  | .std _ :: c => dsave c
  | .defer _ :: c => 375 + dsave c
  | .defer1 _ :: c => 375 + dsave c
  | .pay _ :: c => dsave c

/-- The records each deferred fixup saves. -/
def drsave {n} : DCode n → Nat
  | [] => 0
  | .std _ :: c => drsave c
  | .defer _ :: c => 382 + drsave c
  | .defer1 _ :: c => 382 + drsave c
  | .pay _ :: c => drsave c

@[simp] theorem paid_std {n} {α : Type} (l : List α) (g : α → FBlock2 n) (rest : DCode n)
    (d : List (ClearPort n)) : Paid (l.map (fun x => DBlock.std (g x)) ++ rest) d = Paid rest d := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [Paid] using ih

@[simp] theorem dsave_std {n} {α : Type} (l : List α) (g : α → FBlock2 n) (rest : DCode n) :
    dsave (l.map (fun x => DBlock.std (g x)) ++ rest) = dsave rest := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [dsave] using ih

@[simp] theorem drsave_std {n} {α : Type} (l : List α) (g : α → FBlock2 n) (rest : DCode n) :
    drsave (l.map (fun x => DBlock.std (g x)) ++ rest) = drsave rest := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [drsave] using ih

theorem guard_std {n} {α : Type} (l : List α) (g : α → FBlock2 n) :
    ∀ b ∈ l.map (fun x => DBlock.std (g x)), DGuard b := by
  intro b hb
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
  trivial

theorem dprog_tCount {n} (read : ConstantBit n → Bool) (code : DCode n) (hg : ∀ b ∈ code, DGeo b)
    (debt : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((dprog code debt start refs).instantiate read history).tCount = 7 * dcodeTP code := by
  induction code generalizing debt start with
  | nil => simp [dprog, drecs, dcodeTP, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons b code ih =>
    have hgb := hg b (by simp)
    have hgc : ∀ d ∈ code, DGeo d := fun d hd => hg d (by simp [hd])
    cases b with
    | std b =>
      rw [dprog, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h => ih hgc _ _ _ h),
        gblock_tCount read b hgb.1]
      simp only [dcodeTP, dblockTP]; ring
    | defer u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      rw [dprog, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h =>
          MeasuredClear.measureThen_tCount _ read (fun cursor rs hist => ih hgc _ cursor rs hist) _ _ _ h),
        compile_tCount read _ _ _ _ hl.1 start history, traversals_normalize]
      simp only [dcodeTP, dblockTP]; ring
    | defer1 f =>
      rw [dprog, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h =>
          MeasuredClear.measureThen_tCount _ read (fun cursor grefs hist => by
            rw [castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h2 =>
                MeasuredClear.measureThen_tCount _ read (fun c2 rs hist2 => ih hgc _ c2 rs hist2) _ _ _ h2),
              compile_tCount read bank15.bits bank15.paths windowRoot _ (FastSite1.arith_layouts f hgb.1.1) _ hist])
            _ _ _ h),
        FastSite1.swapProgram, FastSite1.selProgram,
        append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
        compile_tCount read selBits1 selPaths1 windowRoot _ (FastSite1.sel_layouts f hgb.1.1), traversals_normalize]
      simp only [dcodeTP, dblockTP, FastSite1.selCode, literalToffolis, traversals, selBits1, bank15, windowBits,
        List.length_range', List.length_append, List.length_cons, List.length_nil]
      norm_num
      try ring
    | pay u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      rw [dprog, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h => by
          rw [append_tCount_fixed _ _ _ _ _ (fun h' => ih hgc _ _ _ h'),
            Defer.fusedFix_tCount read bank15 u.clear _ hl.2 _ _ h]),
        compile_tCount read _ _ _ _ hl.1 start history, traversals_normalize]
      simp only [dcodeTP, dblockTP]; ring

theorem dcodeTP_relation {n} (code : DCode n) (hg : ∀ b ∈ code, DGeo b) :
    dcodeTP code + dsave code = gcodeTP (dfor code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    cases b with
    | std b => simp only [dcodeTP, dsave, dblockTP, dfor_cons, DBlock.toF, gcodeTP]; omega
    | defer u =>
      simp only [dcodeTP, dsave, dblockTP, dfor_cons, DBlock.toF, gcodeTP, gblockTP, blockTP2, bank_tree_nodes]
      omega
    | defer1 f =>
      simp only [dcodeTP, dsave, dblockTP, dfor_cons, DBlock.toF, gcodeTP, gblockTP, FastSite1.fusedTP]
      omega
    | pay u => simp only [dcodeTP, dsave, dblockTP, dfor_cons, DBlock.toF, gcodeTP, gblockTP, blockTP2]; omega

theorem drecs_relation {n} (code : DCode n) (hg : ∀ b ∈ code, DGeo b) :
    drecs code + drsave code = grecs (dfor code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hgb := hg b (by simp)
    cases b with
    | std b => simp only [drecs, drsave, dblockRec, dfor_cons, DBlock.toF, grecs]; omega
    | defer u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      have hcr := (MeasuredClear.recordUnary_counts _ _ _ hl.2 0).1
      rw [bank_tree_nodes] at hcr
      simp only [drecs, drsave, dblockRec, dfor_cons, DBlock.toF, grecs, gblockRec, blockRecP2, hcr, preRec]
      omega
    | defer1 f =>
      simp only [drecs, drsave, dblockRec, dfor_cons, DBlock.toF, grecs, gblockRec, FastSite1.fusedRecords,
        Defer.tailRec, Defer.fuseRec, selRec1, arithRec]
      have hcr := (MeasuredClear.recordUnary_counts _ _ _ (FastSite1.site_layout_bank f hgb.1.1) 0).1
      rw [bank_tree_nodes] at hcr
      have hcr' : MeasuredClear.recordMeasurements
          (MeasuredClear.recordUnaryOps (tableAddressTree bank15.high 0 1) f.site.guard bank15.hp) = 255 := hcr
      rw [hcr']
      omega
    | pay u =>
      simp only [drecs, drsave, dblockRec, dfor_cons, DBlock.toF, grecs, gblockRec, blockRecP2, Defer.fuseRec, preRec]
      omega

theorem gblock_slots {n} (b : FBlock2 n) (hg : GBlockGeo b) (start : Nat) :
    (gblockProg b start).gateSlots ≤ blockSP2 bank15 b.forget + fblockSlack b := by
  cases b with
  | std b =>
    rw [show gblockProg (.std b) start = blockProgH bank15 b start from rfl]
    exact blockH_slots bank15 b (geo_lay2 bank15 bank15_ok b hg) start
  | fast f => exact f.fused_slots hg.1 start
  | fast1 f => exact f.fused_slots hg.1 start

/-- The repaying fixup's slot term grows with the debt; each deferred clear saved at least as much. -/
theorem dprog_slots {n} (code : DCode n) (hg : ∀ b ∈ code, DGeo b) (debt : List (ClearPort n))
    (start : Nat) (refs : List (Fin start)) :
    (dprog code debt start refs).gateSlots ≤
      codeSP2 bank15 (fforget (dfor code)) + fslack (dfor code) + 131072 * debt.length := by
  induction code generalizing debt start with
  | nil => simp [dprog, drecs, Straight.gateSlots, codeSP2]
  | cons b code ih =>
    have hgb := hg b (by simp)
    have hgc : ∀ d ∈ code, DGeo d := fun d hd => hg d (by simp [hd])
    cases b with
    | std b =>
      have hb := gblock_slots b hgb.1 start
      have hr := ih hgc debt (start + gblockRec b) (refs.map (Fin.castLE (Nat.le_add_right _ _)))
      rw [dprog, castFinish_gateSlots, Straight.gateSlots_append]
      simp only [dfor_cons, DBlock.toF, fforget_cons, codeSP2, fslack]
      omega
    | defer u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      have hm := WideBank8.Fast16.measureThen_slots_le (R := drecs code)
        (fun cursor rs => dprog code (debt ++ clearData u.clear.ports) cursor rs) _
        (fun cursor rs => ih hgc (debt ++ clearData u.clear.ports) cursor rs)
        ((clearData u.clear.ports).map ClearPort.target) (start + preRec u)
        (refs.map (Fin.castLE (Nat.le_add_right _ _)))
      rw [dprog, castFinish_gateSlots, Straight.gateSlots_append, compile_slots _ _ _ _ hl.1 start]
      simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget, codeSP2, fslack, fblockSlack, blockSP2,
        bank_tree_leaves, bank_tree_nodes, clearData, List.length_append, List.length_map] at hm ⊢
      omega
    | defer1 f =>
      have hgf := hgb.1.1
      rw [dprog, castFinish_gateSlots]
      simp only [Straight.gateSlots_append]
      refine le_trans (Nat.add_le_add_left (WideBank8.Fast16.measureThen_slots_le _
        (codeSlots bank15.bits (normalizeW f.site.arithmetic) + (codeSP2 bank15 (fforget (dfor code)) +
          fslack (dfor code) + 131072 * ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports).length))
        (fun cursor grefs => ?_) _ _ _) _) ?_
      · rw [castFinish_gateSlots, Straight.gateSlots_append,
          compile_slots bank15.bits bank15.paths windowRoot _ (FastSite1.arith_layouts f hgf)]
        exact Nat.add_le_add_left (WideBank8.Fast16.measureThen_slots_le _ _
          (fun c2 rs => ih hgc ((debt ++ clearData f.garbPorts) ++ clearData f.site.ports) c2 rs) _ _ _) _
      rw [FastSite1.swapProgram, literalFixed_slots, FastSite1.selProgram,
        compile_slots _ _ _ _ (FastSite1.sel_layouts f hgf), FastSite1.sel_slots f hgf]
      have hsw := literal_slot_bound (n := n) f.swapNet
      have hd : (clearData f.garbPorts).length = f.garb.length := by
        rw [clearData, List.length_map, FastSite1.garbPorts_length f hgf]
      have hds : (clearData f.site.ports).length = f.site.ports.length := by
        rw [clearData, List.length_map]
      have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
          (32768 * f.site.ports.length + 327670) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
        rw [prefix_split, normalize_append, old_slots_append, FastSite.lookup_slots]
      simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget, codeSP2, fslack, fblockSlack, blockSP2, siteUnit,
        FastSite1.fastSlack, show bank15.bits = windowBits from rfl, hpre, bank_tree_leaves, bank_tree_nodes,
        List.length_append, hd, hds]
      omega
    | pay u =>
      have hl := geo_lay2 bank15 bank15_ok (.unit u) hgb.1
      have hr := ih hgc List.nil (start + preRec u + u.clear.ports.length + Defer.fuseRec bank15 u.clear) List.nil
      rw [dprog, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append,
        compile_slots _ _ _ _ hl.1 start, Defer.fusedFix_slots bank15 u.clear debt hl.2]
      simp only [dfor_cons, DBlock.toF, fforget_cons, FBlock2.forget, codeSP2, fslack, fblockSlack, blockSP2,
        bank_tree_leaves, bank_tree_nodes, List.length_nil, Nat.mul_zero, Nat.add_zero] at hr ⊢
      have hmin := Nat.min_le_left (debt.length + u.clear.ports.length)
        ((refs.map (Fin.castLE (Nat.le_add_right start (preRec u)))).length + u.clear.ports.length)
      generalize min (debt.length + u.clear.ports.length)
        ((refs.map (Fin.castLE (Nat.le_add_right start (preRec u)))).length + u.clear.ports.length) = k at hmin ⊢
      have : 512 * k * 256 ≤ 512 * (debt.length + u.clear.ports.length) * 256 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmin)
      omega

theorem payFix_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (gd : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) :
    (Defer.fusedFix B site gd start refs).WellFormed := by
  obtain ⟨hl, hi, hdlow, hbank, hs, hshot, -, -, -⟩ := Defer.site_clear_facts B hB site hg
  rw [Defer.fusedFix, castFinish_wellFormed]
  apply MeasuredClear.measureThen_wellFormed
  intro c rs
  rw [castFinish_wellFormed]
  exact MeasuredClear.fixupProgram_wellFormed _ rs low (clearHot site) _ site.guard (scratch site) B.hp hl
    hi hdlow hs hshot

theorem dprog_wellFormed {n} (code : DCode n) (hg : ∀ b ∈ code, DGeo b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 (fforget (dfor code)) → GatePhysical p)
    (debt : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) :
    (dprog code debt start refs).WellFormed := by
  induction code generalizing debt start with
  | nil => trivial
  | cons b code ih =>
    have hgb := hg b (by simp)
    have hgc : ∀ d ∈ code, DGeo d := fun d hd => hg d (by simp [hd])
    have hpb : ∀ p, WInstr.literal p ∈ b.toF.forget.code → GatePhysical p :=
      fun p hm => hp p (by simp [erase2_cons, hm])
    have hpc : ∀ p, WInstr.literal p ∈ erase2 (fforget (dfor code)) → GatePhysical p :=
      fun p hm => hp p (by simp [erase2_cons, hm])
    have hunit (u : UnitSite n) (hu : UnitGeoP bank15 u)
        (hpu : ∀ p, WInstr.literal p ∈ u.code → GatePhysical p) :
        (compile bank15.bits bank15.paths windowRoot (normalizeW u.pre) start).WellFormed := by
      have hpref : ∀ i ∈ u.pre, LPlaced bank15.bits bank15.paths windowRoot i := fun i hi =>
        pair_of_placed_lit _ _ i (hu.placed i (List.mem_append_left _ hi))
      exact compile_wellFormedL _ _ _ _ bank15_ok.bitsLen (lplaced_normalize _ _ _ _ hpref)
        (normalized_literals_valid u.pre (fun p hm => hpu p (List.mem_append_left _ hm))) start
    cases b with
    | std b =>
      rw [dprog, castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (gblock_wellFormed b hgb.1 hpb start) (ih hgc hpc _ _ _)
    | defer u =>
      rw [dprog, castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (hunit u hgb.1 hpb)
        (MeasuredClear.measureThen_wellFormed _ (fun cursor rs => ih hgc hpc _ _ _) _ _ _)
    | defer1 f =>
      have hgf := hgb.1.1
      have harith : ∀ i ∈ f.site.arithmetic, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
        placed_implies_pair _ _ _ _ (hgf.site.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))
      have hlit : ∀ p, WInstr.literal p ∈ f.site.arithmetic → GatePhysical p := fun p hm =>
        hpb p (show WInstr.literal p ∈ f.site.code from List.mem_append_left _ (List.mem_cons_of_mem _ hm))
      rw [dprog, castFinish_wellFormed]
      refine straight_append_wellFormed _ _ (straight_append_wellFormed _ _ ?_ ?_) ?_
      · exact pair_compile_wellFormed _ _ _ _ (by decide)
          (fun i hi => by
            simp only [FastSite1.selCode, List.mem_singleton] at hi
            subst hi
            exact placed_implies_pair _ _ _ _ (FastSite1.sel_placed f hgf))
          (fun p hp => by simp [FastSite1.selCode] at hp) start
      · exact literalFixed_wellFormed _ _ _ (f.swapNet_valid hgf) _
      · apply MeasuredClear.measureThen_wellFormed
        intro cursor grefs
        rw [castFinish_wellFormed]
        exact straight_append_wellFormed _ _
          (pair_compile_wellFormed _ _ _ _ bank15_ok.bitsLen (pair_placed_normalize _ _ _ _ harith)
            (normalized_literals_valid f.site.arithmetic hlit) _)
          (MeasuredClear.measureThen_wellFormed _ (fun c2 rs => ih hgc hpc _ _ _) _ _ _)
    | pay u =>
      have hu : UnitGeoP bank15 u := hgb.1
      rw [dprog, castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (hunit u hu hpb)
        (straight_append_wellFormed _ _ (payFix_wellFormed bank15 bank15_ok u.clear hu.site _ _ _)
          (ih hgc hpc _ _ _))

theorem dprog_residue {n} (code : DCode n) (debt : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) :
    residue (dprog code debt start refs) = 0 := by
  induction code generalizing debt start with
  | nil => simp [dprog, drecs]
  | cons b code ih =>
    cases b with
    | std b =>
      have hb : residue (gblockProg b start) = 0 := by
        cases b with
        | std b => exact blockH_residue bank15 b start
        | fast f => exact f.fused_residue start
        | fast1 f => exact f.fused_residue start
      rw [dprog, residue_cast, residue_append, hb, ih]
    | defer u =>
      rw [dprog, residue_cast, residue_append, compile_residue,
        MeasuredClear.measureThen_residue _ (fun cursor rs => ih _ _ _)]
    | defer1 f =>
      rw [dprog, residue_cast]
      simp only [residue_append]
      rw [FastSite1.selProgram, compile_residue, FastSite1.swapProgram, literalFixed, residue_naive_cast,
        literal_residue, MeasuredClear.measureThen_residue]
      intro cursor grefs
      rw [residue_cast, residue_append, compile_residue,
        MeasuredClear.measureThen_residue _ (fun c2 rs => ih _ _ _)]
    | pay u =>
      have hf : residue (Defer.fusedFix bank15 u.clear debt (start + preRec u)
          (refs.map (Fin.castLE (Nat.le_add_right _ _)))) = 0 := by
        rw [Defer.fusedFix, residue_cast]
        apply MeasuredClear.measureThen_residue
        intro c rs
        rw [residue_cast]
        exact MeasuredClear.fixupProgram_residue _ _ _ _ _ _ _ _
      rw [dprog, residue_cast, residue_append, residue_append, compile_residue, hf, ih]

end
end ShorECDLP.Entrant.WEXFast

/-! #### Support of the deferred narrow row -/

namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.ShorPort ECDSAAdd.Entrant
open MeasuredClear (ClearPort)
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

theorem payFix_support {n} (site : MaskedSite n) (hk : SiteKind site) (gd : List (ClearPort n))
    (S : List Wire) (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low i ∈ S)
    (hhigh : bank15.high ⊆ S) (hpaths : bank15.paths ⊆ S) (start : Nat) (refs : List (Fin start)) :
    ChallengeMigration.straightWires (Defer.fusedFix bank15 site gd start refs) ⊆ S := by
  obtain ⟨-,-,-,hmem,hsm,-,-⟩ := kind_facts site hk
  rw [support_agrees, Defer.fusedFix, MeasuredClear.static_cast]
  apply MeasuredClear.measureThen_within _ S _ _ _ _ (by rw [clearData_targets]; exact hS)
  intro c rs
  rw [MeasuredClear.static_cast]
  apply MeasuredClear.fixupProgram_within _ _ _ _ _ _ _ _ S hgS (hS hsm) hlow
    (fun i => hS (hmem i)) _ (fun w hw => hpaths (bank15_ok.sub w hw))
  intro w hw
  apply hhigh
  rw [← bank15_ok.index]
  exact List.mem_dedup.mpr hw

theorem dprog_hsupport (code : DCode 32768) (hg : ∀ b ∈ code, DGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget (dfor code)) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ newSourceH)
    (hstrict : ∀ b ∈ dfor code, ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ dfor code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ dfor code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget (dfor code)) →
      (∀ q ∈ c, q ∈ newSourceH) ∧ portTargets ps ⊆ newSourceH)
    (hgarb : ∀ b ∈ dfor code, FNoHost b)
    (debt : List (ClearPort 32768)) (start : Nat) (refs : List (Fin start)) :
    ChallengeMigration.straightWires (dprog code debt start refs) ⊆ newSourceH := by
  induction code generalizing debt start with
  | nil => simp [dprog, drecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    have hgb := hg b (by simp)
    have ih' := ih (fun d hd => hg d (by simp [hd])) (fun p hm => hlit p (by simp [erase2_cons, hm]))
      (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd]))
      (fun d hd => hctl3 d (by simp [hd])) (fun c ps hm => hlook c ps (by simp [erase2_cons, hm]))
      (fun d hd => hgarb d (by simp [hd]))
    have hlb : ∀ p, WInstr.literal p ∈ b.toF.forget.code → ∀ w ∈ ECDSAAdd.wires p,
        w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ newSourceH :=
      fun p hm => hlit p (by simp [erase2_cons, hm])
    have hkb : ∀ c ps, WInstr.lookup c ps ∈ b.toF.forget.code →
        (∀ q ∈ c, q ∈ newSourceH) ∧ portTargets ps ⊆ newSourceH :=
      fun c ps hm => hlook c ps (by simp [erase2_cons, hm])
    have hsb := hstrict b.toF (by simp)
    have hblk := gblock_support b.toF hgb.1 hlb hsb (hctl _ (by simp)) (hctl3 _ (by simp)) hkb
      (hgarb _ (by simp)) start
    cases b with
    | std b =>
      rw [dprog, support_cast, straightWires_append]
      exact List.append_subset.mpr ⟨hblk, ih' _ _ _⟩
    | defer u =>
      change ChallengeMigration.straightWires (blockProgP2 bank15 (.unit u) start) ⊆ newSourceH at hblk
      rw [blockProgP2, support_cast, straightWires_append] at hblk
      have hlast := hkb (some u.clear.guard) u.clear.ports
        (by simp [DBlock.toF, FBlock2.forget, Block2.code, UnitSite.code])
      rw [dprog, support_cast, straightWires_append]
      refine List.append_subset.mpr ⟨fun w hw => hblk (List.mem_append_left _ hw), ?_⟩
      rw [support_agrees]
      apply MeasuredClear.measureThen_within _ newSourceH _ _ _ _ (by rw [clearData_targets]; exact hlast.2)
      intro cursor rs
      rw [← support_agrees]
      exact ih' _ _ _
    | pay u =>
      have hu : UnitGeoP bank15 u := hgb.1
      change ChallengeMigration.straightWires (blockProgP2 bank15 (.unit u) start) ⊆ newSourceH at hblk
      rw [blockProgP2, support_cast, straightWires_append] at hblk
      have hlast := hkb (some u.clear.guard) u.clear.ports
        (by simp [DBlock.toF, FBlock2.forget, Block2.code, UnitSite.code])
      rw [dprog, support_cast, straightWires_append, straightWires_append]
      refine List.append_subset.mpr ⟨fun w hw => hblk (List.mem_append_left _ hw),
        List.append_subset.mpr ⟨?_, ih' _ _ _⟩⟩
      exact payFix_support u.clear hu.site.kind _ newSourceH hlast.2 (hlast.1 _ (Option.mem_def.mpr rfl))
        low_new high_new bank_new _ _
    | defer1 f =>
      have hgf : FastGeometry1 f := hgb.1.1
      have hreg := FastSite1.regs_new f hgf (hgarb (FBlock2.fast1 f) (by simp [DBlock.toF]))
      change ChallengeMigration.straightWires (f.fusedProgram start) ⊆ newSourceH at hblk
      rw [FastSite1.fusedProgram, support_cast, straightWires_append, straightWires_append] at hblk
      have hlitA : ∀ p, WInstr.literal p ∈ f.site.arithmetic → ECDSAAdd.wires p ⊆ newSourceH.toFinset := by
        intro p hp w hw
        have hm : WInstr.literal p ∈ (DBlock.defer1 f).toF.forget.code :=
          show WInstr.literal p ∈ f.site.code from List.mem_append_left _ (List.mem_cons_of_mem _ hp)
        rcases hlb p hm w hw with e | e | e | e
        · obtain ⟨c, hc⟩ := hsb p hm (Or.inl (e ▸ hw)); cases hc
        · obtain ⟨c, hc⟩ := hsb p hm (Or.inr (Or.inl (e ▸ hw))); cases hc
        · obtain ⟨c, hc⟩ := hsb p hm (Or.inr (Or.inr (e ▸ hw))); cases hc
        · exact List.mem_toFinset.mpr e
      have hlookA : ∀ c ps, WInstr.lookup c ps ∈ f.site.arithmetic →
          (∀ q ∈ c, q ∈ newSourceH) ∧ portTargets ps ⊆ newSourceH := fun c ps hm =>
        hkb c ps (show WInstr.lookup c ps ∈ f.site.code from List.mem_append_left _ (List.mem_cons_of_mem _ hm))
      rw [dprog, support_cast, straightWires_append, straightWires_append]
      refine List.append_subset.mpr ⟨List.append_subset.mpr
        ⟨fun w hw => hblk (List.mem_append_left _ (List.mem_append_left _ hw)),
         fun w hw => hblk (List.mem_append_left _ (List.mem_append_right _ hw))⟩, ?_⟩
      rw [support_agrees]
      apply MeasuredClear.measureThen_within _ newSourceH _ _ _ _
        (by rw [clearData_targets, FastSite1.garbPorts_targets f hgf]
            exact fun w hw => hreg w (List.mem_append_right _ hw))
      intro cursor grefs
      rw [MeasuredClear.static_cast, ← support_agrees, straightWires_append]
      refine List.append_subset.mpr ⟨compile_support _ _ _ _ newSourceH root_new bits_new bank_new
        (normalized_lit_support _ newSourceH hlitA) (normalized_look_support _ newSourceH hlookA) _, ?_⟩
      rw [support_agrees]
      apply MeasuredClear.measureThen_within _ newSourceH _ _ _ _
        (by rw [clearData_targets]; exact fun w hw => hreg w (List.mem_append_left _ hw))
      intro c2 rs
      rw [← support_agrees]
      exact ih' _ _ _

end
end ShorECDLP.Entrant.WEXFast

end

/-! ### Stage 2 (row-level deferred fixups), formerly `RowFused2.lean` -/

section

/-! # Stage-2 rows and windows: the deferred wide and narrow rows, their signed windows. -/

/-! ### The deferred wide row and its signed window -/

namespace ShorECDLP.Entrant.WideBank8.Row17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- The wide row: the entry site's clear, the second fast site and the corner `y` clear defer their
fixups to the corner output clear. The triple site (generic guard) keeps its own fixup. -/
def code : Fast16.DCode 65536 :=
  ((WEXUnlookup.rowPre3.map toBlock2).take 2).map (fun b => .std (WideBank8.Row16.lift (.std b))) ++
  [.defer (Rows.unit WideBank8.Row16.rows ⟨(WEXUnlookup.site1 probeRows).prefix, WEXUnlookup.site1 probeRows⟩)] ++
  (WEXFast.fgeneric3.take 9).map (fun b => .std (WideBank8.Row16.lift b)) ++ [.defer1 (WideBank8.Row16.fast1 WEXFast.site2F)] ++
  (WEXFast.fgeneric3.drop 10).map (fun b => .std (WideBank8.Row16.lift b)) ++
  [.std (WideBank8.Row16.lift (.std (.plain WEX.cornerNeg))), .defer (Rows.unit WideBank8.Row16.rows WEXUnlookup.cornerUnit₁),
   .pay (Rows.unit WideBank8.Row16.rows WEXUnlookup.cornerUnit₂), .std (WideBank8.Row16.lift (.std (.plain WEX.sfxTailF))),
   .std (WideBank8.Row16.lift (.std (.plain (wLiteral [.X 838]))))]

theorem dfor_code : Fast16.dfor code = WideBank8.Row16.code := rfl

theorem guards : ∀ b ∈ code, Fast16.DGuard b := by
  simp only [code, List.forall_mem_append, List.forall_mem_cons]
  repeat' constructor
  all_goals first
    | exact Fast16.guard_std _ _
    | exact fun x hx => by simp at hx

theorem geometry : ∀ b ∈ code, Fast16.DGeo b := fun b hb =>
  ⟨WideBank8.Row16.geometry _ (by rw [← dfor_code]; exact List.mem_map_of_mem hb), guards b hb⟩

theorem paid : Fast16.Paid code List.nil := by
  simp only [code, List.append_assoc, List.cons_append, List.nil_append, Fast16.paid_std, Fast16.Paid]

theorem dsave_code : Fast16.dsave code = 1506 := by
  simp only [code, List.append_assoc, List.cons_append, List.nil_append, Fast16.dsave_std, Fast16.dsave,
    Nat.add_zero, Nat.reduceAdd]

theorem drsave_code : Fast16.drsave code = 1530 := by
  simp only [code, List.append_assoc, List.cons_append, List.nil_append, Fast16.drsave_std, Fast16.drsave,
    Nat.add_zero, Nat.reduceAdd]

end
end ShorECDLP.Entrant.WideBank8.Row17

namespace ShorECDLP.Entrant.WideBank8.Row17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WEXFast.rowCF WEXUnlookup.rowC Fast16.dprog
  Straight.WellFormed Straight.instantiate AdaptiveCircuit.run

def program (start : Nat) := Fast16.dprog code List.nil start List.nil

theorem coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  have h := Fast16.dprog_coherent (readConstant coeffs Q) code geometry paid liveReady (Add.update .w16 coeffs Q)
    (fun s hs => by rw [dfor_code, WideBank8.Row16.forget]; exact Rows.row_safe _ _ _ hQ hn _ s hs)
    (fun s hs => by
      rw [dfor_code]
      exact WideBank8.Row16.clean_lift coeffs Q _ _ (fun _ h => h) _
        (WEXFast.rowCF_clean (fun _ => coeffs (WideBank8.Row16.rows (tableAddressValue Fast16.windowBits s))) Q hQ
          (fun _ => hn _) _ s hs) (fun v hv => hs.2.1 v (List.mem_append_right _ hv)))
    (fun s hs m => by rw [dfor_code, WideBank8.Row16.forget]; exact Rows.row_run _ _ _ hQ hn _ s hs m) start history
  obtain ⟨cs, aligned, mass⟩ := h
  exact ⟨cs, aligned.imp (fun b c hb s hs => hb s ⟨hs.2.2, hs⟩), mass⟩

theorem wellFormed (start : Nat) : (program start).WellFormed := by
  apply Fast16.dprog_wellFormed _ geometry
  rw [dfor_code, WideBank8.Row16.forget]
  exact Geometry.row_physical .w16

theorem tCount (read : ConstantBit 65536 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate read history).tCount = 7 * Fast16.dcodeTP code :=
  Fast16.dprog_tCount read code geometry _ start _ history

end
end ShorECDLP.Entrant.WideBank8.Row17

namespace ShorECDLP.Entrant.WideBank8.Row17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WideBank8.Row16.code Fast16.dprog WEXFast.rowCF WEXUnlookup.rowC
  ECDSAAdd.toffoliCount ECDSAAdd.Baselines.normalizeProgram literalToffolis normalizeW
  Fast16.fcodeTP Fast16.fsave WEXFast.fcodeTP WEXUnlookup.ccx2 codeTP2 Fast16.dcodeTP Fast16.dsave

theorem credit_relation : Fast16.dcodeTP code + 1506 = Fast16.fcodeTP WideBank8.Row16.code := by
  have h := Fast16.dcodeTP_relation code geometry
  rw [dsave_code, dfor_code] at h
  exact h

theorem body_credit_bound :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) +
      Fast16.dcodeTP code ≤ 2341681 := by
  have h := WideBank8.Row16.body_credit_bound
  have r := credit_relation
  omega

end
end ShorECDLP.Entrant.WideBank8.Row17

namespace ShorECDLP.Entrant.WideBank8.Row17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WideBank8.Row16.code WEXFast.rowCF WEXUnlookup.rowC
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  ECDSAAdd.measurementCount ECDSAAdd.Baselines.normalizeProgram literalRecords normalizeW
  Fast16.frecs Fast16.frsave recordsP2 masks2 lens2 Fast16.drecs Fast16.drsave

theorem row_records : Fast16.drecs code = 1741982 := by
  have h := Fast16.drecs_relation code geometry
  rw [drsave_code, dfor_code, WideBank8.Row16.row_records] at h
  omega

end
end ShorECDLP.Entrant.WideBank8.Row17

namespace ShorECDLP.Entrant.WideBank8.Row17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WideBank8.Row16.code WEXFast.rowCF WEXUnlookup.rowC
  codeSlots literalSlotSum portTotal traversals normalizeW ECDSAAdd.Baselines.normalizeProgram
  Fast16.dprog Fast16.fslack codeSP2 masks2 lens2

theorem slots_bound : codeSP2 Fast16.bank15 (Fast16.fforget (Fast16.dfor code)) + Fast16.fslack (Fast16.dfor code) +
    262144 * (List.nil : List (MeasuredClear.ClearPort 65536)).length ≤ 2475408334 := by
  have hn := WideBank8.Row16.standard_slots
  rw [dfor_code, WideBank8.Row16.forget, WideBank8.Row16.slack, List.length_nil, Nat.mul_zero, Nat.add_zero]
  omega

theorem slots (start : Nat) : (program start).gateSlots ≤ 2475408334 :=
  le_trans (Fast16.dprog_slots code geometry List.nil start List.nil) slots_bound

end
end ShorECDLP.Entrant.WideBank8.Row17

namespace ShorECDLP.Entrant.WideBank8.Row17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] program code Fast16.dprog Fast16.drecs Fast16.dcodeTP WideBank8.Row16.code
  ECDSAAdd.Baselines.normalizeProgram WEX.codeRecords Nat.add Nat.mul

def fixedProgram (start : Nat) : Straight 65536 start (start + 1741982) :=
  castFinish (congrArg (fun m => start + m) row_records) (program start)

attribute [local irreducible] fixedProgram

theorem fixed_run (read : ConstantBit 65536 → Bool) (start : Nat) (hist : Fin start → Bool) :
    ((fixedProgram start).instantiate read hist).run = ((program start).instantiate read hist).run := by
  rw [fixedProgram, castFinish_instantiate]

theorem fixed_wellFormed (start : Nat) : (fixedProgram start).WellFormed := by
  rw [fixedProgram, castFinish_wellFormed]
  exact wellFormed start

theorem fixed_credit (start : Nat) : ProgramCredit (fixedProgram start) (Fast16.dcodeTP code) := by
  rw [fixedProgram]
  apply credit_cast
  have hz : residue (program start) = 0 := by rw [program]; exact Fast16.dprog_residue _ _ _ _
  refine ⟨hz, ?_⟩
  have ht := tCount (fun _ => false) start (fun _ => false)
  have he := exact_t (program start) hz (fun _ => false) (fun _ => false)
  omega

theorem fixed_slots (start : Nat) : (fixedProgram start).gateSlots ≤ 2475408334 := by
  rw [fixedProgram, castFinish_gateSlots]
  exact slots start

theorem fixed_tsupport (start : Nat) :
    straightWires (fixedProgram start) ⊆ Fast16.Tight.support := by
  rw [fixedProgram, straightWires_castFinish, program]
  exact Fast16.Tight.dprog_tsupport code geometry (dfor_code ▸ Fast16.Tight.row_literals)
    (dfor_code ▸ WideBank8.Row16.strict) (dfor_code ▸ WideBank8.Row16.ctl) (dfor_code ▸ WideBank8.Row16.ctl3)
    (dfor_code ▸ Fast16.Tight.row_lookups) (dfor_code ▸ Fast16.Tight.row_nohost) _ _ _

end
end ShorECDLP.Entrant.WideBank8.Row17

set_option Elab.async false
namespace ShorECDLP.Entrant.WideBank8.Signed17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Straight.instantiate Straight.WellFormed AdaptiveCircuit.run
  Frame16.program Fast16.dprog Row17.program Row17.code Fast16.drecs Fast16.dcodeTP WEXFast.rowCF WEXUnlookup.rowC
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram Nat.add Nat.mul

def records : Nat := 1742494
local notation "signedCredit17" => (2 * Body.signCredit + Fast16.dcodeTP Row17.code)

def program (start : Nat) : Straight 65536 start (start + 1742494) :=
  castFinish (congrArg (fun m => start + m) (by decide : 512 + 1741982 = 1742494))
    (Frame16.program 1741982 Row17.fixedProgram start)

attribute [local irreducible] program

def rowSource (coeffs : Fin 65536 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  Fast16.dsrc (readConstant coeffs Q) Row17.code List.nil List.nil
def source (coeffs : Fin 65536 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (Body.prefixSource .w16).seq ((Body.signSource.seq ((rowSource coeffs Q).seq Body.signSource)).seq
    (Body.suffixSource .w16))

theorem row_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (rowSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  obtain ⟨cs, aligned, mass⟩ := Row17.coherent coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs, ?_, mass⟩
  simpa only [Row17.program, Fast16.dprog_run, List.map_nil, rowSource] using aligned

theorem source_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (source coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  have hs : CoherentlyImplementsOn Body.signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady :=
    fastWindowSign_coherent
  have ha := composeCoherent hs (row_coherent coeffs Q hQ hn) (fun s h => liveReady_write _ s h)
  have hb := composeCoherent ha hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  have hc := composeCoherent (Body.prefix_coherent .w16) hb
    (fun s h => Body.prepare_live .w16 _ (rootFlip_live s h))
  have hd := composeCoherent hc (Body.suffix_coherent .w16) (fun _ _ => trivial)
  simpa only [source, Body.state, adaptive_seq_assoc] using hd

theorem run (coeffs : Fin 65536 → PointCoeff) (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).run = (source coeffs Q).run := by
  rw [program, castFinish_instantiate]
  have hr (j : Nat) (hist : Fin j → Bool) :
      ((Row17.fixedProgram j).instantiate (readConstant coeffs Q) hist).run = (rowSource coeffs Q).run := by
    rw [Row17.fixed_run, Row17.program, Fast16.dprog_run, List.map_nil]
    rfl
  simpa only [source] using Frame16.run 1741982 Row17.fixedProgram (rowSource coeffs Q)
    (readConstant coeffs Q) hr start history

theorem coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  unfold CoherentlyImplementsOn
  rw [run]
  exact source_coherent coeffs Q hQ hn

def window : Single.Window 65536 := ⟨(Body.logicalBank .w16).reverse, 1742494, program⟩
def model (coeffs : Fin 65536 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) : Single.Distribution.WindowModel (readConstant coeffs Q) where
  physical := window
  point := fun a => if a < 2 ^ Geometry.Width.w16.bits then
    -constantPoint Q (coeffs (Geometry.rows .w16 (2 ^ Geometry.Width.w16.bits - 1 - a)))
    else constantPoint Q (coeffs (Geometry.rows .w16 (a - 2 ^ Geometry.Width.w16.bits)))
  bias := 0
  ideal := Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)
  valid := windowReady
  nodup := by change (Body.logicalBank .w16).reverse.Nodup; exact List.nodup_reverse.mpr (by decide)
  coherent := coherent coeffs Q hQ hn

theorem program_credit (start : Nat) : ProgramCredit (program start) signedCredit17 := by
  rw [program]
  apply credit_cast
  exact Frame16.credit _ _ Row17.fixedProgram Row17.fixed_credit start

theorem wellFormed (start : Nat) : (program start).WellFormed := by
  rw [program, castFinish_wellFormed]
  exact Frame16.wellFormed _ Row17.fixedProgram Row17.fixed_wellFormed start

theorem sign_credit_bound (s t r : Nat) (hs : s = t) (hb : 2 * t + r ≤ 2341681) :
    2 * s + r ≤ 2341681 := by omega

theorem credit_bound : signedCredit17 ≤ 2341681 :=
  sign_credit_bound Body.signCredit
    (ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram))
    (Fast16.dcodeTP Row17.code) rfl Row17.body_credit_bound

theorem measurements (read : ConstantBit 65536 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate read history).measurementCount = 1742494 := by
  rw [Straight.measurementCount]
  omega

end
end ShorECDLP.Entrant.WideBank8.Signed17

namespace ShorECDLP.Entrant.WideBank8.Signed17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare Single Single.Distribution
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program Row17.program fourierOutcomes AdaptiveCircuit.run

theorem pointRule (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hactive : root 836 = true) (hz : Clean (Body.logicalBank .w16) root) :
    PointRule root (model coeffs Q hQ hn) := by
  intro prior output P
  simpa only [WindowModel.step, model, window, List.reverse_reverse, List.length_reverse, LinearMap.comp_apply] using
    Body.point_sum .w16 coeffs Q hQ hn root hactive hz prior output P

theorem prepared (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hs : windowReady root) (hz : Clean (Body.logicalBank .w16) root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (model coeffs Q hQ hn).valid
      (Quantum.run ((model coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ) := by
  change SupportedOn (Body.model .w16 coeffs Q hQ hn).valid
    (Quantum.run ((Body.model .w16 coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ)
  exact Body.prepared .w16 coeffs Q hQ hn root hs hz ψ hψ

end
end ShorECDLP.Entrant.WideBank8.Signed17

namespace ShorECDLP.Entrant.WideBank8.Signed17
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program Row17.program ECDSAAdd.Baselines.normalizeProgram
  ECDSAAdd.Challenge.gateSlots literalT Bridge.tmplSlots Frame16.program Row17.code Fast16.drecs

theorem slots (start : Nat) : (program start).gateSlots ≤ 2500000000 := by
  have hrow := Row17.fixed_slots (start + 256)
  have hsign (j : Nat) : (Body.nProgram .w16 j).gateSlots ≤ 300000 := by
    rw [Body.nProgram, reindexStraight_gateSlots, nFastProgram_slots]
    have h := literal_slot_bound (n := 32768)
      (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
    rw [ECDSAAdd.Baselines.normalize_slots] at h
    have hmax := fastWindowSign_slots
    omega
  rw [program, castFinish_gateSlots, Frame16.slots]
  have h1 := hsign start
  have h2 := hsign (start + 256 + 1741982)
  omega

theorem signed_tsupport (start : Nat) :
    straightWires (program start) ⊆ Fast16.Tight.support := by
  rw [program, straightWires_castFinish]
  exact TightSupport.frame_support _ Row17.fixedProgram Row17.fixed_tsupport start

theorem packed_support (start : Nat) :
    straightWires (relabelStraight TightSupport.compact (program start)) ⊆ List.range 1618 := by
  rw [straightWires_relabel]
  intro v hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (TightSupport.compact_bound u (signed_tsupport start hu))

end
end ShorECDLP.Entrant.WideBank8.Signed17

/-! ### The deferred narrow row -/

namespace ShorECDLP.Entrant.WEXFast.W15H
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup WEXFast
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- The narrow row: the entry site's clear, the second fast site and the corner `y` clear defer their
fixups to the corner output clear. The triple site (generic guard) keeps its own fixup. -/
def code : DCode 32768 :=
  ((WEXUnlookup.rowPre3.map toBlock2).take 2).map (fun b => .std (.std b)) ++
  [.defer ⟨(WEXUnlookup.site1 probeRows).prefix, WEXUnlookup.site1 probeRows⟩] ++
  (fgeneric3.take 9).map (fun b => .std b) ++ [.defer1 site2F] ++
  (fgeneric3.drop 10).map (fun b => .std b) ++
  [.std (.std (.plain WEX.cornerNeg)), .defer WEXUnlookup.cornerUnit₁, .pay WEXUnlookup.cornerUnit₂,
   .std (.std (.plain WEX.sfxTailF)), .std (.std (.plain (wLiteral [.X 838])))]

theorem dfor_code : dfor code = rowCF := rfl

theorem guards : ∀ b ∈ code, DGuard b := by
  simp only [code, List.forall_mem_append, List.forall_mem_cons]
  repeat' constructor
  all_goals first
    | exact guard_std _ _
    | exact fun x hx => by simp at hx

theorem geometry : ∀ b ∈ code, DGeo b := fun b hb =>
  ⟨rowCF_ggeo _ (by rw [← dfor_code]; exact List.mem_map_of_mem hb), guards b hb⟩

theorem paid_std' (l : FCode2 32768) (rest : DCode 32768) (d : List (MeasuredClear.ClearPort 32768)) :
    Paid (l.map DBlock.std ++ rest) d = Paid rest d := paid_std l (fun x => x) rest d
theorem dsave_std' (l : FCode2 32768) (rest : DCode 32768) :
    dsave (l.map DBlock.std ++ rest) = dsave rest := dsave_std l (fun x => x) rest
theorem drsave_std' (l : FCode2 32768) (rest : DCode 32768) :
    drsave (l.map DBlock.std ++ rest) = drsave rest := drsave_std l (fun x => x) rest

theorem paid : Paid code List.nil := by
  simp only [code, List.append_assoc, List.cons_append, List.nil_append, paid_std, paid_std', Paid]

theorem dsave_code : dsave code = 1125 := by
  simp only [code, List.append_assoc, List.cons_append, List.nil_append, dsave_std, dsave_std', dsave,
    Nat.add_zero, Nat.reduceAdd]

theorem drsave_code : drsave code = 1146 := by
  simp only [code, List.append_assoc, List.cons_append, List.nil_append, drsave_std, drsave_std', drsave,
    Nat.add_zero, Nat.reduceAdd]

end
end ShorECDLP.Entrant.WEXFast.W15H

namespace ShorECDLP.Entrant.WEXFast.W15H
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup WEXFast
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] code rowCF WEXUnlookup.rowC

theorem rowD_gtp : dcodeTP code + 1125 = gcodeTP rowCF := by
  have h := dcodeTP_relation code geometry
  rw [dsave_code, dfor_code] at h
  exact h

theorem sub_arith (x : Nat) (h : x + 1146 = 1652760) : x = 1651614 := by omega

theorem rowD_records : drecs code = 1651614 := by
  have h := drecs_relation code geometry
  rw [drsave_code, dfor_code, W15G.rowCF_grecords] at h
  exact sub_arith _ h

theorem rowD_slots_bound : codeSP2 bank15 (fforget (dfor code)) + fslack (dfor code) +
    131072 * (List.nil : List (MeasuredClear.ClearPort 32768)).length ≤
    codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 418411946 := by
  have h1 : codeSP2 bank15 (fforget (dfor code)) =
      codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 250628164 := by
    rw [dfor_code, fforget_rowCF]
    exact ShorECDLP.Entrant.WEXFast.W15F.rowC_slotsP 0
  have h2 : fslack (dfor code) = 167783782 := by
    rw [dfor_code]
    exact ShorECDLP.Entrant.WEXFast.W15F.rowCF_slack
  have h3 : 131072 * (List.nil : List (MeasuredClear.ClearPort 32768)).length = 0 := by simp
  omega

theorem rowD_slots (start : Nat) : (dprog code List.nil start List.nil).gateSlots ≤
    codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 418411946 :=
  le_trans (dprog_slots code geometry List.nil start List.nil) rowD_slots_bound

attribute [local irreducible] dprog gblockProg blockProgP2 clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx2 gcodeTP dcodeTP Nat.add Nat.mul

def addFixedCH (start : Nat) : Straight 32768 start (start+1651614) :=
  castFinish (congrArg (fun m => start+m) rowD_records) (dprog code List.nil start List.nil)

theorem addFixedCH_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedCH start).instantiate read history).run = (dsrc read code List.nil List.nil).run := by
  rw [addFixedCH, castFinish_instantiate, dprog_run, List.map_nil]

theorem addFixedCH_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedCH start).instantiate read history).tCount = 7 * dcodeTP code := by
  rw [addFixedCH, castFinish_instantiate, dprog_tCount read code geometry]

theorem addFixedCH_slots (start : Nat) : (addFixedCH start).gateSlots ≤
    codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 418411946 := by
  rw [addFixedCH, castFinish_gateSlots]
  exact rowD_slots start

theorem addFixedCH_wellFormed (start : Nat) : (addFixedCH start).WellFormed := by
  rw [addFixedCH, castFinish_wellFormed]
  exact dprog_wellFormed code geometry (by rw [dfor_code, fforget_rowCF]; exact WEXUnlookup.rowC_physical) _ _ _

theorem addFixedCH_residue (start : Nat) : residue (addFixedCH start) = 0 := by
  rw [addFixedCH, residue_cast]
  exact dprog_residue code _ _ _

theorem addFixedCH_credit (start : Nat) : ProgramCredit (addFixedCH start) (dcodeTP code) := by
  have hz := addFixedCH_residue start
  refine ⟨hz, ?_⟩
  have he := exact_t (addFixedCH start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedCH_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixedCH_support (start : Nat) : ChallengeMigration.straightWires (addFixedCH start) ⊆ newSourceH := by
  rw [addFixedCH, support_cast]
  exact dprog_hsupport code geometry (by rw [dfor_code, fforget_rowCF]; exact rowC_lit_relaxed)
    (dfor_code ▸ ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict) (dfor_code ▸ ShorECDLP.Entrant.WEXFast.W15F.rowCF_ctl)
    (dfor_code ▸ ShorECDLP.Entrant.WEXFast.W15F.rowCF_ctl3) (by rw [dfor_code, fforget_rowCF]; exact rowC_look_newH)
    (dfor_code ▸ ShorECDLP.Entrant.WEXFast.W15F.rowCF_nohost) _ _ _

def rowSourceCH (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  dsrc (readConstant coeffs Q) code List.nil List.nil

theorem rowSourceCH_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSourceCH coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := dprog_coherent (readConstant coeffs Q) code geometry paid liveReady (rowPointState coeffs Q)
    (fun s hs => by rw [dfor_code, fforget_rowCF]; exact (WEXUnlookup.rowC_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => by rw [dfor_code]; exact rowCF_clean coeffs Q hQ hn _ s hs)
    (fun s hs m => by rw [dfor_code, fforget_rowCF]; exact WEXUnlookup.rowC_run_any _ coeffs Q hQ hn s hs m)
    0 Fin.elim0
  obtain ⟨cs, aligned, mass⟩ := h
  refine ⟨cs, ?_, mass⟩
  rw [dprog_run, List.map_nil] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceCH coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceCH_coherent coeffs Q hQ hn)
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

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1652126) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedCH (start+256))).append
      (nFastProgram (start+256+1651614))).append (suffixProgram (start+256+1651614+256)))

attribute [local irreducible] fastBodyProgram addFixedCH

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (dsrc (readConstant coeffs Q) code List.nil List.nil)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram, castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (dsrc (readConstant coeffs Q) code List.nil List.nil) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedCH_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (dsrc (readConstant coeffs Q) code List.nil List.nil)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceCH
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
      dcodeTP code) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1651614)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (dcodeTP code) (prefix_credit start) hl (addFixedCH_credit (start+256)) hr
    (suffix_credit (start+256+1651614+256))

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram, castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixedCH_wellFormed _
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
  exact ⟨⟨⟨⟨hp, nFast_newH _⟩, addFixedCH_support _⟩, nFast_newH _⟩, hs _⟩

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append, nFastProgram_slots, prefixProgram, suffixProgram, literalProgram_slots]
  have ha := addFixedCH_slots (start+256)
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
  generalize (addFixedCH (start + 256)).gateSlots = A at ha ⊢
  generalize ECDSAAdd.Challenge.gateSlots fastWindowSignProgram = G at sign bound
  generalize Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) = S
    at sign ⊢
  exact ShorECDLP.Entrant.WEXFast.W15F.body_slot_arith S A G C _ _ _ _ windowBits.length _ sign bound ha hc rfl hm.2.1 hm.2.2.1 hl hm.2.2.2.1 hp

def compactProgram (start : Nat) : Straight 32768 start (start+1652126) :=
  relabelStraight piH (fastBodyProgram start)

theorem count_arith (s x y : Nat) (h : s + y ≤ 2252440) (hr : x + 1125 = y) : s + x ≤ 2251315 := by omega

theorem fastCount_upper : 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    dcodeTP code ≤ 2251315 := by
  exact count_arith _ _ _ W15G.fastCount_upper rowD_gtp

end
end ShorECDLP.Entrant.WEXFast.W15H

end

/-! ### The concrete width-16 implementation, formerly the tail of `Schedule27.lean` -/

namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] fourierOutcomes

theorem clear_relabel (e : Wire ≃ Wire) (ws : List Wire) (s : BasisState) :
    fourierClear (ws.map e) (relabelBasis e s) = relabelBasis e (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, fourierClear, ← relabelBasis_upd, ih]

theorem coefficient_relabel (e : Wire ≃ Wire) (dir : PhaseDir) (ws : List Wire)
    (prior bits : List Bool) (s : BasisState) :
    fourierBranchCoeff dir (ws.map e) prior bits (relabelBasis e s) =
      fourierBranchCoeff dir ws prior bits s := by
  induction ws generalizing prior bits s with
  | nil => cases bits <;> rfl
  | cons w ws ih =>
    cases bits with
    | nil => rfl
    | cons b bs =>
      simp only [List.map_cons, fourierBranchCoeff, relabelBasis_at, ← relabelBasis_upd, ih]

theorem fourier_relabel (e : Wire ≃ Wire) (dir : PhaseDir) (ws : List Wire)
    (prior bits : List Bool) (ψ : State) :
    fourierBranch dir (ws.map e) prior bits (relabelState e ψ) =
      relabelState e (fourierBranch dir ws prior bits ψ) := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single s c =>
    have hs : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [hs]
    simp only [map_smul, relabelState_ket, fourierBranch_ket, coefficient_relabel,
      clear_relabel]

def relabelModel {n : Nat} {read : ConstantBit n → Bool} (e : Wire ≃ Wire)
    (m : WindowModel read) : WindowModel read where
  physical := ⟨m.physical.wires.map e,m.physical.count,
    fun start => relabelStraight e (m.physical.program start)⟩
  point := m.point
  bias := m.bias
  ideal := (relabelState e).comp (m.ideal.comp (relabelState e.symm))
  valid := fun s => m.valid (relabelBasis e.symm s)
  nodup := m.nodup.map e.injective
  coherent := by
    intro start history
    rw [relabelStraight_instantiate]
    exact (m.coherent start history).relabel e

theorem hadamards_relabel (e : Wire ≃ Wire) (ws : List Wire) (ψ : State) :
    Quantum.run ((ws.map e).map Gate.H) (relabelState e ψ) =
      relabelState e (Quantum.run (ws.map Gate.H) ψ) := by
  have he : (ws.map e).map Gate.H = (ws.map Gate.H).map (Gate.relabel e) := by
    simp only [List.map_map, Function.comp_def, Gate.relabel]
  rw [he]
  exact Quantum.run_relabel e _ ψ

theorem relabelModel_step {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read) (prior bits : List Bool) (ψ : State) :
    (relabelModel e m).step prior bits (relabelState e ψ) =
      relabelState e (m.step prior bits ψ) := by
  simp only [WindowModel.step, relabelModel, LinearMap.comp_apply, ← List.map_reverse,
    hadamards_relabel, relabelState_symm, fourier_relabel]

theorem root_relabel (e : Wire ≃ Wire) (he : e 836 = 836) :
    relabelBasis e initialRoot = initialRoot := by
  have hz : relabelBasis e zeroBasisState = zeroBasisState := rfl
  simp only [initialRoot, relabelBasis_upd, hz, he]

theorem relabelModel_pointRule {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read)
    (pointFrame : ∀ P s, relabelBasis e (pointWrite P s) = pointWrite P (relabelBasis e s))
    (he : e 836 = 836) (h : PointRule initialRoot m) :
    PointRule initialRoot (relabelModel e m) := by
  intro prior bits P
  have hk : ket (pointWrite P initialRoot) = relabelState e (ket (pointWrite P initialRoot)) := by
    rw [relabelState_ket, pointFrame, root_relabel e he]
  rw [hk, relabelModel_step, h]
  simp only [map_smul, map_list_sum, relabelState_ket, pointFrame, root_relabel e he,
    List.map_map, Function.comp_def, relabelModel, List.length_map]

theorem supported_relabel (e : Wire ≃ Wire) (V : BasisState → Prop) (ψ : State)
    (hψ : SupportedOn V ψ) :
    SupportedOn (fun s => V (relabelBasis e.symm s)) (relabelState e ψ) := by
  refine Support.linear V (fun s => V (relabelBasis e.symm s)) (relabelState e) ?_ ψ hψ
  intro s hs
  rw [relabelState_ket]
  exact supportedOn_ket _ _ (by simpa only [relabelBasis_symm] using hs)

theorem relabelModel_prepared {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read)
    (pointFrame : ∀ P s, relabelBasis e.symm (pointWrite P s) = pointWrite P (relabelBasis e.symm s))
    (he : e 836 = 836)
    (hp : ∀ ψ, SupportedOn (pointFamily initialRoot) ψ →
      SupportedOn m.valid (Quantum.run (m.physical.wires.reverse.map Gate.H) ψ))
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (relabelModel e m).valid
      (Quantum.run ((relabelModel e m).physical.wires.reverse.map Gate.H) ψ) := by
  have hes : e.symm 836 = 836 := (Equiv.symm_apply_eq e).mpr he.symm
  have hs : SupportedOn (pointFamily initialRoot) (relabelState e.symm ψ) := by
    refine Support.linear (pointFamily initialRoot) (pointFamily initialRoot) (relabelState e.symm) ?_ ψ hψ
    intro s hs
    obtain ⟨P,rfl⟩ := hs
    rw [relabelState_ket, pointFrame, root_relabel e.symm hes]
    exact supportedOn_ket _ _ ⟨P,rfl⟩
  have hc := supported_relabel e m.valid _ (hp _ hs)
  have hh := hadamards_relabel e m.physical.wires.reverse (relabelState e.symm ψ)
  rw [relabelState_symm_right] at hh
  simpa only [relabelModel, ← List.map_reverse, hh] using hc

end
end ShorECDLP.Entrant.Width16Actual


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule
noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

attribute [local irreducible] WideBank8.Signed17.program WEXFast.W15H.fastBodyProgram
  WEXFast.W15H.compactProgram WideBank8.Row17.program PathShare.narrowCF15

local notation "wideCredit" =>
  (2 * WideSigned.Body.signCredit + WideBank8.Fast16.dcodeTP WideBank8.Row17.code)
local notation "normalCredit" =>
  (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    WEXFast.dcodeTP WEXFast.W15H.code)

def wide : Window 65536 :=
  ⟨(WideSigned.Body.logicalBank .w16).reverse.map TightSupport.compact,
    1742494, fun start => relabelStraight TightSupport.compact (WideBank8.Signed17.program start)⟩

def normal : Window 32768 :=
  ⟨streamAddress.reverse,1652126,WEXFast.W15H.compactProgram⟩

def signed : Digit → Window 1769472 := familyWindows wide normal


theorem signed_width (w : Digit) : (signed w).wires.length = w.width :=
  family_widths wide normal (by simp only [wide,List.length_map,List.length_reverse]; decide) (by decide) w

theorem signed_count (w : Digit) : (signed w).count = count 1742494 1652126 w :=
  family_counts wide normal w

theorem signed_credit (w : Digit) (start : Nat) :
    ProgramCredit ((signed w).program start) (count wideCredit normalCredit w) := by
  cases w with
  | left17 j | right17 j =>
    rw [count]
    change ProgramCredit (reindexStraight _ (relabelStraight _ (WideBank8.Signed17.program start))) wideCredit
    constructor
    · rw [WEXCredit.residue_reindex, WEXUnlookup.residue_relabel]
      exact (WideBank8.Signed17.program_credit start).1
    · rw [added_reindex, added_relabel]
      exact (WideBank8.Signed17.program_credit start).2
  | left16 j =>
    rw [count]
    constructor
    · rw [show ((signed (.left16 j)).program start) = reindexStraight (row (.left16 j)) (WEXFast.W15H.compactProgram start) from rfl,
        WEXCredit.residue_reindex]
      exact by rw [WEXFast.W15H.compactProgram,WEXUnlookup.residue_relabel]; exact (WEXFast.W15H.fastBodyProgram_credit start).1
    · rw [show ((signed (.left16 j)).program start) = reindexStraight (row (.left16 j)) (WEXFast.W15H.compactProgram start) from rfl,
        added_reindex]
      exact by rw [WEXFast.W15H.compactProgram,added_relabel]; exact (WEXFast.W15H.fastBodyProgram_credit start).2
  | right16 j =>
    rw [count]
    constructor
    · rw [show ((signed (.right16 j)).program start) = reindexStraight (row (.right16 j)) (WEXFast.W15H.compactProgram start) from rfl,
        WEXCredit.residue_reindex]
      exact by rw [WEXFast.W15H.compactProgram,WEXUnlookup.residue_relabel]; exact (WEXFast.W15H.fastBodyProgram_credit start).1
    · rw [show ((signed (.right16 j)).program start) = reindexStraight (row (.right16 j)) (WEXFast.W15H.compactProgram start) from rfl,
        added_reindex]
      exact by rw [WEXFast.W15H.compactProgram,added_relabel]; exact (WEXFast.W15H.fastBodyProgram_credit start).2

def implementation : Implementation :=
  withHeads 1742494 1652126 wideCredit normalCredit signed signed_width signed_count
    (fun w start => (signed_credit w start).1) (fun w start => (signed_credit w start).2)


theorem withHeads_credits {r17 r16 c17 c16 : Nat} {s : Digit → Window 1769472} {hw hc hz ha} :
    (withHeads r17 r16 c17 c16 s hw hc hz ha).credit17 = c17 ∧
      (withHeads r17 r16 c17 c16 s hw hc hz ha).credit16 = c16 := ⟨rfl, rfl⟩

theorem credits : implementation.credit17 ≤ 2341681 ∧ implementation.credit16 ≤ 2251315 := by
  rw [implementation, withHeads_credits.1, withHeads_credits.2]
  exact ⟨WideBank8.Signed17.credit_bound, WEXFast.W15H.fastCount_upper⟩

theorem signed_support (w : Digit) (start : Nat) :
    straightWires ((signed w).program start) ⊆ List.range 1618 := by
  cases w with
  | left17 j | right17 j =>
    change straightWires (reindexStraight _ (relabelStraight _ (WideBank8.Signed17.program start))) ⊆ _
    rw [straightWires_reindex]
    exact WideBank8.Signed17.packed_support start
  | left16 j =>
    change straightWires (reindexStraight _ (WEXFast.W15H.compactProgram start)) ⊆ _
    rw [straightWires_reindex, WEXFast.W15H.compactProgram]
    exact (PathShare.relabelH_support _ (WEXFast.W15H.fastBodyProgram_support start)).trans (List.range_subset.mpr (by decide : 1616 ≤ 1618))
  | right16 j =>
    change straightWires (reindexStraight _ (WEXFast.W15H.compactProgram start)) ⊆ _
    rw [straightWires_reindex, WEXFast.W15H.compactProgram]
    exact (PathShare.relabelH_support _ (WEXFast.W15H.fastBodyProgram_support start)).trans (List.range_subset.mpr (by decide : 1616 ≤ 1618))


theorem signed_wellFormed (w : Digit) (start : Nat) : ((signed w).program start).WellFormed := by
  cases w with
  | left17 j | right17 j =>
    apply (reindexStraight_wellFormed _ _).mpr
    exact (relabelStraight_wellFormed _ _).mpr (WideBank8.Signed17.wellFormed start)
  | left16 j | right16 j =>
    apply (reindexStraight_wellFormed _ _).mpr
    change (WEXFast.W15H.compactProgram start).WellFormed
    rw [WEXFast.W15H.compactProgram]
    exact (relabelStraight_wellFormed _ _).mpr (WEXFast.W15H.fastBodyProgram_wellFormed start)

end
end ShorECDLP.Entrant.Width16Actual


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] fourierOutcomes WEXFast.W15H.fastBodyProgram WEXFast.W15H.compactProgram

def normalPoint (coeffs : Fin 32768 → PointCoeff) (Q : Point) (v : Nat) : Point :=
  if v < 32768 then -constantPoint Q (coeffs ⟨(32767-v)%32768,Nat.mod_lt _ (by decide)⟩)
  else constantPoint Q (coeffs ⟨(v-32768)%32768,Nat.mod_lt _ (by decide)⟩)

def normalModel (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) : WindowModel (readConstant coeffs Q) where
  physical := normal
  point := normalPoint coeffs Q
  bias := 0
  ideal := Finsupp.lmapDomain ℂ ℂ (PathShare.stateH coeffs Q)
  valid := fun s => PathShare.readyH s ∧ ∃ P, pointStateCoordinates s=fig14PointEncoding P
  nodup := by decide
  coherent := by
    intro start history
    simpa only [normal,WEXFast.W15H.compactProgram] using
      PathShare.relabelH_coherent _ coeffs Q history
        (WEXFast.W15H.fastBodyProgram_coherent coeffs Q hQ hn start history)

theorem normal_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : PathShare.readyH s) (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    PathShare.stateH coeffs Q s = pointWrite (P+normalPoint coeffs Q (windowRawDigit 0 s)) s := by
  have hl : tableAddressValue WEX.windowBits s < 32768 := by
    simpa only [WEX.windowBits,List.length_range'] using tableAddressValue_lt WEX.windowBits s
  have hv : windowRawDigit 0 s = tableAddressValue WEX.windowBits s + Bool.toNat (s 870) * 32768 := by
    rw [WEX.tableAddress_word]
    change boolWordToNat (wireValues (List.range' 855 15) s)+32768*(s 870).toNat =
      boolWordToNat (wireValues (List.range' 855 15) s)+(s 870).toNat*32768
    omega
  have hsel : (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
      signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
    else -constantPoint Q (coeffs ⟨signedTableAddress 32768 (windowRawDigit 0 s),
      signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)) =
      normalPoint coeffs Q (windowRawDigit 0 s) := by
    cases hb : s 870
    · have hlow : windowRawDigit 0 s < 32768 := by
        simp only [hb,Bool.toNat_false,Nat.zero_mul,Nat.add_zero] at hv
        omega
      simp only [hb,Bool.false_eq_true,if_false,normalPoint,if_pos hlow]
      apply congrArg (fun a : Fin 32768 => -constantPoint Q (coeffs a))
      apply Fin.ext
      simp only [signedTableAddress,if_pos hlow,Fin.val_mk]
      rw [Nat.mod_eq_of_lt (by omega)]
    · have hhigh : ¬windowRawDigit 0 s < 32768 := by
        simp only [hb,Bool.toNat_true,Nat.one_mul] at hv
        omega
      have hval : windowRawDigit 0 s - 32768 < 32768 := by
        have := windowRawDigit_bound 0 s
        omega
      simp only [hb,if_true,normalPoint,if_neg hhigh]
      apply congrArg (fun a : Fin 32768 => constantPoint Q (coeffs a))
      apply Fin.ext
      simp only [signedTableAddress,if_neg hhigh,Fin.val_mk]
      rw [Nat.mod_eq_of_lt hval]
  rw [PathShare.stateH_correct coeffs Q s hs P hP,PathShare.readyH_active s hs]
  rw [if_pos (show true=true from rfl)]
  exact congrArg (fun R : Point => pointWrite (P+R) s) hsel

theorem normal_assigned_valid (root : BasisState) (hs : FirstWindowInput root)
    (P : Point) (input : List Bool) :
    PathShare.readyH (phaseWordState streamAddress input (pointWrite P root)) ∧
      ∃ A,pointStateCoordinates (phaseWordState streamAddress input (pointWrite P root))=fig14PointEncoding A := by
  refine ⟨phaseWordState_preserves PathShare.readyH streamAddress PathShare.readyH_address
    input _ (PathShare.readyH_first root hs P),P,?_⟩
  rw [phaseWordState_pointWrite _ (by decide),pointWrite_coordinates]

theorem normal_pointRule (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q=0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root) :
    PointRule root (normalModel coeffs Q hQ hn) := by
  intro prior output P
  have hc : Clean streamAddress (pointWrite P root) := by
    intro v hv
    rw [pointWrite_frame _ _ _ ((show ∀ v ∈ streamAddress,v ∉ pointLogicalWires by decide) v hv)]
    exact hz v hv
  have hcoords (input : List Bool) :
      pointStateCoordinates (phaseWordState streamAddress input (pointWrite P root)) = fig14PointEncoding P := by
    rw [phaseWordState_pointWrite _ (by decide),pointWrite_coordinates]
  have hword (input : List Bool) (hi : input.length=streamAddress.length) :
      streamAddress.map (PathShare.stateH coeffs Q (phaseWordState streamAddress input (pointWrite P root))) = input := by
    rw [normal_correct coeffs Q _ (normal_assigned_valid root hs P input).1 P (hcoords input)]
    have hf : streamAddress.map (pointWrite
        (P+normalPoint coeffs Q (windowRawDigit 0 (phaseWordState streamAddress input (pointWrite P root))))
        (phaseWordState streamAddress input (pointWrite P root))) =
        streamAddress.map (phaseWordState streamAddress input (pointWrite P root)) := by
      apply List.map_congr_left
      intro v hv
      exact pointWrite_frame _ _ _ ((show ∀ v ∈ streamAddress,v ∉ pointLogicalWires by decide) v hv)
    rw [hf]
    exact phaseWordState_word _ (by decide) input hi _
  simp only [WindowModel.step,normalModel,normal,List.reverse_reverse,LinearMap.comp_apply,List.length_reverse]
  rw [window_branch_uniform .inverse streamAddress (by decide) (PathShare.stateH coeffs Q)
    prior output _ hc (fun input hi => hword input ((fourierOutcomes_mem _ _).mp hi))]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ))^streamAddress.length) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  have hr : windowRawDigit 0 (phaseWordState streamAddress input (pointWrite P root)) = boolWordToNat input := by
    exact assigned_window_digit input ((fourierOutcomes_mem _ _).mp hi) _
  rw [normal_correct coeffs Q _ (normal_assigned_valid root hs P input).1 P (hcoords input),hr,
    clear_assigned_point _ input (pointWrite P root) hc (by decide),pointWrite_overwrite]

theorem normal_prepared (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q=0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (root : BasisState) (hs : FirstWindowInput root) (hz : Clean streamAddress root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (normalModel coeffs Q hQ hn).valid
      (Quantum.run ((normalModel coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ) := by
  simp only [normalModel,normal,List.reverse_reverse]
  refine Support.linear (pointFamily root) (normalModel coeffs Q hQ hn).valid
    (Quantum.run (streamAddress.map Gate.H)) ?_ ψ hψ
  intro s hs'
  obtain ⟨P,rfl⟩ := hs'
  have hc : Clean streamAddress (pointWrite P root) := by
    intro v hv
    rw [pointWrite_frame _ _ _ ((show ∀ v ∈ streamAddress,v ∉ pointLogicalWires by decide) v hv)]
    exact hz v hv
  rw [phaseHadamards_uniform _ (by decide) _ hc]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact supportedOn_ket _ _ (normal_assigned_valid root hs P input)

end
end ShorECDLP.Entrant.Width16Actual


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem positivePoint_eq (Q : Point) (w : Digit) (a : Nat) :
    positivePoint Q w a = (2*a+1) • ((halfOrder*2^w.exponent) • w.base Q) := by
  unfold Width16Schedule.positivePoint Single.oddScalar
  rw [Nat.mul_assoc,Nat.mul_comm (2^w.exponent) halfOrder,mul_smul]

theorem signed_magnitude (P : Point) (half v : Nat) (_hh : 0<half) (hv : v<2*half) :
    (if v<half then -((2*((half-1-v)%half)+1) • P)
      else (2*((v-half)%half)+1) • P) =
      (2*(v:Int)-2*(half:Int)+1) • P := by
  rw [← signedTableOdd_value half v]
  unfold signedTableOdd signedTableAddress
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [neg_smul,natCast_zsmul]
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [natCast_zsmul]

theorem selected_point (Q : Point) (w : Digit) (v : Nat) (hv : v<2^w.width) :
    (if v<2^(w.width-1) then -positivePoint Q w ((2^(w.width-1)-1-v)%2^(w.width-1))
      else positivePoint Q w ((v-2^(w.width-1))%2^(w.width-1))) =
      Width16Schedule.increment (w.base Q) w.width w.exponent v := by
  simp only [positivePoint_eq]
  have hp : 2^w.width=2*2^(w.width-1) := by rcases width_cases w with h|h <;> rw [h] <;> decide
  rw [signed_magnitude _ _ _ (by positivity) (by omega)]
  unfold Width16Schedule.increment
  have he : (2:Int)^w.width=2*(2^(w.width-1):Nat) := by
    rcases width_cases w with h|h <;> rw [h] <;> norm_num
  rw [he]

def localCoefficients (w : Digit) : Fin (2^(w.width-1)) → PointCoeff :=
  fun a => signedCoefficients w a.val

theorem local_nonzero (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit)
    (a : Fin (2^(w.width-1))) : constantPoint Q (localCoefficients w a) ≠0 := by
  rw [localCoefficients,signedCoefficients_point Q hQ]
  exact positivePoint_ne_zero Q hQ hn w a.val a.isLt

end
end ShorECDLP.Entrant.Width16Actual


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] fourierOutcomes WideBank8.Signed17.program
local instance bodyInstance : Single.WindowBody := PathShare.bodyCF
local instance resourceInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0:Wire)∈resetWires; decide)
    (by change (1:Wire)∈resetWires; decide)

def interpretModel {n} {read : ConstantBit n→Bool} (m : WindowModel read)
    (point : Nat→Point) (bias : Point) : WindowModel read := {m with point:=point,bias:=bias}

theorem interpret_pointRule {n} {read : ConstantBit n→Bool} (m : WindowModel read)
    (point : Nat→Point) (bias : Point) (root : BasisState)
    (hm : PointRule root m) (hp : ∀ v, v<2^m.physical.wires.length → m.point v=point v) :
    PointRule root (interpretModel m point bias) := by
  intro prior output P
  change m.step prior output (ket (pointWrite P root)) = _
  rw [hm prior output P]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^m.physical.wires.length) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [hp _ (by simpa only [(fourierOutcomes_mem _ _).mp hi] using boolWordToNat_lt_pow_two input)]
  rfl

/-- Coefficients of a 17-wire body window (left or right axis). -/
def wideCoefficients (d : Digit) : Fin 65536 → PointCoeff := fun a => signedCoefficients d a.val

theorem wide_nonzero (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17)
    (a : Fin 65536) : constantPoint Q (wideCoefficients d a) ≠ 0 := by
  rw [wideCoefficients, Width16Schedule.signedCoefficients_point Q hQ]
  exact Width16Schedule.positivePoint_ne_zero Q hQ hn d a.val (by rw [hw]; exact a.isLt)

theorem wide_point (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17)
    (v : Nat) (hv : v<131072) :
    (WideBank8.Signed17.model (wideCoefficients d) Q hQ (wide_nonzero Q hQ hn d hw)).point v =
      Width16Schedule.increment (d.base Q) 17 d.exponent v := by
  change (if v<65536 then -constantPoint Q
      (wideCoefficients d (WideSigned.Geometry.rows .w16 (65535-v)))
    else constantPoint Q (wideCoefficients d (WideSigned.Geometry.rows .w16 (v-65536)))) = _
  simp only [wideCoefficients,WideSigned.Geometry.rows,WideSigned.Geometry.Width.bits,
    Width16Schedule.signedCoefficients_point Q hQ]
  have h := selected_point Q d v (by rw [hw]; exact hv)
  rw [hw] at h
  exact h

theorem normal_point (Q : Point) (hQ : order•Q=0) (w : Digit) (hw : w.width=16)
    (v : Nat) (hv : v<65536) :
    normalPoint (fun a : Fin 32768 => Width16Schedule.signedCoefficients w a.val) Q v =
      Width16Schedule.increment (w.base Q) w.width w.exponent v := by
  simp only [normalPoint,Width16Schedule.signedCoefficients_point Q hQ]
  have h := selected_point Q w v (by simpa only [hw] using hv)
  simpa only [hw] using h

def wideRawModel (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17) :=
  interpretModel
    (WideBank8.Signed17.model (wideCoefficients d) Q hQ (wide_nonzero Q hQ hn d hw))
    (Width16Schedule.increment (d.base Q) 17 d.exponent)
    (offsetScalar 17 d.exponent • d.base Q)

def widePackedModel (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17) :=
  relabelModel TightSupport.compact (wideRawModel Q hQ hn d hw)

theorem normal_nonzero (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit) (hw : w.width=16)
    (a : Fin 32768) : constantPoint Q (Width16Schedule.signedCoefficients w a.val) ≠ 0 := by
  rw [Width16Schedule.signedCoefficients_point Q hQ]
  exact Width16Schedule.positivePoint_ne_zero Q hQ hn w a.val (by simpa only [hw] using a.isLt)

def localNormalModel (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit) (hw : w.width=16) :=
  interpretModel
    (normalModel (fun a : Fin 32768 => Width16Schedule.signedCoefficients w a.val) Q hQ
      (normal_nonzero Q hQ hn w hw))
    (Width16Schedule.increment (w.base Q) w.width w.exponent)
    (offsetScalar w.width w.exponent • w.base Q)

def signedModel (Q : Point) (hQ : order•Q=0) (hn : Q≠0) :
    Digit→WindowModel (readConstant Width16Schedule.coefficientAt Q)
  | .left17 j => reindexModel (wideCoefficients (.left17 j)) Width16Schedule.coefficientAt
      (row (.left17 j)) (fun a => (coefficientAt_row (.left17 j) a).symm) Q
      (widePackedModel Q hQ hn (.left17 j) rfl)
  | .right17 j => reindexModel (wideCoefficients (.right17 j)) Width16Schedule.coefficientAt
      (row (.right17 j)) (fun a => (coefficientAt_row (.right17 j) a).symm) Q
      (widePackedModel Q hQ hn (.right17 j) rfl)
  | .left16 j => reindexModel (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.left16 j) a.val)
      Width16Schedule.coefficientAt (row (.left16 j)) (fun a => (coefficientAt_row (.left16 j) a).symm) Q
      (localNormalModel Q hQ hn (.left16 j) rfl)
  | .right16 j => reindexModel (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.right16 j) a.val)
      Width16Schedule.coefficientAt (row (.right16 j)) (fun a => (coefficientAt_row (.right16 j) a).symm) Q
      (localNormalModel Q hQ hn (.right16 j) rfl)

def models (Q : Point) (hQ : order•Q=0) (hn : Q≠0) : ModelFrame implementation Q where
  headA := Width16Schedule.headAModel Q hQ hn
  headB := Width16Schedule.headBModel Q
  signed := signedModel Q hQ hn
  headA_physical := rfl
  headB_physical := rfl
  signed_physical := by intro w; cases w <;> rfl
  headA_point := fun _ => rfl
  headA_bias := rfl
  headB_point := fun _ => rfl
  headB_bias := rfl
  signed_point := by intro w v; cases w <;> rfl
  signed_bias := by intro w; cases w <;> rfl

theorem wide_raw_rule (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17) :
    PointRule initialRoot (wideRawModel Q hQ hn d hw) := by
  apply interpret_pointRule
  · exact WideBank8.Signed17.pointRule (wideCoefficients d) Q hQ
      (wide_nonzero Q hQ hn d hw) initialRoot initialRoot_input.1 (by
      intro v hv
      have hb := WideSigned.Body.bank_bounds .w16 v hv
      simp only [initialRoot,upd,zeroBasisState]
      split_ifs <;> dsimp only [Wire] at * <;> omega)
  · intro v hv
    exact wide_point Q hQ hn d hw v hv

theorem inverse_pointFrame (P : Point) (s : BasisState) :
    relabelBasis TightSupport.compact.symm (pointWrite P s) =
      pointWrite P (relabelBasis TightSupport.compact.symm s) := by
  have h := congrArg (relabelBasis TightSupport.compact.symm)
    (TightSupport.compact_pointWrite P (relabelBasis TightSupport.compact.symm s))
  have hr : relabelBasis TightSupport.compact (relabelBasis TightSupport.compact.symm s)=s := by
    simpa only [Equiv.symm_symm] using relabelBasis_symm TightSupport.compact.symm s
  simpa only [relabelBasis_symm,hr] using h.symm

theorem signed_rule (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit) :
    PointRule initialRoot (signedModel Q hQ hn w) := by
  cases w with
  | left17 j =>
    change PointRule initialRoot (widePackedModel Q hQ hn (.left17 j) rfl)
    exact relabelModel_pointRule _ _ TightSupport.compact_pointWrite
      TightSupport.compact_active (wide_raw_rule Q hQ hn (.left17 j) rfl)
  | right17 j =>
    change PointRule initialRoot (widePackedModel Q hQ hn (.right17 j) rfl)
    exact relabelModel_pointRule _ _ TightSupport.compact_pointWrite
      TightSupport.compact_active (wide_raw_rule Q hQ hn (.right17 j) rfl)
  | left16 j =>
    change PointRule initialRoot (localNormalModel Q hQ hn (.left16 j) rfl)
    apply interpret_pointRule
    · exact normal_pointRule (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.left16 j) a.val)
        Q hQ (normal_nonzero Q hQ hn (.left16 j) rfl) initialRoot initialRoot_input initialRoot_clean
    · intro v hv
      exact normal_point Q hQ (.left16 j) rfl v hv
  | right16 j =>
    change PointRule initialRoot (localNormalModel Q hQ hn (.right16 j) rfl)
    apply interpret_pointRule
    · exact normal_pointRule (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.right16 j) a.val)
        Q hQ (normal_nonzero Q hQ hn (.right16 j) rfl) initialRoot initialRoot_input initialRoot_clean
    · intro v hv
      exact normal_point Q hQ (.right16 j) rfl v hv

theorem wide_raw_prepared (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (d : Digit) (hw : d.width=17)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (wideRawModel Q hQ hn d hw).valid
      (Quantum.run ((wideRawModel Q hQ hn d hw).physical.wires.reverse.map Gate.H) ψ) := by
  have hfamily : SupportedOn (pointFamily (pointWrite 0 initialRoot)) ψ := by
    intro s hs
    obtain ⟨P,hP⟩ := hψ s hs
    exact ⟨P,by rw [pointWrite_overwrite]; exact hP⟩
  exact WideBank8.Signed17.prepared (wideCoefficients d) Q hQ
    (wide_nonzero Q hQ hn d hw) (pointWrite 0 initialRoot)
    (WEX.windowReady_first initialRoot initialRoot_input 0)
    (by
      intro v hv
      rw [pointWrite_frame _ _ _ (WideSigned.Body.bank_not_point .w16 v hv)]
      have hb := WideSigned.Body.bank_bounds .w16 v hv
      simp only [initialRoot,upd,zeroBasisState]
      split_ifs <;> dsimp only [Wire] at * <;> omega)
    ψ hfamily

theorem signed_prepared (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (signedModel Q hQ hn w).valid
      (Quantum.run ((signedModel Q hQ hn w).physical.wires.reverse.map Gate.H) ψ) := by
  cases w with
  | left17 j =>
    exact relabelModel_prepared _ _ inverse_pointFrame TightSupport.compact_active
      (wide_raw_prepared Q hQ hn (.left17 j) rfl) ψ hψ
  | right17 j =>
    exact relabelModel_prepared _ _ inverse_pointFrame TightSupport.compact_active
      (wide_raw_prepared Q hQ hn (.right17 j) rfl) ψ hψ
  | left16 j =>
    exact normal_prepared (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.left16 j) a.val)
      Q hQ (normal_nonzero Q hQ hn (.left16 j) rfl) initialRoot initialRoot_input initialRoot_clean ψ hψ
  | right16 j =>
    exact normal_prepared (fun a : Fin 32768 => Width16Schedule.signedCoefficients (.right16 j) a.val)
      Q hQ (normal_nonzero Q hQ hn (.right16 j) rfl) initialRoot initialRoot_input initialRoot_clean ψ hψ

theorem signed_preserves (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (w : Digit)
    (prior bits : List Bool) (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (pointFamily initialRoot) ((signedModel Q hQ hn w).step prior bits ψ) := by
  refine Support.linear (pointFamily initialRoot) (pointFamily initialRoot)
    ((signedModel Q hQ hn w).step prior bits) ?_ ψ hψ
  intro s hs
  obtain ⟨P,rfl⟩ := hs
  rw [signed_rule Q hQ hn w prior bits P]
  apply Support.smul
  apply Support.list_sum
  intro input hi
  exact Support.smul _ (supportedOn_ket _ _ ⟨_,rfl⟩)

theorem ready_signed (Q : Point) (hQ : order•Q=0) (hn : Q≠0) (ws : List Digit)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    Ready (ws.map (signedModel Q hQ hn)) ψ := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨signed_prepared Q hQ hn w ψ hψ,fun prior bits=>
      ih _ (signed_preserves Q hQ hn w prior bits ψ hψ)⟩

theorem ready_models (Q : Point) (hQ : order•Q=0) (hn : Q≠0) :
    Ready ((models Q hQ hn).headA :: (models Q hQ hn).headB ::
      (leftDigits.map (models Q hQ hn).signed ++ rightDigits.map (models Q hQ hn).signed))
      (ket initialRoot) := by
  rw [← List.map_append]
  constructor
  · change SupportedOn SelectSchedule18.Input
      (Quantum.run (headLWires.reverse.reverse.map Gate.H) (ket initialRoot))
    rw [List.reverse_reverse]
    exact SelectSchedule18.input_prepare _ headL_sub _
      (supportedOn_ket _ _ (SelectSchedule18.input_of_strong initialRoot initialRoot_input))
  · intro prior bits
    constructor
    · intro s _
      trivial
    · intro prior' bits'
      apply ready_signed Q hQ hn (leftDigits++rightDigits)
      change SupportedOn (pointFamily initialRoot)
        ((Width16Schedule.headBModel Q).step prior' bits'
          ((Width16Schedule.headAModel Q hQ hn).step prior bits (ket initialRoot)))
      rw [Width16Schedule.joint_first_step Q hQ hn prior bits prior' bits' initialRoot
        initialRoot_input initialRoot_clean]
      apply Support.smul
      apply Support.list_sum
      intro inL hinL
      apply Support.list_sum
      intro inR hinR
      exact Support.smul _ (supportedOn_ket _ _ ⟨_,rfl⟩)

end
end ShorECDLP.Entrant.Width16Actual

namespace ShorECDLP.Entrant.Width16Readout
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule RoundedReadout
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
local instance bodyInstance : Single.WindowBody := PathShare.bodyCF
local instance ledgerInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0:Wire)∈resetWires; decide)
    (by change (1:Wire)∈resetWires; decide)
variable (impl : Implementation)

abbrev reset := resetWires
abbrev startCursor := cursor impl reset

def fineEvent (accept : Nat→Nat→Bool) (history : List Bool) : Bool :=
  pairAccept (trialPositions impl.records17 impl.records16).left.toList
    (trialPositions impl.records17 impl.records16).right.toList accept history

theorem model_left (Q : Point) (m : ModelFrame impl Q) :
    (leftDigits.map m.signed).map WindowModel.physical = Width16Schedule.leftBodies impl := by
  simp only [List.map_map,Function.comp_def,m.signed_physical,Width16Schedule.leftBodies]

theorem model_right (Q : Point) (m : ModelFrame impl Q) :
    (rightDigits.map m.signed).map WindowModel.physical = Width16Schedule.rightBodies impl := by
  simp only [List.map_map,Function.comp_def,m.signed_physical,Width16Schedule.rightBodies]

theorem event_mass (Q : Point) (hQ : order•Q=0) (m : ModelFrame impl Q)
    (hfirst : ∀ bA ∈ fourierOutcomes (modelDigit m.headA).width,
      ∀ bB ∈ fourierOutcomes (modelDigit m.headB).width,
        m.headB.step List.nil bB (m.headA.step List.nil bA (ket initialRoot)) =
          jointClosedForm (modelDigit m.headA) (modelDigit m.headB) bA bB initialRoot)
    (pointRules : ∀ w∈leftDigits++rightDigits,PointRule initialRoot (m.signed w))
    (ready : Ready (m.headA :: m.headB :: ((leftDigits.map m.signed) ++ (rightDigits.map m.signed)))
      (ket initialRoot))
    (J : Instrument) (hJ : ∀ ψ,J.bornMass ψ=normSq ψ) (accept : Nat→Nat→Bool) :
    Instrument.bornMass
      (((mixedData impl.headA impl.headB (Width16Schedule.leftBodies impl)
        (Width16Schedule.rightBodies impl) (readConstant Width16Schedule.coefficientAt Q)
        0 Fin.elim0).seq J).filter (fun b => fineEvent impl accept b.history)) (ket initialRoot) =
      idealEventMass Q initialRoot 261 208 accept := by
  have hm := conditional_event_mass impl Q hQ m initialRoot (ket initialRoot) hfirst
    pointRules ready 0 Fin.elim0 J hJ accept
  rw [selectedMixed_fixed_filter] at hm
  rw [m.headA_physical, m.headB_physical, model_left impl Q m, model_right impl Q m] at hm
  have hA : axisPositions [impl.headA] 0 = positions [(132606,10)] 0 := by
    simp [Single.axisPositions, impl.headA_count, impl.headA_width]
  have hB : axisPositions [impl.headB] (mixS1 impl.headA 0) = positions [(0,8)] 132616 := by
    simp [Single.axisPositions, impl.headB_count, impl.headB_width, mixS1, Width16Schedule.headA_axisCount]
  have hL : axisPositions (Width16Schedule.leftBodies impl) (mixS2 impl.headA impl.headB 0) =
      positions (Width16Schedule.leftMetadata impl.records17 impl.records16) 132624 := by
    rw [Single.axisPositions, Width16Schedule.left_metadata]
    simp [mixS2, mixS1, Width16Schedule.headA_axisCount, Width16Schedule.headB_axisCount]
  have hR : axisPositions (Width16Schedule.rightBodies impl)
      (mixS3 impl.headA impl.headB (Width16Schedule.leftBodies impl) 0) =
      positions (Width16Schedule.rightMetadata impl.records17 impl.records16)
        (132624 + (11*impl.records17 + 4*impl.records16 + 251)) := by
    rw [Single.axisPositions, Width16Schedule.right_metadata]
    simp only [mixS3, mixS2, mixS1, Width16Schedule.headA_axisCount, Width16Schedule.headB_axisCount,
      Width16Schedule.left_count, Nat.zero_add]
  rw [hA, hB, hL, hR] at hm
  simpa only [fineEvent,Width16Schedule.trialPositions,Width16Schedule.leftPositions,
    Width16Schedule.rightPositions,Vector.toList_mk,List.toList_toArray] using hm

theorem program_run_data (read : ConstantBit 1769472→Bool) :
    ((Width16Schedule.program impl reset).instantiate read Fin.elim0).run =
      ((mixedData impl.headA impl.headB (Width16Schedule.leftBodies impl)
        (Width16Schedule.rightBodies impl) read 0 Fin.elim0).seq terminalInstrument).map
        (fun b => ({history := List.nil,kraus := Quantum.run [.X 836]}:InstrumentBranch).seq b) := by
  unfold Width16Schedule.program
  have hh : mixS4 impl.headA impl.headB (Width16Schedule.leftBodies impl)
      (Width16Schedule.rightBodies impl) 0 + reset.length = cursor impl reset := by
    rw [Width16Schedule.mixS4_value]
    unfold cursor
    omega
  simpa only [mixedData,mixProgram,terminalInstrument,bodyInstance,PathShare.bodyCF,reset] using
    framed_reset_run (mixHead impl.headA 0)
      (mixTail impl.headA impl.headB (Width16Schedule.leftBodies impl) (Width16Schedule.rightBodies impl) 0)
      (resetProgram 1769472 (mixS4 impl.headA impl.headB (Width16Schedule.leftBodies impl)
        (Width16Schedule.rightBodies impl) 0) reset)
      hh read Fin.elim0 (measureResetWithCorrection reset (fun _=>List.nil))
      (fun h => resetProgram_run _ _ _ read h)

theorem program_event_mass (Q : Point) (hQ : order•Q=0) (m : ModelFrame impl Q)
    (hfirst : ∀ bA ∈ fourierOutcomes (modelDigit m.headA).width,
      ∀ bB ∈ fourierOutcomes (modelDigit m.headB).width,
        m.headB.step List.nil bB (m.headA.step List.nil bA (ket initialRoot)) =
          jointClosedForm (modelDigit m.headA) (modelDigit m.headB) bA bB initialRoot)
    (pointRules : ∀ w∈leftDigits++rightDigits,PointRule initialRoot (m.signed w))
    (ready : Ready (m.headA :: m.headB :: ((leftDigits.map m.signed) ++ (rightDigits.map m.signed)))
      (ket initialRoot))
    (accept : Nat→Nat→Bool) :
    Instrument.bornMass (((Width16Schedule.program impl reset).instantiate
      (readConstant Width16Schedule.coefficientAt Q) Fin.elim0).run.filter
      (fun b => fineEvent impl accept b.history)) (ket zeroBasisState) =
      idealEventMass Q initialRoot 261 208 accept := by
  rw [program_run_data,prefix_filter_mass _ ([Gate.X 836]) (fineEvent impl accept) (ket zeroBasisState)]
  have hs : Quantum.run [.X 836] (ket zeroBasisState)=ket initialRoot := by
    simp [Quantum.run,applyGate_ket,onKet,initialRoot,zeroBasisState]
  rw [hs]
  exact event_mass impl Q hQ m hfirst pointRules ready terminalInstrument terminalInstrument_mass accept

theorem program_clean (read : ConstantBit 1769472→Bool) (b : InstrumentBranch)
    (hb : b∈((Width16Schedule.program impl reset).instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [program_run_data] at hb
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hb
  obtain ⟨a,_,hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
  simp only [terminalInstrument,AdaptiveCircuit.run] at hc
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean bodyInstance.reset ledgerInstance.reset_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 ledgerInstance.reset_zero,h s hs 1 ledgerInstance.reset_one⟩

theorem verified_of_reads (ps : Vector Nat 208) (hps : ps∈Readout56.rightWords56 (fineBits impl reset))
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist (trialPositions impl.records17 impl.records16).left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d:ZMod order)∈fixedCandidates SinAverage261.params261 a b) :
    (verifiedCandidate (Width16Schedule.layout impl reset) Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d:ZMod order),?_,?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨positionsFor impl.records17 impl.records16 ps,List.mem_map.mpr ⟨ps,hps,rfl⟩,?_⟩
    simpa only [decodeTrial,trialCandidates,positionsFor,Width16Schedule.layout,hl,hr,
      fixedCandidates_take,Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq,ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order]; exact Nat.mod_mod _ _)

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q=d•G)
    (read : ConstantBit 1769472→Bool) (history : Fin (startCursor impl)→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : fineEvent impl (SinAverage261.pairRecovered261 d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈((readout impl reset).instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate (Width16Schedule.layout impl reset) Q (List.ofFn history++b.history)).isSome := by
  have hr := NeighborReadout.input_read (fineBits impl reset) history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩ := Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩ := of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩ := Readout56.suffix56_reads 1769472 (startCursor impl) (fineBits impl reset)
    read history ψ hψ b (by simpa only [readout,castFinish_instantiate] using hb) hn
    ((i.val:ℤ)-28) (by have h:=i.isLt;omega)
  apply verified_of_reads impl ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h := left_position_bound impl.records17 impl.records16 j hj
    have hh : 132875+11*impl.records17+4*impl.records16 ≤ startCursor impl := by
      unfold startCursor cursor
      omega
    simpa only [List.length_ofFn] using h.trans_le hh

theorem strong_success (Q : Point) (d : Nat) (hd : Q=d•G)
    (hQ : order•Q=0) (m : ModelFrame impl Q)
    (hfirst : ∀ bA ∈ fourierOutcomes (modelDigit m.headA).width,
      ∀ bB ∈ fourierOutcomes (modelDigit m.headB).width,
        m.headB.step List.nil bB (m.headA.step List.nil bA (ket initialRoot)) =
          jointClosedForm (modelDigit m.headA) (modelDigit m.headB) bA bB initialRoot)
    (pointRules : ∀ w∈leftDigits++rightDigits,PointRule initialRoot (m.signed w))
    (ready : Ready (m.headA :: m.headB :: ((leftDigits.map m.signed) ++ (rightDigits.map m.signed)))
      (ket initialRoot)) :
    (990038025/1000000000:ℝ) ≤ Instrument.bornMass
      (((fullProgram impl reset).instantiate (readConstant Width16Schedule.coefficientAt Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate (Width16Schedule.layout impl reset) Q b.history).isSome)) (ket zeroBasisState) := by
  have hneighbor : (990038025/1000000000:ℝ) ≤ Instrument.bornMass
      (((Width16Schedule.program impl reset).instantiate (readConstant Width16Schedule.coefficientAt Q) Fin.elim0).run.filter
        (fun b => fineEvent impl (SinAverage261.pairRecovered261 d) b.history)) (ket zeroBasisState) := by
    rw [program_event_mass impl Q hQ m hfirst pointRules ready,idealEventMass_distribution Q d hd]
    exact PhaseTrimHeadroom.improved_pair_success d
  apply hneighbor.trans
  unfold fullProgram
  rw [Single.append_run_history]
  apply Rounded.appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      ((readout impl reset).instantiate_wellFormed _ _ (readout_wellFormed impl reset)) _
  · intro a ha hf b hb hne
    have hlen : a.history.length=startCursor impl := by
      have h := straight_history_length (Width16Schedule.program impl reset)
        (readConstant Width16Schedule.coefficientAt Q) Fin.elim0 a ha
      simpa only [startCursor,Nat.zero_add,Nat.sub_zero] using h
    have hh : List.ofFn (Single.historyAfter (startCursor impl) Fin.elim0 a.history)=a.history := by
      simpa only [List.ofFn_zero,List.nil_append] using Single.historyAfter_list Fin.elim0 a.history
        (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept impl Q d hd (readConstant Width16Schedule.coefficientAt Q)
      (Single.historyAfter (startCursor impl) Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean impl _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh,InstrumentBranch.seq] using h

end
end ShorECDLP.Entrant.Width16Readout


namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule ConditionalCatalyst
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] PathShare.narrowCF15 WideBank8.Signed17.program
  WideBank8.Row17.program Single.axis resetProgram
attribute [local instance] bodyInstance resourceInstance

def reset : List Wire := resetWires
abbrev impl := implementation
abbrev rawProgram := Width16Schedule.fullProgram impl reset
abbrev rawEntry := Width16Schedule.sourceEntry impl reset
abbrev rawLayout := Width16Schedule.layout impl reset

/-- Every window of the program is one of the two head banks or a signed body window. -/
def IsWin (w : Window 1769472) : Prop :=
  w = Width16Schedule.headA ∨ w = Width16Schedule.headB ∨ ∃ d, w = signed d

theorem isWin_headA : IsWin impl.headA := Or.inl rfl
theorem isWin_headB : IsWin impl.headB := Or.inr (Or.inl rfl)
theorem isWin_left (w : Window 1769472) (hw : w ∈ (Width16Schedule.leftBodies impl)) : IsWin w := by
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hw
  exact Or.inr (Or.inr ⟨d,rfl⟩)
theorem isWin_right (w : Window 1769472) (hw : w ∈ (Width16Schedule.rightBodies impl)) : IsWin w := by
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hw
  exact Or.inr (Or.inr ⟨d,rfl⟩)

theorem signed_slots (w : Digit) (start : Nat) : ((signed w).program start).gateSlots ≤ 3000000000 := by
  cases w with
  | left17 j | right17 j =>
    change (reindexStraight _ (relabelStraight _ (WideBank8.Signed17.program start))).gateSlots ≤ _
    rw [reindexStraight_gateSlots,relabelStraight_slots]
    exact (WideBank8.Signed17.slots start).trans (by decide)
  | left16 j | right16 j =>
    change (reindexStraight _ (WEXFast.W15H.compactProgram start)).gateSlots ≤ _
    rw [reindexStraight_gateSlots, WEXFast.W15H.compactProgram, relabelStraight_slots]
    exact (WEXFast.W15H.fastBodyProgram_slots_upper start).trans (by decide)

theorem win_wellFormed (w : Window 1769472) (hw : IsWin w) (start : Nat) :
    (w.program start).WellFormed := by
  rcases hw with rfl|rfl|⟨d,rfl⟩
  · exact prepareOuterBank_wellFormed _ _ (RootPass.window_wellFormed Width16Schedule.firstRow start)
  · exact prepareOuterBank_wellFormed _ _ trivial
  · exact signed_wellFormed d start

theorem win_slots (w : Window 1769472) (hw : IsWin w) (start : Nat) :
    (w.program start).gateSlots ≤ 3000000000 := by
  rcases hw with rfl|rfl|⟨d,rfl⟩
  · change (prepareOuterBank Width16Schedule.headRWires
      (Width16Schedule.firstWindow.program start)).gateSlots ≤ _
    rw [prepareOuterBank_slots]
    have h : (Width16Schedule.firstWindow.program start).gateSlots ≤ 1000000000 :=
      RootPass.window_slots Width16Schedule.firstRow start
    have hl : Width16Schedule.headRWires.length = 8 := Width16Schedule.headR_length
    omega
  · change (prepareOuterBank Width16Schedule.headRWires.reverse
      (Straight.done : Straight 1769472 start start)).gateSlots ≤ _
    rw [prepareOuterBank_slots]
    have hl : Width16Schedule.headRWires.length = 8 := Width16Schedule.headR_length
    simp only [List.length_reverse, hl]
    change 8 + 0 ≤ _
    omega
  · exact signed_slots d start

theorem bits_range : ∀ v ∈ SelectSchedule18.bits, v ∈ List.range 1618 := by decide

theorem win_bank_support (w : Window 1769472) (hw : IsWin w) : w.wires ⊆ List.range 1618 := by
  rcases hw with rfl|rfl|⟨d,rfl⟩
  · intro v hv
    exact bits_range v (Width16Schedule.headL_sub v (List.mem_reverse.mp hv))
  · intro v hv
    exact bits_range v (by
      rw [← Width16Schedule.head_bits]
      exact List.mem_append_left _ (List.mem_reverse.mp hv))
  · cases d with
    | left17 j | right17 j =>
      change (WideSigned.Body.logicalBank .w16).reverse.map TightSupport.compact ⊆ _
      decide
    | left16 j | right16 j => change streamAddress.reverse ⊆ _; decide

theorem win_support (w : Window 1769472) (hw : IsWin w) (start : Nat)
    (read : ConstantBit 1769472→Bool) (history : Fin start→Bool) :
    ((w.program start).instantiate read history).wires ⊆ List.range 1618 := by
  rcases hw with rfl|rfl|⟨d,rfl⟩
  · change ((prepareOuterBank Width16Schedule.headRWires
      (Width16Schedule.firstWindow.program start)).instantiate read history).wires ⊆ _
    apply prepareOuterBank_support
    · intro v hv
      exact bits_range v (Width16Schedule.headR_sub' v hv)
    · exact (straight_instantiate_support _ read history).trans
        ((RootPass.window_support Width16Schedule.firstRow start).trans
          (First18.support_range.trans (List.range_subset.mpr (by decide))))
  · change ((prepareOuterBank Width16Schedule.headRWires.reverse
      (Straight.done : Straight 1769472 start start)).instantiate read history).wires ⊆ _
    apply prepareOuterBank_support
    · intro v hv
      exact bits_range v (Width16Schedule.headR_sub' v (List.mem_reverse.mp hv))
    · intro v hv
      simp [Straight.instantiate, AdaptiveCircuit.wires] at hv
  · apply (straight_instantiate_support _ read history).trans
    exact signed_support d start

theorem program_wellFormed : (Width16Schedule.program impl reset).WellFormed := by
  unfold Width16Schedule.program
  apply framed_wellFormed
  · exact axis_wellFormed ([impl.headA]) (fun w hw start => by
      rcases List.mem_singleton.mp hw with rfl; exact win_wellFormed _ isWin_headA start) _ _
  · unfold mixTail
    apply straight_append_wellFormed
    · exact axis_wellFormed ([impl.headB]) (fun w hw start => by
        rcases List.mem_singleton.mp hw with rfl; exact win_wellFormed _ isWin_headB start) _ _
    · apply straight_append_wellFormed
      · exact axis_wellFormed (Width16Schedule.leftBodies impl) (fun w hw start => win_wellFormed w (isWin_left w hw) start) _ _
      · exact axis_wellFormed (Width16Schedule.rightBodies impl) (fun w hw start => win_wellFormed w (isWin_right w hw) start) _ _
  · exact resetProgram_wellFormed _ _ _

theorem full_wellFormed : rawProgram.WellFormed :=
  straight_append_wellFormed _ _ program_wellFormed (Width16Schedule.readout_wellFormed impl reset)

theorem mix_slots_bound :
    (mixHead impl.headA 0).gateSlots +
      (mixTail impl.headA impl.headB (Width16Schedule.leftBodies impl)
        (Width16Schedule.rightBodies impl) 0).gateSlots ≤ 99998999998 := by
  have hA := axis_slots ([impl.headA]) 3000000000
    (fun w hw start => by rcases List.mem_singleton.mp hw with rfl; exact win_slots _ isWin_headA start)
    0 List.nil
  have hB := axis_slots ([impl.headB]) 3000000000
    (fun w hw start => by rcases List.mem_singleton.mp hw with rfl; exact win_slots _ isWin_headB start)
    (mixS1 impl.headA 0) List.nil
  have hL := axis_slots (Width16Schedule.leftBodies impl) 3000000000
    (fun w hw start => win_slots w (isWin_left w hw) start)
    (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0)
  have hR := axis_slots (Width16Schedule.rightBodies impl) 3000000000
    (fun w hw start => win_slots w (isWin_right w hw) start)
    (mixS3 impl.headA impl.headB (Width16Schedule.leftBodies impl) 0)
    (mixPriorR impl.headA impl.headB (Width16Schedule.leftBodies impl) 0)
  rw [Width16Schedule.mixPriorL_length] at hL
  rw [Width16Schedule.mixPriorR_length] at hR
  simp only [List.length_nil, List.map_cons, List.map_nil, impl.headA_count, impl.headA_width,
    impl.headB_count, impl.headB_width] at hA hB
  rw [Width16Schedule.left_metadata] at hL
  rw [Width16Schedule.right_metadata] at hR
  have hb : metadataSlots 3000000000 ([(132606,10)]) 0 + metadataSlots 3000000000 ([(0,8)]) 0 +
      metadataSlots 3000000000 (Width16Schedule.leftMetadata impl.records17 impl.records16) 10 +
      metadataSlots 3000000000 (Width16Schedule.rightMetadata impl.records17 impl.records16) 8 ≤
      99998999998 := by
    norm_num [Width16Schedule.leftMetadata, Width16Schedule.rightMetadata, metadataSlots, fourierSlots,
      List.replicate]
  rw [mixHead_slots, mixTail_slots]
  omega

theorem full_slots : rawProgram.gateSlots ≤ 100000000000 := by
  have hm := mix_slots_bound
  have hro : (Width16Schedule.readout impl reset).gateSlots = 122311 := by
    unfold Width16Schedule.readout
    rw [castFinish_gateSlots]
    exact Readout56.suffix56_slots _ _ _ _
  unfold rawProgram Width16Schedule.fullProgram Width16Schedule.program
  rw [Straight.gateSlots_append,framed_slots,resetProgram_gateSlots,hro]
  omega

theorem reset_range : reset ⊆ List.range 1618 := by
  intro w hw
  simp only [reset, resetWires, List.mem_append, List.mem_range, List.mem_singleton,
    List.mem_range'_1] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem full_support (read : ConstantBit 1769472→Bool) (history : Fin 0→Bool) :
    (rawProgram.instantiate read history).wires ⊆ List.range 1618 := by
  have hA := axis_support ([impl.headA]) (List.range 1618)
    (fun w hw => by rcases List.mem_singleton.mp hw with rfl; exact win_bank_support _ isWin_headA)
    (fun w hw start r h => by
      rcases List.mem_singleton.mp hw with rfl; exact win_support _ isWin_headA start r h)
    0 List.nil read history
  have hB (h : Fin (mixS1 impl.headA 0)→Bool) := axis_support ([impl.headB]) (List.range 1618)
    (fun w hw => by rcases List.mem_singleton.mp hw with rfl; exact win_bank_support _ isWin_headB)
    (fun w hw start r h' => by
      rcases List.mem_singleton.mp hw with rfl; exact win_support _ isWin_headB start r h')
    (mixS1 impl.headA 0) List.nil read h
  have hL (h : Fin (mixS2 impl.headA impl.headB 0)→Bool) := axis_support (Width16Schedule.leftBodies impl) (List.range 1618)
    (fun w hw => win_bank_support w (isWin_left w hw))
    (fun w hw start r h' => win_support w (isWin_left w hw) start r h')
    (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0) read h
  have hR (h : Fin (mixS3 impl.headA impl.headB (Width16Schedule.leftBodies impl) 0)→Bool) := axis_support (Width16Schedule.rightBodies impl) (List.range 1618)
    (fun w hw => win_bank_support w (isWin_right w hw))
    (fun w hw start r h' => win_support w (isWin_right w hw) start r h')
    (mixS3 impl.headA impl.headB (Width16Schedule.leftBodies impl) 0) (mixPriorR impl.headA impl.headB (Width16Schedule.leftBodies impl) 0) read h
  apply outer_append_support _ _ read history (List.range 1618) ?_ ?_
  · unfold Width16Schedule.program
    refine framed_support _ _ _ _ read history _ (by decide) hA ?_
      (fun h => resetProgram_support _ _ _ _ read h reset_range)
    intro h
    unfold mixTail
    exact outer_append_support _ _ read h (List.range 1618) (hB h)
      (fun h' => outer_append_support _ _ read h' (List.range 1618) (hL h') (fun h'' => hR h''))
  · intro h
    unfold Width16Schedule.readout
    rw [castFinish_instantiate]
    exact (Readout56.suffix56_support _ _ _ _ read h).trans (by decide)

theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n→Fin m)
    (ws : List Wire) (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1,ih hp.2⟩
  | recordGate i v g p ih => exact ⟨hp.1,ih hp.2⟩
  | measure w p ih => exact ⟨hp.1,ih hp.2⟩

theorem source_within : Within (List.range 1618) rawEntry.program := by
  unfold rawEntry Width16Schedule.sourceEntry Single.fixedEntry
  dsimp only
  exact within_reindex rawProgram _ (List.range 1618)
    (within_of_instantiate rawProgram (List.range 1618) full_support)

theorem added_le_weight {n s e} (p : Straight n s e) : 4*added p ≤ weight4 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp only [added,weight4,weightedLiteral] <;> omega
    | whenBit r b g => simp only [added,weight4]; omega
  | recordGate i b g p ih => simp only [added,weight4]; omega
  | measure w p ih => exact ih

theorem source_credit_bound : added rawEntry.program ≤ 62737992 := by
  have h := added_le_weight rawEntry.program
  have hw := Width16Schedule.fullProgram_weight impl reset
  have hc := credits
  have he : weight4 rawEntry.program = weight4 (Width16Schedule.fullProgram impl reset) := by
    unfold rawEntry Width16Schedule.sourceEntry Single.fixedEntry
    dsimp only
    exact weight4_reindex _ _
  rw [he] at h
  change impl.credit17 ≤ _ ∧ impl.credit16 ≤ _ at hc
  omega

theorem source_counts : rawEntry.finalCursor ≤ 50000000 ∧
    rawEntry.finalCursor+added rawEntry.program ≤ 544000000 ∧
    4*(rawEntry.program.gateSlots+18*added rawEntry.program)+2 ≤ officialLimits.gateSlots := by
  have hc := source_credit_bound
  have hs : rawEntry.program.gateSlots ≤ 100000000000 := by
    rw [rawEntry,Width16Schedule.sourceEntry,Single.fixedEntry_slots]
    exact full_slots
  have hm : rawEntry.finalCursor = 46493269 := by
    change 132606+19*1742494+8*1652126+469+resetWires.length+34946=46493269
    decide
  change _ ∧ _ ∧ _ ≤ 4000000000000000
  omega

end
end ShorECDLP.Entrant.Width16Actual

namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule ConditionalCatalyst
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] Single.axis WideBank8.Signed17.program WEXFast.W15H.compactProgram
  ConditionalCatalyst.fourEntry ConditionalCatalyst.compileEntry ConditionalCatalyst.compile
  AndGadget.lowerEntry AndGadget.lowerLayout
attribute [local instance] bodyInstance resourceInstance

theorem primitive_t_bound (g : Gate) : tCost g ≤ 7 := by cases g <;> simp only [tCost] <;> norm_num

theorem straight_t_bound {n s e} (p : Straight n s e) (read : ConstantBit n→Bool) (history : Fin s→Bool) :
    (p.instantiate read history).tCount ≤ 7*p.gateSlots := by
  induction p with
  | done => simp [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
  | gate g p ih =>
    cases g with
    | literal g =>
      have hg := primitive_t_bound g
      simpa only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
        ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
        Straight.gateSlots,Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
    | whenBit r v g =>
      have hg := primitive_t_bound g
      simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
        Straight.gateSlots]
      split
      · simpa only [ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
          Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
      · simpa only [ShorECDLP.tCount,List.map_nil,List.sum_nil,Nat.zero_add] using
          (ih history).trans (by omega)
  | recordGate i v g p ih =>
    have hg := primitive_t_bound g
    simp only [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
    split
    · simpa only [ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
        Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
    · simpa only [ShorECDLP.tCount,List.map_nil,List.sum_nil,Nat.zero_add] using
        (ih history).trans (by omega)
  | measure w p ih =>
    simp only [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
    exact max_le (ih _) (ih _)

theorem strong_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d•G) :
    (990038025/1000000000:ℝ) ≤ Instrument.bornMass
      ((rawEntry.instantiate Q).run.filter (fun b => (verifiedCandidate rawLayout Q b.history).isSome))
      (ket zeroBasisState) := by
  have hQ : order•Q=0 := by rw [hd,smul_comm order d,generator_nsmul_eq_zero,nsmul_zero]
  rw [rawEntry,sourceEntry,Single.fixedEntry_instantiate]
  exact Width16Readout.strong_success implementation Q d hd hQ (models Q hQ hn)
    (Width16Schedule.hfirst_concrete Q hQ hn initialRoot initialRoot_input initialRoot_clean)
    (fun w _ => signed_rule Q hQ hn w) (ready_models Q hQ hn)

def rawBounds : Bounds := ⟨1618,700000000000,50000000⟩

theorem raw_certificate : Certificate rawLimits rawLayout rawEntry rawBounds where
  gateBudget := by
    rw [rawEntry,sourceEntry,Single.fixedEntry_slots]
    exact full_slots.trans (by decide)
  recordBudget := source_counts.1.trans (by decide)
  tableBudget := by
    rw [rawEntry,sourceEntry,Single.fixedEntry_rows]
    decide
  candidateBudget := by
    change 56*(2*(order/2^208+2))≤56*(2^49+2)
    exact SinAverage261.decoder_budget261
  wellFormed := by
    rw [rawEntry,sourceEntry,Single.fixedEntry_wellFormed]
    exact full_wellFormed
  resources := by
    intro Q
    have hs := source_within.instantiate (readConstant rawEntry.coefficients.get Q) Fin.elim0
    have hq : (rawEntry.instantiate Q).qubitCount ≤ 1618 := by
      have ht : (rawEntry.instantiate Q).wires.dedup.toFinset ⊆ (List.range 1618).toFinset := by
        intro v hv
        exact List.mem_toFinset.mpr (hs (by simpa only [List.mem_toFinset,List.mem_dedup] using hv))
      have hc := (Finset.card_le_card ht).trans (List.toFinset_card_le _)
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc
    refine ⟨hq,?_,?_⟩
    · have ht := straight_t_bound rawEntry.program (readConstant rawEntry.coefficients.get Q) Fin.elim0
      have hb : rawEntry.program.gateSlots≤100000000000 := by
        rw [rawEntry,sourceEntry,Single.fixedEntry_slots]
        exact full_slots
      exact ht.trans (by change _≤700000000000;omega)
    · have hm := source_counts.1
      change (rawEntry.program.instantiate _ _).measurementCount≤50000000
      rw [Straight.measurementCount]
      omega
  success := by
    intro Q d hn hd
    exact (by norm_num : (99/100:ℝ)≤990038025/1000000000).trans (strong_success Q d hn hd)

def entry : StraightEntry := Width16Schedule.finalEntry implementation reset

def layout : DecodeLayout :=
  lowerLayout 1938 (trimNEntry rawEntry) rawLayout

def bounds : Bounds := ⟨1620,250907747,544000000⟩

theorem hcert : Certificate officialLimits
      (lowerLayout 1938 (trimNEntry (Width16Schedule.sourceEntry implementation reset))
        (Width16Schedule.layout implementation reset))
      (Width16Schedule.finalEntry implementation reset)
      ⟨1620,4*(132595+19*implementation.credit17+8*implementation.credit16)+10767,544000000⟩ :=
  Width16Schedule.conditional_certificate implementation reset (List.range 1618)
    rawBounds 1620 raw_certificate source_within strong_success (by decide) (by decide)
    source_counts.2.2 (source_counts.2.1.trans (by decide)) (by decide) source_counts.2.1

theorem tmodel_key : ∀ a b : Nat, a ≤ 2341681 → b ≤ 2251315 → 4*(132595+19*a+8*b)+10767 ≤ 250907747 := by
  intro a b ha hb
  omega

theorem tmodel_of {lim : Limits} {lay : DecodeLayout} {e : StraightEntry} {q t m : Nat}
    (h : Certificate lim lay e ⟨q,t,m⟩) (Q : Point) : (resources (e.instantiate Q)).tModel ≤ t :=
  (h.resources Q).2.1

theorem hres (Q : Point) : (resources (entry.instantiate Q)).qubits ≤ bounds.qubits ∧
    (resources (entry.instantiate Q)).tModel ≤ bounds.tModel ∧
    (resources (entry.instantiate Q)).measurements ≤ bounds.measurements :=
  ⟨(hcert.resources Q).1, (tmodel_of hcert Q).trans (tmodel_key _ _ credits.1 credits.2),
    (hcert.resources Q).2.2⟩

theorem certificate : Certificate officialLimits layout entry bounds :=
  Certificate.mk hcert.gateBudget hcert.recordBudget hcert.tableBudget hcert.candidateBudget
    hcert.wellFormed hres hcert.success

#print axioms certificate
end
end ShorECDLP.Entrant.Width16Actual

namespace ShorECDLP.Entrant.GeometricPhase
open Quantum Challenge Secp256k1 AndGadget WEXCredit WeightedPhase28 ApproximatePhase34
open Paper2607_13816 Paper2607_13816.ChallengeMigration Single Single.Distribution
noncomputable section
set_option Elab.async false
attribute [local irreducible] List.ofFn
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem sharp_unit : unit = (6283186/1000000:ℝ)/2^28 := rfl
theorem charge_balance (dir : PhaseDir) (w : Wire) (k : Nat) :
    charge (.P dir k w) + potential (k+1) = potential k := by
  by_cases hk : 27 < k
  · have h1 : max 28 k = k := max_eq_right (by omega)
    have h2 : max 28 (k+1) = k+1 := max_eq_right (by omega)
    simp only [charge,hk,if_true,potential,h1,h2,pow_succ]
    have hp : (2:ℝ)^k ≠ 0 := by positivity
    field_simp
    <;> ring
  · have h1 : max 28 k = 28 := max_eq_left (by omega)
    have h2 : max 28 (k+1) = 28 := max_eq_left (by omega)
    simp [charge,hk,potential,h1,h2]


theorem error_feedback_balance {n s e} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    errorCost (feedbackProgram dir w indices k p) + potential (k+indices.length) =
      potential k + errorCost p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram,add_comm]
  | cons i is ih =>
    have hi := ih (k+1)
    have hc := charge_balance dir w k
    have he : k + (i::is).length = (k+1)+is.length := by simp; omega
    simp only [feedbackProgram,errorCost,he]
    linarith

def account : Nat → Nat → ℝ
  | 0,_ => 0
  | n+1,p => unit - potential (p+2) + account n (p+1)

theorem account_append (a b p : Nat) :
    account (a+b) p = account a p + account b (p+a) := by
  induction a generalizing p with
  | zero => simp [account]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [account,ih]
    have he : p+(a+1) = (p+1)+a := by omega
    rw [he]
    ring

theorem error_fourier_exact (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    errorCost (fourierProgram n dir ws start prior) = account ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [fourierProgram,errorCost,account]
  | cons w ws ih =>
    simp only [fourierProgram,error_cast]
    have hi := ih (start+1) (Fin.last start :: prior.map Fin.castSucc)
    have hf := error_feedback_balance dir w prior 2 (.measure w
      (fourierProgram n dir ws (start+1) (Fin.last start :: prior.map Fin.castSucc)))
    have he : potential 2 = unit := by norm_num [potential,unit]
    simp only [errorCost,hi,he,List.length_cons,List.length_map] at hf hi
    rw [List.length_cons,account]
    have hn : 2+prior.length = prior.length+2 := by omega
    rw [hn] at hf
    linarith


theorem potential_half (k : Nat) (hk : 28 ≤ k) :
    2*potential (k+1) = potential k := by
  have h1 : max 28 k = k := max_eq_right hk
  have h2 : max 28 (k+1) = k+1 := max_eq_right (by omega)
  simp only [potential,h1,h2,pow_succ]
  ring

theorem account_geometric (n p : Nat) (hp : 26 ≤ p) :
    account n p + 2*potential (p+2) = (n:ℝ)*unit + 2*potential (p+n+2) := by
  induction n generalizing p with
  | zero => simp [account]
  | succ n ih =>
    have hi := ih (p+1) (by omega)
    have hh := potential_half (p+2) (by omega)
    have he : p+2+1 = p+1+2 := by omega
    rw [he] at hh
    have he2 : p+(n+1)+2 = (p+1)+n+2 := by omega
    simp only [account,Nat.cast_add,Nat.cast_one,he2]
    linarith

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem joint_error : account 261 0 + account 208 0 ≤ (1653/4:ℝ)*unit := by
  have hz : account 26 0 = 0 := by norm_num [account,potential,unit]
  rw [show 261=26+235 from rfl, show 208=26+182 from rfl,account_append,account_append,hz]
  norm_num only [zero_add]
  have h1 := account_geometric 235 26 (by decide)
  have h2 := account_geometric 182 26 (by decide)
  norm_num [potential,unit] at h1 h2 ⊢
  rw [show 263=255+8 from rfl,pow_add] at h1
  norm_num at h1
  linarith

theorem error_axis_exact {n} (ws : List (Window n))
    (hz : ∀ w ∈ ws, ∀ start, errorCost (w.program start) = 0)
    (start : Nat) (prior : List (Fin start)) :
    errorCost (axis ws start prior) =
      account ((ws.map (fun w => w.wires.length)).sum) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis,errorCost,account]
  | cons w ws ih =>
    simp only [axis,error_cast,error_append,error_prepare]
    rw [hz w (by simp) start,zero_add]
    have hf := error_fourier_exact n .inverse w.wires (start+w.count) (bankPrior w.count prior)
    have hi := ih (fun v hv s => hz v (List.mem_cons_of_mem w hv) s)
      (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior)
    rw [hf,hi]
    simp only [bankPrior,nextPrior,List.length_append,List.length_reverse,List.length_ofFn,List.length_map,List.map_cons,List.sum_cons,account_append]
    rw [Nat.add_comm w.wires.length prior.length]

theorem budget_floor : ((1653/4:ℝ) + 1211) * ((6283186/1000000:ℝ)/2^28) ≤
    990038025/1000000000 - 99/100 := by norm_num


open Width16Schedule ConditionalCatalyst
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
set_option linter.unusedSectionVars false
attribute [local irreducible] Width16Schedule.sourceEntry Width16Schedule.program
  Width16Schedule.fullProgram Width16Schedule.readout Single.fixedEntry Single.axis

theorem axis_width_sum {n} {ws : List (Single.Window n)} {widths : List Nat}
    (h : List.Forall₂ (fun w c => w.wires.length = c) ws widths) :
    (ws.map (fun w => w.wires.length)).sum = widths.sum := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons,List.sum_cons,head,ih]

theorem full_error (impl : Width16Schedule.Implementation) (reset : List Wire) :
    errorCost (Width16Schedule.fullProgram impl reset) ≤ (1653/4:ℝ)*unit := by
  have hA := error_axis_exact ([impl.headA])
    (by
      intro w hw start
      apply error_zero
      rcases List.mem_singleton.mp hw with rfl
      exact impl.headA_zero start) 0 List.nil
  have hB := error_axis_exact ([impl.headB])
    (by
      intro w hw start
      apply error_zero
      rcases List.mem_singleton.mp hw with rfl
      exact impl.headB_zero start) (mixS1 impl.headA 0) List.nil
  have hL := error_axis_exact (leftBodies impl)
    (by
      intro w hw start
      apply error_zero
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
      exact impl.signed_zero d start) (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0)
  have hR := error_axis_exact (rightBodies impl)
    (by
      intro w hw start
      apply error_zero
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
      exact impl.signed_zero d start)
    (mixS3 impl.headA impl.headB (leftBodies impl) 0) (mixPriorR impl.headA impl.headB (leftBodies impl) 0)
  rw [mixPriorL_length] at hL
  rw [mixPriorR_length] at hR
  rw [axis_width_sum (left_width_relation impl)] at hL
  rw [axis_width_sum (right_width_relation impl)] at hR
  have hsA : (([impl.headA]).map (fun w => w.wires.length)).sum = 10 := by
    simp [impl.headA_width]
  have hsB : (([impl.headB]).map (fun w => w.wires.length)).sum = 8 := by
    simp [impl.headB_width]
  rw [hsA, List.length_nil] at hA
  rw [hsB, List.length_nil] at hB
  have hlw : leftWidthsBody.sum = 251 := by simp [leftWidthsBody, List.replicate]
  have hrw : rightWidthsBody.sum = 200 := by simp [rightWidthsBody, List.replicate]
  rw [hlw] at hL
  rw [hrw] at hR
  have hz (n start : Nat) (ws : List Wire) : residue (resetProgram n start ws) = 0 := by
    induction ws generalizing start with
    | nil => simp [resetProgram,residue]
    | cons w ws ih => simpa [resetProgram,residue_cast,residue] using ih (start+1)
  have hreset : errorCost (resetProgram 1769472
      (mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0) reset) = 0 :=
    error_zero _ (hz _ _ _)
  have hro : errorCost (Width16Schedule.readout impl reset) = 0 := by
    apply error_zero
    simp only [Width16Schedule.readout,residue_cast,ApproximatePhase34.residue_suffix56]
  have hacc1 : account 261 0 = account 10 0 + account 251 10 := by
    have := account_append 10 251 0
    simpa using this
  have hacc2 : account 208 0 = account 8 0 + account 200 8 := by
    have := account_append 8 200 0
    simpa using this
  simp only [Width16Schedule.fullProgram,error_append,Width16Schedule.program,Single.framed,error_cast,errorCost,charge,zero_add,hreset,hro,mixHead,mixTail]
  linarith [joint_error]

theorem source_error (impl : Width16Schedule.Implementation) (reset : List Wire) :
    errorCost (Width16Schedule.sourceEntry impl reset).program ≤ (1653/4:ℝ)*unit := by
  unfold Width16Schedule.sourceEntry Single.fixedEntry
  rw [error_reindex]
  exact full_error impl reset

def entryTrim (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := entry.finalCursor
  program := Phase23Partial.trimN 86 entry.program
theorem trim_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds : Bounds) (ws : List ShorECDLP.Wire) (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (herror : AffineLoss.cost23 entry.program ≤ (1685/4:ℝ)*AffineLoss.unit23)
    (hstrong : ∀ (Q : ShorECDLP.Secp256k1.Point) (d : Nat), Q ≠ 0 →
      Q = d • ShorECDLP.Secp256k1.G →
      (990038025/1000000000 : ℝ) ≤ Instrument.bornMass ((entry.instantiate Q).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket ShorECDLP.zeroBasisState)) :
    Certificate limits layout (entryTrim entry) ⟨ws.length, bounds.tModel, entry.finalCursor⟩ where
  gateBudget := (Phase23Partial.trimN_slots 86 entry.program).trans cert.gateBudget
  recordBudget := cert.recordBudget
  tableBudget := cert.tableBudget
  candidateBudget := cert.candidateBudget
  wellFormed := Phase23Partial.trimN_wellFormed 86 entry.program cert.wellFormed
  resources := by
    intro Q
    have hsup := (Phase23Partial.trimN_within 86 entry.program ws hs).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((entryTrim entry).instantiate Q).wires.dedup.toFinset).card ≤ ws.length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le ws)
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((entryTrim entry).instantiate Q).qubitCount ≤ ws.length := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc
    refine ⟨hqc, ?_, ?_⟩
    · exact (Phase23Partial.trimN_t 86 entry.program (readConstant entry.coefficients.get Q) Fin.elim0).trans
          (cert.resources Q).2.1
    · have he := (entryTrim entry).program.measurementCount
        (readConstant entry.coefficients.get Q) Fin.elim0
      simpa only [Nat.add_zero] using he.le
  success := by
    intro Q d hn hd
    have hc := Phase23Partial.activeCost_nonneg 86 entry.program
    have he := Phase23Partial.activeCost_bound 86 entry.program
    have hbound : Phase23Partial.activeCost 86 entry.program ≤ ((1685/4:ℝ)+86)*AffineLoss.unit23 := by
      norm_num only [Nat.cast_ofNat] at he
      linarith
    have hb : Phase23Partial.activeCost 86 entry.program ≤ 1/5000 := by
      norm_num [AffineLoss.unit23] at hbound
      linarith
    let acc : (Fin entry.finalCursor → Bool) → Bool :=
      fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome
    have h := Phase23Partial.trimN_affine (readConstant entry.coefficients.get Q) entry.program 86 Fin.elim0
      (ket ShorECDLP.zeroBasisState) (fun h => !acc h) cert.wellFormed hb
    have hA := ComplementLoss.expectation_compl (readConstant entry.coefficients.get Q) entry.program Fin.elim0
      (ket ShorECDLP.zeroBasisState) acc cert.wellFormed
    have hB := ComplementLoss.expectation_compl (readConstant entry.coefficients.get Q) (Phase23Partial.trimN 86 entry.program) Fin.elim0
      (ket ShorECDLP.zeroBasisState) acc (Phase23Partial.trimN_wellFormed 86 entry.program cert.wellFormed)
    dsimp only [acc] at hA hB h
    rw [expectation_verified,normSq_ket] at hA hB
    rw [normSq_ket] at h
    have hS := hstrong Q d hn hd
    change 990038025/1000000000 ≤ Instrument.bornMass
      ((entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket ShorECDLP.zeroBasisState) at hS
    have hf : expectation (readConstant entry.coefficients.get Q) entry.program Fin.elim0
        (ket ShorECDLP.zeroBasisState)
        (fun h => !(verifiedCandidate layout Q (List.ofFn h)).isSome) ≤ 1-990038025/1000000000 := by
      linarith
    have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ 1+(10021/1000)*Phase23Partial.activeCost 86 entry.program by positivity)
    change 99/100 ≤ Instrument.bornMass
      (((Phase23Partial.trimN 86 entry.program).instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket ShorECDLP.zeroBasisState)
    norm_num [AffineLoss.unit23] at hbound
    nlinarith



theorem source_weight (impl : Implementation) (reset : List Wire) :
    weight4 (Phase23Partial.trimN 86 (sourceEntry impl reset).program) ≤
      4*(132595+19*impl.credit17+8*impl.credit16)+9259 := by
  have hw := fullProgram_weight impl reset
  have hr := AffineLoss.source_removed23 impl reset
  have hew : weight4 (sourceEntry impl reset).program = weight4 (fullProgram impl reset) := by
    unfold sourceEntry
    exact weight4_fixedEntry _ _
  have h := Phase23Partial.weight4_trimN 86 (sourceEntry impl reset).program
  rw [hew,Phase23Partial.source_spent86] at h
  omega


theorem compiled_coefficients (impl : Width16Schedule.Implementation) (reset : List Wire) :
    (ConditionalCatalyst.fourEntry 1938 1939 (entryTrim (sourceEntry impl reset))).coefficients =
      List.ofFn Width16Schedule.coefficientAt :=
  (four_coefficients 1938 1939 (entryTrim (sourceEntry impl reset))).trans
    (by simpa only [entryTrim] using Width16Schedule.source_coefficients impl reset)

def finalEntry (impl : Width16Schedule.Implementation) (reset : List Wire) : StraightEntry :=
  specializeEntry (ConditionalCatalyst.fourEntry 1938 1939 (entryTrim (sourceEntry impl reset)))
    (compiled_coefficients impl reset)
theorem conditional_certificate (impl : Implementation) (reset ws : List Wire)
    (baseBounds : Bounds) (qBound : Nat)
    (rawCertificate : Certificate rawLimits (Width16Schedule.layout impl reset) (sourceEntry impl reset) baseBounds)
    (support : Within ws (sourceEntry impl reset).program)
    (strongSuccess : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q=d•G →
      (990038025/1000000000 : ℝ) ≤ Instrument.bornMass (((sourceEntry impl reset).instantiate Q).run.filter
        (fun b => (verifiedCandidate (Width16Schedule.layout impl reset) Q b.history).isSome)) (ket zeroBasisState))
    (hq : (1938 : Wire) ∉ ws) (hy : (1939 : Wire) ∉ 1938::ws)
    (slotBudget : 4*((sourceEntry impl reset).program.gateSlots+
      18*added (sourceEntry impl reset).program)+2 ≤ officialLimits.gateSlots)
    (recordBudget : (sourceEntry impl reset).finalCursor+added (sourceEntry impl reset).program ≤ officialLimits.measurements)
    (qubitBudget : ws.length+2 ≤ qBound)
    (measurementBound : (sourceEntry impl reset).finalCursor+added (sourceEntry impl reset).program ≤ 544000000) :
    Certificate officialLimits
      (lowerLayout 1938 (entryTrim (sourceEntry impl reset)) (Width16Schedule.layout impl reset))
      (finalEntry impl reset) ⟨qBound,4*(132595+19*impl.credit17+8*impl.credit16)+9260,544000000⟩ := by
  have trimmed := trim_certificate rawLimits (Width16Schedule.layout impl reset) (sourceEntry impl reset) baseBounds ws
    rawCertificate support (AffineLoss.source_error impl reset) strongSuccess
  have hslots := Phase23Partial.trimN_slots 86 (sourceEntry impl reset).program
  have hw := source_weight impl reset
  unfold finalEntry
  apply specializeEntry_certificate _ (compiled_coefficients impl reset)
  apply ConditionalCatalyst.four_certificate rawLimits (Width16Schedule.layout impl reset)
    (entryTrim (sourceEntry impl reset)) _ _ 1938 1939 ws
    trimmed (Phase23Partial.trimN_within 86 (sourceEntry impl reset).program ws support) hq hy
  · change 4*((Phase23Partial.trimN 86 (sourceEntry impl reset).program).gateSlots+
      18*added (Phase23Partial.trimN 86 (sourceEntry impl reset).program))+2 ≤ officialLimits.gateSlots
    rw [Phase23Partial.trimN_added]
    omega
  · change (sourceEntry impl reset).finalCursor+added (Phase23Partial.trimN 86 (sourceEntry impl reset).program) ≤ officialLimits.measurements
    rw [Phase23Partial.trimN_added]
    exact recordBudget
  · exact qubitBudget
  · change weight4 (Phase23Partial.trimN 86 (sourceEntry impl reset).program)+1 ≤
      4*(132595+19*impl.credit17+8*impl.credit16)+9260
    omega
  · change (sourceEntry impl reset).finalCursor+added (Phase23Partial.trimN 86 (sourceEntry impl reset).program) ≤ 544000000
    rw [Phase23Partial.trimN_added]
    exact measurementBound


end
end ShorECDLP.Entrant.GeometricPhase

namespace ShorECDLP.Entrant.GeometricActual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Width16Actual
attribute [local instance] Width16Actual.bodyInstance Width16Actual.resourceInstance
attribute [local irreducible] Single.axis WideBank8.Signed17.program WEXFast.W15H.compactProgram
  ConditionalCatalyst.fourEntry ConditionalCatalyst.compileEntry ConditionalCatalyst.compile
  AndGadget.lowerEntry AndGadget.lowerLayout
noncomputable section
set_option Elab.async false
attribute [local irreducible] List.ofFn
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

def entry : StraightEntry := GeometricPhase.finalEntry implementation reset

def layout : DecodeLayout := lowerLayout 1938 (GeometricPhase.entryTrim rawEntry) rawLayout

def bounds : Bounds := ⟨1620,250549476,544000000⟩

theorem hcert : Certificate officialLimits
      (lowerLayout 1938 (GeometricPhase.entryTrim (Width16Schedule.sourceEntry implementation reset))
        (Width16Schedule.layout implementation reset))
      (GeometricPhase.finalEntry implementation reset)
      ⟨1620,4*(132595+19*implementation.credit17+8*implementation.credit16)+9260,544000000⟩ :=
  GeometricPhase.conditional_certificate implementation reset (List.range 1618)
    rawBounds 1620 raw_certificate source_within strong_success (by decide) (by decide)
    source_counts.2.2 (source_counts.2.1.trans (by decide)) (by decide) source_counts.2.1

theorem tmodel_key : ∀ a b : Nat, a ≤ 2341681 → b ≤ 2251315 →
    4*(132595+19*a+8*b)+9260 ≤ 250549476 := by
  intro a b ha hb
  omega

theorem hres (Q : Point) : (resources (entry.instantiate Q)).qubits ≤ bounds.qubits ∧
    (resources (entry.instantiate Q)).tModel ≤ bounds.tModel ∧
    (resources (entry.instantiate Q)).measurements ≤ bounds.measurements :=
  ⟨(hcert.resources Q).1, (Width16Actual.tmodel_of hcert Q).trans (tmodel_key _ _ credits.1 credits.2),
    (hcert.resources Q).2.2⟩

theorem certificate : Certificate officialLimits layout entry bounds :=
  Certificate.mk hcert.gateBudget hcert.recordBudget hcert.tableBudget hcert.candidateBudget
    hcert.wellFormed hres hcert.success

#print axioms certificate
end
end ShorECDLP.Entrant.GeometricActual
