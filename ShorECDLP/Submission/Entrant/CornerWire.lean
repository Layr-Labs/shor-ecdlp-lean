import ShorECDLP.Submission.Entrant.WideBank8

set_option Elab.async false

/-! ### Consolidated from `Site1Fast.lean` -/
section
/-! Two-pass SelectSwap replacement for `site1` (the entry lookup site of every window row).

`site1` loads 771 wires (`scrShortWires` = 258, `scrPairWires` = 258, `scrDExtraWires` = 255)
with a single 0-bit QROM (`N - 1` Toffolis). With 1,042 clean pool wires available in both
narrow (15-bit) and wide (16-bit) windows:
- Pass A loads `scrShortWires` (258 wires) with 2-bit SelectSwap (`4 × 258 = 1,032` wires,
  `N/4 - 1` QROM + `774` swaps), immediately measure-resets its 774 garbage wires, runs
  `shortPart`, and measure-resets `scrShortWires` (258 wires).
- Pass B loads `scrPairWires ++ scrDExtraWires` (513 wires) with 1-bit SelectSwap
  (`2 × 513 = 1,026` wires, `N/2 - 1` QROM + `513` swaps), immediately measure-resets its
  513 garbage wires, runs `pairPart ++ pointDialogGenericFlag ++ zrep ++ pair1Prog`, and
  runs one single fused measured clear that clears `scrPairWires ++ scrDExtraWires` while
  repaying all deferred X-basis phases from Pass A and Pass B.

Savings: `15,098` Toffolis per wide window and `6,906` Toffolis per narrow window
(`342,110` Toffolis = `1,368,440` T-model gates across 19 wide + 8 narrow windows). -/

namespace ShorECDLP.Entrant.Site1Fast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
theorem run_nil (m : List Bool) (s : ECDSAAdd.State) : ECDSAAdd.run List.nil m s = s := rfl

theorem run_cons_X (t : Wire) (p : ECDSAAdd.Program) (m : List Bool) (s : ECDSAAdd.State) :
    ECDSAAdd.run (.X t :: p) m s =
      ECDSAAdd.run p m ⟨s.phase, ECDSAAdd.writeBit s.basis t (!s.basis t)⟩ := rfl

theorem run_cons_CX (c t : Wire) (p : ECDSAAdd.Program) (m : List Bool) (s : ECDSAAdd.State) :
    ECDSAAdd.run (.CX c t :: p) m s =
      ECDSAAdd.run p m ⟨s.phase, ECDSAAdd.writeBit s.basis t (s.basis t ^^ s.basis c)⟩ := rfl

theorem run_cons_CCX (a b t : Wire) (p : ECDSAAdd.Program) (m : List Bool) (s : ECDSAAdd.State) :
    ECDSAAdd.run (.CCX a b t :: p) m s =
      ECDSAAdd.run p m ⟨s.phase, ECDSAAdd.writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩ := rfl

theorem run_cons_measureX (t : Wire) (c₀ c₁ : List ECDSAAdd.Correction) (p : ECDSAAdd.Program)
    (m : List Bool) (s : ECDSAAdd.State) :
    ECDSAAdd.run (.measureX t c₀ c₁ :: p) m s =
      ECDSAAdd.run p m.tail (ECDSAAdd.measureAndCorrect t c₀ c₁ (m.headD false) s) := rfl

theorem correct_basis : ∀ (cs : List ECDSAAdd.Correction) (s : ECDSAAdd.State),
    (ECDSAAdd.correct cs s).basis = s.basis
  | [], _ => rfl
  | .Z _ :: cs, s => correct_basis cs _
  | .CZ _ _ :: cs, s => correct_basis cs _

attribute [local irreducible] ECDSAAdd.run scrInP1 scrInP2 pair1Prog
  scrPairWires scrShortWires scrDExtraWires WEXUnlookup.rowC WEXUnlookup.rowHead
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram

theorem list_all_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem scrDExtraWires_explicit : scrDExtraWires = List.range' 15399 255 := by
  unfold scrDExtraWires
  exact WEX.map_poolWire 1284 255 (by norm_num)

theorem sl_yLow : yLow streamLayout = 580 := by
  simp only [yLow, streamLayout_point, List.range'_succ, List.headD_cons]
theorem sl_control : streamLayout.control = 836 := rfl
theorem sl_doubleSelect : streamLayout.doubleSelect = 19815 := rfl
theorem sl_genericSelect : streamLayout.genericSelect = 19814 := rfl
theorem sl_equalX : streamLayout.core.equalX = 14111 := rfl
theorem sl_equalNegY : streamLayout.core.equalNegY = 14112 := rfl
theorem sl_generic : streamLayout.core.generic = 14113 := rfl

/-! ### Part 1: Pure `ECDSAAdd` two-pass decomposition of `site1` -/

def pairPart : ECDSAAdd.Program :=
  cxList scrPairWires scrPairTargets ++
    (scrInP1 ++ (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]))

def shortPart : ECDSAAdd.Program :=
  cxList scrShortWires scrShortTargets ++
    (scrInP2 ++ cxList scrShortWires scrShortTargets)

def tailPart : ECDSAAdd.Program :=
  pairPart ++ (pointDialogGenericFlag streamLayout ++
    (ECDSAAdd.Frontier.zrep streamLayout ++ pair1Prog))

def shortPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  retarget (scrInShortBits rows) scrShortWires

def pairExtraPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  retarget (scrPairBits rows (wBit rows .y)) scrPairWires ++ negYExtraPorts rows

def shortWires : List Wire := scrShortWires
def pairExtraWires : List Wire := scrPairWires ++ scrDExtraWires

theorem shortPorts_targets (rows : Nat → Fin 32768) : portTargets (shortPorts rows) = shortWires :=
  retarget_targets _ _ ((scrInShortBits_length rows).trans scrShortWires_length.symm)

theorem pairExtraPorts_targets (rows : Nat → Fin 32768) : portTargets (pairExtraPorts rows) = pairExtraWires := by
  simp only [pairExtraPorts, portTargets, List.map_append, pairExtraWires]
  exact congrArg₂ (· ++ ·)
    (retarget_targets _ _ ((scrPairBits_length rows _).trans scrPairWires_length.symm))
    (negYExtra_targets rows)

theorem shortWires_length : shortWires.length = 258 := scrShortWires_length

theorem pairExtraWires_length : pairExtraWires.length = 513 := by
  have h1 : scrPairWires.length = 258 := scrPairWires_length
  have h2 : scrDExtraWires.length = 255 := by rw [scrDExtraWires_explicit]; simp
  simp [pairExtraWires, h1, h2]

theorem shortPorts_length (rows : Nat → Fin 32768) : (shortPorts rows).length = 258 := by
  have h := congrArg List.length (shortPorts_targets rows)
  simpa [portTargets, shortWires_length] using h

theorem pairExtraPorts_length (rows : Nat → Fin 32768) : (pairExtraPorts rows).length = 513 := by
  have h := congrArg List.length (pairExtraPorts_targets rows)
  simpa [portTargets, pairExtraWires_length] using h

/-- Concrete target effect of `scrInP1` on `yLow`, `doubleSelect`, and `genericSelect`. -/
def p1Effect (v : Bool) (s : BasisState) : BasisState :=
  let s1 := ECDSAAdd.writeBit s streamLayout.doubleSelect (s streamLayout.doubleSelect ^^ (v && s (yLow streamLayout)))
  let s2 := ECDSAAdd.writeBit s1 (yLow streamLayout) (!s1 (yLow streamLayout))
  ECDSAAdd.writeBit s2 streamLayout.genericSelect (s2 streamLayout.genericSelect ^^ (v && s2 (yLow streamLayout)))

theorem p1Effect_frame (v : Bool) (s : BasisState) (w : Wire)
    (hw : w ∉ [yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect]) :
    p1Effect v s w = s w := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨h1, h2, h3⟩ := hw
  simp [p1Effect, ECDSAAdd.writeBit, Function.update, h1, h2, h3]

theorem p1Effect_write (v : Bool) (s : BasisState) (w : Wire) (z : Bool)
    (hw : w ∉ [yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect]) :
    p1Effect v (ECDSAAdd.writeBit s w z) = ECDSAAdd.writeBit (p1Effect v s) w z := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨h1, h2, h3⟩ := hw
  have hy1 : yLow streamLayout ≠ streamLayout.doubleSelect := by rw [sl_yLow, sl_doubleSelect]; decide
  have hy2 : yLow streamLayout ≠ streamLayout.genericSelect := by rw [sl_yLow, sl_genericSelect]; decide
  have h12 : streamLayout.doubleSelect ≠ streamLayout.genericSelect := by rw [sl_doubleSelect, sl_genericSelect]; decide
  funext u
  by_cases hu : u = w
  · subst hu; simp [p1Effect, ECDSAAdd.writeBit, Function.update, h1, h2, h3]
  · simp [p1Effect, ECDSAAdd.writeBit, Function.update, hu, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      hy1, hy2, h12, Ne.symm hy1, Ne.symm hy2, Ne.symm h12]

theorem run_outside_basis : ∀ (p : ECDSAAdd.Program) (m : List Bool) (s : ECDSAAdd.State) (w : Wire),
    w ∉ ECDSAAdd.wires p → (ECDSAAdd.run p m s).basis w = s.basis w
  | [], _, _, _, _ => by rw [run_nil]
  | .X t :: p, m, s, w, hw => by
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_singleton, not_or] at hw
    rw [run_cons_X, run_outside_basis p m _ w hw.2]
    simp [ECDSAAdd.writeBit, Function.update, hw.1]
  | .CX c t :: p, m, s, w, hw => by
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hw
    rw [run_cons_CX, run_outside_basis p m _ w hw.2]
    simp [ECDSAAdd.writeBit, Function.update, hw.1.2]
  | .CCX a b t :: p, m, s, w, hw => by
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hw
    rw [run_cons_CCX, run_outside_basis p m _ w hw.2]
    simp [ECDSAAdd.writeBit, Function.update, hw.1.2.2]
  | .measureX t c₀ c₁ :: p, m, s, w, hw => by
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hw
    rw [run_cons_measureX, run_outside_basis p m.tail _ w hw.2, ECDSAAdd.measureAndCorrect, correct_basis]
    simp [ECDSAAdd.writeBit, Function.update, hw.1.1]

theorem p1Tail_run (c : Wire)
    (hc : c ∉ [yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect])
    (s : ECDSAAdd.State) (m : List Bool) :
    ECDSAAdd.run ([.CCX c (yLow streamLayout) streamLayout.doubleSelect,
      .X (yLow streamLayout), .CCX c (yLow streamLayout) streamLayout.genericSelect] : ECDSAAdd.Program) m s =
      ⟨s.phase, p1Effect (s.basis c) s.basis⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hy1 : yLow streamLayout ≠ streamLayout.doubleSelect := by rw [sl_yLow, sl_doubleSelect]; decide
  rw [run_cons_CCX, run_cons_X, run_cons_CCX, run_nil]
  simp [p1Effect, ECDSAAdd.writeBit, Function.update, hc1, hc2, hc3, hy1, Ne.symm hy1]

theorem pool_take_eq (k : Nat) (hk : k ≤ 2613) :
    streamLayout.dialogPool.take k = List.range' 14115 k := by
  rw [ECDSAAdd.Entrant.pool_block streamLayout streamLayout_widths k hk]
  exact WEX.map_poolWire 0 k (by omega)

theorem mem_pool_take (k : Nat) (hk : k ≤ 2613) {w : Wire} :
    w ∈ streamLayout.dialogPool.take k ↔ 14115 ≤ w ∧ w < 14115 + k := by
  rw [pool_take_eq k hk, List.mem_range'_1]

theorem zeroPorts_mem_flatMap {xs ys : List Wire} {w : Wire}
    (hw : w ∈ (zeroPorts xs ys).flatMap ZeroBit.wires) : w ∈ xs ∨ w ∈ ys := by
  induction xs generalizing ys with
  | nil => simp [zeroPorts] at hw
  | cons x xs ih =>
    cases ys with
    | nil => simp [zeroPorts] at hw
    | cons y ys =>
      simp only [zeroPorts, List.flatMap_cons, ZeroBit.wires, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | rfl) | h
      · exact Or.inl List.mem_cons_self
      · exact Or.inr List.mem_cons_self
      · exact (ih h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)

theorem zeroPorts_flatMap_nodup {xs ys : List Wire} (hx : xs.Nodup) (hy : ys.Nodup)
    (hxy : ∀ x ∈ xs, x ∉ ys) : ((zeroPorts xs ys).flatMap ZeroBit.wires).Nodup := by
  induction xs generalizing ys with
  | nil => simp [zeroPorts]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zeroPorts]
    | cons y ys =>
      have ⟨hxn, hx'⟩ := List.nodup_cons.mp hx
      have ⟨hyn, hy'⟩ := List.nodup_cons.mp hy
      have hxy1 : x ≠ y := fun e => hxy x List.mem_cons_self (e ▸ List.mem_cons_self)
      have hsub : ∀ a ∈ xs, a ∉ ys := fun a ha hm => hxy a (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hm)
      have hrest := ih hx' hy' hsub
      simp only [zeroPorts, List.flatMap_cons, ZeroBit.wires, List.cons_append, List.nil_append, List.nodup_cons]
      refine ⟨?_, ?_, hrest⟩
      · intro hm
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact hxy1 rfl
        · rcases zeroPorts_mem_flatMap hm with h | h
          · exact hxn h
          · exact hxy x List.mem_cons_self (List.mem_cons_of_mem _ h)
      · intro hm
        rcases zeroPorts_mem_flatMap hm with h | h
        · exact hxy y (List.mem_cons_of_mem _ h) List.mem_cons_self
        · exact hyn h

theorem zeroPorts_mem_input_work {xs ys : List Wire} {b : ZeroBit} (hb : b ∈ zeroPorts xs ys) :
    b.input ∈ xs ∧ b.work ∈ ys := by
  induction xs generalizing ys with
  | nil => simp [zeroPorts] at hb
  | cons x xs ih =>
    cases ys with
    | nil => simp [zeroPorts] at hb
    | cons y ys =>
      simp only [zeroPorts, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨List.mem_cons_self, List.mem_cons_self⟩
      · exact ⟨List.mem_cons_of_mem _ (ih hb).1, List.mem_cons_of_mem _ (ih hb).2⟩

theorem pairSrc_eq : ECDSAAdd.Entrant.pairSrc streamLayout = 838 :: List.range' 263 256 := by
  simp [ECDSAAdd.Entrant.pairSrc, streamLayout_point]

theorem shortSrc_eq : ECDSAAdd.Entrant.shortSrc streamLayout =
    838 :: List.range' 263 256 ++ [580] := by
  simp [ECDSAAdd.Entrant.shortSrc, streamLayout_point]

theorem pairPorts_nodup : (streamLayout.control :: (pairPorts streamLayout).flatMap ZeroBit.wires).Nodup := by
  have hx : (ECDSAAdd.Entrant.pairSrc streamLayout).Nodup := by
    rw [pairSrc_eq, List.nodup_cons]
    exact ⟨by simp [List.mem_range'_1], List.nodup_range'⟩
  have hy : (streamLayout.dialogPool.take 257).Nodup := by
    rw [pool_take_eq 257 (by decide)]; exact List.nodup_range'
  have hxy : ∀ x ∈ ECDSAAdd.Entrant.pairSrc streamLayout, x ∉ streamLayout.dialogPool.take 257 := by
    intro x hx' hm
    rw [pairSrc_eq, List.mem_cons, List.mem_range'_1] at hx'
    rw [mem_pool_take 257 (by decide)] at hm
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  rw [List.nodup_cons]
  refine ⟨?_, zeroPorts_flatMap_nodup hx hy hxy⟩
  intro hm
  rcases zeroPorts_mem_flatMap hm with h | h
  · rw [pairSrc_eq, List.mem_cons, List.mem_range'_1, sl_control] at h
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rw [mem_pool_take 257 (by decide), sl_control] at h
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem pairPorts_disj : ∀ b ∈ pairPorts streamLayout,
    b.input ∉ [yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect] ∧
    b.work ∉ [yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect] := by
  intro b hb
  obtain ⟨hi, hw⟩ := zeroPorts_mem_input_work hb
  rw [pairSrc_eq, List.mem_cons, List.mem_range'_1] at hi
  rw [mem_pool_take 257 (by decide)] at hw
  constructor <;> intro hm <;>
    (simp only [List.mem_cons, List.not_mem_nil, or_false, sl_yLow, sl_doubleSelect, sl_genericSelect] at hm;
     dsimp only [Wire, ECDSAAdd.Wire] at *; omega)

theorem pairPorts_work_in_pool : ∀ b ∈ pairPorts streamLayout, b.work ∈ streamLayout.dialogPool.take 258 := by
  intro b hb
  have hw := (zeroPorts_mem_input_work hb).2
  rw [mem_pool_take 257 (by decide)] at hw
  rw [mem_pool_take 258 (by decide)]
  dsimp only [Wire, ECDSAAdd.Wire] at *
  omega

theorem scrInP1_run (s : ECDSAAdd.State) (m : List Bool)
    (hz : Clean (streamLayout.dialogPool.take 258) s.basis) :
    ECDSAAdd.run scrInP1 m s =
      ⟨s.phase, p1Effect (s.basis streamLayout.control &&
        (pairPorts streamLayout).all (fun b => !s.basis b.input)) s.basis⟩ := by
  have hcu : streamLayout.control ∉ [yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, sl_control, sl_yLow, sl_doubleSelect, sl_genericSelect]
    decide
  rw [show scrInP1 = zeroWith (fun w => [.CCX w (yLow streamLayout) streamLayout.doubleSelect,
      .X (yLow streamLayout), .CCX w (yLow streamLayout) streamLayout.genericSelect])
      streamLayout.control (pairPorts streamLayout) by unfold scrInP1; rfl]
  exact ECDSAAdd.Frontier.zeroWith_effect_run
    [yLow streamLayout, streamLayout.doubleSelect, streamLayout.genericSelect]
    (fun _ => True) p1Effect
    (fun w => [.CCX w (yLow streamLayout) streamLayout.doubleSelect,
      .X (yLow streamLayout), .CCX w (yLow streamLayout) streamLayout.genericSelect])
    (fun _ _ _ _ => Iff.rfl) p1Effect_frame p1Effect_write
    (fun c hc st k _ => p1Tail_run c hc st k)
    streamLayout.control (pairPorts streamLayout) hcu pairPorts_nodup pairPorts_disj
    s m trivial (fun b hb => hz b.work (pairPorts_work_in_pool b hb))

theorem shortPorts2_nodup :
    (streamLayout.core.equalX :: streamLayout.core.equalNegY ::
      (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).flatMap ZeroBit.wires).Nodup := by
  have hx : (shortSrc streamLayout).Nodup := by
    rw [shortSrc_eq, List.cons_append, List.nodup_cons, List.nodup_append]
    refine ⟨by simp [List.mem_range'_1], List.nodup_range', List.nodup_singleton _, fun a ha b hb hab => ?_⟩
    subst hab; simp only [List.mem_range'_1, List.mem_singleton] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hy : (streamLayout.dialogPool.take 258).Nodup := by
    rw [pool_take_eq 258 (by decide)]; exact List.nodup_range'
  have hxy : ∀ x ∈ shortSrc streamLayout, x ∉ streamLayout.dialogPool.take 258 := by
    intro x hx' hm
    rw [shortSrc_eq, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton] at hx'
    rw [mem_pool_take 258 (by decide)] at hm
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  rw [List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ?_, zeroPorts_flatMap_nodup hx hy hxy⟩
  · intro hm
    simp only [List.mem_cons] at hm
    rcases hm with hm | hm
    · rw [sl_equalX, sl_equalNegY] at hm; exact absurd hm (by decide)
    · rcases zeroPorts_mem_flatMap hm with h | h
      · rw [shortSrc_eq, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton, sl_equalX] at h
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · rw [mem_pool_take 258 (by decide), sl_equalX] at h
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · intro hm
    rcases zeroPorts_mem_flatMap hm with h | h
    · rw [shortSrc_eq, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton, sl_equalNegY] at h
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · rw [mem_pool_take 258 (by decide), sl_equalNegY] at h
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem shortPorts2_work_in_pool :
    ∀ b ∈ zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258),
      b.work ∈ streamLayout.dialogPool.take 258 := fun _ hb => (zeroPorts_mem_input_work hb).2

theorem scrInP2_run (s : ECDSAAdd.State) (m : List Bool)
    (hz : Clean (streamLayout.dialogPool.take 258) s.basis) :
    ECDSAAdd.run scrInP2 m s =
      ⟨s.phase, ECDSAAdd.writeBit s.basis streamLayout.core.equalNegY
        (s.basis streamLayout.core.equalNegY ^^
          (s.basis streamLayout.core.equalX &&
            (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).all
              (fun b => !s.basis b.input)))⟩ := by
  rw [show scrInP2 = zeroControlled streamLayout.core.equalX streamLayout.core.equalNegY
      (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)) by unfold scrInP2; rfl]
  exact zeroControlled_correct streamLayout.core.equalX streamLayout.core.equalNegY
    (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258))
    shortPorts2_nodup s m (fun b hb => hz b.work (shortPorts2_work_in_pool b hb))

theorem cxList_run_exact : ∀ (cs ts : List Wire) (hl : cs.length = ts.length), (cs ++ ts).Nodup →
    ∀ (s : ECDSAAdd.State) (m : List Bool),
      (ECDSAAdd.run (cxList cs ts) m s).phase = s.phase ∧
      (∀ w, w ∉ ts → (ECDSAAdd.run (cxList cs ts) m s).basis w = s.basis w) ∧
      (∀ i (hi : i < ts.length),
        (ECDSAAdd.run (cxList cs ts) m s).basis (ts[i]'hi) =
          (s.basis (ts[i]'hi) ^^ s.basis (cs[i]'(hl.symm ▸ hi)))) := by
  intro cs
  induction cs with
  | nil =>
    intro ts hl _ s m
    cases ts with
    | nil =>
      have h0 : ECDSAAdd.run (cxList List.nil List.nil) m s = s := run_nil m s
      exact ⟨by rw [h0], fun _ _ => by rw [h0], fun i hi => by simp at hi⟩
    | cons _ _ => simp at hl
  | cons c cs ih =>
    intro ts hl hnd s m
    cases ts with
    | nil => simp at hl
    | cons t ts =>
      have hl' : cs.length = ts.length := by simpa using hl
      have hnd' : c ∉ cs ++ t :: ts ∧ (cs ++ t :: ts).Nodup := by
        simpa [List.cons_append] using List.nodup_cons.mp hnd
      have hts : t ∉ cs ∧ t ∉ ts ∧ (cs ++ ts).Nodup := by
        have h1 := List.nodup_append.mp hnd'.2
        have h2 := List.nodup_cons.mp h1.2.1
        exact ⟨fun hc => h1.2.2 t hc t List.mem_cons_self rfl, h2.1,
          List.nodup_append.mpr ⟨h1.1, h2.2, fun a ha b hb => h1.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩⟩
      have hstep : ECDSAAdd.run (cxList (c :: cs) (t :: ts)) m s =
          ECDSAAdd.run (cxList cs ts) m ⟨s.phase, ECDSAAdd.writeBit s.basis t (s.basis t ^^ s.basis c)⟩ :=
        run_cons_CX c t (cxList cs ts) m s
      rw [hstep]
      have hrec := ih ts hl' hts.2.2 ⟨s.phase, ECDSAAdd.writeBit s.basis t (s.basis t ^^ s.basis c)⟩ m
      refine ⟨hrec.1, ?_, ?_⟩
      · intro w hw
        simp only [List.mem_cons, not_or] at hw
        rw [hrec.2.1 w hw.2]
        simp [ECDSAAdd.writeBit, Function.update, hw.1]
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero]
          rw [hrec.2.1 t hts.2.1]
          simp [ECDSAAdd.writeBit, Function.update]
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hj : j < ts.length := Nat.lt_of_succ_lt_succ hi
          rw [hrec.2.2 j hj]
          have hne1 : ts[j]'hj ≠ t := fun e => hts.2.1 (e ▸ List.getElem_mem hj)
          have hne2 : cs[j]'(hl'.symm ▸ hj) ≠ t := fun e => hts.1 (e ▸ List.getElem_mem _)
          simp [ECDSAAdd.writeBit, Function.update, hne1, hne2]

theorem scrPairTargets_eq : scrPairTargets = 838 :: List.range' 263 256 ++ [580] := by
  simp [scrPairTargets, sl_yLow, streamLayout_point]
theorem scrShortTargets_eq : scrShortTargets = 838 :: List.range' 263 256 ++ [580] := by
  simp [scrShortTargets, streamLayout_point]

theorem targets_nodup : (838 :: List.range' 263 256 ++ [580] : List Wire).Nodup := by
  rw [List.cons_append, List.nodup_cons, List.nodup_append]
  refine ⟨by simp [List.mem_range'_1], List.nodup_range', List.nodup_singleton _, fun a ha b hb hab => ?_⟩
  simp only [List.mem_range'_1, List.mem_singleton] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem scrPairWires_nd : scrPairWires.Nodup := (List.nodup_append.mp scrWires_nodup).1
theorem scrShortWires_nd : scrShortWires.Nodup := (List.nodup_append.mp scrWires_nodup).2.1

theorem scrPair_cx_nd : (scrPairWires ++ scrPairTargets).Nodup := by
  rw [List.nodup_append]
  refine ⟨scrPairWires_nd, by rw [scrPairTargets_eq]; exact targets_nodup, fun a ha b hb hab => ?_⟩
  subst hab
  exact scrWires_pair_targets a (List.mem_append_left _ ha) hb

theorem scrShort_cx_nd : (scrShortWires ++ scrShortTargets).Nodup := by
  rw [List.nodup_append]
  refine ⟨scrShortWires_nd, by rw [scrShortTargets_eq]; exact targets_nodup, fun a ha b hb hab => ?_⟩
  subst hab
  exact scrWires_short_targets a (List.mem_append_right _ ha) hb

theorem scrPair_len_eq : scrPairWires.length = scrPairTargets.length := by
  have h1 : scrPairWires.length = 258 := scrPairWires_length
  have h2 : scrPairTargets.length = 258 := by rw [scrPairTargets_eq]; simp
  omega

theorem scrShort_len_eq : scrShortWires.length = scrShortTargets.length := by
  have h1 : scrShortWires.length = 258 := scrShortWires_length
  have h2 : scrShortTargets.length = 258 := by rw [scrShortTargets_eq]; simp
  omega

theorem pairTargets_not_pool : ∀ w ∈ streamLayout.dialogPool.take 258, w ∉ scrPairTargets := by
  intro w hw hm
  rw [mem_pool_take 258 (by decide)] at hw
  rw [scrPairTargets_eq, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton] at hm
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem shortTargets_not_pool : ∀ w ∈ streamLayout.dialogPool.take 258, w ∉ scrShortTargets := pairTargets_not_pool

theorem pairTargets_no_flags :
    streamLayout.doubleSelect ∉ scrPairTargets ∧ streamLayout.genericSelect ∉ scrPairTargets ∧
    streamLayout.core.equalX ∉ scrPairTargets ∧ streamLayout.core.equalNegY ∉ scrPairTargets := by
  rw [sl_doubleSelect, sl_genericSelect, sl_equalX, sl_equalNegY]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hm <;>
    (rw [scrPairTargets_eq, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton] at hm;
     dsimp only [Wire, ECDSAAdd.Wire] at *; omega)

theorem shortTargets_no_flags :
    streamLayout.doubleSelect ∉ scrShortTargets ∧ streamLayout.genericSelect ∉ scrShortTargets ∧
    streamLayout.core.equalX ∉ scrShortTargets ∧ streamLayout.core.equalNegY ∉ scrShortTargets :=
  pairTargets_no_flags

theorem shortWires_bounds (w : Wire) (hw : w ∈ shortWires) : 14884 ≤ w ∧ w < 15142 := by
  rw [shortWires, scrShortWires_explicit] at hw
  simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.mem_singleton,
    List.not_mem_nil, or_false] at hw
  dsimp only [Wire, ECDSAAdd.Wire] at *
  omega

theorem pairWires_bounds (w : Wire) (hw : w ∈ scrPairWires) :
    (14373 ≤ w ∧ w < 14630) ∨ w = 14883 := by
  rw [scrPairWires_explicit] at hw
  simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.mem_singleton,
    List.not_mem_nil, or_false] at hw
  dsimp only [Wire, ECDSAAdd.Wire] at *
  omega

theorem scrPairWires_no_flags :
    streamLayout.doubleSelect ∉ scrPairWires ∧ streamLayout.genericSelect ∉ scrPairWires ∧
    streamLayout.core.equalX ∉ scrPairWires ∧ streamLayout.core.equalNegY ∉ scrPairWires := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    (have hb := pairWires_bounds _ h;
     simp only [sl_doubleSelect, sl_genericSelect, sl_equalX, sl_equalNegY] at hb;
     dsimp only [Wire, ECDSAAdd.Wire] at *; omega)

theorem scrShortWires_no_flags :
    streamLayout.doubleSelect ∉ scrShortWires ∧ streamLayout.genericSelect ∉ scrShortWires ∧
    streamLayout.core.equalX ∉ scrShortWires ∧ streamLayout.core.equalNegY ∉ scrShortWires := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    (have hb := shortWires_bounds _ h;
     simp only [sl_doubleSelect, sl_genericSelect, sl_equalX, sl_equalNegY] at hb;
     dsimp only [Wire, ECDSAAdd.Wire] at *; omega)

/-- Closed-form action of `pairPart`: flips only `doubleSelect` and `genericSelect`, preserves every other wire. -/
theorem pairPart_run (s : ECDSAAdd.State) (m : List Bool)
    (hz : Clean (streamLayout.dialogPool.take 258) s.basis) :
    let u := ECDSAAdd.run (cxList scrPairWires scrPairTargets) List.nil s
    let v := u.basis streamLayout.control && (pairPorts streamLayout).all (fun b => !u.basis b.input)
    let y0 := u.basis (yLow streamLayout)
    ECDSAAdd.run pairPart m s =
      ⟨s.phase, ECDSAAdd.writeBit (ECDSAAdd.writeBit s.basis streamLayout.doubleSelect
        (s.basis streamLayout.doubleSelect ^^ (v && y0)))
        streamLayout.genericSelect (s.basis streamLayout.genericSelect ^^ (v && !y0))⟩ := by
  intro u v y0
  have hcx := cxList_run_exact scrPairWires scrPairTargets scrPair_len_eq scrPair_cx_nd s List.nil
  have hu_pool : Clean (streamLayout.dialogPool.take 258) u.basis := fun w hw => by
    dsimp only [u]; rw [hcx.2.1 w (pairTargets_not_pool w hw)]; exact hz w hw
  have hmc : ECDSAAdd.measurementCount (cxList scrPairWires scrPairTargets) = 0 := cxList_records _ _
  simp only [pairPart]
  rw [run_zero_append _ _ hmc, run_meas_append scrInP1, scrInP1_run u _ hu_pool,
    run_zero_append _ _ hmc]
  set p1 : ECDSAAdd.State := ⟨u.phase, p1Effect v u.basis⟩ with hp1
  have hcx2 := cxList_run_exact scrPairWires scrPairTargets scrPair_len_eq scrPair_cx_nd p1 List.nil
  have hnd_flags : yLow streamLayout ≠ streamLayout.doubleSelect ∧
      yLow streamLayout ≠ streamLayout.genericSelect ∧
      streamLayout.doubleSelect ≠ streamLayout.genericSelect := by
    rw [sl_yLow, sl_doubleSelect, sl_genericSelect]; decide
  have hp1_agree_cs : ∀ i (hi : i < scrPairWires.length),
      p1.basis (scrPairWires[i]'hi) = u.basis (scrPairWires[i]'hi) := by
    intro i hi
    apply p1Effect_frame v u.basis
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm
    · have hb := pairWires_bounds _ (List.getElem_mem hi)
      rw [hm, sl_yLow] at hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · exact scrPairWires_no_flags.1 (hm ▸ List.getElem_mem hi)
    · exact scrPairWires_no_flags.2.1 (hm ▸ List.getElem_mem hi)
  have hrunX (st : ECDSAAdd.State) :
      ECDSAAdd.run ([.X (yLow streamLayout)] : ECDSAAdd.Program) (m.drop (ECDSAAdd.measurementCount scrInP1)) st =
        ⟨st.phase, ECDSAAdd.writeBit st.basis (yLow streamLayout) (!st.basis (yLow streamLayout))⟩ := by
    rw [run_cons_X, run_nil]
  rw [hrunX]
  have hph : (ECDSAAdd.run (cxList scrPairWires scrPairTargets) List.nil p1).phase = s.phase :=
    hcx2.1.trans hcx.1
  refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hph, ?_⟩
  funext w
  by_cases hw2 : w = streamLayout.genericSelect
  · subst hw2
    have h1 := hcx2.2.1 _ pairTargets_no_flags.2.1
    have h2 := hcx.2.1 _ pairTargets_no_flags.2.1
    simp only [ECDSAAdd.writeBit, Function.update, Ne.symm hnd_flags.2.1, ↓reduceDIte]
    rw [h1, hp1]
    simp [p1Effect, ECDSAAdd.writeBit, Function.update, hnd_flags.1, hnd_flags.2.1, hnd_flags.2.2,
      Ne.symm hnd_flags.1, Ne.symm hnd_flags.2.1, Ne.symm hnd_flags.2.2, u, y0, h2]
  · by_cases hw1 : w = streamLayout.doubleSelect
    · subst hw1
      have h1 := hcx2.2.1 _ pairTargets_no_flags.1
      have h2 := hcx.2.1 _ pairTargets_no_flags.1
      simp only [ECDSAAdd.writeBit, Function.update, Ne.symm hnd_flags.1, Ne.symm hnd_flags.2.2,
        hnd_flags.2.2, ↓reduceDIte]
      rw [h1, hp1]
      simp [p1Effect, ECDSAAdd.writeBit, Function.update, hnd_flags.1, hnd_flags.2.1, hnd_flags.2.2,
        Ne.symm hnd_flags.1, Ne.symm hnd_flags.2.1, Ne.symm hnd_flags.2.2, u, y0, h2]
    · simp only [ECDSAAdd.writeBit, Function.update, hw2, hw1, ↓reduceDIte]
      by_cases hwy : w = yLow streamLayout
      · subst hwy
        simp only [↓reduceDIte]
        have hmem : yLow streamLayout ∈ scrPairTargets := by
          rw [scrPairTargets_eq, sl_yLow]; simp
        obtain ⟨i, hi, he⟩ := List.getElem_of_mem hmem
        have h1 := hcx2.2.2 i hi
        have h2 := hcx.2.2 i hi
        rw [he] at h1 h2
        rw [h1, hp1_agree_cs i (scrPair_len_eq.symm ▸ hi)]
        have hp1y : p1.basis (yLow streamLayout) = !u.basis (yLow streamLayout) := by
          simp [hp1, p1Effect, ECDSAAdd.writeBit, Function.update, hnd_flags.1, hnd_flags.2.1]
        have huw : u.basis (scrPairWires[i]'(scrPair_len_eq.symm ▸ hi)) =
            s.basis (scrPairWires[i]'(scrPair_len_eq.symm ▸ hi)) := by
          dsimp only [u]
          exact hcx.2.1 _ (fun hm => scrWires_pair_targets _ (List.mem_append_left _ (List.getElem_mem _)) hm)
        rw [hp1y, huw]
        dsimp only [u]
        rw [h2]
        cases s.basis (yLow streamLayout) <;> cases s.basis (scrPairWires[i]'(scrPair_len_eq.symm ▸ hi)) <;> rfl
      · simp only [hwy, ↓reduceDIte]
        by_cases hwt : w ∈ scrPairTargets
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hwt
          rw [hcx2.2.2 i hi, hp1_agree_cs i (scrPair_len_eq.symm ▸ hi)]
          have hp1w : p1.basis (scrPairTargets[i]'hi) = u.basis (scrPairTargets[i]'hi) := by
            rw [hp1]; exact p1Effect_frame v u.basis _ (by simp [hwy, hw1, hw2])
          have huw : u.basis (scrPairWires[i]'(scrPair_len_eq.symm ▸ hi)) =
              s.basis (scrPairWires[i]'(scrPair_len_eq.symm ▸ hi)) := by
            dsimp only [u]
            exact hcx.2.1 _ (fun hm => scrWires_pair_targets _ (List.mem_append_left _ (List.getElem_mem _)) hm)
          rw [hp1w, huw]
          dsimp only [u]
          rw [hcx.2.2 i hi]
          cases s.basis (scrPairTargets[i]'hi) <;> cases s.basis (scrPairWires[i]'(scrPair_len_eq.symm ▸ hi)) <;> rfl
        · rw [hcx2.2.1 w hwt, hp1]
          dsimp only
          rw [p1Effect_frame v u.basis w (by simp [hwy, hw1, hw2])]
          dsimp only [u]
          exact hcx.2.1 w hwt

/-- Closed-form action of `shortPart`: flips only `equalNegY`, preserves every other wire. -/
theorem shortPart_run (s : ECDSAAdd.State) (m : List Bool)
    (hz : Clean (streamLayout.dialogPool.take 258) s.basis) :
    let u := ECDSAAdd.run (cxList scrShortWires scrShortTargets) List.nil s
    let v := u.basis streamLayout.core.equalX &&
      (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).all (fun b => !u.basis b.input)
    ECDSAAdd.run shortPart m s =
      ⟨s.phase, ECDSAAdd.writeBit s.basis streamLayout.core.equalNegY (s.basis streamLayout.core.equalNegY ^^ v)⟩ := by
  intro u v
  have hcx := cxList_run_exact scrShortWires scrShortTargets scrShort_len_eq scrShort_cx_nd s List.nil
  have hu_pool : Clean (streamLayout.dialogPool.take 258) u.basis := fun w hw => by
    dsimp only [u]; rw [hcx.2.1 w (shortTargets_not_pool w hw)]; exact hz w hw
  have hmc : ECDSAAdd.measurementCount (cxList scrShortWires scrShortTargets) = 0 := cxList_records _ _
  simp only [shortPart]
  rw [run_zero_append _ _ hmc, run_meas_append scrInP2, scrInP2_run u _ hu_pool]
  set p2 : ECDSAAdd.State := ⟨u.phase, ECDSAAdd.writeBit u.basis streamLayout.core.equalNegY
    (u.basis streamLayout.core.equalNegY ^^ v)⟩ with hp2
  have hcx2 := cxList_run_exact scrShortWires scrShortTargets scrShort_len_eq scrShort_cx_nd p2
    (m.drop (ECDSAAdd.measurementCount scrInP2))
  have hp2_agree_cs : ∀ i (hi : i < scrShortWires.length),
      p2.basis (scrShortWires[i]'hi) = u.basis (scrShortWires[i]'hi) := by
    intro i hi
    have hne : scrShortWires[i]'hi ≠ streamLayout.core.equalNegY :=
      fun e => scrShortWires_no_flags.2.2.2 (e ▸ List.getElem_mem hi)
    simp [hp2, ECDSAAdd.writeBit, Function.update, hne]
  have hph : (ECDSAAdd.run (cxList scrShortWires scrShortTargets)
      (m.drop (ECDSAAdd.measurementCount scrInP2)) p2).phase = s.phase := hcx2.1.trans hcx.1
  refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hph, ?_⟩
  funext w
  by_cases hw : w = streamLayout.core.equalNegY
  · subst hw
    rw [hcx2.2.1 _ shortTargets_no_flags.2.2.2]
    simp only [hp2, ECDSAAdd.writeBit, Function.update, ↓reduceDIte]
    dsimp only [u]
    rw [hcx.2.1 _ shortTargets_no_flags.2.2.2]
  · simp only [ECDSAAdd.writeBit, Function.update, hw, ↓reduceDIte]
    by_cases hwt : w ∈ scrShortTargets
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hwt
      rw [hcx2.2.2 i hi, hp2_agree_cs i (scrShort_len_eq.symm ▸ hi)]
      simp only [hp2, ECDSAAdd.writeBit, Function.update, hw, ↓reduceDIte]
      have huw : u.basis (scrShortWires[i]'(scrShort_len_eq.symm ▸ hi)) =
          s.basis (scrShortWires[i]'(scrShort_len_eq.symm ▸ hi)) := by
        dsimp only [u]
        exact hcx.2.1 _ (fun hm => scrWires_short_targets _ (List.mem_append_right _ (List.getElem_mem _)) hm)
      rw [huw]
      dsimp only [u]
      rw [hcx.2.2 i hi]
      cases s.basis (scrShortTargets[i]'hi) <;> cases s.basis (scrShortWires[i]'(scrShort_len_eq.symm ▸ hi)) <;> rfl
    · rw [hcx2.2.1 w hwt]
      simp only [hp2, ECDSAAdd.writeBit, Function.update, hw, ↓reduceDIte]
      dsimp only [u]
      exact hcx.2.1 w hwt

/-- `shortPart` and `pairPart` commute on any state with clean `dialogPool.take 258`. -/
theorem shortPart_pairPart_comm (s : ECDSAAdd.State) (m₁ m₂ : List Bool)
    (hz : Clean (streamLayout.dialogPool.take 258) s.basis) :
    ECDSAAdd.run (shortPart ++ pairPart) m₁ s = ECDSAAdd.run (pairPart ++ shortPart) m₂ s := by
  have hne : streamLayout.core.equalNegY ≠ streamLayout.doubleSelect ∧
      streamLayout.core.equalNegY ≠ streamLayout.genericSelect ∧
      streamLayout.doubleSelect ≠ streamLayout.genericSelect := by
    rw [sl_equalNegY, sl_doubleSelect, sl_genericSelect]; decide
  have heq_pool : streamLayout.core.equalNegY ∉ streamLayout.dialogPool.take 258 ∧
      streamLayout.doubleSelect ∉ streamLayout.dialogPool.take 258 ∧
      streamLayout.genericSelect ∉ streamLayout.dialogPool.take 258 := by
    rw [sl_equalNegY, sl_doubleSelect, sl_genericSelect]
    refine ⟨?_, ?_, ?_⟩ <;> intro hm <;>
      (rw [mem_pool_take 258 (by decide)] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
  let uS := ECDSAAdd.run (cxList scrShortWires scrShortTargets) List.nil s
  let vS := uS.basis streamLayout.core.equalX &&
    (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).all (fun b => !uS.basis b.input)
  let uP := ECDSAAdd.run (cxList scrPairWires scrPairTargets) List.nil s
  let vP := uP.basis streamLayout.control && (pairPorts streamLayout).all (fun b => !uP.basis b.input)
  let y0 := uP.basis (yLow streamLayout)
  let bA : BasisState := ECDSAAdd.writeBit s.basis streamLayout.core.equalNegY
    (s.basis streamLayout.core.equalNegY ^^ vS)
  let bB : BasisState := ECDSAAdd.writeBit (ECDSAAdd.writeBit s.basis streamLayout.doubleSelect
    (s.basis streamLayout.doubleSelect ^^ (vP && y0)))
    streamLayout.genericSelect (s.basis streamLayout.genericSelect ^^ (vP && !y0))
  have h1 : ECDSAAdd.run shortPart (m₁.take (ECDSAAdd.measurementCount shortPart)) s = ⟨s.phase, bA⟩ :=
    shortPart_run s (m₁.take (ECDSAAdd.measurementCount shortPart)) hz
  have h2 : ECDSAAdd.run pairPart (m₂.take (ECDSAAdd.measurementCount pairPart)) s = ⟨s.phase, bB⟩ :=
    pairPart_run s (m₂.take (ECDSAAdd.measurementCount pairPart)) hz
  rw [ECDSAAdd.run_append, h1, ECDSAAdd.run_append, h2]
  have hzA : Clean (streamLayout.dialogPool.take 258) bA := fun w hw => by
    have hne' : w ≠ streamLayout.core.equalNegY := fun e => heq_pool.1 (e ▸ hw)
    simp [bA, ECDSAAdd.writeBit, Function.update, hne', hz w hw]
  have hzB : Clean (streamLayout.dialogPool.take 258) bB := fun w hw => by
    have hne1 : w ≠ streamLayout.doubleSelect := fun e => heq_pool.2.1 (e ▸ hw)
    have hne2 : w ≠ streamLayout.genericSelect := fun e => heq_pool.2.2 (e ▸ hw)
    simp [bB, ECDSAAdd.writeBit, Function.update, hne1, hne2, hz w hw]
  rw [pairPart_run ⟨s.phase, bA⟩ _ hzA, shortPart_run ⟨s.phase, bB⟩ _ hzB]
  have hcxP_agree : ∀ w, w ≠ streamLayout.core.equalNegY →
      (ECDSAAdd.run (cxList scrPairWires scrPairTargets) List.nil ⟨s.phase, bA⟩).basis w = uP.basis w := by
    intro w hw
    have ha := cxList_run_exact scrPairWires scrPairTargets scrPair_len_eq scrPair_cx_nd ⟨s.phase, bA⟩ List.nil
    have hb := cxList_run_exact scrPairWires scrPairTargets scrPair_len_eq scrPair_cx_nd s List.nil
    by_cases hwt : w ∈ scrPairTargets
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hwt
      rw [ha.2.2 i hi]; dsimp only [uP]; rw [hb.2.2 i hi]
      have hne1 : scrPairWires[i]'(scrPair_len_eq.symm ▸ hi) ≠ streamLayout.core.equalNegY :=
        fun e => scrPairWires_no_flags.2.2.2 (e ▸ List.getElem_mem _)
      simp [bA, ECDSAAdd.writeBit, Function.update, hw, hne1]
    · rw [ha.2.1 w hwt]; dsimp only [uP]; rw [hb.2.1 w hwt]
      simp [bA, ECDSAAdd.writeBit, Function.update, hw]
  have hcxS_agree : ∀ w, w ≠ streamLayout.doubleSelect → w ≠ streamLayout.genericSelect →
      (ECDSAAdd.run (cxList scrShortWires scrShortTargets) List.nil ⟨s.phase, bB⟩).basis w = uS.basis w := by
    intro w hw1 hw2
    have ha := cxList_run_exact scrShortWires scrShortTargets scrShort_len_eq scrShort_cx_nd ⟨s.phase, bB⟩ List.nil
    have hb := cxList_run_exact scrShortWires scrShortTargets scrShort_len_eq scrShort_cx_nd s List.nil
    by_cases hwt : w ∈ scrShortTargets
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hwt
      rw [ha.2.2 i hi]; dsimp only [uS]; rw [hb.2.2 i hi]
      have hne1 : scrShortWires[i]'(scrShort_len_eq.symm ▸ hi) ≠ streamLayout.doubleSelect :=
        fun e => scrShortWires_no_flags.1 (e ▸ List.getElem_mem _)
      have hne2 : scrShortWires[i]'(scrShort_len_eq.symm ▸ hi) ≠ streamLayout.genericSelect :=
        fun e => scrShortWires_no_flags.2.1 (e ▸ List.getElem_mem _)
      simp [bB, ECDSAAdd.writeBit, Function.update, hw1, hw2, hne1, hne2]
    · rw [ha.2.1 w hwt]; dsimp only [uS]; rw [hb.2.1 w hwt]
      simp [bB, ECDSAAdd.writeBit, Function.update, hw1, hw2]
  have hallP : (pairPorts streamLayout).all
      (fun b => !(ECDSAAdd.run (cxList scrPairWires scrPairTargets) List.nil ⟨s.phase, bA⟩).basis b.input) =
      (pairPorts streamLayout).all (fun b => !uP.basis b.input) := by
    apply list_all_congr
    intro b hb
    have hne' : b.input ≠ streamLayout.core.equalNegY := by
      have hi := (zeroPorts_mem_input_work hb).1
      rw [pairSrc_eq, List.mem_cons, List.mem_range'_1] at hi
      rw [sl_equalNegY]
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    rw [hcxP_agree b.input hne']
  have hallS : (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).all
      (fun b => !(ECDSAAdd.run (cxList scrShortWires scrShortTargets) List.nil ⟨s.phase, bB⟩).basis b.input) =
      (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).all (fun b => !uS.basis b.input) := by
    apply list_all_congr
    intro b hb
    have hne' : b.input ≠ streamLayout.doubleSelect ∧ b.input ≠ streamLayout.genericSelect := by
      have hi := (zeroPorts_mem_input_work hb).1
      rw [shortSrc_eq, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton] at hi
      rw [sl_doubleSelect, sl_genericSelect]
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    rw [hcxS_agree b.input hne'.1 hne'.2]
  have hctlP := hcxP_agree streamLayout.control (by rw [sl_control, sl_equalNegY]; decide)
  have hyP := hcxP_agree (yLow streamLayout) (by rw [sl_yLow, sl_equalNegY]; decide)
  have heqS := hcxS_agree streamLayout.core.equalX (by rw [sl_equalX, sl_doubleSelect]; decide)
    (by rw [sl_equalX, sl_genericSelect]; decide)
  refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  funext w
  dsimp only
  rw [hallP, hallS, hctlP, hyP, heqS]
  by_cases h1 : w = streamLayout.core.equalNegY
  · subst h1; simp [bA, bB, vS, vP, y0, ECDSAAdd.writeBit, Function.update, hne.1, hne.2.1, Ne.symm hne.1, Ne.symm hne.2.1]
  · by_cases h2 : w = streamLayout.doubleSelect
    · subst h2; simp [bA, bB, vS, vP, y0, ECDSAAdd.writeBit, Function.update, hne.1, hne.2.2, Ne.symm hne.1, Ne.symm hne.2.2]
    · by_cases h3 : w = streamLayout.genericSelect
      · subst h3; simp [bA, bB, vS, vP, y0, ECDSAAdd.writeBit, Function.update, hne.2.1, hne.2.2, Ne.symm hne.2.1, Ne.symm hne.2.2]
      · simp [bA, bB, vS, vP, y0, ECDSAAdd.writeBit, Function.update, h1, h2, h3]

theorem shortPart_avoid_pairExtra : ∀ w ∈ pairExtraWires, w ∉ ECDSAAdd.wires shortPart := by
  intro w hw
  have hS : w ∈ scrAllWires := by
    rcases List.mem_append.mp hw with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact List.mem_append_right _ h
  have hns : w ∉ scrShortWires := by
    rcases List.mem_append.mp hw with h | h
    · exact fun hm => (List.nodup_append.mp scrWires_nodup).2.2 w h w hm rfl
    · exact fun hm => extra_not_scrWires w h (List.mem_append_right _ hm)
  simp only [shortPart, ECDSAAdd.wires_append, Finset.mem_union, not_or]
  refine ⟨?_, scrAll_not_P2 w hS, ?_⟩
  · intro hm; rcases cxList_wires _ _ _ hm with hm | hm
    · exact hns hm
    · exact scrAll_short_targets w hS hm
  · intro hm; rcases cxList_wires _ _ _ hm with hm | hm
    · exact hns hm
    · exact scrAll_short_targets w hS hm

theorem tailPart_avoid_short : ∀ w ∈ shortWires, w ∉ ECDSAAdd.wires tailPart := by
  intro w hw
  have hS : w ∈ scrAllWires := List.mem_append_left _ (List.mem_append_right _ hw)
  have hnp : w ∉ scrPairWires := fun hm => (List.nodup_append.mp scrWires_nodup).2.2 w hm w hw rfl
  have hpair : w ∉ ECDSAAdd.wires pairPart := by
    simp only [pairPart, ECDSAAdd.wires_append, Finset.mem_union, not_or]
    refine ⟨?_, scrAll_not_P1 w hS, ?_, ?_⟩
    · intro hm; rcases cxList_wires _ _ _ hm with hm | hm
      · exact hnp hm
      · exact scrAll_pair_targets w hS hm
    · intro hm; rcases cxList_wires _ _ _ hm with hm | hm
      · exact hnp hm
      · exact scrAll_pair_targets w hS hm
    · intro hm
      simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_singleton] at hm
      have hb := shortWires_bounds w hw
      rw [hm, sl_yLow] at hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hp1 : w ∉ ECDSAAdd.wires pair1Prog := by
    intro hm
    have hsub := List.mem_toFinset.mp (pair1Prog_subset hm)
    have hsw := shortWires_bounds w hw
    simp only [pair1List, xAdd, yAdd, negXW, MeasuredCanonicalModLayout.wires,
      CompactRecoveryNegateLayout.wires, cxWord, cyWord, addCarry,
      streamLayout_point, sl_control, List.mem_append, List.mem_cons, List.mem_range'_1,
      List.not_mem_nil, or_false] at hsub
    dsimp only [Wire, ECDSAAdd.Wire] at *
    omega
  simp only [tailPart, ECDSAAdd.wires_append, Finset.mem_union, not_or]
  exact ⟨hpair, scrAll_avoid_gf w hS, scrAll_avoid_zrep w hS, hp1⟩

theorem site1Arith_eq : site1Arith = pairPart ++ (shortPart ++
    (pointDialogGenericFlag streamLayout ++ (ECDSAAdd.Frontier.zrep streamLayout ++ pair1Prog))) := by
  simp only [site1Arith, scrInArith_eq, pairPart, shortPart, List.append_assoc]

theorem shortPart_wires_sub : ECDSAAdd.wires shortPart ⊆ ECDSAAdd.wires site1Arith := by
  rw [site1Arith_eq]
  intro w hw
  simp [ECDSAAdd.wires_append, hw]

theorem tailPart_wires_sub : ECDSAAdd.wires tailPart ⊆ ECDSAAdd.wires site1Arith := by
  rw [site1Arith_eq, tailPart]
  intro w hw
  simp only [ECDSAAdd.wires_append, Finset.mem_union] at hw ⊢
  tauto

theorem shortPart_root : windowRoot ∉ ECDSAAdd.wires shortPart :=
  fun hm => site1Arith_window windowRoot List.mem_cons_self (shortPart_wires_sub hm)

theorem tailPart_root : windowRoot ∉ ECDSAAdd.wires tailPart :=
  fun hm => site1Arith_window windowRoot List.mem_cons_self (tailPart_wires_sub hm)

theorem site1_counts_split :
    ECDSAAdd.toffoliCount shortPart + ECDSAAdd.toffoliCount tailPart = ECDSAAdd.toffoliCount site1Arith ∧
    ECDSAAdd.measurementCount shortPart + ECDSAAdd.measurementCount tailPart = ECDSAAdd.measurementCount site1Arith ∧
    ECDSAAdd.Challenge.gateSlots shortPart + ECDSAAdd.Challenge.gateSlots tailPart = ECDSAAdd.Challenge.gateSlots site1Arith := by
  rw [site1Arith_eq, tailPart]
  simp only [ECDSAAdd.toffoliCount_append, ECDSAAdd.measurementCount_append,
    ECDSAAdd.Challenge.gateSlots_append]
  omega

theorem site1Arith_physical : GatePhysical site1Arith := by
  apply WEXUnlookup.rowC_physical site1Arith
  have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
    unfold WEXUnlookup.rowC; rfl
  have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
    unfold WEXUnlookup.rowHead; rfl
  rw [h1, h2, List.map_append, erase2_append, erase2_append]
  apply List.mem_append_left
  apply List.mem_append_left
  rw [WEXUnlookup.rowPre3]
  simp only [List.map_cons, List.map_nil, erase2_cons, erase2_nil, List.append_nil, toBlock2,
    Block2.code, UnitSite.code, site1, MaskedSite.prefix]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem shortPart_physical : GatePhysical shortPart := by
  have h := site1Arith_physical
  rw [site1Arith_eq] at h
  intro i hi
  exact h i (List.mem_append_right _ (List.mem_append_left _ hi))

theorem tailPart_physical : GatePhysical tailPart := by
  have h := site1Arith_physical
  rw [site1Arith_eq] at h
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact h i (List.mem_append_left _ hi)
  · exact h i (List.mem_append_right _ (List.mem_append_right _ hi))

theorem cBits_commute (c : Wire) (A B : List Wire) (kA kB : List Bool)
    (hcA : c ∉ A) (hcB : c ∉ B) (hAB : ∀ a ∈ A, a ∉ B) (s : ECDSAAdd.State) :
    ECDSAAdd.run (cBits c A kA) List.nil (ECDSAAdd.run (cBits c B kB) List.nil s) =
      ECDSAAdd.run (cBits c B kB) List.nil (ECDSAAdd.run (cBits c A kA) List.nil s) := by
  rw [cBits_run _ _ _ _ _ hcB, cBits_run _ _ _ _ _ hcA, cBits_run _ _ _ _ _ hcA, cBits_run _ _ _ _ _ hcB]
  simp only [xMask_outside B kB c hcB, xMask_outside A kA c hcA, Bool.and_false, Bool.xor_false]
  cases s with
  | mk ph b =>
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
    funext w
    dsimp only
    cases b w <;> cases b c <;> cases xMask A kA w <;> cases xMask B kB w <;> rfl

theorem portMask_append {n : Nat} (read : ConstantBit n → Bool) (ps₁ ps₂ : List (LookupPort n)) (a : Nat) :
    portMask read (ps₁ ++ ps₂) a = portMask read ps₁ a ++ portMask read ps₂ a := by
  induction ps₁ with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.cons_append, portMask, portTargets, List.map_cons, tableBitsMask] at ih ⊢
    by_cases h : decide (read (p.ref a) = p.value) = true
    · simp only [h, ↓reduceIte, List.cons_append, ih]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ih]

theorem xMask_get : ∀ (T : List Wire) (k : List Bool), T.Nodup → (hl : T.length = k.length) →
    ∀ (i : Nat) (hi : i < T.length), xMask T k (T[i]'hi) = k[i]'(hl ▸ hi)
  | [], [], _, _, _, hi => by simp at hi
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | t :: ts, b :: bs, hnd, hl, 0, _ => by
    have ⟨ht, _⟩ := List.nodup_cons.mp hnd
    simp [xMask, xMask_outside ts bs t ht]
  | t :: ts, b :: bs, hnd, hl, i + 1, hi => by
    have ⟨ht, hnd'⟩ := List.nodup_cons.mp hnd
    have hl' : ts.length = bs.length := by simpa using hl
    have hi' : i < ts.length := Nat.lt_of_succ_lt_succ hi
    have hne : ts[i]'hi' ≠ t := fun e => ht (e ▸ List.getElem_mem hi')
    simp only [List.getElem_cons_succ, xMask, hne, decide_false, Bool.false_and, Bool.false_xor]
    exact xMask_get ts bs hnd' hl' i hi'

theorem short_not_pairExtra : ∀ w ∈ shortWires, w ∉ pairExtraWires := by
  intro w hw hm
  rcases List.mem_append.mp hm with h | h
  · exact (List.nodup_append.mp scrWires_nodup).2.2 w h w hw rfl
  · exact extra_not_scrWires w h (List.mem_append_right _ hw)

theorem windowRoot_not_short : windowRoot ∉ shortWires :=
  fun h => windowRoot_not_scr (List.mem_append_right _ h)

theorem windowRoot_not_pairExtra : windowRoot ∉ pairExtraWires := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact windowRoot_not_scr (List.mem_append_left _ h)
  · have := extra_bounds windowRoot h; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega

/-- Loading all of `sitePorts` is identical to loading `shortPorts` followed by `pairExtraPorts`. -/
theorem siteLoad_eq_two {n : Nat} (read : ConstantBit n → Bool) (r : Nat → Fin n)
    (a : Nat) (s : ECDSAAdd.State) :
    let sp := WideSigned.Rows.ports r (shortPorts probeRows)
    let pp := WideSigned.Rows.ports r (pairExtraPorts probeRows)
    let allp := WideSigned.Rows.ports r (sitePorts probeRows)
    tableXorState (portMask read allp a) (s.basis windowRoot) s.basis =
      tableXorState (portMask read pp a) (s.basis windowRoot)
        (tableXorState (portMask read sp a) (s.basis windowRoot) s.basis) := by
  intro sp pp allp
  let p1 := WideSigned.Rows.ports r (retarget (scrPairBits probeRows (wBit probeRows .y)) scrPairWires)
  let p3 := WideSigned.Rows.ports r (negYExtraPorts probeRows)
  have hall : portMask read allp a = portMask read p1 a ++ portMask read sp a ++ portMask read p3 a := by
    simp only [allp, sp, p1, p3, sitePorts, scrInPorts, shortPorts, WideSigned.Rows.ports,
      List.map_append, portMask_append, List.append_assoc]
  have hpp : portMask read pp a = portMask read p1 a ++ portMask read p3 a := by
    simp only [pp, p1, p3, pairExtraPorts, WideSigned.Rows.ports, List.map_append, portMask_append]
  have hdisj_sp_p3 : ∀ w, w ∈ portMask read sp a → w ∉ portMask read p3 a := fun w h1 h2 => by
    have ha : w ∈ scrShortWires := by
      have := tableBitsMask_subset _ _ h1
      simpa [sp, WideSigned.Rows.targets, shortPorts_targets, shortWires] using this
    have hb : w ∈ scrDExtraWires := by
      have := tableBitsMask_subset _ _ h2
      simpa [p3, WideSigned.Rows.targets, negYExtra_targets] using this
    exact extra_not_scrWires w hb (List.mem_append_right _ ha)
  funext w
  simp only [tableXorState, hall, hpp, List.mem_append]
  by_cases h1 : w ∈ portMask read p1 a
  · have h2 : w ∉ portMask read sp a := fun hm => by
      have ha : w ∈ scrPairWires := by
        have := tableBitsMask_subset _ _ h1
        simpa [p1, WideSigned.Rows.targets,
          retarget_targets _ _ ((scrPairBits_length probeRows _).trans scrPairWires_length.symm)] using this
      have hb : w ∈ scrShortWires := by
        have := tableBitsMask_subset _ _ hm
        simpa [sp, WideSigned.Rows.targets, shortPorts_targets, shortWires] using this
      exact (List.nodup_append.mp scrWires_nodup).2.2 w ha w hb rfl
    simp [h1, h2]
  · by_cases h2 : w ∈ portMask read sp a
    · have h3 := hdisj_sp_p3 w h2
      simp [h1, h2, h3]
    · simp [h1, h2]

theorem twoPass_abstract (Lsp Lpp pairP shortP restP : ECDSAAdd.Program)
    (s : ECDSAAdd.State) (mA mB : List Bool)
    (hmA : mA.length = ECDSAAdd.measurementCount shortP)
    (hmB : mB.length = ECDSAAdd.measurementCount (pairP ++ restP))
    (hcomm_ps : ∀ t m₁ m₂, Clean (streamLayout.dialogPool.take 258) t.basis →
      ECDSAAdd.run (shortP ++ pairP) m₁ t = ECDSAAdd.run (pairP ++ shortP) m₂ t)
    (hclean : Clean (streamLayout.dialogPool.take 258) (ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil s)).basis)
    (hcomm_Lpp_short : ∀ k t, ECDSAAdd.run shortP k (ECDSAAdd.run Lpp List.nil t) = ECDSAAdd.run Lpp List.nil (ECDSAAdd.run shortP k t))
    (hcomm_Lsp_tail : ∀ k t, ECDSAAdd.run (pairP ++ restP) k (ECDSAAdd.run Lsp List.nil t) = ECDSAAdd.run Lsp List.nil (ECDSAAdd.run (pairP ++ restP) k t))
    (hcomm_Lpp_Lsp : ∀ t, ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil t) = ECDSAAdd.run Lsp List.nil (ECDSAAdd.run Lpp List.nil t)) :
    let mPerm := mB.take (ECDSAAdd.measurementCount pairP) ++ mA ++ mB.drop (ECDSAAdd.measurementCount pairP)
    ECDSAAdd.run Lpp List.nil (ECDSAAdd.run (pairP ++ restP) mB (ECDSAAdd.run Lpp List.nil
      (ECDSAAdd.run Lsp List.nil (ECDSAAdd.run shortP mA (ECDSAAdd.run Lsp List.nil s))))) =
    ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil
      (ECDSAAdd.run ((pairP ++ shortP) ++ restP) mPerm (ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil s)))) := by
  intro mPerm
  have hp_le : ECDSAAdd.measurementCount pairP ≤ mB.length := by
    rw [hmB, ECDSAAdd.measurementCount_append]; omega
  have hmc_ps : ECDSAAdd.measurementCount (pairP ++ shortP) =
      ECDSAAdd.measurementCount pairP + ECDSAAdd.measurementCount shortP :=
    ECDSAAdd.measurementCount_append _ _
  have htake_ps : mPerm.take (ECDSAAdd.measurementCount (pairP ++ shortP)) =
      mB.take (ECDSAAdd.measurementCount pairP) ++ mA := by
    rw [hmc_ps, show mPerm = (mB.take (ECDSAAdd.measurementCount pairP) ++ mA) ++
      mB.drop (ECDSAAdd.measurementCount pairP) from rfl, List.take_left' (by
      rw [List.length_append, List.length_take, Nat.min_eq_left hp_le, hmA])]
  have hdrop_ps : mPerm.drop (ECDSAAdd.measurementCount (pairP ++ shortP)) =
      mB.drop (ECDSAAdd.measurementCount pairP) := by
    rw [hmc_ps, show mPerm = (mB.take (ECDSAAdd.measurementCount pairP) ++ mA) ++
      mB.drop (ECDSAAdd.measurementCount pairP) from rfl, List.drop_left' (by
      rw [List.length_append, List.length_take, Nat.min_eq_left hp_le, hmA])]
  rw [ECDSAAdd.run_append (pairP ++ shortP) restP, htake_ps, hdrop_ps,
    ← hcomm_ps _ (mA ++ mB.take (ECDSAAdd.measurementCount pairP)) _ hclean,
    ECDSAAdd.run_append shortP pairP, ← hmA, List.take_left, List.drop_left]
  have hre : ECDSAAdd.run restP (mB.drop (ECDSAAdd.measurementCount pairP))
      (ECDSAAdd.run pairP (mB.take (ECDSAAdd.measurementCount pairP))
        (ECDSAAdd.run shortP mA (ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil s)))) =
      ECDSAAdd.run (pairP ++ restP) mB (ECDSAAdd.run shortP mA (ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil s))) := by
    rw [ECDSAAdd.run_append pairP restP]
  rw [hre, hcomm_Lpp_short, hcomm_Lpp_Lsp, hcomm_Lsp_tail, hcomm_Lpp_Lsp]

/-- Key two-pass equivalence on `ECDSAAdd.run`: running Pass A (`shortPorts` + `shortPart`)
    then Pass B (`pairExtraPorts` + `tailPart`) computes the exact same state as `site1`
    with permuted measurement list `mB_pair ++ mA ++ mB_pair1`. -/
theorem site1_twoPass_run {n : Nat} (read : ConstantBit n → Bool) (r : Nat → Fin n)
    (a : Nat) (s : ECDSAAdd.State) (mA mB : List Bool)
    (hmA : mA.length = ECDSAAdd.measurementCount shortPart)
    (hmB : mB.length = ECDSAAdd.measurementCount tailPart)
    (hroot : s.basis windowRoot = true)
    (hclean : Clean (streamLayout.dialogPool.take 258) s.basis) :
    let sp := WideSigned.Rows.ports r (shortPorts probeRows)
    let pp := WideSigned.Rows.ports r (pairExtraPorts probeRows)
    let sL1 : ECDSAAdd.State := ⟨s.phase, tableXorState (portMask read sp a) true s.basis⟩
    let sA1 := ECDSAAdd.run shortPart mA sL1
    let sMid : ECDSAAdd.State := ⟨sA1.phase, tableXorState (portMask read sp a) true sA1.basis⟩
    let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp a) true sMid.basis⟩
    let sB1 := ECDSAAdd.run tailPart mB sL2
    let sOut : ECDSAAdd.State := ⟨sB1.phase, tableXorState (portMask read pp a) true sB1.basis⟩
    let mPerm := mB.take (ECDSAAdd.measurementCount pairPart) ++ mA ++ mB.drop (ECDSAAdd.measurementCount pairPart)
    mPerm.length = ECDSAAdd.measurementCount site1Arith ∧
    sOut = ECDSAAdd.run ((specialize (WideSigned.Rows.site r (site1 probeRows)).code a).instantiate read) mPerm s := by
  intro sp pp sL1 sA1 sMid sL2 sB1 sOut mPerm
  let allp := WideSigned.Rows.ports r (sitePorts probeRows)
  have hmc_len : mPerm.length = ECDSAAdd.measurementCount site1Arith := by
    have hcs := site1_counts_split.2.1
    have htail_mc : ECDSAAdd.measurementCount pairPart ≤ ECDSAAdd.measurementCount tailPart := by
      rw [tailPart, ECDSAAdd.measurementCount_append]; omega
    simp only [mPerm, List.length_append, List.length_take, List.length_drop]
    omega
  refine ⟨hmc_len, ?_⟩
  have hsp_t : portTargets sp = shortWires := by
    simpa [sp, WideSigned.Rows.targets] using shortPorts_targets probeRows
  have hpp_t : portTargets pp = pairExtraWires := by
    simpa [pp, WideSigned.Rows.targets] using pairExtraPorts_targets probeRows
  have hall_t : portTargets allp = scrAllWires := by
    simpa [allp, WideSigned.Rows.targets] using sitePorts_targets probeRows
  have hsp_nd : (portTargets sp).Nodup := by rw [hsp_t]; exact scrShortWires_nd
  have hpp_nd : (portTargets pp).Nodup := by
    rw [hpp_t, pairExtraWires, List.nodup_append]
    refine ⟨scrPairWires_nd, ?_, fun x hx y hy hxy => ?_⟩
    · have := (List.nodup_append.mp WEX.scrAllWires_nodup).2.1
      simpa [scrAllWires] using this
    · subst hxy
      exact extra_not_scrWires x hy (List.mem_append_left _ hx)
  have hall_nd : (portTargets allp).Nodup := by rw [hall_t]; exact WEX.scrAllWires_nodup
  have hroot_all : windowRoot ∉ portTargets allp := by
    rw [hall_t]; intro h; rcases List.mem_append.mp h with h | h
    · exact windowRoot_not_scr h
    · have := extra_bounds windowRoot h; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega
  have hrhs_inst : (specialize (WideSigned.Rows.site r (site1 probeRows)).code a).instantiate read =
      (portTemplate (some windowRoot) allp a).instantiate read ++
        (site1Arith ++ (portTemplate (some windowRoot) allp a).instantiate read) := by
    simp only [WideSigned.Rows.site, site1, MaskedSite.code, MaskedSite.prefix, specialize,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, WInstr.specialize,
      Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit, List.append_nil,
      List.append_assoc, WideSigned.Rows.code, WideSigned.Rows.instr, wLiteral, List.map_cons,
      List.map_nil]
    rfl
  rw [hrhs_inst]
  have hpt_all (t : ECDSAAdd.State) (hr : t.basis windowRoot = true) :
      ECDSAAdd.run ((portTemplate (some windowRoot) allp a).instantiate read) List.nil t =
        ⟨t.phase, tableXorState (portMask read allp a) true t.basis⟩ := by
    simpa [lookupRoot, hr] using portTemplate_run read (some windowRoot) allp a windowRoot List.nil t hall_nd hroot_all hr
  have hpt_all_mc : ECDSAAdd.measurementCount ((portTemplate (some windowRoot) allp a).instantiate read) = 0 :=
    (portTemplate_counts read (some windowRoot) allp a).2
  rw [run_zero_append _ _ hpt_all_mc, hpt_all s hroot, run_meas_append site1Arith,
    run_zero_records _ hpt_all_mc]
  have hxor_cBits (ps : List (LookupPort n)) (hnd : (portTargets ps).Nodup) (hrp : windowRoot ∉ portTargets ps)
      (t : ECDSAAdd.State) (hr : t.basis windowRoot = true) :
      (⟨t.phase, tableXorState (portMask read ps a) true t.basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run (cBits windowRoot (portTargets ps) (portBits read ps a)) List.nil t := by
    rw [cBits_run windowRoot _ _ List.nil t hrp]
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
    funext w
    simp only [hr, Bool.true_and, tableXorState]
    by_cases hw : w ∈ portTargets ps
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      have hi' : i < ps.length := by simpa [portTargets] using hi
      have hp : ps[i]'hi' ∈ ps := List.getElem_mem hi'
      have hmask : (portTargets ps)[i]'hi ∈ portMask read ps a ↔
          decide (read ((ps[i]'hi').ref a) = (ps[i]'hi').value) = true := by
        have hps := port_selected read ps a hnd (ps[i]'hi') hp
        simpa [portTargets, List.getElem_map] using hps
      have hxmask : xMask (portTargets ps) (portBits read ps a) ((portTargets ps)[i]'hi) =
          decide (read ((ps[i]'hi').ref a) = (ps[i]'hi').value) := by
        have hlen : (portTargets ps).length = (portBits read ps a).length := by simp [portTargets, portBits]
        have hx := xMask_get (portTargets ps) (portBits read ps a) hnd hlen i hi
        simpa [portBits, List.getElem_map] using hx
      rw [hxmask]
      by_cases hb : decide (read ((ps[i]'hi').ref a) = (ps[i]'hi').value) = true
      · simp [hb, hmask.mpr hb]
      · have hbf : decide (read ((ps[i]'hi').ref a) = (ps[i]'hi').value) = false := Bool.eq_false_iff.mpr hb
        have hnm : (portTargets ps)[i]'hi ∉ portMask read ps a := fun hm => hb (hmask.mp hm)
        simp [hbf, hnm]
    · have hnm : w ∉ portMask read ps a := fun hm => hw (tableBitsMask_subset _ _ hm)
      rw [xMask_outside _ _ w hw]
      simp [hnm]
  have hroot_sp : windowRoot ∉ portTargets sp := by rw [hsp_t]; exact windowRoot_not_short
  have hroot_pp : windowRoot ∉ portTargets pp := by rw [hpp_t]; exact windowRoot_not_pairExtra
  set Lsp := cBits windowRoot (portTargets sp) (portBits read sp a)
  set Lpp := cBits windowRoot (portTargets pp) (portBits read pp a)
  have hroot_Lsp (t : ECDSAAdd.State) (hr : t.basis windowRoot = true) :
      (ECDSAAdd.run Lsp List.nil t).basis windowRoot = true := by
    rw [cBits_run _ _ _ _ _ hroot_sp]; dsimp only
    rw [xMask_outside _ _ windowRoot hroot_sp]; simpa using hr
  have hroot_Lpp (t : ECDSAAdd.State) (hr : t.basis windowRoot = true) :
      (ECDSAAdd.run Lpp List.nil t).basis windowRoot = true := by
    rw [cBits_run _ _ _ _ _ hroot_pp]; dsimp only
    rw [xMask_outside _ _ windowRoot hroot_pp]; simpa using hr
  have hroot_short (t : ECDSAAdd.State) (k : List Bool) (hr : t.basis windowRoot = true) :
      (ECDSAAdd.run shortPart k t).basis windowRoot = true := by
    rw [run_outside_basis shortPart k t windowRoot shortPart_root]; exact hr
  have hroot_tail (t : ECDSAAdd.State) (k : List Bool) (hr : t.basis windowRoot = true) :
      (ECDSAAdd.run tailPart k t).basis windowRoot = true := by
    rw [run_outside_basis tailPart k t windowRoot tailPart_root]; exact hr
  have h1 : sL1 = ECDSAAdd.run Lsp List.nil s := hxor_cBits sp hsp_nd hroot_sp s hroot
  have hr1 : sL1.basis windowRoot = true := h1 ▸ hroot_Lsp s hroot
  have h2 : sA1 = ECDSAAdd.run shortPart mA (ECDSAAdd.run Lsp List.nil s) := congrArg (ECDSAAdd.run shortPart mA) h1
  have hr2 : sA1.basis windowRoot = true := hroot_short sL1 mA hr1
  have h3 : sMid = ECDSAAdd.run Lsp List.nil (ECDSAAdd.run shortPart mA (ECDSAAdd.run Lsp List.nil s)) :=
    (hxor_cBits sp hsp_nd hroot_sp sA1 hr2).trans (congrArg (ECDSAAdd.run Lsp List.nil) h2)
  have hr3 : sMid.basis windowRoot = true := h3 ▸ hroot_Lsp _ (hroot_short _ mA (hroot_Lsp s hroot))
  have h4 : sL2 = ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil (ECDSAAdd.run shortPart mA (ECDSAAdd.run Lsp List.nil s))) :=
    (hxor_cBits pp hpp_nd hroot_pp sMid hr3).trans (congrArg (ECDSAAdd.run Lpp List.nil) h3)
  have hr4 : sL2.basis windowRoot = true := h4 ▸ hroot_Lpp _ (hroot_Lsp _ (hroot_short _ mA (hroot_Lsp s hroot)))
  have h5 : sB1 = ECDSAAdd.run tailPart mB (ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil (ECDSAAdd.run shortPart mA (ECDSAAdd.run Lsp List.nil s)))) :=
    congrArg (ECDSAAdd.run tailPart mB) h4
  have hr5 : sB1.basis windowRoot = true := hroot_tail sL2 mB hr4
  have hsOut_eq : sOut = ECDSAAdd.run Lpp List.nil (ECDSAAdd.run tailPart mB (ECDSAAdd.run Lpp List.nil
      (ECDSAAdd.run Lsp List.nil (ECDSAAdd.run shortPart mA (ECDSAAdd.run Lsp List.nil s))))) :=
    (hxor_cBits pp hpp_nd hroot_pp sB1 hr5).trans (congrArg (ECDSAAdd.run Lpp List.nil) h5)
  have hall_eq (t : ECDSAAdd.State) (hr : t.basis windowRoot = true) :
      (⟨t.phase, tableXorState (portMask read allp a) true t.basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil t) := by
    have h1' := siteLoad_eq_two read r a t
    rw [hr] at h1'
    rw [← hxor_cBits pp hpp_nd hroot_pp _ (hroot_Lsp t hr), ← hxor_cBits sp hsp_nd hroot_sp t hr]
    exact ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, h1'⟩
  have hroot_site : (ECDSAAdd.run site1Arith mPerm
      ⟨s.phase, tableXorState (portMask read allp a) true s.basis⟩).basis windowRoot = true := by
    have hroot_sAll : (⟨s.phase, tableXorState (portMask read allp a) true s.basis⟩ : ECDSAAdd.State).basis windowRoot = true := by
      rw [hall_eq s hroot]; exact hroot_Lpp _ (hroot_Lsp s hroot)
    rw [run_outside_basis site1Arith mPerm _ windowRoot (site1Arith_window windowRoot List.mem_cons_self)]
    exact hroot_sAll
  rw [hpt_all _ hroot_site, hall_eq _ hroot_site, hall_eq s hroot, hsOut_eq]
  let rest := pointDialogGenericFlag streamLayout ++ (ECDSAAdd.Frontier.zrep streamLayout ++ pair1Prog)
  have hsite1_split : site1Arith = (pairPart ++ shortPart) ++ rest := by
    rw [site1Arith_eq]; simp [rest, List.append_assoc]
  have htail_split : tailPart = pairPart ++ rest := rfl
  have hclean_all : Clean (streamLayout.dialogPool.take 258)
      (ECDSAAdd.run Lpp List.nil (ECDSAAdd.run Lsp List.nil s)).basis := by
    have hpool_sp : ∀ w ∈ streamLayout.dialogPool.take 258, w ∉ portTargets sp := by
      intro w hw hm
      rw [mem_pool_take 258 (by decide)] at hw
      rw [hsp_t] at hm
      have := shortWires_bounds w hm
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    have hpool_pp : ∀ w ∈ streamLayout.dialogPool.take 258, w ∉ portTargets pp := by
      intro w hw hm
      rw [mem_pool_take 258 (by decide)] at hw
      rw [hpp_t, pairExtraWires, List.mem_append] at hm
      rcases hm with hm | hm
      · have := pairWires_bounds w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · have := extra_bounds w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    intro w hw
    rw [cBits_run _ _ _ _ _ hroot_pp]; dsimp only
    rw [xMask_outside _ _ w (hpool_pp w hw), cBits_run _ _ _ _ _ hroot_sp]; dsimp only
    rw [xMask_outside _ _ w (hpool_sp w hw)]
    simpa using hclean w hw
  rw [hsite1_split, htail_split]
  exact twoPass_abstract Lsp Lpp pairPart shortPart rest s mA mB hmA hmB
    (fun t m₁ m₂ hc => shortPart_pairPart_comm t m₁ m₂ hc) hclean_all
    (fun k t => load_commute windowRoot (portTargets pp) (portBits read pp a) shortPart
      shortPart_root (by rw [hpp_t]; exact shortPart_avoid_pairExtra) k t)
    (fun k t => load_commute windowRoot (portTargets sp) (portBits read sp a) tailPart
      tailPart_root (by rw [hsp_t]; exact tailPart_avoid_short) k t)
    (fun t => cBits_commute windowRoot (portTargets pp) (portTargets sp) _ _ hroot_pp hroot_sp
      (by rw [hpp_t, hsp_t]; exact fun w hw hm => short_not_pairExtra w hm hw) t)

/-! ### Part 2: Bank-generic SelectSwap load + swap gadgets (2-bit and 1-bit) -/

/-- A bank-generic 2-bit SelectSwap load + swap gadget (4 registers: targets + `g1, g2, g3`). -/
structure SS2 (n : Nat) where
  bits : List Wire
  paths : List Wire
  selBits : List Wire
  selPaths : List Wire
  guard : Wire
  ports : List (LookupPort n)
  g1 : List Wire
  g2 : List Wire
  g3 : List Wire

namespace SS2
variable {n : Nat} (f : SS2 n)

def garb : List Wire := f.g1 ++ f.g2 ++ f.g3

def rowOf1 (a : Nat) : Nat := 4 * (a / 4) + (1 - a % 2)
def rowOf2 (a : Nat) : Nat := 4 * (a / 4) + 2 * (1 - a / 2 % 2) + a % 2
def rowOf3 (a : Nat) : Nat := 4 * (a / 4) + 3 - a % 2

def selPorts : List (LookupPort n) :=
  f.ports.map (fun p => ⟨fun h => p.ref (4 * h), p.value, p.target⟩) ++
  WideBank8.Fast16.regPorts (fun h => 4 * h + 1) f.ports f.g1 ++
  WideBank8.Fast16.regPorts (fun h => 4 * h + 2) f.ports f.g2 ++
  WideBank8.Fast16.regPorts (fun h => 4 * h + 3) f.ports f.g3

def garbPorts : List (LookupPort n) :=
  WideBank8.Fast16.regPorts rowOf1 f.ports f.g1 ++
  WideBank8.Fast16.regPorts rowOf2 f.ports f.g2 ++
  WideBank8.Fast16.regPorts rowOf3 f.ports f.g3

def swapNet : ECDSAAdd.Program :=
  WideBank8.Fast16.swapLayer 855 (portTargets f.ports) f.g1 ++
  WideBank8.Fast16.swapLayer 855 f.g2 f.g3 ++
  WideBank8.Fast16.swapLayer 856 (portTargets f.ports) f.g2

def selCode : WCode n := [.lookup (some f.guard) f.selPorts]

def loadProg (start : Nat) : Straight n start (start + codeRecords f.selBits f.selPaths windowRoot f.selCode) :=
  castFinish (by omega)
    ((compile f.selBits f.selPaths windowRoot f.selCode start).append
      (literalFixed f.swapNet 0 ((literal_meas (n := n) _).trans (by
        simp [swapNet, ECDSAAdd.measurementCount_append, WideBank8.Fast16.swapLayer_meas]))
        (start + codeRecords f.selBits f.selPaths windowRoot f.selCode)))

def loadSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  (source read f.selBits f.selPaths windowRoot f.selCode).seq (literalSource f.swapNet)

structure Geo : Prop where
  bitsEq : f.bits = 855 :: 856 :: f.selBits
  pathsSub : ∀ w ∈ f.selPaths, w ∈ f.paths
  selLen : f.selPaths.length = f.selBits.length
  selNodup : (f.guard :: f.selBits ++ f.selPaths).Nodup
  selDisj : List.Disjoint (windowRoot :: f.guard :: f.selBits ++ f.selPaths) (portTargets f.ports ++ f.garb)
  len1 : f.g1.length = f.ports.length
  len2 : f.g2.length = f.ports.length
  len3 : f.g3.length = f.ports.length
  nodup : (portTargets f.ports ++ f.garb).Nodup
  n855 : (855 : Wire) ∉ portTargets f.ports ++ f.garb
  n856 : (856 : Wire) ∉ portTargets f.ports ++ f.garb

theorem selPorts_targets (hg : f.Geo) : portTargets f.selPorts = portTargets f.ports ++ f.garb := by
  have h1 : portTargets (WideBank8.Fast16.regPorts (fun h => 4 * h + 1) f.ports f.g1) = f.g1 :=
    WideBank8.Fast16.regPorts_targets _ _ _ hg.len1
  have h2 : portTargets (WideBank8.Fast16.regPorts (fun h => 4 * h + 2) f.ports f.g2) = f.g2 :=
    WideBank8.Fast16.regPorts_targets _ _ _ hg.len2
  have h3 : portTargets (WideBank8.Fast16.regPorts (fun h => 4 * h + 3) f.ports f.g3) = f.g3 :=
    WideBank8.Fast16.regPorts_targets _ _ _ hg.len3
  simp only [selPorts, WideBank8.Fast16.FastSite.portTargets_append, h1, h2, h3, garb, List.append_assoc]
  congr 1
  simp [portTargets, List.map_map, Function.comp_def]

theorem garbPorts_targets (hg : f.Geo) : portTargets f.garbPorts = f.garb := by
  have h1 := WideBank8.Fast16.regPorts_targets rowOf1 f.ports f.g1 hg.len1
  have h2 := WideBank8.Fast16.regPorts_targets rowOf2 f.ports f.g2 hg.len2
  have h3 := WideBank8.Fast16.regPorts_targets rowOf3 f.ports f.g3 hg.len3
  simp only [garbPorts, WideBank8.Fast16.FastSite.portTargets_append, h1, h2, h3, garb]

theorem garbPorts_length (hg : f.Geo) : f.garbPorts.length = 3 * f.ports.length := by
  have h := congrArg List.length (garbPorts_targets f hg)
  simp only [portTargets, List.length_map, garb, List.length_append, hg.len1, hg.len2, hg.len3] at h
  omega

theorem selPorts_length (hg : f.Geo) : f.selPorts.length = 4 * f.ports.length := by
  have h := congrArg List.length (selPorts_targets f hg)
  simp only [portTargets, List.length_map, List.length_append, garb, hg.len1, hg.len2, hg.len3] at h
  omega

theorem sel_placed (hg : f.Geo) : Placed f.selBits f.selPaths windowRoot (.lookup (some f.guard) f.selPorts) := by
  refine ⟨by simpa [lookupRoot] using hg.selNodup, by rw [selPorts_targets f hg]; exact hg.nodup,
    by rw [selPorts_targets f hg]; simpa [lookupRoot] using hg.selDisj⟩

theorem sel_layouts (hg : f.Geo) : LookupLayouts f.selBits f.selPaths windowRoot f.selCode := by
  refine ⟨hg.selLen.ge, fun c ps hm => ?_⟩
  simp only [selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  simpa [lookupRoot] using hg.selNodup

theorem swapNet_toff (hg : f.Geo) : ECDSAAdd.toffoliCount f.swapNet = 3 * f.ports.length := by
  have ht : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  simp only [swapNet, ECDSAAdd.toffoliCount_append, WideBank8.Fast16.swapLayer_toff, ht,
    hg.len1, hg.len2, hg.len3, Nat.min_self]
  omega

theorem swapNet_slots (hg : f.Geo) : ECDSAAdd.Challenge.gateSlots f.swapNet = 9 * f.ports.length := by
  have ht : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  simp only [swapNet, ECDSAAdd.Challenge.gateSlots_append, WideBank8.Fast16.swapLayer_slots, ht,
    hg.len1, hg.len2, hg.len3, Nat.min_self]
  omega

theorem swapNet_valid (hg : f.Geo) : ∀ i ∈ f.swapNet, ECDSAAdd.Challenge.instructionValid i := by
  have sub1 : List.Sublist (portTargets f.ports ++ f.g1) (portTargets f.ports ++ f.garb) :=
    ((List.sublist_append_left f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have sub2 : List.Sublist (f.g2 ++ f.g3) (portTargets f.ports ++ f.garb) := by
    have h23 : List.Sublist (f.g2 ++ f.g3) f.garb := by
      simp only [garb, List.append_assoc]; exact List.sublist_append_right f.g1 (f.g2 ++ f.g3)
    exact h23.trans (List.sublist_append_right _ _)
  have sub3 : List.Sublist (portTargets f.ports ++ f.g2) (portTargets f.ports ++ f.garb) :=
    ((List.sublist_append_right f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have hp1 := WideBank8.Fast16.swapLayer_valid 855 _ _ (fun h => hg.n855 (sub1.subset h)) (hg.nodup.sublist sub1)
  have hp2 := WideBank8.Fast16.swapLayer_valid 855 _ _ (fun h => hg.n855 (sub2.subset h)) (hg.nodup.sublist sub2)
  have hp3 := WideBank8.Fast16.swapLayer_valid 856 _ _ (fun h => hg.n856 (sub3.subset h)) (hg.nodup.sublist sub3)
  intro i hi
  simp only [swapNet, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact hp1 i hi
  · exact hp2 i hi
  · exact hp3 i hi

theorem loadProg_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.loadProg start).instantiate read history).run = (f.loadSource read).run := by
  rw [loadProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h),
    AdaptiveCircuit.run_seq, compile_run]
  simp only [loadSource, AdaptiveCircuit.run_seq]

theorem loadProg_tCount (read : ConstantBit n → Bool) (hg : f.Geo) (start : Nat) (history : Fin start → Bool) :
    ((f.loadProg start).instantiate read history).tCount =
      7 * (2 ^ f.selBits.length - 1 + 3 * f.ports.length) := by
  rw [loadProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read f.selBits f.selPaths windowRoot f.selCode (sel_layouts f hg),
    swapNet_toff f hg]
  simp only [selCode, literalToffolis, traversals, Nat.zero_add, Nat.one_mul]
  ring

theorem loadProg_records (hg : f.Geo) :
    codeRecords f.selBits f.selPaths windowRoot f.selCode = 2 ^ f.selBits.length - 1 := by
  rw [codeRecords_eq _ _ _ _ (sel_layouts f hg)]
  simp [selCode, literalRecords, traversals]

theorem loadProg_slots (hg : f.Geo) (start : Nat) :
    (f.loadProg start).gateSlots ≤ 2 ^ f.selBits.length * (4 * f.ports.length) + 10 * (2 ^ f.selBits.length - 1) +
      36 * f.ports.length := by
  rw [loadProg, castFinish_gateSlots, Straight.gateSlots_append,
    compile_slots _ _ _ _ (sel_layouts f hg), literalFixed_slots]
  have h1 : codeSlots f.selBits f.selCode = 2 ^ f.selBits.length * f.selPorts.length + 10 * (2 ^ f.selBits.length - 1) := by
    simp [selCode, codeSlots]
  have h2 := literal_slot_bound (n := n) f.swapNet
  rw [swapNet_slots f hg] at h2
  rw [h1, selPorts_length f hg]
  omega

theorem loadProg_wellFormed (hg : f.Geo) (start : Nat) : (f.loadProg start).WellFormed := by
  rw [loadProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ ?_ (literalFixed_wellFormed _ _ _ (swapNet_valid f hg) _)
  exact pair_compile_wellFormed _ _ _ _ hg.selLen.ge
    (fun i hi => by
      simp only [selCode, List.mem_singleton] at hi; subst hi
      exact placed_implies_pair _ _ _ _ (sel_placed f hg))
    (fun p hp => by simp [selCode] at hp) start

theorem loadProg_residue (start : Nat) : AndGadget.residue (f.loadProg start) = 0 := by
  rw [loadProg, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
    literalFixed, WEXCredit.residue_naive_cast, WEXCredit.literal_residue]

theorem loadProg_support (hg : f.Geo) (S : List Wire)
    (hroot : windowRoot ∈ S) (hguard : f.guard ∈ S) (h855 : (855 : Wire) ∈ S) (h856 : (856 : Wire) ∈ S)
    (hbits : f.selBits ⊆ S) (hpaths : f.selPaths ⊆ S) (hreg : portTargets f.ports ++ f.garb ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (f.loadProg start) ⊆ S := by
  rw [loadProg, support_cast, straightWires_append]
  refine List.append_subset.mpr ⟨?_, ?_⟩
  · refine compile_support f.selBits f.selPaths windowRoot f.selCode S hroot hbits hpaths
      (fun p hp => by simp [selCode] at hp) ?_ start
    intro c ps hm
    simp only [selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨fun q hq => by rw [Option.mem_def, Option.some_inj] at hq; exact hq ▸ hguard,
      by rw [selPorts_targets f hg]; exact hreg⟩
  · refine literalFixed_support _ _ _ S ?_ _
    intro w hw
    simp only [swapNet, ECDSAAdd.wires_append, Finset.mem_union] at hw
    simp only [List.mem_toFinset]
    rcases hw with (hw | hw) | hw
    · have h := WideBank8.Fast16.swapLayer_wires 855 _ _ hw
      simp only [List.mem_toFinset, List.cons_append, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact h855
      · exact hreg (List.mem_append_left _ h)
      · exact hreg (List.mem_append_right _ (by simp [garb, h]))
    · have h := WideBank8.Fast16.swapLayer_wires 855 _ _ hw
      simp only [List.mem_toFinset, List.cons_append, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact h855
      · exact hreg (List.mem_append_right _ (by simp [garb, h]))
      · exact hreg (List.mem_append_right _ (by simp [garb, h]))
    · have h := WideBank8.Fast16.swapLayer_wires 856 _ _ hw
      simp only [List.mem_toFinset, List.cons_append, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact h856
      · exact hreg (List.mem_append_left _ h)
      · exact hreg (List.mem_append_right _ (by simp [garb, h]))

theorem load_state (read : ConstantBit n → Bool) (hg : f.Geo) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid f.bits f.paths windowRoot a st)
    (hc : Clean (portTargets f.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue f.selBits st.basis)).instantiate read) List.nil st)
    s₂.phase = st.phase ∧
    (∀ w, w ∉ portTargets f.ports → w ∉ f.garb → s₂.basis w = st.basis w) ∧
    (∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.guard && decide (read (q.ref a) = q.value))) ∧
    clearRegister f.garb s₂.basis = tableXorState (portMask read f.ports a) (st.basis f.guard) st.basis := by
  intro s₂
  have hsel := selPorts_targets f hg
  have hselnd : (portTargets f.selPorts).Nodup := by rw [hsel]; exact hg.nodup
  have hguard : f.guard ∉ portTargets f.selPorts := by
    rw [hsel]; exact List.disjoint_left.mp hg.selDisj (by simp)
  have lt : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  have hnd_app := List.nodup_append.mp hg.nodup
  have hd : ∀ w ∈ f.garb, w ∉ portTargets f.ports := fun w hw hm => hnd_app.2.2 w hm w hw rfl
  have hgn := hnd_app.2.1
  have h' := List.nodup_append.mp hgn
  have h'' := List.nodup_append.mp h'.1
  have d1 : ∀ w ∈ f.g1, w ∉ portTargets f.ports := fun w hw => hd w (by simp [garb, hw])
  have d2 : ∀ w ∈ f.g2, w ∉ portTargets f.ports := fun w hw => hd w (by simp [garb, hw])
  have d3 : ∀ w ∈ f.g3, w ∉ portTargets f.ports := fun w hw => hd w (by simp [garb, hw])
  have d21 : ∀ w ∈ f.g2, w ∉ f.g1 := fun w hw h1 => h''.2.2 w h1 w hw rfl
  have d31 : ∀ w ∈ f.g3, w ∉ f.g1 := fun w hw h1 => h'.2.2 w (List.mem_append_left _ h1) w hw rfl
  have d32 : ∀ w ∈ f.g3, w ∉ f.g2 := fun w hw h2 => h'.2.2 w (List.mem_append_right _ h2) w hw rfl
  set h := tableAddressValue f.selBits st.basis with hh
  have e1 : specialize f.selCode h = portTemplate (some f.guard) f.selPorts h := by
    simp [selCode, specialize, WInstr.specialize]
  set s₁ := ECDSAAdd.run ((specialize f.selCode h).instantiate read) List.nil st with hs₁
  have r1 : s₁ = ⟨st.phase, tableXorState (portMask read f.selPorts h) (st.basis f.guard) st.basis⟩ := by
    rw [hs₁, e1]
    exact portTemplate_run read (some f.guard) f.selPorts h windowRoot List.nil st hselnd hguard hs.2.2
  have sel_at : ∀ q ∈ f.selPorts, s₁.basis q.target =
      (st.basis f.guard && decide (read (q.ref h) = q.value)) := by
    intro q hq
    rw [r1]; show tableXorState _ _ _ q.target = _
    simp only [tableXorState, port_selected read f.selPorts h hselnd q hq]
    have hm : q.target ∈ portTargets f.selPorts := List.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hsel] at hm
    simp [hc _ hm]
  have frame1 : ∀ w, w ∉ portTargets f.ports → w ∉ f.garb → s₁.basis w = st.basis w := by
    intro w h1 h2
    rw [r1]; show tableXorState _ _ _ w = _
    apply tableXorState_outside
    intro hm
    have hm' := tableBitsMask_subset _ _ hm
    rw [hsel] at hm'
    rcases List.mem_append.mp hm' with h | h
    · exact h1 h
    · exact h2 h
  have H0 : WideBank8.Fast16.FastSite.Holds read f.ports (portTargets f.ports) (4 * h) (st.basis f.guard) s₁.basis := by
    intro i hi hgi
    have hq : (⟨fun h => (f.ports[i]'hi).ref (4 * h), (f.ports[i]'hi).value, (f.ports[i]'hi).target⟩ : LookupPort n) ∈
        f.selPorts := by
      simp only [selPorts, List.mem_append]; left; left; left
      exact List.mem_map.mpr ⟨f.ports[i]'hi, List.getElem_mem hi, rfl⟩
    simpa [portTargets, List.getElem_map] using sel_at _ hq
  have H1 : WideBank8.Fast16.FastSite.Holds read f.ports f.g1 (4 * h + 1) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; left; left; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have H2 : WideBank8.Fast16.FastSite.Holds read f.ports f.g2 (4 * h + 2) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; left; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have H3 : WideBank8.Fast16.FastSite.Holds read f.ports f.g3 (4 * h + 3) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have sub1 : List.Sublist (portTargets f.ports ++ f.g1) (portTargets f.ports ++ f.garb) :=
    ((List.sublist_append_left f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have sub2 : List.Sublist (f.g2 ++ f.g3) (portTargets f.ports ++ f.garb) := by
    have h23 : List.Sublist (f.g2 ++ f.g3) f.garb := by
      simp only [garb, List.append_assoc]; exact List.sublist_append_right f.g1 (f.g2 ++ f.g3)
    exact h23.trans (List.sublist_append_right _ _)
  have sub3 : List.Sublist (portTargets f.ports ++ f.g2) (portTargets f.ports ++ f.garb) :=
    ((List.sublist_append_right f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have nd1 := hg.nodup.sublist sub1
  have nd2 := hg.nodup.sublist sub2
  have nd3 := hg.nodup.sublist sub3
  have c1 : (855 : Wire) ∉ portTargets f.ports ++ f.g1 := fun h => hg.n855 (sub1.subset h)
  have c2 : (855 : Wire) ∉ f.g2 ++ f.g3 := fun h => hg.n855 (sub2.subset h)
  have c3 : (856 : Wire) ∉ portTargets f.ports ++ f.g2 := fun h => hg.n856 (sub3.subset h)
  set t₁ := ECDSAAdd.run (WideBank8.Fast16.swapLayer 855 (portTargets f.ports) f.g1) List.nil s₁ with ht₁
  set t₂ := ECDSAAdd.run (WideBank8.Fast16.swapLayer 855 f.g2 f.g3) List.nil t₁ with ht₂
  have hs₂ : s₂ = ECDSAAdd.run (WideBank8.Fast16.swapLayer 856 (portTargets f.ports) f.g2) List.nil t₂ := by
    show ECDSAAdd.run f.swapNet List.nil s₁ = _
    simp only [swapNet, ECDSAAdd.run_append, ECDSAAdd.measurementCount_append, WideBank8.Fast16.swapLayer_meas,
      Nat.add_zero, List.take_zero, List.drop_zero, List.take_nil, List.drop_nil]
    rw [ht₂, ht₁]
  obtain ⟨p1, fr1, -⟩ := WideBank8.Fast16.swapLayer_run 855 _ _ c1 nd1 (by rw [lt, hg.len1]) s₁ List.nil
  obtain ⟨p2, fr2, -⟩ := WideBank8.Fast16.swapLayer_run 855 _ _ c2 nd2 (by rw [hg.len2, hg.len3]) t₁ List.nil
  obtain ⟨p3, fr3, -⟩ := WideBank8.Fast16.swapLayer_run 856 _ _ c3 nd3 (by rw [lt, hg.len2]) t₂ List.nil
  have frame : ∀ w, w ∉ portTargets f.ports → w ∉ f.garb → s₂.basis w = st.basis w := fun w h1 h2 => by
    rw [hs₂, fr3 w h1 (fun hm => h2 (by simp [garb, hm])),
      ht₂, fr2 w (fun hm => h2 (by simp [garb, hm])) (fun hm => h2 (by simp [garb, hm])),
      ht₁, fr1 w h1 (fun hm => h2 (by simp [garb, hm])), frame1 w h1 h2]
  have n855t : (855 : Wire) ∉ portTargets f.ports := fun h => hg.n855 (List.mem_append_left _ h)
  have n855g : (855 : Wire) ∉ f.garb := fun h => hg.n855 (List.mem_append_right _ h)
  have n856t : (856 : Wire) ∉ portTargets f.ports := fun h => hg.n856 (List.mem_append_left _ h)
  have n856g : (856 : Wire) ∉ f.garb := fun h => hg.n856 (List.mem_append_right _ h)
  have b0_1 : s₁.basis 855 = st.basis 855 := frame1 _ n855t n855g
  have b0_2 : t₁.basis 855 = st.basis 855 := by rw [ht₁, fr1 855 n855t (fun h => n855g (by simp [garb, h])), b0_1]
  have b1_3 : t₂.basis 856 = st.basis 856 := by
    rw [ht₂, fr2 856 (fun h => n856g (by simp [garb, h])) (fun h => n856g (by simp [garb, h])),
      ht₁, fr1 856 n856t (fun h => n856g (by simp [garb, h])), frame1 856 n856t n856g]
  obtain ⟨T1, G1⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 855 (4 * h) (4 * h + 1) (st.basis f.guard) s₁ List.nil
    c1 nd1 lt hg.len1 H0 H1
  rw [b0_1] at T1 G1
  have H2' := WideBank8.Fast16.FastSite.holds_frame read f.ports f.g2 _ _ _ _ H2 (fun w hw => fr1 w (d2 w hw) (d21 w hw))
  have H3' := WideBank8.Fast16.FastSite.holds_frame read f.ports f.g3 _ _ _ _ H3 (fun w hw => fr1 w (d3 w hw) (d31 w hw))
  obtain ⟨G2, G3⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 855 (4 * h + 2) (4 * h + 3) (st.basis f.guard) t₁ List.nil
    c2 nd2 hg.len2 hg.len3 H2' H3'
  rw [b0_2] at G2 G3
  have T2 := WideBank8.Fast16.FastSite.holds_frame read f.ports _ _ _ _ _ T1 (fun w hw => fr2 w (fun hm => d2 _ hm hw) (fun hm => d3 _ hm hw))
  have G1' := WideBank8.Fast16.FastSite.holds_frame read f.ports f.g1 _ _ _ _ G1 (fun w hw => fr2 w (fun hm => d21 _ hm hw) (fun hm => d31 _ hm hw))
  obtain ⟨T3, G2'⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 856 _ _ (st.basis f.guard) t₂ List.nil
    c3 nd3 lt hg.len2 T2 G2
  rw [b1_3] at T3 G2'
  have G1'' := WideBank8.Fast16.FastSite.holds_frame read f.ports f.g1 _ _ _ _ G1' (fun w hw => fr3 w (d1 w hw) (fun hm => d21 _ hm hw))
  have G3'' := WideBank8.Fast16.FastSite.holds_frame read f.ports f.g3 _ _ _ _ G3 (fun w hw => fr3 w (d3 w hw) (d32 w hw))
  have haddr : a = (st.basis 855).toNat + 2 * (st.basis 856).toNat + 4 * h := by
    have htv := hs.2.1
    rw [hg.bitsEq] at htv
    simp only [tableAddressValue, wireValues, List.map_cons, boolWordToNat] at htv
    omega
  have hr0 : (if st.basis 856 then (if st.basis 855 then 4 * h + 3 else 4 * h + 2)
      else (if st.basis 855 then 4 * h + 1 else 4 * h)) = a := by
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1] at haddr ⊢ <;> omega
  have hr1 : (if st.basis 855 then 4 * h else 4 * h + 1) = rowOf1 a := by
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf1] at haddr ⊢ <;> omega
  have hr2 : (if st.basis 856 then (if st.basis 855 then 4 * h + 1 else 4 * h)
      else (if st.basis 855 then 4 * h + 3 else 4 * h + 2)) = rowOf2 a := by
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf2] at haddr ⊢ <;> omega
  have hr3 : (if st.basis 855 then 4 * h + 2 else 4 * h + 3) = rowOf3 a := by
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf3] at haddr ⊢ <;> omega
  rw [hr0] at T3; rw [hr1] at G1''; rw [hr2] at G2'; rw [hr3] at G3''
  refine ⟨by rw [hs₂, p3, ht₂, p2, ht₁, p1, r1], frame, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    simp only [garbPorts, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp
      rw [hs₂]; exact G1'' i hi hgi
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp
      rw [hs₂]; exact G2' i hi hgi
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp
      rw [hs₂]; exact G3'' i hi hgi
  · funext w
    by_cases hwg : w ∈ f.garb
    · rw [clearRegister_clean f.garb s₂.basis w hwg]
      have hnt : w ∉ portTargets f.ports := hd w hwg
      rw [tableXorState_outside (portMask read f.ports a) _ _ w (fun hm => hnt (tableBitsMask_subset _ _ hm))]
      exact (hc w (List.mem_append_right _ hwg)).symm
    · rw [MeasuredClear.clearRegister_frame f.garb s₂.basis w hwg]
      by_cases hwt : w ∈ portTargets f.ports
      · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hwt
        have hi' : i < f.ports.length := by simpa [portTargets] using hi
        have hT := T3 i hi' hi
        rw [he] at hT
        have hp : f.ports[i]'hi' ∈ f.ports := List.getElem_mem hi'
        have htg : (f.ports[i]'hi').target = w := by simpa [portTargets, List.getElem_map] using he
        have hsel' := port_selected read f.ports a hnd_app.1 (f.ports[i]'hi') hp
        rw [htg] at hsel'
        have hcw := hc w (List.mem_append_left _ hwt)
        simp only [tableXorState, hsel', hcw, Bool.false_xor]
        rw [hs₂]; exact hT
      · rw [frame w hwt hwg]
        exact (tableXorState_outside _ _ _ _ (fun hm => hwt (tableBitsMask_subset _ _ hm))).symm

theorem load_sim (read : ConstantBit n → Bool) (hg : f.Geo) :
    ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∀ a (st : ECDSAAdd.State),
        SimulationValid f.bits f.paths windowRoot a st →
        Clean (portTargets f.ports ++ f.garb) st.basis →
        b.kraus (Bridge.signedKet st) = c • Bridge.signedKet
          (ECDSAAdd.run f.swapNet List.nil
            (ECDSAAdd.run ((specialize f.selCode (tableAddressValue f.selBits st.basis)).instantiate read) List.nil st)))
      (f.loadSource read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hp1 : ∀ i ∈ f.selCode, PlacedPair f.selBits f.selPaths windowRoot i := by
    intro i hi
    simp only [selCode, List.mem_singleton] at hi; subst hi
    exact placed_implies_pair _ _ _ _ (sel_placed f hg)
  obtain ⟨c1, a1, m1⟩ := pair_source_simulation read f.selBits f.selPaths windowRoot hg.selLen.ge f.selCode hp1
  obtain ⟨c2, a2, m2⟩ := literal_simulation f.swapNet
  have h1 : ∀ a (st : ECDSAAdd.State), SimulationValid f.bits f.paths windowRoot a st →
      SimulationValid f.selBits f.selPaths windowRoot (tableAddressValue f.selBits st.basis) st :=
    fun a st hs => ⟨fun w hw => hs.1 w (hg.pathsSub w hw), rfl, hs.2.2⟩
  refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
  rw [loadSource, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a1 a2
  intro b₁ k₁ b₂ k₂ hb₁ hb₂ a st hs _
  obtain ⟨m, hm, hb₁⟩ := hb₁
  have hm0 : m = List.nil := List.eq_nil_of_length_eq_zero (by simpa [selCode, literalRecords] using hm)
  have hh0 : b₂.history = List.nil := List.eq_nil_of_length_eq_zero (by
    rw [hb₂.1]; simp [swapNet, ECDSAAdd.measurementCount_append, WideBank8.Fast16.swapLayer_meas])
  change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
  rw [hb₁ _ st (h1 a st hs), map_smul, hb₂.2, hm0, hh0]
  simp [smul_smul]

end SS2

/-- A bank-generic 1-bit SelectSwap load + swap gadget (2 registers: targets + `g1`). -/
structure SS1 (n : Nat) where
  bits : List Wire
  paths : List Wire
  selBits : List Wire
  selPaths : List Wire
  guard : Wire
  ports : List (LookupPort n)
  g1 : List Wire

namespace SS1
variable {n : Nat} (f : SS1 n)

def rowOf1 (a : Nat) : Nat := 2 * (a / 2) + (1 - a % 2)

def selPorts : List (LookupPort n) :=
  f.ports.map (fun p => ⟨fun h => p.ref (2 * h), p.value, p.target⟩) ++
  WideBank8.Fast16.regPorts (fun h => 2 * h + 1) f.ports f.g1

def garbPorts : List (LookupPort n) :=
  WideBank8.Fast16.regPorts rowOf1 f.ports f.g1

def swapNet : ECDSAAdd.Program :=
  WideBank8.Fast16.swapLayer 855 (portTargets f.ports) f.g1

def selCode : WCode n := [.lookup (some f.guard) f.selPorts]

def loadProg (start : Nat) : Straight n start (start + codeRecords f.selBits f.selPaths windowRoot f.selCode) :=
  castFinish (by omega)
    ((compile f.selBits f.selPaths windowRoot f.selCode start).append
      (literalFixed f.swapNet 0 ((literal_meas (n := n) _).trans (by
        simp [swapNet, WideBank8.Fast16.swapLayer_meas]))
        (start + codeRecords f.selBits f.selPaths windowRoot f.selCode)))

def loadSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  (source read f.selBits f.selPaths windowRoot f.selCode).seq (literalSource f.swapNet)

structure Geo : Prop where
  bitsEq : f.bits = 855 :: f.selBits
  pathsSub : ∀ w ∈ f.selPaths, w ∈ f.paths
  selLen : f.selPaths.length = f.selBits.length
  selNodup : (f.guard :: f.selBits ++ f.selPaths).Nodup
  selDisj : List.Disjoint (windowRoot :: f.guard :: f.selBits ++ f.selPaths) (portTargets f.ports ++ f.g1)
  len1 : f.g1.length = f.ports.length
  nodup : (portTargets f.ports ++ f.g1).Nodup
  n855 : (855 : Wire) ∉ portTargets f.ports ++ f.g1

theorem selPorts_targets (hg : f.Geo) : portTargets f.selPorts = portTargets f.ports ++ f.g1 := by
  have h1 := WideBank8.Fast16.regPorts_targets (fun h => 2 * h + 1) f.ports f.g1 hg.len1
  simp only [selPorts, WideBank8.Fast16.FastSite.portTargets_append, h1]
  congr 1; simp [portTargets, List.map_map, Function.comp_def]

theorem garbPorts_targets (hg : f.Geo) : portTargets f.garbPorts = f.g1 :=
  WideBank8.Fast16.regPorts_targets _ _ _ hg.len1

theorem garbPorts_length (hg : f.Geo) : f.garbPorts.length = f.ports.length := by
  have h := congrArg List.length (garbPorts_targets f hg)
  simp only [portTargets, List.length_map, hg.len1] at h; exact h

theorem selPorts_length (hg : f.Geo) : f.selPorts.length = 2 * f.ports.length := by
  have h := congrArg List.length (selPorts_targets f hg)
  simp only [portTargets, List.length_map, List.length_append, hg.len1] at h; omega

theorem sel_placed (hg : f.Geo) : Placed f.selBits f.selPaths windowRoot (.lookup (some f.guard) f.selPorts) := by
  refine ⟨by simpa [lookupRoot] using hg.selNodup, by rw [selPorts_targets f hg]; exact hg.nodup,
    by rw [selPorts_targets f hg]; simpa [lookupRoot] using hg.selDisj⟩

theorem sel_layouts (hg : f.Geo) : LookupLayouts f.selBits f.selPaths windowRoot f.selCode := by
  refine ⟨hg.selLen.ge, fun c ps hm => ?_⟩
  simp only [selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  simpa [lookupRoot] using hg.selNodup

theorem swapNet_toff (hg : f.Geo) : ECDSAAdd.toffoliCount f.swapNet = f.ports.length := by
  have ht : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  simp only [swapNet, WideBank8.Fast16.swapLayer_toff, ht, hg.len1, Nat.min_self]

theorem swapNet_slots (hg : f.Geo) : ECDSAAdd.Challenge.gateSlots f.swapNet = 3 * f.ports.length := by
  have ht : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  simp only [swapNet, WideBank8.Fast16.swapLayer_slots, ht, hg.len1, Nat.min_self]

theorem swapNet_valid (hg : f.Geo) : ∀ i ∈ f.swapNet, ECDSAAdd.Challenge.instructionValid i :=
  WideBank8.Fast16.swapLayer_valid 855 _ _ hg.n855 hg.nodup

theorem loadProg_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.loadProg start).instantiate read history).run = (f.loadSource read).run := by
  rw [loadProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h),
    AdaptiveCircuit.run_seq, compile_run]
  simp only [loadSource, AdaptiveCircuit.run_seq]

theorem loadProg_tCount (read : ConstantBit n → Bool) (hg : f.Geo) (start : Nat) (history : Fin start → Bool) :
    ((f.loadProg start).instantiate read history).tCount =
      7 * (2 ^ f.selBits.length - 1 + f.ports.length) := by
  rw [loadProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read f.selBits f.selPaths windowRoot f.selCode (sel_layouts f hg),
    swapNet_toff f hg]
  simp only [selCode, literalToffolis, traversals, Nat.zero_add, Nat.one_mul]
  ring

theorem loadProg_records (hg : f.Geo) :
    codeRecords f.selBits f.selPaths windowRoot f.selCode = 2 ^ f.selBits.length - 1 := by
  rw [codeRecords_eq _ _ _ _ (sel_layouts f hg)]
  simp [selCode, literalRecords, traversals]

theorem loadProg_slots (hg : f.Geo) (start : Nat) :
    (f.loadProg start).gateSlots ≤ 2 ^ f.selBits.length * (2 * f.ports.length) + 10 * (2 ^ f.selBits.length - 1) +
      12 * f.ports.length := by
  rw [loadProg, castFinish_gateSlots, Straight.gateSlots_append,
    compile_slots _ _ _ _ (sel_layouts f hg), literalFixed_slots]
  have h1 : codeSlots f.selBits f.selCode = 2 ^ f.selBits.length * f.selPorts.length + 10 * (2 ^ f.selBits.length - 1) := by
    simp [selCode, codeSlots]
  have h2 := literal_slot_bound (n := n) f.swapNet
  rw [swapNet_slots f hg] at h2
  rw [h1, selPorts_length f hg]
  omega

theorem loadProg_wellFormed (hg : f.Geo) (start : Nat) : (f.loadProg start).WellFormed := by
  rw [loadProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ ?_ (literalFixed_wellFormed _ _ _ (swapNet_valid f hg) _)
  exact pair_compile_wellFormed _ _ _ _ hg.selLen.ge
    (fun i hi => by
      simp only [selCode, List.mem_singleton] at hi; subst hi
      exact placed_implies_pair _ _ _ _ (sel_placed f hg))
    (fun p hp => by simp [selCode] at hp) start

theorem loadProg_residue (start : Nat) : AndGadget.residue (f.loadProg start) = 0 := by
  rw [loadProg, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
    literalFixed, WEXCredit.residue_naive_cast, WEXCredit.literal_residue]

theorem loadProg_support (hg : f.Geo) (S : List Wire)
    (hroot : windowRoot ∈ S) (hguard : f.guard ∈ S) (h855 : (855 : Wire) ∈ S)
    (hbits : f.selBits ⊆ S) (hpaths : f.selPaths ⊆ S) (hreg : portTargets f.ports ++ f.g1 ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (f.loadProg start) ⊆ S := by
  rw [loadProg, support_cast, straightWires_append]
  refine List.append_subset.mpr ⟨?_, ?_⟩
  · refine compile_support f.selBits f.selPaths windowRoot f.selCode S hroot hbits hpaths
      (fun p hp => by simp [selCode] at hp) ?_ start
    intro c ps hm
    simp only [selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨fun q hq => by rw [Option.mem_def, Option.some_inj] at hq; exact hq ▸ hguard,
      by rw [selPorts_targets f hg]; exact hreg⟩
  · refine literalFixed_support _ _ _ S ?_ _
    intro w hw
    have h := WideBank8.Fast16.swapLayer_wires 855 _ _ hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons, List.mem_append] at h ⊢
    rcases h with rfl | h | h
    · exact h855
    · exact hreg (List.mem_append_left _ h)
    · exact hreg (List.mem_append_right _ h)

theorem load_state (read : ConstantBit n → Bool) (hg : f.Geo) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid f.bits f.paths windowRoot a st)
    (hc : Clean (portTargets f.ports ++ f.g1) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue f.selBits st.basis)).instantiate read) List.nil st)
    s₂.phase = st.phase ∧
    (∀ w, w ∉ portTargets f.ports → w ∉ f.g1 → s₂.basis w = st.basis w) ∧
    (∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.guard && decide (read (q.ref a) = q.value))) ∧
    clearRegister f.g1 s₂.basis = tableXorState (portMask read f.ports a) (st.basis f.guard) st.basis := by
  intro s₂
  have hsel := selPorts_targets f hg
  have hselnd : (portTargets f.selPorts).Nodup := by rw [hsel]; exact hg.nodup
  have hguard : f.guard ∉ portTargets f.selPorts := by
    rw [hsel]; exact List.disjoint_left.mp hg.selDisj (by simp)
  have lt : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  have hnd_app := List.nodup_append.mp hg.nodup
  have hd : ∀ w ∈ f.g1, w ∉ portTargets f.ports := fun w hw hm => hnd_app.2.2 w hm w hw rfl
  set h := tableAddressValue f.selBits st.basis with hh
  have e1 : specialize f.selCode h = portTemplate (some f.guard) f.selPorts h := by
    simp [selCode, specialize, WInstr.specialize]
  set s₁ := ECDSAAdd.run ((specialize f.selCode h).instantiate read) List.nil st with hs₁
  have r1 : s₁ = ⟨st.phase, tableXorState (portMask read f.selPorts h) (st.basis f.guard) st.basis⟩ := by
    rw [hs₁, e1]
    exact portTemplate_run read (some f.guard) f.selPorts h windowRoot List.nil st hselnd hguard hs.2.2
  have sel_at : ∀ q ∈ f.selPorts, s₁.basis q.target =
      (st.basis f.guard && decide (read (q.ref h) = q.value)) := by
    intro q hq
    rw [r1]; show tableXorState _ _ _ q.target = _
    simp only [tableXorState, port_selected read f.selPorts h hselnd q hq]
    have hm : q.target ∈ portTargets f.selPorts := List.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hsel] at hm
    simp [hc _ hm]
  have frame1 : ∀ w, w ∉ portTargets f.ports → w ∉ f.g1 → s₁.basis w = st.basis w := by
    intro w h1 h2
    rw [r1]; show tableXorState _ _ _ w = _
    apply tableXorState_outside
    intro hm
    have hm' := tableBitsMask_subset _ _ hm
    rw [hsel] at hm'
    rcases List.mem_append.mp hm' with h | h
    · exact h1 h
    · exact h2 h
  have H0 : WideBank8.Fast16.FastSite.Holds read f.ports (portTargets f.ports) (2 * h) (st.basis f.guard) s₁.basis := by
    intro i hi hgi
    have hq : (⟨fun h => (f.ports[i]'hi).ref (2 * h), (f.ports[i]'hi).value, (f.ports[i]'hi).target⟩ : LookupPort n) ∈
        f.selPorts := by
      simp only [selPorts, List.mem_append]; left
      exact List.mem_map.mpr ⟨f.ports[i]'hi, List.getElem_mem hi, rfl⟩
    simpa [portTargets, List.getElem_map] using sel_at _ hq
  have H1 : WideBank8.Fast16.FastSite.Holds read f.ports f.g1 (2 * h + 1) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  obtain ⟨p1, fr1, -⟩ := WideBank8.Fast16.swapLayer_run 855 _ _ hg.n855 hg.nodup (by rw [lt, hg.len1]) s₁ List.nil
  have frame : ∀ w, w ∉ portTargets f.ports → w ∉ f.g1 → s₂.basis w = st.basis w := fun w h1 h2 => by
    change (ECDSAAdd.run (WideBank8.Fast16.swapLayer 855 _ _) List.nil s₁).basis w = _
    rw [fr1 w h1 h2, frame1 w h1 h2]
  have b0_1 : s₁.basis 855 = st.basis 855 :=
    frame1 _ (fun h => hg.n855 (List.mem_append_left _ h)) (fun h => hg.n855 (List.mem_append_right _ h))
  obtain ⟨T1, G1⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 855 (2 * h) (2 * h + 1) (st.basis f.guard) s₁ List.nil
    hg.n855 hg.nodup lt hg.len1 H0 H1
  rw [b0_1] at T1 G1
  have haddr : a = (st.basis 855).toNat + 2 * h := by
    have htv := hs.2.1
    rw [hg.bitsEq] at htv
    simp only [tableAddressValue, wireValues, List.map_cons, boolWordToNat] at htv
    omega
  have hr0 : (if st.basis 855 then 2 * h + 1 else 2 * h) = a := by
    cases hb0 : st.basis 855 <;> simp [hb0] at haddr ⊢ <;> omega
  have hr1 : (if st.basis 855 then 2 * h else 2 * h + 1) = rowOf1 a := by
    cases hb0 : st.basis 855 <;> simp [hb0, rowOf1] at haddr ⊢ <;> omega
  rw [hr0] at T1; rw [hr1] at G1
  refine ⟨by change (ECDSAAdd.run (WideBank8.Fast16.swapLayer 855 _ _) List.nil s₁).phase = _; rw [p1, r1], frame, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp
    exact G1 i hi hgi
  · funext w
    by_cases hwg : w ∈ f.g1
    · rw [clearRegister_clean f.g1 s₂.basis w hwg]
      have hnt : w ∉ portTargets f.ports := hd w hwg
      rw [tableXorState_outside (portMask read f.ports a) _ _ w (fun hm => hnt (tableBitsMask_subset _ _ hm))]
      exact (hc w (List.mem_append_right _ hwg)).symm
    · rw [MeasuredClear.clearRegister_frame f.g1 s₂.basis w hwg]
      by_cases hwt : w ∈ portTargets f.ports
      · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hwt
        have hi' : i < f.ports.length := by simpa [portTargets] using hi
        have hT := T1 i hi' hi
        rw [he] at hT
        have hp : f.ports[i]'hi' ∈ f.ports := List.getElem_mem hi'
        have htg : (f.ports[i]'hi').target = w := by simpa [portTargets, List.getElem_map] using he
        have hsel' := port_selected read f.ports a hnd_app.1 (f.ports[i]'hi') hp
        rw [htg] at hsel'
        have hcw := hc w (List.mem_append_left _ hwt)
        simp only [tableXorState, hsel', hcw, Bool.false_xor]
        exact hT
      · rw [frame w hwt hwg]
        exact (tableXorState_outside _ _ _ _ (fun hm => hwt (tableBitsMask_subset _ _ hm))).symm

theorem load_sim (read : ConstantBit n → Bool) (hg : f.Geo) :
    ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∀ a (st : ECDSAAdd.State),
        SimulationValid f.bits f.paths windowRoot a st →
        Clean (portTargets f.ports ++ f.g1) st.basis →
        b.kraus (Bridge.signedKet st) = c • Bridge.signedKet
          (ECDSAAdd.run f.swapNet List.nil
            (ECDSAAdd.run ((specialize f.selCode (tableAddressValue f.selBits st.basis)).instantiate read) List.nil st)))
      (f.loadSource read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hp1 : ∀ i ∈ f.selCode, PlacedPair f.selBits f.selPaths windowRoot i := by
    intro i hi
    simp only [selCode, List.mem_singleton] at hi; subst hi
    exact placed_implies_pair _ _ _ _ (sel_placed f hg)
  obtain ⟨c1, a1, m1⟩ := pair_source_simulation read f.selBits f.selPaths windowRoot hg.selLen.ge f.selCode hp1
  obtain ⟨c2, a2, m2⟩ := literal_simulation f.swapNet
  have h1 : ∀ a (st : ECDSAAdd.State), SimulationValid f.bits f.paths windowRoot a st →
      SimulationValid f.selBits f.selPaths windowRoot (tableAddressValue f.selBits st.basis) st :=
    fun a st hs => ⟨fun w hw => hs.1 w (hg.pathsSub w hw), rfl, hs.2.2⟩
  refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
  rw [loadSource, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a1 a2
  intro b₁ k₁ b₂ k₂ hb₁ hb₂ a st hs _
  obtain ⟨m, hm, hb₁⟩ := hb₁
  have hm0 : m = List.nil := List.eq_nil_of_length_eq_zero (by simpa [selCode, literalRecords] using hm)
  have hh0 : b₂.history = List.nil := List.eq_nil_of_length_eq_zero (by
    rw [hb₂.1]; simp [swapNet, WideBank8.Fast16.swapLayer_meas])
  change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
  rw [hb₁ _ st (h1 a st hs), map_smul, hb₂.2, hm0, hh0]
  simp [smul_smul]

end SS1

end
end ShorECDLP.Entrant.Site1Fast
end

/-! ### Consolidated from `Site1Wire.lean` -/
section
/-! Wiring the two-pass SelectSwap replacement for `site1` into both the narrow (15-bit) and
wide (16-bit) window rows.

Replaces only block #2 (`site1`) of `WEXFast.W15G.rowH` and `WideBank8.Row16.code`:
- Wide (`Wide16`): records `1,743,514 → 1,728,416`, credit `≤ 2,342,691 → ≤ 2,327,593` (`-15,098`).
Total savings across 19 wide + 8 narrow windows: `342,110` Toffolis = `1,368,440` T-model gates. -/

namespace ShorECDLP.Entrant.Site1Wire
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare Site1Fast
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

attribute [local irreducible] ECDSAAdd.run scrInP1 scrInP2 pair1Prog
  scrPairWires scrShortWires scrDExtraWires WEXUnlookup.rowC WEXUnlookup.rowHead
  WEXFast.W15G.rowH WideBank8.Row16.code WEXFast.rowCF
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8
  MeasuredClear.fixupProgram MeasuredClear.fixupProgram8
  ECDSAAdd.Baselines.normalizeProgram
  WEXFast.hprog WEXFast.hblockProg WideBank8.Fast16.fprog WideBank8.Fast16.fblockProg

/-! ### Shared garbage wire lists and clean-pool invariants -/

def gA1 : List Wire := List.range' 14115 258
def gA2 : List Wire := List.range' 14373 257 ++ [14883]
def gA3 : List Wire := List.range' 15399 256 ++ List.range' 15142 2
def garbA : List Wire := gA1 ++ gA2 ++ gA3
def gB : List Wire := List.range' 14115 258 ++ List.range' 14884 255

theorem gA1_len : gA1.length = 258 := by simp [gA1]
theorem gA2_len : gA2.length = 258 := by simp [gA2]
theorem gA3_len : gA3.length = 258 := by simp [gA3]
theorem garbA_len : garbA.length = 774 := by simp [garbA, gA1_len, gA2_len, gA3_len]
theorem gB_len : gB.length = 513 := by simp [gB]

theorem mem_gA1 {w : Wire} : w ∈ gA1 ↔ 14115 ≤ w ∧ w < 14373 := by simp [gA1, List.mem_range'_1]
theorem mem_gA2 {w : Wire} : w ∈ gA2 ↔ (14373 ≤ w ∧ w < 14630) ∨ w = 14883 := by
  simp [gA2, List.mem_range'_1]
theorem mem_gA3 {w : Wire} : w ∈ gA3 ↔ (15399 ≤ w ∧ w < 15655) ∨ (15142 ≤ w ∧ w < 15144) := by
  simp [gA3, List.mem_range'_1]
theorem mem_gB {w : Wire} : w ∈ gB ↔ (14115 ≤ w ∧ w < 14373) ∨ (14884 ≤ w ∧ w < 15139) := by
  simp [gB, List.mem_range'_1]

theorem mem_garbA {w : Wire} (h : w ∈ garbA) :
    (14115 ≤ w ∧ w < 14630) ∨ w = 14883 ∨ (15142 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
  simp only [garbA, List.mem_append, mem_gA1, mem_gA2, mem_gA3] at h
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem mem_short_garbA {w : Wire} (h : w ∈ shortWires ++ garbA) :
    (14115 ≤ w ∧ w < 14630) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
  rcases List.mem_append.mp h with h | h
  · have := shortWires_bounds w h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · have := mem_garbA h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem mem_pairExtra {w : Wire} (h : w ∈ pairExtraWires) :
    (14373 ≤ w ∧ w < 14630) ∨ w = 14883 ∨ (15399 ≤ w ∧ w < 15654) := by
  rcases List.mem_append.mp h with h | h
  · have := pairWires_bounds w h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rw [scrDExtraWires_explicit, List.mem_range'_1] at h
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem mem_pairExtra_gB {w : Wire} (h : w ∈ pairExtraWires ++ gB) :
    (14115 ≤ w ∧ w < 14630) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
  rcases List.mem_append.mp h with h | h
  · have := mem_pairExtra h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rw [mem_gB] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem pool_band_in_newH7 {w : Wire}
    (h : (14115 ≤ w ∧ w < 14630) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655)) :
    w ∈ PoolHost.newSourceH7 := by
  rw [PoolHost.newSourceH7_mem]
  refine ⟨Or.inr ?_, ?_⟩
  · unfold oldWork; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · unfold PoolHost.retiredH7 retiredH retired; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem pool_band_in_dialogPool {w : Wire}
    (h : (14115 ≤ w ∧ w < 14630) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655)) :
    w ∈ streamLayout.dialogPool := by
  have h1 : w ∈ streamLayout.dialogPool.take 2613 := by
    rw [mem_pool_take 2613 (le_refl _)]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  exact List.mem_of_mem_take h1

theorem short_garbA_nodup : (shortWires ++ garbA).Nodup := by
  have nd1 : gA1.Nodup := List.nodup_range'
  have nd2 : gA2.Nodup := by
    rw [gA2, List.nodup_append]
    refine ⟨List.nodup_range', List.nodup_singleton _, fun a ha b hb hab => ?_⟩
    subst hab; simp only [List.mem_range'_1, List.mem_singleton] at ha hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have nd3 : gA3.Nodup := by
    rw [gA3, List.nodup_append]
    refine ⟨List.nodup_range', List.nodup_range', fun a ha b hb hab => ?_⟩
    subst hab; simp only [List.mem_range'_1] at ha hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have nd12 : (gA1 ++ gA2).Nodup := by
    rw [List.nodup_append]
    refine ⟨nd1, nd2, fun a ha b hb hab => ?_⟩
    subst hab; rw [mem_gA1] at ha; rw [mem_gA2] at hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have ndg : garbA.Nodup := by
    rw [garbA, List.nodup_append]
    refine ⟨nd12, nd3, fun a ha b hb hab => ?_⟩
    subst hab; rw [List.mem_append, mem_gA1, mem_gA2] at ha; rw [mem_gA3] at hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  rw [List.nodup_append]
  refine ⟨scrShortWires_nd, ndg, fun a ha b hb hab => ?_⟩
  subst hab; have h1 := shortWires_bounds a ha; have h2 := mem_garbA hb
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem garbA_nodup : garbA.Nodup := (List.nodup_append.mp short_garbA_nodup).2.1

theorem pairExtra_nodup : pairExtraWires.Nodup := by
  rw [pairExtraWires, List.nodup_append]
  refine ⟨scrPairWires_nd, ?_, fun a ha b hb hab => ?_⟩
  · rw [scrDExtraWires_explicit]; exact List.nodup_range'
  · subst hab; exact extra_not_scrWires a hb (List.mem_append_left _ ha)

theorem gB_nodup : gB.Nodup := by
  rw [gB, List.nodup_append]
  refine ⟨List.nodup_range', List.nodup_range', fun a ha b hb hab => ?_⟩
  subst hab; simp only [List.mem_range'_1] at ha hb; omega

theorem pairExtra_gB_nodup : (pairExtraWires ++ gB).Nodup := by
  rw [List.nodup_append]
  refine ⟨pairExtra_nodup, gB_nodup, fun a ha b hb hab => ?_⟩
  subst hab; have h1 := mem_pairExtra ha; rw [mem_gB] at hb
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem gB_sub_short_garbA : gB ⊆ shortWires ++ garbA := by
  intro w hw
  rw [mem_gB] at hw
  rcases hw with hw | hw
  · exact List.mem_append_right _ (by simp only [garbA, List.mem_append]; left; left; exact mem_gA1.mpr hw)
  · apply List.mem_append_left
    rw [shortWires, scrShortWires_explicit]
    simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.mem_singleton]
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem pairExtra_sub_garbA : pairExtraWires ⊆ garbA := by
  intro w hw
  have h := mem_pairExtra hw
  simp only [garbA, List.mem_append, mem_gA1, mem_gA2, mem_gA3]
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem dialogPool_sub_work : streamLayout.dialogPool ⊆ streamLayout.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 streamLayout.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool] at h1
  simp only [work, outWork, temporary, inPlaceFlags, selectors, PointAddLayout.work, PointAddLayout.words,
    PointAddLayout.flags, List.flatten_cons, List.flatten_nil, List.append_nil, List.count_append,
    List.count_cons, List.count_nil] at h1 ht ⊢
  omega

theorem scrHead_wires_not_pool (w : Wire) (hw : w ∈ ECDSAAdd.wires scrHeadProgram) :
    w < 14115 ∨ w = 19816 := by
  have hs : scrHeadProgram = [.CX streamLayout.control streamLayout.core.double] ++
      [.CX streamLayout.control streamLayout.core.equalX] ++
      zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect := rfl
  have hd : streamLayout.core.double = 14114 := rfl
  have hi : streamLayout.infinitySelect = 19816 := rfl
  rw [hs, zeroFlag] at hw
  simp only [ECDSAAdd.wires_append, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false,
    sl_control, sl_equalX, hd, hi, streamLayout_point] at hw
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem liveReady_pool_after_b01 {n : Nat} (read : ConstantBit n → Bool) (r : Nat → Fin n)
    (a : Nat) (s : BasisState) (hs : liveReady s) (m0 m1 : List Bool) :
    let st0 : ECDSAAdd.State := ⟨false, s⟩
    let st1 := ECDSAAdd.run (reference2 read a ([Block2.plain (WideSigned.Rows.code r (wLiteral ([.X 838])))])) m0 st0
    let st2 := ECDSAAdd.run (reference2 read a ([Block2.plain (WideSigned.Rows.code r scrHead)])) m1 st1
    Clean streamLayout.dialogPool st2.basis := by
  intro st0 st1 st2 w hw
  have hwb : 14115 ≤ w ∧ w < 16728 := by
    have h1 : w ∈ streamLayout.dialogPool.take 2613 := by
      have ht : streamLayout.dialogPool.take 2613 = streamLayout.dialogPool := by
        simp only [dialogPool, List.take_take, Nat.min_self]
      rwa [ht]
    exact (mem_pool_take 2613 (le_refl _)).mp h1
  have hr0 : reference2 read a ([Block2.plain (WideSigned.Rows.code r (wLiteral ([.X 838])))]) = [.X 838] := by
    simp [reference2, erase2, Block2.code, WideSigned.Rows.code, WideSigned.Rows.instr, wLiteral,
      specialize, WInstr.specialize, Tmpl.instantiate_lit]
  have hr1 : reference2 read a ([Block2.plain (WideSigned.Rows.code r scrHead)]) = scrHeadProgram := by
    simp [reference2, erase2, Block2.code, WideSigned.Rows.code, WideSigned.Rows.instr, scrHead,
      scrHeadProgram, wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_append, Tmpl.instantiate_lit]
  have hns1 : w ∉ ECDSAAdd.wires scrHeadProgram := fun hm => by
    have := scrHead_wires_not_pool w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hns0 : w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program) := fun hm => by
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_singleton] at hm
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  dsimp only [st2, st1]
  rw [hr1, run_outside_basis scrHeadProgram m1 _ w hns1, hr0, run_outside_basis [.X 838] m0 st0 w hns0]
  exact hs.2.1 w (List.mem_append_left _ (dialogPool_sub_work hw))

/-! ### Normalized `shortPart` and `tailPart` metrics -/

def shortNorm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram shortPart
def tailNorm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram tailPart
def mShort : Nat := ECDSAAdd.measurementCount shortPart
def mTail : Nat := ECDSAAdd.measurementCount tailPart

theorem shortNorm_meas : ECDSAAdd.measurementCount shortNorm = mShort :=
  ECDSAAdd.Baselines.normalize_measurements shortPart

theorem tailNorm_meas : ECDSAAdd.measurementCount tailNorm = mTail :=
  ECDSAAdd.Baselines.normalize_measurements tailPart

theorem mShort_add_mTail : mShort + mTail = ECDSAAdd.measurementCount site1Arith := by
  rw [mShort, mTail]; exact site1_counts_split.2.1

theorem shortNorm_valid : ∀ i ∈ shortNorm, ECDSAAdd.Challenge.instructionValid i :=
  ECDSAAdd.Baselines.normalize_physical shortPart shortPart_physical

theorem tailNorm_valid : ∀ i ∈ tailNorm, ECDSAAdd.Challenge.instructionValid i :=
  ECDSAAdd.Baselines.normalize_physical tailPart tailPart_physical

theorem norm_toff_split_gen (pA pB pC pD pE : ECDSAAdd.Program) :
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram pB) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (pA ++ (pC ++ (pD ++ pE)))) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (pA ++ (pB ++ (pC ++ (pD ++ pE))))) := by
  have hna (p q : ECDSAAdd.Program) :
      ECDSAAdd.Baselines.normalizeProgram (p ++ q) =
        ECDSAAdd.Baselines.normalizeProgram p ++ ECDSAAdd.Baselines.normalizeProgram q := by
    unfold ECDSAAdd.Baselines.normalizeProgram; simp
  simp only [hna, ECDSAAdd.toffoliCount_append]; omega

theorem norm_toff_split :
    ECDSAAdd.toffoliCount shortNorm + ECDSAAdd.toffoliCount tailNorm =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram site1Arith) := by
  rw [shortNorm, tailNorm, tailPart, site1Arith_eq]
  exact norm_toff_split_gen pairPart shortPart (pointDialogGenericFlag streamLayout)
    (ECDSAAdd.Frontier.zrep streamLayout) pair1Prog

theorem norm_slots_split :
    ECDSAAdd.Challenge.gateSlots shortNorm + ECDSAAdd.Challenge.gateSlots tailNorm =
      ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) := by
  rw [shortNorm, tailNorm, ECDSAAdd.Baselines.normalize_slots, ECDSAAdd.Baselines.normalize_slots,
    ECDSAAdd.Baselines.normalize_slots]
  exact site1_counts_split.2.2

theorem shortPart_wires_newH7 : ECDSAAdd.wires shortNorm ⊆ PoolHost.newSourceH7.toFinset := by
  rw [shortNorm, ECDSAAdd.Baselines.normalize_wires]
  intro w hw
  have hmem : WInstr.literal site1Arith ∈ erase2 WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [h1, h2, List.map_append, erase2_append, erase2_append]
    apply List.mem_append_left; apply List.mem_append_left
    rw [WEXUnlookup.rowPre3]
    simp only [List.map_cons, List.map_nil, erase2_cons, erase2_nil, List.append_nil, toBlock2,
      Block2.code, UnitSite.code, site1, MaskedSite.prefix]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hunit : Block2.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩ ∈ WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [h1, h2, List.map_append]
    apply List.mem_append_left; apply List.mem_append_left
    rw [WEXUnlookup.rowPre3]; simp [toBlock2]
  have hno4 := (PoolHost.rowC_unit_no4 _ hunit).1 site1Arith (by simp [UnitSite.code, site1, MaskedSite.prefix, wLiteral]) w (shortPart_wires_sub hw)
  have hstrict : ¬ (hostWire ∈ ECDSAAdd.wires site1Arith ∨ hostWire2 ∈ ECDSAAdd.wires site1Arith ∨
      hostWire3 ∈ ECDSAAdd.wires site1Arith) := by
    intro hh
    have hm_rowH : WEXFast.HBlock.blk (.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩)) ∈ WEXFast.W15G.rowH := by
      unfold WEXFast.W15G.rowH
      apply List.mem_append_left
      refine List.mem_map.mpr ⟨.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩), ?_, rfl⟩
      rw [WideBank8.Row16.headF]
      apply List.mem_append_left
      rw [WEXUnlookup.rowPre3]; simp [toBlock2]
    have hst := WEXFast.W15G.rowH_strict _ hm_rowH site1Arith
      (by simp [WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, erase2, Block2.code, UnitSite.code, site1, MaskedSite.prefix, wLiteral])
      (by rcases hh with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)))
    obtain ⟨c, hc⟩ := hst; cases hc
  rcases PoolHost.rowC_lit_relaxed7 site1Arith hmem w (shortPart_wires_sub hw) with e | e | e | e | e | e | e | e
  · exact absurd (Or.inl (e ▸ shortPart_wires_sub hw)) hstrict
  · exact absurd (Or.inr (Or.inl (e ▸ shortPart_wires_sub hw))) hstrict
  · exact absurd (Or.inr (Or.inr (e ▸ shortPart_wires_sub hw))) hstrict
  · exact absurd e hno4.1
  · exact absurd e hno4.2.1
  · exact absurd e hno4.2.2.1
  · exact absurd e hno4.2.2.2
  · exact List.mem_toFinset.mpr e

theorem tailPart_wires_newH7 : ECDSAAdd.wires tailNorm ⊆ PoolHost.newSourceH7.toFinset := by
  rw [tailNorm, ECDSAAdd.Baselines.normalize_wires]
  intro w hw
  have hmem : WInstr.literal site1Arith ∈ erase2 WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [h1, h2, List.map_append, erase2_append, erase2_append]
    apply List.mem_append_left; apply List.mem_append_left
    rw [WEXUnlookup.rowPre3]
    simp only [List.map_cons, List.map_nil, erase2_cons, erase2_nil, List.append_nil, toBlock2,
      Block2.code, UnitSite.code, site1, MaskedSite.prefix]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hunit : Block2.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩ ∈ WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [h1, h2, List.map_append]
    apply List.mem_append_left; apply List.mem_append_left
    rw [WEXUnlookup.rowPre3]; simp [toBlock2]
  have hno4 := (PoolHost.rowC_unit_no4 _ hunit).1 site1Arith (by simp [UnitSite.code, site1, MaskedSite.prefix, wLiteral]) w (tailPart_wires_sub hw)
  have hstrict : ¬ (hostWire ∈ ECDSAAdd.wires site1Arith ∨ hostWire2 ∈ ECDSAAdd.wires site1Arith ∨
      hostWire3 ∈ ECDSAAdd.wires site1Arith) := by
    intro hh
    have hm_rowH : WEXFast.HBlock.blk (.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩)) ∈ WEXFast.W15G.rowH := by
      unfold WEXFast.W15G.rowH
      apply List.mem_append_left
      refine List.mem_map.mpr ⟨.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩), ?_, rfl⟩
      rw [WideBank8.Row16.headF]
      apply List.mem_append_left
      rw [WEXUnlookup.rowPre3]; simp [toBlock2]
    have hst := WEXFast.W15G.rowH_strict _ hm_rowH site1Arith
      (by simp [WEXFast.HBlock.forgetL, WEXFast.FBlock2.forget, erase2, Block2.code, UnitSite.code, site1, MaskedSite.prefix, wLiteral])
      (by rcases hh with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)))
    obtain ⟨c, hc⟩ := hst; cases hc
  rcases PoolHost.rowC_lit_relaxed7 site1Arith hmem w (tailPart_wires_sub hw) with e | e | e | e | e | e | e | e
  · exact absurd (Or.inl (e ▸ tailPart_wires_sub hw)) hstrict
  · exact absurd (Or.inr (Or.inl (e ▸ tailPart_wires_sub hw))) hstrict
  · exact absurd (Or.inr (Or.inr (e ▸ tailPart_wires_sub hw))) hstrict
  · exact absurd e hno4.1
  · exact absurd e hno4.2.1
  · exact absurd e hno4.2.2.1
  · exact absurd e hno4.2.2.2
  · exact List.mem_toFinset.mpr e

theorem measureThen_slots_le {n R : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor + R))
    (B : Nat) (hn : ∀ cursor refs, (next cursor refs).gateSlots ≤ B)
    (wires : List Wire) (start : Nat) (refs : List (Fin start)) :
    (MeasuredClear.measureThen next wires start refs).gateSlots ≤ B := by
  induction wires generalizing start with
  | nil => exact hn start refs
  | cons w ws ih =>
    simp only [MeasuredClear.measureThen, castFinish_gateSlots, Straight.gateSlots]
    exact ih _ _

theorem rows_port_probeRows (p : LookupPort 32768)
    (h : ∀ a, (p.ref a).point = probeRows a) : WideSigned.Rows.port probeRows p = p := by
  cases p with | mk ref val tgt =>
  simp only [WideSigned.Rows.port]
  congr 1; funext a
  have ha := h a
  cases hr : ref a with | mk pt fld bt =>
  simp only [hr] at ha; subst ha; rfl

theorem rows_ports_probeRows (ps : List (LookupPort 32768))
    (h : ∀ p ∈ ps, ∀ a, (p.ref a).point = probeRows a) :
    WideSigned.Rows.ports probeRows ps = ps := by
  unfold WideSigned.Rows.ports
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, rows_port_probeRows p (h p List.mem_cons_self),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem indexedPorts_row_eq (ws : List Wire) (refs : Nat → Nat → ConstantBit 32768) (v : Bool)
    (hr : ∀ a i, (refs a i).point = probeRows a) :
    ∀ p ∈ indexedPorts ws refs v, ∀ a, (p.ref a).point = probeRows a := by
  induction ws generalizing refs with
  | nil => intro p hp; cases hp
  | cons w ws ih =>
    intro p hp a
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hr a 0
    · exact ih (fun a i => refs a (i + 1)) (fun a i => hr a (i + 1)) p hp a

theorem retarget_row_eq (ps : List (LookupPort 32768)) (ws : List Wire)
    (h : ∀ p ∈ ps, ∀ a, (p.ref a).point = probeRows a) :
    ∀ p ∈ retarget ps ws, ∀ a, (p.ref a).point = probeRows a := by
  induction ps generalizing ws with
  | nil => intro p hp; cases hp
  | cons p ps ih =>
    cases ws with
    | nil => intro q hq; cases hq
    | cons w ws =>
      intro q hq a
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h p List.mem_cons_self a
      · exact ih ws (fun x hx => h x (List.mem_cons_of_mem _ hx)) q hq a

theorem shortPorts_row_eq : ∀ p ∈ shortPorts probeRows, ∀ a, (p.ref a).point = probeRows a := by
  apply retarget_row_eq
  intro p hp a
  unfold scrInShortBits shortNegPorts at hp
  simp only [List.mem_append, List.mem_cons] at hp
  rcases hp with (rfl | hp) | hp
  · rfl
  · exact indexedPorts_row_eq _ _ _ (fun _ _ => rfl) p hp a
  · exact indexedPorts_row_eq _ _ _ (fun _ _ => rfl) p hp a

theorem pairExtraPorts_row_eq : ∀ p ∈ pairExtraPorts probeRows, ∀ a, (p.ref a).point = probeRows a := by
  intro p hp a
  unfold pairExtraPorts at hp
  rcases List.mem_append.mp hp with hp | hp
  · refine retarget_row_eq _ _ ?_ p hp a
    intro q hq b
    unfold scrPairBits pairParityPorts at hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | hq) | rfl
    · rfl
    · exact indexedPorts_row_eq _ _ _ (fun _ _ => rfl) q hq b
    · rfl
  · exact indexedPorts_row_eq _ _ _ (fun _ _ => rfl) p hp a

theorem shortPorts_probeRows_id :
    WideSigned.Rows.ports probeRows (shortPorts probeRows) = shortPorts probeRows :=
  rows_ports_probeRows _ shortPorts_row_eq

theorem pairExtraPorts_probeRows_id :
    WideSigned.Rows.ports probeRows (pairExtraPorts probeRows) = pairExtraPorts probeRows :=
  rows_ports_probeRows _ pairExtraPorts_row_eq

theorem sitePorts_probeRows_id :
    WideSigned.Rows.ports probeRows (sitePorts probeRows) = sitePorts probeRows := by
  apply rows_ports_probeRows
  intro p hp a
  unfold sitePorts WEX.scrInPorts at hp
  simp only [List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · exact pairExtraPorts_row_eq p (List.mem_append_left _ hp) a
  · exact shortPorts_row_eq p hp a
  · exact pairExtraPorts_row_eq p (List.mem_append_right _ hp) a

theorem site1_probeRows_id :
    WideSigned.Rows.site probeRows (site1 probeRows) = site1 probeRows := by
  simp only [WideSigned.Rows.site, site1, sitePorts_probeRows_id, WideSigned.Rows.code,
    WideSigned.Rows.instr, wLiteral, List.map_cons, List.map_nil]

theorem x838_meas_zero : ECDSAAdd.measurementCount ([.X 838] : ECDSAAdd.Program) = 0 := rfl

theorem scrHeadProgram_meas_zero : ECDSAAdd.measurementCount scrHeadProgram = 0 := by
  simp [scrHeadProgram, zeroFlag, ECDSAAdd.measurementCount]

theorem literalSlotSum_le_of_mem {n : Nat} (c : WCode n) (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ c) : ECDSAAdd.Challenge.gateSlots p ≤ literalSlotSum c := by
  induction c with
  | nil => cases hp
  | cons i c ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.le_add_right _ _
    · exact (ih hp).trans (by cases i <;> simp only [literalSlotSum]; exact Nat.le_add_left _ _; exact le_rfl)

theorem hblockRec_std {n} (b : Block2 n) :
    WEXFast.hblockRec (.blk (.std b)) = PathShare.blockRecP2 PathShare.bank15 b := rfl

theorem hblockTP_unit {n} (u : UnitSite n) :
    WEXFast.hblockTP (.blk (.std (.unit u))) = PathShare.blockTP2 PathShare.bank15 (.unit u) := rfl

theorem hrecs_cons {n} (a : WEXFast.HBlock n) (r : WEXFast.HCode n) :
    WEXFast.hrecs (a :: r) = WEXFast.hblockRec a + WEXFast.hrecs r := rfl

theorem hcodeTP_cons {n} (a : WEXFast.HBlock n) (r : WEXFast.HCode n) :
    WEXFast.hcodeTP (a :: r) = WEXFast.hblockTP a + WEXFast.hcodeTP r := rfl

theorem fblockRec_std {n} (b : Block2 n) :
    WideBank8.Fast16.fblockRec (.std b) = WideBank8.blockRecP2 WideBank8.Fast16.bank15 b := rfl

theorem fblockTP_std {n} (b : Block2 n) :
    WideBank8.Fast16.fblockTP (.std b) =
      WideBank8.blockTP2 WideBank8.Fast16.bank15 b + PoolHost.blockExtra b := rfl

theorem frecs_cons {n} (a : WideBank8.Fast16.FBlock2 n) (r : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.frecs (a :: r) = WideBank8.Fast16.fblockRec a + WideBank8.Fast16.frecs r := rfl

theorem fcodeTP_cons {n} (a : WideBank8.Fast16.FBlock2 n) (r : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.fcodeTP (a :: r) = WideBank8.Fast16.fblockTP a + WideBank8.Fast16.fcodeTP r := rfl

attribute [local irreducible] shortPart tailPart pairPart site1Arith shortNorm tailNorm mShort mTail
  ECDSAAdd.measurementCount ECDSAAdd.toffoliCount ECDSAAdd.Challenge.gateSlots
  WEXFast.hcodeTP WEXFast.hrecs WEXFast.hblockRec WEXFast.hblockTP
  WideBank8.Fast16.fcodeTP WideBank8.Fast16.frecs WideBank8.Fast16.fblockRec WideBank8.Fast16.fblockTP
  Straight.WellFormed MeasuredClear.measureThen
  SS2.selCode SS2.swapNet SS1.selCode SS1.swapNet
  shortPorts pairExtraPorts sitePorts clearData

def site1RecGen (cA cB mS mT fR : Nat) : Nat := cA + 774 + mS + 258 + cB + 513 + mT + 513 + fR

theorem add_assoc_3 (s a b : Nat) : s + a + b = s + (a + b) := Nat.add_assoc s a b

theorem twoPass_fin_gen (s rA cA cB mS mT fR : Nat) (hr : rA = cA) :
    s + rA + (774 + (mS + (258 + (cB + (513 + (mT + (513 + fR))))))) =
      s + site1RecGen cA cB mS mT fR := by
  subst hr; unfold site1RecGen; omega

theorem row_cast_arith (s a b c d e : Nat) (h : a + b + c + d = e) :
    s + a + b + c + d = s + e := by omega

theorem row_rec_arith (a b h2 r s1 diff tot : Nat)
    (ht : a + b + h2 + r = tot) (hd : h2 = s1 + diff) :
    a + b + s1 + r = tot - diff := by omega

theorem rowTP_arith (a b h2 r s1 diff : Nat)
    (hd : h2 = s1 + diff) :
    a + b + s1 + r = (a + b + h2 + r) - diff := by omega

theorem rowTP_sub_arith (tot a b h2 r s1 diff : Nat)
    (ht : tot = a + b + h2 + r) (hd : h2 = s1 + diff) :
    a + b + s1 + r = tot - diff := by omega

theorem tcount_mul7_4 (a b c d t : Nat) (h : a + b + c + d = t) :
    7 * a + 7 * b + (7 * c + 7 * d) = 7 * t := by omega

theorem twoPass_tcount_arith (cA gA tS cB gB tT tF : Nat) :
    7 * (cA + gA) + (7 * tS + (7 * (cB + gB) + (7 * tT + 7 * tF))) =
      7 * (cA + gA + tS + cB + gB + tT + tF) := by ring

theorem mPerm_len_arith (nA nB nP nAll : Nat) (h1 : nP ≤ nB) (h2 : nA + nB = nAll) :
    min nP nB + nA + (nB - nP) = nAll := by omega

theorem narrow_rec_diff_arith (mAll mS mT fR : Nat) (hcs : mS + mT = mAll) (hf : fR = 382) :
    mAll + 32767 + 771 + (255 + 127) = site1RecGen 8191 16383 mS mT fR + 6906 := by
  unfold site1RecGen; omega

theorem wide_rec_diff_arith (mAll mS mT fR : Nat) (hcs : mS + mT = mAll) (hf : fR = 510) :
    mAll + 65535 + 771 + (255 + 255) = site1RecGen 16383 32767 mS mT fR + 15098 := by
  unfold site1RecGen; omega

theorem narrow_tp_diff_arith (tS tT : Nat) :
    tS + tT + 1 * (2 ^ 15 - 1) + (255 + 120) =
      (8191 + 774 + tS + 16383 + 513 + tT + (255 + 120)) + 6906 := by omega

theorem wide_tp_diff_arith (tS tT : Nat) :
    tS + tT + 1 * (2 ^ 16 - 1) + (255 + 247) =
      (16383 + 774 + tS + 32767 + 513 + tT + (255 + 247)) + 15098 := by omega

theorem litToff_lookup_lit {n} (ctl : Option Wire) (ps : List (LookupPort n)) (p : ECDSAAdd.Program) :
    literalToffolis (normalizeW ([WInstr.lookup ctl ps, WInstr.literal p])) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram p) := by
  simp [normalizeW, normalizeWInstr, literalToffolis]

theorem trav_lookup_lit {n} (ctl : Option Wire) (ps : List (LookupPort n)) (p : ECDSAAdd.Program) :
    traversals ([WInstr.lookup ctl ps, WInstr.literal p]) = 1 := by
  simp [traversals]

theorem litRec_lookup_lit {n} (ctl : Option Wire) (ps : List (LookupPort n)) (p : ECDSAAdd.Program) :
    literalRecords ([WInstr.lookup ctl ps, WInstr.literal p]) = ECDSAAdd.measurementCount p := by
  simp [literalRecords]

theorem litRec_lookup_lit_lookup {n} (ctl1 ctl2 : Option Wire)
    (ps1 ps2 : List (LookupPort n)) (p : ECDSAAdd.Program) :
    literalRecords ([WInstr.lookup ctl1 ps1, WInstr.literal p, WInstr.lookup ctl2 ps2]) =
      ECDSAAdd.measurementCount p := by
  simp [literalRecords]

attribute [local irreducible] normalizeW literalRecords literalToffolis traversals
  codeSlots literalSlotSum portTotal

theorem phase_cancel_base (ph : Bool) (mag c a1 a2 a3 p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (c * (a1 * a2 * a3 * p)) =
      mag * c * a1 * a2 * a3 * (if ph then (-1 : ℂ) else 1) := by
  calc (if ph then (-1 : ℂ) else 1) * (mag * p) * (c * (a1 * a2 * a3 * p))
      = mag * c * a1 * a2 * a3 * (if ph then (-1 : ℂ) else 1) * (p * p) := by ring
    _ = mag * c * a1 * a2 * a3 * (if ph then (-1 : ℂ) else 1) := by rw [hp, mul_one]

theorem phase_cancel_step2 (ph : Bool) (mag c a1 a2 p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (if ph then (-1 : ℂ) else 1) * (c * a1 * a2 * p) =
      mag * c * a1 * a2 := by
  cases ph <;>
  · simp only [ite_true, ite_false, Bool.false_eq_true]
    calc _ = (mag * c * a1 * a2) * (p * p) := by ring
      _ = mag * c * a1 * a2 := by rw [hp, mul_one]

theorem phase_cancel_step1 (ph : Bool) (mag c a1 p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (if ph then (-1 : ℂ) else 1) * (c * a1 * p) =
      mag * c * a1 := by
  cases ph <;>
  · simp only [ite_true, ite_false, Bool.false_eq_true]
    calc _ = (mag * c * a1) * (p * p) := by ring
      _ = mag * c * a1 := by rw [hp, mul_one]

theorem phase_cancel_step0 (ph : Bool) (mag c p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (if ph then (-1 : ℂ) else 1) * (c * p) =
      mag * c := by
  cases ph <;>
  · simp only [ite_true, ite_false, Bool.false_eq_true]
    calc _ = (mag * c) * (p * p) := by ring
      _ = mag * c := by rw [hp, mul_one]

theorem clearData_loaded_of_clean {n : Nat} (read : ConstantBit n → Bool) (ps : List (LookupPort n))
    (a : Nat) (root : Wire) (s : BasisState) (hroot : s root = true)
    (hnd : (portTargets ps).Nodup)
    (hcl : Clean (portTargets ps) (tableXorState (portMask read ps a) true s)) :
    ∀ q ∈ clearData ps, s q.target = decide (read (q.ref a) = q.value) := by
  intro q hq
  rw [clearData] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hcl' : Clean (portTargets ps) (tableXorState (portMask read ps a) (s root) s) := by
    rw [hroot]; exact hcl
  have hL := loaded_of_clean_unload read ps a root s hnd hcl' p hp
  rw [hroot, Bool.true_and] at hL
  exact hL

theorem clearData_loaded_of_xor {n : Nat} (read : ConstantBit n → Bool) (ps : List (LookupPort n))
    (a : Nat) (s0 s1 : BasisState)
    (hnd : (portTargets ps).Nodup)
    (hcl0 : Clean (portTargets ps) s0)
    (heq : ∀ w ∈ portTargets ps, s1 w = tableXorState (portMask read ps a) true s0 w) :
    ∀ q ∈ clearData ps, s1 q.target = decide (read (q.ref a) = q.value) := by
  intro q hq
  rw [clearData] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hpt : p.target ∈ portTargets ps := List.mem_map.mpr ⟨p, hp, rfl⟩
  change s1 p.target = decide (read (p.ref a) = p.value)
  rw [heq p.target hpt]
  dsimp only [tableXorState]
  rw [port_selected read ps a hnd p hp, hcl0 p.target hpt]
  simp only [Bool.true_and, Bool.false_xor]

theorem clearRegister_eq_xor_of_loaded {n : Nat} (read : ConstantBit n → Bool) (ps : List (LookupPort n))
    (a : Nat) (s : BasisState)
    (hnd : (portTargets ps).Nodup)
    (hload : ∀ q ∈ clearData ps, s q.target = decide (read (q.ref a) = q.value)) :
    clearRegister (portTargets ps) s = tableXorState (portMask read ps a) true s := by
  funext w
  by_cases hw : w ∈ portTargets ps
  · rw [clearRegister_clean (portTargets ps) s w hw]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hL : s p.target = decide (read (p.ref a) = p.value) :=
      hload ⟨p.ref, p.value, p.target⟩ (by rw [clearData]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
    dsimp only [tableXorState]
    rw [port_selected read ps a hnd p hp, hL, Bool.true_and, Bool.xor_self]
  · rw [MeasuredClear.clearRegister_frame (portTargets ps) s w hw]
    exact (tableXorState_outside _ _ _ _ (fun hm => hw (tableBitsMask_subset _ _ hm))).symm

theorem twoPass_state_congr {n : Nat} (read : ConstantBit n → Bool) (sp pp : List (LookupPort n))
    (a : Nat) (sA1 : ECDSAAdd.State) (mB : List Bool) (c : List Wire)
    (hmid : clearRegister c sA1.basis = tableXorState (portMask read sp a) true sA1.basis) :
    let sMid1 : ECDSAAdd.State := ⟨sA1.phase, clearRegister c sA1.basis⟩
    let sL2_1 : ECDSAAdd.State := ⟨sMid1.phase, tableXorState (portMask read pp a) true sMid1.basis⟩
    let sMid2 : ECDSAAdd.State := ⟨sA1.phase, tableXorState (portMask read sp a) true sA1.basis⟩
    let sL2_2 : ECDSAAdd.State := ⟨sMid2.phase, tableXorState (portMask read pp a) true sMid2.basis⟩
    (⟨(ECDSAAdd.run tailPart mB sL2_1).phase,
      tableXorState (portMask read pp a) true (ECDSAAdd.run tailPart mB sL2_1).basis⟩ : ECDSAAdd.State) =
    ⟨(ECDSAAdd.run tailPart mB sL2_2).phase,
      tableXorState (portMask read pp a) true (ECDSAAdd.run tailPart mB sL2_2).basis⟩ := by
  intro sMid1 sL2_1 sMid2 sL2_2
  have hm : sMid1 = sMid2 := congrArg (ECDSAAdd.State.mk sA1.phase) hmid
  have hl : sL2_1 = sL2_2 := congrArg (fun m : ECDSAAdd.State =>
    (⟨m.phase, tableXorState (portMask read pp a) true m.basis⟩ : ECDSAAdd.State)) hm
  rw [hl]

theorem site1_twoPass_run_free {n : Nat} (read : ConstantBit n → Bool) (r : Nat → Fin n)
    (a : Nat) (s sA1 : ECDSAAdd.State) (mA mB : List Bool)
    (hmA : mA.length = ECDSAAdd.measurementCount shortPart)
    (hmB : mB.length = ECDSAAdd.measurementCount tailPart)
    (hroot : s.basis windowRoot = true)
    (hclean : Clean (streamLayout.dialogPool.take 258) s.basis)
    (hsA1 : sA1 = ECDSAAdd.run shortPart mA
      ⟨s.phase, tableXorState (portMask read (WideSigned.Rows.ports r (shortPorts probeRows)) a) true s.basis⟩) :
    let sp := WideSigned.Rows.ports r (shortPorts probeRows)
    let pp := WideSigned.Rows.ports r (pairExtraPorts probeRows)
    let sMid : ECDSAAdd.State := ⟨sA1.phase, tableXorState (portMask read sp a) true sA1.basis⟩
    let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp a) true sMid.basis⟩
    let sB1 := ECDSAAdd.run tailPart mB sL2
    let mPerm := mB.take (ECDSAAdd.measurementCount pairPart) ++ mA ++ mB.drop (ECDSAAdd.measurementCount pairPart)
    (⟨sB1.phase, tableXorState (portMask read pp a) true sB1.basis⟩ : ECDSAAdd.State) =
      ECDSAAdd.run ((specialize (WideSigned.Rows.site r (site1 probeRows)).code a).instantiate read) mPerm s := by
  subst hsA1
  exact (site1_twoPass_run read r a s mA mB hmA hmB hroot hclean).2

theorem add_reassoc4 (a b c d : Nat) : a + (b + (c + d)) = a + b + c + d := by omega

theorem hcodeTP_cons3 {n} (a b c : WEXFast.HBlock n) (r : WEXFast.HCode n) :
    WEXFast.hcodeTP (a :: b :: c :: r) =
      WEXFast.hblockTP a + WEXFast.hblockTP b + WEXFast.hblockTP c + WEXFast.hcodeTP r := by
  rw [hcodeTP_cons, hcodeTP_cons, hcodeTP_cons, add_reassoc4]

theorem fcodeTP_cons3 {n} (a b c : WideBank8.Fast16.FBlock2 n) (r : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.fcodeTP (a :: b :: c :: r) =
      WideBank8.Fast16.fblockTP a + WideBank8.Fast16.fblockTP b + WideBank8.Fast16.fblockTP c +
        WideBank8.Fast16.fcodeTP r := by
  rw [fcodeTP_cons, fcodeTP_cons, fcodeTP_cons, add_reassoc4]

theorem blockRecP2_unit_15 {n} (B : PathShare.Bank) (u : UnitSite n) :
    PathShare.blockRecP2 B (.unit u) =
      codeRecords B.bits B.paths windowRoot (normalizeW u.pre) + u.clear.ports.length +
        (MeasuredClear.recordMeasurements
          (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) u.clear.guard B.hp) + 127) := rfl

theorem blockTP2_unit_15 {n} (B : PathShare.Bank) (u : UnitSite n) :
    PathShare.blockTP2 B (.unit u) =
      literalToffolis (normalizeW u.pre) + traversals u.pre * (2 ^ B.bits.length - 1) +
        ((tableAddressTree B.high 0 1).internalNodes + 120) := rfl

theorem blockRecP2_unit_16 {n} (B : PathShare.Bank) (u : UnitSite n) :
    WideBank8.blockRecP2 B (.unit u) =
      codeRecords B.bits B.paths windowRoot (normalizeW u.pre) + u.clear.ports.length +
        (MeasuredClear.recordMeasurements
          (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) u.clear.guard B.hp) + 255) := rfl

theorem blockTP2_unit_16 {n} (B : PathShare.Bank) (u : UnitSite n) :
    WideBank8.blockTP2 B (.unit u) =
      literalToffolis (normalizeW u.pre) + traversals u.pre * (2 ^ B.bits.length - 1) +
        ((tableAddressTree B.high 0 1).internalNodes + 247) := rfl

theorem site1_slots_le_rowC :
    ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) ≤
      literalSlotSum (erase2 WEXUnlookup.rowC) := by
  rw [ECDSAAdd.Baselines.normalize_slots]
  have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
    unfold WEXUnlookup.rowC; rfl
  have h2 : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
    unfold WEXUnlookup.rowHead; rfl
  apply literalSlotSum_le_of_mem (erase2 WEXUnlookup.rowC) site1Arith
  rw [h1, h2, List.map_append, erase2_append, erase2_append]
  apply List.mem_append_left; apply List.mem_append_left
  rw [WEXUnlookup.rowPre3]
  simp only [List.map_cons, List.map_nil, erase2_cons, erase2_nil, List.append_nil, toBlock2,
    Block2.code, UnitSite.code, site1, MaskedSite.prefix, wLiteral]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))


/-! ### Part B: Wide (16-bit) two-pass `site1` and spliced row `Wide16` -/

namespace Wide16
open WideSigned

def r16 : Nat → Fin 65536 := WideBank8.Row16.rows

def sp16 : List (LookupPort 65536) := Rows.ports r16 (shortPorts probeRows)
def pp16 : List (LookupPort 65536) := Rows.ports r16 (pairExtraPorts probeRows)
def site1_16 : MaskedSite 65536 := Rows.site r16 (site1 probeRows)

theorem sp16_targets : portTargets sp16 = shortWires := by
  rw [sp16, Rows.targets]; exact shortPorts_targets probeRows
theorem pp16_targets : portTargets pp16 = pairExtraWires := by
  rw [pp16, Rows.targets]; exact pairExtraPorts_targets probeRows
theorem sp16_length : sp16.length = 258 := by
  rw [sp16, Rows.ports, List.length_map]; exact shortPorts_length probeRows
theorem pp16_length : pp16.length = 513 := by
  rw [pp16, Rows.ports, List.length_map]; exact pairExtraPorts_length probeRows

def fA : SS2 65536 where
  bits := WideBank8.Fast16.windowBits
  paths := WideBank8.Fast16.pathBank
  selBits := WideBank8.Fast16.selBits
  selPaths := WideBank8.Fast16.selPaths
  guard := windowRoot
  ports := sp16
  g1 := gA1
  g2 := gA2
  g3 := gA3

def fB : SS1 65536 where
  bits := WideBank8.Fast16.windowBits
  paths := WideBank8.Fast16.pathBank
  selBits := WideBank8.Fast16.selBits1
  selPaths := WideBank8.Fast16.selPaths1
  guard := windowRoot
  ports := pp16
  g1 := gB

theorem fA_geo : fA.Geo where
  bitsEq := by decide
  pathsSub := by
    intro w hw
    simp only [fA, WideBank8.Fast16.selPaths, WideBank8.Fast16.pathBank,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw ⊢
    dsimp only [Wire, ECDSAAdd.Wire] at hw ⊢; omega
  selLen := by decide
  selNodup := by decide
  selDisj := by
    apply List.disjoint_left.mpr
    intro w hw hm
    rw [fA, sp16_targets] at hm
    have hb := mem_short_garbA hm
    simp only [fA, windowRoot, WideBank8.Fast16.selBits, WideBank8.Fast16.selPaths,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change gA1.length = sp16.length; rw [gA1_len, sp16_length]
  len2 := by change gA2.length = sp16.length; rw [gA2_len, sp16_length]
  len3 := by change gA3.length = sp16.length; rw [gA3_len, sp16_length]
  nodup := by rw [fA, sp16_targets]; exact short_garbA_nodup
  n855 := fun hm => by rw [fA, sp16_targets] at hm; have := mem_short_garbA hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  n856 := fun hm => by rw [fA, sp16_targets] at hm; have := mem_short_garbA hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem fB_geo : fB.Geo where
  bitsEq := by decide
  pathsSub := by
    intro w hw
    simp only [fB, WideBank8.Fast16.selPaths1, WideBank8.Fast16.pathBank,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw ⊢
    dsimp only [Wire, ECDSAAdd.Wire] at hw ⊢; omega
  selLen := by decide
  selNodup := by decide
  selDisj := by
    apply List.disjoint_left.mpr
    intro w hw hm
    rw [fB, pp16_targets] at hm
    have hb := mem_pairExtra_gB hm
    simp only [fB, windowRoot, WideBank8.Fast16.selBits1, WideBank8.Fast16.selPaths1,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change gB.length = pp16.length; rw [gB_len, pp16_length]
  nodup := by rw [fB, pp16_targets]; exact pairExtra_gB_nodup
  n855 := fun hm => by rw [fB, pp16_targets] at hm; have := mem_pairExtra_gB hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

def hot8 (i : Fin 256) : Wire := 14374 + i.val
def scratch8 : Wire := 14373
def tree8 : UnaryActionTree := tableAddressTree WideBank8.Fast16.bank15.high 0 1

def d1 : List (MeasuredClear.ClearPort 65536) := clearData fA.garbPorts
def d2 : List (MeasuredClear.ClearPort 65536) := clearData sp16
def d3 : List (MeasuredClear.ClearPort 65536) := clearData fB.garbPorts
def d4 : List (MeasuredClear.ClearPort 65536) := clearData pp16
def allData : List (MeasuredClear.ClearPort 65536) := d1 ++ d2 ++ d3 ++ d4

theorem d1_targets : d1.map MeasuredClear.ClearPort.target = garbA := by
  rw [d1, clearData_targets]; exact fA.garbPorts_targets fA_geo
theorem d2_targets : d2.map MeasuredClear.ClearPort.target = shortWires := by
  rw [d2, clearData_targets]; exact sp16_targets
theorem d3_targets : d3.map MeasuredClear.ClearPort.target = gB := by
  rw [d3, clearData_targets]; exact fB.garbPorts_targets fB_geo
theorem d4_targets : d4.map MeasuredClear.ClearPort.target = pairExtraWires := by
  rw [d4, clearData_targets]; exact pp16_targets

theorem d1_len : d1.length = 774 := by
  have := congrArg List.length d1_targets; simpa [garbA_len] using this
theorem d2_len : d2.length = 258 := by
  have := congrArg List.length d2_targets; simpa [shortWires_length] using this
theorem d3_len : d3.length = 513 := by
  have := congrArg List.length d3_targets; simpa [gB_len] using this
theorem d4_len : d4.length = 513 := by
  have := congrArg List.length d4_targets; simpa [pairExtraWires_length] using this
theorem allData_len : allData.length = 2058 := by
  simp only [allData, List.length_append, d1_len, d2_len, d3_len, d4_len]

def fixRec8 : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree8 windowRoot WideBank8.Fast16.bank15.hp) + 255

theorem tree8_layout : tree8.Layout windowRoot WideBank8.Fast16.bank15.hp :=
  tableAddressTree_layout _ _ _ 0 1 (by decide) (by decide)

theorem tree8_nodes : tree8.internalNodes = 255 := WideBank8.Fast16.high_nodes

theorem tree8_leaves : tree8.leaves = 256 := by
  have h := MeasuredClear.addressTree_leaves WideBank8.Fast16.bank15.high 0 1
  simpa [tree8, WideBank8.Fast16.bank15, WideBank8.Fast16.high] using h

theorem fixRec8_eq : fixRec8 = 510 := by
  rw [fixRec8, (MeasuredClear.recordUnary_counts tree8 windowRoot WideBank8.Fast16.bank15.hp tree8_layout 0).1,
    tree8_nodes]

theorem fA_rec : codeRecords fA.selBits fA.selPaths windowRoot fA.selCode = 16383 := by
  rw [fA.loadProg_records fA_geo]; decide

theorem fB_rec : codeRecords fB.selBits fB.selPaths windowRoot fB.selCode = 32767 := by
  rw [fB.loadProg_records fB_geo]; decide

def step8 (start : Nat) (refs123 : List (Fin start)) : Straight 65536 start (start + (513 + fixRec8)) :=
  castFinish (by rw [pairExtraWires_length]; exact Nat.add_assoc start 513 fixRec8)
    (MeasuredClear.measureThen (R := fixRec8)
      (fun cursor rs => castFinish (by rw [fixRec8]; exact Nat.add_assoc cursor _ 255)
        (MeasuredClear.fixupProgram8 allData rs WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp))
      pairExtraWires start refs123)

def step78 (start : Nat) (refs123 : List (Fin start)) : Straight 65536 start (start + (mTail + (513 + fixRec8))) :=
  castFinish (Nat.add_assoc start mTail (513 + fixRec8))
    ((literalFixed tailNorm mTail ((literal_meas (n := 65536) _).trans tailNorm_meas) start).append
      (step8 (start + mTail) (refs123.map (Fin.castLE (Nat.le_add_right _ _)))))

def step678 (start : Nat) (refs12 : List (Fin start)) :
    Straight 65536 start (start + (513 + (mTail + (513 + fixRec8)))) :=
  castFinish (by rw [gB_len]; exact Nat.add_assoc start 513 _)
    (MeasuredClear.measureThen (R := mTail + (513 + fixRec8))
      (fun cursor rs => step78 cursor rs) gB start refs12)

def step5678 (start : Nat) (refs12 : List (Fin start)) :
    Straight 65536 start (start + (32767 + (513 + (mTail + (513 + fixRec8))))) :=
  castFinish (by rw [fB_rec]; exact Nat.add_assoc start 32767 _)
    ((fB.loadProg start).append
      (step678 (start + codeRecords fB.selBits fB.selPaths windowRoot fB.selCode)
        (refs12.map (Fin.castLE (Nat.le_add_right _ _)))))

def step4_8 (start : Nat) (refs1 : List (Fin start)) :
    Straight 65536 start (start + (258 + (32767 + (513 + (mTail + (513 + fixRec8)))))) :=
  castFinish (by rw [shortWires_length]; exact Nat.add_assoc start 258 _)
    (MeasuredClear.measureThen (R := 32767 + (513 + (mTail + (513 + fixRec8))))
      (fun cursor rs => step5678 cursor rs) shortWires start refs1)

def step3_8 (start : Nat) (refs1 : List (Fin start)) :
    Straight 65536 start (start + (mShort + (258 + (32767 + (513 + (mTail + (513 + fixRec8))))))) :=
  castFinish (Nat.add_assoc start mShort _)
    ((literalFixed shortNorm mShort ((literal_meas (n := 65536) _).trans shortNorm_meas) start).append
      (step4_8 (start + mShort) (refs1.map (Fin.castLE (Nat.le_add_right _ _)))))

def step2_8 (start : Nat) :
    Straight 65536 start (start + (774 + (mShort + (258 + (32767 + (513 + (mTail + (513 + fixRec8)))))))) :=
  castFinish (by rw [garbA_len]; exact Nat.add_assoc start 774 _)
    (MeasuredClear.measureThen (R := mShort + (258 + (32767 + (513 + (mTail + (513 + fixRec8))))))
      (fun cursor rs => step3_8 cursor rs) garbA start List.nil)

def site1Rec : Nat := site1RecGen 16383 32767 mShort mTail fixRec8

def twoPassProg (start : Nat) : Straight 65536 start (start + site1Rec) :=
  castFinish (twoPass_fin_gen start _ 16383 32767 mShort mTail fixRec8 fA_rec)
    ((fA.loadProg start).append
      (step2_8 (start + codeRecords fA.selBits fA.selPaths windowRoot fA.selCode)))

attribute [local irreducible] step8 step78 step678 step5678 step4_8 step3_8 step2_8 twoPassProg

def step8Src (read : ConstantBit 65536 → Bool) (o123 : List Bool) : AdaptiveCircuit :=
  measureResetThen pairExtraWires (fun o4 =>
    MeasuredClear.fixupSource8 allData (o123 ++ o4) read WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp)

def step78Src (read : ConstantBit 65536 → Bool) (o123 : List Bool) : AdaptiveCircuit :=
  (literalSource tailNorm).seq (step8Src read o123)

def step678Src (read : ConstantBit 65536 → Bool) (o12 : List Bool) : AdaptiveCircuit :=
  measureResetThen gB (fun o3 => step78Src read (o12 ++ o3))

def step5678Src (read : ConstantBit 65536 → Bool) (o12 : List Bool) : AdaptiveCircuit :=
  (fB.loadSource read).seq (step678Src read o12)

def step4_8Src (read : ConstantBit 65536 → Bool) (o1 : List Bool) : AdaptiveCircuit :=
  measureResetThen shortWires (fun o2 => step5678Src read (o1 ++ o2))

def step3_8Src (read : ConstantBit 65536 → Bool) (o1 : List Bool) : AdaptiveCircuit :=
  (literalSource shortNorm).seq (step4_8Src read o1)

def step2_8Src (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  measureResetThen garbA (fun o1 => step3_8Src read o1)

def twoPassSrc (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  (fA.loadSource read).seq (step2_8Src read)

theorem step8_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs123 : List (Fin start))
    (h : Fin start → Bool) :
    ((step8 start refs123).instantiate read h).run = (step8Src read (refs123.map h)).run := by
  rw [step8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => MeasuredClear.fixupSource8 allData o read WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp) read
      (fun cursor rs hh => by rw [castFinish_instantiate, MeasuredClear.fixupProgram_run8])]
  rfl

theorem step78_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs123 : List (Fin start))
    (h : Fin start → Bool) :
    ((step78 start refs123).instantiate read h).run = (step78Src read (refs123.map h)).run := by
  rw [step78, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step8Src read (refs123.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step8_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step678_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs12 : List (Fin start))
    (h : Fin start → Bool) :
    ((step678 start refs12).instantiate read h).run = (step678Src read (refs12.map h)).run := by
  rw [step678, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step78Src read o) read
      (fun cursor rs hh => step78_run read cursor rs hh)]
  rfl

theorem step5678_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs12 : List (Fin start))
    (h : Fin start → Bool) :
    ((step5678 start refs12).instantiate read h).run = (step5678Src read (refs12.map h)).run := by
  rw [step5678, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step678Src read (refs12.map h)),
    AdaptiveCircuit.run_seq, fB.loadProg_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step678_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step4_8_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs1 : List (Fin start))
    (h : Fin start → Bool) :
    ((step4_8 start refs1).instantiate read h).run = (step4_8Src read (refs1.map h)).run := by
  rw [step4_8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step5678Src read o) read
      (fun cursor rs hh => step5678_run read cursor rs hh)]
  rfl

theorem step3_8_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs1 : List (Fin start))
    (h : Fin start → Bool) :
    ((step3_8 start refs1).instantiate read h).run = (step3_8Src read (refs1.map h)).run := by
  rw [step3_8, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step4_8Src read (refs1.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'
    rw [step4_8_run, List.map_map]
    congr 2; rw [← hh']; rfl

theorem step2_8_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((step2_8 start).instantiate read h).run = (step2_8Src read).run := by
  rw [step2_8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => step3_8Src read o) read
      (fun cursor rs hh => step3_8_run read cursor rs hh)]
  simp only [List.map_nil, List.nil_append]; rfl

theorem twoPass_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((twoPassProg start).instantiate read h).run = (twoPassSrc read).run := by
  rw [twoPassProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun hh => step2_8_run read _ hh),
    AdaptiveCircuit.run_seq, fA.loadProg_run, ← AdaptiveCircuit.run_seq]
  rfl

theorem hot8_inj : Function.Injective hot8 := fun i j he => by
  apply Fin.ext; simp only [hot8] at he; dsimp only [Wire] at he; omega

theorem low8_ne_hot8 (i : Fin 8) (j : Fin 256) : WideBank8.low8 i ≠ hot8 j := by
  have hi := i.isLt; simp only [WideBank8.low8, hot8]; dsimp only [Wire]; omega

theorem hot8_disj : (MeasuredClear.hotBank8 hot8).Disjoint
    (windowRoot :: tree8.indexWires.dedup ++ WideBank8.Fast16.bank15.hp) := by
  apply List.disjoint_left.mpr
  intro w hw hm
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  have hi := i.isLt
  rw [tree8, WideBank8.Fast16.bank15_ok.index] at hm
  simp only [hot8, windowRoot, WideBank8.Fast16.bank15, WideBank8.Fast16.high,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hm
  dsimp only [Wire] at *; omega

theorem scratch8_not_tree : scratch8 ∉ windowRoot :: tree8.indexWires.dedup ++ WideBank8.Fast16.bank15.hp := by
  rw [tree8, WideBank8.Fast16.bank15_ok.index]
  simp only [scratch8, windowRoot, WideBank8.Fast16.bank15, WideBank8.Fast16.high,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire]; omega

theorem scratch8_not_hot : scratch8 ∉ MeasuredClear.hotBank8 hot8 := by
  intro hm; obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp only [scratch8, hot8] at hi; dsimp only [Wire] at hi; omega

theorem hot8_in_pairExtra (i : Fin 256) : hot8 i ∈ pairExtraWires := by
  apply List.mem_append_left
  rw [scrPairWires_explicit]
  have hi := i.isLt
  simp only [hot8, List.mem_append, List.mem_cons, List.mem_range'_1, List.mem_singleton]
  dsimp only [Wire, ECDSAAdd.Wire]; omega

theorem twoPass_tCount (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((twoPassProg start).instantiate read h).tCount =
      7 * (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 247)) := by
  have h8 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step8 c rs).instantiate read hh).tCount = 7 * (255 + 247) := by
    rw [step8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => by
      rw [castFinish_instantiate, MeasuredClear.fixupProgram_tCount8 _ _ _ _ _ _ _ _ tree8_layout, tree8_nodes])]
  have h78 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step78 c rs).instantiate read hh).tCount = 7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247) := by
    rw [step78, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h8 _ _ h'), literalFixed_tCount]
  have h678 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step678 c rs).instantiate read hh).tCount = 7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247) := by
    rw [step678, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h78 cur rs' h')]
  have h5678 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step5678 c rs).instantiate read hh).tCount =
        7 * (32767 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247)) := by
    rw [step5678, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h678 _ _ h'),
      fB.loadProg_tCount read fB_geo]
    have hbl : fB.selBits.length = 15 := by decide
    have hpl : fB.ports.length = 513 := pp16_length
    rw [hbl, hpl, show 2 ^ 15 - 1 = 32767 from rfl]
  have h48 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step4_8 c rs).instantiate read hh).tCount =
        7 * (32767 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247)) := by
    rw [step4_8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h5678 cur rs' h')]
  have h38 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step3_8 c rs).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount shortNorm +
          (7 * (32767 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247))) := by
    rw [step3_8, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h48 _ _ h'), literalFixed_tCount]
  have h28 (c : Nat) (hh : Fin c → Bool) :
      ((step2_8 c).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount shortNorm +
          (7 * (32767 + 513) + (7 * ECDSAAdd.toffoliCount tailNorm + 7 * (255 + 247))) := by
    rw [step2_8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h38 cur rs' h')]
  rw [twoPassProg, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h28 _ h'),
    fA.loadProg_tCount read fA_geo]
  have hbl : fA.selBits.length = 14 := by decide
  have hpl : fA.ports.length = 258 := sp16_length
  rw [hbl, hpl, show 2 ^ 14 - 1 = 16383 from rfl, show 3 * 258 = 774 from rfl]
  exact twoPass_tcount_arith 16383 774 (ECDSAAdd.toffoliCount shortNorm) 32767 513 (ECDSAAdd.toffoliCount tailNorm) (255 + 247)

theorem twoPass_residue (start : Nat) : AndGadget.residue (twoPassProg start) = 0 := by
  have h8 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step8 c rs) = 0 := by
    rw [step8, AndGadget.residue_cast]
    exact MeasuredClear.measureThen_residue _ (fun _ _ => by rw [AndGadget.residue_cast]; exact MeasuredClear.fixupProgram_residue8 _ _ _ _ _ _ _ _) _ _ _
  have h78 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step78 c rs) = 0 := by
    rw [step78, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast,
      WEXCredit.literal_residue, h8]
  have h678 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step678 c rs) = 0 := by
    rw [step678, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h78 _ _ _
  have h5678 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step5678 c rs) = 0 := by
    rw [step5678, AndGadget.residue_cast, AndGadget.residue_append, fB.loadProg_residue, h678]
  have h48 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step4_8 c rs) = 0 := by
    rw [step4_8, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h5678 _ _ _
  have h38 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step3_8 c rs) = 0 := by
    rw [step3_8, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast,
      WEXCredit.literal_residue, h48]
  have h28 (c : Nat) : AndGadget.residue (step2_8 c) = 0 := by
    rw [step2_8, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h38 _ _ _
  rw [twoPassProg, AndGadget.residue_cast, AndGadget.residue_append, fA.loadProg_residue, h28]

theorem twoPass_wellFormed (start : Nat) : (twoPassProg start).WellFormed := by
  have h8 (c : Nat) (rs : List (Fin c)) : (step8 c rs).WellFormed := by
    rw [step8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := fixRec8) _ (fun _ _ => by
      rw [castFinish_wellFormed]
      exact MeasuredClear.fixupProgram_wellFormed8 _ _ _ _ _ _ _ _ tree8_layout hot8_inj low8_ne_hot8
        scratch8_not_tree scratch8_not_hot) _ _ _
  have h78 (c : Nat) (rs : List (Fin c)) : (step78 c rs).WellFormed := by
    rw [step78, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ tailNorm_valid _) (h8 _ _)
  have h678 (c : Nat) (rs : List (Fin c)) : (step678 c rs).WellFormed := by
    rw [step678, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mTail + (513 + fixRec8)) (fun cur rs' => step78 cur rs') h78 gB c rs
  have h5678 (c : Nat) (rs : List (Fin c)) : (step5678 c rs).WellFormed := by
    rw [step5678, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (fB.loadProg_wellFormed fB_geo _) (h678 _ _)
  have h48 (c : Nat) (rs : List (Fin c)) : (step4_8 c rs).WellFormed := by
    rw [step4_8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := 32767 + (513 + (mTail + (513 + fixRec8)))) (fun cur rs' => step5678 cur rs') h5678 shortWires c rs
  have h38 (c : Nat) (rs : List (Fin c)) : (step3_8 c rs).WellFormed := by
    rw [step3_8, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ shortNorm_valid _) (h48 _ _)
  have h28 (c : Nat) : (step2_8 c).WellFormed := by
    rw [step2_8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mShort + (258 + (32767 + (513 + (mTail + (513 + fixRec8)))))) (fun cur rs' => step3_8 cur rs') h38 garbA c List.nil
  rw [twoPassProg, castFinish_wellFormed]
  exact straight_append_wellFormed _ _ (fA.loadProg_wellFormed fA_geo _) (h28 _)

theorem twoPass_support (start : Nat) :
    ChallengeMigration.straightWires (twoPassProg start) ⊆ WideBank8.Fast16.Tight.support := by
  have hcov := WideBank8.Fast16.Tight.old_cover
  have hroot : windowRoot ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.root_new
  have h855 : (855 : Wire) ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new ⟨0, by decide⟩
  have h856 : (856 : Wire) ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new ⟨1, by decide⟩
  have hsA : fA.selBits ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selBits_new
  have hpA : fA.selPaths ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selPaths_new
  have hsB : fB.selBits ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selBits1_new
  have hpB : fB.selPaths ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selPaths1_new
  have hlow : ∀ i : Fin 8, WideBank8.low8 i ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new
  have hhot : ∀ i : Fin 256, hot8 i ∈ WideBank8.Fast16.Tight.support := fun i =>
    hcov (pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_left _ (hot8_in_pairExtra i))))
  have hscr : scratch8 ∈ WideBank8.Fast16.Tight.support :=
    hcov (pool_band_in_newH7 (by rw [scratch8]; left; dsimp only [Wire]; omega))
  have htree : tree8.indexWires ⊆ WideBank8.Fast16.Tight.support := by
    intro w hw; rw [tree8] at hw
    have h1 : w ∈ WideBank8.Fast16.bank15.high := by
      have := List.mem_dedup.mpr hw; rw [WideBank8.Fast16.bank15_ok.index] at this; exact this
    exact WideBank8.Fast16.Tight.high_new h1
  have hhp : WideBank8.Fast16.bank15.hp ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    WideBank8.Fast16.Tight.bank_new (WideBank8.Fast16.bank15_ok.sub w hw)
  have hregA : portTargets fA.ports ++ fA.garb ⊆ WideBank8.Fast16.Tight.support := fun w hw => by
    rw [fA, sp16_targets] at hw; exact hcov (pool_band_in_newH7 (mem_short_garbA hw))
  have hregB : portTargets fB.ports ++ fB.g1 ⊆ WideBank8.Fast16.Tight.support := fun w hw => by
    rw [fB, pp16_targets] at hw; exact hcov (pool_band_in_newH7 (mem_pairExtra_gB hw))
  have hgarbA : garbA ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (pool_band_in_newH7 (mem_short_garbA (List.mem_append_right _ hw)))
  have hshortW : shortWires ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (pool_band_in_newH7 (mem_short_garbA (List.mem_append_left _ hw)))
  have hgB : gB ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_right _ hw)))
  have hpairW : pairExtraWires ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (pool_band_in_newH7 (mem_pairExtra_gB (List.mem_append_left _ hw)))
  have hshortN : ECDSAAdd.wires shortNorm ⊆ WideBank8.Fast16.Tight.support.toFinset := fun w hw =>
    List.mem_toFinset.mpr (hcov (List.mem_toFinset.mp (shortPart_wires_newH7 hw)))
  have htailN : ECDSAAdd.wires tailNorm ⊆ WideBank8.Fast16.Tight.support.toFinset := fun w hw =>
    List.mem_toFinset.mpr (hcov (List.mem_toFinset.mp (tailPart_wires_newH7 hw)))
  have h8 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step8 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun _ _ => by
      rw [MeasuredClear.static_cast]
      exact MeasuredClear.fixupProgram_within8 _ _ _ _ _ _ _ _ _ hroot hscr hlow hhot htree hhp) _ _ _ hpairW
  have h78 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step78 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step78, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ htailN _, h8 _ _⟩
  have h678 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step678 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step678, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h78 cur rs') _ _ _ hgB
  have h5678 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step5678 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step5678, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨fB.loadProg_support fB_geo _ hroot hroot h855 hsB hpB hregB _, h678 _ _⟩
  have h48 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step4_8 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step4_8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h5678 cur rs') _ _ _ hshortW
  have h38 (c : Nat) (rs : List (Fin c)) :
      ChallengeMigration.straightWires (step3_8 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step3_8, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ hshortN _, h48 _ _⟩
  have h28 (c : Nat) :
      ChallengeMigration.straightWires (step2_8 c) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step2_8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h38 cur rs') _ _ _ hgarbA
  rw [twoPassProg, support_cast, straightWires_append]
  exact List.append_subset.mpr ⟨fA.loadProg_support fA_geo _ hroot hroot h855 h856 hsA hpA hregA _, h28 _⟩

theorem twoPass_slots (start : Nat) :
    (twoPassProg start).gateSlots ≤
      4 * ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) + 610000000 := by
  have h8 (c : Nat) (rs : List (Fin c)) :
      (step8 c rs).gateSlots ≤ 1024 * allData.length * 256 + 10 * 255 + 2291 := by
    rw [step8, castFinish_gateSlots, MeasuredClear.measureThen_slots _
      (fun k => 1024 * min allData.length k * 256 + 10 * 255 + 2291)
      (fun cur rs' => by
        rw [castFinish_gateSlots, MeasuredClear.fixupProgram_slots8 _ _ _ _ _ _ _ _ tree8_layout,
          tree8_leaves, tree8_nodes])]
    have hmin : min allData.length (rs.length + pairExtraWires.length) ≤ allData.length := Nat.min_le_left _ _
    omega
  have h78 (c : Nat) (rs : List (Fin c)) :
      (step78 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291) := by
    rw [step78, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 65536) tailNorm
    have h8' := h8 (c + mTail) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at hl ⊢
    omega
  have h678 (c : Nat) (rs : List (Fin c)) :
      (step678 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291) := by
    rw [step678, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step78 cur rs') _ h78 gB c rs
  have h5678 (c : Nat) (rs : List (Fin c)) :
      (step5678 c rs).gateSlots ≤ (2 ^ 15 * (2 * 513) + 10 * (2 ^ 15 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291)) := by
    rw [step5678, castFinish_gateSlots, Straight.gateSlots_append]
    have hb := fB.loadProg_slots fB_geo c
    have hbl : fB.selBits.length = 15 := by decide
    have hpl : fB.ports.length = 513 := pp16_length
    rw [hbl, hpl] at hb
    have h6 := h678 (c + codeRecords fB.selBits fB.selPaths windowRoot fB.selCode) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at h6 ⊢
    omega
  have h48 (c : Nat) (rs : List (Fin c)) :
      (step4_8 c rs).gateSlots ≤ (2 ^ 15 * (2 * 513) + 10 * (2 ^ 15 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291)) := by
    rw [step4_8, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step5678 cur rs') _ h5678 shortWires c rs
  have h38 (c : Nat) (rs : List (Fin c)) :
      (step3_8 c rs).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots shortNorm +
        ((2 ^ 15 * (2 * 513) + 10 * (2 ^ 15 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291))) := by
    rw [step3_8, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 65536) shortNorm
    have h4 := h48 (c + mShort) (rs.map (Fin.castLE (Nat.le_add_right _ _)))
    generalize ECDSAAdd.Challenge.gateSlots shortNorm = gS at hl ⊢
    generalize ECDSAAdd.Challenge.gateSlots tailNorm = gT at h4 ⊢
    omega
  have h28 (c : Nat) :
      (step2_8 c).gateSlots ≤ 4 * ECDSAAdd.Challenge.gateSlots shortNorm +
        ((2 ^ 15 * (2 * 513) + 10 * (2 ^ 15 - 1) + 12 * 513) +
        (4 * ECDSAAdd.Challenge.gateSlots tailNorm + (1024 * allData.length * 256 + 10 * 255 + 2291))) := by
    rw [step2_8, castFinish_gateSlots]
    exact measureThen_slots_le (fun cur rs' => step3_8 cur rs') _ h38 garbA c List.nil
  rw [twoPassProg, castFinish_gateSlots, Straight.gateSlots_append]
  have ha := fA.loadProg_slots fA_geo start
  have hbl : fA.selBits.length = 14 := by decide
  have hpl : fA.ports.length = 258 := sp16_length
  rw [hbl, hpl] at ha
  have h2 := h28 (start + codeRecords fA.selBits fA.selPaths windowRoot fA.selCode)
  have hns := norm_slots_split
  rw [allData_len] at h2
  generalize ECDSAAdd.Challenge.gateSlots shortNorm = gsS at h2 hns
  generalize ECDSAAdd.Challenge.gateSlots tailNorm = gsT at h2 hns
  generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) = gsA at hns ⊢
  omega

theorem twoPass_sim (read : ConstantBit 65536 → Bool) :
    ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
        ∀ a (st : ECDSAAdd.State), AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          Clean WideBank8.Fast16.pathBank st.basis →
          Clean streamLayout.dialogPool st.basis →
          (∀ m', Clean scrAllWires
            (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis) →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m st))
      (twoPassSrc read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hsplit : ∀ s : BasisState, 256 * tree8.routeLabel s + MeasuredClear.hotAddress8 WideBank8.low8 s =
      tableAddressValue WideBank8.Fast16.windowBits s := WideBank8.Fast16.bank15_ok.split
  have hbits_no_pe : ∀ w ∈ WideBank8.Fast16.windowBits, w ∉ pairExtraWires := fun w hw hm => by
    have hb := mem_pairExtra hm
    simp only [WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hhp_no_pe : ∀ w ∈ WideBank8.Fast16.bank15.hp, w ∉ pairExtraWires := fun w hw hm => by
    have hb := mem_pairExtra hm
    simp only [WideBank8.Fast16.bank15, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hroot_no_pe : windowRoot ∉ pairExtraWires := windowRoot_not_pairExtra
  have hsite1_win16 : ∀ w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank,
      w ∉ ECDSAAdd.wires site1Arith := fun w hw hm => by
    have hgeo : PathShare.UnitGeoP WideBank8.Fast16.bank15 (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩) :=
      WideBank8.Row16.geometry (.std (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩))) (by
        unfold WideBank8.Row16.code
        apply List.mem_append_left
        refine List.mem_map.mpr ⟨.std (.unit ⟨(site1 probeRows).prefix, site1 probeRows⟩), ?_, rfl⟩
        rw [WideBank8.Row16.headF]
        apply List.mem_append_left
        rw [WEXUnlookup.rowPre3]; simp [toBlock2])
    exact hgeo.placed (WInstr.literal site1Arith)
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) w hw hm
  have htail_avoid_window : ∀ w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank,
      w ∉ ECDSAAdd.wires tailPart := fun w hw hm => hsite1_win16 w hw (tailPart_wires_sub hm)
  have hshort_avoid_window : ∀ w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank,
      w ∉ ECDSAAdd.wires shortPart := fun w hw hm => hsite1_win16 w hw (shortPart_wires_sub hm)
  have h8_sim (o1 o2 o3 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) (ho3 : o3.length = 513) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∀ a (next : ECDSAAdd.State) (u1 u2 u3 : BasisState),
          tableAddressValue WideBank8.Fast16.windowBits next.basis = a →
          next.basis windowRoot = true →
          Clean WideBank8.Fast16.bank15.hp next.basis →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, next.basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet next) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
              Bridge.signedKet ⟨next.phase, clearRegister pairExtraWires next.basis⟩)
        (step8Src read (o1 ++ o2 ++ o3)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step8Src
    apply MeasuredClear.measureResetThen_sim pairExtraWires _
      (fun o4 => BranchCoherentOn (MeasuredClear.basisIdeal id
        (MeasuredClear.fixupFactor8 allData ((o1 ++ o2 ++ o3) ++ o4) read WideBank8.low8 hot8 tree8 windowRoot))
        (fun s => MeasuredClear.HotClean8 hot8 s ∧ Clean WideBank8.Fast16.bank15.hp s))
    · intro o4 _
      exact MeasuredClear.fixupSource_coherent8 allData _ read WideBank8.low8 hot8 tree8 windowRoot scratch8
        WideBank8.Fast16.bank15.hp tree8_layout hot8_inj low8_ne_hot8 hot8_disj scratch8_not_tree scratch8_not_hot
    · intro o4 ho4 b c hb a next u1 u2 u3 haddr hroot hhp hu1 hu2 hu3 hu4
      have hk := xResetRegisterKraus_ket pairExtraWires o4 next.basis ho4 pairExtra_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho4] at hk
      set t := clearRegister pairExtraWires next.basis with ht
      have hfr (w : Wire) (hw : w ∉ pairExtraWires) : t w = next.basis w :=
        MeasuredClear.clearRegister_frame _ _ _ hw
      have hhot : MeasuredClear.HotClean8 hot8 t := fun i => clearRegister_clean _ _ _ (hot8_in_pairExtra i)
      have hvalid : MeasuredClear.HotClean8 hot8 t ∧ Clean WideBank8.Fast16.bank15.hp t :=
        ⟨hhot, fun w hw => by rw [hfr w (hhp_no_pe w hw)]; exact hhp w hw⟩
      have haddr_t : tableAddressValue WideBank8.Fast16.windowBits t = a :=
        (WEX.tableAddressValue_congr _ _ _ (fun w hw => hfr w (hbits_no_pe w hw))).trans haddr
      have hroot_t : t windowRoot = true := (hfr _ hroot_no_pe).trans hroot
      have hfac : MeasuredClear.fixupFactor8 allData ((o1 ++ o2 ++ o3) ++ o4) read WideBank8.low8 hot8 tree8 windowRoot t =
          registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 *
            registerXPhase gB o3 u3 * registerXPhase pairExtraWires o4 next.basis := by
        have hlen12 : (o1 ++ o2).length = (d1 ++ d2).length := by simp [ho1, ho2, d1_len, d2_len]
        have hlen123 : (o1 ++ o2 ++ o3).length = (d1 ++ d2 ++ d3).length := by
          simp [ho1, ho2, ho3, d1_len, d2_len, d3_len]
        rw [allData, MeasuredClear.fixupFactor8_append _ _ _ _ hlen123,
          MeasuredClear.fixupFactor8_append _ _ _ _ hlen12,
          MeasuredClear.fixupFactor8_append _ _ _ _ (by rw [ho1, d1_len])]
        have hf1 : MeasuredClear.fixupFactor8 d1 o1 read WideBank8.low8 hot8 tree8 windowRoot t =
            registerXPhase garbA o1 u1 := by
          rw [← d1_targets]
          exact MeasuredClear.fixupFactor8_loaded d1 o1 read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            hot8_inj low8_ne_hot8 hot8_disj t u1 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu1 q hq)
        have hf2 : MeasuredClear.fixupFactor8 d2 o2 read WideBank8.low8 hot8 tree8 windowRoot t =
            registerXPhase shortWires o2 u2 := by
          rw [← d2_targets]
          exact MeasuredClear.fixupFactor8_loaded d2 o2 read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            hot8_inj low8_ne_hot8 hot8_disj t u2 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu2 q hq)
        have hf3 : MeasuredClear.fixupFactor8 d3 o3 read WideBank8.low8 hot8 tree8 windowRoot t =
            registerXPhase gB o3 u3 := by
          rw [← d3_targets]
          exact MeasuredClear.fixupFactor8_loaded d3 o3 read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            hot8_inj low8_ne_hot8 hot8_disj t u3 hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu3 q hq)
        have hf4 : MeasuredClear.fixupFactor8 d4 o4 read WideBank8.low8 hot8 tree8 windowRoot t =
            registerXPhase pairExtraWires o4 next.basis := by
          rw [← d4_targets]
          exact MeasuredClear.fixupFactor8_loaded d4 o4 read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            hot8_inj low8_ne_hot8 hot8_disj t next.basis hhot (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using hu4 q hq)
        rw [hf1, hf2, hf3, hf4]
      have hsq := MeasuredClear.registerXPhase_square pairExtraWires o4 next.basis
      change b.kraus (xResetRegisterKraus pairExtraWires o4 (Bridge.signedKet next)) = _
      simp only [Bridge.signedKet, map_smul, hk, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac, smul_smul, ← ht]
      exact congrArg (· • ket t) (phase_cancel_base next.phase (registerXResetMagnitude pairExtraWires.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 u2) (registerXPhase gB o3 u3)
        (registerXPhase pairExtraWires o4 next.basis) hsq)
  have h78_sim (o1 o2 o3 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) (ho3 : o3.length = 513) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sL2 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
            AddrValid WideBank8.Fast16.windowBits windowRoot a sL2 →
            Clean WideBank8.Fast16.pathBank sL2.basis →
            Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sL2) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step78Src read (o1 ++ o2 ++ o3)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation tailNorm
    obtain ⟨c2, a2, m2⟩ := h8_sim o1 o2 o3 ho1 ho2 ho3
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step78Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    refine ⟨b₁.history, by rw [hb₁.1, tailNorm_meas], ?_⟩
    intro a sL2 u1 u2 u3 ha hpath hclOut hu1 hu2 hu3
    set sB1 := ECDSAAdd.run tailPart b₁.history sL2 with hsB1
    have hnorm : ECDSAAdd.run tailNorm b₁.history sL2 = sB1 := by
      rw [tailNorm]; exact ECDSAAdd.Baselines.normalize_run tailPart b₁.history sL2
    have hrootB : sB1.basis windowRoot = true := by
      rw [hsB1, run_outside_basis tailPart b₁.history sL2 windowRoot tailPart_root]; exact ha.2
    have haddrB : tableAddressValue WideBank8.Fast16.windowBits sB1.basis = a := by
      rw [← ha.1]; apply WEX.tableAddressValue_congr
      intro w hw; rw [hsB1, run_outside_basis tailPart b₁.history sL2 w (htail_avoid_window w (by simp [hw]))]
    have hhpB : Clean WideBank8.Fast16.bank15.hp sB1.basis := fun w hw => by
      have hw' : w ∈ WideBank8.Fast16.pathBank := WideBank8.Fast16.bank15_ok.sub w hw
      rw [hsB1, run_outside_basis tailPart b₁.history sL2 w (htail_avoid_window w (by simp [hw']))]; exact hpath w hw'
    have hpp_nd : (portTargets pp16).Nodup := by rw [pp16_targets]; exact pairExtra_nodup
    have hclOut' : Clean (portTargets pp16)
        (tableXorState (portMask read pp16 a) (sB1.basis windowRoot) sB1.basis) := by
      rw [pp16_targets, hrootB]; exact hclOut
    have hloadedB : ∀ q ∈ d4, sB1.basis q.target = decide (read (q.ref a) = q.value) :=
      clearData_loaded_of_clean read pp16 a windowRoot sB1.basis hrootB hpp_nd
        (by rw [pp16_targets]; exact hclOut)
    have hclr : clearRegister pairExtraWires sB1.basis =
        tableXorState (portMask read pp16 a) true sB1.basis := by
      have h0 := clear_eq_unload read pp16 a windowRoot sB1.basis hclOut'
      rw [pp16_targets, hrootB] at h0; exact h0
    change b₂.kraus (b₁.kraus (Bridge.signedKet sL2)) = _
    rw [hb₁.2, hnorm, map_smul, hb₂ a sB1 u1 u2 u3 haddrB hrootB hhpB hu1 hu2 hu3 hloadedB, hclr, smul_smul]
    exact congrArg (· • _) (by simp only [mul_assoc])
  have h68_sim (o1 o2 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sB0 : ECDSAAdd.State) (u1 u2 : BasisState),
            let sL2 : ECDSAAdd.State := ⟨sB0.phase, clearRegister gB sB0.basis⟩
            AddrValid WideBank8.Fast16.windowBits windowRoot a sL2 →
            Clean WideBank8.Fast16.pathBank sL2.basis →
            Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, sB0.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sB0) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step678Src read (o1 ++ o2)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step678Src
    apply MeasuredClear.measureResetThen_sim gB _
      (fun o3 b c => ∃ mB : List Bool, mB.length = mTail ∧
        ∀ a (sL2 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
          AddrValid WideBank8.Fast16.windowBits windowRoot a sL2 →
          Clean WideBank8.Fast16.pathBank sL2.basis →
          Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sL2) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2 * registerXPhase gB o3 u3) •
              Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
    · intro o3 ho3
      exact h78_sim o1 o2 o3 ho1 ho2 (by rw [gB_len] at ho3; exact ho3)
    · intro o3 ho3 b c hb
      obtain ⟨mB, hmB, hb⟩ := hb
      refine ⟨mB, hmB, ?_⟩
      intro a sB0 u1 u2 sL2 ha hpath hclOut hu1 hu2 hu3
      have hk := xResetRegisterKraus_ket gB o3 sB0.basis ho3 gB_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho3] at hk
      have hsq := MeasuredClear.registerXPhase_square gB o3 sB0.basis
      change b.kraus (xResetRegisterKraus gB o3 (Bridge.signedKet sB0)) = _
      have hstep := hb a sL2 u1 u2 sB0.basis ha hpath hclOut hu1 hu2 hu3
      rw [show Bridge.signedKet sB0 = (if sB0.phase then (-1 : ℂ) else 1) • ket sB0.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister gB sB0.basis)) =
          (if sB0.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet sL2) := by
        simp only [Bridge.signedKet, sL2, map_smul, smul_smul]
        cases sB0.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step2 sB0.phase (registerXResetMagnitude gB.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 u2)
        (registerXPhase gB o3 sB0.basis) hsq)
  have h58_sim (o1 o2 : List Bool) (ho1 : o1.length = 774) (ho2 : o2.length = 258) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sMid : ECDSAAdd.State) (u1 u2 : BasisState),
            let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp16 a) true sMid.basis⟩
            AddrValid WideBank8.Fast16.windowBits windowRoot a sMid →
            Clean WideBank8.Fast16.pathBank sMid.basis →
            Clean (pairExtraWires ++ gB) sMid.basis →
            Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sMid) =
              (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step5678Src read (o1 ++ o2)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := fB.load_sim read fB_geo
    obtain ⟨c2, a2, m2⟩ := h68_sim o1 o2 ho1 ho2
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step5678Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨mB, hmB, hb₂⟩ := hb₂
    refine ⟨mB, hmB, ?_⟩
    intro a sMid u1 u2 sL2 ha hpath hclB hclOut hu1 hu2
    have hclB' : Clean (portTargets fB.ports ++ fB.g1) sMid.basis := by
      change Clean (portTargets pp16 ++ gB) sMid.basis
      rw [pp16_targets]; exact hclB
    have hst := fB.load_state read fB_geo a sMid ⟨hpath, ha.1, ha.2⟩ hclB'
    set sB0 := ECDSAAdd.run fB.swapNet List.nil
      (ECDSAAdd.run ((specialize fB.selCode (tableAddressValue fB.selBits sMid.basis)).instantiate read) List.nil sMid) with hsB0
    have hsL2_eq : (⟨sB0.phase, clearRegister gB sB0.basis⟩ : ECDSAAdd.State) = sL2 := by
      refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
      have h2 := hst.2.2.2; change clearRegister gB sB0.basis = tableXorState (portMask read pp16 a) (sMid.basis windowRoot) sMid.basis at h2
      rw [ha.2] at h2; exact h2
    have hfrB : ∀ w, w ∉ pairExtraWires → w ∉ gB → sL2.basis w = sMid.basis w := fun w h1 h2 => by
      dsimp only [sL2]; exact tableXorState_outside _ _ _ _ (fun hm => h1 (by rw [← pp16_targets]; exact tableBitsMask_subset _ _ hm))
    have haL2 : AddrValid WideBank8.Fast16.windowBits windowRoot a sL2 := by
      refine ⟨?_, ?_⟩
      · rw [← ha.1]; apply WEX.tableAddressValue_congr; intro w hw
        exact hfrB w (hbits_no_pe w hw) (fun hm => by
          rw [mem_gB] at hm
          simp only [WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            List.mem_range'_1] at hw
          dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      · rw [hfrB windowRoot hroot_no_pe (fun hm => by rw [mem_gB] at hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega)]; exact ha.2
    have hpathL2 : Clean WideBank8.Fast16.pathBank sL2.basis := fun w hw => by
      have h1 : w ∉ pairExtraWires := fun hm => by
        have := mem_pairExtra hm
        simp only [WideBank8.Fast16.pathBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_range'_1] at hw
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have h2 : w ∉ gB := fun hm => by
        rw [mem_gB] at hm
        simp only [WideBank8.Fast16.pathBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_range'_1] at hw
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      rw [hfrB w h1 h2]; exact hpath w hw
    have hu3 : ∀ q ∈ d3, sB0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
      have h1 := hst.2.2.1 q hq
      change sB0.basis q.target = (sMid.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
      rw [ha.2, Bool.true_and] at h1; exact h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet sMid)) = _
    rw [hb₁ a sMid ⟨hpath, ha.1, ha.2⟩ hclB', map_smul]
    have hstep := hb₂ a sB0 u1 u2 (by rw [hsL2_eq]; exact haL2) (by rw [hsL2_eq]; exact hpathL2)
      (by rw [hsL2_eq]; exact hclOut) hu1 hu2 hu3
    rw [hsL2_eq] at hstep
    rw [hstep, smul_smul]
    exact congrArg (· • _) (by simp only [mul_assoc])
  have h48_sim (o1 : List Bool) (ho1 : o1.length = 774) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ mB : List Bool, mB.length = mTail ∧
          ∀ a (sA1 : ECDSAAdd.State) (u1 : BasisState),
            let sMid : ECDSAAdd.State := ⟨sA1.phase, clearRegister shortWires sA1.basis⟩
            let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp16 a) true sMid.basis⟩
            AddrValid WideBank8.Fast16.windowBits windowRoot a sMid →
            Clean WideBank8.Fast16.pathBank sMid.basis →
            Clean (pairExtraWires ++ gB) sMid.basis →
            Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, sA1.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sA1) =
              (c * registerXPhase garbA o1 u1) •
                Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                  tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
        (step4_8Src read o1).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step4_8Src
    apply MeasuredClear.measureResetThen_sim shortWires _
      (fun o2 b c => ∃ mB : List Bool, mB.length = mTail ∧
        ∀ a (sMid : ECDSAAdd.State) (u1 u2 : BasisState),
          let sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp16 a) true sMid.basis⟩
          AddrValid WideBank8.Fast16.windowBits windowRoot a sMid →
          Clean WideBank8.Fast16.pathBank sMid.basis →
          Clean (pairExtraWires ++ gB) sMid.basis →
          Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sMid) =
            (c * registerXPhase garbA o1 u1 * registerXPhase shortWires o2 u2) •
              Bridge.signedKet ⟨(ECDSAAdd.run tailPart mB sL2).phase,
                tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩)
    · intro o2 ho2
      exact h58_sim o1 o2 ho1 (by rw [shortWires_length] at ho2; exact ho2)
    · intro o2 ho2 b c hb
      obtain ⟨mB, hmB, hb⟩ := hb
      refine ⟨mB, hmB, ?_⟩
      intro a sA1 u1 sMid sL2 ha hpath hclB hclOut hu1 hu2
      have hk := xResetRegisterKraus_ket shortWires o2 sA1.basis ho2 scrShortWires_nd
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho2] at hk
      have hsq := MeasuredClear.registerXPhase_square shortWires o2 sA1.basis
      change b.kraus (xResetRegisterKraus shortWires o2 (Bridge.signedKet sA1)) = _
      have hstep := hb a sMid u1 sA1.basis ha hpath hclB hclOut hu1 hu2
      rw [show Bridge.signedKet sA1 = (if sA1.phase then (-1 : ℂ) else 1) • ket sA1.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister shortWires sA1.basis)) =
          (if sA1.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet sMid) := by
        simp only [Bridge.signedKet, sMid, map_smul, smul_smul]
        cases sA1.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step1 sA1.phase (registerXResetMagnitude shortWires.length) c
        (registerXPhase garbA o1 u1) (registerXPhase shortWires o2 sA1.basis) hsq)
  have h38_sim (o1 : List Bool) (ho1 : o1.length = 774) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
          ∀ a (st : ECDSAAdd.State) (u1 : BasisState),
            let sL1 : ECDSAAdd.State := ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩
            AddrValid WideBank8.Fast16.windowBits windowRoot a st →
            Clean WideBank8.Fast16.pathBank st.basis →
            Clean streamLayout.dialogPool st.basis →
            (∀ m', Clean scrAllWires
              (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sL1) =
              (c * registerXPhase garbA o1 u1) •
                Bridge.signedKet (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m st))
        (step3_8Src read o1).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation shortNorm
    obtain ⟨c2, a2, m2⟩ := h48_sim o1 ho1
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step3_8Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨mB, hmB, hb₂⟩ := hb₂
    let mA := b₁.history
    have hmA : mA.length = mShort := by rw [hb₁.1, shortNorm_meas]
    let mPerm := mB.take (ECDSAAdd.measurementCount pairPart) ++ mA ++ mB.drop (ECDSAAdd.measurementCount pairPart)
    have hmc_len : mPerm.length = ECDSAAdd.measurementCount site1Arith := by
      have htail_mc : ECDSAAdd.measurementCount pairPart ≤ mTail := by
        rw [mTail, tailPart, ECDSAAdd.measurementCount_append]
        exact Nat.le_add_right _ _
      have hcs : mShort + mTail = ECDSAAdd.measurementCount site1Arith := by
        rw [mShort, mTail]; exact site1_counts_split.2.1
      dsimp only [mPerm]
      rw [List.length_append, List.length_append, List.length_take, List.length_drop, hmA, hmB]
      exact mPerm_len_arith mShort mTail (ECDSAAdd.measurementCount pairPart) (ECDSAAdd.measurementCount site1Arith) htail_mc hcs
    refine ⟨mPerm, hmc_len, ?_⟩
    intro a st u1 sL1 ha hpath hpool hsafe hu1
    have hclean258 : Clean (streamLayout.dialogPool.take 258) st.basis := fun w hw => hpool w (List.mem_of_mem_take hw)
    have hclean258_L1 : Clean (streamLayout.dialogPool.take 258) sL1.basis := fun w hw => by
      dsimp only [sL1]
      rw [tableXorState_outside _ _ _ _ (fun hm => by
        have h1 : w ∈ shortWires := by simpa [sp16_targets] using tableBitsMask_subset _ _ hm
        have h2 := shortWires_bounds w h1
        rw [mem_pool_take 258 (by decide)] at hw; dsimp only [Wire, ECDSAAdd.Wire] at hw h2; omega)]
      exact hclean258 w hw
    have hnorm : ECDSAAdd.run shortNorm mA sL1 = ECDSAAdd.run shortPart mA sL1 := by
      rw [shortNorm]; exact ECDSAAdd.Baselines.normalize_run shortPart mA sL1
    have hsA1_form := shortPart_run sL1 mA hclean258_L1
    generalize hsA1 : ECDSAAdd.run shortPart mA sL1 = sA1 at hnorm hsA1_form
    have htwo := site1_twoPass_run_free read r16 a st sA1 mA mB
      (by rw [← mShort]; exact hmA) (by rw [← mTail]; exact hmB) ha.2 hclean258 hsA1.symm
    have hne_eq (w : Wire) (hne : w ≠ streamLayout.core.equalNegY) : sA1.basis w = sL1.basis w := by
      rw [hsA1_form]; simp [ECDSAAdd.writeBit, Function.update, hne]
    have hsp_nd : (portTargets sp16).Nodup := by rw [sp16_targets]; exact scrShortWires_nd
    have hsA1_loaded : ∀ q ∈ d2, sA1.basis q.target = decide (read (q.ref a) = q.value) :=
      clearData_loaded_of_xor read sp16 a st.basis sA1.basis hsp_nd
        (fun w hw => by rw [sp16_targets] at hw; exact hpool w (pool_band_in_dialogPool (mem_short_garbA (List.mem_append_left _ hw))))
        (fun w hw => by
          rw [sp16_targets] at hw
          exact hne_eq w (fun e => scrShortWires_no_flags.2.2.2 (e ▸ hw)))
    have hmid_basis : clearRegister shortWires sA1.basis =
        tableXorState (portMask read sp16 a) true sA1.basis := by
      rw [← sp16_targets]
      exact clearRegister_eq_xor_of_loaded read sp16 a sA1.basis hsp_nd hsA1_loaded
    set sMid : ECDSAAdd.State := ⟨sA1.phase, clearRegister shortWires sA1.basis⟩
    set sL2 : ECDSAAdd.State := ⟨sMid.phase, tableXorState (portMask read pp16 a) true sMid.basis⟩
    have hmid_frame (w : Wire) (hw1 : w ∉ shortWires) (hw2 : w ≠ streamLayout.core.equalNegY) :
        sMid.basis w = st.basis w := by
      dsimp only [sMid]
      rw [MeasuredClear.clearRegister_frame shortWires sA1.basis w hw1, hne_eq w hw2]
      dsimp only [sL1]
      exact tableXorState_outside _ _ _ _ (fun hm => hw1 (by simpa [sp16_targets] using tableBitsMask_subset _ _ hm))
    have haMid : AddrValid WideBank8.Fast16.windowBits windowRoot a sMid := by
      refine ⟨?_, ?_⟩
      · rw [← ha.1]; apply WEX.tableAddressValue_congr; intro w hw
        exact hmid_frame w
          (fun hm => by
            have h1 := shortWires_bounds w hm
            simp only [WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
              List.mem_range'_1] at hw
            dsimp only [Wire, ECDSAAdd.Wire] at hw h1; omega)
          (fun e => by
            rw [e, sl_equalNegY] at hw
            simp only [WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
              List.mem_range'_1] at hw
            dsimp only [Wire, ECDSAAdd.Wire] at hw; omega)
      · rw [hmid_frame windowRoot windowRoot_not_short (by rw [sl_equalNegY]; decide)]; exact ha.2
    have hpathMid : Clean WideBank8.Fast16.pathBank sMid.basis := fun w hw => by
      rw [hmid_frame w
        (fun hm => by
          have h1 := shortWires_bounds w hm
          simp only [WideBank8.Fast16.pathBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            List.mem_range'_1] at hw
          dsimp only [Wire, ECDSAAdd.Wire] at hw h1; omega)
        (fun e => by
          rw [e, sl_equalNegY] at hw
          simp only [WideBank8.Fast16.pathBank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            List.mem_range'_1] at hw
          dsimp only [Wire, ECDSAAdd.Wire] at hw; omega)]
      exact hpath w hw
    have hclMid : Clean (pairExtraWires ++ gB) sMid.basis := fun w hw => by
      by_cases hs : w ∈ shortWires
      · exact clearRegister_clean shortWires sA1.basis w hs
      · rw [hmid_frame w hs (fun e => by have h1 := mem_pairExtra_gB hw; rw [e, sl_equalNegY] at h1; dsimp only [Wire, ECDSAAdd.Wire] at h1; omega)]
        exact hpool w (pool_band_in_dialogPool (mem_pairExtra_gB hw))
    have hsOut_eq : (⟨(ECDSAAdd.run tailPart mB sL2).phase,
        tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run ((specialize site1_16.code a).instantiate read) mPerm st :=
      (twoPass_state_congr read sp16 pp16 a sA1 mB shortWires hmid_basis).trans htwo
    have hclOut : Clean pairExtraWires (tableXorState (portMask read pp16 a) true (ECDSAAdd.run tailPart mB sL2).basis) := by
      intro w hw
      have h1 := hsafe mPerm w (by
        rcases List.mem_append.mp hw with h | h
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_right _ h)
      have h2 := congrArg (fun x => x.basis w) hsOut_eq
      exact h2.trans h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet sL1)) = _
    rw [hb₁.2, hnorm, map_smul, hb₂ a sA1 u1 haMid hpathMid hclMid hclOut hu1 hsA1_loaded, smul_smul, hsOut_eq]
    exact congrArg (· • _) (by simp only [mul_assoc])
  have h28_sim :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
          ∀ a (st sA0 : ECDSAAdd.State),
            (⟨sA0.phase, clearRegister garbA sA0.basis⟩ : ECDSAAdd.State) =
              ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩ →
            AddrValid WideBank8.Fast16.windowBits windowRoot a st →
            Clean WideBank8.Fast16.pathBank st.basis →
            Clean streamLayout.dialogPool st.basis →
            (∀ m', Clean scrAllWires
              (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis) →
            (∀ q ∈ d1, sA0.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sA0) =
              c • Bridge.signedKet (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m st))
        (step2_8Src read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step2_8Src
    apply MeasuredClear.measureResetThen_sim garbA _
      (fun o1 b c => ∃ m : List Bool, m.length = ECDSAAdd.measurementCount site1Arith ∧
        ∀ a (st : ECDSAAdd.State) (u1 : BasisState),
          let sL1 : ECDSAAdd.State := ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩
          AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          Clean WideBank8.Fast16.pathBank st.basis →
          Clean streamLayout.dialogPool st.basis →
          (∀ m', Clean scrAllWires
            (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sL1) =
            (c * registerXPhase garbA o1 u1) •
              Bridge.signedKet (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m st))
    · intro o1 ho1
      exact h38_sim o1 (by rw [garbA_len] at ho1; exact ho1)
    · intro o1 ho1 b c hb
      obtain ⟨m, hm, hb⟩ := hb
      refine ⟨m, hm, ?_⟩
      intro a st sA0 hsL1 ha hpath hpool hsafe hu1
      have hk := xResetRegisterKraus_ket garbA o1 sA0.basis ho1 garbA_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho1] at hk
      have hsq := MeasuredClear.registerXPhase_square garbA o1 sA0.basis
      change b.kraus (xResetRegisterKraus garbA o1 (Bridge.signedKet sA0)) = _
      have hstep := hb a st sA0.basis ha hpath hpool hsafe hu1
      have ⟨hph, hba⟩ := (ECDSAAdd.State.mk.injEq _ _ _ _).mp hsL1
      rw [show Bridge.signedKet sA0 = (if sA0.phase then (-1 : ℂ) else 1) • ket sA0.basis from rfl,
        map_smul, map_smul, hk, map_smul]
      have he : b.kraus (ket (clearRegister garbA sA0.basis)) =
          (if sA0.phase then (-1 : ℂ) else 1) •
            b.kraus (Bridge.signedKet ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩) := by
        rw [hba, hph]
        simp only [Bridge.signedKet, map_smul, smul_smul]
        cases st.phase <;> simp
      rw [he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step0 sA0.phase (registerXResetMagnitude garbA.length) c
        (registerXPhase garbA o1 sA0.basis) hsq)
  obtain ⟨c1, a1, m1⟩ := fA.load_sim read fA_geo
  obtain ⟨c2, a2, m2⟩ := h28_sim
  refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
  rw [twoPassSrc, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a1 a2
  intro b₁ k₁ b₂ k₂ hb₁ hb₂
  obtain ⟨m, hm, hb₂⟩ := hb₂
  refine ⟨m, hm, ?_⟩
  intro a st ha hpath hpool hsafe
  have hclA : Clean (portTargets fA.ports ++ fA.garb) st.basis := fun w hw => by
    rw [fA, sp16_targets] at hw
    exact hpool w (pool_band_in_dialogPool (mem_short_garbA hw))
  have hst := fA.load_state read fA_geo a st ⟨hpath, ha.1, ha.2⟩ hclA
  set sA0 := ECDSAAdd.run fA.swapNet List.nil
    (ECDSAAdd.run ((specialize fA.selCode (tableAddressValue fA.selBits st.basis)).instantiate read) List.nil st) with hsA0
  have hsL1 : (⟨sA0.phase, clearRegister garbA sA0.basis⟩ : ECDSAAdd.State) =
      ⟨st.phase, tableXorState (portMask read sp16 a) true st.basis⟩ := by
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
    have h2 := hst.2.2.2
    change clearRegister garbA sA0.basis = tableXorState (portMask read sp16 a) (st.basis windowRoot) st.basis at h2
    rw [ha.2] at h2; exact h2
  have hu1 : ∀ q ∈ d1, sA0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
    have h1 := hst.2.2.1 q hq
    change sA0.basis q.target = (st.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
    rw [ha.2, Bool.true_and] at h1; exact h1
  change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
  rw [hb₁ a st ⟨hpath, ha.1, ha.2⟩ hclA, map_smul, hb₂ a st sA0 hsL1 ha hpath hpool hsafe hu1, smul_smul]

/-! Splicing `twoPassProg` into `WideBank8.Row16.code = b0 :: b1 :: b2 :: restW`. -/

def b0 : WideBank8.Fast16.FBlock2 65536 := .std (.plain (Rows.code r16 (wLiteral [.X 838])))
def b1 : WideBank8.Fast16.FBlock2 65536 := .std (.plain (Rows.code r16 scrHead))
def b2 : WideBank8.Fast16.FBlock2 65536 := .std (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩))
def restW : WideBank8.Fast16.FCode2 65536 := WideBank8.Row16.code.drop 3

theorem code_split : WideBank8.Row16.code = b0 :: b1 :: b2 :: restW := by
  have h : WideBank8.Row16.code =
      b0 :: b1 :: b2 :: ((WEXFast.fgeneric3 ++ (WEXFast.FBlock2.std (.plain WEX.cornerNeg) :: List.nil)).map WideBank8.Row16.lift ++
        WideBank8.Fast16.FBlock2.pair WideBank8.Row16.corner :: WideBank8.Row16.tailF.map WideBank8.Row16.lift) := by
    unfold WideBank8.Row16.code
    rw [WideBank8.Row16.headF, WEXUnlookup.rowPre3]
    simp [b0, b1, b2, r16, WideBank8.Row16.lift, Rows.block, toBlock2]
  rw [restW, h]; rfl

theorem b2_rec_diff : WideBank8.Fast16.fblockRec b2 = site1Rec + 15098 := by
  have hgeo := WideBank8.Row16.geometry b2 (by rw [code_split]; simp)
  have hlay := WideBank8.geo_lay2 WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok
    (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) hgeo
  have hpre_eq : (site1 probeRows).prefix = [WInstr.lookup (some windowRoot) (sitePorts probeRows), WInstr.literal site1Arith] := rfl
  have hpre : codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
      (normalizeW (Rows.code r16 (site1 probeRows).prefix)) =
      ECDSAAdd.measurementCount site1Arith + 65535 := by
    have hlay1 : LookupLayouts WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
        (normalizeW (Rows.code r16 (site1 probeRows).prefix)) := hlay.1
    have h1 : codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
        (normalizeW (Rows.code r16 (site1 probeRows).prefix)) =
        literalRecords (site1 probeRows).prefix +
        traversals (site1 probeRows).prefix * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) := by
      rw [codeRecords_eq _ _ _ _ hlay1, literalRecords_normalize, traversals_normalize,
        (WideBank8.Counts.lift_metrics r16 _).2.1, (WideBank8.Counts.lift_metrics r16 _).2.2]
    have h2' : literalRecords (site1 probeRows).prefix = ECDSAAdd.measurementCount site1Arith := by
      rw [hpre_eq]; exact litRec_lookup_lit _ _ _
    have h3' : traversals (site1 probeRows).prefix * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) = 65535 := by
      rw [hpre_eq, trav_lookup_lit]; decide
    exact h1.trans (congrArg₂ (· + ·) h2' h3')
  have hcr : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree WideBank8.Fast16.bank15.high 0 1) (site1 probeRows).guard WideBank8.Fast16.bank15.hp) = 255 := by
    change MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree8 windowRoot WideBank8.Fast16.bank15.hp) = 255
    rw [(MeasuredClear.recordUnary_counts _ _ _ tree8_layout 0).1, tree8_nodes]
  have hlen : (Rows.ports r16 (site1 probeRows).ports).length = 771 := by
    have h := congrArg List.length (sitePorts_targets probeRows)
    have hs : scrAllWires.length = 771 := by
      have h1 : scrPairWires.length = 258 := scrPairWires_length
      have h2 : scrShortWires.length = 258 := scrShortWires_length
      have h3 : scrDExtraWires.length = 255 := by rw [scrDExtraWires_explicit]; simp
      simp [scrAllWires, scrWires, h1, h2, h3]
    rw [Rows.ports, List.length_map]
    simpa [site1, portTargets, hs] using h
  have hrec_eq : WideBank8.Fast16.fblockRec b2 =
      WideBank8.blockRecP2 WideBank8.Fast16.bank15 (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) :=
    fblockRec_std _
  have hlhs : WideBank8.Fast16.fblockRec b2 =
      ECDSAAdd.measurementCount site1Arith + 65535 + 771 + (255 + 255) :=
    hrec_eq.trans ((blockRecP2_unit_16 WideBank8.Fast16.bank15 (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)).trans
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) hpre hlen) (congrArg (· + 255) hcr)))
  exact (hlhs.trans (wide_rec_diff_arith (ECDSAAdd.measurementCount site1Arith) mShort mTail fixRec8 mShort_add_mTail fixRec8_eq)).trans
    (congrArg (· + 15098) (show site1RecGen 16383 32767 mShort mTail fixRec8 = site1Rec from rfl))

theorem b2_tp_diff :
    WideBank8.Fast16.fblockTP b2 =
      (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 247)) + 15098 := by
  have hpre_eq : (site1 probeRows).prefix = [WInstr.lookup (some windowRoot) (sitePorts probeRows), WInstr.literal site1Arith] := rfl
  have htp_pre : literalToffolis (normalizeW (Rows.code r16 (site1 probeRows).prefix)) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram site1Arith) := by
    rw [WideBank8.Counts.lift_normal_metrics, hpre_eq]; exact litToff_lookup_lit _ _ _
  have htr_pre : traversals (Rows.code r16 (site1 probeRows).prefix) = 1 := by
    rw [(WideBank8.Counts.lift_metrics r16 _).2.2, hpre_eq]; exact trav_lookup_lit _ _ _
  have htp_eq : WideBank8.Fast16.fblockTP b2 =
      WideBank8.blockTP2 WideBank8.Fast16.bank15 (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) +
      PoolHost.blockExtra (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) :=
    fblockTP_std _
  have hno_extra : PoolHost.blockExtra (Block2.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) = 0 := rfl
  have h1 : literalToffolis (normalizeW (Rows.code r16 (site1 probeRows).prefix)) =
      ECDSAAdd.toffoliCount shortNorm + ECDSAAdd.toffoliCount tailNorm :=
    htp_pre.trans norm_toff_split.symm
  have h2' : traversals (Rows.code r16 (site1 probeRows).prefix) * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) = 1 * (2 ^ 16 - 1) := by
    rw [htr_pre]; rfl
  have h3 : (tableAddressTree WideBank8.Fast16.bank15.high 0 1).internalNodes + 247 = 255 + 247 :=
    congrArg (· + 247) tree8_nodes
  have hlhs : WideBank8.Fast16.fblockTP b2 =
      ECDSAAdd.toffoliCount shortNorm + ECDSAAdd.toffoliCount tailNorm + 1 * (2 ^ 16 - 1) + (255 + 247) :=
    htp_eq.trans ((congrArg (_ + ·) hno_extra).trans ((Nat.add_zero _).trans
      ((blockTP2_unit_16 WideBank8.Fast16.bank15 (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)).trans
        (congrArg₂ (· + ·) (congrArg₂ (· + ·) h1 h2') h3))))
  exact hlhs.trans (wide_tp_diff_arith (ECDSAAdd.toffoliCount shortNorm) (ECDSAAdd.toffoliCount tailNorm))

theorem newRow_rec :
    WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + site1Rec + WideBank8.Fast16.frecs restW = 1727904 := by
  have h := WideBank8.Row16.row_records
  rw [code_split, frecs_cons, frecs_cons, frecs_cons] at h
  have h' : WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 +
      WideBank8.Fast16.fblockRec b2 + WideBank8.Fast16.frecs restW = 1743002 := by
    simpa only [Nat.add_assoc] using h
  exact row_rec_arith _ _ _ _ _ 15098 1743002 h' b2_rec_diff

def rowProg (start : Nat) : Straight 65536 start (start + 1727904) :=
  castFinish (row_cast_arith start _ _ _ _ _ newRow_rec)
    (((WideBank8.Fast16.fblockProg b0 start).append
      (WideBank8.Fast16.fblockProg b1 (start + WideBank8.Fast16.fblockRec b0))).append
      ((twoPassProg (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1)).append
        (WideBank8.Fast16.fprog restW (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + site1Rec))))

def rowSrc (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  ((WideBank8.Fast16.fblockSrc read b0).seq (WideBank8.Fast16.fblockSrc read b1)).seq
    ((twoPassSrc read).seq (WideBank8.Fast16.fsrc read restW))

theorem rowProg_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rowProg start).instantiate read h).run = (rowSrc read).run := by
  rw [rowProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h1 => by
      rw [append_run_fixed _ _ _ _ _ (fun h2 => WideBank8.Fast16.fprog_run read restW _ h2),
        AdaptiveCircuit.run_seq, twoPass_run read _ h1, ← AdaptiveCircuit.run_seq]),
    AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h1 => WideBank8.Fast16.fblockProg_run read b1 _ h1),
    AdaptiveCircuit.run_seq, WideBank8.Fast16.fblockProg_run read b0 _ h]
  simp only [rowSrc, AdaptiveCircuit.run_seq]

local notation "rowTP16" => (WideBank8.Fast16.fcodeTP WideBank8.Row16.code - 15098)

theorem rowTP_eq :
    WideBank8.Fast16.fblockTP b0 + WideBank8.Fast16.fblockTP b1 +
      (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 247)) + WideBank8.Fast16.fcodeTP restW = rowTP16 :=
  rowTP_sub_arith (WideBank8.Fast16.fcodeTP WideBank8.Row16.code) (WideBank8.Fast16.fblockTP b0)
    (WideBank8.Fast16.fblockTP b1) (WideBank8.Fast16.fblockTP b2) (WideBank8.Fast16.fcodeTP restW)
    (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 + ECDSAAdd.toffoliCount tailNorm + (255 + 247))
    15098 ((congrArg WideBank8.Fast16.fcodeTP code_split).trans (fcodeTP_cons3 b0 b1 b2 restW)) b2_tp_diff

theorem rowProg_tCount (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rowProg start).instantiate read h).tCount = 7 * rowTP16 := by
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split]; simp)
  have hgr : ∀ b ∈ restW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (by rw [code_split]; simp [hb])
  rw [rowProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h1 => by
      rw [append_tCount_fixed _ _ _ _ _ (fun h2 => WideBank8.Fast16.fprog_tCount read restW hgr _ h2),
        twoPass_tCount read _ h1]),
    append_tCount_fixed _ _ _ _ _ (fun h1 => WideBank8.Fast16.fblock_tCount read b1 hg1 _ h1),
    WideBank8.Fast16.fblock_tCount read b0 hg0 start h]
  exact tcount_mul7_4 _ _ _ _ _ rowTP_eq

theorem rowProg_residue (start : Nat) : AndGadget.residue (rowProg start) = 0 := by
  have hbr (b : WideBank8.Fast16.FBlock2 65536) (s : Nat) : AndGadget.residue (WideBank8.Fast16.fblockProg b s) = 0 := by
    have h := WideBank8.Fast16.fprog_residue [b] s
    rw [WideBank8.Fast16.fprog, AndGadget.residue_cast, AndGadget.residue_append] at h
    omega
  rw [rowProg, AndGadget.residue_cast, AndGadget.residue_append, AndGadget.residue_append,
    AndGadget.residue_append, hbr, hbr, twoPass_residue, WideBank8.Fast16.fprog_residue]

theorem rowProg_credit (start : Nat) : ProgramCredit (rowProg start) rowTP16 := by
  have hz := rowProg_residue start
  refine ⟨hz, ?_⟩
  have he := exact_t (rowProg start) hz (fun _ => false) (fun _ => false)
  have ht := rowProg_tCount (fun _ => false) start (fun _ => false)
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7) (he.symm.trans ht)

theorem rowProg_wellFormed (start : Nat) : (rowProg start).WellFormed := by
  have hphys : ∀ p, WInstr.literal p ∈ erase2 (WideBank8.Fast16.fforget WideBank8.Row16.code) → GatePhysical p := by
    rw [WideBank8.Row16.forget]; exact Geometry.row_physical .w16
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split]; simp)
  have hgr : ∀ b ∈ restW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (by rw [code_split]; simp [hb])
  have hp_sub (b : WideBank8.Fast16.FBlock2 65536) (hb : b ∈ WideBank8.Row16.code) :
      ∀ p, WInstr.literal p ∈ erase2 b.forgetL → GatePhysical p := fun p hp =>
    hphys p (by
      rw [WideBank8.Fast16.fforget, erase2]
      have h1 : b.forgetL ⊆ WideBank8.Fast16.fforget WideBank8.Row16.code := fun x hx => List.mem_flatMap.mpr ⟨b, hb, hx⟩
      obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
      exact List.mem_flatMap.mpr ⟨d, h1 hd, hdp⟩)
  rw [rowProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _
    (straight_append_wellFormed _ _
      (WideBank8.Fast16.fblock_wellFormed b0 hg0 (hp_sub b0 (by rw [code_split]; simp)) start)
      (WideBank8.Fast16.fblock_wellFormed b1 hg1 (hp_sub b1 (by rw [code_split]; simp)) _))
    (straight_append_wellFormed _ _ (twoPass_wellFormed _)
      (WideBank8.Fast16.fprog_wellFormed restW hgr (fun p hp => by
        obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
        obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
        exact hp_sub b (by rw [code_split]; simp [hb]) p (List.mem_flatMap.mpr ⟨d, hdb, hdp⟩)) _))

theorem rowProg_support (start : Nat) :
    ChallengeMigration.straightWires (rowProg start) ⊆ WideBank8.Fast16.Tight.support := by
  have hsup_orig := WideBank8.Fast16.Tight.row_program_support start
  rw [WideBank8.Row16.program, code_split, WideBank8.Fast16.fprog, support_cast, straightWires_append] at hsup_orig
  have hs0 : ChallengeMigration.straightWires (WideBank8.Fast16.fblockProg b0 start) ⊆ WideBank8.Fast16.Tight.support :=
    (List.append_subset.mp hsup_orig).1
  have htail1 := (List.append_subset.mp hsup_orig).2
  rw [WideBank8.Fast16.fprog, support_cast, straightWires_append] at htail1
  have hs1 : ChallengeMigration.straightWires (WideBank8.Fast16.fblockProg b1 (start + WideBank8.Fast16.fblockRec b0)) ⊆ WideBank8.Fast16.Tight.support :=
    (List.append_subset.mp htail1).1
  have hrest_sup (s : Nat) : ChallengeMigration.straightWires (WideBank8.Fast16.fprog restW s) ⊆ WideBank8.Fast16.Tight.support := by
    have hmem : ∀ b ∈ restW, b ∈ WideBank8.Row16.code := fun b hb => by rw [code_split]; simp [hb]
    have hf_sub : ∀ x ∈ erase2 (WideBank8.Fast16.fforget restW), x ∈ erase2 (WideBank8.Fast16.fforget WideBank8.Row16.code) := fun x hx => by
      obtain ⟨d, hd, hdx⟩ := List.mem_flatMap.mp hx
      obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
      exact List.mem_flatMap.mpr ⟨d, List.mem_flatMap.mpr ⟨b, hmem b hb, hdb⟩, hdx⟩
    exact WideBank8.Fast16.Tight.fprog_support restW (fun b hb => WideBank8.Row16.geometry b (hmem b hb))
      (fun p hp => WideBank8.Fast16.Tight.row_literals p (hf_sub _ hp))
      (fun b hb => WideBank8.Row16.strict b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl3 b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl4 b (hmem b hb))
      (fun c ps hp => WideBank8.Fast16.Tight.row_lookups c ps (hf_sub _ hp))
      (fun b hb => WideBank8.Fast16.Tight.row_nohost b (hmem b hb)) s
  rw [rowProg, support_cast, straightWires_append, straightWires_append, straightWires_append]
  exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨hs0, hs1⟩,
    List.append_subset.mpr ⟨twoPass_support _, hrest_sup _⟩⟩

theorem rowProg_slots (start : Nat) : (rowProg start).gateSlots ≤ 3290000000 := by
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split]; simp)
  have hgr : ∀ b ∈ restW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (by rw [code_split]; simp [hb])
  have hs0 := WideBank8.Fast16.fprog_slots [b0] (fun b hb => by simp at hb; subst hb; exact hg0) start
  rw [WideBank8.Fast16.fprog, castFinish_gateSlots, Straight.gateSlots_append] at hs0
  simp only [WideBank8.Fast16.fprog, Straight.gateSlots, WideBank8.Fast16.fforget, WideBank8.Fast16.fslack,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero] at hs0
  have hs1 := WideBank8.Fast16.fprog_slots [b1] (fun b hb => by simp at hb; subst hb; exact hg1)
    (start + WideBank8.Fast16.fblockRec b0)
  rw [WideBank8.Fast16.fprog, castFinish_gateSlots, Straight.gateSlots_append] at hs1
  simp only [WideBank8.Fast16.fprog, Straight.gateSlots, WideBank8.Fast16.fforget, WideBank8.Fast16.fslack,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero] at hs1
  have hsr := WideBank8.Fast16.fprog_slots restW hgr
    (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + site1Rec)
  have htp := twoPass_slots (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1)
  have hsp_split :
      WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget WideBank8.Row16.code) =
        WideBank8.codeSP2 WideBank8.Fast16.bank15 b0.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 b1.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 b2.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget restW) := by
    rw [code_split]
    simp only [WideBank8.Fast16.fforget_cons, WideBank8.Fast16.codeSP2_append, Nat.add_assoc]
  have hsl_split :
      WideBank8.Fast16.fslack WideBank8.Row16.code =
        WideBank8.Fast16.fblockSlack b0 + WideBank8.Fast16.fblockSlack b1 +
        WideBank8.Fast16.fblockSlack b2 + WideBank8.Fast16.fslack restW := by
    rw [code_split]; simp only [WideBank8.Fast16.fslack, Nat.add_assoc]
  have hsp_all := WideBank8.Row16.standard_slots
  rw [← WideBank8.Row16.forget] at hsp_all
  have hsl_all := WideBank8.Row16.slack
  have hlit_le := site1_slots_le_rowC
  have hl0 := WEX.clearReferenceRow_literal_slots_bound
  have hm := WEXUnlookup.rowC_measures.2.2.1
  rw [rowProg, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append, Straight.gateSlots_append]
  generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Baselines.normalizeProgram site1Arith) = gS at htp hlit_le
  generalize literalSlotSum (erase2 WEXUnlookup.rowC) = L1 at hlit_le hm
  generalize literalSlotSum (WEX.clearReferenceRow probeRows) = L0 at hl0 hm
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget WideBank8.Row16.code) = spAll at hsp_split hsp_all
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 b0.forgetL = sp0 at hs0 hsp_split
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 b1.forgetL = sp1 at hs1 hsp_split
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 b2.forgetL = sp2 at hsp_split
  generalize WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget restW) = spR at hsr hsp_split
  generalize WideBank8.Fast16.fslack WideBank8.Row16.code = slAll at hsl_split hsl_all
  generalize WideBank8.Fast16.fblockSlack b0 = sl0 at hs0 hsl_split
  generalize WideBank8.Fast16.fblockSlack b1 = sl1 at hs1 hsl_split
  generalize WideBank8.Fast16.fblockSlack b2 = sl2 at hsl_split
  generalize WideBank8.Fast16.fslack restW = slR at hsr hsl_split
  omega

theorem rowSrc_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (rowSrc (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  let read := readConstant coeffs Q
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split]; simp)
  have hgr : ∀ b ∈ restW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (by rw [code_split]; simp [hb])
  obtain ⟨c0, a0, m0⟩ := WideBank8.Fast16.fblock_sim read b0 hg0
  obtain ⟨c1, a1, m1⟩ := WideBank8.Fast16.fblock_sim read b1 hg1
  obtain ⟨c2, a2, m2⟩ := twoPass_sim read
  obtain ⟨cr, ar, mr⟩ := WideBank8.Fast16.fsrc_sim read restW hgr
  have h01_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (b0.forgetL ++ b1.forgetL)) ∧
        ∀ a st, AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          WideBank8.Fast16.FBlockClean b0 st →
          (∀ m', m'.length = ECDSAAdd.measurementCount (reference2 read a b0.forgetL) →
            WideBank8.Fast16.FBlockClean b1 (ECDSAAdd.run (reference2 read a b0.forgetL) m' st)) →
          Safe2 read a (b0.forgetL ++ b1.forgetL) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (b0.forgetL ++ b1.forgetL)) m st))
      ((WideBank8.Fast16.fblockSrc read b0).seq (WideBank8.Fast16.fblockSrc read b1)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c0 c1, ?_, by rw [simulationCoefficients_mass, m0, m1]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a0 a1
    intro b₀ k₀ b₁ k₁ hb₀ hb₁
    obtain ⟨m₀, lm₀, r₀⟩ := hb₀
    obtain ⟨m₁, lm₁, r₁⟩ := hb₁
    refine ⟨m₀ ++ m₁, by simp [erase2_append, List.length_append, lm₀, lm₁], ?_⟩
    intro a st ha hc0 hc1 hsafe
    have hm₀ : m₀.length = ECDSAAdd.measurementCount (reference2 read a b0.forgetL) :=
      lm₀.trans (specialize_counts read (erase2 b0.forgetL) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a b0.forgetL b1.forgetL st hsafe
    have ha1 := WideBank8.Fast16.fblock_addr read b0 hg0 a st ha hc0 m₀
    change b₁.kraus (b₀.kraus (Bridge.signedKet st)) = _
    rw [r₀ a st ha hc0 hsp.1, map_smul,
      r₁ a _ ha1 (hc1 m₀ hm₀) (hsp.2 m₀ hm₀), reference2_append, run_append_records _ _ m₀ m₁ st hm₀, smul_smul]
  have h2r_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (b2.forgetL ++ WideBank8.Fast16.fforget restW)) ∧
        ∀ a st, AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          WideBank8.Fast16.FCodeClean read a (b2 :: restW) st →
          Clean streamLayout.dialogPool st.basis →
          Safe2 read a (b2.forgetL ++ WideBank8.Fast16.fforget restW) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (b2.forgetL ++ WideBank8.Fast16.fforget restW)) m st))
      ((twoPassSrc read).seq (WideBank8.Fast16.fsrc read restW)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c2 cr, ?_, by rw [simulationCoefficients_mass, m2, mr]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a2 ar
    intro b₂ k₂ br kr hb₂ hbr
    obtain ⟨m₂, lm₂, r₂⟩ := hb₂
    obtain ⟨mr', lmr', rr⟩ := hbr
    have h2_lit : literalRecords (erase2 b2.forgetL) = ECDSAAdd.measurementCount site1Arith := by
      have heq : erase2 b2.forgetL =
          [WInstr.lookup (some windowRoot) (Rows.ports r16 (sitePorts probeRows)), WInstr.literal site1Arith,
           WInstr.lookup (some windowRoot) (Rows.ports r16 (sitePorts probeRows))] := by
        simp [b2, WideBank8.Fast16.FBlock2.forgetL, erase2, Block2.code, UnitSite.code, Rows.unit, Rows.site,
          Rows.code, Rows.instr, site1, MaskedSite.prefix, wLiteral]
      rw [heq]; exact litRec_lookup_lit_lookup _ _ _ _ _
    have h2_ref (a : Nat) : reference2 read a b2.forgetL = (specialize site1_16.code a).instantiate read := by
      have hce : erase2 b2.forgetL = site1_16.code := by
        simp [b2, WideBank8.Fast16.FBlock2.forgetL, erase2, Block2.code, UnitSite.code, Rows.unit,
          site1_16, Rows.site, MaskedSite.code, MaskedSite.prefix, Rows.code, Rows.instr]
      rw [reference2, hce]
    refine ⟨m₂ ++ mr', by simp [erase2_append, List.length_append, h2_lit, lm₂, lmr'], ?_⟩
    intro a st ha hcl hpool hsafe
    have hm₂ : m₂.length = ECDSAAdd.measurementCount (reference2 read a b2.forgetL) := by
      rw [← h2_lit] at lm₂; exact lm₂.trans (specialize_counts read (erase2 b2.forgetL) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a b2.forgetL (WideBank8.Fast16.fforget restW) st hsafe
    have ha2 := WideBank8.Fast16.fblock_addr read b2 (WideBank8.Row16.geometry b2 (by rw [code_split]; simp)) a st ha hcl.1 m₂
    have hpath2 : Clean WideBank8.Fast16.pathBank st.basis := hcl.1.1
    have hsafe2 : ∀ m', Clean scrAllWires (ECDSAAdd.run ((specialize site1_16.code a).instantiate read) m' st).basis := by
      have hs1 : BlockSafe2 read a (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) st := hsp.1.1
      have hcode_eq : (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩).code = site1_16.code := by
        simp [Rows.unit, UnitSite.code, site1_16, Rows.site, MaskedSite.code, MaskedSite.prefix, Rows.code, Rows.instr]
      have hpr : portTargets (Rows.site r16 (site1 probeRows)).ports = scrAllWires := by
        rw [Rows.site, Rows.targets]; exact sitePorts_targets probeRows
      intro m'
      have hm' := hs1 m'
      rw [hcode_eq] at hm'
      simpa [Rows.unit, hpr] using hm'
    change br.kraus (b₂.kraus (Bridge.signedKet st)) = _
    rw [r₂ a st ha hpath2 hpool hsafe2, ← h2_ref a, map_smul,
      rr a _ ha2 (hcl.2 m₂ hm₂) (hsp.2 m₂ hm₂), reference2_append, run_append_records _ _ m₂ mr' st hm₂, smul_smul]
  obtain ⟨c01, a01, m01⟩ := h01_sim
  obtain ⟨c2r, a2r, m2r⟩ := h2r_sim
  refine ⟨coherentSeqCoefficients c01 c2r, ?_, by rw [simulationCoefficients_mass, m01, m2r]; norm_num⟩
  rw [rowSrc, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a01 a2r
  intro b₁ k₁ b₂ k₂ hb₁ hb₂ s hs
  obtain ⟨m₁, lm₁, r₁⟩ := hb₁
  obtain ⟨m₂, lm₂, r₂⟩ := hb₂
  let a := tableAddressValue WideBank8.Fast16.windowBits s
  have hsafe_all : Safe2 read a (WideBank8.Fast16.fforget WideBank8.Row16.code) ⟨false, s⟩ := by
    rw [WideBank8.Row16.forget]; exact Rows.row_safe _ _ _ hQ hn a s hs
  have hclean_all : WideBank8.Fast16.FCodeClean read a WideBank8.Row16.code ⟨false, s⟩ :=
    WideBank8.Row16.clean_fused _ _ _ (WideBank8.Row16.clean_lift coeffs Q _ _ _
      (WEXFast.rowCF_clean (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs)
      (PoolHost.poolBand_clean_in_rowCF (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs)
      (by rw [WEXFast.fforget_rowCF]; exact PoolHost.rowC_host4 (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs))
  rw [code_split] at hsafe_all hclean_all
  simp only [WideBank8.Fast16.fforget_cons, List.append_assoc] at hsafe_all
  have hsafe_split := WideBank8.Fast16.safe2_append_inv read a (b0.forgetL ++ b1.forgetL)
    (b2.forgetL ++ WideBank8.Fast16.fforget restW) ⟨false, s⟩ (by simpa [List.append_assoc] using hsafe_all)
  have hm₁ : m₁.length = ECDSAAdd.measurementCount (reference2 read a (b0.forgetL ++ b1.forgetL)) :=
    lm₁.trans (specialize_counts read (erase2 (b0.forgetL ++ b1.forgetL)) a).2.symm
  have h0_m : ECDSAAdd.measurementCount (reference2 read a b0.forgetL) = 0 := by
    have hr : reference2 read a b0.forgetL = [.X 838] := by
      simp [b0, WideBank8.Fast16.FBlock2.forgetL, reference2, erase2, Block2.code, Rows.code, Rows.instr,
        wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_lit]
    rw [hr]; exact x838_meas_zero
  have h1_m : ECDSAAdd.measurementCount (reference2 read a b1.forgetL) = 0 := by
    have hr : reference2 read a b1.forgetL = scrHeadProgram := by
      simp [b1, WideBank8.Fast16.FBlock2.forgetL, reference2, erase2, Block2.code, Rows.code, Rows.instr,
        scrHead, scrHeadProgram, wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_append, Tmpl.instantiate_lit]
    rw [hr]; exact scrHeadProgram_meas_zero
  have hm₁_0 : m₁ = List.nil := List.eq_nil_of_length_eq_zero (by
    rw [hm₁, reference2_append, ECDSAAdd.measurementCount_append, h0_m, h1_m])
  have ha0 : AddrValid WideBank8.Fast16.windowBits windowRoot a ⟨false, s⟩ := ⟨rfl, hs.2.2⟩
  have hcl0 : WideBank8.Fast16.FBlockClean b0 ⟨false, s⟩ := hclean_all.1
  have hcl1 : ∀ m', m'.length = ECDSAAdd.measurementCount (reference2 read a b0.forgetL) →
      WideBank8.Fast16.FBlockClean b1 (ECDSAAdd.run (reference2 read a b0.forgetL) m' ⟨false, s⟩) :=
    fun m' hm' => (hclean_all.2 m' hm').1
  have hstep01 := r₁ a ⟨false, s⟩ ha0 hcl0 hcl1 hsafe_split.1
  set st12 := ECDSAAdd.run (reference2 read a (b0.forgetL ++ b1.forgetL)) m₁ ⟨false, s⟩ with hst12
  have hst12_eq : st12 = ECDSAAdd.run (reference2 read a b1.forgetL) List.nil
      (ECDSAAdd.run (reference2 read a b0.forgetL) List.nil ⟨false, s⟩) := by
    rw [hst12, hm₁_0, reference2_append, ECDSAAdd.run_append, h0_m]; rfl
  have hpool12 : Clean streamLayout.dialogPool st12.basis := by
    rw [hst12_eq]
    exact liveReady_pool_after_b01 read r16 a s hs List.nil List.nil
  have ha12 : AddrValid WideBank8.Fast16.windowBits windowRoot a st12 := by
    rw [hst12_eq]
    have ha1' := WideBank8.Fast16.fblock_addr read b0 hg0 a ⟨false, s⟩ ha0 hcl0 List.nil
    exact WideBank8.Fast16.fblock_addr read b1 hg1 a _ ha1' (hcl1 List.nil (by simp [h0_m])) List.nil
  have hcl2r : WideBank8.Fast16.FCodeClean read a (b2 :: restW) st12 := by
    rw [hst12_eq]
    exact (hclean_all.2 List.nil (by simp [h0_m])).2 List.nil (by simp [h1_m])
  have hstep2r := r₂ a st12 ha12 hcl2r hpool12 (hsafe_split.2 m₁ hm₁)
  change b₂.kraus (b₁.kraus (ket s)) = _
  rw [← Bridge.signedKet_false s, hstep01, map_smul, hstep2r, smul_smul]
  have hcomb : ECDSAAdd.run (reference2 read a (b2.forgetL ++ WideBank8.Fast16.fforget restW)) m₂ st12 =
      ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget WideBank8.Row16.code)) (m₁ ++ m₂) ⟨false, s⟩ := by
    rw [hst12, ← run_append_records _ _ m₁ m₂ ⟨false, s⟩ hm₁, ← reference2_append, code_split]
    simp [WideBank8.Fast16.fforget_cons, List.append_assoc]
  have hrun : ECDSAAdd.run (reference2 read a (Geometry.row Geometry.Width.w16)) (m₁ ++ m₂) ⟨false, s⟩ =
      ⟨false, Add.update Geometry.Width.w16 coeffs Q s⟩ :=
    Rows.row_run r16 coeffs Q hQ hn a s hs (m₁ ++ m₂)
  rw [hcomb, WideBank8.Row16.forget, hrun, Bridge.signedKet_false, Bridge.signedKet_false]
  simp [ket]

attribute [local irreducible] rowProg WideSigned.Frame16.program

local notation "signedCredit16" => (2 * Body.signCredit + rowTP16)

def program (start : Nat) : Straight 65536 start (start + 1728416) :=
  castFinish (congrArg (fun m => start + m) (by decide : 512 + 1727904 = 1728416))
    (Frame16.program 1727904 rowProg start)

attribute [local irreducible] program

def source (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (Body.prefixSource .w16).seq ((Body.signSource.seq ((rowSrc (readConstant coeffs Q)).seq Body.signSource)).seq
    (Body.suffixSource .w16))

theorem source_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (source coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  have hs : CoherentlyImplementsOn Body.signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady :=
    fastWindowSign_coherent
  have ha := composeCoherent hs (rowSrc_coherent coeffs Q hQ hn) (fun s h => liveReady_write _ s h)
  have hb := composeCoherent ha hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  have hc := composeCoherent (Body.prefix_coherent .w16) hb
    (fun s h => Body.prepare_live .w16 _ (rootFlip_live s h))
  have hd := composeCoherent hc (Body.suffix_coherent .w16) (fun _ _ => trivial)
  simpa only [source, Body.state, adaptive_seq_assoc] using hd

theorem run (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).run = (source coeffs Q).run := by
  rw [program, castFinish_instantiate]
  have hr (j : Nat) (hist : Fin j → Bool) :
      ((rowProg j).instantiate (readConstant coeffs Q) hist).run = (rowSrc (readConstant coeffs Q)).run :=
    rowProg_run _ j hist
  simpa only [source] using Frame16.run 1727904 rowProg (rowSrc (readConstant coeffs Q))
    (readConstant coeffs Q) hr start history

theorem coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  unfold CoherentlyImplementsOn
  rw [run]
  exact source_coherent coeffs Q hQ hn

def window : Single.Window 65536 := ⟨(Body.logicalBank .w16).reverse, 1728416, program⟩

def model (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
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

theorem program_credit (start : Nat) : ProgramCredit (program start) signedCredit16 := by
  rw [program]
  apply credit_cast
  exact Frame16.credit _ _ rowProg rowProg_credit start

theorem wellFormed (start : Nat) : (program start).WellFormed := by
  rw [program, castFinish_wellFormed]
  exact Frame16.wellFormed _ rowProg rowProg_wellFormed start

theorem credit_bound : signedCredit16 ≤ 2327593 := by
  have h1 : WideBank8.Fast16.fcodeTP WideBank8.Row16.code =
      WideBank8.Fast16.fblockTP b0 + WideBank8.Fast16.fblockTP b1 +
      WideBank8.Fast16.fblockTP b2 + WideBank8.Fast16.fcodeTP restW :=
    (congrArg WideBank8.Fast16.fcodeTP code_split).trans (fcodeTP_cons3 b0 b1 b2 restW)
  have h2 := b2_tp_diff
  have hold := WideBank8.Signed16.credit_bound
  generalize WideBank8.Fast16.fcodeTP WideBank8.Row16.code = T at h1 hold ⊢
  generalize WideBank8.Fast16.fblockTP b2 = T2 at h1 h2
  generalize ECDSAAdd.toffoliCount shortNorm = tS at h2
  generalize ECDSAAdd.toffoliCount tailNorm = tT at h2
  generalize Body.signCredit = tSign at hold ⊢
  omega

theorem signed_support (start : Nat) :
    ChallengeMigration.straightWires (program start) ⊆ WideBank8.Fast16.Tight.support := by
  rw [program, straightWires_castFinish]
  exact TightSupport.frame_support17_7 _ rowProg rowProg_support start

theorem packed_support (start : Nat) :
    ChallengeMigration.straightWires (relabelStraight TightSupport.compact17_7 (program start)) ⊆ List.range 1613 := by
  rw [straightWires_relabel]
  intro v hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (TightSupport.compact17_7_bound u (signed_support start hu))

theorem pointRule (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hactive : root 836 = true) (hz : Clean (Body.logicalBank .w16) root) :
    Single.Distribution.PointRule root (model coeffs Q hQ hn) := by
  intro prior output P
  simpa only [Single.Distribution.WindowModel.step, model, window, List.reverse_reverse,
    List.length_reverse, LinearMap.comp_apply] using
    Body.point_sum .w16 coeffs Q hQ hn root hactive hz prior output P

theorem prepared (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hs : windowReady root) (hz : Clean (Body.logicalBank .w16) root)
    (ψ : State) (hψ : SupportedOn (Single.Distribution.pointFamily root) ψ) :
    SupportedOn (model coeffs Q hQ hn).valid
      (Quantum.run ((model coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ) := by
  change SupportedOn (Body.model .w16 coeffs Q hQ hn).valid
    (Quantum.run ((Body.model .w16 coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ)
  exact Body.prepared .w16 coeffs Q hQ hn root hs hz ψ hψ

theorem slots (start : Nat) : (program start).gateSlots ≤ 3300000000 := by
  have hrow := rowProg_slots (start + 256)
  have hsign (j : Nat) : (Body.nProgram .w16 j).gateSlots ≤ 300000 := by
    rw [Body.nProgram, reindexStraight_gateSlots, nFastProgram_slots]
    have h := literal_slot_bound (n := 32768)
      (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
    rw [ECDSAAdd.Baselines.normalize_slots] at h
    have hmax := fastWindowSign_slots
    generalize ECDSAAdd.Challenge.gateSlots fastWindowSignProgram = G at h hmax
    generalize Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) = S at h ⊢
    omega
  rw [program, castFinish_gateSlots, Frame16.slots]
  have h1 := hsign start
  have h2 := hsign (start + 256 + 1727904)
  omega

end Wide16

end
end ShorECDLP.Entrant.Site1Wire
end

/-! ### Consolidated from `CornerFast.lean` -/
section
/-! Three-pass SelectSwap fusion of `[site2F, zrep, cornerNeg, corner]` for wide (16-bit) window rows.

Replaces the 4-block tail `[site2F, zrep, cornerNeg, corner]` (`99,818` QROM/swap/clear Toffolis
plus `513` Toffolis in `scrCWrite`) with 3 SelectSwap passes + 1 fused 8-bit measured clear:
- Pass 0 (`k = 1`, `529` bits = `cxWord (256)` + `cyWord (256)` + `extra0 (17)` on `14849..14865`):
  `32,767 + 529 = 33,296` Toffolis; runs `xAdd + negY + yAdd + zrep + cornerNeg + scrW1 +
  scrCWriteFused + scrW2 + negY + ccxList(17)` (saving `1` Toffoli in `scrCWriteFused` via
  `CX doubleSelect point.finite`), clears `cyWord.tail (255) ++ extra0 (17)`, keeps `cxWord + 14883`.
- Pass 1 (`k = 3`, `95` bits = `scrDExtra[17..111]` via `SS3`):
  `8,191 + 7 × 95 = 8,856` Toffolis; runs `ccxList(95)`, clears `95` wires.
- Pass 2 (`k = 1`, `401` bits = `scrShort (258)` + `scrDExtra[112..254] (143)`):
  `32,767 + 401 = 33,168` Toffolis; runs `ccxList(401)`, clears `extra2 (143)`, sets
  `14373 = true` and flips `14883` via `CX windowRoot`, runs `cornerA2` unchanged, clears `14373`,
  clears `scrShort ++ cxWord ++ [14883]`, and runs one single 8-bit fixup (`502` Toffolis).

Total savings: `23,997` Toffolis and `24,518` measurement records per wide window
(`623,922` Toffolis = `2,495,688` T-model gates across 26 wide windows). -/

namespace ShorECDLP.Entrant.CornerFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare Site1Fast
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 250000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

attribute [local irreducible] ECDSAAdd.run scrInP1 scrInP2 pair1Prog pair2Prog
  xAddProg yAddProg negYProg scrNegP ECDSAAdd.Frontier.zrep scrP1 scrP2
  scrPairWires scrShortWires scrDExtraWires WEXUnlookup.rowC WEXUnlookup.rowHead
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram

/-! ### Part 1: Bank-generic 3-bit SelectSwap gadget (`SS3`, 8 registers: targets + `g1..g7`) -/

structure SS3 (n : Nat) where
  bits : List Wire
  paths : List Wire
  selBits : List Wire
  selPaths : List Wire
  guard : Wire
  ports : List (LookupPort n)
  g1 : List Wire
  g2 : List Wire
  g3 : List Wire
  g4 : List Wire
  g5 : List Wire
  g6 : List Wire
  g7 : List Wire

namespace SS3
variable {n : Nat} (f : SS3 n)

def garb : List Wire := f.g1 ++ f.g2 ++ f.g3 ++ f.g4 ++ f.g5 ++ f.g6 ++ f.g7

def rowOf1 (a : Nat) : Nat := 8 * (a / 8) + (1 - a % 2)
def rowOf2 (a : Nat) : Nat := 8 * (a / 8) + 2 * (1 - a / 2 % 2) + a % 2
def rowOf3 (a : Nat) : Nat := 8 * (a / 8) + 3 - a % 2
def rowOf4 (a : Nat) : Nat := 8 * (a / 8) + 4 * (1 - a / 4 % 2) + 2 * (a / 2 % 2) + a % 2
def rowOf5 (a : Nat) : Nat := 8 * (a / 8) + 5 - a % 2
def rowOf6 (a : Nat) : Nat := 8 * (a / 8) + 4 + 2 * (1 - a / 2 % 2) + a % 2
def rowOf7 (a : Nat) : Nat := 8 * (a / 8) + 7 - a % 2

def selPorts : List (LookupPort n) :=
  f.ports.map (fun p => ⟨fun h => p.ref (8 * h), p.value, p.target⟩) ++
  WideBank8.Fast16.regPorts (fun h => 8 * h + 1) f.ports f.g1 ++
  WideBank8.Fast16.regPorts (fun h => 8 * h + 2) f.ports f.g2 ++
  WideBank8.Fast16.regPorts (fun h => 8 * h + 3) f.ports f.g3 ++
  WideBank8.Fast16.regPorts (fun h => 8 * h + 4) f.ports f.g4 ++
  WideBank8.Fast16.regPorts (fun h => 8 * h + 5) f.ports f.g5 ++
  WideBank8.Fast16.regPorts (fun h => 8 * h + 6) f.ports f.g6 ++
  WideBank8.Fast16.regPorts (fun h => 8 * h + 7) f.ports f.g7

def garbPorts : List (LookupPort n) :=
  WideBank8.Fast16.regPorts rowOf1 f.ports f.g1 ++
  WideBank8.Fast16.regPorts rowOf2 f.ports f.g2 ++
  WideBank8.Fast16.regPorts rowOf3 f.ports f.g3 ++
  WideBank8.Fast16.regPorts rowOf4 f.ports f.g4 ++
  WideBank8.Fast16.regPorts rowOf5 f.ports f.g5 ++
  WideBank8.Fast16.regPorts rowOf6 f.ports f.g6 ++
  WideBank8.Fast16.regPorts rowOf7 f.ports f.g7

def swapNet : ECDSAAdd.Program :=
  WideBank8.Fast16.swapLayer 855 (portTargets f.ports) f.g1 ++
  WideBank8.Fast16.swapLayer 855 f.g2 f.g3 ++
  WideBank8.Fast16.swapLayer 855 f.g4 f.g5 ++
  WideBank8.Fast16.swapLayer 855 f.g6 f.g7 ++
  WideBank8.Fast16.swapLayer 856 (portTargets f.ports) f.g2 ++
  WideBank8.Fast16.swapLayer 856 f.g4 f.g6 ++
  WideBank8.Fast16.swapLayer 857 (portTargets f.ports) f.g4

def selCode : WCode n := [.lookup (some f.guard) f.selPorts]

def loadProg (start : Nat) : Straight n start (start + codeRecords f.selBits f.selPaths windowRoot f.selCode) :=
  castFinish (by omega)
    ((compile f.selBits f.selPaths windowRoot f.selCode start).append
      (literalFixed f.swapNet 0 ((literal_meas (n := n) _).trans (by
        simp [swapNet, ECDSAAdd.measurementCount_append, WideBank8.Fast16.swapLayer_meas]))
        (start + codeRecords f.selBits f.selPaths windowRoot f.selCode)))

def loadSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  (source read f.selBits f.selPaths windowRoot f.selCode).seq (literalSource f.swapNet)

structure Geo : Prop where
  bitsEq : f.bits = 855 :: 856 :: 857 :: f.selBits
  pathsSub : ∀ w ∈ f.selPaths, w ∈ f.paths
  selLen : f.selPaths.length = f.selBits.length
  selNodup : (f.guard :: f.selBits ++ f.selPaths).Nodup
  selDisj : List.Disjoint (windowRoot :: f.guard :: f.selBits ++ f.selPaths) (portTargets f.ports ++ f.garb)
  len1 : f.g1.length = f.ports.length
  len2 : f.g2.length = f.ports.length
  len3 : f.g3.length = f.ports.length
  len4 : f.g4.length = f.ports.length
  len5 : f.g5.length = f.ports.length
  len6 : f.g6.length = f.ports.length
  len7 : f.g7.length = f.ports.length
  nodup : (portTargets f.ports ++ f.garb).Nodup
  n855 : (855 : Wire) ∉ portTargets f.ports ++ f.garb
  n856 : (856 : Wire) ∉ portTargets f.ports ++ f.garb
  n857 : (857 : Wire) ∉ portTargets f.ports ++ f.garb

theorem selPorts_targets (hg : f.Geo) : portTargets f.selPorts = portTargets f.ports ++ f.garb := by
  have h1 := WideBank8.Fast16.regPorts_targets (fun h => 8 * h + 1) f.ports f.g1 hg.len1
  have h2 := WideBank8.Fast16.regPorts_targets (fun h => 8 * h + 2) f.ports f.g2 hg.len2
  have h3 := WideBank8.Fast16.regPorts_targets (fun h => 8 * h + 3) f.ports f.g3 hg.len3
  have h4 := WideBank8.Fast16.regPorts_targets (fun h => 8 * h + 4) f.ports f.g4 hg.len4
  have h5 := WideBank8.Fast16.regPorts_targets (fun h => 8 * h + 5) f.ports f.g5 hg.len5
  have h6 := WideBank8.Fast16.regPorts_targets (fun h => 8 * h + 6) f.ports f.g6 hg.len6
  have h7 := WideBank8.Fast16.regPorts_targets (fun h => 8 * h + 7) f.ports f.g7 hg.len7
  simp only [selPorts, WideBank8.Fast16.FastSite.portTargets_append, h1, h2, h3, h4, h5, h6, h7,
    garb, List.append_assoc]
  congr 1
  simp [portTargets, List.map_map, Function.comp_def]

theorem garbPorts_targets (hg : f.Geo) : portTargets f.garbPorts = f.garb := by
  have h1 := WideBank8.Fast16.regPorts_targets rowOf1 f.ports f.g1 hg.len1
  have h2 := WideBank8.Fast16.regPorts_targets rowOf2 f.ports f.g2 hg.len2
  have h3 := WideBank8.Fast16.regPorts_targets rowOf3 f.ports f.g3 hg.len3
  have h4 := WideBank8.Fast16.regPorts_targets rowOf4 f.ports f.g4 hg.len4
  have h5 := WideBank8.Fast16.regPorts_targets rowOf5 f.ports f.g5 hg.len5
  have h6 := WideBank8.Fast16.regPorts_targets rowOf6 f.ports f.g6 hg.len6
  have h7 := WideBank8.Fast16.regPorts_targets rowOf7 f.ports f.g7 hg.len7
  simp only [garbPorts, WideBank8.Fast16.FastSite.portTargets_append, h1, h2, h3, h4, h5, h6, h7, garb]

theorem garbPorts_length (hg : f.Geo) : f.garbPorts.length = 7 * f.ports.length := by
  have h := congrArg List.length (garbPorts_targets f hg)
  simp only [portTargets, List.length_map, garb, List.length_append,
    hg.len1, hg.len2, hg.len3, hg.len4, hg.len5, hg.len6, hg.len7] at h
  omega

theorem selPorts_length (hg : f.Geo) : f.selPorts.length = 8 * f.ports.length := by
  have h := congrArg List.length (selPorts_targets f hg)
  simp only [portTargets, List.length_map, List.length_append, garb,
    hg.len1, hg.len2, hg.len3, hg.len4, hg.len5, hg.len6, hg.len7] at h
  omega

theorem sel_placed (hg : f.Geo) : Placed f.selBits f.selPaths windowRoot (.lookup (some f.guard) f.selPorts) := by
  refine ⟨by simpa [lookupRoot] using hg.selNodup, by rw [selPorts_targets f hg]; exact hg.nodup,
    by rw [selPorts_targets f hg]; simpa [lookupRoot] using hg.selDisj⟩

theorem sel_layouts (hg : f.Geo) : LookupLayouts f.selBits f.selPaths windowRoot f.selCode := by
  refine ⟨hg.selLen.ge, fun c ps hm => ?_⟩
  simp only [selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  simpa [lookupRoot] using hg.selNodup

theorem swapNet_toff (hg : f.Geo) : ECDSAAdd.toffoliCount f.swapNet = 7 * f.ports.length := by
  have ht : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  simp only [swapNet, ECDSAAdd.toffoliCount_append, WideBank8.Fast16.swapLayer_toff, ht,
    hg.len1, hg.len2, hg.len3, hg.len4, hg.len5, hg.len6, hg.len7, Nat.min_self]
  omega

theorem swapNet_slots (hg : f.Geo) : ECDSAAdd.Challenge.gateSlots f.swapNet = 21 * f.ports.length := by
  have ht : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  simp only [swapNet, ECDSAAdd.Challenge.gateSlots_append, WideBank8.Fast16.swapLayer_slots, ht,
    hg.len1, hg.len2, hg.len3, hg.len4, hg.len5, hg.len6, hg.len7, Nat.min_self]
  omega

private theorem pair_sublist_8 (A B C D E F G H : List Wire) :
    List.Sublist (A ++ B) (A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H)) ∧
    List.Sublist (C ++ D) (A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H)) ∧
    List.Sublist (E ++ F) (A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H)) ∧
    List.Sublist (G ++ H) (A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H)) ∧
    List.Sublist (A ++ C) (A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H)) ∧
    List.Sublist (E ++ G) (A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H)) ∧
    List.Sublist (A ++ E) (A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H)) := by
  have sB : List.Sublist B (B ++ C ++ D ++ E ++ F ++ G ++ H) := by
    simp only [List.append_assoc]; exact List.sublist_append_left _ _
  have sC : List.Sublist C (B ++ C ++ D ++ E ++ F ++ G ++ H) := by
    simp only [List.append_assoc]; exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)
  have sE : List.Sublist E (B ++ C ++ D ++ E ++ F ++ G ++ H) := by
    simp only [List.append_assoc]
    exact (List.sublist_append_left _ _).trans ((List.sublist_append_right _ _).trans
      ((List.sublist_append_right _ _).trans (List.sublist_append_right _ _)))
  have sCD : List.Sublist (C ++ D) (B ++ C ++ D ++ E ++ F ++ G ++ H) := by
    simp only [List.append_assoc]
    exact (List.Sublist.append (List.Sublist.refl C) (List.sublist_append_left D _)).trans
      (List.sublist_append_right B _)
  have sEF : List.Sublist (E ++ F) (B ++ C ++ D ++ E ++ F ++ G ++ H) := by
    simp only [List.append_assoc]
    exact (List.Sublist.append (List.Sublist.refl E) (List.sublist_append_left F _)).trans
      ((List.sublist_append_right D _).trans ((List.sublist_append_right C _).trans (List.sublist_append_right B _)))
  have sGH : List.Sublist (G ++ H) (B ++ C ++ D ++ E ++ F ++ G ++ H) := by
    simp only [List.append_assoc]
    exact (List.sublist_append_right F _).trans ((List.sublist_append_right E _).trans
      ((List.sublist_append_right D _).trans ((List.sublist_append_right C _).trans (List.sublist_append_right B _))))
  have sEG : List.Sublist (E ++ G) (B ++ C ++ D ++ E ++ F ++ G ++ H) := by
    simp only [List.append_assoc]
    have sG : List.Sublist G (F ++ (G ++ H)) := (List.sublist_append_left G H).trans (List.sublist_append_right F _)
    exact (List.Sublist.append (List.Sublist.refl E) sG).trans
      ((List.sublist_append_right D _).trans ((List.sublist_append_right C _).trans (List.sublist_append_right B _)))
  exact ⟨sB.append_left A, sCD.trans (List.sublist_append_right A _), sEF.trans (List.sublist_append_right A _),
    sGH.trans (List.sublist_append_right A _), sC.append_left A, sEG.trans (List.sublist_append_right A _),
    sE.append_left A⟩

theorem swapNet_valid (hg : f.Geo) : ∀ i ∈ f.swapNet, ECDSAAdd.Challenge.instructionValid i := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ :=
    pair_sublist_8 (portTargets f.ports) f.g1 f.g2 f.g3 f.g4 f.g5 f.g6 f.g7
  have h1 := WideBank8.Fast16.swapLayer_valid 855 _ _ (fun h => hg.n855 (s1.subset h)) (hg.nodup.sublist s1)
  have h2 := WideBank8.Fast16.swapLayer_valid 855 _ _ (fun h => hg.n855 (s2.subset h)) (hg.nodup.sublist s2)
  have h3 := WideBank8.Fast16.swapLayer_valid 855 _ _ (fun h => hg.n855 (s3.subset h)) (hg.nodup.sublist s3)
  have h4 := WideBank8.Fast16.swapLayer_valid 855 _ _ (fun h => hg.n855 (s4.subset h)) (hg.nodup.sublist s4)
  have h5 := WideBank8.Fast16.swapLayer_valid 856 _ _ (fun h => hg.n856 (s5.subset h)) (hg.nodup.sublist s5)
  have h6 := WideBank8.Fast16.swapLayer_valid 856 _ _ (fun h => hg.n856 (s6.subset h)) (hg.nodup.sublist s6)
  have h7 := WideBank8.Fast16.swapLayer_valid 857 _ _ (fun h => hg.n857 (s7.subset h)) (hg.nodup.sublist s7)
  intro i hi
  simp only [swapNet, List.mem_append] at hi
  rcases hi with (((((hi | hi) | hi) | hi) | hi) | hi) | hi
  · exact h1 i hi
  · exact h2 i hi
  · exact h3 i hi
  · exact h4 i hi
  · exact h5 i hi
  · exact h6 i hi
  · exact h7 i hi

theorem loadProg_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.loadProg start).instantiate read history).run = (f.loadSource read).run := by
  rw [loadProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h),
    AdaptiveCircuit.run_seq, compile_run]
  simp only [loadSource, AdaptiveCircuit.run_seq]

theorem loadProg_tCount (read : ConstantBit n → Bool) (hg : f.Geo) (start : Nat) (history : Fin start → Bool) :
    ((f.loadProg start).instantiate read history).tCount =
      7 * (2 ^ f.selBits.length - 1 + 7 * f.ports.length) := by
  rw [loadProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read f.selBits f.selPaths windowRoot f.selCode (sel_layouts f hg),
    swapNet_toff f hg]
  simp only [selCode, literalToffolis, traversals, Nat.zero_add, Nat.one_mul]
  ring

theorem loadProg_records (hg : f.Geo) :
    codeRecords f.selBits f.selPaths windowRoot f.selCode = 2 ^ f.selBits.length - 1 := by
  rw [codeRecords_eq _ _ _ _ (sel_layouts f hg)]
  simp [selCode, literalRecords, traversals]

theorem loadProg_slots (hg : f.Geo) (start : Nat) :
    (f.loadProg start).gateSlots ≤ 2 ^ f.selBits.length * (8 * f.ports.length) + 10 * (2 ^ f.selBits.length - 1) +
      84 * f.ports.length := by
  rw [loadProg, castFinish_gateSlots, Straight.gateSlots_append,
    compile_slots _ _ _ _ (sel_layouts f hg), literalFixed_slots]
  have h1 : codeSlots f.selBits f.selCode = 2 ^ f.selBits.length * f.selPorts.length + 10 * (2 ^ f.selBits.length - 1) := by
    simp [selCode, codeSlots]
  have h2 := literal_slot_bound (n := n) f.swapNet
  rw [swapNet_slots f hg] at h2
  rw [h1, selPorts_length f hg]
  omega

theorem loadProg_wellFormed (hg : f.Geo) (start : Nat) : (f.loadProg start).WellFormed := by
  rw [loadProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ ?_ (literalFixed_wellFormed _ _ _ (swapNet_valid f hg) _)
  exact pair_compile_wellFormed _ _ _ _ hg.selLen.ge
    (fun i hi => by
      simp only [selCode, List.mem_singleton] at hi; subst hi
      exact placed_implies_pair _ _ _ _ (sel_placed f hg))
    (fun p hp => by simp [selCode] at hp) start

theorem loadProg_residue (start : Nat) : AndGadget.residue (f.loadProg start) = 0 := by
  rw [loadProg, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
    literalFixed, WEXCredit.residue_naive_cast, WEXCredit.literal_residue]

theorem loadProg_support (hg : f.Geo) (S : List Wire)
    (hroot : windowRoot ∈ S) (hguard : f.guard ∈ S)
    (h855 : (855 : Wire) ∈ S) (h856 : (856 : Wire) ∈ S) (h857 : (857 : Wire) ∈ S)
    (hbits : f.selBits ⊆ S) (hpaths : f.selPaths ⊆ S) (hreg : portTargets f.ports ++ f.garb ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (f.loadProg start) ⊆ S := by
  rw [loadProg, support_cast, straightWires_append]
  refine List.append_subset.mpr ⟨?_, ?_⟩
  · refine compile_support f.selBits f.selPaths windowRoot f.selCode S hroot hbits hpaths
      (fun p hp => by simp [selCode] at hp) ?_ start
    intro c ps hm
    simp only [selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨fun q hq => by rw [Option.mem_def, Option.some_inj] at hq; exact hq ▸ hguard,
      by rw [selPorts_targets f hg]; exact hreg⟩
  · refine literalFixed_support _ _ _ S ?_ _
    intro w hw
    simp only [swapNet, ECDSAAdd.wires_append, Finset.mem_union] at hw
    simp only [List.mem_toFinset]
    have hsw (c : Wire) (A B : List Wire) (hc : c ∈ S) (hA : A ⊆ S) (hB : B ⊆ S)
        (hw' : w ∈ ECDSAAdd.wires (WideBank8.Fast16.swapLayer c A B)) : w ∈ S := by
      have h := WideBank8.Fast16.swapLayer_wires c A B hw'
      simp only [List.mem_toFinset, List.cons_append, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact hc
      · exact hA h
      · exact hB h
    have hT : portTargets f.ports ⊆ S := fun x hx => hreg (List.mem_append_left _ hx)
    have h1 : f.g1 ⊆ S := fun x hx => hreg (List.mem_append_right _ (by simp [garb, hx]))
    have h2 : f.g2 ⊆ S := fun x hx => hreg (List.mem_append_right _ (by simp [garb, hx]))
    have h3 : f.g3 ⊆ S := fun x hx => hreg (List.mem_append_right _ (by simp [garb, hx]))
    have h4 : f.g4 ⊆ S := fun x hx => hreg (List.mem_append_right _ (by simp [garb, hx]))
    have h5 : f.g5 ⊆ S := fun x hx => hreg (List.mem_append_right _ (by simp [garb, hx]))
    have h6 : f.g6 ⊆ S := fun x hx => hreg (List.mem_append_right _ (by simp [garb, hx]))
    have h7 : f.g7 ⊆ S := fun x hx => hreg (List.mem_append_right _ (by simp [garb, hx]))
    rcases hw with (((((hw | hw) | hw) | hw) | hw) | hw) | hw
    · exact hsw 855 _ _ h855 hT h1 hw
    · exact hsw 855 _ _ h855 h2 h3 hw
    · exact hsw 855 _ _ h855 h4 h5 hw
    · exact hsw 855 _ _ h855 h6 h7 hw
    · exact hsw 856 _ _ h856 hT h2 hw
    · exact hsw 856 _ _ h856 h4 h6 hw
    · exact hsw 857 _ _ h857 hT h4 hw

private theorem holds_congr {read : ConstantBit n → Bool} {ps : List (LookupPort n)}
    {ws : List Wire} {r : Nat} {g : Bool} {s t : BasisState}
    (h : WideBank8.Fast16.FastSite.Holds read ps ws r g s)
    (heq : ∀ w ∈ ws, t w = s w) :
    WideBank8.Fast16.FastSite.Holds read ps ws r g t := fun i hi hgi => by
  rw [heq _ (List.getElem_mem hgi)]; exact h i hi hgi

private theorem disj_of_nodup_8 {A B C D E F G H : List Wire}
    (hnd : (A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H)).Nodup) :
    (∀ w ∈ A, w ∉ B ∧ w ∉ C ∧ w ∉ D ∧ w ∉ E ∧ w ∉ F ∧ w ∉ G ∧ w ∉ H) ∧
    (∀ w ∈ B, w ∉ A ∧ w ∉ C ∧ w ∉ D ∧ w ∉ E ∧ w ∉ F ∧ w ∉ G ∧ w ∉ H) ∧
    (∀ w ∈ C, w ∉ A ∧ w ∉ B ∧ w ∉ D ∧ w ∉ E ∧ w ∉ F ∧ w ∉ G ∧ w ∉ H) ∧
    (∀ w ∈ D, w ∉ A ∧ w ∉ B ∧ w ∉ C ∧ w ∉ E ∧ w ∉ F ∧ w ∉ G ∧ w ∉ H) ∧
    (∀ w ∈ E, w ∉ A ∧ w ∉ B ∧ w ∉ C ∧ w ∉ D ∧ w ∉ F ∧ w ∉ G ∧ w ∉ H) ∧
    (∀ w ∈ F, w ∉ A ∧ w ∉ B ∧ w ∉ C ∧ w ∉ D ∧ w ∉ E ∧ w ∉ G ∧ w ∉ H) ∧
    (∀ w ∈ G, w ∉ A ∧ w ∉ B ∧ w ∉ C ∧ w ∉ D ∧ w ∉ E ∧ w ∉ F ∧ w ∉ H) ∧
    (∀ w ∈ H, w ∉ A ∧ w ∉ B ∧ w ∉ C ∧ w ∉ D ∧ w ∉ E ∧ w ∉ F ∧ w ∉ G) := by
  have hc := fun w => List.nodup_iff_count.mp hnd w
  have aux : ∀ w, List.count w A + List.count w B + List.count w C + List.count w D +
      List.count w E + List.count w F + List.count w G + List.count w H ≤ 1 := fun w => by
    have h := hc w
    simp only [List.count_append] at h
    omega
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_,
          fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩ <;>
  · have h := aux w
    have hpos := List.count_pos_iff.mpr hw
    refine ⟨fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩ <;>
    · have hp2 := List.count_pos_iff.mpr hm; omega

private theorem div8_bits (r h : Nat) (hr : r < 8) :
    (r + 8 * h) / 8 = h ∧ (r + 8 * h) % 2 = r % 2 ∧
    (r + 8 * h) / 2 % 2 = r / 2 % 2 ∧ (r + 8 * h) / 4 % 2 = r / 4 % 2 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

private theorem rowOf_arith (b0 b1 b2 : Bool) (h a : Nat)
    (haddr : a = b0.toNat + 2 * (b1.toNat + 2 * (b2.toNat + 2 * h))) :
    (if b2 then (if b1 then (if b0 then 8 * h + 7 else 8 * h + 6) else (if b0 then 8 * h + 5 else 8 * h + 4))
      else (if b1 then (if b0 then 8 * h + 3 else 8 * h + 2) else (if b0 then 8 * h + 1 else 8 * h))) = a ∧
    (if b0 then 8 * h else 8 * h + 1) = rowOf1 a ∧
    (if b1 then (if b0 then 8 * h + 1 else 8 * h) else (if b0 then 8 * h + 3 else 8 * h + 2)) = rowOf2 a ∧
    (if b0 then 8 * h + 2 else 8 * h + 3) = rowOf3 a ∧
    (if b2 then (if b1 then (if b0 then 8 * h + 3 else 8 * h + 2) else (if b0 then 8 * h + 1 else 8 * h))
      else (if b1 then (if b0 then 8 * h + 7 else 8 * h + 6) else (if b0 then 8 * h + 5 else 8 * h + 4))) = rowOf4 a ∧
    (if b0 then 8 * h + 4 else 8 * h + 5) = rowOf5 a ∧
    (if b1 then (if b0 then 8 * h + 5 else 8 * h + 4) else (if b0 then 8 * h + 7 else 8 * h + 6)) = rowOf6 a ∧
    (if b0 then 8 * h + 6 else 8 * h + 7) = rowOf7 a := by
  let r := b0.toNat + 2 * b1.toNat + 4 * b2.toNat
  have ha : a = r + 8 * h := by
    dsimp only [r]; omega
  have hr : r < 8 := by
    dsimp only [r]; cases b0 <;> cases b1 <;> cases b2 <;> decide
  obtain ⟨hd8, hm2, hd2, hd4⟩ := div8_bits r h hr
  rw [ha]
  simp only [rowOf1, rowOf2, rowOf3, rowOf4, rowOf5, rowOf6, rowOf7, hd8, hm2, hd2, hd4]
  dsimp only [r]
  cases b0 <;> cases b1 <;> cases b2 <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte,
      Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
      Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
      Nat.add_comm, Nat.add_assoc, and_self, true_and, and_true] <;>
    try omega

theorem load_state (read : ConstantBit n → Bool) (hg : f.Geo) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid f.bits f.paths windowRoot a st)
    (hc : Clean (portTargets f.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue f.selBits st.basis)).instantiate read) List.nil st)
    s₂.phase = st.phase ∧
    (∀ w, w ∉ portTargets f.ports → w ∉ f.garb → s₂.basis w = st.basis w) ∧
    (∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.guard && decide (read (q.ref a) = q.value))) ∧
    clearRegister f.garb s₂.basis = tableXorState (portMask read f.ports a) (st.basis f.guard) st.basis := by
  intro s₂
  have hsel := selPorts_targets f hg
  have hselnd : (portTargets f.selPorts).Nodup := by rw [hsel]; exact hg.nodup
  have hguard : f.guard ∉ portTargets f.selPorts := by
    rw [hsel]; exact List.disjoint_left.mp hg.selDisj (by simp)
  have lt : (portTargets f.ports).length = f.ports.length := by simp [portTargets]
  have hnd_app := List.nodup_append.mp hg.nodup
  have hd : ∀ w ∈ f.garb, w ∉ portTargets f.ports := fun w hw hm => hnd_app.2.2 w hm w hw rfl
  obtain ⟨dA, dB, dC, dD, dE, dF, dG, dH⟩ := disj_of_nodup_8 hg.nodup
  set h := tableAddressValue f.selBits st.basis with hh
  have e1 : specialize f.selCode h = portTemplate (some f.guard) f.selPorts h := by
    simp [selCode, specialize, WInstr.specialize]
  set s₁ := ECDSAAdd.run ((specialize f.selCode h).instantiate read) List.nil st with hs₁
  have r1 : s₁ = ⟨st.phase, tableXorState (portMask read f.selPorts h) (st.basis f.guard) st.basis⟩ := by
    rw [hs₁, e1]
    exact portTemplate_run read (some f.guard) f.selPorts h windowRoot List.nil st hselnd hguard hs.2.2
  have sel_at : ∀ q ∈ f.selPorts, s₁.basis q.target =
      (st.basis f.guard && decide (read (q.ref h) = q.value)) := by
    intro q hq
    rw [r1]; show tableXorState _ _ _ q.target = _
    simp only [tableXorState, port_selected read f.selPorts h hselnd q hq]
    have hm : q.target ∈ portTargets f.selPorts := List.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hsel] at hm
    simp [hc _ hm]
  have frame1 : ∀ w, w ∉ portTargets f.ports → w ∉ f.garb → s₁.basis w = st.basis w := by
    intro w h1 h2
    rw [r1]; show tableXorState _ _ _ w = _
    apply tableXorState_outside
    intro hm
    have hm' := tableBitsMask_subset _ _ hm
    rw [hsel] at hm'
    rcases List.mem_append.mp hm' with h' | h'
    · exact h1 h'
    · exact h2 h'
  have H0 : WideBank8.Fast16.FastSite.Holds read f.ports (portTargets f.ports) (8 * h) (st.basis f.guard) s₁.basis := by
    intro i hi hgi
    have hq : (⟨fun h => (f.ports[i]'hi).ref (8 * h), (f.ports[i]'hi).value, (f.ports[i]'hi).target⟩ : LookupPort n) ∈
        f.selPorts := by
      simp only [selPorts, List.mem_append]; left; left; left; left; left; left; left
      exact List.mem_map.mpr ⟨f.ports[i]'hi, List.getElem_mem hi, rfl⟩
    simpa [portTargets, List.getElem_map] using sel_at _ hq
  have H1 : WideBank8.Fast16.FastSite.Holds read f.ports f.g1 (8 * h + 1) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; left; left; left; left; left; left; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have H2 : WideBank8.Fast16.FastSite.Holds read f.ports f.g2 (8 * h + 2) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; left; left; left; left; left; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have H3 : WideBank8.Fast16.FastSite.Holds read f.ports f.g3 (8 * h + 3) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; left; left; left; left; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have H4 : WideBank8.Fast16.FastSite.Holds read f.ports f.g4 (8 * h + 4) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; left; left; left; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have H5 : WideBank8.Fast16.FastSite.Holds read f.ports f.g5 (8 * h + 5) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; left; left; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have H6 : WideBank8.Fast16.FastSite.Holds read f.ports f.g6 (8 * h + 6) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; left; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  have H7 : WideBank8.Fast16.FastSite.Holds read f.ports f.g7 (8 * h + 7) (st.basis f.guard) s₁.basis := fun i hi hgi =>
    sel_at _ (by simp only [selPorts, List.mem_append]; right; exact WideBank8.Fast16.mem_regPorts _ _ _ i hi hgi)
  obtain ⟨sb1, sb2, sb3, sb4, sb5, sb6, sb7⟩ :=
    pair_sublist_8 (portTargets f.ports) f.g1 f.g2 f.g3 f.g4 f.g5 f.g6 f.g7
  have nd1 := hg.nodup.sublist sb1
  have nd2 := hg.nodup.sublist sb2
  have nd3 := hg.nodup.sublist sb3
  have nd4 := hg.nodup.sublist sb4
  have nd5 := hg.nodup.sublist sb5
  have nd6 := hg.nodup.sublist sb6
  have nd7 := hg.nodup.sublist sb7
  have c1 : (855 : Wire) ∉ portTargets f.ports ++ f.g1 := fun h' => hg.n855 (sb1.subset h')
  have c2 : (855 : Wire) ∉ f.g2 ++ f.g3 := fun h' => hg.n855 (sb2.subset h')
  have c3 : (855 : Wire) ∉ f.g4 ++ f.g5 := fun h' => hg.n855 (sb3.subset h')
  have c4 : (855 : Wire) ∉ f.g6 ++ f.g7 := fun h' => hg.n855 (sb4.subset h')
  have c5 : (856 : Wire) ∉ portTargets f.ports ++ f.g2 := fun h' => hg.n856 (sb5.subset h')
  have c6 : (856 : Wire) ∉ f.g4 ++ f.g6 := fun h' => hg.n856 (sb6.subset h')
  have c7 : (857 : Wire) ∉ portTargets f.ports ++ f.g4 := fun h' => hg.n857 (sb7.subset h')
  set t₁ := ECDSAAdd.run (WideBank8.Fast16.swapLayer 855 (portTargets f.ports) f.g1) List.nil s₁ with ht₁
  set t₂ := ECDSAAdd.run (WideBank8.Fast16.swapLayer 855 f.g2 f.g3) List.nil t₁ with ht₂
  set t₃ := ECDSAAdd.run (WideBank8.Fast16.swapLayer 855 f.g4 f.g5) List.nil t₂ with ht₃
  set t₄ := ECDSAAdd.run (WideBank8.Fast16.swapLayer 855 f.g6 f.g7) List.nil t₃ with ht₄
  set t₅ := ECDSAAdd.run (WideBank8.Fast16.swapLayer 856 (portTargets f.ports) f.g2) List.nil t₄ with ht₅
  set t₆ := ECDSAAdd.run (WideBank8.Fast16.swapLayer 856 f.g4 f.g6) List.nil t₅ with ht₆
  have hs₂ : s₂ = ECDSAAdd.run (WideBank8.Fast16.swapLayer 857 (portTargets f.ports) f.g4) List.nil t₆ := by
    show ECDSAAdd.run f.swapNet List.nil s₁ = _
    simp only [swapNet, ECDSAAdd.run_append, ECDSAAdd.measurementCount_append, WideBank8.Fast16.swapLayer_meas,
      Nat.add_zero, List.take_zero, List.drop_zero, List.take_nil, List.drop_nil]
    rw [ht₆, ht₅, ht₄, ht₃, ht₂, ht₁]
  obtain ⟨p1, fr1, -⟩ := WideBank8.Fast16.swapLayer_run 855 _ _ c1 nd1 (by rw [lt, hg.len1]) s₁ List.nil
  obtain ⟨p2, fr2, -⟩ := WideBank8.Fast16.swapLayer_run 855 _ _ c2 nd2 (by rw [hg.len2, hg.len3]) t₁ List.nil
  obtain ⟨p3, fr3, -⟩ := WideBank8.Fast16.swapLayer_run 855 _ _ c3 nd3 (by rw [hg.len4, hg.len5]) t₂ List.nil
  obtain ⟨p4, fr4, -⟩ := WideBank8.Fast16.swapLayer_run 855 _ _ c4 nd4 (by rw [hg.len6, hg.len7]) t₃ List.nil
  obtain ⟨p5, fr5, -⟩ := WideBank8.Fast16.swapLayer_run 856 _ _ c5 nd5 (by rw [lt, hg.len2]) t₄ List.nil
  obtain ⟨p6, fr6, -⟩ := WideBank8.Fast16.swapLayer_run 856 _ _ c6 nd6 (by rw [hg.len4, hg.len6]) t₅ List.nil
  obtain ⟨p7, fr7, -⟩ := WideBank8.Fast16.swapLayer_run 857 _ _ c7 nd7 (by rw [lt, hg.len4]) t₆ List.nil
  rw [← ht₁] at p1 fr1; rw [← ht₂] at p2 fr2; rw [← ht₃] at p3 fr3; rw [← ht₄] at p4 fr4
  rw [← ht₅] at p5 fr5; rw [← ht₆] at p6 fr6; rw [← hs₂] at p7 fr7
  have b0_1 : s₁.basis 855 = st.basis 855 :=
    frame1 _ (fun h' => hg.n855 (List.mem_append_left _ h')) (fun h' => hg.n855 (List.mem_append_right _ h'))
  have b0_2 : t₁.basis 855 = st.basis 855 :=
    (fr1 _ (fun h' => c1 (List.mem_append_left _ h')) (fun h' => c1 (List.mem_append_right _ h'))).trans b0_1
  have b0_3 : t₂.basis 855 = st.basis 855 :=
    (fr2 _ (fun h' => c2 (List.mem_append_left _ h')) (fun h' => c2 (List.mem_append_right _ h'))).trans b0_2
  have b0_4 : t₃.basis 855 = st.basis 855 :=
    (fr3 _ (fun h' => c3 (List.mem_append_left _ h')) (fun h' => c3 (List.mem_append_right _ h'))).trans b0_3
  have b1_5 : t₄.basis 856 = st.basis 856 := by
    have h856_0 : s₁.basis 856 = st.basis 856 :=
      frame1 _ (fun h' => hg.n856 (List.mem_append_left _ h')) (fun h' => hg.n856 (List.mem_append_right _ h'))
    have h1 : 856 ∉ portTargets f.ports ∧ 856 ∉ f.g1 ∧ 856 ∉ f.g2 ∧ 856 ∉ f.g3 ∧ 856 ∉ f.g4 ∧ 856 ∉ f.g5 ∧ 856 ∉ f.g6 ∧ 856 ∉ f.g7 := by
      have hm := hg.n856
      simp only [garb, List.mem_append, not_or] at hm
      tauto
    rw [fr4 _ h1.2.2.2.2.2.2.1 h1.2.2.2.2.2.2.2, fr3 _ h1.2.2.2.2.1 h1.2.2.2.2.2.1,
      fr2 _ h1.2.2.1 h1.2.2.2.1, fr1 _ h1.1 h1.2.1, h856_0]
  have b1_6 : t₅.basis 856 = st.basis 856 :=
    (fr5 _ (fun h' => c5 (List.mem_append_left _ h')) (fun h' => c5 (List.mem_append_right _ h'))).trans b1_5
  have b2_7 : t₆.basis 857 = st.basis 857 := by
    have h857_0 : s₁.basis 857 = st.basis 857 :=
      frame1 _ (fun h' => hg.n857 (List.mem_append_left _ h')) (fun h' => hg.n857 (List.mem_append_right _ h'))
    have h1 : 857 ∉ portTargets f.ports ∧ 857 ∉ f.g1 ∧ 857 ∉ f.g2 ∧ 857 ∉ f.g3 ∧ 857 ∉ f.g4 ∧ 857 ∉ f.g5 ∧ 857 ∉ f.g6 ∧ 857 ∉ f.g7 := by
      have hm := hg.n857
      simp only [garb, List.mem_append, not_or] at hm
      tauto
    rw [fr6 _ h1.2.2.2.2.1 h1.2.2.2.2.2.2.1, fr5 _ h1.1 h1.2.2.1, fr4 _ h1.2.2.2.2.2.2.1 h1.2.2.2.2.2.2.2,
      fr3 _ h1.2.2.2.2.1 h1.2.2.2.2.2.1, fr2 _ h1.2.2.1 h1.2.2.2.1, fr1 _ h1.1 h1.2.1, h857_0]
  -- Layer 1: 4 swaps controlled on 855
  obtain ⟨T_1, G1_1⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 855 (8 * h) (8 * h + 1) (st.basis f.guard) s₁ List.nil
    c1 nd1 lt hg.len1 H0 H1
  rw [← ht₁, b0_1] at T_1 G1_1
  have H2_1 := holds_congr H2 (fun w hw => fr1 w (dC w hw).1 (dC w hw).2.1)
  have H3_1 := holds_congr H3 (fun w hw => fr1 w (dD w hw).1 (dD w hw).2.1)
  obtain ⟨G2_2, G3_2⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 855 (8 * h + 2) (8 * h + 3) (st.basis f.guard) t₁ List.nil
    c2 nd2 hg.len2 hg.len3 H2_1 H3_1
  rw [← ht₂, b0_2] at G2_2 G3_2
  have H4_2 := holds_congr H4 (fun w hw => (fr2 w (dE w hw).2.2.1 (dE w hw).2.2.2.1).trans (fr1 w (dE w hw).1 (dE w hw).2.1))
  have H5_2 := holds_congr H5 (fun w hw => (fr2 w (dF w hw).2.2.1 (dF w hw).2.2.2.1).trans (fr1 w (dF w hw).1 (dF w hw).2.1))
  obtain ⟨G4_3, G5_3⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 855 (8 * h + 4) (8 * h + 5) (st.basis f.guard) t₂ List.nil
    c3 nd3 hg.len4 hg.len5 H4_2 H5_2
  rw [← ht₃, b0_3] at G4_3 G5_3
  have H6_3 := holds_congr H6 (fun w hw => (fr3 w (dG w hw).2.2.2.2.1 (dG w hw).2.2.2.2.2.1).trans
    ((fr2 w (dG w hw).2.2.1 (dG w hw).2.2.2.1).trans (fr1 w (dG w hw).1 (dG w hw).2.1)))
  have H7_3 := holds_congr H7 (fun w hw => (fr3 w (dH w hw).2.2.2.2.1 (dH w hw).2.2.2.2.2.1).trans
    ((fr2 w (dH w hw).2.2.1 (dH w hw).2.2.2.1).trans (fr1 w (dH w hw).1 (dH w hw).2.1)))
  obtain ⟨G6_4, G7_4⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 855 (8 * h + 6) (8 * h + 7) (st.basis f.guard) t₃ List.nil
    c4 nd4 hg.len6 hg.len7 H6_3 H7_3
  rw [← ht₄, b0_4] at G6_4 G7_4
  -- Layer 2: 2 swaps controlled on 856
  have T_4 := holds_congr T_1 (fun w hw => (fr4 w (dA w hw).2.2.2.2.2.1 (dA w hw).2.2.2.2.2.2).trans
    ((fr3 w (dA w hw).2.2.2.1 (dA w hw).2.2.2.2.1).trans (fr2 w (dA w hw).2.1 (dA w hw).2.2.1)))
  have G2_4 := holds_congr G2_2 (fun w hw => (fr4 w (dC w hw).2.2.2.2.2.1 (dC w hw).2.2.2.2.2.2).trans
    (fr3 w (dC w hw).2.2.2.1 (dC w hw).2.2.2.2.1))
  obtain ⟨T_5, G2_5⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 856 _ _ (st.basis f.guard) t₄ List.nil
    c5 nd5 lt hg.len2 T_4 G2_4
  rw [← ht₅, b1_5] at T_5 G2_5
  have G4_5 := holds_congr G4_3 (fun w hw => (fr5 w (dE w hw).1 (dE w hw).2.2.1).trans
    (fr4 w (dE w hw).2.2.2.2.2.1 (dE w hw).2.2.2.2.2.2))
  have G6_5 := holds_congr G6_4 (fun w hw => fr5 w (dG w hw).1 (dG w hw).2.2.1)
  obtain ⟨G4_6, G6_6⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 856 _ _ (st.basis f.guard) t₅ List.nil
    c6 nd6 hg.len4 hg.len6 G4_5 G6_5
  rw [← ht₆, b1_6] at G4_6 G6_6
  -- Layer 3: 1 swap controlled on 857
  have T_6 := holds_congr T_5 (fun w hw => fr6 w (dA w hw).2.2.2.1 (dA w hw).2.2.2.2.2.1)
  obtain ⟨T_7, G4_7⟩ := WideBank8.Fast16.FastSite.holds_swap read f.ports _ _ 857 _ _ (st.basis f.guard) t₆ List.nil
    c7 nd7 lt hg.len4 T_6 G4_6
  rw [← hs₂, b2_7] at T_7 G4_7
  -- Carry untouched garbage registers to s₂
  have G1_7 := holds_congr G1_1 (fun w hw =>
    (fr7 w (dB w hw).1 (dB w hw).2.2.2.1).trans ((fr6 w (dB w hw).2.2.2.1 (dB w hw).2.2.2.2.2.1).trans
    ((fr5 w (dB w hw).1 (dB w hw).2.1).trans ((fr4 w (dB w hw).2.2.2.2.2.1 (dB w hw).2.2.2.2.2.2).trans
    ((fr3 w (dB w hw).2.2.2.1 (dB w hw).2.2.2.2.1).trans (fr2 w (dB w hw).2.1 (dB w hw).2.2.1))))))
  have G2_7 := holds_congr G2_5 (fun w hw =>
    (fr7 w (dC w hw).1 (dC w hw).2.2.2.1).trans (fr6 w (dC w hw).2.2.2.1 (dC w hw).2.2.2.2.2.1))
  have G3_7 := holds_congr G3_2 (fun w hw =>
    (fr7 w (dD w hw).1 (dD w hw).2.2.2.1).trans ((fr6 w (dD w hw).2.2.2.1 (dD w hw).2.2.2.2.2.1).trans
    ((fr5 w (dD w hw).1 (dD w hw).2.2.1).trans ((fr4 w (dD w hw).2.2.2.2.2.1 (dD w hw).2.2.2.2.2.2).trans
    (fr3 w (dD w hw).2.2.2.1 (dD w hw).2.2.2.2.1)))))
  have G5_7 := holds_congr G5_3 (fun w hw =>
    (fr7 w (dF w hw).1 (dF w hw).2.2.2.2.1).trans ((fr6 w (dF w hw).2.2.2.2.1 (dF w hw).2.2.2.2.2.1).trans
    ((fr5 w (dF w hw).1 (dF w hw).2.2.1).trans (fr4 w (dF w hw).2.2.2.2.2.1 (dF w hw).2.2.2.2.2.2))))
  have G6_7 := holds_congr G6_6 (fun w hw => fr7 w (dG w hw).1 (dG w hw).2.2.2.2.1)
  have G7_7 := holds_congr G7_4 (fun w hw =>
    (fr7 w (dH w hw).1 (dH w hw).2.2.2.2.1).trans ((fr6 w (dH w hw).2.2.2.2.1 (dH w hw).2.2.2.2.2.2).trans
    (fr5 w (dH w hw).1 (dH w hw).2.2.1)))
  -- Address arithmetic
  have haddr : a = (st.basis 855).toNat + 2 * ((st.basis 856).toNat + 2 * ((st.basis 857).toNat + 2 * h)) := by
    have htv := hs.2.1
    rw [hg.bitsEq] at htv
    simp only [tableAddressValue, wireValues, List.map_cons, boolWordToNat] at htv
    omega
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ :=
    rowOf_arith (st.basis 855) (st.basis 856) (st.basis 857) h a haddr
  rw [hr0] at T_7; rw [hr1] at G1_7; rw [hr2] at G2_7; rw [hr3] at G3_7
  rw [hr4] at G4_7; rw [hr5] at G5_7; rw [hr6] at G6_7; rw [hr7] at G7_7
  have frame : ∀ w, w ∉ portTargets f.ports → w ∉ f.garb → s₂.basis w = st.basis w := fun w h1 h2 => by
    simp only [garb, List.mem_append, not_or] at h2
    rw [fr7 w h1 h2.1.1.1.2, fr6 w h2.1.1.1.2 h2.1.2, fr5 w h1 h2.1.1.1.1.1.2,
      fr4 w h2.1.2 h2.2, fr3 w h2.1.1.1.2 h2.1.1.2, fr2 w h2.1.1.1.1.1.2 h2.1.1.1.1.2,
      fr1 w h1 h2.1.1.1.1.1.1, frame1 w h1 (by simp [garb, h2])]
  refine ⟨by rw [p7, p6, p5, p4, p3, p2, p1, r1], frame, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    simp only [garbPorts, List.mem_append] at hp
    rcases hp with (((((hp | hp) | hp) | hp) | hp) | hp) | hp
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp; exact G1_7 i hi hgi
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp; exact G2_7 i hi hgi
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp; exact G3_7 i hi hgi
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp; exact G4_7 i hi hgi
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp; exact G5_7 i hi hgi
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp; exact G6_7 i hi hgi
    · obtain ⟨i, hi, hgi, rfl⟩ := WideBank8.Fast16.of_mem_regPorts _ _ _ p hp; exact G7_7 i hi hgi
  · funext w
    by_cases hwg : w ∈ f.garb
    · rw [clearRegister_clean f.garb s₂.basis w hwg]
      have hnt : w ∉ portTargets f.ports := hd w hwg
      rw [tableXorState_outside (portMask read f.ports a) _ _ w (fun hm => hnt (tableBitsMask_subset _ _ hm))]
      exact (hc w (List.mem_append_right _ hwg)).symm
    · rw [MeasuredClear.clearRegister_frame f.garb s₂.basis w hwg]
      by_cases hwt : w ∈ portTargets f.ports
      · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hwt
        have hi' : i < f.ports.length := by simpa [portTargets] using hi
        have hT := T_7 i hi' hi
        rw [he] at hT
        have hp : f.ports[i]'hi' ∈ f.ports := List.getElem_mem hi'
        have htg : (f.ports[i]'hi').target = w := by simpa [portTargets, List.getElem_map] using he
        have hsel' := port_selected read f.ports a hnd_app.1 (f.ports[i]'hi') hp
        rw [htg] at hsel'
        have hcw := hc w (List.mem_append_left _ hwt)
        simp only [tableXorState, hsel', hcw, Bool.false_xor]
        exact hT
      · rw [frame w hwt hwg]
        exact (tableXorState_outside _ _ _ _ (fun hm => hwt (tableBitsMask_subset _ _ hm))).symm

theorem load_sim (read : ConstantBit n → Bool) (hg : f.Geo) :
    ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∀ a (st : ECDSAAdd.State),
        SimulationValid f.bits f.paths windowRoot a st →
        Clean (portTargets f.ports ++ f.garb) st.basis →
        b.kraus (Bridge.signedKet st) = c • Bridge.signedKet
          (ECDSAAdd.run f.swapNet List.nil
            (ECDSAAdd.run ((specialize f.selCode (tableAddressValue f.selBits st.basis)).instantiate read) List.nil st)))
      (f.loadSource read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hp1 : ∀ i ∈ f.selCode, PlacedPair f.selBits f.selPaths windowRoot i := by
    intro i hi
    simp only [selCode, List.mem_singleton] at hi; subst hi
    exact placed_implies_pair _ _ _ _ (sel_placed f hg)
  obtain ⟨c1, a1, m1⟩ := pair_source_simulation read f.selBits f.selPaths windowRoot hg.selLen.ge f.selCode hp1
  obtain ⟨c2, a2, m2⟩ := literal_simulation f.swapNet
  have h1 : ∀ a (st : ECDSAAdd.State), SimulationValid f.bits f.paths windowRoot a st →
      SimulationValid f.selBits f.selPaths windowRoot (tableAddressValue f.selBits st.basis) st :=
    fun a st hs => ⟨fun w hw => hs.1 w (hg.pathsSub w hw), rfl, hs.2.2⟩
  refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
  rw [loadSource, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a1 a2
  intro b₁ k₁ b₂ k₂ hb₁ hb₂ a st hs _
  obtain ⟨m, hm, hb₁⟩ := hb₁
  have hm0 : m = List.nil := List.eq_nil_of_length_eq_zero (by simpa [selCode, literalRecords] using hm)
  have hh0 : b₂.history = List.nil := List.eq_nil_of_length_eq_zero (by
    rw [hb₂.1]; simp [swapNet, ECDSAAdd.measurementCount_append, WideBank8.Fast16.swapLayer_meas])
  change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
  rw [hb₁ _ st (h1 a st hs), map_smul, hb₂.2, hm0, hh0]
  simp [smul_smul]

end SS3

/-! ### Part 2: Fused 3-pass `[site2, zrep, cornerNeg, corner]` wires, ports, and arithmetic -/

def extra0Wires : List Wire := List.range' 14849 17
def extra1Wires : List Wire := List.range' 14884 95
def extra2Wires : List Wire := List.range' 15399 143
def cyTailWires : List Wire := List.range' 15399 255
def p0ClearWires : List Wire := cyTailWires ++ extra0Wires
def keepWires : List Wire := cxWord ++ [14883]
def finalClearWires : List Wire := scrShortWires ++ cxWord ++ [14883]
def yTail : List Wire := streamLayout.point.y.drop 1

theorem extra0Wires_len : extra0Wires.length = 17 := by simp [extra0Wires]
theorem extra1Wires_len : extra1Wires.length = 95 := by simp [extra1Wires]
theorem extra2Wires_len : extra2Wires.length = 143 := by simp [extra2Wires]
theorem cyTailWires_len : cyTailWires.length = 255 := by simp [cyTailWires]
theorem cyTailWires_eq : cyTailWires = scrDExtraWires := scrDExtraWires_explicit.symm
theorem p0ClearWires_len : p0ClearWires.length = 272 := by simp [p0ClearWires, cyTailWires_len, extra0Wires_len]
theorem finalClearWires_len : finalClearWires.length = 515 := by
  have h1 : scrShortWires.length = 258 := scrShortWires_length
  simp [finalClearWires, cxWord, h1]
theorem yTail_eq : yTail = List.range' 581 255 := by
  simp [yTail, streamLayout_point, List.range'_succ]
theorem yTail_len : yTail.length = 255 := by rw [yTail_eq]; simp
theorem yTail_split : yTail = yTail.take 17 ++ (yTail.drop 17).take 95 ++ yTail.drop 112 := by
  have h2 : (yTail.drop 17).take 95 ++ yTail.drop 112 = yTail.drop 17 := by
    rw [show (112 : Nat) = 17 + 95 from rfl, ← List.drop_drop]
    exact List.take_append_drop 95 (yTail.drop 17)
  rw [List.append_assoc, h2, List.take_append_drop]

def extra0Ports (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  retarget ((scrDExtraBits rows).take 17) extra0Wires

def extra1Ports (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  retarget (((scrDExtraBits rows).drop 17).take 95) extra1Wires

def extra2Ports (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  retarget ((scrDExtraBits rows).drop 112) extra2Wires

def shortOutPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  retarget (scrShortBits rows) scrShortWires

def p0Ports (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  site2Ports rows ++ extra0Ports rows

def p1Ports (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  extra1Ports rows

def p2Ports (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  shortOutPorts rows ++ extra2Ports rows

def p0ClearPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  negYExtraPorts rows ++ extra0Ports rows

def finalClearPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  shortOutPorts rows ++ indexedPorts cxWord (wFields rows .x) true ++
    [⟨wBit rows .y 0, false, streamLayout.core.poolWire 768⟩]

theorem extra0Ports_targets (rows : Nat → Fin 32768) : portTargets (extra0Ports rows) = extra0Wires :=
  retarget_targets _ _ (by simp [scrDExtraBits_length, extra0Wires_len])

theorem extra1Ports_targets (rows : Nat → Fin 32768) : portTargets (extra1Ports rows) = extra1Wires :=
  retarget_targets _ _ (by simp [scrDExtraBits_length, extra1Wires_len])

theorem extra2Ports_targets (rows : Nat → Fin 32768) : portTargets (extra2Ports rows) = extra2Wires :=
  retarget_targets _ _ (by simp [scrDExtraBits_length, extra2Wires_len])

theorem shortOutPorts_targets (rows : Nat → Fin 32768) : portTargets (shortOutPorts rows) = scrShortWires :=
  retarget_targets _ _ ((scrShortBits_length rows).trans scrShortWires_length.symm)

theorem p0Ports_targets (rows : Nat → Fin 32768) : portTargets (p0Ports rows) = site2Wires ++ extra0Wires := by
  simp only [p0Ports, portTargets, List.map_append]
  exact congrArg₂ (· ++ ·) (site2Ports_targets rows) (extra0Ports_targets rows)

theorem p1Ports_targets (rows : Nat → Fin 32768) : portTargets (p1Ports rows) = extra1Wires :=
  extra1Ports_targets rows

theorem p2Ports_targets (rows : Nat → Fin 32768) : portTargets (p2Ports rows) = scrShortWires ++ extra2Wires := by
  simp only [p2Ports, portTargets, List.map_append]
  exact congrArg₂ (· ++ ·) (shortOutPorts_targets rows) (extra2Ports_targets rows)

theorem p0ClearPorts_targets (rows : Nat → Fin 32768) : portTargets (p0ClearPorts rows) = p0ClearWires := by
  simp only [p0ClearPorts, portTargets, List.map_append, p0ClearWires, cyTailWires_eq]
  exact congrArg₂ (· ++ ·) (negYExtra_targets rows) (extra0Ports_targets rows)

theorem finalClearPorts_targets (rows : Nat → Fin 32768) : portTargets (finalClearPorts rows) = finalClearWires := by
  have h1 := shortOutPorts_targets rows
  have h2 := indexed_targets cxWord (wFields rows .x) true
  have h768 : streamLayout.core.poolWire 768 = 14883 := poolWire_eq 768 (by norm_num)
  simp only [finalClearPorts, portTargets, List.map_append, List.map_cons, List.map_nil, finalClearWires] at h1 h2 ⊢
  rw [h1, h2, h768]

theorem p0Ports_length (rows : Nat → Fin 32768) : (p0Ports rows).length = 529 := by
  have h := congrArg List.length (p0Ports_targets rows)
  have hs : site2Wires.length = 512 := by simp [site2Wires, cxWord, cyWord]
  simpa [portTargets, hs, extra0Wires_len] using h

theorem p1Ports_length (rows : Nat → Fin 32768) : (p1Ports rows).length = 95 := by
  have h := congrArg List.length (p1Ports_targets rows)
  simpa [portTargets, extra1Wires_len] using h

theorem p2Ports_length (rows : Nat → Fin 32768) : (p2Ports rows).length = 401 := by
  have h := congrArg List.length (p2Ports_targets rows)
  simpa [portTargets, scrShortWires_length, extra2Wires_len] using h

theorem extra0Ports_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (extra0Ports rows) a = (portBits read (scrDExtraBits rows) a).take 17 := by
  rw [extra0Ports, retarget_bits _ _ _ (by simp [scrDExtraBits_length, extra0Wires_len])]
  simp [portBits, List.map_take]

theorem extra1Ports_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (extra1Ports rows) a = ((portBits read (scrDExtraBits rows) a).drop 17).take 95 := by
  rw [extra1Ports, retarget_bits _ _ _ (by simp [scrDExtraBits_length, extra1Wires_len])]
  simp [portBits, List.map_take, List.map_drop]

theorem extra2Ports_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (extra2Ports rows) a = (portBits read (scrDExtraBits rows) a).drop 112 := by
  rw [extra2Ports, retarget_bits _ _ _ (by simp [scrDExtraBits_length, extra2Wires_len])]
  simp [portBits, List.map_drop]

theorem shortOutPorts_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (shortOutPorts rows) a = portBits read (scrShortBits rows) a :=
  retarget_bits read _ _ ((scrShortBits_length rows).trans scrShortWires_length.symm) a

def scrCWriteFused : ECDSAAdd.Program :=
  [.CX streamLayout.doubleSelect streamLayout.point.finite] ++
  ccxList streamLayout.doubleSelect cxWord streamLayout.point.x ++
  ccxList streamLayout.doubleSelect cyWord streamLayout.point.y

def cornerNegProg : ECDSAAdd.Program := scrNegE ++ (scrNegP ++ scrNegE)

def cornerA1Prog : ECDSAAdd.Program :=
  scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++
    (scrSw1 ++ (scrW1 ++ (scrCWrite ++ scrW2))))

def cornerA2Prog : ECDSAAdd.Program :=
  scrNegP ++ (pointDialogGenericFlag streamLayout ++
   (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
    (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets))))))

def lit0 : ECDSAAdd.Program :=
  xAddProg ++ negYProg ++ yAddProg ++ ECDSAAdd.Frontier.zrep streamLayout ++ cornerNegProg ++
  (scrW1 ++ scrCWriteFused ++ scrW2) ++ negYProg ++
  (scrSw1 ++ ccxList streamLayout.core.equalNegY extra0Wires (yTail.take 17) ++ scrSw1)

def lit1 : ECDSAAdd.Program :=
  scrSw1 ++ ccxList streamLayout.core.equalNegY extra1Wires ((yTail.drop 17).take 95) ++ scrSw1

def lit2a : ECDSAAdd.Program :=
  scrSw1 ++ ccxList streamLayout.core.equalNegY (scrShortWires ++ extra2Wires) (scrShortTargets ++ yTail.drop 112) ++ scrSw1

def lit2b : ECDSAAdd.Program :=
  [.CX windowRoot 14373] ++ cornerA2Prog ++ [.CX windowRoot 14373]

attribute [local irreducible] scrCWriteFused cornerNegProg cornerA1Prog cornerA2Prog
  scrCWrite scrW1 scrW2 scrSw1 scrNegE pointDialogGenericFlag

/-! ### Disjointness, physicality, counts, and support of `lit0`, `lit1`, `lit2a`, `lit2b` -/

theorem ccxList_toff (c : Wire) (S T : List Wire) :
    ECDSAAdd.toffoliCount (ccxList c S T) = min S.length T.length := by
  induction S generalizing T with
  | nil => simp [ccxList, ECDSAAdd.toffoliCount]
  | cons a S ih =>
    cases T with
    | nil => simp [ccxList, ECDSAAdd.toffoliCount]
    | cons t T =>
      simp only [ccxList, ECDSAAdd.toffoliCount, ih T, List.length_cons]
      omega

theorem ccxList_slots (c : Wire) (S T : List Wire) :
    ECDSAAdd.Challenge.gateSlots (ccxList c S T) = min S.length T.length := by
  induction S generalizing T with
  | nil => simp [ccxList, ECDSAAdd.Challenge.gateSlots]
  | cons a S ih =>
    cases T with
    | nil => simp [ccxList, ECDSAAdd.Challenge.gateSlots]
    | cons t T =>
      have hs : ECDSAAdd.Challenge.gateSlots (.CCX c a t :: ccxList c S T) =
          1 + ECDSAAdd.Challenge.gateSlots (ccxList c S T) := by
        simp [ECDSAAdd.Challenge.gateSlots, ECDSAAdd.Challenge.instructionSlots]
      rw [ccxList, hs, ih T, List.length_cons, List.length_cons]
      omega

theorem ccxList_meas (c : Wire) (S T : List Wire) :
    ECDSAAdd.measurementCount (ccxList c S T) = 0 := ccxList_records c S T

theorem ccxList_norm_toff (c : Wire) (S T : List Wire) (hc : c ∉ S) :
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (ccxList c S T)) = min S.length T.length := by
  have hrc : ECDSAAdd.Baselines.repeatedControls (ccxList c S T) = 0 := by
    induction S generalizing T with
    | nil => rfl
    | cons a S ih =>
      cases T with
      | nil => rfl
      | cons t T =>
        have hne : c ≠ a := fun e => hc (e ▸ List.mem_cons_self)
        simp [ccxList, ECDSAAdd.Baselines.repeatedControls, hne, ih T (fun h => hc (List.mem_cons_of_mem _ h))]
  have h := ECDSAAdd.Baselines.normalize_toffoli_exact (ccxList c S T)
  rw [hrc, Nat.add_zero, ccxList_toff] at h; exact h

attribute [local irreducible] ccxList cxList

private theorem point_x_len : streamLayout.point.x.length = 256 := by
  rw [streamLayout_point, List.length_range']

private theorem point_y_len : streamLayout.point.y.length = 256 := by
  rw [streamLayout_point, List.length_range']

private theorem scrDTargets_len : scrDTargets.length = 513 := by
  rw [scrDTargets, List.cons_append, List.length_cons, List.length_append, point_x_len, point_y_len]

private theorem cx_toff (a t : Wire) : ECDSAAdd.toffoliCount ([.CX a t] : ECDSAAdd.Program) = 0 := rfl
private theorem cx_meas (a t : Wire) : ECDSAAdd.measurementCount ([.CX a t] : ECDSAAdd.Program) = 0 := rfl
private theorem cx_slots (a t : Wire) : ECDSAAdd.Challenge.gateSlots ([.CX a t] : ECDSAAdd.Program) = 1 := rfl
private theorem cx3_toff (a b c t : Wire) :
    ECDSAAdd.toffoliCount ([.CX a t, .CX b t, .CX c t] : ECDSAAdd.Program) = 0 := rfl
private theorem cx3_meas (a b c t : Wire) :
    ECDSAAdd.measurementCount ([.CX a t, .CX b t, .CX c t] : ECDSAAdd.Program) = 0 := rfl
private theorem cx_norm_toff (a t : Wire) :
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram [.CX a t]) = 0 := by
  unfold ECDSAAdd.Baselines.normalizeProgram; rfl
private theorem cx3_norm_toff (a b c t : Wire) :
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram [.CX a t, .CX b t, .CX c t]) = 0 := by
  unfold ECDSAAdd.Baselines.normalizeProgram; rfl

theorem scrCWriteFused_toff : ECDSAAdd.toffoliCount scrCWriteFused = 512 := by
  rw [scrCWriteFused, ECDSAAdd.toffoliCount_append, ECDSAAdd.toffoliCount_append, cx_toff, ccxList_toff, ccxList_toff]
  simp only [cxWord, cyWord, List.length_cons, List.length_range', point_x_len, point_y_len]
  decide

theorem scrCWrite_toff : ECDSAAdd.toffoliCount scrCWrite = 513 := by
  have hc : cSources.length = 513 := by
    rw [cSources, List.length_append, List.length_take, scrPairWires_length, yWires_length]; decide
  rw [scrCWrite, ccxList_toff, hc, scrDTargets_len]; decide

theorem scrCWriteFused_meas : ECDSAAdd.measurementCount scrCWriteFused = 0 := by
  rw [scrCWriteFused, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount_append, cx_meas, ccxList_meas, ccxList_meas]

theorem scrCWriteFused_slots : ECDSAAdd.Challenge.gateSlots scrCWriteFused = 513 := by
  rw [scrCWriteFused, ECDSAAdd.Challenge.gateSlots_append, ECDSAAdd.Challenge.gateSlots_append, cx_slots, ccxList_slots, ccxList_slots]
  simp only [cxWord, cyWord, List.length_cons, List.length_range', point_x_len, point_y_len]
  decide

theorem lit1_meas : ECDSAAdd.measurementCount lit1 = 0 := by
  have hsw : ECDSAAdd.measurementCount scrSw1 = 0 := by unfold scrSw1; exact cx_meas _ _
  rw [lit1, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount_append, hsw, ccxList_meas]

theorem lit2a_meas : ECDSAAdd.measurementCount lit2a = 0 := by
  have hsw : ECDSAAdd.measurementCount scrSw1 = 0 := by unfold scrSw1; exact cx_meas _ _
  rw [lit2a, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount_append, hsw, ccxList_meas]

theorem lit0_meas : ECDSAAdd.measurementCount lit0 =
    ECDSAAdd.measurementCount pair2Prog + ECDSAAdd.measurementCount cornerNegProg := by
  have hz : ECDSAAdd.measurementCount (ECDSAAdd.Frontier.zrep streamLayout) = 0 := zrep_records
  have hw1 : ECDSAAdd.measurementCount scrW1 = 0 := by unfold scrW1; exact cx3_meas _ _ _ _
  have hw2 : ECDSAAdd.measurementCount scrW2 = 0 := by unfold scrW2; exact cx3_meas _ _ _ _
  have hsw : ECDSAAdd.measurementCount scrSw1 = 0 := by unfold scrSw1; exact cx_meas _ _
  have hp2 : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
  rw [lit0, hp2]
  simp only [ECDSAAdd.measurementCount_append, hz, hw1, hw2, hsw, scrCWriteFused_meas, ccxList_meas]
  generalize ECDSAAdd.measurementCount xAddProg = a
  generalize ECDSAAdd.measurementCount negYProg = b
  generalize ECDSAAdd.measurementCount yAddProg = c
  generalize ECDSAAdd.measurementCount cornerNegProg = d
  omega

theorem lit2b_meas : ECDSAAdd.measurementCount lit2b = ECDSAAdd.measurementCount cornerA2Prog := by
  rw [lit2b, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount_append, cx_meas]
  generalize ECDSAAdd.measurementCount cornerA2Prog = a
  omega

theorem cornerA1Prog_meas : ECDSAAdd.measurementCount cornerA1Prog = 0 := by
  have hsw : ECDSAAdd.measurementCount scrSw1 = 0 := by unfold scrSw1; exact cx_meas _ _
  have hw1 : ECDSAAdd.measurementCount scrW1 = 0 := by unfold scrW1; exact cx3_meas _ _ _ _
  have hw2 : ECDSAAdd.measurementCount scrW2 = 0 := by unfold scrW2; exact cx3_meas _ _ _ _
  have hcw : ECDSAAdd.measurementCount scrCWrite = 0 := by unfold scrCWrite; exact ccxList_meas _ _ _
  rw [cornerA1Prog]
  simp only [ECDSAAdd.measurementCount_append, hsw, hw1, hw2, hcw, ccxList_meas]

theorem corner_toff_split :
    ECDSAAdd.toffoliCount lit0 + ECDSAAdd.toffoliCount lit1 +
      ECDSAAdd.toffoliCount lit2a + ECDSAAdd.toffoliCount lit2b + 1 =
    ECDSAAdd.toffoliCount pair2Prog + ECDSAAdd.toffoliCount (ECDSAAdd.Frontier.zrep streamLayout) +
      ECDSAAdd.toffoliCount cornerNegProg + ECDSAAdd.toffoliCount cornerA1Prog +
      ECDSAAdd.toffoliCount cornerA2Prog := by
  have hp2 : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
  have hw1 : ECDSAAdd.toffoliCount scrW1 = 0 := by unfold scrW1; exact cx3_toff _ _ _ _
  have hw2 : ECDSAAdd.toffoliCount scrW2 = 0 := by unfold scrW2; exact cx3_toff _ _ _ _
  have hsw : ECDSAAdd.toffoliCount scrSw1 = 0 := by unfold scrSw1; exact cx_toff _ _
  have hcx : ECDSAAdd.toffoliCount ([.CX windowRoot 14373] : ECDSAAdd.Program) = 0 := cx_toff _ _
  have hdw : scrDWires.length = 513 := by simp [scrDWires, scrShortWires_length, scrDExtraWires_length]
  have hsT : scrShortTargets.length = 258 := by rw [scrShortTargets_eq]; simp
  rw [lit0, lit1, lit2a, lit2b, hp2, cornerA1Prog]
  simp only [ECDSAAdd.toffoliCount_append, hw1, hw2, hsw, hcx,
    scrCWriteFused_toff, scrCWrite_toff, ccxList_toff,
    List.length_append, List.length_take, List.length_drop,
    hdw, scrDTargets_len, extra0Wires_len, extra1Wires_len, extra2Wires_len,
    scrShortWires_length, hsT, yTail_len]
  generalize ECDSAAdd.toffoliCount xAddProg = t1
  generalize ECDSAAdd.toffoliCount negYProg = t2
  generalize ECDSAAdd.toffoliCount yAddProg = t3
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Frontier.zrep streamLayout) = t4
  generalize ECDSAAdd.toffoliCount cornerNegProg = t5
  generalize ECDSAAdd.toffoliCount cornerA2Prog = t6
  omega

theorem norm_toff_split_corner :
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram lit0) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram lit1) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram lit2a) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram lit2b) + 1 =
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram pair2Prog) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (ECDSAAdd.Frontier.zrep streamLayout)) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerNegProg) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA1Prog) +
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA2Prog) := by
  have hna (p q : ECDSAAdd.Program) :
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (p ++ q)) =
        ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram p) +
        ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram q) := by
    have he : ECDSAAdd.Baselines.normalizeProgram (p ++ q) =
        ECDSAAdd.Baselines.normalizeProgram p ++ ECDSAAdd.Baselines.normalizeProgram q := by
      unfold ECDSAAdd.Baselines.normalizeProgram; simp
    rw [he, ECDSAAdd.toffoliCount_append]
  have hp2 : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
  have hw1 : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram scrW1) = 0 := by unfold scrW1; exact cx3_norm_toff _ _ _ _
  have hw2 : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram scrW2) = 0 := by unfold scrW2; exact cx3_norm_toff _ _ _ _
  have hsw : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram scrSw1) = 0 := by unfold scrSw1; exact cx_norm_toff _ _
  have hcx : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram ([.CX windowRoot 14373] : ECDSAAdd.Program)) = 0 := cx_norm_toff _ _
  have hcf : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram scrCWriteFused) = 512 := by
    rw [scrCWriteFused, hna, hna, cx_norm_toff,
      ccxList_norm_toff _ _ _ (fun hm => by simp only [cxWord, sl_doubleSelect, List.mem_range'_1] at hm; omega),
      ccxList_norm_toff _ _ _ (fun hm => by simp only [cyWord, sl_doubleSelect, List.mem_cons, List.mem_range'_1] at hm; (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega)]
    simp only [cxWord, cyWord, List.length_cons, List.length_range', point_x_len, point_y_len]; decide
  have hcW : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram scrCWrite) = 513 := by
    rw [scrCWrite, ccxList_norm_toff _ _ _ doubleSelect_cSources]
    have hc : cSources.length = 513 := by
      rw [cSources, List.length_append, List.length_take, scrPairWires_length, yWires_length]; decide
    rw [hc, scrDTargets_len]; decide
  have hD : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (ccxList streamLayout.core.equalNegY scrDWires scrDTargets)) = 513 := by
    rw [ccxList_norm_toff _ _ _ (fun hm => by
      rcases List.mem_append.mp hm with h | h
      · exact scrShortWires_no_flags.2.2.2 h
      · rw [scrDExtraWires_explicit, sl_equalNegY, List.mem_range'_1] at h; omega)]
    have h1 : scrDWires.length = 513 := by simp [scrDWires, scrShortWires_length, scrDExtraWires_length]
    rw [h1, scrDTargets_len]; decide
  have hc0 : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (ccxList streamLayout.core.equalNegY extra0Wires (yTail.take 17))) = 17 := by
    rw [ccxList_norm_toff _ _ _ (fun hm => by simp only [extra0Wires, sl_equalNegY, List.mem_range'_1] at hm; omega),
      extra0Wires_len, List.length_take, yTail_len]; decide
  have hc1 : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (ccxList streamLayout.core.equalNegY extra1Wires ((yTail.drop 17).take 95))) = 95 := by
    rw [ccxList_norm_toff _ _ _ (fun hm => by simp only [extra1Wires, sl_equalNegY, List.mem_range'_1] at hm; omega),
      extra1Wires_len, List.length_take, List.length_drop, yTail_len]; decide
  have hc2 : ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (ccxList streamLayout.core.equalNegY (scrShortWires ++ extra2Wires) (scrShortTargets ++ yTail.drop 112))) = 401 := by
    have hsT : scrShortTargets.length = 258 := by rw [scrShortTargets_eq]; simp
    rw [ccxList_norm_toff _ _ _ (fun hm => by
      rcases List.mem_append.mp hm with h | h
      · exact scrShortWires_no_flags.2.2.2 h
      · simp only [extra2Wires, sl_equalNegY, List.mem_range'_1] at h; omega),
      List.length_append, List.length_append, scrShortWires_length, extra2Wires_len, hsT, List.length_drop, yTail_len]; decide
  rw [lit0, lit1, lit2a, lit2b, hp2, cornerA1Prog]
  simp only [hna, hw1, hw2, hsw, hcx, hcf, hcW]
  rw [hc0, hc1, hc2, hD]
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram xAddProg) = t1
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram negYProg) = t2
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram yAddProg) = t3
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (ECDSAAdd.Frontier.zrep streamLayout)) = t4
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerNegProg) = t5
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA2Prog) = t6
  omega

theorem corner_slots_le :
    ECDSAAdd.Challenge.gateSlots lit0 + ECDSAAdd.Challenge.gateSlots lit1 +
      ECDSAAdd.Challenge.gateSlots lit2a + ECDSAAdd.Challenge.gateSlots lit2b ≤
    ECDSAAdd.Challenge.gateSlots pair2Prog + ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Frontier.zrep streamLayout) +
      ECDSAAdd.Challenge.gateSlots cornerNegProg + ECDSAAdd.Challenge.gateSlots cornerA1Prog +
      ECDSAAdd.Challenge.gateSlots cornerA2Prog + 20 := by
  have hp2 : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
  have hdw : scrDWires.length = 513 := by simp [scrDWires, scrShortWires_length, scrDExtraWires_length]
  have hsT : scrShortTargets.length = 258 := by rw [scrShortTargets_eq]; simp
  have hC : ECDSAAdd.Challenge.gateSlots scrCWrite = 513 := by
    have hc : cSources.length = 513 := by
      rw [cSources, List.length_append, List.length_take, scrPairWires_length, yWires_length]; decide
    rw [scrCWrite, ccxList_slots, hc, scrDTargets_len]; decide
  have hsw : ECDSAAdd.Challenge.gateSlots scrSw1 = 1 := by unfold scrSw1; exact cx_slots _ _
  have hcx : ECDSAAdd.Challenge.gateSlots ([.CX windowRoot 14373] : ECDSAAdd.Program) = 1 := cx_slots _ _
  have hw1 : ECDSAAdd.Challenge.gateSlots scrW1 = 3 := by
    have h : ∀ a b c t : Wire, ECDSAAdd.Challenge.gateSlots ([.CX a t, .CX b t, .CX c t] : ECDSAAdd.Program) = 3 := fun _ _ _ _ => rfl
    unfold scrW1; exact h _ _ _ _
  have hw2 : ECDSAAdd.Challenge.gateSlots scrW2 = 3 := by
    have h : ∀ a b c t : Wire, ECDSAAdd.Challenge.gateSlots ([.CX a t, .CX b t, .CX c t] : ECDSAAdd.Program) = 3 := fun _ _ _ _ => rfl
    unfold scrW2; exact h _ _ _ _
  rw [lit0, lit1, lit2a, lit2b, hp2, cornerA1Prog]
  simp only [ECDSAAdd.Challenge.gateSlots_append, hsw, hw1, hw2, hcx,
    scrCWriteFused_slots, ccxList_slots, hC,
    List.length_append, List.length_take, List.length_drop,
    hdw, scrDTargets_len, extra0Wires_len, extra1Wires_len, extra2Wires_len,
    scrShortWires_length, hsT, yTail_len]
  generalize ECDSAAdd.Challenge.gateSlots xAddProg = g1
  generalize ECDSAAdd.Challenge.gateSlots negYProg = g2
  generalize ECDSAAdd.Challenge.gateSlots yAddProg = g3
  generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Frontier.zrep streamLayout) = g4
  generalize ECDSAAdd.Challenge.gateSlots cornerNegProg = g5
  generalize ECDSAAdd.Challenge.gateSlots cornerA2Prog = g6
  omega

/-! ### Physicality and support of `lit0`, `lit1`, `lit2a`, `lit2b` -/

theorem pair2Prog_physical : GatePhysical pair2Prog := by
  apply WEXUnlookup.rowC_physical pair2Prog
  have hmem := WEXFast.site2_unit_mem
  have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by unfold WEXUnlookup.rowC; rfl
  rw [erase2]
  refine List.mem_flatMap.mpr ⟨Block2.unit (WEXFast.siteUnit (site2 probeRows)), hmem, ?_⟩
  simp [Block2.code, UnitSite.code, WEXFast.siteUnit, site2, MaskedSite.prefix, wLiteral]

theorem zrep_physical : GatePhysical (ECDSAAdd.Frontier.zrep streamLayout) := by
  intro i hi
  apply Site1Fast.site1Arith_physical i
  rw [site1Arith_eq]
  simp [hi]

theorem cornerNeg_physical : GatePhysical cornerNegProg := by
  have hmem : Block2.plain cornerNeg ∈ WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by unfold WEXUnlookup.rowC; rfl
    rw [h1]; apply List.mem_append_right; simp [WEXUnlookup.rowPost3]
  have hp : ∀ p, WInstr.literal p ∈ cornerNeg → GatePhysical p := fun p hp =>
    WEXUnlookup.rowC_physical p (List.mem_flatMap.mpr ⟨.plain cornerNeg, hmem, hp⟩)
  intro i hi
  simp only [cornerNegProg, List.mem_append] at hi
  rcases hi with hi | hi | hi
  · exact hp scrNegE (by simp [cornerNeg, wLiteral]) i hi
  · exact hp scrNegP (by simp [cornerNeg, wLiteral]) i hi
  · exact hp scrNegE (by simp [cornerNeg, wLiteral]) i hi

theorem wZeroWith_litOnly {n : Nat} (tail : Wire → WCode n)
    (ht : ∀ w, ∀ i ∈ tail w, ∃ p, i = .literal p) (c : Wire) (bs : List ZeroBit) :
    ∀ i ∈ wZeroWith tail c bs, ∃ p, i = .literal p := by
  induction bs generalizing c with
  | nil => exact ht c
  | cons b bs ih =>
    intro i hi
    simp only [wZeroWith, wLiteral, List.mem_append, List.mem_singleton] at hi
    rcases hi with (rfl | hi) | rfl
    · exact ⟨_, rfl⟩
    · exact ih b.work i hi
    · exact ⟨_, rfl⟩

theorem cornerA2_litOnly : ∀ i ∈ cornerA2, ∃ p, i = .literal p := by
  intro i hi
  simp only [cornerA2, scrDMiddle, wLiteral, List.mem_append, List.mem_singleton] at hi
  rcases hi with (rfl | rfl) | (((((rfl | hi) | rfl) | rfl) | rfl) | rfl)
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact wZeroWith_litOnly _ (fun w j hj => by simp [wPairTailBare, wLiteral] at hj; exact ⟨_, hj⟩) _ _ i hi
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem cornerA2Prog_eq_litProg : cornerA2Prog = litProg cornerA2 := by
  have h1 := cornerA2_inst (fun _ => false) 0
  have h2 := litProg_inst (fun _ => false) cornerA2 0 cornerA2_litOnly
  unfold cornerA2Prog
  exact h1.symm.trans h2

theorem cornerA2Prog_physical : GatePhysical cornerA2Prog := by
  rw [cornerA2Prog_eq_litProg]
  have hmem : Block2.unit WEXUnlookup.cornerUnit₂ ∈ WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by unfold WEXUnlookup.rowC; rfl
    rw [h1]; apply List.mem_append_right; simp [WEXUnlookup.rowPost3]
  have hp : ∀ p, WInstr.literal p ∈ cornerA2 → GatePhysical p := fun p hp =>
    WEXUnlookup.rowC_physical p (List.mem_flatMap.mpr ⟨.unit WEXUnlookup.cornerUnit₂, hmem,
      by simp [Block2.code, UnitSite.code, WEXUnlookup.cornerUnit₂, hp]⟩)
  have aux : ∀ (c : WCode 32768), (∀ p, WInstr.literal p ∈ c → GatePhysical p) → GatePhysical (litProg c) := by
    intro c hc
    induction c with
    | nil => intro i hi; cases hi
    | cons x xs ih =>
      cases x with
      | literal p =>
        intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact hc p List.mem_cons_self i hi
        · exact ih (fun q hq => hc q (List.mem_cons_of_mem _ hq)) i hi
      | lookup _ _ => exact ih (fun q hq => hc q (List.mem_cons_of_mem _ hq))
  exact aux cornerA2 hp

theorem scrCWriteFused_physical : GatePhysical scrCWriteFused := by
  have h1 : GatePhysical ([.CX streamLayout.doubleSelect streamLayout.point.finite] : ECDSAAdd.Program) := by
    intro i hi; simp only [List.mem_singleton] at hi; subst hi
    simp [ECDSAAdd.RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, sl_doubleSelect, streamLayout_point]
  have h2 : GatePhysical (ccxList streamLayout.doubleSelect cxWord streamLayout.point.x) := by
    apply ccxList_physical
    · intro a ha hm
      simp only [cxWord, streamLayout_point, List.mem_range'_1] at ha hm
      omega
    · intro hm; simp only [cxWord, sl_doubleSelect, List.mem_range'_1] at hm; omega
    · intro hm; simp only [streamLayout_point, sl_doubleSelect, List.mem_range'_1] at hm; omega
  have h3 : GatePhysical (ccxList streamLayout.doubleSelect cyWord streamLayout.point.y) := by
    apply ccxList_physical
    · intro a ha hm
      simp only [cyWord, streamLayout_point, List.mem_cons, List.mem_range'_1] at ha hm
      (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega
    · intro hm; simp only [cyWord, sl_doubleSelect, List.mem_cons, List.mem_range'_1] at hm; (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega
    · intro hm; simp only [streamLayout_point, sl_doubleSelect, List.mem_range'_1] at hm; omega
  intro i hi
  simp only [scrCWriteFused, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact h1 i hi
  · exact h2 i hi
  · exact h3 i hi

theorem scrSw1_physical : GatePhysical scrSw1 := by
  intro i hi; simp only [scrSw1, List.mem_singleton] at hi; subst hi
  simp [ECDSAAdd.RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, sl_doubleSelect, sl_equalNegY]

theorem scrW1_physical : GatePhysical scrW1 := by
  intro i hi
  simp only [scrW1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;>
    simp [ECDSAAdd.RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl]

theorem scrW2_physical : GatePhysical scrW2 := by
  intro i hi
  simp only [scrW2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;>
    simp [ECDSAAdd.RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl]

theorem lit0_physical : GatePhysical lit0 := by
  have hp2 := pair2Prog_physical
  have hp2' : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
  rw [hp2'] at hp2
  have hc0 : GatePhysical (ccxList streamLayout.core.equalNegY extra0Wires (yTail.take 17)) := by
    apply ccxList_physical
    · intro a ha hm
      have hm' := List.mem_of_mem_take hm
      simp only [extra0Wires, yTail_eq, List.mem_range'_1] at ha hm'
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · intro hm; simp only [extra0Wires, sl_equalNegY, List.mem_range'_1] at hm; omega
    · intro hm; have hm' := List.mem_of_mem_take hm
      simp only [yTail_eq, sl_equalNegY, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  intro i hi
  simp only [lit0, List.mem_append] at hi
  rcases hi with ((((((hi | hi) | hi) | hi) | hi) | (hi | hi) | hi) | hi) | (hi | hi) | hi
  · exact hp2 i (by simp [hi])
  · exact hp2 i (by simp [hi])
  · exact hp2 i (by simp [hi])
  · exact zrep_physical i hi
  · exact cornerNeg_physical i hi
  · exact scrW1_physical i hi
  · exact scrCWriteFused_physical i hi
  · exact scrW2_physical i hi
  · exact hp2 i (by simp [hi])
  · exact scrSw1_physical i hi
  · exact hc0 i hi
  · exact scrSw1_physical i hi

theorem lit1_physical : GatePhysical lit1 := by
  have hc1 : GatePhysical (ccxList streamLayout.core.equalNegY extra1Wires ((yTail.drop 17).take 95)) := by
    apply ccxList_physical
    · intro a ha hm
      have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm)
      simp only [extra1Wires, yTail_eq, List.mem_range'_1] at ha hm'
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · intro hm; simp only [extra1Wires, sl_equalNegY, List.mem_range'_1] at hm; omega
    · intro hm; have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm)
      simp only [yTail_eq, sl_equalNegY, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  intro i hi
  simp only [lit1, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact scrSw1_physical i hi
  · exact hc1 i hi
  · exact scrSw1_physical i hi

theorem lit2a_physical : GatePhysical lit2a := by
  have hc2 : GatePhysical (ccxList streamLayout.core.equalNegY (scrShortWires ++ extra2Wires) (scrShortTargets ++ yTail.drop 112)) := by
    apply ccxList_physical
    · intro a ha hm
      have ha' : (14884 ≤ a ∧ a < 15142) ∨ (15399 ≤ a ∧ a < 15542) := by
        rcases List.mem_append.mp ha with ha | ha
        · left; exact shortWires_bounds a ha
        · right; simp only [extra2Wires, List.mem_range'_1] at ha; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      rcases List.mem_append.mp hm with hm | hm
      · rw [scrShortTargets_eq] at hm
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hm
        (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega
      · have hm' := List.mem_of_mem_drop hm
        simp only [yTail_eq, List.mem_range'_1] at hm'
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact scrShortWires_no_flags.2.2.2 hm
      · simp only [extra2Wires, sl_equalNegY, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact shortTargets_no_flags.2.2.2 hm
      · have hm' := List.mem_of_mem_drop hm
        simp only [yTail_eq, sl_equalNegY, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  intro i hi
  simp only [lit2a, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact scrSw1_physical i hi
  · exact hc2 i hi
  · exact scrSw1_physical i hi

theorem lit2b_physical : GatePhysical lit2b := by
  intro i hi
  simp only [lit2b, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · simp [ECDSAAdd.RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, windowRoot]
  · exact cornerA2Prog_physical i hi
  · simp [ECDSAAdd.RecordedQuantum.PhysicalInstr, ECDSAAdd.ProperGate, windowRoot]

/-! ### Support of `lit0`, `lit1`, `lit2a`, `lit2b` inside `WideBank8.Fast16.Tight.support` -/

theorem mem_newH7_of_band {w : Wire}
    (h : (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 836) ∨ w = 838 ∨ w = 836 ∨ w = 10015 ∨
      (14111 ≤ w ∧ w < 14630) ∨ (14832 ≤ w ∧ w < 14874) ∨ (14883 ≤ w ∧ w < 15144) ∨
      (15399 ≤ w ∧ w < 15655) ∨ w = 19814 ∨ w = 19815 ∨ w = 19816) :
    w ∈ PoolHost.newSourceH7 := by
  rw [PoolHost.newSourceH7_mem]
  unfold fixedPort oldWork PoolHost.retiredH7 retiredH retired
  dsimp only [Wire, ECDSAAdd.Wire] at *
  omega

/-! Explicit wire bounds for `lit0`, `lit1`, `lit2a`, `lit2b` in `PoolHost.newSourceH7` (hence `Tight.support`). -/

theorem pair2Prog_wires_newH7 : ECDSAAdd.wires pair2Prog ⊆ PoolHost.newSourceH7.toFinset := by
  intro w hw
  have hsub := List.mem_toFinset.mp (pair2Prog_subset hw)
  apply List.mem_toFinset.mpr
  apply mem_newH7_of_band
  simp only [pair2List, xAdd, yAdd, negYW, MeasuredCanonicalModLayout.wires,
    CompactRecoveryNegateLayout.wires, cxWord, cyWord, addCarry,
    streamLayout_point, sl_generic, List.mem_append, List.mem_cons, List.mem_range'_1,
    List.not_mem_nil, or_false] at hsub
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem zrep_wires_newH7 : ECDSAAdd.wires (ECDSAAdd.Frontier.zrep streamLayout) ⊆ PoolHost.newSourceH7.toFinset := by
  intro w hw
  apply List.mem_toFinset.mpr; apply mem_newH7_of_band
  rcases ECDSAAdd.Frontier.zrep_wires streamLayout w hw with h | h
  · rw [streamLayout_point] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rw [streamLayout_point, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem scrNegP_wires_newH7 : ECDSAAdd.wires scrNegP ⊆ PoolHost.newSourceH7.toFinset := by
  have hsub0 : ECDSAAdd.wires scrNegP ⊆ ((negateYLayout streamLayout).wires streamLayout.core.equalNegY).toFinset := by
    unfold scrNegP
    exact (negateYLayout streamLayout).program_support streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
      (negateYLayout_widths streamLayout streamLayout_widths).2
  intro w hw
  have hmem := List.mem_toFinset.mp (hsub0 hw)
  have hpool := negateYLayout_pool streamLayout streamLayout_widths
  have htake : streamLayout.dialogPool.take 258 = List.range' 14115 258 := pool_take_eq 258 (by decide)
  apply List.mem_toFinset.mpr; apply mem_newH7_of_band
  simp only [CompactRecoveryNegateLayout.wires, List.mem_cons, List.mem_append] at hmem
  rcases hmem with rfl | rfl | rfl | hmem | hmem
  · rw [sl_equalNegY]; dsimp only [Wire, ECDSAAdd.Wire]; omega
  · have hm : (negateYLayout streamLayout).cin ∈ streamLayout.dialogPool.take 258 := by rw [← hpool]; simp
    rw [htake, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · have hm : (negateYLayout streamLayout).zero ∈ streamLayout.dialogPool.take 258 := by rw [← hpool]; simp
    rw [htake, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [negateYLayout, streamLayout_point, List.mem_range'_1] at hmem; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · have hm : w ∈ streamLayout.dialogPool.take 258 := by rw [← hpool]; simp [hmem]
    rw [htake, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem cornerNeg_wires_newH7 : ECDSAAdd.wires cornerNegProg ⊆ PoolHost.newSourceH7.toFinset := by
  intro w hw
  simp only [cornerNegProg, ECDSAAdd.wires_append, Finset.mem_union] at hw
  have hE : ∀ u ∈ ECDSAAdd.wires scrNegE, u ∈ PoolHost.newSourceH7.toFinset := fun u hu => by
    simp only [scrNegE, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_genericSelect, sl_equalNegY] at hu
    apply List.mem_toFinset.mpr; apply mem_newH7_of_band; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  rcases hw with hw | hw | hw
  · exact hE w hw
  · exact scrNegP_wires_newH7 hw
  · exact hE w hw

theorem scrCWriteFused_wires_newH7 : ECDSAAdd.wires scrCWriteFused ⊆ PoolHost.newSourceH7.toFinset := by
  intro w hw
  apply List.mem_toFinset.mpr; apply mem_newH7_of_band
  simp only [scrCWriteFused, ECDSAAdd.wires_append, Finset.mem_union] at hw
  rcases hw with (hw | hw) | hw
  · simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, streamLayout_point] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rcases ccxList_wires _ _ _ _ hw with rfl | hw | hw
    · rw [sl_doubleSelect]; dsimp only [Wire, ECDSAAdd.Wire]; omega
    · simp only [cxWord, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · simp only [streamLayout_point, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rcases ccxList_wires _ _ _ _ hw with rfl | hw | hw
    · rw [sl_doubleSelect]; dsimp only [Wire, ECDSAAdd.Wire]; omega
    · simp only [cyWord, List.mem_cons, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · simp only [streamLayout_point, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem lit0_wires_newH7 : ECDSAAdd.wires lit0 ⊆ PoolHost.newSourceH7.toFinset := by
  have hp2 := pair2Prog_wires_newH7
  have hp2' : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
  rw [hp2'] at hp2
  intro w hw
  simp only [lit0, ECDSAAdd.wires_append, Finset.mem_union] at hw
  have hsw : ∀ u ∈ ECDSAAdd.wires scrSw1, u ∈ PoolHost.newSourceH7.toFinset := fun u hu => by
    simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hu
    apply List.mem_toFinset.mpr; apply mem_newH7_of_band; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hw1 : ∀ u ∈ ECDSAAdd.wires scrW1, u ∈ PoolHost.newSourceH7.toFinset := fun u hu => by
    simp only [scrW1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl] at hu
    apply List.mem_toFinset.mpr; apply mem_newH7_of_band; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hw2 : ∀ u ∈ ECDSAAdd.wires scrW2, u ∈ PoolHost.newSourceH7.toFinset := fun u hu => by
    simp only [scrW2, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl] at hu
    apply List.mem_toFinset.mpr; apply mem_newH7_of_band; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  rcases hw with ((((((hw | hw) | hw) | hw) | hw) | (hw | hw) | hw) | hw) | (hw | hw) | hw
  · exact hp2 (by simp [ECDSAAdd.wires_append, hw])
  · exact hp2 (by simp [ECDSAAdd.wires_append, hw])
  · exact hp2 (by simp [ECDSAAdd.wires_append, hw])
  · exact zrep_wires_newH7 hw
  · exact cornerNeg_wires_newH7 hw
  · exact hw1 w hw
  · exact scrCWriteFused_wires_newH7 hw
  · exact hw2 w hw
  · exact hp2 (by simp [ECDSAAdd.wires_append, hw])
  · exact hsw w hw
  · apply List.mem_toFinset.mpr; apply mem_newH7_of_band
    rcases ccxList_wires _ _ _ _ hw with rfl | hw | hw
    · rw [sl_equalNegY]; dsimp only [Wire, ECDSAAdd.Wire]; omega
    · simp only [extra0Wires, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · have hw' := List.mem_of_mem_take hw
      rw [yTail_eq, List.mem_range'_1] at hw'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · exact hsw w hw

theorem lit1_wires_newH7 : ECDSAAdd.wires lit1 ⊆ PoolHost.newSourceH7.toFinset := by
  intro w hw
  apply List.mem_toFinset.mpr; apply mem_newH7_of_band
  simp only [lit1, ECDSAAdd.wires_append, Finset.mem_union] at hw
  rcases hw with (hw | hw) | hw
  · simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rcases ccxList_wires _ _ _ _ hw with rfl | hw | hw
    · rw [sl_equalNegY]; dsimp only [Wire, ECDSAAdd.Wire]; omega
    · simp only [extra1Wires, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · have hw' := List.mem_of_mem_drop (List.mem_of_mem_take hw)
      rw [yTail_eq, List.mem_range'_1] at hw'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem lit2a_wires_newH7 : ECDSAAdd.wires lit2a ⊆ PoolHost.newSourceH7.toFinset := by
  intro w hw
  apply List.mem_toFinset.mpr; apply mem_newH7_of_band
  simp only [lit2a, ECDSAAdd.wires_append, Finset.mem_union] at hw
  rcases hw with (hw | hw) | hw
  · simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rcases ccxList_wires _ _ _ _ hw with rfl | hw | hw
    · rw [sl_equalNegY]; dsimp only [Wire, ECDSAAdd.Wire]; omega
    · rcases List.mem_append.mp hw with hw | hw
      · have := shortWires_bounds w hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · simp only [extra2Wires, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · rcases List.mem_append.mp hw with hw | hw
      · rw [scrShortTargets_eq] at hw
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hw
        (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega
      · have hw' := List.mem_of_mem_drop hw
        rw [yTail_eq, List.mem_range'_1] at hw'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem cornerA2Prog_wires_newH7 : ECDSAAdd.wires cornerA2Prog ⊆ PoolHost.newSourceH7.toFinset := by
  rw [cornerA2Prog_eq_litProg]
  intro w hw
  obtain ⟨p, hp, hwp⟩ := litProg_wires cornerA2 w hw
  have hunit : Block2.unit WEXUnlookup.cornerUnit₂ ∈ WEXUnlookup.rowC := by
    have h1 : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by unfold WEXUnlookup.rowC; rfl
    rw [h1]; apply List.mem_append_right; simp [WEXUnlookup.rowPost3]
  have hmem : WInstr.literal p ∈ erase2 WEXUnlookup.rowC :=
    List.mem_flatMap.mpr ⟨.unit WEXUnlookup.cornerUnit₂, hunit,
      by simp [Block2.code, UnitSite.code, WEXUnlookup.cornerUnit₂, hp]⟩
  have hno4 := (PoolHost.rowC_unit_no4 _ hunit).1 p (by simp [UnitSite.code, WEXUnlookup.cornerUnit₂, hp]) w hwp
  have hstrict : ¬ (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) := by
    intro hh
    have hm_rowH : WEXFast.HBlock.pair WEXFast.W15G.corner7 ∈ WEXFast.W15G.rowH := by
      rw [WEXFast.W15G.rowH]
      exact List.mem_append_right _ List.mem_cons_self
    have hst := WEXFast.W15G.rowH_strict _ hm_rowH p
      (by simp [WEXFast.HBlock.forgetL, WEXFast.W15G.corner7, erase2, Block2.code, UnitSite.code, WEXUnlookup.cornerUnit₂, hp])
      (by rcases hh with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)))
    obtain ⟨c, hc⟩ := hst; cases hc
  rcases PoolHost.rowC_lit_relaxed7 p hmem w hwp with e | e | e | e | e | e | e | e
  · exact absurd (Or.inl (e ▸ hwp)) hstrict
  · exact absurd (Or.inr (Or.inl (e ▸ hwp))) hstrict
  · exact absurd (Or.inr (Or.inr (e ▸ hwp))) hstrict
  · exact absurd e hno4.1
  · exact absurd e hno4.2.1
  · exact absurd e hno4.2.2.1
  · exact absurd e hno4.2.2.2
  · exact List.mem_toFinset.mpr e

theorem lit2b_wires_newH7 : ECDSAAdd.wires lit2b ⊆ PoolHost.newSourceH7.toFinset := by
  intro w hw
  simp only [lit2b, ECDSAAdd.wires_append, Finset.mem_union] at hw
  rcases hw with (hw | hw) | hw
  · simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty,
      Finset.mem_insert, Finset.mem_singleton, windowRoot] at hw
    apply List.mem_toFinset.mpr; apply mem_newH7_of_band; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · exact cornerA2Prog_wires_newH7 hw
  · simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, windowRoot] at hw
    apply List.mem_toFinset.mpr; apply mem_newH7_of_band; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

/-! ### Pure `ECDSAAdd` fused execution equivalence (`corner_fused_run`) -/

private theorem regValue_bit_of_eq (ws : List Wire) (hnd : ws.Nodup) (hlen : ws.length = 256)
    (b : BasisState) (v : Nat) (hv : v < 2 ^ 256) (hreg : ECDSAAdd.regValue ws b = v) :
    ∀ i (hi : i < 256), b (ws[i]'(hlen.symm ▸ hi)) = v.testBit i := by
  let b' : BasisState := fun q =>
    if h : ∃ j : Fin 256, ws[j.val]'(hlen.symm ▸ j.isLt) = q then v.testBit (Classical.choose h).val else false
  have hreg' : ECDSAAdd.regValue ws b' = v := by
    apply regValue_of_bits ws b' v (by rw [hlen]; exact hv)
    intro i hi
    have hi256 : i < 256 := hlen ▸ hi
    have hex : ∃ j : Fin 256, ws[j.val]'(hlen.symm ▸ j.isLt) = ws[i]'hi := ⟨⟨i, hi256⟩, rfl⟩
    simp only [b', dif_pos hex]
    have hch := Classical.choose_spec hex
    have hij : (Classical.choose hex).val = i := (List.Nodup.getElem_inj_iff hnd).mp hch
    rw [hij]
  intro i hi
  have heq := (ECDSAAdd.Arithmetic.regValue_eq_iff ws b b').mp (hreg.trans hreg'.symm) (ws[i]'(hlen.symm ▸ hi)) (List.getElem_mem _)
  rw [heq]
  have hex : ∃ j : Fin 256, ws[j.val]'(hlen.symm ▸ j.isLt) = ws[i]'(hlen.symm ▸ hi) := ⟨⟨i, hi⟩, rfl⟩
  simp only [b', dif_pos hex]
  have hch := Classical.choose_spec hex
  have hij : (Classical.choose hex).val = i := (List.Nodup.getElem_inj_iff hnd).mp hch
  rw [hij]

private theorem scrNegP_effect_pool258 (s : ECDSAAdd.State) (m : List Bool)
    (hY : ECDSAAdd.regValue streamLayout.point.y s.basis < ECDSAAdd.p)
    (hclean : Clean (streamLayout.dialogPool.take 258) s.basis) :
    (ECDSAAdd.run scrNegP m s).phase = s.phase ∧
    ECDSAAdd.regValue streamLayout.point.y (ECDSAAdd.run scrNegP m s).basis =
      (if s.basis streamLayout.core.equalNegY then (ECDSAAdd.p - ECDSAAdd.regValue streamLayout.point.y s.basis) % ECDSAAdd.p
        else ECDSAAdd.regValue streamLayout.point.y s.basis) ∧
    ∀ q, q ∉ streamLayout.point.y → (ECDSAAdd.run scrNegP m s).basis q = s.basis q := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have width := negateYLayout_widths streamLayout hw
  have hpool := negateYLayout_pool streamLayout hw
  have aux : ∀ q ∈ (negateYLayout streamLayout).work ++ [(negateYLayout streamLayout).cin, (negateYLayout streamLayout).zero],
      s.basis q = false := fun q hq => by rw [hpool] at hq; exact hclean q hq
  unfold scrNegP
  exact (negateYLayout streamLayout).program_correct streamLayout.core.equalNegY (negateYLayout_nodup streamLayout hw hn) width.2
    (by rw [width.1]; decide) ECDSAAdd.p SquareReduction.c (ECDSAAdd.regValue streamLayout.point.y s.basis)
    (by rw [width.1]; norm_num [ECDSAAdd.p, SquareReduction.c]) (by norm_num [SquareReduction.c]) hY
    s m rfl ((ECDSAAdd.Arithmetic.regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq])))
    (aux _ (by simp)) (aux _ (by simp))

private theorem state_phase_mk (p : Bool) (b : BasisState) :
    (ECDSAAdd.State.mk p b).phase = p := rfl

private theorem state_basis_mk (p : Bool) (b : BasisState) :
    (ECDSAAdd.State.mk p b).basis = b := rfl

private theorem state_ext {a b : ECDSAAdd.State} (h1 : a.phase = b.phase) (h2 : a.basis = b.basis) : a = b := by
  cases a; cases b; cases h1; cases h2; rfl

private theorem state_eq_phase {a : ECDSAAdd.State} {p : Bool} {b : BasisState}
    (h : a = ⟨p, b⟩) : a.phase = p := (congrArg ECDSAAdd.State.phase h).trans (state_phase_mk p b)

private theorem state_eq_basis {a : ECDSAAdd.State} {p : Bool} {b : BasisState}
    (h : a = ⟨p, b⟩) (q : Wire) : a.basis q = b q :=
  congrFun ((congrArg ECDSAAdd.State.basis h).trans (state_basis_mk p b)) q

private theorem sl_infinitySelect : streamLayout.infinitySelect = 19816 := rfl

private theorem cornerNegProg_effect (s : ECDSAAdd.State) (m : List Bool)
    (hY : ECDSAAdd.regValue streamLayout.point.y s.basis < ECDSAAdd.p)
    (hclean : Clean (streamLayout.dialogPool.take 258) s.basis) :
    (ECDSAAdd.run cornerNegProg m s).phase = s.phase ∧
    ECDSAAdd.regValue streamLayout.point.y (ECDSAAdd.run cornerNegProg m s).basis =
      (if (s.basis streamLayout.core.equalNegY ^^ s.basis streamLayout.genericSelect)
        then (ECDSAAdd.p - ECDSAAdd.regValue streamLayout.point.y s.basis) % ECDSAAdd.p
        else ECDSAAdd.regValue streamLayout.point.y s.basis) ∧
    ∀ q, q ∉ streamLayout.point.y → (ECDSAAdd.run cornerNegProg m s).basis q = s.basis q := by
  have hE_m : ECDSAAdd.measurementCount scrNegE = 0 := by unfold scrNegE; exact cx_meas _ _
  have hE_run (t : ECDSAAdd.State) (k : List Bool) :
      ECDSAAdd.run scrNegE k t =
        ⟨t.phase, ECDSAAdd.writeBit t.basis streamLayout.core.equalNegY
          (t.basis streamLayout.core.equalNegY ^^ t.basis streamLayout.genericSelect)⟩ := by
    rw [scrNegE, run_cons_CX, Site1Fast.run_nil]
  have hne_gy : streamLayout.core.equalNegY ≠ streamLayout.genericSelect := by
    rw [sl_equalNegY, sl_genericSelect]; decide
  have hny : streamLayout.core.equalNegY ∉ streamLayout.point.y := by
    rw [sl_equalNegY, streamLayout_point, List.mem_range'_1]; omega
  have hnp : streamLayout.core.equalNegY ∉ streamLayout.dialogPool.take 258 := by
    rw [sl_equalNegY, pool_take_eq 258 (by decide), List.mem_range'_1]; omega
  rw [cornerNegProg, run_zero_append _ _ hE_m, ECDSAAdd.run_append scrNegP scrNegE, hE_run, hE_run]
  set s1 : ECDSAAdd.State := ⟨s.phase, ECDSAAdd.writeBit s.basis streamLayout.core.equalNegY
    (s.basis streamLayout.core.equalNegY ^^ s.basis streamLayout.genericSelect)⟩ with hs1
  have hy1 : ECDSAAdd.regValue streamLayout.point.y s1.basis = ECDSAAdd.regValue streamLayout.point.y s.basis :=
    ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq => by
      simp [hs1, ECDSAAdd.writeBit, Function.update, show q ≠ streamLayout.core.equalNegY from fun e => hny (e ▸ hq)])
  have hc1 : Clean (streamLayout.dialogPool.take 258) s1.basis := fun q hq => by
    simp [hs1, ECDSAAdd.writeBit, Function.update, show q ≠ streamLayout.core.equalNegY from fun e => hnp (e ▸ hq), hclean q hq]
  obtain ⟨hp, hval, hout⟩ := scrNegP_effect_pool258 s1 (m.take (ECDSAAdd.measurementCount scrNegP)) (hy1.symm ▸ hY) hc1
  generalize ECDSAAdd.run scrNegP (m.take (ECDSAAdd.measurementCount scrNegP)) s1 = s2 at hp hval hout ⊢
  have heq1 : s1.basis streamLayout.core.equalNegY = (s.basis streamLayout.core.equalNegY ^^ s.basis streamLayout.genericSelect) := by
    simp [hs1, ECDSAAdd.writeBit, Function.update]
  have hs1p : s1.phase = s.phase := rfl
  rw [hy1, heq1] at hval
  rw [state_phase_mk, state_basis_mk]
  refine ⟨hp.trans hs1p, ?_, ?_⟩
  · have hcongr := ECDSAAdd.Arithmetic.regValue_congr streamLayout.point.y
      (ECDSAAdd.writeBit s2.basis streamLayout.core.equalNegY
        (s2.basis streamLayout.core.equalNegY ^^ s2.basis streamLayout.genericSelect))
      s2.basis
      (fun q hq => by simp [ECDSAAdd.writeBit, Function.update, show q ≠ streamLayout.core.equalNegY from fun e => hny (e ▸ hq)])
    exact hcongr.trans hval
  · intro q hq
    by_cases hqe : q = streamLayout.core.equalNegY
    · subst hqe
      simp only [ECDSAAdd.writeBit, Function.update, ↓reduceDIte]
      rw [hout _ hny, hout _ (by rw [sl_genericSelect, streamLayout_point, List.mem_range'_1]; omega), hs1]
      simp [ECDSAAdd.writeBit, Function.update, Ne.symm hne_gy]
    · simp only [ECDSAAdd.writeBit, Function.update, hqe, ↓reduceDIte]
      rw [hout q hq, hs1]
      simp [ECDSAAdd.writeBit, Function.update, hqe]

private theorem scrW1_run (s : ECDSAAdd.State) (m : List Bool) :
    ECDSAAdd.run scrW1 m s =
      ⟨s.phase, ECDSAAdd.writeBit s.basis streamLayout.doubleSelect
        (s.basis streamLayout.doubleSelect ^^ s.basis streamLayout.infinitySelect ^^
          s.basis streamLayout.genericSelect ^^ s.basis streamLayout.core.equalNegY)⟩ := by
  have h1 : streamLayout.infinitySelect ≠ streamLayout.doubleSelect := by
    rw [sl_infinitySelect, sl_doubleSelect]; decide
  have h2 : streamLayout.genericSelect ≠ streamLayout.doubleSelect := by
    rw [sl_genericSelect, sl_doubleSelect]; decide
  have h3 : streamLayout.core.equalNegY ≠ streamLayout.doubleSelect := by
    rw [sl_equalNegY, sl_doubleSelect]; decide
  rw [scrW1, run_cons_CX, run_cons_CX, run_cons_CX, Site1Fast.run_nil]
  refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  funext q
  by_cases hq : q = streamLayout.doubleSelect
  · subst hq; simp [ECDSAAdd.writeBit, Function.update, h1, h2, h3]
  · simp [ECDSAAdd.writeBit, Function.update, hq]

private theorem scrW2_run (s : ECDSAAdd.State) (m : List Bool) :
    ECDSAAdd.run scrW2 m s =
      ⟨s.phase, ECDSAAdd.writeBit s.basis streamLayout.doubleSelect
        (s.basis streamLayout.doubleSelect ^^ s.basis streamLayout.core.equalNegY ^^
          s.basis streamLayout.genericSelect ^^ s.basis streamLayout.infinitySelect)⟩ := by
  have h1 : streamLayout.infinitySelect ≠ streamLayout.doubleSelect := by
    rw [sl_infinitySelect, sl_doubleSelect]; decide
  have h2 : streamLayout.genericSelect ≠ streamLayout.doubleSelect := by
    rw [sl_genericSelect, sl_doubleSelect]; decide
  have h3 : streamLayout.core.equalNegY ≠ streamLayout.doubleSelect := by
    rw [sl_equalNegY, sl_doubleSelect]; decide
  rw [scrW2, run_cons_CX, run_cons_CX, run_cons_CX, Site1Fast.run_nil]
  refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  funext q
  by_cases hq : q = streamLayout.doubleSelect
  · subst hq; simp [ECDSAAdd.writeBit, Function.update, h1, h2, h3]
  · simp [ECDSAAdd.writeBit, Function.update, hq]

private theorem scrSw1_run (s : ECDSAAdd.State) (m : List Bool) :
    ECDSAAdd.run scrSw1 m s =
      ⟨s.phase, ECDSAAdd.writeBit s.basis streamLayout.core.equalNegY
        (s.basis streamLayout.core.equalNegY ^^ s.basis streamLayout.doubleSelect)⟩ := by
  rw [scrSw1, run_cons_CX, Site1Fast.run_nil]

private theorem scrCWriteFused_run_eq (read : ConstantBit 32768 → Bool) (a : Nat)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (probeRows a) (.some hc))
    (G : Bool) (t : ECDSAAdd.State)
    (hg : t.basis streamLayout.core.generic = G)
    (hflag : G = true → t.basis streamLayout.infinitySelect = false ∧
      t.basis streamLayout.doubleSelect = false ∧
      t.basis streamLayout.genericSelect = false ∧
      t.basis streamLayout.core.equalNegY = false)
    (hcx : ECDSAAdd.regValue cxWord t.basis = cx.val)
    (hcy : ECDSAAdd.regValue cyWord t.basis = if G then (-cy).val else cy.val) :
    ECDSAAdd.run (scrW1 ++ scrCWriteFused ++ scrW2) List.nil t =
      ECDSAAdd.run (scrW1 ++ cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts probeRows) a) ++ scrW2) List.nil t := by
  have hw1_m : ECDSAAdd.measurementCount scrW1 = 0 := by simp [scrW1, ECDSAAdd.measurementCount]
  have hcf_m : ECDSAAdd.measurementCount scrCWriteFused = 0 := scrCWriteFused_meas
  have hcb_m : ECDSAAdd.measurementCount (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts probeRows) a)) = 0 :=
    cBits_records _ _ _
  rw [run_zero_append _ _ (by simp [ECDSAAdd.measurementCount_append, hw1_m, hcf_m]),
    run_zero_append _ _ hw1_m,
    run_zero_append _ _ (by simp [ECDSAAdd.measurementCount_append, hw1_m, hcb_m]),
    run_zero_append _ _ hw1_m]
  apply congrArg (ECDSAAdd.run scrW2 List.nil)
  set s := ECDSAAdd.run scrW1 List.nil t with hs
  have hs_eq : s = ⟨t.phase, ECDSAAdd.writeBit t.basis streamLayout.doubleSelect
      (t.basis streamLayout.doubleSelect ^^ t.basis streamLayout.infinitySelect ^^
        t.basis streamLayout.genericSelect ^^ t.basis streamLayout.core.equalNegY)⟩ := scrW1_run t List.nil
  have hds_ne_cx : ∀ q ∈ cxWord, q ≠ streamLayout.doubleSelect := fun q hq => by
    simp only [cxWord, List.mem_range'_1] at hq; rw [sl_doubleSelect]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hds_ne_cy : ∀ q ∈ cyWord, q ≠ streamLayout.doubleSelect := fun q hq => by
    simp only [cyWord, List.mem_cons, List.mem_range'_1] at hq; rw [sl_doubleSelect]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hds_ne_fin : streamLayout.point.finite ≠ streamLayout.doubleSelect := by
    rw [streamLayout_point, sl_doubleSelect]; decide
  have hds_not_x : streamLayout.doubleSelect ∉ streamLayout.point.x := by
    rw [streamLayout_point, sl_doubleSelect, List.mem_range'_1]; omega
  have hds_not_y : streamLayout.doubleSelect ∉ streamLayout.point.y := by
    rw [streamLayout_point, sl_doubleSelect, List.mem_range'_1]; omega
  have hcx_not_x : ∀ q ∈ cxWord, q ∉ streamLayout.point.x := fun q hq hm => by
    simp only [cxWord, streamLayout_point, List.mem_range'_1] at hq hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hcy_not_y : ∀ q ∈ cyWord, q ∉ streamLayout.point.y := fun q hq hm => by
    simp only [cyWord, streamLayout_point, List.mem_cons, List.mem_range'_1] at hq hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hcf_run : ECDSAAdd.run scrCWriteFused List.nil s =
      ⟨s.phase, fun q =>
        let b1 := ECDSAAdd.writeBit s.basis streamLayout.point.finite (s.basis streamLayout.point.finite ^^ s.basis streamLayout.doubleSelect)
        let b2 := fun u => b1 u ^^ (s.basis streamLayout.doubleSelect && xMask streamLayout.point.x (cxWord.map s.basis) u)
        b2 q ^^ (s.basis streamLayout.doubleSelect && xMask streamLayout.point.y (cyWord.map s.basis) q)⟩ := by
    have hcx1 : ECDSAAdd.measurementCount ([.CX streamLayout.doubleSelect streamLayout.point.finite] : ECDSAAdd.Program) = 0 := rfl
    rw [scrCWriteFused, run_zero_append _ _ (by rw [ECDSAAdd.measurementCount_append, hcx1, ccxList_meas]),
      run_zero_append _ _ hcx1, run_cons_CX, Site1Fast.run_nil]
    set s1 : ECDSAAdd.State := ⟨s.phase, ECDSAAdd.writeBit s.basis streamLayout.point.finite
      (s.basis streamLayout.point.finite ^^ s.basis streamLayout.doubleSelect)⟩ with hs1
    rw [ccxList_run _ _ _ _ _ hcx_not_x hds_not_x, ccxList_run _ _ _ _ _ hcy_not_y hds_not_y]
    have hcx_s1 : cxWord.map s1.basis = cxWord.map s.basis := List.map_congr_left (fun q hq => by
      simp [hs1, ECDSAAdd.writeBit, Function.update, show q ≠ streamLayout.point.finite from by
        simp only [cxWord, List.mem_range'_1] at hq; rw [streamLayout_point]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega])
    have hds_s1 : s1.basis streamLayout.doubleSelect = s.basis streamLayout.doubleSelect := by
      simp [hs1, ECDSAAdd.writeBit, Function.update, Ne.symm hds_ne_fin]
    have hcy_s2 : cyWord.map (fun q => s1.basis q ^^ (s1.basis streamLayout.doubleSelect && xMask streamLayout.point.x (cxWord.map s1.basis) q)) =
        cyWord.map s.basis := List.map_congr_left (fun q hq => by
      have hq_not_x : q ∉ streamLayout.point.x := fun hm => by
        simp only [cyWord, streamLayout_point, List.mem_cons, List.mem_range'_1] at hq hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have hq_ne_fin : q ≠ streamLayout.point.finite := by
        simp only [cyWord, List.mem_cons, List.mem_range'_1] at hq; rw [streamLayout_point]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      simp [xMask_outside _ _ _ hq_not_x, hs1, ECDSAAdd.writeBit, Function.update, hq_ne_fin])
    have hds_s2 : (s1.basis streamLayout.doubleSelect ^^ (s1.basis streamLayout.doubleSelect && xMask streamLayout.point.x (cxWord.map s1.basis) streamLayout.doubleSelect)) =
        s.basis streamLayout.doubleSelect := by
      simp [xMask_outside _ _ _ hds_not_x, hds_s1]
    dsimp only
    rw [hcy_s2, hds_s2, hcx_s1, hds_s1]
  have hcb_run : ECDSAAdd.run (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts probeRows) a)) List.nil s =
      ⟨s.phase, fun q => s.basis q ^^ (s.basis streamLayout.doubleSelect && xMask scrDTargets (portBits read (scrCPorts probeRows) a) q)⟩ :=
    cBits_run _ _ _ _ _ (by
      intro hm; simp only [scrDTargets, List.cons_append, List.mem_cons, List.mem_append] at hm
      rcases hm with h | h | h
      · exact hds_ne_fin h.symm
      · exact hds_not_x h
      · exact hds_not_y h)
  rw [hcf_run, hcb_run]
  cases hd : s.basis streamLayout.doubleSelect with
  | false =>
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
    funext q
    simp only [Bool.false_and, Bool.xor_false, ECDSAAdd.writeBit, Function.update]
    by_cases hq : q = streamLayout.point.finite
    · subst hq; simp
    · simp [hq]
  | true =>
    have hGf : G = false := by
      cases hG : G
      · rfl
      · exfalso
        obtain ⟨h1, h2, h3, h4⟩ := hflag hG
        rw [hs_eq] at hd
        simp [ECDSAAdd.writeBit, Function.update, h1, h2, h3, h4] at hd
    have hcx_s : ECDSAAdd.regValue cxWord s.basis = cx.val :=
      (ECDSAAdd.Arithmetic.regValue_congr cxWord s.basis t.basis (fun q hq => by
        rw [congrArg ECDSAAdd.State.basis hs_eq]; simp [ECDSAAdd.writeBit, Function.update, hds_ne_cx q hq])).trans hcx
    have hcy_s : ECDSAAdd.regValue cyWord s.basis = cy.val := by
      have h1 := (ECDSAAdd.Arithmetic.regValue_congr cyWord s.basis t.basis (fun q hq => by
        rw [congrArg ECDSAAdd.State.basis hs_eq]; simp [ECDSAAdd.writeBit, Function.update, hds_ne_cy q hq])).trans hcy
      simpa [hGf] using h1
    have hcx_bits : cxWord.map s.basis = portBits read (indexedPorts streamLayout.point.x (wFields probeRows .x) true) a := by
      apply List.ext_getElem
      · rw [List.length_map, cxWord, List.length_range', portBits, List.length_map, indexed_length, point_x_len]
      · intro i hi1 hi2
        have hi256 : i < 256 := by simpa [cxWord] using hi1
        rw [List.getElem_map]
        have hbit := regValue_bit_of_eq cxWord (by simp [cxWord]; exact List.nodup_range')
          (by simp [cxWord]) s.basis cx.val (cx.isLt.trans (by norm_num [ECDSAAdd.p])) hcx_s i hi256
        have hpi := portBits_indexed read streamLayout.point.x (wFields probeRows .x) true a
        simp only [hbit, hpi, List.getElem_map, List.getElem_range]
        simp [row_bits hc hr .x cx (field_some_x hc) i hi256]
    have hcy_bits : cyWord.map s.basis = portBits read (indexedPorts streamLayout.point.y (wFields probeRows .y) true) a := by
      apply List.ext_getElem
      · rw [List.length_map, cyWord, List.length_cons, List.length_range', portBits, List.length_map, indexed_length, point_y_len]
      · intro i hi1 hi2
        have hi256 : i < 256 := by simpa [cyWord] using hi1
        rw [List.getElem_map]
        have hnd : cyWord.Nodup := by
          rw [cyWord, List.nodup_cons]; exact ⟨by simp [List.mem_range'_1], List.nodup_range'⟩
        have hbit := regValue_bit_of_eq cyWord hnd (by simp [cyWord]) s.basis cy.val
          (cy.isLt.trans (by norm_num [ECDSAAdd.p])) hcy_s i hi256
        have hpi := portBits_indexed read streamLayout.point.y (wFields probeRows .y) true a
        simp only [hbit, hpi, List.getElem_map, List.getElem_range]
        have hyf : fieldValue (toA (.some hc)) .y = cy.val := rfl
        simp [row_bits hc hr .y cy hyf i hi256]
    have hinf_bit : decide (read (wBit probeRows .infinity 0 a) = false) = true := by
      have hb := hr.bit .infinity 0 (by decide)
      rw [infinity_bit] at hb
      simp [wBit, hb, pointFinite]
    have hcports_eq : portBits read (scrCPorts probeRows) a =
        true :: (cxWord.map s.basis ++ cyWord.map s.basis) := by
      unfold scrCPorts portBits
      rw [List.cons_append, List.map_cons, List.map_append]
      exact congrArg₂ (· :: ·) hinf_bit (congrArg₂ (· ++ ·) hcx_bits.symm hcy_bits.symm)
    have hxlen : streamLayout.point.x.length = (cxWord.map s.basis).length := by
      rw [point_x_len, List.length_map, cxWord, List.length_range']
    have hfin_not_x : streamLayout.point.finite ∉ streamLayout.point.x := by
      intro hm; rw [streamLayout_point, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at hm; omega
    have hfin_not_y : streamLayout.point.finite ∉ streamLayout.point.y := by
      intro hm; rw [streamLayout_point, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at hm; omega
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
    funext q
    simp only [Bool.true_and, hcports_eq, scrDTargets, List.cons_append, xMask,
      xMask_append streamLayout.point.x streamLayout.point.y _ _ hxlen]
    by_cases hqf : q = streamLayout.point.finite
    · subst hqf
      simp only [ECDSAAdd.writeBit, Function.update, ↓reduceDIte, decide_true, Bool.true_and,
        xMask_outside _ _ _ hfin_not_x, xMask_outside _ _ _ hfin_not_y, Bool.xor_false]
    · simp only [ECDSAAdd.writeBit, Function.update, hqf, ↓reduceDIte, decide_false, Bool.false_and, Bool.false_xor]
      cases s.basis q <;> cases xMask streamLayout.point.x (cxWord.map s.basis) q <;>
        cases xMask streamLayout.point.y (cyWord.map s.basis) q <;> rfl

private theorem bool_xor_4_cancel (d i g e : Bool) :
    ((d ^^ i ^^ g ^^ e ^^ e ^^ g ^^ i) = d) := by
  cases d <;> cases i <;> cases g <;> cases e <;> rfl

private theorem bool_comm_xor (q d i g e c k : Bool) :
    (((q ^^ ((d ^^ i ^^ g ^^ e) && c)) ^^ ((e ^^ d) && k)) =
      ((q ^^ ((e ^^ d) && k)) ^^ ((d ^^ i ^^ g ^^ e) && c))) := by
  cases q <;> cases d <;> cases i <;> cases g <;> cases e <;> cases c <;> cases k <;> rfl

private theorem scrW_cBits_effect (kC : List Bool) (t : ECDSAAdd.State) :
    let d := t.basis streamLayout.doubleSelect ^^ t.basis streamLayout.infinitySelect ^^
      t.basis streamLayout.genericSelect ^^ t.basis streamLayout.core.equalNegY
    ECDSAAdd.run (scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2) List.nil t =
      ⟨t.phase, fun q => t.basis q ^^ (d && xMask scrDTargets kC q)⟩ := by
  intro d
  have hw1_m : ECDSAAdd.measurementCount scrW1 = 0 := by simp [scrW1, ECDSAAdd.measurementCount]
  have hcb_m : ECDSAAdd.measurementCount (cBits streamLayout.doubleSelect scrDTargets kC) = 0 := cBits_records _ _ _
  rw [run_zero_append _ _ (by simp [ECDSAAdd.measurementCount_append, hw1_m, hcb_m]),
    run_zero_append _ _ hw1_m, scrW1_run, cBits_run _ _ _ _ _ (by
      intro hm; simp only [scrDTargets, sl_doubleSelect, streamLayout_point, List.cons_append,
        List.mem_cons, List.mem_append, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
    scrW2_run]
  have hfl_not_dt : ∀ w ∈ [streamLayout.doubleSelect, streamLayout.infinitySelect,
      streamLayout.genericSelect, streamLayout.core.equalNegY], w ∉ scrDTargets := by
    intro w hw hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl] at hw
    simp only [scrDTargets, streamLayout_point, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1] at hm
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have h1 : streamLayout.infinitySelect ≠ streamLayout.doubleSelect := by rw [sl_infinitySelect, sl_doubleSelect]; decide
  have h2 : streamLayout.genericSelect ≠ streamLayout.doubleSelect := by rw [sl_genericSelect, sl_doubleSelect]; decide
  have h3 : streamLayout.core.equalNegY ≠ streamLayout.doubleSelect := by rw [sl_equalNegY, sl_doubleSelect]; decide
  refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  funext q
  simp only [ECDSAAdd.writeBit, Function.update, ↓reduceDIte,
    xMask_outside scrDTargets kC streamLayout.doubleSelect (hfl_not_dt streamLayout.doubleSelect (by simp)),
    xMask_outside scrDTargets kC streamLayout.infinitySelect (hfl_not_dt streamLayout.infinitySelect (by simp)),
    xMask_outside scrDTargets kC streamLayout.genericSelect (hfl_not_dt streamLayout.genericSelect (by simp)),
    xMask_outside scrDTargets kC streamLayout.core.equalNegY (hfl_not_dt streamLayout.core.equalNegY (by simp))]
  by_cases hq : q = streamLayout.doubleSelect
  · subst hq
    simp only [↓reduceDIte, h1, h2, h3, Bool.and_false, Bool.xor_false, d,
      xMask_outside scrDTargets kC streamLayout.doubleSelect (hfl_not_dt streamLayout.doubleSelect (by simp))]
    exact bool_xor_4_cancel _ _ _ _
  · simp [hq, d]

private theorem scrSw_cBits_effect (T : List Wire) (kD : List Bool)
    (hfl : streamLayout.core.equalNegY ∉ T ∧ streamLayout.doubleSelect ∉ T) (t : ECDSAAdd.State) :
    let e := t.basis streamLayout.core.equalNegY ^^ t.basis streamLayout.doubleSelect
    ECDSAAdd.run (scrSw1 ++ cBits streamLayout.core.equalNegY T kD ++ scrSw1) List.nil t =
      ⟨t.phase, fun q => t.basis q ^^ (e && xMask T kD q)⟩ := by
  intro e
  have hsw_m : ECDSAAdd.measurementCount scrSw1 = 0 := by unfold scrSw1; exact cx_meas _ _
  have hcb_m : ECDSAAdd.measurementCount (cBits streamLayout.core.equalNegY T kD) = 0 := cBits_records _ _ _
  have hne : streamLayout.doubleSelect ≠ streamLayout.core.equalNegY := by rw [sl_doubleSelect, sl_equalNegY]; decide
  rw [run_zero_append _ _ (by simp [ECDSAAdd.measurementCount_append, hsw_m, hcb_m]),
    run_zero_append _ _ hsw_m, scrSw1_run, cBits_run _ _ _ _ _ hfl.1, scrSw1_run]
  refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  funext q
  simp only [ECDSAAdd.writeBit, Function.update, ↓reduceDIte,
    xMask_outside T kD streamLayout.core.equalNegY hfl.1,
    xMask_outside T kD streamLayout.doubleSelect hfl.2, Bool.and_false, Bool.xor_false]
  by_cases hq : q = streamLayout.core.equalNegY
  · subst hq
    simp only [↓reduceDIte, hne, e, xMask_outside T kD streamLayout.core.equalNegY hfl.1, Bool.and_false, Bool.xor_false]
    cases t.basis streamLayout.core.equalNegY <;> cases t.basis streamLayout.doubleSelect <;> rfl
  · simp [hq, e]

private theorem scrSw_ccx_eq_cBits (S T : List Wire) (k : List Bool) (t : ECDSAAdd.State)
    (hST : ∀ a ∈ S, a ∉ T)
    (hflT : streamLayout.core.equalNegY ∉ T ∧ streamLayout.doubleSelect ∉ T)
    (hflS : streamLayout.core.equalNegY ∉ S)
    (hmap : S.map t.basis = k) :
    ECDSAAdd.run (scrSw1 ++ ccxList streamLayout.core.equalNegY S T ++ scrSw1) List.nil t =
      ECDSAAdd.run (scrSw1 ++ cBits streamLayout.core.equalNegY T k ++ scrSw1) List.nil t := by
  have hsw_m : ECDSAAdd.measurementCount scrSw1 = 0 := by unfold scrSw1; exact cx_meas _ _
  have hcc_m : ECDSAAdd.measurementCount (ccxList streamLayout.core.equalNegY S T) = 0 := ccxList_meas _ _ _
  have hcb_m : ECDSAAdd.measurementCount (cBits streamLayout.core.equalNegY T k) = 0 := cBits_records _ _ _
  rw [run_zero_append _ _ (by simp [ECDSAAdd.measurementCount_append, hsw_m, hcc_m]),
    run_zero_append _ _ hsw_m,
    run_zero_append _ _ (by simp [ECDSAAdd.measurementCount_append, hsw_m, hcb_m]),
    run_zero_append _ _ hsw_m]
  congr 1
  rw [scrSw1_run, ccxList_run _ _ _ _ _ hST hflT.1, cBits_run _ _ _ _ _ hflT.1]
  have hm' : S.map (ECDSAAdd.writeBit t.basis streamLayout.core.equalNegY
      (t.basis streamLayout.core.equalNegY ^^ t.basis streamLayout.doubleSelect)) = k := by
    rw [← hmap]
    apply List.map_congr_left
    intro q hq
    simp [ECDSAAdd.writeBit, Function.update, show q ≠ streamLayout.core.equalNegY from fun e => hflS (e ▸ hq)]
  rw [hm']

private theorem scrW_comm_scrSw (kC kD : List Bool) (t : ECDSAAdd.State) :
    ECDSAAdd.run ((scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2) ++
        (scrSw1 ++ cBits streamLayout.core.equalNegY scrDTargets kD ++ scrSw1)) List.nil t =
      ECDSAAdd.run ((scrSw1 ++ cBits streamLayout.core.equalNegY scrDTargets kD ++ scrSw1) ++
        (scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2)) List.nil t := by
  have hfl_not_dt : ∀ w ∈ [streamLayout.doubleSelect, streamLayout.infinitySelect,
      streamLayout.genericSelect, streamLayout.core.equalNegY], w ∉ scrDTargets := by
    intro w hw hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl] at hw
    simp only [scrDTargets, streamLayout_point, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1] at hm
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hflSw : streamLayout.core.equalNegY ∉ scrDTargets ∧ streamLayout.doubleSelect ∉ scrDTargets :=
    ⟨hfl_not_dt _ (by simp), hfl_not_dt _ (by simp)⟩
  have hmW : ECDSAAdd.measurementCount (scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2) = 0 := by
    simp [scrW1, scrW2, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount, cBits_records]
  have hmSw : ECDSAAdd.measurementCount (scrSw1 ++ cBits streamLayout.core.equalNegY scrDTargets kD ++ scrSw1) = 0 := by
    simp [scrSw1, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount, cBits_records]
  rw [run_zero_append _ _ hmW, run_zero_append _ _ hmSw,
    scrW_cBits_effect kC t, scrSw_cBits_effect scrDTargets kD hflSw,
    scrSw_cBits_effect scrDTargets kD hflSw t, scrW_cBits_effect kC]
  refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  funext q
  simp only [
    xMask_outside scrDTargets kC streamLayout.doubleSelect (hfl_not_dt streamLayout.doubleSelect (by simp)),
    xMask_outside scrDTargets kC streamLayout.infinitySelect (hfl_not_dt streamLayout.infinitySelect (by simp)),
    xMask_outside scrDTargets kC streamLayout.genericSelect (hfl_not_dt streamLayout.genericSelect (by simp)),
    xMask_outside scrDTargets kC streamLayout.core.equalNegY (hfl_not_dt streamLayout.core.equalNegY (by simp)),
    xMask_outside scrDTargets kD streamLayout.doubleSelect (hfl_not_dt streamLayout.doubleSelect (by simp)),
    xMask_outside scrDTargets kD streamLayout.infinitySelect (hfl_not_dt streamLayout.infinitySelect (by simp)),
    xMask_outside scrDTargets kD streamLayout.genericSelect (hfl_not_dt streamLayout.genericSelect (by simp)),
    xMask_outside scrDTargets kD streamLayout.core.equalNegY (hfl_not_dt streamLayout.core.equalNegY (by simp)),
    Bool.and_false, Bool.xor_false]
  exact bool_comm_xor _ _ _ _ _ _ _

private theorem cornerA2Prog_avoid_extra : ∀ w ∈ scrDExtraWires, w ∉ ECDSAAdd.wires cornerA2Prog := by
  intro w hw hm
  rw [cornerA2Prog_eq_litProg] at hm
  obtain ⟨p, hp, hwp⟩ := litProg_wires cornerA2 w hm
  have he := scrDExtraWires_explicit
  rw [he, List.mem_range'_1] at hw
  simp only [cornerA2, scrDMiddle, wLiteral, List.mem_append, List.mem_singleton] at hp
  rcases hp with (h | h) | (((((h | h) | h) | h) | h) | h)
  · cases h
    have hsub0 : ECDSAAdd.wires scrNegP ⊆ ((negateYLayout streamLayout).wires streamLayout.core.equalNegY).toFinset := by
      unfold scrNegP
      exact (negateYLayout streamLayout).program_support streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
        (negateYLayout_widths streamLayout streamLayout_widths).2
    have := scrAll_neg w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw))
    exact this (List.mem_toFinset.mp (hsub0 hwp))
  · cases h
    exact scrAll_avoid_gf w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw)) hwp
  · cases h
    rcases cxList_wires _ _ _ hwp with h1 | h1
    · exact extra_not_scrWires w (by rw [he, List.mem_range'_1]; exact hw) (List.mem_append_left _ h1)
    · exact scrAll_pair_targets w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw)) h1
  · have hsub : ECDSAAdd.wires p ⊆ ECDSAAdd.wires scrP1 := by
      have hinst := scr_chain_inst (fun _ => false) 0
      have hlit := litProg_inst (fun _ => false) _ 0
        (wZeroWith_litOnly (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.infinitySelect
            streamLayout.core.equalNegY)
          (fun u j hj => by simp only [wPairTailBare, wLiteral, List.mem_singleton] at hj; exact ⟨_, hj⟩)
          streamLayout.control (pairPorts streamLayout))
      have hpe : litProg (wZeroWith (wPairTailBare (n := 32768) (yLow streamLayout) streamLayout.infinitySelect
          streamLayout.core.equalNegY) streamLayout.control (pairPorts streamLayout)) = scrP1 := hlit.symm.trans hinst
      rw [← hpe]
      have aux : ∀ (c : WCode 32768), WInstr.literal p ∈ c → ECDSAAdd.wires p ⊆ ECDSAAdd.wires (litProg c) := by
        intro c; induction c with
        | nil => intro hc; cases hc
        | cons x xs ih =>
          intro hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · simp [litProg, ECDSAAdd.wires_append]
          · cases x with
            | literal q =>
              simp only [litProg, ECDSAAdd.wires_append]
              exact (ih hc').trans Finset.subset_union_right
            | lookup _ _ =>
              simp only [litProg]
              exact ih hc'
      exact aux _ h
    exact scrAllP1_wires w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw)) (hsub hwp)
  · cases h
    simp only [ECDSAAdd.wires_append, Finset.mem_union] at hwp
    rcases hwp with hwp | hwp
    · rcases cxList_wires _ _ _ hwp with h1 | h1
      · exact extra_not_scrWires w (by rw [he, List.mem_range'_1]; exact hw) (List.mem_append_left _ h1)
      · exact scrAll_pair_targets w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw)) h1
    · simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_singleton] at hwp
      exact scrAll_y w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw)) (by simp [hwp])
  · cases h
    rcases cxList_wires _ _ _ hwp with h1 | h1
    · exact extra_not_scrWires w (by rw [he, List.mem_range'_1]; exact hw) (List.mem_append_right _ h1)
    · exact scrAll_short_targets w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw)) h1
  · cases h
    exact scrAllP2_wires w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw)) hwp
  · cases h
    rcases cxList_wires _ _ _ hwp with h1 | h1
    · exact extra_not_scrWires w (by rw [he, List.mem_range'_1]; exact hw) (List.mem_append_right _ h1)
    · exact scrAll_short_targets w (List.mem_append_right _ (by rw [he, List.mem_range'_1]; exact hw)) h1

private theorem xBits_run_inj (ws : List Wire) (bits : List Bool) (u1 u2 : ECDSAAdd.State)
    (h : ECDSAAdd.run (xBits ws bits) List.nil u1 = ECDSAAdd.run (xBits ws bits) List.nil u2) :
    u1 = u2 := by
  rw [xBits_run, xBits_run] at h
  have ⟨hph, hba⟩ := (ECDSAAdd.State.mk.injEq _ _ _ _).mp h
  cases u1; cases u2
  refine (ECDSAAdd.State.mk.injEq _ _ _ _).mpr ⟨hph, ?_⟩
  funext q
  have hq := congrFun hba q
  have hcancel : ∀ a b c : Bool, (a ^^ c) = (b ^^ c) → a = b := by decide
  exact hcancel _ _ _ hq

private theorem cornerA2_scrWires_run (read : ConstantBit 32768 → Bool) (a : Nat)
    (m : List Bool) (x : ECDSAAdd.State) (hx : ∀ w ∈ scrAllWires, x.basis w = false) :
    let kPS := portBits read (scrPairBits probeRows (wBit probeRows .y)) a ++ portBits read (scrShortBits probeRows) a
    ECDSAAdd.run cornerA2Prog m (scrLoad scrWires kPS x) =
      scrLoad scrWires kPS (ECDSAAdd.run (scrNegP ++ midIP read probeRows a) m x) ∧
    ∀ w ∈ scrAllWires, (ECDSAAdd.run (scrNegP ++ midIP read probeRows a) m x).basis w = false := by
  intro kPS
  have hsim := cornerA2_dSim read probeRows a
  set kE := portBits read (scrDExtraBits probeRows) a
  have hlPS : scrWires.length = kPS.length := by
    simp [scrWires, kPS, scrPairWires_length, scrShortWires_length, portBits, scrPairBits_length, scrShortBits_length]
  obtain ⟨hstep, hcl⟩ := hsim.step m x hx
  have hload_eq : ∀ u : ECDSAAdd.State,
      ECDSAAdd.run (xBits scrDExtraWires kE) List.nil (scrLoad scrWires kPS u) =
        scrLoad scrAllWires (kPS ++ kE) u := by
    intro u
    rw [xBits_run]
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
    funext q
    simp only [scrLoad, scrAllWires, xMask_append scrWires scrDExtraWires kPS kE hlPS, Bool.xor_assoc]
  have hdisj : Disjoint (ECDSAAdd.wires cornerA2Prog) (ECDSAAdd.wires (xBits scrDExtraWires kE)) :=
    Finset.disjoint_left.mpr fun q hq hs => cornerA2Prog_avoid_extra q (xBits_wires scrDExtraWires kE q hs) hq
  have hcomm := ECDSAAdd.Arithmetic.run_disjoint_commute cornerA2Prog (xBits scrDExtraWires kE) hdisj m List.nil (scrLoad scrWires kPS x)
  have hca2 : cornerA2Prog =
      scrNegP ++ (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets)))))) := by
    unfold cornerA2Prog; rfl
  rw [← hca2] at hstep
  rw [hload_eq x, hstep, ← hload_eq] at hcomm
  exact ⟨xBits_run_inj _ _ _ _ hcomm.symm, hcl⟩

/-! ### Full 3-pass fused `corner` execution equivalence -/

def origCornerRef (read : ConstantBit 32768 → Bool) (a : Nat) : ECDSAAdd.Program :=
  (specialize (site2 probeRows).code a).instantiate read ++
  ECDSAAdd.Frontier.zrep streamLayout ++
  cornerNegProg ++
  (specialize (WEX.cornerUnit₁ ++ WEX.cornerUnit₂) a).instantiate read

def cornerPerm (m0 m2b : List Bool) : List Bool :=
  let kPre := ECDSAAdd.measurementCount xAddProg + ECDSAAdd.measurementCount negYProg + ECDSAAdd.measurementCount yAddProg
  let kCN := ECDSAAdd.measurementCount cornerNegProg
  (m0.take kPre ++ m0.drop (kPre + kCN)) ++ (m0.drop kPre).take kCN ++ m2b

theorem origCornerRef_meas (read : ConstantBit 32768 → Bool) (a : Nat) :
    ECDSAAdd.measurementCount (origCornerRef read a) =
      ECDSAAdd.measurementCount pair2Prog + ECDSAAdd.measurementCount cornerNegProg +
        ECDSAAdd.measurementCount cornerA2Prog := by
  have hs2 : (specialize (site2 probeRows).code a).instantiate read =
      site2Load read probeRows a ++ (pair2Prog ++ site2Load read probeRows a) := by
    rw [site2_code, site2_inst]
  have hc12 : (specialize (WEX.cornerUnit₁ ++ WEX.cornerUnit₂) a).instantiate read =
      cBits windowRoot (scrAllWires ++ yWires)
        (portBits read (scrDPorts probeRows) a ++ portBits read (yPorts probeRows) a) ++
      (cornerA1Prog ++ (cBits windowRoot yWires (portBits read (yPorts probeRows) a) ++
        (cornerA2Prog ++ cBits windowRoot scrAllWires (portBits read (scrDPorts probeRows) a)))) := by
    simp only [WEX.cornerUnit₁, WEX.cornerUnit₂, WEX.cornerPre₁, specialize_append, Tmpl.instantiate_append,
      scr_lookup_some_inst, cornerPorts_targets, cornerPorts_bits, yPorts_targets, scrDPorts_targets,
      cornerA1_inst, cornerA2_inst, cornerA1Prog, cornerA2Prog, List.append_assoc]
  rw [origCornerRef, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount_append,
    ECDSAAdd.measurementCount_append, hs2, hc12]
  simp only [ECDSAAdd.measurementCount_append, site2Load_records, zrep_records, cBits_records, cornerA1Prog_meas]
  generalize ECDSAAdd.measurementCount pair2Prog = m1
  generalize ECDSAAdd.measurementCount cornerNegProg = m2
  generalize ECDSAAdd.measurementCount cornerA2Prog = m3
  omega

theorem cornerPerm_len (m0 m2b : List Bool)
    (hm0 : m0.length = ECDSAAdd.measurementCount lit0)
    (hm2b : m2b.length = ECDSAAdd.measurementCount cornerA2Prog) :
    (cornerPerm m0 m2b).length =
      ECDSAAdd.measurementCount pair2Prog + ECDSAAdd.measurementCount cornerNegProg +
        ECDSAAdd.measurementCount cornerA2Prog := by
  have hp2 : ECDSAAdd.measurementCount pair2Prog =
      ECDSAAdd.measurementCount xAddProg + ECDSAAdd.measurementCount negYProg +
      ECDSAAdd.measurementCount yAddProg + ECDSAAdd.measurementCount negYProg := by
    have hp2' : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
    rw [hp2']; simp only [ECDSAAdd.measurementCount_append]
  have hl0 := lit0_meas
  simp only [cornerPerm, List.length_append, List.length_take, List.length_drop, hm0, hm2b, hl0, hp2]
  generalize ECDSAAdd.measurementCount xAddProg = a
  generalize ECDSAAdd.measurementCount negYProg = b
  generalize ECDSAAdd.measurementCount yAddProg = c
  generalize ECDSAAdd.measurementCount cornerNegProg = d
  generalize ECDSAAdd.measurementCount cornerA2Prog = e
  omega

private theorem p0Ports_nodup : (portTargets (p0Ports probeRows)).Nodup := by
  rw [p0Ports_targets, List.nodup_append]
  refine ⟨site2Wires_nodup, by rw [extra0Wires]; exact List.nodup_range', fun a ha b hb hab => ?_⟩
  subst hab
  simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at ha hb
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

private theorem p1Ports_nodup : (portTargets (p1Ports probeRows)).Nodup := by
  rw [p1Ports_targets, extra1Wires]; exact List.nodup_range'

private theorem p2Ports_nodup : (portTargets (p2Ports probeRows)).Nodup := by
  rw [p2Ports_targets, List.nodup_append]
  refine ⟨scrShortWires_nd, by rw [extra2Wires]; exact List.nodup_range', fun a ha b hb hab => ?_⟩
  subst hab
  have h1 := shortWires_bounds a ha
  simp only [extra2Wires, List.mem_range'_1] at hb
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

private theorem p0ClearWires_nodup : p0ClearWires.Nodup := by
  rw [p0ClearWires, cyTailWires, extra0Wires, List.nodup_append]
  refine ⟨List.nodup_range', List.nodup_range', fun a ha b hb hab => ?_⟩
  subst hab; simp only [List.mem_range'_1] at ha hb; omega

private theorem finalClearWires_nodup : finalClearWires.Nodup := by
  rw [finalClearWires, List.nodup_append]
  refine ⟨?_, List.nodup_singleton _, fun a ha b hb hab => ?_⟩
  · rw [List.nodup_append]
    refine ⟨scrShortWires_nd, by rw [cxWord]; exact List.nodup_range', fun a ha b hb hab => ?_⟩
    subst hab; have h1 := shortWires_bounds a ha
    simp only [cxWord, List.mem_range'_1] at hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · subst hab; simp only [List.mem_singleton] at hb; subst hb
    rcases List.mem_append.mp ha with h | h
    · have := shortWires_bounds 14883 h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · simp only [cxWord, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

private theorem mem_p0Wires_pool {w : Wire} (h : w ∈ site2Wires ++ extra0Wires) :
    w ∈ streamLayout.dialogPool := by
  have h1 : w ∈ streamLayout.dialogPool.take 2613 := by
    rw [mem_pool_take 2613 (le_refl _)]
    simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at h
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  exact List.mem_of_mem_take h1

private theorem portMask_eq_xMask (read : ConstantBit 32768 → Bool) (ps : List (LookupPort 32768))
    (a : Nat) (hnd : (portTargets ps).Nodup) (q : Wire) :
    decide (q ∈ portMask read ps a) = xMask (portTargets ps) (portBits read ps a) q := by
  induction ps with
  | nil => simp [portMask, portTargets, portBits, tableBitsMask, xMask]
  | cons p ps ih =>
    rw [portTargets, List.map_cons, List.nodup_cons] at hnd
    have ih' := ih hnd.2
    change decide (q ∈ if decide (read (p.ref a) = p.value) = true then p.target :: portMask read ps a else portMask read ps a) =
      ((decide (q = p.target) && decide (read (p.ref a) = p.value)) ^^ xMask (portTargets ps) (portBits read ps a) q)
    by_cases hqp : q = p.target
    · subst hqp
      have hnot : p.target ∉ portMask read ps a := fun hm =>
        hnd.1 (tableBitsMask_subset _ _ hm)
      have hnotx : xMask (portTargets ps) (portBits read ps a) p.target = false := by
        rw [← ih']; exact decide_eq_false hnot
      by_cases hd : decide (read (p.ref a) = p.value) = true
      · simp only [hd, if_true, List.mem_cons, true_or, decide_true, Bool.true_and, hnotx, Bool.xor_false]
      · have hdf : decide (read (p.ref a) = p.value) = false := Bool.eq_false_iff.mpr hd
        simp only [hdf, Bool.false_eq_true, if_false, Bool.and_false, Bool.false_xor]
        exact ih'
    · by_cases hd : decide (read (p.ref a) = p.value) = true
      · simp only [hd, if_true, List.mem_cons, hqp, false_or, decide_false, Bool.false_and, Bool.false_xor]
        exact ih'
      · have hdf : decide (read (p.ref a) = p.value) = false := Bool.eq_false_iff.mpr hd
        simp only [hdf, Bool.false_eq_true, if_false, Bool.and_false, Bool.false_xor]
        exact ih'

private theorem xMask_p0_split (read : ConstantBit 32768 → Bool) (a : Nat) (q : Wire) :
    decide (q ∈ portMask read (p0Ports probeRows) a) =
      (xMask site2Wires (site2Bits read probeRows a) q ^^
        xMask extra0Wires ((portBits read (scrDExtraBits probeRows) a).take 17) q) := by
  have heq : portBits read (p0Ports probeRows) a =
      site2Bits read probeRows a ++ (portBits read (scrDExtraBits probeRows) a).take 17 := by
    rw [p0Ports, WEX.portBits_append, extra0Ports_bits]; rfl
  have hlen : site2Wires.length = (site2Bits read probeRows a).length := by
    simp [site2Wires, cxWord, cyWord, site2Bits, portBits, site2Ports_length]
  rw [← xMask_append site2Wires extra0Wires _ _ hlen, ← heq, ← p0Ports_targets probeRows]
  exact portMask_eq_xMask read (p0Ports probeRows) a p0Ports_nodup q

private theorem xor_three_yTail (kS kE : List Bool)
    (hkS : kS.length = 258) (hkE : kE.length = 255) (q : Wire) :
    (xMask (yTail.take 17) (kE.take 17) q ^^
      xMask ((yTail.drop 17).take 95) ((kE.drop 17).take 95) q ^^
      xMask (scrShortTargets ++ yTail.drop 112) (kS ++ kE.drop 112) q) =
      xMask scrDTargets (kS ++ kE) q := by
  have hsT : scrShortTargets.length = kS.length := by rw [scrShortTargets_eq, hkS]; simp
  have h1 : (yTail.take 17).length = (kE.take 17).length := by simp [yTail_len, hkE]
  have h2 : ((yTail.drop 17).take 95).length = ((kE.drop 17).take 95).length := by simp [yTail_len, hkE]
  have h12 : (yTail.take 17 ++ (yTail.drop 17).take 95).length = (kE.take 17 ++ (kE.drop 17).take 95).length := by
    simp [h1, h2]
  have hdt : scrDTargets = scrShortTargets ++ yTail := by
    rw [scrDTargets, scrShortTargets, yTail, List.append_assoc, List.take_append_drop]
  have hkE_split : kE = kE.take 17 ++ (kE.drop 17).take 95 ++ kE.drop 112 := by
    have h2' : (kE.drop 17).take 95 ++ kE.drop 112 = kE.drop 17 := by
      rw [show (112 : Nat) = 17 + 95 from rfl, ← List.drop_drop]
      exact List.take_append_drop 95 (kE.drop 17)
    rw [List.append_assoc, h2', List.take_append_drop]
  rw [hdt, xMask_append scrShortTargets yTail kS kE hsT,
    xMask_append scrShortTargets (yTail.drop 112) kS (kE.drop 112) hsT]
  have hy_eq : xMask yTail kE q =
      ((xMask (yTail.take 17) (kE.take 17) q ^^
        xMask ((yTail.drop 17).take 95) ((kE.drop 17).take 95) q) ^^
        xMask (yTail.drop 112) (kE.drop 112) q) := by
    conv_lhs => rw [yTail_split, hkE_split]
    rw [xMask_append _ _ _ _ h12, xMask_append _ _ _ _ h1]
  rw [hy_eq]
  cases xMask scrShortTargets kS q <;>
    cases xMask (yTail.take 17) (kE.take 17) q <;>
    cases xMask ((yTail.drop 17).take 95) ((kE.drop 17).take 95) q <;>
    cases xMask (yTail.drop 112) (kE.drop 112) q <;> rfl

private theorem xor5_dist (x e a b c : Bool) :
    (((x ^^ (e && a)) ^^ (e && b)) ^^ (e && c)) = (x ^^ (e && ((a ^^ b) ^^ c))) := by
  cases x <;> cases e <;> cases a <;> cases b <;> cases c <;> rfl

private theorem xAddProg_run (vx vy : Nat) (hvx : vx < ECDSAAdd.p) (hvy : vy < ECDSAAdd.p)
    (s : ECDSAAdd.State) (m : List Bool)
    (hsx : ECDSAAdd.regValue cxWord s.basis = vx)
    (hsy : ECDSAAdd.regValue streamLayout.point.x s.basis = vy)
    (hhi : s.basis 14371 = false) (hfl : s.basis 14847 = false)
    (hca : ∀ q ∈ addCarry, s.basis q = false) (hci : s.basis 14372 = false) :
    (ECDSAAdd.run xAddProg m s).phase = s.phase ∧
    ECDSAAdd.regValue streamLayout.point.x (ECDSAAdd.run xAddProg m s).basis = (vx + vy) % ECDSAAdd.p ∧
    ∀ q, q ∉ streamLayout.point.x → (ECDSAAdd.run xAddProg m s).basis q = s.basis q := by
  have h := xAdd.program_correct 256 SquareReduction.c ECDSAAdd.p xAdd_widths xAdd_nodup
    p_pos_facts.1 p_pos_facts.2.1 p_pos_facts.2.2 vx vy hvx hvy s m hsx hsy hhi hfl hca hci
  unfold xAddProg; exact h

private theorem yAddProg_run (vx vy : Nat) (hvx : vx < ECDSAAdd.p) (hvy : vy < ECDSAAdd.p)
    (s : ECDSAAdd.State) (m : List Bool)
    (hsx : ECDSAAdd.regValue cyWord s.basis = vx)
    (hsy : ECDSAAdd.regValue streamLayout.point.y s.basis = vy)
    (hhi : s.basis 14371 = false) (hfl : s.basis 14847 = false)
    (hca : ∀ q ∈ addCarry, s.basis q = false) (hci : s.basis 14372 = false) :
    (ECDSAAdd.run yAddProg m s).phase = s.phase ∧
    ECDSAAdd.regValue streamLayout.point.y (ECDSAAdd.run yAddProg m s).basis = (vx + vy) % ECDSAAdd.p ∧
    ∀ q, q ∉ streamLayout.point.y → (ECDSAAdd.run yAddProg m s).basis q = s.basis q := by
  have h := yAdd.program_correct 256 SquareReduction.c ECDSAAdd.p yAdd_widths yAdd_nodup
    p_pos_facts.1 p_pos_facts.2.1 p_pos_facts.2.2 vx vy hvx hvy s m hsx hsy hhi hfl hca hci
  unfold yAddProg; exact h

private theorem origCornerRef_split (read : ConstantBit 32768 → Bool) (a : Nat)
    (st : ECDSAAdd.State) (m0 m2b : List Bool)
    (hm0 : m0.length = ECDSAAdd.measurementCount lit0) :
    let kPre := ECDSAAdd.measurementCount xAddProg + ECDSAAdd.measurementCount negYProg + ECDSAAdd.measurementCount yAddProg
    let kCN := ECDSAAdd.measurementCount cornerNegProg
    let m_s2 := m0.take kPre ++ m0.drop (kPre + kCN)
    let m_cn := (m0.drop kPre).take kCN
    ECDSAAdd.run (origCornerRef read a) (cornerPerm m0 m2b) st =
      ECDSAAdd.run ((specialize (WEX.cornerUnit₁ ++ WEX.cornerUnit₂) a).instantiate read) m2b
        (ECDSAAdd.run cornerNegProg m_cn
          (ECDSAAdd.run (ECDSAAdd.Frontier.zrep streamLayout) List.nil
            (ECDSAAdd.run ((specialize (site2 probeRows).code a).instantiate read) m_s2 st))) := by
  intro kPre kCN m_s2 m_cn
  have hp2 : ECDSAAdd.measurementCount pair2Prog = kPre + ECDSAAdd.measurementCount negYProg := by
    have hp2' : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
    rw [hp2']; simp only [ECDSAAdd.measurementCount_append, kPre]
  have hms2_len : m_s2.length = ECDSAAdd.measurementCount ((specialize (site2 probeRows).code a).instantiate read) := by
    have hs2 : (specialize (site2 probeRows).code a).instantiate read =
        site2Load read probeRows a ++ (pair2Prog ++ site2Load read probeRows a) := by
      rw [site2_code, site2_inst]
    rw [hs2, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount_append, site2Load_records]
    simp only [m_s2, kCN, List.length_append, List.length_take, List.length_drop, hm0, lit0_meas, hp2]
    generalize kPre = a1
    generalize ECDSAAdd.measurementCount negYProg = a2
    generalize ECDSAAdd.measurementCount cornerNegProg = a3
    omega
  have hmcn_len : m_cn.length = ECDSAAdd.measurementCount cornerNegProg := by
    simp only [m_cn, kCN, List.length_take, List.length_drop, hm0, lit0_meas, hp2]
    generalize kPre = a1
    generalize ECDSAAdd.measurementCount negYProg = a2
    generalize ECDSAAdd.measurementCount cornerNegProg = a3
    omega
  have hperm : cornerPerm m0 m2b = m_s2 ++ (m_cn ++ m2b) := by
    simp only [cornerPerm, m_s2, m_cn, kPre, kCN, List.append_assoc]
  rw [origCornerRef, List.append_assoc, List.append_assoc, hperm,
    run_append_records _ _ m_s2 (m_cn ++ m2b) st hms2_len,
    run_zero_append _ _ zrep_records, run_append_records _ _ m_cn m2b _ hmcn_len]

set_option maxHeartbeats 1000000 in
theorem corner_fused_run (read : ConstantBit 32768 → Bool) (a : Nat)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (probeRows a) (.some hc))
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) (st : ECDSAAdd.State)
    (hv : PointDialogValues streamLayout X Y G base st.basis)
    (hroot : base windowRoot = true)
    (hctl : base streamLayout.control = true)
    (hflag : G = true → base streamLayout.infinitySelect = false ∧
      base streamLayout.doubleSelect = false ∧
      base streamLayout.genericSelect = false ∧
      base streamLayout.core.equalNegY = false)
    (m0 m2b : List Bool)
    (hm0 : m0.length = ECDSAAdd.measurementCount lit0)
    (hm2b : m2b.length = ECDSAAdd.measurementCount cornerA2Prog) :
    let sL0 : ECDSAAdd.State := ⟨st.phase, tableXorState (portMask read (p0Ports probeRows) a) true st.basis⟩
    let s0 := ECDSAAdd.run lit0 m0 sL0
    let sA : ECDSAAdd.State := ⟨s0.phase, clearRegister p0ClearWires s0.basis⟩
    let sL1 : ECDSAAdd.State := ⟨sA.phase, tableXorState (portMask read (p1Ports probeRows) a) true sA.basis⟩
    let s1 := ECDSAAdd.run lit1 List.nil sL1
    let sB : ECDSAAdd.State := ⟨s1.phase, clearRegister extra1Wires s1.basis⟩
    let sL2 : ECDSAAdd.State := ⟨sB.phase, tableXorState (portMask read (p2Ports probeRows) a) true sB.basis⟩
    let s2a := ECDSAAdd.run lit2a List.nil sL2
    let sC : ECDSAAdd.State := ⟨s2a.phase, clearRegister extra2Wires s2a.basis⟩
    let s2b := ECDSAAdd.run lit2b m2b sC
    let sOut : ECDSAAdd.State := ⟨s2b.phase, clearRegister finalClearWires s2b.basis⟩
    (∀ q ∈ p0ClearPorts probeRows, s0.basis q.target = decide (read (q.ref a) = q.value)) ∧
    (∀ w ∈ streamLayout.dialogPool, w ∉ keepWires → sA.basis w = false) ∧
    (∀ q ∈ p1Ports probeRows, s1.basis q.target = decide (read (q.ref a) = q.value)) ∧
    (∀ w ∈ streamLayout.dialogPool, w ∉ keepWires → sB.basis w = false) ∧
    (∀ q ∈ extra2Ports probeRows, s2a.basis q.target = decide (read (q.ref a) = q.value)) ∧
    (∀ q ∈ finalClearPorts probeRows, s2b.basis q.target = decide (read (q.ref a) = q.value)) ∧
    s2b.basis 14373 = false ∧
    sOut = ECDSAAdd.run (origCornerRef read a) (cornerPerm m0 m2b) st := by
  intro sL0 s0 sA sL1 s1 sB sL2 s2a sC s2b sOut
  -- Basic clean/wire facts from `hv`
  have hclean : ∀ q ∈ streamLayout.dialogPool, st.basis q = false :=
    (ECDSAAdd.Arithmetic.regValue_zero _ _).mp hv.clean
  have st_root : st.basis windowRoot = true := (hv.rest _ root_not_xy).trans hroot
  have st_ctl : st.basis streamLayout.control = true := (hv.rest _ control_not_xy).trans hctl
  have st_gen : st.basis streamLayout.core.generic = G := hv.generic
  have st_flags_eq : ∀ w ∈ [streamLayout.infinitySelect, streamLayout.doubleSelect,
      streamLayout.genericSelect, streamLayout.core.equalNegY], st.basis w = base w := fun w hw => by
    apply hv.rest w
    simp only [List.mem_cons, List.not_mem_nil, or_false, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl] at hw
    simp only [streamLayout_point, List.mem_append, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  -- Helper membership bounds
  have hpx_b : ∀ q ∈ streamLayout.point.x, 263 ≤ q ∧ q < 519 := fun q hq => by
    rw [streamLayout_point, List.mem_range'_1] at hq; exact hq
  have hpy_b : ∀ q ∈ streamLayout.point.y, 580 ≤ q ∧ q < 836 := fun q hq => by
    rw [streamLayout_point, List.mem_range'_1] at hq; exact hq
  have hp0_b : ∀ q ∈ site2Wires ++ extra0Wires,
      (14374 ≤ q ∧ q < 14630) ∨ q = 14883 ∨ (15399 ≤ q ∧ q < 15654) ∨ (14849 ≤ q ∧ q < 14866) := fun q hq => by
    simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at hq
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hcy_b : ∀ q ∈ cyWord, q = 14883 ∨ (15399 ≤ q ∧ q < 15654) := fun q hq => by
    simp only [cyWord, List.mem_cons, List.mem_range'_1] at hq; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hcx_b : ∀ q ∈ cxWord, 14374 ≤ q ∧ q < 14630 := fun q hq => by
    simp only [cxWord, List.mem_range'_1] at hq; exact hq
  have hdt_b : ∀ q ∈ scrDTargets, q = 838 ∨ (263 ≤ q ∧ q < 519) ∨ (580 ≤ q ∧ q < 836) := fun q hq => by
    simp only [scrDTargets, streamLayout_point, List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1] at hq
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hps_b : ∀ q ∈ pairScratch, (14115 ≤ q ∧ q < 14373) ∨ q = 14847 := fun q hq => by
    simp only [pairScratch, addCarry, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hq
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  -- sL0 characterization
  have sL0_out : ∀ q, q ∉ site2Wires ++ extra0Wires → sL0.basis q = st.basis q := fun q hq => by
    dsimp only [sL0]
    exact tableXorState_outside _ _ _ _ (fun hm => hq (by rw [← p0Ports_targets probeRows]; exact tableBitsMask_subset _ _ hm))
  have sL0_in : ∀ q ∈ site2Wires ++ extra0Wires,
      sL0.basis q = (xMask site2Wires (site2Bits read probeRows a) q ^^
        xMask extra0Wires ((portBits read (scrDExtraBits probeRows) a).take 17) q) := fun q hq => by
    dsimp only [sL0]
    simp only [tableXorState, Bool.true_and, hclean q (mem_p0Wires_pool hq), Bool.false_xor]
    exact xMask_p0_split read a q
  have sL0_site2 : ∀ q ∈ site2Wires, sL0.basis q = xMask site2Wires (site2Bits read probeRows a) q := fun q hq => by
    rw [sL0_in q (List.mem_append_left _ hq), xMask_outside extra0Wires _ q (fun hm => by
      simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at hq hm
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega), Bool.xor_false]
  have sL0_extra0 : extra0Wires.map sL0.basis = (portBits read (scrDExtraBits probeRows) a).take 17 := by
    apply List.ext_getElem
    · simp [extra0Wires_len, portBits, scrDExtraBits_length]
    · intro i hi1 hi2
      rw [List.getElem_map]
      have hi1' : i < extra0Wires.length := by simpa using hi1
      have hmem : extra0Wires[i]'hi1' ∈ extra0Wires := List.getElem_mem hi1'
      rw [sL0_in _ (List.mem_append_right _ hmem), xMask_outside site2Wires _ _ (fun hm => by
        simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at hmem hm
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega), Bool.false_xor]
      exact xMask_get extra0Wires _ (by rw [extra0Wires]; exact List.nodup_range')
        (by simp [extra0Wires_len, portBits, scrDExtraBits_length]) i hi1'
  have sL0_cx : ECDSAAdd.regValue cxWord sL0.basis = cx.val := loaded_cx2 read probeRows a hc hr sL0.basis sL0_site2
  have sL0_cy : ECDSAAdd.regValue cyWord sL0.basis = (-cy).val := loaded_cy2 read probeRows a hc hr sL0.basis sL0_site2
  have sL0_px : ECDSAAdd.regValue streamLayout.point.x sL0.basis = X.val :=
    (ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq => sL0_out q (fun hm => by
      have := hpx_b q hq; have := hp0_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))).trans hv.x
  have sL0_py : ECDSAAdd.regValue streamLayout.point.y sL0.basis = Y.val :=
    (ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq => sL0_out q (fun hm => by
      have := hpy_b q hq; have := hp0_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))).trans hv.y
  have sL0_ps : ∀ q ∈ pairScratch, sL0.basis q = false := fun q hq => by
    rw [sL0_out q (fun hm => by have := hps_b q hq; have := hp0_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
    exact hclean q (pairScratch_pool q hq)
  -- Unpack `lit0` measurement splits
  let kX := ECDSAAdd.measurementCount xAddProg
  let kN := ECDSAAdd.measurementCount negYProg
  let kY := ECDSAAdd.measurementCount yAddProg
  let kCN := ECDSAAdd.measurementCount cornerNegProg
  have hmc_x : ECDSAAdd.measurementCount xAddProg = kX := rfl
  have hmc_n : ECDSAAdd.measurementCount negYProg = kN := rfl
  have hmc_y : ECDSAAdd.measurementCount yAddProg = kY := rfl
  have hmc_cn : ECDSAAdd.measurementCount cornerNegProg = kCN := rfl
  have hmc_w : ECDSAAdd.measurementCount (scrW1 ++ scrCWriteFused ++ scrW2) = 0 := by
    simp [scrW1, scrW2, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount, scrCWriteFused_meas]
  have hmc_e0 : ECDSAAdd.measurementCount (scrSw1 ++ ccxList streamLayout.core.equalNegY extra0Wires (yTail.take 17) ++ scrSw1) = 0 := by
    simp [scrSw1, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount, ccxList_meas]
  let m_x := m0.take kX
  let m_n1 := (m0.drop kX).take kN
  let m_y := (m0.drop (kX + kN)).take kY
  let m_cn := (m0.drop (kX + kN + kY)).take kCN
  let m_n2 := m0.drop (kX + kN + kY + kCN)
  have hs0_steps : s0 =
      ECDSAAdd.run (scrSw1 ++ ccxList streamLayout.core.equalNegY extra0Wires (yTail.take 17) ++ scrSw1) List.nil
        (ECDSAAdd.run negYProg m_n2
          (ECDSAAdd.run (scrW1 ++ scrCWriteFused ++ scrW2) List.nil
            (ECDSAAdd.run cornerNegProg m_cn
              (ECDSAAdd.run (ECDSAAdd.Frontier.zrep streamLayout) List.nil
                (ECDSAAdd.run yAddProg m_y
                  (ECDSAAdd.run negYProg m_n1
                    (ECDSAAdd.run xAddProg m_x sL0))))))) := by
    set pW := scrW1 ++ scrCWriteFused ++ scrW2
    set pE0 := scrSw1 ++ ccxList streamLayout.core.equalNegY extra0Wires (yTail.take 17) ++ scrSw1
    have hlit0 : lit0 = xAddProg ++ (negYProg ++ (yAddProg ++ (ECDSAAdd.Frontier.zrep streamLayout ++
        (cornerNegProg ++ (pW ++ (negYProg ++ pE0)))))) := by
      dsimp only [lit0, pW, pE0]; simp only [List.append_assoc]
    dsimp only [s0]
    rw [hlit0, ECDSAAdd.run_append xAddProg, ECDSAAdd.run_append negYProg, ECDSAAdd.run_append yAddProg,
      run_zero_append _ _ zrep_records, ECDSAAdd.run_append cornerNegProg,
      run_zero_append _ _ hmc_w, ECDSAAdd.run_append negYProg,
      run_zero_records _ hmc_e0]
    have hmn2_take : (m0.drop (kX + (kN + (kY + kCN)))).take kN = m0.drop (kX + (kN + (kY + kCN))) := by
      apply List.take_of_length_le
      have hp2 : ECDSAAdd.measurementCount pair2Prog = kX + kN + kY + kN := by
        have hp2' : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
        rw [hp2']; simp only [ECDSAAdd.measurementCount_append, kX, kN, kY]
      rw [List.length_drop, hm0, lit0_meas, hp2]; omega
    simp only [List.drop_drop, m_x, m_n1, m_y, m_cn, m_n2, Nat.add_assoc, hmc_x, hmc_n, hmc_y, hmc_cn, hmn2_take]
  -- Trace substeps inside `lit0`: s_1..s_8
  set s_1 := ECDSAAdd.run xAddProg m_x sL0 with hs_1
  set s_2 := ECDSAAdd.run negYProg m_n1 s_1 with hs_2
  set s_3 := ECDSAAdd.run yAddProg m_y s_2 with hs_3
  set s_4 := ECDSAAdd.run (ECDSAAdd.Frontier.zrep streamLayout) List.nil s_3 with hs_4
  set s_5 := ECDSAAdd.run cornerNegProg m_cn s_4 with hs_5
  set s_6 := ECDSAAdd.run (scrW1 ++ scrCWriteFused ++ scrW2) List.nil s_5 with hs_6
  set s_7 := ECDSAAdd.run negYProg m_n2 s_6 with hs_7
  -- Step 1: xAddProg
  have hcy0 : cy ≠ 0 := ECDSAAdd.Frontier.curve_y_ne_zero hc
  obtain ⟨A, hA, hA1, hA2, hA3⟩ := pair2_word cy Y G hcy0
  have hA_val : A = (if G then (-cy).val else cy.val) := by
    cases G <;> simp only [Bool.false_eq_true, ↓reduceIte] at hA1 ⊢
    · have hne : cy.val ≠ 0 := fun h => hcy0 ((ZMod.val_eq_zero cy).mp h)
      have hnv : (-cy).val = ECDSAAdd.p - cy.val := neg_val_of_ne hcy0
      have hlt : cy.val < ECDSAAdd.p := cy.isLt
      rw [← hA1, hnv]; omega
    · exact hA1.symm
  have hxAdd : xAdd.program SquareReduction.c ECDSAAdd.p = xAddProg := by unfold xAddProg; rfl
  have hyAdd : yAdd.program SquareReduction.c ECDSAAdd.p = yAddProg := by unfold yAddProg; rfl
  have hst_b : ∀ q ∈ scrShortTargets, q = 838 ∨ (263 ≤ q ∧ q < 519) ∨ q = 580 := fun q hq => by
    rw [scrShortTargets_eq] at hq
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_range'_1, List.not_mem_nil, or_false] at hq
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have r_1 := xAddProg_run cx.val X.val cx.isLt X.isLt sL0 m_x
    sL0_cx sL0_px (sL0_ps 14371 (by simp [pairScratch])) (sL0_ps 14847 (by simp [pairScratch]))
    (fun q hq => sL0_ps q (List.mem_append_left _ hq)) (sL0_ps 14372 (by simp [pairScratch]))
  rw [← hs_1] at r_1
  have r_1x : ECDSAAdd.regValue streamLayout.point.x s_1.basis = (X + cx).val := by
    rw [r_1.2.1, ZMod.val_add, Nat.add_comm]
  -- Step 2: negYProg (first)
  have r_2 := negYProg_run (-cy).val (-cy).isLt s_1 m_n1
    ((ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq => r_1.2.2 q (fun hm => by
      have := hcy_b q hq; have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))).trans sL0_cy)
    ((ECDSAAdd.Arithmetic.regValue_zero _ _).mpr (fun q hq =>
      (r_1.2.2 q (fun hm => by have := hps_b q (List.mem_append_left _ hq); have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
        (sL0_ps q (List.mem_append_left _ hq))))
    ((r_1.2.2 14371 (fun hm => by have := hpx_b 14371 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans (sL0_ps 14371 (by simp [pairScratch])))
    ((r_1.2.2 14372 (fun hm => by have := hpx_b 14372 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans (sL0_ps 14372 (by simp [pairScratch])))
  have s1_gen : s_1.basis streamLayout.core.generic = G := by
    rw [r_1.2.2 _ (fun hm => by have := hpx_b _ hm; rw [sl_generic] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
      sL0_out _ (fun hm => by have := hp0_b _ hm; rw [sl_generic] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega), st_gen]
  rw [s1_gen, hA1, ← hs_2] at r_2
  -- Step 3: yAddProg
  have r_3 := yAddProg_run A Y.val hA Y.isLt s_2 m_y r_2.2.1
    ((ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq =>
      (r_2.2.2 q (fun hm => by have := hpy_b q hq; have := hcy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      (r_1.2.2 q (fun hm => by have := hpy_b q hq; have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)))).trans sL0_py)
    ((r_2.2.2 14371 (fun hm => by have := hcy_b 14371 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((r_1.2.2 14371 (fun hm => by have := hpx_b 14371 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans (sL0_ps 14371 (by simp [pairScratch]))))
    ((r_2.2.2 14847 (fun hm => by have := hcy_b 14847 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((r_1.2.2 14847 (fun hm => by have := hpx_b 14847 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans (sL0_ps 14847 (by simp [pairScratch]))))
    (fun q hq =>
      (r_2.2.2 q (fun hm => by have := hps_b q (List.mem_append_left _ hq); have := hcy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((r_1.2.2 q (fun hm => by have := hps_b q (List.mem_append_left _ hq); have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
        (sL0_ps q (List.mem_append_left _ hq))))
    ((r_2.2.2 14372 (fun hm => by have := hcy_b 14372 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((r_1.2.2 14372 (fun hm => by have := hpx_b 14372 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans (sL0_ps 14372 (by simp [pairScratch]))))
  rw [← hs_3] at r_3
  have r_3y : ECDSAAdd.regValue streamLayout.point.y s_3.basis = (Y + (if G then -cy else cy)).val := by
    rw [r_3.2.1, hA3]
  -- Step 4: zrep
  have r_4 := ECDSAAdd.Frontier.zrep_run streamLayout streamLayout_widths streamLayout_nodup s_3 List.nil
  rw [← hs_4] at r_4
  -- Step 5: cornerNegProg
  have s4_pool258 : Clean (streamLayout.dialogPool.take 258) s_4.basis := fun q hq => by
    rw [mem_pool_take 258 (by decide)] at hq
    rw [r_4.2.1 q (fun hm => by have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
      r_3.2.2 q (fun hm => by have := hpy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
      r_2.2.2 q (fun hm => by have := hcy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
      r_1.2.2 q (fun hm => by have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
      sL0_out q (fun hm => by have := hp0_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
    exact hclean q (List.mem_of_mem_take ((mem_pool_take 258 (by decide)).mpr hq))
  have s4_py : ECDSAAdd.regValue streamLayout.point.y s_4.basis = (Y + (if G then -cy else cy)).val :=
    (ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq => r_4.2.1 q (fun hm => by
      have := hpy_b q hq; have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))).trans r_3y
  have r_5 := cornerNegProg_effect s_4 m_cn (s4_py.symm ▸ (Y + (if G then -cy else cy)).isLt) s4_pool258
  rw [← hs_5] at r_5
  -- Helper: wires outside `point.x ++ point.y ++ cyWord` are unchanged from `sL0` through `s_5`
  have s5_out : ∀ q, q ∉ streamLayout.point.x → q ∉ streamLayout.point.y → q ∉ cyWord → s_5.basis q = sL0.basis q :=
    fun q h1 h2 h3 => (r_5.2.2 q h2).trans ((r_4.2.1 q h1).trans ((r_3.2.2 q h2).trans ((r_2.2.2 q h3).trans (r_1.2.2 q h1))))
  have s5_out_st : ∀ q, q ∉ streamLayout.point.x → q ∉ streamLayout.point.y → q ∉ site2Wires ++ extra0Wires →
      s_5.basis q = st.basis q := fun q h1 h2 h3 =>
    (s5_out q h1 h2 (fun hm => h3 (List.mem_append_left _ (List.mem_append_right _ hm)))).trans (sL0_out q h3)
  -- Step 6: scrW1 ++ scrCWriteFused ++ scrW2
  have s5_gen : s_5.basis streamLayout.core.generic = G := by
    rw [s5_out_st _ (fun hm => by have := hpx_b _ hm; rw [sl_generic] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      (fun hm => by have := hpy_b _ hm; rw [sl_generic] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      (fun hm => by have := hp0_b _ hm; rw [sl_generic] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega), st_gen]
  have s5_fl : ∀ w ∈ [streamLayout.infinitySelect, streamLayout.doubleSelect,
      streamLayout.genericSelect, streamLayout.core.equalNegY], s_5.basis w = base w := fun w hw => by
    have hwb : w = 19816 ∨ w = 19815 ∨ w = 19814 ∨ w = 14112 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
        sl_infinitySelect] at hw
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    rw [s5_out_st w (fun hm => by have := hpx_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      (fun hm => by have := hpy_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      (fun hm => by have := hp0_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
    exact st_flags_eq w hw
  have s5_cx : ECDSAAdd.regValue cxWord s_5.basis = cx.val :=
    (ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq => s5_out q
      (fun hm => by have := hcx_b q hq; have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      (fun hm => by have := hcx_b q hq; have := hpy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      (fun hm => by have := hcx_b q hq; have := hcy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))).trans sL0_cx
  have s5_cy : ECDSAAdd.regValue cyWord s_5.basis = if G then (-cy).val else cy.val := by
    rw [← hA_val]
    exact (ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq =>
      (r_5.2.2 q (fun hm => by have := hcy_b q hq; have := hpy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((r_4.2.1 q (fun hm => by have := hcy_b q hq; have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      (r_3.2.2 q (fun hm => by have := hcy_b q hq; have := hpy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))))).trans r_2.2.1
  have s6_eq : s_6 = ECDSAAdd.run (scrW1 ++ cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts probeRows) a) ++ scrW2) List.nil s_5 :=
    scrCWriteFused_run_eq read a hc hr G s_5 s5_gen (fun hG => by
      obtain ⟨h1, h2, h3, h4⟩ := hflag hG
      exact ⟨(s5_fl _ (by simp)).trans h1, (s5_fl _ (by simp)).trans h2, (s5_fl _ (by simp)).trans h3, (s5_fl _ (by simp)).trans h4⟩)
      s5_cx s5_cy
  have s6_eff := scrW_cBits_effect (portBits read (scrCPorts probeRows) a) s_5
  rw [← s6_eq] at s6_eff
  have s6_phase := state_eq_phase s6_eff
  have s6_basis := state_eq_basis s6_eff
  have s6_out : ∀ q, q ∉ scrDTargets → s_6.basis q = s_5.basis q := fun q hq => by
    rw [s6_basis, xMask_outside _ _ _ hq, Bool.and_false, Bool.xor_false]
  -- Step 7: negYProg (second) restores cyWord back to -cy
  have r_7 := negYProg_run A hA s_6 m_n2
    ((ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun q hq => s6_out q (fun hm => by
      have := hcy_b q hq; have := hdt_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))).trans (s5_cy.trans hA_val.symm))
    ((ECDSAAdd.Arithmetic.regValue_zero _ _).mpr (fun q hq =>
      (s6_out q (fun hm => by have := hps_b q (List.mem_append_left _ hq); have := hdt_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((s5_out q (fun hm => by have := hps_b q (List.mem_append_left _ hq); have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
        (fun hm => by have := hps_b q (List.mem_append_left _ hq); have := hpy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
        (fun hm => by have := hps_b q (List.mem_append_left _ hq); have := hcy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
        (sL0_ps q (List.mem_append_left _ hq)))))
    ((s6_out 14371 (fun hm => by have := hdt_b 14371 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((s5_out 14371 (fun hm => by have := hpx_b 14371 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
        (fun hm => by have := hpy_b 14371 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
        (fun hm => by have := hcy_b 14371 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans (sL0_ps 14371 (by simp [pairScratch]))))
    ((s6_out 14372 (fun hm => by have := hdt_b 14372 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((s5_out 14372 (fun hm => by have := hpx_b 14372 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
        (fun hm => by have := hpy_b 14372 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
        (fun hm => by have := hcy_b 14372 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans (sL0_ps 14372 (by simp [pairScratch]))))
  have s6_gen : s_6.basis streamLayout.core.generic = G :=
    (s6_out _ (fun hm => by have := hdt_b _ hm; rw [sl_generic] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans s5_gen
  rw [s6_gen, hA2, ← hs_7] at r_7
  have s7_cy_eq : ∀ q ∈ cyWord, s_7.basis q = sL0.basis q :=
    (ECDSAAdd.Arithmetic.regValue_eq_iff cyWord s_7.basis sL0.basis).mp (r_7.2.1.trans sL0_cy.symm)
  have s7_p0_eq : ∀ q ∈ site2Wires ++ extra0Wires, s_7.basis q = sL0.basis q := fun q hq => by
    by_cases hcy : q ∈ cyWord
    · exact s7_cy_eq q hcy
    · exact (r_7.2.2 q hcy).trans ((s6_out q (fun hm => by have := hp0_b q hq; have := hdt_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
        (s5_out q (fun hm => by have := hp0_b q hq; have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
          (fun hm => by have := hp0_b q hq; have := hpy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega) hcy))
  -- Step 8: extra0 scrSw
  set kS := portBits read (scrShortBits probeRows) a with hkS
  set kE := portBits read (scrDExtraBits probeRows) a with hkE
  set kC := portBits read (scrCPorts probeRows) a with hkC
  set eFlag := base streamLayout.core.equalNegY ^^ base streamLayout.doubleSelect with heFlag
  have s7_e : (s_7.basis streamLayout.core.equalNegY ^^ s_7.basis streamLayout.doubleSelect) = eFlag := by
    have he1 : s_7.basis streamLayout.core.equalNegY = base streamLayout.core.equalNegY :=
      (r_7.2.2 _ (fun hm => by have := hcy_b _ hm; rw [sl_equalNegY] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((s6_out _ (fun hm => by have := hdt_b _ hm; rw [sl_equalNegY] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
        (s5_fl _ (by simp)))
    have hd1 : s_7.basis streamLayout.doubleSelect = base streamLayout.doubleSelect :=
      (r_7.2.2 _ (fun hm => by have := hcy_b _ hm; rw [sl_doubleSelect] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
      ((s6_out _ (fun hm => by have := hdt_b _ hm; rw [sl_doubleSelect] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
        (s5_fl _ (by simp)))
    rw [he1, hd1]
  have s0_eq : s0 = ⟨s_7.phase, fun q => s_7.basis q ^^ (eFlag && xMask (yTail.take 17) (kE.take 17) q)⟩ := by
    rw [hs0_steps, scrSw_ccx_eq_cBits extra0Wires (yTail.take 17) (kE.take 17) s_7
      (fun u hu hm => by have hm' := List.mem_of_mem_take hm; simp only [extra0Wires, yTail_eq, List.mem_range'_1] at hu hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      ⟨fun hm => by have hm' := List.mem_of_mem_take hm; rw [sl_equalNegY, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega,
       fun hm => by have hm' := List.mem_of_mem_take hm; rw [sl_doubleSelect, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩
      (fun hm => by simp only [extra0Wires, sl_equalNegY, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      ((List.map_congr_left (fun u hu => s7_p0_eq u (List.mem_append_right _ hu))).trans sL0_extra0),
      scrSw_cBits_effect (yTail.take 17) (kE.take 17)
        ⟨fun hm => by have hm' := List.mem_of_mem_take hm; rw [sl_equalNegY, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega,
         fun hm => by have hm' := List.mem_of_mem_take hm; rw [sl_doubleSelect, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩ s_7]
    exact congrArg (ECDSAAdd.State.mk s_7.phase) (funext fun q => by rw [s7_e])
  have s0_phase := state_eq_phase s0_eq
  have s0_basis := state_eq_basis s0_eq
  have s0_p0_eq : ∀ q ∈ site2Wires ++ extra0Wires, s0.basis q = sL0.basis q := fun q hq => by
    rw [s0_basis, xMask_outside (yTail.take 17) _ q (fun hm => by
      have hm' := List.mem_of_mem_take hm; have := hp0_b q hq; rw [yTail_eq, List.mem_range'_1] at hm'
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega), Bool.and_false, Bool.xor_false]
    exact s7_p0_eq q hq
  -- Prove goal 1: `p0ClearPorts` loaded in `s0`
  have hg1 : ∀ q ∈ p0ClearPorts probeRows, s0.basis q.target = decide (read (q.ref a) = q.value) := by
    intro q hq
    have hmem_p0 : q ∈ p0Ports probeRows := by
      simp only [p0ClearPorts, p0Ports, site2Ports, List.mem_append, List.mem_cons] at hq ⊢
      rcases hq with hq | hq
      · left; right; right; exact hq
      · right; exact hq
    have ht_mem : q.target ∈ site2Wires ++ extra0Wires := by
      rw [← p0Ports_targets probeRows]; exact List.mem_map_of_mem hmem_p0
    rw [s0_p0_eq q.target ht_mem]
    dsimp only [sL0]
    simp only [tableXorState, Bool.true_and, hclean q.target (mem_p0Wires_pool ht_mem), Bool.false_xor]
    exact port_selected read (p0Ports probeRows) a p0Ports_nodup q hmem_p0
  -- Prove goal 2: `sA` clean on `dialogPool \ keepWires`
  have hg2 : ∀ w ∈ streamLayout.dialogPool, w ∉ keepWires → sA.basis w = false := by
    intro w hw hnk
    dsimp only [sA]
    by_cases hpc : w ∈ p0ClearWires
    · exact clearRegister_clean p0ClearWires s0.basis w hpc
    · rw [MeasuredClear.clearRegister_frame p0ClearWires s0.basis w hpc]
      have hnp0 : w ∉ site2Wires ++ extra0Wires := fun hm => by
        simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at hm
        simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hnk
        simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hpc
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have hwb : 14115 ≤ w ∧ w < 16728 := by
        have h1 : w ∈ streamLayout.dialogPool.take 2613 := by
          have ht : streamLayout.dialogPool.take 2613 = streamLayout.dialogPool := by simp [dialogPool]
          rwa [ht]
        exact (mem_pool_take 2613 (le_refl _)).mp h1
      rw [s0_basis, xMask_outside (yTail.take 17) _ w (fun hm => by
        have hm' := List.mem_of_mem_take hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
        Bool.and_false, Bool.xor_false,
        r_7.2.2 w (fun hm => hnp0 (List.mem_append_left _ (List.mem_append_right _ hm))),
        s6_out w (fun hm => by have := hdt_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
        s5_out_st w (fun hm => by have := hpx_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
          (fun hm => by have := hpy_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega) hnp0]
      exact hclean w hw
  -- Pass 1: sL1, s1, sB
  have hmem_e1_pool : ∀ w ∈ extra1Wires, w ∈ streamLayout.dialogPool ∧ w ∉ keepWires := fun w hw => by
    simp only [extra1Wires, List.mem_range'_1] at hw
    refine ⟨List.mem_of_mem_take ((mem_pool_take 2613 (by decide)).mpr (by dsimp only [Wire, ECDSAAdd.Wire] at *; omega)), ?_⟩
    simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have sL1_out : ∀ q, q ∉ extra1Wires → sL1.basis q = sA.basis q := fun q hq => by
    dsimp only [sL1]
    exact tableXorState_outside _ _ _ _ (fun hm => hq (by rw [← p1Ports_targets probeRows]; exact tableBitsMask_subset _ _ hm))
  have sL1_extra1 : extra1Wires.map sL1.basis = (kE.drop 17).take 95 := by
    apply List.ext_getElem
    · simp [extra1Wires_len, hkE, portBits, scrDExtraBits_length]
    · intro i hi1 hi2
      rw [List.getElem_map]
      have hi1' : i < extra1Wires.length := by simpa using hi1
      have hmem := List.getElem_mem hi1'
      have ⟨hp, hnk⟩ := hmem_e1_pool _ hmem
      dsimp only [sL1]
      simp only [tableXorState, Bool.true_and, hg2 _ hp hnk, Bool.false_xor]
      rw [portMask_eq_xMask read (p1Ports probeRows) a p1Ports_nodup, p1Ports_targets, p1Ports, extra1Ports_bits, ← hkE]
      exact xMask_get extra1Wires ((kE.drop 17).take 95)
        (by rw [extra1Wires]; exact List.nodup_range')
        (by simp [extra1Wires_len, hkE, portBits, scrDExtraBits_length]) i hi1'
  have sA_fl : sA.basis streamLayout.core.equalNegY = base streamLayout.core.equalNegY ∧
      sA.basis streamLayout.doubleSelect = base streamLayout.doubleSelect := by
    have hnot_pc (w : Wire) (hw : w = 14112 ∨ w = 19815) : w ∉ p0ClearWires := by
      simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    have hnot_yt (w : Wire) (hw : w = 14112 ∨ w = 19815) : w ∉ yTail.take 17 := fun hm => by
      have hm' := List.mem_of_mem_take hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    constructor
    · dsimp only [sA]
      rw [MeasuredClear.clearRegister_frame _ _ _ (hnot_pc _ (by rw [sl_equalNegY]; left; rfl)), s0_basis,
        xMask_outside _ _ _ (hnot_yt _ (by rw [sl_equalNegY]; left; rfl)), Bool.and_false, Bool.xor_false,
        r_7.2.2 _ (fun hm => by have := hcy_b _ hm; rw [sl_equalNegY] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
        s6_out _ (fun hm => by have := hdt_b _ hm; rw [sl_equalNegY] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
      exact s5_fl _ (by simp)
    · dsimp only [sA]
      rw [MeasuredClear.clearRegister_frame _ _ _ (hnot_pc _ (by rw [sl_doubleSelect]; right; rfl)), s0_basis,
        xMask_outside _ _ _ (hnot_yt _ (by rw [sl_doubleSelect]; right; rfl)), Bool.and_false, Bool.xor_false,
        r_7.2.2 _ (fun hm => by have := hcy_b _ hm; rw [sl_doubleSelect] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
        s6_out _ (fun hm => by have := hdt_b _ hm; rw [sl_doubleSelect] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
      exact s5_fl _ (by simp)
  have s1_eq : s1 = ⟨sL1.phase, fun q => sL1.basis q ^^ (eFlag && xMask ((yTail.drop 17).take 95) ((kE.drop 17).take 95) q)⟩ := by
    have hfl1 : streamLayout.core.equalNegY ∉ (yTail.drop 17).take 95 ∧ streamLayout.doubleSelect ∉ (yTail.drop 17).take 95 :=
      ⟨fun hm => by have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); rw [sl_equalNegY, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega,
       fun hm => by have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); rw [sl_doubleSelect, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩
    have hsL1_e : (sL1.basis streamLayout.core.equalNegY ^^ sL1.basis streamLayout.doubleSelect) = eFlag := by
      rw [sL1_out _ (fun hm => by rw [sl_equalNegY, extra1Wires, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
        sL1_out _ (fun hm => by rw [sl_doubleSelect, extra1Wires, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
        sA_fl.1, sA_fl.2]
    dsimp only [s1, lit1]
    rw [scrSw_ccx_eq_cBits extra1Wires ((yTail.drop 17).take 95) ((kE.drop 17).take 95) sL1
      (fun u hu hm => by have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); simp only [extra1Wires, yTail_eq, List.mem_range'_1] at hu hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      hfl1 (fun hm => by rw [sl_equalNegY, extra1Wires, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega) sL1_extra1,
      scrSw_cBits_effect _ _ hfl1 sL1]
    exact congrArg (ECDSAAdd.State.mk sL1.phase) (funext fun q => by rw [hsL1_e])
  have s1_phase := state_eq_phase s1_eq
  have s1_basis := state_eq_basis s1_eq
  have hg3 : ∀ q ∈ p1Ports probeRows, s1.basis q.target = decide (read (q.ref a) = q.value) := by
    intro q hq
    have ht_mem : q.target ∈ extra1Wires := by rw [← p1Ports_targets probeRows]; exact List.mem_map_of_mem hq
    have ⟨hp, hnk⟩ := hmem_e1_pool q.target ht_mem
    rw [s1_basis, xMask_outside _ _ q.target (fun hm => by
      have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); simp only [extra1Wires, yTail_eq, List.mem_range'_1] at ht_mem hm'
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega), Bool.and_false, Bool.xor_false]
    dsimp only [sL1]
    simp only [tableXorState, Bool.true_and, hg2 q.target hp hnk, Bool.false_xor]
    exact port_selected read (p1Ports probeRows) a p1Ports_nodup q hq
  have hsB_ph : sB.phase = s1.phase := state_phase_mk _ _
  have hsL1_ph : sL1.phase = sA.phase := state_phase_mk _ _
  have sB_eq : sB = ⟨sA.phase, fun q => sA.basis q ^^ (eFlag && xMask ((yTail.drop 17).take 95) ((kE.drop 17).take 95) q)⟩ := by
    refine state_ext ((hsB_ph.trans (s1_phase.trans hsL1_ph)).trans (state_phase_mk _ _).symm) ?_
    rw [state_basis_mk]
    funext q
    dsimp only [sB]
    by_cases he1 : q ∈ extra1Wires
    · rw [clearRegister_clean extra1Wires _ q he1]
      have ⟨hp, hnk⟩ := hmem_e1_pool q he1
      rw [hg2 q hp hnk, xMask_outside _ _ q (fun hm => by
        have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); simp only [extra1Wires, yTail_eq, List.mem_range'_1] at he1 hm'
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
      simp
    · rw [MeasuredClear.clearRegister_frame extra1Wires _ q he1, s1_basis, sL1_out q he1]
  have sB_phase := state_eq_phase sB_eq
  have sB_basis := state_eq_basis sB_eq
  have hg4 : ∀ w ∈ streamLayout.dialogPool, w ∉ keepWires → sB.basis w = false := fun w hw hnk => by
    rw [sB_basis, hg2 w hw hnk, xMask_outside _ _ w (fun hm => by
      have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm)
      have hwb : 14115 ≤ w ∧ w < 16728 := by
        have h1 : w ∈ streamLayout.dialogPool.take 2613 := by
          have ht : streamLayout.dialogPool.take 2613 = streamLayout.dialogPool := by simp [dialogPool]
          rwa [ht]
        exact (mem_pool_take 2613 (le_refl _)).mp h1
      rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
    simp
  -- Pass 2: sL2, s2a, sC
  have hmem_p2_pool : ∀ w ∈ scrShortWires ++ extra2Wires, w ∈ streamLayout.dialogPool ∧ w ∉ keepWires := fun w hw => by
    have hwb : (14884 ≤ w ∧ w < 15142) ∨ (15399 ≤ w ∧ w < 15542) := by
      rcases List.mem_append.mp hw with h | h
      · exact Or.inl (shortWires_bounds w h)
      · rw [extra2Wires, List.mem_range'_1] at h; exact Or.inr h
    refine ⟨List.mem_of_mem_take ((mem_pool_take 2613 (by decide)).mpr (by dsimp only [Wire, ECDSAAdd.Wire] at *; omega)), ?_⟩
    simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have sL2_out : ∀ q, q ∉ scrShortWires ++ extra2Wires → sL2.basis q = sB.basis q := fun q hq => by
    dsimp only [sL2]
    exact tableXorState_outside _ _ _ _ (fun hm => hq (by rw [← p2Ports_targets probeRows]; exact tableBitsMask_subset _ _ hm))
  have sL2_map : (scrShortWires ++ extra2Wires).map sL2.basis = kS ++ kE.drop 112 := by
    have heq_bits : portBits read (p2Ports probeRows) a = kS ++ kE.drop 112 := by
      rw [p2Ports, WEX.portBits_append, shortOutPorts_bits, extra2Ports_bits]
    apply List.ext_getElem
    · simp [scrShortWires_length, extra2Wires_len, hkS, hkE, portBits, scrShortBits_length, scrDExtraBits_length]
    · intro i hi1 hi2
      rw [List.getElem_map]
      have hi1' : i < (scrShortWires ++ extra2Wires).length := by simpa using hi1
      have hmem := List.getElem_mem hi1'
      have ⟨hp, hnk⟩ := hmem_p2_pool _ hmem
      dsimp only [sL2]
      simp only [tableXorState, Bool.true_and, hg4 _ hp hnk, Bool.false_xor,
        portMask_eq_xMask read (p2Ports probeRows) a p2Ports_nodup, p2Ports_targets, heq_bits]
      exact xMask_get (scrShortWires ++ extra2Wires) (kS ++ kE.drop 112) (p2Ports_targets probeRows ▸ p2Ports_nodup)
        (by simp [scrShortWires_length, extra2Wires_len, hkS, hkE, portBits, scrShortBits_length, scrDExtraBits_length]) i hi1'
  have s2a_eq : s2a = ⟨sL2.phase, fun q => sL2.basis q ^^ (eFlag && xMask (scrShortTargets ++ yTail.drop 112) (kS ++ kE.drop 112) q)⟩ := by
    have hfl2 : streamLayout.core.equalNegY ∉ scrShortTargets ++ yTail.drop 112 ∧
        streamLayout.doubleSelect ∉ scrShortTargets ++ yTail.drop 112 := by
      constructor <;> intro hm <;> rcases List.mem_append.mp hm with hm | hm
      · exact shortTargets_no_flags.2.2.2 hm
      · have hm' := List.mem_of_mem_drop hm; rw [sl_equalNegY, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · exact shortTargets_no_flags.1 hm
      · have hm' := List.mem_of_mem_drop hm; rw [sl_doubleSelect, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    have hsL2_e : (sL2.basis streamLayout.core.equalNegY ^^ sL2.basis streamLayout.doubleSelect) = eFlag := by
      have hne1 : streamLayout.core.equalNegY ∉ scrShortWires ++ extra2Wires := fun hm => by
        rcases List.mem_append.mp hm with h | h
        · exact scrShortWires_no_flags.2.2.2 h
        · rw [sl_equalNegY, extra2Wires, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have hne2 : streamLayout.doubleSelect ∉ scrShortWires ++ extra2Wires := fun hm => by
        rcases List.mem_append.mp hm with h | h
        · exact scrShortWires_no_flags.1 h
        · rw [sl_doubleSelect, extra2Wires, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      rw [sL2_out _ hne1, sL2_out _ hne2, sB_basis, sB_basis,
        xMask_outside _ _ streamLayout.core.equalNegY (fun hm => by have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); rw [sl_equalNegY, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
        xMask_outside _ _ streamLayout.doubleSelect (fun hm => by have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); rw [sl_doubleSelect, yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
      simp [sA_fl.1, sA_fl.2, heFlag]
    dsimp only [s2a, lit2a]
    rw [scrSw_ccx_eq_cBits (scrShortWires ++ extra2Wires) (scrShortTargets ++ yTail.drop 112) (kS ++ kE.drop 112) sL2
      (fun u hu hm => by
        have hu' : (14884 ≤ u ∧ u < 15142) ∨ (15399 ≤ u ∧ u < 15542) := by
          rcases List.mem_append.mp hu with h | h
          · exact Or.inl (shortWires_bounds u h)
          · rw [extra2Wires, List.mem_range'_1] at h; exact Or.inr h
        rcases List.mem_append.mp hm with hm | hm
        · have := hst_b u hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
        · have hm' := List.mem_of_mem_drop hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      hfl2
      (fun hm => by rcases List.mem_append.mp hm with h | h
                    · exact scrShortWires_no_flags.2.2.2 h
                    · rw [sl_equalNegY, extra2Wires, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      sL2_map,
      scrSw_cBits_effect _ _ hfl2 sL2]
    exact congrArg (ECDSAAdd.State.mk sL2.phase) (funext fun q => by rw [hsL2_e])
  have s2a_phase := state_eq_phase s2a_eq
  have s2a_basis := state_eq_basis s2a_eq
  have hg5 : ∀ q ∈ extra2Ports probeRows, s2a.basis q.target = decide (read (q.ref a) = q.value) := by
    intro q hq
    have hmem_p2 : q ∈ p2Ports probeRows := List.mem_append_right _ hq
    have ht_mem : q.target ∈ extra2Wires := by rw [← extra2Ports_targets probeRows]; exact List.mem_map_of_mem hq
    have ⟨hp, hnk⟩ := hmem_p2_pool q.target (List.mem_append_right _ ht_mem)
    rw [s2a_basis, xMask_outside _ _ q.target (fun hm => by
      simp only [extra2Wires, List.mem_range'_1] at ht_mem
      rcases List.mem_append.mp hm with hm | hm
      · have := hst_b q.target hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · have hm' := List.mem_of_mem_drop hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
      Bool.and_false, Bool.xor_false]
    dsimp only [sL2]
    simp only [tableXorState, Bool.true_and, hg4 q.target hp hnk, Bool.false_xor]
    exact port_selected read (p2Ports probeRows) a p2Ports_nodup q hmem_p2
  -- Now compare `origCornerRef` up to right before `scrNegP ++ midIP`!
  have horig_split := origCornerRef_split read a st m0 m2b hm0
  set m_s2 := m0.take (kX + kN + kY) ++ m_n2
  set o_1 := ECDSAAdd.run ((specialize (site2 probeRows).code a).instantiate read) m_s2 st with ho_1
  set o_2 := ECDSAAdd.run (ECDSAAdd.Frontier.zrep streamLayout) List.nil o_1 with ho_2
  set o_3 := ECDSAAdd.run cornerNegProg m_cn o_2 with ho_3
  -- Relate `o_1`, `o_2`, `o_3` to `s_3`, `s_4`, `s_5` outside `site2Wires ++ extra0Wires`!
  have ho1_triple : o_1.phase = st.phase ∧
      PointDialogValues streamLayout (X + cx) (Y + (if G then -cy else cy)) G base o_1.basis := by
    have hs2 : (specialize (site2 probeRows).code a).instantiate read =
        site2Load read probeRows a ++ (pair2Prog ++ site2Load read probeRows a) := by
      rw [site2_code, site2_inst]
    have hp2' : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
    have htr := site_block_triple2 read probeRows a hc hr pair2Prog X Y (X + cx) (Y + (if G then -cy else cy)) G base hroot hctl
      (fun t m _ hg hcx' hcy' hx' hy' hs' => by
        rw [hp2', run_meas_append, run_meas_append, run_meas_append, ← hxAdd, ← hyAdd]
        exact pair2_steps hc X Y G t _ _ _ _ hg hcx' hcy' hx' hy' hs')
    rw [ho_1, hs2]
    exact htr st m_s2 hv
  have ho1_eq_s3 : o_1.phase = s_3.phase ∧ ∀ q, q ∉ site2Wires ++ extra0Wires → o_1.basis q = s_3.basis q := by
    refine ⟨by rw [ho1_triple.1, r_3.1, r_2.1, r_1.1], ?_⟩
    intro q hq
    by_cases hqx : q ∈ streamLayout.point.x
    · have hs3_x : ECDSAAdd.regValue streamLayout.point.x s_3.basis = (X + cx).val :=
        (ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun u hu =>
          (r_3.2.2 u (fun hm => by have := hpx_b u hu; have := hpy_b u hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans
          (r_2.2.2 u (fun hm => by have := hpx_b u hu; have := hcy_b u hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)))).trans r_1x
      exact (ECDSAAdd.Arithmetic.regValue_eq_iff _ _ _).mp (ho1_triple.2.x.trans hs3_x.symm) q hqx
    · by_cases hqy : q ∈ streamLayout.point.y
      · exact (ECDSAAdd.Arithmetic.regValue_eq_iff _ _ _).mp (ho1_triple.2.y.trans r_3y.symm) q hqy
      · rw [ho1_triple.2.rest q (by simp [hqx, hqy]), ← hv.rest q (by simp [hqx, hqy]),
          r_3.2.2 q hqy, r_2.2.2 q (fun hm => hq (List.mem_append_left _ (List.mem_append_right _ hm))),
          r_1.2.2 q hqx, sL0_out q hq]
  have ho2_eq_s4 : o_2.phase = s_4.phase ∧ ∀ q, q ∉ site2Wires ++ extra0Wires → o_2.basis q = s_4.basis q := by
    have rz := ECDSAAdd.Frontier.zrep_run streamLayout streamLayout_widths streamLayout_nodup o_1 List.nil
    rw [← ho_2] at rz
    refine ⟨by rw [rz.1, ho1_eq_s3.1, r_4.1], ?_⟩
    intro q hq
    by_cases hqx : q ∈ streamLayout.point.x
    · have hrx : ECDSAAdd.regValue streamLayout.point.x o_1.basis = ECDSAAdd.regValue streamLayout.point.x s_3.basis :=
        ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun u hu => ho1_eq_s3.2 u (fun hm => by
          have := hpx_b u hu; have := hp0_b u hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
      have hrf : o_1.basis streamLayout.point.finite = s_3.basis streamLayout.point.finite :=
        ho1_eq_s3.2 _ (fun hm => by have := hp0_b _ hm; rw [streamLayout_point] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
      exact (ECDSAAdd.Arithmetic.regValue_eq_iff _ _ _).mp (by rw [rz.2.2, r_4.2.2, hrx, hrf]) q hqx
    · rw [rz.2.1 q hqx, r_4.2.1 q hqx, ho1_eq_s3.2 q hq]
  have ho2_pool : ∀ q ∈ streamLayout.dialogPool, o_2.basis q = false := fun q hq => by
    have rz := ECDSAAdd.Frontier.zrep_run streamLayout streamLayout_widths streamLayout_nodup o_1 List.nil
    have hqb : 14115 ≤ q ∧ q < 16728 := by
      have h1 : q ∈ streamLayout.dialogPool.take 2613 := by
        have ht : streamLayout.dialogPool.take 2613 = streamLayout.dialogPool := by simp [dialogPool]
        rwa [ht]
      exact (mem_pool_take 2613 (le_refl _)).mp h1
    rw [ho_2, rz.2.1 q (fun hm => by have := hpx_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
    exact (ECDSAAdd.Arithmetic.regValue_zero _ _).mp ho1_triple.2.clean q hq
  have ho3_eq_s5 : o_3.phase = s_5.phase ∧ (∀ q, q ∉ site2Wires ++ extra0Wires → o_3.basis q = s_5.basis q) ∧
      o_3.basis windowRoot = true ∧ (∀ q ∈ streamLayout.dialogPool, o_3.basis q = false) := by
    have ho2_py : ECDSAAdd.regValue streamLayout.point.y o_2.basis = ECDSAAdd.regValue streamLayout.point.y s_4.basis :=
      ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun u hu => ho2_eq_s4.2 u (fun hm => by
        have := hpy_b u hu; have := hp0_b u hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
    have rcn := cornerNegProg_effect o_2 m_cn (ho2_py.symm ▸ (s4_py.symm ▸ (Y + (if G then -cy else cy)).isLt))
      (fun q hq => ho2_pool q (List.mem_of_mem_take hq))
    rw [← ho_3] at rcn
    have he1 : o_2.basis streamLayout.core.equalNegY = s_4.basis streamLayout.core.equalNegY :=
      ho2_eq_s4.2 _ (fun hm => by have := hp0_b _ hm; rw [sl_equalNegY] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
    have hg1' : o_2.basis streamLayout.genericSelect = s_4.basis streamLayout.genericSelect :=
      ho2_eq_s4.2 _ (fun hm => by have := hp0_b _ hm; rw [sl_genericSelect] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
    refine ⟨by rw [rcn.1, ho2_eq_s4.1, r_5.1], ?_, ?_, ?_⟩
    · intro q hq
      by_cases hqy : q ∈ streamLayout.point.y
      · exact (ECDSAAdd.Arithmetic.regValue_eq_iff _ _ _).mp (by rw [rcn.2.1, r_5.2.1, ho2_py, he1, hg1']) q hqy
      · rw [rcn.2.2 q hqy, r_5.2.2 q hqy, ho2_eq_s4.2 q hq]
    · rw [rcn.2.2 windowRoot windowRoot_pointY, ho2_eq_s4.2 windowRoot (fun hm => by have := hp0_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
        r_4.2.1 windowRoot (fun hm => by have := hpx_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
        r_3.2.2 windowRoot windowRoot_pointY,
        r_2.2.2 windowRoot (fun hm => by have := hcy_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
        r_1.2.2 windowRoot (fun hm => by have := hpx_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
        sL0_out windowRoot (fun hm => by have := hp0_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega), st_root]
    · intro q hq
      have hqb : 14115 ≤ q ∧ q < 16728 := by
        have h1 : q ∈ streamLayout.dialogPool.take 2613 := by
          have ht : streamLayout.dialogPool.take 2613 = streamLayout.dialogPool := by simp [dialogPool]
          rwa [ht]
        exact (mem_pool_take 2613 (le_refl _)).mp h1
      rw [rcn.2.2 q (fun hm => by have := hpy_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
      exact ho2_pool q hq
  -- Reduce `cornerUnit₁ ++ cornerUnit₂` on `o_3` via `corner_reduce` + `scrW_comm_scrSw`
  have hcr := corner_reduce read a m2b o_3 ho3_eq_s5.2.2.1
    (fun w hw => ho3_eq_s5.2.2.2 w (WEX.scrAll_pool w hw))
    (fun w hw => ho3_eq_s5.2.2.2 w (yWires_pool w hw))
  have hflSw : streamLayout.core.equalNegY ∉ scrDTargets ∧ streamLayout.doubleSelect ∉ scrDTargets :=
    ⟨fun hm => by have := hdt_b _ hm; rw [sl_equalNegY] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega,
     fun hm => by have := hdt_b _ hm; rw [sl_doubleSelect] at this; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩
  have hmSwW : ECDSAAdd.measurementCount ((scrSw1 ++ cBits streamLayout.core.equalNegY scrDTargets (kS ++ kE) ++ scrSw1) ++
      (scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2)) = 0 := by
    simp [scrSw1, scrW1, scrW2, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount, cBits_records]
  have hleader : ECDSAAdd.run (leaderTail read a) m2b o_3 =
      ECDSAAdd.run (scrNegP ++ midIP read probeRows a) m2b
        (ECDSAAdd.run ((scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2) ++
          (scrSw1 ++ cBits streamLayout.core.equalNegY scrDTargets (kS ++ kE) ++ scrSw1)) List.nil o_3) := by
    have hl_eq : leaderTail read a =
        ((scrSw1 ++ cBits streamLayout.core.equalNegY scrDTargets (kS ++ kE) ++ scrSw1) ++
          (scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2)) ++ (scrNegP ++ midIP read probeRows a) := by
      simp only [leaderTail, kS, kE, kC, List.append_assoc]
    rw [hl_eq, run_zero_append _ _ hmSwW, ← scrW_comm_scrSw kC (kS ++ kE) o_3]
  set o_4 := ECDSAAdd.run ((scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2) ++
      (scrSw1 ++ cBits streamLayout.core.equalNegY scrDTargets (kS ++ kE) ++ scrSw1)) List.nil o_3 with ho_4
  -- Explicitly characterize `o_4`!
  have o4_eff : o_4 = ⟨o_3.phase, fun q =>
      o_3.basis q ^^
        ((base streamLayout.doubleSelect ^^ base streamLayout.infinitySelect ^^
          base streamLayout.genericSelect ^^ base streamLayout.core.equalNegY) && xMask scrDTargets kC q) ^^
        (eFlag && xMask scrDTargets (kS ++ kE) q)⟩ := by
    have hmW : ECDSAAdd.measurementCount (scrW1 ++ cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2) = 0 := by
      simp [scrW1, scrW2, ECDSAAdd.measurementCount_append, ECDSAAdd.measurementCount, cBits_records]
    rw [ho_4, run_zero_append _ _ hmW, scrW_cBits_effect kC o_3, scrSw_cBits_effect scrDTargets (kS ++ kE) hflSw]
    have o3_fl : ∀ w ∈ [streamLayout.infinitySelect, streamLayout.doubleSelect,
        streamLayout.genericSelect, streamLayout.core.equalNegY], o_3.basis w = base w := fun w hw => by
      have hwb : w = 19816 ∨ w = 19815 ∨ w = 19814 ∨ w = 14112 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
          sl_infinitySelect] at hw
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      exact (ho3_eq_s5.2.1 w (fun hm => by have := hp0_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)).trans (s5_fl w hw)
    have hfl_inf : o_3.basis streamLayout.infinitySelect = base streamLayout.infinitySelect := o3_fl _ (by simp)
    have hfl_ds : o_3.basis streamLayout.doubleSelect = base streamLayout.doubleSelect := o3_fl _ (by simp)
    have hfl_gs : o_3.basis streamLayout.genericSelect = base streamLayout.genericSelect := o3_fl _ (by simp)
    have hfl_eq : o_3.basis streamLayout.core.equalNegY = base streamLayout.core.equalNegY := o3_fl _ (by simp)
    refine state_ext ((state_phase_mk _ _).trans ((state_phase_mk _ _).trans (state_phase_mk _ _).symm)) ?_
    rw [state_basis_mk, state_basis_mk]
    funext q
    simp only [state_basis_mk, xMask_outside scrDTargets kC streamLayout.core.equalNegY hflSw.1,
      xMask_outside scrDTargets kC streamLayout.doubleSelect hflSw.2,
      Bool.and_false, Bool.xor_false, hfl_inf, hfl_ds, hfl_gs, hfl_eq, heFlag]
  have o4_phase := state_eq_phase o4_eff
  have o4_basis := state_eq_basis o4_eff
  have o4_clean : ∀ w ∈ scrAllWires, o_4.basis w = false := fun w hw => by
    have hpool := WEX.scrAll_pool w hw
    have hwb : 14115 ≤ w ∧ w < 16728 := by
      have h1 : w ∈ streamLayout.dialogPool.take 2613 := by
        have ht : streamLayout.dialogPool.take 2613 = streamLayout.dialogPool := by simp [dialogPool]
        rwa [ht]
      exact (mem_pool_take 2613 (le_refl _)).mp h1
    rw [o4_basis, ho3_eq_s5.2.2.2 w hpool,
      xMask_outside scrDTargets kC w (fun hm => by have := hdt_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
      xMask_outside scrDTargets (kS ++ kE) w (fun hm => by have := hdt_b w hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
    simp
  -- Now prove `ECDSAAdd.run [.CX windowRoot 14373] [] sC = scrLoad scrWires (kPair ++ kShort) o_4`!
  set kP := portBits read (scrPairBits probeRows (wBit probeRows .y)) a with hkP
  have hinf_bit : decide (read (wBit probeRows .infinity 0 a) = false) = true := by
    have hb := hr.bit .infinity 0 (by decide)
    rw [infinity_bit] at hb; simp [wBit, hb, pointFinite]
  have hkP_eq : kP = true :: (portBits read (indexedPorts cxWord (wFields probeRows .x) true) a ++
      [decide (read (wBit probeRows .y 0 a) = false)]) := by
    have h1 : ∀ (ws1 ws2 : List Wire) (refs : Nat → Nat → ConstantBit 32768) (v : Bool),
        ws1.length = ws2.length → portBits read (indexedPorts ws1 refs v) a = portBits read (indexedPorts ws2 refs v) a := by
      intro ws1 ws2 refs v hl; rw [portBits_indexed, portBits_indexed, hl]
    have hcons : ∀ (p : LookupPort 32768) (ps : List (LookupPort 32768)),
        portBits read (p :: ps) a = decide (read (p.ref a) = p.value) :: portBits read ps a := fun _ _ => rfl
    have hsing : ∀ (p : LookupPort 32768),
        portBits read ([p]) a = [decide (read (p.ref a) = p.value)] := fun _ => rfl
    change portBits read ((⟨wBit probeRows .infinity, false, streamLayout.point.finite⟩ ::
      indexedPorts streamLayout.point.x (wFields probeRows .x) true) ++
      [⟨wBit probeRows .y, false, yLow streamLayout⟩]) a = _
    rw [WEX.portBits_append, hcons, hsing, List.cons_append, hinf_bit]
    exact congrArg (fun xs => true :: (xs ++ [decide (read (wBit probeRows .y 0 a) = false)]))
      (h1 streamLayout.point.x cxWord (wFields probeRows .x) true (by rw [point_x_len]; simp [cxWord]))
  have hscrW_exp : scrPairWires = 14373 :: (cxWord ++ [14883]) := by
    rw [scrPairWires_explicit, cxWord, List.cons_append]
  have hlenP : scrPairWires.length = kP.length := by
    simp [scrPairWires_length, kP, portBits, scrPairBits_length]
  have hcx_len : cxWord.length = (portBits read (indexedPorts cxWord (wFields probeRows .x) true) a).length := by
    simp [cxWord, portBits, indexed_length]
  have hsC_root : sC.basis windowRoot = true := by
    have h1 : windowRoot ∉ extra2Wires := by rw [extra2Wires, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire, windowRoot]; omega
    have h2 : windowRoot ∉ scrShortWires ++ extra2Wires := fun hm => by
      rcases List.mem_append.mp hm with h | h
      · exact windowRoot_not_short h
      · exact h1 h
    have h3 : windowRoot ∉ p0ClearWires := by
      simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire, windowRoot]; omega
    have h4 : windowRoot ∉ site2Wires ++ extra0Wires := fun hm => by
      have := hp0_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega
    dsimp only [sC]
    rw [MeasuredClear.clearRegister_frame _ _ _ h1, s2a_basis,
      xMask_outside _ _ _ (fun hm => by
        rcases List.mem_append.mp hm with hm | hm
        · have := hst_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega
        · have hm' := List.mem_of_mem_drop hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
      Bool.and_false, Bool.xor_false, sL2_out _ h2, sB_basis,
      xMask_outside _ _ _ (fun hm => by have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
      Bool.and_false, Bool.xor_false]
    dsimp only [sA]
    rw [MeasuredClear.clearRegister_frame _ _ _ h3, s0_basis,
      xMask_outside _ _ _ (fun hm => by have hm' := List.mem_of_mem_take hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
      Bool.and_false, Bool.xor_false,
      r_7.2.2 windowRoot (fun hm => by have := hcy_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
      s6_out windowRoot (fun hm => by have := hdt_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega),
      s5_out_st windowRoot (fun hm => by have := hpx_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega)
        (fun hm => by have := hpy_b windowRoot hm; dsimp only [Wire, ECDSAAdd.Wire, windowRoot] at *; omega) h4, st_root]
  have hsC_cx_eq : ECDSAAdd.run ([.CX windowRoot 14373] : ECDSAAdd.Program) List.nil sC =
      scrLoad scrWires (kP ++ kS) o_4 := by
    rw [run_cons_CX, Site1Fast.run_nil, hsC_root]
    have hph : sC.phase = o_4.phase := by
      have h1 : sC.phase = s2a.phase := state_phase_mk _ _
      have h2 : sL2.phase = sB.phase := state_phase_mk _ _
      have h3 : sA.phase = s0.phase := state_phase_mk _ _
      exact h1.trans (s2a_phase.trans (h2.trans (sB_phase.trans (h3.trans (s0_phase.trans (r_7.1.trans (s6_phase.trans (ho3_eq_s5.1.symm.trans o4_phase.symm))))))))
    refine state_ext ((state_phase_mk _ _).trans (hph.trans (state_phase_mk _ _).symm)) ?_
    rw [scrLoad]
    refine Eq.trans (state_basis_mk _ _) (Eq.trans ?_ (state_basis_mk _ _).symm)
    funext q
    simp only [scrWires, xMask_append scrPairWires scrShortWires kP kS hlenP]
    by_cases hq_73 : q = 14373
    · subst hq_73
      have h73_sC : sC.basis 14373 = false := by
        dsimp only [sC]
        rw [MeasuredClear.clearRegister_frame _ _ _ (by rw [extra2Wires, List.mem_range'_1]; omega), s2a_basis,
          xMask_outside _ _ _ (fun hm => by
            rcases List.mem_append.mp hm with hm | hm
            · have := hst_b 14373 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
            · have hm' := List.mem_of_mem_drop hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
          Bool.and_false, Bool.xor_false,
          sL2_out 14373 (fun hm => by rcases List.mem_append.mp hm with h | h
                                      · have := shortWires_bounds 14373 h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
                                      · rw [extra2Wires, List.mem_range'_1] at h; omega)]
        exact hg4 14373 (List.mem_of_mem_take ((mem_pool_take 2613 (by decide)).mpr (by dsimp only [Wire, ECDSAAdd.Wire]; omega)))
          (by simp [keepWires, cxWord, List.mem_range'_1])
      have h73_o4 : o_4.basis 14373 = false := o4_clean 14373 (List.mem_append_left _ (List.mem_append_left _ (by rw [hscrW_exp]; simp)))
      have h73_ns : (14373 : Wire) ∉ scrShortWires := fun hm => by have := shortWires_bounds 14373 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have h73_p : xMask scrPairWires kP 14373 = true := by
        rw [hscrW_exp, hkP_eq, xMask]
        simp [xMask_outside (cxWord ++ [14883]) _ 14373 (by simp [cxWord, List.mem_range'_1])]
      simp [ECDSAAdd.writeBit, Function.update, h73_sC, h73_o4, h73_p, xMask_outside _ _ _ h73_ns]
    · simp only [ECDSAAdd.writeBit, Function.update, hq_73, ↓reduceDIte]
      by_cases hq_k : q ∈ keepWires
      · have hq_o4 : o_4.basis q = false := o4_clean q (List.mem_append_left _ (List.mem_append_left _ (by
          rw [hscrW_exp]; exact List.mem_cons_of_mem _ hq_k)))
        have hq_ns : q ∉ scrShortWires := fun hm => by
          have := shortWires_bounds q hm
          simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hq_k
          dsimp only [Wire, ECDSAAdd.Wire] at *; omega
        have hq_sC : sC.basis q = sL0.basis q := by
          have hkb : (14374 ≤ q ∧ q < 14630) ∨ q = 14883 := by
            simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hq_k
            dsimp only [Wire, ECDSAAdd.Wire] at *; omega
          dsimp only [sC]
          rw [MeasuredClear.clearRegister_frame _ _ _ (by rw [extra2Wires, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
            s2a_basis, xMask_outside _ _ _ (fun hm => by
              rcases List.mem_append.mp hm with hm | hm
              · have := hst_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
              · have hm' := List.mem_of_mem_drop hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
            Bool.and_false, Bool.xor_false,
            sL2_out q (fun hm => by rcases List.mem_append.mp hm with h | h
                                    · exact hq_ns h
                                    · rw [extra2Wires, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
            sB_basis, xMask_outside _ _ _ (fun hm => by have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm); rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
            Bool.and_false, Bool.xor_false]
          dsimp only [sA]
          rw [MeasuredClear.clearRegister_frame _ _ _ (by simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
          exact s0_p0_eq q (List.mem_append_left _ (by simp only [site2Wires, cxWord, cyWord, List.mem_append, List.mem_cons, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
        have hq_xp : sL0.basis q = xMask scrPairWires kP q := by
          have hmem_s2 : q ∈ site2Wires := by
            simp only [site2Wires, cxWord, cyWord, keepWires, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hq_k ⊢
            dsimp only [Wire, ECDSAAdd.Wire] at *; omega
          rw [sL0_site2 q hmem_s2, hscrW_exp, hkP_eq, xMask, site2Wires, site2Bits_eq,
            xMask_append cxWord cyWord _ _ hcx_len, xMask_append cxWord ([14883]) _ _ hcx_len]
          simp only [hq_73, decide_false, Bool.false_and, Bool.false_xor]
          have hcy_split : xMask cyWord (decide (read (wBit probeRows .y 0 a) = false) :: portBits read (negYExtraPorts probeRows) a) q =
              xMask ([14883]) ([decide (read (wBit probeRows .y 0 a) = false)]) q := by
            rw [cyWord, xMask, xMask, xMask_outside (List.range' 15399 255) _ q (by
              simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hq_k ⊢
              dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
            simp [xMask]
          rw [hcy_split]
        rw [hq_sC, hq_xp, hq_o4, xMask_outside _ _ _ hq_ns]; simp
      · by_cases hq_sh : q ∈ scrShortWires
        · have hqb := shortWires_bounds q hq_sh
          have hq_o4 : o_4.basis q = false := o4_clean q (List.mem_append_left _ (List.mem_append_right _ hq_sh))
          have hq_np : q ∉ scrPairWires := fun hm => by
            rw [hscrW_exp, List.mem_cons] at hm
            rcases hm with h | h
            · exact hq_73 h
            · exact hq_k h
          have hq_sC : sC.basis q = xMask scrShortWires kS q := by
            dsimp only [sC]
            rw [MeasuredClear.clearRegister_frame _ _ _ (by rw [extra2Wires, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
              s2a_basis, xMask_outside _ _ _ (fun hm => by
                rcases List.mem_append.mp hm with hm | hm
                · have := hst_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
                · have hm' := List.mem_of_mem_drop hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
              Bool.and_false, Bool.xor_false]
            have ⟨hp, hnk⟩ := hmem_p2_pool q (List.mem_append_left _ hq_sh)
            dsimp only [sL2]
            simp only [tableXorState, Bool.true_and, hg4 q hp hnk, Bool.false_xor]
            rw [portMask_eq_xMask read (p2Ports probeRows) a p2Ports_nodup, p2Ports_targets, p2Ports, WEX.portBits_append,
              shortOutPorts_bits, extra2Ports_bits,
              xMask_append scrShortWires extra2Wires (portBits read (scrShortBits probeRows) a)
                ((portBits read (scrDExtraBits probeRows) a).drop 112)
                (by simp [scrShortWires_length, portBits, scrShortBits_length]),
              xMask_outside extra2Wires _ q (by rw [extra2Wires, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
              Bool.xor_false, hkS]
          rw [hq_sC, hq_o4, xMask_outside _ _ _ hq_np]; simp
        · -- q ∉ scrWires
          have hq_np : q ∉ scrPairWires := fun hm => by
            rw [hscrW_exp, List.mem_cons] at hm; rcases hm with h | h; exact hq_73 h; exact hq_k h
          rw [xMask_outside scrPairWires kP q hq_np, xMask_outside scrShortWires kS q hq_sh, Bool.xor_false, Bool.xor_false]
          by_cases hq_e2 : q ∈ extra2Wires
          · rw [show sC.basis q = false from clearRegister_clean extra2Wires _ q hq_e2]
            have hqb : 15399 ≤ q ∧ q < 15542 := by simpa [extra2Wires, List.mem_range'_1] using hq_e2
            exact (o4_clean q (List.mem_append_right _ (by rw [scrDExtraWires_explicit, List.mem_range'_1]; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))).symm
          · by_cases hq_pc : q ∈ p0ClearWires
            · have hq_o4 : o_4.basis q = false := by
                have hq_pool : q ∈ streamLayout.dialogPool := by
                  simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hq_pc
                  exact List.mem_of_mem_take ((mem_pool_take 2613 (by decide)).mpr (by dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
                rw [o4_basis, ho3_eq_s5.2.2.2 q hq_pool,
                  xMask_outside scrDTargets kC q (fun hm => by have := hdt_b q hm; simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hq_pc; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
                  xMask_outside scrDTargets (kS ++ kE) q (fun hm => by have := hdt_b q hm; simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hq_pc; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
                simp
              dsimp only [sC]
              rw [MeasuredClear.clearRegister_frame _ _ _ hq_e2, s2a_basis,
                xMask_outside _ _ _ (fun hm => by
                  simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hq_pc
                  rcases List.mem_append.mp hm with hm | hm
                  · have := hst_b q hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
                  · have hm' := List.mem_of_mem_drop hm; rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega),
                Bool.and_false, Bool.xor_false, sL2_out q (by simp [hq_sh, hq_e2])]
              have hq_pool : q ∈ streamLayout.dialogPool := by
                simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hq_pc
                exact List.mem_of_mem_take ((mem_pool_take 2613 (by decide)).mpr (by dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
              rw [hg4 q hq_pool hq_k, hq_o4]
            · -- q ∉ site2Wires ++ extra0Wires, q ∉ scrShortWires ++ extra2Wires, q ∉ p0ClearWires
              have hq_np0 : q ∉ site2Wires ++ extra0Wires := fun hm => by
                simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at hm
                simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hq_k
                simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hq_pc
                dsimp only [Wire, ECDSAAdd.Wire] at *; omega
              dsimp only [sC]
              rw [MeasuredClear.clearRegister_frame _ _ _ hq_e2, s2a_basis, sL2_out q (by simp [hq_sh, hq_e2]), sB_basis]
              dsimp only [sA]
              rw [MeasuredClear.clearRegister_frame _ _ _ hq_pc, s0_basis,
                r_7.2.2 q (fun hm => hq_np0 (List.mem_append_left _ (List.mem_append_right _ hm))),
                s6_basis, o4_basis, ho3_eq_s5.2.1 q hq_np0,
                s5_fl streamLayout.doubleSelect (by simp), s5_fl streamLayout.infinitySelect (by simp),
                s5_fl streamLayout.genericSelect (by simp), s5_fl streamLayout.core.equalNegY (by simp)]
              have hx3 := xor_three_yTail kS kE (by simp [hkS, portBits, scrShortBits_length])
                (by simp [hkE, portBits, scrDExtraBits_length]) q
              rw [← hx3]
              exact xor5_dist _ eFlag _ _ _
  -- Now run `lit2b = [.CX windowRoot 14373] ++ cornerA2Prog ++ [.CX windowRoot 14373]`!
  have hcx_m : ECDSAAdd.measurementCount ([.CX windowRoot 14373] : ECDSAAdd.Program) = 0 := rfl
  have ha2_sim := cornerA2_scrWires_run read a m2b o_4 o4_clean
  set sOrig := ECDSAAdd.run (scrNegP ++ midIP read probeRows a) m2b o_4 with hsOrig
  have hsOrig_eq : sOrig = ECDSAAdd.run (origCornerRef read a) (cornerPerm m0 m2b) st := by
    rw [horig_split, ← ho_1, ← ho_2, ← ho_3, hcr.1, hleader]
  have hsOrig_clean : ∀ w ∈ scrAllWires, sOrig.basis w = false := ha2_sim.2
  have hsOrig_root : sOrig.basis windowRoot = true := by
    have h1 := cornerA2_root read a m2b (scrLoad scrWires (kP ++ kS) o_4) (by
      rw [← hsC_cx_eq, run_cons_CX, Site1Fast.run_nil, hsC_root]
      simp [ECDSAAdd.writeBit, Function.update, show windowRoot ≠ 14373 by decide, hsC_root])
    have hca2 : cornerA2Prog =
        scrNegP ++ (pointDialogGenericFlag streamLayout ++
         (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
          (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets)))))) := by
      unfold cornerA2Prog; rfl
    rw [← hca2, ha2_sim.1] at h1
    rw [scrLoad, state_basis_mk, xMask_outside scrWires (kP ++ kS) windowRoot windowRoot_not_scr, Bool.xor_false] at h1
    exact h1
  have hs2b_eq : s2b = ⟨sOrig.phase, fun q => if q = 14373 then false else
      sOrig.basis q ^^ xMask scrWires (kP ++ kS) q⟩ := by
    dsimp only [s2b, lit2b]
    rw [List.append_assoc, run_zero_append _ _ hcx_m, hsC_cx_eq, ← List.append_nil m2b,
      run_append_records cornerA2Prog ([.CX windowRoot 14373]) m2b List.nil _ hm2b,
      ha2_sim.1, run_cons_CX, Site1Fast.run_nil]
    have hsr : (scrLoad scrWires (kP ++ kS) sOrig).basis windowRoot = true := by
      rw [scrLoad, state_basis_mk, xMask_outside scrWires (kP ++ kS) windowRoot windowRoot_not_scr, Bool.xor_false]
      exact hsOrig_root
    rw [hsr]
    have hph : (scrLoad scrWires (kP ++ kS) sOrig).phase = sOrig.phase := state_phase_mk _ _
    refine state_ext ((state_phase_mk _ _).trans (hph.trans (state_phase_mk _ _).symm)) ?_
    refine Eq.trans (state_basis_mk _ _) (Eq.trans ?_ (state_basis_mk _ _).symm)
    rw [scrLoad, state_basis_mk, ← hkP, ← hkS]
    funext q
    by_cases hq73 : q = 14373
    · subst hq73
      have h73_o : sOrig.basis 14373 = false := hsOrig_clean 14373 (List.mem_append_left _ (List.mem_append_left _ (by rw [hscrW_exp]; simp)))
      have h73_w : xMask scrWires (kP ++ kS) 14373 = true := by
        rw [scrWires, xMask_append scrPairWires scrShortWires kP kS hlenP, hscrW_exp, hkP_eq, xMask,
          xMask_outside (cxWord ++ [14883]) _ 14373 (by simp [cxWord, List.mem_range'_1]),
          xMask_outside scrShortWires _ 14373 (fun hm => by have := shortWires_bounds 14373 hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)]
        simp
      simp [ECDSAAdd.writeBit, Function.update, h73_o, h73_w]
    · simp [ECDSAAdd.writeBit, Function.update, hq73]
  have hs2b_phase := state_eq_phase hs2b_eq
  have hs2b_basis := state_eq_basis hs2b_eq
  -- Goals 6, 7, 8!
  have hfc_eq : ∀ q, q ∈ finalClearWires →
      xMask scrWires (kP ++ kS) q = xMask finalClearWires (portBits read (finalClearPorts probeRows) a) q := by
    intro q hq
    have hq73 : q ≠ 14373 := by
      intro e; subst e
      simp only [finalClearWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hq
      rcases hq with (h | h) | h
      · have := shortWires_bounds 14373 h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    have hlenS : scrShortWires.length = kS.length := by simp [scrShortWires_length, kS, portBits, scrShortBits_length]
    have hy0_bits : portBits read ([⟨wBit probeRows .y 0, false, streamLayout.core.poolWire 768⟩]) a =
        [decide (read (wBit probeRows .y 0 a) = false)] := rfl
    rw [scrWires, xMask_append scrPairWires scrShortWires kP kS hlenP, hscrW_exp, hkP_eq, xMask,
      xMask_append cxWord ([14883]) _ _ hcx_len]
    simp only [hq73, decide_false, Bool.false_and, Bool.false_xor]
    rw [finalClearWires, finalClearPorts, WEX.portBits_append, WEX.portBits_append, shortOutPorts_bits, hy0_bits,
      xMask_append (scrShortWires ++ cxWord) ([14883]) _ _ (by simp [scrShortWires_length, cxWord, portBits, scrShortBits_length, indexed_length]),
      xMask_append scrShortWires cxWord _ _ hlenS]
    cases xMask scrShortWires kS q <;>
      cases xMask cxWord (portBits read (indexedPorts cxWord (wFields probeRows .x) true) a) q <;>
      cases xMask ([14883]) ([decide (read (wBit probeRows .y 0 a) = false)]) q <;> rfl
  refine ⟨hg1, hg2, hg3, hg4, hg5, ?_, ?_, ?_⟩
  · -- Goal 6: `finalClearPorts` loaded in `s2b`
    intro q hq
    have ht_mem : q.target ∈ finalClearWires := by rw [← finalClearPorts_targets probeRows]; exact List.mem_map_of_mem hq
    have hq73 : q.target ≠ 14373 := by
      intro e
      simp only [finalClearWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1, e] at ht_mem
      rcases ht_mem with (h | h) | h
      · have := shortWires_bounds 14373 h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    have hq_all : q.target ∈ scrAllWires := by
      apply List.mem_append_left
      simp only [finalClearWires, List.mem_append, List.mem_singleton] at ht_mem
      rcases ht_mem with (h | h) | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ (by rw [hscrW_exp]; exact List.mem_cons_of_mem _ (List.mem_append_left _ h))
      · exact List.mem_append_left _ (by rw [hscrW_exp]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [h])))
    rw [hs2b_basis, if_neg hq73, hsOrig_clean q.target hq_all, Bool.false_xor, hfc_eq q.target ht_mem,
      ← finalClearPorts_targets probeRows, ← portMask_eq_xMask read (finalClearPorts probeRows) a (finalClearPorts_targets probeRows ▸ finalClearWires_nodup)]
    exact port_selected read (finalClearPorts probeRows) a (finalClearPorts_targets probeRows ▸ finalClearWires_nodup) q hq
  · -- Goal 7: `s2b.basis 14373 = false`
    rw [hs2b_basis]; simp
  · -- Goal 8: `sOut = sOrig`
    rw [← hsOrig_eq]
    refine state_ext ((state_phase_mk _ _).trans hs2b_phase) ?_
    rw [state_basis_mk]
    funext q
    by_cases hfc : q ∈ finalClearWires
    · rw [clearRegister_clean finalClearWires _ q hfc]
      have hq_all : q ∈ scrAllWires := by
        apply List.mem_append_left
        simp only [finalClearWires, List.mem_append, List.mem_singleton] at hfc
        rcases hfc with (h | h) | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ (by rw [hscrW_exp]; exact List.mem_cons_of_mem _ (List.mem_append_left _ h))
        · exact List.mem_append_left _ (by rw [hscrW_exp]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [h])))
      exact (hsOrig_clean q hq_all).symm
    · rw [MeasuredClear.clearRegister_frame finalClearWires _ q hfc, hs2b_basis]
      by_cases hq73 : q = 14373
      · subst hq73; simp [hsOrig_clean 14373 (List.mem_append_left _ (List.mem_append_left _ (by rw [hscrW_exp]; simp)))]
      · have hq_nw : q ∉ scrWires := fun hm => by
          rcases List.mem_append.mp hm with h | h
          · rw [hscrW_exp, List.mem_cons] at h
            rcases h with h | h
            · exact hq73 h
            · rcases List.mem_append.mp h with h | h
              · exact hfc (List.mem_append_left _ (List.mem_append_right _ h))
              · exact hfc (List.mem_append_right _ h)
          · exact hfc (List.mem_append_left _ (List.mem_append_left _ h))
        rw [if_neg hq73, xMask_outside scrWires (kP ++ kS) q hq_nw, Bool.xor_false]

/-! ### Prefix invariant (`preSite2_values`): entering `site2F` with `PointDialogValues` and `hflag` -/

def generic3Pre (rows : Nat → Fin 32768) : Code 32768 :=
  [.plain (wLiteral guard5), .plain (wLiteral (ECDSAAdd.Frontier.arithS streamLayout false)),
   .plain (wLiteral guard5), .plain (wLiteral (ECDSAAdd.Frontier.SquareOB5.program streamLayout))] ++
  constAdd streamLayout streamLayout.point.x (wFields rows .tripleX) ++
  [.plain (wLiteral guard5), .plain (wLiteral (ECDSAAdd.Frontier.arithS streamLayout true)),
   .plain (wLiteral guard5), .plain (wLiteral negXReg)]

def preSite2Code : Code 32768 := rowPre3 ++ generic3Pre probeRows

private theorem chain_plain_pre (read : ConstantBit 32768 → Bool) (address : Nat) (rows : Nat → Fin 32768)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState)
    (hroot : base windowRoot = true) (hctl : base streamLayout.control = true)
    (hD : base streamLayout.doubleSelect = false) (hI : base streamLayout.genericSelect = false)
    (X0 X1 a X3 : ECDSAAdd.Fp)
    (hX0 : X0.val = X.val ^^^ (if base streamLayout.point.finite then 0 else 5))
    (hX1d : X1 = X0 - cx) (hX1 : X1 ≠ 0) (ha : a = (Y - cy) / X1)
    (hX3d : X3 = X1 - (if G then a * a else 0) + (if G then 3 * cx else 0)) (hX3 : X3 ≠ 0) :
    Checked read address (PointDialogValues streamLayout X Y G base) (preBlock rows ++ generic3Pre rows)
      (PointDialogValues streamLayout (if G then -X3 else X3) (a * X3) G base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hex : ¬ (base streamLayout.doubleSelect = true ∧ base streamLayout.genericSelect = true) := by rw [hD]; simp
  have gid : ∀ (Z : ECDSAAdd.Fp), Z.val = (Z.val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := fun Z => by rw [hD, hI]; simp
  have z1 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X X0 Y G base hX0)
  have p1 := pair1_checked read address rows hc hr X0 Y G base hroot hctl
  rw [← hX1d] at p1
  have g1 := guard5_checked read address X1 X1 (Y - cy) G base hex (gid X1)
  have d1 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X1 (Y - cy) G base false hX1)
  simp only [Bool.false_eq_true, if_false] at d1; rw [← ha] at d1
  have g2 := guard5_checked read address X1 X1 a G base hex (gid X1)
  have sq := literal_checked read address _ _ _ (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn X1 a G base)
  have t3 := addX_checked read address streamLayout hw hn (X1 - (if G then a * a else 0)) a G base (3 * cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3 * cx) (field_some_tripleX hc))
  rw [← hX3d] at t3
  have g3 := guard5_checked read address X3 X3 a G base hex (gid X3)
  have m1 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X3 a G base true hX3)
  simp only [if_true] at m1
  have g4 := guard5_checked read address X3 X3 (a * X3) G base hex (gid X3)
  have ng := literal_checked read address _ _ _ (negXReg_step X3 (a * X3) G base (fun _ => hX3))
  have h := (((((((((z1.seq p1).seq g1).seq d1).seq g2).seq sq).seq t3).seq g3).seq m1).seq g4).seq ng
  simpa only [preBlock, generic3Pre, constAdd, List.append_assoc, List.cons_append, List.nil_append] using h

private theorem chain_toggle_pre (read : ConstantBit 32768 → Bool) (address : Nat) (rows : Nat → Fin 32768)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState)
    (hroot : base windowRoot = true) (hctl : base streamLayout.control = true)
    (hfin : base streamLayout.point.finite = true)
    (hex : ¬ (base streamLayout.doubleSelect = true ∧ base streamLayout.genericSelect = true))
    (hD : base streamLayout.doubleSelect = true → X = cx) (hI : base streamLayout.genericSelect = true → X = cx)
    (hX1 : base streamLayout.doubleSelect = false → base streamLayout.genericSelect = false → X - cx ≠ 0) :
    Checked read address (PointDialogValues streamLayout X Y false base) (preBlock rows ++ generic3Pre rows)
      (PointDialogValues streamLayout (X - cx) (Y - cy) false base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  set E := (base streamLayout.doubleSelect || base streamLayout.genericSelect) with hE
  let xg : ECDSAAdd.Fp := if E then 5 else X - cx
  have hxg0 : xg ≠ 0 := by
    simp only [xg]; split
    · exact ECDSAAdd.Frontier.finFive_ne_zero
    · rename_i hne; simp only [hE, Bool.or_eq_true, not_or, Bool.not_eq_true] at hne; exact hX1 hne.1 hne.2
  have hzero : E = true → X - cx = 0 := fun h => by
    simp only [hE, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [hD h, sub_self]
    · rw [hI h, sub_self]
  have fwd : xg.val = ((X - cx).val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := by
    simp only [xg]; cases hd : base streamLayout.doubleSelect <;> cases hi : base streamLayout.genericSelect
    · simp [hE, hd, hi]
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]; rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]; rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · exact absurd ⟨hd, hi⟩ hex
  have back : (X - cx).val = (xg.val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := by
    simp only [xg]; cases hd : base streamLayout.doubleSelect <;> cases hi : base streamLayout.genericSelect
    · simp [hE, hd, hi]
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]; rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]; rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · exact absurd ⟨hd, hi⟩ hex
  have zid : X.val = X.val ^^^ (if base streamLayout.point.finite then 0 else 5) := by rw [hfin]; simp
  have z1 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X X Y false base zid)
  have p1 := pair1_checked read address rows hc hr X Y false base hroot hctl
  have g1 := guard5_checked read address (X - cx) xg (Y - cy) false base hex fwd
  have d1 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn xg (Y - cy) false base false hxg0)
  simp only [Bool.false_eq_true, if_false] at d1
  have g2 := guard5_checked read address xg (X - cx) ((Y - cy) / xg) false base hex back
  have sq := literal_checked read address _ _ _ (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn (X - cx) ((Y - cy) / xg) false base)
  simp only [Bool.false_eq_true, if_false, sub_zero] at sq
  have t3 := addX_checked read address streamLayout hw hn (X - cx) ((Y - cy) / xg) false base (3 * cx) (wFields rows .tripleX)
    (row_bits hc hr .tripleX (3 * cx) (field_some_tripleX hc))
  simp only [Bool.false_eq_true, if_false, add_zero] at t3
  have g3 := guard5_checked read address (X - cx) xg ((Y - cy) / xg) false base hex fwd
  have m1 := literal_checked read address _ _ _ (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn xg ((Y - cy) / xg) false base true hxg0)
  simp only [if_true, div_mul_cancel₀ _ hxg0] at m1
  have g4 := guard5_checked read address xg (X - cx) (Y - cy) false base hex back
  have ng := literal_checked read address _ _ _ (negXReg_step (X - cx) (Y - cy) false base (fun h => by cases h))
  simp only [Bool.false_eq_true, if_false] at ng
  have h := (((((((((z1.seq p1).seq g1).seq d1).seq g2).seq sq).seq t3).seq g3).seq m1).seq g4).seq ng
  simpa only [preBlock, generic3Pre, constAdd, List.append_assoc, List.cons_append, List.nil_append] using h

theorem preSite2_values (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point) + .some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point) + .some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _ => false) (flipInfinity s))
    (hroot : s windowRoot = true) (m : List Bool) :
    ∃ (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState),
      PointDialogValues streamLayout X Y G base (ECDSAAdd.run (reference read address preSite2Code) m ⟨false, s⟩).basis ∧
      base windowRoot = true ∧
      base streamLayout.control = true ∧
      (G = true → base streamLayout.infinitySelect = false ∧ base streamLayout.doubleSelect = false ∧
        base streamLayout.genericSelect = false ∧ base streamLayout.core.equalNegY = false) := by
  classical
  have hrun : ECDSAAdd.run (reference read address preSite2Code) m ⟨false, s⟩ =
      ECDSAAdd.run (reference read address (preBlock probeRows ++ generic3Pre probeRows))
        (m.drop (ECDSAAdd.measurementCount (reference read address rowPre)))
        (ECDSAAdd.run (reference read address rowPre) (m.take (ECDSAAdd.measurementCount (reference read address rowPre))) ⟨false, s⟩) := by
    have hsplit : reference read address preSite2Code =
        reference read address rowPre3 ++ reference read address (generic3Pre probeRows) :=
      reference_append read address rowPre3 (generic3Pre probeRows)
    rw [hsplit, ECDSAAdd.run_append (reference read address rowPre3), rowPre3_run, rowPre3_records,
      ← ECDSAAdd.run_append (reference read address (rowPre ++ preBlock probeRows)),
      ← reference_append read address (rowPre ++ preBlock probeRows) (generic3Pre probeRows),
      List.append_assoc,
      reference_append read address rowPre (preBlock probeRows ++ generic3Pre probeRows),
      ECDSAAdd.run_append (reference read address rowPre)]
  rw [hrun]
  set mPre := m.take (ECDSAAdd.measurementCount (reference read address rowPre))
  set mRest := m.drop (ECDSAAdd.measurementCount (reference read address rowPre))
  set st3 := ECDSAAdd.run (reference read address rowPre) mPre ⟨false, s⟩ with hst3
  have bnd := rowPre_boundary read address R hc hr h₁ h₂ hD hDo s hs hroot mPre
  rw [← hst3] at bnd
  have root3 : st3.basis windowRoot = true :=
    root_preserves read windowBits windowPaths windowRoot (erase rowPre) address rowPre_placed ⟨false, s⟩ hroot mPre
  have hp := (point_holds _ _ _).mp bnd.point
  have hctl : st3.basis streamLayout.control = true := bnd.control
  have hCneg := some_ne_neg hc h₁
  have hC0 : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have rd := dialogFlagState_read streamLayout streamLayout_nodup (dialogInfinity true R)
    (dialogDouble true R (.some hc)) (dialogInversePoint true R (.some hc)) (dialogOrdinary true R (.some hc))
    (true && decide (dialogExceptionEnabled (.some hc))) (dialogException true R (.some hc))
    (true && decide (cy ≠ -cy))
  have sInf : st3.basis streamLayout.infinitySelect = dialogInfinity true R :=
    (bnd.flags _ (by simp [inPlaceFlags])).trans rd.1
  have sD : st3.basis streamLayout.doubleSelect = dialogDouble true R (.some hc) :=
    (bnd.flags _ (by simp [inPlaceFlags])).trans rd.2.1
  have sI : st3.basis streamLayout.genericSelect = dialogInversePoint true R (.some hc) :=
    (bnd.flags _ (by simp [inPlaceFlags])).trans rd.2.2.1
  have sG : st3.basis streamLayout.core.generic = dialogOrdinary true R (.some hc) :=
    (bnd.flags _ (by simp [inPlaceFlags])).trans rd.2.2.2.1
  have sE : st3.basis streamLayout.core.equalNegY = dialogException true R (.some hc) :=
    (bnd.flags _ (by simp [inPlaceFlags])).trans rd.2.2.2.2.2.1
  have sD' : st3.basis streamLayout.doubleSelect = decide (R = (.some hc : Point)) := by
    rw [sD, dialogDouble, decide_eq_true hCneg]; simp
  have sI' : st3.basis streamLayout.genericSelect = decide (R = -(.some hc : Point)) := by
    rw [sI]; simp [dialogInversePoint]
  have hex : ¬ (st3.basis streamLayout.doubleSelect = true ∧ st3.basis streamLayout.genericSelect = true) := by
    rw [sD', sI']; simp only [decide_eq_true_eq, not_and]; intro h1 h2; exact hCneg (h1.symm.trans h2)
  cases R with
  | zero =>
    have hG : st3.basis streamLayout.core.generic = false := by
      rw [sG]; cases h : dialogOrdinary true 0 (.some hc)
      · rfl
      · exact absurd rfl ((dialogOrdinary_true true 0 _ hC0).mp h).2.1
    have hD0 : st3.basis streamLayout.doubleSelect = false := by rw [sD']; simp [hC0.symm]
    have hI0 : st3.basis streamLayout.genericSelect = false := by rw [sI']; simp [(neg_ne_zero.mpr hC0).symm]
    have values : PointDialogValues streamLayout 0 0 false st3.basis st3.basis := ⟨hp.2.1, hp.2.2, hG, bnd.clean, fun _ _ => rfl⟩
    have hfin : st3.basis streamLayout.point.finite = false := hp.1
    have hX1 : (5 : ECDSAAdd.Fp) - cx ≠ 0 := sub_ne_zero.mpr (ECDSAAdd.Frontier.x_ne_five hc).symm
    have hchk := chain_plain_pre read address probeRows hc hr 0 0 false st3.basis root3 hctl hD0 hI0
      5 (5 - cx) ((0 - cy) / (5 - cx)) (5 - cx)
      (by rw [hfin, ECDSAAdd.Frontier.finFive_val, ZMod.val_zero]; decide) rfl hX1 rfl (by simp) hX1
    exact ⟨_, _, false, st3.basis, (hchk.correct st3 mRest values).2, root3, hctl, fun h => by cases h⟩
  | @some x y hrp =>
    have hfin : st3.basis streamLayout.point.finite = true := hp.1
    cases hG : dialogOrdinary true (.some hrp) (.some hc) with
    | false =>
      have sG' : st3.basis streamLayout.core.generic = false := sG.trans hG
      have values : PointDialogValues streamLayout x y false st3.basis st3.basis := ⟨hp.2.1, hp.2.2, sG', bnd.clean, fun _ _ => rfl⟩
      have hD_imp : st3.basis streamLayout.doubleSelect = true → x = cx := by
        rw [sD']; intro h; exact (WeierstrassCurve.Affine.Point.some.inj (of_decide_eq_true h)).1
      have hI_imp : st3.basis streamLayout.genericSelect = true → x = cx := by
        rw [sI']; intro h; have h' := of_decide_eq_true h; rw [WeierstrassCurve.Affine.Point.neg_some] at h'
        exact (WeierstrassCurve.Affine.Point.some.inj h').1
      have hX1 : st3.basis streamLayout.doubleSelect = false → st3.basis streamLayout.genericSelect = false → x - cx ≠ 0 := by
        rw [sD', sI']; intro h1 h2 hz
        rcases (sameX_iff_eq_or_neg hrp hc).mp (sub_eq_zero.mp hz) with h | h
        · exact absurd (decide_eq_true h) (by rw [h1]; decide)
        · exact absurd (decide_eq_true h) (by rw [h2]; decide)
      have hchk := chain_toggle_pre read address probeRows hc hr x y st3.basis root3 hctl hfin hex hD_imp hI_imp hX1
      exact ⟨_, _, false, st3.basis, (hchk.correct st3 mRest values).2, root3, hctl, fun h => by cases h⟩
    | true =>
      have he := ((dialogOrdinary_true true _ _ hC0).mp hG).2
      have den := dialog_denominators_ne_zero hrp hc he.2.1 he.2.2.1 he.2.2.2
      have sG' : st3.basis streamLayout.core.generic = true := sG.trans hG
      have values : PointDialogValues streamLayout x y true st3.basis st3.basis := ⟨hp.2.1, hp.2.2, sG', bnd.clean, fun _ _ => rfl⟩
      have hInf0 : st3.basis streamLayout.infinitySelect = false := by
        rw [sInf, dialogInfinity]; simp [he.1]
      have hD0 : st3.basis streamLayout.doubleSelect = false := by rw [sD']; exact decide_eq_false he.2.1
      have hI0 : st3.basis streamLayout.genericSelect = false := by rw [sI']; exact decide_eq_false he.2.2.1
      have hE0 : st3.basis streamLayout.core.equalNegY = false := by
        rw [sE, dialogException]; simp [he.2.2.2]
      let a := genericSlope x y cx cy
      let d := cx - genericX x y cx cy
      have hv := generic_inplace_values x y cx cy den.1
      have hchk := chain_plain_pre read address probeRows hc hr x y true st3.basis root3 hctl hD0 hI0
        x (x - cx) a d (by rw [hfin]; simp) rfl (sub_ne_zero.mpr den.1) rfl
        (by simp only [if_true]; exact hv.2.1.symm) den.2
      exact ⟨_, _, true, st3.basis, (hchk.correct st3 mRest values).2, root3, hctl, fun _ => ⟨hInf0, hD0, hI0, hE0⟩⟩

end
end ShorECDLP.Entrant.CornerFast
end

/-! ### Consolidated from `CornerWire.lean` -/
section
/-! Wiring the 3-pass SelectSwap fusion of `[site2F, zrep, cornerNeg, corner]` (`CornerFast`)
together with `Site1Wire.Wide16.twoPassProg` into the wide (16-bit) signed window row (`Wide16`).

Replaces BOTH block #2 (`site1`, `-15,098` Toffolis / records) AND blocks #12..#15
(`[site2F, zrep, cornerNeg, corner]`, `-23,997` Toffolis, `-24,518` records) of
`WideBank8.Row16.code`:
- Row records: `1,743,002 → 1,727,904 → 1,703,386` (`-39,616` vs `WideBank8.Row16`)
- Window records: `1,743,514 → 1,728,416 → 1,703,898`
- Wide signed credit: `≤ 2,342,691 → ≤ 2,327,593 → ≤ 2,303,596` (`-23,997` vs `Site1Wire.Wide16`)
- Total savings across 26 wide windows: `623,922` Toffolis (`2,495,688` T-model gates),
  dropping Q×T from `392,201,595,275` to `388,171,059,155`. -/

namespace ShorECDLP.Entrant.CornerWire
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare Site1Fast Site1Wire CornerFast
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

attribute [local irreducible] ECDSAAdd.run scrInP1 scrInP2 pair1Prog pair2Prog
  xAddProg yAddProg negYProg scrNegP ECDSAAdd.Frontier.zrep scrP1 scrP2
  scrCWriteFused cornerNegProg cornerA1Prog cornerA2Prog
  lit0 lit1 lit2a lit2b site1Arith
  scrPairWires scrShortWires scrDExtraWires WEXUnlookup.rowC WEXUnlookup.rowHead
  WideBank8.Row16.code WEXFast.rowCF
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 MeasuredClear.measureThen
  MeasuredClear.fixupProgram MeasuredClear.fixupProgram8
  ECDSAAdd.Baselines.normalizeProgram
  WideBank8.Fast16.fprog WideBank8.Fast16.fblockProg
  Site1Wire.Wide16.twoPassProg Site1Wire.Wide16.rowProg
  Site1Wire.Wide16.fixRec8 Site1Wire.Wide16.tree8 Site1Wire.Wide16.site1Rec

/-! ### Part 1: Normalized literals, `litOnly` metrics, and wire-avoidance helpers -/

def lit0Norm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram lit0
def lit1Norm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram lit1
def lit2aNorm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram lit2a
def lit2bNorm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram lit2b

def mLit0 : Nat := ECDSAAdd.measurementCount lit0
def mLit2b : Nat := ECDSAAdd.measurementCount lit2b

attribute [local irreducible] lit0Norm lit1Norm lit2aNorm lit2bNorm

theorem lit0Norm_meas : ECDSAAdd.measurementCount lit0Norm = mLit0 := by
  rw [lit0Norm, mLit0]; exact ECDSAAdd.Baselines.normalize_measurements lit0
theorem lit1Norm_meas : ECDSAAdd.measurementCount lit1Norm = 0 := by
  rw [lit1Norm, ECDSAAdd.Baselines.normalize_measurements lit1, lit1_meas]
theorem lit2aNorm_meas : ECDSAAdd.measurementCount lit2aNorm = 0 := by
  rw [lit2aNorm, ECDSAAdd.Baselines.normalize_measurements lit2a, lit2a_meas]
theorem lit2bNorm_meas : ECDSAAdd.measurementCount lit2bNorm = mLit2b := by
  rw [lit2bNorm, mLit2b]; exact ECDSAAdd.Baselines.normalize_measurements lit2b

attribute [local irreducible] mLit0 mLit2b

theorem lit0Norm_valid : ∀ i ∈ lit0Norm, ECDSAAdd.Challenge.instructionValid i := by
  rw [lit0Norm]; exact ECDSAAdd.Baselines.normalize_physical lit0 lit0_physical
theorem lit1Norm_valid : ∀ i ∈ lit1Norm, ECDSAAdd.Challenge.instructionValid i := by
  rw [lit1Norm]; exact ECDSAAdd.Baselines.normalize_physical lit1 lit1_physical
theorem lit2aNorm_valid : ∀ i ∈ lit2aNorm, ECDSAAdd.Challenge.instructionValid i := by
  rw [lit2aNorm]; exact ECDSAAdd.Baselines.normalize_physical lit2a lit2a_physical
theorem lit2bNorm_valid : ∀ i ∈ lit2bNorm, ECDSAAdd.Challenge.instructionValid i := by
  rw [lit2bNorm]; exact ECDSAAdd.Baselines.normalize_physical lit2b lit2b_physical

theorem lit0Norm_wires_newH7 : ECDSAAdd.wires lit0Norm ⊆ PoolHost.newSourceH7.toFinset := by
  rw [lit0Norm, ECDSAAdd.Baselines.normalize_wires]; exact lit0_wires_newH7
theorem lit1Norm_wires_newH7 : ECDSAAdd.wires lit1Norm ⊆ PoolHost.newSourceH7.toFinset := by
  rw [lit1Norm, ECDSAAdd.Baselines.normalize_wires]; exact lit1_wires_newH7
theorem lit2aNorm_wires_newH7 : ECDSAAdd.wires lit2aNorm ⊆ PoolHost.newSourceH7.toFinset := by
  rw [lit2aNorm, ECDSAAdd.Baselines.normalize_wires]; exact lit2a_wires_newH7
theorem lit2bNorm_wires_newH7 : ECDSAAdd.wires lit2bNorm ⊆ PoolHost.newSourceH7.toFinset := by
  rw [lit2bNorm, ECDSAAdd.Baselines.normalize_wires]; exact lit2b_wires_newH7

theorem lit0_avoid_window (w : Wire)
    (hw : w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank) :
    w ∉ ECDSAAdd.wires lit0 := by
  have hwb : w = 10015 ∨ (855 ≤ w ∧ w < 870) ∨ w = 871 ∨ (14832 ≤ w ∧ w < 14847) ∨ w = 14848 := by
    simp only [windowRoot, WideBank8.Fast16.windowBits, WideBank8.Fast16.pathBank,
      List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  intro hm
  have hp2 := pair2Prog_subset
  have hp2' : pair2Prog = xAddProg ++ negYProg ++ yAddProg ++ negYProg := by unfold pair2Prog; rfl
  rw [hp2'] at hp2
  have hnot_p2 (hu : w ∈ ECDSAAdd.wires pair2Prog) : False := by
    have hs := List.mem_toFinset.mp (pair2Prog_subset hu)
    simp only [pair2List, xAdd, yAdd, negYW, MeasuredCanonicalModLayout.wires,
      CompactRecoveryNegateLayout.wires, cxWord, cyWord, addCarry,
      streamLayout_point, sl_generic, List.mem_append, List.mem_cons, List.mem_range'_1,
      List.not_mem_nil, or_false] at hs
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  have hnot_negP (hu : w ∈ ECDSAAdd.wires scrNegP) : False := by
    have hsub0 : ECDSAAdd.wires scrNegP ⊆ ((negateYLayout streamLayout).wires streamLayout.core.equalNegY).toFinset := by
      unfold scrNegP
      exact (negateYLayout streamLayout).program_support streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
        (negateYLayout_widths streamLayout streamLayout_widths).2
    have hmem := List.mem_toFinset.mp (hsub0 hu)
    have hpool := negateYLayout_pool streamLayout streamLayout_widths
    have htake : streamLayout.dialogPool.take 258 = List.range' 14115 258 := pool_take_eq 258 (by decide)
    simp only [CompactRecoveryNegateLayout.wires, List.mem_cons, List.mem_append] at hmem
    rcases hmem with rfl | rfl | rfl | hmem | hmem
    · rw [sl_equalNegY] at hwb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · have h1 : (negateYLayout streamLayout).cin ∈ streamLayout.dialogPool.take 258 := by rw [← hpool]; simp
      rw [htake, List.mem_range'_1] at h1; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · have h1 : (negateYLayout streamLayout).zero ∈ streamLayout.dialogPool.take 258 := by rw [← hpool]; simp
      rw [htake, List.mem_range'_1] at h1; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · simp only [negateYLayout, streamLayout_point, List.mem_range'_1] at hmem; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · have h1 : w ∈ streamLayout.dialogPool.take 258 := by rw [← hpool]; simp [hmem]
      rw [htake, List.mem_range'_1] at h1; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  simp only [lit0, ECDSAAdd.wires_append, Finset.mem_union] at hm
  rcases hm with ((((((hm | hm) | hm) | hm) | hm) | (hm | hm) | hm) | hm) | (hm | hm) | hm
  · exact hnot_p2 (by rw [hp2']; simp [ECDSAAdd.wires_append, hm])
  · exact hnot_p2 (by rw [hp2']; simp [ECDSAAdd.wires_append, hm])
  · exact hnot_p2 (by rw [hp2']; simp [ECDSAAdd.wires_append, hm])
  · rcases ECDSAAdd.Frontier.zrep_wires streamLayout w hm with h | h
    · rw [streamLayout_point] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · rw [streamLayout_point, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [cornerNegProg, ECDSAAdd.wires_append, Finset.mem_union] at hm
    rcases hm with hm | hm | hm
    · simp only [scrNegE, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
        Finset.mem_singleton, sl_genericSelect, sl_equalNegY] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · exact hnot_negP hm
    · simp only [scrNegE, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
        Finset.mem_singleton, sl_genericSelect, sl_equalNegY] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [scrW1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [scrCWriteFused, ECDSAAdd.wires_append, Finset.mem_union] at hm
    rcases hm with (hm | hm) | hm
    · simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
        Finset.mem_singleton, sl_doubleSelect, streamLayout_point] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · rcases ccxList_wires _ _ _ _ hm with rfl | hm | hm
      · rw [sl_doubleSelect] at hwb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · simp only [cxWord, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · simp only [streamLayout_point, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · rcases ccxList_wires _ _ _ _ hm with rfl | hm | hm
      · rw [sl_doubleSelect] at hwb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · simp only [cyWord, List.mem_cons, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · simp only [streamLayout_point, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [scrW2, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, sl_doubleSelect, sl_genericSelect, sl_equalNegY,
      show streamLayout.infinitySelect = 19816 from rfl] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · exact hnot_p2 (by rw [hp2']; simp [ECDSAAdd.wires_append, hm])
  · simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rcases ccxList_wires _ _ _ _ hm with rfl | hm | hm
    · rw [sl_equalNegY] at hwb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · simp only [extra0Wires, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · have hm' := List.mem_of_mem_take hm
      rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem lit1_avoid_window (w : Wire)
    (hw : w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank) :
    w ∉ ECDSAAdd.wires lit1 := by
  have hwb : w = 10015 ∨ (855 ≤ w ∧ w < 870) ∨ w = 871 ∨ (14832 ≤ w ∧ w < 14847) ∨ w = 14848 := by
    simp only [windowRoot, WideBank8.Fast16.windowBits, WideBank8.Fast16.pathBank,
      List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  intro hm
  simp only [lit1, ECDSAAdd.wires_append, Finset.mem_union] at hm
  rcases hm with (hm | hm) | hm
  · simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · rcases ccxList_wires _ _ _ _ hm with rfl | hm | hm
    · rw [sl_equalNegY] at hwb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · simp only [extra1Wires, List.mem_range'_1] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · have hm' := List.mem_of_mem_drop (List.mem_of_mem_take hm)
      rw [yTail_eq, List.mem_range'_1] at hm'; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  · simp only [scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, sl_doubleSelect, sl_equalNegY] at hm; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem litOnly_metrics {n : Nat} : ∀ (c : WCode n), (∀ i ∈ c, ∃ p, i = .literal p) →
    traversals c = 0 ∧
    literalRecords c = ECDSAAdd.measurementCount (litProg c) ∧
    literalToffolis (normalizeW c) = ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (litProg c)) ∧
    ECDSAAdd.Challenge.gateSlots (litProg c) = literalSlotSum c
  | [], _ => by
    refine ⟨rfl, rfl, ?_, rfl⟩
    unfold ECDSAAdd.Baselines.normalizeProgram; rfl
  | .lookup _ _ :: _, hc => by obtain ⟨p, hp⟩ := hc _ List.mem_cons_self; cases hp
  | .literal p :: cs, hc => by
    obtain ⟨ht, hr, hf, hs⟩ := litOnly_metrics cs (fun i hi => hc i (List.mem_cons_of_mem _ hi))
    have hna : ECDSAAdd.Baselines.normalizeProgram (p ++ litProg cs) =
        ECDSAAdd.Baselines.normalizeProgram p ++ ECDSAAdd.Baselines.normalizeProgram (litProg cs) := by
      unfold ECDSAAdd.Baselines.normalizeProgram; simp
    refine ⟨ht, ?_, ?_, ?_⟩
    · simp [literalRecords, litProg, ECDSAAdd.measurementCount_append, hr]
    · simp only [normalizeW, List.map_cons, normalizeWInstr, literalToffolis, litProg, hna, ECDSAAdd.toffoliCount_append]
      change ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram p) + literalToffolis (normalizeW cs) = _
      rw [hf]
    · simp [literalSlotSum, litProg, ECDSAAdd.Challenge.gateSlots_append, hs]

theorem cornerNeg_litOnly : ∀ i ∈ WEX.cornerNeg, ∃ p, i = .literal p := by
  intro i hi; simp only [WEX.cornerNeg, wLiteral, List.mem_append, List.mem_singleton] at hi
  rcases hi with (rfl | rfl) | rfl <;> exact ⟨_, rfl⟩

theorem cornerA1_litOnly : ∀ i ∈ WEX.cornerA1, ∃ p, i = .literal p := by
  intro i hi; simp only [WEX.cornerA1, wLiteral, List.mem_append, List.mem_singleton] at hi
  rcases hi with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> exact ⟨_, rfl⟩

theorem cornerNegProg_eq_litProg : cornerNegProg = litProg WEX.cornerNeg := by
  unfold cornerNegProg; simp [WEX.cornerNeg, wLiteral, litProg]

theorem cornerA1Prog_eq_litProg : cornerA1Prog = litProg WEX.cornerA1 := by
  unfold cornerA1Prog; simp [WEX.cornerA1, wLiteral, litProg]

theorem phase_cancel_last (ph : Bool) (mag c prev p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (c * (prev * p)) =
      mag * c * prev * (if ph then (-1 : ℂ) else 1) := by
  calc (if ph then (-1 : ℂ) else 1) * (mag * p) * (c * (prev * p))
      = mag * c * prev * (if ph then (-1 : ℂ) else 1) * (p * p) := by ring
    _ = mag * c * prev * (if ph then (-1 : ℂ) else 1) := by rw [hp, mul_one]

theorem phase_cancel_mid (ph : Bool) (mag c prev p : ℂ) (hp : p * p = 1) :
    (if ph then (-1 : ℂ) else 1) * (mag * p) * (if ph then (-1 : ℂ) else 1) * (c * (prev * p)) =
      mag * c * prev := by
  cases ph <;>
  · simp only [ite_true, ite_false, Bool.false_eq_true]
    calc _ = (mag * c * prev) * (p * p) := by ring
      _ = mag * c * prev := by rw [hp, mul_one]

theorem rows_portMask_eq (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (a : Nat)
    (ps : List (LookupPort 32768)) :
    portMask (readConstant coeffs Q) (WideSigned.Rows.ports WideBank8.Row16.rows ps) a =
      portMask (readConstant (fun _ : Fin 32768 => coeffs (WideBank8.Row16.rows a)) Q) ps a := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hb : readConstant coeffs Q ((WideSigned.Rows.port WideBank8.Row16.rows p).ref a) =
        readConstant (fun _ : Fin 32768 => coeffs (WideBank8.Row16.rows a)) Q (p.ref a) := rfl
    change (if decide (readConstant coeffs Q ((WideSigned.Rows.port WideBank8.Row16.rows p).ref a) = p.value) = true
        then p.target :: portMask (readConstant coeffs Q) (WideSigned.Rows.ports WideBank8.Row16.rows ps) a
        else portMask (readConstant coeffs Q) (WideSigned.Rows.ports WideBank8.Row16.rows ps) a) =
      (if decide (readConstant (fun _ : Fin 32768 => coeffs (WideBank8.Row16.rows a)) Q (p.ref a) = p.value) = true
        then p.target :: portMask (readConstant (fun _ : Fin 32768 => coeffs (WideBank8.Row16.rows a)) Q) ps a
        else portMask (readConstant (fun _ : Fin 32768 => coeffs (WideBank8.Row16.rows a)) Q) ps a)
    rw [hb, ih]

/-! ### Part 2: Wide (16-bit) ports, disjoint garbage bands, and SelectSwap gadgets `f0`, `f1`, `f2` -/

namespace Wide16
open WideSigned

abbrev r16 : Nat → Fin 65536 := Site1Wire.Wide16.r16

def p0_16 : List (LookupPort 65536) := Rows.ports r16 (p0Ports probeRows)
def p1_16 : List (LookupPort 65536) := Rows.ports r16 (p1Ports probeRows)
def p2_16 : List (LookupPort 65536) := Rows.ports r16 (p2Ports probeRows)
def p0Clear_16 : List (LookupPort 65536) := Rows.ports r16 (p0ClearPorts probeRows)
def extra2_16 : List (LookupPort 65536) := Rows.ports r16 (extra2Ports probeRows)
def finalClear_16 : List (LookupPort 65536) := Rows.ports r16 (finalClearPorts probeRows)

theorem p0_16_targets : portTargets p0_16 = site2Wires ++ extra0Wires := by
  rw [p0_16, Rows.targets]; exact p0Ports_targets probeRows
theorem p1_16_targets : portTargets p1_16 = extra1Wires := by
  rw [p1_16, Rows.targets]; exact p1Ports_targets probeRows
theorem p2_16_targets : portTargets p2_16 = scrShortWires ++ extra2Wires := by
  rw [p2_16, Rows.targets]; exact p2Ports_targets probeRows
theorem p0Clear_16_targets : portTargets p0Clear_16 = p0ClearWires := by
  rw [p0Clear_16, Rows.targets]; exact p0ClearPorts_targets probeRows
theorem extra2_16_targets : portTargets extra2_16 = extra2Wires := by
  rw [extra2_16, Rows.targets]; exact extra2Ports_targets probeRows
theorem finalClear_16_targets : portTargets finalClear_16 = finalClearWires := by
  rw [finalClear_16, Rows.targets]; exact finalClearPorts_targets probeRows

theorem p0_16_len : p0_16.length = 529 := by rw [p0_16, Rows.ports, List.length_map]; exact p0Ports_length probeRows
theorem p1_16_len : p1_16.length = 95 := by rw [p1_16, Rows.ports, List.length_map]; exact p1Ports_length probeRows
theorem p2_16_len : p2_16.length = 401 := by rw [p2_16, Rows.ports, List.length_map]; exact p2Ports_length probeRows

def selBits3 : List Wire := List.range' 858 12 ++ [871]
def selPaths3 : List Wire := List.range' 14835 12 ++ [14848]

def garb0 : List Wire :=
  List.range' 14115 259 ++ [14847] ++ List.range' 14866 8 ++ List.range' 14884 260 ++ [15654]

def g1_1 : List Wire := List.range' 14115 95
def g1_2 : List Wire := List.range' 14210 95
def g1_3 : List Wire := List.range' 14305 69 ++ List.range' 14979 26
def g1_4 : List Wire := List.range' 15005 95
def g1_5 : List Wire := List.range' 15100 44 ++ List.range' 15399 51
def g1_6 : List Wire := List.range' 15450 95
def g1_7 : List Wire := List.range' 15545 95
def garb1 : List Wire := g1_1 ++ g1_2 ++ g1_3 ++ g1_4 ++ g1_5 ++ g1_6 ++ g1_7

-- Note: `14832` is in `pathBank` (clean at Pass 2 entry) and outside `selPaths1` (`14833..14846, 14848`),
-- reset to `false` immediately after Pass 2's swap net.
def garb2 : List Wire :=
  List.range' 14115 259 ++ [14832, 14847] ++ List.range' 14849 25 ++ List.range' 15142 2 ++ List.range' 15542 113

theorem garb0_len : garb0.length = 529 := by simp [garb0]
theorem g1_1_len : g1_1.length = 95 := by simp [g1_1]
theorem g1_2_len : g1_2.length = 95 := by simp [g1_2]
theorem g1_3_len : g1_3.length = 95 := by simp [g1_3]
theorem g1_4_len : g1_4.length = 95 := by simp [g1_4]
theorem g1_5_len : g1_5.length = 95 := by simp [g1_5]
theorem g1_6_len : g1_6.length = 95 := by simp [g1_6]
theorem g1_7_len : g1_7.length = 95 := by simp [g1_7]
theorem garb1_len : garb1.length = 665 := by
  simp [garb1, g1_1_len, g1_2_len, g1_3_len, g1_4_len, g1_5_len, g1_6_len, g1_7_len]
theorem garb2_len : garb2.length = 401 := by simp [garb2]

theorem mem_garb0 {w : Wire} : w ∈ garb0 ↔
    (14115 ≤ w ∧ w < 14374) ∨ w = 14847 ∨ (14866 ≤ w ∧ w < 14874) ∨ (14884 ≤ w ∧ w < 15144) ∨ w = 15654 := by
  simp only [garb0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire, ECDSAAdd.Wire]; omega

theorem mem_garb1 {w : Wire} : w ∈ garb1 ↔
    (14115 ≤ w ∧ w < 14374) ∨ (14979 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15640) := by
  simp only [garb1, g1_1, g1_2, g1_3, g1_4, g1_5, g1_6, g1_7, List.mem_append, List.mem_range'_1]
  dsimp only [Wire, ECDSAAdd.Wire]; omega

theorem mem_garb2 {w : Wire} : w ∈ garb2 ↔
    (14115 ≤ w ∧ w < 14374) ∨ w = 14832 ∨ w = 14847 ∨ (14849 ≤ w ∧ w < 14874) ∨
      (15142 ≤ w ∧ w < 15144) ∨ (15542 ≤ w ∧ w < 15655) := by
  simp only [garb2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire, ECDSAAdd.Wire]; omega

theorem mem_p0Wires {w : Wire} (h : w ∈ site2Wires ++ extra0Wires) :
    (14374 ≤ w ∧ w < 14630) ∨ w = 14883 ∨ (15399 ≤ w ∧ w < 15654) ∨ (14849 ≤ w ∧ w < 14866) := by
  simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at h
  dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem mem_p2Wires {w : Wire} (h : w ∈ scrShortWires ++ extra2Wires) :
    (14884 ≤ w ∧ w < 15142) ∨ (15399 ≤ w ∧ w < 15542) := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (shortWires_bounds w h)
  · simp only [extra2Wires, List.mem_range'_1] at h; exact Or.inr h

theorem garb0_nodup : garb0.Nodup := by
  rw [garb0]
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
    ⟨List.nodup_range', List.nodup_singleton _, fun a ha b hb => by simp only [List.mem_range'_1, List.mem_singleton] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩,
    List.nodup_range', fun a ha b hb => by simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩,
    List.nodup_range', fun a ha b hb => by simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩,
    List.nodup_singleton _, fun a ha b hb => by simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩

theorem garb1_nodup : garb1.Nodup := by
  have nd3 : g1_3.Nodup := List.nodup_append.mpr ⟨List.nodup_range', List.nodup_range', fun a ha b hb => by
    simp only [List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩
  have nd5 : g1_5.Nodup := List.nodup_append.mpr ⟨List.nodup_range', List.nodup_range', fun a ha b hb => by
    simp only [List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩
  have app (A B : List Wire) (hA : A.Nodup) (hB : B.Nodup) (hd : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) : (A ++ B).Nodup :=
    List.nodup_append.mpr ⟨hA, hB, hd⟩
  rw [garb1]
  refine app _ _ (app _ _ (app _ _ (app _ _ (app _ _ (app _ _ List.nodup_range' List.nodup_range'
    (fun a ha b hb => by simp only [g1_1, g1_2, List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
    nd3 (fun a ha b hb => by simp only [g1_1, g1_2, g1_3, List.mem_append, List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
    List.nodup_range' (fun a ha b hb => by simp only [g1_1, g1_2, g1_3, g1_4, List.mem_append, List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
    nd5 (fun a ha b hb => by simp only [g1_1, g1_2, g1_3, g1_4, g1_5, List.mem_append, List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
    List.nodup_range' (fun a ha b hb => by simp only [g1_1, g1_2, g1_3, g1_4, g1_5, g1_6, List.mem_append, List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
    List.nodup_range' (fun a ha b hb => by simp only [g1_1, g1_2, g1_3, g1_4, g1_5, g1_6, g1_7, List.mem_append, List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega)

theorem garb2_nodup : garb2.Nodup := by
  have nd1 : ([14832, 14847] : List Wire).Nodup := by decide
  rw [garb2]
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
    ⟨List.nodup_range', nd1, fun a ha b hb => by simp only [List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩,
    List.nodup_range', fun a ha b hb => by simp only [List.mem_append, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩,
    List.nodup_range', fun a ha b hb => by simp only [List.mem_append, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩,
    List.nodup_range', fun a ha b hb => by simp only [List.mem_append, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩

theorem p0Wires_nodup : (site2Wires ++ extra0Wires).Nodup :=
  List.nodup_append.mpr ⟨site2Wires_nodup, by rw [extra0Wires]; exact List.nodup_range', fun a ha b hb => by
    simp only [site2Wires, cxWord, cyWord, extra0Wires, List.mem_append, List.mem_cons, List.mem_range'_1] at ha hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩

theorem p2Wires_nodup : (scrShortWires ++ extra2Wires).Nodup :=
  List.nodup_append.mpr ⟨scrShortWires_nd, by rw [extra2Wires]; exact List.nodup_range', fun a ha b hb => by
    have := shortWires_bounds a ha; simp only [extra2Wires, List.mem_range'_1] at hb
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩

theorem p0ClearWires_nodup : p0ClearWires.Nodup :=
  List.nodup_append.mpr ⟨by rw [cyTailWires]; exact List.nodup_range', by rw [extra0Wires]; exact List.nodup_range',
    fun a ha b hb => by simp only [cyTailWires, extra0Wires, List.mem_range'_1] at ha hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩

theorem extra1Wires_nodup : extra1Wires.Nodup := by rw [extra1Wires]; exact List.nodup_range'
theorem extra2Wires_nodup : extra2Wires.Nodup := by rw [extra2Wires]; exact List.nodup_range'

theorem finalClearWires_nodup : finalClearWires.Nodup := by
  rw [finalClearWires, List.nodup_append]
  refine ⟨List.nodup_append.mpr ⟨scrShortWires_nd, by rw [cxWord]; exact List.nodup_range', fun a ha b hb => by
    have := shortWires_bounds a ha; simp only [cxWord, List.mem_range'_1] at hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩,
    List.nodup_singleton _, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb
      rcases List.mem_append.mp ha with h | h
      · have := shortWires_bounds a h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · simp only [cxWord, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩

def f0 : SS1 65536 where
  bits := WideBank8.Fast16.windowBits
  paths := WideBank8.Fast16.pathBank
  selBits := WideBank8.Fast16.selBits1
  selPaths := WideBank8.Fast16.selPaths1
  guard := windowRoot
  ports := p0_16
  g1 := garb0

def f1 : SS3 65536 where
  bits := WideBank8.Fast16.windowBits
  paths := WideBank8.Fast16.pathBank
  selBits := selBits3
  selPaths := selPaths3
  guard := windowRoot
  ports := p1_16
  g1 := g1_1
  g2 := g1_2
  g3 := g1_3
  g4 := g1_4
  g5 := g1_5
  g6 := g1_6
  g7 := g1_7

def f2 : SS1 65536 where
  bits := WideBank8.Fast16.windowBits
  paths := WideBank8.Fast16.pathBank
  selBits := WideBank8.Fast16.selBits1
  selPaths := WideBank8.Fast16.selPaths1
  guard := windowRoot
  ports := p2_16
  g1 := garb2

theorem f0_geo : f0.Geo where
  bitsEq := by decide
  pathsSub := fun w hw => by
    simp only [f0, WideBank8.Fast16.selPaths1, WideBank8.Fast16.pathBank,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw ⊢
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  selLen := by decide
  selNodup := by decide
  selDisj := List.disjoint_left.mpr fun w hw hm => by
    rw [f0, p0_16_targets] at hm
    have hb : (14115 ≤ w ∧ w < 14630) ∨ w = 14847 ∨ (14849 ≤ w ∧ w < 14874) ∨ (14883 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
      rcases List.mem_append.mp hm with h | h
      · have := mem_p0Wires h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · rw [mem_garb0] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    simp only [f0, windowRoot, WideBank8.Fast16.selBits1, WideBank8.Fast16.selPaths1,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change garb0.length = p0_16.length; rw [garb0_len, p0_16_len]
  nodup := by
    rw [f0, p0_16_targets]
    exact List.nodup_append.mpr ⟨p0Wires_nodup, garb0_nodup, fun a ha b hb => by
      have h1 := mem_p0Wires ha; rw [mem_garb0] at hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩
  n855 := fun hm => by
    rw [f0, p0_16_targets] at hm
    rcases List.mem_append.mp hm with h | h
    · have := mem_p0Wires h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · rw [mem_garb0] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem f1_geo : f1.Geo where
  bitsEq := by decide
  pathsSub := fun w hw => by
    simp only [f1, selPaths3, WideBank8.Fast16.pathBank,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw ⊢
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  selLen := by decide
  selNodup := by decide
  selDisj := List.disjoint_left.mpr fun w hw hm => by
    rw [f1, p1_16_targets] at hm
    change w ∈ extra1Wires ++ garb1 at hm
    have hb : (14115 ≤ w ∧ w < 14374) ∨ (14884 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15640) := by
      rcases List.mem_append.mp hm with h | h
      · simp only [extra1Wires, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · rw [mem_garb1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    simp only [f1, windowRoot, selBits3, selPaths3,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change g1_1.length = p1_16.length; rw [g1_1_len, p1_16_len]
  len2 := by change g1_2.length = p1_16.length; rw [g1_2_len, p1_16_len]
  len3 := by change g1_3.length = p1_16.length; rw [g1_3_len, p1_16_len]
  len4 := by change g1_4.length = p1_16.length; rw [g1_4_len, p1_16_len]
  len5 := by change g1_5.length = p1_16.length; rw [g1_5_len, p1_16_len]
  len6 := by change g1_6.length = p1_16.length; rw [g1_6_len, p1_16_len]
  len7 := by change g1_7.length = p1_16.length; rw [g1_7_len, p1_16_len]
  nodup := by
    rw [f1, p1_16_targets]
    change (extra1Wires ++ garb1).Nodup
    exact List.nodup_append.mpr ⟨extra1Wires_nodup, garb1_nodup, fun a ha b hb => by
      simp only [extra1Wires, List.mem_range'_1] at ha; rw [mem_garb1] at hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩
  n855 := fun hm => by
    rw [f1, p1_16_targets] at hm; change (855 : Wire) ∈ extra1Wires ++ garb1 at hm
    rcases List.mem_append.mp hm with h | h
    · simp only [extra1Wires, List.mem_range'_1] at h; omega
    · rw [mem_garb1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  n856 := fun hm => by
    rw [f1, p1_16_targets] at hm; change (856 : Wire) ∈ extra1Wires ++ garb1 at hm
    rcases List.mem_append.mp hm with h | h
    · simp only [extra1Wires, List.mem_range'_1] at h; omega
    · rw [mem_garb1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  n857 := fun hm => by
    rw [f1, p1_16_targets] at hm; change (857 : Wire) ∈ extra1Wires ++ garb1 at hm
    rcases List.mem_append.mp hm with h | h
    · simp only [extra1Wires, List.mem_range'_1] at h; omega
    · rw [mem_garb1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

theorem f2_geo : f2.Geo where
  bitsEq := by decide
  pathsSub := fun w hw => by
    simp only [f2, WideBank8.Fast16.selPaths1, WideBank8.Fast16.pathBank,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw ⊢
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  selLen := by decide
  selNodup := by decide
  selDisj := List.disjoint_left.mpr fun w hw hm => by
    rw [f2, p2_16_targets] at hm
    have hb : (14115 ≤ w ∧ w < 14374) ∨ w = 14832 ∨ w = 14847 ∨ (14849 ≤ w ∧ w < 14874) ∨
        (14884 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
      rcases List.mem_append.mp hm with h | h
      · have := mem_p2Wires h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · rw [mem_garb2] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    simp only [f2, windowRoot, WideBank8.Fast16.selBits1, WideBank8.Fast16.selPaths1,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
    dsimp only [Wire, ECDSAAdd.Wire] at *; omega
  len1 := by change garb2.length = p2_16.length; rw [garb2_len, p2_16_len]
  nodup := by
    rw [f2, p2_16_targets]
    exact List.nodup_append.mpr ⟨p2Wires_nodup, garb2_nodup, fun a ha b hb => by
      have h1 := mem_p2Wires ha; rw [mem_garb2] at hb; dsimp only [Wire, ECDSAAdd.Wire] at *; omega⟩
  n855 := fun hm => by
    rw [f2, p2_16_targets] at hm
    rcases List.mem_append.mp hm with h | h
    · have := mem_p2Wires h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    · rw [mem_garb2] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

/-! ### Part 3: 14-step `cornerFusedProg`, `cornerFusedSrc`, counts, wellFormed, support, slots -/

def d1 : List (MeasuredClear.ClearPort 65536) := clearData f0.garbPorts
def d2 : List (MeasuredClear.ClearPort 65536) := clearData p0Clear_16
def d3 : List (MeasuredClear.ClearPort 65536) := clearData f1.garbPorts
def d4 : List (MeasuredClear.ClearPort 65536) := clearData p1_16
def d5 : List (MeasuredClear.ClearPort 65536) := clearData f2.garbPorts
def d6 : List (MeasuredClear.ClearPort 65536) := clearData extra2_16
def d7 : List (MeasuredClear.ClearPort 65536) := clearData finalClear_16
def allData : List (MeasuredClear.ClearPort 65536) := d1 ++ d2 ++ d3 ++ d4 ++ d5 ++ d6 ++ d7

theorem d1_targets : d1.map MeasuredClear.ClearPort.target = garb0 := by
  rw [d1, clearData_targets]; exact f0.garbPorts_targets f0_geo
theorem d2_targets : d2.map MeasuredClear.ClearPort.target = p0ClearWires := by
  rw [d2, clearData_targets]; exact p0Clear_16_targets
theorem d3_targets : d3.map MeasuredClear.ClearPort.target = garb1 := by
  rw [d3, clearData_targets]; exact f1.garbPorts_targets f1_geo
theorem d4_targets : d4.map MeasuredClear.ClearPort.target = extra1Wires := by
  rw [d4, clearData_targets]; exact p1_16_targets
theorem d5_targets : d5.map MeasuredClear.ClearPort.target = garb2 := by
  rw [d5, clearData_targets]; exact f2.garbPorts_targets f2_geo
theorem d6_targets : d6.map MeasuredClear.ClearPort.target = extra2Wires := by
  rw [d6, clearData_targets]; exact extra2_16_targets
theorem d7_targets : d7.map MeasuredClear.ClearPort.target = finalClearWires := by
  rw [d7, clearData_targets]; exact finalClear_16_targets

theorem d1_len : d1.length = 529 := by have := congrArg List.length d1_targets; simpa [garb0_len] using this
theorem d2_len : d2.length = 272 := by have := congrArg List.length d2_targets; simpa [p0ClearWires_len] using this
theorem d3_len : d3.length = 665 := by have := congrArg List.length d3_targets; simpa [garb1_len] using this
theorem d4_len : d4.length = 95 := by have := congrArg List.length d4_targets; simpa [extra1Wires_len] using this
theorem d5_len : d5.length = 401 := by have := congrArg List.length d5_targets; simpa [garb2_len] using this
theorem d6_len : d6.length = 143 := by have := congrArg List.length d6_targets; simpa [extra2Wires_len] using this
theorem d7_len : d7.length = 515 := by have := congrArg List.length d7_targets; simpa [finalClearWires_len] using this
theorem allData_len : allData.length = 2620 := by
  simp only [allData, List.length_append, d1_len, d2_len, d3_len, d4_len, d5_len, d6_len, d7_len]

theorem f0_rec : codeRecords f0.selBits f0.selPaths windowRoot f0.selCode = 32767 := by
  rw [f0.loadProg_records f0_geo]; decide
theorem f1_rec : codeRecords f1.selBits f1.selPaths windowRoot f1.selCode = 8191 := by
  rw [f1.loadProg_records f1_geo]; decide
theorem f2_rec : codeRecords f2.selBits f2.selPaths windowRoot f2.selCode = 32767 := by
  rw [f2.loadProg_records f2_geo]; decide

abbrev hot8 := Site1Wire.Wide16.hot8
abbrev scratch8 := Site1Wire.Wide16.scratch8
abbrev tree8 := Site1Wire.Wide16.tree8
abbrev fixRec8 := Site1Wire.Wide16.fixRec8

theorem hot8_in_finalClear (i : Fin 256) : hot8 i ∈ finalClearWires := by
  have hi := i.isLt
  apply List.mem_append_left; apply List.mem_append_right
  simp only [hot8, Site1Wire.Wide16.hot8, cxWord, List.mem_range'_1]
  dsimp only [Wire, ECDSAAdd.Wire]; omega

local notation "cornerRec" => (76855 + mLit0 + mLit2b)

private theorem fin_step14 (s l f : Nat) (hl : l = 515) (hf : f = 510) : s + l + f = s + 1025 := by omega
private theorem fin_add_step (s l k1 k2 k3 m : Nat) (hl : l = k1) (hk : k1 + k2 = k3) : s + l + (m + k2) = s + (m + k3) := by omega
private theorem fin_zero_step (s r : Nat) : s + 0 + r = s + r := by omega
private theorem fin_step13 (s m : Nat) : s + m + 1025 = s + (m + 1025) := by omega
private theorem fin_step3 (s a b : Nat) : s + a + (b + 43559) = s + (a + b + 43559) := by omega
private theorem fin_step0 (s l a b : Nat) (hl : l = 32767) : s + l + (a + b + 44088) = s + (76855 + a + b) := by omega

def step14 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + 1025) :=
  castFinish (fin_step14 start finalClearWires.length fixRec8 finalClearWires_len Site1Wire.Wide16.fixRec8_eq)
    (MeasuredClear.measureThen (R := fixRec8)
      (fun cur rs => castFinish (by rw [fixRec8, Site1Wire.Wide16.fixRec8]; exact Nat.add_assoc cur _ 255)
        (MeasuredClear.fixupProgram8 allData rs WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp))
      finalClearWires start refs)

def step13 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 1025)) :=
  castFinish (fin_step13 start mLit2b)
    ((literalFixed lit2bNorm mLit2b ((literal_meas (n := 65536) _).trans lit2bNorm_meas) start).append
      (step14 (start + mLit2b) (refs.map (Fin.castLE (Nat.le_add_right _ _)))))

def step12 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 1168)) :=
  castFinish (fin_add_step start extra2Wires.length 143 1025 1168 mLit2b extra2Wires_len rfl)
    (MeasuredClear.measureThen (R := mLit2b + 1025) (fun cur rs => step13 cur rs) extra2Wires start refs)

def step11 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 1168)) :=
  castFinish (fin_zero_step start (mLit2b + 1168))
    ((literalFixed lit2aNorm 0 ((literal_meas (n := 65536) _).trans lit2aNorm_meas) start).append
      (step12 (start + 0) (refs.map (Fin.castLE (Nat.le_add_right _ _)))))

def step10 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 1569)) :=
  castFinish (fin_add_step start garb2.length 401 1168 1569 mLit2b garb2_len rfl)
    (MeasuredClear.measureThen (R := mLit2b + 1168) (fun cur rs => step11 cur rs) garb2 start refs)

def step9 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 34336)) :=
  castFinish (fin_add_step start _ 32767 1569 34336 mLit2b f2_rec rfl)
    ((f2.loadProg start).append
      (step10 (start + codeRecords f2.selBits f2.selPaths windowRoot f2.selCode)
        (refs.map (Fin.castLE (Nat.le_add_right _ _)))))

def step8 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 34431)) :=
  castFinish (fin_add_step start extra1Wires.length 95 34336 34431 mLit2b extra1Wires_len rfl)
    (MeasuredClear.measureThen (R := mLit2b + 34336) (fun cur rs => step9 cur rs) extra1Wires start refs)

def step7 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 34431)) :=
  castFinish (fin_zero_step start (mLit2b + 34431))
    ((literalFixed lit1Norm 0 ((literal_meas (n := 65536) _).trans lit1Norm_meas) start).append
      (step8 (start + 0) (refs.map (Fin.castLE (Nat.le_add_right _ _)))))

def step6 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 35096)) :=
  castFinish (fin_add_step start garb1.length 665 34431 35096 mLit2b garb1_len rfl)
    (MeasuredClear.measureThen (R := mLit2b + 34431) (fun cur rs => step7 cur rs) garb1 start refs)

def step5 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 43287)) :=
  castFinish (fin_add_step start _ 8191 35096 43287 mLit2b f1_rec rfl)
    ((f1.loadProg start).append
      (step6 (start + codeRecords f1.selBits f1.selPaths windowRoot f1.selCode)
        (refs.map (Fin.castLE (Nat.le_add_right _ _)))))

def step4 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit2b + 43559)) :=
  castFinish (fin_add_step start p0ClearWires.length 272 43287 43559 mLit2b p0ClearWires_len rfl)
    (MeasuredClear.measureThen (R := mLit2b + 43287) (fun cur rs => step5 cur rs) p0ClearWires start refs)

def step3 (start : Nat) (refs : List (Fin start)) : Straight 65536 start (start + (mLit0 + mLit2b + 43559)) :=
  castFinish (fin_step3 start mLit0 mLit2b)
    ((literalFixed lit0Norm mLit0 ((literal_meas (n := 65536) _).trans lit0Norm_meas) start).append
      (step4 (start + mLit0) (refs.map (Fin.castLE (Nat.le_add_right _ _)))))

def step2 (start : Nat) : Straight 65536 start (start + (mLit0 + mLit2b + 44088)) :=
  castFinish (fin_add_step start garb0.length 529 43559 44088 (mLit0 + mLit2b) garb0_len rfl)
    (MeasuredClear.measureThen (R := mLit0 + mLit2b + 43559) (fun cur rs => step3 cur rs) garb0 start List.nil)

def cornerFusedProg (start : Nat) : Straight 65536 start (start + cornerRec) :=
  castFinish (fin_step0 start _ mLit0 mLit2b f0_rec)
    ((f0.loadProg start).append
      (step2 (start + codeRecords f0.selBits f0.selPaths windowRoot f0.selCode)))

attribute [local irreducible] step14 step13 step12 step11 step10 step9 step8 step7 step6 step5 step4 step3 step2 cornerFusedProg

def step14Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  measureResetThen finalClearWires (fun o7 =>
    MeasuredClear.fixupSource8 allData (os ++ o7) read WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp)
def step13Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  (literalSource lit2bNorm).seq (step14Src read os)
def step12Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  measureResetThen extra2Wires (fun o6 => step13Src read (os ++ o6))
def step11Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  (literalSource lit2aNorm).seq (step12Src read os)
def step10Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  measureResetThen garb2 (fun o5 => step11Src read (os ++ o5))
def step9Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  (f2.loadSource read).seq (step10Src read os)
def step8Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  measureResetThen extra1Wires (fun o4 => step9Src read (os ++ o4))
def step7Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  (literalSource lit1Norm).seq (step8Src read os)
def step6Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  measureResetThen garb1 (fun o3 => step7Src read (os ++ o3))
def step5Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  (f1.loadSource read).seq (step6Src read os)
def step4Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  measureResetThen p0ClearWires (fun o2 => step5Src read (os ++ o2))
def step3Src (read : ConstantBit 65536 → Bool) (os : List Bool) : AdaptiveCircuit :=
  (literalSource lit0Norm).seq (step4Src read os)
def step2Src (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  measureResetThen garb0 (fun o1 => step3Src read o1)
def cornerFusedSrc (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  (f0.loadSource read).seq (step2Src read)

theorem step14_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step14 start refs).instantiate read h).run = (step14Src read (refs.map h)).run := by
  rw [step14, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun o => MeasuredClear.fixupSource8 allData o read WideBank8.low8 hot8 tree8 windowRoot scratch8 WideBank8.Fast16.bank15.hp) read
      (fun cur rs hh => by rw [castFinish_instantiate, MeasuredClear.fixupProgram_run8])]
  rfl

theorem step13_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step13 start refs).instantiate read h).run = (step13Src read (refs.map h)).run := by
  rw [step13, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step14Src read (refs.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'; rw [step14_run, List.map_map]; congr 2; rw [← hh']; rfl

theorem step12_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step12 start refs).instantiate read h).run = (step12Src read (refs.map h)).run := by
  rw [step12, castFinish_instantiate, MeasuredClear.measureThen_run _ (fun o => step13Src read o) read (fun cur rs hh => step13_run read cur rs hh)]; rfl

theorem step11_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step11 start refs).instantiate read h).run = (step11Src read (refs.map h)).run := by
  rw [step11, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step12Src read (refs.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'; rw [step12_run, List.map_map]; congr 2; rw [← hh']; rfl

theorem step10_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step10 start refs).instantiate read h).run = (step10Src read (refs.map h)).run := by
  rw [step10, castFinish_instantiate, MeasuredClear.measureThen_run _ (fun o => step11Src read o) read (fun cur rs hh => step11_run read cur rs hh)]; rfl

theorem step9_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step9 start refs).instantiate read h).run = (step9Src read (refs.map h)).run := by
  rw [step9, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step10Src read (refs.map h)),
    AdaptiveCircuit.run_seq, f2.loadProg_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'; rw [step10_run, List.map_map]; congr 2; rw [← hh']; rfl

theorem step8_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step8 start refs).instantiate read h).run = (step8Src read (refs.map h)).run := by
  rw [step8, castFinish_instantiate, MeasuredClear.measureThen_run _ (fun o => step9Src read o) read (fun cur rs hh => step9_run read cur rs hh)]; rfl

theorem step7_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step7 start refs).instantiate read h).run = (step7Src read (refs.map h)).run := by
  rw [step7, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step8Src read (refs.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'; rw [step8_run, List.map_map]; congr 2; rw [← hh']; rfl

theorem step6_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step6 start refs).instantiate read h).run = (step6Src read (refs.map h)).run := by
  rw [step6, castFinish_instantiate, MeasuredClear.measureThen_run _ (fun o => step7Src read o) read (fun cur rs hh => step7_run read cur rs hh)]; rfl

theorem step5_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step5 start refs).instantiate read h).run = (step5Src read (refs.map h)).run := by
  rw [step5, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step6Src read (refs.map h)),
    AdaptiveCircuit.run_seq, f1.loadProg_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'; rw [step6_run, List.map_map]; congr 2; rw [← hh']; rfl

theorem step4_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step4 start refs).instantiate read h).run = (step4Src read (refs.map h)).run := by
  rw [step4, castFinish_instantiate, MeasuredClear.measureThen_run _ (fun o => step5Src read o) read (fun cur rs hh => step5_run read cur rs hh)]; rfl

theorem step3_run (read : ConstantBit 65536 → Bool) (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((step3 start refs).instantiate read h).run = (step3Src read (refs.map h)).run := by
  rw [step3, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl (step4Src read (refs.map h)),
    AdaptiveCircuit.run_seq, literalFixed_run, ← AdaptiveCircuit.run_seq]
  · rfl
  · intro h' hh'; rw [step4_run, List.map_map]; congr 2; rw [← hh']; rfl

theorem step2_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((step2 start).instantiate read h).run = (step2Src read).run := by
  rw [step2, castFinish_instantiate, MeasuredClear.measureThen_run _ (fun o => step3Src read o) read (fun cur rs hh => step3_run read cur rs hh)]
  simp only [List.map_nil, List.nil_append]; rfl

theorem cornerFused_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((cornerFusedProg start).instantiate read h).run = (cornerFusedSrc read).run := by
  rw [cornerFusedProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun hh => step2_run read _ hh),
    AdaptiveCircuit.run_seq, f0.loadProg_run, ← AdaptiveCircuit.run_seq]
  rfl

local notation "cornerTP" =>
  (75822 + ECDSAAdd.toffoliCount lit0Norm + ECDSAAdd.toffoliCount lit1Norm +
    ECDSAAdd.toffoliCount lit2aNorm + ECDSAAdd.toffoliCount lit2bNorm)

theorem cornerFused_tCount (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((cornerFusedProg start).instantiate read h).tCount = 7 * cornerTP := by
  have h14 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step14 c rs).instantiate read hh).tCount = 7 * 502 := by
    rw [step14, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => by
      rw [castFinish_instantiate, MeasuredClear.fixupProgram_tCount8 _ _ _ _ _ _ _ _ Site1Wire.Wide16.tree8_layout,
        Site1Wire.Wide16.tree8_nodes])]
  have h13 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step13 c rs).instantiate read hh).tCount = 7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502 := by
    rw [step13, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h14 _ _ h'), literalFixed_tCount]
  have h12 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step12 c rs).instantiate read hh).tCount = 7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502 := by
    rw [step12, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h13 cur rs' h')]
  have h11 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step11 c rs).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502) := by
    rw [step11, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h12 _ _ h'), literalFixed_tCount]
  have h10 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step10 c rs).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502) := by
    rw [step10, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h11 cur rs' h')]
  have h9 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step9 c rs).instantiate read hh).tCount =
        7 * 33168 + (7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502)) := by
    rw [step9, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h10 _ _ h'), f2.loadProg_tCount read f2_geo]
    have hbl : f2.selBits.length = 15 := by decide
    have hpl : f2.ports.length = 401 := p2_16_len
    rw [hbl, hpl]
    exact congrArg (· + _) (by decide)
  have h8 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step8 c rs).instantiate read hh).tCount =
        7 * 33168 + (7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502)) := by
    rw [step8, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h9 cur rs' h')]
  have h7 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step7 c rs).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount lit1Norm +
          (7 * 33168 + (7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502))) := by
    rw [step7, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h8 _ _ h'), literalFixed_tCount]
  have h6 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step6 c rs).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount lit1Norm +
          (7 * 33168 + (7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502))) := by
    rw [step6, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h7 cur rs' h')]
  have h5 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step5 c rs).instantiate read hh).tCount =
        7 * 8856 + (7 * ECDSAAdd.toffoliCount lit1Norm +
          (7 * 33168 + (7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502)))) := by
    rw [step5, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h6 _ _ h'), f1.loadProg_tCount read f1_geo]
    have hbl : f1.selBits.length = 13 := by decide
    have hpl : f1.ports.length = 95 := p1_16_len
    rw [hbl, hpl]
    exact congrArg (· + _) (by decide)
  have h4 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step4 c rs).instantiate read hh).tCount =
        7 * 8856 + (7 * ECDSAAdd.toffoliCount lit1Norm +
          (7 * 33168 + (7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502)))) := by
    rw [step4, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h5 cur rs' h')]
  have h3 (c : Nat) (rs : List (Fin c)) (hh : Fin c → Bool) :
      ((step3 c rs).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount lit0Norm + (7 * 8856 + (7 * ECDSAAdd.toffoliCount lit1Norm +
          (7 * 33168 + (7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502))))) := by
    rw [step3, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h4 _ _ h'), literalFixed_tCount]
  have h2 (c : Nat) (hh : Fin c → Bool) :
      ((step2 c).instantiate read hh).tCount =
        7 * ECDSAAdd.toffoliCount lit0Norm + (7 * 8856 + (7 * ECDSAAdd.toffoliCount lit1Norm +
          (7 * 33168 + (7 * ECDSAAdd.toffoliCount lit2aNorm + (7 * ECDSAAdd.toffoliCount lit2bNorm + 7 * 502))))) := by
    rw [step2, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (fun cur rs' h' => h3 cur rs' h')]
  rw [cornerFusedProg, castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => h2 _ h'), f0.loadProg_tCount read f0_geo]
  have hbl : f0.selBits.length = 15 := by decide
  have hpl : f0.ports.length = 529 := p0_16_len
  rw [hbl, hpl]
  generalize ECDSAAdd.toffoliCount lit0Norm = t0
  generalize ECDSAAdd.toffoliCount lit1Norm = t1
  generalize ECDSAAdd.toffoliCount lit2aNorm = t2a
  generalize ECDSAAdd.toffoliCount lit2bNorm = t2b
  omega

theorem cornerFused_residue (start : Nat) : AndGadget.residue (cornerFusedProg start) = 0 := by
  have h14 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step14 c rs) = 0 := by
    rw [step14, AndGadget.residue_cast]
    exact MeasuredClear.measureThen_residue _ (fun _ _ => by rw [AndGadget.residue_cast]; exact MeasuredClear.fixupProgram_residue8 _ _ _ _ _ _ _ _) _ _ _
  have h13 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step13 c rs) = 0 := by
    rw [step13, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast, WEXCredit.literal_residue, h14]
  have h12 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step12 c rs) = 0 := by
    rw [step12, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h13 _ _ _
  have h11 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step11 c rs) = 0 := by
    rw [step11, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast, WEXCredit.literal_residue, h12]
  have h10 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step10 c rs) = 0 := by
    rw [step10, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h11 _ _ _
  have h9 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step9 c rs) = 0 := by
    rw [step9, AndGadget.residue_cast, AndGadget.residue_append, f2.loadProg_residue, h10]
  have h8 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step8 c rs) = 0 := by
    rw [step8, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h9 _ _ _
  have h7 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step7 c rs) = 0 := by
    rw [step7, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast, WEXCredit.literal_residue, h8]
  have h6 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step6 c rs) = 0 := by
    rw [step6, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h7 _ _ _
  have h5 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step5 c rs) = 0 := by
    rw [step5, AndGadget.residue_cast, AndGadget.residue_append, f1.loadProg_residue, h6]
  have h4 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step4 c rs) = 0 := by
    rw [step4, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h5 _ _ _
  have h3 (c : Nat) (rs : List (Fin c)) : AndGadget.residue (step3 c rs) = 0 := by
    rw [step3, AndGadget.residue_cast, AndGadget.residue_append, literalFixed, WEXCredit.residue_naive_cast, WEXCredit.literal_residue, h4]
  have h2 (c : Nat) : AndGadget.residue (step2 c) = 0 := by
    rw [step2, AndGadget.residue_cast]; exact MeasuredClear.measureThen_residue _ h3 _ _ _
  rw [cornerFusedProg, AndGadget.residue_cast, AndGadget.residue_append, f0.loadProg_residue, h2]

theorem cornerFused_wellFormed (start : Nat) : (cornerFusedProg start).WellFormed := by
  have h14 (c : Nat) (rs : List (Fin c)) : (step14 c rs).WellFormed := by
    rw [step14, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := fixRec8) _ (fun _ _ => by
      rw [castFinish_wellFormed]
      exact MeasuredClear.fixupProgram_wellFormed8 _ _ _ _ _ _ _ _
        Site1Wire.Wide16.tree8_layout Site1Wire.Wide16.hot8_inj Site1Wire.Wide16.low8_ne_hot8
        Site1Wire.Wide16.scratch8_not_tree Site1Wire.Wide16.scratch8_not_hot) _ _ _
  have h13 (c : Nat) (rs : List (Fin c)) : (step13 c rs).WellFormed := by
    rw [step13, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ lit2bNorm_valid _) (h14 _ _)
  have h12 (c : Nat) (rs : List (Fin c)) : (step12 c rs).WellFormed := by
    rw [step12, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mLit2b + 1025) (fun cur rs' => step13 cur rs') h13 extra2Wires c rs
  have h11 (c : Nat) (rs : List (Fin c)) : (step11 c rs).WellFormed := by
    rw [step11, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ lit2aNorm_valid _) (h12 _ _)
  have h10 (c : Nat) (rs : List (Fin c)) : (step10 c rs).WellFormed := by
    rw [step10, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mLit2b + 1168) (fun cur rs' => step11 cur rs') h11 garb2 c rs
  have h9 (c : Nat) (rs : List (Fin c)) : (step9 c rs).WellFormed := by
    rw [step9, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (f2.loadProg_wellFormed f2_geo _) (h10 _ _)
  have h8 (c : Nat) (rs : List (Fin c)) : (step8 c rs).WellFormed := by
    rw [step8, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mLit2b + 34336) (fun cur rs' => step9 cur rs') h9 extra1Wires c rs
  have h7 (c : Nat) (rs : List (Fin c)) : (step7 c rs).WellFormed := by
    rw [step7, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ lit1Norm_valid _) (h8 _ _)
  have h6 (c : Nat) (rs : List (Fin c)) : (step6 c rs).WellFormed := by
    rw [step6, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mLit2b + 34431) (fun cur rs' => step7 cur rs') h7 garb1 c rs
  have h5 (c : Nat) (rs : List (Fin c)) : (step5 c rs).WellFormed := by
    rw [step5, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (f1.loadProg_wellFormed f1_geo _) (h6 _ _)
  have h4 (c : Nat) (rs : List (Fin c)) : (step4 c rs).WellFormed := by
    rw [step4, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mLit2b + 43287) (fun cur rs' => step5 cur rs') h5 p0ClearWires c rs
  have h3 (c : Nat) (rs : List (Fin c)) : (step3 c rs).WellFormed := by
    rw [step3, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalFixed_wellFormed _ _ _ lit0Norm_valid _) (h4 _ _)
  have h2 (c : Nat) : (step2 c).WellFormed := by
    rw [step2, castFinish_wellFormed]
    exact MeasuredClear.measureThen_wellFormed (R := mLit0 + mLit2b + 43559) (fun cur rs' => step3 cur rs') h3 garb0 c List.nil
  rw [cornerFusedProg, castFinish_wellFormed]
  exact straight_append_wellFormed _ _ (f0.loadProg_wellFormed f0_geo _) (h2 _)

theorem cornerFused_support (start : Nat) :
    ChallengeMigration.straightWires (cornerFusedProg start) ⊆ WideBank8.Fast16.Tight.support := by
  have hcov := WideBank8.Fast16.Tight.old_cover
  have hroot : windowRoot ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.root_new
  have h855 : (855 : Wire) ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new ⟨0, by decide⟩
  have h856 : (856 : Wire) ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new ⟨1, by decide⟩
  have h857 : (857 : Wire) ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new ⟨2, by decide⟩
  have hs1 : WideBank8.Fast16.selBits1 ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selBits1_new
  have hp1 : WideBank8.Fast16.selPaths1 ⊆ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.selPaths1_new
  have hs3 : selBits3 ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    WideBank8.Fast16.Tight.bits_new (by
      simp only [selBits3, WideBank8.Fast16.windowBits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw ⊢
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega)
  have hp3 : selPaths3 ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    WideBank8.Fast16.Tight.bank_new (f1_geo.pathsSub w hw)
  have hlow : ∀ i : Fin 8, WideBank8.low8 i ∈ WideBank8.Fast16.Tight.support := WideBank8.Fast16.Tight.low8_new
  have hhot : ∀ i : Fin 256, hot8 i ∈ WideBank8.Fast16.Tight.support := fun i =>
    hcov (mem_newH7_of_band (by have := i.isLt; simp only [hot8, Site1Wire.Wide16.hot8]; dsimp only [Wire, ECDSAAdd.Wire]; omega))
  have hscr : scratch8 ∈ WideBank8.Fast16.Tight.support :=
    hcov (mem_newH7_of_band (by simp only [scratch8, Site1Wire.Wide16.scratch8]; dsimp only [Wire, ECDSAAdd.Wire]; omega))
  have htree : tree8.indexWires ⊆ WideBank8.Fast16.Tight.support := fun w hw => by
    have h1 : w ∈ WideBank8.Fast16.bank15.high := by
      have htr : tree8 = tableAddressTree WideBank8.Fast16.bank15.high 0 1 := by
        unfold tree8 Site1Wire.Wide16.tree8; rfl
      have := List.mem_dedup.mpr hw; rw [htr, WideBank8.Fast16.bank15_ok.index] at this; exact this
    exact WideBank8.Fast16.Tight.high_new h1
  have hhp : WideBank8.Fast16.bank15.hp ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    WideBank8.Fast16.Tight.bank_new (WideBank8.Fast16.bank15_ok.sub w hw)
  have hg0 : garb0 ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (mem_newH7_of_band (by rw [mem_garb0] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
  have hg1 : garb1 ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (mem_newH7_of_band (by rw [mem_garb1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
  have hg2 : garb2 ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (mem_newH7_of_band (by rw [mem_garb2] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
  have hp0c : p0ClearWires ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (mem_newH7_of_band (by simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
  have he1 : extra1Wires ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (mem_newH7_of_band (by simp only [extra1Wires, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
  have he2 : extra2Wires ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (mem_newH7_of_band (by simp only [extra2Wires, List.mem_range'_1] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
  have hfc : finalClearWires ⊆ WideBank8.Fast16.Tight.support := fun w hw =>
    hcov (mem_newH7_of_band (by
      simp only [finalClearWires, cxWord, List.mem_append, List.mem_singleton, List.mem_range'_1] at hw
      rcases hw with (h | h) | h
      · have := shortWires_bounds w h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
  have hreg0 : portTargets f0.ports ++ f0.g1 ⊆ WideBank8.Fast16.Tight.support := fun w hw => by
    rw [f0, p0_16_targets] at hw
    rcases List.mem_append.mp hw with h | h
    · exact hcov (mem_newH7_of_band (by have := mem_p0Wires h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
    · exact hg0 h
  have hreg1 : portTargets f1.ports ++ f1.garb ⊆ WideBank8.Fast16.Tight.support := fun w hw => by
    rw [f1, p1_16_targets] at hw; change w ∈ extra1Wires ++ garb1 at hw
    rcases List.mem_append.mp hw with h | h
    · exact he1 h
    · exact hg1 h
  have hreg2 : portTargets f2.ports ++ f2.g1 ⊆ WideBank8.Fast16.Tight.support := fun w hw => by
    rw [f2, p2_16_targets] at hw
    rcases List.mem_append.mp hw with h | h
    · exact hcov (mem_newH7_of_band (by have := mem_p2Wires h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega))
    · exact hg2 h
  have hl0 : ECDSAAdd.wires lit0Norm ⊆ WideBank8.Fast16.Tight.support.toFinset := fun w hw =>
    List.mem_toFinset.mpr (hcov (List.mem_toFinset.mp (lit0Norm_wires_newH7 hw)))
  have hl1 : ECDSAAdd.wires lit1Norm ⊆ WideBank8.Fast16.Tight.support.toFinset := fun w hw =>
    List.mem_toFinset.mpr (hcov (List.mem_toFinset.mp (lit1Norm_wires_newH7 hw)))
  have hl2a : ECDSAAdd.wires lit2aNorm ⊆ WideBank8.Fast16.Tight.support.toFinset := fun w hw =>
    List.mem_toFinset.mpr (hcov (List.mem_toFinset.mp (lit2aNorm_wires_newH7 hw)))
  have hl2b : ECDSAAdd.wires lit2bNorm ⊆ WideBank8.Fast16.Tight.support.toFinset := fun w hw =>
    List.mem_toFinset.mpr (hcov (List.mem_toFinset.mp (lit2bNorm_wires_newH7 hw)))
  have h14 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step14 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step14, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun _ _ => by
      rw [MeasuredClear.static_cast]
      exact MeasuredClear.fixupProgram_within8 _ _ _ _ _ _ _ _ _ hroot hscr hlow hhot htree hhp) _ _ _ hfc
  have h13 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step13 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step13, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ hl2b _, h14 _ _⟩
  have h12 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step12 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step12, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h13 cur rs') _ _ _ he2
  have h11 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step11 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step11, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ hl2a _, h12 _ _⟩
  have h10 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step10 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step10, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h11 cur rs') _ _ _ hg2
  have h9 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step9 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step9, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨f2.loadProg_support f2_geo _ hroot hroot h855 hs1 hp1 hreg2 _, h10 _ _⟩
  have h8 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step8 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step8, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h9 cur rs') _ _ _ he1
  have h7 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step7 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step7, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ hl1 _, h8 _ _⟩
  have h6 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step6 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step6, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h7 cur rs') _ _ _ hg1
  have h5 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step5 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step5, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨f1.loadProg_support f1_geo _ hroot hroot h855 h856 h857 hs3 hp3 hreg1 _, h6 _ _⟩
  have h4 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step4 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step4, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h5 cur rs') _ _ _ hp0c
  have h3 (c : Nat) (rs : List (Fin c)) : ChallengeMigration.straightWires (step3 c rs) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step3, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨literalFixed_support _ _ _ _ hl0 _, h4 _ _⟩
  have h2 (c : Nat) : ChallengeMigration.straightWires (step2 c) ⊆ WideBank8.Fast16.Tight.support := by
    rw [step2, support_cast, WEX.support_agrees]
    exact MeasuredClear.measureThen_within _ _ (fun cur rs' => by rw [← WEX.support_agrees]; exact h3 cur rs') _ _ _ hg0
  rw [cornerFusedProg, support_cast, straightWires_append]
  exact List.append_subset.mpr ⟨f0.loadProg_support f0_geo _ hroot hroot h855 hs1 hp1 hreg0 _, h2 _⟩

private theorem literalSlotSum_sublist_le {n} (c d : WCode n) (h : ∀ i ∈ c, i ∈ d) :
    ∀ p, WInstr.literal p ∈ c → ECDSAAdd.Challenge.gateSlots p ≤ literalSlotSum d := fun p hp =>
  literalSlotSum_le_of_mem d p (h _ hp)

private theorem literalSlotSum_append_eq {n} (a b : WCode n) :
    literalSlotSum (a ++ b) = literalSlotSum a + literalSlotSum b := by
  induction a with
  | nil => simp [literalSlotSum]
  | cons x a ih => cases x <;> simp [literalSlotSum, ih, Nat.add_assoc]

private theorem literalSlotSum_cons_look {n} (c : Option Wire) (ps : List (LookupPort n)) (xs : WCode n) :
    literalSlotSum (WInstr.lookup c ps :: xs) = literalSlotSum xs := rfl

private theorem literalSlotSum_cons_lit {n} (p : ECDSAAdd.Program) (xs : WCode n) :
    literalSlotSum (WInstr.literal p :: xs) = ECDSAAdd.Challenge.gateSlots p + literalSlotSum xs := rfl

private theorem literalSlotSum_nil_eq {n} : literalSlotSum ([] : WCode n) = 0 := rfl

private theorem literalSlotSum_2blocks {n} (c1 c2 : Option Wire) (p1 p2 : List (LookupPort n))
    (a b : ECDSAAdd.Program) :
    literalSlotSum ([WInstr.lookup c1 p1, WInstr.literal a, WInstr.lookup c2 p2] ++ ([WInstr.literal b] ++ [])) =
      ECDSAAdd.Challenge.gateSlots a + ECDSAAdd.Challenge.gateSlots b := by
  simp only [literalSlotSum_append_eq, literalSlotSum_cons_look, literalSlotSum_cons_lit,
    literalSlotSum_nil_eq, Nat.zero_add, Nat.add_zero]

private theorem literalSlotSum_3blocks {n} (c1 c2 c3 : Option Wire) (p1 p2 p3 : List (LookupPort n))
    (a b c : WCode n) :
    literalSlotSum (a ++ (([WInstr.lookup c1 p1] ++ b ++ [WInstr.lookup c2 p2]) ++ ((c ++ [WInstr.lookup c3 p3]) ++ []))) =
      literalSlotSum a + literalSlotSum b + literalSlotSum c := by
  simp only [literalSlotSum_append_eq, literalSlotSum_cons_look, literalSlotSum_nil_eq,
    Nat.zero_add, Nat.add_zero, Nat.add_assoc]

private theorem literalSlotSum_erase2_sublist {n} (xs ys : Code2 n) (h : xs.Sublist ys) :
    literalSlotSum (erase2 xs) ≤ literalSlotSum (erase2 ys) := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons _ _ ih => rw [erase2_cons, literalSlotSum_append_eq]; exact Nat.le_trans ih (Nat.le_add_left _ _)
  | cons₂ _ _ ih => rw [erase2_cons, erase2_cons, literalSlotSum_append_eq, literalSlotSum_append_eq]; exact Nat.add_le_add_left ih _

private theorem corner_slots_arith (ha0 hb0 g00 g0 g1 g2 op1 op2 op3 op4 op5 L : Nat)
    (ha : ha0 ≤ 2 ^ 15 * (2 * 529) + 10 * (2 ^ 15 - 1) + 12 * 529)
    (hb : hb0 ≤ 3 * g00 + (6500000 + (3 * g0 + (27000000 + (3 * g1 + (3 * g2 + 686900000))))))
    (hcs : g00 + g0 + g1 + g2 ≤ op1 + op2 + op3 + op4 + op5 + 20)
    (h5 : op1 + op2 + op3 + op4 + op5 ≤ L) (hL : L ≤ 50115160) :
    ha0 + hb0 ≤ 960000000 := by omega

theorem cornerFused_slots (start : Nat) :
    (cornerFusedProg start).gateSlots ≤ 960000000 := by
  have h14 (c : Nat) (rs : List (Fin c)) : (step14 c rs).gateSlots ≤ 686900000 := by
    rw [step14, castFinish_gateSlots, MeasuredClear.measureThen_slots _
      (fun k => 1024 * min allData.length k * 256 + 10 * 255 + 2291)
      (fun cur rs' => by
        rw [castFinish_gateSlots, MeasuredClear.fixupProgram_slots8 _ _ _ _ _ _ _ _ Site1Wire.Wide16.tree8_layout,
          Site1Wire.Wide16.tree8_leaves, Site1Wire.Wide16.tree8_nodes])]
    have hmin : min allData.length (rs.length + finalClearWires.length) ≤ 2620 := by
      rw [← allData_len]; exact Nat.min_le_left _ _
    exact (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right 256 (Nat.mul_le_mul_left 1024 hmin)) _) _).trans (by decide)
  have h13 (c : Nat) (rs : List (Fin c)) : (step13 c rs).gateSlots ≤ 3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000 := by
    rw [step13, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 65536) lit2bNorm
    have hns : ECDSAAdd.Challenge.gateSlots lit2bNorm = ECDSAAdd.Challenge.gateSlots lit2b := by
      rw [lit2bNorm, ECDSAAdd.Baselines.normalize_slots]
    rw [hns] at hl
    exact Nat.add_le_add hl (h14 (c + mLit2b) (rs.map (Fin.castLE (Nat.le_add_right _ _))))
  have h12 (c : Nat) (rs : List (Fin c)) : (step12 c rs).gateSlots ≤ 3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000 := by
    rw [step12, castFinish_gateSlots]; exact measureThen_slots_le (fun cur rs' => step13 cur rs') _ h13 extra2Wires c rs
  have h11 (c : Nat) (rs : List (Fin c)) :
      (step11 c rs).gateSlots ≤ 3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000) := by
    rw [step11, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 65536) lit2aNorm
    have hns : ECDSAAdd.Challenge.gateSlots lit2aNorm = ECDSAAdd.Challenge.gateSlots lit2a := by
      rw [lit2aNorm, ECDSAAdd.Baselines.normalize_slots]
    rw [hns] at hl
    exact Nat.add_le_add hl (h12 (c + 0) (rs.map (Fin.castLE (Nat.le_add_right _ _))))
  have h10 (c : Nat) (rs : List (Fin c)) :
      (step10 c rs).gateSlots ≤ 3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000) := by
    rw [step10, castFinish_gateSlots]; exact measureThen_slots_le (fun cur rs' => step11 cur rs') _ h11 garb2 c rs
  have h9 (c : Nat) (rs : List (Fin c)) :
      (step9 c rs).gateSlots ≤ 27000000 + (3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000)) := by
    rw [step9, castFinish_gateSlots, Straight.gateSlots_append]
    have hb := f2.loadProg_slots f2_geo c
    have hbl : f2.selBits.length = 15 := by decide
    have hpl : f2.ports.length = 401 := p2_16_len
    rw [hbl, hpl] at hb
    exact Nat.add_le_add (hb.trans (by decide))
      (h10 (c + codeRecords f2.selBits f2.selPaths windowRoot f2.selCode) (rs.map (Fin.castLE (Nat.le_add_right _ _))))
  have h8 (c : Nat) (rs : List (Fin c)) :
      (step8 c rs).gateSlots ≤ 27000000 + (3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000)) := by
    rw [step8, castFinish_gateSlots]; exact measureThen_slots_le (fun cur rs' => step9 cur rs') _ h9 extra1Wires c rs
  have h7 (c : Nat) (rs : List (Fin c)) :
      (step7 c rs).gateSlots ≤ 3 * ECDSAAdd.Challenge.gateSlots lit1 + (27000000 + (3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000))) := by
    rw [step7, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 65536) lit1Norm
    have hns : ECDSAAdd.Challenge.gateSlots lit1Norm = ECDSAAdd.Challenge.gateSlots lit1 := by
      rw [lit1Norm, ECDSAAdd.Baselines.normalize_slots]
    rw [hns] at hl
    exact Nat.add_le_add hl (h8 (c + 0) (rs.map (Fin.castLE (Nat.le_add_right _ _))))
  have h6 (c : Nat) (rs : List (Fin c)) :
      (step6 c rs).gateSlots ≤ 3 * ECDSAAdd.Challenge.gateSlots lit1 + (27000000 + (3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000))) := by
    rw [step6, castFinish_gateSlots]; exact measureThen_slots_le (fun cur rs' => step7 cur rs') _ h7 garb1 c rs
  have h5 (c : Nat) (rs : List (Fin c)) :
      (step5 c rs).gateSlots ≤ 6500000 + (3 * ECDSAAdd.Challenge.gateSlots lit1 + (27000000 + (3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000)))) := by
    rw [step5, castFinish_gateSlots, Straight.gateSlots_append]
    have hb := f1.loadProg_slots f1_geo c
    have hbl : f1.selBits.length = 13 := by decide
    have hpl : f1.ports.length = 95 := p1_16_len
    rw [hbl, hpl] at hb
    exact Nat.add_le_add (hb.trans (by decide))
      (h6 (c + codeRecords f1.selBits f1.selPaths windowRoot f1.selCode) (rs.map (Fin.castLE (Nat.le_add_right _ _))))
  have h4 (c : Nat) (rs : List (Fin c)) :
      (step4 c rs).gateSlots ≤ 6500000 + (3 * ECDSAAdd.Challenge.gateSlots lit1 + (27000000 + (3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000)))) := by
    rw [step4, castFinish_gateSlots]; exact measureThen_slots_le (fun cur rs' => step5 cur rs') _ h5 p0ClearWires c rs
  have h3 (c : Nat) (rs : List (Fin c)) :
      (step3 c rs).gateSlots ≤ 3 * ECDSAAdd.Challenge.gateSlots lit0 + (6500000 + (3 * ECDSAAdd.Challenge.gateSlots lit1 + (27000000 + (3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000))))) := by
    rw [step3, castFinish_gateSlots, Straight.gateSlots_append, literalFixed_slots]
    have hl := literal_slot_bound (n := 65536) lit0Norm
    have hns : ECDSAAdd.Challenge.gateSlots lit0Norm = ECDSAAdd.Challenge.gateSlots lit0 := by
      rw [lit0Norm, ECDSAAdd.Baselines.normalize_slots]
    rw [hns] at hl
    exact Nat.add_le_add hl (h4 (c + mLit0) (rs.map (Fin.castLE (Nat.le_add_right _ _))))
  have h2 (c : Nat) :
      (step2 c).gateSlots ≤ 3 * ECDSAAdd.Challenge.gateSlots lit0 + (6500000 + (3 * ECDSAAdd.Challenge.gateSlots lit1 + (27000000 + (3 * ECDSAAdd.Challenge.gateSlots lit2a + (3 * ECDSAAdd.Challenge.gateSlots lit2b + 686900000))))) := by
    rw [step2, castFinish_gateSlots]; exact measureThen_slots_le (fun cur rs' => step3 cur rs') _ h3 garb0 c List.nil
  have hrow_slot : literalSlotSum (erase2 WEXUnlookup.rowC) ≤ 50115160 :=
    WEXUnlookup.rowC_measures.2.2.1.trans
      ((Nat.add_le_add_right (Nat.add_le_add_right WEX.clearReferenceRow_literal_slots_bound 93082) 513).trans (by decide))
  have h5sum : ECDSAAdd.Challenge.gateSlots pair2Prog + ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Frontier.zrep streamLayout) +
      ECDSAAdd.Challenge.gateSlots cornerNegProg + ECDSAAdd.Challenge.gateSlots cornerA1Prog +
      ECDSAAdd.Challenge.gateSlots cornerA2Prog ≤ literalSlotSum (erase2 WEXUnlookup.rowC) := by
    have hrowC_eq : WEXUnlookup.rowC = WEXUnlookup.rowHead.map toBlock2 ++ WEXUnlookup.rowPost3 := by
      unfold WEXUnlookup.rowC; rfl
    have hrowH_eq : WEXUnlookup.rowHead = WEXUnlookup.rowPre3 ++ WEXUnlookup.generic3 probeRows := by
      unfold WEXUnlookup.rowHead; rfl
    rw [hrowC_eq, hrowH_eq, List.map_append, erase2_append, erase2_append,
      literalSlotSum_append_eq, literalSlotSum_append_eq]
    have hgen : ECDSAAdd.Challenge.gateSlots pair2Prog + ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Frontier.zrep streamLayout) ≤
        literalSlotSum (erase2 ((WEXUnlookup.generic3 probeRows).map toBlock2)) := by
      have hsub : ([toBlock2 (.masked (site2 probeRows)),
          toBlock2 (.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout)))] : Code2 32768).Sublist
          ((WEXUnlookup.generic3 probeRows).map toBlock2) := by
        rw [generic3_list]
        simp only [List.map_cons, List.map_nil]
        exact .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _
          (.cons₂ _ (.cons₂ _ .slnil))))))))))
      have hle := literalSlotSum_erase2_sublist _ _ hsub
      have heq : literalSlotSum (erase2 [toBlock2 (.masked (site2 probeRows)),
          toBlock2 (.plain (wLiteral (n := 32768) (ECDSAAdd.Frontier.zrep streamLayout)))]) =
          ECDSAAdd.Challenge.gateSlots pair2Prog + ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Frontier.zrep streamLayout) := by
        have h1 : (toBlock2 (.masked (site2 probeRows))).code =
            [.lookup (some windowRoot) (site2Ports probeRows), .literal pair2Prog,
             .lookup (some windowRoot) (site2Ports probeRows)] := by
          simp only [toBlock2, Block2.code, UnitSite.code, site2, MaskedSite.prefix, wLiteral,
            List.cons_append, List.nil_append]
        have h2 : (toBlock2 (.plain (wLiteral (n := 32768) (ECDSAAdd.Frontier.zrep streamLayout)))).code =
            [.literal (ECDSAAdd.Frontier.zrep streamLayout)] := rfl
        rw [erase2_cons, erase2_cons, erase2_nil, h1, h2]
        exact literalSlotSum_2blocks _ _ _ _ pair2Prog (ECDSAAdd.Frontier.zrep streamLayout)
      exact heq ▸ hle
    have hpost : ECDSAAdd.Challenge.gateSlots cornerNegProg + ECDSAAdd.Challenge.gateSlots cornerA1Prog +
        ECDSAAdd.Challenge.gateSlots cornerA2Prog ≤ literalSlotSum (erase2 WEXUnlookup.rowPost3) := by
      rw [cornerNegProg_eq_litProg, (litOnly_metrics WEX.cornerNeg cornerNeg_litOnly).2.2.2,
        cornerA1Prog_eq_litProg, (litOnly_metrics WEX.cornerA1 cornerA1_litOnly).2.2.2,
        cornerA2Prog_eq_litProg, (litOnly_metrics WEX.cornerA2 cornerA2_litOnly).2.2.2]
      have hsub : ([Block2.plain WEX.cornerNeg, .unit WEXUnlookup.cornerUnit₁,
          .unit WEXUnlookup.cornerUnit₂] : Code2 32768).Sublist WEXUnlookup.rowPost3 := by
        rw [WEXUnlookup.rowPost3]
        exact .cons₂ _ (.cons₂ _ (.cons₂ _ (.cons _ (.cons _ .slnil))))
      have hle := literalSlotSum_erase2_sublist _ _ hsub
      have h0 : (Block2.plain WEX.cornerNeg).code = WEX.cornerNeg := rfl
      have h1 : (Block2.unit WEXUnlookup.cornerUnit₁).code =
          [.lookup (some windowRoot) (cornerPorts probeRows)] ++ WEX.cornerA1 ++ [.lookup (some windowRoot) (yPorts probeRows)] := rfl
      have h2 : (Block2.unit WEXUnlookup.cornerUnit₂).code =
          WEX.cornerA2 ++ [.lookup (some windowRoot) (scrDPorts probeRows)] := rfl
      have heq : literalSlotSum (erase2 [Block2.plain WEX.cornerNeg, .unit WEXUnlookup.cornerUnit₁,
          .unit WEXUnlookup.cornerUnit₂]) =
          literalSlotSum WEX.cornerNeg + literalSlotSum WEX.cornerA1 + literalSlotSum WEX.cornerA2 := by
        rw [erase2_cons, erase2_cons, erase2_cons, erase2_nil, h0, h1, h2]
        exact literalSlotSum_3blocks _ _ _ _ _ _ WEX.cornerNeg WEX.cornerA1 WEX.cornerA2
      exact heq ▸ hle
    have h5a : ∀ a b c d e x y z : Nat, a + b ≤ y → c + d + e ≤ z → a + b + c + d + e ≤ x + y + z := by omega
    exact h5a _ _ _ _ _ _ _ _ hgen hpost
  rw [cornerFusedProg, castFinish_gateSlots, Straight.gateSlots_append]
  have ha := f0.loadProg_slots f0_geo start
  have hbl : f0.selBits.length = 15 := by decide
  have hpl : f0.ports.length = 529 := p0_16_len
  rw [hbl, hpl] at ha
  exact corner_slots_arith _ _ _ _ _ _ _ _ _ _ _ _ ha
    (h2 (start + codeRecords f0.selBits f0.selPaths windowRoot f0.selCode))
    CornerFast.corner_slots_le h5sum hrow_slot

/-! ### Part 4: Exact simulation of `cornerFusedSrc` (`cornerFused_sim`) -/

attribute [local irreducible] registerXPhase registerXResetMagnitude clearRegister

private def read32C (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (a : Nat) : ConstantBit 32768 → Bool :=
  readConstant (fun _ : Fin 32768 => coeffs (r16 a)) Q
private def simL0 (read : ConstantBit 65536 → Bool) (a : Nat) (st : ECDSAAdd.State) : ECDSAAdd.State :=
  ⟨st.phase, tableXorState (portMask read p0_16 a) true st.basis⟩
private def simC (s2a : ECDSAAdd.State) : ECDSAAdd.State :=
  ⟨s2a.phase, clearRegister extra2Wires s2a.basis⟩
private def sim2b (m2b : List Bool) (sC : ECDSAAdd.State) : ECDSAAdd.State :=
  ECDSAAdd.run lit2b m2b sC
private def simT (m2b : List Bool) (sC : ECDSAAdd.State) : BasisState :=
  clearRegister finalClearWires (sim2b m2b sC).basis
private def sim2a (sL2 : ECDSAAdd.State) : ECDSAAdd.State :=
  ECDSAAdd.run lit2a List.nil sL2
private def simL2 (read : ConstantBit 65536 → Bool) (a : Nat) (sB : ECDSAAdd.State) : ECDSAAdd.State :=
  ⟨sB.phase, tableXorState (portMask read p2_16 a) true sB.basis⟩
private def simB (s1 : ECDSAAdd.State) : ECDSAAdd.State :=
  ⟨s1.phase, clearRegister extra1Wires s1.basis⟩
private def sim1 (sL1 : ECDSAAdd.State) : ECDSAAdd.State :=
  ECDSAAdd.run lit1 List.nil sL1
private def simL1 (read : ConstantBit 65536 → Bool) (a : Nat) (sA : ECDSAAdd.State) : ECDSAAdd.State :=
  ⟨sA.phase, tableXorState (portMask read p1_16 a) true sA.basis⟩
private def simA (s0 : ECDSAAdd.State) : ECDSAAdd.State :=
  ⟨s0.phase, clearRegister p0ClearWires s0.basis⟩

private theorem lift_fused
    (P0 P1 P2a P2b Porig : ECDSAAdd.Program)
    (mask0 mask1 mask2 mask0' mask1' mask2' : List Wire)
    (read32 : ConstantBit 32768 → Bool) (a : Nat) (st : ECDSAAdd.State) (m0 m2b mPerm : List Bool)
    (fL0 fA fL1 f1 fB fL2 f2a fC f2b : ECDSAAdd.State → ECDSAAdd.State)
    (fT : ECDSAAdd.State → BasisState)
    (h0 : mask0 = mask0') (h1 : mask1 = mask1') (h2 : mask2 = mask2')
    (hfL0 : fL0 st = ⟨st.phase, tableXorState mask0 true st.basis⟩)
    (hfA : ∀ s, fA s = ⟨s.phase, clearRegister p0ClearWires s.basis⟩)
    (hfL1 : ∀ s, fL1 s = ⟨s.phase, tableXorState mask1 true s.basis⟩)
    (hf1 : ∀ s, f1 s = ECDSAAdd.run P1 List.nil s)
    (hfB : ∀ s, fB s = ⟨s.phase, clearRegister extra1Wires s.basis⟩)
    (hfL2 : ∀ s, fL2 s = ⟨s.phase, tableXorState mask2 true s.basis⟩)
    (hf2a : ∀ s, f2a s = ECDSAAdd.run P2a List.nil s)
    (hfC : ∀ s, fC s = ⟨s.phase, clearRegister extra2Wires s.basis⟩)
    (hf2b : ∀ s, f2b s = ECDSAAdd.run P2b m2b s)
    (hfT : ∀ s, fT s = clearRegister finalClearWires (f2b s).basis)
    (h : let sL0 : ECDSAAdd.State := ⟨st.phase, tableXorState mask0' true st.basis⟩
         let s0 := ECDSAAdd.run P0 m0 sL0
         let sA : ECDSAAdd.State := ⟨s0.phase, clearRegister p0ClearWires s0.basis⟩
         let sL1 : ECDSAAdd.State := ⟨sA.phase, tableXorState mask1' true sA.basis⟩
         let s1 := ECDSAAdd.run P1 List.nil sL1
         let sB : ECDSAAdd.State := ⟨s1.phase, clearRegister extra1Wires s1.basis⟩
         let sL2 : ECDSAAdd.State := ⟨sB.phase, tableXorState mask2' true sB.basis⟩
         let s2a := ECDSAAdd.run P2a List.nil sL2
         let sC : ECDSAAdd.State := ⟨s2a.phase, clearRegister extra2Wires s2a.basis⟩
         let s2b := ECDSAAdd.run P2b m2b sC
         let sOut : ECDSAAdd.State := ⟨s2b.phase, clearRegister finalClearWires s2b.basis⟩
         (∀ q ∈ p0ClearPorts probeRows, s0.basis q.target = decide (read32 (q.ref a) = q.value)) ∧
         (∀ w ∈ streamLayout.dialogPool, w ∉ keepWires → sA.basis w = false) ∧
         (∀ q ∈ p1Ports probeRows, s1.basis q.target = decide (read32 (q.ref a) = q.value)) ∧
         (∀ w ∈ streamLayout.dialogPool, w ∉ keepWires → sB.basis w = false) ∧
         (∀ q ∈ extra2Ports probeRows, s2a.basis q.target = decide (read32 (q.ref a) = q.value)) ∧
         (∀ q ∈ finalClearPorts probeRows, s2b.basis q.target = decide (read32 (q.ref a) = q.value)) ∧
         s2b.basis 14373 = false ∧
         sOut = ECDSAAdd.run Porig mPerm st) :
    (∀ q ∈ p0ClearPorts probeRows, (ECDSAAdd.run P0 m0 (fL0 st)).basis q.target = decide (read32 (q.ref a) = q.value)) ∧
    (∀ w ∈ streamLayout.dialogPool, w ∉ keepWires → (fA (ECDSAAdd.run P0 m0 (fL0 st))).basis w = false) ∧
    (∀ q ∈ p1Ports probeRows, (f1 (fL1 (fA (ECDSAAdd.run P0 m0 (fL0 st))))).basis q.target = decide (read32 (q.ref a) = q.value)) ∧
    (∀ w ∈ streamLayout.dialogPool, w ∉ keepWires → (fB (f1 (fL1 (fA (ECDSAAdd.run P0 m0 (fL0 st)))))).basis w = false) ∧
    (∀ q ∈ extra2Ports probeRows, (f2a (fL2 (fB (f1 (fL1 (fA (ECDSAAdd.run P0 m0 (fL0 st)))))))).basis q.target = decide (read32 (q.ref a) = q.value)) ∧
    (∀ q ∈ finalClearPorts probeRows, (f2b (fC (f2a (fL2 (fB (f1 (fL1 (fA (ECDSAAdd.run P0 m0 (fL0 st)))))))))).basis q.target = decide (read32 (q.ref a) = q.value)) ∧
    (⟨(f2b (fC (f2a (fL2 (fB (f1 (fL1 (fA (ECDSAAdd.run P0 m0 (fL0 st)))))))))).phase,
      fT (fC (f2a (fL2 (fB (f1 (fL1 (fA (ECDSAAdd.run P0 m0 (fL0 st)))))))))⟩ : ECDSAAdd.State) =
      ECDSAAdd.run Porig mPerm st := by
  subst h0; subst h1; subst h2
  simp only [hfT, hf2b, hfC, hf2a, hfL2, hfB, hf1, hfL1, hfA, hfL0]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

attribute [local irreducible] read32C simL0 simC sim2b simT sim2a simL2 simB sim1 simL1 simA

set_option maxHeartbeats 800000 in
theorem cornerFused_sim (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) :
    let read := readConstant coeffs Q
    ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = mLit0 + mLit2b ∧
        ∀ a (st : ECDSAAdd.State) {cx cy : ECDSAAdd.Fp} (hc : ECDSAAdd.Secp256k1.curve.toAffine.Nonsingular cx cy),
          RowReads (read32C coeffs Q a) (probeRows a) (.some hc) →
          ∀ (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState),
          PointDialogValues streamLayout X Y G base st.basis →
          base windowRoot = true →
          base streamLayout.control = true →
          (G = true → base streamLayout.infinitySelect = false ∧
            base streamLayout.doubleSelect = false ∧
            base streamLayout.genericSelect = false ∧
            base streamLayout.core.equalNegY = false) →
          AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          Clean WideBank8.Fast16.pathBank st.basis →
          AddrValid WideBank8.Fast16.windowBits windowRoot a (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st) →
          Clean WideBank8.Fast16.pathBank (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st).basis →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st))
      (cornerFusedSrc read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  intro read
  have hsplit : ∀ s : BasisState, 256 * tree8.routeLabel s + MeasuredClear.hotAddress8 WideBank8.low8 s =
      tableAddressValue WideBank8.Fast16.windowBits s := fun s => by
    have htr : tree8 = tableAddressTree WideBank8.Fast16.bank15.high 0 1 := by
      unfold tree8 Site1Wire.Wide16.tree8; rfl
    rw [htr]; exact WideBank8.Fast16.bank15_ok.split s
  have h14_sim (o1 o2 o3 o4 o5 o6 : List Bool)
      (ho1 : o1.length = 529) (ho2 : o2.length = 272) (ho3 : o3.length = 665)
      (ho4 : o4.length = 95) (ho5 : o5.length = 401) (ho6 : o6.length = 143) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∀ a (next : ECDSAAdd.State) (u1 u2 u3 u4 u5 u6 : BasisState),
          let t := clearRegister finalClearWires next.basis
          tableAddressValue WideBank8.Fast16.windowBits t = a →
          t windowRoot = true →
          Clean WideBank8.Fast16.bank15.hp t →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d5, u5 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d6, u6 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d7, next.basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet next) =
            (c * (((((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
              registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4) *
              registerXPhase garb2 o5 u5) * registerXPhase extra2Wires o6 u6)) •
              Bridge.signedKet ⟨next.phase, t⟩)
        (step14Src read (o1 ++ o2 ++ o3 ++ o4 ++ o5 ++ o6)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step14Src
    apply MeasuredClear.measureResetThen_sim finalClearWires _
      (fun o7 => BranchCoherentOn (MeasuredClear.basisIdeal id
        (MeasuredClear.fixupFactor8 allData ((o1 ++ o2 ++ o3 ++ o4 ++ o5 ++ o6) ++ o7) read WideBank8.low8 hot8 tree8 windowRoot))
        (fun s => MeasuredClear.HotClean8 hot8 s ∧ Clean WideBank8.Fast16.bank15.hp s))
    · intro o7 _
      exact MeasuredClear.fixupSource_coherent8 allData _ read WideBank8.low8 hot8 tree8 windowRoot scratch8
        WideBank8.Fast16.bank15.hp Site1Wire.Wide16.tree8_layout Site1Wire.Wide16.hot8_inj Site1Wire.Wide16.low8_ne_hot8
        Site1Wire.Wide16.hot8_disj Site1Wire.Wide16.scratch8_not_tree Site1Wire.Wide16.scratch8_not_hot
    · intro o7 ho7 b c hb a next u1 u2 u3 u4 u5 u6 t haddr_t hroot_t hhp_t hu1 hu2 hu3 hu4 hu5 hu6 hu7
      have hk := xResetRegisterKraus_ket finalClearWires o7 next.basis ho7 finalClearWires_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho7] at hk
      have hhot : MeasuredClear.HotClean8 hot8 t := fun i => clearRegister_clean _ _ _ (hot8_in_finalClear i)
      have hvalid : MeasuredClear.HotClean8 hot8 t ∧ Clean WideBank8.Fast16.bank15.hp t := ⟨hhot, hhp_t⟩
      have hfac : MeasuredClear.fixupFactor8 allData ((o1 ++ o2 ++ o3 ++ o4 ++ o5 ++ o6) ++ o7) read WideBank8.low8 hot8 tree8 windowRoot t =
          ((((((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
            registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4) *
            registerXPhase garb2 o5 u5) * registerXPhase extra2Wires o6 u6) *
            registerXPhase finalClearWires o7 next.basis) := by
        rw [allData,
          MeasuredClear.fixupFactor8_append _ _ _ _ (by simp [ho1, ho2, ho3, ho4, ho5, ho6, d1_len, d2_len, d3_len, d4_len, d5_len, d6_len]),
          MeasuredClear.fixupFactor8_append _ _ _ _ (by simp [ho1, ho2, ho3, ho4, ho5, d1_len, d2_len, d3_len, d4_len, d5_len]),
          MeasuredClear.fixupFactor8_append _ _ _ _ (by simp [ho1, ho2, ho3, ho4, d1_len, d2_len, d3_len, d4_len]),
          MeasuredClear.fixupFactor8_append _ _ _ _ (by simp [ho1, ho2, ho3, d1_len, d2_len, d3_len]),
          MeasuredClear.fixupFactor8_append _ _ _ _ (by simp [ho1, ho2, d1_len, d2_len]),
          MeasuredClear.fixupFactor8_append _ _ _ _ (by rw [ho1, d1_len])]
        have hf (dk : List (MeasuredClear.ClearPort 65536)) (ws : List Wire) (ok : List Bool) (uk : BasisState)
            (htg : dk.map MeasuredClear.ClearPort.target = ws)
            (huk : ∀ q ∈ dk, uk q.target = decide (read (q.ref a) = q.value)) :
            MeasuredClear.fixupFactor8 dk ok read WideBank8.low8 hot8 tree8 windowRoot t = registerXPhase ws ok uk := by
          rw [← htg]
          exact MeasuredClear.fixupFactor8_loaded dk ok read WideBank8.low8 hot8 tree8 windowRoot WideBank8.Fast16.bank15.hp
            Site1Wire.Wide16.hot8_inj Site1Wire.Wide16.low8_ne_hot8 Site1Wire.Wide16.hot8_disj t uk hhot
            (fun q hq => by rw [hsplit, haddr_t, hroot_t]; simpa using huk q hq)
        rw [hf d1 garb0 o1 u1 d1_targets hu1, hf d2 p0ClearWires o2 u2 d2_targets hu2,
          hf d3 garb1 o3 u3 d3_targets hu3, hf d4 extra1Wires o4 u4 d4_targets hu4,
          hf d5 garb2 o5 u5 d5_targets hu5, hf d6 extra2Wires o6 u6 d6_targets hu6,
          hf d7 finalClearWires o7 next.basis d7_targets hu7]
      have hsq := MeasuredClear.registerXPhase_square finalClearWires o7 next.basis
      have ht : clearRegister finalClearWires next.basis = t := rfl
      change b.kraus (xResetRegisterKraus finalClearWires o7 (Bridge.signedKet next)) = _
      simp only [Bridge.signedKet, map_smul, hk, ht, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac, smul_smul]
      exact congrArg (· • ket t) (phase_cancel_last next.phase (registerXResetMagnitude finalClearWires.length) c _ _ hsq)
  -- Step 13: literal `lit2bNorm`
  have h13_sim (o1 o2 o3 o4 o5 o6 : List Bool)
      (ho1 : o1.length = 529) (ho2 : o2.length = 272) (ho3 : o3.length = 665)
      (ho4 : o4.length = 95) (ho5 : o5.length = 401) (ho6 : o6.length = 143) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (sC : ECDSAAdd.State) (u1 u2 u3 u4 u5 u6 : BasisState),
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b sC) = a →
            (simT m2b sC) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b sC) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d5, u5 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, u6 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b sC).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sC) =
              (c * (((((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
                registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4) *
                registerXPhase garb2 o5 u5) * registerXPhase extra2Wires o6 u6)) •
                Bridge.signedKet ⟨(sim2b m2b sC).phase, simT m2b sC⟩)
        (step13Src read (o1 ++ o2 ++ o3 ++ o4 ++ o5 ++ o6)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation lit2bNorm
    obtain ⟨c2, a2, m2⟩ := h14_sim o1 o2 o3 o4 o5 o6 ho1 ho2 ho3 ho4 ho5 ho6
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step13Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    refine ⟨b₁.history, by rw [hb₁.1, lit2bNorm_meas], ?_⟩
    intro a sC u1 u2 u3 u4 u5 u6 haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hnorm : ECDSAAdd.run lit2bNorm b₁.history sC = sim2b b₁.history sC := by
      rw [lit2bNorm, sim2b]; exact ECDSAAdd.Baselines.normalize_run lit2b b₁.history sC
    have hT : simT b₁.history sC = clearRegister finalClearWires (sim2b b₁.history sC).basis := by
      unfold simT; rfl
    rw [hT] at haddr hroot hhp ⊢
    change b₂.kraus (b₁.kraus (Bridge.signedKet sC)) = _
    rw [hb₁.2, hnorm, map_smul, hb₂ a (sim2b b₁.history sC) u1 u2 u3 u4 u5 u6 haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7, smul_smul]
    exact congrArg (· • _) (by ring)
  -- Step 12: measureReset `extra2Wires` (`o6`)
  have h12_sim (o1 o2 o3 o4 o5 : List Bool)
      (ho1 : o1.length = 529) (ho2 : o2.length = 272) (ho3 : o3.length = 665)
      (ho4 : o4.length = 95) (ho5 : o5.length = 401) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (s2a : ECDSAAdd.State) (u1 u2 u3 u4 u5 : BasisState),
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC s2a)) = a →
            (simT m2b (simC s2a)) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC s2a)) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d5, u5 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, s2a.basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC s2a)).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet s2a) =
              (c * ((((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
                registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4) *
                registerXPhase garb2 o5 u5)) •
                Bridge.signedKet ⟨(sim2b m2b (simC s2a)).phase, simT m2b (simC s2a)⟩)
        (step12Src read (o1 ++ o2 ++ o3 ++ o4 ++ o5)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step12Src
    apply MeasuredClear.measureResetThen_sim extra2Wires _
      (fun o6 b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
        ∀ a (sC : ECDSAAdd.State) (u1 u2 u3 u4 u5 u6 : BasisState),
          tableAddressValue WideBank8.Fast16.windowBits (simT m2b sC) = a →
          (simT m2b sC) windowRoot = true →
          Clean WideBank8.Fast16.bank15.hp (simT m2b sC) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d5, u5 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d6, u6 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d7, (sim2b m2b sC).basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sC) =
            (c * (((((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
              registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4) *
              registerXPhase garb2 o5 u5) * registerXPhase extra2Wires o6 u6)) •
              Bridge.signedKet ⟨(sim2b m2b sC).phase, simT m2b sC⟩)
    · intro o6 ho6; exact h13_sim o1 o2 o3 o4 o5 o6 ho1 ho2 ho3 ho4 ho5 (by rw [extra2Wires_len] at ho6; exact ho6)
    · intro o6 ho6 b c hb; obtain ⟨m2b, hm2b, hb⟩ := hb; refine ⟨m2b, hm2b, ?_⟩
      intro a s2a u1 u2 u3 u4 u5 haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7
      have hk := xResetRegisterKraus_ket extra2Wires o6 s2a.basis ho6 extra2Wires_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho6] at hk
      have hsq := MeasuredClear.registerXPhase_square extra2Wires o6 s2a.basis
      change b.kraus (xResetRegisterKraus extra2Wires o6 (Bridge.signedKet s2a)) = _
      have he : b.kraus (ket (clearRegister extra2Wires s2a.basis)) =
          (if s2a.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet (simC s2a)) := by
        rw [simC]; simp only [Bridge.signedKet, map_smul, smul_smul]; cases s2a.phase <;> simp
      have hstep := hb a (simC s2a) u1 u2 u3 u4 u5 s2a.basis haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7
      rw [show Bridge.signedKet s2a = (if s2a.phase then (-1 : ℂ) else 1) • ket s2a.basis from rfl,
        map_smul, map_smul, hk, map_smul, he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_mid s2a.phase (registerXResetMagnitude extra2Wires.length) c _ _ hsq)
  -- Step 11: literal `lit2aNorm` (0 measurements)
  have h11_sim (o1 o2 o3 o4 o5 : List Bool)
      (ho1 : o1.length = 529) (ho2 : o2.length = 272) (ho3 : o3.length = 665)
      (ho4 : o4.length = 95) (ho5 : o5.length = 401) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (sL2 : ECDSAAdd.State) (u1 u2 u3 u4 u5 : BasisState),
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a sL2))) = a →
            (simT m2b (simC (sim2a sL2))) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a sL2))) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d5, u5 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, (sim2a sL2).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC (sim2a sL2))).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sL2) =
              (c * ((((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
                registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4) *
                registerXPhase garb2 o5 u5)) •
                Bridge.signedKet ⟨(sim2b m2b (simC (sim2a sL2))).phase, simT m2b (simC (sim2a sL2))⟩)
        (step11Src read (o1 ++ o2 ++ o3 ++ o4 ++ o5)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation lit2aNorm
    obtain ⟨c2, a2, m2⟩ := h12_sim o1 o2 o3 o4 o5 ho1 ho2 ho3 ho4 ho5
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step11Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨m2b, hm2b, hb₂⟩ := hb₂
    have hh0 : b₁.history = List.nil := List.eq_nil_of_length_eq_zero (by rw [hb₁.1, lit2aNorm_meas])
    refine ⟨m2b, hm2b, ?_⟩
    intro a sL2 u1 u2 u3 u4 u5 haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hnorm : ECDSAAdd.run lit2aNorm b₁.history sL2 = sim2a sL2 := by
      rw [hh0, lit2aNorm, sim2a]; exact ECDSAAdd.Baselines.normalize_run lit2a List.nil sL2
    have hstep := hb₂ a (sim2a sL2) u1 u2 u3 u4 u5 haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7
    change b₂.kraus (b₁.kraus (Bridge.signedKet sL2)) = _
    rw [hb₁.2, hnorm, map_smul, hstep, smul_smul]
    exact congrArg (· • _) (by ring)
  -- Step 10: measureReset `garb2` (`o5`)
  have h10_sim (o1 o2 o3 o4 : List Bool)
      (ho1 : o1.length = 529) (ho2 : o2.length = 272) (ho3 : o3.length = 665) (ho4 : o4.length = 95) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (s2_0 sL2 : ECDSAAdd.State) (u1 u2 u3 u4 : BasisState),
            (⟨s2_0.phase, clearRegister garb2 s2_0.basis⟩ : ECDSAAdd.State) = sL2 →
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a sL2))) = a →
            (simT m2b (simC (sim2a sL2))) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a sL2))) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d5, s2_0.basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, (sim2a sL2).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC (sim2a sL2))).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet s2_0) =
              (c * (((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
                registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4)) •
                Bridge.signedKet ⟨(sim2b m2b (simC (sim2a sL2))).phase, simT m2b (simC (sim2a sL2))⟩)
        (step10Src read (o1 ++ o2 ++ o3 ++ o4)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step10Src
    apply MeasuredClear.measureResetThen_sim garb2 _
      (fun o5 b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
        ∀ a (sL2 : ECDSAAdd.State) (u1 u2 u3 u4 u5 : BasisState),
          tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a sL2))) = a →
          (simT m2b (simC (sim2a sL2))) windowRoot = true →
          Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a sL2))) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d5, u5 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d6, (sim2a sL2).basis q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d7, (sim2b m2b (simC (sim2a sL2))).basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sL2) =
            (c * ((((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
              registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4) *
              registerXPhase garb2 o5 u5)) •
              Bridge.signedKet ⟨(sim2b m2b (simC (sim2a sL2))).phase, simT m2b (simC (sim2a sL2))⟩)
    · intro o5 ho5; exact h11_sim o1 o2 o3 o4 o5 ho1 ho2 ho3 ho4 (by rw [garb2_len] at ho5; exact ho5)
    · intro o5 ho5 b c hb; obtain ⟨m2b, hm2b, hb⟩ := hb; refine ⟨m2b, hm2b, ?_⟩
      intro a s2_0 sL2 u1 u2 u3 u4 hsL2 haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7
      have hk := xResetRegisterKraus_ket garb2 o5 s2_0.basis ho5 garb2_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho5] at hk
      have hsq := MeasuredClear.registerXPhase_square garb2 o5 s2_0.basis
      have ⟨hph, hba⟩ := (ECDSAAdd.State.mk.injEq _ _ _ _).mp hsL2
      change b.kraus (xResetRegisterKraus garb2 o5 (Bridge.signedKet s2_0)) = _
      have he : b.kraus (ket (clearRegister garb2 s2_0.basis)) =
          (if s2_0.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet sL2) := by
        rw [hba, hph]; simp only [Bridge.signedKet, map_smul, smul_smul]; cases sL2.phase <;> simp
      have hstep := hb a sL2 u1 u2 u3 u4 s2_0.basis haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7
      rw [show Bridge.signedKet s2_0 = (if s2_0.phase then (-1 : ℂ) else 1) • ket s2_0.basis from rfl,
        map_smul, map_smul, hk, map_smul, he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_mid s2_0.phase (registerXResetMagnitude garb2.length) c _ _ hsq)
  -- Step 9: `f2.loadSource`
  have h9_sim (o1 o2 o3 o4 : List Bool)
      (ho1 : o1.length = 529) (ho2 : o2.length = 272) (ho3 : o3.length = 665) (ho4 : o4.length = 95) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (sB : ECDSAAdd.State) (u1 u2 u3 u4 : BasisState),
            AddrValid WideBank8.Fast16.windowBits windowRoot a sB →
            Clean WideBank8.Fast16.pathBank sB.basis →
            Clean (scrShortWires ++ extra2Wires ++ garb2) sB.basis →
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a sB)))) = a →
            (simT m2b (simC (sim2a (simL2 read a sB)))) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a sB)))) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, (sim2a (simL2 read a sB)).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a sB)))).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sB) =
              (c * (((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
                registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4)) •
                Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a sB)))).phase, simT m2b (simC (sim2a (simL2 read a sB)))⟩)
        (step9Src read (o1 ++ o2 ++ o3 ++ o4)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := f2.load_sim read f2_geo
    obtain ⟨c2, a2, m2⟩ := h10_sim o1 o2 o3 o4 ho1 ho2 ho3 ho4
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step9Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨m2b, hm2b, hb₂⟩ := hb₂
    refine ⟨m2b, hm2b, ?_⟩
    intro a sB u1 u2 u3 u4 ha hpath hcl haddr hroot hhp hu1 hu2 hu3 hu4 hu6 hu7
    have hcl' : Clean (portTargets f2.ports ++ f2.g1) sB.basis := by
      change Clean (portTargets p2_16 ++ garb2) sB.basis; rw [p2_16_targets]; exact hcl
    have hst := f2.load_state read f2_geo a sB ⟨hpath, ha.1, ha.2⟩ hcl'
    set s2_0 := ECDSAAdd.run f2.swapNet List.nil
      (ECDSAAdd.run ((specialize f2.selCode (tableAddressValue f2.selBits sB.basis)).instantiate read) List.nil sB)
    have hsL2 : (⟨s2_0.phase, clearRegister garb2 s2_0.basis⟩ : ECDSAAdd.State) = simL2 read a sB := by
      rw [simL2]
      refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
      have h2 := hst.2.2.2; change clearRegister garb2 s2_0.basis = tableXorState (portMask read p2_16 a) (sB.basis windowRoot) sB.basis at h2
      rw [ha.2] at h2; exact h2
    have hu5 : ∀ q ∈ d5, s2_0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
      have h1 := hst.2.2.1 q hq
      change s2_0.basis q.target = (sB.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
      rw [ha.2, Bool.true_and] at h1; exact h1
    have hstep := hb₂ a s2_0 (simL2 read a sB) u1 u2 u3 u4 hsL2 haddr hroot hhp hu1 hu2 hu3 hu4 hu5 hu6 hu7
    change b₂.kraus (b₁.kraus (Bridge.signedKet sB)) = _
    rw [hb₁ a sB ⟨hpath, ha.1, ha.2⟩ hcl', map_smul, hstep, smul_smul]
    exact congrArg (· • _) (by ring)
  -- Step 8: measureReset `extra1Wires` (`o4`)
  have h8_sim (o1 o2 o3 : List Bool) (ho1 : o1.length = 529) (ho2 : o2.length = 272) (ho3 : o3.length = 665) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (s1 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
            AddrValid WideBank8.Fast16.windowBits windowRoot a (simB s1) →
            Clean WideBank8.Fast16.pathBank (simB s1).basis →
            Clean (scrShortWires ++ extra2Wires ++ garb2) (simB s1).basis →
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a (simB s1))))) = a →
            (simT m2b (simC (sim2a (simL2 read a (simB s1))))) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a (simB s1))))) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, s1.basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, (sim2a (simL2 read a (simB s1))).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a (simB s1))))).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet s1) =
              (c * ((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
                registerXPhase garb1 o3 u3)) •
                Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a (simB s1))))).phase, simT m2b (simC (sim2a (simL2 read a (simB s1))))⟩)
        (step8Src read (o1 ++ o2 ++ o3)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step8Src
    apply MeasuredClear.measureResetThen_sim extra1Wires _
      (fun o4 b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
        ∀ a (sB : ECDSAAdd.State) (u1 u2 u3 u4 : BasisState),
          AddrValid WideBank8.Fast16.windowBits windowRoot a sB →
          Clean WideBank8.Fast16.pathBank sB.basis →
          Clean (scrShortWires ++ extra2Wires ++ garb2) sB.basis →
          tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a sB)))) = a →
          (simT m2b (simC (sim2a (simL2 read a sB)))) windowRoot = true →
          Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a sB)))) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, u4 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d6, (sim2a (simL2 read a sB)).basis q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a sB)))).basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sB) =
            (c * (((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
              registerXPhase garb1 o3 u3) * registerXPhase extra1Wires o4 u4)) •
              Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a sB)))).phase, simT m2b (simC (sim2a (simL2 read a sB)))⟩)
    · intro o4 ho4; exact h9_sim o1 o2 o3 o4 ho1 ho2 ho3 (by rw [extra1Wires_len] at ho4; exact ho4)
    · intro o4 ho4 b c hb; obtain ⟨m2b, hm2b, hb⟩ := hb; refine ⟨m2b, hm2b, ?_⟩
      intro a s1 u1 u2 u3 haB hpathB hclB haddr hroot hhp hu1 hu2 hu3 hu4 hu6 hu7
      have hk := xResetRegisterKraus_ket extra1Wires o4 s1.basis ho4 extra1Wires_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho4] at hk
      have hsq := MeasuredClear.registerXPhase_square extra1Wires o4 s1.basis
      change b.kraus (xResetRegisterKraus extra1Wires o4 (Bridge.signedKet s1)) = _
      have he : b.kraus (ket (clearRegister extra1Wires s1.basis)) =
          (if s1.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet (simB s1)) := by
        rw [simB]; simp only [Bridge.signedKet, map_smul, smul_smul]; cases s1.phase <;> simp
      have hstep := hb a (simB s1) u1 u2 u3 s1.basis haB hpathB hclB haddr hroot hhp hu1 hu2 hu3 hu4 hu6 hu7
      rw [show Bridge.signedKet s1 = (if s1.phase then (-1 : ℂ) else 1) • ket s1.basis from rfl,
        map_smul, map_smul, hk, map_smul, he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_mid s1.phase (registerXResetMagnitude extra1Wires.length) c _ _ hsq)
  -- Step 7: literal `lit1Norm` (0 measurements)
  have h7_sim (o1 o2 o3 : List Bool) (ho1 : o1.length = 529) (ho2 : o2.length = 272) (ho3 : o3.length = 665) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (sL1 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
            AddrValid WideBank8.Fast16.windowBits windowRoot a (simB (sim1 sL1)) →
            Clean WideBank8.Fast16.pathBank (simB (sim1 sL1)).basis →
            Clean (scrShortWires ++ extra2Wires ++ garb2) (simB (sim1 sL1)).basis →
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) = a →
            (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, (sim1 sL1).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, (sim2a (simL2 read a (simB (sim1 sL1)))).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sL1) =
              (c * ((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
                registerXPhase garb1 o3 u3)) •
                Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))).phase,
                  simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))⟩)
        (step7Src read (o1 ++ o2 ++ o3)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation lit1Norm
    obtain ⟨c2, a2, m2⟩ := h8_sim o1 o2 o3 ho1 ho2 ho3
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step7Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨m2b, hm2b, hb₂⟩ := hb₂
    have hh0 : b₁.history = List.nil := List.eq_nil_of_length_eq_zero (by rw [hb₁.1, lit1Norm_meas])
    refine ⟨m2b, hm2b, ?_⟩
    intro a sL1 u1 u2 u3 haB hpathB hclB haddr hroot hhp hu1 hu2 hu3 hu4 hu6 hu7
    have hnorm : ECDSAAdd.run lit1Norm b₁.history sL1 = sim1 sL1 := by
      rw [hh0, lit1Norm, sim1]; exact ECDSAAdd.Baselines.normalize_run lit1 List.nil sL1
    have hstep := hb₂ a (sim1 sL1) u1 u2 u3 haB hpathB hclB haddr hroot hhp hu1 hu2 hu3 hu4 hu6 hu7
    change b₂.kraus (b₁.kraus (Bridge.signedKet sL1)) = _
    rw [hb₁.2, hnorm, map_smul, hstep, smul_smul]
    exact congrArg (· • _) (by ring)
  -- Step 6: measureReset `garb1` (`o3`)
  have h6_sim (o1 o2 : List Bool) (ho1 : o1.length = 529) (ho2 : o2.length = 272) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (s1_0 sL1 : ECDSAAdd.State) (u1 u2 : BasisState),
            (⟨s1_0.phase, clearRegister garb1 s1_0.basis⟩ : ECDSAAdd.State) = sL1 →
            AddrValid WideBank8.Fast16.windowBits windowRoot a (simB (sim1 sL1)) →
            Clean WideBank8.Fast16.pathBank (simB (sim1 sL1)).basis →
            Clean (scrShortWires ++ extra2Wires ++ garb2) (simB (sim1 sL1)).basis →
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) = a →
            (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d3, s1_0.basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, (sim1 sL1).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, (sim2a (simL2 read a (simB (sim1 sL1)))).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet s1_0) =
              (c * (registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2)) •
                Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))).phase,
                  simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))⟩)
        (step6Src read (o1 ++ o2)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step6Src
    apply MeasuredClear.measureResetThen_sim garb1 _
      (fun o3 b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
        ∀ a (sL1 : ECDSAAdd.State) (u1 u2 u3 : BasisState),
          AddrValid WideBank8.Fast16.windowBits windowRoot a (simB (sim1 sL1)) →
          Clean WideBank8.Fast16.pathBank (simB (sim1 sL1)).basis →
          Clean (scrShortWires ++ extra2Wires ++ garb2) (simB (sim1 sL1)).basis →
          tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) = a →
          (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) windowRoot = true →
          Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d3, u3 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, (sim1 sL1).basis q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d6, (sim2a (simL2 read a (simB (sim1 sL1)))).basis q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))).basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sL1) =
            (c * ((registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2) *
              registerXPhase garb1 o3 u3)) •
              Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))).phase,
                simT m2b (simC (sim2a (simL2 read a (simB (sim1 sL1)))))⟩)
    · intro o3 ho3; exact h7_sim o1 o2 o3 ho1 ho2 (by rw [garb1_len] at ho3; exact ho3)
    · intro o3 ho3 b c hb; obtain ⟨m2b, hm2b, hb⟩ := hb; refine ⟨m2b, hm2b, ?_⟩
      intro a s1_0 sL1 u1 u2 hsL1 haB hpathB hclB haddr hroot hhp hu1 hu2 hu3 hu4 hu6 hu7
      have hk := xResetRegisterKraus_ket garb1 o3 s1_0.basis ho3 garb1_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho3] at hk
      have hsq := MeasuredClear.registerXPhase_square garb1 o3 s1_0.basis
      have ⟨hph, hba⟩ := (ECDSAAdd.State.mk.injEq _ _ _ _).mp hsL1
      change b.kraus (xResetRegisterKraus garb1 o3 (Bridge.signedKet s1_0)) = _
      have he : b.kraus (ket (clearRegister garb1 s1_0.basis)) =
          (if s1_0.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet sL1) := by
        rw [hba, hph]; simp only [Bridge.signedKet, map_smul, smul_smul]; cases sL1.phase <;> simp
      have hstep := hb a sL1 u1 u2 s1_0.basis haB hpathB hclB haddr hroot hhp hu1 hu2 hu3 hu4 hu6 hu7
      rw [show Bridge.signedKet s1_0 = (if s1_0.phase then (-1 : ℂ) else 1) • ket s1_0.basis from rfl,
        map_smul, map_smul, hk, map_smul, he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_mid s1_0.phase (registerXResetMagnitude garb1.length) c _ _ hsq)
  -- Step 5: `f1.loadSource`
  have h5_sim (o1 o2 : List Bool) (ho1 : o1.length = 529) (ho2 : o2.length = 272) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (sA : ECDSAAdd.State) (u1 u2 : BasisState),
            AddrValid WideBank8.Fast16.windowBits windowRoot a sA →
            Clean WideBank8.Fast16.pathBank sA.basis →
            Clean (extra1Wires ++ garb1) sA.basis →
            AddrValid WideBank8.Fast16.windowBits windowRoot a (simB (sim1 (simL1 read a sA))) →
            Clean WideBank8.Fast16.pathBank (simB (sim1 (simL1 read a sA))).basis →
            Clean (scrShortWires ++ extra2Wires ++ garb2) (simB (sim1 (simL1 read a sA))).basis →
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))) = a →
            (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, (sim1 (simL1 read a sA)).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet sA) =
              (c * (registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2)) •
                Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))).phase,
                  simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))⟩)
        (step5Src read (o1 ++ o2)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := f1.load_sim read f1_geo
    obtain ⟨c2, a2, m2⟩ := h6_sim o1 o2 ho1 ho2
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step5Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨m2b, hm2b, hb₂⟩ := hb₂
    refine ⟨m2b, hm2b, ?_⟩
    intro a sA u1 u2 haA hpathA hclA haB hpathB hclB haddr hroot hhp hu1 hu2 hu4 hu6 hu7
    have hclA' : Clean (portTargets f1.ports ++ f1.garb) sA.basis := by
      change Clean (portTargets p1_16 ++ garb1) sA.basis; rw [p1_16_targets]; exact hclA
    have hst := f1.load_state read f1_geo a sA ⟨hpathA, haA.1, haA.2⟩ hclA'
    set s1_0 := ECDSAAdd.run f1.swapNet List.nil
      (ECDSAAdd.run ((specialize f1.selCode (tableAddressValue f1.selBits sA.basis)).instantiate read) List.nil sA)
    have hsL1 : (⟨s1_0.phase, clearRegister garb1 s1_0.basis⟩ : ECDSAAdd.State) = simL1 read a sA := by
      rw [simL1]
      refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
      have h2 := hst.2.2.2; change clearRegister garb1 s1_0.basis = tableXorState (portMask read p1_16 a) (sA.basis windowRoot) sA.basis at h2
      rw [haA.2] at h2; exact h2
    have hu3 : ∀ q ∈ d3, s1_0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
      have h1 := hst.2.2.1 q hq
      change s1_0.basis q.target = (sA.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
      rw [haA.2, Bool.true_and] at h1; exact h1
    have hstep := hb₂ a s1_0 (simL1 read a sA) u1 u2 hsL1 haB hpathB hclB haddr hroot hhp hu1 hu2 hu3 hu4 hu6 hu7
    change b₂.kraus (b₁.kraus (Bridge.signedKet sA)) = _
    rw [hb₁ a sA ⟨hpathA, haA.1, haA.2⟩ hclA', map_smul, hstep, smul_smul]
    exact congrArg (· • _) (by ring)
  -- Step 4: measureReset `p0ClearWires` (`o2`)
  have h4_sim (o1 : List Bool) (ho1 : o1.length = 529) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
          ∀ a (s0 : ECDSAAdd.State) (u1 : BasisState),
            AddrValid WideBank8.Fast16.windowBits windowRoot a (simA s0) →
            Clean WideBank8.Fast16.pathBank (simA s0).basis →
            Clean (extra1Wires ++ garb1) (simA s0).basis →
            AddrValid WideBank8.Fast16.windowBits windowRoot a (simB (sim1 (simL1 read a (simA s0)))) →
            Clean WideBank8.Fast16.pathBank (simB (sim1 (simL1 read a (simA s0)))).basis →
            Clean (scrShortWires ++ extra2Wires ++ garb2) (simB (sim1 (simL1 read a (simA s0)))).basis →
            tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA s0)))))))) = a →
            (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA s0)))))))) windowRoot = true →
            Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA s0)))))))) →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d2, s0.basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d4, (sim1 (simL1 read a (simA s0))).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d6, (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA s0)))))).basis q.target = decide (read (q.ref a) = q.value)) →
            (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA s0)))))))).basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet s0) =
              (c * registerXPhase garb0 o1 u1) •
                Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA s0)))))))).phase,
                  simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA s0)))))))⟩)
        (step4Src read o1).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step4Src
    apply MeasuredClear.measureResetThen_sim p0ClearWires _
      (fun o2 b c => ∃ m2b : List Bool, m2b.length = mLit2b ∧
        ∀ a (sA : ECDSAAdd.State) (u1 u2 : BasisState),
          AddrValid WideBank8.Fast16.windowBits windowRoot a sA →
          Clean WideBank8.Fast16.pathBank sA.basis →
          Clean (extra1Wires ++ garb1) sA.basis →
          AddrValid WideBank8.Fast16.windowBits windowRoot a (simB (sim1 (simL1 read a sA))) →
          Clean WideBank8.Fast16.pathBank (simB (sim1 (simL1 read a sA))).basis →
          Clean (scrShortWires ++ extra2Wires ++ garb2) (simB (sim1 (simL1 read a sA))).basis →
          tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))) = a →
          (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))) windowRoot = true →
          Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))) →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d2, u2 q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d4, (sim1 (simL1 read a sA)).basis q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d6, (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))).basis q.target = decide (read (q.ref a) = q.value)) →
          (∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))).basis q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet sA) =
            (c * (registerXPhase garb0 o1 u1 * registerXPhase p0ClearWires o2 u2)) •
              Bridge.signedKet ⟨(sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))).phase,
                simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a sA))))))⟩)
    · intro o2 ho2; exact h5_sim o1 o2 ho1 (by rw [p0ClearWires_len] at ho2; exact ho2)
    · intro o2 ho2 b c hb; obtain ⟨m2b, hm2b, hb⟩ := hb; refine ⟨m2b, hm2b, ?_⟩
      intro a s0 u1 haA hpathA hclA haB hpathB hclB haddr hroot hhp hu1 hu2 hu4 hu6 hu7
      have hk := xResetRegisterKraus_ket p0ClearWires o2 s0.basis ho2 p0ClearWires_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho2] at hk
      have hsq := MeasuredClear.registerXPhase_square p0ClearWires o2 s0.basis
      change b.kraus (xResetRegisterKraus p0ClearWires o2 (Bridge.signedKet s0)) = _
      have he : b.kraus (ket (clearRegister p0ClearWires s0.basis)) =
          (if s0.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet (simA s0)) := by
        rw [simA]; simp only [Bridge.signedKet, map_smul, smul_smul]; cases s0.phase <;> simp
      have hstep := hb a (simA s0) u1 s0.basis haA hpathA hclA haB hpathB hclB haddr hroot hhp hu1 hu2 hu4 hu6 hu7
      rw [show Bridge.signedKet s0 = (if s0.phase then (-1 : ℂ) else 1) • ket s0.basis from rfl,
        map_smul, map_smul, hk, map_smul, he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_mid s0.phase (registerXResetMagnitude p0ClearWires.length) c _ _ hsq)
  -- Step 3: literal `lit0Norm` + apply `CornerFast.corner_fused_run`!
  have h3_sim (o1 : List Bool) (ho1 : o1.length = 529) :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m : List Bool, m.length = mLit0 + mLit2b ∧
          ∀ a (st : ECDSAAdd.State) (u1 : BasisState) {cx cy : ECDSAAdd.Fp} (hc : ECDSAAdd.Secp256k1.curve.toAffine.Nonsingular cx cy),
            RowReads (read32C coeffs Q a) (probeRows a) (.some hc) →
            ∀ (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState),
            PointDialogValues streamLayout X Y G base st.basis →
            base windowRoot = true → base streamLayout.control = true →
            (G = true → base streamLayout.infinitySelect = false ∧ base streamLayout.doubleSelect = false ∧
              base streamLayout.genericSelect = false ∧ base streamLayout.core.equalNegY = false) →
            AddrValid WideBank8.Fast16.windowBits windowRoot a st →
            Clean WideBank8.Fast16.pathBank st.basis →
            AddrValid WideBank8.Fast16.windowBits windowRoot a (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st) →
            Clean WideBank8.Fast16.pathBank (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st).basis →
            (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet (simL0 read a st)) =
              (c * registerXPhase garb0 o1 u1) •
                Bridge.signedKet (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st))
        (step3Src read o1).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    obtain ⟨c1, a1, m1⟩ := literal_simulation lit0Norm
    obtain ⟨c2, a2, m2⟩ := h4_sim o1 ho1
    refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
    rw [step3Src, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨m2b, hm2b, hb₂⟩ := hb₂
    have hm0 : b₁.history.length = ECDSAAdd.measurementCount lit0 := by rw [hb₁.1, lit0Norm_meas, mLit0]
    have hm2b' : m2b.length = ECDSAAdd.measurementCount cornerA2Prog := by rw [hm2b, mLit2b, lit2b_meas]
    have hmP : (cornerPerm b₁.history m2b).length = mLit0 + mLit2b := by
      rw [cornerPerm_len b₁.history m2b hm0 hm2b', mLit0, lit0_meas, mLit2b, lit2b_meas]
    refine ⟨cornerPerm b₁.history m2b, hmP, ?_⟩
    intro a st u1 cx cy hc hr X Y G base hv hroot hctl hflag ha hpath haOut hpathOut hu1
    have hp0_eq : portMask read p0_16 a = portMask (read32C coeffs Q a) (p0Ports probeRows) a := by
      rw [read32C]; exact rows_portMask_eq coeffs Q a _
    have hp1_eq : portMask read p1_16 a = portMask (read32C coeffs Q a) (p1Ports probeRows) a := by
      rw [read32C]; exact rows_portMask_eq coeffs Q a _
    have hp2_eq : portMask read p2_16 a = portMask (read32C coeffs Q a) (p2Ports probeRows) a := by
      rw [read32C]; exact rows_portMask_eq coeffs Q a _
    obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6, hsOut_eq⟩ := lift_fused
      lit0 lit1 lit2a lit2b (origCornerRef (read32C coeffs Q a) a)
      (portMask read p0_16 a) (portMask read p1_16 a) (portMask read p2_16 a)
      (portMask (read32C coeffs Q a) (p0Ports probeRows) a)
      (portMask (read32C coeffs Q a) (p1Ports probeRows) a)
      (portMask (read32C coeffs Q a) (p2Ports probeRows) a)
      (read32C coeffs Q a) a st b₁.history m2b (cornerPerm b₁.history m2b)
      (simL0 read a) simA (simL1 read a) sim1 simB (simL2 read a) sim2a simC (sim2b m2b) (simT m2b)
      hp0_eq hp1_eq hp2_eq
      (by unfold simL0; rfl) (fun _ => by unfold simA; rfl) (fun _ => by unfold simL1; rfl)
      (fun _ => by unfold sim1; rfl) (fun _ => by unfold simB; rfl) (fun _ => by unfold simL2; rfl)
      (fun _ => by unfold sim2a; rfl) (fun _ => by unfold simC; rfl) (fun _ => by unfold sim2b; rfl)
      (fun _ => by unfold simT; rfl)
      (CornerFast.corner_fused_run (read32C coeffs Q a) a hc hr X Y G base st hv hroot hctl hflag b₁.history m2b hm0 hm2b')
    have hnorm : ECDSAAdd.run lit0Norm b₁.history (simL0 read a st) = ECDSAAdd.run lit0 b₁.history (simL0 read a st) := by
      rw [lit0Norm]; exact ECDSAAdd.Baselines.normalize_run lit0 b₁.history (simL0 read a st)
    have hwin_not_p0 (w : Wire) (hw : w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank) :
        w ∉ site2Wires ++ extra0Wires := fun hm => by
      have := mem_p0Wires hm
      simp only [windowRoot, WideBank8.Fast16.windowBits, WideBank8.Fast16.pathBank,
        List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    have hwin_not_p0c (w : Wire) (hw : w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank) :
        w ∉ p0ClearWires := fun hm => by
      simp only [p0ClearWires, cyTailWires, extra0Wires, List.mem_append, List.mem_range'_1] at hm
      simp only [windowRoot, WideBank8.Fast16.windowBits, WideBank8.Fast16.pathBank,
        List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    have hwin_not_e1 (w : Wire) (hw : w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank) :
        w ∉ extra1Wires := fun hm => by
      simp only [extra1Wires, List.mem_range'_1] at hm
      simp only [windowRoot, WideBank8.Fast16.windowBits, WideBank8.Fast16.pathBank,
        List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, List.mem_range'_1] at hw
      dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    have hfrA (w : Wire) (hw : w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank) :
        (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st))).basis w = st.basis w := by
      rw [simA]; dsimp only
      rw [MeasuredClear.clearRegister_frame _ _ _ (hwin_not_p0c w hw),
        Site1Fast.run_outside_basis lit0 b₁.history (simL0 read a st) w (lit0_avoid_window w hw), simL0]; dsimp only
      exact tableXorState_outside _ _ _ _ (fun hm => hwin_not_p0 w hw (by rw [← p0_16_targets]; exact tableBitsMask_subset _ _ hm))
    have hfrB (w : Wire) (hw : w ∈ windowRoot :: WideBank8.Fast16.windowBits ++ WideBank8.Fast16.pathBank) :
        (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))).basis w = st.basis w := by
      rw [simB, sim1]; dsimp only
      rw [MeasuredClear.clearRegister_frame _ _ _ (hwin_not_e1 w hw),
        Site1Fast.run_outside_basis lit1 List.nil (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))) w (lit1_avoid_window w hw), simL1]; dsimp only
      rw [tableXorState_outside _ _ _ _ (fun hm => hwin_not_e1 w hw (by rw [← p1_16_targets]; exact tableBitsMask_subset _ _ hm))]
      exact hfrA w hw
    have haA : AddrValid WideBank8.Fast16.windowBits windowRoot a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st))) :=
      ⟨(WEX.tableAddressValue_congr _ _ _ (fun w hw => hfrA w (by simp [hw]))).trans ha.1,
       (hfrA windowRoot (by simp)).trans ha.2⟩
    have hpathA : Clean WideBank8.Fast16.pathBank (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st))).basis :=
      fun w hw => (hfrA w (by simp [hw])).trans (hpath w hw)
    have haB : AddrValid WideBank8.Fast16.windowBits windowRoot a (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))) :=
      ⟨(WEX.tableAddressValue_congr _ _ _ (fun w hw => hfrB w (by simp [hw]))).trans ha.1,
       (hfrB windowRoot (by simp)).trans ha.2⟩
    have hpathB : Clean WideBank8.Fast16.pathBank (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))).basis :=
      fun w hw => (hfrB w (by simp [hw])).trans (hpath w hw)
    have hmem_pool_band (w : Wire) (h : 14115 ≤ w ∧ w < 16728) : w ∈ streamLayout.dialogPool :=
      List.mem_of_mem_take ((mem_pool_take 2613 (le_refl _)).mpr h)
    have hclA : Clean (extra1Wires ++ garb1) (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st))).basis := fun w hw => by
      have hwb : (14115 ≤ w ∧ w < 14374) ∨ (14884 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15640) := by
        rcases List.mem_append.mp hw with h | h
        · simp only [extra1Wires, List.mem_range'_1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
        · rw [mem_garb1] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have hnk : w ∉ keepWires := by
        simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      exact hg2 w (hmem_pool_band w (by dsimp only [Wire, ECDSAAdd.Wire] at *; omega)) hnk
    have hclB : Clean (scrShortWires ++ extra2Wires ++ garb2) (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))).basis := fun w hw => by
      have hwb : (14115 ≤ w ∧ w < 14374) ∨ w = 14832 ∨ w = 14847 ∨ (14849 ≤ w ∧ w < 14874) ∨
          (14884 ≤ w ∧ w < 15144) ∨ (15399 ≤ w ∧ w < 15655) := by
        rcases List.mem_append.mp hw with h | h
        · have := mem_p2Wires h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
        · rw [mem_garb2] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      have hnk : w ∉ keepWires := by
        simp only [keepWires, cxWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
        dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      exact hg4 w (hmem_pool_band w (by dsimp only [Wire, ECDSAAdd.Wire] at *; omega)) hnk
    have hlift_clear (ps : List (LookupPort 32768)) (bs : BasisState)
        (h : ∀ q ∈ ps, bs q.target = decide (read32C coeffs Q a (q.ref a) = q.value)) :
        ∀ q ∈ clearData (Rows.ports r16 ps), bs q.target = decide (read (q.ref a) = q.value) := by
      intro q hq
      obtain ⟨p16, hp16, rfl⟩ := List.mem_map.mp hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp16
      have h1 := h p hp
      rw [read32C] at h1
      exact h1
    have hu2 : ∀ q ∈ d2, (ECDSAAdd.run lit0 b₁.history (simL0 read a st)).basis q.target = decide (read (q.ref a) = q.value) :=
      hlift_clear _ _ hg1
    have hu4 : ∀ q ∈ d4, (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st))))).basis q.target = decide (read (q.ref a) = q.value) :=
      hlift_clear _ _ hg3
    have hu6 : ∀ q ∈ d6, (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))))).basis q.target =
        decide (read (q.ref a) = q.value) :=
      hlift_clear _ _ hg5
    have hu7 : ∀ q ∈ d7, (sim2b m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))))))).basis q.target =
        decide (read (q.ref a) = q.value) :=
      hlift_clear _ _ hg6
    have hba_eq := congrArg ECDSAAdd.State.basis hsOut_eq
    dsimp only at hba_eq
    have haddr_t : tableAddressValue WideBank8.Fast16.windowBits (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))))))) = a := by
      rw [hba_eq]; exact haOut.1
    have hroot_t : (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))))))) windowRoot = true := by
      rw [hba_eq]; exact haOut.2
    have hhp_t : Clean WideBank8.Fast16.bank15.hp (simT m2b (simC (sim2a (simL2 read a (simB (sim1 (simL1 read a (simA (ECDSAAdd.run lit0 b₁.history (simL0 read a st)))))))))) := fun w hw => by
      rw [hba_eq]; exact hpathOut w (WideBank8.Fast16.bank15_ok.sub w hw)
    have hstep := hb₂ a (ECDSAAdd.run lit0 b₁.history (simL0 read a st)) u1 haA hpathA hclA haB hpathB hclB haddr_t hroot_t hhp_t hu1 hu2 hu4 hu6 hu7
    change b₂.kraus (b₁.kraus (Bridge.signedKet (simL0 read a st))) = _
    rw [hb₁.2, hnorm, map_smul, hstep, hsOut_eq, smul_smul]
    exact congrArg (· • _) (by ring)
  -- Step 2: measureReset `garb0` (`o1`)
  have h2_sim :
      ∃ cs : List ℂ, List.Forall₂
        (fun b c => ∃ m : List Bool, m.length = mLit0 + mLit2b ∧
          ∀ a (st s0_0 : ECDSAAdd.State) {cx cy : ECDSAAdd.Fp} (hc : ECDSAAdd.Secp256k1.curve.toAffine.Nonsingular cx cy),
            (⟨s0_0.phase, clearRegister garb0 s0_0.basis⟩ : ECDSAAdd.State) = simL0 read a st →
            RowReads (read32C coeffs Q a) (probeRows a) (.some hc) →
            ∀ (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState),
            PointDialogValues streamLayout X Y G base st.basis →
            base windowRoot = true → base streamLayout.control = true →
            (G = true → base streamLayout.infinitySelect = false ∧ base streamLayout.doubleSelect = false ∧
              base streamLayout.genericSelect = false ∧ base streamLayout.core.equalNegY = false) →
            AddrValid WideBank8.Fast16.windowBits windowRoot a st →
            Clean WideBank8.Fast16.pathBank st.basis →
            AddrValid WideBank8.Fast16.windowBits windowRoot a (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st) →
            Clean WideBank8.Fast16.pathBank (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st).basis →
            (∀ q ∈ d1, s0_0.basis q.target = decide (read (q.ref a) = q.value)) →
            b.kraus (Bridge.signedKet s0_0) =
              c • Bridge.signedKet (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st))
        (step2Src read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
    unfold step2Src
    apply MeasuredClear.measureResetThen_sim garb0 _
      (fun o1 b c => ∃ m : List Bool, m.length = mLit0 + mLit2b ∧
        ∀ a (st : ECDSAAdd.State) (u1 : BasisState) {cx cy : ECDSAAdd.Fp} (hc : ECDSAAdd.Secp256k1.curve.toAffine.Nonsingular cx cy),
          RowReads (read32C coeffs Q a) (probeRows a) (.some hc) →
          ∀ (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState),
          PointDialogValues streamLayout X Y G base st.basis →
          base windowRoot = true → base streamLayout.control = true →
          (G = true → base streamLayout.infinitySelect = false ∧ base streamLayout.doubleSelect = false ∧
            base streamLayout.genericSelect = false ∧ base streamLayout.core.equalNegY = false) →
          AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          Clean WideBank8.Fast16.pathBank st.basis →
          AddrValid WideBank8.Fast16.windowBits windowRoot a (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st) →
          Clean WideBank8.Fast16.pathBank (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st).basis →
          (∀ q ∈ d1, u1 q.target = decide (read (q.ref a) = q.value)) →
          b.kraus (Bridge.signedKet (simL0 read a st)) =
            (c * registerXPhase garb0 o1 u1) • Bridge.signedKet (ECDSAAdd.run (origCornerRef (read32C coeffs Q a) a) m st))
    · intro o1 ho1; exact h3_sim o1 (by rw [garb0_len] at ho1; exact ho1)
    · intro o1 ho1 b c hb; obtain ⟨m, hm, hb⟩ := hb; refine ⟨m, hm, ?_⟩
      intro a st s0_0 cx cy hc hsL0 hr X Y G base hv hroot hctl hflag ha hpath haOut hpathOut hu1
      have hk := xResetRegisterKraus_ket garb0 o1 s0_0.basis ho1 garb0_nodup
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho1] at hk
      have hsq := MeasuredClear.registerXPhase_square garb0 o1 s0_0.basis
      have hsL0' := hsL0
      rw [simL0] at hsL0'
      have ⟨hph, hba⟩ := (ECDSAAdd.State.mk.injEq _ _ _ _).mp hsL0'
      change b.kraus (xResetRegisterKraus garb0 o1 (Bridge.signedKet s0_0)) = _
      have he : b.kraus (ket (clearRegister garb0 s0_0.basis)) =
          (if s0_0.phase then (-1 : ℂ) else 1) • b.kraus (Bridge.signedKet (simL0 read a st)) := by
        rw [simL0, hba, hph]; simp only [Bridge.signedKet, map_smul, smul_smul]; cases st.phase <;> simp
      have hstep := hb a st s0_0.basis hc hr X Y G base hv hroot hctl hflag ha hpath haOut hpathOut hu1
      rw [show Bridge.signedKet s0_0 = (if s0_0.phase then (-1 : ℂ) else 1) • ket s0_0.basis from rfl,
        map_smul, map_smul, hk, map_smul, he, hstep, smul_smul, smul_smul, smul_smul]
      exact congrArg (· • _) (phase_cancel_step0 s0_0.phase (registerXResetMagnitude garb0.length) c
        (registerXPhase garb0 o1 s0_0.basis) hsq)
  -- Step 1: `f0.loadSource`
  obtain ⟨c1, a1, m1⟩ := f0.load_sim read f0_geo
  obtain ⟨c2, a2, m2⟩ := h2_sim
  refine ⟨coherentSeqCoefficients c1 c2, ?_, by rw [simulationCoefficients_mass, m1, m2]; norm_num⟩
  rw [cornerFusedSrc, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq a1 a2
  intro b₁ k₁ b₂ k₂ hb₁ hb₂
  obtain ⟨m, hm, hb₂⟩ := hb₂
  refine ⟨m, hm, ?_⟩
  intro a st cx cy hc hr X Y G base hv hroot hctl hflag ha hpath haOut hpathOut
  have hclean : Clean streamLayout.dialogPool st.basis := (ECDSAAdd.Arithmetic.regValue_zero _ _).mp hv.clean
  have hcl0 : Clean (portTargets f0.ports ++ f0.g1) st.basis := fun w hw => by
    rw [f0, p0_16_targets] at hw
    have hwb : 14115 ≤ w ∧ w < 16728 := by
      rcases List.mem_append.mp hw with h | h
      · have := mem_p0Wires h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
      · rw [mem_garb0] at h; dsimp only [Wire, ECDSAAdd.Wire] at *; omega
    exact hclean w (List.mem_of_mem_take ((mem_pool_take 2613 (le_refl _)).mpr hwb))
  have hst := f0.load_state read f0_geo a st ⟨hpath, ha.1, ha.2⟩ hcl0
  set s0_0 := ECDSAAdd.run f0.swapNet List.nil
    (ECDSAAdd.run ((specialize f0.selCode (tableAddressValue f0.selBits st.basis)).instantiate read) List.nil st)
  have hsL0 : (⟨s0_0.phase, clearRegister garb0 s0_0.basis⟩ : ECDSAAdd.State) = simL0 read a st := by
    rw [simL0]
    refine ECDSAAdd.State.mk.injEq _ _ _ _ |>.mpr ⟨hst.1, ?_⟩
    have h2 := hst.2.2.2; change clearRegister garb0 s0_0.basis = tableXorState (portMask read p0_16 a) (st.basis windowRoot) st.basis at h2
    rw [ha.2] at h2; exact h2
  have hu1 : ∀ q ∈ d1, s0_0.basis q.target = decide (read (q.ref a) = q.value) := fun q hq => by
    have h1 := hst.2.2.1 q hq
    change s0_0.basis q.target = (st.basis windowRoot && decide (read (q.ref a) = q.value)) at h1
    rw [ha.2, Bool.true_and] at h1; exact h1
  have hstep := hb₂ a st s0_0 hc hsL0 hr X Y G base hv hroot hctl hflag ha hpath haOut hpathOut hu1
  change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
  rw [hb₁ a st ⟨hpath, ha.1, ha.2⟩ hcl0, map_smul, hstep, smul_smul]

/-! ### Part 5: Splicing `twoPassProg` AND `cornerFusedProg` into `WideBank8.Row16.code` -/

local notation "b0" => Site1Wire.Wide16.b0
local notation "b1" => Site1Wire.Wide16.b1
local notation "b2" => Site1Wire.Wide16.b2

def midW : WideBank8.Fast16.FCode2 65536 := (WEXFast.fgeneric3.take 9).map WideBank8.Row16.lift
def b12 : WideBank8.Fast16.FBlock2 65536 := .fast1 (WideBank8.Row16.fast1 WEXFast.site2F)
def b13 : WideBank8.Fast16.FBlock2 65536 := .std (.plain (Rows.code r16 (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))))
def b14 : WideBank8.Fast16.FBlock2 65536 := .std (.plain (Rows.code r16 WEX.cornerNeg))
def b15 : WideBank8.Fast16.FBlock2 65536 := .pair WideBank8.Row16.corner
def tailW : WideBank8.Fast16.FCode2 65536 := WideBank8.Row16.tailF.map WideBank8.Row16.lift
def cornerBlocks : WideBank8.Fast16.FCode2 65536 := [b12, b13, b14, b15]

private theorem fblockRec_fast1 {n} (f : WideBank8.Fast16.FastSite1 n) :
    WideBank8.Fast16.fblockRec (.fast1 f) =
      codeRecords WideBank8.Fast16.selBits1 WideBank8.Fast16.selPaths1 windowRoot f.selCode + 0 +
        (f.garbPorts.length +
          (codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot (normalizeW f.site.arithmetic) +
            (f.site.ports.length +
              (MeasuredClear.recordMeasurements
                (MeasuredClear.recordUnaryOps (tableAddressTree WideBank8.Fast16.bank15.high 0 1) f.site.guard WideBank8.Fast16.bank15.hp) + 255)))) := rfl

private theorem fblockRec_plain {n} (c : WCode n) :
    WideBank8.Fast16.fblockRec (.std (.plain c)) =
      codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot (normalizeW c) := rfl

private theorem fblockRec_pair {n} (q : WideBank8.Fast16.UnitPair n) :
    WideBank8.Fast16.fblockRec (.pair q) =
      codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot (normalizeW q.u₁.pre) +
        (q.gd.length +
          (codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot (normalizeW q.u₂.pre) +
            (q.u₂.clear.ports.length +
              (MeasuredClear.recordMeasurements
                (MeasuredClear.recordUnaryOps (tableAddressTree WideBank8.Fast16.bank15.high 0 1) q.u₂.clear.guard WideBank8.Fast16.bank15.hp) + 255)))) := rfl

private theorem fblockTP_fast1 {n} (f : WideBank8.Fast16.FastSite1 n) :
    WideBank8.Fast16.fblockTP (.fast1 f) =
      32767 + ECDSAAdd.toffoliCount f.swapNet +
        (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502 := rfl

private theorem fblockTP_plain {n} (c : WCode n) :
    WideBank8.Fast16.fblockTP (.std (.plain c)) =
      literalToffolis (normalizeW c) + traversals c * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) +
        PoolHost.hostCodeExtra c := rfl

private theorem literalRecords_wLiteral {n} (p : ECDSAAdd.Program) :
    literalRecords (n := n) (wLiteral p) = ECDSAAdd.measurementCount p := Nat.add_zero _

private theorem traversals_wLiteral {n} (p : ECDSAAdd.Program) :
    traversals (n := n) (wLiteral p) = 0 := rfl

private theorem literalToffolis_wLiteral {n} (p : ECDSAAdd.Program) :
    literalToffolis (n := n) (normalizeW (wLiteral p)) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram p) := Nat.add_zero _

private theorem literalRecords_lookup_singleton {n} (ctl : Option Wire) (ps : List (LookupPort n)) :
    literalRecords [WInstr.lookup ctl ps] = 0 := rfl

private theorem traversals_lookup_singleton {n} (ctl : Option Wire) (ps : List (LookupPort n)) :
    traversals [WInstr.lookup ctl ps] = 1 := rfl

private theorem literalToffolis_lookup_singleton {n} (ctl : Option Wire) (ps : List (LookupPort n)) :
    literalToffolis (normalizeW [WInstr.lookup ctl ps]) = 0 := rfl

private theorem fblockTP_pair {n} (q : WideBank8.Fast16.UnitPair n) :
    WideBank8.Fast16.fblockTP (.pair q) =
      literalToffolis (normalizeW q.u₁.pre) + traversals q.u₁.pre * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) +
        (literalToffolis (normalizeW q.u₂.pre) + traversals q.u₂.pre * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) +
          ((tableAddressTree WideBank8.Fast16.bank15.high 0 1).internalNodes + 247)) := rfl

private theorem b12_rec_arith (m : Nat) : 32767 + 0 + (512 + (m + (512 + (255 + 255)))) = 34301 + m := by omega
private theorem b15_rec_arith (m : Nat) : 65535 + (256 + (m + (771 + (255 + 255)))) = 67072 + m := by omega
private theorem b12_tp_arith (t : Nat) : 32767 + 512 + (t + 0 * 65535) + 502 = 33781 + t := by omega
private theorem b15_tp_arith (t1 t2 : Nat) : t1 + 1 * (2 ^ 16 - 1) + (t2 + 0 * (2 ^ 16 - 1) + (255 + 247)) = 66037 + t1 + t2 := by omega
private theorem b12_b15_tp_arith (l0 l1 l2a l2b p1 p2 p3 p4 p5 : Nat)
    (hsp : l0 + l1 + l2a + l2b + 1 = p1 + p2 + p3 + p4 + p5) :
    33781 + p1 + p2 + p3 + (66037 + p4 + p5) =
      (75822 + l0 + l1 + l2a + l2b) + 23997 := by omega
private theorem newRow_rec_arith (r0 r1 r2 rm rc rt : Nat)
    (h : r0 + r1 + r2 + (rm + (rc + 24518) + rt) = 1727904) :
    r0 + r1 + r2 + rm + rc + rt = 1703386 := by omega
private theorem rowTP_arith (tall t0 t1 ts tt tm tc tw : Nat)
    (h : t0 + t1 + (16383 + 774 + ts + 32767 + 513 + tt + (255 + 247)) + (tm + (tc + 23997) + tw) = tall - 15098) :
    t0 + t1 + (16383 + 774 + ts + 32767 + 513 + tt + (255 + 247)) + tm + tc + tw = tall - 15098 - 23997 := by omega

theorem restW_split : Site1Wire.Wide16.restW = midW ++ cornerBlocks ++ tailW := by
  have h1 : WideBank8.Row16.code =
      b0 :: b1 :: b2 :: (midW ++ cornerBlocks ++ tailW) := by
    unfold WideBank8.Row16.code
    rw [WideBank8.Row16.headF, WEXUnlookup.rowPre3]
    have hfg : WEXFast.fgeneric3 =
        WEXFast.fgeneric3.take 9 ++ [.fast1 WEXFast.site2F, .std (.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout)))] := rfl
    conv_lhs => rw [hfg]
    simp [Site1Wire.Wide16.b0, Site1Wire.Wide16.b1, Site1Wire.Wide16.b2,
      midW, cornerBlocks, b12, b13, b14, b15, tailW, r16, Site1Wire.Wide16.r16,
      WideBank8.Row16.lift, Rows.block, toBlock2, List.append_assoc]
  rw [Site1Wire.Wide16.restW, h1]; rfl

theorem code_split_corner : WideBank8.Row16.code = b0 :: b1 :: b2 :: (midW ++ cornerBlocks ++ tailW) := by
  rw [Site1Wire.Wide16.code_split, restW_split]

theorem mem_midW_code (b : WideBank8.Fast16.FBlock2 65536) (hb : b ∈ midW) : b ∈ WideBank8.Row16.code := by
  rw [code_split_corner]; simp [hb]
theorem mem_tailW_code (b : WideBank8.Fast16.FBlock2 65536) (hb : b ∈ tailW) : b ∈ WideBank8.Row16.code := by
  rw [code_split_corner]; simp [hb]
theorem mem_corner_code (b : WideBank8.Fast16.FBlock2 65536) (hb : b ∈ cornerBlocks) : b ∈ WideBank8.Row16.code := by
  rw [code_split_corner]; simp [hb]

private theorem frecs_append {n} (a b : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.frecs (a ++ b) = WideBank8.Fast16.frecs a + WideBank8.Fast16.frecs b := by
  induction a with
  | nil => simp [WideBank8.Fast16.frecs]
  | cons x a ih => simp [WideBank8.Fast16.frecs, ih, Nat.add_assoc]

private theorem fcodeTP_append {n} (a b : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.fcodeTP (a ++ b) = WideBank8.Fast16.fcodeTP a + WideBank8.Fast16.fcodeTP b := by
  induction a with
  | nil => simp [WideBank8.Fast16.fcodeTP]
  | cons x a ih => simp [WideBank8.Fast16.fcodeTP, ih, Nat.add_assoc]

private theorem fslack_append {n} (a b : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.fslack (a ++ b) = WideBank8.Fast16.fslack a + WideBank8.Fast16.fslack b := by
  induction a with
  | nil => simp [WideBank8.Fast16.fslack]
  | cons x a ih => simp [WideBank8.Fast16.fslack, ih, Nat.add_assoc]

theorem b12_rec_eq : WideBank8.Fast16.fblockRec b12 = 34301 + ECDSAAdd.measurementCount pair2Prog := by
  have hg := WideBank8.Row16.geometry b12 (mem_corner_code _ (by simp [cornerBlocks]))
  have hgeo : WideBank8.Fast16.FastGeometry1 (WideBank8.Row16.fast1 WEXFast.site2F) := hg.1
  have hsel := WideBank8.Fast16.FastSite1.sel_records _ hgeo
  have hgl : (WideBank8.Row16.fast1 WEXFast.site2F).garbPorts.length = 512 :=
    (WideBank8.Fast16.FastSite1.garbPorts_length _ hgeo).trans WEXFast.site2F_garb_length
  have hplen : (WideBank8.Row16.fast1 WEXFast.site2F).site.ports.length = 512 := by
    have hp : (WideBank8.Row16.fast1 WEXFast.site2F).site.ports = Rows.ports r16 (site2Ports probeRows) := rfl
    rw [hp, Rows.ports, List.length_map]; exact site2Ports_length probeRows
  have hari := codeRecords_eq _ _ _ _ (WideBank8.Fast16.FastSite1.arith_layouts _ hgeo)
  have ha_eq : (WideBank8.Row16.fast1 WEXFast.site2F).site.arithmetic = Rows.code r16 (wLiteral pair2Prog) := rfl
  have hlit : literalRecords (normalizeW (WideBank8.Row16.fast1 WEXFast.site2F).site.arithmetic) = ECDSAAdd.measurementCount pair2Prog := by
    rw [ha_eq, literalRecords_normalize, (WideBank8.Counts.lift_metrics r16 _).2.1]
    exact literalRecords_wLiteral pair2Prog
  have htr : traversals (normalizeW (WideBank8.Row16.fast1 WEXFast.site2F).site.arithmetic) = 0 := by
    rw [ha_eq, traversals_normalize, (WideBank8.Counts.lift_metrics r16 _).2.2]
    exact traversals_wLiteral pair2Prog
  have hbits : WideBank8.Fast16.bank15.bits = WideBank8.Fast16.windowBits := rfl
  have hpaths : WideBank8.Fast16.bank15.paths = WideBank8.Fast16.pathBank := rfl
  have hari' : codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
      (normalizeW (WideBank8.Row16.fast1 WEXFast.site2F).site.arithmetic) = ECDSAAdd.measurementCount pair2Prog := by
    rw [hbits, hpaths, hari, hlit, htr, Nat.zero_mul, Nat.add_zero]
  have hcr := (MeasuredClear.recordUnary_counts _ _ _ (WideBank8.Fast16.FastSite1.site_layout_bank _ hgeo) 0).1
  rw [WideBank8.Fast16.bank_tree_nodes] at hcr
  have hlhs : WideBank8.Fast16.fblockRec b12 = 32767 + 0 + (512 + (ECDSAAdd.measurementCount pair2Prog + (512 + (255 + 255)))) :=
    (congrArg WideBank8.Fast16.fblockRec (show b12 = .fast1 (WideBank8.Row16.fast1 WEXFast.site2F) from rfl)).trans
      ((fblockRec_fast1 (WideBank8.Row16.fast1 WEXFast.site2F)).trans
        (congrArg₂ (· + ·) (congrArg (· + 0) hsel)
          (congrArg₂ (· + ·) hgl (congrArg₂ (· + ·) hari' (congrArg₂ (· + ·) hplen (congrArg (· + 255) hcr))))))
  exact hlhs.trans (b12_rec_arith _)

theorem b13_rec_eq : WideBank8.Fast16.fblockRec b13 = 0 := by
  have hg : BlockGeoP2 WideBank8.Fast16.bank15 (.plain (Rows.code r16 (wLiteral (ECDSAAdd.Frontier.zrep streamLayout)))) :=
    WideBank8.Row16.geometry b13 (mem_corner_code _ (by simp [cornerBlocks]))
  have hlay := WideBank8.geo_lay2 WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok _ hg
  rw [b13, fblockRec_plain, codeRecords_eq _ _ _ _ hlay, literalRecords_normalize, traversals_normalize,
    (WideBank8.Counts.lift_metrics r16 _).2.1, (WideBank8.Counts.lift_metrics r16 _).2.2,
    literalRecords_wLiteral, traversals_wLiteral, zrep_records, Nat.zero_mul, Nat.add_zero]

theorem b14_rec_eq : WideBank8.Fast16.fblockRec b14 = ECDSAAdd.measurementCount cornerNegProg := by
  have hg : BlockGeoP2 WideBank8.Fast16.bank15 (.plain (Rows.code r16 WEX.cornerNeg)) :=
    WideBank8.Row16.geometry b14 (mem_corner_code _ (by simp [cornerBlocks]))
  have hlay := WideBank8.geo_lay2 WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok _ hg
  rw [b14, fblockRec_plain, codeRecords_eq _ _ _ _ hlay, literalRecords_normalize, traversals_normalize,
    (WideBank8.Counts.lift_metrics r16 _).2.1, (WideBank8.Counts.lift_metrics r16 _).2.2,
    (litOnly_metrics WEX.cornerNeg cornerNeg_litOnly).1,
    (litOnly_metrics WEX.cornerNeg cornerNeg_litOnly).2.1, ← cornerNegProg_eq_litProg,
    Nat.zero_mul, Nat.add_zero]

theorem b15_rec_eq : WideBank8.Fast16.fblockRec b15 = 67072 + ECDSAAdd.measurementCount cornerA2Prog := by
  have hg := WideBank8.Row16.corner_geo
  obtain ⟨hl1, -⟩ := WideBank8.geo_lay2 WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok (.unit WideBank8.Row16.corner.u₁) hg.1
  obtain ⟨hl2, ht2⟩ := WideBank8.geo_lay2 WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok (.unit WideBank8.Row16.corner.u₂) hg.2.1
  have hp1 : WideBank8.Row16.corner.u₁.pre = Rows.code r16 WEX.cornerPre₁ := rfl
  have hp2 : WideBank8.Row16.corner.u₂.pre = Rows.code r16 WEX.cornerA2 := rfl
  have hbl : WideBank8.Fast16.bank15.bits.length = 16 := rfl
  have hcr1 : codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
      (normalizeW WideBank8.Row16.corner.u₁.pre) = 65535 := by
    rw [codeRecords_eq _ _ _ _ hl1, literalRecords_normalize, traversals_normalize, hp1, hbl,
      (WideBank8.Counts.lift_metrics r16 _).2.1, (WideBank8.Counts.lift_metrics r16 _).2.2,
      WEX.cornerPre₁, literalRecords_append, traversals_append,
      (litOnly_metrics WEX.cornerA1 cornerA1_litOnly).1, (litOnly_metrics WEX.cornerA1 cornerA1_litOnly).2.1,
      ← cornerA1Prog_eq_litProg, cornerA1Prog_meas,
      literalRecords_lookup_singleton, traversals_lookup_singleton]
    decide
  have hcr2 : codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot
      (normalizeW WideBank8.Row16.corner.u₂.pre) = ECDSAAdd.measurementCount cornerA2Prog := by
    rw [codeRecords_eq _ _ _ _ hl2, literalRecords_normalize, traversals_normalize, hp2,
      (WideBank8.Counts.lift_metrics r16 _).2.1, (WideBank8.Counts.lift_metrics r16 _).2.2,
      (litOnly_metrics WEX.cornerA2 cornerA2_litOnly).1, (litOnly_metrics WEX.cornerA2 cornerA2_litOnly).2.1,
      ← cornerA2Prog_eq_litProg, Nat.zero_mul, Nat.add_zero]
  have hgd : WideBank8.Row16.corner.gd.length = 256 := by
    have h : WideBank8.Row16.corner.gd = clearData (Rows.ports r16 (yPorts probeRows)) := rfl
    rw [h]; simp [clearData, Rows.ports, yPorts_length]
  have hcp2 : WideBank8.Row16.corner.u₂.clear.ports.length = 771 := by
    have h0 : WideBank8.Row16.corner.u₂.clear.ports = Rows.ports r16 (scrDPorts probeRows) := rfl
    have h := congrArg List.length (scrDPorts_targets probeRows)
    have hs : scrAllWires.length = 771 := by
      have h1 := scrPairWires_length; have h2 := scrShortWires_length
      have h3 : scrDExtraWires.length = 255 := by rw [scrDExtraWires_explicit]; simp
      simp [scrAllWires, scrWires, h1, h2, h3]
    rw [h0, Rows.ports, List.length_map]; simpa [portTargets, hs] using h
  have hru := (MeasuredClear.recordUnary_counts _ _ _ ht2 0).1
  rw [WideBank8.Fast16.bank_tree_nodes] at hru
  have hlhs : WideBank8.Fast16.fblockRec b15 = 65535 + (256 + (ECDSAAdd.measurementCount cornerA2Prog + (771 + (255 + 255)))) :=
    (congrArg WideBank8.Fast16.fblockRec (show b15 = .pair WideBank8.Row16.corner from rfl)).trans
      ((fblockRec_pair WideBank8.Row16.corner).trans
        (congrArg₂ (· + ·) hcr1 (congrArg₂ (· + ·) hgd (congrArg₂ (· + ·) hcr2 (congrArg₂ (· + ·) hcp2 (congrArg (· + 255) hru))))))
  exact hlhs.trans (b15_rec_arith _)

private theorem frecs_4 {n} (a b c d : WideBank8.Fast16.FBlock2 n) :
    WideBank8.Fast16.frecs [a, b, c, d] =
      WideBank8.Fast16.fblockRec a + WideBank8.Fast16.fblockRec b +
      WideBank8.Fast16.fblockRec c + WideBank8.Fast16.fblockRec d := by
  simp only [WideBank8.Fast16.frecs, Nat.add_zero, Nat.add_assoc]

private theorem fcodeTP_4 {n} (a b c d : WideBank8.Fast16.FBlock2 n) :
    WideBank8.Fast16.fcodeTP [a, b, c, d] =
      WideBank8.Fast16.fblockTP a + WideBank8.Fast16.fblockTP b +
      WideBank8.Fast16.fblockTP c + WideBank8.Fast16.fblockTP d := by
  simp only [WideBank8.Fast16.fcodeTP, Nat.add_zero, Nat.add_assoc]

theorem b12_b15_rec_diff : WideBank8.Fast16.frecs cornerBlocks = cornerRec + 24518 := by
  have h1 : WideBank8.Fast16.frecs cornerBlocks =
      WideBank8.Fast16.fblockRec b12 + WideBank8.Fast16.fblockRec b13 +
      WideBank8.Fast16.fblockRec b14 + WideBank8.Fast16.fblockRec b15 :=
    (congrArg WideBank8.Fast16.frecs (show cornerBlocks = [b12, b13, b14, b15] from rfl)).trans (frecs_4 b12 b13 b14 b15)
  have hm0 : mLit0 = ECDSAAdd.measurementCount pair2Prog + ECDSAAdd.measurementCount cornerNegProg := by
    rw [mLit0]; exact lit0_meas
  have hm2b : mLit2b = ECDSAAdd.measurementCount cornerA2Prog := by
    rw [mLit2b]; exact lit2b_meas
  have hrec_arith (m1 m2 m3 : Nat) :
      34301 + m1 + 0 + m2 + (67072 + m3) = 76855 + (m1 + m2) + m3 + 24518 := by omega
  rw [h1, b12_rec_eq, b13_rec_eq, b14_rec_eq, b15_rec_eq, hm0, hm2b]
  exact hrec_arith _ _ _

theorem b12_tp_eq :
    WideBank8.Fast16.fblockTP b12 = 33781 + ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram pair2Prog) := by
  have hg := (WideBank8.Row16.geometry b12 (mem_corner_code _ (by simp [cornerBlocks]))).1
  have hsw : ECDSAAdd.toffoliCount (WideBank8.Row16.fast1 WEXFast.site2F).swapNet = 512 := by
    have hp : (WideBank8.Row16.fast1 WEXFast.site2F).site.ports = Rows.ports r16 (site2Ports probeRows) := rfl
    have hplen : (WideBank8.Row16.fast1 WEXFast.site2F).site.ports.length = 512 := by
      rw [hp, Rows.ports, List.length_map]; exact site2Ports_length probeRows
    exact (WideBank8.Fast16.FastSite1.swapNet_toff _ hg).trans hplen
  have ha_eq : (WideBank8.Row16.fast1 WEXFast.site2F).site.arithmetic = Rows.code r16 (wLiteral pair2Prog) := rfl
  have hlt : literalToffolis (normalizeW (WideBank8.Row16.fast1 WEXFast.site2F).site.arithmetic) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram pair2Prog) := by
    rw [ha_eq, WideBank8.Counts.lift_normal_metrics]
    exact literalToffolis_wLiteral pair2Prog
  have htr : traversals (WideBank8.Row16.fast1 WEXFast.site2F).site.arithmetic = 0 := by
    rw [ha_eq, (WideBank8.Counts.lift_metrics r16 _).2.2]
    exact traversals_wLiteral pair2Prog
  have hlhs : WideBank8.Fast16.fblockTP b12 =
      32767 + 512 + (ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram pair2Prog) + 0 * 65535) + 502 :=
    (congrArg WideBank8.Fast16.fblockTP (show b12 = .fast1 (WideBank8.Row16.fast1 WEXFast.site2F) from rfl)).trans
      ((fblockTP_fast1 (WideBank8.Row16.fast1 WEXFast.site2F)).trans
        (congrArg (· + 502) (congrArg₂ (· + ·) (congrArg (32767 + ·) hsw) (congrArg₂ (· + ·) hlt (congrArg (· * 65535) htr)))))
  exact hlhs.trans (b12_tp_arith _)

theorem b13_tp_eq :
    WideBank8.Fast16.fblockTP b13 = ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram (ECDSAAdd.Frontier.zrep streamLayout)) := by
  have hex : PoolHost.hostCodeExtra (Rows.code r16 (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))) = 0 :=
    (PoolHost.hostCodeExtra_rows r16 _).trans (PoolHost.hostCodeExtra_zero_of_avoidsB _ PoolHost.zrep_avoidsB)
  rw [b13, fblockTP_plain, hex, WideBank8.Counts.lift_normal_metrics, (WideBank8.Counts.lift_metrics r16 _).2.2,
    literalToffolis_wLiteral, traversals_wLiteral, Nat.zero_mul, Nat.add_zero]

private theorem plain_tp_arith (t k : Nat) : t + 0 * k + 0 = t := by simp

theorem b14_tp_eq :
    WideBank8.Fast16.fblockTP b14 = ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerNegProg) := by
  have hex : PoolHost.hostCodeExtra (Rows.code r16 WEX.cornerNeg) = 0 :=
    (PoolHost.hostCodeExtra_rows r16 _).trans (PoolHost.hostCodeExtra_zero_of_avoidsB _ PoolHost.cornerNeg_avoidsB)
  have h1 : literalToffolis (normalizeW (Rows.code r16 WEX.cornerNeg)) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerNegProg) := by
    rw [WideBank8.Counts.lift_normal_metrics, (litOnly_metrics WEX.cornerNeg cornerNeg_litOnly).2.2.1, ← cornerNegProg_eq_litProg]
  have h2 : traversals (Rows.code r16 WEX.cornerNeg) = 0 := by
    rw [(WideBank8.Counts.lift_metrics r16 _).2.2, (litOnly_metrics WEX.cornerNeg cornerNeg_litOnly).1]
  have h3 : WideBank8.Fast16.fblockTP b14 =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerNegProg) +
        0 * (2 ^ WideBank8.Fast16.bank15.bits.length - 1) + 0 :=
    (congrArg WideBank8.Fast16.fblockTP (show b14 = .std (.plain (Rows.code r16 WEX.cornerNeg)) from rfl)).trans
      ((fblockTP_plain (Rows.code r16 WEX.cornerNeg)).trans
        (congrArg₂ (· + ·) (congrArg₂ (· + ·) h1 (congrArg (· * _) h2)) hex))
  exact h3.trans (plain_tp_arith _ _)

theorem b15_tp_eq :
    WideBank8.Fast16.fblockTP b15 =
      66037 + ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA1Prog) +
        ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA2Prog) := by
  have hp1 : WideBank8.Row16.corner.u₁.pre = Rows.code r16 WEX.cornerPre₁ := rfl
  have hp2 : WideBank8.Row16.corner.u₂.pre = Rows.code r16 WEX.cornerA2 := rfl
  have hbl : WideBank8.Fast16.bank15.bits.length = 16 := rfl
  have hlt1 : literalToffolis (normalizeW WideBank8.Row16.corner.u₁.pre) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA1Prog) := by
    rw [hp1, WideBank8.Counts.lift_normal_metrics, WEX.cornerPre₁, normalize_append, literalToffolis_append,
      (litOnly_metrics WEX.cornerA1 cornerA1_litOnly).2.2.1, ← cornerA1Prog_eq_litProg,
      literalToffolis_lookup_singleton, Nat.zero_add]
  have htr1 : traversals WideBank8.Row16.corner.u₁.pre = 1 := by
    rw [hp1, (WideBank8.Counts.lift_metrics r16 _).2.2, WEX.cornerPre₁, traversals_append,
      (litOnly_metrics WEX.cornerA1 cornerA1_litOnly).1, traversals_lookup_singleton, Nat.add_zero]
  have hlt2 : literalToffolis (normalizeW WideBank8.Row16.corner.u₂.pre) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA2Prog) := by
    rw [hp2, WideBank8.Counts.lift_normal_metrics, (litOnly_metrics WEX.cornerA2 cornerA2_litOnly).2.2.1,
      ← cornerA2Prog_eq_litProg]
  have htr2 : traversals WideBank8.Row16.corner.u₂.pre = 0 := by
    rw [hp2, (WideBank8.Counts.lift_metrics r16 _).2.2, (litOnly_metrics WEX.cornerA2 cornerA2_litOnly).1]
  have hnd : (tableAddressTree WideBank8.Fast16.bank15.high 0 1).internalNodes = 255 := WideBank8.Fast16.high_nodes
  have hlhs : WideBank8.Fast16.fblockTP b15 =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA1Prog) + 1 * (2 ^ 16 - 1) +
        (ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram cornerA2Prog) + 0 * (2 ^ 16 - 1) + (255 + 247)) :=
    (congrArg WideBank8.Fast16.fblockTP (show b15 = .pair WideBank8.Row16.corner from rfl)).trans
      ((fblockTP_pair WideBank8.Row16.corner).trans
        (congrArg₂ (· + ·)
          (congrArg₂ (· + ·) hlt1 (congrArg₂ (· * ·) htr1 (congrArg (fun k => 2 ^ k - 1) hbl)))
          (congrArg₂ (· + ·) (congrArg₂ (· + ·) hlt2 (congrArg₂ (· * ·) htr2 (congrArg (fun k => 2 ^ k - 1) hbl)))
            (congrArg (· + 247) hnd))))
  exact hlhs.trans (b15_tp_arith _ _)

theorem b12_b15_tp_diff : WideBank8.Fast16.fcodeTP cornerBlocks = cornerTP + 23997 := by
  have h1 : WideBank8.Fast16.fcodeTP cornerBlocks =
      WideBank8.Fast16.fblockTP b12 + WideBank8.Fast16.fblockTP b13 +
      WideBank8.Fast16.fblockTP b14 + WideBank8.Fast16.fblockTP b15 :=
    (congrArg WideBank8.Fast16.fcodeTP (show cornerBlocks = [b12, b13, b14, b15] from rfl)).trans (fcodeTP_4 b12 b13 b14 b15)
  have hl0 : ECDSAAdd.toffoliCount lit0Norm = ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram lit0) :=
    congrArg ECDSAAdd.toffoliCount (by unfold lit0Norm; rfl)
  have hl1 : ECDSAAdd.toffoliCount lit1Norm = ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram lit1) :=
    congrArg ECDSAAdd.toffoliCount (by unfold lit1Norm; rfl)
  have hl2a : ECDSAAdd.toffoliCount lit2aNorm = ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram lit2a) :=
    congrArg ECDSAAdd.toffoliCount (by unfold lit2aNorm; rfl)
  have hl2b : ECDSAAdd.toffoliCount lit2bNorm = ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram lit2b) :=
    congrArg ECDSAAdd.toffoliCount (by unfold lit2bNorm; rfl)
  rw [h1, b12_tp_eq, b13_tp_eq, b14_tp_eq, b15_tp_eq, hl0, hl1, hl2a, hl2b]
  exact b12_b15_tp_arith _ _ _ _ _ _ _ _ _ CornerFast.norm_toff_split_corner

theorem newRow_rec :
    WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + Site1Wire.Wide16.site1Rec +
      WideBank8.Fast16.frecs midW + cornerRec + WideBank8.Fast16.frecs tailW = 1703386 := by
  have hrest : WideBank8.Fast16.frecs Site1Wire.Wide16.restW =
      WideBank8.Fast16.frecs midW + (cornerRec + 24518) + WideBank8.Fast16.frecs tailW :=
    (congrArg WideBank8.Fast16.frecs restW_split).trans
      ((frecs_append (midW ++ cornerBlocks) tailW).trans
        (congrArg (· + WideBank8.Fast16.frecs tailW)
          ((frecs_append midW cornerBlocks).trans
            (congrArg (WideBank8.Fast16.frecs midW + ·) b12_b15_rec_diff))))
  have h := (congrArg (WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 +
    Site1Wire.Wide16.site1Rec + ·) hrest).symm.trans Site1Wire.Wide16.newRow_rec
  exact newRow_rec_arith _ _ _ _ _ _ h

private theorem row_cast6 (s a b c d e f n : Nat) (h : a + b + c + d + e + f = n) :
    s + a + b + c + d + e + f = s + n := by omega

def rowProg (start : Nat) : Straight 65536 start (start + 1703386) :=
  castFinish (row_cast6 start _ _ _ _ _ _ 1703386 newRow_rec)
    ((((WideBank8.Fast16.fblockProg b0 start).append
        (WideBank8.Fast16.fblockProg b1 (start + WideBank8.Fast16.fblockRec b0))).append
      ((Site1Wire.Wide16.twoPassProg (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1)).append
        (WideBank8.Fast16.fprog midW (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + Site1Wire.Wide16.site1Rec)))).append
      ((cornerFusedProg (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + Site1Wire.Wide16.site1Rec + WideBank8.Fast16.frecs midW)).append
        (WideBank8.Fast16.fprog tailW (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + Site1Wire.Wide16.site1Rec + WideBank8.Fast16.frecs midW + cornerRec))))

def rowSrc (read : ConstantBit 65536 → Bool) : AdaptiveCircuit :=
  (((WideBank8.Fast16.fblockSrc read b0).seq (WideBank8.Fast16.fblockSrc read b1)).seq
    ((Site1Wire.Wide16.twoPassSrc read).seq (WideBank8.Fast16.fsrc read midW))).seq
    ((cornerFusedSrc read).seq (WideBank8.Fast16.fsrc read tailW))

theorem rowProg_run (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rowProg start).instantiate read h).run = (rowSrc read).run := by
  rw [rowProg, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h1 => by
      rw [append_run_fixed _ _ _ _ _ (fun h2 => WideBank8.Fast16.fprog_run read tailW _ h2),
        AdaptiveCircuit.run_seq, cornerFused_run read _ h1, ← AdaptiveCircuit.run_seq]),
    AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h1 => by
      rw [append_run_fixed _ _ _ _ _ (fun h2 => WideBank8.Fast16.fprog_run read midW _ h2),
        AdaptiveCircuit.run_seq, Site1Wire.Wide16.twoPass_run read _ h1, ← AdaptiveCircuit.run_seq]),
    AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h1 => WideBank8.Fast16.fblockProg_run read b1 _ h1),
    AdaptiveCircuit.run_seq, WideBank8.Fast16.fblockProg_run read b0 _ h]
  simp only [rowSrc, AdaptiveCircuit.run_seq]

local notation "rowTP16C" => (WideBank8.Fast16.fcodeTP WideBank8.Row16.code - 15098 - 23997)

theorem rowTP_eq :
    WideBank8.Fast16.fblockTP b0 + WideBank8.Fast16.fblockTP b1 +
      (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 +
        ECDSAAdd.toffoliCount tailNorm + (255 + 247)) +
      WideBank8.Fast16.fcodeTP midW + cornerTP + WideBank8.Fast16.fcodeTP tailW = rowTP16C := by
  have hrest : WideBank8.Fast16.fcodeTP Site1Wire.Wide16.restW =
      WideBank8.Fast16.fcodeTP midW + (cornerTP + 23997) + WideBank8.Fast16.fcodeTP tailW :=
    (congrArg WideBank8.Fast16.fcodeTP restW_split).trans
      ((fcodeTP_append (midW ++ cornerBlocks) tailW).trans
        (congrArg (· + WideBank8.Fast16.fcodeTP tailW)
          ((fcodeTP_append midW cornerBlocks).trans
            (congrArg (WideBank8.Fast16.fcodeTP midW + ·) b12_b15_tp_diff))))
  have h := (congrArg (WideBank8.Fast16.fblockTP b0 + WideBank8.Fast16.fblockTP b1 +
    (16383 + 774 + ECDSAAdd.toffoliCount shortNorm + 32767 + 513 +
      ECDSAAdd.toffoliCount tailNorm + (255 + 247)) + ·) hrest).symm.trans Site1Wire.Wide16.rowTP_eq
  exact rowTP_arith _ _ _ _ _ _ _ _ h

private theorem tcount_mul7_6 (a b c d e f t : Nat) (h : a + b + c + d + e + f = t) :
    ((7 * a + 7 * b) + (7 * c + 7 * d)) + (7 * e + 7 * f) = 7 * t := by omega

theorem rowProg_tCount (read : ConstantBit 65536 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rowProg start).instantiate read h).tCount = 7 * rowTP16C := by
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split_corner]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split_corner]; simp)
  have hgm : ∀ b ∈ midW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_midW_code b hb)
  have hgt : ∀ b ∈ tailW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_tailW_code b hb)
  rw [rowProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h1 => by
      rw [append_tCount_fixed _ _ _ _ _ (fun h2 => WideBank8.Fast16.fprog_tCount read tailW hgt _ h2),
        cornerFused_tCount read _ h1]),
    append_tCount_fixed _ _ _ _ _ (fun h1 => by
      rw [append_tCount_fixed _ _ _ _ _ (fun h2 => WideBank8.Fast16.fprog_tCount read midW hgm _ h2),
        Site1Wire.Wide16.twoPass_tCount read _ h1]),
    append_tCount_fixed _ _ _ _ _ (fun h1 => WideBank8.Fast16.fblock_tCount read b1 hg1 _ h1),
    WideBank8.Fast16.fblock_tCount read b0 hg0 start h]
  exact tcount_mul7_6 _ _ _ _ _ _ _ rowTP_eq

theorem rowProg_residue (start : Nat) : AndGadget.residue (rowProg start) = 0 := by
  have hbr (b : WideBank8.Fast16.FBlock2 65536) (s : Nat) : AndGadget.residue (WideBank8.Fast16.fblockProg b s) = 0 := by
    have h := WideBank8.Fast16.fprog_residue [b] s
    rw [WideBank8.Fast16.fprog, AndGadget.residue_cast, AndGadget.residue_append] at h; omega
  rw [rowProg, AndGadget.residue_cast, AndGadget.residue_append, AndGadget.residue_append,
    AndGadget.residue_append, AndGadget.residue_append, AndGadget.residue_append,
    hbr, hbr, Site1Wire.Wide16.twoPass_residue, WideBank8.Fast16.fprog_residue,
    cornerFused_residue, WideBank8.Fast16.fprog_residue]

theorem rowProg_credit (start : Nat) : ProgramCredit (rowProg start) rowTP16C := by
  have hz := rowProg_residue start
  refine ⟨hz, ?_⟩
  have he := exact_t (rowProg start) hz (fun _ => false) (fun _ => false)
  have ht := rowProg_tCount (fun _ => false) start (fun _ => false)
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7) (he.symm.trans ht)

theorem rowProg_wellFormed (start : Nat) : (rowProg start).WellFormed := by
  have hphys : ∀ p, WInstr.literal p ∈ erase2 (WideBank8.Fast16.fforget WideBank8.Row16.code) → GatePhysical p := by
    rw [WideBank8.Row16.forget]; exact Geometry.row_physical .w16
  have hp_sub (b : WideBank8.Fast16.FBlock2 65536) (hb : b ∈ WideBank8.Row16.code) :
      ∀ p, WInstr.literal p ∈ erase2 b.forgetL → GatePhysical p := fun p hp =>
    hphys p (by
      rw [WideBank8.Fast16.fforget, erase2]
      have h1 : b.forgetL ⊆ WideBank8.Fast16.fforget WideBank8.Row16.code := fun x hx => List.mem_flatMap.mpr ⟨b, hb, hx⟩
      obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
      exact List.mem_flatMap.mpr ⟨d, h1 hd, hdp⟩)
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split_corner]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split_corner]; simp)
  have hgm : ∀ b ∈ midW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_midW_code b hb)
  have hgt : ∀ b ∈ tailW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_tailW_code b hb)
  rw [rowProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _
    (straight_append_wellFormed _ _
      (straight_append_wellFormed _ _
        (WideBank8.Fast16.fblock_wellFormed b0 hg0 (hp_sub b0 (by rw [code_split_corner]; simp)) start)
        (WideBank8.Fast16.fblock_wellFormed b1 hg1 (hp_sub b1 (by rw [code_split_corner]; simp)) _))
      (straight_append_wellFormed _ _ (Site1Wire.Wide16.twoPass_wellFormed _)
        (WideBank8.Fast16.fprog_wellFormed midW hgm (fun p hp => by
          obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp; obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
          exact hp_sub b (mem_midW_code b hb) p (List.mem_flatMap.mpr ⟨d, hdb, hdp⟩)) _)))
    (straight_append_wellFormed _ _ (cornerFused_wellFormed _)
      (WideBank8.Fast16.fprog_wellFormed tailW hgt (fun p hp => by
        obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp; obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
        exact hp_sub b (mem_tailW_code b hb) p (List.mem_flatMap.mpr ⟨d, hdb, hdp⟩)) _))

theorem rowProg_support (start : Nat) :
    ChallengeMigration.straightWires (rowProg start) ⊆ WideBank8.Fast16.Tight.support := by
  have hsup_orig := WideBank8.Fast16.Tight.row_program_support start
  rw [WideBank8.Row16.program, code_split_corner, WideBank8.Fast16.fprog, support_cast, straightWires_append] at hsup_orig
  have hs0 : ChallengeMigration.straightWires (WideBank8.Fast16.fblockProg b0 start) ⊆ WideBank8.Fast16.Tight.support :=
    (List.append_subset.mp hsup_orig).1
  have htail1 := (List.append_subset.mp hsup_orig).2
  rw [WideBank8.Fast16.fprog, support_cast, straightWires_append] at htail1
  have hs1 : ChallengeMigration.straightWires (WideBank8.Fast16.fblockProg b1 (start + WideBank8.Fast16.fblockRec b0)) ⊆ WideBank8.Fast16.Tight.support :=
    (List.append_subset.mp htail1).1
  have hsub_sup (c : WideBank8.Fast16.FCode2 65536) (hmem : ∀ b ∈ c, b ∈ WideBank8.Row16.code) (s : Nat) :
      ChallengeMigration.straightWires (WideBank8.Fast16.fprog c s) ⊆ WideBank8.Fast16.Tight.support := by
    have hf_sub : ∀ x ∈ erase2 (WideBank8.Fast16.fforget c), x ∈ erase2 (WideBank8.Fast16.fforget WideBank8.Row16.code) := fun x hx => by
      obtain ⟨d, hd, hdx⟩ := List.mem_flatMap.mp hx; obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
      exact List.mem_flatMap.mpr ⟨d, List.mem_flatMap.mpr ⟨b, hmem b hb, hdb⟩, hdx⟩
    exact WideBank8.Fast16.Tight.fprog_support c (fun b hb => WideBank8.Row16.geometry b (hmem b hb))
      (fun p hp => WideBank8.Fast16.Tight.row_literals p (hf_sub _ hp))
      (fun b hb => WideBank8.Row16.strict b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl3 b (hmem b hb))
      (fun b hb => WideBank8.Row16.ctl4 b (hmem b hb))
      (fun c ps hp => WideBank8.Fast16.Tight.row_lookups c ps (hf_sub _ hp))
      (fun b hb => WideBank8.Fast16.Tight.row_nohost b (hmem b hb)) s
  rw [rowProg, support_cast, straightWires_append, straightWires_append, straightWires_append,
    straightWires_append, straightWires_append]
  exact List.append_subset.mpr ⟨
    List.append_subset.mpr ⟨List.append_subset.mpr ⟨hs0, hs1⟩,
      List.append_subset.mpr ⟨Site1Wire.Wide16.twoPass_support _, hsub_sup midW mem_midW_code _⟩⟩,
    List.append_subset.mpr ⟨cornerFused_support _, hsub_sup tailW mem_tailW_code _⟩⟩

private theorem codeSP2_split6 {n} (B : PathShare.Bank) (c0 c1 c2 cM cC cT : Code2 n) :
    WideBank8.codeSP2 B (c0 ++ (c1 ++ (c2 ++ ((cM ++ cC) ++ cT)))) =
      WideBank8.codeSP2 B c0 + WideBank8.codeSP2 B c1 + WideBank8.codeSP2 B c2 +
      WideBank8.codeSP2 B cM + WideBank8.codeSP2 B cC + WideBank8.codeSP2 B cT := by
  simp only [WideBank8.Fast16.codeSP2_append]; omega

private theorem fslack_split6 {n} (x0 x1 x2 : WideBank8.Fast16.FBlock2 n)
    (m c t : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.fslack (x0 :: x1 :: x2 :: (m ++ c ++ t)) =
      WideBank8.Fast16.fblockSlack x0 + WideBank8.Fast16.fblockSlack x1 + WideBank8.Fast16.fblockSlack x2 +
      WideBank8.Fast16.fslack m + WideBank8.Fast16.fslack c + WideBank8.Fast16.fslack t := by
  simp only [WideBank8.Fast16.fslack, fslack_append]; omega

private theorem fcodeTP_split6 {n} (x0 x1 x2 : WideBank8.Fast16.FBlock2 n)
    (m c t : WideBank8.Fast16.FCode2 n) :
    WideBank8.Fast16.fcodeTP (x0 :: x1 :: x2 :: (m ++ c ++ t)) =
      WideBank8.Fast16.fblockTP x0 + WideBank8.Fast16.fblockTP x1 + WideBank8.Fast16.fblockTP x2 +
      WideBank8.Fast16.fcodeTP m + WideBank8.Fast16.fcodeTP c + WideBank8.Fast16.fcodeTP t := by
  simp only [WideBank8.Fast16.fcodeTP, fcodeTP_append]; omega

theorem rowProg_slots (start : Nat) : (rowProg start).gateSlots ≤ 4250000000 := by
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split_corner]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split_corner]; simp)
  have hgm : ∀ b ∈ midW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_midW_code b hb)
  have hgt : ∀ b ∈ tailW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_tailW_code b hb)
  have hs0 := WideBank8.Fast16.fprog_slots [b0] (fun b hb => by simp at hb; subst hb; exact hg0) start
  rw [WideBank8.Fast16.fprog, castFinish_gateSlots, Straight.gateSlots_append] at hs0
  simp only [WideBank8.Fast16.fprog, Straight.gateSlots, WideBank8.Fast16.fforget, WideBank8.Fast16.fslack,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero] at hs0
  have hs1 := WideBank8.Fast16.fprog_slots [b1] (fun b hb => by simp at hb; subst hb; exact hg1)
    (start + WideBank8.Fast16.fblockRec b0)
  rw [WideBank8.Fast16.fprog, castFinish_gateSlots, Straight.gateSlots_append] at hs1
  simp only [WideBank8.Fast16.fprog, Straight.gateSlots, WideBank8.Fast16.fforget, WideBank8.Fast16.fslack,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero] at hs1
  have hsm := WideBank8.Fast16.fprog_slots midW hgm
    (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + Site1Wire.Wide16.site1Rec)
  have hst := WideBank8.Fast16.fprog_slots tailW hgt
    (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 + Site1Wire.Wide16.site1Rec +
      WideBank8.Fast16.frecs midW + cornerRec)
  have htp := Site1Wire.Wide16.twoPass_slots (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1)
  have hcf := cornerFused_slots (start + WideBank8.Fast16.fblockRec b0 + WideBank8.Fast16.fblockRec b1 +
    Site1Wire.Wide16.site1Rec + WideBank8.Fast16.frecs midW)
  have hsp_split :
      WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget WideBank8.Row16.code) =
        WideBank8.codeSP2 WideBank8.Fast16.bank15 Site1Wire.Wide16.b0.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 Site1Wire.Wide16.b1.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 Site1Wire.Wide16.b2.forgetL +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget midW) +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget cornerBlocks) +
        WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget tailW) := by
    have hff : WideBank8.Fast16.fforget WideBank8.Row16.code =
        Site1Wire.Wide16.b0.forgetL ++ (Site1Wire.Wide16.b1.forgetL ++ (Site1Wire.Wide16.b2.forgetL ++
          ((WideBank8.Fast16.fforget midW ++ WideBank8.Fast16.fforget cornerBlocks) ++ WideBank8.Fast16.fforget tailW))) :=
      (congrArg WideBank8.Fast16.fforget code_split_corner).trans
        ((WideBank8.Fast16.fforget_cons b0 _).trans
          (congrArg (Site1Wire.Wide16.b0.forgetL ++ ·)
            ((WideBank8.Fast16.fforget_cons b1 _).trans
              (congrArg (Site1Wire.Wide16.b1.forgetL ++ ·)
                ((WideBank8.Fast16.fforget_cons b2 _).trans
                  (congrArg (Site1Wire.Wide16.b2.forgetL ++ ·)
                    ((WideBank8.Fast16.fforget_append (midW ++ cornerBlocks) tailW).trans
                      (congrArg (· ++ WideBank8.Fast16.fforget tailW)
                        (WideBank8.Fast16.fforget_append midW cornerBlocks)))))))))
    exact (congrArg (WideBank8.codeSP2 WideBank8.Fast16.bank15) hff).trans
      (codeSP2_split6 WideBank8.Fast16.bank15 Site1Wire.Wide16.b0.forgetL Site1Wire.Wide16.b1.forgetL
        Site1Wire.Wide16.b2.forgetL (WideBank8.Fast16.fforget midW)
        (WideBank8.Fast16.fforget cornerBlocks) (WideBank8.Fast16.fforget tailW))
  have hsl_split :
      WideBank8.Fast16.fslack WideBank8.Row16.code =
        WideBank8.Fast16.fblockSlack b0 + WideBank8.Fast16.fblockSlack b1 + WideBank8.Fast16.fblockSlack b2 +
        WideBank8.Fast16.fslack midW + WideBank8.Fast16.fslack cornerBlocks + WideBank8.Fast16.fslack tailW :=
    (congrArg WideBank8.Fast16.fslack code_split_corner).trans (fslack_split6 b0 b1 b2 midW cornerBlocks tailW)
  have hsp_all : WideBank8.codeSP2 WideBank8.Fast16.bank15 (WideBank8.Fast16.fforget WideBank8.Row16.code) ≤ 2139852392 :=
    (congrArg (WideBank8.codeSP2 WideBank8.Fast16.bank15) WideBank8.Row16.forget).trans_le WideBank8.Row16.standard_slots
  have hsl_all := WideBank8.Row16.slack
  have hlit_le := Site1Wire.site1_slots_le_rowC
  have hl0 := WEX.clearReferenceRow_literal_slots_bound
  have hm := WEXUnlookup.rowC_measures.2.2.1
  rw [rowProg, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append, Straight.gateSlots_append,
    Straight.gateSlots_append, Straight.gateSlots_append]
  have row_arith (g0 g1 gtp gm gcf gt spAll sp0 sp1 sp2 spM spC spT slAll sl0 sl1 sl2 slM slC slT gS L1 L0 : Nat)
      (h0 : g0 ≤ sp0 + sl0) (h1 : g1 ≤ sp1 + sl1) (hm' : gm ≤ spM + slM) (ht' : gt ≤ spT + slT)
      (htp' : gtp ≤ 4 * gS + 610000000) (hcf' : gcf ≤ 960000000)
      (hsp : spAll = sp0 + sp1 + sp2 + spM + spC + spT) (hspA : spAll ≤ 2139852392)
      (hsl : slAll = sl0 + sl1 + sl2 + slM + slC + slT) (hslA : slAll = 335556282)
      (hgS : gS ≤ L1) (hL0 : L0 ≤ 50021565) (hL1 : L1 ≤ L0 + 93082 + 513) :
      ((g0 + g1) + (gtp + gm)) + (gcf + gt) ≤ 4250000000 := by omega
  exact row_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hs0 hs1 hsm hst htp hcf hsp_split hsp_all hsl_split hsl_all hlit_le hl0 hm

-- Helper connecting `b0..b2 ++ midW` reference to `CornerFast.preSite2Code` and `cornerBlocks` reference to `origCornerRef`
private theorem pre_forget_eq :
    Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW =
      Rows.blocks r16 (CornerFast.preSite2Code.map toBlock2) := by
  have h1 : WideBank8.Fast16.fforget midW = Rows.blocks r16 ((CornerFast.generic3Pre probeRows).map toBlock2) := by
    rw [midW, WideBank8.Row16.fforget_lift]
    have hfg : WEXFast.fforget (WEXFast.fgeneric3.take 9) = (CornerFast.generic3Pre probeRows).map toBlock2 := by
      rfl
    rw [hfg]; rfl
  rw [h1, CornerFast.preSite2Code, List.map_append]
  simp only [Rows.blocks, List.map_append, List.append_assoc]
  rfl

private theorem cornerBlocks_ref_eq (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (a : Nat) :
    reference2 (readConstant coeffs Q) a (WideBank8.Fast16.fforget cornerBlocks) =
      origCornerRef (readConstant (fun _ : Fin 32768 => coeffs (r16 a)) Q) a := by
  have hf : WideBank8.Fast16.fforget cornerBlocks =
      Rows.blocks r16 ([Block2.unit (WEXFast.siteUnit (site2 probeRows)),
        .plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout)), .plain WEX.cornerNeg,
        .unit WEXUnlookup.cornerUnit₁, .unit WEXUnlookup.cornerUnit₂]) := by
    simp only [cornerBlocks, b12, b13, b14, b15, WideBank8.Fast16.fforget, WideBank8.Fast16.FBlock2.forgetL,
      WideBank8.Row16.fast1, WideBank8.Row16.corner, Rows.blocks, Rows.block,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_nil]; rfl
  rw [hf, Rows.reference_blocks]
  let read32 := readConstant (fun _ : Fin 32768 => coeffs (r16 a)) Q
  have hcn : (specialize WEX.cornerNeg a).instantiate read32 = cornerNegProg := by
    rw [WEX.cornerNeg_inst]; unfold cornerNegProg; rfl
  have hz : (specialize (wLiteral (ECDSAAdd.Frontier.zrep streamLayout)) a).instantiate read32 =
      ECDSAAdd.Frontier.zrep streamLayout := by
    simp only [wLiteral, specialize, WInstr.specialize, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Tmpl.instantiate_lit]
  have hs2 : (WEXFast.siteUnit (site2 probeRows)).code = (site2 probeRows).code := rfl
  have he : erase2 ([Block2.unit (WEXFast.siteUnit (site2 probeRows)),
        .plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout)), .plain WEX.cornerNeg,
        .unit WEXUnlookup.cornerUnit₁, .unit WEXUnlookup.cornerUnit₂]) =
      (site2 probeRows).code ++ (wLiteral (ECDSAAdd.Frontier.zrep streamLayout) ++
        (WEX.cornerNeg ++ (WEX.cornerUnit₁ ++ WEX.cornerUnit₂))) := by
    simp only [erase2_cons, erase2_nil, List.append_nil, Block2.code, hs2,
      WEXUnlookup.cornerUnit₁_code, WEXUnlookup.cornerUnit₂_code]
  rw [reference2, he, specialize_append, Tmpl.instantiate_append, specialize_append, Tmpl.instantiate_append,
    specialize_append, Tmpl.instantiate_append, hz, hcn, origCornerRef, List.append_assoc, List.append_assoc]

private theorem cornerBlocks_litRec :
    literalRecords (erase2 (WideBank8.Fast16.fforget cornerBlocks)) = mLit0 + mLit2b := by
  let c0 : PointCoeff := ⟨⟨0, order_prime.pos⟩, ⟨0, order_prime.pos⟩⟩
  have h := (specialize_counts (readConstant (fun _ : Fin 65536 => c0) 0)
    (erase2 (WideBank8.Fast16.fforget cornerBlocks)) 0).2
  change ECDSAAdd.measurementCount (reference2 (readConstant (fun _ : Fin 65536 => c0) 0) 0
    (WideBank8.Fast16.fforget cornerBlocks)) =
    literalRecords (erase2 (WideBank8.Fast16.fforget cornerBlocks)) at h
  rw [cornerBlocks_ref_eq, origCornerRef_meas] at h
  rw [← h, mLit0, lit0_meas, mLit2b, lit2b_meas]

private theorem fcodeClean_append_inv {n} (read : ConstantBit n → Bool) (a : Nat)
    (xs ys : WideBank8.Fast16.FCode2 n) (st : ECDSAAdd.State)
    (h : WideBank8.Fast16.FCodeClean read a (xs ++ ys) st) :
    WideBank8.Fast16.FCodeClean read a xs st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (reference2 read a (WideBank8.Fast16.fforget xs)) →
        WideBank8.Fast16.FCodeClean read a ys (ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget xs)) m st) := by
  induction xs generalizing st with
  | nil =>
    refine ⟨trivial, fun m hm => ?_⟩
    simp only [WideBank8.Fast16.fforget, List.flatMap_nil, reference2_nil, ECDSAAdd.measurementCount] at hm ⊢
    rw [List.eq_nil_of_length_eq_zero hm, Site1Fast.run_nil]; exact h
  | cons x xs ih =>
    rcases h with ⟨hx, hrest⟩
    refine ⟨⟨hx, fun m hm => (ih _ (hrest m hm)).1⟩, fun m hm => ?_⟩
    rw [WideBank8.Fast16.fforget_cons, reference2_append, ECDSAAdd.measurementCount_append] at hm
    rw [WideBank8.Fast16.fforget_cons, reference2_append, ECDSAAdd.run_append]
    have ht : (m.take (ECDSAAdd.measurementCount (reference2 read a x.forgetL))).length =
        ECDSAAdd.measurementCount (reference2 read a x.forgetL) := by rw [List.length_take]; omega
    have hd : (m.drop (ECDSAAdd.measurementCount (reference2 read a x.forgetL))).length =
        ECDSAAdd.measurementCount (reference2 read a (WideBank8.Fast16.fforget xs)) := by rw [List.length_drop]; omega
    exact (ih _ (hrest _ ht)).2 _ hd

private theorem fcode_addr {n} (read : ConstantBit n → Bool) (xs : WideBank8.Fast16.FCode2 n)
    (hg : ∀ b ∈ xs, WideBank8.Fast16.FBlockGeo b) (a : Nat) (st : ECDSAAdd.State)
    (ha : AddrValid WideBank8.Fast16.windowBits windowRoot a st)
    (hcl : WideBank8.Fast16.FCodeClean read a xs st) (m : List Bool)
    (hm : m.length = ECDSAAdd.measurementCount (reference2 read a (WideBank8.Fast16.fforget xs))) :
    AddrValid WideBank8.Fast16.windowBits windowRoot a (ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget xs)) m st) := by
  induction xs generalizing st m with
  | nil =>
    simp only [WideBank8.Fast16.fforget, List.flatMap_nil, reference2_nil, ECDSAAdd.measurementCount] at hm ⊢
    rw [List.eq_nil_of_length_eq_zero hm, Site1Fast.run_nil]; exact ha
  | cons x xs ih =>
    rw [WideBank8.Fast16.fforget_cons, reference2_append, ECDSAAdd.measurementCount_append] at hm
    rw [WideBank8.Fast16.fforget_cons, reference2_append, ECDSAAdd.run_append]
    have ht : (m.take (ECDSAAdd.measurementCount (reference2 read a x.forgetL))).length =
        ECDSAAdd.measurementCount (reference2 read a x.forgetL) := by rw [List.length_take]; omega
    have hd : (m.drop (ECDSAAdd.measurementCount (reference2 read a x.forgetL))).length =
        ECDSAAdd.measurementCount (reference2 read a (WideBank8.Fast16.fforget xs)) := by rw [List.length_drop]; omega
    exact ih (fun b hb => hg b (List.mem_cons_of_mem _ hb)) _
      (WideBank8.Fast16.fblock_addr read x (hg x List.mem_cons_self) a st ha hcl.1 _)
      (hcl.2 _ ht) _ hd

private theorem fblock_path_clean {n} (read : ConstantBit n → Bool)
    (b : WideBank8.Fast16.FBlock2 n) (hg : WideBank8.Fast16.FBlockGeo b)
    (hnp : ∀ code, b = .std (.plain code) → ∀ p, WInstr.literal p ∈ code → ∀ w ∈ WideBank8.Fast16.pathBank, w ∉ ECDSAAdd.wires p)
    (a : Nat) (st : ECDSAAdd.State)
    (hs : AddrValid WideBank8.Fast16.windowBits windowRoot a st)
    (hc : Clean WideBank8.Fast16.pathBank st.basis) (m : List Bool) :
    Clean WideBank8.Fast16.pathBank (ECDSAAdd.run (reference2 read a b.forgetL) m st).basis := by
  cases b with
  | std b =>
    cases b with
    | plain code =>
      rw [show (WideBank8.Fast16.FBlock2.std (.plain code)).forgetL = [.plain code] from rfl, WideBank8.Fast16.reference2_single]
      have hp : ∀ i ∈ code, PlacedPair WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot i := by
        intro i hi
        obtain ⟨p, rfl, hwb⟩ := hg i hi
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hwb w hw
        · exact hnp code rfl p hi w hw
      exact (strict_preserves read WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank code a hp st ⟨hc, hs.1, hs.2⟩ m).1
    | unit u =>
      rw [show (WideBank8.Fast16.FBlock2.std (.unit u)).forgetL = [.unit u] from rfl, WideBank8.Fast16.reference2_single]
      exact (strict_preserves read WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank u.code a hg.placed st ⟨hc, hs.1, hs.2⟩ m).1
  | fast f =>
    rw [show (WideBank8.Fast16.FBlock2.fast f).forgetL = [Block2.unit (WEXFast.siteUnit f.site)] from rfl, WideBank8.Fast16.reference2_single]
    have hp : ∀ i ∈ f.site.code, PlacedPair WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.1.site.placed i hi)
    exact (strict_preserves read WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank f.site.code a hp st ⟨hc, hs.1, hs.2⟩ m).1
  | fast1 f =>
    rw [show (WideBank8.Fast16.FBlock2.fast1 f).forgetL = [Block2.unit (WEXFast.siteUnit f.site)] from rfl, WideBank8.Fast16.reference2_single]
    have hp : ∀ i ∈ f.site.code, PlacedPair WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.1.site.placed i hi)
    exact (strict_preserves read WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank f.site.code a hp st ⟨hc, hs.1, hs.2⟩ m).1
  | pair q =>
    have hp : ∀ i ∈ erase2 ([Block2.unit q.u₁, Block2.unit q.u₂]),
        PlacedPair WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot i := by
      intro i hi
      rw [erase2_cons, erase2_cons, erase2_nil, List.append_nil, List.mem_append] at hi
      rcases hi with hi | hi
      · exact hg.1.placed i hi
      · exact hg.2.1.placed i hi
    exact (strict_preserves read WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank
      (erase2 ([Block2.unit q.u₁, Block2.unit q.u₂])) a hp st ⟨hc, hs.1, hs.2⟩ m).1

private theorem fcode_path_clean {n} (read : ConstantBit n → Bool) (xs : WideBank8.Fast16.FCode2 n)
    (hg : ∀ b ∈ xs, WideBank8.Fast16.FBlockGeo b)
    (hnp : ∀ b ∈ xs, ∀ code, b = .std (.plain code) → ∀ p, WInstr.literal p ∈ code → ∀ w ∈ WideBank8.Fast16.pathBank, w ∉ ECDSAAdd.wires p)
    (a : Nat) (st : ECDSAAdd.State)
    (ha : AddrValid WideBank8.Fast16.windowBits windowRoot a st)
    (hcl : WideBank8.Fast16.FCodeClean read a xs st)
    (hp : Clean WideBank8.Fast16.pathBank st.basis) (m : List Bool)
    (hm : m.length = ECDSAAdd.measurementCount (reference2 read a (WideBank8.Fast16.fforget xs))) :
    Clean WideBank8.Fast16.pathBank (ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget xs)) m st).basis := by
  induction xs generalizing st m with
  | nil =>
    simp only [WideBank8.Fast16.fforget, List.flatMap_nil, reference2_nil, ECDSAAdd.measurementCount] at hm ⊢
    rw [List.eq_nil_of_length_eq_zero hm, Site1Fast.run_nil]; exact hp
  | cons x xs ih =>
    rw [WideBank8.Fast16.fforget_cons, reference2_append, ECDSAAdd.measurementCount_append] at hm
    rw [WideBank8.Fast16.fforget_cons, reference2_append, ECDSAAdd.run_append]
    have ht : (m.take (ECDSAAdd.measurementCount (reference2 read a x.forgetL))).length =
        ECDSAAdd.measurementCount (reference2 read a x.forgetL) := by rw [List.length_take]; omega
    have hd : (m.drop (ECDSAAdd.measurementCount (reference2 read a x.forgetL))).length =
        ECDSAAdd.measurementCount (reference2 read a (WideBank8.Fast16.fforget xs)) := by rw [List.length_drop]; omega
    exact ih (fun b hb => hg b (List.mem_cons_of_mem _ hb))
      (fun b hb => hnp b (List.mem_cons_of_mem _ hb)) _
      (WideBank8.Fast16.fblock_addr read x (hg x List.mem_cons_self) a st ha hcl.1 _)
      (hcl.2 _ ht)
      (fblock_path_clean read x (hg x List.mem_cons_self) (hnp x List.mem_cons_self) a st ha hp _) _ hd

private theorem cornerBlocks_plain_avoid_path :
    ∀ b ∈ cornerBlocks, ∀ code, b = .std (.plain code) →
      ∀ p, WInstr.literal p ∈ code → ∀ w ∈ WideBank8.Fast16.pathBank, w ∉ ECDSAAdd.wires p := by
  intro b hb code hbc p hp w hw
  have hlit0 : w ∉ ECDSAAdd.wires lit0 :=
    lit0_avoid_window w (List.mem_append_right _ hw)
  rw [lit0] at hlit0
  simp only [ECDSAAdd.wires_append, Finset.mem_union, not_or] at hlit0
  have hz : w ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.zrep streamLayout) := hlit0.1.1.1.1.2
  have hcn : w ∉ ECDSAAdd.wires cornerNegProg := hlit0.1.1.1.2
  rw [cornerNegProg] at hcn
  simp only [ECDSAAdd.wires_append, Finset.mem_union, not_or] at hcn
  simp only [cornerBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · simp [b12] at hbc
  · simp only [b13, WideBank8.Fast16.FBlock2.std.injEq, Block2.plain.injEq] at hbc
    subst hbc
    simp only [Rows.code, Rows.instr, wLiteral, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, WInstr.literal.injEq] at hp
    subst hp; exact hz
  · simp only [b14, WideBank8.Fast16.FBlock2.std.injEq, Block2.plain.injEq] at hbc
    subst hbc
    simp only [WEX.cornerNeg, Rows.code, Rows.instr, wLiteral, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, WInstr.literal.injEq] at hp
    rcases hp with rfl | rfl | rfl
    · exact hcn.1
    · exact hcn.2.1
    · exact hcn.2.2
  · simp [b15] at hbc

theorem rowSrc_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (rowSrc (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  let read := readConstant coeffs Q
  have hg0 := WideBank8.Row16.geometry b0 (by rw [code_split_corner]; simp)
  have hg1 := WideBank8.Row16.geometry b1 (by rw [code_split_corner]; simp)
  have hg2 := WideBank8.Row16.geometry b2 (by rw [code_split_corner]; simp)
  have hgm : ∀ b ∈ midW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_midW_code b hb)
  have hgc : ∀ b ∈ cornerBlocks, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_corner_code b hb)
  have hgt : ∀ b ∈ tailW, WideBank8.Fast16.FBlockGeo b := fun b hb => WideBank8.Row16.geometry b (mem_tailW_code b hb)
  obtain ⟨c0, a0, m0⟩ := WideBank8.Fast16.fblock_sim read b0 hg0
  obtain ⟨c1, a1, m1⟩ := WideBank8.Fast16.fblock_sim read b1 hg1
  obtain ⟨c2, a2, m2⟩ := Site1Wire.Wide16.twoPass_sim read
  obtain ⟨cm, am, mm⟩ := WideBank8.Fast16.fsrc_sim read midW hgm
  obtain ⟨cc, ac, mc⟩ := cornerFused_sim coeffs Q
  obtain ⟨ct, at_, mt⟩ := WideBank8.Fast16.fsrc_sim read tailW hgt
  -- Combine `[b0, b1]`
  have h01_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL)) ∧
        ∀ a st, AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          WideBank8.Fast16.FBlockClean b0 st →
          (∀ m', m'.length = ECDSAAdd.measurementCount (reference2 read a Site1Wire.Wide16.b0.forgetL) →
            WideBank8.Fast16.FBlockClean b1 (ECDSAAdd.run (reference2 read a Site1Wire.Wide16.b0.forgetL) m' st)) →
          Safe2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL)) m st))
      ((WideBank8.Fast16.fblockSrc read b0).seq (WideBank8.Fast16.fblockSrc read b1)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c0 c1, ?_, by rw [simulationCoefficients_mass, m0, m1]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]; apply simulationAligned_seq a0 a1
    intro b₀ k₀ b₁ k₁ hb₀ hb₁
    obtain ⟨m₀, lm₀, r₀⟩ := hb₀; obtain ⟨m₁, lm₁, r₁⟩ := hb₁
    refine ⟨m₀ ++ m₁, by simp [erase2_append, List.length_append, lm₀, lm₁], ?_⟩
    intro a st ha hc0 hc1 hsafe
    have hm₀ : m₀.length = ECDSAAdd.measurementCount (reference2 read a Site1Wire.Wide16.b0.forgetL) :=
      lm₀.trans (specialize_counts read (erase2 Site1Wire.Wide16.b0.forgetL) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a Site1Wire.Wide16.b0.forgetL Site1Wire.Wide16.b1.forgetL st hsafe
    have ha1 := WideBank8.Fast16.fblock_addr read b0 hg0 a st ha hc0 m₀
    change b₁.kraus (b₀.kraus (Bridge.signedKet st)) = _
    rw [r₀ a st ha hc0 hsp.1, map_smul, r₁ a _ ha1 (hc1 m₀ hm₀) (hsp.2 m₀ hm₀),
      reference2_append, run_append_records _ _ m₀ m₁ st hm₀, smul_smul]
  -- Combine `[b2] ++ midW`
  have h2m_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)) ∧
        ∀ a st, AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          WideBank8.Fast16.FCodeClean read a (b2 :: midW) st →
          Clean streamLayout.dialogPool st.basis →
          Safe2 read a (Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)) m st))
      ((Site1Wire.Wide16.twoPassSrc read).seq (WideBank8.Fast16.fsrc read midW)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c2 cm, ?_, by rw [simulationCoefficients_mass, m2, mm]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]; apply simulationAligned_seq a2 am
    intro b₂ k₂ bm km hb₂ hbm
    obtain ⟨m₂, lm₂, r₂⟩ := hb₂; obtain ⟨mm', lmm', rm⟩ := hbm
    have h2_lit : literalRecords (erase2 Site1Wire.Wide16.b2.forgetL) = ECDSAAdd.measurementCount site1Arith := by
      have heq : erase2 Site1Wire.Wide16.b2.forgetL =
          [WInstr.lookup (some windowRoot) (Rows.ports r16 (sitePorts probeRows)), WInstr.literal site1Arith,
           WInstr.lookup (some windowRoot) (Rows.ports r16 (sitePorts probeRows))] := by
        simp [Site1Wire.Wide16.b2, WideBank8.Fast16.FBlock2.forgetL, erase2, Block2.code, UnitSite.code,
          Rows.unit, Rows.site, Rows.code, Rows.instr, site1, MaskedSite.prefix, wLiteral]
      rw [heq]; exact litRec_lookup_lit_lookup _ _ _ _ _
    have h2_ref (a : Nat) : reference2 read a Site1Wire.Wide16.b2.forgetL = (specialize Site1Wire.Wide16.site1_16.code a).instantiate read := by
      have hce : erase2 Site1Wire.Wide16.b2.forgetL = Site1Wire.Wide16.site1_16.code := by
        simp [Site1Wire.Wide16.b2, WideBank8.Fast16.FBlock2.forgetL, erase2, Block2.code, UnitSite.code,
          Rows.unit, Site1Wire.Wide16.site1_16, Rows.site, MaskedSite.code, MaskedSite.prefix, Rows.code, Rows.instr]
      rw [reference2, hce]
    refine ⟨m₂ ++ mm', by simp [erase2_append, List.length_append, h2_lit, lm₂, lmm'], ?_⟩
    intro a st ha hcl hpool hsafe
    have hm₂ : m₂.length = ECDSAAdd.measurementCount (reference2 read a Site1Wire.Wide16.b2.forgetL) := by
      rw [← h2_lit] at lm₂; exact lm₂.trans (specialize_counts read (erase2 Site1Wire.Wide16.b2.forgetL) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a Site1Wire.Wide16.b2.forgetL (WideBank8.Fast16.fforget midW) st hsafe
    have ha2 := WideBank8.Fast16.fblock_addr read b2 hg2 a st ha hcl.1 m₂
    have hsafe2 : ∀ m', Clean scrAllWires (ECDSAAdd.run ((specialize Site1Wire.Wide16.site1_16.code a).instantiate read) m' st).basis := by
      have hs1 : BlockSafe2 read a (.unit (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩)) st := hsp.1.1
      have hcode_eq : (Rows.unit r16 ⟨(site1 probeRows).prefix, site1 probeRows⟩).code = Site1Wire.Wide16.site1_16.code := by
        simp [Rows.unit, UnitSite.code, Site1Wire.Wide16.site1_16, Rows.site, MaskedSite.code, MaskedSite.prefix, Rows.code, Rows.instr]
      have hpr : portTargets (Rows.site r16 (site1 probeRows)).ports = scrAllWires := by
        rw [Rows.site, Rows.targets]; exact sitePorts_targets probeRows
      intro m'; have hm' := hs1 m'; rw [hcode_eq] at hm'; simpa [Rows.unit, hpr] using hm'
    change bm.kraus (b₂.kraus (Bridge.signedKet st)) = _
    rw [r₂ a st ha hcl.1.1 hpool hsafe2, ← h2_ref a, map_smul,
      rm a _ ha2 (hcl.2 m₂ hm₂) (hsp.2 m₂ hm₂), reference2_append, run_append_records _ _ m₂ mm' st hm₂, smul_smul]
  -- Combine `cornerBlocks ++ tailW`
  have hct_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (WideBank8.Fast16.fforget cornerBlocks ++ WideBank8.Fast16.fforget tailW)) ∧
        ∀ a st {cx cy : ECDSAAdd.Fp} (hc : ECDSAAdd.Secp256k1.curve.toAffine.Nonsingular cx cy),
          RowReads (read32C coeffs Q a) (probeRows a) (.some hc) →
          ∀ (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState),
          PointDialogValues streamLayout X Y G base st.basis →
          base windowRoot = true → base streamLayout.control = true →
          (G = true → base streamLayout.infinitySelect = false ∧ base streamLayout.doubleSelect = false ∧
            base streamLayout.genericSelect = false ∧ base streamLayout.core.equalNegY = false) →
          AddrValid WideBank8.Fast16.windowBits windowRoot a st →
          WideBank8.Fast16.FCodeClean read a (cornerBlocks ++ tailW) st →
          Safe2 read a (WideBank8.Fast16.fforget cornerBlocks ++ WideBank8.Fast16.fforget tailW) st →
          b.kraus (Bridge.signedKet st) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget cornerBlocks ++ WideBank8.Fast16.fforget tailW)) m st))
      ((cornerFusedSrc read).seq (WideBank8.Fast16.fsrc read tailW)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients cc ct, ?_, by rw [simulationCoefficients_mass, mc, mt]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]; apply simulationAligned_seq ac at_
    intro bc kc bt kt hbc hbt
    obtain ⟨mc', lmc', rc⟩ := hbc; obtain ⟨mt', lmt', rt⟩ := hbt
    refine ⟨mc' ++ mt', by simp [erase2_append, List.length_append, cornerBlocks_litRec, lmc', lmt'], ?_⟩
    intro a st cx cy hc hr X Y G base hv hroot hctl hflag ha hcl hsafe
    have hmc' : mc'.length = ECDSAAdd.measurementCount (reference2 read a (WideBank8.Fast16.fforget cornerBlocks)) := by
      rw [← cornerBlocks_litRec] at lmc'; exact lmc'.trans (specialize_counts read (erase2 _) a).2.symm
    have hsp := WideBank8.Fast16.safe2_append_inv read a (WideBank8.Fast16.fforget cornerBlocks) (WideBank8.Fast16.fforget tailW) st hsafe
    have hcl_sp := fcodeClean_append_inv read a cornerBlocks tailW st hcl
    have haOut := fcode_addr read cornerBlocks hgc a st ha hcl_sp.1 mc' hmc'
    have hclTail := hcl_sp.2 mc' hmc'
    have hpathIn : Clean WideBank8.Fast16.pathBank st.basis := hcl_sp.1.1.1
    have hpathOut : Clean WideBank8.Fast16.pathBank (ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget cornerBlocks)) mc' st).basis :=
      fcode_path_clean read cornerBlocks hgc cornerBlocks_plain_avoid_path a st ha hcl_sp.1 hpathIn mc' hmc'
    have hcref : reference2 read a (WideBank8.Fast16.fforget cornerBlocks) = origCornerRef (read32C coeffs Q a) a := by
      rw [read32C]; exact cornerBlocks_ref_eq coeffs Q a
    change bt.kraus (bc.kraus (Bridge.signedKet st)) = _
    rw [rc a st hc hr X Y G base hv hroot hctl hflag ha hpathIn (hcref ▸ haOut) (hcref ▸ hpathOut),
      ← hcref, map_smul, rt a _ haOut hclTail (hsp.2 mc' hmc'), reference2_append,
      run_append_records _ _ mc' mt' st hmc', smul_smul]
  -- Combine `([b0, b1] ++ [b2] ++ midW)` and `(cornerBlocks ++ tailW)`
  obtain ⟨c01, a01, m01⟩ := h01_sim
  obtain ⟨c2m, a2m, m2m⟩ := h2m_sim
  obtain ⟨cct, act, mct⟩ := hct_sim
  have hpre_sim : ∃ cs : List ℂ, List.Forall₂
      (fun b c => ∃ m : List Bool, m.length = literalRecords (erase2 (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)) ∧
        ∀ a (s : BasisState), liveReady s → tableAddressValue WideBank8.Fast16.windowBits s = a →
          WideBank8.Fast16.FCodeClean read a (b0 :: b1 :: b2 :: midW) ⟨false, s⟩ →
          Safe2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW) ⟨false, s⟩ →
          b.kraus (Bridge.signedKet ⟨false, s⟩) = c •
            Bridge.signedKet (ECDSAAdd.run (reference2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)) m ⟨false, s⟩))
      (((WideBank8.Fast16.fblockSrc read b0).seq (WideBank8.Fast16.fblockSrc read b1)).seq
        ((Site1Wire.Wide16.twoPassSrc read).seq (WideBank8.Fast16.fsrc read midW))).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
    refine ⟨coherentSeqCoefficients c01 c2m, ?_, by rw [simulationCoefficients_mass, m01, m2m]; norm_num⟩
    rw [AdaptiveCircuit.run_seq]; apply simulationAligned_seq a01 a2m
    intro b₁ k₁ b₂ k₂ hb₁ hb₂
    obtain ⟨m₁, lm₁, r₁⟩ := hb₁; obtain ⟨m₂, lm₂, r₂⟩ := hb₂
    refine ⟨m₁ ++ m₂, by simp only [List.append_assoc, erase2_append, literalRecords_append, List.length_append, lm₁, lm₂, Nat.add_assoc], ?_⟩
    intro a s hs ha_s hcl hsafe
    have hsp := WideBank8.Fast16.safe2_append_inv read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL)
      (Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW) ⟨false, s⟩ (by simpa [List.append_assoc] using hsafe)
    have hm₁ : m₁.length = ECDSAAdd.measurementCount (reference2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL)) :=
      lm₁.trans (specialize_counts read (erase2 (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL)) a).2.symm
    have h0_m : ECDSAAdd.measurementCount (reference2 read a Site1Wire.Wide16.b0.forgetL) = 0 := by
      have hr : reference2 read a Site1Wire.Wide16.b0.forgetL = [.X 838] := by
        simp [Site1Wire.Wide16.b0, WideBank8.Fast16.FBlock2.forgetL, reference2, erase2, Block2.code,
          Rows.code, Rows.instr, wLiteral, specialize, WInstr.specialize, Tmpl.instantiate_lit]
      rw [hr]; exact x838_meas_zero
    have h1_m : ECDSAAdd.measurementCount (reference2 read a Site1Wire.Wide16.b1.forgetL) = 0 := by
      have hr : reference2 read a Site1Wire.Wide16.b1.forgetL = scrHeadProgram := by
        simp [Site1Wire.Wide16.b1, WideBank8.Fast16.FBlock2.forgetL, reference2, erase2, Block2.code,
          Rows.code, Rows.instr, scrHead, scrHeadProgram, wLiteral, specialize, WInstr.specialize,
          Tmpl.instantiate_append, Tmpl.instantiate_lit]
      rw [hr]; exact scrHeadProgram_meas_zero
    have hm₁_0 : m₁ = List.nil := List.eq_nil_of_length_eq_zero (by
      rw [hm₁, reference2_append, ECDSAAdd.measurementCount_append, h0_m, h1_m])
    have ha0 : AddrValid WideBank8.Fast16.windowBits windowRoot a ⟨false, s⟩ := ⟨ha_s, hs.2.2⟩
    have hstep01 := r₁ a ⟨false, s⟩ ha0 hcl.1 (fun m' hm' => (hcl.2 m' hm').1) hsp.1
    set st12 := ECDSAAdd.run (reference2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL)) m₁ ⟨false, s⟩ with hst12
    have hst12_eq : st12 = ECDSAAdd.run (reference2 read a Site1Wire.Wide16.b1.forgetL) List.nil
        (ECDSAAdd.run (reference2 read a Site1Wire.Wide16.b0.forgetL) List.nil ⟨false, s⟩) := by
      rw [hst12, hm₁_0, reference2_append, ECDSAAdd.run_append, h0_m]; rfl
    have hpool12 : Clean streamLayout.dialogPool st12.basis := by
      rw [hst12_eq]; exact liveReady_pool_after_b01 read r16 a s hs List.nil List.nil
    have ha12 : AddrValid WideBank8.Fast16.windowBits windowRoot a st12 := by
      rw [hst12_eq]
      exact WideBank8.Fast16.fblock_addr read b1 hg1 a _
        (WideBank8.Fast16.fblock_addr read b0 hg0 a ⟨false, s⟩ ha0 hcl.1 List.nil)
        ((hcl.2 List.nil (by simp [h0_m])).1) List.nil
    have hcl2m : WideBank8.Fast16.FCodeClean read a (b2 :: midW) st12 := by
      rw [hst12_eq]; exact (hcl.2 List.nil (by simp [h0_m])).2 List.nil (by simp [h1_m])
    change b₂.kraus (b₁.kraus (Bridge.signedKet ⟨false, s⟩)) = _
    rw [hstep01, map_smul, r₂ a st12 ha12 hcl2m hpool12 (hsp.2 m₁ hm₁), smul_smul]
    have hcomb : ECDSAAdd.run (reference2 read a (Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)) m₂ st12 =
        ECDSAAdd.run (reference2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)) (m₁ ++ m₂) ⟨false, s⟩ := by
      rw [hst12, ← run_append_records _ _ m₁ m₂ ⟨false, s⟩ hm₁, ← reference2_append]; simp [List.append_assoc]
    rw [hcomb]
  obtain ⟨cpre, apre, mpre⟩ := hpre_sim
  refine ⟨coherentSeqCoefficients cpre cct, ?_, by rw [simulationCoefficients_mass, mpre, mct]; norm_num⟩
  rw [rowSrc, AdaptiveCircuit.run_seq]
  apply simulationAligned_seq apre act
  intro b₁ k₁ b₂ k₂ hb₁ hb₂ s hs
  obtain ⟨m₁, lm₁, r₁⟩ := hb₁; obtain ⟨m₂, lm₂, r₂⟩ := hb₂
  let a := tableAddressValue WideBank8.Fast16.windowBits s
  have hsafe_all : Safe2 read a (WideBank8.Fast16.fforget WideBank8.Row16.code) ⟨false, s⟩ := by
    rw [WideBank8.Row16.forget]; exact Rows.row_safe _ _ _ hQ hn a s hs
  have hclean_all : WideBank8.Fast16.FCodeClean read a WideBank8.Row16.code ⟨false, s⟩ :=
    WideBank8.Row16.clean_fused _ _ _ (WideBank8.Row16.clean_lift coeffs Q _ _ _
      (WEXFast.rowCF_clean (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs)
      (PoolHost.poolBand_clean_in_rowCF (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs)
      (by rw [WEXFast.fforget_rowCF]; exact PoolHost.rowC_host4 (fun _ => coeffs (r16 a)) Q hQ (fun _ => hn _) a s hs))
  have hcode_app : WideBank8.Row16.code = (b0 :: b1 :: b2 :: midW) ++ (cornerBlocks ++ tailW) := by
    rw [code_split_corner]; simp [List.append_assoc]
  rw [hcode_app] at hsafe_all hclean_all
  have hff_pre : WideBank8.Fast16.fforget (b0 :: b1 :: b2 :: midW) =
      Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW := by
    simp [WideBank8.Fast16.fforget_cons, List.append_assoc]
  have hclean_sp := fcodeClean_append_inv read a (b0 :: b1 :: b2 :: midW) (cornerBlocks ++ tailW) ⟨false, s⟩ hclean_all
  rw [WideBank8.Fast16.fforget_append, WideBank8.Fast16.fforget_append, hff_pre] at hsafe_all
  have hsafe_sp := WideBank8.Fast16.safe2_append_inv read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)
    (WideBank8.Fast16.fforget cornerBlocks ++ WideBank8.Fast16.fforget tailW) ⟨false, s⟩ hsafe_all
  have hm₁ : m₁.length = ECDSAAdd.measurementCount (reference2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)) :=
    lm₁.trans (specialize_counts read (erase2 _) a).2.symm
  have hstep1 := r₁ a s hs rfl hclean_sp.1 hsafe_sp.1
  set stPre := ECDSAAdd.run (reference2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW)) m₁ ⟨false, s⟩ with hstPre
  have hclCT : WideBank8.Fast16.FCodeClean read a (cornerBlocks ++ tailW) stPre := by
    have h1 := hclean_sp.2 m₁ (by rw [hff_pre]; exact hm₁)
    rwa [hff_pre] at h1
  have haPre : AddrValid WideBank8.Fast16.windowBits windowRoot a stPre := by
    have hg_pre : ∀ b ∈ b0 :: b1 :: b2 :: midW, WideBank8.Fast16.FBlockGeo b := fun b hb =>
      WideBank8.Row16.geometry b (by rw [hcode_app]; exact List.mem_append_left _ hb)
    have h1 := fcode_addr read (b0 :: b1 :: b2 :: midW) hg_pre a ⟨false, s⟩ ⟨rfl, hs.2.2⟩ hclean_sp.1 m₁ (by rw [hff_pre]; exact hm₁)
    rwa [hff_pre] at h1
  -- Extract `PointDialogValues` on `stPre` via `CornerFast.preSite2_values`!
  let coeffs32 : Fin 32768 → PointCoeff := fun _ => coeffs (r16 a)
  have hstPre_ref : reference2 read a (Site1Wire.Wide16.b0.forgetL ++ Site1Wire.Wide16.b1.forgetL ++ Site1Wire.Wide16.b2.forgetL ++ WideBank8.Fast16.fforget midW) =
      reference (read32C coeffs Q a) a CornerFast.preSite2Code := by
    rw [pre_forget_eq, Rows.reference_blocks, read32C]
    simp only [reference2, reference, erase2_map]
  let C := Single.Physical.tablePoint coeffs32 Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs32 Q hQ a
  obtain ⟨P, hP⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (ECDSAAdd.Arithmetic.regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (ECDSAAdd.Arithmetic.regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P) true (fun _ => false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P) (StreamPoint.of_coordinates s P hs.1.1.1.1 hP), ?_, ?_, ?_⟩
    · simpa [streamLayout_control, flipInfinity, ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (ECDSAAdd.Arithmetic.regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  cases he : Bridge.toB C with
  | zero => exact (hC (congrArg ECDSAAdd.ShorPort.toA he)).elim
  | @some cx cy hc =>
    have ce : C = toA (.some hc) := congrArg toA he
    have hr : RowReads (read32C coeffs Q a) (probeRows a) (.some hc) := by
      rw [read32C]; exact readConstant_rowReads coeffs32 Q _ _ ce
    have ho : ShorECDLP.order • (.some hc : ECDSAAdd.Secp256k1.Point) = 0 := by rw [← he]; exact hord
    have hp2 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 2
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hp3 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 3
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hd : (.some hc : ECDSAAdd.Secp256k1.Point) + .some hc ≠ 0 := by simpa only [two_nsmul] using hp2
    have ht : (.some hc : ECDSAAdd.Secp256k1.Point) + .some hc + .some hc ≠ 0 := by
      simpa only [show (3 : Nat) = 2 + 1 from rfl, succ_nsmul, two_nsmul] using hp3
    have en := enables_true hc hd ht
    have hdo : ShorECDLP.order • ((.some hc : ECDSAAdd.Secp256k1.Point) + .some hc) = 0 := by rw [nsmul_add, ho, zero_add]
    obtain ⟨X, Y, G, base, hv, hroot, hctl, hflag⟩ :=
      CornerFast.preSite2_values (read32C coeffs Q a) a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial hs.2.2 m₁
    rw [← hstPre_ref, ← hstPre] at hv
    have hstep2 := r₂ a stPre hc hr X Y G base hv hroot hctl hflag haPre hclCT (hsafe_sp.2 m₁ hm₁)
    change b₂.kraus (b₁.kraus (ket s)) = _
    rw [← Bridge.signedKet_false s, hstep1, map_smul, hstep2, smul_smul]
    have hcomb : ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget cornerBlocks ++ WideBank8.Fast16.fforget tailW)) m₂ stPre =
        ECDSAAdd.run (reference2 read a (WideBank8.Fast16.fforget WideBank8.Row16.code)) (m₁ ++ m₂) ⟨false, s⟩ := by
      rw [hstPre, ← run_append_records _ _ m₁ m₂ ⟨false, s⟩ hm₁, ← reference2_append, hcode_app,
        WideBank8.Fast16.fforget_append, WideBank8.Fast16.fforget_append, hff_pre]
    have hrun : ECDSAAdd.run (reference2 read a (Geometry.row Geometry.Width.w16)) (m₁ ++ m₂) ⟨false, s⟩ =
        ⟨false, Add.update Geometry.Width.w16 coeffs Q s⟩ :=
      Rows.row_run r16 coeffs Q hQ hn a s hs (m₁ ++ m₂)
    rw [hcomb, WideBank8.Row16.forget, hrun, Bridge.signedKet_false, Bridge.signedKet_false]
    simp [ket]

/-! ### Part 6: Signed 17-bit window wrapper (`CornerWire.Wide16`) -/

attribute [local irreducible] rowProg WideSigned.Frame16.program

local notation "signedCredit16C" => (2 * Body.signCredit + rowTP16C)

def program (start : Nat) : Straight 65536 start (start + 1703898) :=
  castFinish (congrArg (fun m => start + m) (by decide : 512 + 1703386 = 1703898))
    (Frame16.program 1703386 rowProg start)

attribute [local irreducible] program

def source (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (Body.prefixSource .w16).seq ((Body.signSource.seq ((rowSrc (readConstant coeffs Q)).seq Body.signSource)).seq
    (Body.suffixSource .w16))

theorem source_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (source coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  have hs : CoherentlyImplementsOn Body.signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady :=
    fastWindowSign_coherent
  have ha := composeCoherent hs (rowSrc_coherent coeffs Q hQ hn) (fun s h => liveReady_write _ s h)
  have hb := composeCoherent ha hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  have hc := composeCoherent (Body.prefix_coherent .w16) hb
    (fun s h => Body.prepare_live .w16 _ (rootFlip_live s h))
  have hd := composeCoherent hc (Body.suffix_coherent .w16) (fun _ _ => trivial)
  simpa only [source, Body.state, adaptive_seq_assoc] using hd

theorem run (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).run = (source coeffs Q).run := by
  rw [program, castFinish_instantiate]
  have hr (j : Nat) (hist : Fin j → Bool) :
      ((rowProg j).instantiate (readConstant coeffs Q) hist).run = (rowSrc (readConstant coeffs Q)).run :=
    rowProg_run _ j hist
  simpa only [source] using Frame16.run 1703386 rowProg (rowSrc (readConstant coeffs Q))
    (readConstant coeffs Q) hr start history

theorem coherent (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  unfold CoherentlyImplementsOn; rw [run]; exact source_coherent coeffs Q hQ hn

def window : Single.Window 65536 := ⟨(Body.logicalBank .w16).reverse, 1703898, program⟩

def model (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
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

theorem program_credit (start : Nat) : ProgramCredit (program start) signedCredit16C := by
  rw [program]; apply credit_cast; exact Frame16.credit _ _ rowProg rowProg_credit start

theorem wellFormed (start : Nat) : (program start).WellFormed := by
  rw [program, castFinish_wellFormed]; exact Frame16.wellFormed _ rowProg rowProg_wellFormed start

theorem credit_bound : signedCredit16C ≤ 2303596 := by
  have h1 : WideBank8.Fast16.fcodeTP WideBank8.Row16.code =
      WideBank8.Fast16.fblockTP b0 + WideBank8.Fast16.fblockTP b1 +
      WideBank8.Fast16.fblockTP b2 + WideBank8.Fast16.fcodeTP midW +
      WideBank8.Fast16.fcodeTP cornerBlocks + WideBank8.Fast16.fcodeTP tailW :=
    (congrArg WideBank8.Fast16.fcodeTP code_split_corner).trans (fcodeTP_split6 b0 b1 b2 midW cornerBlocks tailW)
  have hcb_arith (T T0 T1 T2 TM TC TW Cnew tS tT tSign : Nat)
      (h1 : T = T0 + T1 + T2 + TM + TC + TW)
      (h2 : T2 = (16383 + 774 + tS + 32767 + 513 + tT + (255 + 247)) + 15098)
      (h3 : TC = Cnew + 23997)
      (hold : 2 * tSign + T ≤ 2342691) :
      2 * tSign + (T - 15098 - 23997) ≤ 2303596 := by omega
  exact hcb_arith _ _ _ _ _ _ _ _ _ _ _ h1 Site1Wire.Wide16.b2_tp_diff b12_b15_tp_diff WideBank8.Signed16.credit_bound

theorem signed_support (start : Nat) :
    ChallengeMigration.straightWires (program start) ⊆ WideBank8.Fast16.Tight.support := by
  rw [program, straightWires_castFinish]
  exact TightSupport.frame_support17_7 _ rowProg rowProg_support start

theorem packed_support (start : Nat) :
    ChallengeMigration.straightWires (relabelStraight TightSupport.compact17_7 (program start)) ⊆ List.range 1613 := by
  rw [straightWires_relabel]
  intro v hv; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (TightSupport.compact17_7_bound u (signed_support start hu))

theorem pointRule (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hactive : root 836 = true) (hz : Clean (Body.logicalBank .w16) root) :
    Single.Distribution.PointRule root (model coeffs Q hQ hn) := by
  intro prior output P
  simpa only [Single.Distribution.WindowModel.step, model, window, List.reverse_reverse,
    List.length_reverse, LinearMap.comp_apply] using
    Body.point_sum .w16 coeffs Q hQ hn root hactive hz prior output P

theorem prepared (coeffs : Fin 65536 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hs : windowReady root) (hz : Clean (Body.logicalBank .w16) root)
    (ψ : State) (hψ : SupportedOn (Single.Distribution.pointFamily root) ψ) :
    SupportedOn (model coeffs Q hQ hn).valid
      (Quantum.run ((model coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ) := by
  change SupportedOn (Body.model .w16 coeffs Q hQ hn).valid
    (Quantum.run ((Body.model .w16 coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ)
  exact Body.prepared .w16 coeffs Q hQ hn root hs hz ψ hψ

theorem slots (start : Nat) : (program start).gateSlots ≤ 4260000000 := by
  have hrow := rowProg_slots (start + 256)
  have hsign (j : Nat) : (Body.nProgram .w16 j).gateSlots ≤ 300000 := by
    rw [Body.nProgram, reindexStraight_gateSlots, nFastProgram_slots]
    have h := literal_slot_bound (n := 32768)
      (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
    rw [ECDSAAdd.Baselines.normalize_slots] at h
    have hmax := fastWindowSign_slots
    generalize ECDSAAdd.Challenge.gateSlots fastWindowSignProgram = G at h hmax
    generalize Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) = S at h ⊢
    omega
  rw [program, castFinish_gateSlots, Frame16.slots]
  have h1 := hsign start
  have h2 := hsign (start + 256 + 1703386)
  generalize (Body.nProgram .w16 start).gateSlots = s1 at h1 ⊢
  generalize (rowProg (start + 256)).gateSlots = s2 at hrow ⊢
  generalize (Body.nProgram .w16 (start + 256 + 1703386)).gateSlots = s3 at h2 ⊢
  omega

end Wide16

end
end ShorECDLP.Entrant.CornerWire
end
