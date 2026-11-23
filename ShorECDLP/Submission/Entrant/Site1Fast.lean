import ShorECDLP.Submission.Entrant.WideBank8

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
