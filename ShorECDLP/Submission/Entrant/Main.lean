import ShorECDLP.Submission.Entrant.FusedRow
import ShorECDLP.Submission.Entrant.FusedRow14

/-! Entry module. To keep the number of Entrant modules (each replayed by leanchecker as a concurrent task with its
own environment) as low as the base entrant's 13, this file holds, in order: lane B's width-15 corner row (formerly
`CornerRow`), its width-14 twin (formerly `CornerRow14`), the 261/208 schedule with the averaged success bound and
the 56-word readout (formerly `Schedule261`, itself a fold of `SinAverage`, `SinAverage261`, `Readout56`), and the
exported `entry`, `layout`, `bounds`, `certificate`. -/

-- ===== formerly CornerRow =====

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-! The corner point write from loaded words.

The output-half word `scrD` holds `C.finite`, `C.x` and the doubled point `C+C`. The leader wrote
`C` into the point register with its own controlled table traversal (`wPoint`). Here the load of
`scrD` also loads `C.y` into the 256 clean pool wires `14115..14370` (the `y` word), the corner
write of `C` becomes 513 Toffolis from the two loaded words, and the `y` word is cleared early by
its own measured clear, before the final negation and the comparison middle need those pool wires.
The negation under `genericSelect ⊕ equalNegY` moves ahead of the load; it does not read the words. -/

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000

/-- The corner `y` word: pool positions 0 through 255. -/
def yWires : List Wire := List.range' 14115 256

def yBits (rows : Nat → Fin 32768) : List (LookupPort 32768) :=
  indexedPorts streamLayout.point.y (wFields rows .y) true

def yPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) := retarget (yBits rows) yWires

/-- Sources of the corner write of `C`: the pair word without its parity wire, then the `y` word. -/
def cSources : List Wire := scrPairWires.take 257 ++ yWires

/-- The pair-word part of the point register: `finite` and `x`. -/
def scrXTargets : List Wire := streamLayout.point.finite :: streamLayout.point.x

def scrCWrite : Program := ccxList streamLayout.doubleSelect cSources scrDTargets

def cornerNeg : WCode 32768 := wLiteral scrNegE ++ wLiteral scrNegP ++ wLiteral scrNegE

def cornerA1 : WCode 32768 :=
  wLiteral scrSw1 ++ wLiteral (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) ++
  wLiteral scrSw1 ++ wLiteral scrW1 ++ wLiteral scrCWrite ++ wLiteral scrW2

def cornerA2 : WCode 32768 := wLiteral scrNegP ++ wLiteral (pointDialogGenericFlag streamLayout) ++ scrDMiddle

def cornerPorts (rows : Nat → Fin 32768) : List (LookupPort 32768) := scrDPorts rows ++ yPorts rows

/-! ### List facts -/

theorem yBits_length (rows : Nat → Fin 32768) : (yBits rows).length = 256 := by
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  rw [yBits, WEXUnlookup.indexed_length, hy]

theorem yWires_length : yWires.length = 256 := by simp [yWires]

theorem yPorts_targets (rows : Nat → Fin 32768) : portTargets (yPorts rows) = yWires :=
  retarget_targets _ _ ((yBits_length rows).trans yWires_length.symm)

theorem yPorts_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (yPorts rows) a = portBits read (yBits rows) a :=
  retarget_bits read _ _ ((yBits_length rows).trans yWires_length.symm) a

theorem yPorts_length (rows : Nat → Fin 32768) : (yPorts rows).length = 256 := by
  have h := congrArg List.length (yPorts_targets rows)
  simpa [portTargets, yWires_length] using h

theorem portTargets_append {n} (a b : List (LookupPort n)) :
    portTargets (a ++ b) = portTargets a ++ portTargets b := by
  simp [portTargets]

theorem portBits_append {n} (read : ConstantBit n → Bool) (a b : List (LookupPort n)) (x : Nat) :
    portBits read (a ++ b) x = portBits read a x ++ portBits read b x := by
  simp [portBits]

theorem cornerPorts_targets (rows : Nat → Fin 32768) :
    portTargets (cornerPorts rows) = scrAllWires ++ yWires := by
  rw [cornerPorts, portTargets_append, scrDPorts_targets, yPorts_targets]

theorem cornerPorts_bits (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    portBits read (cornerPorts rows) a = portBits read (scrDPorts rows) a ++ portBits read (yPorts rows) a := by
  rw [cornerPorts, portBits_append]

theorem scrDPorts_length (rows : Nat → Fin 32768) : (scrDPorts rows).length = 771 := by
  have h := congrArg List.length (scrDPorts_targets rows)
  simp only [portTargets, List.length_map] at h
  rw [h, WEXUnlookup.scrAllWires_eq, WEXUnlookup.scrWires_eq]
  simp

theorem scrAllWires_length : scrAllWires.length = 771 := by
  rw [WEXUnlookup.scrAllWires_eq, WEXUnlookup.scrWires_eq]; simp

theorem yWires_nodup : yWires.Nodup := List.nodup_range'

theorem yWires_bounds : ∀ a ∈ yWires, 14115 ≤ a ∧ a < 14371 := by
  intro a ha
  simp only [yWires, List.mem_range'_1] at ha
  omega

/-- Disjointness from the `y` word by a single pass over the other list. -/
theorem yWires_not_of (L : List Wire) (hL : (L.all fun b => decide (b < 14115 ∨ 14371 ≤ b)) = true) :
    ∀ a ∈ yWires, a ∉ L := by
  intro a ha hm
  have h1 := List.all_eq_true.mp hL a hm
  have h2 := yWires_bounds a ha
  simp only [decide_eq_true_eq] at h1
  dsimp only [Wire] at *
  omega

theorem yWires_scrAll : ∀ a ∈ yWires, a ∉ scrAllWires := by
  intro a ha hm
  have h1 := scrAll_bounds a hm
  have h2 := yWires_bounds a ha
  dsimp only [Wire] at *
  omega

theorem scrAll_yWires : ∀ a ∈ scrAllWires, a ∉ yWires := fun a ha hm => yWires_scrAll a hm ha

theorem yWires_d_targets : ∀ a ∈ yWires, a ∉ scrDTargets := yWires_not_of _ (by decide +kernel)
theorem yWires_flags : ∀ a ∈ yWires, a ∉ [streamLayout.control, streamLayout.core.generic,
    streamLayout.infinitySelect, streamLayout.doubleSelect, streamLayout.genericSelect,
    streamLayout.core.equalNegY] := yWires_not_of _ (by decide +kernel)
theorem scrDWires_sub : ∀ a ∈ scrDWires, a ∈ scrAllWires := by
  intro a hm
  rcases List.mem_append.mp hm with h | h
  · exact List.mem_append_left _ (List.mem_append_right _ h)
  · exact List.mem_append_right _ h

theorem yWires_scrDWires : ∀ a ∈ yWires, a ∉ scrDWires :=
  fun a ha hm => yWires_scrAll a ha (scrDWires_sub a hm)
theorem yWires_pair257 : ∀ a ∈ yWires, a ∉ scrPairWires.take 257 := by
  intro a ha hm
  exact yWires_scrAll a ha (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_take hm)))

theorem yWires_pool (a : Wire) (ha : a ∈ yWires) : a ∈ streamLayout.dialogPool := by
  simp only [yWires, List.mem_range'_1] at ha
  have e : streamLayout.core.poolWire (a - 14115) = a := by
    rw [poolWire_eq (a - 14115) (by omega)]
    exact Nat.add_sub_of_le ha.1
  rw [← e]
  exact deltaPool_mem_dialog _ (by omega)

theorem yWires_source : ∀ a ∈ yWires, a ∈ sourceSupport := by
  intro a ha
  have h := yWires_bounds a ha
  rw [sourceSupport_mem]
  right
  unfold oldWork
  dsimp only [Wire] at *
  omega

theorem windowRoot_yWires : windowRoot ∉ yWires := by
  intro h; have := yWires_bounds _ h; unfold windowRoot at this; dsimp only [Wire] at *; omega

theorem xBits_append (A B : List Wire) (kA kB : List Bool) (hl : A.length = kA.length) :
    xBits (A ++ B) (kA ++ kB) = xBits A kA ++ xBits B kB := by
  induction A generalizing kA with
  | nil =>
    cases kA with
    | nil => simp [xBits]
    | cons _ _ => simp at hl
  | cons w A ih =>
    cases kA with
    | nil => simp at hl
    | cons b kA => simp [xBits, ih kA (by simpa using hl), List.append_assoc]

theorem cBits_append (c : Wire) (A B : List Wire) (kA kB : List Bool) (hl : A.length = kA.length) :
    cBits c (A ++ B) (kA ++ kB) = cBits c A kA ++ cBits c B kB := by
  induction A generalizing kA with
  | nil =>
    cases kA with
    | nil => simp [cBits]
    | cons _ _ => simp at hl
  | cons w A ih =>
    cases kA with
    | nil => simp at hl
    | cons b kA => simp [cBits, ih kA (by simpa using hl), List.append_assoc]

theorem ccxList_append (c : Wire) (A B T U : List Wire) (hl : A.length = T.length) :
    ccxList c (A ++ B) (T ++ U) = ccxList c A T ++ ccxList c B U := by
  induction A generalizing T with
  | nil =>
    cases T with
    | nil => simp [ccxList]
    | cons _ _ => simp at hl
  | cons a A ih =>
    cases T with
    | nil => simp at hl
    | cons t T => simp [ccxList, ih T (by simpa using hl)]

theorem scrXTargets_length : scrXTargets.length = 257 := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  simp [scrXTargets, hx]

theorem scrDTargets_split : scrDTargets = scrXTargets ++ streamLayout.point.y := rfl

theorem pair257_length : (scrPairWires.take 257).length = 257 := by
  rw [List.length_take, scrPairWires_length]; rfl

theorem scrCWrite_split : scrCWrite =
    ccxList streamLayout.doubleSelect (scrPairWires.take 257) scrXTargets ++
      ccxList streamLayout.doubleSelect yWires streamLayout.point.y := by
  rw [scrCWrite, cSources, scrDTargets_split, ccxList_append _ _ _ _ _ (pair257_length.trans scrXTargets_length.symm)]

/-- The pair word's first 257 ports are the `finite` and `x` ports of the corner point. -/
theorem pairBits_take (rows : Nat → Fin 32768) :
    (scrPairBits rows (wBit rows .y)).take 257 =
      ⟨wBit rows .infinity, false, streamLayout.point.finite⟩ ::
        indexedPorts streamLayout.point.x (wFields rows .x) true := by
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hl : (⟨wBit rows .infinity, false, streamLayout.point.finite⟩ ::
      indexedPorts streamLayout.point.x (wFields rows .x) true : List (LookupPort 32768)).length = 257 := by
    simp [WEXUnlookup.indexed_length, hx]
  simp only [scrPairBits, pairParityPorts, List.cons_append]
  rw [show (257 : Nat) = (⟨wBit rows .infinity, false, streamLayout.point.finite⟩ ::
      indexedPorts streamLayout.point.x (wFields rows .x) true : List (LookupPort 32768)).length from hl.symm]
  exact List.take_left' rfl

theorem scrCPorts_split (rows : Nat → Fin 32768) :
    scrCPorts rows = (scrPairBits rows (wBit rows .y)).take 257 ++ yBits rows := by
  rw [pairBits_take]; rfl

theorem doubleSelect_notin : streamLayout.doubleSelect ∉ scrAllWires ∧ streamLayout.doubleSelect ∉ yWires ∧
    streamLayout.doubleSelect ∉ scrXTargets ∧ streamLayout.doubleSelect ∉ streamLayout.point.y := by
  refine ⟨fun h => scrAll_flags _ h (by simp), fun h => yWires_flags _ h (by simp), ?_, ?_⟩ <;> decide +kernel

theorem scrAll_x_targets : ∀ a ∈ scrAllWires, a ∉ scrXTargets := by
  intro a ha hm
  exact scrAll_d_targets a ha (by rw [scrDTargets_split]; exact List.mem_append_left _ hm)

theorem yWires_y : ∀ a ∈ yWires, a ∉ streamLayout.point.y := by
  intro a ha hm
  exact yWires_d_targets a ha (by rw [scrDTargets_split]; exact List.mem_append_right _ hm)

theorem scrAll_y_reg : ∀ a ∈ scrAllWires, a ∉ streamLayout.point.y := by
  intro a ha hm
  exact scrAll_d_targets a ha (by rw [scrDTargets_split]; exact List.mem_append_right _ hm)

/-! ### Simulations of the corner block over the two loaded words -/

/-- With the `y` word loaded, the corner write of `C` acts like a controlled constant write of `y`. -/
theorem cornerA1_ySim (kY : List Bool) (hl : kY.length = 256) :
    ScrSim yWires kY
      (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrW1 ++
        ((ccxList streamLayout.doubleSelect (scrPairWires.take 257) scrXTargets ++
          ccxList streamLayout.doubleSelect yWires streamLayout.point.y) ++ scrW2)))))
      (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrW1 ++
        ((ccxList streamLayout.doubleSelect (scrPairWires.take 257) scrXTargets ++
          cBits streamLayout.doubleSelect streamLayout.point.y kY) ++ scrW2))))) := by
  have fl := scrE_flags
  have sw := scrSw_flags
  have h1 : ScrSim yWires kY scrSw1 scrSw1 :=
    ScrSim.disjoint _ _ _ (fun a ha hq => yWires_flags a ha (sw.1 _ hq))
  have hW1 : ScrSim yWires kY scrW1 scrW1 :=
    ScrSim.disjoint _ _ _ (fun a ha hq => yWires_flags a ha (fl.2.1 _ hq))
  have hW2 : ScrSim yWires kY scrW2 scrW2 :=
    ScrSim.disjoint _ _ _ (fun a ha hq => yWires_flags a ha (fl.2.2 _ hq))
  have hD : ScrSim yWires kY (ccxList streamLayout.core.equalNegY scrDWires scrDTargets)
      (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) := by
    apply ScrSim.disjoint
    intro a ha hq
    rcases ccxList_wires _ _ _ _ hq with h | h | h
    · exact yWires_flags a ha (by rw [h]; simp)
    · exact yWires_scrDWires a ha h
    · exact yWires_d_targets a ha h
  have hP : ScrSim yWires kY (ccxList streamLayout.doubleSelect (scrPairWires.take 257) scrXTargets)
      (ccxList streamLayout.doubleSelect (scrPairWires.take 257) scrXTargets) := by
    apply ScrSim.disjoint
    intro a ha hq
    rcases ccxList_wires _ _ _ _ hq with h | h | h
    · exact yWires_flags a ha (by rw [h]; simp)
    · exact yWires_pair257 a ha h
    · exact yWires_d_targets a ha (by rw [scrDTargets_split]; exact List.mem_append_left _ h)
  have hY : ScrSim yWires kY (ccxList streamLayout.doubleSelect yWires streamLayout.point.y)
      (cBits streamLayout.doubleSelect streamLayout.point.y kY) :=
    ScrSim.ccx yWires yWires streamLayout.point.y streamLayout.doubleSelect kY kY
      (xMask_map yWires kY yWires_nodup (yWires_length.trans hl.symm)) (fun a ha => ha) yWires_y
      doubleSelect_notin.2.1 doubleSelect_notin.2.2.2
  exact h1.append (hD.append (h1.append (hW1.append ((hP.append hY).append hW2))))

/-- With the `scrD` word loaded, the rest of the corner block acts in place. -/
theorem cornerA1_dSim (K kD kP kY : List Bool) (hmapD : scrDWires.map (xMask scrAllWires K) = kD)
    (hmapP : (scrPairWires.take 257).map (xMask scrAllWires K) = kP) :
    ScrSim scrAllWires K
      (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrW1 ++
        ((ccxList streamLayout.doubleSelect (scrPairWires.take 257) scrXTargets ++
          cBits streamLayout.doubleSelect streamLayout.point.y kY) ++ scrW2)))))
      (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets kD ++ (scrSw1 ++ (scrW1 ++
        ((cBits streamLayout.doubleSelect scrXTargets kP ++
          cBits streamLayout.doubleSelect streamLayout.point.y kY) ++ scrW2))))) := by
  have fl := scrE_flags
  have hs := scrD_swSim K
  have hW1 := ScrSim.disjoint scrAllWires K scrW1 (fun w hw' => scrAll_flag_avoid w hw' _ fl.2.1)
  have hW2 := ScrSim.disjoint scrAllWires K scrW2 (fun w hw' => scrAll_flag_avoid w hw' _ fl.2.2)
  have hcc := scrD_ccxSim K kD hmapD
  have hP : ScrSim scrAllWires K (ccxList streamLayout.doubleSelect (scrPairWires.take 257) scrXTargets)
      (cBits streamLayout.doubleSelect scrXTargets kP) :=
    ScrSim.ccx scrAllWires (scrPairWires.take 257) scrXTargets streamLayout.doubleSelect K kP hmapP
      (fun a ha => List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_take ha)))
      scrAll_x_targets doubleSelect_notin.1 doubleSelect_notin.2.2.1
  have hY : ScrSim scrAllWires K (cBits streamLayout.doubleSelect streamLayout.point.y kY)
      (cBits streamLayout.doubleSelect streamLayout.point.y kY) := by
    apply ScrSim.disjoint
    intro a ha hq
    rcases cBits_wires _ _ _ _ hq with h | h
    · exact doubleSelect_notin.1 (h ▸ ha)
    · exact scrAll_y_reg a ha h
  exact hs.1.append (hcc.append (hs.1.append (hW1.append ((hP.append hY).append hW2))))

theorem cornerA2_dSim (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    ScrSim scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
        portBits read (scrDExtraBits rows) a)
      (scrNegP ++ (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets)))))))
      (scrNegP ++ midIP read rows a) := by
  have hm := scrD_maps read rows a
  exact (scrD_negSim _).append (scrD_midSim _ _ _ _ rfl hm.1 hm.2.1)


/-! ### Clearing the two words with one load -/

/-- Flags are away from the dialog pool. -/
theorem flag_pool_away (L : ControlledPointLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q ∈ L.inPlaceFlags) : q ∉ L.dialogPool := by
  intro bad
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hb := List.count_pos_iff.mpr bad
  have hf := List.count_pos_iff.mpr hq
  simp only [dialogUsedWires, List.count_append] at h
  omega

theorem scrNegE_wires : ∀ q ∈ ECDSAAdd.wires scrNegE, q ∈ streamLayout.inPlaceFlags := by
  intro q hq
  simp only [scrNegE, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.union_empty, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl <;> simp [inPlaceFlags]

theorem scrNegE_pool : ∀ w ∈ streamLayout.dialogPool, w ∉ ECDSAAdd.wires scrNegE :=
  fun w hw hq => flag_pool_away streamLayout streamLayout_nodup _ (scrNegE_wires _ hq) hw

theorem scrNegE_pointY : ∀ w ∈ streamLayout.point.y, w ∉ ECDSAAdd.wires scrNegE :=
  fun w hw hq => point_flag_away streamLayout streamLayout_nodup _ (scrNegE_wires _ hq)
    (by simp [PointAddLayout.pointWires, hw])

theorem windowRoot_scrNegE : windowRoot ∉ ECDSAAdd.wires scrNegE := by
  intro hq
  have h := scrE_flags.1 _ hq
  revert h
  decide +kernel

theorem windowRoot_pointY : windowRoot ∉ streamLayout.point.y := by decide +kernel

theorem scrNegP_negH : scrNegP = negH streamLayout := rfl

/-- The leading negation keeps the root, the pool and the point bound. -/
theorem cornerNeg_run (m : List Bool) (t : State) (hr : t.basis windowRoot = true)
    (hpool : ECDSAAdd.regValue streamLayout.dialogPool t.basis = 0)
    (hy : ECDSAAdd.regValue streamLayout.point.y t.basis < ECDSAAdd.p) :
    (run (scrNegE ++ (scrNegP ++ scrNegE)) m t).basis windowRoot = true ∧
      ECDSAAdd.regValue streamLayout.dialogPool (run (scrNegE ++ (scrNegP ++ scrNegE)) m t).basis = 0 := by
  rw [scrNegP_negH]
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have e1 : ∀ (k : List Bool) (s : State), ECDSAAdd.regValue streamLayout.dialogPool (run scrNegE k s).basis =
      ECDSAAdd.regValue streamLayout.dialogPool s.basis := by
    intro k s
    apply ECDSAAdd.Arithmetic.regValue_congr
    intro w hw'
    exact run_preserves_outside _ _ _ _ (scrNegE_pool w hw')
  have e2 : ∀ (k : List Bool) (s : State), ECDSAAdd.regValue streamLayout.point.y (run scrNegE k s).basis =
      ECDSAAdd.regValue streamLayout.point.y s.basis := by
    intro k s
    apply ECDSAAdd.Arithmetic.regValue_congr
    intro w hw'
    exact run_preserves_outside _ _ _ _ (scrNegE_pointY w hw')
  simp only [run_append]
  constructor
  · rw [run_preserves_outside _ _ _ _ windowRoot_scrNegE]
    rw [(negH_effect streamLayout hw hn _ _ (by rw [e2]; exact hy) (by rw [e1]; exact hpool)).2.2 _ windowRoot_pointY]
    rw [run_preserves_outside _ _ _ _ windowRoot_scrNegE]
    exact hr
  · rw [e1]
    exact negH_clean streamLayout hw hn _ _ (by rw [e2]; exact hy) (by rw [e1]; exact hpool)


theorem run_cBits_head (r : Wire) (S : List Wire) (k : List Bool) (Q : Program) (m : List Bool) (t : State)
    (hc : r ∉ S) (ht : t.basis r = true) :
    run (cBits r S k ++ Q) m t = run (xBits S k ++ Q) m t := by
  rw [run_append, run_append, cBits_records, xBits_records, cBits_eq_xBits_run r S k _ t hc ht]

theorem xBits_root (r : Wire) (S : List Wire) (k n : List Bool) (t : State) (hc : r ∉ S) (ht : t.basis r = true) :
    (run (xBits S k) n t).basis r = true := by
  rw [xBits_run]; simp [xMask_outside S k r hc, ht]

/-- One rooted load of two words, the second word unloaded early: on root-true states the controlled
form is the plain form. -/
theorem cBits_double_root (r : Wire) (S₁ S₂ : List Wire) (k₁ k₂ : List Bool) (M₁ M₂ : Program)
    (m : List Bool) (t : State) (hc₁ : r ∉ S₁) (hc₂ : r ∉ S₂) (ht : t.basis r = true)
    (hl : S₁.length = k₁.length)
    (hM₁ : ∀ n (t' : State), t'.basis r = true → (run M₁ n t').basis r = true)
    (hM₂ : ∀ n (t' : State), t'.basis r = true → (run M₂ n t').basis r = true) :
    run (cBits r (S₁ ++ S₂) (k₁ ++ k₂) ++ (M₁ ++ (cBits r S₂ k₂ ++ (M₂ ++ cBits r S₁ k₁)))) m t =
      run (xBits S₁ k₁ ++ (xBits S₂ k₂ ++ (M₁ ++ (xBits S₂ k₂ ++ (M₂ ++ xBits S₁ k₁))))) m t := by
  have hc₁₂ : r ∉ S₁ ++ S₂ := by simp [hc₁, hc₂]
  rw [run_cBits_head r _ _ _ m t hc₁₂ ht, xBits_append S₁ S₂ k₁ k₂ hl, List.append_assoc]
  rw [run_append (xBits S₁ k₁), run_append (xBits S₁ k₁)]
  have h1 : (run (xBits S₁ k₁) (m.take (measurementCount (xBits S₁ k₁))) t).basis r = true :=
    xBits_root r S₁ k₁ _ t hc₁ ht
  set t₁ := run (xBits S₁ k₁) (m.take (measurementCount (xBits S₁ k₁))) t with ht₁
  set m₁ := m.drop (measurementCount (xBits S₁ k₁)) with hm₁
  rw [run_append (xBits S₂ k₂), run_append (xBits S₂ k₂)]
  have h2 : (run (xBits S₂ k₂) (m₁.take (measurementCount (xBits S₂ k₂))) t₁).basis r = true :=
    xBits_root r S₂ k₂ _ t₁ hc₂ h1
  set t₂ := run (xBits S₂ k₂) (m₁.take (measurementCount (xBits S₂ k₂))) t₁ with ht₂
  set m₂ := m₁.drop (measurementCount (xBits S₂ k₂)) with hm₂
  rw [run_append M₁, run_append M₁]
  have h3 := hM₁ (m₂.take (measurementCount M₁)) t₂ h2
  set t₃ := run M₁ (m₂.take (measurementCount M₁)) t₂ with ht₃
  set m₃ := m₂.drop (measurementCount M₁) with hm₃
  rw [run_cBits_head r S₂ k₂ _ m₃ t₃ hc₂ h3]
  rw [run_append (xBits S₂ k₂), run_append (xBits S₂ k₂)]
  have h4 : (run (xBits S₂ k₂) (m₃.take (measurementCount (xBits S₂ k₂))) t₃).basis r = true :=
    xBits_root r S₂ k₂ _ t₃ hc₂ h3
  set t₄ := run (xBits S₂ k₂) (m₃.take (measurementCount (xBits S₂ k₂))) t₃ with ht₄
  set m₄ := m₃.drop (measurementCount (xBits S₂ k₂)) with hm₄
  rw [run_append M₂, run_append M₂]
  have h5 := hM₂ (m₄.take (measurementCount M₂)) t₄ h4
  exact cBits_eq_xBits_run r S₁ k₁ _ _ hc₁ h5

/-- Two nested scratch sandwiches: the inner word is cleared before the outer one. -/
theorem double_sandwich (S₁ S₂ : List Wire) (k₁ k₂ : List Bool) (P₁ P₁' P₂ Q : Program)
    (h₁ : ScrSim S₂ k₂ P₁ P₁') (h₂ : ScrSim S₁ k₁ (P₁' ++ P₂) Q)
    (hdisj : ∀ a ∈ S₂, a ∉ S₁) (m : List Bool) (t : State)
    (hs₁ : ∀ a ∈ S₁, t.basis a = false) (hs₂ : ∀ a ∈ S₂, t.basis a = false) :
    run (xBits S₁ k₁ ++ (xBits S₂ k₂ ++ (P₁ ++ (xBits S₂ k₂ ++ (P₂ ++ xBits S₁ k₁))))) m t = run Q m t := by
  have e1 : run (xBits S₁ k₁ ++ (xBits S₂ k₂ ++ (P₁ ++ (xBits S₂ k₂ ++ (P₂ ++ xBits S₁ k₁))))) m t =
      run (xBits S₂ k₂ ++ (P₁ ++ (xBits S₂ k₂ ++ (P₂ ++ xBits S₁ k₁)))) m (run (xBits S₁ k₁) ([]) t) := by
    rw [run_append, xBits_records, List.take_zero, List.drop_zero]
  have hclean : ∀ a ∈ S₂, (run (xBits S₁ k₁) ([]) t).basis a = false := by
    intro a ha
    rw [xBits_run]; simp [xMask_outside S₁ k₁ a (hdisj a ha), hs₂ a ha]
  have e2 := scr_sandwich_append S₂ k₂ P₁ P₁' (P₂ ++ xBits S₁ k₁) h₁ m _ hclean
  simp only [List.append_assoc] at e2
  have e3 : run (xBits S₁ k₁ ++ (P₁' ++ P₂) ++ xBits S₁ k₁) m t =
      run (P₁' ++ (P₂ ++ xBits S₁ k₁)) m (run (xBits S₁ k₁) ([]) t) := by
    simp only [List.append_assoc]
    rw [run_append (xBits S₁ k₁), xBits_records, List.take_zero, List.drop_zero]
  rw [e1, e2, ← e3]
  exact scr_sandwich S₁ k₁ (P₁' ++ P₂) Q h₂ m t hs₁

/-! ### The new literal -/

theorem cSources_lower : ∀ a ∈ cSources, 14115 ≤ a := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · have := scrAll_bounds a (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_take h)))
    dsimp only [Wire] at *
    omega
  · exact (yWires_bounds a h).1

theorem cSources_pool : ∀ a ∈ cSources, a ∈ streamLayout.dialogPool := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact scrWires_pool a (List.mem_append_left _ (List.mem_of_mem_take h))
  · exact yWires_pool a h

/-- The output word's wires are in the source support (from the leader's lookup ledger). -/
theorem scrAll_source : ∀ a ∈ scrAllWires, a ∈ sourceSupport := by
  have h := WEXUnlookup.row_oldWithin.2 (some windowRoot) (scrDPorts probeRows) (by
    rw [clearReferenceRow_eq]
    simp [portFinite6, portSuffixCodeF])
  rw [scrDPorts_targets] at h
  exact h.2

theorem cSources_source : ∀ a ∈ cSources, a ∈ sourceSupport := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact scrAll_source a (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_take h)))
  · exact yWires_source a h

theorem cSources_d_targets : ∀ a ∈ cSources, a ∉ scrDTargets := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact scrAll_d_targets a (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_take h)))
  · exact yWires_d_targets a h

theorem cSources_nodup : cSources.Nodup := by
  have h : (scrPairWires.take 257 ++ yWires).Nodup := by
    rw [List.nodup_append]
    refine ⟨(scrWires_nodup.of_append_left).sublist (List.take_sublist _ _), yWires_nodup, ?_⟩
    intro a ha b hb hab
    subst hab
    exact yWires_scrAll _ hb (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_take ha)))
  exact h

theorem doubleSelect_cSources : streamLayout.doubleSelect ∉ cSources := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact scrAll_flags _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_take h))) (by simp)
  · exact yWires_flags _ h (by simp)

theorem scrCWrite_facts :
    ECDSAAdd.wires scrCWrite ⊆ streamLayout.dialogUsedWires.toFinset ∧ GatePhysical scrCWrite ∧
      ECDSAAdd.wires scrCWrite ⊆ sourceSupport.toFinset := by
  have hd : streamLayout.doubleSelect ∈ streamLayout.inPlaceFlags := by simp [inPlaceFlags]
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    apply List.mem_toFinset.mpr
    rcases ccxList_wires _ _ _ _ hq with h | h | h
    · subst h
      exact List.mem_append_left _ (List.mem_append_right _ hd)
    · exact List.mem_append_right _ (cSources_pool q h)
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  · exact ccxList_physical _ _ _ cSources_d_targets doubleSelect_cSources (by decide +kernel)
  · intro q hq
    apply List.mem_toFinset.mpr
    rcases ccxList_wires _ _ _ _ hq with h | h | h
    · subst h; exact streamFlagsPoint_source (List.mem_append_left _ hd)
    · exact cSources_source q h
    · exact streamFlagsPoint_source (List.mem_append_right _ (by
        simpa [PointAddLayout.pointWires, scrDTargets] using h))


/-! ### The corner code and its reference run -/

/-- Load of both words, then the first half of the corner block. -/
def cornerPre₁ : WCode 32768 := [.lookup (some windowRoot) (cornerPorts probeRows)] ++ cornerA1

def cornerUnit₁ : WCode 32768 := cornerPre₁ ++ [.lookup (some windowRoot) (yPorts probeRows)]
def cornerUnit₂ : WCode 32768 := cornerA2 ++ [.lookup (some windowRoot) (scrDPorts probeRows)]

theorem cornerNeg_inst (read : ConstantBit 32768 → Bool) (a : Nat) :
    (specialize cornerNeg a).instantiate read = scrNegE ++ (scrNegP ++ scrNegE) := by
  simp only [cornerNeg, specialize_append, Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit,
    List.append_assoc]

theorem cornerA1_inst (read : ConstantBit 32768 → Bool) (a : Nat) :
    (specialize cornerA1 a).instantiate read =
      scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrW1 ++
        (scrCWrite ++ scrW2)))) := by
  simp only [cornerA1, specialize_append, Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit,
    List.append_assoc]

theorem cornerA2_inst (read : ConstantBit 32768 → Bool) (a : Nat) :
    (specialize cornerA2 a).instantiate read =
      scrNegP ++ (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets)))))) := by
  simp only [cornerA2, scrDMiddle, specialize_append, Tmpl.instantiate_append, specialize_literal,
    Tmpl.instantiate_lit, scr_chain_inst, List.append_assoc]

theorem cornerLoad_inst (read : ConstantBit 32768 → Bool) (a : Nat) :
    (specialize ([.lookup (some windowRoot) (cornerPorts probeRows)] : WCode 32768) a).instantiate read =
      cBits windowRoot (scrAllWires ++ yWires)
        (portBits read (scrDPorts probeRows) a ++ portBits read (yPorts probeRows) a) := by
  rw [scr_lookup_some_inst, cornerPorts_targets, cornerPorts, portBits_append]

theorem cornerA2_sub : ∀ i ∈ cornerA2, i ∈ sfxMidF probeRows := by
  intro i hi
  simp only [cornerA2, sfxMidF, cornersE_split, sfxCC, wLiteral, List.mem_append, List.mem_singleton,
    or_assoc] at hi ⊢
  rcases hi with h | h | h <;> simp only [h, true_or, or_true, eq_self_iff_true]

theorem cornerNeg_sub : ∀ i ∈ cornerNeg, i ∈ sfxMidF probeRows := by
  intro i hi
  simp only [cornerNeg, sfxMidF, cornersE_split, sfxCC, wLiteral, List.mem_append, List.mem_singleton,
    or_assoc] at hi ⊢
  rcases hi with h | h | h <;> simp only [h, true_or, or_true, eq_self_iff_true]

theorem cornerA1_mem (i : WInstr 32768) (hi : i ∈ cornerA1) :
    i ∈ sfxMidF probeRows ∨ i = .literal scrCWrite := by
  simp only [cornerA1, sfxMidF, cornersE_split, sfxCC, wLiteral, List.mem_append, List.mem_singleton,
    or_assoc] at hi ⊢
  rcases hi with h | h | h | h | h | h <;> simp only [h, true_or, or_true, eq_self_iff_true]

theorem scrCWrite_placed : PlacedPair windowBits windowPaths windowRoot (WInstr.literal (n := 32768) scrCWrite) :=
  lit_facts_placed _ scrCWrite_facts.1

theorem cornerA1_placed : ∀ i ∈ cornerA1, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  rcases cornerA1_mem i hi with h | rfl
  · exact sfxMid_placed i h
  · exact scrCWrite_placed

theorem cornerA2_placed : ∀ i ∈ cornerA2, PlacedPair windowBits windowPaths windowRoot i :=
  fun i hi => sfxMid_placed i (cornerA2_sub i hi)

theorem cornerNeg_placed : ∀ i ∈ cornerNeg, PlacedPair windowBits windowPaths windowRoot i :=
  fun i hi => sfxMid_placed i (cornerNeg_sub i hi)

theorem cornerA1_root (read : ConstantBit 32768 → Bool) (a : Nat) (n : List Bool) (t : State)
    (h : t.basis windowRoot = true) :
    (run (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrW1 ++
        (scrCWrite ++ scrW2))))) n t).basis windowRoot = true := by
  rw [← cornerA1_inst read a]
  exact root_preserves read windowBits windowPaths windowRoot cornerA1 a cornerA1_placed t h n

theorem cornerA2_root (read : ConstantBit 32768 → Bool) (a : Nat) (n : List Bool) (t : State)
    (h : t.basis windowRoot = true) :
    (run (scrNegP ++ (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets))))))) n t).basis
      windowRoot = true := by
  rw [← cornerA2_inst read a]
  exact root_preserves read windowBits windowPaths windowRoot cornerA2 a cornerA2_placed t h n

/-- The point bits read by the corner write, as the pair word's head bits and the `y` word. -/
theorem cPorts_bits (read : ConstantBit 32768 → Bool) (a : Nat) :
    portBits read (scrCPorts probeRows) a =
      portBits read ((scrPairBits probeRows (wBit probeRows .y)).take 257) a ++ portBits read (yPorts probeRows) a := by
  rw [scrCPorts_split, portBits_append, yPorts_bits]

theorem kP_length (read : ConstantBit 32768 → Bool) (a : Nat) :
    (portBits read ((scrPairBits probeRows (wBit probeRows .y)).take 257) a).length = 257 := by
  simp [portBits, List.length_take, scrPairBits_length]

theorem kY_length (read : ConstantBit 32768 → Bool) (a : Nat) :
    (portBits read (yPorts probeRows) a).length = 256 := by
  simp [portBits, yPorts_length]

theorem kD_length (read : ConstantBit 32768 → Bool) (a : Nat) :
    (portBits read (scrDPorts probeRows) a).length = 771 := by
  simp [portBits, scrDPorts_length]

theorem kP_map (read : ConstantBit 32768 → Bool) (a : Nat) :
    (scrPairWires.take 257).map (xMask scrAllWires
      ((portBits read (scrPairBits probeRows (wBit probeRows .y)) a ++ portBits read (scrShortBits probeRows) a) ++
        portBits read (scrDExtraBits probeRows) a)) =
      portBits read ((scrPairBits probeRows (wBit probeRows .y)).take 257) a := by
  have h := (scrD_maps read probeRows a).1
  simp only [portBits] at h ⊢
  rw [List.map_take, h, List.map_take]

/-- The leader's in-place corner tail, after its scratch sandwich. -/
def leaderTail (read : ConstantBit 32768 → Bool) (a : Nat) : Program :=
  scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
      (portBits read (scrShortBits probeRows) a ++ portBits read (scrDExtraBits probeRows) a) ++
    (scrSw1 ++ (scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts probeRows) a) ++
      (scrW2 ++ (scrNegP ++ midIP read probeRows a))))))

theorem leader_reduce (read : ConstantBit 32768 → Bool) (a : Nat) (m : List Bool) (t : State)
    (hr : t.basis windowRoot = true) (hD : ∀ w ∈ scrAllWires, t.basis w = false) :
    run ((specialize WEXUnlookup.scrDSite.code a).instantiate read) m t =
      run ((scrNegE ++ (scrNegP ++ scrNegE)) ++ leaderTail read a) m t := by
  have hsw := scr_sandwich _ _ _ _ (scrE_sim read probeRows a) m t hD
  rw [WEXUnlookup.scrDSite_code, scrDCode_inst, cBits_sandwich_root windowRoot scrAllWires _ _ m t scrAll_root hr
    (fun n t' h' => root_preserves read windowBits windowPaths windowRoot _ a sfxMid_placed t' h' n),
    scrDPorts_bits]
  simp only [sfxMidF, scrDMiddle, specialize_append, Tmpl.instantiate_append, specialize_literal,
    Tmpl.instantiate_lit, scr_chain_inst, scrECorners_inst, List.append_assoc]
  simp only [List.append_assoc] at hsw
  with_reducible rw [hsw]
  simp only [leaderTail, List.append_assoc]

/-- The corner code after the leading negation, on a state with both words clean. -/
theorem corner_reduce (read : ConstantBit 32768 → Bool) (a : Nat) (m : List Bool) (t : State)
    (hr : t.basis windowRoot = true) (hD : ∀ w ∈ scrAllWires, t.basis w = false)
    (hY : ∀ w ∈ yWires, t.basis w = false) :
    run ((specialize (cornerUnit₁ ++ cornerUnit₂) a).instantiate read) m t = run (leaderTail read a) m t ∧
      ∀ w ∈ scrAllWires, (run (leaderTail read a) m t).basis w = false := by
  have hkD := scrDPorts_bits read probeRows a
  have e : (specialize (cornerUnit₁ ++ cornerUnit₂) a).instantiate read =
      cBits windowRoot (scrAllWires ++ yWires)
        (portBits read (scrDPorts probeRows) a ++ portBits read (yPorts probeRows) a) ++
      ((specialize cornerA1 a).instantiate read ++
        (cBits windowRoot yWires (portBits read (yPorts probeRows) a) ++
          ((specialize cornerA2 a).instantiate read ++
            cBits windowRoot scrAllWires (portBits read (scrDPorts probeRows) a)))) := by
    simp only [cornerUnit₁, cornerUnit₂, cornerPre₁, specialize_append, Tmpl.instantiate_append,
      scr_lookup_some_inst, cornerPorts_targets, cornerPorts_bits, yPorts_targets, scrDPorts_targets,
      List.append_assoc]
  rw [e, cornerA1_inst, cornerA2_inst]
  rw [cBits_double_root windowRoot scrAllWires yWires (portBits read (scrDPorts probeRows) a)
    (portBits read (yPorts probeRows) a) _ _ m t scrAll_root windowRoot_yWires hr
    (by rw [kD_length, scrAllWires_length]) (cornerA1_root read a) (cornerA2_root read a)]
  rw [scrCWrite_split]
  have h₁ := cornerA1_ySim (portBits read (yPorts probeRows) a) (kY_length read a)
  have h₂ : ScrSim scrAllWires (portBits read (scrDPorts probeRows) a)
      ((scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrW1 ++
        ((ccxList streamLayout.doubleSelect (scrPairWires.take 257) scrXTargets ++
          cBits streamLayout.doubleSelect streamLayout.point.y (portBits read (yPorts probeRows) a)) ++ scrW2))))) ++
       (scrNegP ++ (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets))))))))
      ((scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
          (portBits read (scrShortBits probeRows) a ++ portBits read (scrDExtraBits probeRows) a) ++ (scrSw1 ++ (scrW1 ++
        ((cBits streamLayout.doubleSelect scrXTargets (portBits read ((scrPairBits probeRows (wBit probeRows .y)).take 257) a) ++
          cBits streamLayout.doubleSelect streamLayout.point.y (portBits read (yPorts probeRows) a)) ++ scrW2))))) ++
       (scrNegP ++ midIP read probeRows a)) := by
    rw [hkD]
    exact (cornerA1_dSim _ _ _ _ (scrD_maps read probeRows a).2.2 (kP_map read a)).append (cornerA2_dSim read probeRows a)
  have hC : cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts probeRows) a) =
      cBits streamLayout.doubleSelect scrXTargets (portBits read ((scrPairBits probeRows (wBit probeRows .y)).take 257) a) ++
        cBits streamLayout.doubleSelect streamLayout.point.y (portBits read (yPorts probeRows) a) := by
    rw [cPorts_bits, scrDTargets_split, cBits_append _ _ _ _ _ (scrXTargets_length.trans (kP_length read a).symm)]
  have key := double_sandwich scrAllWires yWires _ _ _ _ _ _ h₁ h₂ yWires_scrAll m t hD hY
  constructor
  · rw [key]
    simp only [leaderTail, hC, List.append_assoc]
  · have hc := (h₂.step m t hD).2
    simp only [leaderTail, hC, List.append_assoc] at hc ⊢
    exact hc

theorem cBits_double_root₁ (r : Wire) (S₁ S₂ : List Wire) (k₁ k₂ : List Bool) (M₁ : Program)
    (m : List Bool) (t : State) (hc₁ : r ∉ S₁) (hc₂ : r ∉ S₂) (ht : t.basis r = true)
    (hl : S₁.length = k₁.length)
    (hM₁ : ∀ n (t' : State), t'.basis r = true → (run M₁ n t').basis r = true) :
    run (cBits r (S₁ ++ S₂) (k₁ ++ k₂) ++ (M₁ ++ cBits r S₂ k₂)) m t =
      run (xBits S₁ k₁ ++ (xBits S₂ k₂ ++ (M₁ ++ xBits S₂ k₂))) m t := by
  have hc₁₂ : r ∉ S₁ ++ S₂ := by simp [hc₁, hc₂]
  rw [run_cBits_head r _ _ _ m t hc₁₂ ht, xBits_append S₁ S₂ k₁ k₂ hl, List.append_assoc]
  rw [run_append (xBits S₁ k₁), run_append (xBits S₁ k₁)]
  have h1 : (run (xBits S₁ k₁) (m.take (measurementCount (xBits S₁ k₁))) t).basis r = true :=
    xBits_root r S₁ k₁ _ t hc₁ ht
  set t₁ := run (xBits S₁ k₁) (m.take (measurementCount (xBits S₁ k₁))) t with ht₁
  set m₁ := m.drop (measurementCount (xBits S₁ k₁)) with hm₁
  rw [run_append (xBits S₂ k₂), run_append (xBits S₂ k₂)]
  have h2 : (run (xBits S₂ k₂) (m₁.take (measurementCount (xBits S₂ k₂))) t₁).basis r = true :=
    xBits_root r S₂ k₂ _ t₁ hc₂ h1
  set t₂ := run (xBits S₂ k₂) (m₁.take (measurementCount (xBits S₂ k₂))) t₁ with ht₂
  set m₂ := m₁.drop (measurementCount (xBits S₂ k₂)) with hm₂
  rw [run_append M₁, run_append M₁]
  have h3 := hM₁ (m₂.take (measurementCount M₁)) t₂ h2
  exact cBits_eq_xBits_run r S₂ k₂ _ _ hc₂ h3

theorem scr_sandwich' (S : List Wire) (k : List Bool) (P P' : Program) (h : ScrSim S k P P')
    (m : List Bool) (s : State) (hs : ∀ a ∈ S, s.basis a = false) :
    run (xBits S k ++ (P ++ xBits S k)) m s = run P' m s := by
  rw [← List.append_assoc]
  exact scr_sandwich S k P P' h m s hs

/-- The `y` word is clean after its early unload, on a state with both words clean. -/
theorem corner_yclean (read : ConstantBit 32768 → Bool) (a : Nat) (m : List Bool) (t : State)
    (hr : t.basis windowRoot = true) (hD : ∀ w ∈ scrAllWires, t.basis w = false)
    (hY : ∀ w ∈ yWires, t.basis w = false) :
    ∀ w ∈ yWires, (run ((specialize cornerUnit₁ a).instantiate read) m t).basis w = false := by
  have e : (specialize cornerUnit₁ a).instantiate read =
      cBits windowRoot (scrAllWires ++ yWires)
        (portBits read (scrDPorts probeRows) a ++ portBits read (yPorts probeRows) a) ++
      ((specialize cornerA1 a).instantiate read ++
        cBits windowRoot yWires (portBits read (yPorts probeRows) a)) := by
    simp only [cornerUnit₁, cornerPre₁, specialize_append, Tmpl.instantiate_append,
      scr_lookup_some_inst, cornerPorts_targets, cornerPorts_bits, yPorts_targets, List.append_assoc]
  rw [e, cornerA1_inst]
  rw [cBits_double_root₁ windowRoot scrAllWires yWires (portBits read (scrDPorts probeRows) a)
    (portBits read (yPorts probeRows) a) _ m t scrAll_root windowRoot_yWires hr
    (by rw [kD_length, scrAllWires_length]) (cornerA1_root read a)]
  rw [run_append (xBits scrAllWires _), xBits_records, List.take_zero, List.drop_zero]
  have hclean : ∀ w ∈ yWires,
      (run (xBits scrAllWires (portBits read (scrDPorts probeRows) a)) ([]) t).basis w = false := by
    intro w hw
    rw [xBits_run]; simp [xMask_outside scrAllWires _ w (yWires_scrAll w hw), hY w hw]
  have h₁ := cornerA1_ySim (portBits read (yPorts probeRows) a) (kY_length read a)
  rw [scrCWrite_split, scr_sandwich' yWires _ _ _ h₁ m _ hclean]
  exact (h₁.step m _ hclean).2

end
end ShorECDLP.Entrant.WEX

/-! ### Units: a compiled prefix followed by the measured clear of a word it loaded

A masked site is the unit whose prefix is the site's own load and arithmetic. The corner block is two
units sharing one load: the first unit clears the `y` word, the second the `scrD` word. -/
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

structure UnitSite (n : Nat) where
  pre : WCode n
  clear : MaskedSite n

def UnitSite.code {n} (u : UnitSite n) : WCode n := u.pre ++ [.lookup (some u.clear.guard) u.clear.ports]

inductive Block2 (n : Nat) where
  | plain (code : WCode n)
  | unit (u : UnitSite n)
abbrev Code2 (n : Nat) := List (Block2 n)

def Block2.code {n} : Block2 n → WCode n
  | .plain code => code
  | .unit u => u.code

def erase2 {n} (code : Code2 n) : WCode n := code.flatMap Block2.code
@[simp] theorem erase2_append {n} (a b : Code2 n) : erase2 (a++b) = erase2 a ++ erase2 b := by
  simp [erase2,List.flatMap_append]
@[simp] theorem erase2_cons {n} (b : Block2 n) (code : Code2 n) : erase2 (b::code) = b.code ++ erase2 code := rfl
@[simp] theorem erase2_nil {n} : erase2 ([] : Code2 n) = [] := rfl

def reference2 {n} (read : ConstantBit n → Bool) (address : Nat) (code : Code2 n) : ECDSAAdd.Program :=
  (specialize (erase2 code) address).instantiate read
@[simp] theorem reference2_append {n} (read : ConstantBit n → Bool) (address : Nat)
    (a b : Code2 n) : reference2 read address (a++b) = reference2 read address a ++ reference2 read address b := by
  simp [reference2]

def blockReference2 {n} (read : ConstantBit n → Bool) (address : Nat) (b : Block2 n) : ECDSAAdd.Program :=
  (specialize b.code address).instantiate read

def BlockSafe2 {n} (read : ConstantBit n → Bool) (address : Nat) : Block2 n → ECDSAAdd.State → Prop
  | .plain _, _ => True
  | .unit u, st => ∀ m, Clean (portTargets u.clear.ports)
      (ECDSAAdd.run ((specialize u.code address).instantiate read) m st).basis

def Safe2 {n} (read : ConstantBit n → Bool) (address : Nat) : Code2 n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => BlockSafe2 read address b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference2 read address b) →
        Safe2 read address code (ECDSAAdd.run (blockReference2 read address b) m st)

@[simp] theorem reference2_cons {n} (read : ConstantBit n → Bool) (address : Nat)
    (b : Block2 n) (code : Code2 n) : reference2 read address (b::code) =
      blockReference2 read address b ++ reference2 read address code := by
  simp [reference2,erase2,blockReference2,specialize]

@[simp] theorem reference2_nil {n} (read : ConstantBit n → Bool) (address : Nat) :
    reference2 read address ([] : Code2 n) = [] := rfl

theorem safe2_append {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code2 n)
    (st : ECDSAAdd.State) (ha : Safe2 read address a st)
    (hb : ∀ m, m.length = ECDSAAdd.measurementCount (reference2 read address a) →
      Safe2 read address b (ECDSAAdd.run (reference2 read address a) m st)) :
    Safe2 read address (a++b) st := by
  induction a generalizing st with
  | nil => simpa [Safe2,ECDSAAdd.run] using hb [] rfl
  | cons x xs ih =>
    refine ⟨ha.1,?_⟩
    intro m hm
    apply ih _ (ha.2 m hm)
    intro tail ht
    have hc := hb (m++tail) (by simp [ECDSAAdd.measurementCount_append,hm,ht])
    rw [reference2_cons,run_append_records _ _ m tail st hm] at hc
    exact hc

/-- The leader's blocks as units. -/
def toBlock2 {n} : Block n → Block2 n
  | .plain code => .plain code
  | .masked site => .unit ⟨site.prefix, site⟩

theorem toBlock2_code {n} (b : Block n) : (toBlock2 b).code = b.code := by
  cases b <;> rfl

theorem erase2_map {n} (code : Code n) : erase2 (code.map toBlock2) = erase code := by
  induction code with
  | nil => rfl
  | cons b code ih => rw [List.map_cons, erase2_cons, erase_cons, toBlock2_code, ih]

theorem reference2_map {n} (read : ConstantBit n → Bool) (address : Nat) (code : Code n) :
    reference2 read address (code.map toBlock2) = reference read address code := by
  simp [reference2, reference, erase2_map]

theorem blockReference2_map {n} (read : ConstantBit n → Bool) (address : Nat) (b : Block n) :
    blockReference2 read address (toBlock2 b) = blockReference read address b := by
  simp [blockReference2, blockReference, toBlock2_code]

theorem blockSafe2_map {n} (read : ConstantBit n → Bool) (address : Nat) (b : Block n) (st : ECDSAAdd.State)
    (h : BlockSafe read address b st) : BlockSafe2 read address (toBlock2 b) st := by
  cases b with
  | plain code => trivial
  | masked site => exact h

theorem safe2_map {n} (read : ConstantBit n → Bool) (address : Nat) (code : Code n) (st : ECDSAAdd.State)
    (h : Safe read address code st) : Safe2 read address (code.map toBlock2) st := by
  induction code generalizing st with
  | nil => trivial
  | cons b code ih =>
    refine ⟨blockSafe2_map read address b st h.1, fun m hm => ?_⟩
    rw [blockReference2_map] at hm ⊢
    exact ih _ (h.2 m hm)

/-! #### Compilation -/

def blockRecords2 {n} : Block2 n → Nat
  | .plain code => codeRecords windowBits windowPaths windowRoot (normalizeW code)
  | .unit u => codeRecords windowBits windowPaths windowRoot (normalizeW u.pre) +
      u.clear.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) u.clear.guard highPaths)+127)

def blockProgram2 {n} (b : Block2 n) (start : Nat) : Straight n start (start+blockRecords2 b) :=
  match b with
  | .plain code => compile windowBits windowPaths windowRoot (normalizeW code) start
  | .unit u => castFinish (by simp [blockRecords2,clearData]; omega)
      ((compile windowBits windowPaths windowRoot (normalizeW u.pre) start).append
        (clearProgram u.clear (start+codeRecords windowBits windowPaths windowRoot (normalizeW u.pre))))

def records2 {n} : Code2 n → Nat
  | [] => 0
  | b::code => blockRecords2 b + records2 code

def program2 {n} : (code : Code2 n) → (start : Nat) → Straight n start (start+records2 code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [records2]; omega)
      ((blockProgram2 b start).append (program2 code (start+blockRecords2 b)))

def blockSource2 {n} (read : ConstantBit n → Bool) : Block2 n → AdaptiveCircuit
  | .plain code => source read windowBits windowPaths windowRoot (normalizeW code)
  | .unit u => (source read windowBits windowPaths windowRoot (normalizeW u.pre)).seq
      (clearSource read u.clear)

def sourceCode2 {n} (read : ConstantBit n → Bool) : Code2 n → AdaptiveCircuit
  | [] => .done
  | b::code => (blockSource2 read b).seq (sourceCode2 read code)

theorem blockProgram2_run {n} (read : ConstantBit n → Bool) (b : Block2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram2 b start).instantiate read history).run = (blockSource2 read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | unit u =>
    rw [blockProgram2,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearProgram_run read u.clear _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSource2,AdaptiveCircuit.run_seq]

theorem program2_run {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((program2 code start).instantiate read history).run = (sourceCode2 read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [program2,castFinish_instantiate,append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,blockProgram2_run]
    simp only [sourceCode2,AdaptiveCircuit.run_seq]

structure UnitGeometry {n} (u : UnitSite n) : Prop where
  placed : ∀ i ∈ u.code, PlacedPair windowBits windowPaths windowRoot i
  bank : ∀ i ∈ u.code, HotAvoid i
  site : SiteGeometry u.clear

def BlockGeometry2 {n} : Block2 n → Prop
  | .plain code => (∀ i ∈ code, PlacedPair windowBits windowPaths windowRoot i) ∧
      (∀ i ∈ code, HotAvoid i)
  | .unit u => UnitGeometry u

theorem geometry_toBlock2 {n} (b : Block n) (hg : BlockGeometry b) : BlockGeometry2 (toBlock2 b) := by
  cases b with
  | plain code => exact hg
  | masked site =>
    exact ⟨fun i hi => placed_implies_pair _ _ _ _ (hg.placed i hi), hg.bank, hg⟩

theorem block2_placed {n} (b : Block2 n) (hg : BlockGeometry2 b) :
    (∀ i ∈ b.code, PlacedPair windowBits windowPaths windowRoot i) ∧
      (∀ i ∈ b.code, HotAvoid i) := by
  cases b with
  | plain code => exact hg
  | unit u => exact ⟨hg.placed,hg.bank⟩

theorem unit_run {n} (read : ConstantBit n → Bool) (u : UnitSite n)
    (hg : UnitGeometry u) (a : Nat) (st : ECDSAAdd.State) (m : List Bool)
    (hs : SimulationValid windowBits windowPaths windowRoot a st)
    (hh : MeasuredClear.HotClean hot st.basis) :
    ECDSAAdd.run ((specialize u.code a).instantiate read) m st =
      let next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m st
      ⟨next.phase,tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis⟩ := by
  have hp : ∀ i ∈ u.pre, PlacedPair windowBits windowPaths windowRoot i := by
    intro i hi; exact hg.placed i (List.mem_append_left _ hi)
  have hhot : ∀ i ∈ u.pre, HotAvoid i := by
    intro i hi; exact hg.bank i (List.mem_append_left _ hi)
  have hnext := reference_preserves read u.pre a hp hhot st hs hh m
  have hlast := hg.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
  have hroot : u.clear.guard ∉ portTargets u.clear.ports := List.disjoint_left.mp hlast.2.2 (by simp [lookupRoot])
  simp only [UnitSite.code,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
    ECDSAAdd.run_append,ECDSAAdd.run_take]
  simpa [specialize,WInstr.specialize] using portTemplate_run read (some u.clear.guard) u.clear.ports a windowRoot
    (m.drop (ECDSAAdd.measurementCount ((specialize u.pre a).instantiate read)))
    (ECDSAAdd.run ((specialize u.pre a).instantiate read) m st)
    hlast.2.1 hroot hnext.1.2.2

def BlockSimulation2 {n} (read : ConstantBit n → Bool) (block : Block2 n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, SimulationValid windowBits windowPaths windowRoot address st →
      MeasuredClear.HotClean hot st.basis → BlockSafe2 read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference2 read address block) m st)

theorem block2_simulation {n} (read : ConstantBit n → Bool) (block : Block2 n)
    (hg : BlockGeometry2 block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimulation2 read block) (blockSource2 read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    obtain ⟨cs,aligned,mass⟩ := normalized_simulation read code hg.1
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    exact ⟨m,hm,fun address st hs _ _ => hb address st hs⟩
  | unit u =>
    have hp : ∀ i ∈ u.pre, PlacedPair windowBits windowPaths windowRoot i := by
      intro i hi; exact hg.placed i (List.mem_append_left _ hi)
    have hhot : ∀ i ∈ u.pre, HotAvoid i := by
      intro i hi; exact hg.bank i (List.mem_append_left _ hi)
    obtain ⟨preCs,preAligned,preMass⟩ := normalized_simulation read u.pre hp
    obtain ⟨cs,aligned,mass⟩ := clearProgram_coherent read u.clear hg.site 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSource2,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block2.code,UnitSite.code,literalRecords_append,literalRecords] using hm
      · intro a st hs hh hsafe
        let next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m st
        have hn := reference_preserves read u.pre a hp hhot st hs hh m
        have hrun := unit_run read u hg a st m hs hh
        have hclean : Clean (portTargets u.clear.ports)
            (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
        have hvalid : MeasuredClear.HotClean hot next.basis ∧ Clean windowPaths next.basis ∧
            ∀ p ∈ u.clear.ports, next.basis p.target = (next.basis u.clear.guard &&
              decide (read (p.ref (tableAddressValue windowBits next.basis)) = p.value)) := by
          refine ⟨hn.2,hn.1.1,?_⟩
          rw [hn.1.2.1]
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
        rw [h₁ a st hs,map_smul,hsigned]
        simp [smul_smul,blockReference2,Block2.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num

def Simulation2 {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 code) ∧
    ∀ a st, SimulationValid windowBits windowPaths windowRoot a st →
      MeasuredClear.HotClean hot st.basis → Safe2 read a code st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference2 read a code) m st)

theorem source2_simulation {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (hg : ∀ b ∈ code, BlockGeometry2 b) :
    ∃ cs : List ℂ, List.Forall₂ (Simulation2 read code) (sourceCode2 read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1],.cons ?_ .nil,by simp⟩
    exact ⟨[],rfl,fun a st _ _ _ => by simp [reference2,erase2,specialize,ECDSAAdd.ShorPort.Tmpl.instantiate,ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁,h₁,mass₁⟩ := block2_simulation read b (hg b (by simp))
    obtain ⟨cs₂,h₂,mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    have geo := block2_placed b (hg b (by simp))
    refine ⟨coherentSeqCoefficients cs₁ cs₂,?_,?_⟩
    · rw [sourceCode2,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁,len₁,run₁⟩ := hb₁
      obtain ⟨m₂,len₂,run₂⟩ := hb₂
      refine ⟨m₁++m₂,?_,?_⟩
      · simp [erase2,List.length_append,len₁,len₂]
      · intro a st hs hh hsafe
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a b) :=
          len₁.trans (specialize_counts read b.code a).2.symm
        have hn := reference_preserves read b.code a geo.1 geo.2 st hs hh m₁
        change SimulationValid windowBits windowPaths windowRoot a
            (ECDSAAdd.run (blockReference2 read a b) m₁ st) ∧ MeasuredClear.HotClean hot
            (ECDSAAdd.run (blockReference2 read a b) m₁ st).basis at hn
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hh hsafe.1,map_smul,run₂ a (ECDSAAdd.run (blockReference2 read a b) m₁ st) hn.1 hn.2 (hsafe.2 m₁ hm),
          reference2_cons,run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass,mass₁,mass₂]
      norm_num

theorem program2_coherent {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (hg : ∀ b ∈ code, BlockGeometry2 b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue windowBits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue windowBits s) code) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program2 code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result)
      (fun s => Clean windowPaths s ∧ s windowRoot = true ∧ MeasuredClear.HotClean hot s ∧ Valid s) := by
  obtain ⟨cs,aligned,mass⟩ := source2_simulation read code hg
  refine ⟨cs,?_,mass⟩
  rw [program2_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m,_,h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨hs.1,rfl,hs.2.1⟩ hs.2.2.1 (hsafe s hs.2.2.2)
  rw [Bridge.signedKet_false,hrun s hs.2.2.2 m,Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.WEXUnlookup

/-! #### Ledgers of a unit code -/
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program2 blockProgram2 clearProgram

def blockCCX2 {n} : Block2 n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * 32767
  | .unit u => literalToffolis (normalizeW u.pre) + traversals u.pre * 32767 + 382

def blockMasks2 {n} : Block2 n → Nat
  | .plain _ => 0
  | .unit _ => 1

def ccx2 {n} : Code2 n → Nat
  | [] => 0
  | b::code => blockCCX2 b + ccx2 code

def masks2 {n} : Code2 n → Nat
  | [] => 0
  | b::code => blockMasks2 b + masks2 code

def blockLen2 {n} : Block2 n → Nat
  | .plain _ => 0
  | .unit u => u.clear.ports.length

def lens2 {n} : Code2 n → Nat
  | [] => 0
  | b::code => blockLen2 b + lens2 code

theorem ccx2_append {n} (a b : Code2 n) : ccx2 (a ++ b) = ccx2 a + ccx2 b := by
  induction a with
  | nil => simp [ccx2]
  | cons x a ih => simp [ccx2,ih,Nat.add_assoc]
theorem masks2_append {n} (a b : Code2 n) : masks2 (a ++ b) = masks2 a + masks2 b := by
  induction a with
  | nil => simp [masks2]
  | cons x a ih => simp [masks2,ih,Nat.add_assoc]
theorem lens2_append {n} (a b : Code2 n) : lens2 (a ++ b) = lens2 a + lens2 b := by
  induction a with
  | nil => simp [lens2]
  | cons x a ih => simp [lens2,ih,Nat.add_assoc]
theorem records2_append {n} (a b : Code2 n) : records2 (a ++ b) = records2 a + records2 b := by
  induction a with
  | nil => simp [records2]
  | cons x a ih => simp [records2,ih,Nat.add_assoc]

theorem block2_tCount {n} (read : ConstantBit n → Bool) (b : Block2 n) (hg : BlockGeometry2 b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram2 b start).instantiate read history).tCount = 7 * blockCCX2 b := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW code)
      (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram2,WEX.compile_tCount read windowBits windowPaths windowRoot (normalizeW code) hl start history,traversals_normalize]
    simp [blockCCX2,windowBits,Nat.mul_add,Nat.mul_assoc]
  | unit u =>
    have hp : ∀ i ∈ u.pre, PlacedPair windowBits windowPaths windowRoot i := by
      intro i hi; exact hg.placed i (List.mem_append_left _ hi)
    have hl := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW u.pre)
      (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    rw [blockProgram2,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearProgram_tCount read u.clear hg.site _ h),
      WEX.compile_tCount read windowBits windowPaths windowRoot (normalizeW u.pre) hl start history,traversals_normalize]
    simp [blockCCX2,windowBits]
    ring

theorem program2_tCount {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (hg : ∀ b ∈ code, BlockGeometry2 b) (start : Nat) (history : Fin start → Bool) :
    ((program2 code start).instantiate read history).tCount = 7 * ccx2 code := by
  induction code generalizing start with
  | nil => simp [program2,records2,ccx2,Straight.instantiate,AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [program2,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      block2_tCount read b (hg b (by simp))]
    simp [ccx2,Nat.mul_add]

theorem block2_ccx_relation {n} (b : Block2 n) :
    blockCCX2 b + blockMasks2 b * 32385 = literalToffolis (normalizeW b.code) + traversals b.code * 32767 := by
  cases b with
  | plain code => simp [blockCCX2,blockMasks2,Block2.code]
  | unit u =>
    have hl : literalToffolis (normalizeW u.code) = literalToffolis (normalizeW u.pre) := by
      rw [UnitSite.code,normalize_append,literalToffolis_append]
      simp [normalizeW,normalizeWInstr,literalToffolis]
    have ht : traversals u.code = traversals u.pre + 1 := by
      rw [UnitSite.code,traversals_append]
      rfl
    simp only [blockCCX2,blockMasks2,Block2.code]
    rw [hl,ht,Nat.add_mul]
    omega

theorem ccx2_relation {n} (code : Code2 n) :
    ccx2 code + masks2 code * 32385 = literalToffolis (normalizeW (erase2 code)) + traversals (erase2 code) * 32767 := by
  induction code with
  | nil => simp [ccx2,masks2,erase2,normalizeW,literalToffolis,traversals]
  | cons b code ih =>
    have hb := block2_ccx_relation b
    simp only [ccx2,masks2,erase2_cons,normalize_append,literalToffolis_append,traversals_append,Nat.add_mul]
    omega

theorem block2_records_relation {n} (b : Block2 n) (hg : BlockGeometry2 b) :
    blockRecords2 b + blockMasks2 b * 32385 = codeRecords windowBits windowPaths windowRoot (normalizeW b.code) + blockLen2 b := by
  cases b with
  | plain code => simp [blockRecords2,blockMasks2,Block2.code,blockLen2]
  | unit u =>
    rw [blockRecords2,high_records u.clear hg.site]
    rw [Block2.code,UnitSite.code,normalize_append,records_old_append]
    have hc : normalizeW ([.lookup (some u.clear.guard) u.clear.ports] : WCode n) = [.lookup (some u.clear.guard) u.clear.ports] := by simp [normalizeW,normalizeWInstr]
    rw [hc,site_old_clear_records u.clear hg.site]
    have hm : blockMasks2 (Block2.unit u) = 1 := rfl
    have hl : blockLen2 (Block2.unit u) = u.clear.ports.length := rfl
    omega

theorem records2_relation {n} (code : Code2 n) (hg : ∀ b ∈ code, BlockGeometry2 b) :
    records2 code + masks2 code * 32385 = codeRecords windowBits windowPaths windowRoot (normalizeW (erase2 code)) + lens2 code := by
  induction code with
  | nil => simp [records2,masks2,erase2,normalizeW,codeRecords,lens2]
  | cons b code ih =>
    have hb := block2_records_relation b (hg b (by simp))
    have ht := ih (fun d hd => hg d (by simp [hd]))
    simp only [records2,masks2,lens2,erase2_cons,normalize_append,records_old_append,Nat.add_mul]
    omega

open AndGadget WEXCredit in
theorem block2_residue {n} (b : Block2 n) (start : Nat) : residue (blockProgram2 b start) = 0 := by
  cases b with
  | plain code => rw [blockProgram2]; exact compile_residue _ _ _ _ _
  | unit u => simp [blockProgram2,residue_cast,residue_append,compile_residue,
      clearProgram,MeasuredClear.measuredClear_residue]

open AndGadget in
theorem program2_residue {n} (code : Code2 n) (start : Nat) : residue (program2 code start) = 0 := by
  induction code generalizing start with
  | nil => simp [program2,records2]
  | cons b code ih => simp [program2,residue_cast,residue_append,block2_residue,ih]

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

theorem block2_wellFormed {n} (b : Block2 n) (hg : BlockGeometry2 b)
    (hp : ∀ p, WInstr.literal p ∈ b.code → GatePhysical p) (start : Nat) :
    (blockProgram2 b start).WellFormed := by
  cases b with
  | plain code =>
    unfold blockProgram2
    exact pair_compile_wellFormed _ _ _ _ (by simp [windowBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hg.1) (normalized_literals_valid code hp) start
  | unit u =>
    have hpref : ∀ i ∈ u.pre, PlacedPair windowBits windowPaths windowRoot i := by
      intro i hi; exact hg.placed i (List.mem_append_left _ hi)
    have hphys : ∀ p, WInstr.literal p ∈ u.pre → GatePhysical p := by
      intro p hm; exact hp p (List.mem_append_left _ hm)
    rw [blockProgram2,castFinish_wellFormed]
    exact straight_append_wellFormed _ _
      (pair_compile_wellFormed _ _ _ _ (by simp [windowBits,windowPaths])
        (pair_placed_normalize _ _ _ _ hpref) (normalized_literals_valid u.pre hphys) start)
      (clearProgram_wellFormed u.clear hg.site _)

theorem program2_wellFormed {n} (code : Code2 n) (hg : ∀ b ∈ code, BlockGeometry2 b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 code → GatePhysical p) (start : Nat) :
    (program2 code start).WellFormed := by
  induction code generalizing start with
  | nil => simp [program2,records2,Straight.WellFormed]
  | cons b code ih =>
    rw [program2,castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact block2_wellFormed b (hg b (by simp)) (fun p hm => hp p (by simp [erase2_cons,hm])) start
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase2_cons,hm])) _

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram WEX.codeSlots WEX.normalizeW WEX.codeRecords
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.portOps lookupMeasurements tableAddressTree

theorem block2_slots_relation {n} (b : Block2 n) (hg : BlockGeometry2 b) (start : Nat) :
    (blockProgram2 b start).gateSlots + blockMasks2 b * 324100 =
      codeSlots windowBits (normalizeW b.code) + blockLen2 b * 98304 := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW code)
      (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram2,compile_slots windowBits windowPaths windowRoot (normalizeW code) hl start]
    simp [blockMasks2,blockLen2,Block2.code]
  | unit u =>
    have hp : ∀ i ∈ u.pre, PlacedPair windowBits windowPaths windowRoot i := by
      intro i hi; exact hg.placed i (List.mem_append_left _ hi)
    have hl := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW u.pre)
      (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    rw [blockProgram2,castFinish_gateSlots,Straight.gateSlots_append,clearProgram_slots u.clear hg.site,
      compile_slots windowBits windowPaths windowRoot (normalizeW u.pre) hl start,Block2.code,UnitSite.code,normalize_append,old_slots_append]
    have hc : normalizeW ([.lookup (some u.clear.guard) u.clear.ports] : WCode n) = [.lookup (some u.clear.guard) u.clear.ports] := by simp [normalizeW,normalizeWInstr]
    rw [hc,site_old_clear_slots u.clear]
    simp only [blockMasks2,blockLen2]
    omega

theorem program2_slots_relation {n} (code : Code2 n) (hg : ∀ b ∈ code, BlockGeometry2 b) (start : Nat) :
    (program2 code start).gateSlots + masks2 code * 324100 =
      codeSlots windowBits (normalizeW (erase2 code)) + lens2 code * 98304 := by
  induction code generalizing start with
  | nil => simp [program2,records2,masks2,lens2,Straight.gateSlots,erase2,normalizeW,codeSlots]
  | cons b code ih =>
    have hb := block2_slots_relation b (hg b (by simp)) start
    have ht := ih (fun d hd => hg d (by simp [hd])) (start+blockRecords2 b)
    rw [program2,castFinish_gateSlots,Straight.gateSlots_append]
    simp only [masks2,lens2,erase2_cons,normalize_append,old_slots_append,Nat.add_mul]
    omega

end
end ShorECDLP.Entrant.WEXUnlookup

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.wires ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

theorem block2_support {n} (b : Block2 n) (hg : BlockGeometry2 b) (hw : OldWithin b.code) (start : Nat) :
    ChallengeMigration.straightWires (blockProgram2 b start) ⊆ logicalSupport := by
  cases b with
  | plain code => rw [blockProgram2]; exact (old_compile_support code hw start).trans (List.subset_append_left _ _)
  | unit u =>
    have hp : OldWithin u.pre := oldWithin_sub u.pre u.code (List.subset_append_left _ _) hw
    rw [blockProgram2,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨(old_compile_support u.pre hp start).trans (List.subset_append_left _ _),
      clearProgram_support u.clear hg.site _⟩

theorem program2_support {n} (code : Code2 n) (hg : ∀ b ∈ code, BlockGeometry2 b)
    (hw : OldWithin (erase2 code)) (start : Nat) :
    ChallengeMigration.straightWires (program2 code start) ⊆ logicalSupport := by
  induction code generalizing start with
  | nil => simp [program2,records2,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hb : OldWithin b.code := oldWithin_sub b.code (erase2 (b::code)) (by rw [erase2_cons]; exact List.subset_append_left _ _) hw
    have ht : OldWithin (erase2 code) := oldWithin_sub (erase2 code) (erase2 (b::code)) (by rw [erase2_cons]; exact List.subset_append_right _ _) hw
    rw [program2,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨block2_support b (hg b (by simp)) hb start,
      ih (fun d hd => hg d (by simp [hd])) ht _⟩

end
end ShorECDLP.Entrant.WEXUnlookup

/-! ### The corner row -/
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- The early clear of the corner `y` word. -/
def ySite : MaskedSite 32768 := ⟨windowRoot, WEX.yPorts probeRows, []⟩
/-- The clear of the output comparison word, now after the corner block's second half. -/
def scrDClear : MaskedSite 32768 := ⟨windowRoot, WEX.scrDPorts probeRows, []⟩

def cornerUnit₁ : UnitSite 32768 := ⟨WEX.cornerPre₁, ySite⟩
def cornerUnit₂ : UnitSite 32768 := ⟨WEX.cornerA2, scrDClear⟩

theorem cornerUnit₁_code : cornerUnit₁.code = WEX.cornerUnit₁ := rfl
theorem cornerUnit₂_code : cornerUnit₂.code = WEX.cornerUnit₂ := rfl

def rowPost3 : Code2 32768 := [.plain WEX.cornerNeg, .unit cornerUnit₁, .unit cornerUnit₂,
  .plain WEX.sfxTailF, .plain (wLiteral [.X 838])]

def rowHead : Code 32768 := rowPre ++ generic2 probeRows

def rowC : Code2 32768 := rowHead.map toBlock2 ++ rowPost3

theorem row2_eq : row2 = rowHead ++ rowPost := by rw [row2_split, rowHead, List.append_assoc]

theorem erase_rowPost : erase rowPost = scrDSite.code ++ (WEX.sfxTailF ++ wLiteral [.X 838]) := by
  simp [rowPost, erase, Block.code]

theorem erase2_rowPost3 : erase2 rowPost3 =
    WEX.cornerNeg ++ (WEX.cornerUnit₁ ++ (WEX.cornerUnit₂ ++ (WEX.sfxTailF ++ wLiteral [.X 838]))) := by
  simp [rowPost3, erase2, Block2.code, cornerUnit₁_code, cornerUnit₂_code]

/-! #### Geometry -/

theorem scrDSite_geometry : SiteGeometry scrDSite :=
  row_geometry (.masked scrDSite) (by simp [row, portFused])

theorem scrD_unload_mem :
    WInstr.lookup (n := 32768) (some windowRoot) (WEX.scrDPorts probeRows) ∈ scrDSite.code := by
  rw [scrDSite_code]; simp

theorem scrD_lookup_placed : PlacedPair windowBits windowPaths windowRoot
    (WInstr.lookup (n := 32768) (some windowRoot) (WEX.scrDPorts probeRows)) :=
  placed_implies_pair _ _ _ _ (scrDSite_geometry.placed _ scrD_unload_mem)

theorem window_small : ∀ w ∈ windowRoot :: lookupRoot windowRoot (some windowRoot) :: windowBits ++ windowPaths,
    w < 10016 := by
  intro w hw
  simp only [lookupRoot, Option.getD, windowRoot, windowBits, windowPaths, List.mem_cons, List.mem_append,
    List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem corner_targets_large : ∀ w ∈ WEX.scrAllWires ++ WEX.yWires, 14115 ≤ w := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · have := WEX.scrAll_bounds w h
    dsimp only [Wire] at *
    omega
  · exact (WEX.yWires_bounds w h).1

theorem cornerTargets_nodup : (WEX.scrAllWires ++ WEX.yWires).Nodup := by
  rw [List.nodup_append]
  refine ⟨scrAllWires_nodup, WEX.yWires_nodup, ?_⟩
  intro a ha b hb hab
  subst hab
  exact WEX.scrAll_yWires a ha hb

theorem root_window_nodup : (windowRoot :: windowBits ++ windowPaths).Nodup := by decide +kernel

theorem cornerLoad_placed : PlacedPair windowBits windowPaths windowRoot
    (WInstr.lookup (n := 32768) (some windowRoot) (WEX.cornerPorts probeRows)) := by
  refine ⟨root_window_nodup, ?_, ?_, ?_⟩
  · rw [portTargets, List.map_take, ← portTargets, WEX.cornerPorts_targets]
    exact cornerTargets_nodup.sublist (List.take_sublist _ _)
  · rw [portTargets, List.map_drop, ← portTargets, WEX.cornerPorts_targets]
    exact cornerTargets_nodup.sublist (List.drop_sublist _ _)
  · rw [WEX.cornerPorts_targets]
    intro w hw hm
    have h1 := window_small w hw
    have h2 := corner_targets_large w hm
    dsimp only [Wire] at *
    omega

theorem yUnload_placed : PlacedPair windowBits windowPaths windowRoot
    (WInstr.lookup (n := 32768) (some windowRoot) (WEX.yPorts probeRows)) := by
  refine ⟨root_window_nodup, ?_, ?_, ?_⟩
  · rw [portTargets, List.map_take, ← portTargets, WEX.yPorts_targets]
    exact WEX.yWires_nodup.sublist (List.take_sublist _ _)
  · rw [portTargets, List.map_drop, ← portTargets, WEX.yPorts_targets]
    exact WEX.yWires_nodup.sublist (List.drop_sublist _ _)
  · rw [WEX.yPorts_targets]
    intro w hw hm
    have h1 := window_small w hw
    have h2 := (WEX.yWires_bounds w hm).1
    dsimp only [Wire] at *
    omega

theorem yUnload_placed' : Placed windowBits windowPaths windowRoot
    (WInstr.lookup (n := 32768) (some windowRoot) (WEX.yPorts probeRows)) := by
  refine ⟨root_window_nodup, ?_, ?_⟩
  · rw [WEX.yPorts_targets]; exact WEX.yWires_nodup
  · rw [WEX.yPorts_targets]
    intro w hw hm
    have h1 := window_small w hw
    have h2 := (WEX.yWires_bounds w hm).1
    dsimp only [Wire] at *
    omega

theorem hot_small (i : Fin 128) : hot i < 2058 := by
  show (1930 + i.val : Nat) < 2058
  have := i.isLt
  omega

theorem hot_avoid_large (L : List Wire) (hL : ∀ w ∈ L, 14115 ≤ w) (i : Fin 128) : hot i ∉ L :=
  fun h => absurd (lt_of_le_of_lt (hL _ h) (hot_small i)) (by decide)

theorem hot_avoid_source (p : ECDSAAdd.Program) (hs : ECDSAAdd.wires p ⊆ sourceSupport.toFinset) : HotAvoid (.literal (n := 32768) p) :=
  fun j hj => hot_outside_source j (List.mem_toFinset.mp (hs hj))

theorem sfxMid_sub_row : ∀ i ∈ sfxMidF probeRows, i ∈ clearReferenceRow probeRows := by
  intro i hi
  rw [WEX.clearReferenceRow_eq]
  simp [WEX.portFinite6, WEX.portSuffixCodeF, hi]

theorem sfxMid_hotavoid : ∀ i ∈ sfxMidF probeRows, HotAvoid i :=
  fun i hi => row_hotavoid i (sfxMid_sub_row i hi)

theorem sfxMid_physical : ∀ p, WInstr.literal p ∈ sfxMidF probeRows → GatePhysical p :=
  fun p hp => clearReferenceRow_physical p (sfxMid_sub_row _ hp)

theorem sfxMid_source : ∀ p, WInstr.literal p ∈ sfxMidF probeRows → ECDSAAdd.wires p ⊆ sourceSupport.toFinset :=
  fun p hp => clearReferenceRow_literal_source p (sfxMid_sub_row _ hp)

theorem cornerA1_hotavoid : ∀ i ∈ WEX.cornerA1, HotAvoid i := by
  intro i hi
  rcases WEX.cornerA1_mem i hi with h | rfl
  · exact sfxMid_hotavoid i h
  · exact hot_avoid_source _ WEX.scrCWrite_facts.2.2

theorem cornerA1_physical : ∀ p, WInstr.literal p ∈ WEX.cornerA1 → GatePhysical p := by
  intro p hp
  rcases WEX.cornerA1_mem _ hp with h | h
  · exact sfxMid_physical p h
  · cases h; exact WEX.scrCWrite_facts.2.1

theorem cornerA1_source : ∀ p, WInstr.literal p ∈ WEX.cornerA1 → ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  intro p hp
  rcases WEX.cornerA1_mem _ hp with h | h
  · exact sfxMid_source p h
  · cases h; exact WEX.scrCWrite_facts.2.2

theorem ySite_geometry : SiteGeometry ySite := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [ySite, MaskedSite.code, MaskedSite.prefix, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact yUnload_placed'
  · intro i hi
    simp only [ySite, MaskedSite.code, MaskedSite.prefix, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact fun j => by
      rw [WEX.yPorts_targets]; exact hot_avoid_large _ (fun w hw => (WEX.yWires_bounds w hw).1) j
  · right; right; right; right
    exact ⟨WEX.yPorts_targets probeRows, rfl⟩

theorem scrDClear_geometry : SiteGeometry scrDClear := by
  have hg := scrDSite_geometry
  refine ⟨?_, ?_, hg.kind⟩
  · intro i hi
    simp only [scrDClear, MaskedSite.code, MaskedSite.prefix, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact hg.placed _ scrD_unload_mem
  · intro i hi
    simp only [scrDClear, MaskedSite.code, MaskedSite.prefix, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact hg.bank _ scrD_unload_mem

theorem cornerUnit₁_geometry : UnitGeometry cornerUnit₁ := by
  refine ⟨?_, ?_, ySite_geometry⟩
  · intro i hi
    simp only [cornerUnit₁_code, WEX.cornerUnit₁, WEX.cornerPre₁, List.mem_append, List.mem_singleton] at hi
    rcases hi with (rfl | h) | rfl
    · exact cornerLoad_placed
    · exact WEX.cornerA1_placed i h
    · exact yUnload_placed
  · intro i hi
    simp only [cornerUnit₁_code, WEX.cornerUnit₁, WEX.cornerPre₁, List.mem_append, List.mem_singleton] at hi
    rcases hi with (rfl | h) | rfl
    · intro j; rw [WEX.cornerPorts_targets]; exact hot_avoid_large _ corner_targets_large j
    · exact cornerA1_hotavoid i h
    · intro j; rw [WEX.yPorts_targets]; exact hot_avoid_large _ (fun w hw => (WEX.yWires_bounds w hw).1) j

theorem cornerUnit₂_geometry : UnitGeometry cornerUnit₂ := by
  refine ⟨?_, ?_, scrDClear_geometry⟩
  · intro i hi
    simp only [cornerUnit₂_code, WEX.cornerUnit₂, List.mem_append, List.mem_singleton] at hi
    rcases hi with h | rfl
    · exact WEX.cornerA2_placed i h
    · exact scrD_lookup_placed
  · intro i hi
    simp only [cornerUnit₂_code, WEX.cornerUnit₂, List.mem_append, List.mem_singleton] at hi
    rcases hi with h | rfl
    · exact sfxMid_hotavoid i (WEX.cornerA2_sub i h)
    · exact scrDSite_geometry.bank _ scrD_unload_mem

theorem rowHead_sub (b : Block 32768) (hb : b ∈ rowHead) : b ∈ row2 := by
  rw [row2_eq]; exact List.mem_append_left _ hb

theorem tail_blocks_row2 (b : Block 32768) (hb : b ∈ rowPost) : b ∈ row2 := by
  rw [row2_eq]; exact List.mem_append_right _ hb

theorem sfxTail_geometry : BlockGeometry (.plain WEX.sfxTailF) :=
  row2_geometry _ (tail_blocks_row2 _ (by simp [rowPost]))

theorem x838_geometry : BlockGeometry (Block.plain (wLiteral (n := 32768) [.X 838])) :=
  row2_geometry _ (tail_blocks_row2 _ (by simp [rowPost]))

theorem rowC_geometry : ∀ b ∈ rowC, BlockGeometry2 b := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact geometry_toBlock2 c (row2_geometry c (rowHead_sub c hc))
  · simp only [rowPost3, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨WEX.cornerNeg_placed, fun i hi => sfxMid_hotavoid i (WEX.cornerNeg_sub i hi)⟩
    · exact cornerUnit₁_geometry
    · exact cornerUnit₂_geometry
    · exact sfxTail_geometry
    · exact x838_geometry

theorem sfxMid_sub_post : ∀ j ∈ sfxMidF probeRows, j ∈ erase rowPost := by
  intro j hj
  rw [erase_rowPost, scrDSite_code]
  simp [hj]

theorem scrD_unload_post : WInstr.lookup (n := 32768) (some windowRoot) (WEX.scrDPorts probeRows) ∈ erase rowPost := by
  rw [erase_rowPost, scrDSite_code]
  simp

theorem rowPost3_instrs (i : WInstr 32768) (hi : i ∈ erase2 rowPost3) :
    i ∈ erase rowPost ∨ i = .literal WEX.scrCWrite ∨
      i = .lookup (some windowRoot) (WEX.cornerPorts probeRows) ∨
      i = .lookup (some windowRoot) (WEX.yPorts probeRows) := by
  rw [erase2_rowPost3] at hi
  rcases List.mem_append.mp hi with h | h
  · exact Or.inl (sfxMid_sub_post i (WEX.cornerNeg_sub i h))
  rcases List.mem_append.mp h with h | h
  · rw [WEX.cornerUnit₁, WEX.cornerPre₁] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (Or.inr (Or.inl (List.mem_singleton.mp h)))
      · rcases WEX.cornerA1_mem i h with h' | h'
        · exact Or.inl (sfxMid_sub_post i h')
        · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (List.mem_singleton.mp h)))
  rcases List.mem_append.mp h with h | h
  · rw [WEX.cornerUnit₂] at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (sfxMid_sub_post i (WEX.cornerA2_sub i h))
    · rw [List.mem_singleton] at h
      subst h
      exact Or.inl scrD_unload_post
  · rw [erase_rowPost]
    exact Or.inl (List.mem_append_right _ h)

theorem rowC_instrs (i : WInstr 32768) (hi : i ∈ erase2 rowC) :
    i ∈ erase row2 ∨ i = .literal WEX.scrCWrite ∨
      i = .lookup (some windowRoot) (WEX.cornerPorts probeRows) ∨
      i = .lookup (some windowRoot) (WEX.yPorts probeRows) := by
  rw [rowC, erase2_append, erase2_map] at hi
  rw [row2_eq, erase_append]
  rcases List.mem_append.mp hi with h | h
  · exact Or.inl (List.mem_append_left _ h)
  · rcases rowPost3_instrs i h with h' | h'
    · exact Or.inl (List.mem_append_right _ h')
    · exact Or.inr h'

theorem rowC_physical : ∀ p, WInstr.literal p ∈ erase2 rowC → GatePhysical p := by
  intro p hp
  rcases rowC_instrs _ hp with h | h | h | h
  · exact row2_physical p h
  · cases h; exact WEX.scrCWrite_facts.2.1
  · cases h
  · cases h

theorem lookup_source_of (ps : List (LookupPort 32768)) (hs : ∀ w ∈ portTargets ps, w ∈ sourceSupport) :
    (∀ q ∈ (some windowRoot : Option Wire), q ∈ sourceSupport) ∧ portTargets ps ⊆ sourceSupport := by
  refine ⟨?_, hs⟩
  intro q hq
  simp only [Option.mem_def, Option.some.injEq] at hq
  subst hq
  rw [sourceSupport_mem]
  exact Or.inr WEX.windowRoot_oldWork

theorem rowC_oldWithin : OldWithin (erase2 rowC) := by
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases rowC_instrs _ hp with h | h | h | h
    · exact row2_oldWithin.1 p h
    · cases h; exact WEX.scrCWrite_facts.2.2
    · cases h
    · cases h
  · rcases rowC_instrs _ hp with h | h | h | h
    · exact row2_oldWithin.2 c ps h
    · cases h
    · cases h
      apply lookup_source_of
      rw [WEX.cornerPorts_targets]
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact WEX.scrAll_source w h
      · exact WEX.yWires_source w h
    · cases h
      apply lookup_source_of
      rw [WEX.yPorts_targets]
      exact WEX.yWires_source

end
end ShorECDLP.Entrant.WEXUnlookup

/-! #### Safety and the reference run of the corner row -/
namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000

attribute [local irreducible] streamLayout ECDSAAdd.regValue ECDSAAdd.run in
/-- After the common head of the row, the state is a dialog boundary: the pool is clean and the
point register holds a valid point. -/
theorem row6Head_exit (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s))
    (hroot : s windowRoot = true) (k : List Bool) :
    ∃ R' f, PointDialogBoundary streamLayout R' true f
      (run ((specialize (row6Head rows) address).instantiate read) k ⟨false,s⟩).basis := by
  classical
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hop := WEXUnlookup.row_opposite read rows address hc hr h₁
  have hpe := WEXUnlookup.prefixCode_equiv read streamLayout hw hn rows address hop
  have hpi := WEXUnlookup.referencePrefix_inst read streamLayout hw rows address hc hr h₁ h₂ hD hDo
  have hG : (specialize (wGeneric streamLayout rows) address).instantiate read = Arith.genericS streamLayout cx cy := by
    rw [specialize_generic]
    exact Arith.genericT_inst streamLayout hc hr
  have hclean0 : ∀ w ∈ scrWires, (⟨false, flipInfinity s⟩ : State).basis w = false :=
    fun w hw' => (regValue_zero _ _).mp hs.clean w (scrWires_pool w hw')
  let P0' := (specialize (portPrefixCode rows) address).instantiate read
  let P4 := (specialize (portPrefixCode4 rows) address).instantiate read
  let P0 := (specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read
  let G0 := (specialize (wGeneric streamLayout rows) address).instantiate read
  let C : Point := .some hc
  have hC0 : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  let O := dialogInfinity true R
  let D := dialogDouble true R C
  let I := dialogInversePoint true R C
  let H := dialogException true R C
  let Gf := dialogOrdinary true R C
  let E := true && decide (dialogExceptionEnabled C)
  let K := true && decide (cy≠-cy)
  have reads := dialogFlagState_read streamLayout hn O D I Gf E H K
  let A : Program := ([.X 838] : Program) ++ P0' ++ G0
  have hbound : ∀ k, PointDialogBoundary streamLayout (if Gf then R + C else R) true
      (dialogFlagState streamLayout O D I Gf E H K) (run A k ⟨false,s⟩).basis := by
    intro k
    have h7 := Arith.boundary_genericS streamLayout hw hn R true (dialogFlagState streamLayout O D I Gf E H K) hc
      (fun hg => ((dialogOrdinary_true true R C hC0).mp (reads.2.2.2.1.symm.trans hg)).2)
    rw [reads.2.2.2.1] at h7
    have hP (k' : List Bool) : PointDialogBoundary streamLayout R true (dialogFlagState streamLayout O D I Gf E H K)
        (run P0 k' ⟨false, flipInfinity s⟩).basis := by
      have hb := (WEXUnlookup.prefixS_checked streamLayout hw hn R hc true ⟨false, flipInfinity s⟩ k' hs).2
      have he := hpe.2 k' ⟨false, flipInfinity s⟩
      rw [hpi] at he
      change PointDialogBoundary streamLayout R true (dialogFlagState streamLayout O D I Gf E H K)
        (run ((specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read) k' ⟨false, flipInfinity s⟩).basis
      rw [← he]
      exact hb
    obtain ⟨k1, k2, hA⟩ := portRun_split ([.X 838] : Program) P0' G0 ⟨false,s⟩ ⟨false, flipInfinity s⟩
      (fun n => flip_run _ n) k
    change PointDialogBoundary _ _ _ _ (run (([.X 838] : Program) ++ P0' ++ G0) k ⟨false,s⟩).basis
    rw [hA]
    have hpp : run P0' k2 ⟨false, flipInfinity s⟩ = run P0 k2 ⟨false, flipInfinity s⟩ :=
      portPrefix_run read rows address hop k2 _ hclean0
    rw [hpp]
    have hG' : G0 = Arith.genericS streamLayout cx cy := hG
    have hu := (h7 (run P0 k2 ⟨false, flipInfinity s⟩) k1 (hP _)).2
    rw [← hG'] at hu
    exact hu
  have e6 : (specialize (row6Head rows) address).instantiate read = ([.X 838] : Program) ++ P4 ++ G0 := by
    simp only [row6Head, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, P4, G0]
  have hrun : run ((specialize (row6Head rows) address).instantiate read) k ⟨false,s⟩ = run A k ⟨false,s⟩ := by
    rw [e6]
    apply portSuffix_middle _ _ _ _ (portPrefix4_records read rows address) ⟨false,s⟩
    intro k' n
    rw [flip_run]
    apply portPrefix4_eq3 read rows address n
    change flipInfinity s windowRoot = true
    simpa [flipInfinity, ECDSAAdd.writeBit, Function.update, windowRoot] using hroot
  with_reducible rw [hrun]
  exact ⟨_, _, hbound k⟩

/-- The facts the corner block needs at its entry. -/
theorem boundary_entry (R : Point) (f : BasisState) (t : State)
    (hb : PointDialogBoundary streamLayout R true f t.basis) :
    ECDSAAdd.regValue streamLayout.dialogPool t.basis = 0 ∧
      ECDSAAdd.regValue streamLayout.point.y t.basis < ECDSAAdd.p := by
  refine ⟨hb.clean, ?_⟩
  rw [((point_holds _ _ _).mp hb.point).2.2]
  exact (point_coordinates_lt _).2

/-- The corner reference (negation, two units) equals the leader's site on a boundary state. -/
theorem cornerRef_eq_leader (read : ConstantBit 32768 → Bool) (a : Nat) (m : List Bool) (t : State)
    (hr : t.basis windowRoot = true) (hpool : ECDSAAdd.regValue streamLayout.dialogPool t.basis = 0)
    (hy : ECDSAAdd.regValue streamLayout.point.y t.basis < ECDSAAdd.p) :
    run ((specialize (cornerNeg ++ (cornerUnit₁ ++ cornerUnit₂)) a).instantiate read) m t =
      run ((specialize WEXUnlookup.scrDSite.code a).instantiate read) m t := by
  have hD : ∀ w ∈ scrAllWires, t.basis w = false := fun w hw => (regValue_zero _ _).mp hpool w (scrAll_pool w hw)
  rw [leader_reduce read a m t hr hD, specialize_append, Tmpl.instantiate_append, cornerNeg_inst,
    run_append, run_append (scrNegE ++ (scrNegP ++ scrNegE))]
  obtain ⟨hr', hpool'⟩ := cornerNeg_run (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t hr hpool hy
  have hD' : ∀ w ∈ scrAllWires, (run (scrNegE ++ (scrNegP ++ scrNegE)) (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t).basis w = false :=
    fun w hw => (regValue_zero _ _).mp hpool' w (scrAll_pool w hw)
  have hY' : ∀ w ∈ yWires, (run (scrNegE ++ (scrNegP ++ scrNegE)) (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t).basis w = false :=
    fun w hw => (regValue_zero _ _).mp hpool' w (yWires_pool w hw)
  exact (corner_reduce read a _ _ hr' hD' hY').1

/-- The `scrD` word is clean after the corner reference. -/
theorem cornerRef_clean (read : ConstantBit 32768 → Bool) (a : Nat) (m : List Bool) (t : State)
    (hr : t.basis windowRoot = true) (hpool : ECDSAAdd.regValue streamLayout.dialogPool t.basis = 0)
    (hy : ECDSAAdd.regValue streamLayout.point.y t.basis < ECDSAAdd.p) :
    ∀ w ∈ scrAllWires,
      (run ((specialize (cornerNeg ++ (cornerUnit₁ ++ cornerUnit₂)) a).instantiate read) m t).basis w = false := by
  rw [specialize_append, Tmpl.instantiate_append, cornerNeg_inst, run_append]
  obtain ⟨hr', hpool'⟩ := cornerNeg_run (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t hr hpool hy
  have hD' : ∀ w ∈ scrAllWires, (run (scrNegE ++ (scrNegP ++ scrNegE)) (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t).basis w = false :=
    fun w hw => (regValue_zero _ _).mp hpool' w (scrAll_pool w hw)
  have hY' : ∀ w ∈ yWires, (run (scrNegE ++ (scrNegP ++ scrNegE)) (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t).basis w = false :=
    fun w hw => (regValue_zero _ _).mp hpool' w (yWires_pool w hw)
  have h := corner_reduce read a (m.drop (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) _ hr' hD' hY'
  rw [h.1]
  exact h.2

/-- The `y` word is clean after the first corner unit. -/
theorem cornerRef_yclean (read : ConstantBit 32768 → Bool) (a : Nat) (m : List Bool) (t : State)
    (hr : t.basis windowRoot = true) (hpool : ECDSAAdd.regValue streamLayout.dialogPool t.basis = 0)
    (hy : ECDSAAdd.regValue streamLayout.point.y t.basis < ECDSAAdd.p) :
    ∀ w ∈ yWires,
      (run ((specialize (cornerNeg ++ cornerUnit₁) a).instantiate read) m t).basis w = false := by
  rw [specialize_append, Tmpl.instantiate_append, cornerNeg_inst, run_append]
  obtain ⟨hr', hpool'⟩ := cornerNeg_run (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t hr hpool hy
  have hD' : ∀ w ∈ scrAllWires, (run (scrNegE ++ (scrNegP ++ scrNegE)) (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t).basis w = false :=
    fun w hw => (regValue_zero _ _).mp hpool' w (scrAll_pool w hw)
  have hY' : ∀ w ∈ yWires, (run (scrNegE ++ (scrNegP ++ scrNegE)) (m.take (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) t).basis w = false :=
    fun w hw => (regValue_zero _ _).mp hpool' w (yWires_pool w hw)
  exact corner_yclean read a (m.drop (ECDSAAdd.measurementCount (scrNegE ++ (scrNegP ++ scrNegE)))) _ hr' hD' hY'

end
end ShorECDLP.Entrant.WEX

namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] ECDSAAdd.run

theorem erase_rowHead_generic : erase (rowPre ++ generic streamLayout probeRows) = WEX.row6Head probeRows := by
  rw [erase_append,erase_generic]
  simp only [erase,rowPre,List.flatMap_cons,List.flatMap_nil,Block.code,List.append_nil,WEX.row6Head,
    WEX.portPrefixCode4,scrHead,List.append_assoc]

theorem reference_rowPost (read : ConstantBit 32768 → Bool) (a : Nat) :
    reference read a rowPost = (specialize scrDSite.code a).instantiate read ++
      ((specialize WEX.sfxTailF a).instantiate read ++ (specialize (wLiteral [.X 838]) a).instantiate read) := by
  simp only [reference, erase_rowPost, specialize_append, ECDSAAdd.ShorPort.Tmpl.instantiate_append]

theorem reference2_rowPost3 (read : ConstantBit 32768 → Bool) (a : Nat) :
    reference2 read a rowPost3 = (specialize (WEX.cornerNeg ++ (WEX.cornerUnit₁ ++ WEX.cornerUnit₂)) a).instantiate read ++
      ((specialize WEX.sfxTailF a).instantiate read ++ (specialize (wLiteral [.X 838]) a).instantiate read) := by
  simp only [reference2, erase2_rowPost3, specialize_append, ECDSAAdd.ShorPort.Tmpl.instantiate_append,
    List.append_assoc]

/-- The entry state of the corner block, for every record list of the head. -/
theorem rowHead_entry (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s))
    (hroot : s windowRoot = true) (m : List Bool) :
    (ECDSAAdd.run (reference read address rowHead) m ⟨false,s⟩).basis windowRoot = true ∧
      ECDSAAdd.regValue streamLayout.dialogPool (ECDSAAdd.run (reference read address rowHead) m ⟨false,s⟩).basis = 0 ∧
      ECDSAAdd.regValue streamLayout.point.y (ECDSAAdd.run (reference read address rowHead) m ⟨false,s⟩).basis <
        ECDSAAdd.p := by
  have gen := generic2_cases read address probeRows R true (flags streamLayout R (.some hc) true cy)
    hc hr (flags_generic R hc) _ (rowPre_boundary read address R hc hr h₁ h₂ hD hDo s hs hroot m)
  have e : ECDSAAdd.run (reference read address rowHead) m ⟨false,s⟩ =
      ECDSAAdd.run ((specialize (WEX.row6Head probeRows) address).instantiate read) m ⟨false,s⟩ := by
    rw [rowHead, reference_append, run_meas_append, gen.2, ← run_meas_append, ← reference_append,
      reference, erase_rowHead_generic]
  rw [e]
  obtain ⟨R', f, hb⟩ := WEX.row6Head_exit read probeRows address R hc hr h₁ h₂ hD hDo s hs hroot m
  have hpl : ∀ i ∈ WEX.row6Head probeRows, PlacedPair windowBits windowPaths windowRoot i := by
    intro i hi
    apply WEX.portRow6_placed
    rw [(WEX.portRow6_shape probeRows).2]
    exact List.mem_append_left _ hi
  refine ⟨WEX.root_preserves read windowBits windowPaths windowRoot _ address hpl ⟨false,s⟩ hroot m, ?_⟩
  exact WEX.boundary_entry R' f _ hb

theorem rowPost3_safe (read : ConstantBit 32768 → Bool) (a : Nat) (t : ECDSAAdd.State)
    (hr : t.basis windowRoot = true) (hpool : ECDSAAdd.regValue streamLayout.dialogPool t.basis = 0)
    (hy : ECDSAAdd.regValue streamLayout.point.y t.basis < ECDSAAdd.p) :
    Safe2 read a rowPost3 t := by
  refine ⟨True.intro, fun m₁ hm₁ => ⟨?_, fun m₂ hm₂ => ⟨?_, fun _ _ =>
    ⟨True.intro, fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩⟩⟩⟩⟩
  · intro m₃ w hw
    change w ∈ portTargets (WEX.yPorts probeRows) at hw
    rw [WEX.yPorts_targets] at hw
    have hm₁' : m₁.length = ECDSAAdd.measurementCount ((specialize WEX.cornerNeg a).instantiate read) := hm₁
    have h := WEX.cornerRef_yclean read a (m₁ ++ m₃) t hr hpool hy w hw
    rw [specialize_append, ECDSAAdd.ShorPort.Tmpl.instantiate_append, run_append_records _ _ m₁ m₃ t hm₁'] at h
    exact h
  · intro m₃ w hw
    change w ∈ portTargets (WEX.scrDPorts probeRows) at hw
    rw [WEX.scrDPorts_targets] at hw
    have hm₁' : m₁.length = ECDSAAdd.measurementCount ((specialize WEX.cornerNeg a).instantiate read) := hm₁
    have hm₂' : m₂.length = ECDSAAdd.measurementCount ((specialize WEX.cornerUnit₁ a).instantiate read) := hm₂
    have h := WEX.cornerRef_clean read a (m₁ ++ (m₂ ++ m₃)) t hr hpool hy w hw
    rw [specialize_append, ECDSAAdd.ShorPort.Tmpl.instantiate_append, specialize_append,
      ECDSAAdd.ShorPort.Tmpl.instantiate_append, run_append_records _ _ m₁ (m₂ ++ m₃) t hm₁',
      run_append_records _ _ m₂ m₃ _ hm₂'] at h
    exact h

theorem corner_records_eq (read : ConstantBit 32768 → Bool) (a : Nat) :
    ECDSAAdd.measurementCount ((specialize (WEX.cornerNeg ++ (WEX.cornerUnit₁ ++ WEX.cornerUnit₂)) a).instantiate read) =
      ECDSAAdd.measurementCount ((specialize scrDSite.code a).instantiate read) := by
  rw [(specialize_counts read _ a).2, (specialize_counts read _ a).2, scrDSite_code]
  have h0 : ECDSAAdd.measurementCount WEX.scrCWrite = 0 := ccxList_records _ _ _
  simp only [WEX.cornerNeg, WEX.cornerUnit₁, WEX.cornerUnit₂, WEX.cornerPre₁, WEX.cornerA1, WEX.cornerA2,
    sfxMidF, cornersE_split, sfxCC, wLiteral, literalRecords_append, literalRecords, h0]
  omega

theorem rowPost3_run (read : ConstantBit 32768 → Bool) (a : Nat) (t : ECDSAAdd.State)
    (hr : t.basis windowRoot = true) (hpool : ECDSAAdd.regValue streamLayout.dialogPool t.basis = 0)
    (hy : ECDSAAdd.regValue streamLayout.point.y t.basis < ECDSAAdd.p) (m : List Bool) :
    ECDSAAdd.run (reference2 read a rowPost3) m t = ECDSAAdd.run (reference read a rowPost) m t := by
  rw [reference2_rowPost3, reference_rowPost,
    ECDSAAdd.run_append ((specialize (WEX.cornerNeg ++ (WEX.cornerUnit₁ ++ WEX.cornerUnit₂)) a).instantiate read),
    ECDSAAdd.run_append ((specialize scrDSite.code a).instantiate read), corner_records_eq,
    WEX.cornerRef_eq_leader read a _ t hr hpool hy]

/-- From the row-entry boundary, the corner row is safe and keeps the fused row's reference run. -/
theorem rowC_facts (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s))
    (hroot : s windowRoot = true) :
    Safe2 read address rowC ⟨false,s⟩ ∧
      ∀ m, ECDSAAdd.run (reference2 read address rowC) m ⟨false,s⟩ =
        ECDSAAdd.run (reference read address row2) m ⟨false,s⟩ := by
  have hsafe2 : Safe read address row2 ⟨false,s⟩ := (row2_facts read address R hc hr h₁ h₂ hD hDo s hs hroot).1
  have hhead : Safe read address rowHead ⟨false,s⟩ := by
    rw [row2_eq] at hsafe2; exact safe_left _ _ _ _ _ hsafe2
  constructor
  · rw [rowC]
    apply safe2_append _ _ _ _ _ (safe2_map _ _ _ _ hhead)
    intro m hm
    rw [reference2_map]
    obtain ⟨hr', hpool', hy'⟩ := rowHead_entry read address R hc hr h₁ h₂ hD hDo s hs hroot m
    exact rowPost3_safe read address _ hr' hpool' hy'
  · intro m
    rw [rowC, row2_eq, reference2_append, reference_append, reference2_map, run_meas_append, run_meas_append]
    obtain ⟨hr', hpool', hy'⟩ := rowHead_entry read address R hc hr h₁ h₂ hD hDo s hs hroot m
    exact rowPost3_run read address _ hr' hpool' hy' _

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

theorem rowC_safe_run (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    Safe2 (readConstant coeffs Q) a rowC ⟨false,s⟩ ∧
      ∀ m, ECDSAAdd.run (reference2 (readConstant coeffs Q) a rowC) m ⟨false,s⟩ =
        ECDSAAdd.run (reference (readConstant coeffs Q) a row2) m ⟨false,s⟩ := by
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
    exact rowC_facts (readConstant coeffs Q) a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial hs.2.2

theorem rowC_run_any (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (s : BasisState) (hs : liveReady s)
    (m : List Bool) :
    ECDSAAdd.run (reference2 (readConstant coeffs Q) a rowC) m ⟨false,s⟩ =
      ⟨false,pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q a) s⟩ := by
  rw [(rowC_safe_run coeffs Q hQ hn a s hs).2 m]
  exact row2_run_any a coeffs Q hQ hn s hs m

end
end ShorECDLP.Entrant.WEXUnlookup

/-! #### Counts of the corner row -/
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem blockLen2_toBlock2 (b : Block 32768) : blockLen2 (toBlock2 b) = blockLen b := by cases b <;> rfl
theorem blockMasks2_toBlock2 (b : Block 32768) : blockMasks2 (toBlock2 b) = blockMasks b := by cases b <;> rfl
theorem blockRecords2_toBlock2 (b : Block 32768) : blockRecords2 (toBlock2 b) = blockRecords b := by cases b <;> rfl
theorem blockCCX2_toBlock2 (b : Block 32768) : blockCCX2 (toBlock2 b) = blockCCX b := by cases b <;> rfl

theorem lens2_map (code : Code 32768) : lens2 (code.map toBlock2) = lens code := by
  induction code with
  | nil => rfl
  | cons b code ih => simp [lens2, lens, blockLen2_toBlock2, ih]
theorem masks2_map (code : Code 32768) : masks2 (code.map toBlock2) = masks code := by
  induction code with
  | nil => rfl
  | cons b code ih => simp [masks2, masks, blockMasks2_toBlock2, ih]
theorem records2_map (code : Code 32768) : records2 (code.map toBlock2) = records code := by
  induction code with
  | nil => rfl
  | cons b code ih => simp [records2, records, blockRecords2_toBlock2, ih]
theorem ccx2_map (code : Code 32768) : ccx2 (code.map toBlock2) = ccx code := by
  induction code with
  | nil => rfl
  | cons b code ih => simp [ccx2, ccx, blockCCX2_toBlock2, ih]

theorem masks_append' (a b : Code 32768) : masks (a ++ b) = masks a + masks b := by
  induction a with
  | nil => simp [masks]
  | cons x a ih => simp [masks,ih,Nat.add_assoc]

theorem rowC_masks : masks2 rowC = 6 := by
  have h := row2_masks
  rw [row2_eq, masks_append'] at h
  rw [rowC, masks2_append, masks2_map]
  have hp : masks rowPost = 1 := rfl
  have hq : masks2 rowPost3 = 2 := rfl
  omega

theorem rowPost_lens : lens rowPost = 771 := by
  have hd : (WEX.scrDPorts probeRows).length = 771 := WEX.scrDPorts_length probeRows
  simp [rowPost, lens, blockLen, scrDSite, hd]

theorem rowPost3_lens : lens2 rowPost3 = 1027 := by
  have hd : (WEX.scrDPorts probeRows).length = 771 := WEX.scrDPorts_length probeRows
  have hy : (WEX.yPorts probeRows).length = 256 := WEX.yPorts_length probeRows
  simp [rowPost3, lens2, blockLen2, cornerUnit₁, cornerUnit₂, ySite, scrDClear, hd, hy]

theorem rowC_lens : lens2 rowC = 2823 := by
  have h := row2_lens
  rw [row2_eq, lens_append, rowPost_lens] at h
  rw [rowC, lens2_append, lens2_map, rowPost3_lens]
  omega

theorem rowC_placed : ∀ i ∈ erase2 rowC, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  exact (block2_placed b (rowC_geometry b hb)).1 i hib

theorem scrCWrite_counts : ECDSAAdd.measurementCount WEX.scrCWrite = 0 ∧
    ECDSAAdd.toffoliCount WEX.scrCWrite = 513 ∧ ECDSAAdd.Challenge.gateSlots WEX.scrCWrite = 513 := by
  have hl : WEX.cSources.length = 513 := by
    simp [WEX.cSources, List.length_take, scrPairWires_length, WEX.yWires_length]
  have hT : scrDTargets.length = 513 := by
    have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
    have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
    simp [scrDTargets, hx, hy]
  refine ⟨ccxList_records _ _ _, ?_, ?_⟩
  · rw [WEX.scrCWrite, ccxList_toffoli, hl, hT]; exact Nat.min_self _
  · rw [WEX.scrCWrite, ccxList_slots, hl, hT]; exact Nat.min_self _

theorem cPorts_length : (WEX.scrCPorts probeRows).length = 513 := by
  have h := congrArg List.length (WEX.scr_point_targets (wBit probeRows .infinity) (wFields probeRows .x) (wFields probeRows .y))
  simp only [portTargets, List.length_map] at h
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  rw [WEX.scrCPorts]
  simp [WEXUnlookup.indexed_length, hx, hy]

theorem cornerPorts_length : (WEX.cornerPorts probeRows).length = 1027 := by
  rw [WEX.cornerPorts, List.length_append, WEX.scrDPorts_length, WEX.yPorts_length]

/-! Measures of the literal and lookup singletons, generic in the program (no unfolding on concrete code). -/
theorem lit_toffolis (p : ECDSAAdd.Program) : literalToffolis (wLiteral (n := 32768) p) = ECDSAAdd.toffoliCount p := by
  simp [wLiteral, literalToffolis]
theorem lit_traversals (p : ECDSAAdd.Program) : traversals (wLiteral (n := 32768) p) = 0 := by
  simp [wLiteral, traversals]
theorem lit_records (p : ECDSAAdd.Program) : literalRecords (wLiteral (n := 32768) p) = ECDSAAdd.measurementCount p := by
  simp [wLiteral, literalRecords]
theorem lit_slots (p : ECDSAAdd.Program) : literalSlotSum (wLiteral (n := 32768) p) = ECDSAAdd.Challenge.gateSlots p := by
  simp [wLiteral, literalSlotSum]
theorem lit_ports (p : ECDSAAdd.Program) : portTotal (wLiteral (n := 32768) p) = 0 := by
  simp [wLiteral, portTotal]
theorem look_toffolis (c : Option Wire) (ps : List (LookupPort 32768)) :
    literalToffolis ([.lookup c ps] : WCode 32768) = 0 := by simp [literalToffolis]
theorem look_traversals (c : Option Wire) (ps : List (LookupPort 32768)) :
    traversals ([.lookup c ps] : WCode 32768) = 1 := by simp [traversals]
theorem look_records (c : Option Wire) (ps : List (LookupPort 32768)) :
    literalRecords ([.lookup c ps] : WCode 32768) = 0 := by simp [literalRecords]
theorem look_slots (c : Option Wire) (ps : List (LookupPort 32768)) :
    literalSlotSum ([.lookup c ps] : WCode 32768) = 0 := by simp [literalSlotSum]
theorem look_ports (c : Option Wire) (ps : List (LookupPort 32768)) :
    portTotal ([.lookup c ps] : WCode 32768) = ps.length := by simp [portTotal]

theorem rowPost3_toffolis : literalToffolis (erase2 rowPost3) = literalToffolis (erase rowPost) + 513 := by
  have hc := scrCWrite_counts
  rw [erase2_rowPost3, erase_rowPost, scrDSite_code]
  simp only [WEX.cornerNeg, WEX.cornerUnit₁, WEX.cornerUnit₂, WEX.cornerPre₁, WEX.cornerA1, WEX.cornerA2,
    sfxMidF, cornersE_split, sfxCC, literalToffolis_append, lit_toffolis, look_toffolis, hc.2.1]
  omega

theorem rowPost3_traversals : traversals (erase2 rowPost3) = traversals (erase rowPost) := by
  rw [erase2_rowPost3, erase_rowPost, scrDSite_code]
  simp only [WEX.cornerNeg, WEX.cornerUnit₁, WEX.cornerUnit₂, WEX.cornerPre₁, WEX.cornerA1, WEX.cornerA2,
    sfxMidF, cornersE_split, sfxCC, traversals_append, lit_traversals, look_traversals]
  omega

theorem rowPost3_records : literalRecords (erase2 rowPost3) = literalRecords (erase rowPost) := by
  have hc := scrCWrite_counts
  rw [erase2_rowPost3, erase_rowPost, scrDSite_code]
  simp only [WEX.cornerNeg, WEX.cornerUnit₁, WEX.cornerUnit₂, WEX.cornerPre₁, WEX.cornerA1, WEX.cornerA2,
    sfxMidF, cornersE_split, sfxCC, literalRecords_append, lit_records, look_records, hc.1]
  omega

theorem rowPost3_slots : literalSlotSum (erase2 rowPost3) = literalSlotSum (erase rowPost) + 513 := by
  have hc := scrCWrite_counts
  rw [erase2_rowPost3, erase_rowPost, scrDSite_code]
  simp only [WEX.cornerNeg, WEX.cornerUnit₁, WEX.cornerUnit₂, WEX.cornerPre₁, WEX.cornerA1, WEX.cornerA2,
    sfxMidF, cornersE_split, sfxCC, literalSlotSum_append', lit_slots, look_slots, hc.2.2]
  omega

theorem rowPost3_ports : portTotal (erase2 rowPost3) + 1 = portTotal (erase rowPost) := by
  have hcl := cPorts_length
  have hpl := cornerPorts_length
  have hyl := WEX.yPorts_length probeRows
  have hdl := WEX.scrDPorts_length probeRows
  rw [erase2_rowPost3, erase_rowPost, scrDSite_code]
  simp only [WEX.cornerNeg, WEX.cornerUnit₁, WEX.cornerUnit₂, WEX.cornerPre₁, WEX.cornerA1, WEX.cornerA2,
    sfxMidF, cornersE_split, sfxCC, portTotal_append', lit_ports, look_ports, hcl, hpl, hyl, hdl]
  omega

/-- The corner tail against the fused row's tail: one more literal, the same traversal count. -/
theorem rowPost3_measures :
    literalToffolis (erase2 rowPost3) = literalToffolis (erase rowPost) + 513 ∧
    traversals (erase2 rowPost3) = traversals (erase rowPost) ∧
    literalRecords (erase2 rowPost3) = literalRecords (erase rowPost) ∧
    literalSlotSum (erase2 rowPost3) = literalSlotSum (erase rowPost) + 513 ∧
    portTotal (erase2 rowPost3) + 1 = portTotal (erase rowPost) :=
  ⟨rowPost3_toffolis, rowPost3_traversals, rowPost3_records, rowPost3_slots, rowPost3_ports⟩

theorem rowC_measures :
    literalToffolis (erase2 rowC) = literalToffolis (clearReferenceRow probeRows) + 513 ∧
    traversals (erase2 rowC) = 11 ∧
    literalSlotSum (erase2 rowC) ≤ literalSlotSum (clearReferenceRow probeRows) + 33866 + 513 ∧
    portTotal (erase2 rowC) ≤ portTotal (clearReferenceRow probeRows) ∧
    literalRecords (erase2 rowC) = literalRecords (erase row2) := by
  have g := rowPost3_measures
  have h2 := row2_measures
  have e3 : erase2 rowC = erase rowHead ++ erase2 rowPost3 := by
    rw [rowC, erase2_append, erase2_map]
  have e2 : erase row2 = erase rowHead ++ erase rowPost := by
    rw [row2_eq, erase_append]
  rw [e3]
  rw [e2] at h2 ⊢
  simp only [literalToffolis_append, traversals_append, literalSlotSum_append', portTotal_append',
    literalRecords_append] at h2 g ⊢
  omega

theorem rowC_codeRecords : codeRecords windowBits windowPaths windowRoot (normalizeW (erase2 rowC)) =
    codeRecords windowBits windowPaths windowRoot (normalizeW (erase row2)) := by
  have l3 := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW (erase2 rowC))
    (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ rowC_placed)
  have hp2 : ∀ i ∈ erase row2, PlacedPair windowBits windowPaths windowRoot i := by
    intro i hi
    obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
    exact (block_placed b (row2_geometry b hb)).1 i hib
  have l2 := pair_layouts_of_placed windowBits windowPaths windowRoot (normalizeW (erase row2))
    (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp2)
  rw [codeRecords_eq _ _ _ _ l3, codeRecords_eq _ _ _ _ l2, literalRecords_normalize, literalRecords_normalize,
    traversals_normalize, traversals_normalize, rowC_measures.2.2.2.2, rowC_measures.2.1, row2_measures.2.1]

theorem rowC_records : records2 rowC = 1725849 := by
  have h := records2_relation rowC rowC_geometry
  rw [rowC_masks, rowC_lens, rowC_codeRecords, row2_measures.2.2.2.2] at h
  omega

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx2 Nat.add Nat.mul in
theorem rowC_ccx_upper : ccx2 rowC ≤ 2330032 := by
  have h := ccx2_relation rowC
  have hn := WEX.literalToffolis_normalize (erase2 rowC)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis,h0]
  rw [rowC_masks, rowC_measures.2.1] at h
  rw [rowC_measures.1, hrow] at hn
  omega

theorem rowC_slots (start : Nat) : (program2 rowC start).gateSlots =
    codeSlots windowBits (normalizeW (erase2 rowC)) + 275567592 := by
  have h := program2_slots_relation rowC rowC_geometry start
  rw [rowC_masks, rowC_lens] at h
  omega

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem rowC_wellFormed (start : Nat) : (program2 rowC start).WellFormed :=
  program2_wellFormed rowC rowC_geometry rowC_physical start

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem rowC_support (start : Nat) : ChallengeMigration.straightWires (program2 rowC start) ⊆ logicalSupport :=
  program2_support rowC rowC_geometry rowC_oldWithin start

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem rowC_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program2 rowC start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program2_coherent (readConstant coeffs Q) rowC rowC_geometry liveReady (rowPointState coeffs Q)
    (fun s hs => (rowC_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs m => rowC_run_any _ coeffs Q hQ hn s hs m) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩

def rowSource3 (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode2 (readConstant coeffs Q) rowC

theorem rowSource3_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSource3 coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  obtain ⟨cs,aligned,mass⟩ := rowC_coherent coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs,?_,mass⟩
  simpa only [program2_run,rowSource3] using aligned

attribute [local irreducible] Straight.instantiate AdaptiveCircuit.tCount AdaptiveCircuit.run
  program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram WEX.codeRecords WEX.codeSlots WEX.literalToffolis
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps ccx2 masks2

def addFixed3 (start : Nat) : Straight 32768 start (start+1725849) :=
  castFinish (congrArg (fun m => start+m) rowC_records) (program2 rowC start)

theorem addFixed3_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed3 start).instantiate read history).run = (sourceCode2 read rowC).run := by
  rw [addFixed3,castFinish_instantiate,program2_run]

theorem addFixed3_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed3 start).instantiate read history).tCount = 7*ccx2 rowC := by
  rw [addFixed3,castFinish_instantiate,program2_tCount read rowC rowC_geometry]

theorem addFixed3_slots (start : Nat) : (addFixed3 start).gateSlots =
    codeSlots windowBits (normalizeW (erase2 rowC)) + 275567592 := by
  rw [addFixed3,castFinish_gateSlots,rowC_slots]

theorem addFixed3_wellFormed (start : Nat) : (addFixed3 start).WellFormed := by
  rw [addFixed3,castFinish_wellFormed]
  exact rowC_wellFormed start

theorem addFixed3_support (start : Nat) : ChallengeMigration.straightWires (addFixed3 start) ⊆ logicalSupport := by
  rw [addFixed3,support_cast]
  exact rowC_support start

open AndGadget in
theorem addFixed3_residue (start : Nat) : residue (addFixed3 start) = 0 := by
  rw [addFixed3,residue_cast]
  exact program2_residue rowC start

open AndGadget WEXCredit in
theorem addFixed3_credit (start : Nat) : ProgramCredit (addFixed3 start) (ccx2 rowC) := by
  have hz := addFixed3_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed3 start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed3_tCount (fun _ => false) start (fun _ => false)
  omega

end
end ShorECDLP.Entrant.WEXUnlookup

/-! ### The width-15 body on the corner row -/
namespace ShorECDLP.Entrant.WEXUnlookup.Width15Corner
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program2 blockProgram2 clearProgram addFixed3 WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx2 Nat.add Nat.mul
def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSource3 coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource3_coherent coeffs Q hQ hn)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)
def fastBodyProgram (start : Nat) : Straight 32768 start (start+1726361) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed3 (start+256))).append
      (nFastProgram (start+256+1725849))).append (suffixProgram (start+256+1725849+256)))

attribute [local irreducible] fastBodyProgram

theorem fastBodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode2 read rowC)).seq fastSignSource)).seq suffixSource).run := by
  rw [fastBodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource fastSignSource (sourceCode2 read rowC) fastSignSource suffixSource
    (prefixProgram_run _ read) (nFastProgram_run _ read) (addFixed3_run read _)
    (nFastProgram_run _ read) (suffixProgram_run _ read) history

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode2 (readConstant coeffs Q) rowC)).seq fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSource3
    rfl
  have hr := fastBodyProgram_run_read (readConstant coeffs Q) start history
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs,aligned,mass⟩ := fastBodySource_coherent coeffs Q hQ hn
  refine ⟨cs,?_,mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx2 rowC) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1725849)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx2 rowC) (prefix_credit start) hl (addFixed3_credit (start+256)) hr
    (suffix_credit (start+256+1725849+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx2 rowC) := by
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
      · exact addFixed3_wellFormed _
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
    addFixed3_support _⟩,(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,addFixed3_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (erase2 rowC))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.rowC_measures
  have hl2 := hm.2.2.1
  have hp2 := hm.2.2.2.1
  rw [hm.2.1] at hc
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  norm_num [windowBits] at hc
  simp only [windowBits]
  omega
def fastCompactProgram (start : Nat) : Straight 32768 start (start+1726361) :=
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
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastCompactProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (compactState coeffs Q))
      (fun s => WEXUnlookup.compactReady s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have hc : CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready :=
    fastBodyProgram_coherent coeffs Q hQ hn start history
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
    ccx2 rowC ≤ 2330536 := by
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := rowC_ccx_upper
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 15 where
  records := 1726361
  tBound := 16313752
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx2 rowC
  program := fastCompactProgram
  coherent := by
    intro coeffs Q hQ hn _ start history
    have h := fastCompactProgram_coherent coeffs Q hQ hn start history
    simpa only [Single.BodyValid, WEXUnlookup.compactBody] using h
  wellFormed := by
    intro start
    rw [fastCompactProgram]
    exact (relabelStraight_wellFormed WEX.compactPerm (fastBodyProgram start)).mpr (fastBodyProgram_wellFormed start)
  slots := by
    intro start
    rw [fastCompactProgram,relabelStraight_slots]
    exact (fastBodyProgram_slots_upper start).trans (by rw [WEXUnlookup.compactBody])
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
end ShorECDLP.Entrant.WEXUnlookup.Width15Corner

-- ===== formerly CornerRow14 =====

/-! The corner row at physical width 14. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] MeasuredClear.measuredClear

def blockRecords2 {n} : Block2 n → Nat
  | .plain code => codeRecords bits windowPaths windowRoot (normalizeW code)
  | .unit u => codeRecords bits windowPaths windowRoot (normalizeW u.pre) +
      u.clear.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) u.clear.guard highPaths)+127)

def blockProgram2 {n} (b : Block2 n) (start : Nat) : Straight n start (start+blockRecords2 b) :=
  match b with
  | .plain code => compile bits windowPaths windowRoot (normalizeW code) start
  | .unit u => castFinish (by simp [blockRecords2,clearData]; omega)
      ((compile bits windowPaths windowRoot (normalizeW u.pre) start).append
        (clearProgram u.clear (start+codeRecords bits windowPaths windowRoot (normalizeW u.pre))))

def records2 {n} : Code2 n → Nat
  | [] => 0
  | b::code => blockRecords2 b + records2 code

def program2 {n} : (code : Code2 n) → (start : Nat) → Straight n start (start+records2 code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [records2]; omega)
      ((blockProgram2 b start).append (program2 code (start+blockRecords2 b)))

def blockSource2 {n} (read : ConstantBit n → Bool) : Block2 n → AdaptiveCircuit
  | .plain code => source read bits windowPaths windowRoot (normalizeW code)
  | .unit u => (source read bits windowPaths windowRoot (normalizeW u.pre)).seq
      (clearSource read u.clear)

def sourceCode2 {n} (read : ConstantBit n → Bool) : Code2 n → AdaptiveCircuit
  | [] => .done
  | b::code => (blockSource2 read b).seq (sourceCode2 read code)

theorem blockProgram2_run {n} (read : ConstantBit n → Bool) (b : Block2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram2 b start).instantiate read history).run = (blockSource2 read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | unit u =>
    rw [blockProgram2,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearProgram_run read u.clear _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSource2,AdaptiveCircuit.run_seq]

theorem program2_run {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((program2 code start).instantiate read history).run = (sourceCode2 read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [program2,castFinish_instantiate,append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,blockProgram2_run]
    simp only [sourceCode2,AdaptiveCircuit.run_seq]

structure UnitGeometry {n} (u : UnitSite n) : Prop where
  placed : ∀ i ∈ u.code, PlacedPair bits windowPaths windowRoot i
  bank : ∀ i ∈ u.code, HotAvoid i
  site : SiteGeometry u.clear

def BlockGeometry2 {n} : Block2 n → Prop
  | .plain code => (∀ i ∈ code, PlacedPair bits windowPaths windowRoot i) ∧
      (∀ i ∈ code, HotAvoid i)
  | .unit u => UnitGeometry u

theorem geometry_toBlock2 {n} (b : Block n) (hg : BlockGeometry b) : BlockGeometry2 (toBlock2 b) := by
  cases b with
  | plain code => exact hg
  | masked site =>
    exact ⟨fun i hi => placed_implies_pair _ _ _ _ (hg.placed i hi), hg.bank, hg⟩

theorem block2_placed {n} (b : Block2 n) (hg : BlockGeometry2 b) :
    (∀ i ∈ b.code, PlacedPair bits windowPaths windowRoot i) ∧
      (∀ i ∈ b.code, HotAvoid i) := by
  cases b with
  | plain code => exact hg
  | unit u => exact ⟨hg.placed,hg.bank⟩

theorem unit_run {n} (read : ConstantBit n → Bool) (u : UnitSite n)
    (hg : UnitGeometry u) (a : Nat) (st : ECDSAAdd.State) (m : List Bool)
    (hs : SimulationValid bits windowPaths windowRoot a st)
    (hh : MeasuredClear.HotClean hot st.basis) :
    ECDSAAdd.run ((specialize u.code a).instantiate read) m st =
      let next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m st
      ⟨next.phase,tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis⟩ := by
  have hp : ∀ i ∈ u.pre, PlacedPair bits windowPaths windowRoot i := by
    intro i hi; exact hg.placed i (List.mem_append_left _ hi)
  have hhot : ∀ i ∈ u.pre, HotAvoid i := by
    intro i hi; exact hg.bank i (List.mem_append_left _ hi)
  have hnext := reference_preserves read u.pre a hp hhot st hs hh m
  have hlast := hg.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
  have hroot : u.clear.guard ∉ portTargets u.clear.ports := List.disjoint_left.mp hlast.2.2 (by simp [lookupRoot])
  simp only [UnitSite.code,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
    ECDSAAdd.run_append,ECDSAAdd.run_take]
  simpa [specialize,WInstr.specialize] using portTemplate_run read (some u.clear.guard) u.clear.ports a windowRoot
    (m.drop (ECDSAAdd.measurementCount ((specialize u.pre a).instantiate read)))
    (ECDSAAdd.run ((specialize u.pre a).instantiate read) m st)
    hlast.2.1 hroot hnext.1.2.2

def BlockSimulation2 {n} (read : ConstantBit n → Bool) (block : Block2 n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, SimulationValid bits windowPaths windowRoot address st →
      MeasuredClear.HotClean hot st.basis → BlockSafe2 read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference2 read address block) m st)

theorem block2_simulation {n} (read : ConstantBit n → Bool) (block : Block2 n)
    (hg : BlockGeometry2 block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimulation2 read block) (blockSource2 read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    obtain ⟨cs,aligned,mass⟩ := normalized_simulation read code hg.1
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    exact ⟨m,hm,fun address st hs _ _ => hb address st hs⟩
  | unit u =>
    have hp : ∀ i ∈ u.pre, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact hg.placed i (List.mem_append_left _ hi)
    have hhot : ∀ i ∈ u.pre, HotAvoid i := by
      intro i hi; exact hg.bank i (List.mem_append_left _ hi)
    obtain ⟨preCs,preAligned,preMass⟩ := normalized_simulation read u.pre hp
    obtain ⟨cs,aligned,mass⟩ := clearProgram_coherent read u.clear hg.site.original 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSource2,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block2.code,UnitSite.code,literalRecords_append,literalRecords] using hm
      · intro a st hs hh hsafe
        let next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m st
        have hn := reference_preserves read u.pre a hp hhot st hs hh m
        have hrun := unit_run read u hg a st m hs hh
        have hclean : Clean (portTargets u.clear.ports)
            (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
        have hvalid : MeasuredClear.HotClean hot next.basis ∧ Clean windowPaths next.basis ∧
            ∀ p ∈ u.clear.ports, next.basis p.target = (next.basis u.clear.guard &&
              decide (read (p.ref (tableAddressValue bits next.basis)) = p.value)) := by
          refine ⟨hn.2,hn.1.1,?_⟩
          rw [hn.1.2.1]
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
        rw [h₁ a st hs,map_smul,hsigned]
        simp [smul_smul,blockReference2,Block2.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num

def Simulation2 {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 code) ∧
    ∀ a st, SimulationValid bits windowPaths windowRoot a st →
      MeasuredClear.HotClean hot st.basis → Safe2 read a code st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference2 read a code) m st)

theorem source2_simulation {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (hg : ∀ b ∈ code, BlockGeometry2 b) :
    ∃ cs : List ℂ, List.Forall₂ (Simulation2 read code) (sourceCode2 read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1],.cons ?_ .nil,by simp⟩
    exact ⟨[],rfl,fun a st _ _ _ => by simp [reference2,erase2,specialize,ECDSAAdd.ShorPort.Tmpl.instantiate,ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁,h₁,mass₁⟩ := block2_simulation read b (hg b (by simp))
    obtain ⟨cs₂,h₂,mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    have geo := block2_placed b (hg b (by simp))
    refine ⟨coherentSeqCoefficients cs₁ cs₂,?_,?_⟩
    · rw [sourceCode2,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁,len₁,run₁⟩ := hb₁
      obtain ⟨m₂,len₂,run₂⟩ := hb₂
      refine ⟨m₁++m₂,?_,?_⟩
      · simp [erase2,List.length_append,len₁,len₂]
      · intro a st hs hh hsafe
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a b) :=
          len₁.trans (specialize_counts read b.code a).2.symm
        have hn := reference_preserves read b.code a geo.1 geo.2 st hs hh m₁
        change SimulationValid bits windowPaths windowRoot a
            (ECDSAAdd.run (blockReference2 read a b) m₁ st) ∧ MeasuredClear.HotClean hot
            (ECDSAAdd.run (blockReference2 read a b) m₁ st).basis at hn
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hh hsafe.1,map_smul,run₂ a (ECDSAAdd.run (blockReference2 read a b) m₁ st) hn.1 hn.2 (hsafe.2 m₁ hm),
          reference2_cons,run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass,mass₁,mass₂]
      norm_num

theorem program2_coherent {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (hg : ∀ b ∈ code, BlockGeometry2 b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue bits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue bits s) code) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program2 code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result)
      (fun s => Clean windowPaths s ∧ s windowRoot = true ∧ MeasuredClear.HotClean hot s ∧ Valid s) := by
  obtain ⟨cs,aligned,mass⟩ := source2_simulation read code hg
  refine ⟨cs,?_,mass⟩
  rw [program2_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m,_,h⟩ := hb
  have he := h (tableAddressValue bits s) ⟨false,s⟩ ⟨hs.1,rfl,hs.2.1⟩ hs.2.2.1 (hsafe s hs.2.2.2)
  rw [Bridge.signedKet_false,hrun s hs.2.2.2 m,Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.WEXUnlookupWidth14

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] WEX.compile Bridge.translate ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram WEX.normalizeW WEX.literalToffolis WEX.literalRecords WEX.codeRecords
  WEX.portOps lookupMeasurements unaryLookupOps tableAddressTree Straight.instantiate AdaptiveCircuit.tCount
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps program2 blockProgram2 clearProgram

def blockCCX2 {n} : Block2 n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * 16383
  | .unit u => literalToffolis (normalizeW u.pre) + traversals u.pre * 16383 + 254

def ccx2 {n} : Code2 n → Nat
  | [] => 0
  | b::code => blockCCX2 b + ccx2 code

theorem block2_tCount {n} (read : ConstantBit n → Bool) (b : Block2 n) (hg : BlockGeometry2 b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgram2 b start).instantiate read history).tCount = 7 * blockCCX2 b := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW code)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram2,WEX.compile_tCount read bits windowPaths windowRoot (normalizeW code) hl start history,traversals_normalize]
    simp [blockCCX2,bits,WEX.widthBits,Nat.mul_add,Nat.mul_assoc]
  | unit u =>
    have hp : ∀ i ∈ u.pre, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact hg.placed i (List.mem_append_left _ hi)
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW u.pre)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    rw [blockProgram2,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearProgram_tCount read u.clear hg.site.original _ h),
      WEX.compile_tCount read bits windowPaths windowRoot (normalizeW u.pre) hl start history,traversals_normalize]
    simp [blockCCX2,bits,WEX.widthBits]
    ring

theorem program2_tCount {n} (read : ConstantBit n → Bool) (code : Code2 n)
    (hg : ∀ b ∈ code, BlockGeometry2 b) (start : Nat) (history : Fin start → Bool) :
    ((program2 code start).instantiate read history).tCount = 7 * ccx2 code := by
  induction code generalizing start with
  | nil => simp [program2,records2,ccx2,Straight.instantiate,AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [program2,castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      block2_tCount read b (hg b (by simp))]
    simp [ccx2,Nat.mul_add]

theorem block2_ccx_relation {n} (b : Block2 n) :
    blockCCX2 b + blockMasks2 b * 16129 = literalToffolis (normalizeW b.code) + traversals b.code * 16383 := by
  cases b with
  | plain code => simp [blockCCX2,blockMasks2,Block2.code]
  | unit u =>
    have hl : literalToffolis (normalizeW u.code) = literalToffolis (normalizeW u.pre) := by
      rw [UnitSite.code,normalize_append,literalToffolis_append]
      simp [normalizeW,normalizeWInstr,literalToffolis]
    have ht : traversals u.code = traversals u.pre + 1 := by
      rw [UnitSite.code,traversals_append]
      rfl
    simp only [blockCCX2,blockMasks2,Block2.code]
    rw [hl,ht,Nat.add_mul]
    omega

theorem ccx2_relation {n} (code : Code2 n) :
    ccx2 code + masks2 code * 16129 = literalToffolis (normalizeW (erase2 code)) + traversals (erase2 code) * 16383 := by
  induction code with
  | nil => simp [ccx2,masks2,erase2,normalizeW,literalToffolis,traversals]
  | cons b code ih =>
    have hb := block2_ccx_relation b
    simp only [ccx2,masks2,erase2_cons,normalize_append,literalToffolis_append,traversals_append,Nat.add_mul]
    omega

theorem block2_records_relation {n} (b : Block2 n) (hg : BlockGeometry2 b) :
    blockRecords2 b + blockMasks2 b * 16129 = codeRecords bits windowPaths windowRoot (normalizeW b.code) + blockLen2 b := by
  cases b with
  | plain code => simp [blockRecords2,blockMasks2,Block2.code,blockLen2]
  | unit u =>
    rw [blockRecords2,high_records u.clear hg.site.original]
    rw [Block2.code,UnitSite.code,normalize_append,records_old_append]
    have hc : normalizeW ([.lookup (some u.clear.guard) u.clear.ports] : WCode n) = [.lookup (some u.clear.guard) u.clear.ports] := by simp [normalizeW,normalizeWInstr]
    rw [hc,site_old_clear_records u.clear hg.site]
    have hm : blockMasks2 (Block2.unit u) = 1 := rfl
    have hl : blockLen2 (Block2.unit u) = u.clear.ports.length := rfl
    omega

theorem records2_relation {n} (code : Code2 n) (hg : ∀ b ∈ code, BlockGeometry2 b) :
    records2 code + masks2 code * 16129 = codeRecords bits windowPaths windowRoot (normalizeW (erase2 code)) + lens2 code := by
  induction code with
  | nil => simp [records2,masks2,erase2,normalizeW,codeRecords,lens2]
  | cons b code ih =>
    have hb := block2_records_relation b (hg b (by simp))
    have ht := ih (fun d hd => hg d (by simp [hd]))
    simp only [records2,masks2,lens2,erase2_cons,normalize_append,records_old_append,Nat.add_mul]
    omega

open AndGadget WEXCredit in
theorem block2_residue {n} (b : Block2 n) (start : Nat) : residue (blockProgram2 b start) = 0 := by
  cases b with
  | plain code => rw [blockProgram2]; exact compile_residue _ _ _ _ _
  | unit u => simp [blockProgram2,residue_cast,residue_append,compile_residue,
      clearProgram,MeasuredClear.measuredClear_residue]

open AndGadget in
theorem program2_residue {n} (code : Code2 n) (start : Nat) : residue (program2 code start) = 0 := by
  induction code generalizing start with
  | nil => simp [program2,records2]
  | cons b code ih => simp [program2,residue_cast,residue_append,block2_residue,ih]

end
end ShorECDLP.Entrant.WEXUnlookupWidth14

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.wires ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

theorem block2_wellFormed {n} (b : Block2 n) (hg : BlockGeometry2 b)
    (hp : ∀ p, WInstr.literal p ∈ b.code → GatePhysical p) (start : Nat) :
    (blockProgram2 b start).WellFormed := by
  cases b with
  | plain code =>
    unfold blockProgram2
    exact pair_compile_wellFormed _ _ _ _ (by simp [bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hg.1) (normalized_literals_valid code hp) start
  | unit u =>
    have hpref : ∀ i ∈ u.pre, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact hg.placed i (List.mem_append_left _ hi)
    have hphys : ∀ p, WInstr.literal p ∈ u.pre → GatePhysical p := by
      intro p hm; exact hp p (List.mem_append_left _ hm)
    rw [blockProgram2,castFinish_wellFormed]
    exact straight_append_wellFormed _ _
      (pair_compile_wellFormed _ _ _ _ (by simp [bits,WEX.widthBits,windowPaths])
        (pair_placed_normalize _ _ _ _ hpref) (normalized_literals_valid u.pre hphys) start)
      (clearProgram_wellFormed u.clear hg.site.original _)

theorem program2_wellFormed {n} (code : Code2 n) (hg : ∀ b ∈ code, BlockGeometry2 b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 code → GatePhysical p) (start : Nat) :
    (program2 code start).WellFormed := by
  induction code generalizing start with
  | nil => simp [program2,records2,Straight.WellFormed]
  | cons b code ih =>
    rw [program2,castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact block2_wellFormed b (hg b (by simp)) (fun p hm => hp p (by simp [erase2_cons,hm])) start
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase2_cons,hm])) _

theorem block2_support {n} (b : Block2 n) (hg : BlockGeometry2 b) (hw : OldWithin b.code) (start : Nat) :
    ChallengeMigration.straightWires (blockProgram2 b start) ⊆ logicalSupport := by
  cases b with
  | plain code => rw [blockProgram2]; exact (old_compile_support code hw start).trans (List.subset_append_left _ _)
  | unit u =>
    have hp : OldWithin u.pre := oldWithin_sub u.pre u.code (List.subset_append_left _ _) hw
    rw [blockProgram2,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨(old_compile_support u.pre hp start).trans (List.subset_append_left _ _),
      clearProgram_support u.clear hg.site.original _⟩

theorem program2_support {n} (code : Code2 n) (hg : ∀ b ∈ code, BlockGeometry2 b)
    (hw : OldWithin (erase2 code)) (start : Nat) :
    ChallengeMigration.straightWires (program2 code start) ⊆ logicalSupport := by
  induction code generalizing start with
  | nil => simp [program2,records2,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hb : OldWithin b.code := oldWithin_sub b.code (erase2 (b::code)) (by rw [erase2_cons]; exact List.subset_append_left _ _) hw
    have ht : OldWithin (erase2 code) := oldWithin_sub (erase2 code) (erase2 (b::code)) (by rw [erase2_cons]; exact List.subset_append_right _ _) hw
    rw [program2,support_cast,straightWires_append]
    exact List.append_subset.mpr ⟨block2_support b (hg b (by simp)) hb start,
      ih (fun d hd => hg d (by simp [hd])) ht _⟩

end
end ShorECDLP.Entrant.WEXUnlookupWidth14

namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.codeSlots WEX.literalSlotSum WEX.portTotal lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps

theorem block2_slots_upper {n} (b : Block2 n) (hg : BlockGeometry2 b) (start : Nat) :
    (blockProgram2 b start).gateSlots ≤ codeSlots bits (normalizeW b.code) + blockMasks2 b * 50530546 := by
  cases b with
  | plain code =>
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW code)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
    rw [blockProgram2,compile_slots bits windowPaths windowRoot (normalizeW code) hl]
    simp [Block2.code,blockMasks2]
  | unit u =>
    have hp : ∀ i ∈ u.pre, PlacedPair bits windowPaths windowRoot i := by
      intro i hi; exact hg.placed i (List.mem_append_left _ hi)
    have hl := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW u.pre)
      (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp)
    have hc := clearProgram_slots u.clear hg.site.original (start + codeRecords bits windowPaths windowRoot (normalizeW u.pre))
    rw [blockProgram2,castFinish_gateSlots,Straight.gateSlots_append,
      compile_slots bits windowPaths windowRoot (normalizeW u.pre) hl]
    rw [Block2.code,UnitSite.code,normalize_append,codeSlots_append]
    simp only [blockMasks2,Nat.one_mul]
    omega

theorem program2_slots_upper {n} (code : Code2 n) (hg : ∀ b ∈ code, BlockGeometry2 b) (start : Nat) :
    (program2 code start).gateSlots ≤ codeSlots bits (normalizeW (erase2 code)) + masks2 code * 50530546 := by
  induction code generalizing start with
  | nil => simp [program2,records2,erase2,normalizeW,codeSlots,masks2,Straight.gateSlots]
  | cons b code ih =>
    have hb := block2_slots_upper b (hg b (by simp)) start
    have ht := ih (fun d hd => hg d (by simp [hd])) (start + blockRecords2 b)
    rw [program2,castFinish_gateSlots,Straight.gateSlots_append]
    simp only [erase2_cons,normalize_append,codeSlots_append,masks2,Nat.add_mul]
    omega

end
end ShorECDLP.Entrant.WEXUnlookupWidth14

/-! ### The corner row at width 14 -/
namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem root_window_nodup14 : (windowRoot :: bits ++ windowPaths).Nodup := by decide +kernel

theorem window_small14 : ∀ w ∈ windowRoot :: lookupRoot windowRoot (some windowRoot) :: bits ++ windowPaths,
    w < 10016 := by
  intro w hw
  simp only [lookupRoot, Option.getD, windowRoot, bits, WEX.widthBits, windowPaths, List.mem_cons,
    List.mem_append, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem cornerLoad_placed14 : PlacedPair bits windowPaths windowRoot
    (WInstr.lookup (n := 32768) (some windowRoot) (WEX.cornerPorts probeRows)) := by
  refine ⟨root_window_nodup14, ?_, ?_, ?_⟩
  · rw [portTargets, List.map_take, ← portTargets, WEX.cornerPorts_targets]
    exact cornerTargets_nodup.sublist (List.take_sublist _ _)
  · rw [portTargets, List.map_drop, ← portTargets, WEX.cornerPorts_targets]
    exact cornerTargets_nodup.sublist (List.drop_sublist _ _)
  · rw [WEX.cornerPorts_targets]
    intro w hw hm
    have h1 := window_small14 w hw
    have h2 := corner_targets_large w hm
    dsimp only [Wire] at *
    omega

theorem yUnload_placed14 : PlacedPair bits windowPaths windowRoot
    (WInstr.lookup (n := 32768) (some windowRoot) (WEX.yPorts probeRows)) := by
  refine ⟨root_window_nodup14, ?_, ?_, ?_⟩
  · rw [portTargets, List.map_take, ← portTargets, WEX.yPorts_targets]
    exact WEX.yWires_nodup.sublist (List.take_sublist _ _)
  · rw [portTargets, List.map_drop, ← portTargets, WEX.yPorts_targets]
    exact WEX.yWires_nodup.sublist (List.drop_sublist _ _)
  · rw [WEX.yPorts_targets]
    intro w hw hm
    have h1 := window_small14 w hw
    have h2 := (WEX.yWires_bounds w hm).1
    dsimp only [Wire] at *
    omega

theorem yUnload_placed14' : Placed bits windowPaths windowRoot
    (WInstr.lookup (n := 32768) (some windowRoot) (WEX.yPorts probeRows)) := by
  refine ⟨root_window_nodup14, ?_, ?_⟩
  · rw [WEX.yPorts_targets]; exact WEX.yWires_nodup
  · rw [WEX.yPorts_targets]
    intro w hw hm
    have h1 := window_small14 w hw
    have h2 := (WEX.yWires_bounds w hm).1
    dsimp only [Wire] at *
    omega

theorem scrDSite_geometry14 : SiteGeometry scrDSite :=
  row_geometry (.masked scrDSite) (by simp [row, portFused])

theorem ySite_geometry14 : SiteGeometry ySite := by
  refine ⟨ySite_geometry, ?_, ySite_geometry.bank⟩
  intro i hi
  simp only [ySite, MaskedSite.code, MaskedSite.prefix, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact yUnload_placed14'

theorem scrDClear_geometry14 : SiteGeometry scrDClear := by
  have hg := scrDSite_geometry14
  refine ⟨scrDClear_geometry, ?_, scrDClear_geometry.bank⟩
  intro i hi
  simp only [scrDClear, MaskedSite.code, MaskedSite.prefix, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact hg.placed _ scrD_unload_mem

theorem sfxMid_placed14 : ∀ i ∈ sfxMidF probeRows, PlacedPair bits windowPaths windowRoot i := by
  intro i hi
  have hmem := sfxMid_sub_row i hi
  simpa only [bits] using WEX.clearReferenceRow_width_placed 14 (by omega) i hmem

theorem placed_pair_narrow (p : ECDSAAdd.Program)
    (h : PlacedPair windowBits windowPaths windowRoot (WInstr.literal (n := 32768) p)) :
    PlacedPair bits windowPaths windowRoot (WInstr.literal (n := 32768) p) := by
  intro w hw
  apply h
  simp only [bits, WEX.widthBits, windowBits, windowPaths, windowRoot, List.mem_cons, List.mem_append,
    List.mem_range'_1] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem cornerA1_placed14 : ∀ i ∈ WEX.cornerA1, PlacedPair bits windowPaths windowRoot i := by
  intro i hi
  rcases WEX.cornerA1_mem i hi with h | rfl
  · exact sfxMid_placed14 i h
  · exact placed_pair_narrow _ WEX.scrCWrite_placed

theorem cornerUnit₁_geometry14 : UnitGeometry cornerUnit₁ := by
  refine ⟨?_, cornerUnit₁_geometry.bank, ySite_geometry14⟩
  intro i hi
  simp only [cornerUnit₁_code, WEX.cornerUnit₁, WEX.cornerPre₁, List.mem_append, List.mem_singleton] at hi
  rcases hi with (rfl | h) | rfl
  · exact cornerLoad_placed14
  · exact cornerA1_placed14 i h
  · exact yUnload_placed14

theorem cornerUnit₂_geometry14 : UnitGeometry cornerUnit₂ := by
  refine ⟨?_, cornerUnit₂_geometry.bank, scrDClear_geometry14⟩
  intro i hi
  simp only [cornerUnit₂_code, WEX.cornerUnit₂, List.mem_append, List.mem_singleton] at hi
  rcases hi with h | rfl
  · exact sfxMid_placed14 i (WEX.cornerA2_sub i h)
  · exact placed_implies_pair _ _ _ _ (scrDSite_geometry14.placed _ scrD_unload_mem)

theorem rowC_geometry : ∀ b ∈ rowC, BlockGeometry2 b := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact geometry_toBlock2 c (row2_geometry c (rowHead_sub c hc))
  · simp only [rowPost3, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun i hi => sfxMid_placed14 i (WEX.cornerNeg_sub i hi),
        fun i hi => sfxMid_hotavoid i (WEX.cornerNeg_sub i hi)⟩
    · exact cornerUnit₁_geometry14
    · exact cornerUnit₂_geometry14
    · exact row2_geometry (.plain WEX.sfxTailF) (tail_blocks_row2 _ (by simp [rowPost]))
    · exact row2_geometry (.plain (wLiteral [.X 838])) (tail_blocks_row2 _ (by simp [rowPost]))

theorem rowC_placed14 : ∀ i ∈ erase2 rowC, PlacedPair bits windowPaths windowRoot i := by
  intro i hi
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  exact (block2_placed b (rowC_geometry b hb)).1 i hib

theorem rowC_codeRecords14 : codeRecords bits windowPaths windowRoot (normalizeW (erase2 rowC)) =
    codeRecords bits windowPaths windowRoot (normalizeW (erase row2)) := by
  have l3 := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW (erase2 rowC))
    (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ rowC_placed14)
  have hp2 : ∀ i ∈ erase row2, PlacedPair bits windowPaths windowRoot i := by
    intro i hi
    obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
    exact (block_placed b (row2_geometry b hb)).1 i hib
  have l2 := pair_layouts_of_placed bits windowPaths windowRoot (normalizeW (erase row2))
    (by simp [bits,WEX.widthBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp2)
  rw [codeRecords_eq _ _ _ _ l3, codeRecords_eq _ _ _ _ l2, literalRecords_normalize, literalRecords_normalize,
    traversals_normalize, traversals_normalize, WEXUnlookup.rowC_measures.2.2.2.2,
    WEXUnlookup.rowC_measures.2.1, WEXUnlookup.row2_measures.2.1]

theorem rowC_records : records2 rowC = 1643161 := by
  have h := records2_relation rowC rowC_geometry
  rw [WEXUnlookup.rowC_masks, WEXUnlookup.rowC_lens, rowC_codeRecords14, row2_records_code14] at h
  omega

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx2 Nat.add Nat.mul in
theorem rowC_ccx_upper : ccx2 rowC ≤ 2247344 := by
  have h := ccx2_relation rowC
  have hn := WEX.literalToffolis_normalize (erase2 rowC)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis,h0]
  rw [WEXUnlookup.rowC_masks, WEXUnlookup.rowC_measures.2.1] at h
  rw [WEXUnlookup.rowC_measures.1, hrow] at hn
  omega

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem rowC_wellFormed (start : Nat) : (program2 rowC start).WellFormed :=
  program2_wellFormed rowC rowC_geometry rowC_physical start

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem rowC_support (start : Nat) : ChallengeMigration.straightWires (program2 rowC start) ⊆ logicalSupport :=
  program2_support rowC rowC_geometry rowC_oldWithin start

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem rowC_slots_upper (start : Nat) : (program2 rowC start).gateSlots ≤ 1000000000 := by
  have h := program2_slots_upper rowC rowC_geometry start
  rw [WEXUnlookup.rowC_masks] at h
  have hc := WEX.codeSlots_bound bits (normalizeW (erase2 rowC))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.rowC_measures
  have hl2 := hm.2.2.1
  have hp2 := hm.2.2.2.1
  rw [hm.2.1] at hc
  have hlen : bits.length = 14 := by simp [bits,WEX.widthBits]
  rw [hlen] at hc
  norm_num at hc
  omega

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem rowC_coherent (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program2 rowC start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program2_coherent (readConstant coeffs Q) rowC rowC_geometry liveReady (rowState coeffs Q)
    (fun s hs => (rowC_safe_run coeffs Q hQ hn _ s hs).1) (by
      intro s hs m
      simpa only [rowState] using rowC_run_any (tableAddressValue bits s) coeffs Q hQ hn s hs m) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩

def rowSource3 (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode2 (readConstant coeffs Q) rowC

theorem rowSource3_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (rowSource3 coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := rowC_coherent coeffs Q hQ hn 0 Fin.elim0
  have he : rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold rowState rowPointState
    rw [show tableAddressValue bits s = tableAddressValue (WEX.widthBits 14) s from rfl,
      WEX.width_table 14 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  simpa only [program2_run,rowSource3,LiveReady] using aligned

attribute [local irreducible] program2 blockProgram2 clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  MeasuredClear.measuredClear ccx2 Nat.add Nat.mul

def addFixed3 (start : Nat) : Straight 32768 start (start+1643161) :=
  castFinish (congrArg (fun m => start+m) rowC_records) (program2 rowC start)

attribute [local irreducible] addFixed3

theorem addFixed3_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed3 start).instantiate read history).run = (sourceCode2 read rowC).run := by
  rw [addFixed3,castFinish_instantiate,program2_run]

theorem addFixed3_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed3 start).instantiate read history).tCount = 7*ccx2 rowC := by
  rw [addFixed3,castFinish_instantiate,program2_tCount read rowC rowC_geometry]

theorem addFixed3_wellFormed (start : Nat) : (addFixed3 start).WellFormed := by
  rw [addFixed3,castFinish_wellFormed]
  exact rowC_wellFormed start

theorem addFixed3_support (start : Nat) : ChallengeMigration.straightWires (addFixed3 start) ⊆ logicalSupport := by
  rw [addFixed3,support_cast]
  exact rowC_support start

theorem addFixed3_residue (start : Nat) : residue (addFixed3 start) = 0 := by
  rw [addFixed3,residue_cast]
  exact program2_residue rowC start

theorem addFixed3_credit (start : Nat) : ProgramCredit (addFixed3 start) (ccx2 rowC) := by
  have hz := addFixed3_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed3 start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed3_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixed3_slots_upper (start : Nat) : (addFixed3 start).gateSlots ≤ 1000000000 := by
  rw [addFixed3,castFinish_gateSlots]
  exact rowC_slots_upper start

end
end ShorECDLP.Entrant.WEXUnlookupWidth14

namespace ShorECDLP.Entrant.WEXUnlookupWidth14.Corner
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible WEXUnlookupWidth14
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program2 blockProgram2 clearProgram addFixed3 WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx2 Nat.add Nat.mul
def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSource3 coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource3_coherent coeffs Q hQ hn halias)
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
def fastBodyProgram (start : Nat) : Straight 32768 start (start+1643673) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed3 (start+256))).append
      (nFastProgram (start+256+1643161))).append (suffixProgram (start+256+1643161+256)))

attribute [local irreducible] fastBodyProgram

theorem fastBodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode2 read rowC)).seq fastSignSource)).seq suffixSource).run := by
  rw [fastBodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource fastSignSource (sourceCode2 read rowC) fastSignSource suffixSource
    (prefixProgram_run _ read) (nFastProgram_run _ read) (addFixed3_run read _)
    (nFastProgram_run _ read) (suffixProgram_run _ read) history

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode2 (readConstant coeffs Q) rowC)).seq fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSource3
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
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx2 rowC) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1643161)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx2 rowC) (prefix_credit start) hl (addFixed3_credit (start+256)) hr
    (suffix_credit (start+256+1643161+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx2 rowC) := by
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
      · exact addFixed3_wellFormed _
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
    addFixed3_support _⟩,(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := addFixed3_slots_upper (start+256)
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  omega
def fastCompactProgram (start : Nat) : Straight 32768 start (start+1643673) :=
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
    ccx2 rowC ≤ 2247848 := by
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := WEXUnlookupWidth14.rowC_ccx_upper
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 14 where
  records := 1643673
  tBound := 15734936
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx2 rowC
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
end ShorECDLP.Entrant.WEXUnlookupWidth14.Corner

-- ===== formerly Schedule261 =====

/-! One module (to keep the Entrant module count low for the hosted kernel replay) holding, in order:
the sin²-averaged success bound (formerly `SinAverage`), its sharpened 261-bit version (formerly
`SinAverage261`), the 56-word right readout (formerly `Readout56`) and the 261/208 schedule with its
final assembly on lane B's corner-row window body (formerly `Schedule261`). -/

-- ===== formerly SinAverage =====

/-! Averaged success bound for a 262/208 two-axis readout.

Pointwise window bounds lose a factor two: the QPE amplitude carries the numerator
`sin²(π N β)`, and averaged over the nonzero characters `k` this weight is at most `1/2`
(`sum_sin_sq_le`). The tail mass of each axis is therefore bounded by a multiple of that
weight, and the union bound per character is averaged over `k`. -/

namespace ShorECDLP.Entrant.SinAverage
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Entrant.WindowMassSharpProof ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 300

/-- Geometric sum with its exact numerator. -/
theorem amp_normSq_le_sin (N : ℕ) (x : ℝ) (hs : Real.sin (x / 2) ≠ 0) :
    Complex.normSq ((N : ℂ)⁻¹ * ∑ y ∈ range N, Complex.exp (Complex.I * (x : ℂ)) ^ y)
      ≤ Real.sin ((N : ℝ) * x / 2) ^ 2 / ((N : ℝ) * |Real.sin (x / 2)|) ^ 2 := by
  set ω := Complex.exp (Complex.I * (x : ℂ)) with hωdef
  have hω1 : ‖ω - 1‖ = 2 * |Real.sin (x / 2)| := by
    rw [hωdef, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs]
    norm_num
  have hpos : 0 < |Real.sin (x / 2)| := abs_pos.mpr hs
  have hω : ω ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hω1
    linarith
  have hωN : ω ^ N = Complex.exp (Complex.I * (((N : ℝ) * x : ℝ) : ℂ)) := by
    rw [hωdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnum : ‖ω ^ N - 1‖ = 2 * |Real.sin ((N : ℝ) * x / 2)| := by
    rw [hωN, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs]
    norm_num
  rw [geom_sum_eq hω, Complex.normSq_eq_norm_sq, norm_mul, norm_div, norm_inv,
    Complex.norm_natCast, hω1, hnum]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_of_eq
  rw [show (N : ℝ)⁻¹ * (2 * |Real.sin ((N : ℝ) * x / 2)| / (2 * |Real.sin (x / 2)|)) =
      |Real.sin ((N : ℝ) * x / 2)| / ((N : ℝ) * |Real.sin (x / 2)|) by field_simp]
  rw [div_pow, sq_abs]

/-- `sin² (π(Nβ - a)) = sin² (πNβ)` for an integer outcome `a`. -/
theorem ampSq_le_weighted (N : ℕ) (hN : 0 < N) (β : ℝ) (a : ℕ)
    (hs : Real.sin (Real.pi * (β - (a : ℝ) / N)) ≠ 0) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 /
      ((N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))|) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (2 * Real.pi * (β - (a : ℝ) / N)) / 2 = Real.pi * (β - (a : ℝ) / N) := by ring
  have h := amp_normSq_le_sin N (2 * Real.pi * (β - (a : ℝ) / N)) (by rw [hx]; exact hs)
  rw [hx] at h
  have hNx : (N : ℝ) * (2 * Real.pi * (β - (a : ℝ) / N)) / 2 =
      Real.pi * N * β - a * Real.pi := by
    field_simp
  have hsq : Real.sin (Real.pi * N * β - a * Real.pi) ^ 2 = Real.sin (Real.pi * N * β) ^ 2 := by
    rw [Real.sin_sub_nat_mul_pi, mul_pow, ← pow_mul, mul_comm a 2, pow_mul, neg_one_sq,
      one_pow, one_mul]
  rw [hNx, hsq] at h
  exact h

/-- Local weighted bound from a sine lower bound on the directed distance `φ`. -/
theorem ampSq_weighted_of_abs (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat) (φ : ℝ)
    (hd : 0 < φ) (hsmall : φ / (N : ℝ) ≤ 1/16)
    (he : |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (φ / (N : ℝ)))) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (9 * φ ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow := sin_pi_mul_ge_three (φ / (N : ℝ)) (div_nonneg hd.le hNR.le) hsmall
  have hu : 0 < φ / (N : ℝ) := div_pos hd hNR
  have hpos : 0 < |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by rw [he]; linarith
  have hne : Real.sin (Real.pi * (β - (a : ℝ) / N)) ≠ 0 := abs_pos.mp hpos
  refine (ampSq_le_weighted N hN β a hne).trans ?_
  have h3 : 3 * φ ≤ (N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by
    rw [he]
    calc 3 * φ = (N : ℝ) * (3 * (φ / (N : ℝ))) := by field_simp
      _ ≤ (N : ℝ) * Real.sin (Real.pi * (φ / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hlow hNR.le
  have h9 : 9 * φ ^ 2 ≤ ((N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))|) ^ 2 := by
    nlinarith
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h9

theorem ampSq_phiR_weighted (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiR N ((N : ℝ) * β) a)
    (hsmall : phiR N ((N : ℝ) * β) a / (N : ℝ) ≤ 1/16) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (9 * (phiR N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_weighted_of_abs N hN β a _ hd hsmall (abs_sin_phiR N hN β a hd hsmall)

theorem ampSq_phiL_weighted (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiL N ((N : ℝ) * β) a)
    (hsmall : phiL N ((N : ℝ) * β) a / (N : ℝ) ≤ 1/16) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / (9 * (phiL N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_weighted_of_abs N hN β a _ hd hsmall (abs_sin_phiL N hN β a hd hsmall)

theorem directed_tail_weighted (N : Nat) (β : ℝ) (S : Finset Nat) (d : Nat → ℝ) (s R : ℝ)
    (hs : 0 ≤ s) (hR : 1 < R) (hd : ∀ a ∈ S, R ≤ d a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |d a - d b| < 1 → a = b)
    (hpt : ∀ a ∈ S, ampSq N β a ≤ s / (9 * (d a) ^ 2)) :
    ∑ a ∈ S, ampSq N β a ≤ s / 9 * (1 / (R - 1)) := by
  have hi := sum_inv_sq_le S d R hR hd hsep
  calc
    _ ≤ ∑ a ∈ S, (s / 9) * (1 / (d a) ^ 2) := by
      apply Finset.sum_le_sum
      intro a ha
      have hda : 0 < d a := by linarith [hd a ha]
      calc ampSq N β a ≤ s / (9 * (d a) ^ 2) := hpt a ha
        _ = (s / 9) * (1 / (d a) ^ 2) := by field_simp
    _ = (s / 9) * (∑ a ∈ S, 1 / (d a) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (s / 9) * (1 / (R - 1)) := mul_le_mul_of_nonneg_left hi (by positivity)

/-- Circular concentration within radius `R`, weighted by the numerator `sin² (πNβ)`. -/
theorem circular_mass_weighted (N : Nat) (hNbig : 65536 ≤ N) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R : ℝ) (hR : 1 < R) :
    1 - Real.sin (Real.pi * N * β) ^ 2 * (2 / (9 * (R - 1))) - 1/10000 ≤
      ∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R
        then ampSq N β a else 0 := by
  classical
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNreal : (65536 : ℝ) ≤ N := by exact_mod_cast hNbig
  set s := Real.sin (Real.pi * N * β) ^ 2 with hsdef
  have hs0 : 0 ≤ s := sq_nonneg _
  let RS := (Finset.range N).filter
    (fun a => R ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 4096)
  let LS := (Finset.range N).filter
    (fun a => R ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 4096)
  have rBound : ∑ a ∈ RS, ampSq N β a ≤ s / 9 * (1 / (R - 1)) := by
    apply directed_tail_weighted N β RS (phiR N ((N : ℝ) * β)) s R hs0 hR
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiR_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiR_weighted N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      nlinarith [hd.2]
  have lBound : ∑ a ∈ LS, ampSq N β a ≤ s / 9 * (1 / (R - 1)) := by
    apply directed_tail_weighted N β LS (phiL N ((N : ℝ) * β)) s R hs0 hR
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiL_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      apply ampSq_phiL_weighted N hN β a (by linarith [hd.1])
      apply (div_le_iff₀ hNR).mpr
      nlinarith [hd.2]
  have fBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096)
      then ampSq N β a else 0) ≤ (1 : ℝ) / 10000 := by
    have hc := circular_mass N hN β 4096 hβ0 hβ1 (by norm_num)
    have hs : (∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) +
      (∑ a ∈ Finset.range N,
        if ¬(phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096)
        then ampSq N β a else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert parseval N hN β using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    linarith [far_tail_budget]
  have cover (a : Nat) :
      (if ¬(phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R)
        then ampSq N β a else 0) ≤
      (if R ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) +
      (if R ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) +
      (if ¬(phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096)
        then ampSq N β a else 0) := by
    have ha0 : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
    by_cases hb : ¬(phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R)
    · rw [if_pos hb]
      have hr : R ≤ phiR N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inl h))
      have hl : R ≤ phiL N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inr h))
      by_cases hRR : R ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 4096
      · rw [if_pos hRR]
        split_ifs <;> linarith
      · rw [if_neg hRR]
        by_cases hLL : R ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 4096
        · rw [if_pos hLL]
          split_ifs <;> linarith
        · rw [if_neg hLL]
          have hf : ¬(phiR N ((N : ℝ) * β) a < 4096 ∨ phiL N ((N : ℝ) * β) a < 4096) := by
            rintro (h | h)
            · exact hRR ⟨hr, h⟩
            · exact hLL ⟨hl, h⟩
          rw [if_pos hf]
          linarith
    · rw [if_neg hb]
      split_ifs <;> linarith
  have badBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R)
      then ampSq N β a else 0) ≤ s * (2 / (9 * (R - 1))) + 1/10000 := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.range N) => cover a)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    have hRs : (∑ a ∈ Finset.range N,
        if R ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) ≤ s / 9 * (1 / (R - 1)) := by
      simpa only [RS, Finset.sum_filter] using rBound
    have hLs : (∑ a ∈ Finset.range N,
        if R ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 4096
        then ampSq N β a else 0) ≤ s / 9 * (1 / (R - 1)) := by
      simpa only [LS, Finset.sum_filter] using lBound
    have he : s / 9 * (1 / (R - 1)) + s / 9 * (1 / (R - 1)) = s * (2 / (9 * (R - 1))) := by
      have hR1 : R - 1 ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have htotal : (∑ a ∈ Finset.range N,
      if phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R
      then ampSq N β a else 0) +
    (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R ∨ phiL N ((N : ℝ) * β) a < R)
      then ampSq N β a else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert parseval N hN β using 1
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> ring
  linarith

/-- Nearest-numerator window at half-width `N/(2r) ≥ 32`. -/
theorem window_mass_left_weighted (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r)
    (hNbig : 65536 ≤ N) (hrN : 64 * r ≤ N) :
    1 - Real.sin (Real.pi * N * ((n : ℝ) / (r : ℝ))) ^ 2 * (2 / 279) - 1/10000 ≤
      ∑ a ∈ range N,
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
  have hrN' : 64 * (r : ℝ) ≤ N := by exact_mod_cast hrN
  have hL32 : 32 ≤ L := by nlinarith
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβ1 : β < 1 := by rw [hβ]; exact (div_lt_one hrR).2 hnR
  have hmass := circular_mass_weighted N hNbig β hβ0 hβ1 32 (by norm_num)
  have hcβ : (N : ℝ) * β = c := by rw [hβ, hc]; ring
  rw [hcβ, show (2 : ℝ) / (9 * (32 - 1)) = 2 / 279 by norm_num] at hmass
  apply hmass.trans
  apply Finset.sum_le_sum
  intro a ha
  have haN : (a : ℝ) < N := by exact_mod_cast (mem_range.mp ha)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hgood : (phiR N c a < 32 ∨ phiL N c a < 32) →
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

/-- Right axis: the 55 neighbouring words cover radius 27, weighted. -/
theorem rightMass_weighted (r : Nat) (hr : 0 < r) (k : Fin r) :
    1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 * (2 / 234) - 1/10000 ≤
      rightMass r k := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := circular_mass_weighted (2^208) (by norm_num) ((k.val : ℝ) / r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt)) 27 (by norm_num)
  rw [show (2 : ℝ) / (9 * (27 - 1)) = 2 / 234 by norm_num] at h
  have hfin : 1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 * (2 / 234) -
      1/10000 ≤ ∑ b : Fin (2^208),
      if phiR (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b.val < 27 ∨
        phiL (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b.val < 27
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b < 27 ∨
        phiL (2^208) ((2^208 : Nat) * ((k.val : ℝ) / r)) b < 27
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b) else 0)]
    simpa only [ampSq, paperPhaseAmplitude, eigenvalue] using h
  refine hfin.trans (Finset.sum_le_sum (fun b _ => ?_))
  dsimp only [rightMass]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- `∑_{k<r} cos(2πMk/r) ∈ {0, r}`, in particular nonnegative. -/
theorem sum_cos_nonneg (r M : ℕ) :
    0 ≤ ∑ k ∈ range r, Real.cos (k * (2 * Real.pi * M / r)) := by
  set θ : ℝ := 2 * Real.pi * M / r with hθ
  set ω : ℂ := Complex.exp (θ * Complex.I) with hω
  have hterm : ∀ k : ℕ, Real.cos (k * θ) = (ω ^ k).re := by
    intro k
    rw [hω, ← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast
    ring
  have hsum : ∑ k ∈ range r, Real.cos (k * θ) = (∑ k ∈ range r, ω ^ k).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  by_cases h1 : ω = 1
  · simp [h1]
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hr' : ω ^ r = 1 := by
      rw [hω, ← Complex.exp_nat_mul]
      have : (r : ℂ) * ((θ : ℂ) * Complex.I) = (M : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hθ]
        push_cast
        field_simp
      rw [this]
      exact Complex.exp_nat_mul_two_pi_mul_I M
    rw [geom_sum_eq h1, hr', sub_self, zero_div, Complex.zero_re]

/-- Average of the weight over all characters. -/
theorem sum_sin_sq_le (r M : ℕ) :
    ∑ k : Fin r, Real.sin (Real.pi * M * (k.val : ℝ) / r) ^ 2 ≤ (r : ℝ) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => Real.sin (Real.pi * M * (k : ℝ) / r) ^ 2)]
  have h := sum_cos_nonneg r M
  have he : ∀ k ∈ range r, Real.sin (Real.pi * M * (k : ℝ) / r) ^ 2 =
      1/2 - Real.cos (k * (2 * Real.pi * M / r)) / 2 := by
    intro k _
    rw [Real.sin_sq_eq_half_sub]
    congr 3
    ring
  have h2 : ∑ k ∈ range r, Real.cos (k * (2 * Real.pi * M / r)) / 2 =
      (∑ k ∈ range r, Real.cos (k * (2 * Real.pi * M / r))) / 2 := by
    rw [Finset.sum_div]
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, h2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

theorem sin_sq_mod (r m t : ℕ) (hr : 0 < r) :
    Real.sin (Real.pi * m * ((t % r : ℕ) : ℝ) / r) ^ 2 = Real.sin (Real.pi * m * t / r) ^ 2 := by
  have hrR : (r : ℝ) ≠ 0 := by positivity
  have ht : (t : ℝ) = ((t % r : ℕ) : ℝ) + r * ((t / r : ℕ) : ℝ) := by
    have := Nat.mod_add_div t r
    exact_mod_cast this.symm
  have he : Real.pi * m * ((t % r : ℕ) : ℝ) / r =
      Real.pi * m * t / r - ((m * (t / r) : ℕ) : ℝ) * Real.pi := by
    rw [ht]
    push_cast
    field_simp
    ring
  rw [he, Real.sin_sub_nat_mul_pi, mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq,
    one_pow, one_mul]

theorem left_weight_sum (r n : ℕ) :
    ∑ k : Fin r, Real.sin (Real.pi * ((2^n : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2 ≤ (r : ℝ) / 2 := by
  have h := sum_sin_sq_le r (2^n)
  simpa only [mul_div_assoc] using h

theorem right_weight_sum (r d : ℕ) (hr : 0 < r) :
    ∑ k : Fin r, Real.sin (Real.pi * ((2^208 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2 ≤
      (r : ℝ) / 2 := by
  have h := sum_sin_sq_le r (2^208 * d)
  refine le_of_eq_of_le (Finset.sum_congr rfl (fun k _ => ?_)) h
  rw [← mul_div_assoc, sin_sq_mod r (2^208) (d * k.val) hr]
  congr 2
  push_cast
  ring

theorem averaged_pair_coverage (r n d : Nat) (hr : r.Prime)
    (hNbig : 65536 ≤ 2^n) (hprecision : 64 * r ≤ 2^n)
    (accept : Fin (2^n) → Fin (2^208) → Prop) [∀ a b, Decidable (accept a b)]
    (haccept : ∀ (k : Fin r), k.val ≠ 0 → ∀ a b,
      ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val →
      rightGood r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b →
      accept a b) :
    (1 - 1 / (r : ℝ)) * (1 - 2/10000) - 1/279 - 1/234 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208),
      if accept a b then asymmetricPairMass r n 208 d (a, b) else 0 := by
  classical
  let A : Fin r → Fin (2^n) → ℝ := fun k a =>
    Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2^208) → ℝ := fun k b =>
    Complex.normSq (paperPhaseAmplitude 208 (((d * k.val % r : Nat) : ℝ) / r) b.val)
  let good : Fin r → Fin (2^n) → Fin (2^208) → Prop := fun k a b =>
    k.val ≠ 0 ∧ ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val ∧
      rightGood r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b
  let F : Fin r → Fin (2^n) → Fin (2^208) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let sL : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^n : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let sR : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^208 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2
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
      asymmetricPairMass r n 208 d (a, b) = (r : ℝ)⁻¹ * ∑ k : Fin r, A k a * B k b := by
    intro a b
    simp only [asymmetricPairMass, one_div, A, B]
  have step1 :
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2^n), ∑ b : Fin (2^208),
          if accept a b then asymmetricPairMass r n 208 d (a, b) else 0 := by
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
      1 - sL k * (2 / 279) - 1/10000 ≤ ∑ a : Fin (2^n),
        if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val then A k a else 0 := by
    have h := window_mass_left_weighted r (2^n) k.val
      (Nat.pos_of_ne_zero hk) k.isLt hNbig hprecision
    rw [Fin.sum_univ_eq_sum_range (fun a =>
      if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a = k.val then
        Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a) else 0)]
    simpa only [ShorECDLP.Quantum.OrderFinding.nearestNumerator, paperPhaseAmplitude,
      eigenvalue] using h
  have hright (k : Fin r) :
      1 - sR k * (2 / 234) - 1/10000 ≤ rightMass r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ :=
    rightMass_weighted r hr.pos ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩
  have step3 : ∀ k : Fin r,
      (if k.val = 0 then 0 else (1 - 2/10000 : ℝ)) - sL k * (2 / 279) - sR k * (2 / 234) ≤
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    intro k
    have hsL : 0 ≤ sL k := sq_nonneg _
    have hsR : 0 ≤ sR k := sq_nonneg _
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b :=
        Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF k a b))
      nlinarith
    · rw [if_neg hk]
      have he : (∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b) =
          (∑ a : Fin (2^n), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val
            then A k a else 0) * rightMass r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ := by
        rw [rightMass, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F, good, B]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [he]
      have hl := hleft k hk
      have hrt := hright k
      have hsL1 : sL k ≤ 1 := Real.sin_sq_le_one _
      have hsR1 : sR k ≤ 1 := Real.sin_sq_le_one _
      have hl0 : 0 ≤ 1 - sL k * (2 / 279) - 1/10000 := by linarith
      have hr0 : 0 ≤ 1 - sR k * (2 / 234) - 1/10000 := by linarith
      have hprod := mul_le_mul hl hrt hr0 (hl0.trans hl)
      nlinarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  have hcount : (∑ k : Fin r, (if k.val = 0 then (0 : ℝ) else (1 - 2/10000))) =
      ((r : ℝ) - 1) * (1 - 2/10000) := by
    have hz : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
      simp [hr.pos]
    calc
      _ = ∑ k : Fin r, ((1 - 2/10000 : ℝ) - (1 - 2/10000) * (if k.val = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcount, ← Finset.sum_mul,
    ← Finset.sum_mul] at hsum
  have hL := left_weight_sum r n
  have hR := right_weight_sum r d hr.pos
  have hlow : ((r : ℝ) - 1) * (1 - 2/10000) - (r : ℝ) / 2 * (2 / 279) - (r : ℝ) / 2 * (2 / 234) ≤
      ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    have h1 : (∑ k : Fin r, sL k) * (2 / 279) ≤ (r : ℝ) / 2 * (2 / 279) :=
      mul_le_mul_of_nonneg_right hL (by norm_num)
    have h2 : (∑ k : Fin r, sR k) * (2 / 234) ≤ (r : ℝ) / 2 * (2 / 234) :=
      mul_le_mul_of_nonneg_right hR (by norm_num)
    linarith
  have hlower := mul_le_mul_of_nonneg_left hlow hrinv
  have heval : (r : ℝ)⁻¹ * (((r : ℝ) - 1) * (1 - 2/10000) - (r : ℝ) / 2 * (2 / 279) -
      (r : ℝ) / 2 * (2 / 234)) = (1 - 1 / (r : ℝ)) * (1 - 2/10000) - 1/279 - 1/234 := by
    field_simp
  rw [heval, step2] at hlower
  exact hlower.trans step1

theorem success_budget (r : ℝ) (hr : 1000000 ≤ r) :
    (99 : ℝ)/100 ≤ (1 - 1 / r) * (1 - 2/10000) - 1/279 - 1/234 := by
  have hr0 : 0 < r := by linarith
  have hinv : 1 / r ≤ (1 : ℝ) / 1000000 :=
    one_div_le_one_div_of_le (by norm_num) hr
  nlinarith

theorem precision262 : 64 * order ≤ 2^262 := by norm_num [order]

def params262 : DecoderParams := ⟨262,208,by decide,by decide,by decide,by decide⟩
def pairRecovered262 (d a b : Nat) : Bool :=
  decide (∃i : Fin 55,(d : ZMod order)∈fixedCandidates params262 a (neighborWord b ((i.val : ℤ)-27)))

theorem pairRecovered262_of_character (d : Nat) (k : Fin order) (hk : k.val≠0)
    (a : Fin (2^262)) (b : Fin (2^208))
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 262 a.val=k.val)
    (hb : rightGood order ⟨d*k.val%order,Nat.mod_lt _ order_prime.pos⟩ b) :
    pairRecovered262 d a.val b.val=true := by
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
      (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 262 a.val : ZMod order)⁻¹=d
    rw [ha]
    simp only [ZMod.natCast_mod,Nat.cast_mul]
    field_simp

theorem pair_success262 (Q : Point) (d : Nat) (_hn : Q≠0) (_hd : Q=d•G) :
    (99 : ℝ)/100 ≤ ∑a : Fin (2^262),∑b : Fin (2^208),
      if pairRecovered262 d a.val b.val then asymmetricPairMass order 262 208 d (a,b) else 0 := by
  have h:=averaged_pair_coverage order 262 d order_prime (by norm_num) precision262
    (fun a b=>pairRecovered262 d a.val b.val=true)
    (fun k hk a b ha hb=>pairRecovered262_of_character d k hk a b ha hb)
  exact (success_budget order (by norm_num [order])).trans h

theorem decoder_budget262 :
    55*decoderCandidateLimit .wrappedShift params262 ≤ budget55 := by
  norm_num [decoderCandidateLimit,trialCandidateLimit,params262,budget55,order]

end
end ShorECDLP.Entrant.SinAverage

-- ===== formerly SinAverage261 =====

/-! Averaged success bound for a 261/208 two-axis readout with 56 right neighbour words.

Same argument as `SinAverage`, with sharper constants:
* per term `sin (πu) ≥ 3.141591·u` for `u ≤ 2⁻²⁰` (`sin_pi_mul_ge_sharp`);
* separated tail sums `Σ 1/φ² ≤ 1/(R − 1/2)` by telescoping (`sum_inv_sq_le_half`);
* two radii, one per direction (`circular_mass_two`), with the far tail cut at `2^40`;
* left radii `R1, R2 ≥ 16` with `R1 + R2 ≥ 33` (`left_pair`), right radii
  `29 − e, 28 + e` with `|e| ≤ 1/2` (`right_pair`). -/

namespace ShorECDLP.Entrant.SinAverage261
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Entrant.WindowMassSharpProof ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Entrant.RoundedReadout ShorECDLP.Entrant.SinAverage
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding
open ShorECDLP.Quantum.PhaseEstimation
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 300

theorem sin_pi_mul_ge_sharp (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2^20) :
    (3141591 / 1000000 : ℝ) * u ≤ Real.sin (Real.pi * u) := by
  have hpL : (3141592 : ℝ) / 1000000 < Real.pi := by
    have h := Real.pi_gt_d6
    norm_num at h ⊢
    linarith
  have hpU : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hpu0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le hu0
  have hpu : Real.pi * u ≤ 4 * u := mul_le_mul_of_nonneg_right hpU hu0
  have hu2 : u ^ 2 ≤ (1 / 2^20 : ℝ) ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have hu3 : u ^ 3 ≤ u / 2^40 := by
    have h := mul_le_mul_of_nonneg_left hu2 hu0
    calc u ^ 3 = u * u ^ 2 := by ring
      _ ≤ u * (1 / 2^20 : ℝ) ^ 2 := h
      _ = u / 2^40 := by ring
  have hcube : (Real.pi * u) ^ 3 ≤ 64 * (u / 2^40) := by
    calc (Real.pi * u) ^ 3 ≤ (4 * u) ^ 3 := pow_le_pow_left₀ hpu0 hpu 3
      _ = 64 * u ^ 3 := by ring
      _ ≤ 64 * (u / 2^40) := mul_le_mul_of_nonneg_left hu3 (by norm_num)
  have hs := sin_ge_cubic (Real.pi * u) hpu0
  have hp := mul_le_mul_of_nonneg_right hpL.le hu0
  linarith

/-- Local sharp bound from the exact numerator and a sine lower bound on the distance `φ`. -/
theorem ampSq_sharp_of_abs (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat) (φ : ℝ)
    (hd : 0 < φ) (hsmall : φ / (N : ℝ) ≤ 1 / 2^20)
    (he : |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (φ / (N : ℝ)))) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 / ((3141591 / 1000000 : ℝ) ^ 2 * φ ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow := sin_pi_mul_ge_sharp (φ / (N : ℝ)) (div_nonneg hd.le hNR.le) hsmall
  have hu : 0 < φ / (N : ℝ) := div_pos hd hNR
  have hpos : 0 < |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by rw [he]; linarith
  have hne : Real.sin (Real.pi * (β - (a : ℝ) / N)) ≠ 0 := abs_pos.mp hpos
  refine (ampSq_le_weighted N hN β a hne).trans ?_
  have hφ : (N : ℝ) * (φ / (N : ℝ)) = φ := mul_div_cancel₀ φ hNR.ne'
  have h3 : (3141591 / 1000000 : ℝ) * φ ≤
      (N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hlow hNR.le
    calc (3141591 / 1000000 : ℝ) * φ =
          (N : ℝ) * ((3141591 / 1000000 : ℝ) * (φ / (N : ℝ))) := by
            rw [mul_left_comm, hφ]
      _ ≤ _ := hm
  have h9 : (3141591 / 1000000 : ℝ) ^ 2 * φ ^ 2 ≤
      ((N : ℝ) * |Real.sin (Real.pi * (β - (a : ℝ) / N))|) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h3 2
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h9

theorem ampSq_phiR_sharp (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiR N ((N : ℝ) * β) a)
    (hsmall : phiR N ((N : ℝ) * β) a / (N : ℝ) ≤ 1 / 2^20) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 /
      ((3141591 / 1000000 : ℝ) ^ 2 * (phiR N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_sharp_of_abs N hN β a _ hd hsmall
    (abs_sin_phiR N hN β a hd (hsmall.trans (by norm_num)))

theorem ampSq_phiL_sharp (N : Nat) (hN : 0 < N) (β : ℝ) (a : Nat)
    (hd : 0 < phiL N ((N : ℝ) * β) a)
    (hsmall : phiL N ((N : ℝ) * β) a / (N : ℝ) ≤ 1 / 2^20) :
    ampSq N β a ≤ Real.sin (Real.pi * N * β) ^ 2 /
      ((3141591 / 1000000 : ℝ) ^ 2 * (phiL N ((N : ℝ) * β) a) ^ 2) :=
  ampSq_sharp_of_abs N hN β a _ hd hsmall
    (abs_sin_phiL N hN β a hd (hsmall.trans (by norm_num)))

/-- Telescoping with `1/x² ≤ 1/(x − 1/2) − 1/(x + 1/2)`. -/
theorem sum_range_inv_sq_le_half (R : ℝ) (hR : 1/2 < R) (M : ℕ) :
    ∑ k ∈ range M, 1 / (R + k) ^ 2 ≤ 1 / (R - 1/2) - 1 / (R - 1/2 + M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h1 : 0 < R - 1/2 + M := by linarith
    have h2 : 0 < R + M := by linarith
    have h3 : 0 < R + 1/2 + M := by linarith
    have hstep : 1 / (R + M) ^ 2 ≤
        1 / (R - 1/2 + M) - 1 / (R - 1/2 + ((M + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [show R - 1/2 + (M + 1) = R + 1/2 + M by ring]
      rw [div_sub_div _ _ h1.ne' h3.ne', div_le_div_iff₀ (pow_pos h2 2) (mul_pos h1 h3)]
      nlinarith
    linarith

theorem sum_inv_sq_le_half (S : Finset ℕ) (φ : ℕ → ℝ) (R : ℝ) (hR : 1/2 < R)
    (hφ : ∀ a ∈ S, R ≤ φ a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ 1 / (R - 1/2) := by
  set g : ℕ → ℕ := fun a => ⌊φ a - R⌋₊ with hg
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h2 := Nat.lt_floor_add_one (φ a - R)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb))
    have h4 := Nat.lt_floor_add_one (φ b - R)
    simp only [hg] at hab
    rw [hab] at h1 h2
    apply hsep a ha b hb
    rw [abs_lt]; constructor <;> linarith
  have step1 : ∑ a ∈ S, 1 / (φ a) ^ 2 ≤ ∑ a ∈ S, 1 / (R + g a) ^ 2 := by
    apply sum_le_sum
    intro a ha
    have h1 : (g a : ℝ) ≤ φ a - R := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h0 : (0 : ℝ) ≤ g a := Nat.cast_nonneg _
    have h2 : 0 < R + g a := by linarith
    apply one_div_le_one_div_of_le (pow_pos h2 2)
    nlinarith
  have step2 : ∑ a ∈ S, 1 / (R + g a) ^ 2 = ∑ k ∈ S.image g, 1 / (R + k) ^ 2 := by
    rw [sum_image hinj]
  have step3 : ∑ k ∈ S.image g, 1 / (R + k) ^ 2 ≤
      ∑ k ∈ range (S.sup g + 1), 1 / (R + k) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [mem_image] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [mem_range]
      exact Nat.lt_succ_of_le (le_sup ha)
    · intro k _ _
      positivity
  have h4 := sum_range_inv_sq_le_half R hR (S.sup g + 1)
  have h5 : 0 ≤ 1 / (R - 1/2 + ((S.sup g + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) ≤ ((S.sup g + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact one_div_nonneg.mpr (by linarith)
  linarith

theorem directed_tail_sharp (N : Nat) (β : ℝ) (S : Finset Nat) (d : Nat → ℝ) (s R : ℝ)
    (hs : 0 ≤ s) (hR : 1/2 < R) (hd : ∀ a ∈ S, R ≤ d a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |d a - d b| < 1 → a = b)
    (hpt : ∀ a ∈ S, ampSq N β a ≤ s / ((3141591 / 1000000 : ℝ) ^ 2 * (d a) ^ 2)) :
    ∑ a ∈ S, ampSq N β a ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R - 1/2)) := by
  have hi := sum_inv_sq_le_half S d R hR hd hsep
  calc
    _ ≤ ∑ a ∈ S, (s / (3141591 / 1000000 : ℝ) ^ 2) * (1 / (d a) ^ 2) := by
      apply Finset.sum_le_sum
      intro a ha
      calc ampSq N β a ≤ s / ((3141591 / 1000000 : ℝ) ^ 2 * (d a) ^ 2) := hpt a ha
        _ = (s / (3141591 / 1000000 : ℝ) ^ 2) * (1 / (d a) ^ 2) := by
          rw [div_mul_div_comm, mul_one]
    _ = (s / (3141591 / 1000000 : ℝ) ^ 2) * (∑ a ∈ S, 1 / (d a) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)

theorem far_tail_sharp : 3 / (Real.pi ^ 2 * ((2 : ℝ) ^ 40 - 1)) ≤ (1 : ℝ) / 10 ^ 12 := by
  have hp := Real.pi_gt_three
  have hp2 : 9 < Real.pi ^ 2 := by nlinarith
  have h40 : (0 : ℝ) < (2 : ℝ) ^ 40 - 1 := by norm_num
  have hd : 0 < Real.pi ^ 2 * ((2 : ℝ) ^ 40 - 1) := mul_pos (by positivity) h40
  rw [div_le_div_iff₀ hd (by norm_num)]
  have h9 : 9 * ((2 : ℝ) ^ 40 - 1) ≤ Real.pi ^ 2 * ((2 : ℝ) ^ 40 - 1) :=
    mul_le_mul_of_nonneg_right hp2.le h40.le
  have hn : (3 : ℝ) * 10 ^ 12 ≤ 1 * (9 * ((2 : ℝ) ^ 40 - 1)) := by norm_num
  linarith

/-- Weighted circular concentration with one radius per direction. -/
theorem circular_mass_two (N : Nat) (hNbig : 2^60 ≤ N) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R1 R2 : ℝ) (hR1 : 1 ≤ R1) (hR2 : 1 ≤ R2) :
    1 - Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 *
        (1 / (R1 - 1/2) + 1 / (R2 - 1/2)) - 1 / 10^12 ≤
      ∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2
        then ampSq N β a else 0 := by
  classical
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hNbig
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNreal : (2 : ℝ) ^ 60 ≤ N := by exact_mod_cast hNbig
  set s := Real.sin (Real.pi * N * β) ^ 2 with hsdef
  have hs0 : 0 ≤ s := sq_nonneg _
  let RS := (Finset.range N).filter
    (fun a => R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 2^40)
  let LS := (Finset.range N).filter
    (fun a => R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 2^40)
  have hsm : ∀ φ : ℝ, φ < 2^40 → φ / (N : ℝ) ≤ 1 / 2^20 := by
    intro φ hφ
    rw [div_le_iff₀ hNR]
    have : (1 / 2^20 : ℝ) * 2^60 = 2^40 := by norm_num
    nlinarith
  have rBound : ∑ a ∈ RS, ampSq N β a ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2)) := by
    apply directed_tail_sharp N β RS (phiR N ((N : ℝ) * β)) s R1 hs0 (by linarith)
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiR_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      exact ampSq_phiR_sharp N hN β a (by linarith [hd.1]) (hsm _ hd.2)
  have lBound : ∑ a ∈ LS, ampSq N β a ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R2 - 1/2)) := by
    apply directed_tail_sharp N β LS (phiL N ((N : ℝ) * β)) s R2 hs0 (by linarith)
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · intro a ha b hb hab
      exact phiL_sep N ((N : ℝ) * β) a b
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    · intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      exact ampSq_phiL_sharp N hN β a (by linarith [hd.1]) (hsm _ hd.2)
  have fBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40)
      then ampSq N β a else 0) ≤ (1 : ℝ) / 10^12 := by
    have hc := circular_mass N hN β (2^40) hβ0 hβ1 (by norm_num)
    have hs : (∑ a ∈ Finset.range N,
        if phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) +
      (∑ a ∈ Finset.range N,
        if ¬(phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40)
        then ampSq N β a else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert parseval N hN β using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    rw [eq_sub_of_add_eq' hs]
    exact (sub_le_comm.mp hc).trans far_tail_sharp
  have cover (a : Nat) :
      (if ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
        then ampSq N β a else 0) ≤
      (if R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) +
      (if R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) +
      (if ¬(phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40)
        then ampSq N β a else 0) := by
    have ha0 : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
    by_cases hb : ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
    · rw [if_pos hb]
      have hr : R1 ≤ phiR N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inl h))
      have hl : R2 ≤ phiL N ((N : ℝ) * β) a := le_of_not_gt (fun h => hb (Or.inr h))
      by_cases hRR : R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 2^40
      · rw [if_pos hRR]
        split_ifs <;> linarith
      · rw [if_neg hRR]
        by_cases hLL : R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 2^40
        · rw [if_pos hLL]
          split_ifs <;> linarith
        · rw [if_neg hLL]
          have hf : ¬(phiR N ((N : ℝ) * β) a < 2^40 ∨ phiL N ((N : ℝ) * β) a < 2^40) := by
            rintro (h | h)
            · exact hRR ⟨hr, h⟩
            · exact hLL ⟨hl, h⟩
          rw [if_pos hf]
          linarith
    · rw [if_neg hb]
      split_ifs <;> linarith
  have badBound : (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
      then ampSq N β a else 0) ≤
      s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2)) +
        s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R2 - 1/2)) + 1 / 10^12 := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.range N) => cover a)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    have hRs : (∑ a ∈ Finset.range N,
        if R1 ≤ phiR N ((N : ℝ) * β) a ∧ phiR N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2)) := by
      simpa only [RS, Finset.sum_filter] using rBound
    have hLs : (∑ a ∈ Finset.range N,
        if R2 ≤ phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a < 2^40
        then ampSq N β a else 0) ≤ s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R2 - 1/2)) := by
      simpa only [LS, Finset.sum_filter] using lBound
    exact h.trans (add_le_add (add_le_add hRs hLs) fBound)
  have htotal : (∑ a ∈ Finset.range N,
      if phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2
      then ampSq N β a else 0) +
    (∑ a ∈ Finset.range N,
      if ¬(phiR N ((N : ℝ) * β) a < R1 ∨ phiL N ((N : ℝ) * β) a < R2)
      then ampSq N β a else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert parseval N hN β using 1
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> ring
  have he : s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2) + 1 / (R2 - 1/2)) =
      s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R1 - 1/2)) +
        s / (3141591 / 1000000 : ℝ) ^ 2 * (1 / (R2 - 1/2)) := by ring
  linarith

theorem left_pair (x y : ℝ) (hx : 16 ≤ x) (hy : 16 ≤ y) (hxy : 33 ≤ x + y) :
    1 / (x - 1/2) + 1 / (y - 1/2) ≤ 128 / 1023 := by
  have hx' : 0 < x - 1/2 := by linarith
  have hy' : 0 < y - 1/2 := by linarith
  rw [div_add_div _ _ hx'.ne' hy'.ne', div_le_div_iff₀ (mul_pos hx' hy') (by norm_num)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem right_pair (e : ℝ) (he : |e| ≤ 1/2) :
    1 / ((29 - e) - 1/2) + 1 / ((28 + e) - 1/2) ≤ 56 / 783 := by
  have h := abs_le.mp he
  have hx : 0 < (29 - e) - 1/2 := by linarith
  have hy : 0 < (28 + e) - 1/2 := by linarith
  rw [div_add_div _ _ hx.ne' hy.ne', div_le_div_iff₀ (mul_pos hx hy) (by norm_num)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3/2 - e by linarith) (show (0 : ℝ) ≤ 1/2 + e by linarith)]

/-- Nearest-numerator window at half-width `N/(2r) ≥ 16`, with exact integer radii. -/
theorem window_mass_left_two (r N n : ℕ) (hn0 : 0 < n) (hnr : n < r)
    (hNbig : 2^60 ≤ N) (hrN : 32 * r ≤ N) :
    1 - Real.sin (Real.pi * N * ((n : ℝ) / (r : ℝ))) ^ 2 *
        ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) - 1 / 10^12 ≤
      ∑ a ∈ range N,
        if (2 * r * a + N) / (2 * N) = n then ampSq N ((n : ℝ) / (r : ℝ)) a else 0 := by
  have hr : 0 < r := by omega
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hNbig
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
  have hrN' : 32 * (r : ℝ) ≤ N := by exact_mod_cast hrN
  have hL16 : 16 ≤ L := by nlinarith
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβ1 : β < 1 := by rw [hβ]; exact (div_lt_one hrR).2 hnR
  have hcβ : (N : ℝ) * β = c := by rw [hβ, hc]; ring
  -- exact radii of the two excluded half-lines
  have hA1 : c + L ≤ (⌈c + L⌉ : ℝ) := Int.le_ceil _
  have hA2 : (⌈c + L⌉ : ℝ) < c + L + 1 := Int.ceil_lt_add_one _
  have hB1 : c - L ≤ (⌈c - L⌉ : ℝ) := Int.le_ceil _
  have hB2 : (⌈c - L⌉ : ℝ) < c - L + 1 := Int.ceil_lt_add_one _
  set R1 : ℝ := (⌈c + L⌉ : ℝ) - c with hR1
  set R2 : ℝ := c - (⌈c - L⌉ : ℝ) + 1 with hR2
  have hgap : (32 : ℝ) ≤ (⌈c + L⌉ : ℝ) - (⌈c - L⌉ : ℝ) := by
    have hz : (31 : ℝ) < ((⌈c + L⌉ - ⌈c - L⌉ : ℤ) : ℝ) := by push_cast; linarith
    have hz' : (31 : ℤ) < ⌈c + L⌉ - ⌈c - L⌉ := by exact_mod_cast hz
    have hz'' : (32 : ℤ) ≤ ⌈c + L⌉ - ⌈c - L⌉ := by omega
    have hz''' : (32 : ℝ) ≤ ((⌈c + L⌉ - ⌈c - L⌉ : ℤ) : ℝ) := by exact_mod_cast hz''
    push_cast at hz'''
    exact hz'''
  have hpair := left_pair R1 R2 (by rw [hR1]; linarith) (by rw [hR2]; linarith)
    (by rw [hR1, hR2]; linarith)
  have hmass := circular_mass_two N hNbig β hβ0 hβ1 R1 R2 (by rw [hR1]; linarith)
    (by rw [hR2]; linarith)
  rw [hcβ] at hmass
  have hs0 : 0 ≤ Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 := by positivity
  have hweak : Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 *
      (1 / (R1 - 1/2) + 1 / (R2 - 1/2)) ≤
      Real.sin (Real.pi * N * β) ^ 2 * ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) := by
    calc _ ≤ Real.sin (Real.pi * N * β) ^ 2 / (3141591 / 1000000 : ℝ) ^ 2 * (128 / 1023) :=
          mul_le_mul_of_nonneg_left hpair hs0
      _ = _ := by ring
  refine le_trans (by linarith) (hmass.trans ?_)
  apply Finset.sum_le_sum
  intro a ha
  have haN : (a : ℝ) < N := by exact_mod_cast (mem_range.mp ha)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hgood : (phiR N c a < R1 ∨ phiL N c a < R2) →
      (2 * r * a + N) / (2 * N) = n := by
    intro hnear
    by_contra hbad
    rcases window_cases r N n a hN hbad with h | h
    · have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
      have hca : c + L ≤ (a : ℝ) := by nlinarith
      have hceil : ⌈c + L⌉ ≤ (a : ℤ) := Int.ceil_le.mpr (by push_cast; exact hca)
      have hceil' : (⌈c + L⌉ : ℝ) ≤ (a : ℝ) := by exact_mod_cast hceil
      have hpr : R1 ≤ phiR N c a := by
        unfold phiR
        rw [if_pos (by linarith)]
        rw [hR1]; linarith
      have hpl : R2 ≤ phiL N c a := by
        unfold phiL
        rw [if_neg (by linarith)]
        rw [hR2]; linarith
      rcases hnear with hn | hn <;> linarith
    · have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
      have hca : (a : ℝ) < c - L := by nlinarith
      have hceil : (a : ℤ) < ⌈c - L⌉ := Int.lt_ceil.mpr (by push_cast; exact hca)
      have hceil1 : (a : ℤ) + 1 ≤ ⌈c - L⌉ := hceil
      have hceil' : (a : ℝ) + 1 ≤ (⌈c - L⌉ : ℝ) := by exact_mod_cast hceil1
      have hpr : R1 ≤ phiR N c a := by
        unfold phiR
        rw [if_neg (by linarith)]
        rw [hR1]; linarith
      have hpl : R2 ≤ phiL N c a := by
        unfold phiL
        rw [if_pos (by linarith)]
        rw [hR2]; linarith
      rcases hnear with hn | hn <;> linarith
  have hnneg : 0 ≤ ampSq N β a := Complex.normSq_nonneg _
  split_ifs with hn hg
  · exact le_rfl
  · exact (hg (hgood hn)).elim
  · exact hnneg
  · exact le_rfl

/-- Offset of the right peak from its nearest integer. -/
def peakOffset (r : Nat) (k : Fin r) : ℝ :=
  ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r) - round (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r))

theorem peakOffset_abs (r : Nat) (k : Fin r) : |peakOffset r k| ≤ 1/2 := abs_sub_round _

def rightGood56 (r : Nat) (k : Fin r) (b : Fin (2^208)) : Prop :=
  ∃ j : ℤ, -28 ≤ j ∧ j ≤ 27 ∧ neighborWord b.val j = (reducedPeak r 208 k).val

/-- Directed coverage: a sample within `29 − e` to the right or `28 + e` to the left of the
peak is mapped onto the reduced peak by one of the shifts `−28..27`. -/
theorem neighbor_coverage56 (r : Nat) (hr : 0 < r) (k : Fin r) (b : Fin (2^208))
    (hc : phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 29 - peakOffset r k ∨
      phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 28 + peakOffset r k) :
    rightGood56 r k b := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r) with hcdef
  set m : ℤ := round c with hm
  have hpo : peakOffset r k = c - m := rfl
  rw [hpo] at hc
  have hround : |c - m| ≤ 1/2 := abs_sub_round c
  have hr1 := (abs_le.mp hround).1
  have hr2 := (abs_le.mp hround).2
  have hc0 : 0 ≤ c := by positivity
  have hkr : (k.val : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast k.isLt)
  have hNpos : (0 : ℝ) < ((2^208 : Nat) : ℝ) := by positivity
  have hcN : c < ((2^208 : Nat) : ℝ) := by
    rw [hcdef]; nlinarith
  have hb0 : (0 : ℝ) ≤ (b.val : ℝ) := Nat.cast_nonneg _
  have hbN : (b.val : ℝ) < ((2^208 : Nat) : ℝ) := by exact_mod_cast b.isLt
  have hNZ : (((2^208 : Nat) : ℤ) : ℝ) = ((2^208 : Nat) : ℝ) := Int.cast_natCast _
  have hN2 : ((2^208 : Nat) : ℝ) =
      411376139330301510538742295639337626245683966408394965837152256 := by norm_num
  -- an integer lift `B = b + z·2^208` with `m − B ∈ [−28, 27]`
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℤ, (-29 : ℝ) < (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) ∧
      (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) < 28 := by
    rcases hc with hc | hc
    · unfold phiR at hc
      split_ifs at hc with h
      · exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩
      · exact ⟨1, by push_cast; linarith, by push_cast; linarith⟩
    · unfold phiL at hc
      split_ifs at hc with h
      · exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩
      · exact ⟨-1, by push_cast; linarith, by push_cast; linarith⟩
  set j : ℤ := m - ((b.val : ℤ) + z * ((2^208 : Nat) : ℤ)) with hj
  have hjR : (j : ℝ) = (m : ℝ) - ((b.val : ℝ) + z * ((2^208 : Nat) : ℝ)) := by
    rw [hj]; push_cast; ring
  have hj1 : (-29 : ℤ) < j := by
    have h1 : (-29 : ℝ) < (j : ℝ) := by rw [hjR]; exact hz1
    exact_mod_cast h1
  have hj2 : j < 28 := by
    have h2 : (j : ℝ) < 28 := by rw [hjR]; exact hz2
    exact_mod_cast h2
  refine ⟨j, by omega, by omega, ?_⟩
  have he : m = (reducedPeakRaw r 208 k : ℤ) := by
    have hc' : c = ((2^208*k.val : Nat) : ℝ)/r := by rw [hcdef]; push_cast; ring
    rw [hm, hc', round_nat_ratio _ r hr]
    simp only [reducedPeakRaw, Nat.mul_assoc]
  have hmod : (reducedPeakRaw r 208 k : ℤ) % (2^208 : Nat) = ((b.val : ℤ) + j) % (2^208 : Nat) := by
    rw [← he, hj, show (b.val : ℤ) + (m - ((b.val : ℤ) + z * ((2^208 : Nat) : ℤ))) =
      m + (-z) * ((2^208 : Nat) : ℤ) by ring, Int.add_mul_emod_self_right]
  have ht := congrArg Int.toNat hmod
  simpa only [neighborWord, reducedPeak, ← Int.natCast_mod, Int.toNat_natCast] using ht.symm

noncomputable def rightMass56 (r : Nat) (k : Fin r) : ℝ := by
  classical
  exact ∑ b : Fin (2^208), if rightGood56 r k b then
    Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0

theorem rightMass56_weighted (r : Nat) (hr : 0 < r) (k : Fin r) :
    1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) - 1 / 10^12 ≤ rightMass56 r k := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hpo := abs_le.mp (peakOffset_abs r k)
  have h := circular_mass_two (2^208) (by norm_num) ((k.val : ℝ) / r)
    (by positivity) ((div_lt_one hrR).mpr (by exact_mod_cast k.isLt))
    (29 - peakOffset r k) (28 + peakOffset r k) (by linarith) (by linarith)
  have hpair := right_pair (peakOffset r k) (peakOffset_abs r k)
  have hs0 : 0 ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 := div_nonneg (sq_nonneg _) (by norm_num)
  have hweak : Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 *
        (1 / ((29 - peakOffset r k) - 1/2) + 1 / ((28 + peakOffset r k) - 1/2)) ≤
      Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 *
        ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) := by
    calc _ ≤ Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
          (3141591 / 1000000 : ℝ) ^ 2 * (56 / 783) := mul_le_mul_of_nonneg_left hpair hs0
      _ = _ := by ring
  have hfin : 1 - Real.sin (Real.pi * ((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) ^ 2 /
      (3141591 / 1000000 : ℝ) ^ 2 *
        (1 / ((29 - peakOffset r k) - 1/2) + 1 / ((28 + peakOffset r k) - 1/2)) - 1 / 10^12 ≤
      ∑ b : Fin (2^208),
      if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 29 - peakOffset r k ∨
        phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b.val < 28 + peakOffset r k
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b.val) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b < 29 - peakOffset r k ∨
        phiL (2^208) (((2^208 : Nat) : ℝ) * ((k.val : ℝ) / r)) b < 28 + peakOffset r k
      then Complex.normSq (paperPhaseAmplitude 208 ((k.val : ℝ) / r) b) else 0)]
    simpa only [ampSq, paperPhaseAmplitude, eigenvalue] using h
  refine le_trans (by linarith) (hfin.trans (Finset.sum_le_sum (fun b _ => ?_)))
  dsimp only [rightMass56]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage56 r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem prod_lower (x y A B f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : 0 ≤ f)
    (hx : 1 - A - f ≤ x) (hy : 1 - B - f ≤ y) (hA1 : A + f ≤ 1) (hB1 : B + f ≤ 1) :
    1 - 2 * f - A - B ≤ x * y := by
  have h := mul_le_mul hx hy (by linarith) (by linarith)
  nlinarith [mul_nonneg (add_nonneg hA hf) (add_nonneg hB hf)]

theorem averaged_pair_coverage261 (r n d : Nat) (hr : r.Prime)
    (hNbig : 2^60 ≤ 2^n) (hprecision : 32 * r ≤ 2^n)
    (accept : Fin (2^n) → Fin (2^208) → Prop) [∀ a b, Decidable (accept a b)]
    (haccept : ∀ (k : Fin r), k.val ≠ 0 → ∀ a b,
      ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val →
      rightGood56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b →
      accept a b) :
    (1 - 1 / (r : ℝ)) * (1 - 2 / 10^12) - ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) / 2 -
      ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) / 2 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208),
      if accept a b then asymmetricPairMass r n 208 d (a, b) else 0 := by
  classical
  let A : Fin r → Fin (2^n) → ℝ := fun k a =>
    Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2^208) → ℝ := fun k b =>
    Complex.normSq (paperPhaseAmplitude 208 (((d * k.val % r : Nat) : ℝ) / r) b.val)
  let good : Fin r → Fin (2^n) → Fin (2^208) → Prop := fun k a b =>
    k.val ≠ 0 ∧ ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val ∧
      rightGood56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b
  let F : Fin r → Fin (2^n) → Fin (2^208) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let sL : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^n : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let sR : Fin r → ℝ := fun k =>
    Real.sin (Real.pi * ((2^208 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2
  let CL : ℝ := (128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2
  let CR : ℝ := (56 / 783) / (3141591 / 1000000 : ℝ) ^ 2
  have hCL : 0 ≤ CL ∧ CL ≤ 1/2 := by constructor <;> norm_num [CL]
  have hCR : 0 ≤ CR ∧ CR ≤ 1/2 := by constructor <;> norm_num [CR]
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
      asymmetricPairMass r n 208 d (a, b) = (r : ℝ)⁻¹ * ∑ k : Fin r, A k a * B k b := by
    intro a b
    simp only [asymmetricPairMass, one_div, A, B]
  have step1 :
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2^n), ∑ b : Fin (2^208),
          if accept a b then asymmetricPairMass r n 208 d (a, b) else 0 := by
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
      1 - sL k * CL - 1 / 10^12 ≤ ∑ a : Fin (2^n),
        if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val then A k a else 0 := by
    have h := window_mass_left_two r (2^n) k.val
      (Nat.pos_of_ne_zero hk) k.isLt hNbig hprecision
    rw [Fin.sum_univ_eq_sum_range (fun a =>
      if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a = k.val then
        Complex.normSq (paperPhaseAmplitude n ((k.val : ℝ) / r) a) else 0)]
    simpa only [ShorECDLP.Quantum.OrderFinding.nearestNumerator, paperPhaseAmplitude,
      eigenvalue] using h
  have hright (k : Fin r) :
      1 - sR k * CR - 1 / 10^12 ≤ rightMass56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ :=
    rightMass56_weighted r hr.pos ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩
  have step3 : ∀ k : Fin r,
      (if k.val = 0 then 0 else (1 - 2 / 10^12 : ℝ)) - sL k * CL - sR k * CR ≤
      ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    intro k
    have hsL : 0 ≤ sL k := sq_nonneg _
    have hsR : 0 ≤ sR k := sq_nonneg _
    have hsL1 : sL k ≤ 1 := Real.sin_sq_le_one _
    have hsR1 : sR k ≤ 1 := Real.sin_sq_le_one _
    have hAL : 0 ≤ sL k * CL := mul_nonneg hsL hCL.1
    have hAR : 0 ≤ sR k * CR := mul_nonneg hsR hCR.1
    have hAL1 : sL k * CL ≤ 1/2 := by nlinarith [hCL.2]
    have hAR1 : sR k * CR ≤ 1/2 := by nlinarith [hCR.2]
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b :=
        Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF k a b))
      linarith
    · rw [if_neg hk]
      have he : (∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b) =
          (∑ a : Fin (2^n), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r n a.val = k.val
            then A k a else 0) * rightMass56 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ := by
        rw [rightMass56, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F, good, B]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [he]
      have hp := prod_lower _ _ (sL k * CL) (sR k * CR) (1 / 10^12) hAL hAR (by norm_num)
        (hleft k hk) (hright k) (by linarith) (by linarith)
      linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  have hcount : (∑ k : Fin r, (if k.val = 0 then (0 : ℝ) else (1 - 2 / 10^12))) =
      ((r : ℝ) - 1) * (1 - 2 / 10^12) := by
    have hz : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
      simp [hr.pos]
    calc
      _ = ∑ k : Fin r, ((1 - 2 / 10^12 : ℝ) - (1 - 2 / 10^12) * (if k.val = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcount, ← Finset.sum_mul,
    ← Finset.sum_mul] at hsum
  have hL := left_weight_sum r n
  have hR := right_weight_sum r d hr.pos
  have hlow : ((r : ℝ) - 1) * (1 - 2 / 10^12) - (r : ℝ) / 2 * CL - (r : ℝ) / 2 * CR ≤
      ∑ k : Fin r, ∑ a : Fin (2^n), ∑ b : Fin (2^208), F k a b := by
    have h1 : (∑ k : Fin r, sL k) * CL ≤ (r : ℝ) / 2 * CL :=
      mul_le_mul_of_nonneg_right hL hCL.1
    have h2 : (∑ k : Fin r, sR k) * CR ≤ (r : ℝ) / 2 * CR :=
      mul_le_mul_of_nonneg_right hR hCR.1
    linarith
  have hlower := mul_le_mul_of_nonneg_left hlow hrinv
  have heval : (r : ℝ)⁻¹ * (((r : ℝ) - 1) * (1 - 2 / 10^12) - (r : ℝ) / 2 * CL -
      (r : ℝ) / 2 * CR) = (1 - 1 / (r : ℝ)) * (1 - 2 / 10^12) - CL / 2 - CR / 2 := by
    field_simp
  rw [heval, step2] at hlower
  exact hlower.trans step1

theorem success_budget261 (r : ℝ) (hr : 1000000 ≤ r) :
    (99 : ℝ) / 100 ≤ (1 - 1 / r) * (1 - 2 / 10^12) -
      ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) / 2 -
      ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) / 2 := by
  have hr0 : 0 < r := by linarith
  have hinv : 1 / r ≤ (1 : ℝ) / 1000000 :=
    one_div_le_one_div_of_le (by norm_num) hr
  have hC : ((128 / 1023) / (3141591 / 1000000 : ℝ) ^ 2) / 2 +
      ((56 / 783) / (3141591 / 1000000 : ℝ) ^ 2) / 2 ≤ 9963 / 1000000 := by norm_num
  nlinarith

theorem precision261 : 32 * order ≤ 2^261 := by norm_num [order]

def params261 : DecoderParams := ⟨261,208,by decide,by decide,by decide,by decide⟩

def pairRecovered261 (d a b : Nat) : Bool :=
  decide (∃i : Fin 56,(d : ZMod order)∈fixedCandidates params261 a (neighborWord b ((i.val : ℤ)-28)))

theorem pairRecovered261_of_character (d : Nat) (k : Fin order) (hk : k.val≠0)
    (a : Fin (2^261)) (b : Fin (2^208))
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 261 a.val=k.val)
    (hb : rightGood56 order ⟨d*k.val%order,Nat.mod_lt _ order_prime.pos⟩ b) :
    pairRecovered261 d a.val b.val=true := by
  classical
  obtain ⟨j,hlo,hhi,hj⟩:=hb
  let i : Fin 56:=⟨(j+28).toNat,by omega⟩
  have hi : (i.val : ℤ)-28=j := by dsimp [i];omega
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
      (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 261 a.val : ZMod order)⁻¹=d
    rw [ha]
    simp only [ZMod.natCast_mod,Nat.cast_mul]
    field_simp

theorem pair_success261 (Q : Point) (d : Nat) (_hn : Q≠0) (_hd : Q=d•G) :
    (99 : ℝ)/100 ≤ ∑a : Fin (2^261),∑b : Fin (2^208),
      if pairRecovered261 d a.val b.val then asymmetricPairMass order 261 208 d (a,b) else 0 := by
  have h:=averaged_pair_coverage261 order 261 d order_prime (by norm_num) precision261
    (fun a b=>pairRecovered261 d a.val b.val=true)
    (fun k hk a b ha hb=>pairRecovered261_of_character d k hk a b ha hb)
  exact (success_budget261 order (by norm_num [order])).trans h

theorem decoder_budget261 : 56 * (2*(order/2^208+2)) ≤ 56*(2^49+2) := by
  norm_num [order]

end
end ShorECDLP.Entrant.SinAverage261

-- ===== formerly Readout56 =====

/-! Fifty-six neighbouring right words from one sample: the centre, 27 positive shifts and
28 negative shifts. The construction is `NeighborReadout.neighborSuffix` with one more
negative step; every gate is a permitted record-controlled Clifford on wires 0 and 1. -/

namespace ShorECDLP.Entrant.Readout56
open Quantum ShorECDLP.Challenge ShorECDLP.Entrant.RoundedReadout ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def suffix56 (n start width : Nat) (bits : Vector (Fin start) width) :
    Straight n start (start+2+168*width) :=
  let c:=initialCursor bits
  let q:=c.lift (27*(2*width))
  castFinish (by omega)
    ((constantStep n start).append
      ((positiveWords n 27 (start+2) width c).append
        ((complementStep n q).append
          (negativeWords n 28 (start+2+27*(2*width)+2*width) width q.next))))

def rightWords56 {start width : Nat} (bits : Vector (Fin start) width) : List (Vector Nat width) :=
  bits.map Fin.val ::
    List.ofFn (fun i : Fin 27=>sumPositions (start+2+i.val*(2*width)) width) ++
    List.ofFn (fun i : Fin 28=>sumPositions
      (start+2+27*(2*width)+2*width+i.val*(4*width)+2*width) width)

theorem rightWords56_length {start width : Nat} (bits : Vector (Fin start) width) :
    (rightWords56 bits).length=56 := by simp [rightWords56]

attribute [local irreducible] positiveWords negativeWords incrementStep complementStep

theorem suffix56_wellFormed (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix56 n start width bits).WellFormed := by
  unfold suffix56
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed _ _ (constantStep_wellFormed _ _)
  apply straight_append_wellFormed _ _ (positiveWords_wellFormed _ _ _ _ _)
  exact straight_append_wellFormed _ _ (complementStep_wellFormed _ _)
    (negativeWords_wellFormed _ _ _ _ _)

theorem suffix56_slots (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix56 n start width bits).gateSlots=7+588*width := by
  simp only [suffix56,castFinish_gateSlots,Straight.gateSlots_append,
    constantStep_slots,positiveWords_slots,complementStep_slots,negativeWords_slots]
  ring

theorem append_t_zero {n a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n→Bool)
    (hp : ∀h, (p.instantiate read h).tCount=0)
    (hq : ∀h, (q.instantiate read h).tCount=0) (history : Fin a→Bool) :
    ((p.append q).instantiate read history).tCount=0 := by
  apply Nat.eq_zero_of_le_zero
  have h:=outer_append_t_le p q read history 0 (fun h=>le_of_eq (hq h))
  simpa only [hp,Nat.add_zero] using h

theorem suffix56_t (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((suffix56 n start width bits).instantiate read history).tCount=0 := by
  unfold suffix56
  rw [castFinish_instantiate]
  apply append_t_zero _ _ read (constantStep_t _ _ _)
  intro h
  apply append_t_zero _ _ read (positiveWords_t _ _ _ _ _ _)
  intro h
  exact append_t_zero _ _ read (complementStep_t _ _ _)
    (negativeWords_t _ _ _ _ _ _) h

theorem suffix56_support (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((suffix56 n start width bits).instantiate read history).wires⊆[0,1] := by
  unfold suffix56
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history ([0,1] : List Wire) (constantStep_support _ _ _ _)
  intro h
  apply outer_append_support _ _ read h ([0,1] : List Wire) (positiveWords_support _ _ _ _ _ _ _)
  intro h
  exact outer_append_support _ _ read h ([0,1] : List Wire) (complementStep_support _ _ _ _)
    (fun hh=>negativeWords_support _ _ _ _ _ _ hh)

/-- Every nonzero readout branch writes all 56 neighbouring residues explicitly. -/
theorem suffix56_branch (n start : Nat) (bits : Vector (Fin start) 208)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((suffix56 n start 208 bits).instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    b.kraus ψ=ψ ∧
      (∀i : Fin 27, readWord (List.ofFn history++b.history)
        (sumPositions (start+2+i.val*416) 208).toList=
        some ((i.val+1+inputValue bits history)%2^208)) ∧
      (∀i : Fin 28, readWord (List.ofFn history++b.history)
        (sumPositions (start+2+11232+416+i.val*832+416) 208).toList=
        some (2^208-1-((i.val+1+(2^208-1-inputValue bits history))%2^208))) := by
  unfold suffix56 at hb
  rw [castFinish_instantiate] at hb
  obtain ⟨h₁,a,u,ha,hu,he₁,rfl⟩:=straight_append_branch _ _ read history b hb
  have han : a.kraus ψ≠0 := by
    intro h;apply hn;simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hc:=constantStep_branch n start read history ψ hψ a ha han
  have hun : u.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hc.1] using hn
  have hcarr:=initial_carry bits history h₁ (he₁.trans (by rw [hc.2]))
  have hval:=initial_value bits history h₁ a.history he₁
  obtain ⟨h₂,p,v,hp,hv,he₂,rfl⟩:=straight_append_branch _ _ read h₁ u hu
  have hpn : p.kraus ψ≠0 := by
    intro h;apply hun;simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hpos:=positiveWords_branch n 27 (start+2) 208 (initialCursor bits)
    read h₁ hcarr ψ hψ p hp hpn
  have hvn : v.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hpos.1] using hun
  let q:=(initialCursor bits).lift (27*(2*208))
  have hqc : h₂ q.carry=true := (lift_carry (initialCursor bits) _ h₁ h₂ p.history he₂).trans hcarr
  have hqv : cursorValue q h₂=inputValue bits history :=
    (lift_value (initialCursor bits) _ h₁ h₂ p.history he₂).trans hval
  obtain ⟨h₃,c,t,hc',ht,he₃,rfl⟩:=straight_append_branch _ _ read h₂ v hv
  have hcn : c.kraus ψ≠0 := by
    intro h;apply hvn;simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hcomp:=complementStep_post n q read h₂ hqc ψ hψ c hc' hcn h₃ he₃
  have htn : t.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hcomp.1] using hvn
  have hneg:=negativeWords_branch n 28 (start+2+27*(2*208)+2*208) 208 q.next
    read h₃ hcomp.2.1 ψ hψ t ht htn
  have hfull₁ : List.ofFn history++(a.seq (p.seq (c.seq t))).history=
      List.ofFn h₁++(p.seq (c.seq t)).history := by
    rw [he₁];simp only [InstrumentBranch.seq,List.append_assoc]
  have hfull₂ : List.ofFn history++(a.seq (p.seq (c.seq t))).history=
      List.ofFn h₂++(c.seq t).history := by
    rw [hfull₁,he₂];simp only [InstrumentBranch.seq,List.append_assoc]
  have hfull₃ : List.ofFn history++(a.seq (p.seq (c.seq t))).history=
      List.ofFn h₃++t.history := by
    rw [hfull₂,he₃];simp only [InstrumentBranch.seq,List.append_assoc]
  refine ⟨by simp only [InstrumentBranch.seq,LinearMap.comp_apply,hc.1,hpos.1,hcomp.1,hneg.1],?_,?_⟩
  · intro i
    rw [hfull₂,readWord_append_left (List.ofFn h₂) (c.seq t).history _ (by
      intro j hj
      have hj':=sumPositions_bound (start+2+i.val*416) 208 j hj
      have hi:=i.isLt
      simp only [List.length_ofFn]
      omega),he₂]
    simpa only [hval] using hpos.2 i
  · intro i
    rw [hfull₃]
    simpa only [hcomp.2.2,hqv] using hneg.2 i

/-- The physical word list contains a correct explicit record for every offset -28..27. -/
theorem suffix56_reads (n start : Nat) (bits : Vector (Fin start) 208)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((suffix56 n start 208 bits).instantiate read history).run)
    (hn : b.kraus ψ≠0) (j : ℤ) (hj : -28≤j ∧ j≤27) :
    ∃ps∈rightWords56 bits, readWord (List.ofFn history++b.history) ps.toList=
      some ((((inputValue bits history : Nat) : ℤ)+j)%(2^208 : Nat)).toNat := by
  have hs:=suffix56_branch n start bits read history ψ hψ b hb hn
  by_cases hz : j=0
  · subst j
    refine ⟨bits.map Fin.val,by simp [rightWords56],?_⟩
    rw [readWord_append_left (List.ofFn history) b.history _ (by
      intro i hi
      simp only [Vector.toList_map,List.mem_map] at hi
      obtain ⟨k,_,rfl⟩:=hi
      simpa only [List.length_ofFn] using k.isLt),input_read]
    congr 1
    simpa only [Nat.zero_add,Int.natCast_zero,Nat.mod_eq_of_lt (input_lt bits history)] using
      (positive_word_mod (inputValue bits history) 0)
  · by_cases hp : 0<j
    · let i : Fin 27:=⟨j.toNat-1,by omega⟩
      have hi : (i.val+1 : ℤ)=j := by dsimp [i];omega
      refine ⟨sumPositions (start+2+i.val*416) 208,?_,?_⟩
      · unfold rightWords56
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
      · rw [hs.2.1 i,positive_word_mod]
        congr 2
        exact congrArg (fun z : ℤ=>(((inputValue bits history : Nat) : ℤ)+z)%(2^208 : Nat)) hi
    · let i : Fin 28:=⟨(-j).toNat-1,by omega⟩
      have hi : -((i.val+1 : Nat) : ℤ)=j := by dsimp [i];omega
      refine ⟨sumPositions (start+2+11232+416+i.val*832+416) 208,?_,?_⟩
      · unfold rightWords56
        apply List.mem_cons_of_mem
        apply List.mem_append_right
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
      · rw [hs.2.2 i,negative_word_mod _ _ (input_lt bits history)]
        congr 2
        rw [sub_eq_add_neg,hi]

end
end ShorECDLP.Entrant.Readout56

-- ===== formerly Schedule261 =====

/-! The 17-bit first load followed by four physical-15 and twelve physical-14 left digits
(261 left bits) and thirteen physical-15 right digits (208 right bits), read with 56
neighbouring right words (`Readout56.suffix56`). The success argument is the averaged bound
`SinAverage261.pair_success261`. -/

section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
namespace ShorECDLP.Entrant.Schedule29Seventeen244
open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-! Twenty-nine corrected additions after a 17-bit first load: seven physical-15 and nine
physical-14 left digits, then thirteen physical-15 right digits. -/
inductive Digit where
  | left16 (index : Fin 4)
  | left15 (index : Fin 12)
  | right16 (index : Fin 13)

def Digit.width : Digit → Nat
  | .left16 _ | .right16 _ => 16
  | .left15 _ => 15

def Digit.exponent : Digit → Nat
  | .left16 j => 228 - 16 * j.val
  | .left15 j => 165 - 15 * j.val
  | .right16 j => 192 - 16 * j.val

def firstRow (a : Fin 131072) : Fin 884736 := ⟨a.val, by omega⟩

def row : (w : Digit) → Fin (2^(w.width-1)) → Fin 884736
  | .left16 j, a => ⟨131072 + j.val*32768 + a.val, by
    have h : a.val < 32768 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .left15 j, a => ⟨262144 + j.val*16384 + a.val, by
    have h : a.val < 16384 := by simpa only [Digit.width] using a.isLt
    omega⟩
  | .right16 j, a => ⟨458752 + j.val*32768 + a.val, by
    have h : a.val < 32768 := by simpa only [Digit.width] using a.isLt
    omega⟩

theorem width_cases (w : Digit) : w.width = 14 ∨ w.width = 15 ∨ w.width = 16 := by
  cases w <;> simp [Digit.width]

def leftDigits : List Digit := List.ofFn (fun j : Fin 4 => .left16 j) ++
  List.ofFn (fun j : Fin 12 => .left15 j)
def rightDigits : List Digit := List.ofFn (fun j : Fin 13 => .right16 j)

theorem left_widths : leftDigits.map Digit.width =
    List.replicate 4 16 ++ List.replicate 12 15 := by
  simp [leftDigits, List.ofFn_succ, Digit.width, List.replicate]
theorem right_widths : rightDigits.map Digit.width = List.replicate 13 16 := by
  simp [rightDigits, List.ofFn_succ, Digit.width, List.replicate]

def leftOffset : Nat := (leftDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum
def rightOffset : Nat := (rightDigits.map (fun w => Single.offsetScalar w.width w.exponent)).sum

def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients (v * 2^244 + leftOffset) rightOffset

def signedCoefficients (w : Digit) (a : Nat) : PointCoeff :=
  match w with
  | .left16 _ | .left15 _ => coefficients (Single.oddScalar w.exponent a) 0
  | .right16 _ => coefficients 0 (Single.oddScalar w.exponent a)

def coefficientAt (i : Fin 884736) : PointCoeff :=
  if i.val < 131072 then initialCoefficients i.val
  else if i.val < 262144 then
    coefficients (Single.oddScalar (228 - 16 * ((i.val - 131072) / 32768)) ((i.val - 131072) % 32768)) 0
  else if i.val < 458752 then
    coefficients (Single.oddScalar (165 - 15 * ((i.val - 262144) / 16384)) ((i.val - 262144) % 16384)) 0
  else coefficients 0 (Single.oddScalar (192 - 16 * ((i.val - 458752) / 32768)) ((i.val - 458752) % 32768))

theorem coefficientAt_first (a : Fin 131072) :
    coefficientAt (firstRow a) = initialCoefficients a.val := by
  simp [coefficientAt, firstRow, a.isLt]

theorem coefficientAt_row (w : Digit) (a : Fin (2^(w.width-1))) :
    coefficientAt (row w a) = signedCoefficients w a.val := by
  cases w with
  | left16 j =>
    have ha : a.val < 32768 := by
      simpa only [Digit.width] using a.isLt
    have he : (row (.left16 j) a).val < 262144 := by simp only [row]; omega
    have hbase : ¬ (row (.left16 j) a).val < 131072 := by simp only [row]; omega
    have hj : ((row (.left16 j) a).val - 131072) / 32768 = j.val := by simp only [row]; omega
    have hh : ((row (.left16 j) a).val - 131072) % 32768 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, he, hj, hh, signedCoefficients, Digit.exponent]
  | left15 j =>
    have ha : a.val < 16384 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.left15 j) a).val < 131072 := by simp only [row]; omega
    have he : (row (.left15 j) a).val < 458752 := by simp only [row]; omega
    have hbase : ¬ (row (.left15 j) a).val < 262144 := by simp only [row]; omega
    have hj : ((row (.left15 j) a).val - 262144) / 16384 = j.val := by simp only [row]; omega
    have hh : ((row (.left15 j) a).val - 262144) % 16384 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, he, hj, hh, signedCoefficients, Digit.exponent]
  | right16 j =>
    have ha : a.val < 32768 := by
      simpa only [Digit.width] using a.isLt
    have hn0 : ¬ (row (.right16 j) a).val < 131072 := by simp only [row]; omega
    have hn1 : ¬ (row (.right16 j) a).val < 262144 := by simp only [row]; omega
    have hbase : ¬ (row (.right16 j) a).val < 458752 := by simp only [row]; omega
    have hj : ((row (.right16 j) a).val - 458752) / 32768 = j.val := by simp only [row]; omega
    have hh : ((row (.right16 j) a).val - 458752) % 32768 = a.val := by simp only [row]; omega
    simp [coefficientAt, hbase, hn0, hn1, hj, hh, signedCoefficients, Digit.exponent]

end ShorECDLP.Entrant.Schedule29Seventeen244




namespace ShorECDLP.Entrant.Schedule29Seventeen244
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def initialPoint (Q : Point) (v : Nat) : Point :=
  (v * 2^244 + leftOffset) • G + rightOffset • Q

theorem initialCoefficients_point (Q : Point) (hQ : order • Q = 0) (v : Nat) :
    constantPoint Q (initialCoefficients v) = initialPoint Q v := by
  unfold initialCoefficients initialPoint
  exact coefficients_point _ _ Q hQ

def firstWindow : Single.Window 884736 := ScheduleFirst17.windowGeneric firstRow

theorem firstWindow_law : WindowLaw coefficientAt firstWindow
    (ScheduleFirst17.update initialPoint) ScheduleFirst17.Input := by
  apply ScheduleFirst17.window_law_generic
  intro Q hQ a
  rw [coefficientAt_first]
  exact initialCoefficients_point Q hQ a.val

end
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single.Distribution
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def Digit.base (Q : Point) : Digit → Point
  | .left16 _ | .left15 _ => G
  | .right16 _ => Q

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
    | left16 _ | left15 _ => exact G_ne_zero
    | right16 _ => exact hn
  have hr : order • P = 0 := by
    cases w with
    | left16 _ | left15 _ => exact generator_nsmul_eq_zero
    | right16 _ => exact hQ
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
    (width exponent v : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) :
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
    rcases hw with rfl | rfl | rfl <;> norm_num
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

def logicalValue16 (low : Nat) (sign : Bool) : Nat := low + 32768 * sign.toNat

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

theorem bank_length (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) :
    (bank width).length = width := by
  rcases hw with rfl | rfl | rfl <;> simp [bank]

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

theorem digit16_low (s : BasisState) :
    digit 16 s = logicalValue16 (tableAddressValue (List.range' 855 15) s) (s 870) := by
  change tableAddressValue (List.range' 855 15 ++ [870]) s =
    tableAddressValue (List.range' 855 15) s + 32768 * (s 870).toNat
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

theorem physical_padding16 (s : BasisState) :
    windowRawDigit 0 s = Single.paddedValue (tableAddressValue (List.range' 855 15) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, Single.paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat]

theorem digit16_raw (s : BasisState) : digit 16 s = windowRawDigit 0 s := by
  rw [digit16_low, physical_padding16]
  rfl

theorem bank_nodup (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) : (bank width).Nodup := by
  rcases hw with rfl | rfl | rfl <;> decide +kernel

theorem bank_subset (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) :
    ∀ v ∈ bank width, v ∈ streamAddress := by
  rcases hw with rfl | rfl | rfl <;> decide +kernel

theorem bank_not_point (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) :
    ∀ v ∈ bank width, v ∉ pointLogicalWires := by
  intro v hv
  exact (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v
    (bank_subset width hw v hv)

theorem digit_low_sign (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) (s : BasisState) :
    digit width s < 2^(width-1) ↔ s 870 = false := by
  rcases hw with rfl | rfl | rfl
  · rw [digit14_low]
    have hb := tableAddressValue_lt (List.range' 855 13) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue14]
  · rw [digit15_low]
    have hb := tableAddressValue_lt (List.range' 855 14) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue15]
  · rw [digit16_low]
    have hb := tableAddressValue_lt (List.range' 855 15) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue16]

theorem selected_address_alias (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16) (s : BasisState)
    (h869 : width ≠ 16 → s 869 = false) (h868 : width = 14 → s 868 = false) :
    signedTableAddress 32768 (windowRawDigit 0 s) % 2^(width-1) =
      signedTableAddress (2^(width-1)) (digit width s) := by
  rcases hw with rfl | rfl | rfl
  · rw [physical_padding14 s (h868 rfl) (h869 (by decide)), digit14_low]
    exact padded_address14 _ _ (by simpa using tableAddressValue_lt (List.range' 855 13) s)
  · rw [physical_padding15 s (h869 (by decide)), digit15_low]
    exact padded_address15 _ _ (by simpa using tableAddressValue_lt (List.range' 855 14) s)
  · rw [digit16_raw, show (2 : Nat)^(16-1) = 32768 by norm_num]
    exact Nat.mod_eq_of_lt (signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s))

theorem selected_increment (Q : Point) (w : Digit) (s : BasisState)
    (h869 : w.width ≠ 16 → s 869 = false) (h868 : w.width = 14 → s 868 = false) :
    (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1))) =
      increment (w.base Q) w.width w.exponent (digit w.width s) := by
  have hpow : (2 : Int)^w.width = 2 * (2^(w.width-1) : Nat) := by
    rcases width_cases w with hw | hw | hw <;> rw [hw] <;> norm_num
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

def paddedRow (w : Digit) (a : Fin 32768) : Fin 884736 :=
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
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

section
variable [b : Single.WindowBody]

def WindowValid (w : Digit) (s : BasisState) : Prop :=
  Single.BodyValid b s ∧ (w.width ≠ 16 → s 869 = false) ∧ (w.width = 14 → s 868 = false)

def signedWindow (w : Digit) : Single.Window 884736 :=
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
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
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
  simp only [rightDigits, List.mem_ofFn] at hw
  obtain ⟨i, rfl⟩ := hw
  rfl

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
    have hwidths : ((leftDigits.map f).map (fun w => w.physical.wires.length)).sum = 244 := by
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
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
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
theorem bank_padding869 (w : Digit) (hw : w.width ≠ 16) : 869 ∉ bank w.width := by
  rcases width_cases w with h | h | h
  · rw [h]; decide +kernel
  · rw [h]; decide +kernel
  · exact absurd h hw

omit b in
theorem bank_padding868 (w : Digit) (hw : w.width = 14) : 868 ∉ bank w.width := by
  rw [hw]
  decide +kernel

omit b in
theorem bank_clean (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16)
    (s : BasisState) (hz : Clean streamAddress s) : Clean (bank width) s :=
  fun v hv => hz v (bank_subset width hw v hv)

omit b in
theorem point_bank_clean (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16)
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
  · intro hw16
    rw [phaseWordState_frame _ _ _ 869 (bank_padding869 w hw16),
      pointWrite_frame P s 869 (by decide +kernel)]
    exact hz 869 (by decide +kernel)
  · intro hw
    rw [phaseWordState_frame _ _ _ 868 (bank_padding868 w hw),
      pointWrite_frame P s 868 (by decide +kernel)]
    exact hz 868 (by decide +kernel)

omit b in
theorem assigned_coordinates (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16)
    (P : Point) (s : BasisState) (input : List Bool) :
    pointStateCoordinates (phaseWordState (bank width) input (pointWrite P s)) =
      fig14PointEncoding P := by
  rw [phaseWordState_pointWrite _ (bank_not_point width hw), pointWrite_coordinates]

omit b in
theorem assigned_digit (width : Nat) (hw : width = 14 ∨ width = 15 ∨ width = 16)
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
end ShorECDLP.Entrant.Schedule29Seventeen244


namespace ShorECDLP.Entrant.Schedule29Seventeen244
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
  ideal := Finsupp.lmapDomain ℂ ℂ (ScheduleFirst17.update initialPoint Q)
  valid := ScheduleFirst17.Input
  nodup := by change ScheduleFirst17.bits.reverse.Nodup; exact List.nodup_reverse.mpr Single.first17_nodup
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
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 17) •
        ((fourierOutcomes 17).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior bits •
            ket (pointWrite (initialPoint Q (boolWordToNat input)) root))).sum := by
  simp only [WindowModel.step, firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.reverse_reverse, LinearMap.comp_apply]
  exact Single.first17_window_point_sum_generic initialPoint Q prior bits root hs hz

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
  have hlen : ScheduleFirst17.bits.length = 17 := by decide +kernel
  simpa only [firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.length_reverse, hlen] using
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
  · simp only [firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.reverse_reverse]
    exact ScheduleFirst17.input_prepare _ (fun _ h => h) _
      (supportedOn_ket _ _ (ScheduleFirst17.input_of_strong root hs))
  · intro prior bits
    apply ready_signed Q hQ hn ws root hs hz
    rw [firstModel_step Q hQ hn prior bits root hs hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

end
end ShorECDLP.Entrant.Schedule29Seventeen244

namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes

def count (c14 c15 c16 : Nat) (w : Digit) : Nat :=
  if w.width = 14 then c14 else if w.width = 15 then c15 else c16

class Programs (body : Single.WindowBody) where
  records14 : Nat
  records15 : Nat
  records16 : Nat
  cost14 : Nat
  cost15 : Nat
  cost16 : Nat
  program : (w : Digit) → (start : Nat) → Straight 884736 start
    (start + count records14 records15 records16 w)
  coherent : ∀ Q, order • Q = 0 → Q ≠ 0 → ∀ w start history,
    CoherentlyImplementsOn ((program w start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w)
  wellFormed : ∀ w start, (program w start).WellFormed
  slots : ∀ w start, (program w start).gateSlots ≤ body.slotBound
  wires : ∀ w start, straightWires (program w start) ⊆ body.support
  tCount : ∀ Q w start history,
    ((program w start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count cost14 cost15 cost16 w

variable [impl : Programs b]

def signedWindow (w : Digit) : Single.Window 884736 :=
  ⟨(bank w.width).reverse, count impl.records14 impl.records15 impl.records16 w, impl.program w⟩

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
  · simp only [firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.reverse_reverse]
    exact ScheduleFirst17.input_prepare _ (fun _ h => h) _
      (supportedOn_ket _ _ (ScheduleFirst17.input_of_strong root hs))
  · intro prior bits
    apply ready_signed Q hQ hn ws root hs hz
    rw [firstModel_step Q hQ hn prior bits root hs hz]
    apply Support.smul
    apply Support.list_sum
    intro input hi
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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
    precision (firstModel Q hQ hn :: leftDigits.map (signedModel Q hQ hn)) = 261 := by
  rw [precision, List.map_cons, List.sum_cons]
  have hlen : ScheduleFirst17.bits.length = 17 := by decide +kernel
  simp only [firstModel, firstWindow, ScheduleFirst17.windowGeneric, List.length_reverse, hlen,
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
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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
      idealEventMass Q root 261 208 accept := by
  rw [physicalTwoAxes_event_mass Q root _ _ start history _
    (concrete_ready Q hQ hn root hs hz) (concrete_kernel Q hQ hn root hs hz) J hJ accept,
    left_precision Q hQ hn, right_precision Q hQ hn]

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible



namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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

def leftWindows : List (Single.Window 884736) := firstWindow :: leftDigits.map signedWindow

def rightWindows : List (Single.Window 884736) := rightDigits.map signedWindow

def leftMetadata : List (Nat × Nat) :=
  (131071, 17) :: List.replicate 4 (impl.records16, 16) ++ List.replicate 12 (impl.records15, 15)

def rightMetadata : List (Nat × Nat) :=
  List.replicate 13 (impl.records16, 16)

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftDigits, signedWindow,
    Digit.width, count, bank, firstWindow, ScheduleFirst17.windowGeneric, ScheduleFirst17.bits, leftMetadata, List.ofFn_succ, List.replicate]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightDigits, signedWindow,
    Digit.width, count, bank, rightMetadata, List.ofFn_succ, List.replicate]

theorem left_record_count : recordCount leftMetadata = 131071 + 4 * impl.records16 + 12 * impl.records15 + 261 := by
  simp [leftMetadata, recordCount, List.replicate]
  omega

theorem right_record_count : recordCount rightMetadata = 13 * impl.records16 + 208 := by
  simp [rightMetadata, recordCount, List.replicate]
  omega

variable [ledger : Single.ProducerResources body]

theorem left_count : axisCount leftWindows = 131071 + 4 * impl.records16 + 12 * impl.records15 + 261 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 13 * impl.records16 + 208 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

def resetBody (start : Nat) : Straight 884736 start (start + body.reset.length) :=
  resetProgram 884736 start body.reset

omit ledger impl in
theorem resetBody_run (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).run =
      (measureResetWithCorrection body.reset (fun _ => [])).run := by
  unfold resetBody
  rw [resetProgram_run]

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + body.reset.length

theorem trialCount_eq : trialCount = 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length := by
  rw [trialCount, left_count, right_count]
  omega

def trial (start : Nat) : Straight 884736 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

def program : Straight 884736 0 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) :=
  castFinish (by rw [trialCount_eq]; omega) (trial 0)

end
end


section
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 261 := by
  rw [positions_length]
  simp [leftMetadata, List.replicate]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 208 := by
  rw [positions_length]
  simp [rightMetadata, List.replicate]

def trialPositions : TrialPositions SinAverage261.params261 where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, SinAverage261.params261] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata (131071 + 4 * impl.records16 + 12 * impl.records15 + 261)).toArray, by
    simpa only [List.size_toArray, SinAverage261.params261] using right_positions_length (131071 + 4 * impl.records16 + 12 * impl.records15 + 261)⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 131071 + 4 * impl.records16 + 12 * impl.records15 + 261 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    (131071 + 4 * impl.records16 + 12 * impl.records15 + 261) ≤ i ∧ i < 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 := by
  have h := positions_bounds rightMetadata (131071 + 4 * impl.records16 + 12 * impl.records15 + 261) i
    (show i ∈ positions rightMetadata (131071 + 4 * impl.records16 + 12 * impl.records15 + 261) from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

def finePositions : List (Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length)) :=
  trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(right_position_bound i.val i.property).2.trans_le (by omega)⟩

theorem finePositions_length : finePositions.length = 208 := by
  simp [finePositions, SinAverage261.params261]

def fineBits : Vector (Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length)) 208 :=
  Vector.ofFn fun i=> finePositions[i.val]'(by rw [finePositions_length]; exact i.isLt)

def readout : Straight 884736 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length)
    (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946) :=
  castFinish (by omega) (Readout56.suffix56 884736
    (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits)

def fullProgram : Straight 884736 0 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946) :=
  program.append readout

def positionsFor (ps : Vector Nat 208) : TrialPositions SinAverage261.params261 where
  left := trialPositions.left
  right := ps

def layout : DecodeLayout := ⟨.wrappedShift, SinAverage261.params261,
  (Readout56.rightWords56 fineBits).map positionsFor, by
    simp only [List.length_map, Readout56.rightWords56_length]; decide⟩

theorem readout_wellFormed : readout.WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact Readout56.suffix56_wellFormed 884736 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits

theorem readout_t (read : ConstantBit 884736 → Bool)
    (h : Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) → Bool) :
    (readout.instantiate read h).tCount = 0 := by
  unfold readout
  rw [castFinish_instantiate]
  exact Readout56.suffix56_t 884736 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits read h

end
end

end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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
      idealEventMass Q root 261 208 accept := by
  have hm := concrete_event_mass Q hQ hn root hs hz 0 Fin.elim0 J hJ accept
  rw [selectedTwoAxes_fixed_filter, concrete_model_left Q hQ hn, concrete_model_right Q hQ hn,
    left_count, left_positions, right_positions] at hm
  simpa only [fineEvent, trialPositions, Vector.toList_mk, List.toList_toArray] using hm

theorem program_run_data (read : ConstantBit 884736 → Bool) :
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
      idealEventMass Q initialRoot 261 208 accept := by
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
        (fun b => fineEvent (SinAverage261.pairRecovered261 d) b.history)) (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by
    rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [program_event_mass Q hn hQ, idealEventMass_distribution Q d hd]
  exact SinAverage261.pair_success261 Q d hn hd

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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

theorem program_clean (read : ConstantBit 884736 → Bool) (b : InstrumentBranch)
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

theorem verified_of_reads (ps : Vector Nat 208) (hps : ps∈Readout56.rightWords56 fineBits)
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist trialPositions.left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d : ZMod order)∈fixedCandidates SinAverage261.params261 a b) :
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
    (read : ConstantBit 884736→Bool) (history : Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length)→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : fineEvent (SinAverage261.pairRecovered261 d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈(readout.instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate layout Q (List.ofFn history++b.history)).isSome := by
  have hr:=NeighborReadout.input_read fineBits history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩:=Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩:=of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩:=Readout56.suffix56_reads 884736 (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) fineBits
    read history ψ hψ b (by simpa only [readout, castFinish_instantiate] using hb) hn ((i.val : ℤ)-28) (by have h:=i.isLt;omega)
  apply verified_of_reads ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h:=left_position_bound j hj
    simpa only [List.length_ofFn] using h.trans (by omega : (131071 + 4 * impl.records16 + 12 * impl.records15 + 261)<(131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length))

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
    have hlen : a.history.length = (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) := by
      have h := straight_history_length program (readConstant coefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant coefficientAt Q)
      (Single.historyAfter (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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

def triPrograms (n14 : ModNarrow body 13) (n15 : ModNarrow body 14) (n16 : ModNarrow body 15) :
    Programs body where
  records14 := n14.records
  records15 := n15.records
  records16 := n16.records
  cost14 := n14.tBound
  cost15 := n15.tBound
  cost16 := n16.tBound
  program := fun w start =>
    if h14 : w.width = 14 then
      castFinish (by simp [count,h14]) (reindexStraight (paddedRow w) (n14.program start))
    else if h15 : w.width = 15 then
      castFinish (by simp [count,h15]) (reindexStraight (paddedRow w) (n15.program start))
    else castFinish (by simp [count,h14,h15]) (reindexStraight (paddedRow w) (n16.program start))
  coherent := by
    intro Q hQ hn w start history
    have htable : ∀ a, constantPoint Q (windowCoefficients w a) ≠ 0 := by
      intro a
      have he := window_table_point Q hQ w a.val
      simp only [Nat.mod_eq_of_lt a.isLt, Fin.eta] at he
      rw [he]
      exact positivePoint_ne_zero Q hQ hn w _ (Nat.mod_lt _ (pow_pos (by decide) _))
    by_cases h14 : w.width = 14
    · have ha : ModAliased 13 (windowCoefficients w) := by
        simpa only [h14, Nat.reduceSub] using coefficients_aliased w
      have h := n14.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_pos h14, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
    by_cases h15 : w.width = 15
    · have ha : ModAliased 14 (windowCoefficients w) := by
        simpa only [h15, Nat.reduceSub] using coefficients_aliased w
      have h := n15.coherent (windowCoefficients w) Q hQ htable ha start history
      rw [dif_neg h14, dif_pos h15, castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
      obtain ⟨cs, hc, hm⟩ := h
      exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
    have h16 : w.width = 16 := ((width_cases w).resolve_left h14).resolve_left h15
    have ha : ModAliased 15 (windowCoefficients w) := by
      simpa only [h16, Nat.reduceSub] using coefficients_aliased w
    have h := n16.coherent (windowCoefficients w) Q hQ htable ha start history
    rw [dif_neg h14, dif_neg h15, castFinish_instantiate, reindexStraight_instantiate,
      readConstant_reindex (paddedRow w) (windowCoefficients w) coefficientAt Q (fun _ => rfl)]
    obtain ⟨cs, hc, hm⟩ := h
    exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s hs.1), hm⟩
  wellFormed := by
    intro w start
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n14.wellFormed start)
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, castFinish_wellFormed]
      exact (reindexStraight_wellFormed _ _).mpr (n15.wellFormed start)
    rw [dif_neg h14, dif_neg h15, castFinish_wellFormed]
    exact (reindexStraight_wellFormed _ _).mpr (n16.wellFormed start)
  slots := by
    intro w start
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n14.slots start
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, castFinish_gateSlots, reindexStraight_gateSlots]
      exact n15.slots start
    rw [dif_neg h14, dif_neg h15, castFinish_gateSlots, reindexStraight_gateSlots]
    exact n16.slots start
  wires := by
    intro w start
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, straightWires_castFinish, straightWires_reindex]
      exact n14.wires start
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, straightWires_castFinish, straightWires_reindex]
      exact n15.wires start
    rw [dif_neg h14, dif_neg h15, straightWires_castFinish, straightWires_reindex]
    exact n16.wires start
  tCount := by
    intro Q w start history
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h14, if_true] using n14.tCount start _ history
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, castFinish_instantiate, reindexStraight_instantiate]
      simpa only [count, h14, h15, if_true, if_false] using n15.tCount start _ history
    rw [dif_neg h14, dif_neg h15, castFinish_instantiate, reindexStraight_instantiate]
    simpa only [count, h14, h15, if_false] using n16.tCount start _ history

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ScheduleFirst17.program resetProgram leftWindows rightWindows resetBody

def leftCosts (cost16 cost15 : Nat) : List (Nat × Nat) :=
  (917497, 17) :: List.replicate 4 (cost16, 16) ++ List.replicate 12 (cost15, 15)
def rightCosts (cost16 : Nat) : List (Nat × Nat) :=
  List.replicate 13 (cost16, 16)

omit body impl ledger in
theorem left_t_budget (cost16 cost15 : Nat) :
    Single.metadataT (leftCosts cost16 cost15) 0 =
      917497 + 4 * cost16 + 12 * cost15 + 33930 := by
  simp [leftCosts, List.replicate, Single.metadataT, fourierSlots]
  omega

omit body impl ledger in
theorem right_t_budget (cost16 : Nat) :
    Single.metadataT (rightCosts cost16) 0 = 13 * cost16 + 21528 := by
  simp [rightCosts, List.replicate, Single.metadataT, fourierSlots]
  omega

omit body impl ledger in
theorem firstWindow_wellFormed (start : Nat) : (firstWindow.program start).WellFormed := by
  exact ScheduleFirst17.window_wellFormed firstRow start

omit body impl ledger in
theorem firstWindow_slots (start : Nat) : (firstWindow.program start).gateSlots ≤ 3000000000 := by
  exact (ScheduleFirst17.window_slots firstRow start).trans (by norm_num)

omit body impl ledger in
theorem firstWindow_t_uniform (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 917497 := by
  exact ScheduleFirst17.window_t coefficientAt firstRow Q start history

omit impl ledger in
theorem resetBody_wellFormed (start : Nat) : (resetBody start).WellFormed := by
  unfold resetBody
  exact resetProgram_wellFormed _ _ _
omit impl ledger in
theorem resetBody_slots (start : Nat) : (resetBody start).gateSlots = 0 := by
  unfold resetBody
  rw [resetProgram_gateSlots]
omit impl ledger in
theorem resetBody_t (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).tCount = 0 := by
  unfold resetBody
  rw [resetProgram_t]

omit ledger in
theorem signedWindow_wires (w : Digit) : (signedWindow w).wires = (bank w.width).reverse := rfl

omit ledger in
theorem signedWindow_t (Q : Point) (w : Digit) (start : Nat) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      count impl.cost14 impl.cost15 impl.cost16 w := impl.tCount Q w start history

omit ledger in
theorem signedWindow_wellFormed (w : Digit) (start : Nat) :
    ((signedWindow w).program start).WellFormed := impl.wellFormed w start

omit ledger in
theorem signedWindow_slots (w : Digit) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ body.slotBound := impl.slots w start

omit ledger in
theorem windows_cases (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows) :
    w = firstWindow ∨ ∃ s, w = signedWindow s := by
  simp only [leftWindows, rightWindows, List.mem_append, List.mem_cons, List.mem_map] at hw
  rcases hw with (h | ⟨s, _, h⟩) | ⟨s, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h.symm⟩
  · exact Or.inr ⟨s, h.symm⟩

omit ledger in
theorem windows_wellFormed (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).WellFormed := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_wellFormed start
  · exact signedWindow_wellFormed s start

def windowSlots : Nat := max 3000000000 body.slotBound

omit ledger in
theorem windows_slots (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
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
    metadataSlots windowSlots rightMetadata 0 + 2 = 30 * windowSlots + 55929 := by
  simp [leftMetadata, rightMetadata, metadataSlots, List.replicate, fourierSlots]
  omega

theorem trial_slots (start : Nat) : (trial start).gateSlots ≤ 32 * windowSlots + 55929 := by
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

theorem program_slots : program.gateSlots ≤ 32 * windowSlots + 55929 := by
  unfold program
  rw [castFinish_gateSlots]
  exact trial_slots 0


omit ledger in
theorem signed_costs (Q : Point) (ws : List Digit) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      (ws.map signedWindow) (ws.map (fun w => (count impl.cost14 impl.cost15 impl.cost16 w, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => signedWindow_t Q w start h⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

omit ledger in
theorem left_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      leftWindows (leftCosts impl.cost16 impl.cost15) := by
  have he : leftCosts impl.cost16 impl.cost15 =
      (917497, 17) :: leftDigits.map (fun w => (count impl.cost14 impl.cost15 impl.cost16 w, w.width)) := by
    simp [leftCosts, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  unfold leftWindows
  refine .cons ⟨?_, fun start h => (firstWindow_t_uniform Q start h).le⟩ (signed_costs Q leftDigits)
  simp only [firstWindow, ScheduleFirst17.windowGeneric, List.length_reverse]
  decide

omit ledger in
theorem right_costs (Q : Point) :
    List.Forall₂ (fun w c => w.wires.length = c.2 ∧ ∀ start h,
      ((w.program start).instantiate (readConstant coefficientAt Q) h).tCount ≤ c.1)
      rightWindows (rightCosts impl.cost16) := by
  have he : rightCosts impl.cost16 =
      rightDigits.map (fun w => (count impl.cost14 impl.cost15 impl.cost16 w, w.width)) := by
    simp [rightCosts, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
  rw [he]
  simpa only [rightWindows] using signed_costs Q rightDigits

theorem left_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      917497 + 4 * impl.cost16 + 12 * impl.cost15 + 33930 := by
  have h := axis_t leftWindows (readConstant coefficientAt Q) (leftCosts impl.cost16 impl.cost15)
    (left_costs Q) start List.nil history
  have hm := left_t_budget impl.cost16 impl.cost15
  simp only [List.length_nil, hm] at h
  omega

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant coefficientAt Q) history).tCount ≤
      13 * impl.cost16 + 21528 := by
  have h := axis_t rightWindows (readConstant coefficientAt Q) (rightCosts impl.cost16)
    (right_costs Q) start List.nil history
  have hm := right_t_budget impl.cost16
  simp only [List.length_nil, hm] at h
  omega

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 := by
  unfold trial
  apply (framed_t_le _ _ _ _ _ history (917497 + 4 * impl.cost16 + 12 * impl.cost15 + 33930)
    (13 * impl.cost16 + 21528) (left_axis_t Q start history)
    (fun h => right_axis_t Q _ h) (fun h => resetBody_t _ _ h)).trans
  omega

theorem program_t (Q : Point) :
    (program.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ScheduleFirst17.program resetProgram leftWindows rightWindows resetBody

class SupportCover (body : Single.WindowBody) (ledger : Single.ProducerResources body) : Prop where
  covers : body.support ⊆ ledger.support

variable [cover : SupportCover body ledger]

omit impl cover in
theorem stream_support : streamAddress ⊆ ledger.support := by
  intro v hv
  exact ledger.initial_support (List.mem_append_right _ hv)

omit cover in
theorem windows_bank_support (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows) :
    w.wires ⊆ ledger.support := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · intro v hv
    apply ledger.initial_support
    have hbits : ScheduleFirst17.bits ⊆ resetWires := by decide +kernel
    exact hbits (List.mem_reverse.mp hv)
  · rw [signedWindow_wires]
    intro v hv
    exact stream_support (bank_subset s.width (width_cases s) v (List.mem_reverse.mp hv))

theorem windows_support (w : Single.Window 884736) (hw : w ∈ leftWindows ++ rightWindows)
    (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ ledger.support := by
  apply (straight_instantiate_support _ read history).trans
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact (ScheduleFirst17.window_support firstRow start).trans ledger.initial_support
  · exact (impl.wires s start).trans cover.covers

omit impl cover in
private theorem flag_support : (836 : Wire) ∈ ledger.support := by
  apply ledger.initial_support
  simp [resetWires]

omit impl cover in
theorem resetBody_support (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).wires ⊆ ledger.support := by
  unfold resetBody
  exact resetProgram_support _ _ _ _ read history ledger.reset_support

theorem left_axis_support (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support leftWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_left _ hw))
    (fun w hw => windows_support w (List.mem_append_left _ hw)) start List.nil read history

theorem right_axis_support (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate read history).wires ⊆ ledger.support :=
  axis_support rightWindows ledger.support
    (fun w hw => windows_bank_support w (List.mem_append_right _ hw))
    (fun w hw => windows_support w (List.mem_append_right _ hw)) start List.nil read history

theorem trial_support (start : Nat) (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    ((trial start).instantiate read history).wires ⊆ ledger.support := by
  unfold trial
  exact framed_support _ _ _ _ read history ledger.support flag_support
    (left_axis_support start read history) (fun h => right_axis_support _ read h)
    (fun h => resetBody_support _ read h)

theorem program_support (read : ConstantBit 884736 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ ledger.support := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_support 0 read Fin.elim0

omit cover in
theorem readout_support (read : ConstantBit 884736 → Bool)
    (h : Fin (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) → Bool) :
    (readout.instantiate read h).wires ⊆ ledger.support := by
  unfold readout
  rw [castFinish_instantiate]
  apply (Readout56.suffix56_support 884736
    (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits read h).trans
  have hs : [0,1] ⊆ resetWires := by simp [List.subset_def, resetWires]
  exact hs.trans ledger.initial_support

theorem fullProgram_support (read : ConstantBit 884736 → Bool) :
    (fullProgram.instantiate read Fin.elim0).wires ⊆ ledger.support :=
  outer_append_support _ _ read Fin.elim0 ledger.support (program_support read) (readout_support read)

theorem fullProgram_qubits (read : ConstantBit 884736 → Bool) :
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
      917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 := by
  have h := outer_append_t_le program readout (readConstant coefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  change ((program.append readout).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤ _
  exact h.trans (by simpa only [Nat.add_zero] using program_t Q)

omit cover in
theorem fullProgram_wellFormed : fullProgram.WellFormed :=
  straight_append_wellFormed _ _ program_wellFormed readout_wellFormed

omit cover in
theorem fullProgram_slots : fullProgram.gateSlots ≤ 32 * windowSlots + 178240 := by
  unfold fullProgram
  rw [Straight.gateSlots_append]
  have hr : readout.gateSlots = 122311 := by
    unfold readout
    rw [castFinish_gateSlots]
    exact Readout56.suffix56_slots 884736
      (131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length) 208 fineBits
  rw [hr]
  have h := program_slots
  omega


def entry : StraightEntry := Single.fixedEntry coefficientAt fullProgram

def bounds : Bounds := ⟨ledger.support.length, 917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458,
  131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946⟩

theorem certificate
    (hSlots : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots)
    (hRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946 ≤ officialLimits.measurements) :
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
    change 56 * (2*(order/2^208+2)) ≤ 56*(2^49+2)
    exact SinAverage261.decoder_budget261
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
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [impl : Programs body] [ledger : Single.ProducerResources body]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] leftWindows rightWindows program fullProgram readout entry Single.axis ScheduleFirst17.program

omit body impl ledger in
theorem first_count (start : Nat) : AtLeast (firstWindow.program start) 131071 := by
  have h := ScheduleFirst17.window_credit coefficientAt firstRow 0 start (fun _ => false)
  exact h.ge

structure ProgramCredit (c14 c15 c16 : Nat) : Prop where
  zero : ∀ w start, residue (impl.program w start) = 0
  count_eq : ∀ w start, added (impl.program w start) = count c14 c15 c16 w

variable {c14 c15 c16 : Nat} (hc : ProgramCredit c14 c15 c16)
include hc

omit ledger in
theorem signed_credit (w : Digit) (start : Nat) :
    AtLeast ((signedWindow w).program start) (count c14 c15 c16 w) := by
  simpa only [signedWindow, AtLeast] using (hc.count_eq w start).ge

def leftCounted : List (CountedWindow 884736) :=
  ⟨firstWindow, 131071, first_count⟩ :: leftDigits.map
    (fun w => ⟨signedWindow w, count c14 c15 c16 w, signed_credit hc w⟩)

def rightCounted : List (CountedWindow 884736) :=
  rightDigits.map (fun w => ⟨signedWindow w, count c14 c15 c16 w, signed_credit hc w⟩)

theorem parent_credit : AtLeast entry.program (131071 + 17 * c16 + 12 * c15) := by
  have hl := counted_axis (leftCounted hc) 0 List.nil
  have hr := counted_axis (rightCounted hc) (0 + Single.axisCount leftWindows) List.nil
  have hls : (leftCounted hc).map CountedWindow.source = leftWindows := by
    simp [leftCounted, leftWindows]
  have hrs : (rightCounted hc).map CountedWindow.source = rightWindows := by
    simp [rightCounted, rightWindows]
  have hln : ((leftCounted hc).map CountedWindow.saving).sum = 131071 + 4 * c16 + 12 * c15 := by
    simp [leftCounted, leftDigits, List.ofFn_succ, Digit.width, count]
    omega
  have hrn : ((rightCounted hc).map CountedWindow.saving).sum = 13 * c16 := by
    simp [rightCounted, rightDigits, List.ofFn_succ, Digit.width, count]
    omega
  rw [hls, hln] at hl
  rw [hrs, hrn] at hr
  have ht : AtLeast (trial 0) (131071 + 17 * c16 + 12 * c15) := by
    unfold trial
    exact (framed_credit _ _ _ _ hl hr).castCount (by omega)
  have hp : AtLeast program (131071 + 17 * c16 + 12 * c15) := by
    unfold program
    exact ht.castFinish _
  unfold entry fullProgram
  apply fixedEntry_credit
  exact (hp.append (AtLeast.zero _)).castCount (by omega)

omit ledger in
theorem signed_t (w : Digit) (start : Nat)
    (read : ConstantBit 884736 → Bool) (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate read history).tCount =
      7 * count c14 c15 c16 w := by
  unfold signedWindow
  rw [exact_t _ (hc.zero w start), hc.count_eq w start]

def creditLeftCosts : List (Nat × Nat) := leftCosts (7*c16) (7*c15)
def creditRightCosts : List (Nat × Nat) := rightCosts (7*c16)

omit ledger in
theorem signed_costs_credit (ws : List Digit) (read : ConstantBit 884736 → Bool) :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1)
      (ws.map signedWindow) (ws.map (fun w => (7 * count c14 c15 c16 w, w.width))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨?_, fun start h => (signed_t hc w start read h).le⟩ ih
    rw [signedWindow_wires, List.length_reverse, bank_length _ (width_cases w)]

theorem producer_t (Q : Point) :
    (fullProgram.instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      7 * (131071 + 17 * c16 + 12 * c15) + 55458 := by
  let read := readConstant coefficientAt Q
  have lc : List.Forall₂ (fun w k => w.wires.length = k.2 ∧ ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ k.1) leftWindows
      (creditLeftCosts (c15 := c15) (c16 := c16)) := by
    have he : creditLeftCosts (c15 := c15) (c16 := c16) =
        (917497,17) :: leftDigits.map (fun w => (7 * count c14 c15 c16 w, w.width)) := by
      simp [creditLeftCosts, leftCosts, leftDigits, List.ofFn_succ, Digit.width, count, List.replicate]
    rw [he]
    unfold leftWindows
    refine .cons ⟨?_, fun start h => (firstWindow_t_uniform Q start h).le⟩
      (signed_costs_credit hc leftDigits read)
    simp only [firstWindow, ScheduleFirst17.windowGeneric, List.length_reverse]
    decide
  have hl := Single.axis_t leftWindows read _ lc 0 List.nil Fin.elim0
  have hr : ∀ h, ((Single.axis rightWindows
      (0 + Single.axisCount leftWindows) List.nil).instantiate read h).tCount ≤
      Single.metadataT (creditRightCosts (c16 := c16)) 0 := by
    intro h
    apply Single.axis_t rightWindows read _ _ _ List.nil h
    have he : creditRightCosts (c16 := c16) =
        rightDigits.map (fun w => (7 * count c14 c15 c16 w, w.width)) := by
      simp [creditRightCosts, rightCosts, rightDigits, List.ofFn_succ, Digit.width, count, List.replicate]
    rw [he]
    simpa only [rightWindows] using signed_costs_credit hc rightDigits read
  have hln : Single.metadataT (creditLeftCosts (c15 := c15) (c16 := c16)) 0 =
      917497 + 4 * (7*c16) + 12 * (7*c15) + 33930 := left_t_budget _ _
  have hrn : Single.metadataT (creditRightCosts (c16 := c16)) 0 =
      13 * (7*c16) + 21528 := right_t_budget _
  have ht := Single.framed_t_le (Single.axis leftWindows 0 List.nil)
    (Single.axis rightWindows (0 + Single.axisCount leftWindows) List.nil)
    (resetBody (0 + Single.axisCount leftWindows + Single.axisCount rightWindows))
    (show 0 + Single.axisCount leftWindows + Single.axisCount rightWindows +
      body.reset.length = 0 + trialCount from by unfold trialCount; omega)
    read Fin.elim0 _ _ hl hr (resetBody_t _ read)
  have hp : (program.instantiate read Fin.elim0).tCount ≤
      Single.metadataT (creditLeftCosts (c15 := c15) (c16 := c16)) 0 +
        Single.metadataT (creditRightCosts (c16 := c16)) 0 := by
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
    (hBaseSlots : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots)
    (hBaseRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 +
      body.reset.length + 34946 ≤ officialLimits.measurements)
    (hq : q ∉ ledger.support) (hy : y ∉ q :: ledger.support)
    (hslots : entry.program.gateSlots + 21 * added entry.program +
      3 * Catalyst.saved entry.program + 2 ≤ officialLimits.gateSlots)
    (hrecords : entry.finalCursor + added entry.program ≤ officialLimits.measurements) :
    Certificate officialLimits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ledger.support (131071 + 17 * c16 + 12 * c15) 55458) := by
  have base := certificate hBaseSlots hBaseRecords
  have source : Certificate officialLimits layout entry
      ⟨ledger.support.length, 7 * (131071 + 17 * c16 + 12 * c15) + 55458, entry.finalCursor⟩ :=
    { base with
      resources := by
        intro Q
        refine ⟨(base.resources Q).1, ?_, ?_⟩
        change (entry.instantiate Q).tCount ≤ _
        rw [entry, Single.fixedEntry_instantiate]
        · exact producer_t hc Q
        · simpa only [bounds, entry, Single.fixedEntry] using (base.resources Q).2.2 }
  exact WEXCredit.four_certificate officialLimits layout entry ledger.support
    (131071 + 17 * c16 + 12 * c15) 55458 q y source compiler_within hq hy
    (parent_credit hc) hslots hrecords

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
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
    131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length + 34946 := by
  unfold entry
  rw [Single.fixedEntry_cursor]

omit cover in
theorem source_slots : entry.program.gateSlots ≤ 32 * windowSlots + 178240 := by
  unfold entry
  rw [Single.fixedEntry_slots]
  exact fullProgram_slots

theorem source_counts (q y : Wire) (sourceBound : Nat)
    (hBaseSlots : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots)
    (hBaseRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 +
      body.reset.length + 34946 ≤ officialLimits.measurements)
    (hSource : 917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 ≤ sourceBound) :
    added entry.program ≤ sourceBound ∧ Catalyst.saved entry.program ≤ sourceBound := by
  have h := four_identity q y entry.program (readConstant entry.coefficients.get 0) Fin.elim0
  have ht := ((certificate hBaseSlots hBaseRecords).resources 0).2.1
  change (entry.program.instantiate (readConstant entry.coefficients.get 0) Fin.elim0).tCount ≤
    917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 at ht
  omega

theorem bounded_four_certificate {c14 c15 c16 : Nat} (hc : ProgramCredit c14 c15 c16)
    (q y : Wire) (sourceBound : Nat)
    (hBaseSlots : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots)
    (hBaseRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 +
      body.reset.length + 34946 ≤ officialLimits.measurements)
    (hSource : 917497 + 17 * impl.cost16 + 12 * impl.cost15 + 55458 ≤ sourceBound)
    (hSlots : 32 * windowSlots + 178240 + 24 * sourceBound + 2 ≤ officialLimits.gateSlots)
    (hRecords : 131071 + 17 * impl.records16 + 12 * impl.records15 + 469 + body.reset.length +
      34946 + sourceBound ≤ officialLimits.measurements)
    (hq : q ∉ ledger.support) (hy : y ∉ q :: ledger.support) :
    Certificate officialLimits (lowerLayout q entry layout) (fourEntry q y entry)
      (fourBounds entry ledger.support (131071 + 17 * c16 + 12 * c15) 55458) := by
  have hc' := source_counts q y sourceBound hBaseSlots hBaseRecords hSource
  have hs := source_slots
  have hm := source_cursor
  apply four_certificate hc q y hBaseSlots hBaseRecords hq hy
  · omega
  · omega

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem triProgramCredit (n14 : ModNarrow body 13) (n15 : ModNarrow body 14)
    (n16 : ModNarrow body 15) :
    @ProgramCredit body (triPrograms n14 n15 n16) n14.credit n15.credit n16.credit := by
  refine @ProgramCredit.mk body (triPrograms n14 n15 n16) n14.credit n15.credit n16.credit ?_ ?_
  · intro w start
    change residue (if h14 : w.width = 14 then castFinish _ (reindexStraight (paddedRow w) (n14.program start))
      else if h15 : w.width = 15 then castFinish _ (reindexStraight (paddedRow w) (n15.program start))
      else castFinish _ (reindexStraight (paddedRow w) (n16.program start))) = 0
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, residue_cast, residue_reindex]
      exact n14.zero start
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, residue_cast, residue_reindex]
      exact n15.zero start
    rw [dif_neg h14, dif_neg h15, residue_cast, residue_reindex]
    exact n16.zero start
  · intro w start
    change added (if h14 : w.width = 14 then castFinish _ (reindexStraight (paddedRow w) (n14.program start))
      else if h15 : w.width = 15 then castFinish _ (reindexStraight (paddedRow w) (n15.program start))
      else castFinish _ (reindexStraight (paddedRow w) (n16.program start))) =
        count n14.credit n15.credit n16.credit w
    by_cases h14 : w.width = 14
    · rw [dif_pos h14, added_cast, added_reindex, n14.count_eq start]
      simp [count,h14]
    by_cases h15 : w.width = 15
    · rw [dif_neg h14, dif_pos h15, added_cast, added_reindex, n15.count_eq start]
      simp [count,h15]
    rw [dif_neg h14, dif_neg h15, added_cast, added_reindex, n16.count_eq start]
    simp [count,h14,h15]

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
end


namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body] [cover : SupportCover body ledger]
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

omit body ledger cover in
private theorem fusedClearWiden {limits : Limits} {layout : DecodeLayout} {entry : StraightEntry}
    {old new : Bounds} (cert : Certificate limits layout entry old)
    (hq : old.qubits ≤ new.qubits) (ht : old.tModel ≤ new.tModel)
    (hm : old.measurements ≤ new.measurements) : Certificate limits layout entry new :=
  { cert with resources := fun Q =>
      ⟨(cert.resources Q).1.trans hq, (cert.resources Q).2.1.trans ht, (cert.resources Q).2.2.trans hm⟩ }

theorem matched_fused_certificate (n14 : ModNarrow body 13) (n15 : ModNarrow body 14)
    (n16 : ModNarrow body 15)
    (hSupport : ledger.support.length ≤ 1634) (hSlot : body.slotBound ≤ 3000000000)
    (hR15 : n15.records ≤ 1643673) (hR16 : n16.records ≤ 1726361)
    (hReset : body.reset.length ≤ 854)
    (hT15 : n15.tBound ≤ 15734936) (hT16 : n16.tBound ≤ 16313752)
    (hC15 : n15.credit ≤ 2247848) (hC16 : n16.credit ≤ 2330536)
    (hq : (1938 : Wire) ∉ ledger.support) (hy : (1939 : Wire) ∉ 1938 :: ledger.support) :
    letI : Programs body := triPrograms n14 n15 n16
    Certificate officialLimits (lowerLayout 1938 entry layout) (fourEntry 1938 1939 entry)
      ⟨1636, 266952895, 543906879⟩ := by
  letI : Programs body := triPrograms n14 n15 n16
  have hwin : windowSlots ≤ 3000000000 := max_le le_rfl hSlot
  have hbaseS : 32 * windowSlots + 178240 ≤ officialLimits.gateSlots := by
    change 32 * windowSlots + 178240 ≤ 4000000000000000
    omega
  have hbaseR : 131071 + 17 * (triPrograms n14 n15 n16).records16 + 12 * (triPrograms n14 n15 n16).records15 +
      469 + body.reset.length + 34946 ≤ officialLimits.measurements := by
    change 131071 + 17 * n16.records + 12 * n15.records + 469 + body.reset.length + 34946 ≤ 47471340504
    omega
  have hsrc : 917497 + 17 * (triPrograms n14 n15 n16).cost16 + 12 * (triPrograms n14 n15 n16).cost15 +
      55458 ≤ 491238726 := by
    change 917497 + 17 * n16.tBound + 12 * n15.tBound + 55458 ≤ 491238726
    omega
  have hslots : 32 * windowSlots + 178240 + 24 * 491238726 + 2 ≤ officialLimits.gateSlots := by
    change 32 * windowSlots + 178240 + 24 * 491238726 + 2 ≤ 4000000000000000
    omega
  have hrecords : 131071 + 17 * (triPrograms n14 n15 n16).records16 + 12 * (triPrograms n14 n15 n16).records15 +
      469 + body.reset.length + 34946 + 491238726 ≤ officialLimits.measurements := by
    change 131071 + 17 * n16.records + 12 * n15.records + 469 + body.reset.length + 34946 +
      491238726 ≤ 47471340504
    omega
  have raw := bounded_four_certificate (triProgramCredit n14 n15 n16) 1938 1939 491238726
    hbaseS hbaseR hsrc hslots hrecords hq hy
  have hcounts := (source_counts 1938 1939 491238726 hbaseS hbaseR hsrc).1
  have hcursor : entry.finalCursor ≤ 52668153 := by
    rw [source_cursor]
    change 131071 + 17 * n16.records + 12 * n15.records + 469 + body.reset.length + 34946 ≤ 52668153
    omega
  apply fusedClearWiden raw
  · change ledger.support.length + 2 ≤ 1636
    omega
  · change 4 * (131071 + 17 * n16.credit + 12 * n15.credit) + 55458 + 1 ≤ 266952895
    omega
  · change entry.finalCursor + added entry.program ≤ 543906879
    omega
end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible

namespace ShorECDLP.Entrant.Schedule29Seventeen244.Flexible.FusedFinal
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge AndGadget WEXCredit
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Entrant.Single ShorECDLP.Entrant.Single.Distribution
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] WEXUnlookupWidth13.compactProgram WEXUnlookupWidth14.compactProgram WEXUnlookup.Width15Corner.fastCompactProgram WEXUnlookupWidth14.Corner.fastCompactProgram
  WEXUnlookupWidth13.bodyProgram WEXUnlookupWidth14.bodyProgram
  WEXUnlookupWidth13.ccx WEXUnlookupWidth14.ccx
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount
  WEX.literalToffolis WEX.normalizeW Nat.add Nat.mul AndGadget.added

def narrow13 : ModNarrow WEXUnlookup.compactBody 13 := WEXUnlookupWidth13.fastNarrow
def narrow14 : ModNarrow WEXUnlookup.compactBody 14 := WEXUnlookupWidth14.Corner.fastNarrow
def narrow15 : ModNarrow WEXUnlookup.compactBody 15 := WEXUnlookup.Width15Corner.fastNarrow

theorem n14_records : narrow14.records ≤ 1643673 := by
  exact le_rfl
theorem n15_records : narrow15.records ≤ 1726361 := by
  exact le_rfl
theorem n14_cost : narrow14.tBound ≤ 15734936 := by
  exact le_rfl
theorem n15_cost : narrow15.tBound ≤ 16313752 := by
  exact le_rfl

attribute [local irreducible] narrow13 narrow14 narrow15
local instance bodyInstance : Single.WindowBody := WEXUnlookup.compactBody
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEXUnlookup.compactBody
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
local instance programInstance : Programs bodyInstance := triPrograms narrow13 narrow14 narrow15

private theorem count14_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 15734936) :
    c ≤ 2247848 := by omega
private theorem count15_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 16313752) :
    c ≤ 2330536 := by omega

theorem n14_credit : narrow14.credit ≤ 2247848 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow14.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow14.program 0) (narrow14.zero 0) read Fin.elim0
  have hc := narrow14.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count14_bound _ _ he' (ht.trans n14_cost)
theorem n15_credit : narrow15.credit ≤ 2330536 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow15.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow15.program 0) (narrow15.zero 0) read Fin.elim0
  have hc := narrow15.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count15_bound _ _ he' (ht.trans n15_cost)

def entry : StraightEntry := fourEntry 1938 1939 Flexible.entry
def layout : DecodeLayout := lowerLayout 1938 Flexible.entry Flexible.layout
def bounds : Bounds := ⟨1636, 266952895, 543906879⟩

theorem certificate : Certificate officialLimits layout entry bounds := by
  apply @matched_fused_certificate bodyInstance resourcesInstance coverInstance narrow13 narrow14 narrow15
  · change WEXUnlookup.compactSupport.length ≤ 1634
    norm_num [WEXUnlookup.compactSupport,MeasuredClear.hotBank]
  · rw [bodyInstance, WEXUnlookup.compactBody]
    decide +kernel
  · exact n14_records.trans (by norm_num)
  · exact n15_records.trans (by norm_num)
  · change WEXUnlookup.compactBody.reset.length ≤ 854
    exact WEXUnlookup.compactBody_ledger.2.2.2.le
  · exact n14_cost.trans (by norm_num)
  · exact n15_cost.trans (by norm_num)
  · exact n14_credit
  · exact n15_credit
  · change (1938 : Wire) ∉ WEXUnlookup.compactSupport
    decide +kernel
  · change (1939 : Wire) ∉ 1938 :: WEXUnlookup.compactSupport
    decide +kernel
end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible.FusedFinal


-- ===== entry exports =====

namespace ShorECDLP.Entrant
open Challenge

def bounds : Bounds := ⟨1636,266952895,543906879⟩
noncomputable section
def entry : StraightEntry := Schedule29Seventeen244.Flexible.FusedFinal.entry
def layout : DecodeLayout := Schedule29Seventeen244.Flexible.FusedFinal.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Schedule29Seventeen244.Flexible.FusedFinal.certificate
end
end ShorECDLP.Entrant
