import ShorECDLP.Submission.Naive.Challenge.NumericCertificate

/-! EDITABLE. Tight reset support for the Naive round.

The Naive baseline resets every wire of the dense envelope `List.range 206624`
after each round, so its instantiated circuit touches all 206,624 labels. The
concrete arithmetic allocation, however, places three one-wire flag blocks at
full 257-wire strides, so 768 wires of that envelope are never used. This file
proves that every wire of the declared Naive support lies in the smaller list
`tightResetWires` (205,856 wires). -/

namespace ShorECDLP.Entrant
open Quantum Secp256k1 Challenge Arithmetic ShorECDLP.NaiveChallenge

/-- Every wire the Naive trial can touch: the dense prefix below 205854 plus the
two isolated flag wires of the multiplier workspace. -/
def tightResetWires : List Wire := List.range 205854 ++ [206110, 206367]

theorem mem_tightResetWires (w : Nat) :
    w ∈ tightResetWires ↔ w < 205854 ∨ w = 206110 ∨ w = 206367 := by
  simp [tightResetWires, List.mem_range]

theorem tightResetWires_nodup : tightResetWires.Nodup := by
  rw [tightResetWires, List.nodup_append]
  refine ⟨List.nodup_range, by decide, ?_⟩
  intro a ha b hb hab
  have ha' : @LT.lt Nat _ a 205854 := List.mem_range.mp ha
  have hb' : @Eq Nat b 206110 ∨ @Eq Nat b 206367 := by simpa using hb
  have hab' : @Eq Nat a b := hab
  omega

theorem tightResetWires_length : tightResetWires.length = 205856 := by
  simp [tightResetWires]

/-! ## The concrete arithmetic layouts -/

theorem blocksWires_upper (blocks : List Secp256k1Instance.Block) (limit : Nat)
    (hids : ∀ block ∈ blocks, block.id < limit) :
    ∀ w ∈ Secp256k1Instance.blocksWires blocks, w < Secp256k1Instance.fieldWidth * limit := by
  intro w hw
  simp only [Secp256k1Instance.blocksWires, List.mem_flatMap] at hw
  obtain ⟨block, hblock, hwire⟩ := hw
  have hbound := Secp256k1Instance.Block.mem_bounds hwire
  calc
    w < Secp256k1Instance.fieldWidth * (block.id + 1) := hbound.2
    _ ≤ Secp256k1Instance.fieldWidth * limit :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr (hids block hblock))

theorem secpAddLayout_tight :
    ∀ v : Nat, v ∈ Secp256k1Instance.secpAddLayout.allWires → v < 199690 := by
  let blocks :=
    [Secp256k1Instance.regBlock Secp256k1Instance.baseId,
      Secp256k1Instance.regBlock Secp256k1Instance.exponentId,
      Secp256k1Instance.regBlock Secp256k1Instance.outId] ++
      Secp256k1Instance.addScratchBlocks Secp256k1Instance.initialAccId
  have hlayout :
      Secp256k1Instance.secpAddLayout.allWires = Secp256k1Instance.blocksWires blocks := by
    simp [blocks, Secp256k1Instance.secpAddLayout, RegisterLayout.allWires,
      Secp256k1Instance.addWork, Secp256k1Instance.reg, Secp256k1Instance.blocksWires,
      List.append_assoc]
  intro v hv
  rw [hlayout] at hv
  have hupper := blocksWires_upper blocks 10 ?_ v hv
  · simpa [Secp256k1Instance.fieldWidth] using
      hupper.trans_le (by norm_num [Secp256k1Instance.fieldWidth])
  intro block hblock
  simp only [blocks, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hblock
  rcases hblock with (rfl | rfl | rfl) | hblock
  · norm_num [Secp256k1Instance.baseId]
  · norm_num [Secp256k1Instance.exponentId]
  · norm_num [Secp256k1Instance.outId]
  · simp [Secp256k1Instance.addScratchBlocks] at hblock
    rcases hblock with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [Secp256k1Instance.initialAccId]

theorem secpMulLayout_tight :
    ∀ v : Nat, v ∈ Secp256k1Instance.secpMulLayout.allWires → v < 199690 := by
  let blocks :=
    [Secp256k1Instance.regBlock Secp256k1Instance.baseId,
      Secp256k1Instance.regBlock Secp256k1Instance.exponentId,
      Secp256k1Instance.regBlock Secp256k1Instance.outId] ++
      Secp256k1Instance.mulWorkBlocks Secp256k1Instance.initialAccId
        Secp256k1Instance.historyStartId
  have hlayout :
      Secp256k1Instance.secpMulLayout.allWires = Secp256k1Instance.blocksWires blocks := by
    simp only [Secp256k1Instance.secpMulLayout, RegisterLayout.allWires]
    rw [Secp256k1Instance.mulWork_eq_blocksWires]
    simp [blocks, Secp256k1Instance.blocksWires, Secp256k1Instance.reg, List.append_assoc]
  intro v hv
  rw [hlayout] at hv
  have hupper := blocksWires_upper blocks 10 ?_ v hv
  · simpa [Secp256k1Instance.fieldWidth] using
      hupper.trans_le (by norm_num [Secp256k1Instance.fieldWidth])
  intro block hblock
  simp only [blocks, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hblock
  rcases hblock with (rfl | rfl | rfl) | hprivate
  · norm_num [Secp256k1Instance.baseId]
  · norm_num [Secp256k1Instance.exponentId]
  · norm_num [Secp256k1Instance.outId]
  · have hid : block.id ∈
        (Secp256k1Instance.mulWorkBlocks Secp256k1Instance.initialAccId
          Secp256k1Instance.historyStartId).map Secp256k1Instance.Block.id :=
      List.mem_map_of_mem hprivate
    rw [Secp256k1Instance.mulWorkBlocks_ids] at hid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
    norm_num [Secp256k1Instance.initialAccId, Secp256k1Instance.historyStartId] at hid ⊢
    omega

/-- Nat-typed block bounds: a block wire lies in `[257·id, 257·id + size)`. -/
theorem block_mem_bounds (block : Secp256k1Instance.Block) (v : Nat)
    (hv : v ∈ block.wires) : 257 * block.id ≤ v ∧ v < 257 * block.id + block.size := by
  rw [Secp256k1Instance.Block.wires] at hv
  have h := List.mem_range'_1.mp hv
  simpa only [Secp256k1Instance.fieldWidth] using h

/-- The exponentiation layout: full registers below block 777 and three
isolated flag wires at the starts of blocks 777, 778 and 779. -/
theorem secpLayout_tight :
    ∀ v : Nat, v ∈ Secp256k1Instance.secpLayout.allWires →
      v < 199690 ∨ v = 199946 ∨ v = 200203 := by
  intro v hv
  rw [Secp256k1Instance.secpLayout, Secp256k1Instance.secpPlan_allWires] at hv
  simp only [Secp256k1Instance.blocksWires, List.mem_flatMap] at hv
  obtain ⟨block, hblock, hwire⟩ := hv
  have hb := block_mem_bounds block v hwire
  have hsize : block.size ≤ 257 := block.size_le
  have hduplicate : Secp256k1Instance.duplicateId = 774 := by
    unfold Secp256k1Instance.duplicateId
    rw [Secp256k1Instance.historyCount_eq]
    norm_num [Secp256k1Instance.historyStartId]
  have hmulAcc : Secp256k1Instance.mulAccId = 775 := by
    simp [Secp256k1Instance.mulAccId, hduplicate]
  have hmulStart : Secp256k1Instance.mulStartId = 776 := by
    simp [Secp256k1Instance.mulStartId, hmulAcc]
  unfold Secp256k1Instance.secpLayoutBlocks Secp256k1Instance.mulWorkBlocks at hblock
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hblock
  rcases hblock with rfl | rfl | rfl | rfl | hhist | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (simp only [Secp256k1Instance.regBlock, Secp256k1Instance.bitBlock,
         Secp256k1Instance.fieldWidth, Secp256k1Instance.baseId, Secp256k1Instance.exponentId,
         Secp256k1Instance.outId, Secp256k1Instance.initialAccId, hduplicate, hmulAcc,
         hmulStart] at hb
       omega)
    | (have hid := List.mem_map_of_mem (f := Secp256k1Instance.Block.id) hhist
       rw [Secp256k1Instance.historyBlocks_ids, Secp256k1Instance.historyCount_eq,
         List.mem_range'] at hid
       obtain ⟨i, hi, he⟩ := hid
       simp only [Secp256k1Instance.historyStartId] at he
       omega)

/-- The relocated arithmetic engine of one point addition lies in the tight list. -/
theorem pointAddArithmeticWork_tight :
    ∀ w ∈ pointAddArithmeticWork 2052, w ∈ tightResetWires := by
  intro w hw
  have hoffset : pointAddArithmeticOffset 2052 = 6164 := rfl
  simp only [pointAddArithmeticWork, List.mem_dedup, List.mem_append] at hw
  rw [mem_tightResetWires]
  rcases hw with (hadd | hmul) | hexp
  · simp only [shiftWires, List.mem_map] at hadd
    obtain ⟨source, hsource, rfl⟩ := hadd
    have hv := secpAddLayout_tight source hsource
    rw [hoffset]
    omega
  · simp only [shiftWires, List.mem_map] at hmul
    obtain ⟨source, hsource, rfl⟩ := hmul
    have hv := secpMulLayout_tight source hsource
    rw [hoffset]
    omega
  · simp only [shiftWires, List.mem_map] at hexp
    obtain ⟨source, hsource, rfl⟩ := hexp
    have hv := secpLayout_tight source hsource
    rw [hoffset]
    omega

theorem scalarMulWork_tight :
    ∀ w ∈ scalarMulWork bitcoinWorkStart, w ∈ tightResetWires := by
  intro w hw
  change w ∈ List.range' 1026 pointWidth ++ controlledPointAddOutWork 1539 at hw
  rcases List.mem_append.mp hw with htemp | hw
  · have hbound := List.mem_range'_1.mp htemp
    rw [mem_tightResetWires]
    left
    calc
      w < 1026 + pointWidth := hbound.2
      _ < 205854 := by norm_num [pointWidth]
  · change w ∈ List.range' 1539 pointWidth ++ pointAddWork 2052 at hw
    rcases List.mem_append.mp hw with hchoice | hw
    · have hbound := List.mem_range'_1.mp hchoice
      rw [mem_tightResetWires]
      left
      calc
        w < 1539 + pointWidth := hbound.2
        _ < 205854 := by norm_num [pointWidth]
    · change w ∈ List.range' 2052 4112 ++ pointAddArithmeticWork 2052 at hw
      rcases List.mem_append.mp hw with hlocal | harithmetic
      · have hbound := List.mem_range'_1.mp hlocal
        rw [mem_tightResetWires]
        left
        omega
      · exact pointAddArithmeticWork_tight w harithmetic

/-- The declared Naive support lies in the tight reset list. -/
theorem declaredWires_tight :
    ∀ w ∈ bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
      scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla], w ∈ tightResetWires := by
  intro w hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (((ha | hb) | hpoint) | hwork) | hancilla
  · change w ∈ List.range' 0 256 at ha
    have hbound := (List.mem_range'_1.mp ha).2
    rw [mem_tightResetWires]
    omega
  · change w ∈ List.range' 256 256 at hb
    have hbound := (List.mem_range'_1.mp hb).2
    rw [mem_tightResetWires]
    omega
  · change w ∈ List.range' 512 pointWidth at hpoint
    have hbound := (List.mem_range'_1.mp hpoint).2
    rw [mem_tightResetWires]
    left
    calc
      w < 512 + pointWidth := hbound
      _ < 205854 := by norm_num [pointWidth]
  · exact scalarMulWork_tight w hwork
  · subst hancilla
    rw [mem_tightResetWires]
    left
    norm_num [bitcoinQFTAncilla]

/-- Constant rows may denote arbitrary points; the physical wire envelope of the
instantiated round template is independent of the key. -/
theorem trialGates_tight_support (Q : Point) :
    circuitWires (trialGates.flatMap (TemplateGate.instantiate
      (readConstant naivePowerCoefficient Q))) ⊆ tightResetWires := by
  let support := bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
    scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla]
  have hh : CircuitUsesOnly support (PhaseEstimation.hadamards (bitcoinAReg ++ bitcoinBReg)) := by
    apply usesOnly_mono (hadamards_usesOnly _)
    intro w hw
    simp only [support, List.mem_append] at hw ⊢
    tauto
  have hs (cs : List Wire) (points : List Point)
      (hc : ∀ w ∈ cs, w ∈ bitcoinAReg ++ bitcoinBReg) :
      CircuitUsesOnly support (scalarMulCore bitcoinPointReg bitcoinWorkStart cs points) := by
    apply usesOnly_mono (scalarMulCore_usesOnly cs bitcoinPointReg points bitcoinWorkStart)
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · have h := hc w hw
      simp only [support, List.mem_append] at h ⊢
      tauto
    · simp only [support, List.mem_append]; tauto
    · simp only [support, List.mem_append]; tauto
  have hq (cs : List Wire) (hc : ∀ w ∈ cs, w ∈ bitcoinAReg ++ bitcoinBReg) :
      CircuitUsesOnly support (iqft cs bitcoinQFTAncilla) := by
    apply usesOnly_mono (iqft_usesOnly cs bitcoinQFTAncilla)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · have h := hc w hw
      simp only [support, List.mem_append] at h ⊢
      tauto
    · simp only [support, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      tauto
  apply (ModAddSupport.circuitUsesOnly_iff_support _ _).mp
  apply usesOnly_mono (xs := support)
  · simp only [trialGates, List.flatMap_append, literalGates_instantiate, scalarGates_source]
    exact usesOnly_append (usesOnly_append (usesOnly_append hh
      (hs _ _ (fun _ h => List.mem_append_left _ h)))
      (hs _ _ (fun _ h => List.mem_append_right _ h)))
      (usesOnly_append (hq _ (fun _ h => List.mem_append_left _ h))
        (hq _ (fun _ h => List.mem_append_right _ h)))
  · exact declaredWires_tight

end ShorECDLP.Entrant
