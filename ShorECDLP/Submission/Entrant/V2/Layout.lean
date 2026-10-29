import ShorECDLP.Submission.Entrant.V2.ScalarMul
import ShorECDLP.Submission.Naive.Correctness.EndToEnd

/-! EDITABLE. Wire layout of the V2 workspace with the `Engine` inversion.

The Naive public registers (phase registers, point register, QFT ancilla) are kept.  The
workspace is V2's `scalarMulWork`, whose arithmetic engine spans `Engine.blocks` blocks of
257 wires above offset 6164; the whole trial lies below `v2QubitCount`. -/

namespace ShorECDLP
namespace Secp256k1
namespace V2

/-- Dense envelope of the V2 trial (without the phase-register extension). -/
def v2QubitCount : Nat := 6164 + 257 * Engine.blocks

theorem v2QubitCount_eq : v2QubitCount = 17215 := by
  simp [v2QubitCount, Engine.blocks]

def v2AllWires : List Wire := List.range v2QubitCount


private theorem blocksWires_upper
    (blocks : List Secp256k1Instance.Block)
    (limit : Nat)
    (hids : ∀ block ∈ blocks, block.id < limit) :
    ∀ w ∈ Secp256k1Instance.blocksWires blocks,
      w < Secp256k1Instance.fieldWidth * limit := by
  intro w hw
  simp only [Secp256k1Instance.blocksWires,
    List.mem_flatMap] at hw
  obtain ⟨block, hblock, hwire⟩ := hw
  have hbound := Secp256k1Instance.Block.mem_bounds hwire
  calc
    w < Secp256k1Instance.fieldWidth * (block.id + 1) :=
      hbound.2
    _ ≤ Secp256k1Instance.fieldWidth * limit :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr (hids block hblock))

private theorem secpAddLayout_upper :
    ∀ w ∈ Secp256k1Instance.secpAddLayout.allWires,
      w < Secp256k1Instance.fieldWidth * Engine.blocks := by
  let blocks :=
    [Secp256k1Instance.regBlock Secp256k1Instance.baseId,
      Secp256k1Instance.regBlock Secp256k1Instance.exponentId,
      Secp256k1Instance.regBlock Secp256k1Instance.outId] ++
      Secp256k1Instance.addScratchBlocks
        Secp256k1Instance.initialAccId
  have hlayout :
      Secp256k1Instance.secpAddLayout.allWires =
        Secp256k1Instance.blocksWires blocks := by
    simp [blocks, Secp256k1Instance.secpAddLayout,
      RegisterLayout.allWires, Secp256k1Instance.addWork,
      Secp256k1Instance.reg, Secp256k1Instance.blocksWires,
      List.append_assoc]
  rw [hlayout]
  apply blocksWires_upper blocks Engine.blocks
  intro block hblock
  simp only [blocks, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hblock
  rcases hblock with (rfl | rfl | rfl) | hblock
  · norm_num [Secp256k1Instance.baseId, Engine.blocks]
  · norm_num [Secp256k1Instance.exponentId, Engine.blocks]
  · norm_num [Secp256k1Instance.outId, Engine.blocks]
  · simp [Secp256k1Instance.addScratchBlocks] at hblock
    rcases hblock with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [Secp256k1Instance.initialAccId, Engine.blocks]

private theorem secpMulLayout_upper :
    ∀ w ∈ Secp256k1Instance.secpMulLayout.allWires,
      w < Secp256k1Instance.fieldWidth * Engine.blocks := by
  let blocks :=
    [Secp256k1Instance.regBlock Secp256k1Instance.baseId,
      Secp256k1Instance.regBlock Secp256k1Instance.exponentId,
      Secp256k1Instance.regBlock Secp256k1Instance.outId] ++
      Secp256k1Instance.mulWorkBlocks
        Secp256k1Instance.initialAccId
        Secp256k1Instance.historyStartId
  have hlayout :
      Secp256k1Instance.secpMulLayout.allWires =
        Secp256k1Instance.blocksWires blocks := by
    simp only [Secp256k1Instance.secpMulLayout,
      RegisterLayout.allWires]
    rw [Secp256k1Instance.mulWork_eq_blocksWires]
    simp [blocks, Secp256k1Instance.blocksWires,
      Secp256k1Instance.reg, List.append_assoc]
  rw [hlayout]
  apply blocksWires_upper blocks Engine.blocks
  intro block hblock
  simp only [blocks, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hblock
  rcases hblock with (rfl | rfl | rfl) | hprivate
  · norm_num [Secp256k1Instance.baseId, Engine.blocks]
  · norm_num [Secp256k1Instance.exponentId, Engine.blocks]
  · norm_num [Secp256k1Instance.outId, Engine.blocks]
  · have hid : block.id ∈
        (Secp256k1Instance.mulWorkBlocks
          Secp256k1Instance.initialAccId
          Secp256k1Instance.historyStartId).map
            Secp256k1Instance.Block.id :=
        List.mem_map_of_mem hprivate
    rw [Secp256k1Instance.mulWorkBlocks_ids] at hid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
    norm_num [Secp256k1Instance.initialAccId,
      Secp256k1Instance.historyStartId, Engine.blocks] at hid ⊢
    omega

private theorem secpLayout_upper :
    ∀ w ∈ Engine.layout.allWires,
      w < Secp256k1Instance.fieldWidth * Engine.blocks := by
  intro w hw
  simpa [Secp256k1Instance.fieldWidth] using Engine.allWires_lt w hw

private theorem pointAddArithmeticWork_upper :
    ∀ w ∈ pointAddArithmeticWork 2052,
      w < v2QubitCount := by
  intro w hw
  simp only [pointAddArithmeticWork, List.mem_dedup,
    List.mem_append] at hw
  rcases hw with (hadd | hmul) | hexp
  · simp only [shiftWires, List.mem_map] at hadd
    obtain ⟨source, hsource, rfl⟩ := hadd
    have hsourceUpper := secpAddLayout_upper source hsource
    have hoffset : pointAddArithmeticOffset 2052 = 6164 := rfl
    calc
      pointAddArithmeticOffset 2052 + source <
          6164 + Secp256k1Instance.fieldWidth * Engine.blocks := by
        rw [hoffset]
        exact Nat.add_lt_add_left hsourceUpper 6164
      _ = v2QubitCount := by
        norm_num [v2QubitCount, Engine.blocks,
          Secp256k1Instance.fieldWidth]
  · simp only [shiftWires, List.mem_map] at hmul
    obtain ⟨source, hsource, rfl⟩ := hmul
    have hsourceUpper := secpMulLayout_upper source hsource
    have hoffset : pointAddArithmeticOffset 2052 = 6164 := rfl
    calc
      pointAddArithmeticOffset 2052 + source <
          6164 + Secp256k1Instance.fieldWidth * Engine.blocks := by
        rw [hoffset]
        exact Nat.add_lt_add_left hsourceUpper 6164
      _ = v2QubitCount := by
        norm_num [v2QubitCount, Engine.blocks,
          Secp256k1Instance.fieldWidth]
  · simp only [shiftWires, List.mem_map] at hexp
    obtain ⟨source, hsource, rfl⟩ := hexp
    have hsourceUpper := secpLayout_upper source hsource
    have hoffset : pointAddArithmeticOffset 2052 = 6164 := rfl
    calc
      pointAddArithmeticOffset 2052 + source <
          6164 + Secp256k1Instance.fieldWidth * Engine.blocks := by
        rw [hoffset]
        exact Nat.add_lt_add_left hsourceUpper 6164
      _ = v2QubitCount := by
        norm_num [v2QubitCount, Engine.blocks,
          Secp256k1Instance.fieldWidth]

private theorem v2ScalarMulWork_upper :
    ∀ w ∈ scalarMulWork bitcoinWorkStart,
      w < v2QubitCount := by
  intro w hw
  change w ∈ List.range' 1026 pointWidth ++
    controlledPointAddOutWork 1539 at hw
  rcases List.mem_append.mp hw with htemp | hw
  · have hbound := List.mem_range'_1.mp htemp
    calc
      w < 1026 + pointWidth := hbound.2
      _ < v2QubitCount := by
        norm_num [pointWidth, v2QubitCount, Engine.blocks]
  · change w ∈ List.range' 1539 pointWidth ++
      pointAddWork 2052 at hw
    rcases List.mem_append.mp hw with hchoice | hw
    · have hbound := List.mem_range'_1.mp hchoice
      calc
        w < 1539 + pointWidth := hbound.2
        _ < v2QubitCount := by
          norm_num [pointWidth, v2QubitCount, Engine.blocks]
    · change w ∈ List.range' 2052 4112 ++
        pointAddArithmeticWork 2052 at hw
      rcases List.mem_append.mp hw with hlocal | harithmetic
      · have hbound := List.mem_range'_1.mp hlocal
        calc
          w < 2052 + 4112 := hbound.2
          _ < v2QubitCount := by
            norm_num [v2QubitCount, Engine.blocks]
      · exact pointAddArithmeticWork_upper w harithmetic

/--
The fixed submission layout has the required widths, pairwise-disjoint public
and workspace wires, and a fresh QFT ancilla.  The proof uses interval bounds;
it does not evaluate the large workspace with `decide`.
-/
theorem v2WireLayout :
    bitcoinAReg.length = 256 ∧
    bitcoinBReg.length = 256 ∧
    bitcoinPointReg.length = pointWidth ∧
    (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
      scalarMulWork bitcoinWorkStart).Nodup ∧
    bitcoinQFTAncilla ∉
      bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
        scalarMulWork bitcoinWorkStart := by
  have append_nodup_of_bounds :
      ∀ (left right : List Wire) (boundary : Wire),
        left.Nodup →
        right.Nodup →
        (∀ w ∈ left, w < boundary) →
        (∀ w ∈ right, boundary ≤ w) →
        (left ++ right).Nodup := by
    intro left right boundary hleft hright hleftBound hrightBound
    rw [List.nodup_append]
    refine ⟨hleft, hright, ?_⟩
    intro w hwLeft _ hwRight rfl
    exact (Nat.not_lt_of_ge (hrightBound w hwRight)) (hleftBound w hwLeft)

  have hArithmeticNodup :
      (pointAddArithmeticWork 2052).Nodup := by
    exact List.nodup_dedup _
  have hArithmeticOffset : pointAddArithmeticOffset 2052 = 6164 := by
    rfl
  have hArithmeticLower :
      ∀ w ∈ pointAddArithmeticWork 2052, 6164 ≤ w := by
    intro w hw
    simp only [pointAddArithmeticWork, List.mem_dedup,
      List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    all_goals
      simp only [shiftWires, List.mem_map] at hw
      obtain ⟨source, _, rfl⟩ := hw
      rw [hArithmeticOffset]
      exact Nat.le_add_right 6164 source

  have hPointWorkNodup : (pointAddWork 2052).Nodup := by
    change
      (List.range' 2052 4112 ++ pointAddArithmeticWork 2052).Nodup
    apply append_nodup_of_bounds _ _ 6164
    · exact List.nodup_range'
    · exact hArithmeticNodup
    · intro w hw
      exact (List.mem_range'_1.mp hw).2
    · exact hArithmeticLower
  have hPointWorkLower : ∀ w ∈ pointAddWork 2052, 2052 ≤ w := by
    intro w hw
    change
      w ∈ List.range' 2052 4112 ++ pointAddArithmeticWork 2052 at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (List.mem_range'_1.mp hw).1
    · exact (Nat.le_trans (by norm_num) (hArithmeticLower w hw))

  have hOutWorkNodup : (controlledPointAddOutWork 1539).Nodup := by
    change
      (List.range' 1539 pointWidth ++ pointAddWork 2052).Nodup
    apply append_nodup_of_bounds _ _ 2052
    · exact List.nodup_range'
    · exact hPointWorkNodup
    · intro w hw
      simpa [pointWidth] using (List.mem_range'_1.mp hw).2
    · exact hPointWorkLower
  have hOutWorkLower :
      ∀ w ∈ controlledPointAddOutWork 1539, 1539 ≤ w := by
    intro w hw
    change w ∈ List.range' 1539 pointWidth ++ pointAddWork 2052 at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (List.mem_range'_1.mp hw).1
    · exact (Nat.le_trans (by norm_num) (hPointWorkLower w hw))

  have hWorkNodup : (scalarMulWork bitcoinWorkStart).Nodup := by
    change
      (List.range' 1026 pointWidth ++
        controlledPointAddOutWork 1539).Nodup
    apply append_nodup_of_bounds _ _ 1539
    · exact List.nodup_range'
    · exact hOutWorkNodup
    · intro w hw
      simpa [pointWidth] using (List.mem_range'_1.mp hw).2
    · exact hOutWorkLower
  have hWorkLower :
      ∀ w ∈ scalarMulWork bitcoinWorkStart, 1026 ≤ w := by
    intro w hw
    change
      w ∈ List.range' 1026 pointWidth ++
        controlledPointAddOutWork 1539 at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (List.mem_range'_1.mp hw).1
    · exact (Nat.le_trans (by norm_num) (hOutWorkLower w hw))

  have hPublicNodup :
      (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg).Nodup := by
    have hab : (bitcoinAReg ++ bitcoinBReg).Nodup := by
      apply append_nodup_of_bounds _ _ 256
      · exact List.nodup_range'
      · exact List.nodup_range'
      · intro w hw
        change w ∈ List.range' 0 256 at hw
        exact (List.mem_range'_1.mp hw).2
      · intro w hw
        change w ∈ List.range' 256 256 at hw
        exact (List.mem_range'_1.mp hw).1
    have habp :
        ((bitcoinAReg ++ bitcoinBReg) ++ bitcoinPointReg).Nodup := by
      apply append_nodup_of_bounds _ _ 512
      · exact hab
      · exact List.nodup_range'
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · change w ∈ List.range' 0 256 at hw
          exact (List.mem_range'_1.mp hw).2.trans_le (by norm_num)
        · change w ∈ List.range' 256 256 at hw
          simpa using (List.mem_range'_1.mp hw).2
      · intro w hw
        change w ∈ List.range' 512 pointWidth at hw
        exact (List.mem_range'_1.mp hw).1
    simpa only [List.append_assoc] using habp
  have hPublicUpper :
      ∀ w ∈ bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg, w < 1025 := by
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · change w ∈ List.range' 0 256 at hw
        exact (List.mem_range'_1.mp hw).2.trans_le (by norm_num)
      · change w ∈ List.range' 256 256 at hw
        exact (List.mem_range'_1.mp hw).2.trans_le (by norm_num)
    · change w ∈ List.range' 512 pointWidth at hw
      simpa [pointWidth] using (List.mem_range'_1.mp hw).2
  have hnodup :
      (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
        scalarMulWork bitcoinWorkStart).Nodup := by
    have h := append_nodup_of_bounds
      (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg)
      (scalarMulWork bitcoinWorkStart) 1026
      hPublicNodup hWorkNodup
      (fun w hw => (hPublicUpper w hw).trans (by norm_num)) hWorkLower
    simpa only [List.append_assoc] using h
  have hancillaFresh :
      bitcoinQFTAncilla ∉
        bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
          scalarMulWork bitcoinWorkStart := by
    intro hw
    have hw' :
        bitcoinQFTAncilla ∈
          (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg) ++
            scalarMulWork bitcoinWorkStart := by
      simpa only [List.append_assoc] using hw
    rcases List.mem_append.mp hw' with hwPublic | hwWork
    · have := hPublicUpper bitcoinQFTAncilla hwPublic
      norm_num [bitcoinQFTAncilla] at this
    · have := hWorkLower bitcoinQFTAncilla hwWork
      norm_num [bitcoinQFTAncilla] at this

  exact ⟨by simp [bitcoinAReg], by simp [bitcoinBReg],
    by simp [bitcoinPointReg], hnodup, hancillaFresh⟩

theorem v2DeclaredWires_subset :
    ∀ w ∈
      bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
        scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla],
      w ∈ v2AllWires := by
  intro w hw
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with (((ha | hb) | hpoint) | hwork) | hancilla
  · change w ∈ List.range' 0 256 at ha
    have hbound := (List.mem_range'_1.mp ha).2
    simpa [v2AllWires, v2QubitCount, Engine.blocks] using
      (hbound.trans (by norm_num : 256 < 17215))
  · change w ∈ List.range' 256 256 at hb
    have hbound := (List.mem_range'_1.mp hb).2
    simpa [v2AllWires, v2QubitCount, Engine.blocks] using
      (hbound.trans (by norm_num : 512 < 17215))
  · change w ∈ List.range' 512 pointWidth at hpoint
    have hbound := (List.mem_range'_1.mp hpoint).2
    have hlt : w < v2QubitCount := by
      exact hbound.trans (by
        norm_num [pointWidth, v2QubitCount, Engine.blocks])
    simpa [v2AllWires] using hlt
  · have hlt := v2ScalarMulWork_upper w hwork
    simpa [v2AllWires] using hlt
  · subst w
    simp [v2AllWires, v2QubitCount, Engine.blocks,
      bitcoinQFTAncilla]

end V2
end Secp256k1
end ShorECDLP
