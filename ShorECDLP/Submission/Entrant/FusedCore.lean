import ShorECDLP.Submission.Entrant.MainA

/-! Fused constant pairs for the generic branch.

The generic branch adds two pairs of table constants that are needed back to back:
`(-cx, -cy)` at its entry and `(cx, -cy)` in the recovery. Each constant used to be its
own masked site, so every pair paid two table traversals and two measured clears. At
those dialog boundaries the whole dialog pool is clean, so the second constant can be
loaded into a second 256-site register (`pairSrc`) by the same traversal. The `y` adder
then reads `pairSrc` instead of the first register. -/

section
namespace ShorECDLP.Entrant.WEXUnlookup
open ECDSAAdd Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000

/-! ### Program-level reordering -/

theorem run_zero_records (p : ECDSAAdd.Program) (hp : ECDSAAdd.measurementCount p = 0)
    (m : List Bool) (s : ECDSAAdd.State) : ECDSAAdd.run p m s = ECDSAAdd.run p List.nil s := by
  rw [← ECDSAAdd.run_take p m s, hp, List.take_zero]

theorem run_zero_append (p q : ECDSAAdd.Program) (hp : ECDSAAdd.measurementCount p = 0)
    (m : List Bool) (s : ECDSAAdd.State) :
    ECDSAAdd.run (p ++ q) m s = ECDSAAdd.run q m (ECDSAAdd.run p List.nil s) := by
  rw [ECDSAAdd.run_append, hp, List.drop_zero, List.take_zero]

theorem run_meas_append (p q : ECDSAAdd.Program) (m : List Bool) (s : ECDSAAdd.State) :
    ECDSAAdd.run (p ++ q) m s =
      ECDSAAdd.run q (m.drop (ECDSAAdd.measurementCount p)) (ECDSAAdd.run p m s) := by
  rw [ECDSAAdd.run_append, ECDSAAdd.run_take]

/-- Loading two constants by one traversal, then running both adders, is the two
load-add-unload blocks in sequence. -/
theorem fused_run_gen (mA mB pA pB : ECDSAAdd.Program)
    (zA : ECDSAAdd.measurementCount mA = 0) (zB : ECDSAAdd.measurementCount mB = 0)
    (hAB : Disjoint (ECDSAAdd.wires pA) (ECDSAAdd.wires mB))
    (hBA : Disjoint (ECDSAAdd.wires mA) (ECDSAAdd.wires pB))
    (hcomm : ∀ t, ECDSAAdd.run mA List.nil (ECDSAAdd.run mB List.nil t) = ECDSAAdd.run mB List.nil (ECDSAAdd.run mA List.nil t))
    (m : List Bool) (s : ECDSAAdd.State) :
    ECDSAAdd.run ((mA ++ mB) ++ (pA ++ pB) ++ (mA ++ mB)) m s =
      ECDSAAdd.run ((mA ++ pA ++ mA) ++ (mB ++ pB ++ mB)) m s := by
  simp only [List.append_assoc]
  have lhs : ECDSAAdd.run (mA ++ (mB ++ (pA ++ (pB ++ (mA ++ mB))))) m s =
      ECDSAAdd.run mB ((m.drop (ECDSAAdd.measurementCount pA)).drop (ECDSAAdd.measurementCount pB))
        (ECDSAAdd.run mA List.nil (ECDSAAdd.run pB (m.drop (ECDSAAdd.measurementCount pA))
          (ECDSAAdd.run pA m (ECDSAAdd.run mB List.nil (ECDSAAdd.run mA List.nil s))))) := by
    rw [run_zero_append _ _ zA, run_zero_append _ _ zB, run_meas_append pA, run_meas_append pB,
      run_zero_append _ _ zA]
  have rhs : ECDSAAdd.run (mA ++ (pA ++ (mA ++ (mB ++ (pB ++ mB))))) m s =
      ECDSAAdd.run mB ((m.drop (ECDSAAdd.measurementCount pA)).drop (ECDSAAdd.measurementCount pB))
        (ECDSAAdd.run pB (m.drop (ECDSAAdd.measurementCount pA))
        (ECDSAAdd.run mB List.nil (ECDSAAdd.run mA List.nil (ECDSAAdd.run pA m (ECDSAAdd.run mA List.nil s))))) := by
    rw [run_zero_append _ _ zA, run_meas_append pA, run_zero_append _ _ zA, run_zero_append _ _ zB,
      run_meas_append pB]
  rw [lhs, rhs, ECDSAAdd.Arithmetic.run_disjoint_commute pA mB hAB m List.nil (ECDSAAdd.run mA List.nil s),
    ECDSAAdd.Arithmetic.run_disjoint_commute mA pB hBA List.nil _ _, hcomm]

/-- Masked constant loads with one control commute when their registers are disjoint. -/
theorem masked_comm (g : Wire) (ra rb : List Wire) (ka kb : Nat) (hga : g ∉ ra) (hgb : g ∉ rb)
    (hd : Disjoint (ECDSAAdd.wires (xorConstant ra ka)) (ECDSAAdd.wires (xorConstant rb kb)))
    (s : ECDSAAdd.State) :
    ECDSAAdd.run (maskedConstant g ra ka) List.nil (ECDSAAdd.run (maskedConstant g rb kb) List.nil s) =
      ECDSAAdd.run (maskedConstant g rb kb) List.nil (ECDSAAdd.run (maskedConstant g ra ka) List.nil s) := by
  have pa : ∀ t : ECDSAAdd.State, (ECDSAAdd.run (xorConstant ra ka) List.nil t).basis g = t.basis g :=
    fun t => ECDSAAdd.run_preserves_outside _ _ _ _
      (fun h => hga (List.mem_toFinset.mp (xorConstant_wires_subset ra ka h)))
  have pb : ∀ t : ECDSAAdd.State, (ECDSAAdd.run (xorConstant rb kb) List.nil t).basis g = t.basis g :=
    fun t => ECDSAAdd.run_preserves_outside _ _ _ _
      (fun h => hgb (List.mem_toFinset.mp (xorConstant_wires_subset rb kb h)))
  by_cases hg : s.basis g = true
  · have e1 : ECDSAAdd.run (maskedConstant g ra ka) List.nil s = ECDSAAdd.run (xorConstant ra ka) List.nil s := by
      rw [maskedConstant_run g ra ka hga, if_pos hg]
    have e2 : ECDSAAdd.run (maskedConstant g rb kb) List.nil s = ECDSAAdd.run (xorConstant rb kb) List.nil s := by
      rw [maskedConstant_run g rb kb hgb, if_pos hg]
    have e3 : ECDSAAdd.run (maskedConstant g ra ka) List.nil (ECDSAAdd.run (xorConstant rb kb) List.nil s) =
        ECDSAAdd.run (xorConstant ra ka) List.nil (ECDSAAdd.run (xorConstant rb kb) List.nil s) := by
      rw [maskedConstant_run g ra ka hga, if_pos ((pb s).trans hg)]
    have e4 : ECDSAAdd.run (maskedConstant g rb kb) List.nil (ECDSAAdd.run (xorConstant ra ka) List.nil s) =
        ECDSAAdd.run (xorConstant rb kb) List.nil (ECDSAAdd.run (xorConstant ra ka) List.nil s) := by
      rw [maskedConstant_run g rb kb hgb, if_pos ((pa s).trans hg)]
    rw [e2, e1, e3, e4]
    exact ECDSAAdd.Arithmetic.run_disjoint_commute _ _ hd List.nil List.nil s
  · have e1 : ECDSAAdd.run (maskedConstant g ra ka) List.nil s = s := by
      rw [maskedConstant_run g ra ka hga, if_neg hg]
    have e2 : ECDSAAdd.run (maskedConstant g rb kb) List.nil s = s := by
      rw [maskedConstant_run g rb kb hgb, if_neg hg]
    rw [e2, e1, e2]

/-! ### The second constant register -/

/-- 256 dialog-pool sites (pool indices 1284 to 1539), clear of the first constant
adder's footprint (pool indices 0 to 514). -/
def pairSrc : List Wire := List.range' 15399 256

/-- The `y` constant adder of `recoveryConstant`, reading its constant from `pairSrc`. -/
def yPair : MeasuredCanonicalModLayout :=
  { streamLayout.recoveryConstant streamLayout.point.y with src := pairSrc }

theorem pairSrc_dialog (q : Wire) (hq : q ∈ pairSrc) : q ∈ streamLayout.dialogPool := by
  rw [pairSrc,List.mem_range'_1] at hq
  have hp : streamLayout.dialogPool = ((List.range' 4115 5699).map streamWire).take 2613 := rfl
  rw [hp,List.mem_iff_getElem]
  refine ⟨q - 14115,by simp only [List.length_take,List.length_map,List.length_range']; rw [Nat.min_eq_left (by norm_num)]; omega,?_⟩
  simp only [List.getElem_take,List.getElem_map,List.getElem_range']
  unfold streamWire
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem yPair_widths : yPair.Widths 256 := by
  have h := streamLayout.recoveryConstant_widths streamLayout_widths streamLayout.point.y
    streamLayout_widths.inputY
  exact ⟨by simp [yPair, pairSrc], h.out, h.carry⟩

theorem yPair_nodup : (streamLayout.core.generic :: yPair.wires).Nodup := by
  decide +kernel

theorem yPair_counts :
    ECDSAAdd.measurementCount (yPair.program SquareReduction.c ECDSAAdd.p) =
        ECDSAAdd.measurementCount
          ((streamLayout.recoveryConstant streamLayout.point.y).program SquareReduction.c ECDSAAdd.p) ∧
      ECDSAAdd.toffoliCount (yPair.program SquareReduction.c ECDSAAdd.p) =
        ECDSAAdd.toffoliCount
          ((streamLayout.recoveryConstant streamLayout.point.y).program SquareReduction.c ECDSAAdd.p) := by
  have h1 := MeasuredCanonicalModLayout.secp_program_counts yPair yPair_widths SquareReduction.c ECDSAAdd.p
  have h2 := MeasuredCanonicalModLayout.secp_program_counts (streamLayout.recoveryConstant streamLayout.point.y)
    (streamLayout.recoveryConstant_widths streamLayout_widths _ streamLayout_widths.inputY)
    SquareReduction.c ECDSAAdd.p
  exact ⟨h1.2.trans h2.2.symm,h1.1.trans h2.1.symm⟩

theorem yPair_slots : ECDSAAdd.Challenge.gateSlots (yPair.program SquareReduction.c ECDSAAdd.p) ≤ 16933 :=
  ECDSAAdd.Baselines.canonicalMod_gateSlots_le yPair 256 _ _ yPair_widths

theorem xConst_nodup :
    (streamLayout.core.generic :: (streamLayout.recoveryConstant streamLayout.point.x).wires).Nodup :=
  streamLayout.recoveryConstant_nodup streamLayout_widths streamLayout_nodup _ (Or.inl rfl)

theorem pair_disjoint_x :
    ∀ q ∈ streamLayout.core.generic :: pairSrc,
      q ∉ (streamLayout.recoveryConstant streamLayout.point.x).wires := by
  decide +kernel

theorem pair_disjoint_y :
    ∀ q ∈ streamLayout.core.generic :: (streamLayout.recoveryConstant streamLayout.point.x).src,
      q ∉ yPair.wires := by
  decide +kernel

theorem pair_src_disjoint :
    ∀ q ∈ (streamLayout.recoveryConstant streamLayout.point.x).src, q ∉ pairSrc := by
  decide +kernel

theorem pair_generic_x : streamLayout.core.generic ∉ (streamLayout.recoveryConstant streamLayout.point.x).src :=
  fun h => (List.nodup_cons.mp xConst_nodup).1 (by simp [MeasuredCanonicalModLayout.wires, h])

theorem pair_generic_y : streamLayout.core.generic ∉ pairSrc :=
  fun h => (List.nodup_cons.mp yPair_nodup).1 (by simp [MeasuredCanonicalModLayout.wires, yPair, h])

theorem wires_disjoint_of {p q : ECDSAAdd.Program} {lp lq : List Wire}
    (hp : ECDSAAdd.wires p ⊆ lp.toFinset) (hq : ECDSAAdd.wires q ⊆ lq.toFinset)
    (h : ∀ x ∈ lq, x ∉ lp) : Disjoint (ECDSAAdd.wires p) (ECDSAAdd.wires q) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact h a (List.mem_toFinset.mp (hq hb)) (List.mem_toFinset.mp (hp ha))

/-- The fused reference program equals the two constant additions in sequence. -/
theorem pair_run (kA kB : Nat) (m : List Bool) (s : ECDSAAdd.State) :
    ECDSAAdd.run ((maskedConstant streamLayout.core.generic
          (streamLayout.recoveryConstant streamLayout.point.x).src kA ++
        maskedConstant streamLayout.core.generic pairSrc kB) ++
      ((streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p ++
        yPair.program SquareReduction.c ECDSAAdd.p) ++
      (maskedConstant streamLayout.core.generic
          (streamLayout.recoveryConstant streamLayout.point.x).src kA ++
        maskedConstant streamLayout.core.generic pairSrc kB)) m s =
    ECDSAAdd.run (compactRecoveryConstant (streamLayout.recoveryConstant streamLayout.point.x)
        streamLayout.core.generic SquareReduction.c ECDSAAdd.p kA ++
      compactRecoveryConstant yPair streamLayout.core.generic SquareReduction.c ECDSAAdd.p kB) m s := by
  have zA := (maskedConstant_counts streamLayout.core.generic
    (streamLayout.recoveryConstant streamLayout.point.x).src kA).2
  have zB := (maskedConstant_counts streamLayout.core.generic pairSrc kB).2
  have hAB : Disjoint
      (ECDSAAdd.wires ((streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p))
      (ECDSAAdd.wires (maskedConstant streamLayout.core.generic pairSrc kB)) :=
    wires_disjoint_of (MeasuredCanonicalModLayout.program_wires_subset _ _ _)
      (maskedConstant_wires_subset _ _ _) pair_disjoint_x
  have hBA : Disjoint
      (ECDSAAdd.wires (maskedConstant streamLayout.core.generic
        (streamLayout.recoveryConstant streamLayout.point.x).src kA))
      (ECDSAAdd.wires (yPair.program SquareReduction.c ECDSAAdd.p)) :=
    wires_disjoint_of (maskedConstant_wires_subset _ _ _)
      (MeasuredCanonicalModLayout.program_wires_subset _ _ _) (fun x h1 h2 => pair_disjoint_y x h2 h1)
  have hx : Disjoint
      (ECDSAAdd.wires (xorConstant (streamLayout.recoveryConstant streamLayout.point.x).src kA))
      (ECDSAAdd.wires (xorConstant pairSrc kB)) :=
    wires_disjoint_of (xorConstant_wires_subset _ _) (xorConstant_wires_subset _ _)
      (fun x h1 h2 => pair_src_disjoint x h2 h1)
  rw [fused_run_gen _ _ _ _ zA zB hAB hBA
    (fun t => masked_comm _ _ _ _ _ pair_generic_x pair_generic_y hx t) m s]
  rfl

/-- The `y` constant addition from the second register. -/
theorem dialogStep_addY2 (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) (k : ECDSAAdd.Fp) :
    ECDSAAdd.Triple (PointDialogValues streamLayout X Y G base)
      (compactRecoveryConstant yPair streamLayout.core.generic SquareReduction.c ECDSAAdd.p k.val)
      (PointDialogValues streamLayout X (Y+(if G then k else 0)) G base) := by
  intro s m v
  have clean : ∀ q ∈ streamLayout.dialogPool, s.basis q = false := (ECDSAAdd.Arithmetic.regValue_zero _ _).mp v.clean
  have pool := streamLayout.recoveryConstant_pool streamLayout_widths streamLayout.point.y
  have aux : ∀ q ∈ (streamLayout.recoveryConstant streamLayout.point.y).src ++
      (streamLayout.recoveryConstant streamLayout.point.y).carry ++
      [(streamLayout.recoveryConstant streamLayout.point.y).high,
        (streamLayout.recoveryConstant streamLayout.point.y).cin,
        (streamLayout.recoveryConstant streamLayout.point.y).flag], s.basis q = false := by
    rw [pool]
    intro q hq
    exact clean q (List.mem_of_mem_take hq)
  have hh : s.basis yPair.high = false :=
    aux _ (List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl)))
  have hi : s.basis yPair.cin = false :=
    aux _ (List.mem_append_right _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have hf : s.basis yPair.flag = false :=
    aux _ (List.mem_append_right _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
  have hc : ∀ q ∈ yPair.carry, s.basis q = false :=
    fun q hq => aux q (List.mem_append_left _ (List.mem_append_right _ hq))
  have source : ECDSAAdd.regValue yPair.src s.basis = 0 :=
    (ECDSAAdd.Arithmetic.regValue_zero _ _).mpr (fun q hq => clean q (pairSrc_dialog q hq))
  have result := compactRecoveryConstant_correct yPair streamLayout.core.generic 256 SquareReduction.c
    ECDSAAdd.p k.val yPair_widths yPair_nodup (by decide) (by norm_num [ECDSAAdd.p, SquareReduction.c])
    (by norm_num [SquareReduction.c]) k.isLt Y.val Y.isLt s m source v.y hh hf hc hi
  generalize ECDSAAdd.run (compactRecoveryConstant yPair streamLayout.core.generic SquareReduction.c
    ECDSAAdd.p k.val) m s = t at result ⊢
  rw [v.generic] at result
  obtain ⟨hp,hy,hfr⟩ := result
  refine ⟨hp,v.withY streamLayout_nodup ?_ hfr⟩
  change ECDSAAdd.regValue streamLayout.point.y t.basis = _ at hy
  generalize ECDSAAdd.regValue streamLayout.point.y t.basis = V at hy ⊢
  cases G <;> simpa [ZMod.val_add, Nat.mod_eq_of_lt (ZMod.val_lt Y)] using hy

/-! ### The fused masked site -/

/-- Both adders of a fused pair: `x` from the first register, then `y` from `pairSrc`. -/
def pairArith : ECDSAAdd.Program :=
  (streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p ++
    yPair.program SquareReduction.c ECDSAAdd.p

def pairSite {n} (refsA refsB : Nat → Nat → ConstantBit n) : MaskedSite n :=
  ⟨streamLayout.core.generic,
    indexedPorts (streamLayout.recoveryConstant streamLayout.point.x).src refsA true ++
      indexedPorts pairSrc refsB true,
    wLiteral pairArith⟩

def pairAdd {n} (refsA refsB : Nat → Nat → ConstantBit n) : Code n := [.masked (pairSite refsA refsB)]

theorem pairSite_targets {n} (refsA refsB : Nat → Nat → ConstantBit n) :
    portTargets (pairSite refsA refsB).ports = List.range' 14115 256 ++ List.range' 15399 256 := by
  change portTargets (indexedPorts _ refsA true ++ indexedPorts pairSrc refsB true) = _
  simp only [portTargets, List.map_append]
  have h1 := indexed_targets (streamLayout.recoveryConstant streamLayout.point.x).src refsA true
  have h2 := indexed_targets pairSrc refsB true
  simp only [portTargets] at h1 h2
  rw [h1, h2]
  change streamLayout.dialogPool.take 256 ++ pairSrc = _
  decide +kernel

theorem pairSite_guard {n} (refsA refsB : Nat → Nat → ConstantBit n) :
    (pairSite refsA refsB).guard = 14113 := by
  change streamLayout.core.generic = 14113
  decide +kernel

theorem pairSite_inst {n} (read : ConstantBit n → Bool) (address : Nat)
    (refsA refsB : Nat → Nat → ConstantBit n) (kA kB : ECDSAAdd.Fp)
    (hA : ∀ i < 256, read (refsA address i) = kA.val.testBit i)
    (hB : ∀ i < 256, read (refsB address i) = kB.val.testBit i) :
    (specialize (pairSite refsA refsB).code address).instantiate read =
      (maskedConstant streamLayout.core.generic
          (streamLayout.recoveryConstant streamLayout.point.x).src kA.val ++
        maskedConstant streamLayout.core.generic pairSrc kB.val) ++
      ((streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p ++
        yPair.program SquareReduction.c ECDSAAdd.p) ++
      (maskedConstant streamLayout.core.generic
          (streamLayout.recoveryConstant streamLayout.point.x).src kA.val ++
        maskedConstant streamLayout.core.generic pairSrc kB.val) := by
  have lenA : (streamLayout.recoveryConstant streamLayout.point.x).src.length = 256 :=
    (streamLayout.recoveryConstant_widths streamLayout_widths streamLayout.point.x
      streamLayout_widths.inputX).src
  have lenB : pairSrc.length = 256 := by simp [pairSrc]
  have iA := maskedT_inst read streamLayout.core.generic
    (streamLayout.recoveryConstant streamLayout.point.x).src (refsA address) kA.val
    (fun i hi => hA i (by omega))
  have iB := maskedT_inst read streamLayout.core.generic pairSrc (refsB address) kB.val
    (fun i hi => hB i (by omega))
  simp only [pairSite, pairArith, wLiteral, MaskedSite.code, MaskedSite.prefix, specialize, List.cons_append, List.nil_append,
    List.flatMap_cons,
    List.flatMap_nil, List.append_nil, WInstr.specialize, portTemplate_append,
    portTemplate_indexed_some, Tmpl.instantiate_append, Tmpl.instantiate_lit, iA, iB, List.append_assoc]

theorem pair_checked {n} (read : ConstantBit n → Bool) (address : Nat)
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) (kA kB : ECDSAAdd.Fp)
    (refsA refsB : Nat → Nat → ConstantBit n)
    (hA : ∀ i < 256, read (refsA address i) = kA.val.testBit i)
    (hB : ∀ i < 256, read (refsB address i) = kB.val.testBit i) :
    Checked read address (PointDialogValues streamLayout X Y G base) (pairAdd refsA refsB)
      (PointDialogValues streamLayout (X+(if G then kA else 0)) (Y+(if G then kB else 0)) G base) := by
  refine Checked.masked (pairSite refsA refsB) ?_ ?_
  · rw [pairSite_inst read address refsA refsB kA kB hA hB]
    intro s m hs
    rw [pair_run]
    exact ((dialogStep_addX streamLayout streamLayout_widths streamLayout_nodup X Y G base kA).seq
      (dialogStep_addY2 (X+(if G then kA else 0)) Y G base kB)) s m hs
  · intro s hs q hq
    rw [pairSite_targets] at hq
    have hc : ∀ w ∈ streamLayout.dialogPool, s w = false := (ECDSAAdd.Arithmetic.regValue_zero _ _).mp hs.clean
    have hq' : q ∈ streamLayout.dialogPool.take 256 ++ pairSrc := by
      have e : streamLayout.dialogPool.take 256 ++ pairSrc = List.range' 14115 256 ++ List.range' 15399 256 := by
        decide +kernel
      rw [e]; exact hq
    rcases List.mem_append.mp hq' with h | h
    · exact hc q (List.mem_of_mem_take h)
    · exact hc q (pairSrc_dialog q h)

/-! ### The fused generic branch -/

def recovery2 {n} (rows : Nat → Fin n) : Code n :=
  [.plain (wLiteral (pointRecoveryReflection streamLayout)),
    .plain (wLiteral (pointDialogConstantAdd streamLayout streamLayout.point.x 1))] ++
    pairAdd (wFields rows .x) (wFields rows .negY)

def core2 {n} (rows : Nat → Fin n) : Code n :=
  pairAdd (wFields rows .negX) (wFields rows .negY) ++
    [.plain (wLiteral (ECDSAAdd.Frontier.arithS streamLayout false)),
     .plain (wLiteral (ECDSAAdd.Frontier.SquareOB5.program streamLayout))] ++
    constAdd streamLayout streamLayout.point.x (wFields rows .tripleX) ++
    [.plain (wLiteral (ECDSAAdd.Frontier.arithS streamLayout true))] ++ recovery2 rows

def generic2 {n} (rows : Nat → Fin n) : Code n :=
  [.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))] ++ core2 rows ++
    [.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))]

theorem recovery2_checked {n} (read : ConstantBit n → Bool) (address : Nat)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) :
    Checked read address (PointDialogValues streamLayout X Y G base) (recovery2 rows)
      (PointDialogValues streamLayout (if G then cx-X else X) (if G then Y-cy else Y) G base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have a := literal_checked read address _ _ _ (pointRecoveryReflection_step streamLayout hw hn X Y G base)
  have c := literal_checked read address _ _ _
    (dialogStep_addX streamLayout hw hn (if G then -1-X else X) Y G base 1)
  have d := pair_checked read address ((if G then -1-X else X)+(if G then 1 else 0)) Y G base cx (-cy)
    (wFields rows .x) (wFields rows .negY)
    (row_bits hc hr .x cx (field_some_x hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc))
  have all := (a.seq c).seq d
  have hx : ((if G then -1-X else X)+(if G then 1 else 0))+(if G then cx else 0)=
      (if G then cx-X else X) := by cases G <;> simp; ring
  have hy : Y+(if G then -cy else 0)=(if G then Y-cy else Y) := by cases G <;> simp [sub_eq_add_neg]
  rw [hx,hy] at all
  simpa only [recovery2,List.cons_append,List.nil_append,List.append_assoc] using all

theorem core2_checked_true {n} (read : ConstantBit n → Bool) (address : Nat)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Checked read address (PointDialogValues streamLayout X Y true base) (core2 rows)
      (PointDialogValues streamLayout (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h12 := pair_checked read address X Y true base (-cx) (-cy)
    (wFields rows .negX) (wFields rows .negY)
    (row_bits hc hr .negX (-cx) (field_some_negX hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc))
  simp only [if_true,←sub_eq_add_neg] at h12
  have h3 := literal_checked read address _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn (X-cx) (Y-cy) true base false (sub_ne_zero.mpr hX))
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [Bool.false_eq_true,if_false,ha] at h3
  have h4 := literal_checked read address _ _ _
    (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn (X-cx) a true base)
  simp only [if_true] at h4
  have h5 := addX_checked read address streamLayout hw hn ((X-cx)-a*a) a true base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc))
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := literal_checked read address _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn d a true base true hd)
  simp only [if_true] at h6
  have r := recovery2_checked read address rows hc hr d (a*d) true base
  simp only [if_true] at r
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at r
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at r
  have h := ((((h12.seq h3).seq h4).seq h5).seq h6).seq r
  simpa only [core2,List.append_assoc,List.cons_append,List.nil_append] using h

theorem core2_checked_false {n} (read : ConstantBit n → Bool) (address : Nat)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState) (hX0 : X ≠ 0) :
    Checked read address (PointDialogValues streamLayout X Y false base) (core2 rows)
      (PointDialogValues streamLayout X Y false base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have h12 := pair_checked read address X Y false base (-cx) (-cy)
    (wFields rows .negX) (wFields rows .negY)
    (row_bits hc hr .negX (-cx) (field_some_negX hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc))
  have h3 := literal_checked read address _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X Y false base false hX0)
  have h4 := literal_checked read address _ _ _
    (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn X (Y/X) false base)
  have h5 := addX_checked read address streamLayout hw hn X (Y/X) false base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc))
  have h6 := literal_checked read address _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X (Y/X) false base true hX0)
  have r := recovery2_checked read address rows hc hr X Y false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h12 h3 h4 h5 h6 r
  rw [div_mul_cancel₀ Y hX0] at h6
  have h := ((((h12.seq h3).seq h4).seq h5).seq h6).seq r
  simpa only [core2,List.append_assoc,List.cons_append,List.nil_append] using h

theorem values_unique {L : ControlledPointLayout} {X Y : ECDSAAdd.Fp} {G : Bool} {base s t : BasisState}
    (hs : PointDialogValues L X Y G base s) (ht : PointDialogValues L X Y G base t) : s = t := by
  funext q
  by_cases hx : q ∈ L.point.x
  · exact (ECDSAAdd.Arithmetic.regValue_eq_iff _ _ _).mp (hs.x.trans ht.x.symm) q hx
  by_cases hy : q ∈ L.point.y
  · exact (ECDSAAdd.Arithmetic.regValue_eq_iff _ _ _).mp (hs.y.trans ht.y.symm) q hy
  have hq : q ∉ L.point.x ++ L.point.y := by simp [hx, hy]
  exact (hs.rest q hq).trans (ht.rest q hq).symm

/-- Two checked codes with one exact post-state have equal reference runs. -/
theorem checked_run_eq {n} {read : ConstantBit n → Bool} {address : Nat} {P : BasisState → Prop}
    {a b : Code n} {X Y : ECDSAAdd.Fp} {G : Bool} {base : BasisState}
    (ha : Checked read address P a (PointDialogValues streamLayout X Y G base))
    (hb : Checked read address P b (PointDialogValues streamLayout X Y G base))
    (st : ECDSAAdd.State) (hs : P st.basis) (m : List Bool) :
    ECDSAAdd.run (reference read address a) m st = ECDSAAdd.run (reference read address b) m st := by
  obtain ⟨pa, va⟩ := ha.correct st m hs
  obtain ⟨pb, vb⟩ := hb.correct st m hs
  exact ECDSAAdd.State.extensionality _ _ (pa.trans pb.symm) (values_unique va vb)

/-- At every generic boundary the fused branch is safe and has the reference run of the
original branch. -/
theorem generic2_cases {n} (read : ConstantBit n → Bool) (address : Nat)
    (rows : Nat → Fin n) (R : Point) (b : Bool) (f : BasisState)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (hg : f streamLayout.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc))
    (st : ECDSAAdd.State) (hs : PointDialogBoundary streamLayout R b f st.basis) :
    Safe read address (generic2 rows) st ∧
      ∀ m, ECDSAAdd.run (reference read address (generic2 rows)) m st =
        ECDSAAdd.run (reference read address (generic streamLayout rows)) m st := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hp := (point_holds _ _ _).mp hs.point
  have hgen : st.basis streamLayout.core.generic = f streamLayout.core.generic :=
    hs.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f streamLayout.core.generic = false := by
      cases h : f streamLayout.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues streamLayout 0 0 false st.basis st.basis :=
      ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
    have hfin : st.basis streamLayout.point.finite = false := hp.1
    have z1 := literal_checked read address _ _ _ (Frontier.zrep_step streamLayout hw hn 0 5 0 false st.basis
      (by rw [hfin,Frontier.finFive_val]; rfl))
    have mid := core_checked_false read address streamLayout hw hn rows hc hr 5 0 st.basis Frontier.finFive_ne_zero
    have mid2 := core2_checked_false read address rows hc hr 5 0 st.basis Frontier.finFive_ne_zero
    have z2 := literal_checked read address _ _ _ (Frontier.zrep_step streamLayout hw hn 5 0 0 false st.basis
      (by rw [hfin,Frontier.finFive_val]; rfl))
    have e := checked_run_eq ((z1.seq mid2).seq z2) ((z1.seq mid).seq z2) st values
    refine ⟨?_, fun m => ?_⟩
    · simpa only [generic2,List.append_assoc] using ((z1.seq mid2).seq z2).safe st values
    · simpa only [generic2,generic,List.append_assoc] using e m
  | @some x y hrp =>
    have hfin : st.basis streamLayout.point.finite = true := hp.1
    cases hG : f streamLayout.core.generic with
    | false =>
      have values : PointDialogValues streamLayout x y false st.basis st.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
      have z1 := literal_checked read address _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y false st.basis (by rw [hfin]; simp))
      have mid := core_checked_false read address streamLayout hw hn rows hc hr x y st.basis
        (Frontier.curve_x_ne_zero hrp)
      have mid2 := core2_checked_false read address rows hc hr x y st.basis (Frontier.curve_x_ne_zero hrp)
      have z2 := literal_checked read address _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y false st.basis (by rw [hfin]; simp))
      have e := checked_run_eq ((z1.seq mid2).seq z2) ((z1.seq mid).seq z2) st values
      refine ⟨?_, fun m => ?_⟩
      · simpa only [generic2,List.append_assoc] using ((z1.seq mid2).seq z2).safe st values
      · simpa only [generic2,generic,List.append_assoc] using e m
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hrp hc he.2.1 he.2.2.1 he.2.2.2
      have values : PointDialogValues streamLayout x y true st.basis st.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
      have z1 := literal_checked read address _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y true st.basis (by rw [hfin]; simp))
      have mid := core_checked_true read address streamLayout hw hn rows hc hr x y st.basis den.1 den.2
      have mid2 := core2_checked_true read address rows hc hr x y st.basis den.1 den.2
      have z2 := literal_checked read address _ _ _ (Frontier.zrep_step streamLayout hw hn (genericX x y cx cy)
        (genericX x y cx cy) (genericY x y cx cy) true st.basis (by rw [hfin]; simp))
      have e := checked_run_eq ((z1.seq mid2).seq z2) ((z1.seq mid).seq z2) st values
      refine ⟨?_, fun m => ?_⟩
      · simpa only [generic2,List.append_assoc] using ((z1.seq mid2).seq z2).safe st values
      · simpa only [generic2,generic,List.append_assoc] using e m

end
end ShorECDLP.Entrant.WEXUnlookup
end
