import ShorECDLP.Submission.Entrant.MainA
import ShorECDLP.Submission.Entrant.MainB
import ShorECDLP.Submission.Entrant.StackBase

-- Entrant/FusedCore.lean
section

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

end

-- Entrant/FusedRow.lean
section

/-! The window row with fused constant pairs (`generic2`), its safety and reference
run, and the width-15 body built from it. -/

section
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

def portFused2 : Code 32768 := [.plain scrHead,.masked (WEX.scrInSite probeRows),
    .plain (wLiteral (pointDialogGenericFlag streamLayout))] ++ generic2 probeRows ++
  [.masked scrDSite, .plain WEX.sfxTailF]

def row2 : Code 32768 := [.plain (wLiteral [.X 838])] ++ portFused2 ++
  [.plain (wLiteral [.X 838])]

def rowPre : Code 32768 := [.plain (wLiteral [.X 838]),.plain scrHead,.masked (WEX.scrInSite probeRows),
  .plain (wLiteral (pointDialogGenericFlag streamLayout))]

def rowPost : Code 32768 := [.masked scrDSite,.plain WEX.sfxTailF,.plain (wLiteral [.X 838])]

theorem row_split : row = rowPre ++ (generic streamLayout probeRows ++ rowPost) := by
  simp [row,portFused,rowPre,rowPost]

theorem row2_split : row2 = rowPre ++ (generic2 probeRows ++ rowPost) := by
  simp [row2,portFused2,rowPre,rowPost]

theorem safe_left {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code n) (st : ECDSAAdd.State)
    (h : Safe read address (a ++ b) st) : Safe read address a st := by
  induction a generalizing st with
  | nil => trivial
  | cons x a ih =>
    simp only [List.cons_append,Safe] at h ⊢
    exact ⟨h.1,fun m hm => ih _ (h.2 m hm)⟩

theorem safe_right {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code n) (st : ECDSAAdd.State)
    (h : Safe read address (a ++ b) st) :
    ∀ m, m.length = ECDSAAdd.measurementCount (reference read address a) →
      Safe read address b (ECDSAAdd.run (reference read address a) m st) := by
  induction a generalizing st with
  | nil =>
    intro m _
    simp only [List.nil_append] at h
    simp only [reference_nil, ECDSAAdd.run]
    exact h
  | cons x xs ih =>
    intro m hm
    simp only [List.cons_append,Safe] at h
    rw [reference_cons,ECDSAAdd.measurementCount_append] at hm
    have hx := h.2 (m.take (ECDSAAdd.measurementCount (blockReference read address x)))
      (by simp only [List.length_take]; omega)
    have ht := ih _ hx (m.drop (ECDSAAdd.measurementCount (blockReference read address x)))
      (by simp only [List.length_drop]; omega)
    have hsplit := run_append_records (blockReference read address x) (reference read address xs)
      (m.take (ECDSAAdd.measurementCount (blockReference read address x)))
      (m.drop (ECDSAAdd.measurementCount (blockReference read address x))) st
      (by simp only [List.length_take]; omega)
    rw [List.take_append_drop] at hsplit
    rw [reference_cons,hsplit]
    exact ht

theorem rowPre_reference (read : ConstantBit 32768 → Bool) (address : Nat) :
    reference read address rowPre =
      [.X 838] ++ (specialize (WEX.portPrefixCode4 probeRows) address).instantiate read := by
  have e5 : (specialize (WEX.portPrefixCode4 probeRows) address).instantiate read =
      (specialize scrHead address).instantiate read ++
        (specialize (WEX.scrInSite probeRows).code address).instantiate read ++
        (specialize (wLiteral (n := 32768) (pointDialogGenericFlag streamLayout)) address).instantiate read := by
    simp only [WEX.portPrefixCode4,scrHead,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
      List.append_assoc]
  rw [e5]
  simp only [rowPre,reference_cons,reference_nil,blockReference,Block.code,specialize_literal,
    ECDSAAdd.ShorPort.Tmpl.instantiate_lit,List.append_nil,List.append_assoc]

theorem flags_generic (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    flags streamLayout R (.some hc) true cy streamLayout.core.generic = true →
      R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧ R≠dialogExceptionPoint (.some hc) := by
  classical
  intro hg
  have rd := dialogFlagState_read streamLayout streamLayout_nodup (dialogInfinity true R)
    (dialogDouble true R (.some hc)) (dialogInversePoint true R (.some hc)) (dialogOrdinary true R (.some hc))
    (true && decide (dialogExceptionEnabled (.some hc))) (dialogException true R (.some hc))
    (true && decide (cy≠-cy))
  have he : dialogOrdinary true R (.some hc) = true := rd.2.2.2.1.symm.trans hg
  exact ((dialogOrdinary_true true R (.some hc) (WeierstrassCurve.Affine.Point.some_ne_zero hc)).mp he).2

theorem rowPre_boundary (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s))
    (hroot : s windowRoot = true) (m : List Bool) :
    PointDialogBoundary streamLayout R true (flags streamLayout R (.some hc) true cy)
      (ECDSAAdd.run (reference read address rowPre) m ⟨false,s⟩).basis := by
  have hroot' : (flipInfinity s) windowRoot = true := by
    have hne : (838 : Wire) ≠ windowRoot := by decide
    simpa [flipInfinity,ECDSAAdd.writeBit,hne] using hroot
  have hclean : ∀ w ∈ WEX.scrWires, (⟨false,flipInfinity s⟩ : ECDSAAdd.State).basis w = false :=
    fun w hw => (ECDSAAdd.Arithmetic.regValue_zero _ _).mp hs.clean w (WEX.scrWires_pool w hw)
  have hop := row_opposite read probeRows address hc hr h₁
  have hx : ECDSAAdd.run ([.X 838] : ECDSAAdd.Program) List.nil ⟨false,s⟩ = ⟨false,flipInfinity s⟩ := flip_run _ _
  rw [rowPre_reference,run_zero_append ([.X 838] : ECDSAAdd.Program) _ rfl,hx,
    WEX.portPrefix4_eq3 read probeRows address m ⟨false,flipInfinity s⟩ hroot',
    WEX.portPrefix_run read probeRows address hop m ⟨false,flipInfinity s⟩ hclean]
  have he := prefixCode_equiv read streamLayout streamLayout_widths streamLayout_nodup probeRows address hop
  rw [← he.2 m ⟨false,flipInfinity s⟩,
    referencePrefix_inst read streamLayout streamLayout_widths probeRows address hc hr h₁ h₂ hD hDo]
  exact (prefixS_checked streamLayout streamLayout_widths streamLayout_nodup R hc true ⟨false,flipInfinity s⟩ m hs).2

theorem generic2_records {n} (read : ConstantBit n → Bool) (address : Nat) (rows : Nat → Fin n) :
    ECDSAAdd.measurementCount (reference read address (generic2 rows)) =
      ECDSAAdd.measurementCount (reference read address (generic streamLayout rows)) := by
  rw [reference,reference,(specialize_counts read _ address).2,(specialize_counts read _ address).2]
  have hy := yPair_counts.1
  simp [generic2,core2,recovery2,pairAdd,pairSite,pairArith,generic,core,recovery,constAdd,constSite,erase,
    Block.code,MaskedSite.code,MaskedSite.prefix,literalRecords,wLiteral,ECDSAAdd.measurementCount_append,hy]
  omega

/-- From the row-entry boundary, the fused row is safe and keeps the reference run. -/
theorem row2_facts (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s))
    (hroot : s windowRoot = true) :
    Safe read address row2 ⟨false,s⟩ ∧
      ∀ m, ECDSAAdd.run (reference read address row2) m ⟨false,s⟩ =
        ECDSAAdd.run (reference read address row) m ⟨false,s⟩ := by
  have gen := fun m => generic2_cases read address probeRows R true (flags streamLayout R (.some hc) true cy)
    hc hr (flags_generic R hc) _ (rowPre_boundary read address R hc hr h₁ h₂ hD hDo s hs hroot m)
  constructor
  · have old := row_safe_of_boundary read address R hc hr h₁ h₂ hD hDo s hs hroot
    rw [row_split] at old
    rw [row2_split]
    apply safe_append _ _ _ _ _ (safe_left _ _ _ _ _ old)
    intro m hm
    apply safe_append _ _ _ _ _ (gen m).1
    intro m' hm'
    have hm'' : m'.length = ECDSAAdd.measurementCount (reference read address (generic streamLayout probeRows)) := by
      rw [hm',generic2_records read address probeRows]
    rw [(gen m).2 m']
    exact safe_right _ _ _ _ _ (safe_right _ _ _ _ _ old m hm) m' hm''
  · intro m
    rw [row2_split,row_split,reference_append,reference_append,reference_append,reference_append,
      run_meas_append (reference read address rowPre),run_meas_append (reference read address rowPre),
      run_meas_append (reference read address (generic2 probeRows)),
      run_meas_append (reference read address (generic streamLayout probeRows)),
      (gen m).2,generic2_records read address probeRows]

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

/-- `row_safe` and the reference run of `row`, transported to `row2` at any address. -/
theorem row2_safe_run (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    Safe (readConstant coeffs Q) a row2 ⟨false,s⟩ ∧
      ∀ m, ECDSAAdd.run (reference (readConstant coeffs Q) a row2) m ⟨false,s⟩ =
        ECDSAAdd.run (reference (readConstant coeffs Q) a row) m ⟨false,s⟩ := by
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
    exact row2_facts (readConstant coeffs Q) a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial hs.2.2

/-- The reference run of `row2` at any address. -/
theorem row2_run_any (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (hQ : ShorECDLP.order • Q = 0)
    (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) (s : BasisState) (hs : liveReady s) (m : List Bool) :
    ECDSAAdd.run (reference (readConstant coeffs Q) a row2) m ⟨false,s⟩ =
      ⟨false,pointWrite (inputPoint s + Single.Physical.tablePoint coeffs Q a) s⟩ := by
  rw [(row2_safe_run coeffs Q hQ hn a s hs).2 m]
  have old := clearReferenceRow_run_any a coeffs Q hQ hn s hs m
  rw [specialize_normalize_run] at old
  simpa only [reference,erase_row] using old

/-! ### Geometry of the fused sites -/

def pairWireList : List Wire := (streamLayout.recoveryConstant streamLayout.point.x).wires ++ yPair.wires

def pairTargets : List Wire := List.range' 14115 256 ++ List.range' 15399 256

theorem mem_pairWireList {w : Wire} : w ∈ pairWireList ↔
    w ∈ (streamLayout.recoveryConstant streamLayout.point.x).wires ∨ w ∈ yPair.wires := by
  unfold pairWireList
  exact List.mem_append

theorem wires_append_subset {a b : ECDSAAdd.Program} {la lb : List Wire}
    (ha : ECDSAAdd.wires a ⊆ la.toFinset) (hb : ECDSAAdd.wires b ⊆ lb.toFinset) :
    ECDSAAdd.wires (a ++ b) ⊆ (la ++ lb).toFinset := by
  rw [ECDSAAdd.wires_append,List.toFinset_append]
  exact Finset.union_subset_union ha hb

theorem wires_avoid_of {p : ECDSAAdd.Program} {l S : List Wire} (hs : ECDSAAdd.wires p ⊆ l.toFinset)
    (h : ∀ w ∈ S, w ∉ l) : ∀ w ∈ S, w ∉ ECDSAAdd.wires p :=
  fun w hw hp => h w hw (List.mem_toFinset.mp (hs hp))

theorem wires_avoid_fun {p : ECDSAAdd.Program} {l : List Wire} {f : Fin 128 → Wire}
    (hs : ECDSAAdd.wires p ⊆ l.toFinset) (h : ∀ i, f i ∉ l) : ∀ i, f i ∉ ECDSAAdd.wires p :=
  fun i hp => h i (List.mem_toFinset.mp (hs hp))

theorem wires_within_of {p : ECDSAAdd.Program} {l S : List Wire} (hs : ECDSAAdd.wires p ⊆ l.toFinset)
    (h : ∀ w ∈ l, w ∈ S) : ECDSAAdd.wires p ⊆ S.toFinset :=
  fun w hp => List.mem_toFinset.mpr (h w (List.mem_toFinset.mp (hs hp)))

theorem pairArith_subset : ECDSAAdd.wires pairArith ⊆ pairWireList.toFinset := by
  unfold pairArith pairWireList
  exact wires_append_subset (MeasuredCanonicalModLayout.program_wires_subset _ _ _)
    (MeasuredCanonicalModLayout.program_wires_subset _ _ _)

theorem pairWireList_source : ∀ w ∈ pairWireList, fixedPort w ∨ oldWork w := by
  decide +kernel

theorem pairWireList_window : ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ pairWireList := by
  decide +kernel

theorem pairWireList_hot : ∀ i : Fin 128, hot i ∉ pairWireList := by
  decide +kernel

theorem pairTargets_window :
    ∀ w ∈ windowRoot :: lookupRoot windowRoot (some streamLayout.core.generic) :: windowBits ++ windowPaths,
      w ∉ pairTargets := by
  decide +kernel

theorem pairRoot_nodup : (lookupRoot windowRoot (some streamLayout.core.generic) :: windowBits ++ windowPaths).Nodup := by
  decide +kernel

theorem pairTargets_nodup : pairTargets.Nodup := by
  decide +kernel

theorem pairTargets_source : (∀ w ∈ pairTargets, fixedPort w ∨ oldWork w) ∧
    (fixedPort streamLayout.core.generic ∨ oldWork streamLayout.core.generic) := by
  constructor <;> decide +kernel

theorem pairTargets_hot : ∀ i : Fin 128, hot i ∉ pairTargets := by
  decide +kernel

theorem pairArith_physical : GatePhysical pairArith := by
  intro i hi
  unfold pairArith at hi
  rw [List.mem_append] at hi
  rcases hi with h | h
  · exact MeasuredCanonicalModLayout.physical _ _ _ (List.nodup_cons.mp xConst_nodup).2 i h
  · exact MeasuredCanonicalModLayout.physical _ _ _ (List.nodup_cons.mp yPair_nodup).2 i h

theorem pairSite_code (refsA refsB : Nat → Nat → ConstantBit 32768) :
    (pairSite refsA refsB).code = [WInstr.lookup (some streamLayout.core.generic) (pairSite refsA refsB).ports,
      .literal pairArith,.lookup (some streamLayout.core.generic) (pairSite refsA refsB).ports] := rfl

theorem pairSite_geometry (refsA refsB : Nat → Nat → ConstantBit 32768) :
    SiteGeometry (pairSite refsA refsB) := by
  have ht : portTargets (pairSite refsA refsB).ports = pairTargets := pairSite_targets refsA refsB
  have look : Placed windowBits windowPaths windowRoot
      (WInstr.lookup (n := 32768) (some streamLayout.core.generic) (pairSite refsA refsB).ports) := by
    refine ⟨pairRoot_nodup,?_,?_⟩
    · rw [ht]; exact pairTargets_nodup
    · rw [ht]; intro a ha hb; exact pairTargets_window a ha hb
  refine ⟨?_,?_,Or.inr (Or.inr (Or.inl ⟨pairSite_targets refsA refsB,pairSite_guard refsA refsB⟩))⟩
  · intro i hi
    rw [pairSite_code] at hi
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact look
    · exact wires_avoid_of pairArith_subset pairWireList_window
    · exact look
  · intro i hi
    rw [pairSite_code] at hi
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · intro j hj; rw [ht] at hj; exact pairTargets_hot j hj
    · exact wires_avoid_fun pairArith_subset pairWireList_hot
    · intro j hj; rw [ht] at hj; exact pairTargets_hot j hj

theorem pair_instr_facts (refsA refsB : Nat → Nat → ConstantBit 32768) (i : WInstr 32768)
    (hi : i ∈ (pairSite refsA refsB).code) :
    (∀ p, i = .literal p → GatePhysical p ∧ ECDSAAdd.wires p ⊆ sourceSupport.toFinset) ∧
    (∀ c ps, i = .lookup c ps → (∀ q ∈ c, q ∈ sourceSupport) ∧ portTargets ps ⊆ sourceSupport) := by
  have ht : portTargets (pairSite refsA refsB).ports = pairTargets := pairSite_targets refsA refsB
  rw [pairSite_code] at hi
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
  have lit : GatePhysical pairArith ∧ ECDSAAdd.wires pairArith ⊆ sourceSupport.toFinset :=
    ⟨pairArith_physical,wires_within_of pairArith_subset
      (fun w hw => (sourceSupport_mem w).mpr (pairWireList_source w hw))⟩
  have look : (∀ q ∈ some streamLayout.core.generic, q ∈ sourceSupport) ∧
      portTargets (pairSite refsA refsB).ports ⊆ sourceSupport := by
    refine ⟨fun q hq => ?_,fun w hw => ?_⟩
    · rw [Option.mem_def,Option.some_inj] at hq
      rw [← hq]; exact (sourceSupport_mem _).mpr pairTargets_source.2
    · rw [ht] at hw; exact (sourceSupport_mem w).mpr (pairTargets_source.1 w hw)
  rcases hi with rfl | rfl | rfl
  · exact ⟨fun p h => (by cases h),fun c ps h => (by cases h; exact look)⟩
  · exact ⟨fun p h => (by cases h; exact lit),fun c ps h => (by cases h)⟩
  · exact ⟨fun p h => (by cases h),fun c ps h => (by cases h; exact look)⟩

/-! ### `row2` from the blocks of `row` and two fused sites -/

theorem generic_list : generic streamLayout probeRows =
    [Block.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout)),
     Block.masked (constSite streamLayout streamLayout.point.x (wFields probeRows .negX)),
     Block.masked (constSite streamLayout streamLayout.point.y (wFields probeRows .negY)),
     Block.plain (wLiteral (ECDSAAdd.Frontier.arithS streamLayout false)),
     Block.plain (wLiteral (ECDSAAdd.Frontier.SquareOB5.program streamLayout)),
     Block.masked (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)),
     Block.plain (wLiteral (ECDSAAdd.Frontier.arithS streamLayout true)),
     Block.plain (wLiteral (pointRecoveryReflection streamLayout)),
     Block.masked (constSite streamLayout streamLayout.point.x (wFields probeRows .x)),
     Block.plain (wLiteral (pointDialogConstantAdd streamLayout streamLayout.point.x 1)),
     Block.masked (constSite streamLayout streamLayout.point.y (wFields probeRows .negY)),
     Block.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))] := by
  simp only [generic,core,recovery,constAdd,List.cons_append,List.nil_append,List.singleton_append]

theorem generic2_list : generic2 probeRows =
    [Block.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout)),
     Block.masked (pairSite (wFields probeRows .negX) (wFields probeRows .negY)),
     Block.plain (wLiteral (ECDSAAdd.Frontier.arithS streamLayout false)),
     Block.plain (wLiteral (ECDSAAdd.Frontier.SquareOB5.program streamLayout)),
     Block.masked (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)),
     Block.plain (wLiteral (ECDSAAdd.Frontier.arithS streamLayout true)),
     Block.plain (wLiteral (pointRecoveryReflection streamLayout)),
     Block.plain (wLiteral (pointDialogConstantAdd streamLayout streamLayout.point.x 1)),
     Block.masked (pairSite (wFields probeRows .x) (wFields probeRows .negY)),
     Block.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))] := by
  simp only [generic2,core2,recovery2,pairAdd,constAdd,List.cons_append,List.nil_append,
    List.singleton_append]

theorem row2_blocks (b : Block 32768) (hb : b ∈ row2) : b ∈ row ∨
    b = .masked (pairSite (wFields probeRows .negX) (wFields probeRows .negY)) ∨
    b = .masked (pairSite (wFields probeRows .x) (wFields probeRows .negY)) := by
  rw [row2_split] at hb
  rw [row_split]
  rcases List.mem_append.mp hb with h | h
  · exact Or.inl (List.mem_append_left _ h)
  rcases List.mem_append.mp h with h | h
  · have hg : ∀ c ∈ generic streamLayout probeRows, c ∈ rowPre ++ (generic streamLayout probeRows ++ rowPost) :=
      fun c hc => List.mem_append_right _ (List.mem_append_left _ hc)
    rw [generic2_list] at h
    rw [generic_list] at hg
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (hg _ (by simp only [List.mem_cons,eq_self_iff_true,true_or,or_true]))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hg _ (by simp only [List.mem_cons,eq_self_iff_true,true_or,or_true]))
    · exact Or.inl (hg _ (by simp only [List.mem_cons,eq_self_iff_true,true_or,or_true]))
    · exact Or.inl (hg _ (by simp only [List.mem_cons,eq_self_iff_true,true_or,or_true]))
    · exact Or.inl (hg _ (by simp only [List.mem_cons,eq_self_iff_true,true_or,or_true]))
    · exact Or.inl (hg _ (by simp only [List.mem_cons,eq_self_iff_true,true_or,or_true]))
    · exact Or.inl (hg _ (by simp only [List.mem_cons,eq_self_iff_true,true_or,or_true]))
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (hg _ (by simp only [List.mem_cons,eq_self_iff_true,true_or,or_true]))
  · exact Or.inl (List.mem_append_right _ (List.mem_append_right _ h))

theorem row2_geometry : ∀ b ∈ row2, BlockGeometry b := by
  intro b hb
  rcases row2_blocks b hb with h | rfl | rfl
  · exact row_geometry b h
  · exact pairSite_geometry _ _
  · exact pairSite_geometry _ _

theorem row2_instrs (i : WInstr 32768) (hi : i ∈ erase row2) :
    i ∈ clearReferenceRow probeRows ∨ ∃ refsA refsB, i ∈ (pairSite (n := 32768) refsA refsB).code := by
  obtain ⟨b,hb,hib⟩ := List.mem_flatMap.mp hi
  rcases row2_blocks b hb with h | rfl | rfl
  · left
    rw [← erase_row]
    exact block_mem_erase row b h i hib
  · exact Or.inr ⟨_,_,hib⟩
  · exact Or.inr ⟨_,_,hib⟩

theorem row2_physical : ∀ p, WInstr.literal p ∈ erase row2 → GatePhysical p := by
  intro p hp
  rcases row2_instrs _ hp with h | ⟨a,b,h⟩
  · exact clearReferenceRow_physical p h
  · exact ((pair_instr_facts a b _ h).1 p rfl).1

theorem row2_oldWithin : OldWithin (erase row2) := by
  refine ⟨fun p hp => ?_,fun c ps hp => ?_⟩
  · rcases row2_instrs _ hp with h | ⟨a,b,h⟩
    · exact row_oldWithin.1 p h
    · exact ((pair_instr_facts a b _ h).1 p rfl).2
  · rcases row2_instrs _ hp with h | ⟨a,b,h⟩
    · exact row_oldWithin.2 c ps h
    · exact (pair_instr_facts a b _ h).2 c ps rfl

theorem row2_masks : masks row2 = 5 := rfl

/-! ### Counts of `row2` against `row` -/

theorem lookup_meas15 (ps : List (LookupPort 32768)) :
    lookupMeasurements (portOps ps windowBits windowPaths (lookupRoot windowRoot (some streamLayout.core.generic))) =
      32767 := by
  rw [portOps_measurements ps windowBits windowPaths _ (by simp [windowBits,windowPaths]) pairRoot_nodup]
  decide +kernel

theorem site_toffolis (c : Option Wire) (ps : List (LookupPort 32768)) (p : ECDSAAdd.Program) :
    literalToffolis ([.lookup c ps,.literal p,.lookup c ps] : WCode 32768) = ECDSAAdd.toffoliCount p := by
  simp [literalToffolis]

theorem site_traversals (c : Option Wire) (ps : List (LookupPort 32768)) (p : ECDSAAdd.Program) :
    traversals ([.lookup c ps,.literal p,.lookup c ps] : WCode 32768) = 2 := by
  simp [traversals]

theorem site_slotsum (c : Option Wire) (ps : List (LookupPort 32768)) (p : ECDSAAdd.Program) :
    literalSlotSum ([.lookup c ps,.literal p,.lookup c ps] : WCode 32768) = ECDSAAdd.Challenge.gateSlots p := by
  simp [literalSlotSum]

theorem site_ports (c : Option Wire) (ps : List (LookupPort 32768)) (p : ECDSAAdd.Program) :
    portTotal ([.lookup c ps,.literal p,.lookup c ps] : WCode 32768) = 2 * ps.length := by
  simp only [portTotal]
  omega

theorem site_records (c : Option Wire) (ps : List (LookupPort 32768)) (p : ECDSAAdd.Program) :
    codeRecords windowBits windowPaths windowRoot (normalizeW ([.lookup c ps,.literal p,.lookup c ps] : WCode 32768)) =
      2 * lookupMeasurements (portOps ps windowBits windowPaths (lookupRoot windowRoot c)) +
        ECDSAAdd.measurementCount p := by
  simp only [codeRecords,normalizeW,List.map_cons,List.map_nil,normalizeWInstr,
    ECDSAAdd.Baselines.normalize_measurements]
  omega

theorem constSite_code (r : List Wire) (refs : Nat → Nat → ConstantBit 32768) :
    (constSite streamLayout r refs).code =
      [.lookup (some streamLayout.core.generic) (indexedPorts (streamLayout.recoveryConstant r).src refs true),
        .literal ((streamLayout.recoveryConstant r).program SquareReduction.c ECDSAAdd.p),
        .lookup (some streamLayout.core.generic) (indexedPorts (streamLayout.recoveryConstant r).src refs true)] := rfl

theorem indexed_length {n} (ws : List Wire) (refs : Nat → Nat → ConstantBit n) (v : Bool) :
    (indexedPorts ws refs v).length = ws.length := by
  have h := congrArg List.length (indexed_targets ws refs v)
  simpa [portTargets] using h

theorem const_src_length (r : List Wire) (hr : r.length = 256) :
    (streamLayout.recoveryConstant r).src.length = 256 :=
  (streamLayout.recoveryConstant_widths streamLayout_widths r hr).src

theorem generic2_measures :
    literalToffolis (erase (generic2 probeRows)) = literalToffolis (erase (generic streamLayout probeRows)) ∧
    traversals (erase (generic2 probeRows)) + 4 = traversals (erase (generic streamLayout probeRows)) ∧
    literalSlotSum (erase (generic2 probeRows)) ≤ literalSlotSum (erase (generic streamLayout probeRows)) + 33866 ∧
    portTotal (erase (generic2 probeRows)) = portTotal (erase (generic streamLayout probeRows)) ∧
    codeRecords windowBits windowPaths windowRoot (normalizeW (erase (generic2 probeRows))) + 4 * 32767 =
      codeRecords windowBits windowPaths windowRoot (normalizeW (erase (generic streamLayout probeRows))) := by
  have hy := yPair_counts
  have hs2 := yPair_slots
  have lx := const_src_length streamLayout.point.x streamLayout_widths.inputX
  have ly := const_src_length streamLayout.point.y streamLayout_widths.inputY
  have l2 : pairSrc.length = 256 := by simp [pairSrc]
  have lp : ∀ (refsA refsB : Nat → Nat → ConstantBit 32768), (pairSite refsA refsB).ports.length = 512 := by
    intro refsA refsB
    change (indexedPorts _ refsA true ++ indexedPorts pairSrc refsB true).length = 512
    rw [List.length_append,indexed_length,indexed_length,lx,l2]
  rw [generic2_list,generic_list]
  simp only [erase,List.flatMap_cons,List.flatMap_nil,List.append_nil,Block.code,wLiteral,pairSite_code,
    constSite_code,literalToffolis_append,traversals_append,literalSlotSum_append',portTotal_append',
    normalize_append,records_old_append]
  simp only [site_toffolis,site_traversals,site_slotsum,site_ports,site_records,lookup_meas15,lp,
    indexed_length,lx,ly]
  have ea : ECDSAAdd.toffoliCount pairArith =
      ECDSAAdd.toffoliCount ((streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p) +
        ECDSAAdd.toffoliCount ((streamLayout.recoveryConstant streamLayout.point.y).program SquareReduction.c ECDSAAdd.p) := by
    unfold pairArith; rw [ECDSAAdd.toffoliCount_append,hy.2]
  have eb : ECDSAAdd.measurementCount pairArith =
      ECDSAAdd.measurementCount ((streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p) +
        ECDSAAdd.measurementCount ((streamLayout.recoveryConstant streamLayout.point.y).program SquareReduction.c ECDSAAdd.p) := by
    unfold pairArith; rw [ECDSAAdd.measurementCount_append,hy.1]
  have ec : ECDSAAdd.Challenge.gateSlots pairArith =
      ECDSAAdd.Challenge.gateSlots ((streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p) +
        ECDSAAdd.Challenge.gateSlots (yPair.program SquareReduction.c ECDSAAdd.p) := by
    unfold pairArith; rw [ECDSAAdd.Challenge.gateSlots_append]
  rw [ea,eb,ec]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> omega

theorem lens_generic : lens (generic streamLayout probeRows) = 1280 := by
  rw [lens_shared _ (fun b hb => row3_shared b (by simp [row3,portFused3,hb]))]
  rfl

theorem lens_generic2 : lens (generic2 probeRows) = 1280 := by
  have lx := const_src_length streamLayout.point.x streamLayout_widths.inputX
  have l2 : pairSrc.length = 256 := by simp [pairSrc]
  have lp : ∀ (refsA refsB : Nat → Nat → ConstantBit 32768), (pairSite refsA refsB).ports.length = 512 := by
    intro refsA refsB
    change (indexedPorts _ refsA true ++ indexedPorts pairSrc refsB true).length = 512
    rw [List.length_append,indexed_length,indexed_length,lx,l2]
  have lc : (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).ports.length = 256 := by
    change (indexedPorts _ _ true).length = 256
    rw [indexed_length,lx]
  rw [generic2_list]
  simp only [lens,blockLen,lp,lc]

theorem row2_lens : lens row2 = 2567 := by
  have h := row_lens
  rw [row_split,lens_append,lens_append,lens_generic] at h
  rw [row2_split,lens_append,lens_append,lens_generic2]
  omega

theorem row2_measures :
    literalToffolis (erase row2) = literalToffolis (clearReferenceRow probeRows) ∧
    traversals (erase row2) = 11 ∧
    literalSlotSum (erase row2) ≤ literalSlotSum (clearReferenceRow probeRows) + 33866 ∧
    portTotal (erase row2) = portTotal (clearReferenceRow probeRows) ∧
    codeRecords windowBits windowPaths windowRoot (normalizeW (erase row2)) = 2048404 - 4 * 32767 := by
  have g := generic2_measures
  have ht := WEX.clearReferenceRow_traversals
  have hr := WEX.clearReferenceRow_records
  rw [traversals_normalize] at ht
  rw [← erase_row] at ht hr ⊢
  rw [row2_split,row_split] at *
  simp only [erase_append,literalToffolis_append,traversals_append,literalSlotSum_append',portTotal_append',
    normalize_append,records_old_append] at *
  refine ⟨?_,?_,?_,?_,?_⟩ <;> omega

theorem row2_records : records row2 = 1757978 := by
  have h := records_relation row2 row2_geometry
  rw [row2_masks,row2_lens,row2_measures.2.2.2.2] at h
  omega

theorem row2_slots (start : Nat) : (program row2 start).gateSlots =
    codeSlots windowBits (normalizeW (erase row2)) + 250725868 := by
  have h := program_slots_relation row2 row2_geometry start
  rw [row2_masks,row2_lens] at h
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_wellFormed (start : Nat) : (program row2 start).WellFormed :=
  program_wellFormed row2 row2_geometry row2_physical start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_support (start : Nat) : ChallengeMigration.straightWires (program row2 start) ⊆ logicalSupport :=
  program_support row2 row2_geometry row2_oldWithin start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program row2 start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program_coherent (readConstant coeffs Q) row2 row2_geometry liveReady (rowPointState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs m => row2_run_any _ coeffs Q hQ hn s hs m) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩

def rowSource2 (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode (readConstant coeffs Q) row2

theorem rowSource2_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSource2 coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  obtain ⟨cs,aligned,mass⟩ := row2_coherent coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs,?_,mass⟩
  simpa only [program_run,rowSource2] using aligned

attribute [local irreducible] Straight.instantiate AdaptiveCircuit.tCount AdaptiveCircuit.run
  program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram WEX.codeRecords WEX.codeSlots WEX.literalToffolis
  ECDSAAdd.toffoliCount ECDSAAdd.measurementCount lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps ccx masks

def addFixed2 (start : Nat) : Straight 32768 start (start+1757978) :=
  castFinish (congrArg (fun m => start+m) row2_records) (program row2 start)

theorem addFixed2_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed2 start).instantiate read history).run = (sourceCode read row2).run := by
  rw [addFixed2,castFinish_instantiate,program_run]

theorem addFixed2_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed2 start).instantiate read history).tCount = 7*ccx row2 := by
  rw [addFixed2,castFinish_instantiate,program_tCount read row2 row2_geometry]

theorem addFixed2_slots (start : Nat) : (addFixed2 start).gateSlots =
    codeSlots windowBits (normalizeW (erase row2)) + 250725868 := by
  rw [addFixed2,castFinish_gateSlots,row2_slots]

theorem addFixed2_wellFormed (start : Nat) : (addFixed2 start).WellFormed := by
  rw [addFixed2,castFinish_wellFormed]
  exact row2_wellFormed start

theorem addFixed2_support (start : Nat) : ChallengeMigration.straightWires (addFixed2 start) ⊆ logicalSupport := by
  rw [addFixed2,support_cast]
  exact row2_support start

open AndGadget in
theorem addFixed2_residue (start : Nat) : residue (addFixed2 start) = 0 := by
  rw [addFixed2,residue_cast]
  exact program_residue row2 start

open AndGadget WEXCredit in
theorem addFixed2_credit (start : Nat) : ProgramCredit (addFixed2 start) (ccx row2) := by
  have hz := addFixed2_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed2 start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed2_tCount (fun _ => false) start (fun _ => false)
  omega

end
end ShorECDLP.Entrant.WEXUnlookup
end

namespace ShorECDLP.Entrant.WEXUnlookup.Width15Fused
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program blockProgram clearProgram addFixed2 WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx Nat.add Nat.mul
def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSource2 coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource2_coherent coeffs Q hQ hn)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)
def fastBodyProgram (start : Nat) : Straight 32768 start (start+1758490) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed2 (start+256))).append
      (nFastProgram (start+256+1757978))).append (suffixProgram (start+256+1757978+256)))

attribute [local irreducible] fastBodyProgram

theorem fastBodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode read row2)).seq fastSignSource)).seq suffixSource).run := by
  rw [fastBodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource fastSignSource (sourceCode read row2) fastSignSource suffixSource
    (prefixProgram_run _ read) (nFastProgram_run _ read) (addFixed2_run read _)
    (nFastProgram_run _ read) (suffixProgram_run _ read) history

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode (readConstant coeffs Q) row2)).seq fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSource2
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
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1757978)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row2) (prefix_credit start) hl (addFixed2_credit (start+256)) hr
    (suffix_credit (start+256+1757978+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
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
      · exact addFixed2_wellFormed _
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
    addFixed2_support _⟩,(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,addFixed2_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (erase row2))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.row2_measures
  have hl2 := hm.2.2.1
  rw [← hm.2.2.2.1] at hp
  rw [hm.2.1] at hc
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  norm_num [windowBits] at hc
  simp only [windowBits]
  omega
def fastCompactProgram (start : Nat) : Straight 32768 start (start+1758490) :=
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

theorem row2_ccx_upper : ccx row2 ≤ 2361904 := by
  have h := ccx_relation row2
  have hn := WEX.literalToffolis_normalize (erase row2)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis,h0]
  rw [WEXUnlookup.row2_masks,WEXUnlookup.row2_measures.2.1] at h
  rw [WEXUnlookup.row2_measures.1,hrow] at hn
  omega

theorem fastCount_upper : 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    ccx row2 ≤ 2362408 := by
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := row2_ccx_upper
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 15 where
  records := 1758490
  tBound := 16536856
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2
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
end ShorECDLP.Entrant.WEXUnlookup.Width15Fused

end

-- Entrant/FusedRow14.lean
section

/-! The fused row at physical width 14. -/

section
namespace ShorECDLP.Entrant.WEXUnlookupWidth14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem pairRoot_nodup14 :
    (lookupRoot windowRoot (some streamLayout.core.generic) :: bits ++ windowPaths).Nodup := by
  decide +kernel

theorem pairTargets_window14 :
    ∀ w ∈ windowRoot :: lookupRoot windowRoot (some streamLayout.core.generic) :: bits ++ windowPaths,
      w ∉ pairTargets := by
  decide +kernel

theorem pairWireList_window14 : ∀ w ∈ windowRoot :: bits ++ windowPaths, w ∉ pairWireList := by
  decide +kernel

theorem pairSite_placed14 (refsA refsB : Nat → Nat → ConstantBit 32768) :
    ∀ i ∈ (pairSite refsA refsB).code, Placed bits windowPaths windowRoot i := by
  have ht : portTargets (pairSite refsA refsB).ports = pairTargets := pairSite_targets refsA refsB
  have look : Placed bits windowPaths windowRoot
      (WInstr.lookup (n := 32768) (some streamLayout.core.generic) (pairSite refsA refsB).ports) := by
    refine ⟨pairRoot_nodup14,?_,?_⟩
    · rw [ht]; exact pairTargets_nodup
    · rw [ht]; intro a ha hb; exact pairTargets_window14 a ha hb
  intro i hi
  rw [pairSite_code] at hi
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact look
  · exact wires_avoid_of pairArith_subset pairWireList_window14
  · exact look

theorem row2_geometry : ∀ b ∈ row2, BlockGeometry b := by
  intro b hb
  rcases row2_blocks b hb with h | rfl | rfl
  · exact row_geometry b h
  · exact ⟨pairSite_geometry _ _,pairSite_placed14 _ _,(pairSite_geometry _ _).bank⟩
  · exact ⟨pairSite_geometry _ _,pairSite_placed14 _ _,(pairSite_geometry _ _).bank⟩

theorem row2_masks14 : masks row2 = 5 := rfl

theorem lookup_meas14 (ps : List (LookupPort 32768)) :
    lookupMeasurements (portOps ps bits windowPaths (lookupRoot windowRoot (some streamLayout.core.generic))) =
      16383 := by
  rw [portOps_measurements ps bits windowPaths _ (by simp [bits,WEX.widthBits,windowPaths]) pairRoot_nodup14]
  decide +kernel

theorem site3_records14 (c : Option Wire) (ps : List (LookupPort 32768)) (p : ECDSAAdd.Program) :
    codeRecords bits windowPaths windowRoot (normalizeW ([.lookup c ps,.literal p,.lookup c ps] : WCode 32768)) =
      2 * lookupMeasurements (portOps ps bits windowPaths (lookupRoot windowRoot c)) +
        ECDSAAdd.measurementCount p := by
  simp only [codeRecords,normalizeW,List.map_cons,List.map_nil,normalizeWInstr,
    ECDSAAdd.Baselines.normalize_measurements]
  omega

theorem generic2_records14 :
    codeRecords bits windowPaths windowRoot (normalizeW (erase (generic2 probeRows))) + 4 * 16383 =
      codeRecords bits windowPaths windowRoot (normalizeW (erase (generic streamLayout probeRows))) := by
  have hy := yPair_counts
  rw [generic2_list,generic_list]
  simp only [erase,List.flatMap_cons,List.flatMap_nil,List.append_nil,Block.code,wLiteral,pairSite_code,
    constSite_code,normalize_append,records_old_append]
  simp only [site3_records14,lookup_meas14]
  have eb : ECDSAAdd.measurementCount pairArith =
      ECDSAAdd.measurementCount ((streamLayout.recoveryConstant streamLayout.point.x).program SquareReduction.c ECDSAAdd.p) +
        ECDSAAdd.measurementCount ((streamLayout.recoveryConstant streamLayout.point.y).program SquareReduction.c ECDSAAdd.p) := by
    unfold pairArith; rw [ECDSAAdd.measurementCount_append,hy.1]
  rw [eb]
  omega

theorem row2_records_code14 :
    codeRecords bits windowPaths windowRoot (normalizeW (erase row2)) = 1802644 - 4 * 16383 := by
  have g := generic2_records14
  have h := WEX.clearReferenceRow_width_records 14 (by omega)
  have hn : 1556899 + 15 * (2 ^ 14 - 1) = 1802644 := by norm_num
  have hr : codeRecords bits windowPaths windowRoot (normalizeW (clearReferenceRow probeRows)) = 1802644 := by
    simpa only [bits] using h.trans hn
  rw [← erase_row] at hr
  rw [row2_split,row_split] at *
  simp only [erase_append,normalize_append,records_old_append] at *
  omega

theorem row2_records : records row2 = 1659034 := by
  have h := records_relation row2 row2_geometry
  rw [row2_masks14,WEXUnlookup.row2_lens,row2_records_code14] at h
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx Nat.add Nat.mul in
theorem row2_ccx_upper : ccx row2 ≤ 2262960 := by
  have h := ccx_relation row2
  have hn := WEX.literalToffolis_normalize (erase row2)
  have hc := (finite23_literal_counts streamLayout probeRows).1.trans
    (tight_finite_literal_counts streamLayout streamLayout_widths streamLayout_nodup probeRows).1
  have hrow : literalToffolis (clearReferenceRow probeRows) = 2163392 := by
    have h0 : literalToffolis (rowAddCode probeRows) = 2161857 := by
      simp only [rowAddCode,literalToffolis_append,wLiteral,literalToffolis,ECDSAAdd.toffoliCount,
        Nat.zero_add,Nat.add_zero,hc]
    rw [WEX.clearReferenceRow_literalToffolis,h0]
  rw [row2_masks14,WEXUnlookup.row2_measures.2.1] at h
  rw [WEXUnlookup.row2_measures.1,hrow] at hn
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_wellFormed (start : Nat) : (program row2 start).WellFormed :=
  program_wellFormed row2 row2_geometry row2_physical start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_support (start : Nat) : ChallengeMigration.straightWires (program row2 start) ⊆ logicalSupport :=
  program_support row2 row2_geometry row2_oldWithin start

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_slots_upper (start : Nat) : (program row2 start).gateSlots ≤ 1000000000 := by
  have h := program_slots_upper row2 row2_geometry start
  rw [row2_masks14] at h
  have hc := WEX.codeSlots_bound bits (normalizeW (erase row2))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.row2_measures
  have hl2 := hm.2.2.1
  rw [← hm.2.2.2.1] at hp
  rw [hm.2.1] at hc
  have hlen : bits.length = 14 := by simp [bits,WEX.widthBits]
  rw [hlen] at hc
  norm_num at hc
  omega

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in
theorem row2_coherent (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program row2 start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (rowState coeffs Q))
      (fun s => liveReady s ∧ MeasuredClear.HotClean hot s) := by
  have h := program_coherent (readConstant coeffs Q) row2 row2_geometry liveReady (rowState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1) (by
      intro s hs m
      simpa only [rowState] using row2_run_any (tableAddressValue bits s) coeffs Q hQ hn s hs m) start history
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  exact hb s ⟨fun w hw => hs.1.2.1 w (List.mem_append_right _ hw),hs.1.2.2,hs.2,hs.1⟩

def rowSource2 (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCode (readConstant coeffs Q) row2

theorem rowSource2_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (rowSource2 coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := row2_coherent coeffs Q hQ hn 0 Fin.elim0
  have he : rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold rowState rowPointState
    rw [show tableAddressValue bits s = tableAddressValue (WEX.widthBits 14) s from rfl,
      WEX.width_table 14 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  simpa only [program_run,rowSource2,LiveReady] using aligned

attribute [local irreducible] program blockProgram clearProgram WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  lookupMeasurements WEX.portOps tableAddressTree MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  MeasuredClear.measuredClear ccx Nat.add Nat.mul

def addFixed2 (start : Nat) : Straight 32768 start (start+1659034) :=
  castFinish (congrArg (fun m => start+m) row2_records) (program row2 start)

attribute [local irreducible] addFixed2

theorem addFixed2_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed2 start).instantiate read history).run = (sourceCode read row2).run := by
  rw [addFixed2,castFinish_instantiate,program_run]

theorem addFixed2_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixed2 start).instantiate read history).tCount = 7*ccx row2 := by
  rw [addFixed2,castFinish_instantiate,program_tCount read row2 row2_geometry]

theorem addFixed2_wellFormed (start : Nat) : (addFixed2 start).WellFormed := by
  rw [addFixed2,castFinish_wellFormed]
  exact row2_wellFormed start

theorem addFixed2_support (start : Nat) : ChallengeMigration.straightWires (addFixed2 start) ⊆ logicalSupport := by
  rw [addFixed2,support_cast]
  exact row2_support start

theorem addFixed2_residue (start : Nat) : residue (addFixed2 start) = 0 := by
  rw [addFixed2,residue_cast]
  exact program_residue row2 start

theorem addFixed2_credit (start : Nat) : ProgramCredit (addFixed2 start) (ccx row2) := by
  have hz := addFixed2_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixed2 start) hz (fun _ => false) (fun _ => false)
  have ht := addFixed2_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixed2_slots_upper (start : Nat) : (addFixed2 start).gateSlots ≤ 1000000000 := by
  rw [addFixed2,castFinish_gateSlots]
  exact row2_slots_upper start

end
end ShorECDLP.Entrant.WEXUnlookupWidth14
end

namespace ShorECDLP.Entrant.WEXUnlookupWidth14.Fused
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible WEXUnlookupWidth14
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program blockProgram clearProgram addFixed2 WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookup.compactBody ccx Nat.add Nat.mul
def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSource2 coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSource2_coherent coeffs Q hQ hn halias)
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
def fastBodyProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixed2 (start+256))).append
      (nFastProgram (start+256+1659034))).append (suffixProgram (start+256+1659034+256)))

attribute [local irreducible] fastBodyProgram

theorem fastBodyProgram_run_read (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode read row2)).seq fastSignSource)).seq suffixSource).run := by
  rw [fastBodyProgram,castFinish_instantiate]
  exact five_run read _ _ _ _ _ prefixSource fastSignSource (sourceCode read row2) fastSignSource suffixSource
    (prefixProgram_run _ read) (nFastProgram_run _ read) (addFixed2_run read _)
    (nFastProgram_run _ read) (suffixProgram_run _ read) history

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCode (readConstant coeffs Q) row2)).seq fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSource2
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
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1659034)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row2) (prefix_credit start) hl (addFixed2_credit (start+256)) hr
    (suffix_credit (start+256+1659034+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
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
      · exact addFixed2_wellFormed _
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
    addFixed2_support _⟩,(nFastProgram_source _).trans (List.subset_append_left _ _)⟩,(hs _).trans (List.subset_append_left _ _)⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := addFixed2_slots_upper (start+256)
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  omega
def fastCompactProgram (start : Nat) : Straight 32768 start (start+1659546) :=
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
    ccx row2 ≤ 2263464 := by
  have hs := WEX.fastWindowSign_normalized_counts.1
  have hr := WEXUnlookupWidth14.row2_ccx_upper
  omega

def fastNarrow : ModNarrow WEXUnlookup.compactBody 14 where
  records := 1659546
  tBound := 15844248
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2
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
end ShorECDLP.Entrant.WEXUnlookupWidth14.Fused

end

-- Entrant/PathShare.lean
section

/-! Lookup paths on idle dialog-pool wires.

The window lookups used a private bank of fifteen path wires. Those wires are idle while the
field arithmetic runs, and the dialog pool has wires that only the plain generic-branch arithmetic
uses, which starts and ends with a clean pool. This module compiles the same rows with such pool
wires as the lookup path bank.

The compile layer of `StackBase` asks every literal segment to avoid the path bank. Here a literal
segment only has to keep the root and the address bits. In exchange, the simulation asks for clean
paths before every lookup of the reference run (`PathsClean`), and the block layer asks for a clean
bank at the start of every masked site (`CodeClean`). Inside a masked site every instruction still
avoids the bank, so the bank stays clean through the load, the arithmetic and the measured clear. -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ### Straight code with a shared path bank -/

/-- Literal segments may use the path bank; only the root and the address bits are frozen. -/
def LPlaced {n : Nat} (bits paths : List Wire) (root : Wire) : WInstr n → Prop
  | .literal p => ∀ w ∈ root :: bits, w ∉ ECDSAAdd.wires p
  | .lookup ctl ports => PlacedPair bits paths root (.lookup ctl ports)

def AddrValid (bits : List Wire) (root address : Nat) (st : ECDSAAdd.State) : Prop :=
  tableAddressValue bits st.basis = address ∧ st.basis root = true

/-- The path bank is clean before every lookup of the reference run. -/
def PathsClean {n : Nat} (read : ConstantBit n → Bool) (paths : List Wire) (address : Nat) :
    WCode n → ECDSAAdd.State → Prop
  | [], _ => True
  | .literal p :: code, st => ∀ m, PathsClean read paths address code (ECDSAAdd.run p m st)
  | .lookup c ps :: code, st => Clean paths st.basis ∧
      ∀ m, PathsClean read paths address code
        (ECDSAAdd.run ((portTemplate c ps address).instantiate read) m st)

theorem literal_addr {n : Nat} (p : ECDSAAdd.Program) (bits paths : List Wire) (root address : Nat)
    (hp : LPlaced (n := n) bits paths root (.literal p))
    (st : ECDSAAdd.State) (hs : AddrValid bits root address st) (m : List Bool) :
    AddrValid bits root address (ECDSAAdd.run p m st) := by
  have frame (w : Wire) (hw : w ∈ root :: bits) :
      (ECDSAAdd.run p m st).basis w = st.basis w :=
    ECDSAAdd.run_preserves_outside p m st w (hp w hw)
  refine ⟨?_, ?_⟩
  · rw [WEX.tableAddressValue_congr bits _ _ (fun w hw => frame w (by simp [hw]))]
    exact hs.1
  · rw [frame root (by simp)]
    exact hs.2

theorem pair_lookup_addr {n : Nat} (read : ConstantBit n → Bool)
    (control : Option Wire) (ports : List (LookupPort n)) (bits paths : List Wire)
    (root address : Nat) (hp : PlacedPair bits paths root (.lookup control ports))
    (st : ECDSAAdd.State) (hs : AddrValid bits root address st) :
    AddrValid bits root address
      ⟨st.phase, tableXorState (portMask read (ports.drop 258) address)
        (st.basis (lookupRoot root control))
        (tableXorState (portMask read (ports.take 258) address)
          (st.basis (lookupRoot root control)) st.basis)⟩ := by
  dsimp only [PlacedPair] at hp
  have frame (w : Wire) (hw : w ∈ root :: bits) :
      tableXorState (portMask read (ports.drop 258) address) (st.basis (lookupRoot root control))
        (tableXorState (portMask read (ports.take 258) address) (st.basis (lookupRoot root control)) st.basis) w =
        st.basis w := by
    have hd (v : Wire) (h : v ∈ portTargets ports) : v ≠ w := by
      intro e; subst v
      exact List.disjoint_left.mp hp.2.2.2 (by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hw))) h
    have htake : w ∉ portMask read (ports.take 258) address := by
      intro h
      have h' := tableBitsMask_subset _ _ h
      rw [portTargets, List.map_take] at h'
      exact hd w (List.take_subset _ _ h') rfl
    have hdrop : w ∉ portMask read (ports.drop 258) address := by
      intro h
      have h' := tableBitsMask_subset _ _ h
      rw [portTargets, List.map_drop] at h'
      exact hd w (List.drop_subset _ _ h') rfl
    rw [tableXorState_outside _ _ _ _ hdrop, tableXorState_outside _ _ _ _ htake]
  refine ⟨?_, ?_⟩
  · rw [WEX.tableAddressValue_congr bits _ _ (fun w hw => frame w (by simp [hw]))]
    exact hs.1
  · exact (frame root (by simp)).trans hs.2

def LBranch {n : Nat} (read : ConstantBit n → Bool) (code : WCode n)
    (bits paths : List Wire) (root : Wire) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords code ∧
    ∀ address st, AddrValid bits root address st → PathsClean read paths address code st →
      b.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize code address).instantiate read) m st)

/-- `pair_source_simulation` with path-sharing literals: one coefficient list for every address. -/
theorem lsource_simulation {n : Nat} (read : ConstantBit n → Bool)
    (bits paths : List Wire) (root : Wire) (hl : bits.length ≤ paths.length) (code : WCode n)
    (hp : ∀ i ∈ code, LPlaced bits paths root i) :
    ∃ cs : List ℂ, List.Forall₂ (LBranch read code bits paths root)
      (source read bits paths root code).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    refine ⟨[], rfl, ?_⟩
    intro address st _ _
    simp [specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]
  | cons i code ih =>
    have htail := ih (fun j hj => hp j (List.mem_cons_of_mem _ hj))
    obtain ⟨tailCs, tailAligned, tailMass⟩ := htail
    have hi := hp i (by simp)
    cases i with
    | literal p =>
      obtain ⟨cs, aligned, mass⟩ := literal_simulation p
      refine ⟨coherentSeqCoefficients cs tailCs, ?_, ?_⟩
      · rw [source, AdaptiveCircuit.run_seq]
        apply simulationAligned_seq aligned tailAligned
        intro b₁ c₁ b₂ c₂ h₁ h₂
        obtain ⟨m₂, hm₂, h₂⟩ := h₂
        refine ⟨b₁.history ++ m₂, ?_, ?_⟩
        · simp [literalRecords, List.length_append, h₁.1, hm₂]
        · intro address st hs hc
          have hc' : ∀ m, PathsClean read paths address code (ECDSAAdd.run p m st) := hc
          change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
          rw [h₁.2 st, map_smul,
            h₂ address (ECDSAAdd.run p b₁.history st)
              (literal_addr p bits paths root address hi st hs b₁.history) (hc' b₁.history)]
          simp only [specialize, List.flatMap_cons, WInstr.specialize,
            ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
          rw [run_append_records _ _ _ _ _ h₁.1]
          simp [smul_smul]
      · rw [simulationCoefficients_mass, mass, tailMass]
        norm_num
    | lookup control ports =>
      have hpp : PlacedPair bits paths root (.lookup control ports : WInstr n) := hi
      have hi' := hpp
      dsimp only [PlacedPair] at hi'
      have hsep : (lookupRoot root control :: bits ++ paths).Disjoint (portTargets ports) := by
        apply List.disjoint_left.mpr
        intro w hw hm
        exact List.disjoint_left.mp hi'.2.2.2 (List.mem_cons_of_mem root hw) hm
      have hlookup := pairPort_source_state read ports bits paths (lookupRoot root control)
        hl hi'.1 hi'.2.1 hi'.2.2.1 hsep
      obtain ⟨cs, aligned, mass⟩ := hlookup
      refine ⟨coherentSeqCoefficients cs tailCs, ?_, ?_⟩
      · rw [source, AdaptiveCircuit.run_seq]
        apply simulationAligned_seq aligned tailAligned
        intro b₁ c₁ b₂ c₂ h₁ h₂
        obtain ⟨m₂, hm₂, h₂⟩ := h₂
        refine ⟨m₂, hm₂, ?_⟩
        intro address st hs hc
        have hc' : Clean paths st.basis ∧ ∀ m, PathsClean read paths address code
            (ECDSAAdd.run ((portTemplate control ports address).instantiate read) m st) := hc
        let next : ECDSAAdd.State := ⟨st.phase,
          tableXorState (portMask read (ports.drop 258) address) (st.basis (lookupRoot root control))
            (tableXorState (portMask read (ports.take 258) address) (st.basis (lookupRoot root control)) st.basis)⟩
        have hqa : lookupRoot root control ∉ portTargets (ports.take 258) := by
          intro hm; apply List.disjoint_left.mp hsep (show lookupRoot root control ∈ lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_take] at hm
          exact List.take_subset _ _ hm
        have hqb : lookupRoot root control ∉ portTargets (ports.drop 258) := by
          intro hm; apply List.disjoint_left.mp hsep (show lookupRoot root control ∈ lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_drop] at hm
          exact List.drop_subset _ _ hm
        have hra : root ∉ portTargets (ports.take 258) := by
          intro hm; apply List.disjoint_left.mp hi'.2.2.2 (show root ∈ root :: lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_take] at hm
          exact List.take_subset _ _ hm
        have hspec := pairPort_specialize_run_control read control (ports.take 258) (ports.drop 258)
          address root ([] : List Bool) st hi'.2.1 hi'.2.2.1 hqa hqb hra hs.2
        rw [List.take_append_drop] at hspec
        have hnext : PathsClean read paths address code next := by
          have h := hc'.2 []
          rw [hspec] at h
          exact h
        have step : b₁.kraus (Bridge.signedKet st) = c₁ • Bridge.signedKet next := by
          have hstep : b₁.kraus (ket st.basis) = c₁ • ket next.basis := by
            simpa [ket, next, hs.1] using h₁ st.basis hc'.1
          simp only [Bridge.signedKet, map_smul, hstep]
          simp [next, smul_smul, mul_comm]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [step, map_smul, h₂ address next
          (pair_lookup_addr read control ports bits paths root address hpp st hs) hnext]
        simp only [specialize, List.flatMap_cons, WInstr.specialize,
          ECDSAAdd.ShorPort.Tmpl.instantiate_append]
        rw [ECDSAAdd.run_append, (portTemplate_counts read control ports address).2,
          List.take_zero, List.drop_zero, hspec]
        simp [next, smul_smul]
      · rw [simulationCoefficients_mass, mass, tailMass]
        norm_num

/-- Strictly placed code keeps the address, the root and a clean bank on every reference record. -/
theorem strict_preserves {n} (read : ConstantBit n → Bool) (bits paths : List Wire) (code : WCode n)
    (a : Nat) (hp : ∀ i ∈ code, PlacedPair bits paths windowRoot i)
    (st : ECDSAAdd.State) (hs : SimulationValid bits paths windowRoot a st) (m : List Bool) :
    SimulationValid bits paths windowRoot a (ECDSAAdd.run ((specialize code a).instantiate read) m st) := by
  induction code generalizing st m with
  | nil => simpa [specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run] using hs
  | cons i code ih =>
    have ht := fun j hj => hp j (List.mem_cons_of_mem i hj)
    have hi := hp i (by simp)
    simp only [specialize,List.flatMap_cons,ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.run_append]
    cases i with
    | literal p =>
      simp only [WInstr.specialize,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      apply ih ht
      have hip : Placed bits paths windowRoot (.literal p : WInstr n) := by
        simpa only [Placed, PlacedPair] using hi
      exact literal_preserves_simulation (n := n) p _ _ _ _ hip st hs _
    | lookup control ps =>
      have hip := hi
      dsimp only [PlacedPair] at hip
      have hmemq : lookupRoot windowRoot control ∈ windowRoot :: lookupRoot windowRoot control :: bits ++ paths := by simp
      have hmemr : windowRoot ∈ windowRoot :: lookupRoot windowRoot control :: bits ++ paths := by simp
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
      apply ih ht
      exact pair_lookup_preserves_simulation read control ps _ _ _ _ hi st hs

/-- Strictly placed code needs only a clean bank at its start. -/
theorem strict_pathsClean {n} (read : ConstantBit n → Bool) (bits paths : List Wire) (code : WCode n)
    (a : Nat) (hp : ∀ i ∈ code, PlacedPair bits paths windowRoot i)
    (st : ECDSAAdd.State) (hs : SimulationValid bits paths windowRoot a st) :
    PathsClean read paths a code st := by
  induction code generalizing st with
  | nil => trivial
  | cons i code ih =>
    have ht := fun j hj => hp j (List.mem_cons_of_mem i hj)
    have hi := hp i (by simp)
    cases i with
    | literal p =>
      intro m
      have hip : Placed bits paths windowRoot (.literal p : WInstr n) := by
        simpa only [Placed, PlacedPair] using hi
      exact ih ht _ (literal_preserves_simulation (n := n) p _ _ _ _ hip st hs m)
    | lookup control ps =>
      refine ⟨hs.1, fun m => ?_⟩
      have h := strict_preserves read bits paths ([.lookup control ps] : WCode n) a
        (fun j hj => by rw [List.mem_singleton.mp hj]; exact hi) st hs m
      simp only [specialize, List.flatMap_cons, List.flatMap_nil, List.append_nil, WInstr.specialize] at h
      exact ih ht _ h

/-- Literal-only code has no lookup, so it needs no clean bank. -/
def LitAvoid {n} (bits : List Wire) (code : WCode n) : Prop :=
  ∀ i ∈ code, ∃ p, i = .literal p ∧ ∀ w ∈ windowRoot :: bits, w ∉ ECDSAAdd.wires p

theorem litAvoid_pathsClean {n} (read : ConstantBit n → Bool) (bits paths : List Wire) (code : WCode n)
    (a : Nat) (h : LitAvoid bits code) (st : ECDSAAdd.State) : PathsClean read paths a code st := by
  induction code generalizing st with
  | nil => trivial
  | cons i code ih =>
    obtain ⟨p, rfl, -⟩ := h i (by simp)
    intro m
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

theorem litAvoid_placed {n} (bits paths : List Wire) (code : WCode n) (h : LitAvoid bits code) :
    ∀ i ∈ code, LPlaced bits paths windowRoot i := by
  intro i hi
  obtain ⟨p, rfl, hp⟩ := h i hi
  exact hp

theorem litAvoid_addr {n} (read : ConstantBit n → Bool) (bits : List Wire) (code : WCode n) (a : Nat)
    (h : LitAvoid bits code) (st : ECDSAAdd.State) (hs : AddrValid bits windowRoot a st) (m : List Bool) :
    AddrValid bits windowRoot a (ECDSAAdd.run ((specialize code a).instantiate read) m st) := by
  induction code generalizing st m with
  | nil => simpa [specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run] using hs
  | cons i code ih =>
    obtain ⟨p, rfl, hp⟩ := h i (by simp)
    simp only [specialize,List.flatMap_cons,ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.run_append,
      WInstr.specialize,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _
      (literal_addr (n := n) p bits ([] : List Wire) windowRoot a hp st hs _) _

/-! ### Measured clear on a pool path bank -/

theorem clear_coherent_bank {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hk : SiteKind site)
    (bitsW H P : List Wire)
    (hsplit : ∀ s : BasisState, 128 * (tableAddressTree H 0 1).routeLabel s + MeasuredClear.hotAddress low s =
      tableAddressValue bitsW s)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 871) (hP : ∀ w ∈ P, 871 ≤ w ∧ w ∉ portTargets site.ports)
    (hPg : site.guard ∉ P) (hindex : (tableAddressTree H 0 1).indexWires.dedup = H)
    (hnd : (H ++ P).Nodup) (hhl : H.length ≤ P.length)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((MeasuredClear.measuredClear (clearData site.ports) low (clearHot site)
        (tableAddressTree H 0 1) site.guard (scratch site) P start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => Clean P s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue bitsW s)) = p.value))) := by
  obtain ⟨hn,hbd,hhot,hmem,hsm,hg,-⟩ := kind_facts site hk
  have hgl : site.guard < 14115 := by rcases hg with e | e <;> rw [e] <;> decide
  have notT : ∀ w ∈ site.guard :: List.ofFn low ++ H ++ P, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with ((h | h) | h) | h
    · rw [h] at h2; dsimp only [Wire] at *; omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      have := low_lt i
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
      exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) (hmem i))
    (by
      rw [hindex]
      intro hm
      exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) hsm)
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
  simpa [MeasuredClear.LoadedClear,clearData,hsplit] using hs.2 q hq

end
end ShorECDLP.Entrant.PathShare

/-! ### Blocks compiled on a bank -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Address bits, high clear bits, the clear's path bank and the lookup path bank. -/
structure Bank where
  bits : List Wire
  high : List Wire
  hp : List Wire
  paths : List Wire

structure BankOK (B : Bank) : Prop where
  split : ∀ s : BasisState, 128 * (tableAddressTree B.high 0 1).routeLabel s + MeasuredClear.hotAddress low s =
    tableAddressValue B.bits s
  high : ∀ w ∈ B.high, 862 ≤ w ∧ w < 871
  index : (tableAddressTree B.high 0 1).indexWires.dedup = B.high
  nodup : (B.high ++ B.hp).Nodup
  len : B.high.length ≤ B.hp.length
  sub : ∀ w ∈ B.hp, w ∈ B.paths
  out : ∀ w ∈ B.hp, 871 ≤ w
  bitsLen : B.bits.length ≤ B.paths.length

def clearP {n} (B : Bank) (site : MaskedSite n) (start : Nat) :=
  MeasuredClear.measuredClear (clearData site.ports) low (clearHot site) (tableAddressTree B.high 0 1)
    site.guard (scratch site) B.hp start

def clearSourceP {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) : AdaptiveCircuit :=
  (clearP B site 0).instantiate read Fin.elim0

theorem clearP_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (start : Nat) (history : Fin start → Bool) :
    ((clearP B site start).instantiate read history).run = (clearSourceP B read site).run := by
  simp only [clearP,clearSourceP,MeasuredClear.measuredClear_run]

def blockRecP {n} (B : Bank) : Block n → Nat
  | .plain code => codeRecords B.bits B.paths windowRoot (normalizeW code)
  | .masked site => codeRecords B.bits B.paths windowRoot (normalizeW site.prefix) +
      site.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) site.guard B.hp)+127)

def blockProgP {n} (B : Bank) (b : Block n) (start : Nat) : Straight n start (start+blockRecP B b) :=
  match b with
  | .plain code => compile B.bits B.paths windowRoot (normalizeW code) start
  | .masked site => castFinish (by simp [blockRecP,clearData]; omega)
      ((compile B.bits B.paths windowRoot (normalizeW site.prefix) start).append
        (clearP B site (start+codeRecords B.bits B.paths windowRoot (normalizeW site.prefix))))

def recordsP {n} (B : Bank) : Code n → Nat
  | [] => 0
  | b::code => blockRecP B b + recordsP B code

def programP {n} (B : Bank) : (code : Code n) → (start : Nat) → Straight n start (start+recordsP B code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [recordsP]; omega)
      ((blockProgP B b start).append (programP B code (start+blockRecP B b)))

def blockSourceP {n} (B : Bank) (read : ConstantBit n → Bool) : Block n → AdaptiveCircuit
  | .plain code => source read B.bits B.paths windowRoot (normalizeW code)
  | .masked site => (source read B.bits B.paths windowRoot (normalizeW site.prefix)).seq
      (clearSourceP B read site)

def sourceCodeP {n} (B : Bank) (read : ConstantBit n → Bool) : Code n → AdaptiveCircuit
  | [] => .done
  | b::code => (blockSourceP B read b).seq (sourceCodeP B read code)

theorem blockProgP_run {n} (B : Bank) (read : ConstantBit n → Bool) (b : Block n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgP B b start).instantiate read history).run = (blockSourceP B read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | masked site =>
    rw [blockProgP,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearP_run B read site _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSourceP,AdaptiveCircuit.run_seq]

theorem programP_run {n} (B : Bank) (read : ConstantBit n → Bool) (code : Code n)
    (start : Nat) (history : Fin start → Bool) :
    ((programP B code start).instantiate read history).run = (sourceCodeP B read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [programP,castFinish_instantiate,append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,blockProgP_run]
    simp only [sourceCodeP,AdaptiveCircuit.run_seq]

structure SiteGeoP {n} (B : Bank) (site : MaskedSite n) : Prop where
  placed : ∀ i ∈ site.code, Placed B.bits B.paths windowRoot i
  kind : SiteKind site

/-- Plain blocks are literal and keep root and address; masked sites avoid the whole bank. -/
def BlockGeoP {n} (B : Bank) : Block n → Prop
  | .plain code => LitAvoid B.bits code
  | .masked site => SiteGeoP B site

def BlockClean {n} (P : List Wire) : Block n → ECDSAAdd.State → Prop
  | .plain _, _ => True
  | .masked _, st => Clean P st.basis

/-- The bank is clean at the start of every masked site of the reference run. -/
def CodeClean {n} (read : ConstantBit n → Bool) (P : List Wire) (address : Nat) :
    Code n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => BlockClean P b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference read address b) →
        CodeClean read P address code (ECDSAAdd.run (blockReference read address b) m st)

theorem clean_append {n} (read : ConstantBit n → Bool) (P : List Wire) (address : Nat) (a b : Code n)
    (st : ECDSAAdd.State) (ha : CodeClean read P address a st)
    (hb : ∀ m, m.length = ECDSAAdd.measurementCount (reference read address a) →
      CodeClean read P address b (ECDSAAdd.run (reference read address a) m st)) :
    CodeClean read P address (a++b) st := by
  induction a generalizing st with
  | nil => simpa [CodeClean,ECDSAAdd.run] using hb [] rfl
  | cons x xs ih =>
    refine ⟨ha.1,?_⟩
    intro m hm
    apply ih _ (ha.2 m hm)
    intro tail ht
    have hc := hb (m++tail) (by simp [ECDSAAdd.measurementCount_append,hm,ht])
    rw [reference_cons,run_append_records _ _ m tail st hm] at hc
    exact hc

theorem pair_of_placed_lit {n} (bits paths : List Wire) (i : WInstr n)
    (h : PlacedPair bits paths windowRoot i) : LPlaced bits paths windowRoot i := by
  cases i with
  | literal p =>
    intro w hw
    apply h w
    rcases List.mem_cons.mp hw with e | e
    · exact List.mem_cons.mpr (Or.inl e)
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ e)
  | lookup c ps => exact h

theorem clearP_coherent {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (site : MaskedSite n) (hg : SiteGeoP B site) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((clearP B site start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => Clean B.hp s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue B.bits s)) = p.value))) := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  unfold clearP
  apply clear_coherent_bank read site hg.kind B.bits B.high B.hp hB.split hB.high
  · intro w hw
    refine ⟨hB.out w hw, fun ht => ?_⟩
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
        simp [hB.sub w hw]) ht
  · intro hg'
    have hn := hlast.1
    simp only [lookupRoot, Option.getD_some, List.cons_append, List.nodup_cons] at hn
    exact hn.1 (List.mem_append_right _ (hB.sub _ hg'))
  · exact hB.index
  · exact hB.nodup
  · exact hB.len

theorem masked_runP {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (hg : SiteGeoP B site) (a : Nat) (st : ECDSAAdd.State) (m : List Bool)
    (hs : SimulationValid B.bits B.paths windowRoot a st) :
    ECDSAAdd.run ((specialize site.code a).instantiate read) m st =
      let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
      ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩ := by
  have hp : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := by
    intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have hnext := strict_preserves read B.bits B.paths site.prefix a hp st hs m
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  have hroot : site.guard ∉ portTargets site.ports := List.disjoint_left.mp hlast.2.2 (by simp [lookupRoot])
  simp only [MaskedSite.code,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
    ECDSAAdd.run_append,ECDSAAdd.run_take]
  simpa [specialize,WInstr.specialize] using portTemplate_run read (some site.guard) site.ports a windowRoot
    (m.drop (ECDSAAdd.measurementCount ((specialize site.prefix a).instantiate read)))
    (ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st)
    hlast.2.1 hroot hnext.2.2

theorem lplaced_normalize {n} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hp : ∀ i ∈ code, LPlaced bits paths root i) : ∀ i ∈ normalizeW code, LPlaced bits paths root i := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have h := hp j hj
  cases j with
  | literal p => simpa [normalizeWInstr, LPlaced, ECDSAAdd.Baselines.normalize_wires] using h
  | lookup c p => exact h

theorem pathsClean_normalize {n} (read : ConstantBit n → Bool) (paths : List Wire) (a : Nat)
    (code : WCode n) (st : ECDSAAdd.State) (h : PathsClean read paths a code st) :
    PathsClean read paths a (normalizeW code) st := by
  induction code generalizing st with
  | nil => trivial
  | cons i code ih =>
    cases i with
    | literal p =>
      have h' : ∀ m, PathsClean read paths a code (ECDSAAdd.run p m st) := h
      show ∀ m, PathsClean read paths a (normalizeW code)
        (ECDSAAdd.run (ECDSAAdd.Baselines.normalizeProgram p) m st)
      intro m
      rw [ECDSAAdd.Baselines.normalize_run]
      exact ih _ (h' m)
    | lookup c ps =>
      have h' : Clean paths st.basis ∧ ∀ m, PathsClean read paths a code
          (ECDSAAdd.run ((portTemplate c ps a).instantiate read) m st) := h
      exact ⟨h'.1, fun m => ih _ (h'.2 m)⟩

theorem lnormalized_simulation {n} (read : ConstantBit n → Bool) (bits paths : List Wire)
    (hl : bits.length ≤ paths.length) (code : WCode n) (hp : ∀ i ∈ code, LPlaced bits paths windowRoot i) :
    ∃ cs : List ℂ, List.Forall₂ (LBranch read code bits paths windowRoot)
      (source read bits paths windowRoot (normalizeW code)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cs,aligned,mass⟩ := lsource_simulation read bits paths windowRoot hl (normalizeW code)
    (lplaced_normalize _ _ _ _ hp)
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb
  obtain ⟨m,hm,hb⟩ := hb
  refine ⟨m,by simpa [literalRecords_normalize] using hm,?_⟩
  intro address st hs hc
  simpa only [specialize_normalize_run] using hb address st hs (pathsClean_normalize read paths address code st hc)

def BlockSimP {n} (read : ConstantBit n → Bool) (B : Bank) (block : Block n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, AddrValid B.bits windowRoot address st → BlockClean B.paths block st →
      BlockSafe read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference read address block) m st)

theorem block_simulationP {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (block : Block n) (hg : BlockGeoP B block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimP read B block) (blockSourceP B read block).run cs ∧
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
  | masked site =>
    have hg' : SiteGeoP B site := hg
    have hp : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg'.placed i (List.mem_append_left _ hi))
    obtain ⟨preCs,preAligned,preMass⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen site.prefix
      (fun i hi => pair_of_placed_lit _ _ i (hp i hi))
    obtain ⟨cs,aligned,mass⟩ := clearP_coherent read B hB site hg' 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSourceP,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block.code,MaskedSite.code,literalRecords] using hm
      · intro a st hs hcl hsafe
        have hcl' : Clean B.paths st.basis := hcl
        have hsv : SimulationValid B.bits B.paths windowRoot a st := ⟨hcl',hs.1,hs.2⟩
        let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
        have hn := strict_preserves read B.bits B.paths site.prefix a hp st hsv m
        have hrun := masked_runP read B site hg' a st m hsv
        have hclean : Clean (portTargets site.ports)
            (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg'.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
        have hvalid : Clean B.hp next.basis ∧
            ∀ p ∈ site.ports, next.basis p.target = (next.basis site.guard &&
              decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
          refine ⟨fun w hw => hn.1 w (hB.sub w hw),?_⟩
          rw [hn.2.1]
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
        rw [h₁ a st hs (strict_pathsClean read B.bits B.paths site.prefix a hp st hsv),map_smul,hsigned]
        simp [smul_smul,blockReference,Block.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num

theorem block_addr {n} (read : ConstantBit n → Bool) (B : Bank) (b : Block n) (hg : BlockGeoP B b)
    (a : Nat) (st : ECDSAAdd.State) (hs : AddrValid B.bits windowRoot a st)
    (hc : BlockClean B.paths b st) (m : List Bool) :
    AddrValid B.bits windowRoot a (ECDSAAdd.run (blockReference read a b) m st) := by
  cases b with
  | plain code => exact litAvoid_addr read B.bits code a hg st hs m
  | masked site =>
    have hg' : SiteGeoP B site := hg
    have hp : ∀ i ∈ site.code, PlacedPair B.bits B.paths windowRoot i :=
      fun i hi => placed_implies_pair _ _ _ _ (hg'.placed i hi)
    have h := strict_preserves read B.bits B.paths site.code a hp st ⟨hc,hs.1,hs.2⟩ m
    exact ⟨h.2.1,h.2.2⟩

def SimP {n} (read : ConstantBit n → Bool) (B : Bank) (code : Code n)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase code) ∧
    ∀ a st, AddrValid B.bits windowRoot a st → CodeClean read B.paths a code st → Safe read a code st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference read a code) m st)

theorem source_simulationP {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeoP B b) :
    ∃ cs : List ℂ, List.Forall₂ (SimP read B code) (sourceCodeP B read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1],.cons ?_ .nil,by simp⟩
    exact ⟨[],rfl,fun a st _ _ _ => by simp [reference,erase,specialize,ECDSAAdd.ShorPort.Tmpl.instantiate,ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁,h₁,mass₁⟩ := block_simulationP read B hB b (hg b (by simp))
    obtain ⟨cs₂,h₂,mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    refine ⟨coherentSeqCoefficients cs₁ cs₂,?_,?_⟩
    · rw [sourceCodeP,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁,len₁,run₁⟩ := hb₁
      obtain ⟨m₂,len₂,run₂⟩ := hb₂
      refine ⟨m₁++m₂,?_,?_⟩
      · simp [erase,List.length_append,len₁,len₂]
      · intro a st hs hc hsafe
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference read a b) :=
          len₁.trans (specialize_counts read b.code a).2.symm
        have hn := block_addr read B b (hg b (by simp)) a st hs hc.1 m₁
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hc.1 hsafe.1,map_smul,
          run₂ a (ECDSAAdd.run (blockReference read a b) m₁ st) hn (hc.2 m₁ hm) (hsafe.2 m₁ hm),
          reference_cons,run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass,mass₁,mass₂]
      norm_num

/-- All addresses share one normalized branch coefficient list. -/
theorem program_coherentP {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeoP B b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe read (tableAddressValue B.bits s) code ⟨false,s⟩)
    (hclean : ∀ s, Valid s → CodeClean read B.paths (tableAddressValue B.bits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference read (tableAddressValue B.bits s) code) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((programP B code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs,aligned,mass⟩ := source_simulationP read B hB code hg
  refine ⟨cs,?_,mass⟩
  rw [programP_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m,_,h⟩ := hb
  have he := h (tableAddressValue B.bits s) ⟨false,s⟩ ⟨rfl,hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [Bridge.signedKet_false,hrun s hs.2 m,Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.PathShare

/-! ### Clean bank at the masked sites of the fused generic branch -/

namespace ShorECDLP.Entrant.PathShare
open ECDSAAdd Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- An arithmetic contract that also keeps the bank clean at every masked-site start. -/
structure CheckedC {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire)
    (Pre : BasisState → Prop) (code : Code n) (Post : BasisState → Prop) : Prop where
  checked : Checked read address Pre code Post
  clean : ∀ st, Pre st.basis → CodeClean read P address code st

namespace CheckedC
variable {n : Nat} {read : ConstantBit n → Bool} {address : Nat} {P : List Wire}
variable {A B C : BasisState → Prop} {a b : Code n}

theorem seq (ha : CheckedC read address P A a B) (hb : CheckedC read address P B b C) :
    CheckedC read address P A (a++b) C :=
  ⟨ha.checked.seq hb.checked, fun st hs => clean_append read P address a b st (ha.clean st hs)
    (fun m _ => hb.clean _ (ha.checked.correct st m hs).2)⟩

theorem plain {code : WCode n} (h : Checked read address A ([.plain code] : Code n) B) :
    CheckedC read address P A ([.plain code] : Code n) B :=
  ⟨h, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩

theorem masked {site : MaskedSite n} (h : Checked read address A ([.masked site] : Code n) B)
    (hc : ∀ s, A s → Clean P s) : CheckedC read address P A ([.masked site] : Code n) B :=
  ⟨h, fun _ hs => ⟨hc _ hs, fun _ _ => trivial⟩⟩

end CheckedC

def InPool (P : List Wire) : Prop := ∀ w ∈ P, w ∈ streamLayout.dialogPool

theorem values_clean {P : List Wire} (hP : InPool P) {X Y : ECDSAAdd.Fp} {G : Bool} {base s : BasisState}
    (h : PointDialogValues streamLayout X Y G base s) : Clean P s :=
  fun w hw => (ECDSAAdd.Arithmetic.regValue_zero _ _).mp h.clean w (hP w hw)

theorem literal_checkedC {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire)
    (p : ECDSAAdd.Program) (A B : BasisState → Prop) (h : ECDSAAdd.Triple A p B) :
    CheckedC read address P A ([.plain (wLiteral p)] : Code n) B :=
  CheckedC.plain (literal_checked read address p A B h)

theorem recovery2_checkedC {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire) (hP : InPool P)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) :
    CheckedC read address P (PointDialogValues streamLayout X Y G base) (recovery2 rows)
      (PointDialogValues streamLayout (if G then cx-X else X) (if G then Y-cy else Y) G base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have a := literal_checkedC read address P _ _ _ (pointRecoveryReflection_step streamLayout hw hn X Y G base)
  have c := literal_checkedC read address P _ _ _
    (dialogStep_addX streamLayout hw hn (if G then -1-X else X) Y G base 1)
  have d := CheckedC.masked (P := P) (pair_checked read address ((if G then -1-X else X)+(if G then 1 else 0)) Y G base cx (-cy)
    (wFields rows .x) (wFields rows .negY)
    (row_bits hc hr .x cx (field_some_x hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc)))
    (fun _ h => values_clean hP h)
  have all := (a.seq c).seq d
  have hx : ((if G then -1-X else X)+(if G then 1 else 0))+(if G then cx else 0)=
      (if G then cx-X else X) := by cases G <;> simp; ring
  have hy : Y+(if G then -cy else 0)=(if G then Y-cy else Y) := by cases G <;> simp [sub_eq_add_neg]
  rw [hx,hy] at all
  simpa only [recovery2,pairAdd,List.cons_append,List.nil_append,List.append_assoc] using all

theorem core2_checkedC_true {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire) (hP : InPool P)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    CheckedC read address P (PointDialogValues streamLayout X Y true base) (core2 rows)
      (PointDialogValues streamLayout (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h12 := CheckedC.masked (P := P) (pair_checked read address X Y true base (-cx) (-cy)
    (wFields rows .negX) (wFields rows .negY)
    (row_bits hc hr .negX (-cx) (field_some_negX hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc)))
    (fun _ h => values_clean hP h)
  simp only [if_true,←sub_eq_add_neg] at h12
  have h3 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn (X-cx) (Y-cy) true base false (sub_ne_zero.mpr hX))
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [Bool.false_eq_true,if_false,ha] at h3
  have h4 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn (X-cx) a true base)
  simp only [if_true] at h4
  have h5 := CheckedC.masked (P := P) (addX_checked read address streamLayout hw hn ((X-cx)-a*a) a true base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc)))
    (fun _ h => values_clean hP h)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn d a true base true hd)
  simp only [if_true] at h6
  have r := recovery2_checkedC read address P hP rows hc hr d (a*d) true base
  simp only [if_true] at r
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at r
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at r
  have h := ((((h12.seq h3).seq h4).seq h5).seq h6).seq r
  simpa only [core2,pairAdd,constAdd,List.append_assoc,List.cons_append,List.nil_append] using h

theorem core2_checkedC_false {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire) (hP : InPool P)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState) (hX0 : X ≠ 0) :
    CheckedC read address P (PointDialogValues streamLayout X Y false base) (core2 rows)
      (PointDialogValues streamLayout X Y false base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have h12 := CheckedC.masked (P := P) (pair_checked read address X Y false base (-cx) (-cy)
    (wFields rows .negX) (wFields rows .negY)
    (row_bits hc hr .negX (-cx) (field_some_negX hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc)))
    (fun _ h => values_clean hP h)
  have h3 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X Y false base false hX0)
  have h4 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn X (Y/X) false base)
  have h5 := CheckedC.masked (P := P) (addX_checked read address streamLayout hw hn X (Y/X) false base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc)))
    (fun _ h => values_clean hP h)
  have h6 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X (Y/X) false base true hX0)
  have r := recovery2_checkedC read address P hP rows hc hr X Y false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h12 h3 h4 h5 h6 r
  rw [div_mul_cancel₀ Y hX0] at h6
  have h := ((((h12.seq h3).seq h4).seq h5).seq h6).seq r
  simpa only [core2,pairAdd,constAdd,List.append_assoc,List.cons_append,List.nil_append] using h

theorem checkedC_clean {n} {read : ConstantBit n → Bool} {address : Nat} {P : List Wire} (hP : InPool P)
    {code : Code n} {A : BasisState → Prop} {X Y : ECDSAAdd.Fp} {G : Bool} {base : BasisState}
    (h : CheckedC read address P A code (PointDialogValues streamLayout X Y G base))
    (st : ECDSAAdd.State) (ha : A st.basis) :
    CodeClean read P address code st ∧ ∀ m, Clean P (ECDSAAdd.run (reference read address code) m st).basis :=
  ⟨h.clean st ha, fun m => values_clean hP (h.checked.correct st m ha).2⟩

/-- At every generic boundary the bank is clean at each fused site and after the branch. -/
theorem generic2_clean {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire) (hP : InPool P)
    (rows : Nat → Fin n) (R : Point) (b : Bool) (f : BasisState)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (hg : f streamLayout.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc))
    (st : ECDSAAdd.State) (hs : PointDialogBoundary streamLayout R b f st.basis) :
    CodeClean read P address (generic2 rows) st ∧
      ∀ m, Clean P (ECDSAAdd.run (reference read address (generic2 rows)) m st).basis := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hp := (point_holds _ _ _).mp hs.point
  have hgen : st.basis streamLayout.core.generic = f streamLayout.core.generic :=
    hs.flags _ (by simp [inPlaceFlags])
  show CodeClean read P address ([.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))] ++ core2 rows ++
      [.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))]) st ∧
    ∀ m, Clean P (ECDSAAdd.run (reference read address ([.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))] ++
      core2 rows ++ [.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))])) m st).basis
  cases R with
  | zero =>
    have hG : f streamLayout.core.generic = false := by
      cases h : f streamLayout.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues streamLayout 0 0 false st.basis st.basis :=
      ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
    have hfin : st.basis streamLayout.point.finite = false := hp.1
    have z1 := literal_checkedC read address P _ _ _ (Frontier.zrep_step streamLayout hw hn 0 5 0 false st.basis
      (by rw [hfin,Frontier.finFive_val]; rfl))
    have mid2 := core2_checkedC_false read address P hP rows hc hr 5 0 st.basis Frontier.finFive_ne_zero
    have z2 := literal_checkedC read address P _ _ _ (Frontier.zrep_step streamLayout hw hn 5 0 0 false st.basis
      (by rw [hfin,Frontier.finFive_val]; rfl))
    exact checkedC_clean hP ((z1.seq mid2).seq z2) st values
  | @some x y hrp =>
    have hfin : st.basis streamLayout.point.finite = true := hp.1
    cases hG : f streamLayout.core.generic with
    | false =>
      have values : PointDialogValues streamLayout x y false st.basis st.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
      have z1 := literal_checkedC read address P _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y false st.basis (by rw [hfin]; simp))
      have mid2 := core2_checkedC_false read address P hP rows hc hr x y st.basis (Frontier.curve_x_ne_zero hrp)
      have z2 := literal_checkedC read address P _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y false st.basis (by rw [hfin]; simp))
      exact checkedC_clean hP ((z1.seq mid2).seq z2) st values
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hrp hc he.2.1 he.2.2.1 he.2.2.2
      have values : PointDialogValues streamLayout x y true st.basis st.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
      have z1 := literal_checkedC read address P _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y true st.basis (by rw [hfin]; simp))
      have mid2 := core2_checkedC_true read address P hP rows hc hr x y st.basis den.1 den.2
      have z2 := literal_checkedC read address P _ _ _ (Frontier.zrep_step streamLayout hw hn (genericX x y cx cy)
        (genericX x y cx cy) (genericY x y cx cy) true st.basis (by rw [hfin]; simp))
      exact checkedC_clean hP ((z1.seq mid2).seq z2) st values

end
end ShorECDLP.Entrant.PathShare

/-! ### Clean bank along the fused row -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] ECDSAAdd.run

def scrHeadProgram : ECDSAAdd.Program :=
  [.CX streamLayout.control streamLayout.core.double] ++ [.CX streamLayout.control streamLayout.core.equalX] ++
    ECDSAAdd.Entrant.zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect

theorem scrHead_reference (read : ConstantBit 32768 → Bool) (a : Nat) :
    blockReference read a (.plain scrHead : Block 32768) = scrHeadProgram := by
  simp only [blockReference,Block.code,scrHead,scrHeadProgram,specialize_append,specialize_literal,
    ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]

theorem flip_reference (read : ConstantBit 32768 → Bool) (a : Nat) :
    blockReference read a (.plain (wLiteral [.X 838]) : Block 32768) = [.X 838] := by
  simp only [blockReference,Block.code,specialize_literal,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

/-- From a live state, the bank is clean at every masked site of `row2`, at any address. -/
theorem row2_clean (P : List Wire) (hP : InPool P)
    (hflip : ∀ w ∈ P, w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program))
    (hhead : ∀ w ∈ P, w ∉ ECDSAAdd.wires scrHeadProgram)
    (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeClean (readConstant coeffs Q) P a row2 ⟨false,s⟩ := by
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P0,hP0⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P0) true (fun _=>false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P0) (StreamPoint.of_coordinates s P0 hs.1.1.1.1 hP0),?_,?_,?_⟩
    · simpa [streamLayout_control,flipInfinity,ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  have sclean : Clean P s := fun w hw =>
    hs.2.1 w (List.mem_append_left _ (one_boundary_work_subset streamLayout (List.mem_append_right _ (hP w hw))))
  have pre : CodeClean (readConstant coeffs Q) P a rowPre ⟨false,s⟩ := by
    refine ⟨trivial, fun m _ => ⟨trivial, fun m' _ => ⟨?_, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩⟩
    intro w hw
    rw [scrHead_reference, flip_reference,
      ECDSAAdd.run_preserves_outside _ _ _ w (hhead w hw),
      ECDSAAdd.run_preserves_outside _ _ _ w (hflip w hw)]
    exact sclean w hw
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
    rw [row2_split]
    apply clean_append _ _ _ rowPre _ _ pre
    intro m _
    have bd := rowPre_boundary (readConstant coeffs Q) a (Bridge.toB P0) hc hr en.1 en.2 hd hdo s initial hs.2.2 m
    have g := generic2_clean (readConstant coeffs Q) a P hP probeRows (Bridge.toB P0) true
      (flags streamLayout (Bridge.toB P0) (.some hc) true cy) hc hr (flags_generic (Bridge.toB P0) hc) _ bd
    apply clean_append _ _ _ (generic2 probeRows) rowPost _ g.1
    intro m' _
    exact ⟨g.2 m', fun _ _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩

end
end ShorECDLP.Entrant.PathShare

/-! ### Resources of a bank program -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Every traversal and every measured clear has a valid layout. -/
def BlockLay {n} (B : Bank) : Block n → Prop
  | .plain code => LookupLayouts B.bits B.paths windowRoot (normalizeW code)
  | .masked site => LookupLayouts B.bits B.paths windowRoot (normalizeW site.prefix) ∧
      (tableAddressTree B.high 0 1).Layout site.guard B.hp

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

def blockTP {n} (B : Bank) : Block n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * (2^B.bits.length - 1)
  | .masked site => literalToffolis (normalizeW site.prefix) + traversals site.prefix * (2^B.bits.length - 1) +
      ((tableAddressTree B.high 0 1).internalNodes + 127)

def codeTP {n} (B : Bank) : Code n → Nat
  | [] => 0
  | b::code => blockTP B b + codeTP B code

theorem clearP_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp) (start : Nat) (history : Fin start → Bool) :
    ((clearP B site start).instantiate read history).tCount =
      7 * ((tableAddressTree B.high 0 1).internalNodes + 127) := by
  unfold clearP
  exact MeasuredClear.measuredClear_tCount _ _ _ _ _ _ _ hl read start history

theorem blockProgP_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (b : Block n) (hl : BlockLay B b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgP B b start).instantiate read history).tCount = 7 * blockTP B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgP, WEX.compile_tCount read _ _ _ _ hl' start history, traversals_normalize]
    simp only [blockTP]; ring
  | masked site =>
    obtain ⟨h1, h2⟩ := hl
    rw [blockProgP, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearP_tCount read B site h2 _ h),
      WEX.compile_tCount read _ _ _ _ h1 start history, traversals_normalize]
    simp only [blockTP]; ring

theorem programP_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (code : Code n)
    (hl : ∀ b ∈ code, BlockLay B b) (start : Nat) (history : Fin start → Bool) :
    ((programP B code start).instantiate read history).tCount = 7 * codeTP B code := by
  induction code generalizing start with
  | nil => simp [programP, recordsP, codeTP, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [programP, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hl d (by simp [hd])) _ h),
      blockProgP_tCount read B b (hl b (by simp))]
    simp only [codeTP]; ring

def blockSP {n} (B : Bank) : Block n → Nat
  | .plain code => codeSlots B.bits (normalizeW code)
  | .masked site => codeSlots B.bits (normalizeW site.prefix) +
      (512 * site.ports.length * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 1020)

def codeSP {n} (B : Bank) : Code n → Nat
  | [] => 0
  | b::code => blockSP B b + codeSP B code

theorem blockProgP_slots {n} (B : Bank) (b : Block n) (hl : BlockLay B b) (start : Nat) :
    (blockProgP B b start).gateSlots = blockSP B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgP, WEX.compile_slots _ _ _ _ hl' start]
    rfl
  | masked site =>
    obtain ⟨h1, h2⟩ := hl
    rw [blockProgP, castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ h1 start]
    have hc : (clearP B site (start + codeRecords B.bits B.paths windowRoot (normalizeW site.prefix))).gateSlots =
        512 * site.ports.length * (tableAddressTree B.high 0 1).leaves +
          10 * (tableAddressTree B.high 0 1).internalNodes + 1020 := by
      unfold clearP
      rw [MeasuredClear.measuredClear_slots _ _ _ _ _ _ _ h2]
      simp [clearData]
    rw [hc]
    rfl

theorem programP_slots {n} (B : Bank) (code : Code n) (hl : ∀ b ∈ code, BlockLay B b) (start : Nat) :
    (programP B code start).gateSlots = codeSP B code := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [programP, castFinish_gateSlots, Straight.gateSlots_append, blockProgP_slots B b (hl b (by simp)),
      ih (fun d hd => hl d (by simp [hd]))]
    rfl

theorem codeSP_congr {n} (B B' : Bank) (hb : B.bits = B'.bits) (hh : B.high = B'.high) (code : Code n) :
    codeSP B code = codeSP B' code := by
  induction code with
  | nil => rfl
  | cons b code ih => cases b <;> simp [codeSP, blockSP, hb, hh, ih]

theorem codeTP_congr {n} (B B' : Bank) (hb : B.bits = B'.bits) (hh : B.high = B'.high) (code : Code n) :
    codeTP B code = codeTP B' code := by
  induction code with
  | nil => rfl
  | cons b code ih => cases b <;> simp [codeTP, blockTP, hb, hh, ih]

theorem blockRecP_eq {n} (B B' : Bank) (hb : B.bits = B'.bits) (hh : B.high = B'.high) (b : Block n)
    (hl : BlockLay B b) (hl' : BlockLay B' b) : blockRecP B b = blockRecP B' b := by
  cases b with
  | plain code =>
    have h : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    have h' : LookupLayouts B'.bits B'.paths windowRoot (normalizeW code) := hl'
    simp only [blockRecP]
    rw [codeRecords_eq _ _ _ _ h, codeRecords_eq _ _ _ _ h', hb]
  | masked site =>
    obtain ⟨h1,h2⟩ := hl
    obtain ⟨h1',h2'⟩ := hl'
    simp only [blockRecP]
    rw [codeRecords_eq _ _ _ _ h1, codeRecords_eq _ _ _ _ h1', hb,
      (MeasuredClear.recordUnary_counts _ _ _ h2 0).1, (MeasuredClear.recordUnary_counts _ _ _ h2' 0).1, hh]

theorem recordsP_eq {n} (B B' : Bank) (hb : B.bits = B'.bits) (hh : B.high = B'.high) (code : Code n)
    (hl : ∀ b ∈ code, BlockLay B b) (hl' : ∀ b ∈ code, BlockLay B' b) : recordsP B code = recordsP B' code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    simp only [recordsP]
    rw [blockRecP_eq B B' hb hh b (hl b (by simp)) (hl' b (by simp)),
      ih (fun d hd => hl d (by simp [hd])) (fun d hd => hl' d (by simp [hd]))]

theorem programP_residue {n} (B : Bank) (code : Code n) (start : Nat) :
    AndGadget.residue (programP B code start) = 0 := by
  induction code generalizing start with
  | nil => simp [programP, recordsP]
  | cons b code ih =>
    have hb : AndGadget.residue (blockProgP B b start) = 0 := by
      cases b with
      | plain code => exact WEXCredit.compile_residue _ _ _ _ _
      | masked site =>
        simp [blockProgP, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
          clearP, MeasuredClear.measuredClear_residue]
    simp [programP, AndGadget.residue_cast, AndGadget.residue_append, hb, ih]

theorem compile_wellFormedL {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : bits.length ≤ paths.length) (hp : ∀ i ∈ code, LPlaced bits paths root i)
    (hv : ∀ p, WInstr.literal p ∈ code → ∀ i ∈ p, ECDSAAdd.Challenge.instructionValid i)
    (start : Nat) : (compile bits paths root code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons i code ih =>
    have ht := ih (fun j hj => hp j (List.mem_cons_of_mem _ hj))
      (fun p hm => hv p (List.mem_cons_of_mem _ hm))
    have hi := hp i (by simp)
    cases i with
    | literal p =>
      simp only [compile, NaiveChallenge.wellFormed_castFinish]
      apply straight_append_wellFormed
      · apply Bridge.translate_wellFormed
        intro j hj
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
        exact hv p (by simp) k hk
      · exact ht _
    | lookup c p =>
      have hi' : PlacedPair bits paths root (.lookup c p : WInstr n) := hi
      dsimp only [PlacedPair] at hi'
      simp only [compile, NaiveChallenge.wellFormed_castFinish]
      apply straight_append_wellFormed
      · apply portProgram_wellFormed _ _ _ _ _ hl hi'.1
        exact List.disjoint_left.mpr (fun w hw hm =>
          List.disjoint_left.mp hi'.2.2.2 (List.mem_cons_of_mem root hw) hm)
      · exact ht _

theorem clearP_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (start : Nat) : (clearP B site start).WellFormed := by
  obtain ⟨-,hbd,hhot,hmem,hsm,hgl,-⟩ := kind_facts site hg.kind
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  have notT : ∀ w ∈ site.guard :: B.high ++ B.hp, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with (h | h) | h
    · rw [h] at h2; rcases hgl with e | e <;> rw [e] at h2 <;> dsimp only [Wire] at h2 <;> omega
    · have := hB.high w h
      dsimp only [Wire] at *; omega
    · exact List.disjoint_left.mp hlast.2.2
        (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
          simp [hB.sub w h]) ht
  unfold clearP
  apply MeasuredClear.measuredClear_wellFormed
  · exact tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len (site_tree_nodup B hB site hg)
  · intro i j he; apply Fin.ext; rw [hhot i,hhot j] at he; dsimp only [Wire] at he; omega
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low_lt i
    rw [← he] at h1
    dsimp only [Wire] at *
    omega
  · rw [hB.index]
    intro hm
    exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) hsm
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    rw [hhot i] at hi
    dsimp only [Wire] at hi
    omega

theorem programP_wellFormed {n} (B : Bank) (hB : BankOK B) (code : Code n) (hg : ∀ b ∈ code, BlockGeoP B b)
    (hp : ∀ p, WInstr.literal p ∈ erase code → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (programP B code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons b code ih =>
    rw [programP,castFinish_wellFormed]
    apply straight_append_wellFormed
    · have hgb := hg b (by simp)
      have hpb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.Arithmetic.GatePhysical p := fun p hm => hp p (by simp [erase_cons,hm])
      cases b with
      | plain code =>
        have hg' : LitAvoid B.bits code := hgb
        exact compile_wellFormedL _ _ _ _ hB.bitsLen (lplaced_normalize _ _ _ _ (litAvoid_placed _ _ code hg'))
          (normalized_literals_valid code hpb) start
      | masked site =>
        have hg' : SiteGeoP B site := hgb
        have hpref : ∀ i ∈ site.prefix, LPlaced B.bits B.paths windowRoot i := fun i hi =>
          pair_of_placed_lit _ _ i (placed_implies_pair _ _ _ _ (hg'.placed i (List.mem_append_left _ hi)))
        have hphys : ∀ p, WInstr.literal p ∈ site.prefix → ECDSAAdd.Arithmetic.GatePhysical p := by
          intro p hm; exact hpb p (List.mem_append_left _ hm)
        rw [blockProgP,castFinish_wellFormed]
        exact straight_append_wellFormed _ _
          (compile_wellFormedL _ _ _ _ hB.bitsLen (lplaced_normalize _ _ _ _ hpref)
            (normalized_literals_valid site.prefix hphys) start)
          (clearP_wellFormed B hB site hg' _)
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase_cons,hm])) _

end
end ShorECDLP.Entrant.PathShare

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem clearP_support {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hk : SiteKind site)
    (S : List Wire) (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low i ∈ S)
    (hhigh : B.high ⊆ S) (hpaths : B.paths ⊆ S) (start : Nat) :
    ChallengeMigration.straightWires (clearP B site start) ⊆ S := by
  obtain ⟨-,-,-,hmem,hsm,-,-⟩ := kind_facts site hk
  have hscratch : scratch site ∈ (clearData site.ports).map MeasuredClear.ClearPort.target := by
    rw [clearData_targets]
    exact hsm
  unfold clearP
  rw [support_agrees]
  apply List.Subset.trans (MeasuredClear.measuredClear_static _ _ _ _ _ _ _ hscratch start)
  intro w hw
  simp only [MeasuredClear.clearSupport,clearData_targets,hB.index,MeasuredClear.hotBank,
    List.mem_append,List.mem_cons,or_assoc] at hw
  rcases hw with hs | hl | hh | hr | hb | hp
  · exact hS hs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    exact hlow i
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact hS (hmem i)
  · rw [hr]; exact hgS
  · exact hhigh hb
  · exact hpaths (hB.sub _ hp)

theorem normalized_lit_support {n} (code : WCode n) (S : List Wire)
    (h : ∀ p, WInstr.literal p ∈ code → ECDSAAdd.wires p ⊆ S.toFinset) :
    ∀ p, WInstr.literal p ∈ normalizeW code → ECDSAAdd.wires p ⊆ S.toFinset := by
  intro p hp
  rw [normalizeW] at hp
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
  cases j with
  | literal q =>
    cases he
    rw [ECDSAAdd.Baselines.normalize_wires]
    exact h q hj
  | lookup c ps => cases he

theorem normalized_look_support {n} (code : WCode n) (S : List Wire)
    (h : ∀ c ps, WInstr.lookup c ps ∈ code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S) :
    ∀ c ps, WInstr.lookup c ps ∈ normalizeW code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S := by
  intro c ps hp
  rw [normalizeW] at hp
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
  cases j with
  | literal q => cases he
  | lookup d qs => cases he; exact h c ps hj

theorem programP_support {n} (B : Bank) (hB : BankOK B) (code : Code n) (hg : ∀ b ∈ code, BlockGeoP B b)
    (S : List Wire) (hroot : windowRoot ∈ S) (hbits : B.bits ⊆ S) (hpaths : B.paths ⊆ S)
    (hlow : ∀ i, low i ∈ S) (hhigh : B.high ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ erase code → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (programP B code start) ⊆ S := by
  induction code generalizing start with
  | nil => simp [programP,recordsP,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hlb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.wires p ⊆ S.toFinset :=
      fun p hm => hlit p (by simp [erase_cons,hm])
    have hkb : ∀ c ps, WInstr.lookup c ps ∈ b.code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
      fun c ps hm => hlook c ps (by simp [erase_cons,hm])
    rw [programP,support_cast,straightWires_append]
    refine List.append_subset.mpr ⟨?_, ih (fun d hd => hg d (by simp [hd]))
      (fun p hm => hlit p (by simp [erase_cons,hm])) (fun c ps hm => hlook c ps (by simp [erase_cons,hm])) _⟩
    cases b with
    | plain code =>
      exact compile_support _ _ _ _ S hroot hbits hpaths (normalized_lit_support code S hlb)
        (normalized_look_support code S hkb) start
    | masked site =>
      have hg' : SiteGeoP B site := hg (.masked site) (by simp)
      have hpl : ∀ p, WInstr.literal p ∈ site.prefix → ECDSAAdd.wires p ⊆ S.toFinset :=
        fun p hm => hlb p (List.mem_append_left _ hm)
      have hpk : ∀ c ps, WInstr.lookup c ps ∈ site.prefix → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
        fun c ps hm => hkb c ps (List.mem_append_left _ hm)
      have hlast := hkb (some site.guard) site.ports (by simp [Block.code,MaskedSite.code])
      rw [blockProgP,support_cast,straightWires_append]
      exact List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
        (normalized_lit_support _ S hpl) (normalized_look_support _ S hpk) start,
        clearP_support B hB site hg'.kind S hlast.2 (hlast.1 site.guard (Option.mem_def.mpr rfl)) hlow hhigh hpaths _⟩

end
end ShorECDLP.Entrant.PathShare

/-! ### The pool path bank of the fused row -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Fifteen dialog-pool wires used only by the plain arithmetic of the generic branch. -/
def pathBank : List Wire := List.range' 14832 15

def bank15 : Bank := ⟨windowBits, WEXUnlookup.high, pathBank.take 8, pathBank⟩
def old15 : Bank := ⟨windowBits, WEXUnlookup.high, WEXUnlookup.highPaths, windowPaths⟩
def bank14 : Bank := ⟨WEXUnlookupWidth14.bits, WEXUnlookupWidth14.high, pathBank.take 7, pathBank⟩
def old14 : Bank := ⟨WEXUnlookupWidth14.bits, WEXUnlookupWidth14.high, WEXUnlookupWidth14.highPaths, windowPaths⟩

theorem pathBank_pool : InPool pathBank := by
  intro q hq
  rw [pathBank,List.mem_range'_1] at hq
  have hp : streamLayout.dialogPool = ((List.range' 4115 5699).map streamWire).take 2613 := rfl
  rw [hp,List.mem_iff_getElem]
  refine ⟨q - 14115,by simp only [List.length_take,List.length_map,List.length_range']; rw [Nat.min_eq_left (by norm_num)]; omega,?_⟩
  simp only [List.getElem_take,List.getElem_map,List.getElem_range']
  unfold streamWire
  dsimp only [Wire] at *
  split_ifs <;> omega

/-- Disjointness from the bank by a single pass over the other list. -/
theorem pathBank_not_of (L : List Wire) (hL : (L.all fun b => decide (b < 14832 ∨ 14847 ≤ b)) = true) :
    ∀ w ∈ pathBank, w ∉ L := by
  intro w hw hm
  have h1 := List.all_eq_true.mp hL w hm
  simp only [decide_eq_true_eq] at h1
  simp only [pathBank, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem pathBank_nodup : pathBank.Nodup := List.nodup_range'

theorem pathBank_window : ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ pathBank := by
  intro w hw hp
  exact pathBank_not_of _ (by decide +kernel) w hp hw

theorem pathBank_out : ∀ w ∈ pathBank, 871 ≤ w := by
  unfold pathBank
  decide +kernel

theorem pathBank_flip : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program) := by
  intro w hw hm
  simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hm
  subst hm
  revert hw
  unfold pathBank
  decide +kernel


theorem bank15_ok : BankOK bank15 where
  split := WEXUnlookup.splitAddress
  high := by
    unfold bank15 WEXUnlookup.high
    decide +kernel
  index := tableAddressTree_index _ 0 1 (by decide +kernel)
  nodup := by decide +kernel
  len := by decide +kernel
  sub := fun _ hw => List.mem_of_mem_take hw
  out := fun w hw => pathBank_out w (List.mem_of_mem_take hw)
  bitsLen := by decide +kernel

theorem bank14_ok : BankOK bank14 where
  split := WEXUnlookupWidth14.splitAddress
  high := by
    unfold bank14 WEXUnlookupWidth14.high
    decide +kernel
  index := tableAddressTree_index _ 0 1 (by decide +kernel)
  nodup := by decide +kernel
  len := by decide +kernel
  sub := fun _ hw => List.mem_of_mem_take hw
  out := fun w hw => pathBank_out w (List.mem_of_mem_take hw)
  bitsLen := by decide +kernel

/-! A Boolean wire check, so concrete sites are discharged by `decide +kernel`. -/

def corrList : List ECDSAAdd.Correction → List Wire
  | [] => []
  | .Z t :: cs => t :: corrList cs
  | .CZ a b :: cs => a :: b :: corrList cs

def instrList : ECDSAAdd.Instr → List Wire
  | .X t => [t]
  | .CX c t => [c, t]
  | .CCX a b t => [a, b, t]
  | .measureX t c₀ c₁ => t :: (corrList c₀ ++ corrList c₁)

def progAvoid (P : List Wire) (p : ECDSAAdd.Program) : Bool :=
  p.all fun i => (instrList i).all fun w => !(P.contains w)

def avoidW {n} (P : List Wire) : WInstr n → Bool
  | .literal p => progAvoid P p
  | .lookup c ps => (portTargets ps).all (fun w => !(P.contains w)) && c.all (fun q => !(P.contains q))

theorem corr_mem (cs : List ECDSAAdd.Correction) (w : Wire) (h : w ∈ ECDSAAdd.correctionWires cs) :
    w ∈ corrList cs := by
  induction cs with
  | nil => simp [ECDSAAdd.correctionWires] at h
  | cons c cs ih =>
    cases c with
    | Z t =>
      simp only [ECDSAAdd.correctionWires, Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · simp [corrList, h]
      · exact List.mem_cons_of_mem _ (ih h)
    | CZ a b =>
      simp only [ECDSAAdd.correctionWires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with (h | h) | h
      · simp [corrList, h]
      · simp [corrList, h]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))

theorem instr_mem (i : ECDSAAdd.Instr) (w : Wire) (h : w ∈ i.wires) : w ∈ instrList i := by
  cases i with
  | X t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | CX c t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | CCX a b t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | measureX t c₀ c₁ =>
    simp only [ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_singleton] at h
    simp only [instrList, List.mem_cons, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (corr_mem _ _ h))
    · exact Or.inr (Or.inr (corr_mem _ _ h))

theorem progAvoid_sound (P : List Wire) (p : ECDSAAdd.Program) (h : progAvoid P p = true) :
    ∀ w ∈ P, w ∉ ECDSAAdd.wires p := by
  intro w hw hm
  induction p with
  | nil => simp [ECDSAAdd.wires] at hm
  | cons i p ih =>
    simp only [progAvoid, List.all_cons, Bool.and_eq_true] at h
    simp only [ECDSAAdd.wires, Finset.mem_union] at hm
    rcases hm with hm | hm
    · have := List.all_eq_true.mp h.1 w (instr_mem i w hm)
      simp at this
      exact this hw
    · exact ih h.2 hm

theorem pathBank_head : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires scrHeadProgram :=
  progAvoid_sound pathBank scrHeadProgram (by unfold pathBank scrHeadProgram; decide +kernel)

theorem avoidW_lookup {n} (P : List Wire) (c : Option Wire) (ps : List (LookupPort n))
    (h : avoidW P (.lookup c ps) = true) :
    (∀ w ∈ P, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ P := by
  unfold avoidW at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun w hw ht => ?_, fun q hq hp => ?_⟩
  · have := List.all_eq_true.mp h1 w ht
    simp at this
    exact this hw
  · cases c with
    | none => simp at hq
    | some q' =>
      simp only [Option.mem_def, Option.some.injEq] at hq
      subst hq
      simp [Option.all] at h2
      exact h2 hp

end
end ShorECDLP.Entrant.PathShare

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Every literal and every lookup of the code avoids the pool path bank. -/
def Avoids (code : WCode 32768) : Prop :=
  (∀ p, WInstr.literal p ∈ code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ code → (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank)

theorem avoids_of_all (code : WCode 32768) (h : code.all (avoidW pathBank) = true) : Avoids code :=
  ⟨fun p hp => progAvoid_sound pathBank p (List.all_eq_true.mp h _ hp),
    fun c ps hp => avoidW_lookup pathBank c ps (List.all_eq_true.mp h _ hp)⟩

theorem avoids_append {a b : WCode 32768} (ha : Avoids a) (hb : Avoids b) : Avoids (a ++ b) := by
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact ha.1 p h
    · exact hb.1 p h
  · rcases List.mem_append.mp hp with h | h
    · exact ha.2 c ps h
    · exact hb.2 c ps h

theorem avoids_lit (p : ECDSAAdd.Program) (h : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) :
    Avoids (wLiteral (n := 32768) p) := by
  refine ⟨fun q hq => ?_, fun c ps hp => ?_⟩
  · simp only [wLiteral, List.mem_singleton, WInstr.literal.injEq] at hq
    rw [hq]; exact h
  · simp [wLiteral] at hp

theorem scrNegP_avoid : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires WEX.scrNegP :=
  WEX.neg_disjoint (negateYLayout streamLayout) streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths streamLayout streamLayout_widths).2 pathBank (pathBank_not_of _ (by decide +kernel))

/-! The scratch wire lists in explicit form (pool position `i` is wire `14115 + i`), so the kernel
checks below never evaluate pool positions through the layout. -/

theorem pbPairWires_eq : WEX.scrPairWires = 14373 :: List.range' 14374 256 ++ [14883] := by
  simp only [WEX.scrPairWires, WEX.map_poolWire _ _ (by norm_num : 259 + 256 ≤ 5699),
    WEX.poolWire_eq _ (by norm_num : 258 < 5699), WEX.poolWire_eq _ (by norm_num : 768 < 5699)]

theorem pbShortWires_eq : WEX.scrShortWires = 14884 :: List.range' 14885 256 ++ [15141] := by
  simp only [WEX.scrShortWires, WEX.map_poolWire _ _ (by norm_num : 770 + 256 ≤ 5699),
    WEX.poolWire_eq _ (by norm_num : 769 < 5699), WEX.poolWire_eq _ (by norm_num : 1026 < 5699)]

theorem pbExtraWires_eq : WEX.scrDExtraWires = List.range' 15399 255 := by
  simp only [WEX.scrDExtraWires, WEX.map_poolWire _ _ (by norm_num : 1284 + 255 ≤ 5699)]

theorem avoids_lookup {c : Option Wire} {ps : List (LookupPort 32768)}
    (ht : ∀ w ∈ pathBank, w ∉ portTargets ps) (hc : ∀ q ∈ c, q ∉ pathBank) :
    Avoids [.lookup c ps] := by
  refine ⟨fun p hp => ?_, fun c' ps' hp => ?_⟩
  · simp at hp
  · simp only [List.mem_singleton, WInstr.lookup.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨ht, hc⟩

theorem scrDLookup_avoids : Avoids [WInstr.lookup (some windowRoot) (WEX.scrDPorts probeRows)] := by
  refine avoids_lookup ?_ ?_
  · rw [WEX.scrDPorts_targets, WEX.scrAllWires, WEX.scrWires, pbPairWires_eq, pbShortWires_eq,
      pbExtraWires_eq]
    exact pathBank_not_of _ (by decide +kernel)
  · intro q hq
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact fun h => pathBank_not_of [windowRoot] (by decide +kernel) _ h List.mem_cons_self

theorem sfxCC_avoids : Avoids WEX.sfxCC := by
  simp only [WEX.sfxCC, WEX.scrDWires, pbShortWires_eq, pbExtraWires_eq]
  exact avoids_of_all _ (by unfold pathBank; decide +kernel)

theorem scrDMiddle_avoids : Avoids WEX.scrDMiddle := by
  simp only [WEX.scrDMiddle, pbPairWires_eq, pbShortWires_eq]
  repeat' (with_reducible apply avoids_append)
  all_goals exact avoids_of_all _ (by unfold pathBank; decide +kernel)

/-- The output site, split so that the negation program is bounded by its layout. -/
theorem scrD_avoids : Avoids scrDSite.code := by
  have hP : Avoids (wLiteral (n := 32768) WEX.scrNegP) := avoids_lit _ scrNegP_avoid
  rw [scrDSite_code, WEX.sfxMidF, WEX.cornersE_split]
  repeat' (with_reducible apply avoids_append)
  all_goals first
    | (with_reducible exact hP)
    | exact scrDLookup_avoids
    | exact sfxCC_avoids
    | exact scrDMiddle_avoids
    | exact avoids_of_all _ (by unfold pathBank; decide +kernel)

theorem pair_avoid (refsA refsB : Nat → Nat → ConstantBit 32768) :
    (∀ p, WInstr.literal p ∈ (pairSite refsA refsB).code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ (pairSite refsA refsB).code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) := by
  have hw : ∀ w ∈ pathBank, w ∉ pairWireList := pathBank_not_of _ (by decide +kernel)
  have ht : ∀ w ∈ pathBank, w ∉ pairTargets := pathBank_not_of _ (by decide +kernel)
  have hg : streamLayout.core.generic ∉ pathBank := fun h =>
    pathBank_not_of [streamLayout.core.generic] (by decide +kernel) _ h List.mem_cons_self
  rw [pairSite_code]
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_cons.mp hp with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact wires_avoid_of pairArith_subset hw
    · cases List.mem_singleton.mp h
  · have hp' : c = some streamLayout.core.generic ∧ ps = (pairSite refsA refsB).ports := by
      rcases List.mem_cons.mp hp with h | h
      · exact WInstr.lookup.inj h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact WInstr.lookup.inj (List.mem_singleton.mp h)
    obtain ⟨rfl, rfl⟩ := hp'
    refine ⟨fun w hw' hm => ht w hw' (by rw [pairSite_targets] at hm; exact hm), fun q hq => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hg

theorem triple_avoid :
    (∀ p, WInstr.literal p ∈ (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).code →
      ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) := by
  have hw : ∀ w ∈ pathBank, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).wires :=
    pathBank_not_of _ (by decide +kernel)
  have ht : ∀ w ∈ pathBank, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).src :=
    pathBank_not_of _ (by decide +kernel)
  have hg : streamLayout.core.generic ∉ pathBank := fun h =>
    pathBank_not_of [streamLayout.core.generic] (by decide +kernel) _ h List.mem_cons_self
  rw [constSite_code]
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_cons.mp hp with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact wires_avoid_of (MeasuredCanonicalModLayout.program_wires_subset _ _ _) hw
    · cases List.mem_singleton.mp h
  · have hp' : c = some streamLayout.core.generic ∧
        ps = indexedPorts (streamLayout.recoveryConstant streamLayout.point.x).src (wFields probeRows .tripleX) true := by
      rcases List.mem_cons.mp hp with h | h
      · exact WInstr.lookup.inj h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact WInstr.lookup.inj (List.mem_singleton.mp h)
    obtain ⟨rfl, rfl⟩ := hp'
    refine ⟨fun w hw' hm => ht w hw' (by rw [indexed_targets] at hm; exact hm), fun q hq => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hg

theorem scrIn_avoid : (WEX.scrInSite probeRows).code.all (avoidW pathBank) = true := by
  have hl : [WInstr.lookup (some windowRoot) (WEX.scrInPorts probeRows)].all (avoidW pathBank) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, avoidW, WEX.scrInPorts_targets, WEX.scrWires,
      pbPairWires_eq, pbShortWires_eq]
    unfold pathBank
    decide +kernel
  rw [WEX.scrInSite_code]
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨⟨hl, ?_⟩, hl⟩
  simp only [WEX.scrInArith, WEX.scrInMid, pbPairWires_eq, pbShortWires_eq]
  unfold pathBank
  decide +kernel


end
end ShorECDLP.Entrant.PathShare

/-! ### Geometry of the fused row on the pool bank -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem plain_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (code : WCode 32768)
    (hold : ∀ i ∈ code, PlacedPair windowBits windowPaths windowRoot i)
    (hlit : ∀ i ∈ code, ∃ p, i = .literal p) : LitAvoid B.bits code := by
  intro i hi
  obtain ⟨p, rfl⟩ := hlit i hi
  refine ⟨p, rfl, ?_⟩
  intro w hw
  apply hold _ hi w
  rcases List.mem_cons.mp hw with h | h
  · simp [h]
  · simp [hbits w h]

theorem site_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (hbn : B.bits.Nodup)
    (hpaths : B.paths = pathBank) (site : MaskedSite 32768) (hold : WEXUnlookup.SiteGeometry site)
    (hlit : ∀ p, WInstr.literal p ∈ site.code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ site.code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) :
    SiteGeoP B site := by
  refine ⟨?_, hold.kind⟩
  intro i hi
  have ho := hold.placed i hi
  rw [hpaths]
  cases i with
  | literal p =>
    intro w hw
    simp only [List.mem_cons, List.mem_append, or_assoc] at hw
    rcases hw with h | h | h
    · exact ho w (by simp [h])
    · exact ho w (by simp [hbits w h])
    · exact hlit p hi w h
  | lookup c ps =>
    dsimp only [Placed] at ho ⊢
    obtain ⟨hT, hC⟩ := hlook c ps hi
    have hq : lookupRoot windowRoot c ∉ pathBank := by
      cases c with
      | none => exact pathBank_window windowRoot (by simp)
      | some q => exact hC q (Option.mem_def.mpr rfl)
    have hqb : lookupRoot windowRoot c ∉ windowBits := by
      have h0 := ho.1
      rw [List.cons_append] at h0
      have := (List.nodup_cons.mp h0).1
      exact fun h => this (List.mem_append_left _ h)
    refine ⟨?_, ho.2.1, ?_⟩
    · rw [List.cons_append, List.nodup_cons]
      refine ⟨fun h => ?_, ?_⟩
      · rcases List.mem_append.mp h with h | h
        · exact hqb (hbits _ h)
        · exact hq h
      · rw [List.nodup_append]
        refine ⟨hbn, pathBank_nodup, ?_⟩
        intro a ha b hb e
        subst e
        exact pathBank_window a (by simp [hbits a ha]) hb
    · apply List.disjoint_left.mpr
      intro w hw ht
      simp only [List.mem_cons, List.mem_append, or_assoc] at hw
      rcases hw with h | h | h | h
      · exact List.disjoint_left.mp ho.2.2 (by simp [h]) ht
      · exact List.disjoint_left.mp ho.2.2 (by simp [h]) ht
      · exact List.disjoint_left.mp ho.2.2 (by simp [hbits w h]) ht
      · exact hT w h ht

theorem row2_masked_cases (site : MaskedSite 32768) (hb : Block.masked site ∈ row2) :
    site = WEX.scrInSite probeRows ∨ site = pairSite (wFields probeRows .negX) (wFields probeRows .negY) ∨
      site = constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX) ∨
      site = pairSite (wFields probeRows .x) (wFields probeRows .negY) ∨ site = scrDSite := by
  rw [row2_split, generic2_list] at hb
  simp only [rowPre, rowPost, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Block.masked.injEq, reduceCtorEq, false_or] at hb
  tauto

def isLit {n} : WInstr n → Bool
  | .literal _ => true
  | .lookup _ _ => false

def plainLit {n} : Block n → Bool
  | .plain c => c.all isLit
  | .masked _ => true

theorem row2_plainLit : row2.all plainLit = true := by
  decide +kernel

theorem row2_plain_lit (code : WCode 32768) (hb : Block.plain code ∈ row2) : WEX.LitOnly code := by
  have h : code.all isLit = true := List.all_eq_true.mp row2_plainLit _ hb
  intro i hi
  have hi' := List.all_eq_true.mp h i hi
  cases i with
  | literal p => exact ⟨p, rfl⟩
  | lookup c ps => simp [isLit] at hi'

theorem row2_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (hbn : B.bits.Nodup)
    (hpaths : B.paths = pathBank) : ∀ b ∈ row2, BlockGeoP B b := by
  intro b hb
  have old := WEXUnlookup.row2_geometry b hb
  cases b with
  | plain code => exact plain_geoP B hbits code old.1 (row2_plain_lit code hb)
  | masked site =>
    have avoid : Avoids site.code := by
      rcases row2_masked_cases site hb with rfl | rfl | rfl | rfl | rfl
      · exact avoids_of_all _ scrIn_avoid
      · exact pair_avoid _ _
      · exact triple_avoid
      · exact pair_avoid _ _
      · exact scrD_avoids
    exact site_geoP B hbits hbn hpaths site old avoid.1 avoid.2

theorem row2_geo15 : ∀ b ∈ row2, BlockGeoP bank15 b :=
  row2_geoP bank15 (fun _ h => h) (by decide +kernel) rfl

theorem row2_geo14 : ∀ b ∈ row2, BlockGeoP bank14 b :=
  row2_geoP bank14 (by decide +kernel) (by decide +kernel) rfl


end
end ShorECDLP.Entrant.PathShare

/-! ### Supports and the compact labels without the old path bank -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- The body's source labels without the fifteen retired path wires. -/
def retired (w : Nat) : Prop := 10000 ≤ w ∧ w < 10015
instance : DecidablePred retired := fun w => inferInstanceAs (Decidable (10000 ≤ w ∧ w < 10015))

def newSource : List Wire := sourceSupport.filter (fun w => decide (¬retired w))

theorem newSource_mem (w : Nat) :
    w ∈ newSource ↔ (fixedPort w ∨ oldWork w) ∧ ¬retired w := by
  rw [newSource, List.mem_filter, sourceSupport_mem, decide_eq_true_eq]

theorem newSource_of_bounds (xs : List Wire)
    (h : ∀ w ∈ xs, (fixedPort w ∨ oldWork w) ∧ ¬retired w) : xs ⊆ newSource :=
  fun w hw => (newSource_mem w).mpr (h w hw)

theorem newSource_of_old (w : Nat) (h1 : w ∈ sourceSupport) (h2 : w ∉ windowPaths) : w ∈ newSource := by
  rw [newSource_mem]
  refine ⟨(sourceSupport_mem w).mp h1, fun h => h2 ?_⟩
  unfold retired at h
  simp only [windowPaths, List.mem_range'_1]
  omega

/-- Swap the retired path labels with the sources of the top fifteen compact labels. -/
def tauWire (w : Nat) : Nat :=
  if 10000 ≤ w ∧ w < 10012 then w + 5644
  else if 10012 ≤ w ∧ w < 10015 then w + 9802
  else if 15644 ≤ w ∧ w < 15656 then w - 5644
  else if 19814 ≤ w ∧ w < 19817 then w - 9802
  else w

theorem tauWire_involutive : Function.Involutive tauWire := by
  intro w
  unfold tauWire
  split_ifs <;> omega

def tau : Wire ≃ Wire := ⟨tauWire, tauWire, tauWire_involutive, tauWire_involutive⟩

/-- Compact labels: the old compaction after the swap. -/
def pi : Wire ≃ Wire := tau.trans compactPerm

theorem pi_apply (w : Wire) : pi w = compactWire (tauWire w) := rfl

theorem pi_fixed (w : Wire) (h : fixedPort w) : pi w = w := by
  have ht : tauWire w = w := by unfold tauWire fixedPort at *; split_ifs <;> omega
  rw [pi_apply, ht]
  exact compactPerm_fixed w h

theorem pi_hot (i : Fin 128) : pi (hot i) = hot i := by
  have hi := i.isLt
  have ht : tauWire (hot i) = hot i := by unfold tauWire hot; split_ifs <;> omega
  rw [pi_apply, ht]
  exact compactPerm_hot i

theorem pi_bound (w : Nat) (hw : w ∈ newSource) : compactWire (tauWire w) < 1619 := by
  obtain ⟨h1, h2⟩ := (newSource_mem w).mp hw
  unfold retired at h2
  by_cases hA : 15644 ≤ w ∧ w < 15656
  · have ht : tauWire w = w - 5644 := by unfold tauWire; split_ifs <;> omega
    have ho : oldWork (w - 5644) := by unfold oldWork; omega
    rw [ht, compactWire, if_pos ho]
    unfold freeAt oldRank
    split_ifs <;> omega
  by_cases hB : 19814 ≤ w ∧ w < 19817
  · have ht : tauWire w = w - 9802 := by unfold tauWire; split_ifs <;> omega
    have ho : oldWork (w - 9802) := by unfold oldWork; omega
    rw [ht, compactWire, if_pos ho]
    unfold freeAt oldRank
    split_ifs <;> omega
  have ht : tauWire w = w := by unfold tauWire; split_ifs <;> omega
  rw [ht]
  rcases h1 with hf | ho
  · have he : compactWire w = w := compactPerm_fixed w hf
    rw [he]
    unfold fixedPort at hf
    omega
  · rw [compactWire, if_pos ho]
    unfold oldWork at ho
    unfold freeAt oldRank
    split_ifs <;> omega

theorem pi_point (w : Wire) (h : w ∈ pointLogicalWires) : pi w = w := by
  apply pi_fixed
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
  unfold fixedPort; dsimp only [Wire] at *; omega

theorem pi_address (w : Wire) (h : w ∈ streamAddress) : pi w = w := by
  apply pi_fixed
  exact Or.inr (Or.inr (Or.inr (by simpa [streamAddress] using h)))

def pull2 (s : BasisState) : BasisState := relabelBasis pi.symm s

theorem pull2_at (s : BasisState) (w : Wire) (h : fixedPort w) : pull2 s w = s w := by
  simp only [pull2,relabelBasis,Equiv.symm_symm,pi_fixed w h]

theorem pull2_hot (s : BasisState) (i : Fin 128) : pull2 s (hot i) = s (hot i) := by
  simp only [pull2,relabelBasis,Equiv.symm_symm,pi_hot]

theorem pull2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    pull2 (pointWrite P s) = pointWrite P (pull2 s) := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · have he := pi_point w hw
    simp only [pull2,relabelBasis,Equiv.symm_symm,pointWrite,he,if_pos hw]
  · have hn : pi w ∉ pointLogicalWires := by
      intro hh
      have he := pi_point _ hh
      have : pi w = w := pi.injective he
      exact hw (this ▸ hh)
    simp only [pull2,relabelBasis,Equiv.symm_symm,pointWrite,if_neg hw,if_neg hn]

theorem push2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis pi (pointWrite P (pull2 s)) = pointWrite P s := by
  have h := congrArg (relabelBasis pi) (pull2_write P s)
  have hi (t : BasisState) : relabelBasis pi (pull2 t) = t := by
    simpa only [pull2,Equiv.symm_symm] using relabelBasis_symm pi.symm t
  rw [hi] at h
  exact h.symm

theorem pull2_coordinates (s : BasisState) :
    pointStateCoordinates (pull2 s) = pointStateCoordinates s := by
  have he (ws : List Wire) (hw : ∀ w ∈ ws, fixedPort w) :
      wireValues ws (pull2 s) = wireValues ws s := by
    apply List.map_congr_left
    intro w hm; exact pull2_at s w (hw w hm)
  have hx := he (List.range' 263 256) (by
    intro w hw; exact Or.inl (List.mem_range'_1.mp hw))
  have hy := he (List.range' 580 256) (by
    intro w hw
    have hw := List.mem_range'_1.mp hw
    apply Or.inr; apply Or.inl; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,pull2_at s 838 (by decide +kernel)]

theorem pull2_digit (s : BasisState) : windowRawDigit 0 (pull2 s) = windowRawDigit 0 s := by
  have he : wireValues (List.range' 855 15) (pull2 s) = wireValues (List.range' 855 15) s := by
    apply List.map_congr_left
    intro w hw
    apply pull2_at
    have hw := List.mem_range'_1.mp hw
    apply Or.inr; apply Or.inr; apply Or.inr; dsimp only [Wire] at *; omega
  simp only [windowRawDigit,windowAddressBits,windowBankStart,Nat.mul_zero,Nat.add_zero,he,
    pull2_at s 870 (by decide +kernel)]

def ready2 (s : BasisState) : Prop := windowReady (pull2 s) ∧ MeasuredClear.HotClean hot s

theorem ready2_active (s : BasisState) (h : ready2 s) : s 836 = true := by
  simpa only [pull2_at s 836 (by decide +kernel)] using windowReady_active (pull2 s) h.1

theorem ready2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (h : ready2 s) :
    ready2 (pointWrite P s) := by
  refine ⟨?_, pointWrite_hot P s h.2⟩
  rw [pull2_write]
  exact windowReady_write P (pull2 s) h.1

theorem pull2_address (s : BasisState) (v : Wire) (hv : v ∈ streamAddress) (b : Bool) :
    pull2 (s[v ↦ b]) = (pull2 s)[v ↦ b] := by
  have hh' : pi.symm v = v := by
    rw [Equiv.symm_apply_eq]; exact (pi_address v hv).symm
  simp only [pull2,relabelBasis_upd,hh']

theorem ready2_address (s : BasisState) (h : ready2 s)
    (v : Wire) (hv : v ∈ streamAddress) (b : Bool) : ready2 (s[v ↦ b]) := by
  refine ⟨?_, ?_⟩
  · rw [pull2_address s v hv b]
    exact windowReady_address (pull2 s) h.1 v hv b
  · intro i
    have hn : hot i ≠ v := fun he => hot_outside_address i (he.symm ▸ hv)
    exact (upd_other s v b hn).trans (h.2 i)

theorem pull2_first (s : BasisState) (h : FirstWindowInput s) : FirstWindowInput (pull2 s) := by
  constructor
  · simpa only [pull2_at s 836 (by decide +kernel)] using h.1
  · intro w hw ha
    change s (pi w) = false
    apply h.2
    · intro hh
      have hfix : pi 836 = 836 := pi_fixed _ (by decide +kernel)
      exact hw (pi.injective (hh.trans hfix.symm))
    · intro hh
      have hfix := pi_address _ hh
      have he : pi w = w := pi.injective hfix
      exact ha (he ▸ hh)

theorem ready2_first (s : BasisState) (h : FirstWindowInput s) (P : ShorECDLP.Secp256k1.Point) :
    ready2 (pointWrite P s) := by
  refine ⟨?_, ?_⟩
  · rw [pull2_write]
    exact windowReady_first (pull2 s) (pull2_first s h) P
  · apply pointWrite_hot P s
    intro i
    apply h.2
    · have hi := i.isLt
      simp only [hot]
      dsimp only [Wire] at *
      omega
    · exact hot_outside_address i

def state2 (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (s : BasisState) : BasisState :=
  relabelBasis pi (bodyState coeffs Q (pull2 s))

theorem state2_correct (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (s : BasisState) (hs : ready2 s) (P : ShorECDLP.Secp256k1.Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    state2 coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s),signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s),signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩))
        else 0) s := by
  unfold state2
  rw [bodyState_correct coeffs Q (pull2 s) hs.1 P ((pull2_coordinates s).trans hP),push2_write]
  simp only [pull2_at s 836 (by decide +kernel),pull2_at s 870 (by decide +kernel),pull2_digit]

/-- Transport a coherent source body to the new compact labels. -/
theorem relabel2_coherent {s e : Nat} (p : Straight 32768 s e) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (history : Fin s → Bool)
    (hc : CoherentlyImplementsOn (p.instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready) :
    CoherentlyImplementsOn ((relabelStraight pi p).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (state2 coeffs Q))
      (fun s => ready2 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := hc.relabel pi
  have hr : CoherentlyImplementsOn
      ((p.instantiate (readConstant coeffs Q) history).relabel pi)
      ((relabelState pi).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState pi.symm)))
      (fun s => ready2 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,aligned,mass⟩ := h
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb s hs
    apply hb s
    refine ⟨hs.1.1,?_⟩
    intro i
    exact (pull2_hot s i).trans (hs.1.2 i)
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (state2 coeffs Q))
    (by intro s _; simp [state2,pull2,LinearMap.comp_apply,relabelState,ket])
  rw [relabelStraight_instantiate]
  exact he

theorem relabel2_support {s e : Nat} (p : Straight 32768 s e)
    (h : ChallengeMigration.straightWires p ⊆ newSource) :
    ChallengeMigration.straightWires (relabelStraight pi p) ⊆ List.range 1619 := by
  rw [straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr ((pi_apply v).trans_lt (pi_bound v (h hv)))

theorem base_support2 : completeBatchedSupport ⊆ List.range 1619 := by
  intro w hw
  simp only [completeBatchedSupport,resetWires,List.mem_cons,List.mem_append,
    List.mem_range,List.mem_range'_1,List.not_mem_nil,or_false] at hw
  apply List.mem_range.mpr
  dsimp only [Wire] at *; omega

end
end ShorECDLP.Entrant.PathShare

/-! ### The width-15 body on the pool bank -/

namespace ShorECDLP.Entrant.PathShare.W15
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem lay15 : ∀ b ∈ row2, BlockLay bank15 b := fun b hb => geo_lay bank15 bank15_ok b (row2_geo15 b hb)

theorem old15_lay : ∀ b ∈ row2, BlockLay old15 b := by
  intro b hb
  have hg := WEXUnlookup.row2_geometry b hb
  cases b with
  | plain code =>
    exact pair_layouts_of_placed _ _ _ _ (by simp [old15,windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair windowBits windowPaths windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    exact ⟨pair_layouts_of_placed _ _ _ _ (by simp [old15,windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp),
      WEXUnlookup.site_high_layout site hg⟩

theorem recordsP_old15 (code : Code 32768) : recordsP old15 code = WEXUnlookup.records code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    simp only [recordsP, WEXUnlookup.records, ih]
    cases b <;> rfl

theorem row2_recordsP : recordsP bank15 row2 = 1757978 := by
  rw [recordsP_eq bank15 old15 rfl rfl row2 lay15 old15_lay, recordsP_old15]
  exact WEXUnlookup.row2_records

theorem codeTP15 (code : Code 32768) : codeTP bank15 code = WEXUnlookup.ccx code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have hl : 2 ^ bank15.bits.length - 1 = 32767 := by simp [bank15, windowBits]
    have hn : (tableAddressTree bank15.high 0 1).internalNodes = 255 := WEXUnlookup.high_nodes
    simp only [codeTP, WEXUnlookup.ccx, ih]
    cases b <;> simp only [blockTP, WEXUnlookup.blockCCX, hl, hn]

theorem program_slots_old15 (code : Code 32768) (hl : ∀ b ∈ code, BlockLay old15 b) (start : Nat) :
    (WEXUnlookup.program code start).gateSlots = codeSP old15 code := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    have hb : (WEXUnlookup.blockProgram b start).gateSlots = (blockProgP old15 b start).gateSlots := by
      cases b <;> rfl
    rw [WEXUnlookup.program, castFinish_gateSlots, Straight.gateSlots_append, ih (fun d hd => hl d (by simp [hd])),
      hb, blockProgP_slots old15 b (hl b (by simp))]
    rfl

attribute [local irreducible] programP blockProgP clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx Nat.add Nat.mul

def addFixedP (start : Nat) : Straight 32768 start (start+1757978) :=
  castFinish (congrArg (fun m => start+m) row2_recordsP) (programP bank15 row2 start)

theorem addFixedP_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).run = (sourceCodeP bank15 read row2).run := by
  rw [addFixedP,castFinish_instantiate,programP_run]

theorem addFixedP_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).tCount = 7*ccx row2 := by
  rw [addFixedP,castFinish_instantiate,programP_tCount read bank15 row2 lay15,codeTP15]

theorem addFixedP_slots (start : Nat) : (addFixedP start).gateSlots =
    codeSlots windowBits (normalizeW (erase row2)) + 250725868 := by
  rw [addFixedP,castFinish_gateSlots,programP_slots bank15 row2 lay15,codeSP_congr bank15 old15 rfl rfl,
    ← program_slots_old15 row2 old15_lay start]
  exact WEXUnlookup.row2_slots start

theorem addFixedP_wellFormed (start : Nat) : (addFixedP start).WellFormed := by
  rw [addFixedP,castFinish_wellFormed]
  exact programP_wellFormed bank15 bank15_ok row2 row2_geo15 row2_physical start

theorem addFixedP_residue (start : Nat) : residue (addFixedP start) = 0 := by
  rw [addFixedP,residue_cast]
  exact programP_residue bank15 row2 start

theorem addFixedP_credit (start : Nat) : ProgramCredit (addFixedP start) (ccx row2) := by
  have hz := addFixedP_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixedP start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedP_tCount (fun _ => false) start (fun _ => false)
  omega

theorem row2_placed_old : ∀ i ∈ erase row2, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  exact (block_placed b (WEXUnlookup.row2_geometry b hb)).1 i hib

theorem wires_new_of {p : ECDSAAdd.Program} {l : List Wire} (hs : ECDSAAdd.wires p ⊆ l.toFinset)
    (h : ∀ w ∈ l, w ∈ ECDSAAdd.wires p → w ∈ newSource) : ECDSAAdd.wires p ⊆ newSource.toFinset :=
  fun w hw => List.mem_toFinset.mpr (h w (List.mem_toFinset.mp (hs hw)) hw)

theorem row2_lit_new (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ erase row2) :
    ECDSAAdd.wires p ⊆ newSource.toFinset :=
  wires_new_of (row2_oldWithin.1 p hp) (fun w h1 hw => newSource_of_old w h1
    (fun hm => row2_placed_old _ hp w (by simp [hm]) hw))


theorem row2_look_new (c : Option Wire) (ps : List (LookupPort 32768)) (hp : WInstr.lookup c ps ∈ erase row2) :
    (∀ q ∈ c, q ∈ newSource) ∧ portTargets ps ⊆ newSource := by
  have h1 := row2_oldWithin.2 c ps hp
  have h2 := row2_placed_old _ hp
  dsimp only [PlacedPair] at h2
  refine ⟨fun q hq => newSource_of_old q (h1.1 q hq) fun hm => ?_, fun w hw => newSource_of_old w (h1.2 hw) fun hm => ?_⟩
  · have hq' : lookupRoot windowRoot c = q := by
      cases c with
      | none => simp at hq
      | some q' => simp only [Option.mem_def, Option.some.injEq] at hq; simp [lookupRoot, hq]
    have h0 := h2.1
    rw [List.cons_append] at h0
    have hn := (List.nodup_cons.mp h0).1
    exact hn (by rw [hq']; exact List.mem_append_right _ hm)
  · exact List.disjoint_left.mp h2.2.2.2 (by simp [hm]) hw

theorem addFixedP_support (start : Nat) : ChallengeMigration.straightWires (addFixedP start) ⊆ newSource := by
  rw [addFixedP,support_cast]
  apply programP_support bank15 bank15_ok row2 row2_geo15 newSource
  · exact newSource_of_bounds [windowRoot] (by decide +kernel) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank15, windowBits]; decide +kernel)
  · exact newSource_of_bounds _ (by simp only [bank15, pathBank]; decide +kernel)
  · intro i
    exact newSource_of_bounds [low i] (by
      have hi := i.isLt
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [low, fixedPort, oldWork, retired]
      omega) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank15, WEXUnlookup.high]; decide +kernel)
  · exact row2_lit_new
  · exact row2_look_new

def rowSourceP (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCodeP bank15 (readConstant coeffs Q) row2

theorem rowSourceP_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSourceP coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := program_coherentP (readConstant coeffs Q) bank15 bank15_ok row2 row2_geo15 liveReady
    (rowPointState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => row2_clean pathBank pathBank_pool pathBank_flip pathBank_head coeffs Q hQ hn _ s hs)
    (fun s hs m => row2_run_any _ coeffs Q hQ hn s hs m) 0 Fin.elim0
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  rw [programP_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceP coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceP_coherent coeffs Q hQ hn)
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

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1758490) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedP (start+256))).append
      (nFastProgram (start+256+1757978))).append (suffixProgram (start+256+1757978+256)))

attribute [local irreducible] fastBodyProgram addFixedP

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank15 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram,castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (sourceCodeP bank15 (readConstant coeffs Q) row2) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedP_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank15 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceP
    rfl
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
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1757978)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row2) (prefix_credit start) hl (addFixedP_credit (start+256)) hr
    (suffix_credit (start+256+1757978+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
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
      · exact addFixedP_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem nFast_new (start : Nat) : ChallengeMigration.straightWires (nFastProgram start) ⊆ newSource := by
  apply literalFixed_support (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) 256
    ((literal_meas (n := 32768) _).trans fastWindowSign_normalized_counts.2) newSource (start := start)
  rw [ECDSAAdd.Baselines.normalize_wires]
  have hs := WEX.finiteSignMeasured_support (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p
  have cover : 870 :: 838 :: (negateYLayout streamLayout).wires streamLayout.core.generic ⊆ newSource := by
    apply newSource_of_bounds; decide +kernel
  have sub : ECDSAAdd.wires fastWindowSignProgram ⊆ ECDSAAdd.wires
      (WEX.finiteSignMeasured (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p) := by
    simp only [fastWindowSignProgram, WEX.finiteSignMeasured, ECDSAAdd.wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (fun _ h => h) WEX.TrimmedSign.reflection_wires)
      (fun _ h => h)
  exact sub.trans (hs.trans (fun w hw => List.mem_toFinset.mpr (cover (List.mem_toFinset.mp hw))))

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ newSource := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ newSource := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ newSource := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  rw [fastBodyProgram,support_cast]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,nFast_new _⟩,addFixedP_support _⟩,nFast_new _⟩,hs _⟩

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,addFixedP_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (erase row2))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.row2_measures
  have hl2 := hm.2.2.1
  rw [← hm.2.2.2.1] at hp
  rw [hm.2.1] at hc
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  norm_num [windowBits] at hc
  simp only [windowBits]
  omega

def compactProgram (start : Nat) : Straight 32768 start (start+1758490) :=
  relabelStraight pi (fastBodyProgram start)

end
end ShorECDLP.Entrant.PathShare.W15

/-! ### The width-14 body on the pool bank -/

namespace ShorECDLP.Entrant.PathShare.W14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem lay14 : ∀ b ∈ row2, BlockLay bank14 b := fun b hb => geo_lay bank14 bank14_ok b (row2_geo14 b hb)

theorem old14_lay : ∀ b ∈ row2, BlockLay old14 b := by
  intro b hb
  have hg := WEXUnlookupWidth14.row2_geometry b hb
  cases b with
  | plain code =>
    exact pair_layouts_of_placed _ _ _ _ (by simp [old14,WEXUnlookupWidth14.bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hg.1)
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair WEXUnlookupWidth14.bits windowPaths windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    exact ⟨pair_layouts_of_placed _ _ _ _ (by simp [old14,WEXUnlookupWidth14.bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hp), WEXUnlookupWidth14.site_high_layout site hg.original⟩

theorem recordsP_old14 (code : Code 32768) : recordsP old14 code = WEXUnlookupWidth14.records code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    simp only [recordsP, WEXUnlookupWidth14.records, ih]
    cases b <;> rfl

theorem row2_recordsP : recordsP bank14 row2 = 1659034 := by
  rw [recordsP_eq bank14 old14 rfl rfl row2 lay14 old14_lay, recordsP_old14]
  exact WEXUnlookupWidth14.row2_records

theorem codeTP14 (code : Code 32768) : codeTP bank14 code = WEXUnlookupWidth14.ccx code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have hl : 2 ^ bank14.bits.length - 1 = 16383 := by simp [bank14, WEXUnlookupWidth14.bits, WEX.widthBits]
    have hn : (tableAddressTree bank14.high 0 1).internalNodes = 127 := WEXUnlookupWidth14.high_nodes
    simp only [codeTP, WEXUnlookupWidth14.ccx, ih]
    cases b <;> simp only [blockTP, WEXUnlookupWidth14.blockCCX, hl, hn]

theorem program_slots_old14 (code : Code 32768) (hl : ∀ b ∈ code, BlockLay old14 b) (start : Nat) :
    (WEXUnlookupWidth14.program code start).gateSlots = codeSP old14 code := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    have hb : (WEXUnlookupWidth14.blockProgram b start).gateSlots = (blockProgP old14 b start).gateSlots := by
      cases b <;> rfl
    rw [WEXUnlookupWidth14.program, castFinish_gateSlots, Straight.gateSlots_append,
      ih (fun d hd => hl d (by simp [hd])), hb, blockProgP_slots old14 b (hl b (by simp))]
    rfl

attribute [local irreducible] programP blockProgP clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookupWidth14.ccx Nat.add Nat.mul

def addFixedP (start : Nat) : Straight 32768 start (start+1659034) :=
  castFinish (congrArg (fun m => start+m) row2_recordsP) (programP bank14 row2 start)

theorem addFixedP_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).run = (sourceCodeP bank14 read row2).run := by
  rw [addFixedP,castFinish_instantiate,programP_run]

theorem addFixedP_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).tCount = 7*WEXUnlookupWidth14.ccx row2 := by
  rw [addFixedP,castFinish_instantiate,programP_tCount read bank14 row2 lay14,codeTP14]

theorem addFixedP_slots_upper (start : Nat) : (addFixedP start).gateSlots ≤ 1000000000 := by
  rw [addFixedP,castFinish_gateSlots,programP_slots bank14 row2 lay14,codeSP_congr bank14 old14 rfl rfl,
    ← program_slots_old14 row2 old14_lay start]
  exact WEXUnlookupWidth14.row2_slots_upper start

theorem addFixedP_wellFormed (start : Nat) : (addFixedP start).WellFormed := by
  rw [addFixedP,castFinish_wellFormed]
  exact programP_wellFormed bank14 bank14_ok row2 row2_geo14 row2_physical start

theorem addFixedP_residue (start : Nat) : residue (addFixedP start) = 0 := by
  rw [addFixedP,residue_cast]
  exact programP_residue bank14 row2 start

theorem addFixedP_credit (start : Nat) : ProgramCredit (addFixedP start) (WEXUnlookupWidth14.ccx row2) := by
  have hz := addFixedP_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixedP start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedP_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixedP_support (start : Nat) : ChallengeMigration.straightWires (addFixedP start) ⊆ newSource := by
  rw [addFixedP,support_cast]
  apply programP_support bank14 bank14_ok row2 row2_geo14 newSource
  · exact newSource_of_bounds [windowRoot] (by decide +kernel) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank14, WEXUnlookupWidth14.bits, WEX.widthBits]; decide +kernel)
  · exact newSource_of_bounds _ (by simp only [bank14, pathBank]; decide +kernel)
  · intro i
    exact newSource_of_bounds [low i] (by
      have hi := i.isLt
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [low, fixedPort, oldWork, retired]
      omega) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank14, WEXUnlookupWidth14.high]; decide +kernel)
  · exact W15.row2_lit_new
  · exact W15.row2_look_new

def rowSourceP (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCodeP bank14 (readConstant coeffs Q) row2

theorem rowSourceP_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (rowSourceP coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := program_coherentP (readConstant coeffs Q) bank14 bank14_ok row2 row2_geo14 liveReady
    (WEXUnlookupWidth14.rowState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => row2_clean pathBank pathBank_pool pathBank_flip pathBank_head coeffs Q hQ hn _ s hs)
    (fun s hs m => by
      simpa only [WEXUnlookupWidth14.rowState] using
        row2_run_any (tableAddressValue WEXUnlookupWidth14.bits s) coeffs Q hQ hn s hs m) 0 Fin.elim0
  have he : WEXUnlookupWidth14.rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold WEXUnlookupWidth14.rowState rowPointState
    rw [show tableAddressValue WEXUnlookupWidth14.bits s = tableAddressValue (WEX.widthBits 14) s from rfl,
      WEX.width_table 14 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  rw [programP_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceP coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceP_coherent coeffs Q hQ hn halias)
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

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedP (start+256))).append
      (nFastProgram (start+256+1659034))).append (suffixProgram (start+256+1659034+256)))

attribute [local irreducible] fastBodyProgram addFixedP

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank14 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram,castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (sourceCodeP bank14 (readConstant coeffs Q) row2) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedP_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank14 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceP
    rfl
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
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
      WEXUnlookupWidth14.ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1659034)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (WEXUnlookupWidth14.ccx row2) (prefix_credit start) hl (addFixedP_credit (start+256)) hr
    (suffix_credit (start+256+1659034+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
        WEXUnlookupWidth14.ccx row2) := by
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
      · exact addFixedP_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ newSource := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ newSource := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ newSource := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  rw [fastBodyProgram,support_cast]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,W15.nFast_new _⟩,addFixedP_support _⟩,W15.nFast_new _⟩,hs _⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := addFixedP_slots_upper (start+256)
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  omega

def compactProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  relabelStraight pi (fastBodyProgram start)

end
end ShorECDLP.Entrant.PathShare.W14

/-! ### The body with the pool path bank, and its narrow programs -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

attribute [local irreducible] W15.fastBodyProgram W14.fastBodyProgram

def body2 : Single.WindowBody where
  records := 1758490
  tBound := 16536856
  slotBound := 2000000000
  support := List.range 1619
  reset := resetWires
  ready := ready2
  active := ready2_active
  ready_write := ready2_write
  ready_address := ready2_address
  ready_first := ready2_first
  program := W15.compactProgram
  update := state2
  correct := fun coeffs Q _ _ s hs P hP => state2_correct coeffs Q s hs P hP
  coherent := fun coeffs Q hQ hn start history =>
    relabel2_coherent _ coeffs Q history (W15.fastBodyProgram_coherent coeffs Q hQ hn start history)
  wellFormed := fun start => (relabelStraight_wellFormed pi (W15.fastBodyProgram start)).mpr
    (W15.fastBodyProgram_wellFormed start)
  slots := fun start => (relabelStraight_slots pi (W15.fastBodyProgram start)).trans_le
    (W15.fastBodyProgram_slots_upper start)
  tCount := by
    intro coeffs Q start history
    rw [W15.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W15.fastBodyProgram_tCount]
    have h := Width15Fused.fastCount_upper
    omega
  wires := fun start => relabel2_support _ (W15.fastBodyProgram_support start)
  reset_support := fun _ hw => base_support2 (List.mem_cons_of_mem 837 hw)
  skeleton_support := base_support2

def narrow15 : ModNarrow body2 15 where
  records := 1758490
  tBound := 16536856
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2
  program := W15.compactProgram
  coherent := fun coeffs Q hQ hn _ start history => body2.coherent coeffs Q hQ hn start history
  wellFormed := body2.wellFormed
  slots := body2.slots
  wires := body2.wires
  tCount := by
    intro start read history
    rw [W15.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W15.fastBodyProgram_tCount]
    have h := Width15Fused.fastCount_upper
    omega
  zero := by
    intro start
    rw [W15.compactProgram,WEXUnlookup.residue_relabel]
    exact (W15.fastBodyProgram_credit start).1
  count_eq := by
    intro start
    rw [W15.compactProgram,AndGadget.added_relabel]
    exact (W15.fastBodyProgram_credit start).2

def narrow14 : ModNarrow body2 14 where
  records := 1659546
  tBound := 15844248
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    WEXUnlookupWidth14.ccx row2
  program := W14.compactProgram
  coherent := by
    intro coeffs Q hQ hn halias start history
    have ha : WEX.WidthAliased 14 coeffs := by simpa only [WEX.WidthAliased, ModAliased, reducedAddress] using halias
    exact relabel2_coherent _ coeffs Q history (W14.fastBodyProgram_coherent coeffs Q hQ hn ha start history)
  wellFormed := fun start => (relabelStraight_wellFormed pi (W14.fastBodyProgram start)).mpr
    (W14.fastBodyProgram_wellFormed start)
  slots := fun start => (relabelStraight_slots pi (W14.fastBodyProgram start)).trans_le
    ((W14.fastBodyProgram_slots_upper start).trans (by show (1100000000 : Nat) ≤ 2000000000; decide))
  wires := fun start => relabel2_support _ (W14.fastBodyProgram_support start)
  tCount := by
    intro start read history
    rw [W14.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W14.fastBodyProgram_tCount]
    have h := WEXUnlookupWidth14.Fused.fastCount_upper
    omega
  zero := by
    intro start
    rw [W14.compactProgram,WEXUnlookup.residue_relabel]
    exact (W14.fastBodyProgram_credit start).1
  count_eq := by
    intro start
    rw [W14.compactProgram,AndGadget.added_relabel]
    exact (W14.fastBodyProgram_credit start).2

theorem alias13_14 (coeffs : Fin 32768 → PointCoeff) (h : ModAliased 13 coeffs) : ModAliased 14 coeffs := by
  intro a
  have e : reducedAddress 13 (reducedAddress 14 a) = reducedAddress 13 a := by
    apply Fin.ext
    simp only [reducedAddress]
    omega
  rw [h a, h (reducedAddress 14 a), e]

/-- No 14-bit physical windows are scheduled; the width-14 program serves them as well. -/
def narrow13 : ModNarrow body2 13 where
  records := narrow14.records
  tBound := narrow14.tBound
  credit := narrow14.credit
  program := narrow14.program
  coherent := fun coeffs Q hQ hn halias start history =>
    narrow14.coherent coeffs Q hQ hn (alias13_14 coeffs halias) start history
  wellFormed := narrow14.wellFormed
  slots := narrow14.slots
  wires := narrow14.wires
  tCount := narrow14.tCount
  zero := narrow14.zero
  count_eq := narrow14.count_eq

theorem body2_ledger : body2.support.length = 1619 ∧ body2.reset.length = 854 := by
  constructor
  · simp [body2]
  · simp [body2, resetWires]

end
end ShorECDLP.Entrant.PathShare

end

-- Entrant/SinAverage.lean
section

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

end

-- Entrant/SinAverage261.lean
section

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

end

-- Entrant/Schedule261.lean
section

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
    (hSupport : ledger.support.length ≤ 1619) (hSlot : body.slotBound ≤ 3000000000)
    (hR15 : n15.records ≤ 1659546) (hR16 : n16.records ≤ 1758490)
    (hReset : body.reset.length ≤ 854)
    (hT15 : n15.tBound ≤ 15844248) (hT16 : n16.tBound ≤ 16536856)
    (hC15 : n15.credit ≤ 2263464) (hC16 : n16.credit ≤ 2362408)
    (hq : (1938 : Wire) ∉ ledger.support) (hy : (1939 : Wire) ∉ 1938 :: ledger.support) :
    letI : Programs body := triPrograms n14 n15 n16
    Certificate officialLimits (lowerLayout 1938 entry layout) (fourEntry 1938 1939 entry)
      ⟨1621, 269869759, 543906879⟩ := by
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
  · change ledger.support.length + 2 ≤ 1621
    omega
  · change 4 * (131071 + 17 * n16.credit + 12 * n15.credit) + 55458 + 1 ≤ 269869759
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
attribute [local irreducible] WEXUnlookupWidth13.compactProgram WEXUnlookupWidth14.compactProgram WEXUnlookup.Width15Fused.fastCompactProgram WEXUnlookupWidth14.Fused.fastCompactProgram
  WEXUnlookupWidth13.bodyProgram WEXUnlookupWidth14.bodyProgram
  WEXUnlookupWidth13.ccx WEXUnlookupWidth14.ccx
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount
  WEX.literalToffolis WEX.normalizeW Nat.add Nat.mul AndGadget.added

def narrow13 : ModNarrow PathShare.body2 13 := PathShare.narrow13
def narrow14 : ModNarrow PathShare.body2 14 := PathShare.narrow14
def narrow15 : ModNarrow PathShare.body2 15 := PathShare.narrow15

theorem n14_records : narrow14.records ≤ 1659546 := by
  exact le_rfl
theorem n15_records : narrow15.records ≤ 1758490 := by
  exact le_rfl
theorem n14_cost : narrow14.tBound ≤ 15844248 := by
  exact le_rfl
theorem n15_cost : narrow15.tBound ≤ 16536856 := by
  exact le_rfl

attribute [local irreducible] narrow13 narrow14 narrow15
local instance bodyInstance : Single.WindowBody := PathShare.body2
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody PathShare.body2
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide +kernel)
    (by change (1 : Wire) ∈ resetWires; decide +kernel)
local instance coverInstance : SupportCover bodyInstance resourcesInstance := ⟨by intro w hw; exact hw⟩
local instance programInstance : Programs bodyInstance := triPrograms narrow13 narrow14 narrow15

private theorem count14_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 15844248) :
    c ≤ 2263464 := by omega
private theorem count15_bound (t c : Nat) (he : t = 7*c) (hb : t ≤ 16536856) :
    c ≤ 2362408 := by omega

theorem n14_credit : narrow14.credit ≤ 2263464 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow14.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow14.program 0) (narrow14.zero 0) read Fin.elim0
  have hc := narrow14.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count14_bound _ _ he' (ht.trans n14_cost)
theorem n15_credit : narrow15.credit ≤ 2362408 := by
  let read : ConstantBit 32768 → Bool := fun _ => false
  have ht := narrow15.tCount 0 read Fin.elim0
  have he := WEXCredit.exact_t (narrow15.program 0) (narrow15.zero 0) read Fin.elim0
  have hc := narrow15.count_eq 0
  have he' := he.trans (congrArg (fun k : Nat => 7*k) hc)
  exact count15_bound _ _ he' (ht.trans n15_cost)

def entry : StraightEntry := fourEntry 1938 1939 Flexible.entry
def layout : DecodeLayout := lowerLayout 1938 Flexible.entry Flexible.layout
def bounds : Bounds := ⟨1621, 269869759, 543906879⟩

theorem certificate : Certificate officialLimits layout entry bounds := by
  apply @matched_fused_certificate bodyInstance resourcesInstance coverInstance narrow13 narrow14 narrow15
  · change PathShare.body2.support.length ≤ 1619
    exact PathShare.body2_ledger.1.le
  · change PathShare.body2.slotBound ≤ 3000000000
    exact (by decide : (2000000000 : Nat) ≤ 3000000000)
  · exact n14_records.trans (by norm_num)
  · exact n15_records.trans (by norm_num)
  · change PathShare.body2.reset.length ≤ 854
    exact PathShare.body2_ledger.2.le
  · exact n14_cost.trans (by norm_num)
  · exact n15_cost.trans (by norm_num)
  · exact n14_credit
  · exact n15_credit
  · change (1938 : Wire) ∉ List.range 1619
    simp
  · change (1939 : Wire) ∉ 1938 :: List.range 1619
    simp
end
end ShorECDLP.Entrant.Schedule29Seventeen244.Flexible.FusedFinal

end

-- Entrant/Main.lean
section

namespace ShorECDLP.Entrant
open Challenge

def bounds : Bounds := ⟨1621,269869759,543906879⟩
noncomputable section
def entry : StraightEntry := Schedule29Seventeen244.Flexible.FusedFinal.entry
def layout : DecodeLayout := Schedule29Seventeen244.Flexible.FusedFinal.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Schedule29Seventeen244.Flexible.FusedFinal.certificate
end
end ShorECDLP.Entrant

end
