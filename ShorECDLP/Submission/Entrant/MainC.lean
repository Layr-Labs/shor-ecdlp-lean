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

-- Corner row (from 3164f15b CornerRow / CornerRow14)
section

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

end
