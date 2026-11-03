import ShorECDLP.Submission.Entrant.MainB
import ShorECDLP.Submission.Entrant.FusedCore

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
