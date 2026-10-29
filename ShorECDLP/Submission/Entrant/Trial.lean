import ShorECDLP.Submission.Entrant.TightSupport
import Batteries.Tactic.OpenPrivate
import ShorECDLP.Submission.Entrant.V2.Layout
import ShorECDLP.Submission.Entrant.Shift.Phase
import ShorECDLP.Submission.Entrant.Shift.Fourier
import ShorECDLP.Challenge.Official

/-! EDITABLE. One extended-precision trial.

The V2 point arithmetic (Naive circuits with a swap-based field inversion) and the Naive
wire allocation are used; each controlled point addition is the single-pass `fastCPA`.  The left phase register has 263 qubits and the right one 214 (wires `0 … 476`); a half-bin
shift precedes the right register's inverse QFT and only its top 203 bits are decoded. -/

namespace ShorECDLP.Entrant
open Quantum Secp256k1 Challenge NaiveChallenge Arithmetic

local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-- Width of the left (`G`-power) register. -/
abbrev leftWidth : Nat := 263
/-- Decoded top bits of the right register. -/
abbrev rightBits : Nat := 203
/-- Undecoded low bits of the right register. -/
abbrev rightExtra : Nat := 11

/-- One order-finding trial over the single-pass V2 point arithmetic, with the half-bin
shift on the right register. -/
def trialS (aReg bReg pointReg : List Wire) (workStart qftAncilla : Wire) (Q : Point) :
    Circuit :=
  Quantum.PhaseEstimation.hadamards (aReg ++ bReg) ++
    V2.fastOracle aReg bReg pointReg workStart G Q ++
    Quantum.iqft aReg qftAncilla ++
    Quantum.OrderFinding.Two.halfShift bReg (rightBits + 1) ++
    Quantum.iqft bReg qftAncilla

theorem trialS_run (aReg bReg pointReg : List Wire) (workStart qftAncilla : Wire)
    (Q : Point) (s : BasisState) :
    Quantum.run (trialS aReg bReg pointReg workStart qftAncilla Q) (Quantum.ket s) =
      Quantum.OrderFinding.Two.orderFindingShift aReg bReg qftAncilla
        (Quantum.OrderFinding.Two.halfShift bReg (rightBits + 1))
        (Quantum.run (V2.fastOracle aReg bReg pointReg workStart G Q)) (Quantum.ket s) := by
  simp [trialS, Quantum.OrderFinding.Two.orderFindingShift, Quantum.run_append,
    LinearMap.comp_apply]

/-! ## Wire layout -/

def regA : List Wire := List.range' 0 263
def regB : List Wire := List.range' 263 214

theorem regA_length : regA.length = 263 := by simp [regA]

theorem regB_length : regB.length = 214 := by simp [regB]

theorem phase_block : bitcoinAReg ++ bitcoinBReg = List.range' 0 512 := by
  have h := List.range'_append_1 (s := 0) (m := 256) (n := 256)
  simpa [bitcoinAReg, bitcoinBReg] using h

theorem phase_split : bitcoinAReg ++ bitcoinBReg = (regA ++ regB) ++ List.range' 477 35 := by
  have h1 := List.range'_append_1 (s := 0) (m := 263) (n := 214)
  have h2 := List.range'_append_1 (s := 0) (m := 477) (n := 35)
  simp only [Nat.zero_add, Nat.reduceAdd] at h1 h2
  rw [phase_block, regA, regB, h1, h2]

theorem old_lt : ∀ w : ℕ, w ∈ bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
    V2.scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla] → w < 17473 := by
  intro w hw
  have h := V2.v2DeclaredWires_subset w hw
  have h' := List.mem_range.mp h
  rwa [V2.v2QubitCount_eq] at h'

theorem layoutE :
    (regA ++ regB ++ bitcoinPointReg ++ V2.scalarMulWork bitcoinWorkStart).Nodup ∧
    bitcoinQFTAncilla ∉ regA ++ regB ++ bitcoinPointReg ++ V2.scalarMulWork bitcoinWorkStart := by
  obtain ⟨_, _, _, hn, hf⟩ := V2.v2WireLayout
  rw [phase_split] at hn hf
  have hsub : (regA ++ regB ++ bitcoinPointReg ++ V2.scalarMulWork bitcoinWorkStart).Sublist
      ((regA ++ regB) ++ List.range' 477 35 ++ bitcoinPointReg ++
        V2.scalarMulWork bitcoinWorkStart) := by
    simp only [List.append_assoc]
    exact (List.Sublist.refl _).append ((List.Sublist.refl _).append (List.sublist_append_right _ _))
  exact ⟨hsub.nodup hn, fun h => hf (hsub.subset h)⟩

/-- Wires `0 … 476` and `512 … 17472`. -/
def supportList : List Wire := List.range' 0 477 ++ List.range' 512 16961

theorem supportList_nodup : supportList.Nodup := by
  rw [supportList, List.nodup_append]
  refine ⟨List.nodup_range', List.nodup_range', ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [List.mem_range'_1] at ha hb
  omega

theorem supportList_length : supportList.length = 17438 := by simp [supportList]

theorem support_sub : ∀ w : ℕ, w ∈ regA ++ regB ++ bitcoinPointReg ++
    V2.scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla] → w ∈ supportList := by
  obtain ⟨_, _, _, hn, hf⟩ := V2.v2WireLayout
  have hdisj : ∀ w ∈ bitcoinPointReg ++ V2.scalarMulWork bitcoinWorkStart,
      w ∉ bitcoinAReg ++ bitcoinBReg := by
    rw [List.append_assoc] at hn
    have h := (List.nodup_append.mp hn).2.2
    intro w hw hab
    exact h w hab w hw rfl
  have hanc : bitcoinQFTAncilla ∉ bitcoinAReg ++ bitcoinBReg := by
    intro h; exact hf (List.mem_append_left _ (List.mem_append_left _ h))
  have hhigh : ∀ w, w ∉ bitcoinAReg ++ bitcoinBReg → w < 17473 → w ∈ supportList := by
    intro w hw hlt
    have h512 : 512 ≤ w := by
      rcases Nat.lt_or_ge w 512 with h | h
      · refine absurd ?_ hw
        rw [phase_block]
        exact List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using h⟩
      · exact h
    exact List.mem_append_right _ (List.mem_range'_1.mpr ⟨h512, by omega⟩)
  intro w hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (((hab | hp) | hwk) | hanc')
  · have hlt : w < 477 := by
      rcases hab with h | h
      · have := List.mem_range'_1.mp (show w ∈ List.range' 0 263 from h); omega
      · have := List.mem_range'_1.mp (show w ∈ List.range' 263 214 from h); omega
    exact List.mem_append_left _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact hhigh w (hdisj w (List.mem_append_left _ hp))
      (old_lt w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hp))))
  · exact hhigh w (hdisj w (List.mem_append_right _ hwk))
      (old_lt w (List.mem_append_left _ (List.mem_append_right _ hwk)))
  · subst hanc'
    exact hhigh _ hanc (by simp [bitcoinQFTAncilla])

/-! ## Coefficient table and trial gates -/

def negPow (i : Nat) : Fin order := ⟨(order - 2^i % order) % order, Nat.mod_lt _ (by decide)⟩
def gNegCoefficient (i : Nat) : PointCoeff := ⟨negPow i, ⟨0, by decide⟩⟩
def qNegCoefficient (i : Nat) : PointCoeff := ⟨⟨0, by decide⟩, negPow i⟩

theorem negPow_nsmul (P : Point) (h : order • P = 0) (i : Nat) :
    (negPow i).val • P = -((2^i) • P) := by
  have hm : 2^i % order ≤ order := (Nat.mod_lt _ (by decide)).le
  have hs : (order - 2^i % order) • P + (2^i % order) • P = 0 := by
    rw [← add_nsmul, Nat.sub_add_cancel hm, h]
  simp only [negPow]
  rw [nsmul_mod_order P h, eq_neg_of_add_eq_zero_left hs, nsmul_mod_order P h]

theorem gNegCoefficient_point (Q : Point) (i : Nat) :
    constantPoint Q (gNegCoefficient i) = -((2^i) • G) := by
  simp only [constantPoint, gNegCoefficient, zero_nsmul, add_zero]
  exact negPow_nsmul G generator_nsmul_eq_zero i

theorem qNegCoefficient_point (Q : Point) (h : order • Q = 0) (i : Nat) :
    constantPoint Q (qNegCoefficient i) = -((2^i) • Q) := by
  simp only [constantPoint, qNegCoefficient, zero_nsmul, zero_add]
  exact negPow_nsmul Q h i

/-- 263 powers of `G`, 214 powers of `Q`, then their negatives; fixed before `Q` is known. -/
def coeffE (row : Fin 954) : PointCoeff :=
  if row.val < 263 then gPowerCoefficient row.val
  else if row.val < 477 then qPowerCoefficient (row.val - 263)
  else if row.val < 740 then gNegCoefficient (row.val - 477)
  else qNegCoefficient (row.val - 740)

def tableE : List PointCoeff := List.ofFn coeffE

theorem tableE_length : tableE.length = 954 := by
  simp only [tableE, List.length_ofFn]

theorem tableE_get (i : Fin 954) :
    tableE.get ⟨i.val, by rw [tableE_length]; exact i.isLt⟩ = coeffE i := by
  simp only [tableE, List.get_ofFn]
  rfl

attribute [local irreducible] tableE

def gRows : List (Fin 954 × Fin 954) :=
  List.ofFn fun i : Fin 263 => (⟨i.val, by omega⟩, ⟨477 + i.val, by omega⟩)
def qRows : List (Fin 954 × Fin 954) :=
  List.ofFn fun i : Fin 214 => (⟨263 + i.val, by omega⟩, ⟨740 + i.val, by omega⟩)

theorem coeffE_g (Q : Point) (i : Fin 263) :
    constantPoint Q (coeffE ⟨i.val, by omega⟩) = (2 ^ i.val) • G := by
  simp only [coeffE, if_pos i.isLt, gPowerCoefficient_point]

theorem coeffE_q (Q : Point) (h : order • Q = 0) (i : Fin 214) :
    constantPoint Q (coeffE ⟨263 + i.val, by omega⟩) = (2 ^ i.val) • Q := by
  simp only [coeffE, show ¬263 + i.val < 263 by omega, show 263 + i.val < 477 by omega,
    if_false, if_true, Nat.add_sub_cancel_left, qPowerCoefficient_point Q h]

theorem coeffE_gneg (Q : Point) (i : Fin 263) :
    constantPoint Q (coeffE ⟨477 + i.val, by omega⟩) = -((2 ^ i.val) • G) := by
  simp only [coeffE, show ¬477 + i.val < 263 by omega, show ¬477 + i.val < 477 by omega,
    show 477 + i.val < 740 by omega, if_false, if_true, Nat.add_sub_cancel_left,
    gNegCoefficient_point]

theorem coeffE_qneg (Q : Point) (h : order • Q = 0) (i : Fin 214) :
    constantPoint Q (coeffE ⟨740 + i.val, by omega⟩) = -((2 ^ i.val) • Q) := by
  simp only [coeffE, show ¬740 + i.val < 263 by omega, show ¬740 + i.val < 477 by omega,
    show ¬740 + i.val < 740 by omega, if_false, Nat.add_sub_cancel_left,
    qNegCoefficient_point Q h]

theorem gRows_neg (Q : Point) :
    ∀ r ∈ gRows, constantPoint Q (coeffE r.2) = -constantPoint Q (coeffE r.1) := by
  intro r hr
  simp only [gRows, List.mem_ofFn] at hr
  obtain ⟨i, rfl⟩ := hr
  rw [coeffE_gneg, coeffE_g]

theorem qRows_neg (Q : Point) (h : order • Q = 0) :
    ∀ r ∈ qRows, constantPoint Q (coeffE r.2) = -constantPoint Q (coeffE r.1) := by
  intro r hr
  simp only [qRows, List.mem_ofFn] at hr
  obtain ⟨i, rfl⟩ := hr
  rw [coeffE_qneg Q h, coeffE_q Q h]

theorem gRows_source (Q : Point) :
    gRows.map (fun r => constantPoint Q (coeffE r.1)) = Precompute.doublingTable 263 G := by
  simp only [gRows, List.map_ofFn, Precompute.doublingTable]
  apply congrArg List.ofFn
  funext i
  exact coeffE_g Q i

theorem qRows_source (Q : Point) (h : order • Q = 0) :
    qRows.map (fun r => constantPoint Q (coeffE r.1)) = Precompute.doublingTable 214 Q := by
  simp only [qRows, List.map_ofFn, Precompute.doublingTable]
  apply congrArg List.ofFn
  funext i
  exact coeffE_q Q h i

def trialGatesE : List (TemplateGate 954) :=
  (PhaseEstimation.hadamards (regA ++ regB)).map TemplateGate.literal ++
    V2.fastScalarGates bitcoinPointReg bitcoinWorkStart regA gRows ++
    V2.fastScalarGates bitcoinPointReg bitcoinWorkStart regB qRows ++
    (iqft regA bitcoinQFTAncilla ++ Quantum.OrderFinding.Two.halfShift regB (rightBits + 1) ++
      iqft regB bitcoinQFTAncilla).map TemplateGate.literal

theorem trialGatesE_source (Q : Point) (h : order • Q = 0) :
    trialGatesE.flatMap (TemplateGate.instantiate (readConstant coeffE Q)) =
      trialS regA regB bitcoinPointReg bitcoinWorkStart bitcoinQFTAncilla Q := by
  simp only [trialGatesE, List.flatMap_append, literalGates_instantiate,
    V2.fastScalarGates_source coeffE Q _ _ _ gRows (gRows_neg Q),
    V2.fastScalarGates_source coeffE Q _ _ _ qRows (qRows_neg Q h),
    gRows_source, qRows_source Q h, trialS, V2.fastOracle, V2.scalarMulTable,
    regA_length, regB_length, List.append_assoc]

/-- The concrete oracle of the trial (fixed `Fact (Nat.Prime p)` instance of this file). -/
noncomputable def oracleS (Q : Point) : State →ₗ[ℂ] State :=
  Quantum.run (V2.fastOracle regA regB bitcoinPointReg bitcoinWorkStart G Q)

set_option maxRecDepth 100000 in
theorem trialS_run_ket (Q : Point) (s : BasisState) :
    Quantum.run (trialS regA regB bitcoinPointReg bitcoinWorkStart bitcoinQFTAncilla Q)
        (Quantum.ket s) =
      Quantum.OrderFinding.Two.orderFindingShift regA regB bitcoinQFTAncilla
        (Quantum.OrderFinding.Two.halfShift regB (rightBits + 1)) (oracleS Q) (Quantum.ket s) := by
  unfold oracleS
  exact trialS_run regA regB bitcoinPointReg bitcoinWorkStart bitcoinQFTAncilla Q s

/-! ## The submitted straight-line program -/

def progRaw : Straight 954 0 (0 + (regA ++ regB).length) :=
  (constantGateProgram trialGatesE 0).append (observeWires (regA ++ regB) 0)

theorem prog_end : 0 + (regA ++ regB).length = 477 := by
  rw [List.length_append, regA_length, regB_length]

def progE : Straight 954 0 477 := castFinish prog_end progRaw

def entryE : StraightEntry where
  coefficients := tableE
  finalCursor := 477
  program := castTable tableE_length.symm progE

theorem tableE_read (Q : Point) :
    (fun r : ConstantBit 954 => readConstant tableE.get Q
      ⟨Fin.cast tableE_length.symm r.point, r.field, r.bit⟩) = readConstant coeffE Q := by
  funext r
  have hg : tableE.get (Fin.cast tableE_length.symm r.point) = coeffE r.point :=
    tableE_get r.point
  simp only [readConstant]
  rw [hg]

theorem entryE_instantiate (Q : Point) :
    entryE.instantiate Q =
      ((constantGateProgram trialGatesE 0).instantiate (readConstant coeffE Q) Fin.elim0).seq
        (zObserve (regA ++ regB)) := by
  dsimp only [StraightEntry.instantiate, entryE]
  rw [castTable_instantiate, tableE_read, progE, instantiate_castFinish, progRaw,
    constantGateProgram_append_instantiate, observeWires_instantiate]

theorem entryE_run (Q : Point) (h : order • Q = 0) :
    (entryE.instantiate Q).run =
      (observedTrial (trialS regA regB bitcoinPointReg bitcoinWorkStart
        bitcoinQFTAncilla Q) regA regB).run := by
  rw [entryE_instantiate, AdaptiveCircuit.run_seq, constantGateProgram_run,
    trialGatesE_source Q h, ← AdaptiveCircuit.run_seq]
  rfl

/-! ## Well-formedness -/

theorem trialGatesE_wellFormed : ∀ g ∈ trialGatesE, g.WellFormed := by
  obtain ⟨hn, hf⟩ := layoutE
  have hn' : ((regA ++ regB) ++
      (bitcoinPointReg ++ V2.controlledPointAddWork bitcoinWorkStart)).Nodup := by
    simpa only [V2.scalarMulWork, List.append_assoc] using hn
  have ha' : (regA ++ (bitcoinPointReg ++ V2.controlledPointAddWork bitcoinWorkStart)).Nodup := by
    exact (List.sublist_append_left regA regB).append (List.Sublist.refl _) |>.nodup hn'
  have hb' : (regB ++ (bitcoinPointReg ++ V2.controlledPointAddWork bitcoinWorkStart)).Nodup := by
    exact (List.sublist_append_right regA regB).append (List.Sublist.refl _) |>.nodup hn'
  have hab := hn'.of_append_left
  have hfa : bitcoinQFTAncilla ∉ regA := by
    intro h; exact hf (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl h)))
  have hfb : bitcoinQFTAncilla ∉ regB := by
    intro h; exact hf (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr h)))
  intro g hg
  simp only [trialGatesE, List.mem_append] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    have hh : CircuitWellFormed (PhaseEstimation.hadamards (regA ++ regB)) := by
      intro g hg
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
      trivial
    exact hh a ha
  · exact V2.fastScalarGates_wellFormed _ _ _ _ ha' g hg
  · exact V2.fastScalarGates_wellFormed _ _ _ _ hb' g hg
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact ((circuitWellFormed_append _ _).mpr ⟨(circuitWellFormed_append _ _).mpr
      ⟨iqft_wellFormed _ _ hfa hab.of_append_left,
        Quantum.OrderFinding.Two.halfShift_wellFormed _ _⟩,
      iqft_wellFormed _ _ hfb hab.of_append_right⟩) a ha

set_option maxRecDepth 100000 in
theorem progE_wellFormed : progE.WellFormed := by
  unfold progE
  rw [wellFormed_castFinish]
  unfold progRaw
  exact straight_append_wellFormed _ _
    (constantGateProgram_wellFormed _ _ trialGatesE_wellFormed) (observeWires_wellFormed _ _)

attribute [local irreducible] Straight.WellFormed progE

theorem entryE_wellFormed : entryE.program.WellFormed :=
  Eq.mpr (castTable_wellFormed tableE_length.symm progE) progE_wellFormed

/-! ## Resources -/

/-- Every wire the trial can touch, as disjoint ranges: the phase registers, the point
register through the first branch ancilla (512 … 1539), the local point-addition block below
the unused `selected` register, the add and multiply engines, and the blocks of the shifted
inversion engine that its forward sweep touches. -/
def qubitRanges : List (Nat × Nat) :=
  [(0, 263), (263, 214), (512, 1028), (2052, 3599), (6164, 1542), (7706, 1), (7963, 257),
    (8220, 1), (8477, 257), (8734, 257), (9248, 7710), (16958, 1), (17215, 1), (17472, 1)]

def qubitWires : List Wire := qubitRanges.flatMap (fun r => List.range' r.1 r.2)

theorem qubitWires_length : qubitWires.length = 15132 := by
  simp [qubitWires, qubitRanges]

def sortedRanges : List (Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a.1 + a.2 ≤ b.1) && sortedRanges (b :: t)

theorem sortedRanges_head : ∀ (r : Nat × Nat) (rs : List (Nat × Nat)),
    sortedRanges (r :: rs) = true → ∀ s ∈ rs, r.1 + r.2 ≤ s.1
  | _, [], _, s, hs => by simp at hs
  | r, b :: t, h, s, hs => by
    simp only [sortedRanges, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · have := sortedRanges_head b t h.2 s hs
      omega

theorem sortedRanges_tail : ∀ (r : Nat × Nat) (rs : List (Nat × Nat)),
    sortedRanges (r :: rs) = true → sortedRanges rs = true
  | _, [], _ => rfl
  | _, _ :: _, h => by
    simp only [sortedRanges, Bool.and_eq_true] at h
    exact h.2

theorem ranges_nodup : ∀ (rs : List (Nat × Nat)), sortedRanges rs = true →
    (rs.flatMap (fun r => List.range' r.1 r.2)).Nodup
  | [], _ => List.nodup_nil
  | r :: rs, h => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨List.nodup_range', ranges_nodup rs (sortedRanges_tail r rs h), ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨s, hs, hbs⟩ := List.mem_flatMap.mp hb
    have h1 := sortedRanges_head r rs h s hs
    simp only [List.mem_range'_1] at ha hbs
    omega

theorem qubitWires_nodup : qubitWires.Nodup := ranges_nodup qubitRanges (by decide)

theorem qw_of (a n : Nat) (hmem : (a, n) ∈ qubitRanges) (w : Wire) (h : w ∈ List.range' a n) :
    w ∈ qubitWires :=
  List.mem_flatMap.mpr ⟨(a, n), hmem, h⟩

theorem qw_range (a n x m : Nat) (hmem : (a, n) ∈ qubitRanges) (hx : a ≤ x) (hm : x + m ≤ a + n)
    (w : Wire) (h : w ∈ List.range' x m) : w ∈ qubitWires := by
  apply qw_of a n hmem
  simp only [List.mem_range'_1] at h ⊢
  omega

theorem qw_shift (o a n : Nat) (hmem : (o + a, n) ∈ qubitRanges) (w : Wire)
    (h : w ∈ V2.shiftWires o (List.range' a n)) : w ∈ qubitWires := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
  apply qw_of (o + a) n hmem
  simp only [List.mem_range'_1] at hv ⊢
  omega

theorem tight_sub : ∀ w : ℕ, w ∈ regA ++ regB ++ bitcoinPointReg ++
    V2.tightWork bitcoinWorkStart ++ [bitcoinQFTAncilla] → w ∈ qubitWires := by
  intro w hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with ((((ha | hb) | hp) | hwk) | hanc)
  · exact qw_of 0 263 (by decide) w ha
  · exact qw_of 263 214 (by decide) w hb
  · exact qw_range 512 1028 512 513 (by decide) (by norm_num) (by norm_num) w hp
  · simp only [V2.tightWork, V2.tightPW, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hwk
    have ht : V2.controlledPointAddTemp bitcoinWorkStart = List.range' 1026 513 := rfl
    have ha : V2.controlledPointAddAuxStart bitcoinWorkStart = 1539 := rfl
    have hpw : V2.controlledPointAddPointWorkStart 1539 = 2052 := rfl
    have hoff : V2.pointAddArithmeticOffset 2052 = 6164 := rfl
    have hdo : V2.dirtyOffset 2052 = 8734 := rfl
    rw [ht, ha, hpw] at hwk
    rcases hwk with (h | h) | (h | (h | h))
    · exact qw_range 512 1028 1026 513 (by decide) (by norm_num) (by norm_num) w h
    · exact qw_range 512 1028 1539 1 (by decide) (by norm_num) (by norm_num) w
        (by rw [h]; exact List.mem_range'_1.mpr ⟨le_rfl, by norm_num⟩)
    · exact qw_of 2052 3599 (by decide) w h
    · rw [hoff] at h
      simp only [V2.addMulList, V2.shiftWires, List.map_append, List.mem_append] at h
      rcases h with (((h | h) | h) | h) | h
      · exact qw_shift 6164 0 1542 (by decide) w h
      · exact qw_shift 6164 1542 1 (by decide) w h
      · exact qw_shift 6164 1799 257 (by decide) w h
      · exact qw_shift 6164 2056 1 (by decide) w h
      · exact qw_shift 6164 2313 257 (by decide) w h
    · simp only [V2.dirtyEng, hdo, V2.Engine.engList, Entrant.LowInv.engList, V2.shiftWires,
        List.map_append, List.mem_append] at h
      rcases h with ((((h | h) | h) | h) | h)
      · exact qw_shift 8734 0 257 (by decide) w h
      · exact qw_shift 8734 514 7710 (by decide) w h
      · exact qw_shift 8734 8224 1 (by decide) w h
      · exact qw_shift 8734 8481 1 (by decide) w h
      · exact qw_shift 8734 8738 1 (by decide) w h
  · subst hanc
    exact qw_range 512 1028 1025 1 (by decide) (by norm_num) (by norm_num) _
      (List.mem_range'_1.mpr ⟨le_rfl, by simp [bitcoinQFTAncilla]⟩)

theorem trialGatesE_support (Q : Point) :
    circuitWires (trialGatesE.flatMap (TemplateGate.instantiate
      (readConstant coeffE Q))) ⊆ qubitWires := by
  let support := regA ++ regB ++ bitcoinPointReg ++
    V2.tightWork bitcoinWorkStart ++ [bitcoinQFTAncilla]
  have hh : CircuitUsesOnly support (PhaseEstimation.hadamards (regA ++ regB)) := by
    apply usesOnly_mono (hadamards_usesOnly _)
    intro w hw
    simp only [support, List.mem_append] at hw ⊢
    tauto
  have hs (cs : List Wire) (rs : List (Fin 954 × Fin 954))
      (hc : ∀ w ∈ cs, w ∈ regA ++ regB) :
      CircuitUsesOnly support ((V2.fastScalarGates bitcoinPointReg bitcoinWorkStart cs rs).flatMap
        (TemplateGate.instantiate (readConstant coeffE Q))) := by
    apply usesOnly_mono (V2.fastScalarGates_usesOnly_tight coeffE Q _ _ cs rs)
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with hw | hw | hw
    · have h := hc w hw
      simp only [support, List.mem_append] at h ⊢
      tauto
    · simp only [support, List.mem_append]; tauto
    · simp only [support, List.mem_append]; tauto
  have hq (cs : List Wire) (hc : ∀ w ∈ cs, w ∈ regA ++ regB) :
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
  have hsh : CircuitUsesOnly support
      (Quantum.OrderFinding.Two.halfShift regB (rightBits + 1)) := by
    apply usesOnly_mono (Quantum.OrderFinding.Two.halfShift_usesOnly regB _)
    intro w hw
    simp only [support, List.mem_append]
    tauto
  apply (ModAddSupport.circuitUsesOnly_iff_support _ _).mp
  apply usesOnly_mono (xs := support)
  · simp only [trialGatesE, List.flatMap_append, literalGates_instantiate]
    exact usesOnly_append (usesOnly_append (usesOnly_append hh
      (hs _ _ (fun _ h => List.mem_append_left _ h)))
      (hs _ _ (fun _ h => List.mem_append_right _ h)))
      (usesOnly_append (usesOnly_append (hq _ (fun _ h => List.mem_append_left _ h)) hsh)
        (hq _ (fun _ h => List.mem_append_right _ h)))
  · exact tight_sub

theorem entryE_support (Q : Point) : (entryE.instantiate Q).wires ⊆ qubitWires := by
  intro w hw
  rw [entryE_instantiate, wires_seq] at hw
  rcases hw with hw | hw
  · rw [constantGateProgram_instantiate, gateNative_wires] at hw
    exact trialGatesE_support Q hw
  · have h := zObserve_support _ hw
    exact tight_sub w (by simp only [List.mem_append] at h ⊢; tauto)

theorem entryE_qubits (Q : Point) : (resources (entryE.instantiate Q)).qubits ≤ 15132 := by
  have hs : (entryE.instantiate Q).wires.toFinset ⊆ qubitWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (entryE_support Q (List.mem_toFinset.mp hw))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup qubitWires_nodup, qubitWires_length] at hc
  simpa only [resources, AdaptiveCircuit.qubitCount, List.card_toFinset] using hc

theorem templateT_trialE : templateT trialGatesE = 10131447167400 := by
  have hh (ws : List Wire) : tCount (PhaseEstimation.hadamards ws) = 0 := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simpa [PhaseEstimation.hadamards, tCount, tCost] using ih
  have hp : bitcoinPointReg.length = pointWidth := by simp [bitcoinPointReg, pointWidth]
  have hsh : tCount (Quantum.OrderFinding.Two.halfShift regB (rightBits + 1)) = 204 :=
    Quantum.OrderFinding.Two.halfShift_tCount regB _ (by rw [regB_length]; decide)
  simp only [trialGatesE, templateT_append, templateT_literal, hh,
    V2.fastScalarGates_templateT _ _ hp, tCount_append, tCount_iqft, hsh,
    regA_length, regB_length, gRows, qRows, List.length_ofFn]
  norm_num

theorem straightT_entryE : straightT entryE.program = 10131447167400 := by
  change straightT (castTable tableE_length.symm progE) = _
  rw [straightT_castTable, progE, straightT_castFinish, progRaw, straightT_append,
    straightT_constant, straightT_observe, templateT_trialE]

theorem entryE_tModel (Q : Point) :
    (resources (entryE.instantiate Q)).tModel ≤ 10131447167400 := by
  have h := straight_t_bound entryE.program (readConstant entryE.coefficients.get Q) Fin.elim0
  rw [straightT_entryE] at h
  exact h

theorem entryE_measurements (Q : Point) :
    (resources (entryE.instantiate Q)).measurements = 477 := by
  change (entryE.program.instantiate _ _).measurementCount = 477
  rw [Straight.measurementCount]
  rfl

theorem hadamards_length (ws : List Wire) : (PhaseEstimation.hadamards ws).length = ws.length := by
  simp [PhaseEstimation.hadamards]

theorem trialGatesE_length_le : trialGatesE.length ≤ 35800000000000 := by
  have hp : bitcoinPointReg.length = 513 := by
    simp only [bitcoinPointReg, List.length_range']; rfl
  have h1 := V2.fastScalarGates_length_le bitcoinPointReg bitcoinWorkStart hp regA gRows
  have h2 := V2.fastScalarGates_length_le bitcoinPointReg bitcoinWorkStart hp regB qRows
  have h3 := iqft_length_le regA bitcoinQFTAncilla
  have h4 := iqft_length_le regB bitcoinQFTAncilla
  have h5 : (Quantum.OrderFinding.Two.halfShift regB (rightBits + 1)).length ≤ 204 :=
    Quantum.OrderFinding.Two.halfShift_length_le regB (rightBits + 1)
  simp only [regA_length] at h1 h3
  simp only [regB_length] at h2 h4
  simp only [trialGatesE, List.length_append, List.length_map, hadamards_length,
    regA_length, regB_length]
  omega

theorem entryE_gateSlots : entryE.program.gateSlots ≤ 35800000000954 := by
  change (castTable tableE_length.symm progE).gateSlots ≤ _
  rw [gateSlots_castTable, progE, gateSlots_castFinish, progRaw, observedGateProgram_slots]
  have h := trialGatesE_length_le
  simp only [List.length_append, regA_length, regB_length]
  omega

end ShorECDLP.Entrant
