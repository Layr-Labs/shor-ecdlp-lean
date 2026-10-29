import ShorECDLP.Submission.Entrant.FastGates
import ShorECDLP.Submission.Entrant.V2.Layout
import ShorECDLP.Challenge.Official

/-! EDITABLE. One extended-precision trial.

The V2 point arithmetic (Naive circuits with a swap-based field inversion) and the Naive
wire allocation are used; each controlled point addition is the single-pass `fastCPA`.  Each phase register gains seven high-order qubits (placed above the Naive
dense envelope), so the register precision is 263 bits and one observed trial
already meets the success requirement; no reset or repetition is needed. -/

namespace ShorECDLP.Entrant
open Quantum Secp256k1 Challenge NaiveChallenge Arithmetic

local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-- One order-finding trial over the single-pass V2 point arithmetic. -/
def trialV2 (aReg bReg pointReg : List Wire) (workStart qftAncilla : Wire) (Q : Point) :
    Circuit :=
  Quantum.PhaseEstimation.hadamards (aReg ++ bReg) ++
    V2.fastOracle aReg bReg pointReg workStart G Q ++
    Quantum.iqft aReg qftAncilla ++
    Quantum.iqft bReg qftAncilla

theorem trialV2_run (aReg bReg pointReg : List Wire) (workStart qftAncilla : Wire)
    (Q : Point) (s : BasisState) :
    Quantum.run (trialV2 aReg bReg pointReg workStart qftAncilla Q) (Quantum.ket s) =
      Quantum.OrderFinding.orderFinding aReg bReg qftAncilla
        (Quantum.run (V2.fastOracle aReg bReg pointReg workStart G Q)) (Quantum.ket s) := by
  simp [trialV2, Quantum.OrderFinding.orderFinding, Quantum.run_append, LinearMap.comp_apply]


/-! ## Wire layout -/

def extA : List Wire := List.range' 14903 7
def extB : List Wire := List.range' 14910 7
def regA : List Wire := bitcoinAReg ++ extA
def regB : List Wire := bitcoinBReg ++ extB

theorem regA_length : regA.length = 263 := by
  simp [regA, extA, bitcoinAReg]

theorem regB_length : regB.length = 263 := by
  simp [regB, extB, bitcoinBReg]

theorem old_lt : ∀ w : ℕ, w ∈ bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
    V2.scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla] → w < 14903 := by
  intro w hw
  have h := V2.v2DeclaredWires_subset w hw
  have h' := List.mem_range.mp h
  rwa [V2.v2QubitCount_eq] at h'

theorem ext_bounds : ∀ w : ℕ, w ∈ extA ++ extB → 14903 ≤ w ∧ w < 14917 := by
  intro w hw
  simp only [extA, extB, List.mem_append, List.mem_range'_1] at hw
  omega

theorem ext_nodup : (extA ++ extB).Nodup := by
  rw [List.nodup_append]
  refine ⟨List.nodup_range', List.nodup_range', ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [extA, extB, List.mem_range'_1] at ha hb
  omega

theorem layoutE :
    (regA ++ regB ++ bitcoinPointReg ++ V2.scalarMulWork bitcoinWorkStart).Nodup ∧
    bitcoinQFTAncilla ∉ regA ++ regB ++ bitcoinPointReg ++ V2.scalarMulWork bitcoinWorkStart := by
  obtain ⟨_, _, _, hn, hf⟩ := V2.v2WireLayout
  have hperm : (regA ++ regB ++ bitcoinPointReg ++ V2.scalarMulWork bitcoinWorkStart).Perm
      ((bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++ V2.scalarMulWork bitcoinWorkStart) ++
        (extA ++ extB)) := by
    rw [List.perm_iff_count]
    intro x
    simp only [regA, regB, List.count_append]
    omega
  constructor
  · rw [hperm.nodup_iff, List.nodup_append]
    refine ⟨hn, ext_nodup, ?_⟩
    intro a ha b hb hab
    subst hab
    have h1 := old_lt a (List.mem_append_left _ ha)
    have h2 := ext_bounds a hb
    omega
  · intro hmem
    rcases List.mem_append.mp (hperm.subset hmem) with h | h
    · exact hf h
    · have := ext_bounds _ h
      simp [bitcoinQFTAncilla] at this

theorem support_sub : ∀ w : ℕ, w ∈ regA ++ regB ++ bitcoinPointReg ++
    V2.scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla] → w ∈ List.range 14917 := by
  intro w hw
  rw [List.mem_range]
  simp only [regA, regB, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with ((((ha | ha) | (hb | hb)) | hp) | hwk) | hanc
  · have := old_lt w (by simp only [List.mem_append]; tauto)
    omega
  · have := ext_bounds w (List.mem_append_left _ ha)
    omega
  · have := old_lt w (by simp only [List.mem_append]; tauto)
    omega
  · have := ext_bounds w (List.mem_append_right _ hb)
    omega
  · have := old_lt w (by simp only [List.mem_append]; tauto)
    omega
  · have := old_lt w (by simp only [List.mem_append]; tauto)
    omega
  · have := old_lt w (by simp only [List.mem_append, List.mem_cons]; tauto)
    omega

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

/-- Powers of `G`, powers of `Q`, then their negatives; fixed before `Q` is known. -/
def coeffE (row : Fin 1052) : PointCoeff :=
  if row.val < 263 then gPowerCoefficient row.val
  else if row.val < 526 then qPowerCoefficient (row.val - 263)
  else if row.val < 789 then gNegCoefficient (row.val - 526)
  else qNegCoefficient (row.val - 789)

def tableE : List PointCoeff := List.ofFn coeffE

theorem tableE_length : tableE.length = 1052 := by
  simp only [tableE, List.length_ofFn]

theorem tableE_get (i : Fin 1052) :
    tableE.get ⟨i.val, by rw [tableE_length]; exact i.isLt⟩ = coeffE i := by
  simp only [tableE, List.get_ofFn]
  rfl

attribute [local irreducible] tableE

def gRows : List (Fin 1052 × Fin 1052) :=
  List.ofFn fun i : Fin 263 => (⟨i.val, by omega⟩, ⟨526 + i.val, by omega⟩)
def qRows : List (Fin 1052 × Fin 1052) :=
  List.ofFn fun i : Fin 263 => (⟨263 + i.val, by omega⟩, ⟨789 + i.val, by omega⟩)

theorem coeffE_g (Q : Point) (i : Fin 263) :
    constantPoint Q (coeffE ⟨i.val, by omega⟩) = (2 ^ i.val) • G := by
  simp only [coeffE, if_pos i.isLt, gPowerCoefficient_point]

theorem coeffE_q (Q : Point) (h : order • Q = 0) (i : Fin 263) :
    constantPoint Q (coeffE ⟨263 + i.val, by omega⟩) = (2 ^ i.val) • Q := by
  simp only [coeffE, show ¬263 + i.val < 263 by omega, show 263 + i.val < 526 by omega,
    if_false, if_true, Nat.add_sub_cancel_left, qPowerCoefficient_point Q h]

theorem coeffE_gneg (Q : Point) (i : Fin 263) :
    constantPoint Q (coeffE ⟨526 + i.val, by omega⟩) = -((2 ^ i.val) • G) := by
  simp only [coeffE, show ¬526 + i.val < 263 by omega, show ¬526 + i.val < 526 by omega,
    show 526 + i.val < 789 by omega, if_false, if_true, Nat.add_sub_cancel_left,
    gNegCoefficient_point]

theorem coeffE_qneg (Q : Point) (h : order • Q = 0) (i : Fin 263) :
    constantPoint Q (coeffE ⟨789 + i.val, by omega⟩) = -((2 ^ i.val) • Q) := by
  simp only [coeffE, show ¬789 + i.val < 263 by omega, show ¬789 + i.val < 526 by omega,
    show ¬789 + i.val < 789 by omega, if_false, Nat.add_sub_cancel_left,
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
    qRows.map (fun r => constantPoint Q (coeffE r.1)) = Precompute.doublingTable 263 Q := by
  simp only [qRows, List.map_ofFn, Precompute.doublingTable]
  apply congrArg List.ofFn
  funext i
  exact coeffE_q Q h i

def trialGatesE : List (TemplateGate 1052) :=
  (PhaseEstimation.hadamards (regA ++ regB)).map TemplateGate.literal ++
    V2.fastScalarGates bitcoinPointReg bitcoinWorkStart regA gRows ++
    V2.fastScalarGates bitcoinPointReg bitcoinWorkStart regB qRows ++
    (iqft regA bitcoinQFTAncilla ++ iqft regB bitcoinQFTAncilla).map TemplateGate.literal

theorem trialGatesE_source (Q : Point) (h : order • Q = 0) :
    trialGatesE.flatMap (TemplateGate.instantiate (readConstant coeffE Q)) =
      trialV2 regA regB bitcoinPointReg bitcoinWorkStart bitcoinQFTAncilla Q := by
  simp only [trialGatesE, List.flatMap_append, literalGates_instantiate,
    V2.fastScalarGates_source coeffE Q _ _ _ gRows (gRows_neg Q),
    V2.fastScalarGates_source coeffE Q _ _ _ qRows (qRows_neg Q h),
    gRows_source, qRows_source Q h, trialV2, V2.fastOracle, V2.scalarMulTable,
    regA_length, regB_length, List.append_assoc]

/-! ## The submitted straight-line program -/

def progRaw : Straight 1052 0 (0 + (regA ++ regB).length) :=
  (constantGateProgram trialGatesE 0).append (observeWires (regA ++ regB) 0)

theorem prog_end : 0 + (regA ++ regB).length = 526 := by
  rw [List.length_append, regA_length, regB_length]

def progE : Straight 1052 0 526 := castFinish prog_end progRaw

def entryE : StraightEntry where
  coefficients := tableE
  finalCursor := 526
  program := castTable tableE_length.symm progE

theorem tableE_read (Q : Point) :
    (fun r : ConstantBit 1052 => readConstant tableE.get Q
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
      (observedTrial (trialV2 regA regB bitcoinPointReg bitcoinWorkStart
        bitcoinQFTAncilla Q) regA regB).run := by
  rw [entryE_instantiate, AdaptiveCircuit.run_seq, constantGateProgram_run,
    trialGatesE_source Q h, ← AdaptiveCircuit.run_seq]
  rfl

/-! ## Well-formedness -/

theorem trialGatesE_wellFormed : ∀ g ∈ trialGatesE, g.WellFormed := by
  obtain ⟨hn, hf⟩ := layoutE
  have hp : bitcoinPointReg.length = pointWidth := V2.v2WireLayout.2.2.1
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
    exact ((circuitWellFormed_append _ _).mpr ⟨iqft_wellFormed _ _ hfa hab.of_append_left,
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

theorem trialGatesE_support (Q : Point) :
    circuitWires (trialGatesE.flatMap (TemplateGate.instantiate
      (readConstant coeffE Q))) ⊆ List.range 14917 := by
  let support := regA ++ regB ++ bitcoinPointReg ++
    V2.scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla]
  have hh : CircuitUsesOnly support (PhaseEstimation.hadamards (regA ++ regB)) := by
    apply usesOnly_mono (hadamards_usesOnly _)
    intro w hw
    simp only [support, List.mem_append] at hw ⊢
    tauto
  have hs (cs : List Wire) (rs : List (Fin 1052 × Fin 1052))
      (hc : ∀ w ∈ cs, w ∈ regA ++ regB)
      (hnd : (cs ++ (bitcoinPointReg ++ V2.controlledPointAddWork bitcoinWorkStart)).Nodup) :
      CircuitUsesOnly support ((V2.fastScalarGates bitcoinPointReg bitcoinWorkStart cs rs).flatMap
        (TemplateGate.instantiate (readConstant coeffE Q))) := by
    apply usesOnly_mono (V2.fastScalarGates_usesOnly coeffE Q _ _ cs rs hnd)
    clear hnd
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with hw | hw | hw
    · have h := hc w hw
      simp only [support, List.mem_append] at h ⊢
      tauto
    · simp only [support, List.mem_append]; tauto
    · simp only [support, V2.scalarMulWork, List.mem_append]; tauto
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
  obtain ⟨hn, _⟩ := layoutE
  have hn' : ((regA ++ regB) ++
      (bitcoinPointReg ++ V2.controlledPointAddWork bitcoinWorkStart)).Nodup := by
    simpa only [V2.scalarMulWork, List.append_assoc] using hn
  apply (ModAddSupport.circuitUsesOnly_iff_support _ _).mp
  apply usesOnly_mono (xs := support)
  · simp only [trialGatesE, List.flatMap_append, literalGates_instantiate]
    exact usesOnly_append (usesOnly_append (usesOnly_append hh
      (hs _ _ (fun _ h => List.mem_append_left _ h)
        ((List.sublist_append_left regA regB).append (List.Sublist.refl _) |>.nodup hn')))
      (hs _ _ (fun _ h => List.mem_append_right _ h)
        ((List.sublist_append_right regA regB).append (List.Sublist.refl _) |>.nodup hn')))
      (usesOnly_append (hq _ (fun _ h => List.mem_append_left _ h))
        (hq _ (fun _ h => List.mem_append_right _ h)))
  · exact support_sub

theorem entryE_support (Q : Point) : (entryE.instantiate Q).wires ⊆ List.range 14917 := by
  intro w hw
  rw [entryE_instantiate, wires_seq] at hw
  rcases hw with hw | hw
  · rw [constantGateProgram_instantiate, gateNative_wires] at hw
    exact trialGatesE_support Q hw
  · have h := zObserve_support _ hw
    exact support_sub w (by simp only [List.mem_append] at h ⊢; tauto)

theorem entryE_qubits (Q : Point) : (resources (entryE.instantiate Q)).qubits ≤ 14917 := by
  have hs : (entryE.instantiate Q).wires.toFinset ⊆ (List.range 14917).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (entryE_support Q (List.mem_toFinset.mp hw))
  have hc := Finset.card_le_card hs
  simpa only [resources, AdaptiveCircuit.qubitCount, List.card_toFinset,
    List.dedup_eq_self.mpr List.nodup_range, List.length_range] using hc

theorem templateT_trialE : templateT trialGatesE = 22108080533782 := by
  have hh (ws : List Wire) : tCount (PhaseEstimation.hadamards ws) = 0 := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simpa [PhaseEstimation.hadamards, tCount, tCost] using ih
  have hp : bitcoinPointReg.length = pointWidth := by simp [bitcoinPointReg, pointWidth]
  simp only [trialGatesE, templateT_append, templateT_literal, hh,
    V2.fastScalarGates_templateT _ _ hp, tCount_append, tCount_iqft,
    regA_length, regB_length, gRows, qRows, List.length_ofFn]
  norm_num

theorem straightT_entryE : straightT entryE.program = 22108080533782 := by
  change straightT (castTable tableE_length.symm progE) = _
  rw [straightT_castTable, progE, straightT_castFinish, progRaw, straightT_append,
    straightT_constant, straightT_observe, templateT_trialE]

theorem entryE_tModel (Q : Point) :
    (resources (entryE.instantiate Q)).tModel ≤ 22108080533782 := by
  have h := straight_t_bound entryE.program (readConstant entryE.coefficients.get Q) Fin.elim0
  rw [straightT_entryE] at h
  exact h

theorem entryE_measurements (Q : Point) :
    (resources (entryE.instantiate Q)).measurements = 526 := by
  change (entryE.program.instantiate _ _).measurementCount = 526
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
  simp only [regA_length] at h1 h3
  simp only [regB_length] at h2 h4
  simp only [trialGatesE, List.length_append, List.length_map, hadamards_length,
    regA_length, regB_length]
  omega

theorem entryE_gateSlots : entryE.program.gateSlots ≤ 35800000001052 := by
  change (castTable tableE_length.symm progE).gateSlots ≤ _
  rw [gateSlots_castTable, progE, gateSlots_castFinish, progRaw, observedGateProgram_slots]
  have h := trialGatesE_length_le
  simp only [List.length_append, regA_length, regB_length]
  omega

end ShorECDLP.Entrant
