import ShorECDLP.Submission.Naive.QFT.Proofs.Count

namespace ShorECDLP.Entrant
open Quantum
noncomputable section

/-- Four parity phases implement Toffoli/phase/Toffoli, including for a dirty
ancilla. Every parity is computed and uncomputed by Clifford gates. -/
def parityPhase (k : Nat) (c t a : Wire) : Circuit :=
  [.P .forward (k+1) a,
   .CX c a, .P .forward (k+1) a,
   .CX t a, .P .inverse (k+1) a,
   .CX c a, .P .forward (k+1) a,
   .CX t a]

theorem phaseCoeff_half (k : Nat) :
    phaseCoeff .forward (k+1) * phaseCoeff .forward (k+1) =
      phaseCoeff .forward k := by
  have h : (2 * Real.pi / (2 : ℝ) ^ (k+1)) +
      (2 * Real.pi / (2 : ℝ) ^ (k+1)) = 2 * Real.pi / (2 : ℝ) ^ k := by
    rw [pow_succ, div_mul_eq_div_div]
    ring
  unfold phaseCoeff phaseAngle
  rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, h]

def bitPhase (dir : PhaseDir) (k : Nat) (b : Bool) : ℂ :=
  if b then phaseCoeff dir k else 1

private theorem xor_cancel (x y : Bool) : Bool.xor (Bool.xor x y) y = x := by
  cases x <;> cases y <;> rfl

private theorem xor_middle (x y z : Bool) :
    Bool.xor (Bool.xor (Bool.xor x y) z) y = Bool.xor x z := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem upd_overwrite (s : BasisState) (a : Wire) (b d : Bool) :
    s[a ↦ b][a ↦ d] = s[a ↦ d] := by
  funext w
  by_cases hw : w = a <;> simp [upd, hw]

private theorem upd_original (s : BasisState) (a : Wire) : s[a ↦ s a] = s := by
  funext w
  by_cases hw : w = a <;> simp [upd, hw]

private theorem phase_step (dir : PhaseDir) (k a : Nat) (tail : Circuit) (s : BasisState) :
    run (.P dir k a :: tail) (ket s) =
      bitPhase dir k (s a) • run tail (ket s) := by
  rw [run_cons, applyGate_P_ket, map_smul]
  rfl

private theorem cx_step (c a : Wire) (tail : Circuit) (s : BasisState) :
    run (.CX c a :: tail) (ket s) =
      run tail (ket (s[a ↦ Bool.xor (s a) (s c)])) := by
  rw [run_cons, applyGate_CX_ket]

private theorem ccx_step (c t a : Wire) (tail : Circuit) (s : BasisState) :
    run (.CCX c t a :: tail) (ket s) =
      run tail (ket (s[a ↦ Bool.xor (s a) (s c && s t)])) := by
  rw [run_cons, applyGate_CCX_ket]

theorem parityPhase_action (k : Nat) (c t a : Wire)
    (hca : c ≠ a) (hta : t ≠ a) (s : BasisState) :
    run (parityPhase k c t a) (ket s) =
      (bitPhase .forward (k+1) (s a) *
        (bitPhase .forward (k+1) (s a ^^ s c) *
          (bitPhase .inverse (k+1) ((s a ^^ s c) ^^ s t) *
            bitPhase .forward (k+1) (s a ^^ s t)))) • ket s := by
  have uc (u : BasisState) (b : Bool) : u[a ↦ b] c = u c := upd_other u a b hca
  have ut (u : BasisState) (b : Bool) : u[a ↦ b] t = u t := upd_other u a b hta
  simp only [parityPhase, phase_step, cx_step, run_nil, uc, ut, upd_same, upd_overwrite,
    xor_middle, xor_cancel, upd_original, smul_smul, bitPhase]

theorem cPhase_action (k : Nat) (c t a : Wire)
    (hca : c ≠ a) (hta : t ≠ a) (s : BasisState) :
    run (cPhase k c t a) (ket s) =
      bitPhase .forward k (s a ^^ (s c && s t)) • ket s := by
  have uc (u : BasisState) (b : Bool) : u[a ↦ b] c = u c := upd_other u a b hca
  have ut (u : BasisState) (b : Bool) : u[a ↦ b] t = u t := upd_other u a b hta
  simp only [cPhase, phase_step, ccx_step, run_nil, uc, ut, upd_same, upd_overwrite,
    xor_cancel, upd_original, bitPhase]

theorem parityPhase_ket (k : Nat) (c t a : Wire)
    (hca : c ≠ a) (hta : t ≠ a) (s : BasisState) :
    run (parityPhase k c t a) (ket s) =
      run (cPhase k c t a) (ket s) := by
  rw [parityPhase_action k c t a hca hta s, cPhase_action k c t a hca hta s]
  have hcanc : phaseCoeff .forward (k+1) * phaseCoeff .inverse (k+1) = 1 :=
    phaseCoeff_mul_adjoint .forward (k+1)
  have hican : phaseCoeff .inverse (k+1) * phaseCoeff .forward (k+1) = 1 :=
    phaseCoeff_adjoint_mul .forward (k+1)
  congr 1
  cases hc : s c <;> cases ht : s t <;> cases ha : s a <;>
    simp [bitPhase, phaseCoeff_half, hcanc, hican]

theorem parityPhase_eq (k : Nat) (c t a : Wire)
    (hca : c ≠ a) (hta : t ≠ a) :
    run (parityPhase k c t a) = run (cPhase k c t a) := by
  apply Finsupp.lhom_ext
  intro s z
  have hs : Finsupp.single s z = z • ket s := by simp [ket]
  rw [hs, map_smul, map_smul, parityPhase_ket k c t a hca hta s]

def phaseLayer (target anc : Wire) : List Wire → Nat → Circuit
  | [], _ => []
  | c :: cs, k => parityPhase k c target anc ++ phaseLayer target anc cs (k+1)

def core (anc : Wire) : List Wire → Circuit
  | [] => []
  | target :: rest => [.H target] ++ phaseLayer target anc rest 2 ++ core anc rest

def forwardQFT (r : List Wire) (anc : Wire) : Circuit :=
  core anc r.reverse ++ bitReverse r

def inverseQFT (r : List Wire) (anc : Wire) : Circuit :=
  Circuit.adjoint (forwardQFT r anc)

theorem phaseLayer_eq (t a : Wire) (cs : List Wire) (k : Nat)
    (ht : t ≠ a) (hc : a ∉ cs) :
    run (phaseLayer t a cs k) = run (qftPhaseLayer t a cs k) := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at hc
    simp only [phaseLayer, qftPhaseLayer, run_append_map,
      parityPhase_eq k c t a (Ne.symm hc.1) ht, ih (k+1) hc.2]

theorem core_eq (a : Wire) (r : List Wire) (ha : a ∉ r) :
    run (core a r) = run (qftCoreMSB a r) := by
  induction r with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.mem_cons, not_or] at ha
    simp only [core, qftCoreMSB, run_append_map,
      phaseLayer_eq t a rest 2 (Ne.symm ha.1) ha.2, ih ha.2]

theorem forwardQFT_eq (r : List Wire) (a : Wire) (ha : a ∉ r) :
    run (forwardQFT r a) = run (qft r a) := by
  simp only [forwardQFT, qft, qftCore, run_append_map,
    core_eq a r.reverse (by simpa using ha)]

theorem parityPhase_wf (k c t a : Nat) (hc : c ≠ a) (ht : t ≠ a) :
    CircuitWellFormed (parityPhase k c t a) := by
  simp [parityPhase, CircuitWellFormed, Gate.WellFormed, hc, ht]

theorem phaseLayer_wf (t a : Wire) (cs : List Wire) (k : Nat)
    (ht : t ≠ a) (hc : a ∉ cs) : CircuitWellFormed (phaseLayer t a cs k) := by
  induction cs generalizing k with
  | nil => simp [phaseLayer]
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at hc
    exact (circuitWellFormed_append _ _).mpr
      ⟨parityPhase_wf k c t a (Ne.symm hc.1) ht, ih (k+1) hc.2⟩

theorem core_wf (a : Wire) (r : List Wire) (ha : a ∉ r) :
    CircuitWellFormed (core a r) := by
  induction r with
  | nil => simp [core]
  | cons t rest ih =>
    simp only [List.mem_cons, not_or] at ha
    exact (circuitWellFormed_append _ _).mpr
      ⟨(circuitWellFormed_append _ _).mpr
        ⟨by simp [CircuitWellFormed, Gate.WellFormed],
          phaseLayer_wf t a rest 2 (Ne.symm ha.1) ha.2⟩, ih ha.2⟩

theorem forwardQFT_wf (r : List Wire) (a : Wire) (ha : a ∉ r) (hr : r.Nodup) :
    CircuitWellFormed (forwardQFT r a) := by
  exact (circuitWellFormed_append _ _).mpr
    ⟨core_wf a r.reverse (by simpa using ha), bitReverse_wellFormed r hr⟩

theorem inverseQFT_eq (r : List Wire) (a : Wire) (ha : a ∉ r) (hr : r.Nodup) :
    run (inverseQFT r a) = run (iqft r a) := by
  apply LinearMap.ext
  intro ψ
  have hn := forwardQFT_wf r a ha hr
  have ho := qft_wellFormed r a ha hr
  calc
    _ = run (inverseQFT r a) (run (qft r a) (run (iqft r a) ψ)) := by
      rw [iqft, run_run_adjoint _ ho]
    _ = _ := by
      rw [← forwardQFT_eq r a ha]
      exact run_adjoint_run _ hn _

theorem phaseLayer_t (t a : Wire) (cs : List Wire) (k : Nat) :
    tCount (phaseLayer t a cs k) = 4 * cs.length := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih =>
    rw [phaseLayer, tCount_append, ih]
    have hp : tCount (parityPhase k c t a) = 4 := rfl
    rw [hp, List.length_cons]
    omega

theorem core_t (a : Wire) (ws : List Wire) :
    tCount (core a ws) = 4 * (∑ i ∈ Finset.range ws.length, i) := by
  induction ws with
  | nil => simp [core]
  | cons t rest ih =>
    rw [core, tCount_append, tCount_append, phaseLayer_t, ih,
      List.length_cons, Finset.sum_range_succ]
    have hh : tCount [Gate.H t] = 0 := rfl
    rw [hh]
    ring

theorem inverseQFT_t (r : List Wire) (a : Wire) :
    tCount (inverseQFT r a) = 4 * (r.length * (r.length-1) / 2) := by
  rw [inverseQFT, tCount_adjoint, forwardQFT, tCount_append,
    tCount_bitReverse, core_t, List.length_reverse, Finset.sum_range_id, Nat.add_zero]

theorem adjoint_mem (gs : Circuit) (w : Wire) :
    w ∈ circuitWires gs.adjoint ↔ w ∈ circuitWires gs := by
  have hg (g : Gate) : gateWires g.adjoint = gateWires g := by cases g <;> rfl
  simp only [circuitWires, Circuit.adjoint, List.mem_flatMap, List.mem_map,
    List.mem_reverse]
  constructor
  · rintro ⟨g, ⟨v, hv, rfl⟩, hw⟩
    exact ⟨v, hv, by simpa only [hg] using hw⟩
  · rintro ⟨g, hg', hw⟩
    exact ⟨g.adjoint, ⟨g, hg', rfl⟩, by simpa only [hg] using hw⟩

theorem phaseLayer_mem (t a : Wire) (cs : List Wire) (k w : Nat) :
    w ∈ circuitWires (phaseLayer t a cs k) ↔
      w ∈ circuitWires (qftPhaseLayer t a cs k) := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih =>
    simp only [phaseLayer, qftPhaseLayer, circuitWires, List.flatMap_append, List.mem_append]
    change (_ ∨ w ∈ circuitWires (phaseLayer t a cs (k+1))) ↔
      (_ ∨ w ∈ circuitWires (qftPhaseLayer t a cs (k+1)))
    rw [ih]
    simp [parityPhase, cPhase, circuitWires, gateWires]
    tauto

theorem core_mem (a : Wire) (r : List Wire) (w : Wire) :
    w ∈ circuitWires (core a r) ↔ w ∈ circuitWires (qftCoreMSB a r) := by
  induction r with
  | nil => rfl
  | cons t rest ih =>
    simp only [core, qftCoreMSB, circuitWires, List.flatMap_append, List.mem_append]
    change ((_ ∨ w ∈ circuitWires (phaseLayer t a rest 2)) ∨
      w ∈ circuitWires (core a rest)) ↔
      ((_ ∨ w ∈ circuitWires (qftPhaseLayer t a rest 2)) ∨
      w ∈ circuitWires (qftCoreMSB a rest))
    rw [phaseLayer_mem, ih]

theorem inverseQFT_mem (r : List Wire) (a w : Wire) :
    w ∈ circuitWires (inverseQFT r a) ↔ w ∈ circuitWires (iqft r a) := by
  rw [inverseQFT, iqft, adjoint_mem, adjoint_mem]
  simp only [forwardQFT, qft, qftCore, circuitWires, List.flatMap_append, List.mem_append]
  exact or_congr (core_mem a r.reverse w) Iff.rfl

theorem phaseLayer_length (t a : Wire) (cs : List Wire) (k : Nat) :
    (phaseLayer t a cs k).length = 8 * cs.length := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih => simp [phaseLayer, parityPhase, ih]; omega

theorem core_length (a : Wire) (r : List Wire) :
    (core a r).length ≤ 8 * r.length ^ 2 + r.length := by
  induction r with
  | nil => simp [core]
  | cons t rest ih =>
    simp only [core, List.length_append, phaseLayer_length,
      List.length_cons, List.length_nil]
    nlinarith

theorem inverseQFT_length (r : List Wire) (a : Wire) :
    (inverseQFT r a).length ≤ 8 * r.length ^ 2 + 4 * r.length := by
  have hb : (bitReverse r).length ≤ 3 * r.length := by
    simp only [bitReverse, List.length_flatMap]
    have hs : ∀ p : Wire × Wire, (swap p.1 p.2).length = 3 := fun _ => rfl
    simp only [hs, List.map_const', List.sum_const_nat]
    have hl : ((r.zip r.reverse).take (r.length / 2)).length ≤ r.length := by
      simp only [List.length_take, List.length_zip, List.length_reverse, min_self]
      omega
    omega
  have hc := core_length a r.reverse
  simp only [List.length_reverse] at hc
  simp only [inverseQFT, Circuit.adjoint, List.length_map, List.length_reverse,
    forwardQFT, List.length_append]
  omega

end
end ShorECDLP.Entrant
