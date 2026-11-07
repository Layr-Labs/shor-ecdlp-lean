import ShorECDLP.Submission.«2607_13816».Window.Kernel
import ShorECDLP.Submission.«2607_13816».Fourier.Kernel

/-! Spike F1: a uniform window whose address wires split into two disjoint Fourier groups with
independent feedback histories (the joint first load of two exponent registers). -/
namespace ShorECDLP.Entrant.Mixed
open Quantum ShorECDLP ShorECDLP.Paper2607_13816
noncomputable section

theorem upd_upd_same (s : BasisState) (t : Wire) (a b : Bool) : (s[t ↦ a])[t ↦ b] = s[t ↦ b] := by
  funext w
  by_cases h : w = t <;> simp [upd, h]

theorem H_involutive_ket (t : Wire) (s : BasisState) :
    applyGate (.H t) (applyGate (.H t) (ket s)) = ket s := by
  have h2 : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) = 1/2 := by
    have : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
    have h := congrArg (fun r : ℝ => (r : ℂ)) this
    push_cast at h
    simpa using h
  rw [applyGate_H_ket]
  simp only [map_add, map_smul, applyGate_H_ket, upd_same, upd_upd_same]
  by_cases hs : s t
  · have e1 : s[t ↦ true] = s := by
      funext w; by_cases h : w = t <;> simp [upd, h, hs]
    simp only [hs, if_true, e1, smul_add, smul_smul]
    simp only [Bool.false_eq_true, if_false]
    generalize ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) = a at h2 ⊢
    match_scalars <;> first | ring1 | linear_combination 2 * h2
  · have hs' : s t = false := by simpa using hs
    have e0 : s[t ↦ false] = s := by
      funext w; by_cases h : w = t <;> simp [upd, h, hs']
    simp only [hs', Bool.false_eq_true, if_false, e0, smul_add, smul_smul]
    simp only [if_true]
    generalize ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) = a at h2 ⊢
    match_scalars <;> first | ring1 | linear_combination 2 * h2

theorem H_involutive (t : Wire) (ψ : State) :
    applyGate (.H t) (applyGate (.H t) ψ) = ψ := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single s c =>
    have : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [this, map_smul, map_smul, H_involutive_ket]

/-- Hadamards listed forwards then backwards cancel (no commutation needed). -/
theorem hadamards_palindrome (ws : List Wire) (ψ : State) :
    Quantum.run (ws.map Gate.H ++ ws.reverse.map Gate.H) ψ = ψ := by
  induction ws generalizing ψ with
  | nil => simp
  | cons w ws ih =>
    have e : (List.map Gate.H (w :: ws) ++ List.map Gate.H (w :: ws).reverse) =
        Gate.H w :: ((ws.map Gate.H ++ ws.reverse.map Gate.H) ++ [Gate.H w]) := by
      simp [List.map_append]
    rw [e, Quantum.run_cons, Quantum.run_append, ih, Quantum.run_singleton, H_involutive]


theorem branchCoeff_amplitude' (dir : PhaseDir) (ws : List Wire)
    (hws : ws.Nodup) (prior bs : List Bool) (s : BasisState) :
    fourierBranchCoeff dir ws prior bs s = fourierBitAmplitude dir (ws.map s) prior bs := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [fourierBranchCoeff, List.map_cons, fourierBitAmplitude]
      rw [ih (List.nodup_cons.mp hws).2]
      have hm : ws.map (s[w ↦ false]) = ws.map s := by
        apply List.map_congr_left
        intro v hv
        have hvw : v ≠ w := by intro he; subst v; exact (List.nodup_cons.mp hws).1 hv
        simp [upd, hvw]
      rw [hm]

theorem lmap_ket' (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by
  simp [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- Two Hadamard banks on disjoint wire lists act as an iterated uniform sum. -/
theorem hadamards_uniform2 (L R : List Wire) (hnL : L.Nodup) (hnR : R.Nodup)
    (hdisj : ∀ w ∈ L, w ∉ R) (s : BasisState) (hz : Clean (L ++ R) s) :
    Quantum.run ((L ++ R).map Gate.H) (ket s) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ L.length) •
        ((fourierOutcomes L.length).map (fun inL =>
          (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ R.length) •
            ((fourierOutcomes R.length).map (fun inR =>
              ket (phaseWordState R inR (phaseWordState L inL s)))).sum)).sum := by
  classical
  have hzL : Clean L s := fun w hw => hz w (List.mem_append_left _ hw)
  have hzR : Clean R s := fun w hw => hz w (List.mem_append_right _ hw)
  have hzR' (inL : List Bool) : Clean R (phaseWordState L inL s) := by
    intro w hw
    rw [phaseWordState_frame L inL s w (fun h => hdisj w h hw)]
    exact hzR w hw
  rw [List.map_append, Quantum.run_append, phaseHadamards_uniform L hnL s hzL, map_smul]
  congr 1
  simp only [phaseUniformSum, map_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro inL hinL
  rw [phaseHadamards_uniform R hnR _ (hzR' inL)]
  simp only [phaseUniformSum]

theorem window_branch_uniform2 (dir : PhaseDir) (L R : List Wire) (hnL : L.Nodup) (hnR : R.Nodup)
    (hdisj : ∀ w ∈ L, w ∉ R)
    (f : BasisState → BasisState) (priorL priorR outL outR : List Bool)
    (s : BasisState) (hz : Clean (L ++ R) s)
    (hfL : ∀ inL ∈ fourierOutcomes L.length, ∀ inR ∈ fourierOutcomes R.length,
      L.map (f (phaseWordState R inR (phaseWordState L inL s))) = inL)
    (hfR : ∀ inL ∈ fourierOutcomes L.length, ∀ inR ∈ fourierOutcomes R.length,
      R.map (f (phaseWordState R inR (phaseWordState L inL s))) = inR) :
    fourierBranch dir R.reverse priorR outR
      (fourierBranch dir L.reverse priorL outL
        (Finsupp.lmapDomain ℂ ℂ f (Quantum.run ((L ++ R).map Gate.H) (ket s)))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (L.length + R.length)) •
        ((fourierOutcomes L.length).map (fun inL =>
          ((fourierOutcomes R.length).map (fun inR =>
            (fourierBitAmplitude dir inL.reverse priorL outL *
              fourierBitAmplitude dir inR.reverse priorR outR) •
              ket (fourierClear R.reverse (fourierClear L.reverse
                (f (phaseWordState R inR (phaseWordState L inL s))))))).sum)).sum := by
  classical
  rw [hadamards_uniform2 L R hnL hnR hdisj s hz]
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def, pow_add, smul_smul,
    List.smul_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro inL hinL
  apply congrArg List.sum
  apply List.map_congr_left
  intro inR hinR
  rw [lmap_ket', fourierBranch_ket, branchCoeff_amplitude' dir L.reverse (List.nodup_reverse.mpr hnL),
    map_smul, fourierBranch_ket, branchCoeff_amplitude' dir R.reverse (List.nodup_reverse.mpr hnR),
    smul_smul]
  rw [List.map_reverse, hfL inL hinL inR hinR]
  have hR : R.map (fourierClear L.reverse (f (phaseWordState R inR (phaseWordState L inL s)))) = inR := by
    have hc : R.map (fourierClear L.reverse (f (phaseWordState R inR (phaseWordState L inL s)))) =
        R.map (f (phaseWordState R inR (phaseWordState L inL s))) := by
      apply List.map_congr_left
      intro v hv
      rw [fourierClear_apply, if_neg (fun h => hdisj v (List.mem_reverse.mp h) hv)]
    rw [hc]
    exact hfR inL hinL inR hinR
  rw [List.map_reverse, hR]
  simp only [smul_smul, mul_assoc]


/-- The two single-window steps of the split first section (left bank with the joint load inside,
right bank preceded by a cancelling Hadamard palindrome) equal the joint closed form. -/
theorem joint_steps (dir : PhaseDir) (L R : List Wire) (hnL : L.Nodup) (hnR : R.Nodup)
    (hdisj : ∀ w ∈ L, w ∉ R)
    (f : BasisState → BasisState) (priorL priorR outL outR : List Bool)
    (s : BasisState) (hz : Clean (L ++ R) s)
    (hfL : ∀ inL ∈ fourierOutcomes L.length, ∀ inR ∈ fourierOutcomes R.length,
      L.map (f (phaseWordState R inR (phaseWordState L inL s))) = inL)
    (hfR : ∀ inL ∈ fourierOutcomes L.length, ∀ inR ∈ fourierOutcomes R.length,
      R.map (f (phaseWordState R inR (phaseWordState L inL s))) = inR) :
    fourierBranch dir R.reverse priorR outR
      (Quantum.run (R.map Gate.H ++ R.reverse.map Gate.H)
        (fourierBranch dir L.reverse priorL outL
          (Finsupp.lmapDomain ℂ ℂ f
            (Quantum.run (R.map Gate.H) (Quantum.run (L.map Gate.H) (ket s)))))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (L.length + R.length)) •
        ((fourierOutcomes L.length).map (fun inL =>
          ((fourierOutcomes R.length).map (fun inR =>
            (fourierBitAmplitude dir inL.reverse priorL outL *
              fourierBitAmplitude dir inR.reverse priorR outR) •
              ket (fourierClear R.reverse (fourierClear L.reverse
                (f (phaseWordState R inR (phaseWordState L inL s))))))).sum)).sum := by
  rw [hadamards_palindrome, ← Quantum.run_append, ← List.map_append]
  exact window_branch_uniform2 dir L R hnL hnR hdisj f priorL priorR outL outR s hz hfL hfR

end
end ShorECDLP.Entrant.Mixed
