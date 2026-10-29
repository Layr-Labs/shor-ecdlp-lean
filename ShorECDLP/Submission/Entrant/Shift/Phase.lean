import ShorECDLP.Submission.Naive.OrderFinding.Proofs.Probability
import ShorECDLP.Submission.Naive.Arithmetic.Contracts

/-! EDITABLE. A diagonal half-bin phase shift on a phase register.

`halfShift ws m` applies `P(+2π/2^m)` to the first wire of `ws`, `P(+2π/2^(m-1))` to the
second, and so on down to `P(+2π/2)`.  On a register holding `v` it multiplies the state by
`exp(2πi v / 2^m)`: the bits of weight `2^j ≥ 2^m` contribute whole turns. -/

namespace ShorECDLP.Quantum.OrderFinding.Two

open ShorECDLP.Quantum.OrderFinding
open PhaseEstimation

def halfShift : List Wire → Nat → Circuit
  | [], _ => []
  | _ :: _, 0 => []
  | w :: ws, m + 1 => Gate.P .forward (m + 1) w :: halfShift ws m

theorem eigenvalue_add' (x y : ℝ) : eigenvalue (x + y) = eigenvalue x * eigenvalue y := by
  unfold eigenvalue
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eigenvalue_natCast (n : ℕ) : eigenvalue (n : ℝ) = 1 := by
  unfold eigenvalue
  have : Complex.I * ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_nat_mul_two_pi_mul_I]

theorem phaseCoeff_forward (k : ℕ) : phaseCoeff .forward k = eigenvalue (1 / 2 ^ k) := by
  unfold phaseCoeff phaseAngle eigenvalue
  congr 2
  push_cast
  ring

theorem halfShift_ket (ws : List Wire) (m : ℕ) (t : BasisState) :
    run (halfShift ws m) (ket t) = eigenvalue ((regValue ws t : ℝ) / 2 ^ m) • ket t := by
  induction ws generalizing m with
  | nil =>
    simp [halfShift, regValue, eigenvalue]
  | cons w ws ih =>
    cases m with
    | zero =>
      simp only [halfShift, run_nil, pow_zero, div_one, eigenvalue_natCast, one_smul]
    | succ m =>
      rw [halfShift, run_cons, applyGate_P_ket, map_smul, ih m, smul_smul]
      congr 1
      have hval : ((regValue (w :: ws) t : ℕ) : ℝ) / 2 ^ (m + 1) =
          ((if t w then 1 else 0 : ℕ) : ℝ) / 2 ^ (m + 1) + (regValue ws t : ℝ) / 2 ^ m := by
        rw [regValue_cons]; push_cast; rw [pow_succ]; field_simp
      rw [hval, eigenvalue_add']
      cases t w
      · simp [eigenvalue]
      · simp only [if_true, phaseCoeff_forward, Nat.cast_one]

theorem halfShift_labelState (ws : List Wire) (m : ℕ) (hnd : ws.Nodup) (v : ℕ)
    (hv : v < 2 ^ ws.length) (ψ : State) :
    run (halfShift ws m) (labelState ws v ψ) =
      eigenvalue ((v : ℝ) / 2 ^ m) • labelState ws v ψ := by
  classical
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, smul_add]
  | single t c =>
    have hl : labelState ws v (Finsupp.single t c) = c • ket (writeReg ws v t) := by
      simp [labelState, Finsupp.linearCombination_single]
    rw [hl, map_smul, halfShift_ket, regValue_writeReg_of_lt ws v t hnd hv, smul_comm]

/-- The shift hypothesis of `orderFinding_eq_fourierState2` for `σ = 1 / 2 ^ m`. -/
theorem halfShift_spec (ws : List Wire) (m pb : ℕ) (hnd : ws.Nodup) (hw : ws.length = pb)
    (v : Fin (2 ^ pb)) (ψ : State) :
    run (halfShift ws m) (labelState ws v.val ψ) =
      eigenvalue (1 / 2 ^ m) ^ v.val • labelState ws v.val ψ := by
  rw [halfShift_labelState ws m hnd v.val (by rw [hw]; exact v.isLt),
    eigenvalue_pow_eq_eigenvalue_mul]
  congr 2
  ring

theorem mem_halfShift : ∀ (ws : List Wire) (m : ℕ) (g : Gate), g ∈ halfShift ws m →
    ∃ k, ∃ w ∈ ws, g = Gate.P .forward k w
  | [], _, g, h => by simp [halfShift] at h
  | _ :: _, 0, g, h => by simp [halfShift] at h
  | w :: ws, m + 1, g, h => by
    simp only [halfShift, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨m + 1, w, List.mem_cons_self, h⟩
    · obtain ⟨k, v, hv, rfl⟩ := mem_halfShift ws m g h
      exact ⟨k, v, List.mem_cons_of_mem _ hv, rfl⟩

theorem halfShift_tCount : ∀ (ws : List Wire) (m : ℕ), m ≤ ws.length →
    ShorECDLP.tCount (halfShift ws m) = m
  | [], m, h => by simp at h; subst h; rfl
  | _ :: _, 0, _ => rfl
  | w :: ws, m + 1, h => by
    simp only [List.length_cons] at h
    simp only [halfShift, tCount_cons, tCost, halfShift_tCount ws m (by omega)]
    omega

theorem halfShift_length_le : ∀ (ws : List Wire) (m : ℕ), (halfShift ws m).length ≤ m
  | [], _ => by simp [halfShift]
  | _ :: _, 0 => by simp [halfShift]
  | w :: ws, m + 1 => by
    simp only [halfShift, List.length_cons]
    have := halfShift_length_le ws m
    omega

theorem halfShift_wellFormed (ws : List Wire) (m : ℕ) : CircuitWellFormed (halfShift ws m) := by
  intro g hg
  obtain ⟨k, w, _, rfl⟩ := mem_halfShift ws m g hg
  trivial

theorem halfShift_usesOnly (ws : List Wire) (m : ℕ) :
    CircuitUsesOnly ws (halfShift ws m) := by
  intro g hg
  obtain ⟨k, w, hw, rfl⟩ := mem_halfShift ws m g hg
  exact hw

end ShorECDLP.Quantum.OrderFinding.Two
