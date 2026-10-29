import ShorECDLP.Submission.Entrant.PhaseGadget
import ShorECDLP.Submission.Entrant.Frontier

namespace ShorECDLP.Entrant.Improved
open Quantum Secp256k1 Challenge NaiveChallenge
noncomputable section

attribute [local irreducible] V2.fastScalarGates trialGatesE tableE progE
  Straight.WellFormed inverseQFT

def prefixGates : List (TemplateGate 1052) :=
  (PhaseEstimation.hadamards (regA ++ regB)).map TemplateGate.literal ++
    V2.fastScalarGates bitcoinPointReg bitcoinWorkStart regA gRows ++
    V2.fastScalarGates bitcoinPointReg bitcoinWorkStart regB qRows

def improvedGates : List (TemplateGate 1052) :=
  prefixGates ++ (inverseQFT regA bitcoinQFTAncilla ++
    inverseQFT regB bitcoinQFTAncilla).map TemplateGate.literal

theorem old_split : trialGatesE = prefixGates ++
    (iqft regA bitcoinQFTAncilla ++ iqft regB bitcoinQFTAncilla).map
      TemplateGate.literal := by
  unfold trialGatesE prefixGates
  rfl

theorem regA_anc : bitcoinQFTAncilla ∉ regA := by
  intro h
  apply layoutE.2
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))
theorem regB_anc : bitcoinQFTAncilla ∉ regB := by
  intro h
  apply layoutE.2
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))
theorem regA_nodup : regA.Nodup := layoutE.1.of_append_left.of_append_left.of_append_left
theorem regB_nodup : regB.Nodup := layoutE.1.of_append_left.of_append_left.of_append_right

theorem improvedGates_run (read : ConstantBit 1052 → Bool) :
    run (improvedGates.flatMap (TemplateGate.instantiate read)) =
      run (trialGatesE.flatMap (TemplateGate.instantiate read)) := by
  rw [old_split]
  simp only [improvedGates, List.flatMap_append, literalGates_instantiate, run_append_map,
    inverseQFT_eq _ _ regA_anc regA_nodup, inverseQFT_eq _ _ regB_anc regB_nodup]

theorem improvedGates_wf : ∀ g ∈ improvedGates, g.WellFormed := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact trialGatesE_wellFormed g (by rw [old_split]; exact List.mem_append_left _ hg)
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    have wfA : CircuitWellFormed (inverseQFT regA bitcoinQFTAncilla) := by
      unfold inverseQFT
      exact (circuitWellFormed_adjoint _).mpr (forwardQFT_wf _ _ regA_anc regA_nodup)
    have wfB : CircuitWellFormed (inverseQFT regB bitcoinQFTAncilla) := by
      unfold inverseQFT
      exact (circuitWellFormed_adjoint _).mpr (forwardQFT_wf _ _ regB_anc regB_nodup)
    exact ((circuitWellFormed_append _ _).mpr ⟨wfA, wfB⟩) a ha

theorem improvedGates_t : templateT improvedGates = 22108079775816 := by
  have h := templateT_trialE
  rw [old_split, templateT_append, templateT_literal, tCount_append,
    tCount_iqft, tCount_iqft] at h
  simp only [regA_length, regB_length] at h
  simp only [improvedGates, templateT_append, templateT_literal, tCount_append,
    inverseQFT_t, regA_length, regB_length]
  omega

theorem prefix_length : prefixGates.length ≤ trialGatesE.length := by
  rw [old_split, List.length_append]
  exact Nat.le_add_right _ _

theorem inverseA_length : (inverseQFT regA bitcoinQFTAncilla).length ≤ 554404 := by
  simpa only [show regA.length = 263 from regA_length] using
    inverseQFT_length regA bitcoinQFTAncilla

theorem inverseB_length : (inverseQFT regB bitcoinQFTAncilla).length ≤ 554404 := by
  simpa only [show regB.length = 263 from regB_length] using
    inverseQFT_length regB bitcoinQFTAncilla

theorem improvedGates_length : improvedGates.length ≤ 35800002000000 := by
  calc
    improvedGates.length = prefixGates.length +
        ((inverseQFT regA bitcoinQFTAncilla).length +
          (inverseQFT regB bitcoinQFTAncilla).length) := by
      simp only [improvedGates, List.length_append, List.length_map]
    _ ≤ trialGatesE.length + (554404 + 554404) :=
      Nat.add_le_add prefix_length (Nat.add_le_add inverseA_length inverseB_length)
    _ ≤ 35800002000000 := (Nat.add_le_add_right trialGatesE_length_le _).trans (by decide)

def improvedRaw : Straight 1052 0 (0 + (regA ++ regB).length) :=
  (constantGateProgram improvedGates 0).append (observeWires (regA ++ regB) 0)
def improvedProgram : Straight 1052 0 526 := castFinish prog_end improvedRaw
def optimizedEntry : StraightEntry where
  coefficients := tableE
  finalCursor := 526
  program := castTable tableE_length.symm improvedProgram

theorem optimizedEntry_instantiate (Q : Point) :
    optimizedEntry.instantiate Q =
      ((constantGateProgram improvedGates 0).instantiate (readConstant coeffE Q) Fin.elim0).seq
        (zObserve (regA ++ regB)) := by
  dsimp only [StraightEntry.instantiate, optimizedEntry]
  rw [castTable_instantiate, tableE_read, improvedProgram, instantiate_castFinish,
    improvedRaw, constantGateProgram_append_instantiate, observeWires_instantiate]

theorem optimizedEntry_run (Q : Point) :
    (optimizedEntry.instantiate Q).run = (entryE.instantiate Q).run := by
  rw [optimizedEntry_instantiate, entryE_instantiate]
  simp only [AdaptiveCircuit.run_seq, constantGateProgram_run,
    AdaptiveCircuit.run_unitary_done, improvedGates_run]

theorem optimizedEntry_wf : optimizedEntry.program.WellFormed := by
  change (castTable _ improvedProgram).WellFormed
  rw [castTable_wellFormed]
  apply castFinish_WF
  exact straight_append_wellFormed _ _
    (constantGateProgram_wellFormed _ _ improvedGates_wf) (observeWires_wellFormed _ _)

theorem optimizedEntry_straightT : straightT optimizedEntry.program = 22108079775816 := by
  change straightT (castTable _ improvedProgram) = _
  rw [straightT_castTable, improvedProgram, straightT_castFinish, improvedRaw,
    straightT_append, straightT_constant, straightT_observe, improvedGates_t, Nat.add_zero]

theorem optimizedEntry_t (Q : Point) :
    (resources (optimizedEntry.instantiate Q)).tModel ≤ 22108079775816 := by
  have h := straight_t_bound optimizedEntry.program
    (readConstant optimizedEntry.coefficients.get Q) Fin.elim0
  rw [optimizedEntry_straightT] at h
  exact h

theorem optimizedEntry_slots : optimizedEntry.program.gateSlots ≤ 35800002001052 := by
  change (castTable _ improvedProgram).gateSlots ≤ _
  rw [gateSlots_castTable, improvedProgram, gateSlots_castFinish, improvedRaw,
    observedGateProgram_slots, List.length_append, regA_length, regB_length]
  have h := improvedGates_length
  omega

theorem improvedGates_mem (read : ConstantBit 1052 → Bool) (w : Wire) :
    w ∈ circuitWires (improvedGates.flatMap (TemplateGate.instantiate read)) ↔
      w ∈ circuitWires (trialGatesE.flatMap (TemplateGate.instantiate read)) := by
  rw [old_split]
  simp only [improvedGates, List.flatMap_append, literalGates_instantiate,
    circuitWires, List.mem_append]
  exact or_congr Iff.rfl (or_congr (inverseQFT_mem _ _ _) (inverseQFT_mem _ _ _))

theorem optimizedEntry_wireSet (Q : Point) :
    (optimizedEntry.instantiate Q).wires.toFinset = (entryE.instantiate Q).wires.toFinset := by
  apply Finset.ext
  intro w
  simp only [List.mem_toFinset]
  rw [optimizedEntry_instantiate, entryE_instantiate, wires_seq, wires_seq]
  simp only [constantGateProgram_instantiate, gateNative_wires]
  exact or_congr (improvedGates_mem _ _) Iff.rfl

theorem optimizedEntry_qubits (Q : Point) :
    (resources (optimizedEntry.instantiate Q)).qubits ≤ 13892 := by
  have h := entryE_qubits Q
  change (optimizedEntry.instantiate Q).wires.dedup.length ≤ _
  rw [← List.card_toFinset, optimizedEntry_wireSet]
  exact h

end
end ShorECDLP.Entrant.Improved
