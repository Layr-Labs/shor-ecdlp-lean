import ShorECDLP.Submission.Entrant.StackBase

namespace ShorECDLP.Entrant.WEX.TrimmedSign
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def layout : NegLayout := negateYLayout streamLayout
def control : Wire := streamLayout.core.generic
def carryPrefix : Program :=
  [.CCX 580 14371 14115, .CCX 581 14115 14116,
   .CCX 582 14116 14117, .CCX 583 14117 14118]
def cleanWires : List Wire := [14371, 14115, 14116, 14117]
def add : Program := (layout.add control (ECDSAAdd.p + 1)).drop 4
def reflection : Program := layout.complement control ++ add

theorem add_split : layout.add control (ECDSAAdd.p + 1) = carryPrefix ++ add := by
  have h : (layout.add control (ECDSAAdd.p + 1)).take 4 = carryPrefix := by
    decide +kernel
  simpa only [h, add] using (List.take_append_drop 4 (layout.add control (ECDSAAdd.p + 1))).symm

theorem carryPrefix_run (st : State) (m : List Bool)
    (hc : ∀ w ∈ cleanWires, st.basis w = false) : run carryPrefix m st = st := by
  have h0 := hc 14371 (by simp [cleanWires])
  have h1 := hc 14115 (by simp [cleanWires])
  have h2 := hc 14116 (by simp [cleanWires])
  have h3 := hc 14117 (by simp [cleanWires])
  have skip (a b t : Wire) (tail : Program) (hb : st.basis b = false) :
      run (.CCX a b t :: tail) m st = run tail m st := by
    simp only [run, hb, Bool.and_false, Bool.xor_false, writeBit, Function.update_eq_self]
  unfold carryPrefix
  rw [skip _ _ _ _ h0, skip _ _ _ _ h1, skip _ _ _ _ h2, skip _ _ _ _ h3]
  rfl

theorem reflection_run (st : State) (m : List Bool)
    (hc : ∀ w ∈ cleanWires, st.basis w = false) :
    run reflection m st = run (layout.reflection control (ECDSAAdd.p + 1)) m st := by
  have away : ∀ w ∈ cleanWires, w ∉ ECDSAAdd.wires (layout.complement control) := by
    decide +kernel
  have clean (records : List Bool) :
      ∀ w ∈ cleanWires, (run (layout.complement control) records st).basis w = false := by
    intro w hw
    rw [run_preserves_outside _ _ _ _ (away w hw), hc w hw]
  simp only [reflection, CompactRecoveryNegateLayout.reflection, add_split, run_append]
  rw [carryPrefix_run _ _ (clean _)]
  simp only [carryPrefix, measurementCount, List.drop_zero]

theorem reflection_subset : reflection ⊆ layout.reflection control (ECDSAAdd.p + 1) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact List.mem_append_left _ hi
  · exact List.mem_append_right _ (List.mem_of_mem_drop hi)

theorem reflection_counts : toffoliCount reflection = 251 ∧ measurementCount reflection = 255 := by
  have width := negateYLayout_widths streamLayout streamLayout_widths
  have length : layout.word.length = 256 := width.1
  have old := layout.reflection_counts control (ECDSAAdd.p + 1) width.2 (by omega)
  have ht := congrArg toffoliCount add_split
  have hm := congrArg measurementCount add_split
  simp only [toffoliCount_append, measurementCount_append, carryPrefix, toffoliCount,
    measurementCount] at ht hm
  simp only [length] at old
  simp only [CompactRecoveryNegateLayout.reflection, toffoliCount_append,
    measurementCount_append] at old
  simp only [reflection, toffoliCount_append, measurementCount_append]
  omega

theorem reflection_physical : GatePhysical reflection := by
  have old := layout.reflection_physical control (ECDSAAdd.p + 1)
    (negateYLayout_nodup_generic streamLayout streamLayout_widths streamLayout_nodup)
  exact fun i hi => old i (reflection_subset hi)

theorem reflection_wires : ECDSAAdd.wires reflection ⊆
    ECDSAAdd.wires (layout.reflection control (ECDSAAdd.p + 1)) := by
  have hw := congrArg ECDSAAdd.wires add_split
  simp only [ECDSAAdd.wires_append] at hw
  simp only [reflection, CompactRecoveryNegateLayout.reflection, ECDSAAdd.wires_append]
  rw [hw]
  exact Finset.union_subset_union (fun _ h => h) Finset.subset_union_right

theorem reflection_slots : ECDSAAdd.Challenge.gateSlots reflection ≤
    ECDSAAdd.Challenge.gateSlots (layout.reflection control (ECDSAAdd.p + 1)) := by
  have hs := congrArg ECDSAAdd.Challenge.gateSlots add_split
  simp only [ECDSAAdd.Challenge.gateSlots_append] at hs
  simp only [reflection, CompactRecoveryNegateLayout.reflection,
    ECDSAAdd.Challenge.gateSlots_append]
  omega

end
end ShorECDLP.Entrant.WEX.TrimmedSign
