import ShorECDLP.Submission.Entrant.Prefix

/-! Three neighbouring right words from one 204-bit sample: the centre, `+1`, and `-1`.
Direct specialization of `NeighborReadout` (matching `Readout56` at 1 positive and 1 negative step).
Every gate is a record-controlled Clifford on wires 0 and 1 (`weight4 = 0`, `residue = 0`). -/

set_option Elab.async false

namespace ShorECDLP.Entrant.Readout3
open Quantum ShorECDLP.Challenge ShorECDLP.Entrant.RoundedReadout ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def suffix3 (n start width : Nat) (bits : Vector (Fin start) width) :
    Straight n start (start + 2 + 8 * width) :=
  let c := initialCursor bits
  let q := c.lift (1 * (2 * width))
  castFinish (by omega)
    ((constantStep n start).append
      ((positiveWords n 1 (start + 2) width c).append
        ((complementStep n q).append
          (negativeWords n 1 (start + 2 + 1 * (2 * width) + 2 * width) width q.next))))

def rightWords3 {start width : Nat} (bits : Vector (Fin start) width) : List (Vector Nat width) :=
  bits.map Fin.val ::
    List.ofFn (fun i : Fin 1 => sumPositions (start + 2 + i.val * (2 * width)) width) ++
    List.ofFn (fun i : Fin 1 => sumPositions
      (start + 2 + 1 * (2 * width) + 2 * width + i.val * (4 * width) + 2 * width) width)

theorem rightWords3_length {start width : Nat} (bits : Vector (Fin start) width) :
    (rightWords3 bits).length = 3 := by simp [rightWords3]

attribute [local irreducible] positiveWords negativeWords incrementStep complementStep

theorem suffix3_wellFormed (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix3 n start width bits).WellFormed := by
  unfold suffix3
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed _ _ (constantStep_wellFormed _ _)
  apply straight_append_wellFormed _ _ (positiveWords_wellFormed _ _ _ _ _)
  exact straight_append_wellFormed _ _ (complementStep_wellFormed _ _)
    (negativeWords_wellFormed _ _ _ _ _)

theorem suffix3_slots (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix3 n start width bits).gateSlots = 7 + 28 * width := by
  simp only [suffix3, castFinish_gateSlots, Straight.gateSlots_append,
    constantStep_slots, positiveWords_slots, complementStep_slots, negativeWords_slots]
  ring

theorem suffix3_t (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((suffix3 n start width bits).instantiate read history).tCount = 0 := by
  unfold suffix3
  rw [castFinish_instantiate]
  apply Readout56.append_t_zero _ _ read (constantStep_t _ _ _)
  intro h
  apply Readout56.append_t_zero _ _ read (positiveWords_t _ _ _ _ _ _)
  intro h
  exact Readout56.append_t_zero _ _ read (complementStep_t _ _ _)
    (negativeWords_t _ _ _ _ _ _) h

theorem suffix3_support (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((suffix3 n start width bits).instantiate read history).wires ⊆ [0, 1] := by
  unfold suffix3
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history ([0, 1] : List Wire) (constantStep_support _ _ _ _)
  intro h
  apply outer_append_support _ _ read h ([0, 1] : List Wire) (positiveWords_support _ _ _ _ _ _ _)
  intro h
  exact outer_append_support _ _ read h ([0, 1] : List Wire) (complementStep_support _ _ _ _)
    (fun hh => negativeWords_support _ _ _ _ _ _ hh)

theorem weight4_suffix3 (n start width : Nat) (bits : Vector (Fin start) width) :
    ConditionalCatalyst.weight4 (suffix3 n start width bits) = 0 := by
  simp [suffix3, ConditionalCatalyst.weight4_cast, ConditionalCatalyst.weight4_append,
    ConditionalCatalyst.weight4_positive, ConditionalCatalyst.weight4_negative,
    ConditionalCatalyst.weight4_complement]
  rfl

theorem residue_suffix3 (n start width : Nat) (bits : Vector (Fin start) width) :
    AndGadget.residue (suffix3 n start width bits) = 0 := by
  simp [suffix3, AndGadget.residue_cast, AndGadget.residue_append,
    ApproximatePhase34.residue_positive, ApproximatePhase34.residue_negative,
    ApproximatePhase34.residue_complement]
  rfl

/-- Every nonzero readout branch writes all 3 neighbouring 204-bit residues explicitly. -/
theorem suffix3_branch (n start : Nat) (bits : Vector (Fin start) 204)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ ((suffix3 n start 204 bits).instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    b.kraus ψ = ψ ∧
      (∀ i : Fin 1, readWord (List.ofFn history ++ b.history)
        (sumPositions (start + 2 + i.val * 408) 204).toList =
        some ((i.val + 1 + inputValue bits history) % 2^204)) ∧
      (∀ i : Fin 1, readWord (List.ofFn history ++ b.history)
        (sumPositions (start + 2 + 408 + 408 + i.val * 816 + 408) 204).toList =
        some (2^204 - 1 - ((i.val + 1 + (2^204 - 1 - inputValue bits history)) % 2^204))) := by
  unfold suffix3 at hb
  rw [castFinish_instantiate] at hb
  obtain ⟨h₁, a, u, ha, hu, he₁, rfl⟩ := straight_append_branch _ _ read history b hb
  have han : a.kraus ψ ≠ 0 := by
    intro h; apply hn; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hc := constantStep_branch n start read history ψ hψ a ha han
  have hun : u.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hc.1] using hn
  have hcarr := initial_carry bits history h₁ (he₁.trans (by rw [hc.2]))
  have hval := initial_value bits history h₁ a.history he₁
  obtain ⟨h₂, p, v, hp, hv, he₂, rfl⟩ := straight_append_branch _ _ read h₁ u hu
  have hpn : p.kraus ψ ≠ 0 := by
    intro h; apply hun; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hpos := positiveWords_branch n 1 (start + 2) 204 (initialCursor bits)
    read h₁ hcarr ψ hψ p hp hpn
  have hvn : v.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hpos.1] using hun
  let q := (initialCursor bits).lift (1 * (2 * 204))
  have hqc : h₂ q.carry = true := (lift_carry (initialCursor bits) _ h₁ h₂ p.history he₂).trans hcarr
  have hqv : cursorValue q h₂ = inputValue bits history :=
    (lift_value (initialCursor bits) _ h₁ h₂ p.history he₂).trans hval
  obtain ⟨h₃, c, t, hc', ht, he₃, rfl⟩ := straight_append_branch _ _ read h₂ v hv
  have hcn : c.kraus ψ ≠ 0 := by
    intro h; apply hvn; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hcomp := complementStep_post n q read h₂ hqc ψ hψ c hc' hcn h₃ he₃
  have htn : t.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hcomp.1] using hvn
  have hneg := negativeWords_branch n 1 (start + 2 + 1 * (2 * 204) + 2 * 204) 204 q.next
    read h₃ hcomp.2.1 ψ hψ t ht htn
  have hfull₁ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₁ ++ (p.seq (c.seq t)).history := by
    rw [he₁]; simp only [InstrumentBranch.seq, List.append_assoc]
  have hfull₂ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₂ ++ (c.seq t).history := by
    rw [hfull₁, he₂]; simp only [InstrumentBranch.seq, List.append_assoc]
  have hfull₃ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₃ ++ t.history := by
    rw [hfull₂, he₃]; simp only [InstrumentBranch.seq, List.append_assoc]
  refine ⟨by simp only [InstrumentBranch.seq, LinearMap.comp_apply, hc.1, hpos.1, hcomp.1, hneg.1], ?_, ?_⟩
  · intro i
    rw [hfull₂, readWord_append_left (List.ofFn h₂) (c.seq t).history _ (by
      intro j hj
      have hj' := sumPositions_bound (start + 2 + i.val * 408) 204 j hj
      have hi := i.isLt
      simp only [List.length_ofFn]
      omega), he₂]
    simpa only [hval] using hpos.2 i
  · intro i
    rw [hfull₃]
    simpa only [hcomp.2.2, hqv] using hneg.2 i

theorem positive_word_mod204 (b i : Nat) :
    (i + b) % 2^204 = ((((b : Nat) : ℤ) + (i : ℤ)) % (2^204 : Nat)).toNat := by
  omega

theorem negative_word_mod204 (b i : Nat) (hb : b < 2^204) :
    2^204 - 1 - (i + (2^204 - 1 - b)) % 2^204 =
      ((((b : Nat) : ℤ) - (i : ℤ)) % (2^204 : Nat)).toNat := by
  omega

/-- The physical word list contains a correct explicit record for every offset `-1, 0, +1`. -/
theorem suffix3_reads (n start : Nat) (bits : Vector (Fin start) 204)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ ((suffix3 n start 204 bits).instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) (j : ℤ) (hj : -1 ≤ j ∧ j ≤ 1) :
    ∃ ps ∈ rightWords3 bits, readWord (List.ofFn history ++ b.history) ps.toList =
      some ((((inputValue bits history : Nat) : ℤ) + j) % (2^204 : Nat)).toNat := by
  have hs := suffix3_branch n start bits read history ψ hψ b hb hn
  by_cases hz : j = 0
  · subst j
    refine ⟨bits.map Fin.val, by simp [rightWords3], ?_⟩
    rw [readWord_append_left (List.ofFn history) b.history _ (by
      intro i hi
      simp only [Vector.toList_map, List.mem_map] at hi
      obtain ⟨k, _, rfl⟩ := hi
      simpa only [List.length_ofFn] using k.isLt), input_read]
    congr 1
    simpa only [Nat.zero_add, Int.natCast_zero, Nat.mod_eq_of_lt (input_lt bits history)] using
      (positive_word_mod204 (inputValue bits history) 0)
  · by_cases hp : 0 < j
    · let i : Fin 1 := ⟨0, by omega⟩
      have hi : (i.val + 1 : ℤ) = j := by dsimp [i]; omega
      refine ⟨sumPositions (start + 2 + i.val * 408) 204, ?_, ?_⟩
      · unfold rightWords3
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · rw [hs.2.1 i, positive_word_mod204]
        congr 2
        exact congrArg (fun z : ℤ => (((inputValue bits history : Nat) : ℤ) + z) % (2^204 : Nat)) hi
    · let i : Fin 1 := ⟨0, by omega⟩
      have hi : -((i.val + 1 : Nat) : ℤ) = j := by dsimp [i]; omega
      refine ⟨sumPositions (start + 2 + 408 + 408 + i.val * 816 + 408) 204, ?_, ?_⟩
      · unfold rightWords3
        apply List.mem_cons_of_mem
        apply List.mem_append_right
        exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · rw [hs.2.2 i, negative_word_mod204 _ _ (input_lt bits history)]
        congr 2
        rw [sub_eq_add_neg, hi]

#print axioms suffix3_reads

end
end ShorECDLP.Entrant.Readout3
