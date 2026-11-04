import ShorECDLP.Submission.Entrant.PathShare

/-! ### The pool path bank of the fused row -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Fifteen dialog-pool wires used only by the plain arithmetic of the generic branch. -/
def pathBank : List Wire := List.range' 14832 15

def bank15 : Bank := ⟨windowBits, WEXUnlookup.high, pathBank.take 8, pathBank⟩
def old15 : Bank := ⟨windowBits, WEXUnlookup.high, WEXUnlookup.highPaths, windowPaths⟩
def bank14 : Bank := ⟨WEXUnlookupWidth14.bits, WEXUnlookupWidth14.high, pathBank.take 7, pathBank⟩
def old14 : Bank := ⟨WEXUnlookupWidth14.bits, WEXUnlookupWidth14.high, WEXUnlookupWidth14.highPaths, windowPaths⟩

theorem pathBank_pool : InPool pathBank := by
  intro q hq
  rw [pathBank,List.mem_range'_1] at hq
  have hp : streamLayout.dialogPool = ((List.range' 4115 5699).map streamWire).take 2613 := rfl
  rw [hp,List.mem_iff_getElem]
  refine ⟨q - 14115,by simp only [List.length_take,List.length_map,List.length_range']; rw [Nat.min_eq_left (by norm_num)]; omega,?_⟩
  simp only [List.getElem_take,List.getElem_map,List.getElem_range']
  unfold streamWire
  dsimp only [Wire] at *
  split_ifs <;> omega

/-- Disjointness from the bank by a single pass over the other list. -/
theorem pathBank_not_of (L : List Wire) (hL : (L.all fun b => decide (b < 14832 ∨ 14847 ≤ b)) = true) :
    ∀ w ∈ pathBank, w ∉ L := by
  intro w hw hm
  have h1 := List.all_eq_true.mp hL w hm
  simp only [decide_eq_true_eq] at h1
  simp only [pathBank, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem pathBank_nodup : pathBank.Nodup := List.nodup_range'

theorem pathBank_window : ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ pathBank := by
  intro w hw hp
  exact pathBank_not_of _ (by decide +kernel) w hp hw

theorem pathBank_out : ∀ w ∈ pathBank, 871 ≤ w := by
  unfold pathBank
  decide +kernel

theorem pathBank_flip : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program) := by
  intro w hw hm
  simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hm
  subst hm
  revert hw
  unfold pathBank
  decide +kernel


theorem bank15_ok : BankOK bank15 where
  split := WEXUnlookup.splitAddress
  high := by
    unfold bank15 WEXUnlookup.high
    decide +kernel
  index := tableAddressTree_index _ 0 1 (by decide +kernel)
  nodup := by decide +kernel
  len := by decide +kernel
  sub := fun _ hw => List.mem_of_mem_take hw
  out := fun w hw => pathBank_out w (List.mem_of_mem_take hw)
  bitsLen := by decide +kernel

theorem bank14_ok : BankOK bank14 where
  split := WEXUnlookupWidth14.splitAddress
  high := by
    unfold bank14 WEXUnlookupWidth14.high
    decide +kernel
  index := tableAddressTree_index _ 0 1 (by decide +kernel)
  nodup := by decide +kernel
  len := by decide +kernel
  sub := fun _ hw => List.mem_of_mem_take hw
  out := fun w hw => pathBank_out w (List.mem_of_mem_take hw)
  bitsLen := by decide +kernel

/-! A Boolean wire check, so concrete sites are discharged by `decide +kernel`. -/

def corrList : List ECDSAAdd.Correction → List Wire
  | [] => []
  | .Z t :: cs => t :: corrList cs
  | .CZ a b :: cs => a :: b :: corrList cs

def instrList : ECDSAAdd.Instr → List Wire
  | .X t => [t]
  | .CX c t => [c, t]
  | .CCX a b t => [a, b, t]
  | .measureX t c₀ c₁ => t :: (corrList c₀ ++ corrList c₁)

def progAvoid (P : List Wire) (p : ECDSAAdd.Program) : Bool :=
  p.all fun i => (instrList i).all fun w => !(P.contains w)

def avoidW {n} (P : List Wire) : WInstr n → Bool
  | .literal p => progAvoid P p
  | .lookup c ps => (portTargets ps).all (fun w => !(P.contains w)) && c.all (fun q => !(P.contains q))

theorem corr_mem (cs : List ECDSAAdd.Correction) (w : Wire) (h : w ∈ ECDSAAdd.correctionWires cs) :
    w ∈ corrList cs := by
  induction cs with
  | nil => simp [ECDSAAdd.correctionWires] at h
  | cons c cs ih =>
    cases c with
    | Z t =>
      simp only [ECDSAAdd.correctionWires, Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · simp [corrList, h]
      · exact List.mem_cons_of_mem _ (ih h)
    | CZ a b =>
      simp only [ECDSAAdd.correctionWires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with (h | h) | h
      · simp [corrList, h]
      · simp [corrList, h]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))

theorem instr_mem (i : ECDSAAdd.Instr) (w : Wire) (h : w ∈ i.wires) : w ∈ instrList i := by
  cases i with
  | X t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | CX c t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | CCX a b t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | measureX t c₀ c₁ =>
    simp only [ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_singleton] at h
    simp only [instrList, List.mem_cons, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (corr_mem _ _ h))
    · exact Or.inr (Or.inr (corr_mem _ _ h))

theorem progAvoid_sound (P : List Wire) (p : ECDSAAdd.Program) (h : progAvoid P p = true) :
    ∀ w ∈ P, w ∉ ECDSAAdd.wires p := by
  intro w hw hm
  induction p with
  | nil => simp [ECDSAAdd.wires] at hm
  | cons i p ih =>
    simp only [progAvoid, List.all_cons, Bool.and_eq_true] at h
    simp only [ECDSAAdd.wires, Finset.mem_union] at hm
    rcases hm with hm | hm
    · have := List.all_eq_true.mp h.1 w (instr_mem i w hm)
      simp at this
      exact this hw
    · exact ih h.2 hm

theorem pathBank_head : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires scrHeadProgram :=
  progAvoid_sound pathBank scrHeadProgram (by unfold pathBank scrHeadProgram; decide +kernel)

theorem avoidW_lookup {n} (P : List Wire) (c : Option Wire) (ps : List (LookupPort n))
    (h : avoidW P (.lookup c ps) = true) :
    (∀ w ∈ P, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ P := by
  unfold avoidW at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun w hw ht => ?_, fun q hq hp => ?_⟩
  · have := List.all_eq_true.mp h1 w ht
    simp at this
    exact this hw
  · cases c with
    | none => simp at hq
    | some q' =>
      simp only [Option.mem_def, Option.some.injEq] at hq
      subst hq
      simp [Option.all] at h2
      exact h2 hp

end
end ShorECDLP.Entrant.PathShare

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Every literal and every lookup of the code avoids the pool path bank. -/
def Avoids (code : WCode 32768) : Prop :=
  (∀ p, WInstr.literal p ∈ code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ code → (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank)

theorem avoids_of_all (code : WCode 32768) (h : code.all (avoidW pathBank) = true) : Avoids code :=
  ⟨fun p hp => progAvoid_sound pathBank p (List.all_eq_true.mp h _ hp),
    fun c ps hp => avoidW_lookup pathBank c ps (List.all_eq_true.mp h _ hp)⟩

theorem avoids_append {a b : WCode 32768} (ha : Avoids a) (hb : Avoids b) : Avoids (a ++ b) := by
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact ha.1 p h
    · exact hb.1 p h
  · rcases List.mem_append.mp hp with h | h
    · exact ha.2 c ps h
    · exact hb.2 c ps h

theorem avoids_lit (p : ECDSAAdd.Program) (h : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) :
    Avoids (wLiteral (n := 32768) p) := by
  refine ⟨fun q hq => ?_, fun c ps hp => ?_⟩
  · simp only [wLiteral, List.mem_singleton, WInstr.literal.injEq] at hq
    rw [hq]; exact h
  · simp [wLiteral] at hp

theorem scrNegP_avoid : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires WEX.scrNegP :=
  WEX.neg_disjoint (negateYLayout streamLayout) streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths streamLayout streamLayout_widths).2 pathBank (pathBank_not_of _ (by decide +kernel))

/-- The output site, split so that the negation program is bounded by its layout. -/
theorem scrD_avoids : Avoids scrDSite.code := by
  have hP : Avoids (wLiteral (n := 32768) WEX.scrNegP) := avoids_lit _ scrNegP_avoid
  rw [scrDSite_code, WEX.sfxMidF, WEX.cornersE_split]
  repeat' (with_reducible apply avoids_append)
  all_goals first
    | (with_reducible exact hP)
    | exact avoids_of_all _ (by unfold pathBank; decide +kernel)

theorem pair_avoid (refsA refsB : Nat → Nat → ConstantBit 32768) :
    (∀ p, WInstr.literal p ∈ (pairSite refsA refsB).code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ (pairSite refsA refsB).code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) := by
  have hw : ∀ w ∈ pathBank, w ∉ pairWireList := pathBank_not_of _ (by decide +kernel)
  have ht : ∀ w ∈ pathBank, w ∉ pairTargets := pathBank_not_of _ (by decide +kernel)
  have hg : streamLayout.core.generic ∉ pathBank := fun h =>
    pathBank_not_of [streamLayout.core.generic] (by decide +kernel) _ h List.mem_cons_self
  rw [pairSite_code]
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_cons.mp hp with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact wires_avoid_of pairArith_subset hw
    · cases List.mem_singleton.mp h
  · have hp' : c = some streamLayout.core.generic ∧ ps = (pairSite refsA refsB).ports := by
      rcases List.mem_cons.mp hp with h | h
      · exact WInstr.lookup.inj h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact WInstr.lookup.inj (List.mem_singleton.mp h)
    obtain ⟨rfl, rfl⟩ := hp'
    refine ⟨fun w hw' hm => ht w hw' (by rw [pairSite_targets] at hm; exact hm), fun q hq => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hg

theorem triple_avoid :
    (∀ p, WInstr.literal p ∈ (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).code →
      ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) := by
  have hw : ∀ w ∈ pathBank, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).wires :=
    pathBank_not_of _ (by decide +kernel)
  have ht : ∀ w ∈ pathBank, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).src :=
    pathBank_not_of _ (by decide +kernel)
  have hg : streamLayout.core.generic ∉ pathBank := fun h =>
    pathBank_not_of [streamLayout.core.generic] (by decide +kernel) _ h List.mem_cons_self
  rw [constSite_code]
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_cons.mp hp with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact wires_avoid_of (MeasuredCanonicalModLayout.program_wires_subset _ _ _) hw
    · cases List.mem_singleton.mp h
  · have hp' : c = some streamLayout.core.generic ∧
        ps = indexedPorts (streamLayout.recoveryConstant streamLayout.point.x).src (wFields probeRows .tripleX) true := by
      rcases List.mem_cons.mp hp with h | h
      · exact WInstr.lookup.inj h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact WInstr.lookup.inj (List.mem_singleton.mp h)
    obtain ⟨rfl, rfl⟩ := hp'
    refine ⟨fun w hw' hm => ht w hw' (by rw [indexed_targets] at hm; exact hm), fun q hq => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hg

theorem scrIn_avoid : (WEX.scrInSite probeRows).code.all (avoidW pathBank) = true := by
  unfold pathBank
  decide +kernel


end
end ShorECDLP.Entrant.PathShare
