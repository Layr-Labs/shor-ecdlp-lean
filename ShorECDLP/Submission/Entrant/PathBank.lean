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
set_option linter.constructorNameAsVariable false
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

/-! ### Structural bounds: no kernel evaluation of whole site programs -/

/-- A wire outside the bank's label interval. -/
def Far (w : Nat) : Prop := w < 14832 ∨ 14847 ≤ w
instance : DecidablePred Far := fun w => inferInstanceAs (Decidable (w < 14832 ∨ 14847 ≤ w))

theorem far_not {w : Wire} (h : Far w) : w ∉ pathBank := by
  intro hm
  simp only [pathBank, List.mem_range'_1] at hm
  unfold Far at h
  omega

theorem far_of_all (L : List Wire) (h : (L.all fun b => decide (Far b)) = true) : ∀ q ∈ L, Far q := by
  intro q hq
  have := List.all_eq_true.mp h q hq
  simpa only [decide_eq_true_eq] using this

theorem far_of_subset {p : ECDSAAdd.Program} {L : List Wire} (hs : ECDSAAdd.wires p ⊆ L.toFinset)
    (hL : ∀ q ∈ L, Far q) : ∀ q ∈ ECDSAAdd.wires p, Far q :=
  fun q hq => hL q (List.mem_toFinset.mp (hs hq))

/-- Every literal wire and every lookup wire of the code is outside the bank. -/
def AvoidsF (code : WCode 32768) : Prop :=
  (∀ p, WInstr.literal p ∈ code → ∀ q ∈ ECDSAAdd.wires p, Far q) ∧
    (∀ c ps, WInstr.lookup c ps ∈ code → (∀ q ∈ portTargets ps, Far q) ∧ ∀ q ∈ c, Far q)

theorem avoids_of_far {code : WCode 32768} (h : AvoidsF code) : Avoids code :=
  ⟨fun p hp w hw hm => far_not (h.1 p hp w hm) hw,
    fun c ps hp => ⟨fun w hw ht => far_not ((h.2 c ps hp).1 w ht) hw,
      fun q hq hm => far_not ((h.2 c ps hp).2 q hq) hm⟩⟩

theorem avoidsF_append {a b : WCode 32768} (ha : AvoidsF a) (hb : AvoidsF b) : AvoidsF (a ++ b) := by
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact ha.1 p h
    · exact hb.1 p h
  · rcases List.mem_append.mp hp with h | h
    · exact ha.2 c ps h
    · exact hb.2 c ps h

theorem avoidsF_lit (p : ECDSAAdd.Program) (h : ∀ q ∈ ECDSAAdd.wires p, Far q) :
    AvoidsF (wLiteral (n := 32768) p) := by
  refine ⟨fun q hq => ?_, fun c ps hp => ?_⟩
  · simp only [wLiteral, List.mem_singleton, WInstr.literal.injEq] at hq
    rw [hq]; exact h
  · simp [wLiteral] at hp

theorem avoidsF_look (c : Option Wire) (ps : List (LookupPort 32768))
    (ht : ∀ q ∈ portTargets ps, Far q) (hc : ∀ q ∈ c, Far q) :
    AvoidsF ([.lookup c ps] : WCode 32768) := by
  refine ⟨fun p hp => ?_, fun c' ps' hp => ?_⟩
  · simp at hp
  · simp only [List.mem_singleton, WInstr.lookup.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨ht, hc⟩

theorem far_prog_of_all (p : ECDSAAdd.Program) (h : progAvoid (List.range' 14832 15) p = true) :
    ∀ q ∈ ECDSAAdd.wires p, Far q := by
  intro q hq
  have h' := progAvoid_sound _ p h q
  unfold Far
  by_contra hn
  exact h' (by simp only [List.mem_range'_1]; omega) hq

theorem avoidsF_zeroWith (tail : Wire → WCode 32768) (htail : ∀ w, Far w → AvoidsF (tail w))
    (c : Wire) (bs : List ZeroBit) (hc : Far c) (hbs : ∀ b ∈ bs, Far b.input ∧ Far b.work) :
    AvoidsF (wZeroWith tail c bs) := by
  induction bs generalizing c with
  | nil => exact htail c hc
  | cons b bs ih =>
    have hb := hbs b List.mem_cons_self
    have hrest := ih b.work hb.2 (fun d hd => hbs d (List.mem_cons_of_mem _ hd))
    simp only [wZeroWith]
    refine avoidsF_append (avoidsF_append (avoidsF_lit _ ?_) hrest) (avoidsF_lit _ ?_)
    · intro q hq
      have key : q = c ∨ q = b.input ∨ q = b.work := by
        simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires, ECDSAAdd.Entrant.chainAnd, ECDSAAdd.Frontier.chainAnd] at hq
        tauto
      rcases key with h | h | h <;> rw [h]
      · exact hc
      · exact hb.1
      · exact hb.2
    · intro q hq
      have key : q = c ∨ q = b.input ∨ q = b.work := by
        simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires, ECDSAAdd.correctionWires, ECDSAAdd.Entrant.chainErase,
          ECDSAAdd.Frontier.chainErase] at hq
        tauto
      rcases key with h | h | h <;> rw [h]
      · exact hc
      · exact hb.1
      · exact hb.2

theorem far_tail (y t₁ t₂ : Wire) (hy : Far y) (h₁ : Far t₁) (h₂ : Far t₂) :
    ∀ w, Far w → AvoidsF (wPairTailBare (n := 32768) y t₁ t₂ w) := by
  intro w hw
  refine avoidsF_lit _ ?_
  intro q hq
  have key : q = w ∨ q = y ∨ q = t₁ ∨ q = t₂ := by
    simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq
    tauto
  rcases key with h | h | h | h <;> rw [h]
  · exact hw
  · exact hy
  · exact h₁
  · exact h₂

theorem far_litConcat (code : WCode 32768) (h : AvoidsF code) : ∀ q ∈ ECDSAAdd.wires (litConcat code), Far q := by
  intro q hq
  obtain ⟨p, hp, hq'⟩ := litConcat_wires code q hq
  exact h.1 p hp q hq'

theorem scrWires_far : ∀ q ∈ scrWires, Far q := by
  rw [scrWires_eq]
  intro q hq
  simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hq
  unfold Far
  dsimp only [Wire] at *
  omega

theorem scrAll_far : ∀ q ∈ scrAllWires, Far q := by
  rw [scrAll_eq]
  intro q hq
  simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hq
  unfold Far
  dsimp only [Wire] at *
  omega

theorem scrDWires_far : ∀ q ∈ scrDWires, Far q := by
  rw [scrDWires_eq]
  intro q hq
  simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hq
  unfold Far
  dsimp only [Wire] at *
  omega

theorem scrPair_far : ∀ q ∈ scrPairWires, Far q :=
  fun q hq => scrWires_far q (List.mem_append_left _ hq)

theorem scrShort_far : ∀ q ∈ scrShortWires, Far q :=
  fun q hq => scrWires_far q (List.mem_append_right _ hq)

theorem far_cx (S T : List Wire) (hS : ∀ q ∈ S, Far q) (hT : ∀ q ∈ T, Far q) :
    ∀ q ∈ ECDSAAdd.wires (cxList S T), Far q := by
  intro q hq
  rcases cxList_wires S T q hq with h | h
  · exact hS q h
  · exact hT q h

theorem windowRoot_far : ∀ q ∈ (some windowRoot : Option Wire), Far q := by
  intro q hq
  rw [Option.mem_def, Option.some.injEq] at hq
  subst hq
  unfold Far windowRoot
  omega

theorem pairTargets_far : ∀ q ∈ scrPairTargets, Far q := far_of_all _ (by decide +kernel)
theorem shortTargets_far : ∀ q ∈ scrShortTargets, Far q := far_of_all _ (by decide +kernel)
theorem dTargets_far : ∀ q ∈ scrDTargets, Far q := far_of_all _ (by decide +kernel)
theorem flags_far : ∀ q ∈ [yLow streamLayout, streamLayout.control, streamLayout.doubleSelect,
    streamLayout.genericSelect, streamLayout.infinitySelect, streamLayout.core.equalNegY,
    streamLayout.core.equalX, streamLayout.core.double], Far q := far_of_all _ (by decide +kernel)
theorem pairPorts_far : ∀ b ∈ pairPorts streamLayout, Far b.input ∧ Far b.work := by
  have h : ((pairPorts streamLayout).all fun b => decide (Far b.input) && decide (Far b.work)) = true := by
    decide +kernel
  intro b hb
  have := List.all_eq_true.mp h b hb
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

theorem shortPorts_far : ∀ q ∈ (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258)).flatMap
    ZeroBit.wires, Far q := far_of_all _ (by decide +kernel)

theorem zc_far (c t : Wire) (bs : List ZeroBit) (hc : Far c) (ht : Far t)
    (hbs : ∀ q ∈ bs.flatMap ZeroBit.wires, Far q) : ∀ q ∈ ECDSAAdd.wires (zeroControlled c t bs), Far q := by
  intro q hq
  rw [zeroControlled_wires] at hq
  rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with h | h
  · rw [h]; exact hc
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact ht
  · exact hbs q h

theorem flag_far (q : Wire) (h : q ∈ [yLow streamLayout, streamLayout.control, streamLayout.doubleSelect,
    streamLayout.genericSelect, streamLayout.infinitySelect, streamLayout.core.equalNegY,
    streamLayout.core.equalX, streamLayout.core.double]) : Far q := flags_far q h

/-- The literal middle of either comparison site avoids the bank. -/
theorem mid_far (t₁ t₂ : Wire) (h₁ : Far t₁) (h₂ : Far t₂) (zc zt : Wire) (hzc : Far zc) (hzt : Far zt) :
    AvoidsF (wLiteral (cxList scrPairWires scrPairTargets) ++
      wZeroWith (wPairTailBare (yLow streamLayout) t₁ t₂) streamLayout.control (pairPorts streamLayout) ++
      wLiteral (cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
      wLiteral (cxList scrShortWires scrShortTargets) ++
      wLiteral (zeroControlled zc zt (zeroPorts (shortSrc streamLayout) (streamLayout.dialogPool.take 258))) ++
      wLiteral (cxList scrShortWires scrShortTargets)) := by
  have hy : Far (yLow streamLayout) := flag_far _ (by simp)
  have hctl : Far streamLayout.control := flag_far _ (by simp)
  have pairCx := far_cx _ _ scrPair_far pairTargets_far
  have shortCx := far_cx _ _ scrShort_far shortTargets_far
  refine avoidsF_append (avoidsF_append (avoidsF_append (avoidsF_append (avoidsF_append
    (avoidsF_lit _ pairCx)
    (avoidsF_zeroWith _ (far_tail _ _ _ hy h₁ h₂) _ _ hctl pairPorts_far))
    (avoidsF_lit _ ?_)) (avoidsF_lit _ shortCx)) (avoidsF_lit _ (zc_far zc zt _ hzc hzt shortPorts_far))) (avoidsF_lit _ shortCx)
  intro q hq
  rw [ECDSAAdd.wires_append] at hq
  rcases Finset.mem_union.mp hq with h | h
  · exact pairCx q h
  · simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at h
    rw [h]; exact hy

theorem scrIn_avoids : Avoids (WEX.scrInSite probeRows).code := by
  apply avoids_of_far
  rw [WEX.scrInSite_code]
  have hl : AvoidsF ([.lookup (some windowRoot) (WEX.scrInPorts probeRows)] : WCode 32768) :=
    avoidsF_look _ _ (by rw [WEX.scrInPorts_targets]; exact scrWires_far) windowRoot_far
  have hm := mid_far streamLayout.doubleSelect streamLayout.genericSelect (flag_far _ (by simp))
    (flag_far _ (by simp)) streamLayout.core.equalX streamLayout.core.equalNegY (flag_far _ (by simp))
    (flag_far _ (by simp))
  have ha : AvoidsF (wLiteral (n := 32768) WEX.scrInArith) :=
    avoidsF_lit _ (far_litConcat _ (by simpa only [WEX.scrInMid, WEX.scrInP2, List.append_assoc] using hm))
  exact avoidsF_append (avoidsF_append hl ha) hl

/-- The output site, split so that the negation program is bounded by its layout. -/
theorem scrD_avoids : Avoids scrDSite.code := by
  apply avoids_of_far
  have hP : AvoidsF (wLiteral (n := 32768) WEX.scrNegP) := avoidsF_lit _
    (far_of_subset (ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout.program_support (negateYLayout streamLayout)
      streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c (negateYLayout_widths streamLayout streamLayout_widths).2)
      (far_of_all _ (by decide +kernel)))
  have hL : AvoidsF ([.lookup (some windowRoot) (WEX.scrDPorts probeRows)] : WCode 32768) :=
    avoidsF_look _ _ (by rw [WEX.scrDPorts_targets]; exact scrAll_far) windowRoot_far
  have hC : AvoidsF ([.lookup (some streamLayout.doubleSelect) (WEX.scrCPorts probeRows)] : WCode 32768) :=
    avoidsF_look _ _ (by rw [WEX.scrCPorts, WEX.scr_point_targets]; exact dTargets_far)
      (by intro q hq; rw [Option.mem_def, Option.some.injEq] at hq; subst hq; exact flag_far _ (by simp))
  have hCC : AvoidsF WEX.sfxCC := avoidsF_lit _ (by
    intro q hq
    rcases ccxList_wires _ _ _ q hq with h | h | h
    · rw [h]; exact flag_far _ (by simp)
    · exact scrDWires_far q h
    · exact dTargets_far q h)
  have hM : AvoidsF WEX.scrDMiddle := by
    have hm := mid_far streamLayout.infinitySelect streamLayout.core.equalNegY (flag_far _ (by simp))
      (flag_far _ (by simp)) streamLayout.core.double streamLayout.doubleSelect (flag_far _ (by simp))
      (flag_far _ (by simp))
    simpa only [WEX.scrDMiddle, WEX.scrP2, List.append_assoc] using hm
  have small (p : ECDSAAdd.Program) (h : progAvoid (List.range' 14832 15) p = true) :
      AvoidsF (wLiteral (n := 32768) p) := avoidsF_lit _ (far_prog_of_all p h)
  rw [scrDSite_code, WEX.sfxMidF, WEX.cornersE_split]
  refine avoidsF_append (avoidsF_append hL (avoidsF_append (avoidsF_append ?_ (small _ (by decide +kernel))) hM)) hL
  refine avoidsF_append (small _ (by decide +kernel)) (avoidsF_append hP (avoidsF_append (small _ (by decide +kernel))
    (avoidsF_append (small _ (by decide +kernel)) (avoidsF_append hCC (avoidsF_append (small _ (by decide +kernel))
    (avoidsF_append (small _ (by decide +kernel)) (avoidsF_append hC (avoidsF_append (small _ (by decide +kernel)) hP))))))))

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



end
end ShorECDLP.Entrant.PathShare
