import ShorECDLP.Submission.Entrant.AffineLoss
namespace ShorECDLP.Entrant.Phase23Partial
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28 AffineLoss ConditionalCatalyst
open Paper2607_13816 Paper2607_13816.ChallengeMigration Single Single.Distribution
noncomputable section
set_option Elab.async false
attribute [local irreducible] List.ofFn
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem dropped_weight23_local (g : Gate) (hg : largePhase 19 g = true) :
    ConditionalCatalyst.weightedGate g = 1 ∧ ConditionalCatalyst.weightedLiteral g = 1 := by
  cases g <;> simp only [largePhase, Bool.false_eq_true, decide_eq_true_eq] at hg
  case P dir k t =>
    have hk : k ≠ 2 := by omega
    simp [ConditionalCatalyst.weightedGate, ConditionalCatalyst.weightedLiteral,
      ConditionalCatalyst.phaseTwoGate_P, hk, tCost]

def trimN {n s e} (N : Nat) : Straight n s e → Straight n s e
  | .done => .done
  | .gate (.literal g) p =>
      if largePhase 19 g then trimN N p
      else if decide (N > 0) && largePhase 18 g then trimN (N - 1) p
      else .gate (.literal g) (trimN N p)
  | .gate (.whenBit r v g) p =>
      if largePhase 19 g then trimN N p
      else if decide (N > 0) && largePhase 18 g then trimN (N - 1) p
      else .gate (.whenBit r v g) (trimN N p)
  | .recordGate i v g p =>
      if largePhase 19 g then trimN N p
      else if decide (N > 0) && largePhase 18 g then trimN (N - 1) p
      else .recordGate i v g (trimN N p)
  | .measure w p => .measure w (trimN N p)

theorem trimN_added {n s e} (N : Nat) (p : Straight n s e) :
    added (trimN N p) = added p := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [trimN]
      by_cases h27 : largePhase 19 g = true
      · cases g <;> simp only [largePhase, Bool.false_eq_true] at h27
        simp only [largePhase, h27, if_true, added]
        exact ih N
      · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 18 g) = true
        · cases g <;> simp only [largePhase, Bool.and_false, Bool.false_eq_true] at hN
          simp only [largePhase] at h27f
          simp only [largePhase, Bool.false_eq_true, h27f, if_false, hN, if_true,
            added, ih (N - 1)]
        · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
            Bool.eq_false_iff.mpr hN
          cases g <;> simp only [largePhase] at h27f hNf <;>
            simp only [largePhase, Bool.false_eq_true, if_false, if_true,
              added, h27f, hNf, ih N]
    | whenBit r v g =>
      simp only [trimN]
      by_cases h27 : largePhase 19 g = true
      · cases g <;> simp only [largePhase, Bool.false_eq_true] at h27
        simp only [largePhase, h27, if_true, added]
        exact ih N
      · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 18 g) = true
        · cases g <;> simp only [largePhase, Bool.and_false, Bool.false_eq_true] at hN
          simp only [largePhase] at h27f
          simp only [largePhase, Bool.false_eq_true, h27f, if_false, hN, if_true,
            added, ih (N - 1)]
        · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
            Bool.eq_false_iff.mpr hN
          cases g <;> simp only [largePhase] at h27f hNf <;>
            simp only [largePhase, Bool.false_eq_true, if_false, if_true,
              added, h27f, hNf, ih N]
  | recordGate i v g p ih =>
    simp only [trimN]
    by_cases h27 : largePhase 19 g = true
    · simp only [h27, if_true, added]
      exact ih N
    · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
      by_cases hN : (decide (N > 0) && largePhase 18 g) = true
      · simp only [h27f, if_false, hN, if_true, added]
        exact ih (N - 1)
      · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
          Bool.eq_false_iff.mpr hN
        simp only [h27f, if_false, hNf, if_false, added]
        exact ih N
  | measure w p ih => simp [trimN, added, ih]

theorem trimN_wellFormed {n s e} (N : Nat) (p : Straight n s e)
    (hp : p.WellFormed) : (trimN N p).WellFormed := by
  induction p generalizing N with
  | done => trivial
  | gate g p ih =>
    cases g <;> simp only [trimN] <;> split_ifs <;>
      first | exact ih _ hp.2 | exact ⟨hp.1, ih _ hp.2⟩
  | recordGate i v g p ih =>
    simp only [trimN] <;> split_ifs <;>
      first | exact ih _ hp.2 | exact ⟨hp.1, ih _ hp.2⟩
  | measure w p ih => simp only [trimN]; exact ih _ hp

theorem trimN_within {n s e} (N : Nat) (p : Straight n s e) (ws : List ShorECDLP.Wire)
    (hp : Within ws p) : Within ws (trimN N p) := by
  induction p generalizing N with
  | done => trivial
  | gate g p ih =>
    cases g <;> simp only [trimN] <;> split_ifs <;>
      first | exact ih _ hp.2 | exact ⟨hp.1, ih _ hp.2⟩
  | recordGate i v g p ih =>
    simp only [trimN] <;> split_ifs <;>
      first | exact ih _ hp.2 | exact ⟨hp.1, ih _ hp.2⟩
  | measure w p ih => exact ⟨hp.1, ih _ hp.2⟩

theorem trimN_slots {n s e} (N : Nat) (p : Straight n s e) :
    (trimN N p).gateSlots ≤ p.gateSlots := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g <;> simp only [trimN] <;> split_ifs <;>
      simp only [Straight.gateSlots] <;> (have h1 := ih N; have h2 := ih (N - 1); omega)
  | recordGate i v g p ih =>
    simp only [trimN] <;> split_ifs <;>
      simp only [Straight.gateSlots] <;> (have h1 := ih N; have h2 := ih (N - 1); omega)
  | measure w p ih => simp only [trimN, Straight.gateSlots]; exact ih _

theorem trimN_t {n s e} (N : Nat) (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    ((trimN N p).instantiate read history).tCount ≤ (p.instantiate read history).tCount := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g <;> simp only [trimN] <;> split_ifs <;>
      simp only [Straight.instantiate, AdaptiveCircuit.tCount] <;>
      (have h1 := ih N history; have h2 := ih (N - 1) history; omega)
  | recordGate _ _ g p ih =>
    simp only [trimN] <;> split_ifs <;>
      simp only [Straight.instantiate, AdaptiveCircuit.tCount] <;>
      (have h1 := ih N history; have h2 := ih (N - 1) history; omega)
  | measure _ p ih =>
    simp only [trimN, Straight.instantiate, AdaptiveCircuit.tCount]
    exact max_le_max (ih _ _) (ih _ _)

/-! A k = 19 phase gate still has weight 1 when dropped. -/
theorem dropped_weight27 (g : ShorECDLP.Gate) (hg : largePhase 18 g = true) :
    ConditionalCatalyst.weightedGate g = 1 ∧ ConditionalCatalyst.weightedLiteral g = 1 := by
  cases g <;> simp only [largePhase, Bool.false_eq_true] at hg
  case P dir k t =>
    have h1 : 18 < k := by simpa using hg
    have hk : k ≠ 2 := by omega
    simp [ConditionalCatalyst.weightedGate, ConditionalCatalyst.weightedLiteral,
      ConditionalCatalyst.phaseTwoGate_P, hk, ShorECDLP.tCost]

/-! Loss bound for a dropped k = 19 phase gate (unit charge). -/

def trimSpent {n s e} (N : Nat) : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p =>
      if largePhase 19 g then trimSpent N p
      else if decide (N > 0) && largePhase 18 g then 1 + trimSpent (N - 1) p
      else trimSpent N p
  | .gate (.whenBit _ _ g) p =>
      if largePhase 19 g then trimSpent N p
      else if decide (N > 0) && largePhase 18 g then 1 + trimSpent (N - 1) p
      else trimSpent N p
  | .recordGate _ _ g p =>
      if largePhase 19 g then trimSpent N p
      else if decide (N > 0) && largePhase 18 g then 1 + trimSpent (N - 1) p
      else trimSpent N p
  | .measure _ p => trimSpent N p

theorem weight4_trimN {n s e} (N : Nat) (p : Straight n s e) :
    ConditionalCatalyst.weight4 (trimN N p) + removed 19 p + trimSpent N p =
      ConditionalCatalyst.weight4 p := by
  induction p generalizing N with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases h27 : largePhase 19 g = true
      · have hw := (dropped_weight23_local g h27).2
        simp only [trimN, trimSpent, h27, if_true, removed, Bool.toNat_true,
          ConditionalCatalyst.weight4, hw]
        (have h1 := ih N; have h2 := ih (N - 1); omega)
      · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 18 g) = true
        · have hg26 : largePhase 18 g = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
            exact hN.2
          have hw := (dropped_weight27 g hg26).2
          simp only [trimN, trimSpent, h27, Bool.false_eq_true, if_false, hN,
            if_true, removed, Bool.toNat_false, zero_add,
            ConditionalCatalyst.weight4, hw]
          (have h1 := ih N; have h2 := ih (N - 1); omega)
        · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
            Bool.eq_false_iff.mpr hN
          simp only [trimN, trimSpent, h27, Bool.false_eq_true, if_false, hNf,
            Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
            ConditionalCatalyst.weight4]
          (have h1 := ih N; have h2 := ih (N - 1); omega)
    | whenBit r v g =>
      by_cases h27 : largePhase 19 g = true
      · have hw := (dropped_weight23_local g h27).1
        simp only [trimN, trimSpent, h27, if_true, removed, Bool.toNat_true,
          ConditionalCatalyst.weight4, hw]
        (have h1 := ih N; have h2 := ih (N - 1); omega)
      · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 18 g) = true
        · have hg26 : largePhase 18 g = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
            exact hN.2
          have hw := (dropped_weight27 g hg26).1
          simp only [trimN, trimSpent, h27, Bool.false_eq_true, if_false, hN,
            if_true, removed, Bool.toNat_false, zero_add,
            ConditionalCatalyst.weight4, hw]
          (have h1 := ih N; have h2 := ih (N - 1); omega)
        · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
            Bool.eq_false_iff.mpr hN
          simp only [trimN, trimSpent, h27, Bool.false_eq_true, if_false, hNf,
            Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
            ConditionalCatalyst.weight4]
          (have h1 := ih N; have h2 := ih (N - 1); omega)
  | recordGate i v g p ih =>
    by_cases h27 : largePhase 19 g = true
    · have hw := (dropped_weight23_local g h27).1
      simp only [trimN, trimSpent, h27, if_true, removed, Bool.toNat_true,
        ConditionalCatalyst.weight4, hw]
      (have h1 := ih N; have h2 := ih (N - 1); omega)
    · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
      by_cases hN : (decide (N > 0) && largePhase 18 g) = true
      · have hg26 : largePhase 18 g = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
          exact hN.2
        have hw := (dropped_weight27 g hg26).1
        simp only [trimN, trimSpent, h27, Bool.false_eq_true, if_false, hN,
          if_true, removed, Bool.toNat_false, zero_add,
          ConditionalCatalyst.weight4, hw]
        (have h1 := ih N; have h2 := ih (N - 1); omega)
      · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
          Bool.eq_false_iff.mpr hN
        simp only [trimN, trimSpent, h27, Bool.false_eq_true, if_false, hNf,
          Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
          ConditionalCatalyst.weight4]
        (have h1 := ih N; have h2 := ih (N - 1); omega)
  | measure w p ih =>
    simp only [trimN, trimSpent, removed, ConditionalCatalyst.weight4, ih]

/-! === count family: how many k = 19 gates exist (cutoff-18 machinery) === -/

def droppedSlots26 : Nat → Nat → Nat
  | 0, _ => 0
  | width+1, prior => (prior - 17) + droppedSlots26 width (prior + 1)

def metadataDropped26 : List Nat → Nat → Nat
  | [], _ => 0
  | width :: ws, prior => droppedSlots26 width prior + metadataDropped26 ws (prior + width)

theorem removed26_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    removed 18 (p.append q) = removed 18 p + removed 18 q := by
  induction p with
  | done => simp [Straight.append, removed]
  | gate g p ih => cases g <;> simp [Straight.append, removed, ih, Nat.add_assoc]
  | recordGate i v g p ih => simp_all [Straight.append, removed, Nat.add_assoc]
  | measure w p ih => simp_all [Straight.append, removed]

theorem removed26_cast {n s e f} (p : Straight n s e) (h : e = f) :
    removed 18 (castFinish h p) = removed 18 p := by subst f; rfl

theorem removed26_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    removed 18 (reindexStraight f p) = removed 18 p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [reindexStraight, reindexGate, removed, ih]
    | whenBit r v g => simp_all [reindexStraight, reindexGate, removed, ih]
  | recordGate => simp_all [reindexStraight, removed]
  | measure => simp_all [reindexStraight, removed]

theorem removed26_feedback {n s e} (dir : ShorECDLP.PhaseDir) (w : ShorECDLP.Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    removed 18 (feedbackProgram dir w indices k p) =
      (indices.length - min indices.length (19 - k)) + removed 18 p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih =>
    simp only [feedbackProgram, removed, largePhase, ih, List.length_cons]
    by_cases hk : 18 < k
    · simp only [hk, decide_true, Bool.toNat_true]
      omega
    · simp only [hk, decide_false, Bool.toNat_false]
      omega

theorem removed26_prepare {n s e} (ws : List ShorECDLP.Wire) (p : Straight n s e) :
    removed 18 (prepareOuterBank ws p) = removed 18 p := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [prepareOuterBank, removed, largePhase] using ih

theorem removed_fourier26 (n : Nat) (dir : ShorECDLP.PhaseDir) (ws : List ShorECDLP.Wire)
    (start : Nat) (prior : List (Fin start)) :
    removed 18 (fourierProgram n dir ws start prior) = droppedSlots26 ws.length prior.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp [fourierProgram, removed26_cast, removed26_feedback,
      removed, ih, droppedSlots26]; omega

theorem weighted26_removed_framed {n s m k e f} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    removed 18 (Single.framed p q r h) = removed 18 p + removed 18 q + removed 18 r := by
  simp [Single.framed, removed, removed26_cast, removed26_append, largePhase, Nat.add_assoc]

theorem weighted26_removed_fixedEntry {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e) :
    removed 18 (Single.fixedEntry f p).program = removed 18 p := by
  unfold Single.fixedEntry
  exact removed26_reindex p _

theorem largePhase_mono (g : ShorECDLP.Gate) :
    (largePhase 19 g).toNat ≤ (largePhase 18 g).toNat := by
  cases g with
  | P dir k t =>
    simp only [largePhase]
    by_cases h : 19 < k
    · have h26 : 18 < k := by omega
      simp [h, h26, Bool.toNat_true]
    · simp [h, Bool.toNat_false, Nat.zero_le]
  | X t => simp only [largePhase, Bool.toNat_false] <;> omega
  | H t => simp only [largePhase, Bool.toNat_false] <;> omega
  | CX a b => simp only [largePhase, Bool.toNat_false] <;> omega
  | CCX a b c => simp only [largePhase, Bool.toNat_false] <;> omega

theorem largePhase_mono_true (g : ShorECDLP.Gate) (h : largePhase 19 g = true) :
    largePhase 18 g = true := by
  cases g with
  | P dir k t =>
    simp only [largePhase] at h ⊢
    have h27 : 19 < k := by simpa using h
    have h26 : 18 < k := by omega
    simp [h26]
  | X t => simp only [largePhase, Bool.false_eq_true] at h
  | H t => simp only [largePhase, Bool.false_eq_true] at h
  | CX a b => simp only [largePhase, Bool.false_eq_true] at h
  | CCX a b c => simp only [largePhase, Bool.false_eq_true] at h

theorem removed27_le_removed26 {n s e} (p : Straight n s e) :
    removed 19 p ≤ removed 18 p := by
  induction p with
  | done => simp only [removed]; omega
  | gate g p ih =>
    cases g with
    | literal g => simp only [removed]; exact Nat.add_le_add (largePhase_mono g) ih
    | whenBit r v g => simp only [removed]; exact Nat.add_le_add (largePhase_mono g) ih
  | recordGate i v g p ih => simp only [removed]; exact Nat.add_le_add (largePhase_mono g) ih
  | measure w p ih => simp only [removed]; exact ih

theorem droppedSlots_mono (w prior : Nat) :
    AffineLoss.droppedSlots23 w prior ≤ droppedSlots26 w prior := by
  induction w generalizing prior with
  | zero => simp only [AffineLoss.droppedSlots23, droppedSlots26]; omega
  | succ w ih =>
    simp only [AffineLoss.droppedSlots23, droppedSlots26]
    exact Nat.add_le_add (by omega) (ih (prior + 1))

theorem metadataDropped_mono (ws : List Nat) (p : Nat) :
    AffineLoss.metadataDropped23 ws p ≤ metadataDropped26 ws p := by
  induction ws generalizing p with
  | nil => simp only [AffineLoss.metadataDropped23, metadataDropped26]; omega
  | cons w ws ih =>
    simp only [AffineLoss.metadataDropped23, metadataDropped26]
    exact Nat.add_le_add (droppedSlots_mono w p) (ih (p + w))

/-- The count difference of the two cutoffs accumulates through `Single.axis`. -/
theorem removed_axis_diff [body : Single.WindowBody] [ledger : Single.ProducerResources body] {n}
    (ws : List (Single.Window n)) (widths : List Nat)
    (hw : List.Forall₂ (fun w c => w.wires.length = c) ws widths)
    (start : Nat) (prior : List (Fin start)) :
    metadataDropped26 widths prior.length - AffineLoss.metadataDropped23 widths prior.length ≤
      removed 18 (Single.axis ws start prior) - removed 19 (Single.axis ws start prior) := by
  induction ws generalizing widths start with
  | nil =>
    cases hw
    simp only [metadataDropped26, AffineLoss.metadataDropped23, Single.axis, removed]
    omega
  | cons w ws ih =>
    cases hw with
    | cons head tail =>
      rename_i c widths
      simp only [Single.axis, removed26_cast, AffineLoss.removed23_cast,
        removed26_append, AffineLoss.removed23_append, removed26_prepare,
        AffineLoss.removed23_prepare, removed_fourier26,
        AffineLoss.removed_fourier23, bankPrior_length]
      have ht := ih widths tail (start + w.count + w.wires.length)
        (Single.nextPrior w.count w.wires.length prior)
      rw [Single.nextPrior_length] at ht
      simp only [metadataDropped26, AffineLoss.metadataDropped23]
      have hA := removed27_le_removed26 (w.program start)
      have hR := removed27_le_removed26
        (Single.axis ws (start + w.count + c) (Single.nextPrior w.count c prior))
      have hD := droppedSlots_mono c prior.length
      have hm := metadataDropped_mono widths (prior.length + c)
      rw [head] at *
      omega

theorem trimSpent_eq {n s e} (N : Nat) (p : Straight n s e) :
    trimSpent N p = min N (removed 18 p - removed 19 p) := by
  induction p generalizing N with
  | done => simp only [trimSpent, removed]; omega
  | gate g p ih =>
    have hm : removed 19 p ≤ removed 18 p := removed27_le_removed26 p
    cases g with
    | literal g =>
      by_cases h27 : largePhase 19 g = true
      · have h26t : largePhase 18 g = true := largePhase_mono_true g h27
        simp only [trimSpent, h27, if_true]
        simp only [removed, h27, h26t, Bool.toNat_true]
        have h1 := ih N; omega
      · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 18 g) = true
        · have hg26 : largePhase 18 g = true := by
            have h := hN
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact h.2
          have hNpos : 0 < N := by
            have h := hN
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact h.1
          simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hN, if_true]
          simp only [removed, h27f, hg26, Bool.toNat_true, Bool.toNat_false, zero_add]
          have h1 := ih N; have h2 := ih (N - 1); omega
        · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
            Bool.eq_false_iff.mpr hN
          by_cases h26 : largePhase 18 g = true
          · have hN0 : N = 0 := by
              rcases Nat.eq_zero_or_pos N with h0 | hpos
              · exact h0
              · simp [h26, hpos] at hNf
            simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hNf, if_false]
            simp only [removed, h26, h27f, Bool.toNat_true, Bool.toNat_false, zero_add]
            have h1 := ih N; omega
          · have h26f : largePhase 18 g = false := Bool.eq_false_iff.mpr h26
            simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hNf, if_false]
            simp only [removed, h26f, h27f, Bool.toNat_false, zero_add]
            have h1 := ih N; omega
    | whenBit r v g =>
      by_cases h27 : largePhase 19 g = true
      · have h26t : largePhase 18 g = true := largePhase_mono_true g h27
        simp only [trimSpent, h27, if_true]
        simp only [removed, h27, h26t, Bool.toNat_true]
        have h1 := ih N; omega
      · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 18 g) = true
        · have hg26 : largePhase 18 g = true := by
            have h := hN
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact h.2
          have hNpos : 0 < N := by
            have h := hN
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact h.1
          simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hN, if_true]
          simp only [removed, h27f, hg26, Bool.toNat_true, Bool.toNat_false, zero_add]
          have h1 := ih N; have h2 := ih (N - 1); omega
        · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
            Bool.eq_false_iff.mpr hN
          by_cases h26 : largePhase 18 g = true
          · have hN0 : N = 0 := by
              rcases Nat.eq_zero_or_pos N with h0 | hpos
              · exact h0
              · simp [h26, hpos] at hNf
            simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hNf, if_false]
            simp only [removed, h26, h27f, Bool.toNat_true, Bool.toNat_false, zero_add]
            have h1 := ih N; omega
          · have h26f : largePhase 18 g = false := Bool.eq_false_iff.mpr h26
            simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hNf, if_false]
            simp only [removed, h26f, h27f, Bool.toNat_false, zero_add]
            have h1 := ih N; omega
  | recordGate i v g p ih =>
      have hm : removed 19 p ≤ removed 18 p := removed27_le_removed26 p
      by_cases h27 : largePhase 19 g = true
      · have h26t : largePhase 18 g = true := largePhase_mono_true g h27
        simp only [trimSpent, h27, if_true]
        simp only [removed, h27, h26t, Bool.toNat_true]
        have h1 := ih N; omega
      · have h27f : largePhase 19 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 18 g) = true
        · have hg26 : largePhase 18 g = true := by
            have h := hN
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact h.2
          have hNpos : 0 < N := by
            have h := hN
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact h.1
          simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hN, if_true]
          simp only [removed, h27f, hg26, Bool.toNat_true, Bool.toNat_false, zero_add]
          have h1 := ih N; have h2 := ih (N - 1); omega
        · have hNf : (decide (N > 0) && largePhase 18 g) = false :=
            Bool.eq_false_iff.mpr hN
          by_cases h26 : largePhase 18 g = true
          · have hN0 : N = 0 := by
              rcases Nat.eq_zero_or_pos N with h0 | hpos
              · exact h0
              · simp [h26, hpos] at hNf
            simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hNf, if_false]
            simp only [removed, h26, h27f, Bool.toNat_true, Bool.toNat_false, zero_add]
            have h1 := ih N; omega
          · have h26f : largePhase 18 g = false := Bool.eq_false_iff.mpr h26
            simp only [trimSpent, h27f, Bool.false_eq_true, if_false, hNf, if_false]
            simp only [removed, h26f, h27f, Bool.toNat_false, zero_add]
            have h1 := ih N; omega
  | measure w p ih => simp only [trimSpent, removed, ih]



def activeCost {n s e} (N : Nat) : Straight n s e → ℝ
  | .done => 0
  | .gate (.literal g) p =>
      if largePhase 19 g then charge23 g + activeCost N p
      else if decide (N > 0) && largePhase 18 g then unit23 + activeCost (N-1) p
      else activeCost N p
  | .gate (.whenBit _ _ g) p =>
      if largePhase 19 g then charge23 g + activeCost N p
      else if decide (N > 0) && largePhase 18 g then unit23 + activeCost (N-1) p
      else activeCost N p
  | .recordGate _ _ g p =>
      if largePhase 19 g then charge23 g + activeCost N p
      else if decide (N > 0) && largePhase 18 g then unit23 + activeCost (N-1) p
      else activeCost N p
  | .measure _ p => activeCost N p

theorem unit23_pos : (0:ℝ)<unit23 := by unfold unit23; positivity

theorem activeCost_nonneg {n s e} (N : Nat) (p : Straight n s e) : 0 ≤ activeCost N p := by
  induction p generalizing N with
  | done => rfl
  | measure w p ih => exact ih N
  | gate g p ih => cases g <;> simp only [activeCost] <;> split_ifs <;>
      first | exact add_nonneg (charge23_nonneg _) (ih _) | exact add_nonneg unit23_pos.le (ih _) | exact ih _
  | recordGate i v g p ih => simp only [activeCost]; split_ifs <;>
      first | exact add_nonneg (charge23_nonneg _) (ih _) | exact add_nonneg unit23_pos.le (ih _) | exact ih _

theorem activeCost_bound {n s e} (N : Nat) (p : Straight n s e) :
    activeCost N p ≤ cost23 p + N*unit23 := by
  induction p generalizing N with
  | done => simp only [activeCost,cost23,zero_add]; exact mul_nonneg (Nat.cast_nonneg _) unit23_pos.le
  | measure w p ih => exact ih N
  | recordGate i v g p ih =>
    have ht := ih N
    have hc := charge23_nonneg g
    by_cases hg : largePhase 19 g = true
    · simp only [activeCost,hg,if_true,cost23]; linarith
    · have hgf : largePhase 19 g = false := Bool.eq_false_iff.mpr hg
      have hz := charge23_false g hgf
      by_cases hN : (decide (N>0) && largePhase 18 g) = true
      · have hpos : 0<N := by
          have h := hN
          simp only [Bool.and_eq_true,decide_eq_true_eq] at h
          exact h.1
        have hn : ((N-1:Nat):ℝ) = (N:ℝ)-1 := Nat.cast_pred hpos
        have ht' := ih (N-1)
        rw [hn] at ht'
        simp only [activeCost,hgf,Bool.false_eq_true,if_false,hN,if_true,cost23,hz,zero_add]
        linarith
      · have hNf : (decide (N>0) && largePhase 18 g) = false := Bool.eq_false_iff.mpr hN
        simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNf,cost23,hz,zero_add] using ht
  | gate g p ih =>
    cases g with
    | literal g =>
      have ht := ih N
      have hc := charge23_nonneg g
      by_cases hg : largePhase 19 g = true
      · simp only [activeCost,hg,if_true,cost23]; linarith
      · have hgf : largePhase 19 g = false := Bool.eq_false_iff.mpr hg
        have hz := charge23_false g hgf
        by_cases hN : (decide (N>0) && largePhase 18 g) = true
        · have hpos : 0<N := by
            have h := hN
            simp only [Bool.and_eq_true,decide_eq_true_eq] at h
            exact h.1
          have hn : ((N-1:Nat):ℝ) = (N:ℝ)-1 := Nat.cast_pred hpos
          have ht' := ih (N-1)
          rw [hn] at ht'
          simp only [activeCost,hgf,Bool.false_eq_true,if_false,hN,if_true,cost23,hz,zero_add]
          linarith
        · have hNf : (decide (N>0) && largePhase 18 g) = false := Bool.eq_false_iff.mpr hN
          simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNf,cost23,hz,zero_add] using ht
    | whenBit r v g =>
      have ht := ih N
      have hc := charge23_nonneg g
      by_cases hg : largePhase 19 g = true
      · simp only [activeCost,hg,if_true,cost23]; linarith
      · have hgf : largePhase 19 g = false := Bool.eq_false_iff.mpr hg
        have hz := charge23_false g hgf
        by_cases hN : (decide (N>0) && largePhase 18 g) = true
        · have hpos : 0<N := by
            have h := hN
            simp only [Bool.and_eq_true,decide_eq_true_eq] at h
            exact h.1
          have hn : ((N-1:Nat):ℝ) = (N:ℝ)-1 := Nat.cast_pred hpos
          have ht' := ih (N-1)
          rw [hn] at ht'
          simp only [activeCost,hgf,Bool.false_eq_true,if_false,hN,if_true,cost23,hz,zero_add]
          linarith
        · have hNf : (decide (N>0) && largePhase 18 g) = false := Bool.eq_false_iff.mpr hN
          simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNf,cost23,hz,zero_add] using ht

theorem band_affine {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (g : ShorECDLP.Gate) (hg : largePhase 18 g = true) (hf : largePhase 19 g = false) :
    expectation read p history psi accept ≤
      (1+10*unit23)*expectation read p history (applyGate g psi) accept +
        (unit23/10+unit23^2)*normSq psi := by
  cases g <;> simp only [largePhase,Bool.false_eq_true] at hg hf
  case P dir k t =>
    have hk : k=19 := by
      have h1 : 18<k := by simpa using hg
      have h2 : ¬19<k := by simpa using hf
      omega
    subst hk
    have ha : (phaseAngle dir 19/2)^2 ≤ unit23^2 := by
      have hpi := Real.pi_lt_d6
      have hb : 2*Real.pi/(2:ℝ)^19/2 ≤ unit23 := by norm_num [unit23]; linarith
      have hz : 0 ≤ 2*Real.pi/(2:ℝ)^19/2 := by positivity
      cases dir <;> simp only [phaseAngle,neg_div,neg_sq] <;> nlinarith
    exact phase_affine read p history psi accept hp dir 19 t unit23 unit23_pos ha

theorem trimN_affine {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (N : Nat) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (hb : activeCost N p ≤ 14741/1000000) :
    expectation read (trimN N p) history psi accept ≤
      (1+(11729/1000)*activeCost N p)*expectation read p history psi accept +
        (11729/100000)*activeCost N p*normSq psi := by
  induction p generalizing N psi with
  | done => simp [trimN,activeCost,expectation]
  | measure w p ih =>
    have h0 := ih N (Fin.lastCases false history) (xResetKraus w false psi) accept hp hb
    have h1 := ih N (Fin.lastCases true history) (xResetKraus w true psi) accept hp hb
    have hm := normSq_xResetKraus_false_add_true w psi
    simp only [trimN,activeCost,expectation]
    apply (add_le_add h0 h1).trans_eq
    rw [← hm]
    ring
  | recordGate i v g p ih =>
    have hM := mass_nonneg psi
    by_cases hg : largePhase 19 g = true
    · have ht := activeCost_nonneg N p
      have hd : 0≤charge23 g := charge23_nonneg g
      have hb' : activeCost N p ≤ 14741/1000000 := by
        simp only [activeCost,hg,if_true] at hb
        linarith
      have hi := ih N history psi accept hp.2 hb'
      have hs := dropped_affine read p history psi accept hp.2 g hg
      have hb'' : activeCost N p+charge23 g ≤ 14741/1000000 := by
        simpa only [activeCost,hg,if_true,add_comm] using hb
      simp only [trimN,hg,if_true,expectation]
      by_cases hr : history i=v
      · simp only [hr,if_true,run_singleton]
        simpa only [activeCost,hg,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history (applyGate g psi) accept) hM hs hi
      · simp only [hr,if_false,run_nil,LinearMap.id_coe,id_eq]
        have hidle := idle_affine (charge23 g) (expectation read p history psi accept) (normSq psi) hd (expectation_nonneg read p history psi accept) hM
        simpa only [activeCost,hg,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history psi accept) hM hidle hi
    · have hgf : largePhase 19 g = false := Bool.eq_false_iff.mpr hg
      by_cases hNb : (decide (N>0) && largePhase 18 g) = true
      · have hN : 0<N ∧ largePhase 18 g = true := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using hNb
        have ht := activeCost_nonneg (N-1) p
        have hd : 0≤unit23 := unit23_pos.le
        have hb' : activeCost (N-1) p ≤ 14741/1000000 := by
          simp only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true] at hb
          linarith
        have hi := ih (N-1) history psi accept hp.2 hb'
        have hs := band_affine read p history psi accept hp.2 g hN.2 hgf
        have hb'' : activeCost (N-1) p+unit23 ≤ 14741/1000000 := by
          simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true,add_comm] using hb
        simp only [trimN,hgf,Bool.false_eq_true,if_false,hNb,if_true,expectation]
        by_cases hr : history i=v
        · simp only [hr,if_true,run_singleton]
          simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history (applyGate g psi) accept) hM hs hi
        · simp only [hr,if_false,run_nil,LinearMap.id_coe,id_eq]
          have hidle := idle_affine (unit23) (expectation read p history psi accept) (normSq psi) hd (expectation_nonneg read p history psi accept) hM
          simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history psi accept) hM hidle hi
      · have hNf : (decide (N>0) && largePhase 18 g) = false := Bool.eq_false_iff.mpr hNb
        have hb' : activeCost N p ≤ 14741/1000000 := by simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNf] using hb
        have hi := ih N history (Quantum.run (if history i=v then [g] else []) psi) accept hp.2 hb'
        have hn : normSq (Quantum.run (if history i=v then [g] else []) psi) = normSq psi := by
          apply normSq_run
          split_ifs
          · simpa [CircuitWellFormed] using hp.1
          · simp [CircuitWellFormed]
        rw [hn] at hi
        simpa only [trimN,activeCost,hgf,Bool.false_eq_true,if_false,hNf,expectation] using hi
  | gate g p ih =>
    cases g with
    | literal g =>
      have hM := mass_nonneg psi
      by_cases hg : largePhase 19 g = true
      · have ht := activeCost_nonneg N p
        have hd : 0≤charge23 g := charge23_nonneg g
        have hb' : activeCost N p ≤ 14741/1000000 := by
          simp only [activeCost,hg,if_true] at hb
          linarith
        have hi := ih N history psi accept hp.2 hb'
        have hs := dropped_affine read p history psi accept hp.2 g hg
        have hb'' : activeCost N p+charge23 g ≤ 14741/1000000 := by
          simpa only [activeCost,hg,if_true,add_comm] using hb
        simp only [trimN,hg,if_true,expectation,TemplateGate.instantiate,run_singleton]
        simpa only [activeCost,hg,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history (applyGate g psi) accept) hM hs hi
      · have hgf : largePhase 19 g = false := Bool.eq_false_iff.mpr hg
        by_cases hNb : (decide (N>0) && largePhase 18 g) = true
        · have hN : 0<N ∧ largePhase 18 g = true := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using hNb
          have ht := activeCost_nonneg (N-1) p
          have hd : 0≤unit23 := unit23_pos.le
          have hb' : activeCost (N-1) p ≤ 14741/1000000 := by
            simp only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true] at hb
            linarith
          have hi := ih (N-1) history psi accept hp.2 hb'
          have hs := band_affine read p history psi accept hp.2 g hN.2 hgf
          have hb'' : activeCost (N-1) p+unit23 ≤ 14741/1000000 := by
            simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true,add_comm] using hb
          simp only [trimN,hgf,Bool.false_eq_true,if_false,hNb,if_true,expectation,TemplateGate.instantiate,run_singleton]
          simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history (applyGate g psi) accept) hM hs hi
        · have hNf : (decide (N>0) && largePhase 18 g) = false := Bool.eq_false_iff.mpr hNb
          have hb' : activeCost N p ≤ 14741/1000000 := by simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNf] using hb
          have hi := ih N history (Quantum.run [g] psi) accept hp.2 hb'
          have hn : normSq (Quantum.run [g] psi) = normSq psi := by
            apply normSq_run
            simpa [CircuitWellFormed] using hp.1
          rw [hn] at hi
          simpa only [trimN,activeCost,hgf,Bool.false_eq_true,if_false,hNf,expectation,TemplateGate.instantiate] using hi
    | whenBit r v g =>
      have hM := mass_nonneg psi
      by_cases hg : largePhase 19 g = true
      · have ht := activeCost_nonneg N p
        have hd : 0≤charge23 g := charge23_nonneg g
        have hb' : activeCost N p ≤ 14741/1000000 := by
          simp only [activeCost,hg,if_true] at hb
          linarith
        have hi := ih N history psi accept hp.2 hb'
        have hs := dropped_affine read p history psi accept hp.2 g hg
        have hb'' : activeCost N p+charge23 g ≤ 14741/1000000 := by
          simpa only [activeCost,hg,if_true,add_comm] using hb
        simp only [trimN,hg,if_true,expectation,TemplateGate.instantiate]
        by_cases hr : read r=v
        · simp only [hr,if_true,run_singleton]
          simpa only [activeCost,hg,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history (applyGate g psi) accept) hM hs hi
        · simp only [hr,if_false,run_nil,LinearMap.id_coe,id_eq]
          have hidle := idle_affine (charge23 g) (expectation read p history psi accept) (normSq psi) hd (expectation_nonneg read p history psi accept) hM
          simpa only [activeCost,hg,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history psi accept) hM hidle hi
      · have hgf : largePhase 19 g = false := Bool.eq_false_iff.mpr hg
        by_cases hNb : (decide (N>0) && largePhase 18 g) = true
        · have hN : 0<N ∧ largePhase 18 g = true := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using hNb
          have ht := activeCost_nonneg (N-1) p
          have hd : 0≤unit23 := unit23_pos.le
          have hb' : activeCost (N-1) p ≤ 14741/1000000 := by
            simp only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true] at hb
            linarith
          have hi := ih (N-1) history psi accept hp.2 hb'
          have hs := band_affine read p history psi accept hp.2 g hN.2 hgf
          have hb'' : activeCost (N-1) p+unit23 ≤ 14741/1000000 := by
            simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true,add_comm] using hb
          simp only [trimN,hgf,Bool.false_eq_true,if_false,hNb,if_true,expectation,TemplateGate.instantiate]
          by_cases hr : read r=v
          · simp only [hr,if_true,run_singleton]
            simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history (applyGate g psi) accept) hM hs hi
          · simp only [hr,if_false,run_nil,LinearMap.id_coe,id_eq]
            have hidle := idle_affine (unit23) (expectation read p history psi accept) (normSq psi) hd (expectation_nonneg read p history psi accept) hM
            simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNb,if_true,add_comm] using compose_bound _ _ _ _ _ _ ht hd hb'' (expectation_nonneg read p history psi accept) hM hidle hi
        · have hNf : (decide (N>0) && largePhase 18 g) = false := Bool.eq_false_iff.mpr hNb
          have hb' : activeCost N p ≤ 14741/1000000 := by simpa only [activeCost,hgf,Bool.false_eq_true,if_false,hNf] using hb
          have hi := ih N history (Quantum.run ((TemplateGate.whenBit r v g).instantiate read) psi) accept hp.2 hb'
          have hn : normSq (Quantum.run ((TemplateGate.whenBit r v g).instantiate read) psi) = normSq psi := by
            exact normSq_template read (.whenBit r v g) hp.1 psi
          rw [hn] at hi
          simpa only [trimN,activeCost,hgf,Bool.false_eq_true,if_false,hNf,expectation,TemplateGate.instantiate] using hi


open Width16Schedule
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
set_option linter.unusedSectionVars false
theorem exact_band_metadata :
    (metadataDropped26 [9] 0 - AffineLoss.metadataDropped23 [9] 0) +
    (metadataDropped26 [8] 0 - AffineLoss.metadataDropped23 [8] 0) +
    (metadataDropped26 leftWidthsBody 9 - AffineLoss.metadataDropped23 leftWidthsBody 9) +
    (metadataDropped26 rightWidthsBody 8 - AffineLoss.metadataDropped23 rightWidthsBody 8) = 432 := by
  decide +kernel

theorem axes_band_count (impl : Implementation) (start : Nat) :
    432 ≤ (removed 18 (mixHead impl.headA start) +
      removed 18 (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) start)) -
      (removed 19 (mixHead impl.headA start) +
      removed 19 (mixTail impl.headA impl.headB (leftBodies impl) (rightBodies impl) start)) := by
  have hA := removed_axis_diff ([impl.headA]) ([9]) (headA_width_relation impl) start List.nil
  have hB := removed_axis_diff ([impl.headB]) ([8]) (headB_width_relation impl)
    (mixS1 impl.headA start) List.nil
  have hL := removed_axis_diff (leftBodies impl) leftWidthsBody (left_width_relation impl)
    (mixS2 impl.headA impl.headB start) (mixPriorL impl.headA impl.headB start)
  have hR := removed_axis_diff (rightBodies impl) rightWidthsBody (right_width_relation impl)
    (mixS3 impl.headA impl.headB (leftBodies impl) start)
    (mixPriorR impl.headA impl.headB (leftBodies impl) start)
  rw [mixPriorL_length] at hL
  rw [mixPriorR_length] at hR
  simp only [List.length_nil] at hA hB
  have hb := exact_band_metadata
  have m1 := removed27_le_removed26 (Single.axis ([impl.headA]) start List.nil)
  have m2 := removed27_le_removed26 (Single.axis ([impl.headB]) (mixS1 impl.headA start) List.nil)
  have m3 := removed27_le_removed26 (Single.axis (leftBodies impl)
    (mixS2 impl.headA impl.headB start) (mixPriorL impl.headA impl.headB start))
  have m4 := removed27_le_removed26 (Single.axis (rightBodies impl)
    (mixS3 impl.headA impl.headB (leftBodies impl) start)
    (mixPriorR impl.headA impl.headB (leftBodies impl) start))
  simp only [mixHead, mixTail, removed26_append, AffineLoss.removed23_append]
  omega

theorem fullProgram_band_count (impl : Implementation) (reset : List Wire) :
    432 ≤ removed 18 (fullProgram impl reset) - removed 19 (fullProgram impl reset) := by
  have h := axes_band_count impl 0
  have hz := removed27_le_removed26
    (resetProgram 1769472 (mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0) reset)
  have hro := removed27_le_removed26 (readout impl reset)
  simp only [fullProgram, removed26_append, AffineLoss.removed23_append,
    Width16Schedule.program, weighted26_removed_framed, AffineLoss.weighted23_removed_framed]
  omega



theorem source_spent126 (impl : Implementation) (reset : List ShorECDLP.Wire) :
    trimSpent 126 (sourceEntry impl reset).program = 126 := by
  rw [trimSpent_eq]
  have h := fullProgram_band_count impl reset
  unfold sourceEntry
  rw [weighted26_removed_fixedEntry,AffineLoss.weighted23_removed_fixedEntry]
  omega

#print axioms trimN_affine
#print axioms activeCost_bound
#print axioms source_spent126
end
end ShorECDLP.Entrant.Phase23Partial
